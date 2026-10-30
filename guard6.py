#!/usr/bin/env python3
# guard6 — расширение 6.0 для guard.py. Кладётся В ОДНУ ПАПКУ с guard.py и guard5.py; guard.py сам его подхватывает.
#
# Что это. Не новые команды, а усиление трёх уже существующих вещей и защита от упора в лимиты Telegram.
#
# ▸ ПОЛНАЯ ЗАЩИТА (и вообще любая волна, 50+ скамеров):
#     «Дозатор»         все запросы бота к Telegram идут через один регулятор: бан/мут/удаление — вне очереди и без потерь,
#                       «косметика» (объявления, правки) при перегрузке тихо пропускается; после 429 чат «остывает» один раз
#                       на всех, а не каждый запрос засыпает отдельно (раньше тик бота мог зависать на минуты).
#     «Очередь капч»    при волне входов капчи уходят в чат не быстрее лимита группы (20/мин). Раньше при отказе Telegram
#                       отправить капчу бот СНИМАЛ ограничение — скамер входил без проверки. Теперь он остаётся «только чтение»,
#                       а капча ждёт очереди; не дождался за 2 минуты — убирается на 90 секунд (вернуться может сразу).
#     «Сводка волны»    сверх нескольких тревог в минуту владельцу/в журнал/в чат идёт ОДНА сводка раз в ~25 секунд вместо
#                       50 одиночных сообщений. Первые события — как раньше, с кнопками.
#     «Страховка»       когда полная защита выключается, владелец получает список тех, кого она наказала БЕЗ сильных улик,
#                       и кнопку «↩️ Вернуть слабые» (одним нажатием, без десятков сообщений в чат).
#     «Тихая сеть»      «второй взгляд» (RDAP, t.me) во время волны не ждёт сеть и не копит очередь: в волну ссылки и так закрыты.
#     «Перебор?»        отменили 2 наказания за 10 минут, пока включена полная защита, — бот спрашивает, не слишком ли строго
#                       (кнопки «Снять защиту» / «Оставить»). Сам ничего не отключает.
# ▸ СЛЕДОПЫТ (новые улики; работают только в режиме on, в режиме log — лишь пишутся в журнал):
#     «Стая»            три новых аккаунта за 10 минут отвечают контактами под одним сообщением.
#     «Обход вопросов»  один аккаунт раздаёт один и тот же контакт под тремя разными сообщениями (даже разными словами).
#     «Смена облика»    имя/юзернейм сменились за последний час перед сообщением с контактом (слабая улика: только вместе с другой).
# ▸ КУКОЛЬНЫЙ ТЕАТР:
#     «Хор»             без вопроса: питч новичка и «работает!» от двух других новичков (раньше нужен был вопрос).
#     «Одна рука»       участники сцены вошли в чат почти одновременно — сцена увереннее (+1.5, у неполных сцен меньше).
#     «Дела для кукол»  участников постановки, которых бот наказал, теперь можно вернуть одной кнопкой (раньше дела не было).
#
# Как включается. Ничего настраивать не нужно. GUARD6=0 выключает всё сразу (бот работает как 5.0); отдельные части —
# GUARD6_GOV / _CAPQ / _DIGEST / _RESCUE / _SOFTNET / _OVERKILL / _TRACE / _PUPPET = 0.
# Ничего здесь не банит и не наказывает само: расширение только делает то, что уже умел бот, надёжнее и тише; любой сбой
# внутри глушится, пять сбоев подряд отключают узел на 30 минут и бот идёт как 5.0.
from __future__ import annotations

import asyncio
import contextvars
import logging
import os
import re
import time
from collections import defaultdict, deque
from typing import Any

V6_VERSION = "6.0"
log = logging.getLogger("guard.v6")


# ═══════════════════════════════ связь с guard.py ═══════════════════════════════
class _NS:
    """Имена из guard.py (esc, mention, make_captcha…): заполняются один раз функцией bind(globals())."""

    def __getattr__(self, name: str):
        raise AttributeError("guard6: имя %r из guard.py не передано (bind не вызывался?)" % name)


G = _NS()
_GLOBALS: dict = {}


def bind(g: dict) -> None:
    _GLOBALS.clear()
    _GLOBALS["g"] = g
    for k, v in g.items():
        if not k.startswith("__"):
            setattr(G, k, v)


def _flag(name: str, default: bool = True) -> bool:
    v = os.getenv(name)
    if v is None or not v.strip():
        return default
    return v.strip().lower() not in ("0", "off", "no", "false", "нет", "выкл")


FEATS = ("gov", "capq", "digest", "rescue", "softnet", "overkill", "trace", "puppet")
ON: dict = {}


def reload_env() -> None:
    ON.clear()
    ON["all"] = _flag("GUARD6", True)
    for k in FEATS:
        ON[k] = ON["all"] and _flag("GUARD6_" + k.upper(), True)


reload_env()


def feat(name: str) -> bool:
    return bool(ON.get(name))


class Breaker:
    """Любой сбой внутри расширения глушится; 5 подряд — узел отключается на 30 минут."""

    def __init__(self):
        self.fails: dict = {}
        self.off: dict = {}

    def ok(self, name: str) -> bool:
        return time.time() >= self.off.get(name, 0)

    def bad(self, name: str) -> None:
        n = self.fails.get(name, 0) + 1
        self.fails[name] = n
        log.exception("расширение 6.0: сбой в узле %r (%d подряд)", name, n)
        if n >= 5:
            self.off[name] = time.time() + 1800
            self.fails[name] = 0
            log.error("расширение 6.0: узел %r отключён на 30 минут", name)

    def good(self, name: str) -> None:
        if self.fails.get(name):
            self.fails[name] = 0

    def run(self, name: str, fn, *a, default=None, **kw):
        if not self.ok(name):
            return default
        try:
            r = fn(*a, **kw)
            self.good(name)
            return r
        except asyncio.CancelledError:
            raise
        except Exception:                                            # noqa: BLE001
            self.bad(name)
            return default

    async def arun(self, name: str, fn, *a, default=None, **kw):
        if not self.ok(name):
            return default
        try:
            r = await fn(*a, **kw)
            self.good(name)
            return r
        except asyncio.CancelledError:
            raise
        except Exception:                                            # noqa: BLE001
            self.bad(name)
            return default


BR = Breaker()


# ═══════════════════════════════ «Дозатор»: регулятор запросов к Telegram ═══════════════════════════════
# Ориентиры Telegram: ≈30 сообщений/с на бота, ≈20 сообщений/мин в одну группу, ≈1 сообщение/с в личку.
# Берём с запасом. Чтение (get_chat_member и т.п.) и ответы на кнопки не ограничиваем.
CRIT_METHODS = frozenset({
    "ban_chat_member", "unban_chat_member", "restrict_chat_member", "ban_chat_sender_chat", "unban_chat_sender_chat",
    "delete_message", "delete_messages", "decline_chat_join_request", "approve_chat_join_request",
    "delete_all_message_reactions", "set_chat_permissions",
})
FREE_METHODS = frozenset({
    "get_me", "get_chat", "get_chat_member", "get_chat_administrators", "get_chat_member_count", "get_file",
    "answer_callback_query", "get_updates", "set_my_commands",
})
RATE_CRIT, BURST_CRIT = 25.0, 30.0
RATE_HIGH, BURST_HIGH = 8.0, 10.0
RATE_COSM, BURST_COSM = 4.0, 6.0
GROUP_SENDS_PER_MIN = 15          # у Telegram около 20 в минуту на группу; оставляем запас на чужие сообщения бота
DM_GAP = 1.0                      # между сообщениями в одну личку
MAX_WAIT = {"crit": 8.0, "high": 10.0, "cosm": 1.5}
FLOOD_GLOBAL_N, FLOOD_GLOBAL_WIN = 3, 30.0


class Bucket:
    __slots__ = ("rate", "burst", "tokens", "t")

    def __init__(self, rate: float, burst: float, now: float):
        self.rate, self.burst, self.tokens, self.t = rate, burst, burst, now

    def take(self, now: float) -> float:
        """Резервирует один запрос; возвращает, сколько секунд ждать (0 — можно сразу)."""
        self.tokens = min(self.burst, self.tokens + max(0.0, now - self.t) * self.rate)
        self.t = now
        self.tokens -= 1.0
        return 0.0 if self.tokens >= 0 else -self.tokens / self.rate

    def refund(self) -> None:
        self.tokens = min(self.burst, self.tokens + 1.0)


class Governor:
    """Чистая логика без Telegram и без asyncio — поэтому проверяется тестами. clock() — любые монотонные секунды."""

    def __init__(self, clock=time.monotonic):
        self.clock = clock
        now = clock()
        self.b = {"crit": Bucket(RATE_CRIT, BURST_CRIT, now), "high": Bucket(RATE_HIGH, BURST_HIGH, now),
                  "cosm": Bucket(RATE_COSM, BURST_COSM, now)}
        self.sends: dict[int, deque] = defaultdict(deque)       # chat → время сообщений бота в группу
        self.dm_next: dict[int, float] = {}                     # user → когда можно слать в личку
        self.chat_flood: dict[int, float] = {}                  # chat → до какого момента Telegram просил подождать
        self.global_flood = 0.0
        self.flood_log: deque = deque(maxlen=20)
        self.stat = {"pass": 0, "wait": 0, "drop": 0, "flood": 0}

    # ---- классификация ----
    @staticmethod
    def classify(method: str, a: tuple, kw: dict) -> tuple:
        chat = kw.get("chat_id")
        if chat is None and a and isinstance(a[0], int):
            chat = a[0]
        if method in FREE_METHODS:
            return "free", chat
        if method in CRIT_METHODS:
            return "crit", chat
        if method == "send_message":
            if isinstance(chat, int) and chat > 0:
                return "high", chat                              # личка (владелец, пользователь): не теряем, только по очереди
            return ("high" if kw.get("reply_markup") is not None else "cosm"), chat
        return "cosm", chat

    def group_room(self, chat: int, now: float | None = None) -> int:
        """Сколько сообщений бот ещё может отправить в группу за эту минуту в рамках запаса."""
        now = self.clock() if now is None else now
        dq = self.sends[chat]
        while dq and now - dq[0] > 60.0:
            dq.popleft()
        return GROUP_SENDS_PER_MIN - len(dq)

    def cooling(self, chat: int | None, now: float | None = None) -> float:
        now = self.clock() if now is None else now
        return max(self.global_flood - now, (self.chat_flood.get(chat, 0.0) - now) if chat is not None else 0.0, 0.0)

    # ---- допуск ----
    def admit(self, prio: str, method: str, chat: int | None, now: float | None = None):
        """→ секунды ожидания или None (пропустить запрос: только для «косметики»)."""
        now = self.clock() if now is None else now
        if prio == "free":
            self.stat["pass"] += 1
            return 0.0
        cool = self.cooling(chat, now)
        if cool > 0 and prio == "cosm":
            self.stat["drop"] += 1
            return None
        wait = min(cool, 30.0)
        bucket = self.b[prio]
        wait = max(wait, bucket.take(now))
        group_send = method == "send_message" and isinstance(chat, int) and chat < 0
        if group_send:
            room = self.group_room(chat, now)
            if room <= 0:
                if prio == "cosm":
                    bucket.refund()
                    self.stat["drop"] += 1
                    return None
                dq = self.sends[chat]
                wait = max(wait, 60.0 - (now - dq[0]) if dq else 0.0)
        elif method == "send_message" and isinstance(chat, int) and chat > 0:
            nxt = self.dm_next.get(chat, 0.0)
            wait = max(wait, nxt - now)
            self.dm_next[chat] = max(nxt, now) + DM_GAP
            if len(self.dm_next) > 2000:
                self.dm_next = {k: v for k, v in self.dm_next.items() if v > now}
        if wait > MAX_WAIT[prio]:
            if prio == "cosm":
                bucket.refund()
                self.stat["drop"] += 1
                return None
            wait = MAX_WAIT[prio]
        if group_send:
            self.sends[chat].append(now + wait)
        self.stat["wait" if wait > 0.05 else "pass"] += 1
        return wait

    def flood(self, chat: int | None, retry: float, now: float | None = None) -> None:
        """Telegram ответил 429: чат (или весь бот, если это уже не первый раз) остывает ОДИН раз для всех запросов."""
        now = self.clock() if now is None else now
        retry = max(0.5, min(float(retry), 60.0))
        self.stat["flood"] += 1
        self.flood_log.append(now)
        if chat is not None:
            self.chat_flood[chat] = max(self.chat_flood.get(chat, 0.0), now + retry)
        recent = sum(1 for t in self.flood_log if now - t <= FLOOD_GLOBAL_WIN)
        if chat is None or recent >= FLOOD_GLOBAL_N:
            self.global_flood = max(self.global_flood, now + min(retry, 10.0))
        if len(self.chat_flood) > 500:
            self.chat_flood = {k: v for k, v in self.chat_flood.items() if v > now}


# ═══════════════════════════════ «Сводка волны» ═══════════════════════════════
DIG_DIRECT, DIG_WINDOW, DIG_FLUSH, DIG_MAX_LINES = 5, 60.0, 25.0, 12
NOTICE_DIRECT, NOTICE_WINDOW = 3, 30.0
CHATTY_NOTICES = frozenset({"ban_spam", "warn", "mute", "hacked", "captcha_timeout", "captcha_fail", "captcha_ok", "puppet",
                            "ring_mute"})
_TAG_RX = re.compile(r"<[^>]+>")
_ALERT_RX = re.compile(r"Участник:\s*(?P<who>.+?)\s*\n.*?Причина:\s*(?P<why>.+?)\s*\n\s*Что сделал:\s*(?P<what>.+)", re.S)
_LOG_RX = re.compile(r"^(?P<head>.+?)\n(?P<who>.+?\(<code>-?\d+</code>\)):\s*(?P<what>.+?)\nПричина:\s*(?P<why>.+)$", re.S)


def _plain(s: str, n: int = 80) -> str:
    return re.sub(r"\s+", " ", _TAG_RX.sub("", s or "")).strip()[:n]


def digest_line(kind: str, text: str) -> tuple:
    """→ (заголовок чата, короткая строка) или None, если текст не похож на «наказали участника» (тогда он идёт как обычно)."""
    if kind == "alert":
        m = _ALERT_RX.search(text or "")
        if not m:
            return None
        head = _plain((text or "").split("\n", 1)[0], 60)
        return head, f"{_plain(m.group('who'), 40)} — {_plain(m.group('what'), 30)}: {_plain(m.group('why'), 70)}"
    m = _LOG_RX.match((text or "").strip())
    if not m:
        return None
    return _plain(m.group("head"), 60), f"{_plain(m.group('who'), 40)} — {_plain(m.group('what'), 30)}: {_plain(m.group('why'), 70)}"


class Digest:
    def __init__(self, clock=time.time):
        self.clock = clock
        self.hist: dict = defaultdict(deque)      # key → время прямых отправок
        self.buf: dict = {}                       # key → {"t0", "head", "lines"}
        self.notes: dict = defaultdict(deque)     # chat → время «чатовых» объявлений
        self.muted: dict = {}                     # chat → [сколько скрыто, когда началось]
        self.last_sum: dict = {}

    def direct_ok(self, key, now: float) -> bool:
        dq = self.hist[key]
        while dq and now - dq[0] > DIG_WINDOW:
            dq.popleft()
        if len(dq) < DIG_DIRECT and key not in self.buf:
            dq.append(now)
            return True
        return False

    def hold(self, key, head: str, line: str, now: float) -> None:
        b = self.buf.setdefault(key, {"t0": now, "head": head, "lines": [], "n": 0})
        b["n"] += 1
        if len(b["lines"]) < DIG_MAX_LINES * 3:
            b["lines"].append(line)

    def due(self, now: float) -> list:
        out = []
        for key, b in list(self.buf.items()):
            if now - b["t0"] >= DIG_FLUSH or b["n"] >= 40:
                self.buf.pop(key, None)
                out.append((key, b))
        return out

    @staticmethod
    def render(b: dict, what: str) -> str:
        shown = b["lines"][:DIG_MAX_LINES]
        more = b["n"] - len(shown)
        lines = [f"🧯 <b>Сводка волны</b>: {b['head']}", f"Ещё {b['n']} {what} (отдельно не отправлял, чтобы не упереться в лимит Telegram):"]
        lines += ["• " + s for s in shown]
        if more > 0:
            lines.append(f"…и ещё {more}.")
        lines.append("<i>Каждое дело можно открыть и отменить в панели: «🧬 5.0» → «дела».</i>")
        return "\n".join(lines)

    def notice_ok(self, chat: int, now: float) -> bool:
        dq = self.notes[chat]
        while dq and now - dq[0] > NOTICE_WINDOW:
            dq.popleft()
        if len(dq) < NOTICE_DIRECT:
            dq.append(now)
            return True
        m = self.muted.setdefault(chat, [0, now])
        m[0] += 1
        return False

    def notice_summaries(self, now: float) -> list:
        out = []
        for chat, (n, t0) in list(self.muted.items()):
            if now - t0 >= NOTICE_WINDOW:
                self.muted.pop(chat, None)
                if n >= 2 and now - self.last_sum.get(chat, 0) >= 60:
                    self.last_sum[chat] = now
                    out.append((chat, n))
        if len(self.last_sum) > 500:
            self.last_sum = {k: v for k, v in self.last_sum.items() if now - v < 600}
        return out


_DIG_BYPASS = contextvars.ContextVar("g6_dig_bypass", default=False)
CAPQ_MAX_WAIT, CAPQ_ROOM_MIN, CAPQ_TRIES = 120.0, 4, 3
RESCUE_MAX, RESCUE_TTL, RESCUE_UNDO_MAX = 12, 3 * 86400, 60
OVERKILL_N, OVERKILL_WIN, OVERKILL_GAP = 2, 600.0, 1800.0
FLOCK_N, FLOCK_WIN = 3, 600.0
SWEEP_PARENTS, SWEEP_WIN = 3, 1800.0
RENAME_WIN = 3600.0
HAND_WIN = 1200.0
CHORUS_SIGNAL, HAND_FULL, HAND_PART = 2.5, 1.5, 0.8
TRACE_ADD_STRONG = {"flock": 2.2, "sweep": 2.0}
TRACE_ADD_SOFT = {"renamed": 0.9}
TRACE_ADD_LABEL = {"flock": "стая новых аккаунтов", "sweep": "один контакт под разными сообщениями",
                   "renamed": "сменил имя перед ссылкой"}


# ═══════════════════════════════ движок: Следопыт и Кукольный театр ═══════════════════════════════
class EngineMix6:
    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        self.__dict__["_g6e"] = {"flock": {}, "sweep": {}, "name": {}, "hits": defaultdict(int)}

    def _g6e(self) -> dict:
        return self.__dict__["_g6e"]

    # ---- Следопыт ----
    def _trace_find(self, msg, chat, rec, tier: str, a, now: float, prev_seen: float) -> dict:
        ev = super()._trace_find(msg, chat, rec, tier, a, now, prev_seen)
        if ON.get("all") and feat("trace") and BR.ok("trace6"):
            try:
                self._g6_trace_more(msg, chat, rec, tier, a, now, ev)
                BR.good("trace6")
            except Exception:                                        # noqa: BLE001
                BR.bad("trace6")
        return ev

    def _g6_young(self, rec, tier: str, now: float) -> bool:
        if rec is None:
            return True
        if getattr(rec, "vouched", False):
            return False
        return tier == "new" or now - (rec.joined or rec.first_seen or now) < G.PUPPET_YOUNG_AGE

    def _g6_trace_more(self, msg, chat, rec, tier: str, a, now: float, ev: dict) -> None:
        x = self._g6e()
        cid, uid = msg.chat_id, msg.user_id
        key = (cid, uid)
        if msg.edited or uid <= 0:
            return
        # «Смена облика»: имя/юзернейм поменялись недавно, и вот сообщение с контактом
        sig = f"{(msg.name or '').strip()}|{(msg.username or '').strip().lower()}"
        old = x["name"].get(key)
        if old is None:
            x["name"][key] = [sig, now, 0.0, now]                    # подпись, с какого момента, когда сменилась, когда видели
        else:
            if old[0] != sig:
                old[0], old[2] = sig, now
                old[1] = now
            old[3] = now
            if a.has_contact and old[2] and now - old[2] <= RENAME_WIN:
                ev["renamed"] = (TRACE_ADD_SOFT["renamed"], "имя или юзернейм сменились меньше часа назад, и сразу контакт")
        # «Стая»: несколько новых аккаунтов отвечают контактами под одним сообщением
        young = self._g6_young(rec, tier, now)
        if msg.reply_to and a.has_contact and young:
            d = x["flock"].setdefault((cid, msg.reply_to), {})
            d[uid] = now
            for u in [u for u, t in d.items() if now - t > FLOCK_WIN]:
                d.pop(u, None)
            if len(d) >= FLOCK_N:
                ev["flock"] = (TRACE_ADD_STRONG["flock"], f"{len(d)} новых аккаунта ответили контактами под одним сообщением")
        # «Обход вопросов»: один контакт под разными сообщениями
        if msg.reply_to and a.contacts and tier != "veteran":
            dq = x["sweep"].setdefault(key, deque(maxlen=8))
            mine = set(a.contacts)
            parents = {p for t, toks, p in dq if now - t <= SWEEP_WIN and mine & toks and p != msg.reply_to}
            dq.append((now, frozenset(a.contacts), msg.reply_to))
            if len(parents) + 1 >= SWEEP_PARENTS:
                ev["sweep"] = (TRACE_ADD_STRONG["sweep"], f"один и тот же контакт уже под {len(parents) + 1} разными сообщениями за полчаса")

    def _trace_prune(self, now: float) -> None:
        super()._trace_prune(now)
        x = self._g6e()
        for k in [k for k, d in x["flock"].items() if not d or now - max(d.values()) > FLOCK_WIN]:
            x["flock"].pop(k, None)
        for k in [k for k, dq in x["sweep"].items() if not dq or now - dq[-1][0] > SWEEP_WIN]:
            x["sweep"].pop(k, None)
        for k in [k for k, v in x["name"].items() if now - v[3] > 86400]:
            x["name"].pop(k, None)
        if len(x["name"]) > 6000:
            for k in sorted(x["name"], key=lambda k: x["name"][k][3])[:1500]:
                x["name"].pop(k, None)

    # ---- Кукольный театр ----
    def _puppet_eval(self, msg, chat, a, now: float) -> None:
        super()._puppet_eval(msg, chat, a, now)
        if ON.get("all") and feat("puppet") and BR.ok("puppet6"):
            try:
                self._g6_puppet_more(msg, chat, a, now)
                BR.good("puppet6")
            except Exception:                                        # noqa: BLE001
                BR.bad("puppet6")

    def _g6_cohort(self, chat, uids, now: float) -> bool:
        times = []
        for u in dict.fromkeys(uids):
            r = chat.users.get(u)
            t = (r.joined or r.first_seen) if r is not None else 0.0
            if t:
                times.append(t)
        times.sort()
        return len(times) >= 2 and any(b - a_ <= HAND_WIN for a_, b in zip(times, times[1:]))

    def _g6_chorus(self, chat, cur_id: int, cur, now: float):
        cid = chat.chat_id
        beats = self.beats.get(cid, {})
        nodes = {i: beats[i] for i in self.scenes.get(cid, {}).get(cur.root, ()) if i in beats and i != cur_id}
        nodes[cur_id] = cur
        young: dict = {}

        def is_young(u: int) -> bool:
            if u not in young:
                young[u] = self._young(chat, u, now)
            return young[u]

        for p in sorted((i for i, b in nodes.items() if b.roles & G.ROLE_PITCH and i < cur_id), reverse=True):
            pb = nodes[p]
            if not is_young(pb.uid) or pb.uid == cur.uid or not self._under(beats, cur_id, cur, cur_id, p):
                continue
            confirms = {c: b for c, b in nodes.items()
                        if c > p and b.roles & G.ROLE_CONFIRM and b.uid != pb.uid and is_young(b.uid)
                        and (c == cur_id or self._under(beats, cur_id, cur, c, p))}
            uids = {b.uid for b in confirms.values()}
            if cur_id in confirms and len(uids) >= 2:
                return {"kind": "chorus", "root": cur.root, "ask": 0, "pitch": p, "confirm": cur_id, "ask_uid": 0,
                        "pitch_uid": pb.uid, "confirm_uid": cur.uid, "confirm_uids": sorted(uids)}
        return None

    def _g6_puppet_more(self, msg, chat, a, now: float) -> None:
        sc, cur = a.scene, a.beat
        x = self._g6e()
        if sc:
            uids = [sc.get(k) for k in ("ask_uid", "pitch_uid", "confirm_uid") if sc.get(k)]
            if self._g6_cohort(chat, uids, now):
                sc["hand"] = True
                w = HAND_FULL if sc.get("kind") == "full" else HAND_PART
                a.signals.append(("puppet_hand", w, "участники сцены вошли в чат почти одновременно"))
                x["hits"]["hand"] += 1
            return
        if cur is None or not cur.parent or not cur.roles & G.ROLE_CONFIRM:
            return
        found = self._g6_chorus(chat, msg.msg_id, cur, now)
        if not found:
            return
        a.scene = found
        a.signals.append(("puppet_chorus", CHORUS_SIGNAL,
                          "хор: питч новичка и «работает!» от нескольких других новичков, хотя вопроса не было"))
        x["hits"]["chorus"] += 1
        if self._g6_cohort(chat, [found["pitch_uid"]] + list(found["confirm_uids"]), now):
            found["hand"] = True
            a.signals.append(("puppet_hand", HAND_FULL, "участники сцены вошли в чат почти одновременно"))
            x["hits"]["hand"] += 1


# ═══════════════════════════════ охрана ═══════════════════════════════
def esc(s, n: int = 40) -> str:
    return G.esc(s, n)


class GuardMix6:
    """Подмешивается ПЕРЕД guard5 и GuardX: всё, чего здесь нет, работает как раньше."""

    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        self.__dict__["_g6x"] = {"undo": defaultdict(deque), "undo_ask": {}, "net_busy": 0, "net_skip": 0, "capq_task": None,
                                 "capq_fail": 0, "last_stat": 0.0}
        self.__dict__["_g6_gov"] = Governor()
        self.__dict__["_g6_dig"] = Digest(clock=self.now)

    @property
    def g6x(self) -> dict:
        return self.__dict__["_g6x"]

    @property
    def g6_gov(self) -> Governor:
        return self.__dict__["_g6_gov"]

    @property
    def g6_dig(self) -> Digest:
        return self.__dict__["_g6_dig"]

    def _g6_root(self) -> dict:
        r = self.store.meta.setdefault("g6", {})
        r.setdefault("capq", [])
        r.setdefault("rescue", {})
        r.setdefault("seq", 0)
        return r

    def _g6_have_cases(self) -> bool:
        return hasattr(self, "g5b") and callable(getattr(self, "g5b", None))

    # ═══════ «Дозатор» ═══════
    async def call(self, method: str, *a, **kw):
        if not (ON.get("all") and feat("gov") and BR.ok("gov")):
            return await super().call(method, *a, **kw)
        try:
            gov = self.g6_gov
            prio, chat = gov.classify(method, a, kw)
            wait = gov.admit(prio, method, chat)
        except Exception:                                            # noqa: BLE001
            BR.bad("gov")
            return await super().call(method, *a, **kw)
        if wait is None:
            return None
        if wait > 0:
            await asyncio.sleep(wait)
        for attempt in range(3):
            try:
                r = await getattr(self.bot, method)(*a, **kw)
                BR.good("gov")
                return r
            except G.TelegramRetryAfter as e:
                ra = float(getattr(e, "retry_after", 1))
                gov.flood(chat, ra)
                log.info("429 на %s: чат %s остывает %.0f с (один раз для всех запросов)", method, chat, ra)
                if prio == "cosm":
                    return None
                await asyncio.sleep(min(ra, 30.0) + 0.2)
            except (G.TelegramBadRequest, G.TelegramForbiddenError) as e:
                G.log.debug("%s: %s", method, e)
                return None
            except (G.TelegramNetworkError, G.TelegramServerError) as e:
                G.log.warning("%s: сеть/сервер (%s), попытка %d", method, e, attempt + 1)
                await asyncio.sleep(0.6 * (attempt + 1))
            except G.TelegramAPIError as e:
                G.log.warning("%s: %s", method, e)
                return None
        return None

    # ═══════ «Сводка волны» ═══════
    async def alert(self, chat_id: int, text: str, markup=None) -> int:
        if _DIG_BYPASS.get() or not (ON.get("all") and feat("digest") and BR.ok("digest")):
            return await super().alert(chat_id, text, markup)
        try:
            dl = digest_line("alert", text)
            if dl is not None and not self.g6_dig.direct_ok(("alert", chat_id), self.now()):
                self.g6_dig.hold(("alert", chat_id), dl[0], dl[1], self.now())
                return 0
        except Exception:                                            # noqa: BLE001
            BR.bad("digest")
        return await super().alert(chat_id, text, markup)

    async def plus_log(self, chat_id: int, text: str) -> None:
        if _DIG_BYPASS.get() or not (ON.get("all") and feat("digest") and BR.ok("digest")):
            return await super().plus_log(chat_id, text)
        try:
            dl = digest_line("log", text)
            if dl is not None and not self.g6_dig.direct_ok(("log", chat_id), self.now()):
                self.g6_dig.hold(("log", chat_id), dl[0], dl[1], self.now())
                return None
        except Exception:                                            # noqa: BLE001
            BR.bad("digest")
        return await super().plus_log(chat_id, text)

    async def notice(self, chat_id: int, key: str, ttl: float = 30, cooldown: float = 0, cd_key=None, thread=None, **kw):
        if key in CHATTY_NOTICES and ON.get("all") and feat("digest") and BR.ok("digest"):
            try:
                if not self.g6_dig.notice_ok(chat_id, self.now()):
                    return None
            except Exception:                                        # noqa: BLE001
                BR.bad("digest")
        return await super().notice(chat_id, key, ttl=ttl, cooldown=cooldown, cd_key=cd_key, thread=thread, **kw)

    async def _g6_digest_flush(self, now: float) -> None:
        dig = self.g6_dig
        for key, b in dig.due(now):
            kind, cid = key
            tok = _DIG_BYPASS.set(True)
            try:
                if kind == "alert":
                    await self.alert(cid, dig.render(b, "наказаний"))
                else:
                    await self.plus_log(cid, dig.render(b, "записей журнала"))
            finally:
                _DIG_BYPASS.reset(tok)
        for cid, n in dig.notice_summaries(now):
            st = self.store.chats.get(cid)
            if st is None or st.cfg.quiet or not self.chat_ok(cid):
                continue
            sent = await self.call("send_message", cid, f"🧹 Тихо убрал ещё {n} нарушителей за последние полминуты.",
                                   disable_notification=True)
            if sent is not None:
                self.later(60, self.call, "delete_message", cid, sent.message_id)

    # ═══════ «Очередь капч» ═══════
    async def start_captcha(self, chat, user, join_msg_id=None, plan: dict | None = None) -> None:
        if not (ON.get("all") and feat("capq") and BR.ok("capq")):
            return await super().start_captcha(chat, user, join_msg_id, plan)
        try:
            q = self._g6_root()["capq"]
            pressed = bool(q) or self.g6_gov.group_room(chat.id) < CAPQ_ROOM_MIN or self.g6_gov.cooling(chat.id) > 0
        except Exception:                                            # noqa: BLE001
            BR.bad("capq")
            pressed = False
        if not pressed:
            return await super().start_captcha(chat, user, join_msg_id, plan)
        if await self.restrict(chat.id, user.id, None) is None:
            return
        q.append({"c": chat.id, "u": user.id, "n": G.user_name(user)[:40], "j": join_msg_id or 0,
                  "lv": (plan or {}).get("level") or "", "t": round(self.now(), 1), "k": 0, "nx": 0})
        self.store.dirty = True
        log.info("chat=%s: капча для %s ждёт очереди (в очереди %d)", chat.id, user.id, len(q))
        self._g6_capq_kick()

    def _g6_capq_kick(self) -> None:
        t = self.g6x.get("capq_task")
        if t is None or t.done():
            t = asyncio.get_running_loop().create_task(self._g6_capq_run())
            self.g6x["capq_task"] = t
            self._tasks.add(t)
            t.add_done_callback(self._tasks.discard)

    async def _g6_capq_pass(self) -> bool:
        """Один проход по очереди: кому пора — показываем капчу; кто ждёт дольше двух минут — убираем на 90 секунд."""
        q = self._g6_root()["capq"]
        progressed = False
        for it in list(q):
            now = self.now()
            if now - it["t"] > CAPQ_MAX_WAIT:
                if it in q:
                    q.remove(it)
                await self._g6_cap_giveup(it, "не дождался очереди")
                progressed = True
                continue
            if it["nx"] > now or self.g6_gov.group_room(it["c"]) < 2 or self.g6_gov.cooling(it["c"]) > 0:
                continue
            if it in q:
                q.remove(it)
            await self._g6_cap_deliver(it)
            progressed = True
        return progressed

    async def _g6_capq_run(self) -> None:
        try:
            while self._g6_root()["capq"]:
                progressed = await self._g6_capq_pass()
                await asyncio.sleep(0.4 if progressed else 1.0)
        except asyncio.CancelledError:
            raise
        except Exception:                                            # noqa: BLE001
            BR.bad("capq")
        finally:
            self.g6x["capq_task"] = None

    async def _g6_cap_deliver(self, it: dict) -> None:
        from aiogram.types import InlineKeyboardMarkup
        cid, uid = it["c"], it["u"]
        st = self.store.chats.get(cid)
        if st is None or not st.cfg.enabled or f"{cid}:{uid}" in self.store.captchas:
            return
        rec = st.users.get(uid)
        if rec is not None and (rec.banned or rec.verified):
            return
        cfg = st.cfg
        level = it.get("lv") or None
        cap = G.make_captcha(self.eng.rng, level)
        tmo = min(cfg.captcha_timeout, 45) if level == "hard" else cfg.captcha_timeout
        kb = InlineKeyboardMarkup(inline_keyboard=self._captcha_rows(cid, uid, cap))
        text = self.voice.say("captcha_prompt", name=G.mention(uid, it.get("n", "")), q=esc(cap["q"], 80), sec=tmo)
        sent = await self.call("send_message", cid, text, reply_markup=kb, disable_notification=True)
        if sent is None:
            it["k"] = it.get("k", 0) + 1
            if it["k"] >= CAPQ_TRIES:
                await self._g6_cap_giveup(it, "Telegram не принял капчу")
                return
            it["nx"] = self.now() + 4.0 * it["k"]
            self._g6_root()["capq"].append(it)
            return
        now = self.now()
        self.store.captchas[f"{cid}:{uid}"] = {
            "chat": cid, "user": uid, "name": it.get("n", "")[:40], "answer": cap["answer"], "tries": 0,
            "deadline": now + tmo, "msg_id": sent.message_id, "join_msg": it.get("j", 0),
            "level": level, "t0": now, "max_tries": 1 if level == "hard" else 2}
        self.store.dirty = True

    async def _g6_cap_giveup(self, it: dict, why: str) -> None:
        """Капчу так и не удалось показать. Снимать ограничение НЕЛЬЗЯ (так пролез бы скамер): убираем на 90 секунд,
        человек может зайти снова сразу, а скамеру это лишний круг."""
        cid, uid = it["c"], it["u"]
        st = self.store.chats.get(cid)
        await self.kick(cid, uid, seconds=90)
        if it.get("j"):
            self.deleter.add(cid, [it["j"]])
        self.journal("capfail", cid, st.title if st else "", uid, it.get("n", ""), f"капча не показана ({why}): убран на 2 мин")
        self.g6x["capq_fail"] = self.g6x.get("capq_fail", 0) + 1

    async def on_leave(self, chat, uid: int) -> None:
        try:
            q = self._g6_root()["capq"]
            q[:] = [it for it in q if not (it["c"] == chat.id and it["u"] == uid)]
        except Exception:                                            # noqa: BLE001
            pass
        return await super().on_leave(chat, uid)

    # ═══════ «Тихая сеть» ═══════
    async def _g5_preflight(self, m) -> None:
        base = getattr(super(), "_g5_preflight", None)
        if base is None:
            return None
        if not (ON.get("all") and feat("softnet") and BR.ok("softnet")):
            return await base(m)
        hot = busy = False
        try:
            cid, now = m.chat.id, self.now()
            st = self.store.chats.get(cid)
            hot = bool(st is not None and st.cfg.fort_on) or self.eng.raid_active(cid, now) or self.eng.strict_active(cid, now)
            busy = self.g6x["net_busy"] >= 3
        except Exception:                                            # noqa: BLE001
            BR.bad("softnet")
        if hot or busy:
            self.g6x["net_skip"] += 1
            return None
        self.g6x["net_busy"] += 1
        try:
            return await base(m)
        finally:
            self.g6x["net_busy"] -= 1

    # ═══════ «Страховка» ═══════
    async def fort_off_event(self, ev: dict) -> None:
        await super().fort_off_event(ev)
        if ON.get("all") and feat("rescue") and BR.ok("rescue") and self._g6_have_cases():
            await BR.arun("rescue", self._g6_rescue, ev)

    def _g6_weak_cases(self, cid: int, t0: float, t1: float) -> list:
        bk = self.g5b()
        out = []
        for k, c in bk.cases.c.items():
            if (c["c"] == cid and t0 - 2 <= c["t"] <= t1 + 5 and c["st"] == "open" and c["u"] > 0
                    and str(c["a"]).startswith(("бан", "мут")) and c["s"] < G.STRONG_SCAM):
                out.append((int(k), c))
        out.sort(key=lambda kv: kv[1]["t"])
        return out

    def _g6_stash(self, ids: list, now: float) -> str:
        r = self._g6_root()
        r["seq"] += 1
        tok = format(r["seq"], "x")
        r["rescue"][tok] = {"ids": [int(i) for i in ids][:RESCUE_UNDO_MAX], "t": round(now)}
        for k in [k for k, v in r["rescue"].items() if now - v["t"] > RESCUE_TTL]:
            r["rescue"].pop(k, None)
        return tok

    @staticmethod
    def _g6_rescue_kb(tok: str, n: int):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        return InlineKeyboardMarkup(inline_keyboard=[[Btn(text=f"↩️ Вернуть ({n})", callback_data=f"g6:rs:{tok}"),
                                                       Btn(text="✅ Всё верно", callback_data=f"g6:rk:{tok}")]])

    async def _g6_rescue(self, ev: dict) -> None:
        cid, rep = ev["chat"], ev["report"]
        st = self.store.chats.get(cid)
        if st is None:
            return
        weak = self._g6_weak_cases(cid, float(rep.get("started") or 0), float(rep.get("ended") or self.now()))
        if not weak:
            return
        now = self.now()
        tok = self._g6_stash([k for k, _ in weak], now)
        lines = [f"🛟 <b>{esc(st.title, 60)}</b>", f"Пока работала полная защита, без сильных улик наказано: {len(weak)}. "
                                                     "Взгляните — вдруг кто-то зря."]
        for _k, c in weak[:RESCUE_MAX]:
            lines.append(f"• {G.mention(c['u'], c['n'])} — {esc(c['a'], 20)}, оценка {c['s']:g}: {esc(c['w'], 90)}")
        if len(weak) > RESCUE_MAX:
            lines.append(f"…и ещё {len(weak) - RESCUE_MAX}.")
        lines.append("<i>«Вернуть» снимает наказание и учит бота на ошибке; в чат ничего не пишет.</i>")
        await self._g5_tell_owners("\n".join(lines), self._g6_rescue_kb(tok, min(len(weak), RESCUE_UNDO_MAX)))

    async def _g6_undo_quiet(self, case_id: int, by: int) -> bool:
        bk = self.g5b()
        case = bk.cases.get(case_id)
        if case is None or case["st"] != "open":
            return False
        cid, uid, now = case["c"], case["u"], self.now()
        if str(case["a"]).startswith("бан"):
            await self.call("unban_chat_member", cid, uid, only_if_banned=True)
        await self.unrestrict(cid, uid)
        self.eng.forgive(cid, uid)
        try:
            if case.get("m"):
                self.eng.lp_teach(cid, case["m"], "h", by, "g6rescue", now)
        except Exception:                                            # noqa: BLE001
            log.debug("lp_teach после возврата не удался", exc_info=True)
        try:
            bk.farm.forget(uid)
        except AttributeError:
            pass
        bk.cases.set_state(case_id, "undone", by, now)
        st = self.store.chats.get(cid)
        self.journal("undo", cid, st.title if st else "", by, case["n"], f"отменено дело №{case_id} (страховка)")
        self.store.dirty = True
        return True

    # ═══════ «Перебор?» ═══════
    async def g5_undo(self, case_id: int, by: int) -> tuple:
        ok, note = await super().g5_undo(case_id, by)
        if ok and ON.get("all") and feat("overkill") and BR.ok("overkill"):
            await BR.arun("overkill", self._g6_overkill_note, case_id, by)
        return ok, note

    async def _g6_overkill_note(self, case_id: int, by: int) -> None:
        case = self.g5b().cases.get(case_id)
        if case is None:
            return
        cid, now = case["c"], self.now()
        st = self.store.chats.get(cid)
        if st is None or not st.cfg.fort_on:
            return
        dq = self.g6x["undo"][cid]
        dq.append(now)
        while dq and now - dq[0] > OVERKILL_WIN:
            dq.popleft()
        if len(dq) < OVERKILL_N or now - self.g6x["undo_ask"].get(cid, 0.0) < OVERKILL_GAP:
            return
        self.g6x["undo_ask"][cid] = now
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        kb = InlineKeyboardMarkup(inline_keyboard=[[Btn(text="🛡 Снять полную защиту", callback_data=f"g6:fo:{cid}"),
                                                     Btn(text="Оставить", callback_data=f"g6:fx:{cid}")]])
        await self._g5_tell_owners(
            f"🤔 <b>{esc(st.title, 60)}</b>\nПока включена полная защита, отменено наказаний: {len(dq)} за "
            f"{G.human_dur(OVERKILL_WIN)}. Возможно, режим слишком строгий для этой волны. Сам я ничего не отключаю — решать вам.", kb)

    # ═══════ «Дела для кукол» ═══════
    async def puppet_others(self, m, chat_id: int, others: list, rights: dict) -> None:
        await super().puppet_others(m, chat_id, others, rights)
        if not (ON.get("all") and feat("puppet") and BR.ok("puppet_cases") and self._g6_have_cases()):
            return
        await BR.arun("puppet_cases", self._g6_puppet_cases, m, chat_id, others)

    async def _g6_puppet_cases(self, m, chat_id: int, others: list) -> None:
        admins = await self.admins(chat_id)
        now, ids = self.now(), []
        bk = self.g5b()
        for o in others:
            uid = o["uid"]
            if uid in admins or self.is_trusted(uid):
                continue
            act = "бан" if o.get("ban") else f"мут {G.human_dur(o.get('mute_s', 0))}"
            role = "питч" if o.get("role") == "pitch" else "подтверждение"
            ids.append(bk.cases.add(chat_id, uid, "", "puppet", f"постановочный диалог ({role})", G.PUPPET_SIGNAL, "new", act, 0, "", 0, now))
        if not ids:
            return
        self.store.dirty = True
        tok = self._g6_stash(ids, now)
        text = (f"🎭 <b>{esc(m.chat.title, 60)}</b>\nКукольный театр: наказано аккаунтов — {len(ids)}. "
                "Если среди них есть настоящие люди, их можно вернуть одной кнопкой.")
        await self._g5_tell_owners(text, self._g6_rescue_kb(tok, len(ids)))

    # ═══════ кнопки g6: ═══════
    async def on_callback(self, cb) -> None:
        data = getattr(cb, "data", "") or ""
        if not (ON.get("all") and data.startswith("g6:")):
            return await super().on_callback(cb)
        try:
            await self._g6_button(cb, data.split(":"))
        except asyncio.CancelledError:
            raise
        except Exception:                                            # noqa: BLE001
            log.exception("кнопка 6.0 %r упала", data)
            await self._g6_ans(cb)

    @staticmethod
    async def _g6_ans(cb, text: str | None = None, alert: bool = False) -> None:
        try:
            await cb.answer(text, show_alert=alert) if text else await cb.answer()
        except asyncio.CancelledError:
            raise
        except Exception:                                            # noqa: BLE001
            pass

    async def _g6_mark(self, cb, suffix: str) -> None:
        msg = getattr(cb, "message", None)
        if msg is None:
            return
        base = getattr(msg, "html_text", None) or getattr(msg, "text", "") or ""
        await self.call("edit_message_text", (base + "\n\n" + suffix)[:4000], chat_id=msg.chat.id, message_id=msg.message_id)

    async def _g6_button(self, cb, p: list) -> None:
        uid = cb.from_user.id
        act = p[1] if len(p) > 1 else ""
        if uid not in self.owners:
            return await self._g6_ans(cb, "Только для владельца бота.", True)
        if act in ("rs", "rk"):
            tok = p[2] if len(p) > 2 else ""
            r = self._g6_root()["rescue"]
            row = r.get(tok)
            if row is None:
                return await self._g6_ans(cb, "Список уже устарел.", True)
            if act == "rk":
                r.pop(tok, None)
                self.store.dirty = True
                await self._g6_mark(cb, "✅ Отмечено: всё верно.")
                return await self._g6_ans(cb, "Записал.")
            r.pop(tok, None)
            self.store.dirty = True
            await self._g6_ans(cb, "Возвращаю…")
            n = 0
            for cid_ in row["ids"][:RESCUE_UNDO_MAX]:
                if await self._g6_undo_quiet(cid_, uid):
                    n += 1
            await self._g6_mark(cb, f"↩️ <b>Возвращено: {n}</b> из {len(row['ids'])}.")
            return None
        if act in ("fo", "fx"):
            try:
                cid = int(p[2])
            except (IndexError, ValueError):
                return await self._g6_ans(cb)
            if act == "fx":
                await self._g6_mark(cb, "Оставил как есть.")
                return await self._g6_ans(cb, "Оставил.")
            rep = self.eng.fort_disable(cid, self.now(), how="manual", by=uid)
            if self.eng.events:
                await self.handle_events()
            await self._g6_mark(cb, "✅ Полная защита выключена, настройки чата вернулись." if rep else "Полная защита уже выключена.")
            return await self._g6_ans(cb, "Готово.")
        return await self._g6_ans(cb)

    # ═══════ фон ═══════
    async def tick(self, now: float | None = None) -> None:
        await super().tick(now)
        if ON.get("all"):
            await BR.arun("g6tick", self._g6_tick, self.now() if now is None else now)

    async def _g6_tick(self, now: float) -> None:
        if feat("digest") and BR.ok("digest"):
            await BR.arun("digest", self._g6_digest_flush, now)
        if feat("capq") and BR.ok("capq"):
            q = self._g6_root()["capq"]
            if q:
                self._g6_capq_kick()                                 # после перезапуска очередь продолжает работу
        if now - self.g6x["last_stat"] >= 600:
            self.g6x["last_stat"] = now
            s = self.g6_gov.stat
            if s["wait"] or s["drop"] or s["flood"] or self.g6x["net_skip"] or self.g6x["capq_fail"]:
                log.info("6.0: запросов без задержки %d, с задержкой %d, пропущено «косметики» %d, ответов 429 %d; "
                         "сеть пропущена %d раз; капч не показано %d", s["pass"], s["wait"], s["drop"], s["flood"],
                         self.g6x["net_skip"], self.g6x["capq_fail"])


# ═══════════════════════════════ сборка ═══════════════════════════════
def build(engine_cls, guard_cls):
    """→ (EngineV6, GuardV6). При GUARD6=0 возвращает классы как есть: бот работает ровно как 5.0."""
    reload_env()
    g = _GLOBALS.get("g")
    if not ON.get("all") or g is None:
        return engine_cls, guard_cls
    try:
        if feat("trace"):
            g["TRACE_STRONG"].update(TRACE_ADD_STRONG)
            g["TRACE_SOFT"].update(TRACE_ADD_SOFT)
            g["TRACE_LABEL"].update(TRACE_ADD_LABEL)
    except Exception:                                                # noqa: BLE001
        log.exception("6.0: не удалось дополнить таблицы Следопыта — запускаю классы 5.0")
        return engine_cls, guard_cls
    E = type("EngineV6", (EngineMix6, engine_cls), {"__doc__": "Engine + guard6"})
    Gd = type("GuardV6", (GuardMix6, guard_cls), {"__doc__": "Guard + guard6"})
    log.info("guard6 %s подключён: %s", V6_VERSION, ", ".join(k for k in FEATS if feat(k)) or "без частей")
    return E, Gd
