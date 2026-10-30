#!/usr/bin/env python3
# guard5 — расширение 5.0 для guard.py. Кладётся В ОДНУ ПАПКУ с guard.py (корень репозитория); guard.py сам его подхватывает.
#
# Что это. guard.py 4.3 уже умеет много; 5.0 не плодит команды, а усиливает то, что есть:
#   ▸ «Дела»            каждое наказание — запись с уликами и причиной; кнопки «↩️ Отменить» / «✅ Верно» в тревоге владельцу.
#                       Отмена — не просто разбан: бот ещё и учится на ошибке (память о спаме, самообучение, поправка доверия).
#   ▸ «Апелляция»       случайно удалили нормальное сообщение? Автор жмёт «Это не спам» — владелец получает карточку с уликами.
#   ▸ «Второй взгляд»   проверка ссылок по сети в два этапа: возраст домена (RDAP), раскрытие сокращалок, что на самом деле
#                       написано в канале/чате по t.me-ссылке. Нашли — удаляем даже уже опубликованное сообщение.
#   ▸ «Знакомые ссылки» домены, которыми давно делятся надёжные участники чата, больше не штрафуются (меньше ложных срабатываний).
#   ▸ «Честные жалобы»  у жалобщика есть репутация; бот сразу показывает свою оценку жалобы; подтверждённые жалобы учат бота.
#   ▸ «Честные опросы»  голоса новичков не перевешивают, но видны отдельно.
#   ▸ Команды без новых названий, но сильно умнее: /warn /mute /ban /purge (длительность «1ч30м», причина, умная зачистка),
#     /remind («завтра в 10», «каждый день в 9:00», «+15 мин» одной кнопкой), /repeat (дни недели, окно времени, «до даты», «не
#     кричит в пустоту»), /me и /explain (почему так решили), /stats и итоги дня (точность решений бота).
#   ▸ Заявки на вход: анализ «био» заявителя, необязательная проверка в личке; чистка реакций спамера новым методом Bot API.
#   ▸ Свежие приметы мошенничества 2026 (Stars-подарки, мини-приложения/airdrop, «поддержка», ИИ-трейдеры, фейк-«верификация»).
#
# Как включается. Ничего настраивать не нужно. GUARD5=0 выключает всё сразу (бот работает как 4.3); отдельные части —
# GUARD5_CASES / _APPEAL / _LOOK / _NET / _KNOWN / _REPORTS / _POLLS / _CMDS / _REPEAT / _JOINREQ / _RULES = 0.
# Любой сбой внутри расширения глушится и не доходит до модерации; пять сбоев подряд отключают узел на 30 минут.
from __future__ import annotations

import asyncio
import calendar
import contextvars
import html
import http.client
import ipaddress
import json
import logging
import os
import re
import socket
import ssl
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import OrderedDict, deque
from typing import Any

V5_VERSION = "5.0"
log = logging.getLogger("guard.v5")
log_look = logging.getLogger("guard.v5.look")


# ═══════════════════════════════ связь с guard.py ═══════════════════════════════
class _NS:
    """Имена из guard.py (esc, mention, Verdict…): заполняются один раз функцией bind(globals())."""

    def __getattr__(self, name: str):
        raise AttributeError("guard5: имя %r из guard.py не передано (bind не вызывался?)" % name)


G = _NS()


_GLOBALS: dict = {}


def bind(g: dict) -> None:
    """Вызывается из guard.py один раз: передаёт имена guard.py (и сам словарь globals — чтобы build() мог подменять константы)."""
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


FEATS = ("cases", "appeal", "look", "net", "known", "reports", "polls", "cmds", "repeat", "joinreq", "rules")
ON: dict = {}


def reload_env() -> None:
    ON.clear()
    ON["all"] = _flag("GUARD5", True)
    for k in FEATS:
        ON[k] = ON["all"] and _flag("GUARD5_" + k.upper(), True)


reload_env()


def feat(name: str) -> bool:
    return bool(ON.get(name))


# ═══════════════════════════════ длительности и «когда» ═══════════════════════════════
_DUR_UNITS = {
    "с": 1, "сек": 1, "секунд": 1, "секунду": 1, "секунды": 1, "s": 1, "sec": 1, "secs": 1,
    "м": 60, "мин": 60, "минут": 60, "минуту": 60, "минуты": 60, "m": 60, "min": 60, "mins": 60,
    "ч": 3600, "час": 3600, "часа": 3600, "часов": 3600, "h": 3600, "hr": 3600, "hrs": 3600, "hour": 3600, "hours": 3600,
    "д": 86400, "дн": 86400, "день": 86400, "дня": 86400, "дней": 86400, "d": 86400, "day": 86400, "days": 86400,
    "н": 604800, "нед": 604800, "неделя": 604800, "неделю": 604800, "недели": 604800, "недель": 604800,
    "w": 604800, "wk": 604800, "week": 604800, "weeks": 604800,
    "мес": 2592000, "месяц": 2592000, "месяца": 2592000, "месяцев": 2592000, "mo": 2592000, "month": 2592000, "months": 2592000,
}
_DUR_PART = re.compile(r"(\d{1,6})\s*([a-zа-я]{0,8})")
DUR_MAX = 400 * 86400


def parse_duration(tok: str, bare: str = "м") -> int | None:
    """«30», «30м», «2ч», «1д», «1ч30м», «1h30m», «2нед», «1мес» → секунды. Голое число = минуты (как в 4.3). Не похоже → None."""
    t = (tok or "").strip().lower().replace("ё", "е")
    if not t or len(t) > 24:
        return None
    parts = _DUR_PART.findall(t)
    if not parts or _DUR_PART.sub("", t).strip():
        return None
    if len(parts) > 1 and any(not u for _, u in parts):
        return None
    total = 0
    for n, u in parts:
        if not u:
            if len(n) > 5:
                return None
            u = bare
        mult = _DUR_UNITS.get(u)
        if mult is None:
            return None
        total += int(n) * mult
    return total if 0 < total <= DUR_MAX else None


def parse_minutes_v5(tok: str):
    """Замена guard.parse_minutes: те же ответы на старые записи («30», «30м», «2ч», «1д»), плюс «1ч30м», «2нед», «1мес»."""
    sec = parse_duration(tok)
    return None if sec is None else max(1, -(-sec // 60))


_WD_FULL = {"пон": 0, "вто": 1, "сре": 2, "чет": 3, "пят": 4, "суб": 5, "вос": 6}
_WD_SHORT = {"пн": 0, "вт": 1, "ср": 2, "чт": 3, "пт": 4, "сб": 5, "вс": 6}
_WD_NAMES = ("пн", "вт", "ср", "чт", "пт", "сб", "вс")
_WD_RX = r"(?:понедельник\w*|вторник\w*|сред[аыуе]\w*|четверг\w*|пятниц\w*|суббот\w*|воскресень\w*|пн|вт|ср|чт|пт|сб|вс)"
_TOD_RX = r"(\d{1,2})(?::(\d{2}))?\s*(утра|дня|вечера|ночи)?"
_DUR_WORD_RX = (r"(?:(\d{1,4})\s*)?(секунд\w*|сек|минут\w*|мин|м|час(?:а|ов)?|ч|дн\w*|день|дня|дней|д|недел\w*|нед|месяц\w*|мес)\b")
_HALF = r"(?:пол\s*часа|полчаса)"


def weekday_of(word: str) -> int | None:
    w = (word or "").lower().replace("ё", "е")
    if w in _WD_SHORT:
        return _WD_SHORT[w]
    return _WD_FULL.get(w[:3]) if len(w) >= 3 else None


def _unit_secs(word: str) -> int | None:
    w = word.lower()
    for key, sec in (("сек", 1), ("мин", 60), ("час", 3600), ("ч", 3600), ("дн", 86400), ("ден", 86400), ("дня", 86400),
                     ("дней", 86400), ("д", 86400), ("нед", 604800), ("мес", 2592000), ("м", 60)):
        if w == key or w.startswith(key):
            return sec
    return None


def _tod(m_h: str, m_m: str | None, tail: str | None) -> tuple[int, int] | None:
    h, mi = int(m_h), int(m_m or 0)
    if tail in ("вечера", "дня") and h < 12:
        h += 12 if (tail == "вечера" or h < 6) else 0
    elif tail == "ночи" and h == 12:
        h = 0
    elif tail == "утра" and h == 12:
        h = 0
    if not (0 <= h <= 23 and 0 <= mi <= 59):
        return None
    return h, mi


def _local_midnight(now: float, tz_h: float) -> float:
    lt = time.gmtime(now + tz_h * 3600)
    return calendar.timegm((lt.tm_year, lt.tm_mon, lt.tm_mday, 0, 0, 0)) - tz_h * 3600


def _at(day_start: float, h: int, mi: int) -> float:
    return day_start + h * 3600 + mi * 60


def parse_when(text: str, now: float, tz_h: float = 3, default_hour: int = 9) -> dict | None:
    """Разбирает начало фразы «когда»: → {'at': unix, 'repeat': секунд или 0, 'rest': остаток текста} либо None.
    Понимает: «30м», «2ч», «1ч30м», «через 2 часа», «через полчаса», «в 18:30», «в 9 вечера», «завтра [в 10]», «послезавтра»,
    «в пятницу [в 12:00]», «25.12 [в 9:00]», «каждый день [в 9:00]», «каждый час», «каждые 2ч», «каждую неделю», «каждый пн [в 10]»."""
    s = (text or "").strip()
    if not s:
        return None
    low = s.lower().replace("ё", "е")
    today0 = _local_midnight(now, tz_h)
    horizon = now + 366 * 86400

    def done(at: float, used: int, repeat: int = 0):
        if at < now + 5 or at > horizon:
            return None
        if repeat and not (60 <= repeat <= 366 * 86400):
            return None
        return {"at": at, "repeat": repeat, "rest": s[used:].strip(" ,;:—-")}

    def tod_after(pos: int):
        m = re.match(r"\s*(?:в|к|at)?\s*" + _TOD_RX, low[pos:])
        if not m:
            return None
        t = _tod(m.group(1), m.group(2), m.group(3))
        if t is None:
            return None
        if not (m.group(2) or m.group(3)) and not re.match(r"\s*(?:в|к|at)\s*\d", low[pos:]):
            return None
        return t, pos + m.end()

    m = re.match(r"кажды[ейе]\s+(день|час|недел\w*|месяц\w*)(?=\s|$)", low) or re.match(r"кажд(?:ую|ое)\s+(недел\w*|месяц\w*)(?=\s|$)", low)
    if m:
        unit = m.group(1)
        if unit == "час":
            return done(now + 3600, m.end(), 3600)
        if unit == "день":
            t = tod_after(m.end())
            h, mi = t[0] if t else (default_hour, 0)
            used = t[1] if t else m.end()
            at = _at(today0, h, mi)
            if at < now + 5:
                at += 86400
            return done(at, used, 86400)
        if unit.startswith("недел"):
            return done(now + 7 * 86400, m.end(), 7 * 86400)
        return done(now + 30 * 86400, m.end(), 30 * 86400)
    m = re.match(r"кажд(?:ый|ую|ое)\s+(" + _WD_RX + r")(?=\s|$)", low)
    if m and weekday_of(m.group(1)) is not None:
        wd = weekday_of(m.group(1))
        t = tod_after(m.end())
        h, mi = t[0] if t else (default_hour, 0)
        used = t[1] if t else m.end()
        lt = time.gmtime(now + tz_h * 3600)
        add = (wd - lt.tm_wday) % 7
        at = _at(today0 + add * 86400, h, mi)
        if at < now + 5:
            at += 7 * 86400
        return done(at, used, 7 * 86400)
    m = re.match(r"кажд(?:ые|ый)\s+" + _DUR_WORD_RX, low)
    if m:
        k = _unit_secs(m.group(2))
        n = int(m.group(1) or 1)
        if k:
            return done(now + n * k, m.end(), n * k)
        return None
    m = re.match(r"(?:всегда\s+)?кажд\w*\s+(\d+)\s*(м|мин|ч|час\w*|д|дн\w*|дней)\b", low)
    if m:
        k = _unit_secs(m.group(2))
        if k:
            return done(now + int(m.group(1)) * k, m.end(), int(m.group(1)) * k)

    m = re.match(r"через\s+" + _HALF + r"(?=\s|$)", low)
    if m:
        return done(now + 1800, m.end())
    m = re.match(r"через\s+" + _DUR_WORD_RX, low)
    if m:
        k = _unit_secs(m.group(2))
        if k:
            return done(now + int(m.group(1) or 1) * k, m.end())
    m = re.match(r"(\d{1,4})\s*" + _DUR_WORD_RX[len(r"(?:(\d{1,4})\s*)?"):], low)
    if m and re.match(r"\d{1,4}\s+\D", low):
        k = _unit_secs(m.group(2))
        if k:
            return done(now + int(m.group(1)) * k, m.end())
    tok = low.split(None, 1)[0] if low else ""
    sec = parse_duration(tok)
    if sec is not None and re.fullmatch(r"\d{1,5}\s*[a-zа-я]{0,8}(?:\d{1,5}\s*[a-zа-я]{1,8})*", tok):
        return done(now + sec, len(tok))

    for word, add in (("послезавтра", 2), ("завтра", 1), ("сегодня", 0)):
        if low.startswith(word) and (len(low) == len(word) or not low[len(word)].isalpha()):
            t = tod_after(len(word))
            h, mi = t[0] if t else (default_hour, 0)
            used = t[1] if t else len(word)
            return done(_at(today0 + add * 86400, h, mi), used)
    m = re.match(r"в\s+" + _TOD_RX + r"(?=\s|$)", low)
    if m:
        t = _tod(m.group(1), m.group(2), m.group(3))
        if t:
            at = _at(today0, *t)
            if at < now + 5:
                at += 86400
            return done(at, m.end())
    m = re.match(r"(?:в\s+|во\s+)?(" + _WD_RX + r")(?=\s|$)", low)
    if m and weekday_of(m.group(1)) is not None and len(m.group(1)) >= 2:
        wd = weekday_of(m.group(1))
        t = tod_after(m.end())
        h, mi = t[0] if t else (default_hour, 0)
        used = t[1] if t else m.end()
        lt = time.gmtime(now + tz_h * 3600)
        add = (wd - lt.tm_wday) % 7
        at = _at(today0 + add * 86400, h, mi)
        if at < now + 5:
            at += 7 * 86400
        return done(at, used)
    m = re.match(r"(\d{1,2})\.(\d{1,2})(?:\.(\d{2,4}))?(?=\s|$)", low)
    if m:
        d, mo = int(m.group(1)), int(m.group(2))
        lt = time.gmtime(now + tz_h * 3600)
        y = int(m.group(3)) if m.group(3) else lt.tm_year
        if y < 100:
            y += 2000
        t = tod_after(m.end())
        h, mi = t[0] if t else (default_hour, 0)
        used = t[1] if t else m.end()
        try:
            at = calendar.timegm((y, mo, d, h, mi, 0)) - tz_h * 3600
            if at < now + 5 and not m.group(3):
                at = calendar.timegm((y + 1, mo, d, h, mi, 0)) - tz_h * 3600
        except (ValueError, OverflowError):
            return None
        return done(at, used)
    return None


def fmt_when(ts: float, tz_h: float = 3) -> str:
    lt = time.gmtime(ts + tz_h * 3600)
    return "%s %02d.%02d %02d:%02d" % (_WD_NAMES[lt.tm_wday], lt.tm_mday, lt.tm_mon, lt.tm_hour, lt.tm_min)


# ═══════════════════════════════ книги: дела, репутация жалобщиков, знакомые домены ═══════════════════════════════
CASE_KEEP, CASE_TTL, CASE_TEXT_TTL, CASE_TEXT_MAX = 1200, 30 * 86400, 3 * 86400, 400


class CaseBook:
    """«Дела»: короткие записи о решениях бота и людей. Лежат в store.meta['g5']['cases'] (JSON/SQLite как у остального состояния).
    Текст сообщения хранится ТОЛЬКО для отмены/апелляции и только 3 суток, потом стирается; сами дела — 30 суток."""

    def __init__(self, root: dict):
        self.root = root
        root.setdefault("seq", 0)
        root.setdefault("c", {})

    @property
    def c(self) -> dict:
        return self.root["c"]

    def add(self, chat: int, uid: int, name: str, kind: str, why: str, score: float, tier: str, act: str, by: int,
            text: str, mid: int, now: float) -> int:
        self.root["seq"] += 1
        cid = self.root["seq"]
        self.c[str(cid)] = {"t": round(now), "c": int(chat), "u": int(uid), "n": (name or "")[:40], "k": kind[:20],
                            "w": (why or "")[:160], "s": round(float(score or 0), 2), "tr": tier or "", "a": act[:40],
                            "by": int(by), "x": (text or "")[:CASE_TEXT_MAX], "m": int(mid or 0), "st": "open"}
        if len(self.c) > CASE_KEEP:
            for k in sorted(self.c, key=lambda k: self.c[k]["t"])[:len(self.c) - CASE_KEEP]:
                self.c.pop(k, None)
        return cid

    def get(self, cid) -> dict | None:
        try:
            return self.c.get(str(int(cid)))
        except (TypeError, ValueError):
            return None

    def set_state(self, cid, state: str, by: int = 0, now: float = 0.0) -> bool:
        case = self.get(cid)
        if case is None:
            return False
        case["st"] = state
        if by:
            case["ob"] = int(by)
        if now:
            case["at"] = round(now)
        return True

    def of_user(self, chat: int, uid: int, since: float = 0.0, limit: int = 10) -> list:
        rows = [(int(k), v) for k, v in self.c.items() if v["u"] == uid and v["c"] == chat and v["t"] >= since]
        rows.sort(key=lambda kv: -kv[1]["t"])
        return rows[:limit]

    def open_of_user(self, chat: int, uid: int) -> list:
        return [(k, v) for k, v in self.of_user(chat, uid, 0, 50) if v["st"] in ("open", "appeal")]

    def stats(self, chat: int, since: float) -> dict:
        out: dict = {}
        for v in self.c.values():
            if v["c"] == chat and v["t"] >= since:
                out[v["st"]] = out.get(v["st"], 0) + 1
                out["all"] = out.get("all", 0) + 1
        return out

    def prune(self, now: float) -> None:
        for k in [k for k, v in self.c.items() if now - v["t"] > CASE_TTL]:
            self.c.pop(k, None)
        for v in self.c.values():
            if v.get("x") and now - v["t"] > CASE_TEXT_TTL:
                v["x"] = ""


class RepBook:
    """Репутация жалобщиков (одна на весь бот): подтверждённые жалобы повышают вес, ложные — снижают."""

    def __init__(self, root: dict):
        self.d = root

    def counts(self, uid: int) -> tuple:
        r = self.d.get(str(uid))
        return (int(r[0]), int(r[1])) if r else (0, 0)

    def mult(self, uid: int) -> float:
        ok, bad = self.counts(uid)
        if bad >= 5 and ok == 0:
            return 0.3
        p = (ok + 1.0) / (ok + bad + 2.0)
        return round(min(1.5, max(0.5, 0.5 + p)), 2)

    def note(self, uid: int, ok: bool, now: float) -> None:
        r = self.d.setdefault(str(uid), [0, 0, 0])
        r[0 if ok else 1] += 1
        r[2] = round(now)
        if len(self.d) > 4000:
            for k in sorted(self.d, key=lambda k: self.d[k][2])[:800]:
                self.d.pop(k, None)


KNOWN_MIN_USERS, KNOWN_TTL, KNOWN_PER_CHAT = 3, 60 * 86400, 120


class KnownDomains:
    """«Знакомые ссылки чата»: домен, которым без последствий поделились ≥3 разных надёжных участника (хотя бы один — ветеран)."""

    def __init__(self, root: dict):
        self.d = root

    def observe(self, chat: int, reg: str, uid: int, strong: bool, now: float) -> None:
        if not reg or "." not in reg:
            return
        book = self.d.setdefault(str(chat), {})
        e = book.get(reg)
        if e is None:
            if len(book) >= KNOWN_PER_CHAT:
                for k in sorted(book, key=lambda k: book[k][2])[:KNOWN_PER_CHAT // 4]:
                    book.pop(k, None)
            e = book[reg] = [[], round(now), round(now), 0]
        if uid not in e[0]:
            e[0] = (e[0] + [uid])[-6:]
        e[2] = round(now)
        if strong:
            e[3] = 1

    def is_known(self, chat: int, reg: str, now: float) -> bool:
        e = (self.d.get(str(chat)) or {}).get(reg)
        return bool(e and len(e[0]) >= KNOWN_MIN_USERS and e[3] and now - e[2] <= KNOWN_TTL)

    def forget(self, chat: int, reg: str) -> bool:
        return (self.d.get(str(chat)) or {}).pop(reg, None) is not None

    def prune(self, now: float) -> None:
        for cid in list(self.d):
            book = self.d[cid]
            for reg in [r for r, e in book.items() if now - e[2] > KNOWN_TTL]:
                book.pop(reg, None)
            if not book:
                self.d.pop(cid, None)


# ═══════════════════════════════ «Второй взгляд»: сеть, безопасно ═══════════════════════════════
UA = "Mozilla/5.0 (compatible; guard-bot/5.0; chat moderation)"
RDAP_HOSTS = {"rdap.org"}
TG_HOSTS_FETCH = {"t.me"}
DOM_TTL_OK, DOM_TTL_NONE = 60 * 86400, 6 * 3600
TGP_TTL, UNW_TTL = 12 * 3600, 24 * 3600
NET_PER_MIN, NET_PAR, NET_TIMEOUT = 45, 3, 3.2
_NAME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_]{3,31}$")
_HASH_RE = re.compile(r"^[A-Za-z0-9_\-]{8,40}$")


def host_is_public(host: str) -> bool:
    """Все адреса хоста — публичные (не локальные/частные/служебные). Защита от обращения бота внутрь своей сети."""
    try:
        ipaddress.ip_address(host)
        return False
    except ValueError:
        pass
    try:
        infos = socket.getaddrinfo(host, 443, type=socket.SOCK_STREAM)
    except OSError:
        return False
    if not infos:
        return False
    for fam, _t, _p, _c, sa in infos:
        try:
            if not ipaddress.ip_address(sa[0]).is_global:
                return False
        except ValueError:
            return False
    return True


class _SafeRedirect(urllib.request.HTTPRedirectHandler):
    max_redirections = 3

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        u = urllib.parse.urlsplit(newurl)
        if u.scheme != "https" or not u.hostname or (u.port not in (None, 443)) or not host_is_public(u.hostname):
            return None
        return super().redirect_request(req, fp, code, msg, headers, newurl)


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *a, **kw):
        return None


def http_get(url: str, timeout: float = NET_TIMEOUT, max_bytes: int = 150_000, follow: bool = True,
             method: str = "GET", accept: str = "*/*") -> tuple:
    """→ (код, заголовки, тело). Ходит только на https и только на заранее разрешённые хосты (RDAP, t.me, сокращалки из списка)."""
    u = urllib.parse.urlsplit(url)
    if u.scheme != "https" or not u.hostname or (u.port not in (None, 443)):
        raise ValueError("только https")
    if not host_is_public(u.hostname):
        raise ValueError("адрес не публичный")
    handlers = [_SafeRedirect() if follow else _NoRedirect(), urllib.request.HTTPSHandler(context=ssl.create_default_context())]
    opener = urllib.request.build_opener(*handlers)
    req = urllib.request.Request(url, method=method, headers={"User-Agent": UA, "Accept": accept, "Accept-Language": "en"})
    try:
        with opener.open(req, timeout=timeout) as r:
            body = r.read(max_bytes) if method != "HEAD" else b""
            return r.status, dict(r.headers.items()), body
    except urllib.error.HTTPError as e:
        try:
            body = e.read(2000) if method != "HEAD" else b""
        except Exception:                                            # noqa: BLE001
            body = b""
        return e.code, dict(e.headers.items()) if e.headers else {}, body


def iso_to_ts(s: str) -> float | None:
    m = re.match(r"(\d{4})-(\d{2})-(\d{2})(?:[T ](\d{2}):(\d{2})(?::(\d{2}))?)?", s or "")
    if not m:
        return None
    try:
        y, mo, d, h, mi, se = (int(x or 0) for x in m.groups())
        return float(calendar.timegm((y, mo, d, h, mi, se)))
    except (ValueError, OverflowError):
        return None


def rdap_created(js: Any) -> float | None:
    """Дата регистрации домена из ответа RDAP (событие registration). Нет данных → None."""
    if not isinstance(js, dict):
        return None
    best = None
    for e in js.get("events") or []:
        if isinstance(e, dict) and str(e.get("eventAction", "")).lower() == "registration":
            ts = iso_to_ts(str(e.get("eventDate", "")))
            if ts and (best is None or ts < best):
                best = ts
    return best


def age_signal(age_s: float) -> tuple | None:
    """Свежий домен — классика фишинга: чем моложе, тем подозрительнее."""
    d = age_s / 86400.0
    if d < 0:
        return None
    if d < 2:
        return ("g5_young", 3.2, "домен зарегистрирован меньше 2 суток назад")
    if d < 7:
        return ("g5_young", 2.4, "домен зарегистрирован %d дн. назад" % max(1, int(d)))
    if d < 30:
        return ("g5_young", 1.4, "домену меньше месяца (%d дн.)" % int(d))
    return None


_META_RX = {
    "title": re.compile(r'<meta\s+property="og:title"\s+content="([^"]*)"', re.I),
    "desc": re.compile(r'<meta\s+property="og:description"\s+content="([^"]*)"', re.I),
}
_EXTRA_RX = re.compile(r'<div class="tgme_page_extra">(.*?)</div>', re.I | re.S)


def tg_preview_parse(page: str) -> dict:
    """Публичная страница t.me/<имя> или t.me/+код: название, описание, число участников и тип (канал/чат)."""
    out = {"title": "", "desc": "", "members": 0, "kind": ""}
    for k, rx in _META_RX.items():
        m = rx.search(page or "")
        if m:
            out[k] = html.unescape(m.group(1)).strip()[:300]
    m = _EXTRA_RX.search(page or "")
    if m:
        extra = html.unescape(re.sub(r"<[^>]+>", " ", m.group(1)))
        n = re.search(r"(\d[\d\s ,]*)\s*(subscribers|members|подписчик\w*|участник\w*)", extra, re.I)
        if n:
            out["members"] = int(re.sub(r"\D", "", n.group(1)) or 0)
            out["kind"] = "channel" if n.group(2).lower().startswith(("subscr", "подпис")) else "group"
    return out


def tg_target(host: str, raw: str) -> tuple | None:
    """UrlInfo (host, raw=host+путь) → ('name', имя) | ('hash', код) для публичного превью t.me; иначе None."""
    if host not in ("t.me", "telegram.me", "telegram.dog"):
        return None
    path = raw[len(host):].split("?")[0].split("#")[0]
    seg = [x for x in path.split("/") if x]
    if not seg:
        return None
    first = seg[0]
    if first.startswith("+") and _HASH_RE.match(first[1:]):
        return "hash", first[1:]
    if first.lower() == "joinchat" and len(seg) > 1 and _HASH_RE.match(seg[1]):
        return "hash", seg[1]
    if len(seg) == 1 and _NAME_RE.match(first):
        return "name", first
    return None


class Intel:
    """Кэш и сетевые проверки. Всё необязательное: нет сети/лимит/сбой → просто нет доказательств, модерация идёт как раньше."""

    def __init__(self, root_getter, clock=time.time):
        self._root_get = root_getter
        self.clock = clock
        self.hist: deque = deque(maxlen=200)
        self.fails = 0
        self.paused = 0.0
        self.calls = 0
        self.hits = 0
        self._sem: asyncio.Semaphore | None = None
        self._flight: dict = {}

    # ---- кэш ----
    def _r(self) -> dict:
        root = self._root_get()
        for k in ("dom", "tgp", "unw"):
            root.setdefault(k, {})
        return root

    def cached_created(self, reg: str, now: float):
        """→ (известно ли, дата регистрации или 0)"""
        e = self._r()["dom"].get(reg)
        if e is None:
            return False, 0.0
        ts, at = e
        if now - at > (DOM_TTL_OK if ts else DOM_TTL_NONE):
            return False, 0.0
        return True, float(ts)

    def cached_tg(self, key: str, now: float):
        e = self._r()["tgp"].get(key)
        if e and now - e[5] <= TGP_TTL:
            return {"title": e[0], "desc": e[1], "members": e[2], "kind": e[3], "ok": bool(e[4])}
        return None

    def cached_unwrap(self, url: str, now: float):
        e = self._r()["unw"].get(url)
        if e and now - e[1] <= UNW_TTL:
            return e[0]
        return None

    def _trim(self, d: dict, cap: int, ix: int) -> None:
        if len(d) > cap:
            for k in sorted(d, key=lambda k: d[k][ix])[:cap // 5]:
                d.pop(k, None)

    # ---- лимиты ----
    def can_go(self, now: float) -> bool:
        if now < self.paused:
            return False
        while self.hist and now - self.hist[0] > 60:
            self.hist.popleft()
        return len(self.hist) < NET_PER_MIN

    def _ok(self) -> None:
        self.fails = 0

    def _bad(self, now: float) -> None:
        self.fails += 1
        if self.fails >= 6:
            self.paused = now + 600
            self.fails = 0
            log_look.warning("сеть для «второго взгляда» недоступна — пауза на 10 минут (модерация не затронута)")

    async def _run(self, fn, *a):
        if self._sem is None:
            self._sem = asyncio.Semaphore(NET_PAR)
        async with self._sem:
            self.hist.append(self.clock())
            self.calls += 1
            return await asyncio.wait_for(asyncio.to_thread(fn, *a), timeout=NET_TIMEOUT + 1.5)

    # ---- запросы ----
    @staticmethod
    def _rdap_blocking(reg: str):
        try:
            name = reg.encode("idna").decode("ascii")
        except UnicodeError:
            return None
        if not re.fullmatch(r"[a-z0-9.\-]{3,253}", name) or "." not in name:
            return None
        code, _h, body = http_get("https://rdap.org/domain/" + urllib.parse.quote(name), accept="application/rdap+json, application/json")
        if code != 200:
            return "none" if code in (404, 400) else None
        return rdap_created(json.loads(body.decode("utf-8", "ignore")))

    async def created(self, reg: str) -> float:
        now = self.clock()
        known, ts = self.cached_created(reg, now)
        if known:
            return ts
        if not self.can_go(now):
            return 0.0
        key = ("dom", reg)
        t = self._flight.get(key)
        if t is None:
            t = self._flight[key] = asyncio.ensure_future(self._created_task(reg))
            t.add_done_callback(lambda _f, k=key: self._flight.pop(k, None))
        return await asyncio.shield(t)

    async def _created_task(self, reg: str) -> float:
        now = self.clock()
        try:
            res = await self._run(self._rdap_blocking, reg)
        except Exception as e:                                       # noqa: BLE001
            log_look.debug("RDAP %s: %s", reg, e)
            self._bad(now)
            return 0.0
        if res is None:
            self._bad(now)
            return 0.0
        self._ok()
        ts = 0.0 if res == "none" else float(res)
        d = self._r()["dom"]
        d[reg] = [round(ts), round(now)]
        self._trim(d, 4000, 1)
        return ts

    @staticmethod
    def _tg_blocking(kind: str, key: str):
        path = ("+" + key) if kind == "hash" else key
        code, _h, body = http_get("https://t.me/" + urllib.parse.quote(path, safe="+"), accept="text/html")
        if code != 200:
            return None
        return tg_preview_parse(body.decode("utf-8", "ignore"))

    async def tg(self, kind: str, key: str) -> dict | None:
        now = self.clock()
        ck = kind[0] + ":" + key
        hit = self.cached_tg(ck, now)
        if hit is not None:
            return hit if hit["ok"] else None
        if not self.can_go(now):
            return None
        try:
            res = await self._run(self._tg_blocking, kind, key)
        except Exception as e:                                       # noqa: BLE001
            log_look.debug("t.me %s: %s", key, e)
            self._bad(now)
            return None
        d = self._r()["tgp"]
        if res is None:
            self._bad(now)
            return None
        self._ok()
        d[ck] = [res["title"][:90], res["desc"][:240], res["members"], res["kind"], 1 if (res["title"] or res["desc"]) else 0, round(now)]
        self._trim(d, 700, 5)
        return res if (res["title"] or res["desc"]) else None

    @staticmethod
    def _unwrap_blocking(url: str, hosts):
        cur = url
        for _ in range(4):
            u = urllib.parse.urlsplit(cur)
            host = (u.hostname or "").lower()
            if u.scheme != "https" or not any(host == h or host.endswith("." + h) for h in hosts):
                return cur
            code, hdr, _b = http_get(cur, follow=False, method="HEAD")
            if code in (405, 403, 400, 501):
                code, hdr, _b = http_get(cur, follow=False, method="GET", max_bytes=0)
            loc = next((v for k, v in hdr.items() if k.lower() == "location"), "")
            if code in (301, 302, 303, 307, 308) and loc:
                cur = urllib.parse.urljoin(cur, loc)
                continue
            return cur
        return cur

    async def unwrap(self, url: str, hosts) -> str | None:
        """https://bit.ly/x → конечный адрес. Заходим ТОЛЬКО на сами сокращалки из списка; конечный сайт не открываем никогда."""
        now = self.clock()
        hit = self.cached_unwrap(url, now)
        if hit is not None:
            return hit
        if not self.can_go(now):
            return None
        try:
            res = await self._run(self._unwrap_blocking, url, tuple(hosts))
        except Exception as e:                                       # noqa: BLE001
            log_look.debug("unwrap %s: %s", url, e)
            self._bad(now)
            return None
        self._ok()
        d = self._r()["unw"]
        d[url] = [res[:300], round(now)]
        self._trim(d, 400, 1)
        return res

    # ---- главный вход ----
    async def investigate(self, items: list, hosts, deadline: float) -> list:
        """items: [(kind, host, reg, raw)] → список фактов. Никогда не бросает исключений; общий потолок времени — deadline секунд."""
        facts: list = []

        async def one(kind: str, host: str, reg: str, raw: str):
            try:
                if kind == "shortener":
                    final = await self.unwrap("https://" + raw, hosts)
                    if final and final != "https://" + raw:
                        facts.append({"t": "unw", "orig": raw, "final": final})
                        fu = urllib.parse.urlsplit(final)
                        fh = (fu.hostname or "").lower()
                        fr = G.reg_domain(re.sub(r"^www\.", "", fh)) if fh else ""
                        tgt = tg_target(fh, fh + (fu.path or ""))
                        if tgt:
                            pv = await self.tg(*tgt)
                            if pv:
                                facts.append({"t": "tg", "key": tgt[1], "via": "short", **pv})
                        elif fr and fh not in hosts:
                            ts = await self.created(fr)
                            if ts:
                                facts.append({"t": "age", "reg": fr, "created": ts, "via": "short"})
                elif kind in ("invite", "tg_channel", "tg_bot"):
                    tgt = tg_target(host, raw)
                    if tgt:
                        pv = await self.tg(*tgt)
                        if pv:
                            facts.append({"t": "tg", "key": tgt[1], **pv})
                elif kind == "unknown" and reg:
                    ts = await self.created(reg)
                    if ts:
                        facts.append({"t": "age", "reg": reg, "created": ts})
            except asyncio.CancelledError:
                raise
            except Exception:                                        # noqa: BLE001
                log_look.debug("investigate: сбой на %s", host, exc_info=True)

        try:
            await asyncio.wait_for(asyncio.gather(*(one(*it) for it in items[:3]), return_exceptions=True), timeout=deadline)
        except (asyncio.TimeoutError, asyncio.CancelledError):
            pass
        return facts


def facts_to_signals(facts: list, analyze, now: float) -> list:
    """Факты → сигналы анализа [(имя, вес, объяснение)]. analyze — функция guard.analyze_text (для текста из описания канала)."""
    out: list = []
    for f in facts:
        t = f.get("t")
        if t == "age" and f.get("created"):
            sg = age_signal(now - float(f["created"]))
            if sg:
                if f.get("via") == "short":
                    sg = (sg[0], sg[1], "сокращённая ссылка ведёт на " + sg[2].replace("домен", "сайт, домен", 1))
                out.append(sg)
        elif t == "tg":
            text = (f.get("title") or "") + "\n" + (f.get("desc") or "")
            if len(text.strip()) < 8:
                continue
            a = analyze(text[:600])
            if a.raw >= 2.0 or a.hard >= 1.0:
                top = sorted(a.signals, key=lambda s: -s[1])[:2]
                why = "; ".join(s[2] for s in top)
                w = min(3.4, 0.7 * a.raw + 0.4)
                if f.get("members", 0) and f["members"] < 40:
                    w = min(3.8, w + 0.4)
                label = "канал" if f.get("kind") == "channel" else "чат" if f.get("kind") == "group" else "страница"
                out.append(("g5_tgpitch", round(w, 2), "в описании %s по ссылке: %s" % (label, why[:120])))
        elif t == "unw":
            fu = urllib.parse.urlsplit(f["final"])
            a = analyze(f["final"][:300])
            bad = [s for s in a.signals if s[0] in ("lookalike", "brand_sub", "mismatch", "idn_mixed", "userinfo", "download", "redirect",
                                                     "bait2", "bait", "random_host", "deep_sub2", "risky_tld")]
            if bad:
                w = min(4.5, sum(s[1] for s in bad) * 0.8)
                out.append(("g5_unwrap", round(w, 2), "сокращённая ссылка ведёт на %s: %s" % ((fu.hostname or "?")[:40], bad[0][2])))
    return out


# ═══════════════════════════════ /repeat: условия показа ═══════════════════════════════
def _day_set(tok: str) -> set | None:
    t = tok.lower().replace("ё", "е").strip(",.")
    if t in ("будни", "будние", "буд", "workdays", "weekdays"):
        return {0, 1, 2, 3, 4}
    if t in ("выходные", "вых", "weekend"):
        return {5, 6}
    if t in ("ежедневно", "всегдни"):
        return set(range(7))
    out: set = set()
    for part in t.split(","):
        if not part:
            return None
        if "-" in part:
            a, _, b = part.partition("-")
            wa, wb = weekday_of(a), weekday_of(b)
            if wa is None or wb is None or len(a) < 2 or len(b) < 2:
                return None
            d = wa
            while True:
                out.add(d)
                if d == wb:
                    break
                d = (d + 1) % 7
        else:
            w = weekday_of(part)
            if w is None or len(part) < 2:
                return None
            out.add(w)
    return out or None


def parse_repeat_opts(rest: str, now: float, tz_h: float) -> tuple:
    """После интервала в /repeat могут идти необязательные условия, потом текст. → (opts, текст).
    пн-пт | будни | выходные | пн,ср · 10:00-22:00 | с 10 до 22 · до 31.12[.2027] · 5 раз · закреп · всегда"""
    toks = rest.split()
    opts: dict = {}
    i = 0
    while i < len(toks):
        t = toks[i]
        low = t.lower().replace("ё", "е")
        days = _day_set(low) if len(low) <= 24 else None
        if days is not None and "dow" not in opts:
            opts["dow"] = sorted(days)
            i += 1
            continue
        m = re.fullmatch(r"(\d{1,2})(?::(\d{2}))?[-–](\d{1,2})(?::(\d{2}))?", low)
        if m and "win" not in opts:
            a, b = int(m.group(1)) * 60 + int(m.group(2) or 0), int(m.group(3)) * 60 + int(m.group(4) or 0)
            if a < 1440 and b <= 1440 and a != b:
                opts["win"] = [a, b % 1440 if b == 1440 else b]
                i += 1
                continue
        if low in ("с", "from") and i + 3 < len(toks) + 0 and toks[i + 2].lower() in ("до", "to"):
            ma = re.fullmatch(r"(\d{1,2})(?::(\d{2}))?", toks[i + 1])
            mb = re.fullmatch(r"(\d{1,2})(?::(\d{2}))?", toks[i + 3])
            if ma and mb and "win" not in opts:
                a, b = int(ma.group(1)) * 60 + int(ma.group(2) or 0), int(mb.group(1)) * 60 + int(mb.group(2) or 0)
                if a < 1440 and b <= 1440 and a != b:
                    opts["win"] = [a, b % 1440 if b == 1440 else b]
                    i += 4
                    continue
        if low == "до" and i + 1 < len(toks) and "until" not in opts:
            md = re.fullmatch(r"(\d{1,2})\.(\d{1,2})(?:\.(\d{2,4}))?", toks[i + 1])
            if md:
                lt = time.gmtime(now + tz_h * 3600)
                y = int(md.group(3)) if md.group(3) else lt.tm_year
                y += 2000 if y < 100 else 0
                try:
                    end = calendar.timegm((y, int(md.group(2)), int(md.group(1)), 23, 59, 59)) - tz_h * 3600
                    if end < now and not md.group(3):
                        end = calendar.timegm((y + 1, int(md.group(2)), int(md.group(1)), 23, 59, 59)) - tz_h * 3600
                except (ValueError, OverflowError):
                    end = 0
                if end > now:
                    opts["until"] = end
                    i += 2
                    continue
        if re.fullmatch(r"\d{1,3}", low) and i + 1 < len(toks) and toks[i + 1].lower() in ("раз", "раза", "times", "x"):
            n = int(low)
            if 1 <= n <= 500 and "left" not in opts:
                opts["left"] = n
                i += 2
                continue
        if low in ("закреп", "закрепить", "pin") and "pin" not in opts:
            opts["pin"] = True
            i += 1
            continue
        if low in ("всегда", "always", "безусловно") and "always" not in opts:
            opts["always"] = True
            i += 1
            continue
        break
    return opts, " ".join(toks[i:]) if i < len(toks) else ""


def repeat_gate(opts: dict, now: float, tz_h: float, last_human: float, last_post: float) -> tuple:
    """→ ('go',) | ('defer', когда) | ('drop', причина). opts — r['g5'] объявления."""
    if not opts:
        return ("go",)
    if opts.get("until") and now > opts["until"]:
        return ("drop", "срок вышел")
    if opts.get("left") is not None and opts["left"] <= 0:
        return ("drop", "показы закончились")
    lt = time.gmtime(now + tz_h * 3600)
    dow = opts.get("dow")
    if dow and lt.tm_wday not in dow:
        for add in range(1, 8):
            nd = (lt.tm_wday + add) % 7
            if nd in dow:
                start = (opts.get("win") or [0])[0]
                return ("defer", _local_midnight(now, tz_h) + add * 86400 + start * 60)
    win = opts.get("win")
    if win:
        mod = lt.tm_hour * 60 + lt.tm_min
        a, b = win
        inside = (a <= mod < b) if a < b else (mod >= a or mod < b)
        if not inside:
            nxt = _local_midnight(now, tz_h) + a * 60
            if nxt <= now:
                nxt += 86400
            return ("defer", nxt)
    if not opts.get("always") and last_post and last_human <= last_post:
        return ("defer", now + 600)
    return ("go",)


def describe_repeat_opts(opts: dict) -> str:
    bits = []
    dow = opts.get("dow")
    if dow:
        bits.append("по дням: " + ",".join(_WD_NAMES[d] for d in dow) if len(dow) < 7 else "каждый день")
    if opts.get("win"):
        a, b = opts["win"]
        bits.append("в окне %02d:%02d–%02d:%02d" % (a // 60, a % 60, b // 60, b % 60))
    if opts.get("until"):
        bits.append("до " + time.strftime("%d.%m.%Y", time.gmtime(opts["until"] + 0)))
    if opts.get("left") is not None:
        bits.append("осталось показов: %d" % opts["left"])
    if opts.get("pin"):
        bits.append("закрепляется")
    if opts.get("always"):
        bits.append("даже в пустом чате")
    return " · ".join(bits)


# ═══════════════════════════════ «Ферма»: шаблоны имён забаненных аккаунтов ═══════════════════════════════
FARM_TTL, FARM_KEEP, FARM_KEYS_MAX = 3 * 86400, 12, 2500
_ZW_RX = re.compile(r"[​-‏⁠﻿­]")


# Основы, которые носят тысячи настоящих людей («user12345», «id777», «telegram_1»): по ним ферму не ищем — иначе честного
# «user555» заставят проходить сложную капчу из-за двух забаненных «user1» и «user2».
FARM_GENERIC = frozenset({"user", "users", "usr", "id", "tg", "telegram", "account", "acc", "guest", "member", "name", "username",
                          "new", "test", "admin", "support", "help", "bot", "anon", "anonymous", "mr", "mrs", "mix", "pro",
                          "юзер", "пользователь", "аккаунт", "гость", "админ", "тест", "новый"})


def _farm_stem(key: str) -> str:
    return re.sub(r"[#_\s\-.]+", "", key.split(":", 1)[-1])


def farm_keys(name: str, username: str = "") -> set:
    """Шаблоны имени/юзернейма: цифры → «#». Фермы заводят аккаунты пачкой: «anna_91234», «Alina 4821», один и тот же «Alina Rose»."""
    keys: set = set()
    un = (username or "").lower().lstrip("@")
    if un:
        k = re.sub(r"\d+", "#", un)
        if "#" in k and len(re.sub(r"[#_]", "", k)) >= 3 and _farm_stem(k) not in FARM_GENERIC:
            keys.add("u:" + k)
    nm = re.sub(r"\s+", " ", _ZW_RX.sub("", name or "")).strip().lower()
    if nm:
        k = re.sub(r"\d+", "#", nm)
        if "#" in k and len(re.sub(r"[#\s]", "", k)) >= 3:
            if _farm_stem(k) not in FARM_GENERIC:
                keys.add("n:" + k)
        elif len(nm) >= 7 and " " in nm:
            keys.add("n:" + nm)
    return keys


class FarmBook:
    """Шаблоны имён аккаунтов, забаненных за спам где-либо у бота. Три разных забаненных аккаунта с одним шаблоном за 3 суток —
    это ферма: следующий «такой же» получает усложнённую проверку при входе. Сама по себе запись никого не наказывает."""

    def __init__(self, root: dict):
        self.d = root

    def note(self, keys, uid: int, now: float) -> None:
        for k in keys:
            row = self.d.setdefault(k, [])
            row[:] = [e for e in row if e[0] != uid and now - e[1] <= FARM_TTL][-(FARM_KEEP - 1):] + [[int(uid), round(now)]]
        if len(self.d) > FARM_KEYS_MAX:
            for k in sorted(self.d, key=lambda k: self.d[k][-1][1] if self.d[k] else 0)[:FARM_KEYS_MAX // 5]:
                self.d.pop(k, None)

    def hits(self, keys, uid: int, now: float) -> int:
        best = 0
        for k in keys:
            n = len({e[0] for e in self.d.get(k, ()) if e[0] != uid and now - e[1] <= FARM_TTL})
            if n and "#" not in k:                                   # точное имя без цифр — слабее: считаем наполовину
                n = n // 2
            elif n and len(_farm_stem(k)) < 6 and n < 3:             # короткая основа («anna_#») — слабая улика: нужно трое
                n = 0
            best = max(best, n)
        return best

    def forget(self, uid: int) -> int:
        """Бан отменили (ошибка бота) — этот аккаунт больше не «образец фермы»."""
        n = 0
        for k in list(self.d):
            before = len(self.d[k])
            self.d[k] = [e for e in self.d[k] if e[0] != int(uid)]
            n += before - len(self.d[k])
            if not self.d[k]:
                self.d.pop(k, None)
        return n

    def prune(self, now: float) -> None:
        for k in list(self.d):
            self.d[k] = [e for e in self.d[k] if now - e[1] <= FARM_TTL]
            if not self.d[k]:
                self.d.pop(k, None)


# ═══════════════════════════════ состояние, автомат защиты от сбоев ═══════════════════════════════
class Books:
    """Все постоянные книги 5.0 лежат в store.meta['g5'] (общее хранилище бота). Создаются лениво и пересоздаются, если store.meta подменили."""

    def __init__(self, store):
        self.store = store
        self.root = store.meta.setdefault("g5", {})
        self.cases = CaseBook(self.root.setdefault("cases", {}))
        self.rep = RepBook(self.root.setdefault("rep", {}))
        self.known = KnownDomains(self.root.setdefault("known", {}))
        self.farm = FarmBook(self.root.setdefault("farm", {}))
        self.chat = self.root.setdefault("chat", {})
        self.inbox = self.root.setdefault("inbox", {})
        for k, v in (("seq", 0), ("t", {}), ("mute", {}), ("off", {})):
            self.inbox.setdefault(k, v)
        self.gate = self.root.setdefault("gate", {})
        self.intel_root = self.root.setdefault("intel", {})

    def cfg(self, cid: int) -> dict:
        return self.chat.setdefault(str(cid), {})

    def prune(self, now: float) -> None:
        self.cases.prune(now)
        self.known.prune(now)
        self.farm.prune(now)
        t = self.inbox["t"]
        if len(t) > 300:
            for k in sorted(t, key=lambda k: t[k]["t"])[:len(t) - 300]:
                t.pop(k, None)
        for u, until in list(self.inbox["mute"].items()):
            if until and until < now:
                self.inbox["mute"].pop(u, None)


def books(store) -> Books:
    b = store.__dict__.get("_g5_books")
    root = store.meta.get("g5")
    if b is None or root is None or b.root is not root or b.store is not store:
        b = Books(store)
        store.__dict__["_g5_books"] = b
    return b


class Breaker:
    """Любой сбой внутри расширения глушится; 5 подряд — узел отключается на 30 минут (модерация идёт как в 4.3)."""

    def __init__(self):
        self.fails: dict = {}
        self.off: dict = {}

    def ok(self, name: str) -> bool:
        return time.time() >= self.off.get(name, 0)

    def bad(self, name: str) -> None:
        n = self.fails.get(name, 0) + 1
        self.fails[name] = n
        log.exception("расширение 5.0: сбой в узле %r (%d подряд)", name, n)
        if n >= 5:
            self.off[name] = time.time() + 1800
            self.fails[name] = 0
            log.error("расширение 5.0: узел %r отключён на 30 минут", name)

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
PROB_TTL = 3 * 3600
FARM_FLAG_TTL = 6 * 3600
INJECT_TTL = 180.0
# признаки «это атака на конкретное сообщение» — для таких ссылок «знакомый домен» не смягчает ничего
BAD_URL_FLAGS = frozenset({"mismatch", "idn_mixed", "userinfo", "lookalike", "brand_sub", "download", "redirect", "bait2",
                           "deep_sub2", "hidden"})
# признаки самого домена: у знакомого чату домена они перестают быть уликой
DOMAIN_FLAGS = frozenset({"risky_tld", "random_host", "bait", "deep_sub", "link_unknown"})


# ═══════════════════════════════ движок: подмешивается ПЕРЕД EngineX ═══════════════════════════════
class EngineMix:
    """Новые сигналы анализа сообщения и учёт «после проверки». Подключается через _learn_signals/_learn_post —
    те же крючки, что и у самообучения 4.3, поэтому порядок и пороги остальной модерации не меняются."""

    def _g5s(self):
        st = self.__dict__.get("_g5_state")
        if st is None:
            st = self.__dict__["_g5_state"] = {"inject": {}, "last": {}, "prob": {}, "farm": {}, "hits": 0, "soft": 0}
        return st

    def g5_books(self) -> Books:
        return books(self.store)

    def g5_inject(self, cid: int, mid: int, sigs: list, now: float) -> None:
        st = self._g5s()
        st["inject"][(cid, mid)] = (now, list(sigs))
        if len(st["inject"]) > 400:
            for k in [k for k, v in st["inject"].items() if now - v[0] > INJECT_TTL][:200]:
                st["inject"].pop(k, None)

    def g5_mark_farm(self, cid: int, uid: int, now: float, n: int = 2) -> None:
        self._g5s()["farm"][(cid, uid)] = now
        self._g5s().setdefault("farm_n", {})[(cid, uid)] = int(n)

    def g5_mark_prob(self, cid: int, uid: int, now: float) -> None:
        self._g5s()["prob"][(cid, uid)] = now + PROB_TTL

    def g5_last_signals(self, cid: int, mid: int) -> list:
        e = self._g5s()["last"].get((cid, mid))
        return list(e[1]) if e else []

    # ---- сигналы ----
    def _learn_signals(self, msg, chat, a, tier: str, now: float) -> None:
        super()._learn_signals(msg, chat, a, tier, now)
        if ON.get("all"):
            BR.run("signals", self._g5_signals, msg, chat, a, tier, now)

    def _g5_signals(self, msg, chat, a, tier: str, now: float) -> None:
        st = self._g5s()
        sig, cid, uid = a.signals, msg.chat_id, msg.user_id
        inj = st["inject"].get((cid, msg.msg_id))
        if inj and now - inj[0] <= INJECT_TTL:
            sig.extend(inj[1])
        if feat("known") and a.urls and not msg.edited:
            self._g5_soften_known(a, cid, now)
        if tier == "new" and (a.urls or a.contacts) and not msg.edited:
            f = st["farm"].get((cid, uid))
            if f and now - f <= FARM_FLAG_TTL:
                nf = st.get("farm_n", {}).get((cid, uid), 2)
                sig.append(("g5_farm", 1.6 if nf >= 3 else 1.0, "имя аккаунта как у недавно забаненных (ферма)"))
            if st["prob"].get((cid, uid), 0) > now:
                sig.append(("g5_probation", 1.2, "вошёл во время тревоги и сразу дал ссылку/контакт"))

    def _g5_soften_known(self, a, cid: int, now: float) -> None:
        kd = self.g5_books().known
        urls = [u for u in a.urls if u.kind != "allowed"]
        if not urls or any(u.kind != "unknown" or (u.flags & BAD_URL_FLAGS) or not kd.is_known(cid, u.reg, now) for u in urls):
            return
        for i, (n, w, why) in enumerate(a.signals):
            if n in DOMAIN_FLAGS and w > 0:
                a.signals[i] = (n, round(w * 0.15, 2), why + " — знакомый чату домен")
                if n == "link_unknown":
                    self._g5s()["soft"] += 1

    # ---- после проверки ----
    def _learn_post(self, msg, v, la, now: float) -> None:
        super()._learn_post(msg, v, la, now)
        if ON.get("all"):
            BR.run("post", self._g5_post, msg, v, la, now)

    def _g5_post(self, msg, v, la, now: float) -> None:
        ana, tier, strict, chat, rec = la
        cid, uid = msg.chat_id, msg.user_id
        st = self._g5s()
        if (v.delete or v.ban or v.mute_s) and not msg.edited:
            sg = [(n, round(w, 2)) for n, w, _ in sorted(ana.signals, key=lambda s: -s[1]) if w > 0][:8]
            st["last"][(cid, msg.msg_id)] = (now, sg)
            if len(st["last"]) > 300:
                for k in sorted(st["last"], key=lambda k: st["last"][k][0])[:100]:
                    st["last"].pop(k, None)
        bk = self.g5_books()
        if feat("known") and v.ok and tier in ("member", "veteran") and not msg.edited and ana.urls and uid > 0:
            for u in ana.urls:
                if u.kind == "unknown" and u.reg and not (u.flags & BAD_URL_FLAGS):
                    bk.known.observe(cid, u.reg, uid, tier == "veteran", now)
        if v.ban and v.category in ("scam", "scam_ban") and tier == "new" and uid > 0 and not msg.edited:
            keys = farm_keys(msg.name, msg.username)
            if keys:
                bk.farm.note(keys, uid, now)
                self.store.dirty = True

    # ---- жалобы с репутацией ----
    def report_effective(self, chat_id: int, by: dict, now: float):
        if feat("reports"):
            rep = self.g5_books().rep
            by = {u: (w if w >= 3.0 else round(w * rep.mult(u), 2)) for u, w in by.items()}
        return super().report_effective(chat_id, by, now)

    def prune(self, now: float | None = None):
        r = super().prune(now)
        now = self.clock() if now is None else now
        st = self._g5s()
        for k in [k for k, t in st["farm"].items() if now - t > FARM_FLAG_TTL]:
            st["farm"].pop(k, None)
            st.get("farm_n", {}).pop(k, None)
        for k in [k for k, t in st["prob"].items() if t < now]:
            st["prob"].pop(k, None)
        for k in [k for k, v in st["inject"].items() if now - v[0] > INJECT_TTL]:
            st["inject"].pop(k, None)
        BR.run("prune", self.g5_books().prune, now)
        return r


# ═══════════════════════════════ охрана: подмешивается ПЕРЕД GuardX ═══════════════════════════════
def esc(s, n: int = 40) -> str:
    return G.esc(s, n)


def mention(uid: int, name: str = "") -> str:
    return G.mention(uid, name)


def human_dur(sec: float) -> str:
    return G.human_dur(sec)


_CASE = contextvars.ContextVar("g5_case", default=0)
_STATUS = contextvars.ContextVar("g5_status", default=False)
CMD_RX = re.compile(r"^/([A-Za-z_]+)(?:@([A-Za-z0-9_]+))?(?:\s+(.*))?$", re.S)
INBOX_KINDS = {"bug": ("🐞", "Баг"), "feedback": ("💬", "Отзыв")}
INBOX_MAX, INBOX_MIN, INBOX_PER_HOUR = 1500, 4, 4
INBOX_MUTES = {"1h": 3600, "1d": 86400, "7d": 7 * 86400, "0": 0}
RULES_SHOW_TTL, RULES_WAIT = 360, 600
APPEAL_TTL, APPEAL_USER_GAP, APPEAL_CHAT_HOUR = 120, 1800, 6
LOOK_DEADLINE = 2.6
WAIT_TTL = 600


class GuardMix:
    """Всё, что 5.0 добавляет охране: дела и отмена, апелляция, «второй взгляд», правила после проверки, /bug и /feedback,
    «ферма» для проверки при входе. Подмешивается ПЕРЕД GuardX: всё, чего здесь нет, работает как в 4.3."""

    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        self.__dict__["_g5x"] = {"wait": {}, "rate": {}, "ap_user": {}, "ap_chat": {}, "joined": {}, "farm_n": {}}
        self.g5_intel = Intel(lambda: books(self.store).intel_root, clock=self.now)

    # ---- общие мелочи ----
    @property
    def g5x(self) -> dict:
        return self.__dict__["_g5x"]

    def g5b(self) -> Books:
        return books(self.store)

    @staticmethod
    async def _g5_ans(cb, text: str | None = None, alert: bool = False) -> None:
        try:
            await cb.answer(text, show_alert=alert) if text else await cb.answer()
        except asyncio.CancelledError:
            raise
        except Exception:                                            # noqa: BLE001
            pass

    def _g5_targets(self) -> list:
        ids = sorted(self.store.alert_users & self.owners)
        return ids or sorted(self.owners)

    async def _g5_tell_owners(self, text: str, markup=None) -> int:
        n = 0
        for uid in self._g5_targets():
            if await self.dm(uid, text, markup):
                n += 1
        return n

    def g5_owner_ok(self, uid: int) -> bool:
        return uid in self.owners

    def g5_panel_ok(self, uid: int) -> bool:
        return uid in self.owners and (self.panel_hash is None or self.panel_open(uid))

    # ═══════ входной фильтр: /bug, /feedback, ожидание ответа в личке ═══════
    async def on_message(self, m) -> bool:
        if ON.get("all"):
            try:
                if await self._g5_front(m):
                    return True
            except asyncio.CancelledError:
                raise
            except Exception:                                        # noqa: BLE001
                BR.bad("front")
            if feat("look") and feat("net") and BR.ok("look"):
                try:
                    await self._g5_preflight(m)
                except asyncio.CancelledError:
                    raise
                except Exception:                                    # noqa: BLE001
                    BR.bad("look")
        return await super().on_message(m)

    async def _g5_front(self, m) -> bool:
        chat = m.chat
        ctype = getattr(chat, "type", "")
        u = getattr(m, "from_user", None)
        if u is None or getattr(u, "is_bot", False) or u.id == G.ANON_ADMIN_ID:
            return False
        text = (getattr(m, "text", None) or "").strip()
        now = self.now()
        if ctype == "private":
            w = self.g5x["wait"].get(u.id)
            if w is not None and now > w["exp"]:
                self.g5x["wait"].pop(u.id, None)
                w = None
            if w is not None and text and not text.startswith("/"):
                return await self._g5_wait_input(m, u, w, text)
            return False
        if ctype in G.GROUP_TYPES and text.startswith("/"):
            cm = CMD_RX.match(text)
            if not cm or cm.group(1).lower() not in INBOX_KINDS:
                return False
            if cm.group(2) and cm.group(2).lower() != (self.username or "").lower():
                return False
            if not self.chat_ok(chat.id) or str(u.id) in self.gbans() and u.id not in self.owners:
                return False
            await self._g5_inbox_take(m, u, cm.group(1).lower(), (cm.group(3) or "").strip(), group=True)
            return True
        return False

    async def _g5_wait_input(self, m, u, w: dict, text: str) -> bool:
        kind = w["kind"]
        self.g5x["wait"].pop(u.id, None)
        if kind in INBOX_KINDS:
            await self._g5_inbox_take(m, u, kind, text, group=False)
            return True
        if u.id not in self.owners:
            return False
        if kind == "reply":
            await self._g5_owner_reply(m, u, w.get("tid", ""), text)
            return True
        if kind in ("pn_mute", "pn_ban") and self.g5_panel_ok(u.id):
            await self._g5_panel_id_input(m, u, kind, text)
            return True
        return False

    async def cmd_cancel(self, m, args):
        u = getattr(m, "from_user", None)
        if u is not None and self.g5x["wait"].pop(u.id, None) is not None and getattr(m.chat, "type", "") == "private":
            self._pending.pop(u.id, None)
            return await self.out(m, "Отменено.")
        return await super().cmd_cancel(m, args)

    async def cmd_bug(self, m, args):
        await self._g5_cmd_inbox(m, "bug", args)

    async def cmd_feedback(self, m, args):
        await self._g5_cmd_inbox(m, "feedback", args)

    async def _g5_cmd_inbox(self, m, kind: str, args: str) -> None:
        u = getattr(m, "from_user", None)
        if u is None or not ON.get("all"):
            return
        if self.in_group(m):
            return await self._g5_inbox_take(m, u, kind, args.strip(), group=True)
        if args.strip():
            return await self._g5_inbox_take(m, u, kind, args.strip(), group=False)
        self.g5x["wait"][u.id] = {"kind": kind, "exp": self.now() + WAIT_TTL}
        if kind == "bug":
            txt = ("🐞 <b>Сообщить о баге</b>\nОпишите одним сообщением: что делали, что ожидали и что получилось. "
                   "Фильтры здесь не действуют — пишите как есть. Отмена: /cancel.")
        else:
            txt = ("💬 <b>Отзыв</b>\nНапишите одним сообщением, что понравилось или чего не хватает. "
                   "Фильтры здесь не действуют. Отмена: /cancel.")
        await self.out(m, txt)

    # ═══════ «Баги» и «Отзывы» ═══════
    def _g5_muted(self, uid: int, now: float) -> bool:
        until = self.g5b().inbox["mute"].get(str(uid))
        return until is not None and (until == 0 or until > now)

    async def _g5_inbox_take(self, m, u, kind: str, text: str, group: bool) -> None:
        bk, now, uid = self.g5b(), self.now(), u.id
        icon, label = INBOX_KINDS[kind]
        ttl = 15 if group else 0
        if group:
            self.deleter.add(m.chat.id, [m.message_id])
        owner = uid in self.owners
        if bk.inbox["off"].get(kind):
            return await self.out(m, "Приём этого вида сообщений сейчас отключён.", ttl=ttl)
        if not owner and self._g5_muted(uid, now):
            return await self.out(m, "Отправка от вас сейчас отключена.", ttl=ttl)
        text = text.strip()
        if len(text) < INBOX_MIN:
            hint = "/bug <i>что не так</i>" if kind == "bug" else "/feedback <i>что понравилось или чего не хватает</i>"
            return await self.out(m, f"Напишите подробнее: {hint}", ttl=ttl or 20)
        text = text[:INBOX_MAX]
        hist = [t for t in self.g5x["rate"].get(uid, []) if now - t < 3600]
        if len(hist) >= INBOX_PER_HOUR and not owner:
            return await self.out(m, "Слишком часто. Попробуйте через час.", ttl=ttl)
        if any(t["u"] == uid and t["x"] == text and now - t["t"] < 86400 for t in bk.inbox["t"].values()):
            return await self.out(m, "Это уже у меня. Спасибо!", ttl=ttl)
        hist.append(now)
        self.g5x["rate"][uid] = hist
        bk.inbox["seq"] += 1
        tid = str(bk.inbox["seq"])
        un = getattr(u, "username", "") or ""
        chat_title = (m.chat.title or "")[:60] if group else ""
        bk.inbox["t"][tid] = {"k": kind, "u": uid, "n": G.user_name(u)[:40], "un": un[:32], "c": m.chat.id if group else 0,
                              "ct": chat_title, "x": text, "t": round(now), "st": "new"}
        self.store.dirty = True
        n = await self._g5_tell_owners(self.g5_ticket_text(tid), self.g5_ticket_kb(tid))
        await self.out(m, f"{icon} Спасибо! Передал владельцу бота." if n else
                       f"{icon} Принято и сохранено — владелец увидит в панели.", ttl=ttl)

    def g5_ticket_text(self, tid: str, note: str = "") -> str:
        t = self.g5b().inbox["t"].get(tid)
        if t is None:
            return "Запись удалена."
        icon, label = INBOX_KINDS.get(t["k"], ("•", "Сообщение"))
        who = mention(t["u"], t["n"]) + (f" (@{esc(t['un'], 32)})" if t.get("un") else "")
        where = f"«{esc(t['ct'], 60)}»" if t.get("ct") else "личные сообщения"
        out = [f"{icon} <b>{label} №{tid}</b> · {self.fmt_when(t['t'])}", f"От: {who} · id <code>{t['u']}</code>",
               f"Где: {where}", "", esc(t["x"], INBOX_MAX)]
        mu = self.g5b().inbox["mute"].get(str(t["u"]))
        if mu is not None:
            out += ["", "🔇 Мут: " + ("навсегда" if mu == 0 else "до " + self.fmt_when(mu))]
        if t["st"] == "replied":
            out += ["", "✉️ Ответ отправлен"]
        elif t["st"] == "done":
            out += ["", "✔ Принято"]
        if note:
            out += ["", note]
        return "\n".join(out)

    @staticmethod
    def g5_ticket_kb(tid: str, back: str = ""):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        rows = [[Btn(text="💬 Ответить", callback_data=f"g5:br:{tid}"), Btn(text="✔ Принято", callback_data=f"g5:bd:{tid}")],
                [Btn(text="🔇 1 ч", callback_data=f"g5:bm:{tid}:1h"), Btn(text="🔇 сутки", callback_data=f"g5:bm:{tid}:1d"),
                 Btn(text="🔇 неделя", callback_data=f"g5:bm:{tid}:7d"), Btn(text="🔇 навсегда", callback_data=f"g5:bm:{tid}:0")],
                [Btn(text="⛔ Бан везде", callback_data=f"g5:bb:{tid}")]]
        if back:
            rows.append([Btn(text="⬅ Назад", callback_data=back)])
        return InlineKeyboardMarkup(inline_keyboard=rows)

    async def _g5_owner_reply(self, m, u, tid: str, text: str) -> None:
        t = self.g5b().inbox["t"].get(tid)
        if t is None:
            return await self.out(m, "Эта запись уже удалена.")
        icon, label = INBOX_KINDS.get(t["k"], ("•", "сообщение"))
        ok = await self.dm(t["u"], f"✉️ <b>Ответ владельца на ваш {label.lower()}:</b>\n{esc(text, INBOX_MAX)}")
        if ok:
            t["st"] = "replied"
            self.store.dirty = True
        await self.out(m, "✉️ Ответ отправлен." if ok else
                       "Не удалось доставить: человек не запускал бота в личке (Telegram не даёт писать первым).")

    async def g5_mute_user(self, uid: int, secs: int, by: int) -> str:
        bk, now = self.g5b(), self.now()
        if uid in self.owners:
            return "Владельца замутить нельзя."
        bk.inbox["mute"][str(uid)] = (round(now + secs) if secs else 0)
        self.store.dirty = True
        self.journal("bug", 0, "", by, str(uid), "мут отправки багов/отзывов: " + ("навсегда" if not secs else human_dur(secs)))
        return "Мут: " + ("навсегда" if not secs else "до " + self.fmt_when(now + secs))

    async def g5_ban_everywhere(self, uid: int, label: str, reason: str, by: int) -> int:
        """Бан «вовсе»: во всех чатах, где бот админ, плюс бот игнорирует его команды и кнопки. Возвращает число чатов или -1."""
        if uid <= 0 or uid in self.owners or self.is_trusted(uid) or uid == self.me_id:
            return -1
        now, done = self.now(), []
        for cid, st in list(self.store.chats.items()):
            if cid >= 0 or not st.active or not self.chat_ok(cid):
                continue
            if not (await self.rights(cid))["restrict"]:
                continue
            if await self.call("ban_chat_member", cid, uid, revoke_messages=True) is not None:
                done.append(cid)
                self.store.user(st, uid, now).banned = True
            await asyncio.sleep(0.05)
        self.gbans()[str(uid)] = {"r": reason[:100], "t": round(now), "by": by, "n": str(label)[:40], "ch": done}
        self.g5b().inbox["mute"].pop(str(uid), None)
        self.store.dirty = True
        self.journal("gban_add", 0, "", by, str(label), f"{uid}: {reason or 'через панель'}")
        return len(done)

    async def g5_unban_everywhere(self, uid: int, by: int) -> bool:
        entry = self.gbans().pop(str(uid), None)
        if entry is None:
            return False
        for cid in entry.get("ch", []):
            await self.call("unban_chat_member", cid, uid, only_if_banned=True)
            await asyncio.sleep(0.05)
        self.store.dirty = True
        self.journal("gban_del", 0, "", by, str(uid), "снят через панель")
        return True

    def cmd_allowed(self, uid: int) -> bool:
        if uid not in self.owners and str(uid) in self.gbans():
            return False
        return super().cmd_allowed(uid)

    # ═══════ «Дела»: запись, кнопки, отмена, апелляция ═══════
    _CASE_CATS = frozenset({"scam", "scam_ban", "suspicious", "memory", "puppet", "hacked"})

    async def apply(self, m, msg, v, name: str, rights: dict) -> None:
        if v.info.get("delay") or not feat("cases") or not BR.ok("cases"):
            return await super().apply(m, msg, v, name, rights)
        case = 0
        if v.alert or v.ban or v.mute_s or v.category in self._CASE_CATS:
            case = BR.run("cases", self._g5_case_open, msg, v, name, default=0) or 0
        tok = _CASE.set(case)
        try:
            await super().apply(m, msg, v, name, rights)
        finally:
            _CASE.reset(tok)
        if case:
            await BR.arun("appeal", self._g5_after_apply, m, msg, v, case)

    def _g5_case_open(self, msg, v, name: str) -> int:
        now = self.now()
        st = self.store.chats.get(msg.chat_id)
        rec = st.users.get(msg.user_id) if st is not None else None
        tier = self.eng.tier(rec, now) if rec is not None else "new"
        act = "бан" if v.ban else (f"мут {human_dur(v.mute_s)}" if v.mute_s else "удалено")
        sg = self.eng.g5_last_signals(msg.chat_id, msg.msg_id)
        why = (v.why() or v.category or "")[:100]
        if sg:
            why += " · " + ", ".join(n for n, _ in sg[:4])
        return self.g5b().cases.add(msg.chat_id, msg.user_id, name, v.category or "other", why, v.score, tier, act, 0,
                                    msg.text, msg.msg_id, now)

    async def alert(self, chat_id: int, text: str, markup=None) -> int:
        case = _CASE.get()
        if case and markup is None and feat("cases"):
            markup = self.g5_case_kb(case)
        return await super().alert(chat_id, text, markup)

    @staticmethod
    def g5_case_kb(case: int, extra_back: str = ""):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        rows = [[Btn(text="↩️ Отменить", callback_data=f"g5:u:{case}"), Btn(text="✅ Верно", callback_data=f"g5:k:{case}")]]
        if extra_back:
            rows.append([Btn(text="⬅ Назад", callback_data=extra_back)])
        return InlineKeyboardMarkup(inline_keyboard=rows)

    async def _g5_after_apply(self, m, msg, v, case: int) -> None:
        if not (feat("appeal") and v.delete and not v.ban and v.category in ("scam", "suspicious") and v.score < G.STRONG_SCAM):
            return
        cid, uid = msg.chat_id, msg.user_id
        if msg.sender_chat or uid <= 0 or not self.g5b().cfg(cid).get("appeal", 1):
            return
        st = self.store.chat(cid)
        if st.cfg.quiet:
            return
        now, x = self.now(), self.g5x
        if now - x["ap_user"].get((cid, uid), 0) < APPEAL_USER_GAP:
            return
        hist = [t for t in x["ap_chat"].get(cid, []) if now - t < 3600]
        if len(hist) >= APPEAL_CHAT_HOUR:
            return
        x["ap_user"][(cid, uid)] = now
        hist.append(now)
        x["ap_chat"][cid] = hist
        if len(x["ap_user"]) > 3000:
            x["ap_user"] = {k: t for k, t in x["ap_user"].items() if now - t < APPEAL_USER_GAP}
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        kb = InlineKeyboardMarkup(inline_keyboard=[[Btn(text="🙋 Это не спам", callback_data=f"g5:ap:{case}")]])
        extra = {}
        if getattr(m, "is_topic_message", False) and getattr(m, "message_thread_id", None):
            extra["message_thread_id"] = m.message_thread_id
        text = (f"🔎 {mention(uid, msg.name)}, ваше сообщение удалено автоматически как возможный спам. "
                "Если это ошибка — нажмите кнопку: владелец бота проверит.")
        sent = await self.call("send_message", cid, text, reply_markup=kb, disable_notification=True, **extra)
        if sent is not None:
            self.later(APPEAL_TTL, self.call, "delete_message", cid, sent.message_id)

    async def g5_undo(self, case_id: int, by: int) -> tuple:
        bk = self.g5b()
        case = bk.cases.get(case_id)
        if case is None:
            return False, "Дело уже стёрто из памяти (хранится 30 суток)."
        if case["st"] == "undone":
            return False, "Уже отменено."
        cid, uid = case["c"], case["u"]
        now = self.now()
        notes = []
        if case["a"].startswith("бан"):
            await self.call("unban_chat_member", cid, uid, only_if_banned=True)
            notes.append("разбанен (вернуться он может сам по ссылке)")
        await self.unrestrict(cid, uid)
        self.eng.forgive(cid, uid)
        try:
            bk.farm.forget(uid)
        except Exception:                                            # noqa: BLE001
            log.debug("farm.forget не удался", exc_info=True)
        notes.append("нарушения и память о его контактах сброшены, бот учтёт ошибку")
        try:
            if case.get("m"):
                self.eng.lp_teach(cid, case["m"], "h", by, "g5undo", now)
        except Exception:                                            # noqa: BLE001
            log.debug("lp_teach после отмены не удался", exc_info=True)
        st = self.store.chats.get(cid)
        if case.get("x") and st is not None and not st.cfg.quiet and case["u"] > 0:
            await self.call("send_message", cid, f"📎 Сообщение {mention(uid, case['n'])} возвращено — его удалили по ошибке:\n\n"
                                                 f"{esc(case['x'], 400)}", disable_notification=True)
            notes.append("текст возвращён в чат")
        bk.cases.set_state(case_id, "undone", by, now)
        self.journal("undo", cid, st.title if st else "", by, case["n"], f"отменено дело №{case_id}")
        self.store.dirty = True
        return True, "; ".join(notes)

    async def g5_mark_card(self, cb, suffix: str) -> None:
        msg = getattr(cb, "message", None)
        if msg is None:
            return
        base = getattr(msg, "html_text", None) or getattr(msg, "text", "") or ""
        await self.call("edit_message_text", (base + "\n\n" + suffix)[:4000], chat_id=msg.chat.id, message_id=msg.message_id)

    # ═══════ кнопки g5: ═══════
    async def on_callback(self, cb) -> None:
        data = getattr(cb, "data", "") or ""
        if not (ON.get("all") and data.startswith("g5:")):
            return await super().on_callback(cb)
        who = getattr(cb, "from_user", None)
        if who is not None and who.id not in self.owners and (who.id in self.banned_env or str(who.id) in self.gbans()):
            return await self._g5_ans(cb)
        try:
            await self.g5_button(cb, data.split(":"))
        except asyncio.CancelledError:
            raise
        except Exception:                                            # noqa: BLE001
            log.exception("кнопка 5.0 %r упала", data)
            await self._g5_ans(cb)

    async def g5_button(self, cb, p: list) -> None:
        uid = cb.from_user.id
        act = p[1] if len(p) > 1 else ""
        if act in ("u", "k"):
            if not self.g5_owner_ok(uid):
                return await self._g5_ans(cb, "Только для владельца бота.", True)
            return await self._g5_case_button(cb, act, p)
        if act == "ap":
            return await self._g5_appeal_button(cb, p)
        if act in ("rl", "rx"):
            return await self._g5_rules_button(cb, act, p)
        if act in ("br", "bd", "bm", "bb", "bB"):
            if not self.g5_owner_ok(uid):
                return await self._g5_ans(cb, "Только для владельца бота.", True)
            return await self._g5_ticket_button(cb, act, p)
        if act == "sz":
            return await self._g5_snooze_button(cb, p)
        if act == "pn":
            if not self.g5_owner_ok(uid):
                return await self._g5_ans(cb, "Только для владельца бота.", True)
            if not self.g5_panel_ok(uid):
                return await self._g5_ans(cb, "Панель закрыта. Откройте /panel и отправьте слово доступа.", True)
            self.panel_touch(uid)
            return await self._g5_panel_button(cb, p)
        await self._g5_ans(cb)

    async def _g5_case_button(self, cb, act: str, p: list) -> None:
        try:
            case_id = int(p[2])
        except (IndexError, ValueError):
            return await self._g5_ans(cb)
        bk, uid = self.g5b(), cb.from_user.id
        case = bk.cases.get(case_id)
        if case is None:
            return await self._g5_ans(cb, "Дело не найдено.", True)
        if act == "k":
            if case["st"] in ("open", "appeal"):
                bk.cases.set_state(case_id, "ok", uid, self.now())
                self.store.dirty = True
            await self.g5_mark_card(cb, "✅ Решение бота подтверждено.")
            return await self._g5_ans(cb, "Записал.")
        ok, note = await self.g5_undo(case_id, uid)
        if ok:
            await self.g5_mark_card(cb, "↩️ <b>Отменено.</b> " + esc(note, 300))
        return await self._g5_ans(cb, "Отменено." if ok else note, not ok)

    async def _g5_appeal_button(self, cb, p: list) -> None:
        try:
            case_id = int(p[2])
        except (IndexError, ValueError):
            return await self._g5_ans(cb)
        bk, uid = self.g5b(), cb.from_user.id
        case = bk.cases.get(case_id)
        if case is None:
            return await self._g5_ans(cb, "Уже недействительно.")
        if uid != case["u"]:
            return await self._g5_ans(cb, "Эта кнопка — для автора сообщения.")
        if case["st"] != "open":
            return await self._g5_ans(cb, "Уже рассмотрено.")
        st = self.store.chats.get(case["c"])
        text = (f"🙋 <b>Апелляция</b> · «{esc(st.title if st else case['c'], 50)}»\n{mention(case['u'], case['n'])} "
                f"(<code>{case['u']}</code>) говорит, что сообщение удалено зря.\n"
                f"Решение бота: {esc(case['a'], 30)} · оценка {case['s']} · {esc(case['w'], 160)}")
        if case.get("x"):
            text += f"\n\n«{esc(case['x'], 400)}»"
        n = await self.alert(case["c"], text, self.g5_case_kb(case_id))
        if not n:
            return await self._g5_ans(cb, "Не получилось передать: владелец бота не запускал его в личке.", True)
        bk.cases.set_state(case_id, "appeal", 0, self.now())
        self.store.dirty = True
        msg = getattr(cb, "message", None)
        if msg is not None:
            await self.call("edit_message_text", f"✅ {mention(uid, case['n'])}, передал владельцу. Решение придёт от него.",
                            chat_id=msg.chat.id, message_id=msg.message_id)
            self.later(45, self.call, "delete_message", msg.chat.id, msg.message_id)
        await self._g5_ans(cb, "Передал владельцу.")

    async def _g5_ticket_button(self, cb, act: str, p: list) -> None:
        bk, uid, now = self.g5b(), cb.from_user.id, self.now()
        tid = p[2] if len(p) > 2 else ""
        t = bk.inbox["t"].get(tid)
        if t is None:
            return await self._g5_ans(cb, "Запись уже удалена.", True)
        msg = getattr(cb, "message", None)

        async def refresh(note: str = "", kb=True):
            if msg is None:
                return
            extra = {"reply_markup": self.g5_ticket_kb(tid)} if kb else {}
            await self.call("edit_message_text", self.g5_ticket_text(tid, note), chat_id=msg.chat.id, message_id=msg.message_id,
                            **extra)
        if act == "bd":
            t["st"] = "done"
            self.store.dirty = True
            await refresh(kb=False)
            return await self._g5_ans(cb, "Отмечено.")
        if act == "br":
            self.g5x["wait"][uid] = {"kind": "reply", "tid": tid, "exp": now + WAIT_TTL}
            await self.dm(uid, f"✉️ Ответ на №{tid}: напишите текст одним сообщением (он уйдёт автору). Отмена: /cancel.")
            return await self._g5_ans(cb, "Жду ваш ответ в личке.")
        if act == "bm":
            note = await self.g5_mute_user(t["u"], INBOX_MUTES.get(p[3] if len(p) > 3 else "1d", 86400), uid)
            await refresh()
            return await self._g5_ans(cb, note)
        if not self.g5_panel_ok(uid):
            return await self._g5_ans(cb, "Бан доступен после входа в панель: /panel, затем слово доступа.", True)
        if act == "bb":
            from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
            if msg is not None:
                await self.call("edit_message_text", self.g5_ticket_text(tid, "⚠️ Забанить везде? Бот заблокирует человека во всех чатах "
                                                                              "и перестанет отвечать на его команды."),
                                chat_id=msg.chat.id, message_id=msg.message_id,
                                reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
                                    Btn(text="✅ Да, забанить", callback_data=f"g5:bB:{tid}"),
                                    Btn(text="✖ Нет", callback_data=f"g5:bd:{tid}")]]))
            return await self._g5_ans(cb)
        n = await self.g5_ban_everywhere(t["u"], t["n"], f"{INBOX_KINDS.get(t['k'], ('', ''))[1].lower()} №{tid}", uid)
        t["st"] = "done"
        await refresh(f"⛔ Забанен: чатов {n}" if n >= 0 else "Этого человека банить нельзя.", kb=False)
        await self._g5_ans(cb, "Готово." if n >= 0 else "Нельзя.")

    # ═══════ правила после проверки ═══════
    def g5_gate_on(self, cid: int) -> bool:
        st = self.store.chats.get(cid)
        return bool(feat("rules") and st is not None and st.cfg.rules and self.g5b().cfg(cid).get("gate", 1))

    async def captcha_pass(self, entry: dict) -> bool:
        cid = entry["chat"]
        if self.g5_gate_on(cid) and BR.ok("gate"):
            try:
                r = await self._g5_gate_start(entry)
            except asyncio.CancelledError:
                raise
            except Exception:                                        # noqa: BLE001
                BR.bad("gate")
                r = None
            if r is not None:
                return r
        return await super().captcha_pass(entry)

    async def _g5_gate_start(self, entry: dict):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        cid, uid = entry["chat"], entry["user"]
        name = entry.get("name", "")
        text = (f"📜 {mention(uid, name)}, последний шаг: прочитайте правила чата.\n"
                f"Нажмите кнопку — правила появятся здесь, и вы сможете писать. Времени: {RULES_WAIT // 60} мин.")
        kb = InlineKeyboardMarkup(inline_keyboard=[[Btn(text="📜 Показать правила", callback_data=f"g5:rl:{cid}:{uid}")]])
        mid = entry.get("msg_id") or 0
        ok = mid and await self.call("edit_message_text", text, chat_id=cid, message_id=mid, reply_markup=kb) is not None
        if not ok:
            sent = await self.call("send_message", cid, text, reply_markup=kb, disable_notification=True)
            if sent is None:
                return None
            if mid:
                self.deleter.add(cid, [mid])
            mid = sent.message_id
        now = self.now()
        self.store.captchas.pop(f"{cid}:{uid}", None)
        state = self.store.chat(cid)
        self.store.user(state, uid, now).verified = True
        self.store.bump(state, "captcha_ok")
        self.g5b().gate[f"{cid}:{uid}"] = {"mid": mid, "n": name[:40], "dl": round(now + RULES_WAIT), "t": round(now)}
        self.store.dirty = True
        return True

    async def _g5_rules_button(self, cb, act: str, p: list) -> None:
        try:
            cid, uid = int(p[2]), int(p[3])
        except (IndexError, ValueError):
            return await self._g5_ans(cb)
        if cb.from_user.id != uid:
            return await self._g5_ans(cb, "Эта кнопка — для другого участника.")
        bk, key = self.g5b(), f"{cid}:{uid}"
        if act == "rx":
            msg = getattr(cb, "message", None)
            if msg is not None:
                await self.call("delete_message", msg.chat.id, msg.message_id)
            bk.root.setdefault("del", {}).pop(f"{cid}:{msg.message_id}" if msg is not None else "", None)
            return await self._g5_ans(cb)
        g = bk.gate.get(key)
        st = self.store.chats.get(cid)
        if g is None or st is None:
            return await self._g5_ans(cb, "Уже недействительно.")
        if await self.unrestrict(cid, uid) is None:
            return await self._g5_ans(cb, "Не удалось снять ограничение. Обратитесь к администратору.", True)
        bk.gate.pop(key, None)
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        text = (f"📜 <b>Правила чата</b>\n{esc(st.cfg.rules, G.RULES_MAX)}\n\n{mention(uid, g.get('n', ''))}, спасибо — "
                f"теперь вы можете писать. <i>Это сообщение исчезнет через {RULES_SHOW_TTL // 60} мин.</i>")
        kb = InlineKeyboardMarkup(inline_keyboard=[[Btn(text="✅ Понятно", callback_data=f"g5:rx:{cid}:{uid}")]])
        await self.call("edit_message_text", text, chat_id=cid, message_id=g["mid"], reply_markup=kb)
        bk.root.setdefault("del", {})[f"{cid}:{g['mid']}"] = round(self.now() + RULES_SHOW_TTL)
        self.store.bump(st, "rules_read")
        self.store.dirty = True
        await self.greet(cid, uid, g.get("n", ""))
        await self._g5_ans(cb, "Правила открыты.")

    async def on_leave(self, chat, uid: int) -> None:
        g = self.g5b().gate.pop(f"{chat.id}:{uid}", None)
        if g:
            self.deleter.add(chat.id, [g["mid"]])
            self.store.dirty = True
        await super().on_leave(chat, uid)

    async def tick(self, now: float | None = None) -> None:
        await super().tick(now)
        if ON.get("all"):
            await BR.arun("tick", self._g5_tick, self.now() if now is None else now)

    async def _g5_tick(self, now: float) -> None:
        bk = self.g5b()
        for key, g in list(bk.gate.items()):
            if g["dl"] > now:
                continue
            bk.gate.pop(key, None)
            cid, uid = (int(x) for x in key.split(":"))
            st = self.store.chats.get(cid)
            hot = st is not None and (st.cfg.fort_on or self.eng.raid_active(cid, now) or self.eng.strict_active(cid, now))
            if not hot and not _flag("GUARD5_RULES_STRICT", False):
                # человек прошёл капчу и просто не нажал вторую кнопку: пускаем, правила доступны по /rules
                await self.unrestrict(cid, uid)
                self.deleter.add(cid, [g["mid"]])
                self.journal("allow", cid, st.title if st else "", uid, g.get("n", ""), "не открыл правила: допущен без них")
                self.store.dirty = True
                continue
            await self.kick(cid, uid, seconds=600)
            self.deleter.add(cid, [g["mid"]])
            self.journal("capfail", cid, st.title if st else "", uid, g.get("n", ""), "не открыл правила: убран на 10 мин")
            self.store.dirty = True
        dels = bk.root.get("del")
        if dels:
            due = [k for k, t in dels.items() if t <= now]
            for k in due:
                dels.pop(k, None)
                cid, mid = (int(x) for x in k.split(":"))
                await self.call("delete_message", cid, mid)
            if due:
                self.store.dirty = True


# ═══════════════════════════════ охрана, часть 2: вход, «второй взгляд», команды ═══════════════════════════════
_OUT_HOOK = contextvars.ContextVar("g5_out_hook", default=None)
SNOOZE = (("+15 мин", 900), ("+1 ч", 3600), ("завтра", 86400))


class GuardMix2:
    """Вторая половина GuardMix (разнесена только ради читаемости файла)."""

    # ═══════ «Второй взгляд»: сеть до решения ═══════
    async def _g5_preflight(self, m) -> None:
        chat = m.chat
        if getattr(chat, "type", "") not in G.GROUP_TYPES or getattr(m, "edit_date", None):
            return
        u = getattr(m, "from_user", None)
        if u is None or u.is_bot:
            return
        text = getattr(m, "text", None) or getattr(m, "caption", None) or ""
        ents = list(getattr(m, "entities", None) or []) + list(getattr(m, "caption_entities", None) or [])
        if len(text) < 6 and not ents:
            return
        if "." not in text and not any(str(getattr(getattr(e, "type", ""), "value", getattr(e, "type", ""))) in ("text_link", "url")
                                       for e in ents):
            return
        if not self.chat_ok(chat.id):
            return
        st = self.store.chats.get(chat.id)
        if st is None or not st.cfg.enabled or not st.cfg.scam or not st.cfg.smart_links:
            return
        uid, now = u.id, self.now()
        if self.is_trusted(uid):
            return
        rec = st.users.get(uid)
        if rec is not None and self.eng.tier(rec, now) != "new":
            return
        if uid in await self.admins(chat.id):
            return
        msg = G.to_msg(m, uid=uid, name=G.user_name(u))
        items = []
        for x in G.extract_urls(msg.text, msg.ents, st.cfg):
            if x.kind in ("shortener", "invite", "tg_channel", "tg_bot", "unknown"):
                items.append((x.kind, x.host, x.reg, x.raw))
        if not items:
            return
        facts = await self.g5_intel.investigate(items[:3], G.SHORTENERS, LOOK_DEADLINE)
        if not facts:
            return
        sigs = facts_to_signals(facts, lambda t: G.analyze_text(t, (), None), now)
        if sigs:
            self.eng.g5_inject(chat.id, m.message_id, sigs, now)
            self.eng._g5s()["hits"] += 1

    # ═══════ вход: «ферма», тревожный вход ═══════
    async def on_join(self, chat, user, join_msg_id: int | None = None) -> None:
        if ON.get("all") and not getattr(user, "is_bot", False):
            BR.run("join", self._g5_on_join, chat, user)
        return await super().on_join(chat, user, join_msg_id)

    def _g5_on_join(self, chat, user) -> None:
        now, x = self.now(), self.g5x
        key = (chat.id, user.id)
        if now - x["joined"].get(key, 0) < 60:
            return
        x["joined"][key] = now
        if len(x["joined"]) > 3000:
            x["joined"] = {k: t for k, t in x["joined"].items() if now - t < 120}
            x["farm_n"] = {k: v for k, v in x["farm_n"].items() if k in x["joined"]}
        st = self.store.chats.get(chat.id)
        if st is None or not st.cfg.enabled:
            return
        eng = self.eng
        keys = farm_keys(f"{getattr(user, 'first_name', '') or ''} {getattr(user, 'last_name', '') or ''}",
                         getattr(user, "username", "") or "")
        n = self.g5b().farm.hits(keys, user.id, now) if keys else 0
        if n >= 2:
            x["farm_n"][key] = n
            eng.g5_mark_farm(chat.id, user.id, now, n)
            eng.ap_pulse(chat.id, user.id, "farm", now=now)
        if eng.raid_active(chat.id, now) or eng.strict_active(chat.id, now) or st.cfg.fort_on:
            eng.g5_mark_prob(chat.id, user.id, now)

    def captcha_plan(self, chat, user, state, now: float) -> dict:
        plan = super().captcha_plan(chat, user, state, now)
        if ON.get("all") and state.cfg.captcha_smart:
            n = self.g5x["farm_n"].get((chat.id, user.id), 0)
            if n >= 2:
                plan = dict(plan)
                plan["skip"] = False
                plan["level"] = "hard" if n >= 3 or plan.get("level") == "hard" else "normal"
                plan["why"] = list(plan.get("why", [])) + ["имя как у недавно забаненных аккаунтов (ферма)"]
                plan["risk"] = max(plan.get("risk", 0.0), 3.0 if n >= 3 else 1.0)
        return plan

    async def on_join_request(self, ev) -> None:
        if feat("joinreq") and BR.ok("joinreq"):
            try:
                if await self._g5_join_request(ev):
                    return
            except asyncio.CancelledError:
                raise
            except Exception:                                        # noqa: BLE001
                BR.bad("joinreq")
        await super().on_join_request(ev)

    async def _g5_join_request(self, ev) -> bool:
        chat, user = ev.chat, getattr(ev, "from_user", None)
        if user is None or getattr(chat, "type", "") not in G.GROUP_TYPES or not self.chat_ok(chat.id) or user.is_bot:
            return False
        state = self.store.chat(chat.id, chat.title or "")
        cfg, uid, now = state.cfg, user.id, self.now()
        if not cfg.enabled or not cfg.scam or uid in self.owners or self.is_trusted(uid):
            return False
        keys = farm_keys(G.user_name(user), getattr(user, "username", "") or "")
        if keys and self.g5b().farm.hits(keys, uid, now) >= 2:
            self.eng.g5_mark_farm(chat.id, uid, now)
        bio = (getattr(ev, "bio", None) or "").strip()
        if len(bio) < 8:
            return False
        a = G.analyze_text(bio, (), cfg)
        if not (a.raw >= 4.0 and (a.has_contact or a.hard >= 1.0)):
            return False
        top = ", ".join(s[2] for s in sorted(a.signals, key=lambda s: -s[1])[:2])
        if await self.call("decline_chat_join_request", chat.id, uid) is None:
            return False
        self.store.bump(state, "join_decline")
        self.journal("join_decline", chat.id, chat.title or "", uid, G.user_name(user), "в «о себе» реклама/контакт")
        await self.plus_log(chat.id, f"🛡 <b>{esc(chat.title, 60)}</b>\nЗаявка {mention(uid, G.user_name(user))} (<code>{uid}</code>) "
                                     f"отклонена: в «о себе» {esc(top, 140)}")
        return True

    async def fort_feed(self, chat_id: int, uid: int, kind: str) -> None:
        await super().fort_feed(chat_id, uid, kind)
        if kind == "react" and ON.get("all") and feat("joinreq") and uid > 0:
            x = self.g5x
            if not hasattr(self.bot, "delete_all_message_reactions"):
                if not x.get("react_warned"):
                    x["react_warned"] = True
                    log.warning("чистка реакций спамера выключена: установленный aiogram слишком старый "
                                "(нет deleteAllMessageReactions). Обновите: pip install -U aiogram")
                return
            try:
                if not (await self.rights(chat_id)).get("delete"):
                    if not x.get("react_rights_warned"):
                        x["react_rights_warned"] = True
                        log.warning("чистка реакций спамера не работает в чате %s: у бота нет права удалять сообщения", chat_id)
                    return
                await self.call("delete_all_message_reactions", chat_id, user_id=uid)
            except asyncio.CancelledError:
                raise
            except Exception:                                        # noqa: BLE001
                log.debug("delete_all_message_reactions не удался", exc_info=True)

    # ═══════ правила ═══════
    async def cmd_setrules(self, m, args):
        if not feat("rules") or not self.in_group(m):
            return await super().cmd_setrules(m, args)
        a = args.strip()
        head, _, tail = a.lower().partition(" ")
        if head in ("gate", "шлюз", "кнопка"):
            if not await self.need_admin(m):
                return
            self.cleanup(m)
            v = tail.strip()
            c5 = self.g5b().cfg(m.chat.id)
            if v in ("on", "вкл", "1", "да"):
                c5["gate"] = 1
            elif v in ("off", "выкл", "0", "нет"):
                c5["gate"] = 0
            else:
                return await self.out(m, "/setrules gate on|off — показывать ли правила кнопкой после проверки при входе.", ttl=25)
            self.store.dirty = True
            return await self.out(m, "📜 Правила после проверки: " + ("включены — новичок прочитает их до того, как сможет писать."
                                                                     if c5["gate"] else "выключены."), ttl=30)
        cfg = self.store.chat(m.chat.id, m.chat.title or "").cfg
        before = cfg.rules
        await super().cmd_setrules(m, args)
        if cfg.rules and cfg.rules != before:
            c5 = self.g5b().cfg(m.chat.id)
            if c5.get("gate", 1):
                tail = ("После проверки при входе новичок увидит кнопку «Показать правила», а сами правила исчезнут через "
                        f"{RULES_SHOW_TTL // 60} мин. Отключить: /setrules gate off." if cfg.captcha else
                        "Они будут показываться после проверки при входе — сейчас проверка выключена, включите её в /guard.")
                await self.out(m, "📜 " + tail, ttl=45)

    # ═══════ /remind: «завтра в 10», «каждый день в 9:00», кнопки «ещё раз» ═══════
    async def cmd_remind(self, m, args):
        if not feat("repeat") or not BR.ok("remind"):
            return await super().cmd_remind(m, args)
        try:
            await self._g5_remind(m, args)
        except asyncio.CancelledError:
            raise
        except Exception:                                            # noqa: BLE001
            BR.bad("remind")
            await super().cmd_remind(m, args)

    async def _g5_remind(self, m, args: str) -> None:
        if m.from_user is None:
            return
        uid, cid, now = m.from_user.id, m.chat.id, self.now()
        rems = self.store.meta.setdefault("reminders", [])
        mine = sorted((r for r in rems if r["u"] == uid and r["c"] == cid), key=lambda r: r["at"])
        a = args.strip()
        low = a.lower()
        if low in ("", "list", "список"):
            if not mine:
                return await self.out(m, "/remind <i>30м текст</i> · <i>завтра в 10 текст</i> · <i>в пятницу в 18:30 текст</i> · "
                                         "<i>каждый день в 9:00 текст</i>. Список: /remind list; убрать: /remind del <i>номер</i>.", ttl=40)
            lines = []
            for i, r in enumerate(mine, 1):
                rp = f" 🔁 каждые {human_dur(r['rp'])}" if r.get("rp") else ""
                lines.append(f"{i}. ⏰ {fmt_when(r['at'], self.tz_h)} (через {human_dur(max(0, r['at'] - now))}){rp}: {esc(r['t'], 60)}")
            return await self.out(m, "<b>Ваши напоминания</b>\n" + "\n".join(lines) +
                                  "\n<i>/remind del номер — убрать одно; /remind off — все.</i>", ttl=60)
        if low in ("off", "выкл", "clear"):
            self.store.meta["reminders"] = [r for r in rems if r not in mine]
            self.store.dirty = True
            return await self.out(m, "Напоминания стёрты.", ttl=15)
        mm = re.fullmatch(r"(?:del|удалить|убрать|-)\s*(\d{1,2})", low)
        if mm:
            i = int(mm.group(1))
            if not 1 <= i <= len(mine):
                return await self.out(m, "Нет напоминания с таким номером. Список: /remind list.", ttl=15)
            rems.remove(mine[i - 1])
            self.store.dirty = True
            return await self.out(m, "Убрано.", ttl=15)
        w = parse_when(a, now, self.tz_h)
        text = w["rest"] if w else ""
        if w and not text:
            rm = getattr(m, "reply_to_message", None)
            text = ((getattr(rm, "text", None) or getattr(rm, "caption", None) or "") if rm is not None else "").strip()
        if not w or not text:
            return await self.out(m, "/remind <i>30м текст</i> · <i>завтра в 10 текст</i> · <i>в пятницу в 18:30 текст</i> · "
                                     "<i>каждый день в 9:00 текст</i>. Можно ответом на сообщение: /remind 2ч.", ttl=30)
        if len(mine) >= max(G.REMIND_PER_USER, 6):
            return await self.out(m, f"Лимит напоминаний: {max(G.REMIND_PER_USER, 6)} на человека. Уберите лишнее: /remind list.", ttl=20)
        rec = {"c": cid, "u": uid, "n": G.user_name(m.from_user)[:40], "at": w["at"], "t": text.strip()[:200],
               "th": self.thread_of(m) or 0}
        if w["repeat"]:
            rec["rp"] = int(w["repeat"])
            rec["end"] = round(now + 366 * 86400)
        rems.append(rec)
        self.store.dirty = True
        tail = f", а потом каждые {human_dur(w['repeat'])}" if w["repeat"] else ""
        await self.out(m, f"⏰ Напомню {fmt_when(w['at'], self.tz_h)} (через {human_dur(max(0, w['at'] - now))}){tail}: "
                          f"«{esc(text, 80)}»", ttl=30)

    async def fire_reminders(self, now: float) -> None:
        if not feat("repeat") or not BR.ok("remind"):
            return await super().fire_reminders(now)
        rems = self.store.meta.get("reminders")
        if not rems:
            return
        due = [r for r in rems if r["at"] <= now]
        if not due:
            return
        keep = [r for r in rems if r["at"] > now]
        for r in due:
            rp = r.get("rp")
            if rp and r.get("end", 0) > now:
                nxt = r["at"]
                while nxt <= now:
                    nxt += rp
                if nxt <= r["end"]:
                    keep.append({**r, "at": nxt})
        self.store.meta["reminders"] = keep
        self.store.dirty = True
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        bk = self.g5b()
        snz = bk.root.setdefault("snz", {})
        for k in [k for k, v in snz.items() if now - v["t"] > 86400]:
            snz.pop(k, None)
        for r in due:
            tok = format(int(now * 1000) % (36 ** 6), "x") + format(abs(hash((r["u"], r["t"]))) % 4096, "x")
            snz[tok] = {"c": r["c"], "u": r["u"], "n": r.get("n", ""), "t": round(now), "x": r["t"][:200], "th": r.get("th", 0)}
            kb = InlineKeyboardMarkup(inline_keyboard=[[Btn(text=lab, callback_data=f"g5:sz:{tok}:{sec}") for lab, sec in SNOOZE]])
            extra = {"message_thread_id": r["th"]} if r.get("th") else {}
            sent = await self.call("send_message", r["c"], f"⏰ {mention(r['u'], r.get('n', ''))}: {esc(r['t'], 200)}",
                                   reply_markup=kb, **extra)
            if sent is not None:
                self.later(900, self.call, "delete_message", r["c"], sent.message_id)

    async def _g5_snooze_button(self, cb, p: list) -> None:
        try:
            tok, sec = p[2], int(p[3])
        except (IndexError, ValueError):
            return await self._g5_ans(cb)
        snz = self.g5b().root.setdefault("snz", {})
        r = snz.get(tok)
        if r is None:
            return await self._g5_ans(cb, "Это напоминание уже устарело.")
        if cb.from_user.id != r["u"]:
            return await self._g5_ans(cb, "Это напоминание — для другого участника.")
        if sec not in (s for _, s in SNOOZE):
            return await self._g5_ans(cb)
        rems = self.store.meta.setdefault("reminders", [])
        if sum(1 for x in rems if x["u"] == r["u"] and x["c"] == r["c"]) >= max(G.REMIND_PER_USER, 6):
            return await self._g5_ans(cb, "Слишком много напоминаний: уберите лишнее (/remind list).", True)
        at = self.now() + sec
        rems.append({"c": r["c"], "u": r["u"], "n": r["n"], "at": at, "t": r["x"], "th": r.get("th", 0)})
        self.store.dirty = True
        msg = getattr(cb, "message", None)
        if msg is not None:
            await self.call("delete_message", msg.chat.id, msg.message_id)
        await self._g5_ans(cb, f"Напомню {fmt_when(at, self.tz_h)}.")

    # ═══════ /repeat: дни недели, окно времени, «до даты», «не кричит в пустоту» ═══════
    async def cmd_repeat(self, m, args):
        if not feat("repeat") or not BR.ok("repeat"):
            return await super().cmd_repeat(m, args)
        tok, _, rest = args.strip().partition(" ")
        mins = parse_minutes_v5(tok) if tok else None
        opts, tail = parse_repeat_opts(rest.strip(), self.now(), self.tz_h) if mins else ({}, rest)
        if not opts:
            return await super().cmd_repeat(m, args)
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        text = self._text_arg(m, tail.strip())
        if not text:
            return await self.out(m, "После условий нужен текст объявления: /repeat <i>6ч пн-пт 10-22 текст</i>.", ttl=25)
        if mins < G.REPEAT_MIN_MIN:
            return await self.out(m, f"Слишком часто: минимум раз в {G.REPEAT_MIN_MIN} минут.", ttl=20)
        reps = self.store.meta.setdefault("repeats", [])
        if sum(1 for r in reps if r["c"] == m.chat.id) >= G.REPEAT_PER_CHAT:
            return await self.out(m, f"Слишком много объявлений (максимум {G.REPEAT_PER_CHAT} на чат). Уберите лишние: /unrepeat.", ttl=20)
        seq = self.store.meta["repeat_seq"] = int(self.store.meta.get("repeat_seq", 0)) + 1
        now = self.now()
        first = repeat_gate(opts, now, self.tz_h, now + 1, 0)       # первое — сразу, если условия позволяют
        at = now if first[0] == "go" else (first[1] if first[0] == "defer" else now)
        reps.append({"id": seq, "c": m.chat.id, "ev": min(mins, G.REPEAT_MAX_MIN), "at": at, "t": text[:G.REPEAT_TEXT_MAX],
                     "th": self.thread_of(m) or 0, "mid": 0, "f": 0, "g5": opts})
        self.store.dirty = True
        await self.out(m, f"📣 Объявление №{seq}: каждые {human_dur(min(mins, G.REPEAT_MAX_MIN) * 60)}"
                          f" · {describe_repeat_opts(opts)}. Первое — {fmt_when(at, self.tz_h) if at > now + 5 else 'сейчас'}.", ttl=40)

    async def cmd_repeats(self, m, args):
        if not feat("repeat") or not BR.ok("repeat"):
            return await super().cmd_repeats(m, args)
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        mine = [r for r in self.store.meta.get("repeats", []) if r["c"] == m.chat.id]
        if not mine:
            return await self.out(m, "Регулярных объявлений нет. Добавить: /repeat <i>6ч текст</i>.", ttl=20)
        now = self.now()
        lines = []
        for r in mine:
            extra = f" · {describe_repeat_opts(r['g5'])}" if r.get("g5") else ""
            lines.append(f"№{r['id']} · каждые {human_dur(r['ev'] * 60)}, следующее {fmt_when(r['at'], self.tz_h)} "
                         f"(через {human_dur(max(0, r['at'] - now))}){extra}: {esc(r['t'], 60)}")
        await self.out(m, "<b>Регулярные объявления</b>\n" + "\n".join(lines), ttl=90)

    async def _plus_tick(self, now: float) -> None:
        if feat("repeat") and BR.ok("repeat"):
            await BR.arun("repeat", self._g5_repeats, now)
        await super()._plus_tick(now)

    async def _g5_repeats(self, now: float) -> None:
        reps = self.store.meta.get("repeats")
        for r in list(reps or []):
            o = r.get("g5")
            if not o or r["at"] > now or not self.chat_ok(r["c"]):
                continue
            st = self.store.chats.get(r["c"])
            last_human = max((u.last_seen for u in st.users.values()), default=0.0) if st is not None else 0.0
            dec = repeat_gate(o, now, self.tz_h, last_human, r.get("lp", 0.0))
            self.store.dirty = True
            if dec[0] == "drop":
                reps.remove(r)
                continue
            if dec[0] == "defer":
                r["at"] = dec[1]
                continue
            r["at"] = now + r["ev"] * 60
            if r.get("mid"):
                await self.call("delete_message", r["c"], r["mid"])
            extra = {"message_thread_id": r["th"]} if r.get("th") else {}
            sent = await self.call("send_message", r["c"], esc(r["t"], G.REPEAT_TEXT_MAX), disable_notification=True, **extra)
            if sent is None:
                r["f"] = r.get("f", 0) + 1
                if r["f"] >= 5:
                    reps.remove(r)
                continue
            r["mid"], r["f"], r["lp"] = sent.message_id, 0, now
            if o.get("pin"):
                await self.call("pin_chat_message", r["c"], sent.message_id, disable_notification=True)
            if o.get("left") is not None:
                o["left"] -= 1
                if o["left"] <= 0:
                    reps.remove(r)

    # ═══════ жалобы: оценка бота и репутация ═══════
    async def _send_review(self, m, r, rep: dict) -> None:
        if feat("reports") and BR.ok("reports"):
            try:
                text = getattr(r, "text", None) or getattr(r, "caption", None) or ""
                if text:
                    cfg = self.store.chat(m.chat.id).cfg
                    a = G.analyze_text(text, (), cfg)
                    if a.raw >= 2.5:
                        top = ", ".join(s[2] for s in sorted(a.signals, key=lambda s: -s[1])[:2])
                        note = f"бот и сам подозревает спам (оценка {a.raw:g}: {top[:120]})"
                    elif a.raw < 1.0:
                        note = f"бот не нашёл признаков нарушения (оценка {a.raw:g})"
                    else:
                        note = ""
                    if note:
                        rep["note"] = (rep.get("note", "") + "; " if rep.get("note") else "") + note
            except Exception:                                        # noqa: BLE001
                BR.bad("reports")
        await super()._send_review(m, r, rep)

    async def on_review_button(self, cb) -> None:
        rep = None
        try:
            _, cid, mid, _u, act = (cb.data or "").split(":")
            if feat("reports") and self.g5_owner_ok(cb.from_user.id):
                rep = self.reports.get((int(cid), int(mid)))
        except (ValueError, AttributeError):
            act = ""
        by = dict(rep["by"]) if rep else {}
        await super().on_review_button(cb)
        if by and act in ("d", "m", "x"):
            BR.run("reports", self._g5_rep_note, by, act in ("d", "m"))

    def _g5_rep_note(self, by: dict, ok: bool) -> None:
        rb, now = self.g5b().rep, self.now()
        for u in by:
            rb.note(u, ok, now)
        self.store.dirty = True

    # ═══════ дописки к ответам: /status, /me, итоги дня ═══════
    async def out(self, m, text: str, ttl: float = 0, markup=None, reply: bool = False):
        hook = _OUT_HOOK.get()
        if hook is not None:
            try:
                text = hook(text)
            except Exception:                                        # noqa: BLE001
                log.debug("дописка к ответу не удалась", exc_info=True)
        return await super().out(m, text, ttl=ttl, markup=markup, reply=reply)

    def g5_stat_line(self, cid: int, now: float) -> str:
        bk = self.g5b()
        s = bk.cases.stats(cid, now - 7 * 86400)
        bits = []
        if s.get("all"):
            judged = s.get("ok", 0) + s.get("undone", 0)
            acc = f", точность по проверенным {round(100 * s.get('ok', 0) / judged)}%" if judged >= 5 else ""
            bits.append(f"решений за 7 дней: {s['all']} (отменено {s.get('undone', 0)}, подтверждено {s.get('ok', 0)}{acc})")
        known = len(bk.known.d.get(str(cid), {}))
        if known:
            bits.append(f"знакомых доменов: {known}")
        gate = "вкл" if self.g5_gate_on(cid) else ("выкл" if self.store.chats[cid].cfg.rules else "нет правил")
        bits.append(f"правила после проверки: {gate}")
        bits.append("сеть: " + ("вкл" if feat("net") else "выкл"))
        return "🧬 5.0: " + " · ".join(bits)

    async def cmd_status(self, m, args):
        if not feat("cases") or not self.in_group(m):
            return await super().cmd_status(m, args)
        line = self.g5_stat_line(m.chat.id, self.now()) if m.chat.id in self.store.chats else ""
        tok = _OUT_HOOK.set(lambda t: t + "\n" + line if line and t.startswith("<b>Состояние:") else t)
        try:
            await super().cmd_status(m, args)
        finally:
            _OUT_HOOK.reset(tok)

    async def cmd_me(self, m, args):
        if not feat("cases") or not self.in_group(m) or m.from_user is None:
            return await super().cmd_me(m, args)
        r = getattr(m, "reply_to_message", None)
        ru = getattr(r, "from_user", None) if r is not None else None
        own = ru is None or ru.id == m.from_user.id
        target = m.from_user if own else ru
        extra = ""
        if own or m.from_user.id in self.owners:
            rows = self.g5b().cases.of_user(m.chat.id, target.id, self.now() - 14 * 86400, 3)
            if rows:
                extra = "\n<b>Решения бота за 14 дней</b>\n" + "\n".join(
                    f"• {self.fmt_when(c['t'])} — {esc(c['a'], 20)}" + (" (отменено)" if c["st"] == "undone" else "") +
                    (f": {esc(c['w'], 70)}" if own or m.from_user.id in self.owners else "") for _, c in rows)
        tok = _OUT_HOOK.set(lambda t: t + extra if extra and t.startswith("<b>Карточка участника") else t)
        try:
            await super().cmd_me(m, args)
        finally:
            _OUT_HOOK.reset(tok)

    def digest_text(self, st, now: float) -> str:
        text = super().digest_text(st, now)
        if feat("cases"):
            try:
                s = self.g5b().cases.stats(st.chat_id, now - 86400)
                if s.get("all"):
                    text += (f"\n🧬 Решений бота за сутки: {s['all']} · отменено вами: {s.get('undone', 0)} · "
                             f"подтверждено: {s.get('ok', 0)} · апелляций: {s.get('appeal', 0)}")
            except Exception:                                        # noqa: BLE001
                log.debug("итоги дня: строка 5.0 не получилась", exc_info=True)
        return text


# ═══════════════════════════════ панель владельца: «Баги и отзывы», «5.0» ═══════════════════════════════
class GuardPanel5:
    """Экраны панели (только владельцам, только после слова доступа) — кнопки с префиксом g5:pn:."""

    def panel_main(self, uid: int, chats: list, page: int = 0):
        text, kb = super().panel_main(uid, chats, page)
        if not (ON.get("all") and uid in self.owners):
            return text, kb
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        new = sum(1 for t in self.g5b().inbox["t"].values() if t["st"] == "new")
        rows = list(kb.inline_keyboard)
        rows.insert(max(0, len(rows) - 1), [Btn(text="🐞 Баги и отзывы" + (f" ({new})" if new else ""), callback_data="g5:pn:in"),
                                             Btn(text="🧬 5.0", callback_data="g5:pn:ft")])
        return text, InlineKeyboardMarkup(inline_keyboard=rows)

    async def panel_chat(self, cid: int, uid: int = 0):
        text, kb = await super().panel_chat(cid, uid)
        if not (ON.get("all") and uid in self.owners):
            return text, kb
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        rows = list(kb.inline_keyboard)
        rows.insert(max(0, len(rows) - 1), [Btn(text="🧬 5.0: правила, апелляция", callback_data=f"g5:pn:ch:{cid}")])
        return text, InlineKeyboardMarkup(inline_keyboard=rows)

    # ---- экраны ----
    def g5_scr_inbox(self):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        bk, now = self.g5b(), self.now()
        tk = bk.inbox["t"]
        new = sum(1 for t in tk.values() if t["st"] == "new")
        muted = sum(1 for u, until in bk.inbox["mute"].items() if until == 0 or until > now)
        banned = len(self.gbans())
        off = bk.inbox["off"]
        lines = ["<b>🐞 Баги и отзывы</b>",
                 f"Новых: <b>{new}</b> · всего: {len(tk)} · замучено: {muted} · забанено везде: {banned}",
                 f"Приём багов: {'выкл' if off.get('bug') else 'вкл'} · отзывов: {'выкл' if off.get('feedback') else 'вкл'}",
                 "<i>Люди пишут /bug и /feedback — слова не фильтруются. Мут: человек не сможет присылать вам баги и отзывы. "
                 "Бан: бот заблокирует его во всех чатах и перестанет отвечать.</i>"]
        rows = []
        for tid, t in sorted(tk.items(), key=lambda kv: -kv[1]["t"])[:6]:
            icon = INBOX_KINDS.get(t["k"], ("•", ""))[0]
            mark = "🆕 " if t["st"] == "new" else ""
            rows.append([Btn(text=f"{mark}{icon} №{tid} {t['n'][:14]}: {t['x'][:22]}", callback_data=f"g5:pn:t:{tid}")])
        rows.append([Btn(text=f"🐞 Баги: {'выкл' if off.get('bug') else 'вкл'}", callback_data="g5:pn:tg:bug"),
                     Btn(text=f"💬 Отзывы: {'выкл' if off.get('feedback') else 'вкл'}", callback_data="g5:pn:tg:feedback")])
        rows.append([Btn(text="🔇 Замутить по id", callback_data="g5:pn:mi"), Btn(text="⛔ Забанить по id", callback_data="g5:pn:bi")])
        rows.append([Btn(text="📋 Мут и баны", callback_data="g5:pn:ls")])
        rows.append([Btn(text="⬅ Назад", callback_data="ap:m:0")])
        return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows)

    def g5_scr_list(self):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        bk, now = self.g5b(), self.now()
        lines = ["<b>📋 Мут и баны</b>"]
        rows = []
        mutes = [(u, t) for u, t in bk.inbox["mute"].items() if t == 0 or t > now]
        if mutes:
            lines.append("<b>Замучены</b> (баги и отзывы)")
        for u, until in sorted(mutes, key=lambda x: x[1])[:8]:
            lines.append(f"• <code>{u}</code> — " + ("навсегда" if until == 0 else "до " + self.fmt_when(until)))
            rows.append([Btn(text=f"🔊 Снять мут {u}", callback_data=f"g5:pn:um:{u}")])
        bans = sorted(self.gbans().items(), key=lambda kv: -kv[1].get("t", 0))[:8]
        if bans:
            lines.append("<b>Забанены везде</b>")
        for u, e in bans:
            lines.append(f"• <code>{esc(u, 20)}</code> {esc(e.get('n', ''), 24)} — {esc(e.get('r') or 'без причины', 40)}")
            rows.append([Btn(text=f"✅ Разбанить {u}", callback_data=f"g5:pn:ub:{u}")])
        if not mutes and not bans:
            lines.append("Пусто.")
        rows.append([Btn(text="⬅ Назад", callback_data="g5:pn:in")])
        return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows)

    def g5_scr_features(self):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        bk, now, eng = self.g5b(), self.now(), self.eng
        s = {}
        for cid in self.store.chats:
            for k, v in bk.cases.stats(cid, now - 7 * 86400).items():
                s[k] = s.get(k, 0) + v
        it = self.g5_intel
        st = eng._g5s()
        off = [n for n in ("signals", "post", "front", "look", "cases", "appeal", "gate", "tick", "join", "joinreq", "repeat", "remind",
                           "reports") if not BR.ok(n)]
        lines = [f"<b>🧬 Guard {V5_VERSION}</b>",
                 f"Дела за 7 дней: {s.get('all', 0)} · отменено {s.get('undone', 0)} · подтверждено {s.get('ok', 0)} · "
                 f"апелляций {s.get('appeal', 0)}",
                 f"Второй взгляд: сеть {'вкл' if feat('net') else 'выкл'} · запросов {it.calls} · сработал на {st['hits']} сообщениях"
                 + (" · пауза (сеть недоступна)" if it.paused > now else ""),
                 f"Знакомые домены: чатов {len(bk.known.d)}, доменов {sum(len(v) for v in bk.known.d.values())} · "
                 f"смягчений ссылок: {st['soft']}",
                 f"Ферма: запомнено шаблонов имён {len(bk.farm.d)}",
                 f"Репутация жалобщиков: {len(bk.rep.d)} · правила прочитали при входе: "
                 f"{sum(c.get('rules_read', 0) for ch in self.store.chats.values() for c in ch.stats.values())}"]
        if off:
            lines.append("⚠️ Узлы, временно отключённые после сбоев: " + ", ".join(off))
        rows = [[Btn(text="📋 Последние дела", callback_data="g5:pn:cs"), Btn(text="🗂 Чаты 5.0", callback_data="g5:pn:cl")],
                [Btn(text="🐞 Баги и отзывы", callback_data="g5:pn:in")],
                [Btn(text="⬅ Назад", callback_data="ap:m:0")]]
        return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows)

    def g5_scr_cases(self, note: str = ""):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        bk = self.g5b()
        rows_c = sorted(((int(k), v) for k, v in bk.cases.c.items()), key=lambda kv: -kv[1]["t"])[:8]
        lines = ["<b>📋 Последние дела</b>"] + ([note] if note else [])
        rows = []
        if not rows_c:
            lines.append("Решений пока нет.")
        for k, c in rows_c:
            st = self.store.chats.get(c["c"])
            mark = {"undone": " ↩️", "ok": " ✅", "appeal": " 🙋"}.get(c["st"], "")
            lines.append(f"№{k} · {self.fmt_when(c['t'])} · «{esc(st.title if st else c['c'], 18)}» · {esc(c['n'], 16)} — "
                         f"{esc(c['a'], 18)}{mark}")
            if c["st"] in ("open", "appeal"):
                rows.append([Btn(text=f"↩️ Отменить №{k}", callback_data=f"g5:pn:cu:{k}")])
        rows.append([Btn(text="⬅ Назад", callback_data="g5:pn:ft")])
        return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows)

    def g5_scr_chat(self, cid: int):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        st = self.store.chats.get(cid)
        if st is None:
            return "Чат не найден.", InlineKeyboardMarkup(inline_keyboard=[[Btn(text="⬅ Назад", callback_data="g5:pn:cl")]])
        c5 = self.g5b().cfg(cid)
        gate, appeal = c5.get("gate", 1), c5.get("appeal", 1)
        known = self.g5b().known.d.get(str(cid), {})
        lines = [f"<b>🧬 5.0 · {esc(st.title or cid, 50)}</b>",
                 f"Правила чата: {'заданы (' + str(len(st.cfg.rules)) + ' знаков)' if st.cfg.rules else 'не заданы: /setrules текст'}",
                 f"Правила после проверки при входе: <b>{'вкл' if gate else 'выкл'}</b>"
                 + ("" if st.cfg.captcha else " (но проверка при входе выключена)")
                 + f" — кнопка «Показать правила», сообщение исчезает через {RULES_SHOW_TTL // 60} мин",
                 f"Апелляция («Это не спам» под удалением): <b>{'вкл' if appeal else 'выкл'}</b>",
                 f"Знакомых чату доменов: {len(known)}"]
        if known:
            lines.append("<i>" + esc(", ".join(sorted(known)[:12]), 200) + "</i>")
        rows = [[Btn(text=f"📜 Правила при входе: {'вкл' if gate else 'выкл'}", callback_data=f"g5:pn:ct:{cid}:gate")],
                [Btn(text=f"🙋 Апелляция: {'вкл' if appeal else 'выкл'}", callback_data=f"g5:pn:ct:{cid}:appeal")]]
        if known:
            rows.append([Btn(text="🧹 Забыть знакомые домены", callback_data=f"g5:pn:kf:{cid}")])
        rows.append([Btn(text="⬅ Назад", callback_data=f"ap:c:{cid}")])
        return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows)

    async def _g5_panel_button(self, cb, p: list) -> None:
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        msg, uid, now = getattr(cb, "message", None), cb.from_user.id, self.now()
        if msg is None or getattr(msg.chat, "type", "") != "private" or msg.chat.id != uid:
            return await self._g5_ans(cb)
        bk = self.g5b()
        sub = p[2] if len(p) > 2 else "ft"
        arg = p[3] if len(p) > 3 else ""
        note = ""

        async def show(text, kb, popup=None):
            await self._panel_edit(msg, text, kb)
            await self._g5_ans(cb, popup)

        if sub == "in":
            return await show(*self.g5_scr_inbox())
        if sub == "ft":
            return await show(*self.g5_scr_features())
        if sub == "ls":
            return await show(*self.g5_scr_list())
        if sub == "cs":
            return await show(*self.g5_scr_cases())
        if sub == "t":
            if arg not in bk.inbox["t"]:
                return await self._g5_ans(cb, "Запись удалена.", True)
            return await show(self.g5_ticket_text(arg), self.g5_ticket_kb(arg, back="g5:pn:in"))
        if sub == "tg" and arg in INBOX_KINDS:
            bk.inbox["off"][arg] = 0 if bk.inbox["off"].get(arg) else 1
            self.store.dirty = True
            return await show(*self.g5_scr_inbox(), "Приём " + ("выключен." if bk.inbox["off"][arg] else "включён."))
        if sub == "um":
            bk.inbox["mute"].pop(arg, None)
            self.store.dirty = True
            return await show(*self.g5_scr_list(), "Мут снят.")
        if sub == "ub":
            try:
                ok = await self.g5_unban_everywhere(int(arg), uid)
            except ValueError:
                ok = False
            return await show(*self.g5_scr_list(), "Разбанен." if ok else "Не нашёл в списке.")
        if sub in ("mi", "bi"):
            kind = "pn_mute" if sub == "mi" else "pn_ban"
            self.g5x["wait"][uid] = {"kind": kind, "exp": now + WAIT_TTL}
            txt = ("<b>🔇 Мут по id</b>\nОтправьте одним сообщением: <code>id</code> и срок, например <code>123456789 7д</code> "
                   "(«навсегда» — по умолчанию). Человек не сможет присылать вам баги и отзывы. Узнать id: /id ответом на его сообщение."
                   if sub == "mi" else
                   "<b>⛔ Бан по id</b>\nОтправьте одним сообщением: <code>id</code> и причина, например <code>123456789 рассылка рекламы</code>. "
                   "Бот заблокирует человека во всех чатах, где он админ, и перестанет отвечать на его команды и кнопки.")
            return await show(txt, InlineKeyboardMarkup(inline_keyboard=[[Btn(text="✖ Отмена", callback_data="g5:pn:in")]]))
        if sub == "cu":
            try:
                ok, note = await self.g5_undo(int(arg), uid)
            except ValueError:
                ok, note = False, "Не то дело."
            return await show(*self.g5_scr_cases(("↩️ Отменено: " if ok else "⚠️ ") + esc(note, 160)))
        if sub == "cl":
            chats = [c for c, s in self.store.chats.items() if s.active and c < 0][:24]
            rows = [[Btn(text=(self.store.chats[c].title or str(c))[:34], callback_data=f"g5:pn:ch:{c}")] for c in chats]
            rows.append([Btn(text="⬅ Назад", callback_data="g5:pn:ft")])
            return await show("<b>🗂 Чаты</b>" if chats else "Чатов нет.", InlineKeyboardMarkup(inline_keyboard=rows))
        if sub in ("ch", "ct", "kf"):
            try:
                cid = int(arg)
            except ValueError:
                return await self._g5_ans(cb)
            if cid not in self.store.chats:
                return await self._g5_ans(cb, "Чат не найден.", True)
            if sub == "ct":
                what = p[4] if len(p) > 4 else ""
                if what in ("gate", "appeal"):
                    c5 = bk.cfg(cid)
                    c5[what] = 0 if c5.get(what, 1) else 1
                    self.store.dirty = True
            elif sub == "kf":
                bk.known.d.pop(str(cid), None)
                self.store.dirty = True
                note = "Знакомые домены забыты."
            return await show(*self.g5_scr_chat(cid), note or None)
        await self._g5_ans(cb)

    async def _g5_panel_id_input(self, m, u, kind: str, text: str) -> None:
        toks = text.split(None, 1)
        if not toks or not toks[0].lstrip("-").isdigit() or len(toks[0]) < 5:
            return await self.out(m, "Нужен числовой id, например <code>123456789</code>. Откройте «Баги и отзывы» в /panel и повторите.")
        target, rest = int(toks[0]), (toks[1].strip() if len(toks) > 1 else "")
        if kind == "pn_mute":
            low = rest.lower()
            secs = 0 if (not low or low in ("навсегда", "forever", "0")) else parse_duration(rest.split()[0])
            if secs is None:
                return await self.out(m, "Срок не понял: «7д», «12ч» или «навсегда». Повторите через панель.")
            return await self.out(m, "🔇 " + await self.g5_mute_user(target, secs, u.id))
        n = await self.g5_ban_everywhere(target, str(target), rest or "через панель", u.id)
        if n < 0:
            return await self.out(m, "Этого человека банить нельзя (владелец, доверенный или сам бот).")
        await self.out(m, f"⛔ <code>{target}</code> забанен: чатов {n}. Бот больше не отвечает на его команды и кнопки. "
                          "Снять — «Мут и баны» в панели.")


# ═══════════════════════════════ свежие приметы мошенничества 2026 ═══════════════════════════════
def _near(a: str, b: str, gap: int = 60) -> str:
    """Два признака рядом в любом порядке (в пределах одной строки)."""
    return rf"(?:{a}[^\n]{{0,{gap}}}{b}|{b}[^\n]{{0,{gap}}}{a})"


def v5_spam_rules() -> list:
    R = G.R
    act = r"\b(?:бесплатн\w*|халяв\w*|раздач\w*|подар\w+|забер\w+|получ\w+|выигра\w+|free|claim|gift|giveaway)\b"
    stars = r"\b(?:telegram|телеграм\w*|тг)\s+(?:stars|старс\w*|звезд\w*)\b"
    return [
        ("g5_stars", "phish", 3.2, R(_near(act, stars)), "бесплатные Telegram Stars/«звёзды» — типичная приманка"),
        ("g5_airdrop_claim", "phish", 3.0,
         R(_near(r"\b(?:airdrop|аирдроп\w*|эирдроп\w*|эйрдроп\w*)\b", r"\b(?:claim|клейм\w*|забер\w+|получ\w+|подтверд\w+|подключ\w+)\b", 50)),
         "airdrop: «забери/подключи кошелёк»"),
        ("g5_airdrop", "phish", 1.2,
         R(_near(r"\b(?:airdrop|аирдроп\w*|эирдроп\w*|эйрдроп\w*)\b", r"(?:https?://|t\.me/|@\w{4,}|кошел\w*|wallet|metamask|seed)", 80)),
         "airdrop рядом со ссылкой/кошельком"),
        ("g5_support_lock", "phish", 3.5,
         R(_near(r"\bваш\w*\s+(?:telegram\s+|телеграм\w*\s+)?(?:аккаунт|акаунт|профиль)\w*\s+(?:будет\s+|был\s+)?"
                 r"(?:заблокирован\w*|удал[её]н\w*|ограничен\w*|взломан\w*)",
                 r"\b(?:пройдит\w+|подтвердит\w+|перейдит\w+|нажмит\w+|верификац\w+|обратит\w+)\b", 90)),
         "«ваш аккаунт заблокируют, подтвердите» — фальшивая поддержка"),
        ("g5_ai_trader", "phish", 3.0,
         R(_near(r"\b(?:ии|ai|нейросет\w*)[-\s]+(?:бот\w*|трейдер\w*|робот\w*|сигнал\w*)", r"(?:\d+\s*%|\bдоход\w*|\bприбыл\w*|\bзараб\w*|\bпрофит\w*)", 70)),
         "«ИИ-бот торгует за вас» с обещанием дохода"),
        ("g5_seed_ask", "phish", 4.5,
         R(r"\b(?:введите|отправьте|пришлите|напишите|скиньте|send|enter|provide)\s+(?:мне\s+|нам\s+)?(?:ваш\w*\s+|your\s+)?(?:seed|сид)[-\s]*(?:фраз\w*|phrase)"),
         "просят секретную seed-фразу кошелька"),
        ("g5_prize", "phish", 3.0,
         R(_near(r"\b(?:вы|ты)\s+(?:выиграл\w*|стали\s+победител\w*)\b", r"\b(?:забер\w+|получ\w+|клейм\w*|перейд\w+|нажм\w+|ссылк\w+|бот\w*)\b", 60)),
         "«вы выиграли — заберите»"),
        ("g5_clickfix", "phish", 3.5,
         R(r"\b(?:win\s*\+\s*r|ctrl\s*\+\s*v)\b[^\n]{0,60}\b(?:enter|вставьт\w+|вставить|paste)\b"),
         "«нажмите Win+R и вставьте» — заражение через фальшивую проверку"),
    ]


# ═══════════════════════════════ сборка ═══════════════════════════════
def _patch_autopilot(g: dict) -> None:
    """Новый вид импульса «farm» для автопилота: аккаунт-клон забаненных попал в чат. Считается как мягкий признак наплыва."""
    ar = g.get("AP_REFLEXES")
    if not ar or "raid" not in ar:
        return
    if "farm" not in ar["raid"]["soft"]:
        ar["raid"]["soft"] = ar["raid"]["soft"] | {"farm"}
    g["AP_PULSE_WEIGHT"]["farm"] = 0.9
    g["AP_KIND_LABEL"]["farm"] = "аккаунты-клоны забаненных (ферма)"
    if "_AX_HARD_ALL" in g:
        g["_AX_HARD_ALL"] = frozenset().union(*[s["hard"] for s in ar.values()])
        g["_AX_ALL_KINDS"] = frozenset().union(*[s["hard"] | s["soft"] for s in ar.values()])


def build(engine_cls, guard_cls):
    """→ (EngineV5, GuardV5). При GUARD5=0 возвращает классы как есть: бот работает ровно как 4.3."""
    reload_env()
    g = _GLOBALS.get("g")
    if not ON.get("all") or g is None:
        return engine_cls, guard_cls
    try:
        names = tuple(g["COMMAND_NAMES"])
        extra = tuple(n for n in ("bug", "feedback") if n not in names)
        if extra:
            g["COMMAND_NAMES"] = names + extra
            G.COMMAND_NAMES = g["COMMAND_NAMES"]
        if feat("cmds"):
            g["parse_minutes"] = parse_minutes_v5
        if feat("repeat"):
            g["REMIND_PER_USER"] = max(int(g.get("REMIND_PER_USER", 3)), 6)
        _patch_autopilot(g)
        if feat("net") or feat("look"):
            rules = g["SPAM_RULES"]
            have = {r[0] for r in rules}
            rules.extend(r for r in v5_spam_rules() if r[0] not in have)
    except Exception:                                                # noqa: BLE001
        log.exception("5.0: не удалось подменить константы guard.py — запускаю классы 4.3")
        return engine_cls, guard_cls
    icons = {**getattr(guard_cls, "JOURNAL_ICONS", {}), "undo": "↩️", "appeal": "🙋", "bug": "🐞", "gban_add": "⛔", "gban_del": "✅",
             "join_decline": "🚫"}
    E = type("EngineV5", (EngineMix, engine_cls), {"__doc__": "Engine + guard5"})
    Gd = type("GuardV5", (GuardMix, GuardMix2, GuardPanel5, guard_cls), {"JOURNAL_ICONS": icons, "__doc__": "Guard + guard5"})
    log.info("guard5 %s подключён: %s", V5_VERSION, ", ".join(k for k in FEATS if feat(k)) or "без частей")
    return E, Gd
