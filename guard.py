#!/usr/bin/env python3
# guard 6.0 — расширение guard6.py (лежит рядом): «Дозатор» запросов к Telegram и сводки волны (не упираемся в лимиты при 50+ скамерах),
# очередь капч (скамер не проходит без проверки, даже если Telegram не принял капчу), «страховка» после полной защиты, подсказка «перебор?»,
# новые улики Следопыта («стая», «обход вопросов», «смена облика») и Кукольного театра («хор», «одна рука», дела для кукол).
# Нет файла guard6.py или GUARD6=0 — бот работает ровно как 5.0. Подробности — в шапке guard6.py.
# guard 5.0 — расширение guard5.py (лежит рядом): «дела» с отменой и апелляцией, «второй взгляд» (проверка ссылок по сети), знакомые домены,
# правила после проверки при входе, /bug и /feedback, «ферма» для полной защиты и автопилота, /remind и /repeat с расписаниями, честные жалобы.
# Нет файла guard5.py или GUARD5=0 — бот работает ровно как 4.3. Подробности — в шапке guard5.py.
# guard 4.3 — самообучение+: уроки прямо из Telegram (реакции 👎/🤬 с вопросом в личке, /spam ответом, бан владельца командой или из меню), короткие фразы,
# отмеченные авторы, осторожное автообучение на волнах, поправки правил после отмены наказаний, /learn. GUARD_LEARN_PLUS=0 / GUARD_LEARN_AUTO=0 выключают.
# guard 4.2 — что нового: самообучение (карточки «спам / нормально» владельцу в личку, пересланный в личку спам,
# выученные шаблоны с отпечатками вместо текстов, калибровка весов, самоочистка и вечерняя справка; GUARD_LEARN=0 выключает),
# contact_net не считает «первое сообщение» уликой, новые правила (бонус за депозит, продажа веществ, «платят каждый день», «пиши +»).
# Языки: guard_es.py / guard_de.py / guard_ar.py / guard_zh.py рядом с guard.py подхватываются сами (испанский, немецкий, арабский, китайский);
# GUARD_LANGS=es,de (только эти) или GUARD_LANGS=off (никакие); у каждого ещё свой выключатель GUARD_ES / GUARD_DE / GUARD_AR / GUARD_ZH = 0.
# Тесты: python -m unittest discover -s tests -t .   (aiogram для них не нужен)
from __future__ import annotations

import asyncio
import difflib
import hashlib
import hmac
import html
import json
import logging
import math
import os
import random
import re
import secrets
import sys
import threading
import time
import unicodedata
import zlib
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter, OrderedDict, defaultdict, deque
from functools import lru_cache
from dataclasses import asdict, dataclass, field, fields
from pathlib import Path
from typing import Any, NamedTuple

from aiogram import BaseMiddleware, Bot, Dispatcher, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import (
    TelegramAPIError, TelegramBadRequest, TelegramForbiddenError, TelegramNetworkError, TelegramRetryAfter,
    TelegramServerError,
)
from aiogram.filters import Command
from aiogram.types import ChatPermissions


ZW_CHARS = set("​‌‍‎‏⁠⁡⁢⁣⁤﻿­᠎"
               "‪‫‬‭‮⁦⁧⁨⁩")


class _FoldTable(dict):

    def __missing__(self, cp: int):
        ch = chr(cp)
        cat = unicodedata.category(ch)
        val = None if (cat in ("Mn", "Me", "Cf") or (cat == "Cc" and ch not in "\n\t")) else cp
        self[cp] = val
        return val


_FOLD_TABLE = _FoldTable()
_ZW_DEL = {ord(c): None for c in ZW_CHARS}


def fold(s: str) -> str:
    if len(_FOLD_TABLE) > 60000:
        _FOLD_TABLE.clear()
    return unicodedata.normalize("NFKD", s).translate(_FOLD_TABLE).lower().replace("ё", "е")


def collapse(w: str) -> str:
    return re.sub(r"(.)\1+", r"\1", w)


TOKEN_RE = re.compile(r"[^\W_]+")
LAT_RE = re.compile(r"[a-z]")
CYR_RE = re.compile(r"[а-я]")

LAT2CYR = {"a": "а", "b": "в", "c": "с", "e": "е", "h": "н", "k": "к", "m": "м", "o": "о", "p": "р",
           "t": "т", "x": "х", "y": "у", "0": "о", "3": "з"}
LEET_A = {"0": "о", "1": "и", "3": "е", "4": "а", "5": "с", "6": "б", "7": "т", "8": "в", "9": "я"}
LEET_B = {"0": "о", "1": "л", "3": "з", "4": "ч", "5": "с", "6": "б", "7": "т", "8": "в", "9": "я"}
LAT_LEET = {"0": "o", "1": "i", "3": "e", "4": "a", "5": "s", "7": "t", "@": "a", "$": "s"}

MASK_RE = re.compile(r"(?<![a-zа-я])[a-zа-я]+(?:[*_#@%^~.\-·]{1,2}[a-zа-я]+){1,2}")
FILL_CYR = tuple("абвгдежзиклмнопрстуфхцчшщыэюя")
FILL_LAT = tuple("abcdefghijklmnopqrstuvwxyz")


@dataclass
class Norm:
    folded: str
    tokens: list
    mixed: int = 0
    zw: int = 0
    spaced: int = 0
    views: list = field(default_factory=list)
    masks: list = field(default_factory=list)


def normalize(text: str) -> Norm:
    text = text[:4500]
    zw = len(text) - len(text.translate(_ZW_DEL))
    folded = fold(text)
    toks = TOKEN_RE.findall(folded)
    n = Norm(folded=folded, tokens=toks, zw=zw)

    base = [collapse(t) for t in toks]
    homo, leet = [], []
    for t in toks:
        letters_only = t.isalpha() or not any(c.isdigit() for c in t)
        if letters_only and LAT_RE.search(t) and CYR_RE.search(t):
            n.mixed += 1
            homo.append(collapse("".join(LAT2CYR.get(c, c) for c in t)))
        if not letters_only and any(c.isalpha() for c in t):
            leet.append(collapse("".join(LEET_A.get(c, c) for c in t)))
            leet.append(collapse("".join(LEET_B.get(c, c) for c in t)))
            leet.append(collapse("".join(LAT_LEET.get(c, c) for c in t)))

    spaced_words, run = [], []
    for t in toks + [""]:
        if len(t) == 1 and t.isalpha():
            run.append(t)
            continue
        if len(run) >= 3:
            spaced_words.append(collapse("".join(run)))
            if len(run) >= 4:
                n.spaced += 1
        run = []

    n.views = [v for v in (base + spaced_words, homo, leet) if v]
    for m in MASK_RE.finditer(folded):
        raw = m.group(0)
        parts = re.split(r"[*_#@%^~.\-·]+", raw)
        joined = "".join(parts)
        if not 3 <= len(joined) <= 14:
            continue
        fills = []
        if len(parts) == 2:
            fills = [parts[0] + f + parts[1] for f in (FILL_CYR if CYR_RE.search(joined) else FILL_LAT)]
        n.masks.append((collapse(joined), [collapse(x) for x in fills]))
        if len(n.masks) >= 12:
            break
    return n


PREFIXES = tuple(sorted({collapse(fold(p)) for p in
                         "на за по при до от раз рас об вы у с под пере из над недо про пр съ ра о в во со ис воз вз".split()},
                        key=len, reverse=True))


class Lex:

    def __init__(self, roots=(), exact=(), exceptions=(), prefix_roots_min=4):
        self.roots = sorted({collapse(fold(r)) for r in roots if r}, key=len, reverse=True)
        self.exact = {collapse(fold(w)) for w in exact if w}
        self.exc = tuple({collapse(fold(e)) for e in exceptions if e})
        self.direct = re.compile("|".join(map(re.escape, self.roots))) if self.roots else None
        long_roots = [r for r in self.roots if len(r) >= prefix_roots_min]
        self.prefixed = (re.compile("(?:" + "|".join(map(re.escape, PREFIXES)) + ")(?:"
                                    + "|".join(map(re.escape, long_roots)) + ")") if long_roots else None)
        self._memo: dict = {}

    def hit(self, tok: str, tail: int | None = None) -> bool:
        if len(tok) > 40:
            return self._hit(tok, tail)
        key = tok if tail is None else (tok, tail)
        r = self._memo.get(key)
        if r is None:
            r = self._hit(tok, tail)
            if len(self._memo) >= 30000:
                self._memo.clear()
            self._memo[key] = r
        return r

    def _hit(self, tok: str, tail: int | None = None) -> bool:
        if not tok:
            return False
        for e in self.exc:
            if tok.startswith(e) and len(tok) - len(e) <= 6:
                return False
        if tok in self.exact:
            return True
        for rx in (self.direct, self.prefixed):
            if rx is None:
                continue
            m = rx.match(tok)
            if m and (tail is None or len(tok) - m.end() <= tail or m.end() >= 6):
                return True
        return False


PROF_ROOTS = """хуи хуе хуя хую пизд пезд ебат ебан ебал ебл ебу ебн ебис ебен ебуч ебеш ебет ебем блят бляд мудак
мудач мудил мудоз залуп гондон гандон шлюх шалав дроч долбоеб долбаеб мудоеб хуесос пиздабол пиздюк ебаш ебук
нахуи нахуя похуи похуя нихуя нихуа охуе охуи захуя дохуя нехуя ахуе ахуи наеб доеб уеб выеб отъеб отеб разъеб разеб
объеб съеб сьеб проеб приеб поеб заеб
pizd blyat blyad ebat ebal ebany zaeb naeb huyn huin huev huyev naxuy nahuy nahui pohuy pohui xuy
fuck fuk motherfuck cunt bitch asshole dickhead whore""".split()
PROF_EXACT = """бля блять блядь хули хуй пох нахер нахрен еб блд блдь пзд пздц пздец манда манды мандой манду
shit shits shitty bullshit shithead twat wanker slut sluts""".split()
PROF_EXC = """ебенез педикюр pussycat lollipop""".split()

HATE_ROOTS = """пидор пидар пидрил педик педераст черномаз черножоп узкоглаз унтерменш пархат хайль зигхайль
жидов жидяр жидовк faggot fagot kike untermensch""".split()
HATE_EXACT = """жид жиды жида жиду жидом жидам жидах хач хачи хача хачу хачей хачам хачом пидр
heil nazi nazis tranny""".split()
HATE_EXC = """педикюр педикул""".split()
NWORD_RU = re.compile(r"(?<![а-яa-z])ни+г{2,}[аеиоуы]")
NWORD_EN = re.compile(r"(?<![a-zа-я])n+[i1l!|]+[gq9]{2,}(?:e+r|a+(?!rd)|ah|uh|az|ez)")
HATE_COMPACT = ("siegheil", "sieghail", "heilhitler", "hailhitler", "зигхайль", "хайльгитлер")
HATE_SYMBOLS = ("卐", "ᛋᛋ", "ϟϟ")
NUM_1488 = re.compile(r"(?<!\d)14\s*[/\\]\s*88(?!\d)(?!\s*(?:хп|hp|%|урон|dmg|очк|балл|exp|lvl))")

ADULT_ROOTS = """порно порнух хентай минет миньет куннилингус кунилингус дилдо голожоп сиськ сисек титьк титек писюн
porn blowjob handjob hentai dildo xvideos""".split()
ADULT_EXACT = """анал порево вибратор нсфв nsfw nude nudes""".split()
MINOR_ROOTS = """детск дети детей детям детьми ребен ребят малолет школьниц школьник несовершеннолет подростк девочк
мальчик лоли шота loli underage""".split()
MINOR_EXACT = """дитя цп cp child children kid kids minor teen teens boy girl""".split()

PROF = HATEL = ADULT = MINOR = None
_custom = {"prof": [], "hate": [], "adult": [], "allow": [], "prof_x": [], "hate_x": [], "adult_x": []}


def build() -> None:
    global PROF, HATEL, ADULT, MINOR
    PROF = Lex(PROF_ROOTS + _custom["prof"], PROF_EXACT + _custom["prof_x"], PROF_EXC + _custom["allow"])
    HATEL = Lex(HATE_ROOTS + _custom["hate"], HATE_EXACT + _custom["hate_x"], HATE_EXC + _custom["allow"])
    ADULT = Lex(ADULT_ROOTS + _custom["adult"], ADULT_EXACT + _custom["adult_x"], _custom["allow"])
    MINOR = Lex(MINOR_ROOTS, MINOR_EXACT, ["lollipop"])


def load_custom(path: str | Path) -> int:
    p = Path(path)
    if not p.exists():
        return 0
    n = 0
    for line in p.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if ":" not in line:
            continue
        cat, word = (x.strip() for x in line.split(":", 1))
        if not word or cat not in ("prof", "hate", "adult", "allow"):
            continue
        if word.startswith("=") and cat != "allow":
            _custom[cat + "_x"].append(word[1:].strip())
        else:
            _custom[cat].append(word.lstrip("="))
        n += 1
    if n:
        build()
    return n


build()


def scan(n: Norm) -> dict:
    found = {"prof": [], "hate": [], "adult": [], "minor": False}

    def check(tok: str, tail: int | None = None) -> None:
        if PROF.hit(tok, tail):
            found["prof"].append(tok)
        if HATEL.hit(tok, tail):
            found["hate"].append(tok)
        if ADULT.hit(tok, tail):
            found["adult"].append(tok)
        if MINOR.hit(tok, tail):
            found["minor"] = True

    seen = set()
    for view in n.views:
        for tok in view:
            if tok not in seen:
                seen.add(tok)
                check(tok)
    for joined, fills in n.masks:
        if len(joined) >= 4:
            check(joined, 3)
        for f in fills:
            if len(f) >= 4:
                check(f, 3)

    f = n.folded
    if NWORD_RU.search(f) or NWORD_EN.search(f):
        found["hate"].append("n-word")
    if NUM_1488.search(f):
        found["hate"].append("14/88")
    if any(sym in f for sym in HATE_SYMBOLS):
        found["hate"].append("символ")
    compact = re.sub(r"[^a-zа-я]+", "", f)
    for phrase in HATE_COMPACT:
        if phrase in compact:
            found["hate"].append(phrase)
    for k in ("prof", "hate", "adult"):
        found[k] = list(dict.fromkeys(found[k]))
    return found


log_store = logging.getLogger("guard.store")

DEFAULT_ALLOW = (
    "youtube.com", "youtu.be", "wikipedia.org", "github.com", "reddit.com", "twitch.tv",
    "spotify.com", "imgur.com", "giphy.com", "tenor.com", "fandom.com", "wikimedia.org",
)

LINK_POLICIES = ("open", "trusted", "admins")
DAY_KEEP = 14
USER_KEEP_DAYS = 90
STRIKE_KEEP = 12
NAMES_KEEP = 800


_FIELD_NAMES: dict = {}


def _field_names(cls) -> tuple:
    names = _FIELD_NAMES.get(cls)
    if names is None:
        names = _FIELD_NAMES[cls] = tuple(f.name for f in fields(cls))
    return names


def _jdefault(o):
    names = _FIELD_NAMES.get(type(o))
    if names is None:
        if not hasattr(o, "__dataclass_fields__"):
            raise TypeError(f"Object of type {type(o).__name__} is not JSON serializable")
        names = _field_names(type(o))
    return {n: getattr(o, n) for n in names}


def _load(cls, d: dict | None):
    obj = cls()
    for f in fields(cls):
        if not d or f.name not in d:
            continue
        default, val = getattr(obj, f.name), d[f.name]
        try:
            if isinstance(default, bool):
                val = bool(val)
            elif isinstance(default, int) and not isinstance(default, bool):
                val = int(val)
            elif isinstance(default, float):
                val = float(val)
            elif isinstance(default, str):
                val = str(val)
            elif isinstance(default, list):
                val = list(val)
            elif isinstance(default, dict):
                val = dict(val)
        except (TypeError, ValueError):
            continue
        setattr(obj, f.name, val)
    return obj


@dataclass
class ChatCfg:
    enabled: bool = True
    captcha: bool = True
    captcha_timeout: int = 90
    captcha_smart: bool = True
    captcha_ban_min: int = 0
    smart_links: bool = True
    scam: bool = True
    links: str = "trusted"
    hate: bool = True
    adult: bool = True
    profanity: bool = False
    flood: bool = True
    slow: int = 0
    raid: bool = True
    ring: bool = True
    tribunes: bool = False
    admins_in_ring: bool = True
    quiet: bool = False
    clean_joins: bool = True
    allow: list = field(default_factory=list)
    block: list = field(default_factory=list)
    rules: str = ""
    welcome: str = ""
    notes: dict = field(default_factory=dict)
    cas: bool = True
    locks: list = field(default_factory=list)
    night: str = ""
    night_mode: str = "media"
    filters: dict = field(default_factory=dict)
    logchat: int = 0
    impostor: bool = True
    newbie_min: int = 0
    digest_hour: int = -1
    strict_until: float = 0.0
    strict_started: float = 0.0
    strict_auto: bool = True
    puppet: bool = True
    spam_memory: bool = True
    conflicts: bool = True
    jitter: bool = False
    fort_on: bool = False
    fort_until: float = 0.0
    fort_started: float = 0.0
    fort_origin: str = ""
    fort_auto: bool = True
    fort_before: dict = field(default_factory=dict)
    fort_applied: dict = field(default_factory=dict)
    fort_board: int = 0
    fort_why: str = ""
    trace: str = "on"
    autopilot: bool = True
    ap_off: list = field(default_factory=list)
    ap_state: dict = field(default_factory=dict)
    ap_before: dict = field(default_factory=dict)
    ap_applied: dict = field(default_factory=dict)
    ap_cool: dict = field(default_factory=dict)
    ap_scar: float = 0.0
    ap_scar_t: float = 0.0
    ap_hours: list = field(default_factory=list)
    ap_threat_t: float = 0.0
    ap_doubt: dict = field(default_factory=dict)
    ap_dow: list = field(default_factory=list)
    ap_bg: dict = field(default_factory=dict)
    learn: bool = True


@dataclass
class UserRec:
    first_seen: float = 0.0
    last_seen: float = 0.0
    joined: float = 0.0
    clean: int = 0
    last_clean: float = 0.0
    verified: bool = False
    vouched: bool = False
    strikes: list = field(default_factory=list)
    muted_until: float = 0.0
    banned: bool = False
    watch: list = field(default_factory=list)
    src: str = ""
    hours: str = ""


@dataclass
class ChatState:
    chat_id: int = 0
    title: str = ""
    added: float = 0.0
    learning_until: float = 0.0
    cfg: ChatCfg = field(default_factory=ChatCfg)
    users: dict = field(default_factory=dict)
    stats: dict = field(default_factory=dict)
    names: dict = field(default_factory=dict)
    active: bool = True


_UREC_N = len(_field_names(UserRec))


class Store:
    def __init__(self, path: str | os.PathLike = "guard_state.json", clock=time.time):
        self.path = Path(path)
        self.clock = clock
        self.chats: dict[int, ChatState] = {}
        self.captchas: dict[str, dict] = {}
        self.rings: dict[str, dict] = {}
        self.alert_users: set[int] = set()
        self.meta: dict[str, Any] = {}
        self.dirty = False
        self.tz_h = None
        self._wlock = threading.Lock()
        self._last_flush = 0.0
        self._snap_cost = 0.0

    def chat(self, chat_id: int, title: str = "", create: bool = True) -> ChatState | None:
        st = self.chats.get(chat_id)
        if st is None:
            if not create:
                return None
            now = self.clock()
            st = ChatState(chat_id=chat_id, title=title, added=now, learning_until=now + 86400)
            self.chats[chat_id] = st
            self.dirty = True
        elif title and st.title != title:
            st.title = title
            self.dirty = True
        return st

    def user(self, chat: ChatState, uid: int, now: float | None = None) -> UserRec:
        rec = chat.users.get(uid)
        now = self.clock() if now is None else now
        if rec is None:
            old = now < chat.learning_until
            rec = UserRec(first_seen=(chat.added - 7 * 86400) if old else now, last_seen=now)
            chat.users[uid] = rec
            self.dirty = True
        return rec

    def day(self, ts: float | None = None) -> str:
        ts = self.clock() if ts is None else ts
        bucket = int(ts) // 60
        c = getattr(self, "_day_c", None)
        if c is not None and c[0] == bucket and c[1] == self.tz_h:
            return c[2]
        if self.tz_h is None:
            key = time.strftime("%Y-%m-%d", time.localtime(ts))
        else:
            key = time.strftime("%Y-%m-%d", time.gmtime(ts + self.tz_h * 3600))
        self._day_c = (bucket, self.tz_h, key)
        return key

    def bump(self, chat: ChatState, key: str, n: int = 1, now: float | None = None) -> None:
        day = self.day(now)
        d = chat.stats.setdefault(day, {})
        d[key] = d.get(key, 0) + n
        self.dirty = True

    def remember_name(self, chat: ChatState, username: str, uid: int) -> None:
        if not username:
            return
        u = username.lower().lstrip("@")
        if chat.names.get(u) != uid:
            chat.names[u] = uid
            if len(chat.names) > NAMES_KEEP:
                for k in list(chat.names)[: len(chat.names) - NAMES_KEEP]:
                    chat.names.pop(k, None)
            self.dirty = True

    def snapshot(self) -> dict:
        chats = {}
        for cid, st in self.chats.items():
            d = asdict(st)
            d["users"] = {str(u): asdict(r) for u, r in st.users.items()}
            chats[str(cid)] = d
        return {"v": 1, "chats": chats, "captchas": dict(self.captchas), "rings": dict(self.rings),
                "alert_users": sorted(self.alert_users), "meta": dict(self.meta)}

    def _backup(self) -> None:
        try:
            if self.path.exists() and time.time() - getattr(self, "_bak_t", 0.0) > 3600:
                import shutil
                bak = str(self.path) + ".bak"
                shutil.copy2(self.path, bak)
                os.chmod(bak, 0o600)
                self._bak_t = time.time()
        except OSError:
            pass

    def _snap_parts(self, parts: list, step: int = 400):
        enc = json.JSONEncoder(ensure_ascii=False, default=_jdefault).encode
        parts.append('{"v": 1, "chats": {')
        first = True
        for cid, st in list(self.chats.items()):
            head = enc({f: getattr(st, f) for f in _field_names(ChatState) if f != "users"})[1:-1]
            items = list(st.users.items())
            chunks = []
            for i in range(0, len(items), step):
                part = items[i:i + step]
                if all(type(r) is UserRec and len(r.__dict__) == _UREC_N for _u, r in part):
                    chunks.append(enc({str(u): r.__dict__ for u, r in part})[1:-1])
                else:
                    chunks.append(enc({str(u): r for u, r in part})[1:-1])
                if i + step < len(items):
                    yield
            users = ", ".join(c for c in chunks if c)
            parts.append(("" if first else ", ") + enc(str(cid)) + ": {" + head + (", " if head else "") + '"users": {' + users + "}}")
            first = False
            yield
        parts.append('}, "captchas": ' + enc(dict(self.captchas)) + ', "rings": ' + enc(dict(self.rings))
                     + ', "alert_users": ' + enc(sorted(self.alert_users)) + ', "meta": {')
        first = True
        for k, v in list(self.meta.items()):
            parts.append(("" if first else ", ") + enc(str(k)) + ": " + enc(v))
            first = False
            yield
        parts.append("}}")

    def _write(self, data) -> None:
        tmp = Path(str(self.path) + ".tmp")
        with self._wlock:
            fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                if isinstance(data, list):
                    f.writelines(data)
                else:
                    json.dump(data, f, ensure_ascii=False)
                f.flush()
                os.fsync(f.fileno())
            self._backup()
            os.replace(tmp, self.path)

    def save_now(self) -> None:
        self.dirty = False
        try:
            parts: list = []
            for _ in self._snap_parts(parts):
                pass
            self._write(parts)
        except Exception:
            self.dirty = True
            log_store.exception("не удалось сохранить %s", self.path)

    async def flush(self, force: bool = False, every: float = 10.0) -> None:
        import asyncio
        now = time.monotonic()
        every = min(max(every, self._snap_cost * 30), 120.0)
        if not self.dirty or (not force and now - self._last_flush < every):
            return
        self._last_flush = now
        self.dirty = False
        parts: list = []
        try:
            t0 = time.perf_counter()
            for _ in self._snap_parts(parts):
                await asyncio.sleep(0)
            self._snap_cost = time.perf_counter() - t0
            await asyncio.to_thread(self._write, parts)
        except Exception:
            self.dirty = True
            log_store.exception("не удалось сохранить %s", self.path)

    def load(self) -> None:
        if not self.path.exists():
            return
        try:
            raw = json.loads(self.path.read_text(encoding="utf-8"))
            if not isinstance(raw, dict):
                raise ValueError("ожидался словарь")
        except Exception:
            log_store.exception("%s битый (старый файл сохранён как .bad), пробую копию .bak", self.path)
            try:
                os.replace(self.path, str(self.path) + ".bad")
            except OSError:
                pass
            try:
                raw = json.loads(Path(str(self.path) + ".bak").read_text(encoding="utf-8"))
                if not isinstance(raw, dict):
                    raise ValueError("ожидался словарь")
                log_store.warning("состояние восстановлено из .bak (потеряно не больше часа)")
            except Exception:
                log_store.warning("копии .bak нет или она тоже битая — начинаю с чистого листа")
                return
        for cid, d in (raw.get("chats") or {}).items():
            try:
                st = _load(ChatState, d)
                st.chat_id = int(cid)
                st.cfg = _load(ChatCfg, d.get("cfg"))
                if st.cfg.links not in LINK_POLICIES:
                    st.cfg.links = "trusted"
                st.users = {int(u): _load(UserRec, r) for u, r in (d.get("users") or {}).items()}
                st.stats = {k: dict(v) for k, v in (d.get("stats") or {}).items()}
                st.names = {str(k): int(v) for k, v in (d.get("names") or {}).items()}
                self.chats[int(cid)] = st
            except Exception:
                log_store.exception("не смог загрузить чат %s — пропускаю", cid)
        self.captchas = dict(raw.get("captchas") or {})
        self.rings = dict(raw.get("rings") or {})
        self.alert_users = {int(x) for x in raw.get("alert_users", [])}
        self.meta = dict(raw.get("meta") or {})

    def prune(self, now: float | None = None) -> int:
        now = self.clock() if now is None else now
        cut = now - USER_KEEP_DAYS * 86400
        gone = 0
        for st in self.chats.values():
            dead = [u for u, r in st.users.items()
                    if r.last_seen < cut and not r.strikes and not r.banned and not r.vouched
                    and r.muted_until < now]
            for u in dead:
                st.users.pop(u, None)
            gone += len(dead)
            days = sorted(st.stats)
            for d in days[:-DAY_KEEP]:
                st.stats.pop(d, None)
        if gone:
            self.dirty = True
        return gone


log_phrases = logging.getLogger("guard.phrases")


def plural(n: int, one: str, few: str, many: str) -> str:
    n = abs(int(n))
    if 11 <= n % 100 <= 14:
        return many
    r = n % 10
    return one if r == 1 else few if 2 <= r <= 4 else many


def human_dur(sec: float) -> str:
    sec = max(0, int(round(sec)))
    if sec < 90:
        return f"{sec} {plural(sec, 'секунду', 'секунды', 'секунд')}"
    if sec < 3600:
        m = max(2, round(sec / 60))
        return f"{m} {plural(m, 'минуту', 'минуты', 'минут')}"
    if sec < 36 * 3600:
        if sec % 3600 and sec < 3 * 3600:
            m = round(sec / 60)
            return f"{m} {plural(m, 'минуту', 'минуты', 'минут')}"
        h = max(1, round(sec / 3600))
        return f"{h} {plural(h, 'час', 'часа', 'часов')}"
    d = max(2, round(sec / 86400))
    return f"{d} {plural(d, 'день', 'дня', 'дней')}"


PHRASES: dict[str, str] = {
    "warn": "{name}: предупреждение. Сообщение удалено.",
    "mute": "{name}: запись ограничена на {dur}.",
    "ban_spam": "{name}: заблокирован. Причина: рассылка нежелательного содержимого.",
    "hacked": "{name}: аномальная активность аккаунта. Запись ограничена на {dur}. Администраторы уведомлены.",
    "ring_hush": "Активна сессия: {names}. Сообщения остальных участников удаляются.",
    "lock_hush": "Чат закрыт. Запись доступна только администраторам.",
    "ring_mute": "{name}: превышен порог нарушений во время сессии. Запись ограничена на 3 минуты.",
    "slow": "{name}: медленный режим. Повторите отправку через {s} с.",
    "captcha_prompt": "{name}: требуется проверка.\n<b>{q}</b>\nВремя на ответ: {sec} с.",
    "captcha_ok": "{name}: проверка пройдена.",
    "captcha_wrong": "{name}: неверный ответ. Осталось попыток: {left}.",
    "captcha_fail": "{name}: проверка не пройдена. Доступ закрыт на {mins}.",
    "captcha_timeout": "{name}: время проверки истекло. Доступ закрыт на {mins}.",
    "raid_on": "Зафиксирован массовый вход. Усиленная проверка включена на {mins}.",
    "raid_off": "Массовый вход завершён. Усиленная проверка отключена.",
    "shift_on": "Модерация включена.",
    "shift_off": "Модерация отключена.",
    "lockdown_on": "Чат закрыт на {mins}. Запись доступна только администраторам.",
    "lockdown_off": "Чат открыт.",
    "ring_start": "Сессия начата. Участники: {names}. Длительность: {mins}. Досрочное завершение: /bell.",
    "ring_end": "Сессия завершена. Запись открыта для всех.",
    "report_ack": "Жалоба принята.",
    "report_removed": "Сообщение удалено по жалобам.",
    "report_dup": "Жалоба уже учтена.",
    "report_self": "Жалоба на собственное сообщение не принимается.",
    "report_need_reply": "Используйте /report ответом на сообщение, на которое подаётся жалоба.",
    "need_admin": "Недостаточно прав. Команда доступна администраторам.",
    "need_reply": "Используйте команду ответом на сообщение участника.",
    "need_rights": "Недостаточно прав бота. Требуются: удаление сообщений и ограничение участников.",
    "unknown_user": "Участник не найден. Бот знает только тех, кого видел в чате. Используйте команду ответом на сообщение.",
    "forgiven": "{name}: нарушения сброшены.",
    "vouched": "{name}: поручительство оформлено.",
    "unvouched": "{name}: поручительство снято.",
    "purged": "Удалено сообщений: {n}.",
    "muted_manual": "{name}: запись ограничена на {dur}.",
    "unmuted": "{name}: ограничения сняты.",
    "banned_manual": "{name}: заблокирован.",
    "unbanned": "{name}: блокировка снята.",
    "warned_manual": "{name}: выдано предупреждение.",
    "slow_on": "Медленный режим включён: одно сообщение в {s} с.",
    "slow_off": "Медленный режим отключён.",
    "allow_added": "Домен {domain} добавлен в список разрешённых.",
    "allow_removed": "Домен {domain} удалён из списка разрешённых.",
    "block_added": "Домен {domain} добавлен в список запрещённых.",
    "block_removed": "Домен {domain} удалён из списка запрещённых.",
    "ring_need_two": "Укажите двух участников: /ring @первый @второй — или ответом на сообщение одного из них и @вторым.",
    "ring_none": "Активных сессий нет.",
    "added_ok": "Бот активен. Права получены.\nНастройки: /guard. Команды: /help.",
    "added_no_rights": "Бот добавлен без необходимых прав. Требуются: удаление сообщений, ограничение и блокировка участников.",
    "rights_lost": "Права бота отозваны. Требуются: удаление сообщений и ограничение участников.",
    "target_admin": "Действие недоступно: цель является администратором.",
    "bad_domain": "Некорректный домен. Пример: /allow example.com",
    "puppet": "Выявлен постановочный диалог: подставные аккаунты изображали обсуждение. Сообщения удалены, участники наказаны.",
}

PARAMS: dict[str, tuple] = {
    "warn": ("name",), "mute": ("name", "dur"), "ban_spam": ("name",), "hacked": ("name", "dur"),
    "ring_hush": ("names",), "lock_hush": (), "ring_mute": ("name",), "slow": ("name", "s"),
    "captcha_prompt": ("name", "q", "sec"), "captcha_ok": ("name",), "captcha_wrong": ("name", "left"),
    "captcha_fail": ("name", "mins"), "captcha_timeout": ("name", "mins"), "raid_on": ("mins",), "raid_off": (),
    "shift_on": (), "shift_off": (), "lockdown_on": ("mins",), "lockdown_off": (),
    "ring_start": ("names", "mins"), "ring_end": (), "report_ack": (), "report_removed": (), "report_dup": (),
    "report_self": (), "report_need_reply": (), "need_admin": (), "need_reply": (), "need_rights": (),
    "unknown_user": (), "forgiven": ("name",), "vouched": ("name",), "unvouched": ("name",), "purged": ("n",),
    "muted_manual": ("name", "dur"), "unmuted": ("name",), "banned_manual": ("name",), "unbanned": ("name",),
    "warned_manual": ("name",), "slow_on": ("s",), "slow_off": (), "allow_added": ("domain",),
    "allow_removed": ("domain",), "block_added": ("domain",), "block_removed": ("domain",),
    "ring_need_two": (), "ring_none": (), "target_admin": (), "bad_domain": (), "added_ok": (),
    "added_no_rights": (), "rights_lost": (), "puppet": (),
}


RANKS = [(0, "Уровень 1"), (15, "Уровень 2"), (50, "Уровень 3"), (150, "Уровень 4"), (400, "Уровень 5"),
         (1000, "Уровень 6")]


def rank_of(clean: int) -> str:
    title = RANKS[0][1]
    for need, name in RANKS:
        if clean >= need:
            title = name
    return title


class Voice:

    def __init__(self, rng: random.Random | None = None):
        self.rng = rng or random.Random()

    def say(self, key: str, **kw) -> str:
        tpl = PHRASES.get(key)
        if tpl is None:
            log_phrases.error("нет шаблона %r", key)
            return ""
        try:
            return tpl.format(**kw)
        except (KeyError, IndexError, ValueError):
            log_phrases.exception("шаблон %r не форматируется с %s", key, sorted(kw))
            return re.sub(r"\{[^}]*\}", "", tpl).strip()


HELP_USER = (
    "<b>Бот модерации чата</b>\n"
    "Функции: ограничение записи во время сессий, удаление спама и флуда, проверка новых участников.\n\n"
    "<b>Команды для всех</b>\n"
    "/report — жалоба на сообщение (ответом на него)\n"
    "/rules — правила чата; /notes — заметки (или #имя)\n"
    "/me — карточка участника; /top — рейтинг активности\n"
    "/remind <i>30м текст</i> — напоминание (допустимо «2ч», «1д», «завтра в 10», «каждый день в 9:00»); /remind list\n"
    "/bug <i>текст</i> — сообщить о баге; /feedback <i>текст</i> — что понравилось или чего не хватает\n"
    "/poll <i>вопрос | вариант | вариант</i> — опрос\n"
    "/roll <i>2d6</i>, /coin — случайные значения\n"
    "/filters — автоответы чата\n"
    "/id — идентификаторы пользователя и чата\n"
    "/help — эта справка"
)

HELP_ADMIN = (
    "<b>Команды владельца</b>\n"
    "/panel (или /admin) — панель управления в личных сообщениях с ботом\n"
    "/guard — панель настроек в чате\n"
    "/status — текущие настройки\n"
    "/shift on|off — включить или отключить модерацию\n"
    "/ring @a @b — открыть сессию вручную (или ответом на сообщение участника и @вторым); /bell — завершить сессию\n"
    "/lockdown [минут] — закрыть чат: запись только у администраторов; /open — открыть\n"
    "/slow [секунд|off] — медленный режим\n"
    "/warn, /mute [минут], /unmute, /ban, /unban — ответом на сообщение\n"
    "/forgive — сбросить нарушения; /purge [минут] — удалить недавние сообщения участника\n"
    "/vouch, /unvouch — поручительство за участника\n"
    "/allow, /disallow, /block, /unblock <i>домен</i> — списки ссылок; /domains — показать списки\n"
    "/setrules <i>текст</i> — правила; /welcome <i>текст</i> — приветствие ({name} — имя новичка)\n"
    "/addnote <i>имя текст</i>, /delnote <i>имя</i> — заметки чата\n"
    "/explain <i>текст</i> — оценка текста без применения санкций\n"
    "/raid on|off — режим массового входа; /stats — статистика за последние дни\n"
    "/lock, /unlock <i>тип</i> — замки по типам контента (голосовые, стикеры, пересылки…); /locks — список\n"
    "/night <i>23:00 07:00</i> [media|all] — ночной режим; /night off — выключить\n"
    "/filter <i>слово ответ</i>, /stop <i>слово</i> — автоответы\n"
    "/repeat <i>6ч текст</i> — регулярное объявление; /repeats, /unrepeat <i>номер</i>\n"
    "/setlog <i>id чата или канала</i> — журнал банов и ограничений\n"
    "/gban <i>id причина</i>, /ungban <i>id</i>, /gbans — общий чёрный список на все чаты бота\n"
    "/newbie <i>60м</i> — новичкам первое время нельзя медиа, пересылки и приглашения; /newbie off\n"
    "/digest <i>21</i> — итоги дня каждый день в этот час; /digest now, /digest off\n"
    "/copyset <i>id чата</i> — перенести сюда настройки другого чата бота; /ban <i>2д</i> — временный бан\n"
    "/strict [<i>2ч</i>|<i>90м</i>|off] — строгий режим против спама (без срока — на 2 часа); /strict auto on|off — "
    "включать его самому при волне спама\n"
    "/fullguard [<i>2ч</i>|off] — полная защита: сразу самые жёсткие настройки, при выключении всё возвращается как было; "
    "/fullguard radar — радар угроз; /fullguard auto on|off — включать её самому при волне; /panic — то же, что /fullguard\n"
    "/trace [<i>on|log|off</i>] — «Следопыт»: улики из правок, скорости ответов, ритма и связей; "
    "/trace ответом на сообщение — досье: почему бот так решил\n"
    "/autopilot — автопилот: при волне спама, наплыве, самозванцах, флуде, накале и 18+ сам включает нужные функции по трём "
    "уровням и сам возвращает; /autopilot why — что решил и почему; /autopilot off|on [<i>волна</i>|<i>наплыв</i>|…]; /ap — то же\n"
    "/spamlist — что бот помнит о пойманном спаме (контакты на неделю); /forget <i>контакт</i> или /forget all — стереть\n"
    "/contacts — с кем переписывался участник (ответом на его сообщение); бот только показывает вам, никому не пишет\n"
    "/safety — опубликовать и закрепить памятку о мошенниках\n"
    "/invite <i>метка</i> — ссылка-приглашение с меткой; /links — кто по какой вошёл; /revoke <i>метка</i> — отозвать ссылку\n"
    "/spam — ответом на спам: удалить и выучить; /learn — что выучил бот и как его учить\n"
    "<b>5.0</b>: кнопки «↩️ Отменить»/«✅ Верно» в тревоге; /setrules gate off — не показывать правила кнопкой после проверки; "
    "/panel → «🐞 Баги и отзывы», «🧬 5.0»; /repeat <i>6ч пн-пт 10-22 текст</i> — по расписанию"
)

HELP_PRIVATE = (
    "<b>Бот модерации Telegram-чатов.</b>\n"
    "Для работы добавьте бота в группу и назначьте администратором с правами: удаление сообщений, "
    "ограничение и блокировка участников.\n\n"
    "Управление доступно только владельцам: их идентификаторы указаны в настройках бота. Права администратора "
    "в чате для этого не учитываются.\n\n"
    "Владельцу: отправьте /start для получения уведомлений о серьёзных событиях (взлом аккаунтов, массовая "
    "рассылка, жалобы). Панель управления: /panel.\n\n"
    "Внешняя система может сообщать о начале и конце сессий через HTTP-мост: на время сессии писать могут "
    "только её участники."
)


WATCH_T, DELETE_T, BAN_T = 2.5, 4.0, 8.0
STRONG_SCAM = 6.0
TIER_FACTOR = {"new": 1.0, "member": 0.75, "veteran": 0.5}
STRIKE_SCALE = {"new": 1.0, "member": 0.85, "veteran": 0.7}
HALF_LIFE = 12 * 3600
LADDER = ((1.5, 0), (2.5, 600), (3.5, 3600), (5.0, 21600), (1e9, 86400))
RATE = {"new": (5, 10), "member": (7, 10), "veteran": (10, 10)}
RATE_RAID_NEW = (3, 10)
STICKER_LIM = {"new": 5, "member": 8, "veteran": 12}
MEDIA_LIM = {"new": 3, "member": 5, "veteran": 8}
RUN_LIM = {"new": 15, "member": 15, "veteran": 25}
EMOJI_LIM = {"new": 25, "member": 25, "veteran": 40}
MENTION_LIM = {"new": 5, "member": 5, "veteran": 8}
WALL_LIM = {"new": 1800, "member": 1800, "veteran": 3500}
RAID_JOINS, RAID_WINDOW, RAID_HOLD = 8, 60.0, 900.0
RING_TTL_DEFAULT = 2700
NEW_BAN_AGE = 72 * 3600
TRUST_FARM_BASE = 8.0
TRUST_FARM_PER_DAY = 14.0
CNET_WINDOW = 1800
CNET_MIN_OTHERS = 2
WATCH_WINDOW = 15 * 60

STRICT_DEFAULT_MIN = 120
STRICT_MIN_MIN, STRICT_MAX_MIN = 5, 7 * 1440
WATCH_T_S, DELETE_T_S, BAN_T_S = 1.5, 2.5, 5.0
TIER_FACTOR_STRICT = {"new": 1.4, "member": 1.2, "veteran": 0.9}
NEW_BAN_AGE_STRICT = 14 * 86400
RATE_STRICT = {"new": (3, 10), "member": (5, 10), "veteran": (8, 10)}
STICKER_LIM_STRICT = {"new": 2, "member": 4, "veteran": 8}
MEDIA_LIM_STRICT = {"new": 1, "member": 3, "veteran": 5}
MENTION_LIM_STRICT, WALL_LIM_STRICT, EMOJI_LIM_STRICT = 3, 1200, 15
STRICT_SLOW = {"new": 20, "member": 8}
STRICT_STRIKE_MULT = 1.8
STRICT_MIN_MUTE = {"new": 3600, "member": 1800}
STRICT_HACKED_MUTE = 6 * 3600
STRICT_AUTO_USERS, STRICT_AUTO_WINDOW = 3, 600
FLOOD_PURGE = {"слишком часто": 12, "поток стикеров/гифок": 30, "поток медиа": 20,
               "одно и то же снова и снова": 45, "почти одинаковые сообщения подряд": 45}

PUPPET_SIGNAL = 4.0
PUPPET_DUO_SIGNAL = 3.0
PUPPET_TTL = 6 * 3600
PUPPET_MAX_BEATS = 600
PUPPET_THREAD_ROLES = 40
PUPPET_DEPTH = 8
PUPPET_YOUNG_AGE = 48 * 3600
PUPPET_BAN_CLEAN = 2
PUPPET_MUTE_S = 6 * 3600
ROLE_ASK, ROLE_PITCH, ROLE_CONFIRM = 1, 2, 4

SPAM_MEM_TTL = 7 * 86400
SPAM_MEM_MAX = 300
SPAM_MEM_SIGNAL = 4.0
SPAM_MEM_LEARN = 3
SPAMLIST_SHOW = 15

TALK_TTL = 24 * 3600
TALK_MAX = 3000
BAIT_WINDOW = 30 * 60
PROV_SOFT_STRIKE = 0.2
PROV_MIN_CLEAN = 30
PROV_REPEAT = 3
DOGPILE_WINDOW = 180
DOGPILE_MIN, DOGPILE_HOSTILE = 5, 2
DOGPILE_COOLDOWN = 1800
REPORT_CONFLICT_WINDOW = 6 * 3600
REPORT_STRIKE_CAP = 2
CONTACTS_SHOW = 8
INVITE_BAD_MIN = 3
INVITE_BAD_SHARE = 0.4
INVITE_BAD_AGE = 3 * 86400
INVITE_LABEL_RE = re.compile(r"^[A-Za-zА-Яа-яЁё0-9 _.-]{1,24}$")
JITTER_MIN, JITTER_MAX = 3.0, 45.0

FORT_MIN_MIN, FORT_MAX_MIN = 5, 14 * 1440
FORT_LOCKS = ("invitelink", "contact", "story", "channel", "inline", "game", "forward")
FORT_NEWBIE_MIN = 720
FORT_CAPTCHA_TIMEOUT = 45
FORT_CAPTCHA_BAN_MIN = 60
FORT_SLOW_BY_LEVEL = {"new": (8, 12, 20, 30), "member": (0, 4, 8, 12), "veteran": (0, 0, 0, 3)}
RADAR_WEIGHT = {"scam_ban": 2.5, "scam": 1.5, "memory": 1.0, "puppet": 3.0, "minors": 1.5, "adult": 0.8, "hate": 0.5,
                "flood": 0.6, "link": 0.5, "profanity": 0.2, "suspicious": 0.5, "raid": 3.0, "raid_more": 1.0,
                "capfail": 0.8, "cas": 1.5, "impostor": 1.5, "namespam": 1.2, "react": 1.5, "trace": 1.5}
RADAR_SOFT = frozenset({"flood", "link", "profanity", "hate", "adult", "suspicious", "capfail"})
RADAR_LABEL = {"scam_ban": "заблокировано спамеров", "scam": "спам удалён", "memory": "повтор контакта спамера",
               "puppet": "постановочные диалоги", "minors": "18+ рядом с детьми", "adult": "18+", "hate": "оскорбления",
               "flood": "флуд", "link": "ссылки", "profanity": "мат", "suspicious": "подозрительное", "raid": "массовый вход",
               "raid_more": "массовый вход", "capfail": "не прошли проверку", "cas": "база CAS и общий список",
               "impostor": "подмена админов", "namespam": "имена-реклама", "react": "поток реакций", "trace": "подмены правкой и шаблонные ответы"}
FORT_COUNT_AS = {"cas": "ban", "namespam": "ban", "impostor": "mute", "react": "mute", "capfail": "capfail"}
RADAR_HALF, RADAR_WINDOW = 240.0, 900.0
RADAR_ACTOR_CAP, RADAR_ACTOR_MIN = 3.0, 0.4
RADAR_KEEP = 600
RADAR_LEVELS = ((10.0, 3, "осада", "🔴"), (6.0, 2, "волна", "🟠"), (2.5, 1, "тревога", "🟡"), (0.0, 0, "спокойно", "🟢"))
FORT_TRIP_SCORE, FORT_TRIP_ACTORS = 10.0, 4
FORT_KEEP_SCORE = 3.0
FORT_AUTO_MIN, FORT_AUTO_HOLD = 15 * 60, 12 * 60
FORT_REARM_AUTO, FORT_REARM_MANUAL = 5 * 60, 10 * 60
FORT_REMIND = 6 * 3600
FORT_BOARD_EVERY = 30
FORT_SWEEP_WINDOW, FORT_SWEEP_MAX = 20 * 60, 20
FORT_SOURCE_WINDOW = 30 * 60

TRACE_BOOK_MAX, TRACE_BOOK_TTL = 900, 6 * 3600
TRACE_FAST_S = 12.0
TRACE_FAST_MIN = 3.0
TRACE_EDIT_DELAY = 120.0
TRACE_WOKE_GAP, TRACE_WOKE_AGE = 14 * 86400, 30 * 86400
TRACE_WOKE_HOLD = 3600
TRACE_METRO_N, TRACE_METRO_CV = 9, 0.06
TRACE_HOURS_MIN = 30
TRACE_ECHO_MIN = 4
TRACE_CASE_TTL = 86400
TRACE_STRONG = {"inject": 3.5, "canned": 2.5, "fast_contact": 1.8}
TRACE_FAST_NEW = 2.5
TRACE_CANNED_NEW = 4.0
TRACE_SOFT = {"woke": 1.0, "odd_hour": 0.9, "metro": 1.2, "echo": 0.8, "multi_edit": 1.0}
TRACE_SOFT_CAP, TRACE_SOFT_CAP_STRICT = 2.4, 3.5
TRACE_LABEL = {"inject": "подмена правкой", "canned": "шаблонные ответы", "fast_contact": "быстрый ответ со ссылкой",
               "fast_plain": "быстрый ответ", "woke": "проснулся после долгого молчания", "odd_hour": "необычный час",
               "metro": "метроном вместо пауз", "echo": "общается только с новичками", "multi_edit": "много правок"}

AP_REFLEXES = {
    "wave":  {"label": "волна спама и ссылок", "icon": "🌊", "alias": ("волна", "спам", "wave"),
              "hard": frozenset({"scam_ban", "scam", "memory", "puppet", "trace"}), "soft": frozenset({"link", "suspicious"})},
    "raid":  {"label": "наплыв новичков", "icon": "🚪", "alias": ("наплыв", "рейд", "raid"),
              "hard": frozenset({"raid", "raid_more", "cas", "namespam"}), "soft": frozenset({"capfail"})},
    "fakes": {"label": "самозванцы и подмены", "icon": "🎭", "alias": ("самозванцы", "подмена", "fakes"),
              "hard": frozenset({"impostor", "namespam"}), "soft": frozenset()},
    "noise": {"label": "флуд и поток реакций", "icon": "🌪", "alias": ("флуд", "шум", "noise"),
              "hard": frozenset({"react"}), "soft": frozenset({"flood"})},
    "heat":  {"label": "накал в чате", "icon": "🔥", "alias": ("накал", "ссора", "heat"),
              "hard": frozenset({"hate", "heat", "heat_bait"}), "soft": frozenset({"profanity"})},
    "adult": {"label": "18+ в чате", "icon": "🔞", "alias": ("18+", "adult"),
              "hard": frozenset({"minors", "adult"}), "soft": frozenset()},
}
AP_LEVEL_NAME = {0: "нет", 1: "лёгкий", 2: "средний", 3: "жёсткий"}
AP_TRIP = {
    "wave": ((2.5, 2), (5.0, 3), (8.0, 4)),
    "raid": ((2.0, 1), (4.5, 2), (7.5, 3)),
    "fakes": ((1.5, 2), (3.0, 3), (5.0, 4)),
    "noise": ((2.5, 2), (4.5, 3), (7.0, 4)),
    "heat": ((1.6, 2), (3.2, 3), (5.0, 4)),
    "adult": ((1.6, 2), (3.2, 3), (5.0, 4)),
}
AP_MEASURES = {
    "wave": {
        1: {"scam": True, "smart_links": True, "spam_memory": True, "puppet": True, "links": "trusted", "newbie_min": 30},
        2: {"captcha": True, "cas": True, "trace": "on", "jitter": False, "newbie_min": 120, "locks": ("invitelink", "contact")},
        3: {"slow": 4, "newbie_min": 360, "locks": ("channel", "forward", "story", "inline")},
    },
    "raid": {
        1: {"raid": True, "captcha": True, "captcha_smart": True, "clean_joins": True, "cas": True},
        2: {"captcha_timeout": 60, "captcha_ban_min": 30, "newbie_min": 90, "locks": ("invitelink",)},
        3: {"captcha_timeout": 45, "captcha_ban_min": 120, "newbie_min": 360, "slow": 5, "locks": ("contact", "forward", "channel")},
    },
    "fakes": {
        1: {"impostor": True},
        2: {"cas": True, "newbie_min": 180, "locks": ("contact", "channel")},
        3: {"captcha": True, "captcha_ban_min": 60, "newbie_min": 720, "locks": ("forward", "invitelink", "inline")},
    },
    "noise": {
        1: {"flood": True, "slow": 2},
        2: {"slow": 4, "locks": ("dice", "gif")},
        3: {"slow": 8, "locks": ("sticker", "voice", "videonote")},
    },
    "heat": {
        1: {"slow": 3, "conflicts": True, "hate": True},
        2: {"slow": 6, "profanity": True},
        3: {"slow": 10, "newbie_min": 60},
    },
    "adult": {
        1: {"adult": True},
        2: {"newbie_min": 240},
        3: {"locks": ("photo", "video", "gif")},
    },
}
AP_CALM = {"captcha_timeout": 120, "jitter": True}
AP_RANKS = {"links": ("open", "trusted", "admins"), "trace": ("off", "log", "on")}
AP_MAX_KEYS = frozenset({"slow", "newbie_min", "captcha_ban_min"})
AP_MIN_KEYS = frozenset({"captcha_timeout"})
AP_FALSE_STRICT = frozenset({"jitter"})
AP_KEEP = 0.6
AP_HOLD = {1: 240.0, 2: 420.0, 3: 600.0}
AP_REARM = 150.0
AP_OVERRIDE_COOL = 6 * 3600
AP_CALM_COOL = 24 * 3600
AP_SCAR_HALF, AP_SCAR_CAP = 7 * 86400, 4.0
AP_CALM_AFTER = 6 * 3600
AP_CALM_MIN_AGE = 24 * 3600
AP_MULT_MIN, AP_MULT_MAX = 0.5, 1.6
AP_NOTES_KEEP = 40
AP_STRICT_MIN = 30
AP_ALERT_COOL = 1200.0
AP_PULSE_WEIGHT = {"heat": 0.5, "heat_bait": 0.4}
AP_KIND_LABEL = {"heat": "травля", "heat_bait": "наживки"}
AP_OWNER_WHY = "owner"

AP_HID_MIN, AP_HID_MAX = 0.62, 1.45
AP_HID_HOLD_MIN, AP_HID_HOLD_MAX = 0.45, 2.2
AP_FINAL_MIN, AP_FINAL_MAX = 0.4, 2.0
AP_TREND_DT = 60.0
AP_TREND_UP, AP_TREND_BURST = 0.9, 2.2
AP_QUIET_S = 90.0
AP_QUIET_LONG = 180.0
AP_VIGIL_FRAC, AP_VIGIL_S = 0.4, 600.0
AP_PERSIST_S, AP_PERSIST_KEEP = 240.0, 0.85
AP_AFTER_S = 40 * 60.0
AP_NEIGHBOR_S = 30 * 60.0
AP_ADMIN_NEAR, AP_ADMIN_FAR = 240.0, 6 * 3600.0
AP_DOUBT_HALF, AP_DOUBT_CAP = 10 * 86400.0, 4.0
AP_COOL_MAX = 24 * 3600
AP_VEC_SRC = 3
AP_VEC_MEDIA = {"sticker": "sticker", "voice": "voice", "video_note": "videonote", "animation": "gif", "document": "document"}
AP_VEC_LOCKS = frozenset({"invitelink", "forward", "channel", "inline", "contact", "story"} | set(AP_VEC_MEDIA.values()))
AP_VEC_SRC_MEDIA = 4
AP_KNOWN_KINDS = frozenset({"scam_ban", "scam", "memory", "puppet", "cas", "impostor", "namespam", "react"})
AP_KNOWN_S, AP_KNOWN_Q, AP_KNOWN_CAP = 6 * 3600.0, 1.25, 4000
AP_BG_HALF = 2 * 86400.0
AP_BG_MIN, AP_BG_MAX = 0.95, 1.2
AP_BG_REFLEXES = frozenset({"wave", "raid", "noise", "heat"})
AP_VEC_REFLEXES = frozenset({"wave", "fakes", "raid"})
AP_COMBO = frozenset({"wave", "raid", "fakes", "noise"})
AP_SRC_Q = frozenset({"wave", "raid", "fakes", "adult"})
AP_STALE_S, AP_STALE_EVERY = 3 * 3600, 3 * 3600
AP_DBG_KEEP = 60


class Beat(NamedTuple):
    uid: int
    ts: float
    parent: int
    root: int
    roles: int
    contacts: tuple = ()


MEDIA_KINDS = {"photo", "video", "document", "voice", "video_note", "audio"}
STICKER_KINDS = {"sticker", "animation"}


@dataclass
class Ent:
    type: str
    text: str = ""
    url: str = ""
    user_id: int = 0


@dataclass
class Msg:
    chat_id: int
    msg_id: int
    user_id: int
    name: str = ""
    username: str = ""
    text: str = ""
    kind: str = "text"
    ents: list = field(default_factory=list)
    fwd: str = ""
    sender_chat: bool = False
    via_bot: bool = False
    edited: bool = False
    ts: float = 0.0
    reply_to: int = 0
    reply_uid: int = 0


@dataclass
class Verdict:
    delete: bool = False
    category: str = ""
    reasons: list = field(default_factory=list)
    score: float = 0.0
    strike: float = 0.0
    level: float = 0.0
    mute_s: int = 0
    ban: bool = False
    purge: bool = False
    alert: bool = False
    notice: str = ""
    info: dict = field(default_factory=dict)
    purge_s: int = 0
    strict_started: int = 0
    others: list = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not (self.delete or self.ban or self.mute_s)

    def why(self) -> str:
        return ", ".join(self.reasons[:3])


TLDS = set("""com net org ru su рф ua by kz uz md ge me io cc co ly gg tv ai fm ws xyz top site online shop store club live
life world fun pro info biz link click tk ml ga cf gq vip work today cloud app dev cn jp de uk fr es pl us ee lv lt cz sk bg
ro hu fi se no dk nl be ch at ca au nz br mx ar tr ir""".split())
SHORTENERS = {"bit.ly", "t.co", "tinyurl.com", "cutt.ly", "is.gd", "goo.gl", "ow.ly", "clck.ru", "vk.cc", "rb.gy",
              "tiny.cc", "shorturl.at", "u.to", "t.ly", "qr.ae", "buff.ly", "soo.gd", "trib.al", "lnkd.in", "v.gd",
              "rebrand.ly", "bl.ink", "s.id", "shorturl.asia"}
TG_HOSTS = {"t.me", "telegram.me", "telegram.dog"}
SECOND_LEVEL = {"co", "com", "org", "net", "gov", "edu", "ac"}

_URL_RE = re.compile(r"""(?ix)
    (?<![\w@.\-/])
    (?:(?P<scheme>https?://|ftp://)(?P<userinfo>[^\s/@]+@)?)?
    (?P<host>(?:[a-z0-9а-я](?:[a-z0-9а-я\-]{0,61}[a-z0-9а-я])?\.)+(?P<tld>xn--[a-z0-9\-]{2,40}|[a-zа-я]{2,24}))
    (?::(?P<port>\d{2,5}))?
    (?P<path>[/?\#][^\s<>"'«»]*)?
""")
_TLD_ALT = "|".join(sorted((t for t in TLDS if t.isascii()), key=len, reverse=True))
_DEOBF = (
    (re.compile(r"(?i)\bhxxp"), "http"),
    (re.compile(r"(?i)\s*[\[\(\{]\s*(?:dot|точка|\.)\s*[\]\)\}]\s*"), "."),
    (re.compile(r"(?i)(?<=\w)\s+(?:dot|точка)\s+(?=(?:" + _TLD_ALT + r")\b)"), "."),
)
_AUTH_END = re.compile(r"[/?#]")
_LONG_WS = re.compile(r"\s{16,}")
_IPV4 = re.compile(r"^\d{1,3}(?:\.\d{1,3}){3}$")


BRANDS: dict[str, set] = {
    "telegram": {"telegram.org", "t.me", "telegram.me", "telegram.dog", "telesco.pe", "tdesktop.com", "telegra.ph", "graph.org"},
    "discord": {"discord.com", "discord.gg", "discordapp.com", "discordapp.net", "discord.media"},
    "steam": {"steampowered.com", "steamcommunity.com", "steamstatic.com", "steamcontent.com", "steamgames.com", "valvesoftware.com"},
    "steamcommunity": {"steamcommunity.com"},
    "binance": {"binance.com", "binance.us", "binance.me"},
    "whatsapp": {"whatsapp.com", "whatsapp.net", "wa.me"},
    "google": {"google.com", "goo.gl", "googleusercontent.com", "googleapis.com", "gstatic.com", "withgoogle.com",
               "googlevideo.com", "googlemail.com", "google.co.uk", "google.com.ua"},
    "youtube": {"youtube.com", "youtu.be", "youtube-nocookie.com", "ytimg.com"},
    "instagram": {"instagram.com", "cdninstagram.com", "instagr.am"},
    "facebook": {"facebook.com", "fb.com", "fb.me", "fbcdn.net", "facebook.net", "messenger.com"},
    "tiktok": {"tiktok.com", "tiktokv.com", "tiktokcdn.com", "musical.ly"},
    "paypal": {"paypal.com", "paypal.me", "paypalobjects.com"},
    "apple": {"apple.com", "icloud.com", "cdn-apple.com", "mzstatic.com"},
    "microsoft": {"microsoft.com", "live.com", "office.com", "windows.com", "msn.com", "bing.com", "azure.com",
                  "microsoftonline.com", "xbox.com", "skype.com"},
    "amazon": {"amazon.com", "amzn.to", "amazonaws.com", "amazon.co.uk"},
    "netflix": {"netflix.com", "nflxso.net"},
    "sberbank": {"sberbank.ru", "sberbank.com", "sber.ru", "sbrf.ru"},
    "tinkoff": {"tinkoff.ru", "tbank.ru", "tinkoff.com"},
    "gosuslugi": {"gosuslugi.ru"},
    "yandex": {"yandex.ru", "yandex.com", "ya.ru", "yandex.net", "yandex.by", "yandex.kz", "yandex.ua", "yastatic.net"},
    "wildberries": {"wildberries.ru", "wb.ru", "wbstatic.net"},
    "avito": {"avito.ru"},
    "metamask": {"metamask.io"},
    "trustwallet": {"trustwallet.com"},
    "tether": {"tether.to"},
    "coinbase": {"coinbase.com"},
    "opensea": {"opensea.io"},
    "roblox": {"roblox.com", "rbxcdn.com"},
    "minecraft": {"minecraft.net", "mojang.com", "minecraftservices.com"},
    "fortnite": {"fortnite.com", "epicgames.com", "unrealengine.com"},
    "epicgames": {"epicgames.com"},
    "blizzard": {"blizzard.com", "battle.net"},
    "faceit": {"faceit.com"},
}
_OFFICIAL = set().union(*BRANDS.values())
BAIT = set("""free gift claim airdrop giveaway nitro bonus bonuses promo verify wallet reward prize casino jackpot usdt
cashback freebitcoin freespins spins 1win vulkan podarok bonusy халява подарок бонус выигрыш приз казино розыгрыш""".split())
SENSITIVE = set("login signin account secure update support confirm auth billing recovery restore community".split())
RISKY_TLDS = set("tk ml ga cf gq top xyz click link live site online club vip fun shop store work cc ws icu buzz rest "
                 "cyou monster sbs quest bond".split())
BAD_EXT = (".apk", ".exe", ".scr", ".bat", ".cmd", ".msi", ".jar", ".zip", ".rar", ".7z", ".iso", ".lnk", ".vbs",
           ".ps1", ".dmg", ".js", ".hta")
_REDIR_KEYS = {"url", "u", "link", "redirect", "redirect_uri", "redirect_url", "goto", "target", "dest", "destination",
               "out", "next", "continue", "ref_url", "return", "returnurl"}
_DOM_LEET = str.maketrans({"0": "o", "3": "e", "4": "a", "5": "s", "7": "t", "$": "s", "1": "l", "|": "l", "i": "l"})


def _skeleton(label: str) -> str:
    t = re.sub(r"[-_.]", "", label.lower()).replace("rn", "m").replace("vv", "w")
    return t.translate(_DOM_LEET)


def _typo_of(sq: str, brand: str) -> bool:
    if sq == brand:
        return False
    if len(sq) == len(brand):
        diff = [i for i in range(len(sq)) if sq[i] != brand[i]]
        return len(diff) == 2 and diff[1] == diff[0] + 1 and sq[diff[0]] == brand[diff[1]] and sq[diff[1]] == brand[diff[0]]
    if abs(len(sq) - len(brand)) == 1:
        a, b = (sq, brand) if len(sq) > len(brand) else (brand, sq)
        return any(a[:i] + a[i + 1:] == b for i in range(len(a)))
    return False


def _dga_like(label: str) -> bool:
    if label.startswith("xn--"):
        return False
    core = re.sub(r"[^a-z0-9]", "", label.lower())
    if len(core) < 9:
        return False
    letters = [c for c in core if c.isalpha()]
    digits = len(core) - len(letters)
    if digits >= 3 and len(letters) >= 3 and re.search(r"\d[a-z]+\d|[a-z]\d+[a-z]", core):
        return True
    if letters and sum(1 for c in letters if c in "aeiouy") / len(letters) < 0.2:
        return True
    return bool(re.search(r"[^aeiouy0-9]{6,}", core))


def _is_official(reg: str, host: str) -> bool:
    for off in _OFFICIAL:
        if reg == off or host == off or host.endswith("." + off):
            return True
    tld = reg.rsplit(".", 1)[-1]
    return reg.split(".")[0] in BRANDS and len(tld) == 2 and tld not in RISKY_TLDS


def smart_url_flags(host: str, reg: str, path: str) -> set:
    flags: set = set()
    if _is_official(reg, host):
        return flags
    parts = reg.split(".")
    tld = parts[-1]
    core = parts[0]
    labels = host.split(".")
    sub = labels[:max(0, len(labels) - len(parts))]
    pathl = path.lower()
    pure = pathl.split("?")[0].split("#")[0]
    tokens = {t for t in re.split(r"[^a-z0-9а-я]+", host + " " + pure) if t}
    bait = tokens & BAIT
    if len(bait) >= 2:
        flags.add("bait2")
    elif bait:
        flags.add("bait")
    sq = re.sub(r"[-_.]", "", core.lower())
    sk = _skeleton(core)
    for brand in BRANDS:
        if len(brand) < 5:
            continue
        bsk = _skeleton(brand)
        if sq == brand and tld in RISKY_TLDS:
            flags.add("lookalike")
        elif sq != brand and (sk == bsk or _typo_of(sq, brand)):
            flags.add("lookalike")
        elif brand in sq and sq != brand and (tokens & (BAIT | SENSITIVE) or tld in RISKY_TLDS):
            flags.add("lookalike")
        elif any(brand in re.sub(r"[-_.]", "", lab) for lab in sub):
            flags.add("brand_sub")
        if flags & {"lookalike", "brand_sub"}:
            break
    if tld in RISKY_TLDS:
        flags.add("risky_tld")
    if _dga_like(core):
        flags.add("random_host")
    if len(sub) >= 3:
        flags.add("deep_sub2" if any(t in SENSITIVE for lab in sub for t in re.split(r"[^a-z0-9]+", lab)) else "deep_sub")
    if pure.endswith(BAD_EXT):
        flags.add("download")
    q = path.split("?", 1)[1].lower() if "?" in path else ""
    for key, val in re.findall(r"(?:^|[&;])([a-z_]{1,20})=([^&#]{6,300})", q):
        if key in _REDIR_KEYS:
            mm = re.match(r"(?:https?:)?//([a-z0-9.\-а-я]+)", urllib.parse.unquote(val))
            if mm and reg_domain(mm.group(1).strip(".")) != reg:
                flags.add("redirect")
                break
    return flags


@dataclass
class UrlInfo:
    raw: str
    host: str
    reg: str
    kind: str
    flags: set = field(default_factory=set)


def reg_domain(host: str) -> str:
    parts = host.split(".")
    if len(parts) >= 3 and parts[-2] in SECOND_LEVEL and len(parts[-1]) == 2:
        return ".".join(parts[-3:])
    return ".".join(parts[-2:]) if len(parts) >= 2 else host


@lru_cache(maxsize=4096)
def _norm_item(item: str) -> str:
    item = item.strip().lower()
    item = re.sub(r"^[a-z]+://", "", item)
    return re.sub(r"^www\.", "", item).rstrip("/")


def _listed(host: str, path: str, items) -> bool:
    for it in items:
        it = _norm_item(it)
        if not it:
            continue
        h, _, p = it.partition("/")
        if host == h or host.endswith("." + h):
            pl = path.lstrip("/").lower()
            if not p or pl == p or pl.startswith((p + "/", p + "?", p + "#")):
                return True
    return False


def _idn_flags(host: str) -> tuple[str, set]:
    flags: set = set()
    uni = host
    if "xn--" in host:
        flags.add("punycode")
        try:
            uni = host.encode("ascii").decode("idna")
        except Exception:
            uni = host
    for label in uni.split("."):
        has_lat = bool(re.search(r"[a-z]", label))
        has_cyr = bool(re.search(r"[а-я]", label))
        other = any(ord(c) > 127 and not re.match(r"[а-я]", c) and c.isalpha() for c in label)
        if (has_lat and has_cyr) or (other and has_lat):
            flags.add("idn_mixed")
    return uni, flags


def classify_url(host: str, path: str, cfg: ChatCfg, scheme: str = "", userinfo: str = "") -> UrlInfo:
    host = host.lower().strip(".")
    host = re.sub(r"^www\.", "", host)
    uni, flags = _idn_flags(host)
    if userinfo:
        flags.add("userinfo")
    reg = reg_domain(host)
    info = UrlInfo(raw=host + path, host=host, reg=reg, kind="unknown", flags=flags)
    allow = list(DEFAULT_ALLOW) + list(cfg.allow)
    if _listed(host, path, cfg.block):
        info.kind = "blocked"
    elif _IPV4.match(host):
        info.kind = "ip"
    elif host in SHORTENERS or reg in SHORTENERS:
        info.kind = "shortener"
    elif host in TG_HOSTS:
        seg = [s for s in path.split("?")[0].split("/") if s]
        first = seg[0].lower() if seg else ""
        if _listed(host, path, cfg.allow):
            info.kind = "allowed"
        elif first.startswith("+") or first in ("joinchat", "addlist"):
            info.kind = "invite"
        elif path.split("?")[0].count("/") >= 2 and first == "c":
            info.kind = "tg_channel"
        elif "start=" in path or first.endswith("bot"):
            info.kind = "tg_bot"
        else:
            info.kind = "tg_channel"
    elif _listed(host, path, allow):
        info.kind = "allowed"
    if info.kind == "unknown" and cfg.smart_links:
        info.flags |= smart_url_flags(host, reg, path)
    return info


def extract_urls(text: str, ents, cfg: ChatCfg) -> list[UrlInfo]:
    clean = _LONG_WS.sub(" ", text.translate(_ZW_DEL)[:4500])
    for rx, rep in _DEOBF:
        clean = rx.sub(rep, clean)
    out: list[UrlInfo] = []
    seen: set = set()

    def add(info: UrlInfo) -> None:
        key = (info.host, info.raw)
        if key not in seen:
            seen.add(key)
            out.append(info)

    for m in _URL_RE.finditer(clean):
        host, tld = m.group("host").lower(), m.group("tld").lower()
        if not (m.group("scheme") or host.startswith("www.") or tld in TLDS or tld.startswith("xn--")):
            continue
        add(classify_url(host, m.group("path") or "", cfg, m.group("scheme") or "", m.group("userinfo") or ""))

    for m in re.finditer(r"(?i)\btg://([a-z_]+)[^\s<>\"']*", clean):
        kind = "invite" if m.group(1).lower() in ("join", "addlist") else "tg_bot" if "start=" in m.group(0).lower() else "tg_channel"
        add(UrlInfo(raw=m.group(0)[:80], host="tg://" + m.group(1).lower(), reg="tg://", kind=kind, flags=set()))

    for e in ents or []:
        if e.type == "text_link" and e.url:
            try:
                after = re.sub(r"^[a-z]+://", "", e.url.strip(), flags=re.I)
                cut = _AUTH_END.search(after)
                authority, path = (after[:cut.start()], after[cut.start():]) if cut else (after, "")
                userinfo, _, hostport = authority.rpartition("@")
                host = hostport.split(":", 1)[0]
                if "." not in host and not _IPV4.match(host):
                    continue
                info = classify_url(host, path, cfg, "https://", userinfo)
            except Exception:
                continue
            vis = e.text or ""
            vm = _URL_RE.search(vis.translate(_ZW_DEL))
            if vm and (vm.group("scheme") or vm.group("tld").lower() in TLDS):
                if reg_domain(re.sub(r"^www\.", "", vm.group("host").lower())) != info.reg:
                    info.flags.add("mismatch")
            elif info.kind != "allowed":
                info.flags.add("hidden")
            add(info)
    return out


def R(p: str):
    return re.compile(p.replace("й", "и").replace("ё", "е"))


SPAM_RULES = [
    ("earn_pitch", "job", 2.5, R(r"\b(?:зараб\w*|доход\w*|прибыл\w*)\b[^.!?\n]{0,60}\b(?:без вложени|от \d|в день|в неделю|в месяц|в час|удаленн|на дому|каждый день|ежедневно)"), "обещание лёгкого заработка"),
    ("earn_online", "job", 2.5, R(r"\b(?:зарабатыва\w+|заработк\w*)\s+(?:на\s+телефон\w*|в\s+интернет\w*|в\s+сети|онлайн|удаленн\w+|в\s+телеграм\w*|на\s+дому|с\s+телефона)"), "заработок в сети / на телефоне"),
    ("earn_word", "job", 1.5, R(r"\b(?:зарабатыва\w+|заработк\w*)\b"), "разговор о заработке"),
    ("extra_income", "job", 2.0, R(r"\bдополнительн\w+\s+(?:источник\w*\s+)?(?:доход|заработ|прибыл)\w*|\bдоп\.?\s*(?:доход|заработ)\w*|\bподработк\w+\s+(?:на\s+телефон|онлайн|в\s+интернет)"), "«дополнительный доход»"),
    ("fin_pos", "job", 2.0, R(r"(?:улучш\w+|поправ\w+|измен\w+)\s+(?:своё\s+|свое\s+|свою\s+|своего\s+)?(?:финансов\w+|материальн\w+)\s+(?:положени|ситуаци|состояни)\w*"), "«улучшить финансовое положение»"),
    ("fin_free", "job", 0.8, R(r"\bфинансов\w+\s+(?:независимост|свобод)\w*"), "«финансовая независимость»"),
    ("pass_daily", "job", 2.0, R(r"\b(?:ежедневн\w+|стабильн\w+|регулярн\w+)\s+пассив\w*|\bпассив\w*\s+(?:ежедневн|каждый\s+день)"), "«ежедневный пассив»"),
    ("phone_work", "job", 2.5, R(r"\b(?:работ\w+|подработк\w+|заработ\w+)\s+(?:только\s+)?(?:на|с)\s+телефон\w*|\bнужен\s+(?:только|лишь|всего)\s+(?:телефон|смартфон)\b(?!\s+для)"), "работа «только с телефона»"),
    ("paid_daily", "job", 2.0, R(r"\bплат(?:ят|им|ит)\s+(?:каждый\s+день|ежедневн\w+)"), "«платят каждый день»"),
    ("cta_plus", "cta", 2.0, R(r"\b(?:пиши|пишите)\s*(?:мне\s+)?\+(?!\w)"), "«пиши +»"),
    ("hours_day", "job", 2.0, R(r"\bзанима\w+\s+(?:всего\s+|от\s+|около\s+)?\d[\d\-–]*\s*час\w*\s+в\s+день|\b\d[\d\-–]*\s*час\w*\s+в\s+день\b[^.!?\n]{0,30}(?:доход|заработ|₽|руб)"), "«пара часов в день» + доход"),
    ("income_daily", "job", 2.5, R(r"\d[\d\s]*(?:₽|руб\w*|usd|\$|долл\w*)\s*(?:ежедневно|еженедельно|ежемесячно)"), "сумма «ежедневно»"),
    ("income_goal", "job", 2.5, R(r"\b(?:выйти|выйдешь|выйдете|выходи\w*|получа\w+|получить)\s+на\s+доход\w*|\bдоход\w*\s+(?:от\s+)?\d[\d\s]*(?:тыс\w*|к\b|000)"), "обещание дохода в цифрах"),
    ("target_group", "job", 2.0, R(r"\b(?:для|подойд\w+)\s+(?:студент\w*|школьник\w*|пенсионер\w*|мам\w*(?:\s+в\s+декрет\w*)?|домохозяек|декретниц\w*)\b[^.!?\n]{0,40}(?:работ|доход|заработ|подработ)|\bмам\w*\s+в\s+декрет\w*"), "«для студентов и мам в декрете»"),
    ("closed_set", "job", 2.0, R(r"\bнабор\w*\s+в\s+(?:закрыт\w+|приватн\w+)\s+\w+"), "набор в закрытое сообщество"),
    ("signals", "invest", 2.0, R(r"\b(?:проверенн\w+|рабочи\w+|платн\w+|vip)\s+сигнал\w*"), "платные/«проверенные» сигналы"),
    ("proven_way", "job", 1.5, R(r"\b(?:проверенн\w+|рабочий)\s+(?:способ|метод)\b|\bрабочая\s+схема\b"), "«проверенный способ / рабочая схема»"),
    ("stable_result", "job", 1.2, R(r"\bрезультат\w*\s+с\s+перв\w+\s+(?:дня|недели|дней|дн\w+)"), "«результат с первого дня»"),
    ("collab_ask", "job", 1.5, R(r"\bищу\s+(?:ответственн\w+|надежн\w+|активн\w+|целеустремленн\w+|целеустремлённ\w+)\s+людей\s+для\s+сотрудничеств\w*|\bвзаимовыгодн\w+\s+сотрудничеств\w*"), "«ищу людей для сотрудничества»"),
    ("loan_nocheck", "invest", 2.2, R(r"\b(?:кредит\w*|займ\w*|деньги|ссуд\w*)\s+(?:на\s+карту\s+)?без\s+(?:отказ\w*|проверок|справок|залога|поручител\w*|кредитной\s+истори\w*)"), "«кредит без отказа/проверок»"),
    ("no_deposit", "job", 2.0, R(r"\bбез\s+(?:вложени\w*|опыта|рисков?)\b"), "«без вложений/опыта»"),
    ("passive", "job", 2.0, R(r"\bпассивн\w+\s+(?:доход|заработок)"), "пассивный доход"),
    ("side_job", "job", 1.5, R(r"\b(?:удаленн\w+|дистанционн\w+)\s+(?:работ\w*|занятост\w*|сотрудничеств\w*|подработк\w*)|\bподработк\w*|\bудаленк\w*"), "подработка / удалённая работа"),
    ("hiring", "job", 2.0, R(r"\b(?:набира\w+|требу\w+|нужн\w+|ищу|ищем)\s+(?:в\s+команду\s+)?(?:люде\w+|сотрудник\w*|парн\w+|девуш\w+|менеджер\w*|партн\w+|курьер\w*)"), "набор сотрудников"),
    ("income_num", "job", 3.0, R(r"(?:(?:\bот|\bдо)\s*|(?<![\d\s.,]))(?=([\s.,]*\d[\d\s.,]{2,}))\1(?:₽|руб\w*|\bр\b|usd|\$|долл\w*|евро|€|тыс\w*|\bк\b)\s*(?:в|за|/)\s*(?:день|сутк\w*|недел\w*|час|мес\w*)"), "сумма «в день/неделю»"),
    ("cta_dm", "cta", 2.0, R(r"\b(?:пиш\w+|напиш\w+|стучи\w*|обращай\w+|звони\w*)\s+(?:мне\s+|нам\s+|в\s+|на\s+)*(?:л\.?с\b|личк\w*|лс\b|директ\w*|telegram|телеграм\w*|тг\b|whatsapp|вацап\w*|ватсап\w*)|(?:^|\s)\+\s*(?:в\s+)?(?:л\.?с|личку|лс)\b"), "зовёт в личку"),
    ("dm_hint", "cta", 1.2, R(r"(?:^|[\s,.;:!?])(?:в\s+)?(?:л\.?с|личк\w+|личны\w+\s+сообщени\w+|директ)(?=$|[\s,.;:!?)])|\b(?:пиши|пишите|стучи)(?:\s+(?:мне|нам))?\W*$"), "«в лс» / «пиши»"),
    ("detail_dm", "cta", 2.0, R(r"\b(?:подробност\w*|детал\w*|расскаж\w+|объясн\w+|покаж\w+|инструкци\w*|условия|делюс\w+|поделюсь|делимся)\b[^.!?\n]{0,25}\b(?:в|через|по)\s+(?:личн\w+|приватн\w+|лс|личк\w+|директ|тг|телеграм\w*)(?!\w)"), "детали — только в личке"),
    ("dm_full", "cta", 2.0, R(r"\b(?:пиш\w+|напиш\w+)\s+(?:мне\s+|нам\s+)?(?:в\s+)?(?:личн\w+|приватн\w+)\s+сообщени\w+|\bсвяж\w*(?:сь|итесь)\s+(?:со\s+мной|с\s+нами)"), "зовёт написать/связаться"),
    ("cta_word", "cta", 2.5, R(r"\b(?:пиш\w+|напиш\w+)\s+(?:мне\s+)?(?:кодовое\s+)?(?:слово|цифру|плюс)\s*[«\"“]?\w+"), "«напиши слово …»"),
    ("interested_write", "cta", 1.5, R(r"\b(?:интересно|заинтересовал\w*|кому\s+надо|нужно)\W+(?:пиш\w+|напиш\w+)\W*$"), "«интересно — напишите»"),
    ("cta_profile", "cta", 2.5, R(r"\b(?:жми\w*|нажим\w+|кликай\w*|переход\w+|переходи\w*)\s+(?:на\s+|по\s+)?(?:аватар\w*|ссылк\w*|профил\w*|кнопк\w*)|\bссылк\w*\s+(?:в|на)\s+(?:профил\w*|шапк\w*|описани\w*|bio)|\b(?:в|на)\s+(?:шапке|описании)\s+профил\w*"), "«ссылка в профиле»"),
    ("subscribe", "cta", 1.2, R(r"\bподпиш\w+\s+(?:на|в)\s+(?:мо\w+\s+)?(?:канал|группу|чат)|\bподписывай\w+"), "зовёт подписаться"),
    ("tg_promo", "cta", 1.5, R(r"\bмой\s+(?:канал|чат|бот)\b|\bзаходи\w*\s+(?:в\s+)?(?:мой\s+)?(?:канал|чат|группу)\b|\bприсоединяй\w+\b"), "реклама канала/чата"),
    ("urgency", "urgency", 1.5, R(r"\b(?:только\s+сегодня|успей\w*|осталось\s+\d+\s+мест\w*|количество\s+мест\s+ограничено|последн\w+\s+шанс|ограниченн\w+\s+предложени\w+|акция\s+заканчивается)"), "давление срочностью"),
    ("crypto", "invest", 1.2, R(r"\b(?:крипт\w*|биткоин\w*|bitcoin|usdt|трейдинг\w*|трейдер\w*|арбитраж\w*|binance|бинанс\w*|p2p|инвестици\w*|форекс|forex|майнинг\w*)\b"), "крипта / инвестиции"),
    ("invest_promise", "invest", 3.0, R(r"\b(?:удво\w+|умнож\w+|гарантир\w+|гарантия)\b[^.!?\n]{0,40}\b(?:доход\w*|прибыл\w*|депозит\w*|вклад\w*|инвестици\w*)|\b\d{2,4}\s?%\s+(?:в|за)\s+(?:день|недел\w*|месяц)"), "гарантированная прибыль"),
    ("casino", "gamble", 2.5, R(r"\b(?:казино|слоты?|букмекер\w*|ставк\w+\s+на\s+спорт|фрибет\w*|1win|1xbet|joycasino|casino|jackpot|джекпот)\b"), "казино / ставки"),
    ("bonus_dep", "gamble", 2.0, R(r"\b(?:бонус\w*|фрибет\w*|фриспин\w*|кэшбэк\w*)\b[^.!?\n]{0,40}\b(?:депозит\w*|регистрац\w*|пополнен\w*|первый\s+взнос)"), "бонус за депозит/регистрацию"),
    ("promo_weak", "gamble", 1.2, R(r"\b(?:промокод\w*|бонус\w*\s+(?:за|при)\s+регистрац\w*)"), "промокод / бонус за регистрацию"),
    ("adult_ad", "adult_ad", 2.5, R(r"\b(?:интим\w*\s+(?:услуг\w*|досуг\w*|знакомств\w*)|досуг\s+для\s+взросл\w+|эскорт\w*|секс\s*знакомств\w*|девушк\w+\s+(?:ждут|для\s+(?:встреч|общени\w+|знакомств\w*|досуг\w*)|без\s+обязательств)|общени\w+\s+без\s+обязательств|знакомств\w+\s+для\s+взросл\w+)"), "реклама 18+"),
    ("age18", "adult_ad", 1.0, R(r"(?:^|\s)18\s?\+"), "метка 18+"),
    ("sale_spam", "sale", 2.0, R(r"\b(?:продам|продаю|куплю|покупаю)(?:\s+и\s+(?:продам|куплю))?\s+(?:аккаунт\w*|акк\w*|базу|базы|подписчик\w*|трафик|логин\w*)|\bнакрутк\w*|\bраскрутк\w*\s+(?:канал\w*|аккаунт\w*|групп\w*)|\bдиплом\w*\s+(?:купить|заказать)|\bсправк\w+\s+без\b|\bдроп(?:ы|ов|ам|ами|ах|у|а)?\b|\bдроп\s*карт\w*"), "продажа аккаунтов / серые схемы"),
    ("cashout", "illegal", 3.0, R(r"\bобнал\w*|\bкардинг\w*|\bсливаем?\s+карт\w*"), "обнал / серые схемы"),
    ("occult", "sale", 2.0, R(r"\b(?:снят\w+\s+порч\w*|сниму\s+порч\w*|приворот\w*|гадани\w+\s+на\s+картах|гадалк\w*|ясновидящ\w*|магическ\w+\s+помощ\w*)"), "услуги «магов»"),
    ("webcam", "adult_ad", 2.5, R(r"\b(?:вебкам\w*|webcam\s+(?:job|model)s?|работа\s+для\s+девушек|девушк\w+\s+(?:на|для)\s+(?:удаленн\w+|работ\w*))"), "вебкам / работа для девушек"),
    ("loan_spam", "sale", 3.0, R(r"\b(?:кредит\w*|займ\w*|микрозайм\w*|ссуд\w*)\s+(?:без\s+(?:отказ\w*|проверк\w*|справок|залога|процентов)|на\s+карту\s+без)"), "«кредит без отказа»"),
    ("drugs_sale", "illegal", 2.5, R(r"\b(?:мефедрон\w*|гашиш\w*|амфетамин\w*|кокаин\w*|шишки|альфа\s*пвп)\b[^.!?\n]{0,60}\b(?:закладк\w*|доставк\w*|круглосуточно|заказать|купить|оптом|кладмен\w*)|\b(?:закладк\w*|доставк\w*|кладмен\w*)\b[^.!?\n]{0,60}\b(?:мефедрон\w*|гашиш\w*|амфетамин\w*|кокаин\w*|шишки)"), "продажа запрещённых веществ"),
    ("drugs", "illegal", 3.0, R(r"\b(?:мефедрон\w*|гашиш\w*|амфетамин\w*|кокаин\w*|альфа\s*пвп)\b|\bзакладк\w+\s+(?:по\s+городу|в\s+городе|круглосуточно)|\bкупить\s+(?:шишки|траву|меф)\b"), "запрещённые вещества"),
    ("giveaway", "promo", 1.2, R(r"\b(?:розыгрыш\w*|раздач\w+\s+(?:денег|призов|подарк\w*)|бесплатно\s+получи\w*|выиграй\w*|подарок\s+за\s+подписк\w*|получи\w*\s+(?:подарок|приз|бонус))"), "розыгрыш-приманка"),
    ("en_earn", "job", 3.0, R(r"\b(?:earn|make)\s+\$?\d[\d,.]*\s*(?:k|usd|dollars)?\s*(?:(?:per|a|every|/)\s*(?:day|hour|week|month)|daily|hourly|weekly|monthly)\b|\bpassive\s+income\b|\bwork\s+from\s+home\b|\bmake\s+money\s+online\b"), "earn-per-day pitch"),
    ("en_cta", "cta", 2.0, R(r"\b(?:dm|message|text|contact)\s+me\b|\bcheck\s+(?:my|the)\s+(?:bio|profile|link)\b|\bclick\s+(?:the\s+)?link\b|\blink\s+in\s+(?:my\s+)?(?:bio|profile)\b|\bjoin\s+(?:my|our)\s+(?:channel|group|telegram)\b"), "DM / link bait"),
    ("en_invest", "invest", 1.5, R(r"\b(?:invest\w*|crypto\w*|bitcoin|forex|trading\s+signals?|binance|airdrop)\b"), "crypto / invest"),
    ("en_promo", "promo", 1.5, R(r"\bfree\s+(?:gift|money|nitro|robux|vbucks)\b|\bgiveaway\b|\blimited\s+(?:time\s+)?offer\b|\bclaim\s+your\b"), "free-gift bait"),
]
SQUASH_RULES = [
    ("sq_earn", "job", 1.5, R(r"заработ|зарабатыва"), "заработок (буквы разнесены)"),
    ("sq_nodep", "job", 2.0, R(r"безвложен"), "«без вложений» (буквы разнесены)"),
    ("sq_income", "job", 2.0, R(r"(?:руб|рублей|рубля|usd|доллар\w*)в(?:день|неделю|месяц|час)|пассивныйдоход"), "сумма «в день» (буквы разнесены)"),
    ("sq_cta", "cta", 2.0, R(r"пиши(?:мне)?в(?:лс|личку|директ)|пишитев(?:лс|личку)|писатьв(?:лс|личку)"), "зовёт в личку (буквы разнесены)"),
    ("sq_gamble", "gamble", 2.5, R(r"казино|фрибет|ставкинаспорт"), "казино/ставки (буквы разнесены)"),
]
FAMILIES = {
    "money": R(r"\b(?:деньг\w*|заработ\w*|зарабат\w*|доход\w*|прибыл\w*|оплат\w*|зарплат\w*|выплат\w*|платят|платим|кредит\w*|займ\w*|инвест\w*|крипт\w*|биткоин\w*|депозит\w*|баксов|usdt|btc|usd|\$\s?\d+|\d+\s?\$|money|income|profit|earn\w*|cash|crypto\w*|invest\w*|salary|paid|payment|bitcoin|tokens?)"),
    "work": R(r"\b(?:работ[аыуе]|подработ\w*|вакан\w*|набор|удаленк\w*|требуются|нужны\s+люди|сотрудничеств\w*|партн[её]р\w*|бизнес\w*|график|без\s+опыта|без\s+вложени\w*|job|hiring|vacanc\w*|part-time|no\s+experience|from\s+home|business|opportunity|remote)"),
    "cta": R(r"\b(?:пиши\w*|напиш\w*|обращайтесь|л\.?с|личк\w*|личны\w+\s+сообщени\w*|директ\w*|жми\w*|нажм\w*|нажим\w*|переход\w*|ссылк\w*|профил\w*|аватар\w*|подписывай\w*|подпишись|канал\w*|заходи\w*|регистрац\w*|тг|телеграм\w*|вацап\w*|ватсап\w*|whatsapp|dm|message\s+me|text\s+me|contact\s+me|link|bio|profile|join|click|register|sign\s?up)"),
    "hype": R(r"\b(?:бесплатн\w*|халяв\w*|дешев\w*|недорог\w*|быстр\w*|гаранти\w*|выигра\w*|приз\w*|подар\w*|бонус\w*|акци[яи]\w*|скидк\w*|срочно|только\s+сегодня|ограничен\w*|успей\w*|100\s?%|без\s+отказа|free|giveaway|cheap|fast|quick|guarantee\w*|bonus|prize|limited|claim|win)"),
    "sale": R(r"\b(?:продам|продаю|куплю|покупаю|накрутк\w*|раскрутк\w*|подписчик\w*|аккаунт\w*|баз[уы]|дроп\w*|обнал\w*|услуг\w*|заказать|порч\w*|приворот\w*)"),
}
PITCH_GROUPS = {"job", "invest", "gamble", "sale", "adult_ad", "illegal", "promo"}
SHADOWS = {"dm_hint": {"cta_dm", "cta_profile", "en_cta", "sq_cta"},
           "earn_word": {"earn_pitch", "earn_online", "income_num", "en_earn", "sq_income", "passive"},
           "promo_weak": {"casino", "sq_gamble"}}
HARD_SIGNALS = {"wave", "pitch_cta", "families3", "lookalike", "brand_sub", "download", "campaign", "contact_net", "learned_spam", "puppet", "trace_inject", "trace_canned", "trace_combo2", "giveaway_combo"}

_PHONE_RE = re.compile(r"(?<![\d\w])(?:\+?\d{1,3}[\s\-.]?)?(?:\(\d{3}\)|\d{3})[\s\-.]?\d{3}[\s\-.]?\d{2}[\s\-.]?\d{2}(?![\d\w])")
_WALLET_RE = re.compile(r"\b0x[a-fA-F0-9]{40}\b|\bT[1-9A-HJ-NP-Za-km-z]{33}\b|\bbc1[a-z0-9]{25,60}\b")
_RUN_RE = {}
_HANDLE_RE = re.compile(r"@[A-Za-z0-9_]{4,32}")


_ASK_RX = (
    R(r"\b(?:кто|кто-?нибудь|кто-?то|есть\s+кто|может\s+(?:кто|кому))\b[^.!?\n]{0,40}\b(?:пробовал\w*|пользовал\w*|пользуется|юзал\w*|знает|слышал\w*|сталкивал\w*|работал\w*|выводил\w*|проверял\w*|в\s+курсе|имел\w*\s+дел\w*)"),
    R(r"\b(?:надежн\w*|безопасн\w*|нормальн\w+|проверенн\w+)\s+(?:ли|это)\b|\b(?:надежн\w*|безопасн\w*|легитимн\w*)\s*\?|\b(?:это\s+)?(?:не\s+)?(?:развод|лохотрон|скам|обман|кидалово|разводня)\s+(?:ли|или)\b|\bне\s+(?:развод|лохотрон|скам|обман|кидалово)\s*\?"),
    R(r"\b(?:стоит|есть\s+смысл|имеет\s+смысл)\s+ли\b|\b(?:работает|платит|выводит|выводят|платят|легитимн\w*|реально)\s+ли\b"),
    R(r"\b(?:подскажит\w*|посоветуйт\w*|подскажи|посоветуй)\b[^.!?\n]{0,50}\b(?:обменник\w*|обменк\w*|сайт\w*|бот\w*|платформ\w*|бирж\w*|проект\w*|сервис\w*|трейдер\w*|заработ\w*|брокер\w*|кошел\w*)"),
    R(r"\bгде\s+(?:можно\s+|лучше\s+|удобнее\s+|выгодн\w+\s+|реально\s+)?(?:обменять|поменять|вывести|обналичить|заработать|купить\s+usdt|купить\s+крипт\w*)"),
    R(r"\b(?:anyone|anybody|somebody|someone)\s+(?:here\s+)?(?:tried|used|know|knows|heard|worked|has\s+experience)\b|\bis\s+(?:it|this|that)\s+(?:legit|safe|real|a\s+scam|worth)\b|\b(?:any|got\s+any)\s+(?:experience|feedback|reviews?)\b|\bworth\s+(?:it|trying)\b|\b(?:legit|scam)\s*\?"),
)
_CLAIM_RX = R(r"\b(?:вывел\w*|вывод\w*|получил\w*|заработал\w*|заработок|снял\w*|пришл\w+|пришло|зашл\w+|зачислил\w*|выплат\w*|платят|платит|платил\w*|работает|рабочий|рабочая|проверен\w*|проверил\w*|советую|рекомендую|рекомендуем|пользуюсь|пользуемся|без\s+обмана|без\s+развода|гарантир\w+|легитимн\w*|legit|works|paid|withdrew|withdrawn|earn\w*|profit|recommend\w*|trusted)\b")
_MONEY_RX = R(r"(?<![\d\s.,])(?=([\s.,]*\d[\d\s.,]*))\1(?:\$|usd|usdt|бакс\w*|долл\w*|руб\w*|₽|евро|€|тыс\w*)|\$\s?\d+")
_CONFIRM_RX = (
    R(r"(?<!не )\b(?:проверил\w*|проверен\w*|проверено|сработал\w*|получилось|получил\w*|вывел\w*|пришл\w+|пришло|зашл\w+|зачислил\w*|выплатил\w*|платит|платят|работает|рабочий|рабочая|подтверждаю)\b|\bне\s+(?:развод|обман|скам|кидал\w*)\b|\bбез\s+(?:обмана|развода)\b"),
    R(r"\bспасибо\s+(?:за\s+(?:ссылку|совет|инфу|информаци\w+|наводку|подсказку|контакт)|большое|огромное|друг|братан|брат)\b|\bблагодар\w+\s+за\s+(?:ссылку|совет|инфу|информаци\w+)|\bтоже\s+(?:вывел\w*|получил\w*|пользуюсь|пробовал\w*|проверил\w*)\b"),
    R(r"\b(?:thanks|thank\s+you|thx)\b[^.!?\n]{0,30}\b(?:link|info|tip|sharing|share)\b|\b(?:it|this)\s+(?:works|worked|pays|paid)\b|\bgot\s+paid\b|\bwithdrew\b|\bwithdrawn\b|\bconfirm(?:ed)?\b|\blegit\b|\bworks\s+(?:great|fine|well)\b"),
)
_DM_SIGNALS = frozenset({"cta_dm", "dm_hint", "cta_profile", "en_cta", "sq_cta", "tg_promo", "cta"})

_BAIT_RX = (
    R(r"\bникто\s+(?:(?:тебя|тут|здесь)\s+){0,2}(?:не\s+)?(?:слуша\w*|ждал\w*|просил\w*|читает|спрашивал\w*)"),
    R(r"\b(?:что[-\s]?то|чего)\s+ты\s+(?:сегодня\s+|опять\s+|так\s+)?(?:нервн\w*|злой|злая|не\s+в\s+духе|агрессивн\w*|раздражен\w*|завелс\w*)"),
    R(r"\b(?:ты|тебя|тебе)\b[^.!?\n]{0,40}\bпроблемы\s+(?:дома|с\s+головой|в\s+личной\s+жизни|в\s+жизни|с\s+нервами)\b"),
    R(r"\bтебе\s+(?:надо|нужно|пора|стоит)\s+(?:лечиться|к\s+врачу|к\s+психиатру|успокоиться|проспаться|подлечиться)\b"),
    R(r"\b(?:успокойся|не\s+нервничай|не\s+истери|иди\s+проспись|остынь)\b"),
    R(r"\bне\s+позорься\b|\bпозорище\b|\bсколько\s+тебе\s+лет\b|\bдетский\s+сад\b"),
    R(r"\bты\s+(?:что|чего)\b[^.!?\n]{0,12}\b(?:дурак|дура|тупой|тупая|глупый|глупая|совсем)\b"),
    R(r"\bну\s+ты\s+и\s+(?:клоун|шут|тролль|умник)\b|\bумник\s+нашелся\b|\bсамый\s+умный\b"),
    R(r"\b(?:ноешь|нытик|опять\s+ты|опять\s+ноешь|опять\s+начинается)\b"),
    R(r"\bкак\s+обычно\b[^.!?\n]{0,30}\bты\b|\bты\b[^.!?\n]{0,30}\bкак\s+обычно\b"),
    R(r"\bnobody\s+(?:asked|cares)\b|\bcalm\s+down\b|\btouch\s+grass\b|\bget\s+a\s+life\b|\bproblems\s+at\s+home\b"),
)


def puppet_roles(folded: str, kind: str = "text", contact: bool = False, dm: bool = False) -> int:
    t = folded[:1500]
    roles = 0
    if t.strip():
        n = len(t)
        if n <= 300 and any(rx.search(t) for rx in _ASK_RX):
            roles |= ROLE_ASK
        if (contact or dm) and (_CLAIM_RX.search(t) or FAMILIES["money"].search(t) or _MONEY_RX.search(t)):
            roles |= ROLE_PITCH
        if n <= 250 and "?" not in t and any(rx.search(t) for rx in _CONFIRM_RX):
            roles |= ROLE_CONFIRM
    elif kind in ("photo", "video"):
        roles |= ROLE_CONFIRM
    return roles


def contact_tokens(urls, handles, raw_text: str) -> tuple:
    out: list = [h.lower() for h in handles]
    for u in urls:
        if u.kind == "unknown" and u.reg:
            out.append(u.reg)
        elif u.kind in ("tg_channel", "tg_bot", "invite"):
            segs = [s for s in u.raw[len(u.host):].split("?")[0].split("/") if s]
            if not segs:
                continue
            if u.kind == "invite":
                out.append("t.me/" + "/".join(segs[:2] if segs[0].lower() in ("joinchat", "addlist") else segs[:1]))
            elif segs[0].lower() != "c" and re.fullmatch(r"[A-Za-z0-9_]{4,32}", segs[0]):
                out.append("@" + segs[0].lower())
    for mt in _PHONE_RE.finditer(raw_text):
        digits = re.sub(r"\D", "", mt.group(0))
        if len(digits) >= 10:
            out.append("tel:" + digits[-10:])
    return tuple(dict.fromkeys(out))[:8]


_EMOJI_RE = re.compile("[\U0001F000-\U0010FFFF\u2600-\u27BF⭐⬆✅❌]")


def count_emoji(s: str) -> int:
    return len(_EMOJI_RE.findall(s))


FOREIGN_SCRIPTS = True
FOREIGN_MIN = 10
_FOREIGN_RANGES = ((0x0600, 0x06FF), (0x0750, 0x077F), (0x0900, 0x097F), (0x0E00, 0x0E7F), (0x3040, 0x30FF),
                   (0x3400, 0x4DBF), (0x4E00, 0x9FFF), (0xAC00, 0xD7AF))


_FOREIGN_RE = re.compile("[" + "".join(f"{chr(lo)}-{chr(hi)}" for lo, hi in _FOREIGN_RANGES) + "]")


def foreign_letters(s: str) -> int:
    return len(_FOREIGN_RE.findall(s))


_LEETMAP = str.maketrans({"@": "a", "$": "s", "0": "o", "1": "i", "3": "e", "4": "a", "5": "s", "7": "t"})


_LEET_TOK = re.compile(r"(?<!\S)\S*[@$013457]\S*")


def deleet(folded: str) -> str:
    def fix(m):
        t = m.group(0)
        return t.translate(_LEETMAP) if re.search(r"[a-zа-я]", t) and re.search(r"[@$013457]", t) else t
    return _LEET_TOK.sub(fix, folded)


def deglyph(folded: str) -> str:
    def fix(m):
        t = m.group(0)
        if re.search(r"[a-z]", t) and re.search(r"[а-я]", t) and not re.search(r"\d", t):
            return "".join(LAT2CYR.get(c, c) for c in t)
        return t
    return re.sub(r"[^\W_]+", fix, folded)


_BIT_TR = bytes.maketrans(b"01", b"\x00\x01")


@lru_cache(maxsize=512)
def fingerprint(folded: str) -> tuple[int, int, int]:
    t = re.sub(r"https?://\S+|www\.\S+", " u ", folded)
    t = re.sub(r"@\w+", " m ", t)
    t = re.sub(r"\d+", "#", t)
    toks = re.findall(r"[^\W_#]+|#", t)
    if not toks:
        return 0, 0, 0
    exact = int.from_bytes(hashlib.blake2b(" ".join(toks).encode(), digest_size=8).digest(), "big")
    shingles = [" ".join(toks[i:i + 3]) for i in range(max(1, len(toks) - 2))]
    counts = [0] * 64
    for s in range(0, len(shingles), 255):
        lanes = 0
        for sh in shingles[s:s + 255]:
            h = int.from_bytes(hashlib.blake2b(sh.encode(), digest_size=8).digest(), "big")
            lanes += int.from_bytes(format(h, "064b").encode().translate(_BIT_TR), "big")
        part = lanes.to_bytes(64, "big")
        for i in range(64):
            counts[i] += part[i]
    n_sh = len(shingles)
    sim = int("".join("1" if 2 * c > n_sh else "0" for c in counts), 2)
    return exact, sim, len(toks)


@lru_cache(maxsize=512)
def dupkey(folded: str) -> int:
    toks = re.findall(r"[^\W_]+", folded)
    return int.from_bytes(hashlib.blake2b(" ".join(toks).encode(), digest_size=8).digest(), "big") if toks else 0


def hamming(a: int, b: int) -> int:
    return (a ^ b).bit_count()


@dataclass
class Analysis:
    raw: float = 0.0
    signals: list = field(default_factory=list)
    urls: list = field(default_factory=list)
    found: dict = field(default_factory=dict)
    norm: Norm | None = None
    fp: tuple = (0, 0, 0)
    mentions: int = 0
    has_contact: bool = False
    hard: float = 0.0
    beat: Any = None
    scene: dict = field(default_factory=dict)
    contacts: tuple = ()
    mem_hit: str = ""
    lf: Any = None
    lhit: str = ""


_VERIFY_RX = R(r"\b(?:верификац\w*|верифицир\w*|пройд\w+\s+(?:проверк\w*|верификац\w*)|подтверд\w+\s+(?:акк\w+|личност\w*)|"
               r"активир\w+\s+(?:бонус\w*|акк\w+)|(?:жми|нажм\w+)\s+(?:start|старт)|напиш\w+\s+(?:боту|в\s+бот\w*)|"
               r"подпиш\w+\s+(?:на|в)\s+(?:мо[йю]|наш\w*|этот)\s+канал\w*|(?:получ\w+|забер\w+)\s+(?:бонус\w*|приз\w*|выплат\w+))")
_GIVE_BRAND_RX = R(r"\b(?:telegram|телеграм\w*|premium|премиум\w*|ton|toncoin|тон|дуров\w*|durov|илон\w*|маск\w*|elon|musk|usdt|bitcoin|биткоин\w*|nft|нфт)\b")
_GIVE_WALLET_RX = R(r"\b(?:кошел\w+|wallet|подключ\w+|connect|seed|сид[\s\-]?фраз\w*)\b")


def analyze_text(text: str, ents=(), cfg: ChatCfg | None = None, fwd: str = "", known_names=()) -> Analysis:
    cfg = cfg or ChatCfg()
    a = Analysis()
    n = normalize(text)
    a.norm = n
    a.found = scan(n)
    a.fp = fingerprint(n.folded)
    a.urls = extract_urls(text, ents, cfg)
    sig = a.signals

    folded = n.folded[:3000]
    fixed = deglyph(folded) if n.mixed else folded
    by_group: dict[str, list] = {}
    leeted = deleet(folded)
    cands = [fixed] + ([folded] if fixed is not folded else []) + ([leeted] if leeted != folded else [])
    hit = {name: (group, w, why) for name, group, w, rx, why in SPAM_RULES if any(rx.search(c) for c in cands)}
    for name, (group, w, why) in hit.items():
        if SHADOWS.get(name) and SHADOWS[name] & hit.keys():
            continue
        by_group.setdefault(group, []).append((w, name, why))
    if n.spaced and n.views:
        fused = [t for t in n.views[0] if len(t) >= 6]
        for name, group, w, rx, why in SQUASH_RULES:
            if any(rx.search(t) for t in fused):
                by_group.setdefault(group, []).append((w, name, why))
    fam = {k for k, rx in FAMILIES.items() if any(rx.search(c) for c in cands)} if len(folded) >= 20 else set()
    pitch = cta = False
    for group, items in by_group.items():
        items.sort(reverse=True)
        w = items[0][0] + (0.5 * items[1][0] if len(items) > 1 else 0.0)
        sig.append((items[0][1] if len(items) == 1 else group, round(w, 2),
                    items[0][2] + (f" (+{len(items) - 1})" if len(items) > 1 else "")))
        pitch |= group in PITCH_GROUPS
        cta |= group == "cta"
    if pitch and cta:
        sig.append(("pitch_cta", 2.0, "предложение + призыв писать/переходить"))
    overlap = 2.0 if (pitch and cta) else 0.0
    if len(fam) >= 3:
        if 3.0 - overlap > 0:
            sig.append(("families3", 3.0 - overlap, "сразу три приметы: деньги/работа, выгода, призыв"))
    elif len(fam) == 2:
        strong = "cta" in fam and bool(fam & {"money", "work", "sale"})
        w2 = (1.5 if strong else 0.8) - overlap
        if w2 > 0:
            sig.append(("families2", w2, "две приметы рекламы подряд"))

    shown = 0
    for u in a.urls:
        if u.kind == "allowed":
            continue
        w = {"unknown": 2.0, "shortener": 3.0, "invite": 3.0, "tg_channel": 2.0, "tg_bot": 1.5, "ip": 3.0,
             "blocked": 4.0}.get(u.kind, 2.0)
        if shown < 2:
            sig.append((f"link_{u.kind}", w, f"ссылка ({u.kind}): {u.host}"))
            shown += 1
        for fl, fw, why in (("mismatch", 4.0, "текст ссылки врёт: ведёт на другой сайт"),
                            ("idn_mixed", 3.0, "в домене смешаны алфавиты («двойники» букв)"),
                            ("userinfo", 3.0, "хитрый адрес с «@» (логин вместо сайта)"),
                            ("hidden", 1.5, "ссылка спрятана за безобидным словом"),
                            ("lookalike", 3.5, "адрес подделывает известный сервис"),
                            ("brand_sub", 3.5, "известный сервис спрятан внутри чужого адреса"),
                            ("download", 3.0, "ссылка на файл для скачивания"),
                            ("redirect", 2.5, "ссылка-перенаправление на другой сайт"),
                            ("bait2", 2.2, "в адресе несколько приманок (подарок, бонус, вход…)"),
                            ("bait", 1.2, "в адресе слово-приманка"),
                            ("deep_sub2", 2.0, "«login/secure» в поддомене чужого сайта"),
                            ("deep_sub", 1.0, "слишком длинный адрес с поддоменами"),
                            ("random_host", 1.0, "адрес похож на случайный набор букв"),
                            ("risky_tld", 1.0, "зона домена, любимая у мошенников")):
            if fl in u.flags:
                sig.append((fl, fw, why))

    raw_text = text[:3000]
    if _PHONE_RE.search(raw_text):
        sig.append(("phone", 1.2, "номер телефона"))
    if _WALLET_RE.search(raw_text):
        sig.append(("wallet", 3.0, "адрес крипто-кошелька"))
    emo = count_emoji(raw_text)
    if emo >= 6 and emo / max(1, len(raw_text)) >= 0.15:
        sig.append(("emoji_dense", 1.0, "очень много эмодзи"))
    letters = [c for c in raw_text if c.isalpha()] if len(raw_text) >= 25 else ()
    if len(letters) >= 25 and sum(1 for c in letters if c.isupper()) / len(letters) >= 0.75:
        sig.append(("caps", 0.8, "КАПС"))
    if n.mixed >= 3:
        sig.append(("homoglyph", 3.0, "буквы-двойники внутри слов"))
    elif n.mixed >= 1:
        sig.append(("homoglyph", 1.5, "буквы-двойники внутри слова"))
    if n.zw >= 2:
        sig.append(("zero_width", 1.5, "невидимые символы"))
    if FOREIGN_SCRIPTS and foreign_letters(raw_text) >= FOREIGN_MIN:
        sig.append(("foreign_script", 1.5, "много букв чужого алфавита (иероглифы, арабица, тайский…)"))
    if n.spaced:
        sig.append(("spaced", 1.5, "слова «р а з н е с е н ы» буквами"))
    if fwd in ("channel", "chat"):
        sig.append(("fwd_channel", 2.0, "пересылка из канала/чата"))

    handles = _HANDLE_RE.findall(raw_text)
    if handles:
        known = {k.lower() for k in known_names}
        handles = [h for h in handles if h[1:].lower() not in known]
    a.mentions = sum(1 for e in ents or [] if e.type in ("mention", "text_mention")) or len(handles)
    extra = max(0, len(handles) - 1)
    bots = sum(1 for h in handles if h.lower().endswith("bot"))
    if extra or bots:
        sig.append(("handles", round(1.0 * extra + 1.2 * bots, 2), "чужие @упоминания / боты"))

    a.has_contact = bool(any(u.kind != "allowed" for u in a.urls) or handles or _PHONE_RE.search(raw_text))
    a.contacts = contact_tokens(a.urls, handles, raw_text)
    via_tg = any(u.kind in ("tg_bot", "tg_channel", "invite") for u in a.urls) or bool(handles)
    if via_tg and any(_VERIFY_RX.search(c) for c in cands):
        sig.append(("verify_bot", 2.5, "«верификация»/«бонус»/«подпишись» через бота или канал"))
    if ("giveaway" in hit or "en_promo" in hit) and any(_GIVE_BRAND_RX.search(c) for c in cands) \
            and (_WALLET_RE.search(raw_text) or any(_GIVE_WALLET_RX.search(c) for c in cands)):
        sig.append(("giveaway_combo", 3.0, "раздача + громкий бренд + кошелёк: фишинг под розыгрыш"))
    a.raw = round(sum(w for _, w, _ in sig), 2)
    a.hard = round(sum(w for n, w, _ in sig if n in HARD_SIGNALS), 2)
    return a


def effective(a: "Analysis", tier: str, strict: bool = False) -> float:
    f = (TIER_FACTOR_STRICT if strict else TIER_FACTOR)[tier]
    return round((a.raw - a.hard) * f + a.hard, 2)


def scam_action(eff: float, tier: str, age_s: float | None = None, strict: bool = False) -> str:
    watch_t, delete_t, ban_t = (WATCH_T_S, DELETE_T_S, BAN_T_S) if strict else (WATCH_T, DELETE_T, BAN_T)
    max_age = NEW_BAN_AGE_STRICT if strict else NEW_BAN_AGE
    if eff >= ban_t and tier == "new" and (age_s is None or age_s <= max_age):
        return "ban"
    if eff >= delete_t:
        return "delete"
    if eff >= watch_t:
        return "watch"
    return "none"


@dataclass
class Ring:
    key: str
    chat_id: int
    mode: str
    fighters: tuple = ()
    names: tuple = ()
    started: float = 0.0
    expires: float = 0.0

    def has(self, uid: int) -> bool:
        return uid in self.fighters

    def to_dict(self) -> dict:
        return {"key": self.key, "chat_id": self.chat_id, "mode": self.mode, "fighters": list(self.fighters),
                "names": list(self.names), "started": self.started, "expires": self.expires}

    @classmethod
    def from_dict(cls, d: dict) -> "Ring":
        return cls(key=str(d["key"]), chat_id=int(d["chat_id"]), mode=str(d.get("mode", "manual")),
                   fighters=tuple(int(x) for x in d.get("fighters", [])),
                   names=tuple(str(x) for x in d.get("names", [])),
                   started=float(d.get("started", 0)), expires=float(d.get("expires", 0)))


class RingBook:
    def __init__(self):
        self.rings: dict[str, Ring] = {}

    def start(self, ring: Ring) -> Ring:
        self.rings[ring.key] = ring
        return ring

    def touch(self, key: str, ttl: float, now: float) -> bool:
        r = self.rings.get(key)
        if not r:
            return False
        r.expires = max(r.expires, now + ttl)
        return True

    def end(self, key: str) -> Ring | None:
        return self.rings.pop(key, None)

    def end_chat(self, chat_id: int, modes: tuple | None = None) -> list[Ring]:
        gone = [r for r in self.rings.values() if r.chat_id == chat_id and (modes is None or r.mode in modes)]
        for r in gone:
            self.rings.pop(r.key, None)
        return gone

    def active(self, chat_id: int, now: float) -> list[Ring]:
        return [r for r in self.rings.values() if r.chat_id == chat_id and r.expires > now]

    def pop_expired(self, now: float) -> list[Ring]:
        gone = [r for r in self.rings.values() if r.expires <= now]
        for r in gone:
            self.rings.pop(r.key, None)
        return gone

    def dump(self) -> dict:
        return {k: r.to_dict() for k, r in self.rings.items()}

    def load(self, raw: dict) -> None:
        for k, d in (raw or {}).items():
            try:
                self.rings[k] = Ring.from_dict(d)
            except Exception:
                continue


CAPTCHA_ITEMS = {"грушу": "🍐", "бомбу": "💣", "ракету": "🚀", "грибок": "🍄", "звёздочку": "⭐", "рыбку": "🐟",
                 "яблоко": "🍎", "банан": "🍌", "ключ": "🔑", "луну": "🌙", "ёлку": "🎄", "сердечко": "❤️"}


def _classic_captcha(rng: random.Random) -> dict:
    if rng.random() < 0.6:
        names = rng.sample(list(CAPTCHA_ITEMS), 4)
        word = names[0]
        opts = [CAPTCHA_ITEMS[x] for x in names]
        rng.shuffle(opts)
        return {"kind": "emoji", "q": f"Выберите: {word}", "options": opts, "answer": opts.index(CAPTCHA_ITEMS[word])}
    a, b = rng.randint(3, 9), rng.randint(2, 8)
    if rng.random() < 0.5:
        q, ans = f"Сколько будет {a} + {b}?", a + b
    else:
        a, b = max(a, b), min(a, b)
        q, ans = f"Сколько будет {a} − {b}?", a - b
    wrong = set()
    while len(wrong) < 3:
        w = ans + rng.choice([-4, -3, -2, -1, 1, 2, 3, 4])
        if w >= 0 and w != ans:
            wrong.add(w)
    opts = [str(x) for x in wrong] + [str(ans)]
    rng.shuffle(opts)
    return {"kind": "math", "q": q, "options": opts, "answer": opts.index(str(ans))}


ODD_SETS = ("🍎🍌🍇🍓🍊🍋🍒🍑", "🐶🐱🐭🐰🦊🐻🐼🐸", "🚗🚕🚌🚓🚑🚒🚜🚲", "⚽🏀🏈⚾🎾🏐🏉🎱")
LETTER_WORDS = ("груша", "ракета", "яблоко", "банан", "ключ", "звезда", "рыбка", "гриб", "сердце", "лодка", "сыр", "луна")
ALPHABET = "АБВГДЕЖЗИКЛМНОПРСТУФХЦЧШЭЮЯ"


def _num_options(rng: random.Random, ans: int, n: int, lo: int = 0, spread: int = 4) -> list:
    opts = {ans}
    for _ in range(80):
        if len(opts) >= n:
            break
        w = ans + rng.choice([d for d in range(-spread, spread + 1) if d])
        if w >= lo:
            opts.add(w)
    while len(opts) < n:
        opts.add(max(opts) + 1)
    return list(opts)


def make_captcha(rng: random.Random | None = None, level: str | None = None) -> dict:
    rng = rng or random.Random()
    if level is None:
        cap = _classic_captcha(rng)
        cap["cols"] = len(cap["options"])
        return cap
    hard = level == "hard"
    n = 6 if hard else 4
    kind = rng.choice(("math2", "count", "odd", "emoji") if hard else ("emoji", "odd", "math") if level == "easy"
                      else ("emoji", "math", "count", "odd", "letter"))
    if kind == "emoji":
        names = rng.sample(list(CAPTCHA_ITEMS), n)
        opts = [CAPTCHA_ITEMS[x] for x in names]
        right = opts[0]
        rng.shuffle(opts)
        cap = {"kind": "emoji", "q": f"Выберите: {names[0]}", "options": opts, "answer": opts.index(right)}
    elif kind in ("math", "math2"):
        if kind == "math2" and rng.random() < 0.5:
            a, b = rng.randint(3, 9), rng.randint(2, 6)
            q, ans = f"Сколько будет {a} × {b}?", a * b
        elif kind == "math2":
            a, b = rng.randint(6, 15), rng.randint(2, 9)
            c = rng.randint(1, a + b - 1)
            q, ans = f"Сколько будет {a} + {b} − {c}?", a + b - c
        else:
            a, b = rng.randint(3, 9), rng.randint(2, 8)
            if rng.random() < 0.5:
                q, ans = f"Сколько будет {a} + {b}?", a + b
            else:
                a, b = max(a, b), min(a, b)
                q, ans = f"Сколько будет {a} − {b}?", a - b
        opts = [str(x) for x in _num_options(rng, ans, n, spread=6 if hard else 4)]
        rng.shuffle(opts)
        cap = {"kind": "math", "q": q, "options": opts, "answer": opts.index(str(ans))}
    elif kind == "count":
        icons = rng.sample(list(CAPTCHA_ITEMS.values()), 3)
        target, f1, f2 = icons
        k = rng.randint(3, 7) if hard else rng.randint(2, 5)
        row = [target] * k + [rng.choice((f1, f2)) for _ in range(rng.randint(3, 5) if hard else rng.randint(2, 4))]
        rng.shuffle(row)
        opts = [str(x) for x in _num_options(rng, k, n, lo=1, spread=3)]
        rng.shuffle(opts)
        cap = {"kind": "count", "q": f"Сколько {target} в ряду: {''.join(row)}", "options": opts, "answer": opts.index(str(k))}
    elif kind == "odd":
        a_set, b_set = rng.sample(ODD_SETS, 2)
        picks = rng.sample(a_set, n - 1) + [rng.choice(b_set)]
        odd = picks[-1]
        rng.shuffle(picks)
        cap = {"kind": "odd", "q": "Что здесь лишнее?", "options": picks, "answer": picks.index(odd)}
    else:
        w = rng.choice(LETTER_WORDS)
        right = w[0].upper()
        opts = [right] + rng.sample([c for c in ALPHABET if c != right], n - 1)
        rng.shuffle(opts)
        cap = {"kind": "letter", "q": f"Какая первая буква в слове «{w}»?", "options": opts, "answer": opts.index(right)}
    cap["cols"] = 3 if n == 6 else n
    return cap


def fort_targets(cfg: ChatCfg) -> dict:
    return {
        "enabled": True, "captcha": True, "captcha_smart": True, "smart_links": True, "scam": True, "hate": True,
        "adult": True, "profanity": True, "flood": True, "raid": True, "impostor": True, "cas": True, "puppet": True,
        "spam_memory": True, "jitter": False, "clean_joins": True, "tribunes": False, "quiet": True, "links": "admins",
        "captcha_timeout": min(cfg.captcha_timeout, FORT_CAPTCHA_TIMEOUT),
        "captcha_ban_min": max(cfg.captcha_ban_min, FORT_CAPTCHA_BAN_MIN),
        "newbie_min": max(cfg.newbie_min, FORT_NEWBIE_MIN),
        "locks": sorted(set(cfg.locks) | set(FORT_LOCKS)),
    }


def radar_name(score: float) -> tuple:
    for floor, idx, name, icon in RADAR_LEVELS:
        if score >= floor:
            return idx, name, icon
    return 0, "спокойно", "🟢"


class FortCore:

    def init_fort(self) -> None:
        self.radar: dict[int, deque] = {}
        self.fort_counts: dict[int, dict] = {}
        self.fort_peak: dict[int, float] = {}
        self.fort_rearm: dict[int, float] = {}
        self.fort_auto_on = True
        self.fort_trip_score = FORT_TRIP_SCORE
        self.fort_trip_actors = FORT_TRIP_ACTORS
        self.fort_hold_s = float(FORT_AUTO_HOLD)

    def radar_score(self, chat_id: int, now: float | None = None, hard_only: bool = False) -> tuple:
        now = self.clock() if now is None else now
        per: dict[int, float] = {}
        for ts, who, w, kind in self.radar.get(chat_id) or ():
            age = now - ts
            if age > RADAR_WINDOW or (hard_only and kind in RADAR_SOFT):
                continue
            per[who] = per.get(who, 0.0) + w * 0.5 ** (max(0.0, age) / RADAR_HALF)
        total = sum(min(s, RADAR_ACTOR_CAP) for s in per.values())
        return round(total, 2), sum(1 for s in per.values() if s >= RADAR_ACTOR_MIN)

    def radar_level(self, chat_id: int, now: float | None = None) -> tuple:
        now = self.clock() if now is None else now
        st = self.store.chats.get(chat_id)
        score, actors = self.radar_score(chat_id, now, hard_only=bool(st and st.cfg.fort_on))
        idx, name, icon = radar_name(score)
        return idx, name, icon, score, actors

    def radar_kinds(self, chat_id: int, now: float | None = None) -> list:
        now = self.clock() if now is None else now
        who: dict[str, set] = {}
        for ts, uid, w, kind in self.radar.get(chat_id) or ():
            if now - ts <= RADAR_WINDOW:
                who.setdefault(kind, set()).add(uid)
        return sorted(((k, len(s)) for k, s in who.items()), key=lambda kv: (-kv[1], kv[0]))

    def radar_why(self, chat_id: int, now: float | None = None) -> str:
        parts, seen = [], set()
        for kind, n in self.radar_kinds(chat_id, now)[:5]:
            label = RADAR_LABEL.get(kind, kind)
            if label in seen:
                continue
            seen.add(label)
            parts.append(label if kind in ("raid", "raid_more") else f"{label}: {n}")
        return "; ".join(parts[:4])

    def radar_note(self, chat_id: int, uid: int, kind: str, now: float | None = None) -> bool:
        w = RADAR_WEIGHT.get(kind, 0.0)
        if w <= 0:
            return False
        now = self.clock() if now is None else now
        st = self.store.chats.get(chat_id)
        if st is None:
            return False
        cfg = st.cfg
        if kind in AP_KNOWN_KINDS and self.ap_brain:
            self.ap_known_note(chat_id, int(uid), now)
        if cfg.fort_on:
            how = FORT_COUNT_AS.get(kind)
            if how:
                self.fort_count(chat_id, how)
            if kind in RADAR_SOFT:
                return False
        dq = self.radar.setdefault(chat_id, deque(maxlen=RADAR_KEEP))
        dq.append((now, int(uid), w, kind))
        if cfg.fort_on:
            score, _ = self.radar_score(chat_id, now, hard_only=True)
            if score > self.fort_peak.get(chat_id, 0.0):
                self.fort_peak[chat_id] = score
            if cfg.fort_origin == "auto" and cfg.fort_until and score >= FORT_KEEP_SCORE:
                cfg.fort_until = max(cfg.fort_until, now + self.fort_hold_s)
                self.store.dirty = True
            return False
        if not (self.fort_auto_on and cfg.fort_auto and cfg.enabled) or now < self.fort_rearm.get(chat_id, 0.0):
            return False
        score, actors = self.radar_score(chat_id, now)
        if score < self.fort_trip_score or actors < self.fort_trip_actors:
            return False
        return self.fort_enable(chat_id, origin="auto", seconds=FORT_AUTO_MIN, why=self.radar_why(chat_id, now), now=now)

    def fort_active(self, chat_id: int) -> bool:
        st = self.store.chats.get(chat_id)
        return bool(st and st.cfg.fort_on)

    def fort_count(self, chat_id: int, key: str, n: int = 1) -> None:
        c = self.fort_counts.setdefault(chat_id, {})
        c[key] = c.get(key, 0) + n

    def fort_enable(self, chat_id: int, origin: str = "manual", seconds: float = 0.0, why: str = "",
                    now: float | None = None, by: int = 0) -> bool:
        now = self.clock() if now is None else now
        st = self.store.chat(chat_id)
        cfg = st.cfg
        if seconds and seconds > 0:
            seconds = max(FORT_MIN_MIN * 60.0, min(float(seconds), FORT_MAX_MIN * 60.0))
        if cfg.fort_on:
            if origin == "manual":
                cfg.fort_origin = "manual"
                cfg.fort_until = now + seconds if seconds > 0 else 0.0
                self.store.dirty = True
            return False
        before, applied = {}, {}
        for key, want in fort_targets(cfg).items():
            cur = getattr(cfg, key)
            if (set(cur) == set(want)) if key == "locks" else (cur == want):
                continue
            before[key] = list(cur) if isinstance(cur, list) else cur
            applied[key] = list(want) if isinstance(want, list) else want
            setattr(cfg, key, list(want) if isinstance(want, list) else want)
        cfg.fort_before, cfg.fort_applied = before, applied
        cfg.fort_on, cfg.fort_started, cfg.fort_origin, cfg.fort_why = True, now, origin, (why or "")[:200]
        cfg.fort_until = now + seconds if seconds > 0 else 0.0
        cfg.fort_board = 0
        self.fort_counts[chat_id] = {}
        self.fort_peak[chat_id] = self.radar_score(chat_id, now, hard_only=True)[0]
        self.store.bump(st, "fort_on", now=now)
        self.store.dirty = True
        self._event("fort_on", chat=chat_id, origin=origin, why=cfg.fort_why, by=by)
        return True

    @staticmethod
    def fort_revert_values(cfg: ChatCfg) -> tuple:
        restore, kept = {}, []
        for key, base in (cfg.fort_before or {}).items():
            if not hasattr(cfg, key):
                continue
            cur, applied = getattr(cfg, key), (cfg.fort_applied or {}).get(key)
            if key == "locks":
                added = set(applied or ()) - set(base or ())
                restore[key] = [x for x in cur if x not in added]
                if set(restore[key]) != set(base or ()):
                    kept.append(key)
            elif cur == applied:
                restore[key] = list(base) if isinstance(base, list) else base
            else:
                kept.append(key)
        return restore, kept

    def fort_disable(self, chat_id: int, now: float | None = None, how: str = "manual", by: int = 0) -> dict | None:
        now = self.clock() if now is None else now
        st = self.store.chats.get(chat_id)
        if st is None or not st.cfg.fort_on:
            return None
        cfg = st.cfg
        restore, kept = self.fort_revert_values(cfg)
        for key, val in restore.items():
            setattr(cfg, key, val)
        rep = {"how": how, "origin": cfg.fort_origin, "why": cfg.fort_why, "started": cfg.fort_started, "ended": now,
               "counts": dict(self.fort_counts.pop(chat_id, {})), "peak": self.fort_peak.pop(chat_id, 0.0),
               "board": cfg.fort_board, "restored": restore, "kept": kept, "applied": dict(cfg.fort_applied)}
        cfg.fort_on = False
        cfg.fort_until = cfg.fort_started = 0.0
        cfg.fort_origin = cfg.fort_why = ""
        cfg.fort_before, cfg.fort_applied, cfg.fort_board = {}, {}, 0
        self.fort_rearm[chat_id] = now + (FORT_REARM_AUTO if how in ("auto", "timer") else FORT_REARM_MANUAL)
        self.store.dirty = True
        self._event("fort_off", chat=chat_id, how=how, report=rep, by=by)
        return rep

    def fort_extend(self, chat_id: int, seconds: float, now: float | None = None) -> float:
        now = self.clock() if now is None else now
        st = self.store.chats.get(chat_id)
        if st is None or not st.cfg.fort_on or not st.cfg.fort_until:
            return 0.0
        st.cfg.fort_until = max(st.cfg.fort_until, now) + float(seconds)
        self.store.dirty = True
        return st.cfg.fort_until

    def fort_keep(self, chat_id: int) -> bool:
        st = self.store.chats.get(chat_id)
        if st is None or not st.cfg.fort_on:
            return False
        st.cfg.fort_origin, st.cfg.fort_until = "manual", 0.0
        self.store.dirty = True
        return True

    def fort_expired(self, now: float | None = None) -> list:
        now = self.clock() if now is None else now
        out = []
        for cid, st in self.store.chats.items():
            cfg = st.cfg
            if not (cfg.fort_on and cfg.fort_until and cfg.fort_until <= now):
                continue
            if cfg.fort_origin == "auto" and self.radar_score(cid, now, hard_only=True)[0] >= FORT_KEEP_SCORE:
                cfg.fort_until = now + self.fort_hold_s
                self.store.dirty = True
                continue
            out.append(cid)
        return out

    def fort_slow(self, tier: str, chat_id: int, now: float) -> int:
        levels = FORT_SLOW_BY_LEVEL.get(tier)
        if not levels:
            return 0
        c = self.__dict__.setdefault("_slow_c", {})
        hit = c.get(chat_id)
        if hit is not None and 0 <= now - hit[0] < 1.0:
            return levels[hit[1]]
        lvl = self.radar_level(chat_id, now)[0]
        c[chat_id] = (now, lvl)
        return levels[lvl]

    def _fort_prune(self, now: float) -> None:
        for cid in list(self.radar):
            dq = self.radar[cid]
            while dq and now - dq[0][0] > RADAR_WINDOW:
                dq.popleft()
            if not dq:
                self.radar.pop(cid, None)
        for cid in [c for c, t in self.fort_rearm.items() if t <= now]:
            self.fort_rearm.pop(cid, None)
        for d in (self.fort_counts, self.fort_peak):
            for cid in [c for c in d if not self.fort_active(c)]:
                d.pop(cid, None)


_AP_DEFAULTS = ChatCfg()


def _ap_copy(v):
    return sorted(v) if isinstance(v, (list, tuple, set)) else v


def _ap_eq(key: str, a, b) -> bool:
    if key == "locks":
        return set(a or ()) == set(b or ())
    return a == b


def _ap_lvl(s) -> int:
    try:
        return max(0, min(3, int((s or {}).get("lvl", 0) or 0)))
    except (TypeError, ValueError, AttributeError):
        return 0


def _clamp(x: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, x))


def ap_merge(key: str, cur, want):
    if key == "locks":
        return sorted(set(cur or ()) | set(want or ()))
    if key in AP_RANKS:
        r = AP_RANKS[key]
        return r[max(r.index(cur) if cur in r else 0, r.index(want) if want in r else 0)]
    if key in AP_MAX_KEYS:
        return max(int(cur or 0), int(want))
    if key in AP_MIN_KEYS:
        return min(int(cur), int(want)) if cur else int(want)
    if key in AP_FALSE_STRICT:
        return bool(cur) and bool(want)
    return bool(cur) or bool(want)


def ap_want(reflex: str, lvl: int) -> dict:
    out: dict = {}
    for i in range(1, lvl + 1):
        for key, want in AP_MEASURES.get(reflex, {}).get(i, {}).items():
            out[key] = ap_merge(key, out[key], want) if key in out else _ap_copy(want)
    return out


class ApCore:

    def init_ap(self) -> None:
        self.ap_on = True
        self.ap_sens = 1.0
        self.ap_calm_after = float(AP_CALM_AFTER)
        self.ap_brain = True
        self.ap_tz_h = 0
        self.ap_pulses: dict[int, deque] = {}
        self.ap_log: dict[int, deque] = {}
        self.ap_rearm: dict[tuple, float] = {}
        self.ap_vigil: dict[tuple, float] = {}
        self.ap_after: dict[tuple, float] = {}
        self.ap_hot: dict[tuple, float] = {}
        self.ap_vec: dict[int, deque] = {}
        self.ap_admin_t: dict[int, float] = {}
        self.ap_dbg: dict[int, deque] = {}
        self.ap_known: dict[int, dict] = {}

    def ap_pulse(self, chat_id: int, who: int, kind: str, w: float | None = None, now: float | None = None) -> None:
        w = AP_PULSE_WEIGHT.get(kind, 0.0) if w is None else w
        if w <= 0:
            return
        now = self.clock() if now is None else now
        self.ap_pulses.setdefault(chat_id, deque(maxlen=200)).append((now, int(who), float(w), kind))

    def ap_note(self, chat_id: int, now: float, text: str) -> None:
        self.ap_log.setdefault(chat_id, deque(maxlen=AP_NOTES_KEEP)).append((now, text))

    def ap_dbg_note(self, chat_id: int, now: float, text: str) -> None:
        self.ap_dbg.setdefault(chat_id, deque(maxlen=AP_DBG_KEEP)).append((now, text))

    def ap_admin_seen(self, chat_id: int, now: float | None = None) -> None:
        self.ap_admin_t[chat_id] = self.clock() if now is None else now

    @staticmethod
    def ap_vector(msg) -> str:
        try:
            if getattr(msg, "sender_chat", False):
                return "channel"
            if getattr(msg, "via_bot", False):
                return "inline"
            if getattr(msg, "fwd", ""):
                return "forward"
            if getattr(msg, "kind", "") in ("contact", "story"):
                return msg.kind
            if INVITE_RE.search(getattr(msg, "text", "") or ""):
                return "invitelink"
            return AP_VEC_MEDIA.get(getattr(msg, "kind", ""), "")
        except Exception:
            pass
        return ""

    def ap_vec_note(self, chat_id: int, uid: int, vec: str, now: float | None = None) -> None:
        if vec not in AP_VEC_LOCKS:
            return
        now = self.clock() if now is None else now
        self.ap_vec.setdefault(chat_id, deque(maxlen=300)).append((now, int(uid), vec))

    def ap_vec_hot(self, chat_id: int, now: float, need: int = AP_VEC_SRC) -> list:
        who: dict[str, set] = {}
        for ts, uid, vec in self.ap_vec.get(chat_id) or ():
            if 0 <= now - ts <= RADAR_WINDOW:
                who.setdefault(vec, set()).add(uid)
        media = set(AP_VEC_MEDIA.values())
        return sorted(v for v, s in who.items() if len(s) >= (max(need, AP_VEC_SRC_MEDIA) if v in media else need))

    def ap_known_note(self, chat_id: int, uid: int, now: float) -> None:
        if uid > 0:
            seen = self.ap_known.setdefault(uid, {})
            seen[chat_id] = now
            if len(seen) > 4:
                seen.pop(min(seen, key=seen.get), None)

    def _ap_q(self, st, who: int, now: float, chat_id: int = 0) -> float:
        if st is None or who <= 0:
            return 1.0
        rec = st.users.get(who)
        q = 1.0
        if rec is not None:
            if rec.vouched:
                return 0.6
            base = rec.joined or rec.first_seen
            age_d = max(0.0, now - base) / 86400.0 if base else 7.0
            if age_d < 2.0:
                q = 1.2
            elif age_d >= 14.0 and rec.clean >= 20:
                q = 0.75
        seen = self.ap_known.get(who)
        if seen and any(c != chat_id and 0 <= now - t <= AP_KNOWN_S for c, t in seen.items()):
            q = min(1.4, q * AP_KNOWN_Q)
        return q

    def ap_score(self, chat_id: int, reflex: str, now: float, active: bool, at: float | None = None) -> tuple:
        spec = AP_REFLEXES[reflex]
        kinds = spec["hard"] if active else spec["hard"] | spec["soft"]
        t = now if at is None else at
        st = self.store.chats.get(chat_id) if (self.ap_brain and reflex in AP_SRC_Q) else None
        qc: dict[int, float] = {}
        per: dict[int, float] = {}
        for src in (self.radar.get(chat_id), self.ap_pulses.get(chat_id)):
            for ts, who, w, kind in src or ():
                if at is not None and ts > t:
                    continue
                age = t - ts
                if age > RADAR_WINDOW or kind not in kinds:
                    continue
                if st is not None:
                    q = qc.get(who)
                    if q is None:
                        q = qc[who] = self._ap_q(st, who, t, chat_id)
                    w = w * q
                per[who] = per.get(who, 0.0) + w * 0.5 ** (max(0.0, age) / RADAR_HALF)
        total = sum(min(s, RADAR_ACTOR_CAP) for s in per.values())
        return round(total, 2), sum(1 for s in per.values() if s >= RADAR_ACTOR_MIN)

    def ap_last_event(self, chat_id: int, reflex: str, now: float, active: bool) -> float | None:
        spec = AP_REFLEXES[reflex]
        kinds = spec["hard"] if active else spec["hard"] | spec["soft"]
        last = None
        for src in (self.radar.get(chat_id), self.ap_pulses.get(chat_id)):
            for ts, who, w, kind in src or ():
                if kind in kinds and ts <= now and now - ts <= RADAR_WINDOW and (last is None or ts > last):
                    last = ts
        return last

    def ap_why(self, chat_id: int, reflex: str, now: float) -> str:
        spec = AP_REFLEXES[reflex]
        kinds = spec["hard"] | spec["soft"]
        who: dict[str, set] = {}
        for src in (self.radar.get(chat_id), self.ap_pulses.get(chat_id)):
            for ts, uid, w, kind in src or ():
                if now - ts <= RADAR_WINDOW and kind in kinds:
                    who.setdefault(kind, set()).add(uid)
        parts, seen = [], set()
        for kind, s in sorted(who.items(), key=lambda kv: (-len(kv[1]), kv[0])):
            label = AP_KIND_LABEL.get(kind) or RADAR_LABEL.get(kind, kind)
            if label in seen:
                continue
            seen.add(label)
            parts.append(label if kind in ("raid", "raid_more") else f"{label}: {len(s)}")
        return "; ".join(parts[:3])

    @staticmethod
    def ap_scar_now(cfg: ChatCfg, now: float) -> float:
        if not cfg.ap_scar or not cfg.ap_scar_t:
            return 0.0
        return cfg.ap_scar * 0.5 ** (max(0.0, now - cfg.ap_scar_t) / AP_SCAR_HALF)

    def ap_mult(self, cfg: ChatCfg, now: float) -> tuple:
        why: list = []
        m, hold = 1.0 / max(0.3, self.ap_sens), 1.0
        scar = self.ap_scar_now(cfg, now)
        if scar >= 0.5:
            k = min(scar, AP_SCAR_CAP)
            m *= 1.0 - 0.08 * k
            hold *= 1.0 + 0.25 * k
            why.append(f"закалка {scar:.1f}")
        hours = cfg.ap_hours
        if len(hours) == 24 and sum(hours) >= 4:
            h = int((now % 86400) // 3600)
            if (hours[(h - 1) % 24] + hours[h] + hours[(h + 1) % 24]) / sum(hours) >= 0.5:
                m *= 0.85
                why.append("в это время уже бывали волны")
        if int(((now + self.ap_tz_h * 3600) % 86400) // 3600) < 7:
            m *= 0.9
            hold *= 1.5
            why.append("ночь: админы спят")
        return max(AP_MULT_MIN, min(AP_MULT_MAX, m)), hold, why

    def _ap_harden(self, cfg: ChatCfg, now: float, lvl: int) -> None:
        cfg.ap_scar = min(AP_SCAR_CAP * 1.5, self.ap_scar_now(cfg, now) + (1.5 if lvl >= 3 else 1.0))
        cfg.ap_scar_t = now
        if len(cfg.ap_hours) != 24:
            cfg.ap_hours = [0.0] * 24
        h = int((now % 86400) // 3600)
        cfg.ap_hours[h] = min(12.0, cfg.ap_hours[h] + 1.0)
        if sum(cfg.ap_hours) > 40:
            cfg.ap_hours = [x * 0.5 for x in cfg.ap_hours]
        if len(cfg.ap_dow) != 7:
            cfg.ap_dow = [0.0] * 7
        d = int(now // 86400 + 3) % 7
        cfg.ap_dow[d] = min(12.0, cfg.ap_dow[d] + 1.0)
        if sum(cfg.ap_dow) > 40:
            cfg.ap_dow = [x * 0.5 for x in cfg.ap_dow]

    @staticmethod
    def ap_doubt_now(cfg: ChatCfg, reflex: str, now: float) -> float:
        try:
            v, t = (cfg.ap_doubt or {}).get(reflex)
            return max(0.0, float(v) * 0.5 ** (max(0.0, now - float(t)) / AP_DOUBT_HALF))
        except (TypeError, ValueError):
            return 0.0

    def ap_doubt_add(self, cfg: ChatCfg, reflex: str, now: float, w: float = 1.0) -> None:
        if not self.ap_brain:
            return
        if not isinstance(cfg.ap_doubt, dict):
            cfg.ap_doubt = {}
        cfg.ap_doubt[reflex] = [round(min(AP_DOUBT_CAP, self.ap_doubt_now(cfg, reflex, now) + w), 3), now]
        self.store.dirty = True

    def ap_doubt_ease(self, cfg: ChatCfg, reflex: str, now: float, k: float = 0.85) -> None:
        d = self.ap_doubt_now(cfg, reflex, now)
        if not isinstance(cfg.ap_doubt, dict) or reflex not in cfg.ap_doubt:
            return
        if d * k > 0.05:
            cfg.ap_doubt[reflex] = [round(d * k, 3), now]
        else:
            cfg.ap_doubt.pop(reflex, None)
        self.store.dirty = True

    def ap_rollback(self, cfg: ChatCfg, reflex: str, now: float, w: float = 1.0) -> float:
        d = self.ap_doubt_now(cfg, reflex, now) if self.ap_brain else 0.0
        cool = min(float(AP_COOL_MAX), AP_OVERRIDE_COOL * (1.0 + 0.5 * min(d, 3.0)))
        self.ap_doubt_add(cfg, reflex, now, w)
        cfg.ap_cool[reflex] = now + cool
        return cool

    def ap_bg_update(self, cfg: ChatCfg, reflex: str, score: float, now: float) -> None:
        if reflex not in AP_BG_REFLEXES or not self.ap_brain:
            return
        if not isinstance(cfg.ap_bg, dict):
            cfg.ap_bg = {}
        sample = min(score, AP_TRIP[reflex][0][0])
        try:
            bg, t, t0 = cfg.ap_bg[reflex]
            a = 1.0 - 0.5 ** (max(0.0, now - float(t)) / AP_BG_HALF)
            cfg.ap_bg[reflex] = [float(bg) + (sample - float(bg)) * a, now, float(t0)]
        except (KeyError, TypeError, ValueError):
            cfg.ap_bg[reflex] = [sample, now, now]

    @staticmethod
    def ap_bg_factor(cfg: ChatCfg, reflex: str, now: float) -> float:
        try:
            bg, t, t0 = (cfg.ap_bg or {}).get(reflex)
            r = float(bg) / AP_TRIP[reflex][0][0]
            if r >= 0.15:
                return _clamp(1.0 + (r - 0.15) * 0.6, 1.0, AP_BG_MAX)
            if r <= 0.01 and now - float(t0) >= 2 * 86400:
                return AP_BG_MIN
        except (TypeError, ValueError, KeyError):
            pass
        return 1.0

    def ap_neighbors(self, chat_id: int, reflex: str, now: float) -> int:
        n = 0
        for (cid, r), t in self.ap_hot.items():
            if r == reflex and cid != chat_id and 0 <= now - t <= AP_NEIGHBOR_S:
                st = self.store.chats.get(cid)
                if st is not None and st.active:
                    n += 1
        return n

    def ap_hidden(self, chat_id: int, cfg: ChatCfg, reflex: str, s: dict, score: float, actors: int, now: float, cur: int) -> tuple:
        m, h, nk, keep, why = 1.0, 1.0, 1.0, AP_KEEP, []
        if not self.ap_brain:
            return m, h, nk, keep, why
        active = cur > 0
        if score >= 1.0:
            rise = score - self.ap_score(chat_id, reflex, now, active, at=now - AP_TREND_DT)[0]
            if rise >= AP_TREND_BURST:
                m *= 0.8
                why.append("всплеск")
            elif rise >= AP_TREND_UP:
                m *= 0.9
                why.append("рост")
        if active:
            last = self.ap_last_event(chat_id, reflex, now, True)
            if last is not None and now - last >= AP_QUIET_S:
                h *= 0.65 if cur <= 2 else 0.8
                why.append("затихает")
                if now - last >= AP_QUIET_LONG:
                    keep = 1.0 if cur <= 2 else 0.85
                    why.append("тишина")
            r0, lt = float(s.get("r0", 0.0) or 0.0), float(s.get("lt", 0.0) or 0.0)
            if cur < 3 and lt and r0 > 0 and now - lt >= AP_PERSIST_S and score >= AP_PERSIST_KEEP * r0 and actors >= 1:
                nk = 0.8
                why.append("мера не помогает")
        else:
            key = (chat_id, reflex)
            if score >= AP_VIGIL_FRAC * AP_TRIP[reflex][0][0] and actors >= 1:
                self.ap_vigil[key] = now + AP_VIGIL_S
            if now < self.ap_vigil.get(key, 0.0):
                m *= 0.88
                why.append("настороже")
        if now < self.ap_after.get((chat_id, reflex), 0.0):
            m *= 0.85
            why.append("эхо-волна")
        if reflex in AP_COMBO:
            others = sum(1 for r in AP_COMBO if r != reflex and _ap_lvl(cfg.ap_state.get(r)) >= 1)
            if others >= 2:
                m *= 0.85
                why.append("сцепка")
            elif others == 1:
                m *= 0.93
                why.append("сцепка")
            hot = self.ap_neighbors(chat_id, reflex, now)
            if hot >= 2:
                m *= 0.82
                why.append("соседи")
            elif hot == 1:
                m *= 0.9
                why.append("сосед")
        t = self.ap_admin_t.get(chat_id)
        if t:
            since = now - t
            if 0 <= since <= AP_ADMIN_NEAR:
                m *= 1.12 if reflex in ("heat", "noise", "adult") else 1.04
                h *= 0.9
                why.append("админ рядом")
            elif since >= AP_ADMIN_FAR:
                m *= 0.93
                h *= 1.2
                why.append("админов давно нет")
        dow = cfg.ap_dow
        if len(dow) == 7 and sum(dow) >= 6 and dow[int(now // 86400 + 3) % 7] / sum(dow) >= 0.35:
            m *= 0.93
            why.append("день недели")
        bgf = self.ap_bg_factor(cfg, reflex, now)
        if bgf != 1.0:
            m *= bgf
            why.append("фон")
        d = self.ap_doubt_now(cfg, reflex, now)
        if d > 0.2:
            m *= 1.0 + 0.12 * min(d, 3.0)
            h *= 1.0 - 0.06 * min(d, 3.0)
            why.append(f"сомнение {d:.1f}")
        return _clamp(m, AP_HID_MIN, AP_HID_MAX), _clamp(h, AP_HID_HOLD_MIN, AP_HID_HOLD_MAX), nk, keep, why

    @staticmethod
    def ap_level_for(reflex: str, score: float, actors: int, mult: float, cur: int, next_k: float = 1.0, keep: float = AP_KEEP) -> int:
        trip = AP_TRIP[reflex]
        want = 0
        for i, (s, a) in enumerate(trip, start=1):
            k = next_k if i > cur else 1.0
            if score >= s * mult * k and actors >= a:
                want = i
        if cur > 0 and want < cur and score >= trip[cur - 1][0] * mult * keep and actors >= 1:
            want = cur
        return want

    @staticmethod
    def ap_base(cfg: ChatCfg, key: str):
        return cfg.ap_before[key] if key in cfg.ap_before else getattr(cfg, key)

    def ap_desired(self, cfg: ChatCfg, levels: dict, calm: bool) -> dict:
        des: dict = {}
        for reflex, lvl in levels.items():
            for key, want in ap_want(reflex, lvl).items():
                base = self.ap_base(cfg, key)
                if key == "trace" and base == "off":
                    continue
                des[key] = ap_merge(key, des.get(key, base), want)
        if self.ap_brain:
            for reflex, lvl in levels.items():
                if lvl >= 2 and reflex in AP_VEC_REFLEXES:
                    vec = [x for x in ((cfg.ap_state.get(reflex) or {}).get("vec") or ()) if x in AP_VEC_LOCKS]
                    if vec:
                        des["locks"] = ap_merge("locks", des.get("locks", self.ap_base(cfg, "locks")), vec)
        if calm:
            for key, want in AP_CALM.items():
                if key not in des and _ap_eq(key, self.ap_base(cfg, key), getattr(_AP_DEFAULTS, key)):
                    des[key] = want
        return {k: v for k, v in des.items() if not _ap_eq(k, v, self.ap_base(cfg, k))}

    @staticmethod
    def ap_apply(cfg: ChatCfg, desired: dict) -> list:
        out: list = []
        for key in list(cfg.ap_applied):
            if key not in desired:
                old = getattr(cfg, key, None)
                new = cfg.ap_before.pop(key, old)
                cfg.ap_applied.pop(key, None)
                if hasattr(cfg, key) and not _ap_eq(key, old, new):
                    setattr(cfg, key, list(new) if isinstance(new, list) else new)
                    out.append((key, old, new))
        for key, want in desired.items():
            if key in cfg.ap_applied and _ap_eq(key, cfg.ap_applied[key], want):
                continue
            old = getattr(cfg, key)
            if key not in cfg.ap_before:
                cfg.ap_before[key] = list(old) if isinstance(old, list) else old
            setattr(cfg, key, list(want) if isinstance(want, list) else want)
            cfg.ap_applied[key] = list(want) if isinstance(want, list) else want
            out.append((key, old, want))
        return out

    def _ap_sanitize(self, cfg: ChatCfg) -> bool:
        changed = False
        if not isinstance(cfg.ap_state, dict):
            cfg.ap_state, changed = {}, True
        for k in list(cfg.ap_state):
            s = cfg.ap_state[k]
            if not isinstance(s, dict) or (k != "calm" and k not in AP_REFLEXES):
                cfg.ap_state.pop(k, None)
                changed = True
            elif k != "calm" and s.get("lvl") != _ap_lvl(s):
                if _ap_lvl(s) <= 0:
                    cfg.ap_state.pop(k, None)
                else:
                    s["lvl"] = _ap_lvl(s)
                changed = True
        for name in ("ap_before", "ap_applied", "ap_cool", "ap_doubt"):
            if not isinstance(getattr(cfg, name), dict):
                setattr(cfg, name, {})
                changed = True
        return changed

    def _ap_overrides(self, chat_id: int, cfg: ChatCfg, now: float, trans: list) -> bool:
        touched = False
        for key, applied in list(cfg.ap_applied.items()):
            cur = getattr(cfg, key, None)
            if cur is not None and _ap_eq(key, cur, applied):
                continue
            cfg.ap_applied.pop(key, None)
            cfg.ap_before.pop(key, None)
            touched = True
            if cur is not None and _ap_eq(key, ap_merge(key, cur, applied), cur):
                self.ap_note(chat_id, now, f"{key}: владелец поставил не слабее — оставляю его значение")
                if self.ap_brain:
                    for reflex, s in cfg.ap_state.items():
                        if reflex in AP_REFLEXES and _ap_lvl(s) > 0 and key in ap_want(reflex, _ap_lvl(s)):
                            self.ap_doubt_ease(cfg, reflex, now, 0.8)
                continue
            self.ap_note(chat_id, now, f"{key}: владелец вернул сам — отступаю")
            for reflex, s in list(cfg.ap_state.items()):
                lvl = _ap_lvl(s)
                if reflex in AP_REFLEXES and lvl > 0 and key in ap_want(reflex, lvl):
                    cool = self.ap_rollback(cfg, reflex, now)
                    cfg.ap_state.pop(reflex, None)
                    trans.append((reflex, lvl, 0, AP_OWNER_WHY, float(cool), 0))
            if key in AP_CALM and "calm" in cfg.ap_state:
                cfg.ap_cool["calm"] = now + AP_CALM_COOL
                cfg.ap_state.pop("calm", None)
                trans.append(("calm", 1, 0, AP_OWNER_WHY, 0.0, 0))
        return touched

    def ap_step(self, chat_id: int, now: float | None = None) -> dict | None:
        now = self.clock() if now is None else now
        st = self.store.chats.get(chat_id)
        if st is None:
            return None
        cfg = st.cfg
        if cfg.fort_on:
            return None
        if not (self.ap_on and cfg.autopilot and cfg.enabled):
            if cfg.ap_state or cfg.ap_applied or cfg.ap_before:
                return self.ap_release_all(chat_id, now, "off")
            return None
        trans: list = []
        dirty = self._ap_sanitize(cfg)
        dirty = self._ap_overrides(chat_id, cfg, now, trans) or dirty
        for r in [r for r, t in cfg.ap_cool.items() if t <= now]:
            cfg.ap_cool.pop(r, None)
            dirty = True
        mult, hold_k, mwhy = self.ap_mult(cfg, now)
        scar = self.ap_scar_now(cfg, now)
        for reflex in AP_REFLEXES:
            s = cfg.ap_state.get(reflex) or {}
            cur = _ap_lvl(s)
            off = reflex in cfg.ap_off or now < float(cfg.ap_cool.get(reflex, 0.0))
            hh = 1.0
            if off:
                score, actors, want = 0.0, 0, 0
            elif cur == 0 and not (self.radar.get(chat_id) or self.ap_pulses.get(chat_id)):
                score, actors, want = 0.0, 0, 0
                self.ap_bg_update(cfg, reflex, 0.0, now)
            else:
                score, actors = self.ap_score(chat_id, reflex, now, cur > 0)
                if cur == 0:
                    self.ap_bg_update(cfg, reflex, score, now)
                hm, hh, nk, hkeep, hnote = self.ap_hidden(chat_id, cfg, reflex, s, score, actors, now, cur)
                want = self.ap_level_for(reflex, score, actors, _clamp(mult * hm, AP_FINAL_MIN, AP_FINAL_MAX), cur, nk, hkeep)
                if hnote:
                    plain = self.ap_level_for(reflex, score, actors, mult, cur)
                    if plain != want:
                        self.ap_dbg_note(chat_id, now, f"{reflex}: {plain}→{want} (оценка {score:g}, источников {actors}): "
                                                       + ", ".join(hnote))
                if cur == 0 and want == 1 and now < self.ap_rearm.get((chat_id, reflex), 0.0):
                    want = 0
            if want > cur:
                why = self.ap_why(chat_id, reflex, now) or "угроза"
                if mwhy and cur == 0:
                    why += " · " + ", ".join(mwhy)
                new_s = {"lvl": want, "since": s.get("since", now) if cur else now, "low": 0.0,
                         "peak": max(want, int(s.get("peak", 0))) if cur else want, "why": why,
                         "start": s.get("start", now) if cur else now, "lt": now, "r0": score,
                         "rem": s.get("rem", 0.0) if cur else 0.0}
                if cur and s.get("vec"):
                    new_s["vec"] = list(s["vec"])
                cfg.ap_state[reflex] = new_s
                if want >= 2 and cur < 2:
                    self._ap_harden(cfg, now, want)
                elif want >= 3 and cur < 3:
                    self._ap_harden(cfg, now, want)
                trans.append((reflex, cur, want, why, score, actors))
                dirty = True
            elif cur > 0 and want == cur:
                if s.get("low"):
                    s["low"] = 0.0
                    dirty = True
            elif cur > 0:
                if off:
                    new = 0
                else:
                    low = float(s.get("low", 0.0))
                    wait = AP_HOLD[cur] * hold_k * hh * (0.5 if score <= 0 else 1.0)
                    if not low:
                        s["low"], new, dirty = now, cur, True
                    elif now - low >= wait:
                        new = max(want, cur - 1)
                    else:
                        new = cur
                if new != cur:
                    if new == 0:
                        peak = int(s.get("peak", cur))
                        self.ap_rearm[(chat_id, reflex)] = now + AP_REARM
                        cfg.ap_state.pop(reflex, None)
                        if not off and peak >= 2 and self.ap_brain:
                            self.ap_after[(chat_id, reflex)] = now + AP_AFTER_S
                            self.ap_doubt_ease(cfg, reflex, now)
                        trans.append((reflex, cur, 0, "off" if off else "done", float(peak), int(now - float(s.get("start", now)))))
                    else:
                        s["lvl"], s["low"], s["lt"], s["r0"] = new, now, now, score
                        trans.append((reflex, cur, new, "step", score, actors))
                    dirty = True
            if _ap_lvl(cfg.ap_state.get(reflex)) >= 2:
                self.ap_hot[(chat_id, reflex)] = now
        if self.ap_brain:
            for reflex in AP_VEC_REFLEXES:
                s = cfg.ap_state.get(reflex)
                if not s:
                    continue
                if _ap_lvl(s) >= 2:
                    merged = sorted(set(s.get("vec") or ()) | set(self.ap_vec_hot(chat_id, now)))
                    if merged != list(s.get("vec") or ()):
                        s["vec"], dirty = merged, True
                elif s.get("vec"):
                    s.pop("vec", None)
                    dirty = True
        levels = {r: _ap_lvl(s) for r, s in cfg.ap_state.items() if r in AP_REFLEXES and _ap_lvl(s) > 0}
        stale: list = []
        for reflex, lv in levels.items():
            if lv >= 2:
                s = cfg.ap_state[reflex]
                start = float(s.get("start", now) or now)
                last = float(s.get("rem", 0.0) or 0.0) or start
                if now - start >= AP_STALE_S and now - last >= AP_STALE_EVERY:
                    s["rem"] = now
                    stale.append((reflex, lv, int(now - start)))
                    dirty = True
        newest = 0.0
        for src in (self.radar.get(chat_id), self.ap_pulses.get(chat_id)):
            if src:
                newest = max(newest, max(e[0] for e in src))
        if newest > cfg.ap_threat_t:
            cfg.ap_threat_t, dirty = newest, True
        if levels and now - cfg.ap_threat_t > 30.0:
            cfg.ap_threat_t, dirty = now, True
        calm = False
        if (not levels and self.ap_calm_after > 0 and now >= float(cfg.ap_cool.get("calm", 0.0))
                and now - st.added >= AP_CALM_MIN_AGE and not self.strict_active(chat_id, now) and not self.raid_active(chat_id, now)):
            quiet_for = now - (cfg.ap_threat_t or st.added)
            calm = quiet_for >= self.ap_calm_after * (1.0 + 0.5 * min(scar, AP_SCAR_CAP))
        if calm != ("calm" in cfg.ap_state):
            if calm:
                cfg.ap_state["calm"] = {"lvl": 1, "since": now}
            else:
                cfg.ap_state.pop("calm", None)
            trans.append(("calm", 0 if calm else 1, 1 if calm else 0, "", 0.0, 0))
            dirty = True
        changes = self.ap_apply(cfg, self.ap_desired(cfg, levels, calm))
        if trans or changes or stale:
            dirty = True
            for reflex, old, new, why, score, actors in trans:
                self.ap_note(chat_id, now, self._ap_note_text(reflex, old, new, why, score, actors))
            strict = any(r == "wave" and new >= 3 > old for r, old, new, *_ in trans)
            rep = {"trans": trans, "changes": changes, "levels": dict(levels), "calm": calm, "strict": strict, "stale": stale}
            self._event("ap", chat=chat_id, **rep)
            if trans or changes:
                self.store.bump(st, "ap_change", now=now)
        else:
            rep = None
        if dirty:
            self.store.dirty = True
        return rep

    def ap_eta(self, chat_id: int, reflex: str, now: float) -> float | None:
        st = self.store.chats.get(chat_id)
        s = st.cfg.ap_state.get(reflex) if st is not None else None
        cur = _ap_lvl(s)
        if cur <= 0 or reflex not in AP_REFLEXES:
            return None
        mult, hold_k, _ = self.ap_mult(st.cfg, now)
        score, _a = self.ap_score(chat_id, reflex, now, True)
        keep = AP_TRIP[reflex][cur - 1][0] * mult * AP_KEEP
        decay = RADAR_HALF * math.log2(score / keep) if score > keep > 0 else 0.0
        wait = AP_HOLD[cur] * hold_k * (0.5 if score <= 0 else 1.0)
        low = float(s.get("low", 0.0) or 0.0)
        left = max(0.0, wait - (now - low)) if (low and decay <= 0) else wait
        return decay + left

    @staticmethod
    def _ap_note_text(reflex: str, old: int, new: int, why: str, score: float, actors: int) -> str:
        if reflex == "calm":
            return "затишье: смягчаю мелочи" if new else "затишье кончилось: возвращаю как было"
        label = AP_REFLEXES[reflex]["label"]
        if why == AP_OWNER_WHY:
            return f"{label}: владелец откатил настройку — отступаю на {human_dur(int(score or AP_OVERRIDE_COOL))}"
        if new == 0:
            return f"{label}: отбой" + (" (выключен владельцем)" if why == "off" else "")
        if new < old:
            return f"{label}: оценка спала ({score:g}, источников {actors}) — снижаю до уровня «{AP_LEVEL_NAME[new]}»"
        return (f"{label}: уровень «{AP_LEVEL_NAME[new]}» (оценка {score:g}, источников {actors})"
                + (f" — {why}" if why and why != "угроза" else ""))

    def ap_release_all(self, chat_id: int, now: float | None = None, how: str = "off") -> dict | None:
        now = self.clock() if now is None else now
        st = self.store.chats.get(chat_id)
        if st is None:
            return None
        cfg = st.cfg
        self._ap_sanitize(cfg)
        trans = [(r, _ap_lvl(s), 0, how, 0.0, 0) for r, s in cfg.ap_state.items() if r in AP_REFLEXES or r == "calm"]
        cfg.ap_state = {}
        changes = self.ap_apply(cfg, {})
        cfg.ap_before, cfg.ap_applied = {}, {}
        for k in [k for k in self.ap_hot if k[0] == chat_id]:
            self.ap_hot.pop(k, None)
        if not (trans or changes):
            return None
        for reflex, old, new, why, score, actors in trans:
            self.ap_note(chat_id, now, self._ap_note_text(reflex, old, new, why, score, actors))
        self.store.dirty = True
        rep = {"trans": trans, "changes": changes, "levels": {}, "calm": False, "strict": False, "stale": []}
        self._event("ap", chat=chat_id, **rep)
        return rep

    def ap_levels(self, chat_id: int) -> dict:
        st = self.store.chats.get(chat_id)
        if st is None or not isinstance(st.cfg.ap_state, dict):
            return {}
        return {r: _ap_lvl(s) for r, s in st.cfg.ap_state.items() if r in AP_REFLEXES and _ap_lvl(s) > 0}

    def _ap_prune(self, now: float) -> None:
        for cid in list(self.ap_pulses):
            dq = self.ap_pulses[cid]
            while dq and now - dq[0][0] > RADAR_WINDOW:
                dq.popleft()
            if not dq:
                self.ap_pulses.pop(cid, None)
        for cid in list(self.ap_vec):
            dq = self.ap_vec[cid]
            while dq and now - dq[0][0] > RADAR_WINDOW:
                dq.popleft()
            if not dq:
                self.ap_vec.pop(cid, None)
        for k in [k for k, t in self.ap_rearm.items() if t <= now]:
            self.ap_rearm.pop(k, None)
        for d in (self.ap_vigil, self.ap_after):
            for k in [k for k, t in d.items() if t <= now]:
                d.pop(k, None)
        for k in [k for k, t in self.ap_hot.items() if now - t > AP_NEIGHBOR_S]:
            self.ap_hot.pop(k, None)
        for k in [k for k, t in self.ap_admin_t.items() if now - t > 2 * 86400]:
            self.ap_admin_t.pop(k, None)
        for k in list(self.ap_known):
            seen = self.ap_known[k]
            for c in [c for c, t in seen.items() if now - t > AP_KNOWN_S]:
                seen.pop(c, None)
            if not seen:
                self.ap_known.pop(k, None)
        if len(self.ap_known) > AP_KNOWN_CAP:
            for k, _v in sorted(self.ap_known.items(), key=lambda kv: max(kv[1].values()))[:len(self.ap_known) - AP_KNOWN_CAP]:
                self.ap_known.pop(k, None)


class TrMsg(NamedTuple):
    uid: int
    ts: float
    q: bool
    first: frozenset
    edits: int
    replied: bool


_TR_QUESTION = re.compile(r"(?i)\b(?:кто|как|где|что|какой|какая|какие|какое|сколько|куда|откуда|почему|зачем|когда|подскажите|"
                          r"подскажи|посоветуйте|посоветуй|помогите|помоги|ищу|нужен|нужна|нужно|нужны|есть ли|можно ли|стоит ли)\b")
_B36 = "0123456789abcdefghijklmnopqrstuvwxyz"


def trace_question(text: str) -> bool:
    t = (text or "").strip()
    return len(t) >= 8 and ("?" in t or bool(_TR_QUESTION.search(t[:200])))


def hours_bump(prof: str, hour: int) -> str:
    c = [int(x, 36) for x in prof] if len(prof) == 24 and all(x in _B36 for x in prof) else [0] * 24
    c[hour % 24] += 1
    if c[hour % 24] > 35:
        c = [x // 2 for x in c]
    return "".join(_B36[min(35, x)] for x in c)


def hours_odd(prof: str, hour: int) -> bool:
    if len(prof) != 24 or not all(x in _B36 for x in prof):
        return False
    c = [int(x, 36) for x in prof]
    total = sum(c)
    if total < TRACE_HOURS_MIN:
        return False
    return c[hour % 24] / total <= 0.015 and (c[(hour - 1) % 24] + c[(hour + 1) % 24]) / total <= 0.06


TRACE_POST_UID = -777


class TraceCore:

    def init_trace(self) -> None:
        self.trace_on = True
        self.tr_book: dict[int, OrderedDict] = {}
        self.tr_lat: dict[int, deque] = {}
        self.tr_ts: dict[tuple, deque] = {}
        self.tr_replies: dict[tuple, deque] = {}
        self.tr_edges: dict[tuple, deque] = {}
        self.tr_woke: dict[tuple, float] = {}
        self.tr_case: dict[tuple, dict] = {}
        self.tr_admins: dict[int, set] = {}
        self.tr_log: dict[int, deque] = {}

    def _tr_est(self, chat: ChatState, uid: int, now: float) -> bool:
        if uid in self.tr_admins.get(chat.chat_id, ()):
            return True
        rec = chat.users.get(uid)
        return bool(rec and self.tier(rec, now) != "new")

    def _trace_admin(self, msg: Msg, now: float) -> None:
        self.tr_admins.setdefault(msg.chat_id, set()).add(msg.user_id)
        if not msg.edited and msg.text:
            book = self.tr_book.setdefault(msg.chat_id, OrderedDict())
            book[msg.msg_id] = TrMsg(msg.user_id, now, trace_question(msg.text), frozenset(), 0, False)
            while len(book) > TRACE_BOOK_MAX:
                book.popitem(last=False)

    def _trace_record(self, msg: Msg, chat: ChatState, rec: UserRec, tier: str, a: Analysis, now: float) -> None:
        if not self.trace_on or chat.cfg.trace == "off":
            return
        cid, uid = msg.chat_id, msg.user_id
        book = self.tr_book.setdefault(cid, OrderedDict())
        if msg.edited:
            old = book.get(msg.msg_id)
            if old is not None and old.uid == uid:
                book[msg.msg_id] = old._replace(edits=old.edits + 1)
            return
        if not msg.text and not msg.reply_to:
            return
        est = self._tr_est(chat, uid, now)
        book[msg.msg_id] = TrMsg(uid, now, trace_question(msg.text), frozenset(a.contacts), 0, False)
        while len(book) > TRACE_BOOK_MAX:
            book.popitem(last=False)
        if msg.reply_to:
            par = book.get(msg.reply_to)
            if par is not None and par.uid != uid:
                if est:
                    if not par.replied:
                        book[msg.reply_to] = par._replace(replied=True)
                    if par.q:
                        self.tr_lat.setdefault(cid, deque(maxlen=300)).append(max(0.0, now - par.ts))
                self.tr_replies.setdefault((cid, uid), deque(maxlen=6)).append((now, a.fp[1], par.uid, msg.reply_to))
        if msg.reply_uid and msg.reply_uid != uid:
            other_est = self._tr_est(chat, msg.reply_uid, now)
            self.tr_edges.setdefault((cid, uid), deque(maxlen=20)).append((now, msg.reply_uid, other_est))
            self.tr_edges.setdefault((cid, msg.reply_uid), deque(maxlen=20)).append((now, uid, est))
        self.tr_ts.setdefault((cid, uid), deque(maxlen=14)).append(now)
        rec.hours = hours_bump(rec.hours, time.gmtime(now).tm_hour)

    def trace_post(self, chat_id: int, msg_id: int, now: float) -> None:
        st = self.store.chats.get(chat_id)
        if not self.trace_on or st is None or st.cfg.trace == "off":
            return
        book = self.tr_book.setdefault(chat_id, OrderedDict())
        book[msg_id] = TrMsg(TRACE_POST_UID, now, True, frozenset(), 0, False)
        while len(book) > TRACE_BOOK_MAX:
            book.popitem(last=False)

    def trace_fast_thr(self, chat_id: int) -> float:
        lat = self.tr_lat.get(chat_id)
        if lat and len(lat) >= 30:
            s = sorted(lat)
            return max(TRACE_FAST_MIN, min(TRACE_FAST_S, 0.6 * s[len(s) // 5]))
        return TRACE_FAST_S

    def _trace_find(self, msg: Msg, chat: ChatState, rec: UserRec, tier: str, a: Analysis, now: float, prev_seen: float) -> dict:
        cid, uid = msg.chat_id, msg.user_id
        key = (cid, uid)
        book = self.tr_book.get(cid) or {}
        ev: dict[str, tuple] = {}

        orig = book.get(msg.msg_id) if msg.edited else None
        if orig is not None and orig.uid == uid:
            added = [c for c in a.contacts if c not in orig.first]
            if added:
                w = TRACE_STRONG["inject"]
                if TRACE_EDIT_DELAY <= now - orig.ts <= TRACE_BOOK_TTL:
                    w += 0.5
                if orig.replied:
                    w += 0.5
                ev["inject"] = (min(w, 4.5), f"правка: после отправки добавлен контакт или ссылка ({added[0]})")
            if orig.edits >= 2:
                ev["multi_edit"] = (TRACE_SOFT["multi_edit"], "сообщение правили три раза и больше")

        if prev_seen and now - prev_seen >= TRACE_WOKE_GAP and now - rec.first_seen >= TRACE_WOKE_AGE:
            self.tr_woke[key] = now + TRACE_WOKE_HOLD
        if self.tr_woke.get(key, 0.0) > now:
            ev["woke"] = (TRACE_SOFT["woke"], "аккаунт вернулся после долгого молчания")
        if hours_odd(rec.hours, time.gmtime(now).tm_hour):
            ev["odd_hour"] = (TRACE_SOFT["odd_hour"], "пишет в час, в который никогда не писал")

        if not msg.edited:
            par = book.get(msg.reply_to) if msg.reply_to else None
            if par is not None and par.uid != uid and par.q and tier != "veteran":
                lat = now - par.ts
                if 0 <= lat <= self.trace_fast_thr(cid):
                    if a.has_contact:
                        w = TRACE_FAST_NEW if tier == "new" else TRACE_STRONG["fast_contact"]
                        if sum(1 for ts, _d in (self.tr_case.get(key, {}).get("fast_contact") or ()) if now - ts <= TRACE_CASE_TTL) >= 2:
                            w += 1.0
                        ev["fast_contact"] = (w, f"ответ на вопрос за {lat:.0f} с, и сразу со ссылкой или контактом")
                    else:
                        ev["fast_plain"] = (0.0, f"ответ на вопрос за {lat:.0f} с")
            exact, sim, ntok = a.fp
            reps = self.tr_replies.get(key)
            if ntok >= 4 and reps and msg.reply_to and (a.has_contact or tier == "new"):
                same = [r for r in reps if now - r[0] <= 3600 and r[3] != msg.reply_to and hamming(r[1], sim) <= 4]
                if same:
                    if a.has_contact:
                        w = TRACE_CANNED_NEW if tier == "new" else TRACE_STRONG["canned"]
                        ev["canned"] = (w + (0.5 if len(same) >= 2 else 0.0), "один и тот же ответ со ссылкой разным людям")
                    else:
                        ev["canned_plain"] = (0.0, "один и тот же ответ разным людям")
            ts = self.tr_ts.get(key)
            if ts and len(ts) + 1 >= TRACE_METRO_N:
                seq = list(ts) + [now]
                iv = [seq[i + 1] - seq[i] for i in range(len(seq) - 1)]
                mean = sum(iv) / len(iv)
                if 2.0 <= mean <= 900.0:
                    sd = (sum((x - mean) ** 2 for x in iv) / len(iv)) ** 0.5
                    if sd < mean * TRACE_METRO_CV:
                        ev["metro"] = (TRACE_SOFT["metro"], f"паузы между сообщениями почти одинаковые (≈{mean:.0f} с)")
            if tier == "new":
                edges = [e for e in (self.tr_edges.get(key) or ()) if now - e[0] <= 86400]
                if len(edges) >= TRACE_ECHO_MIN and not any(e[2] for e in edges):
                    ev["echo"] = (TRACE_SOFT["echo"], "за сутки общался только с такими же новичками")
        return ev

    def _trace_signals(self, msg: Msg, chat: ChatState, rec: UserRec, tier: str, a: Analysis, now: float, strict: bool,
                       prev_seen: float) -> None:
        cfg = chat.cfg
        if not self.trace_on or cfg.trace == "off":
            return
        ev = self._trace_find(msg, chat, rec, tier, a, now, prev_seen)
        if not ev:
            return
        key = (msg.chat_id, msg.user_id)
        case = self.tr_case.setdefault(key, {})
        for kind, (w, why) in ev.items():
            lst = case.setdefault(kind, [])
            lst.append((now, why))
            del lst[:-6]
        strong = {k: v for k, v in ev.items() if k in TRACE_STRONG}
        soft = {k: v for k, v in ev.items() if k in TRACE_SOFT}
        base = sum(w for _, w, _ in a.signals)
        floor = a.has_contact or base >= 1.0
        add: list[tuple] = [(f"trace_{k}", w, why) for k, (w, why) in strong.items()]
        if tier != "new" and not soft and base < 1.0:
            add = [(n, min(w, 1.5) if n in ("trace_inject", "trace_canned") else w, why) for n, w, why in add]
        if floor and soft and (strong or len(soft) >= (1 if strict else 2)):
            total = min(sum(w for w, _ in soft.values()), TRACE_SOFT_CAP_STRICT if strict else TRACE_SOFT_CAP)
            names = ", ".join(TRACE_LABEL[k] for k in soft)
            add.append(("trace_combo2" if len(soft) >= 2 else "trace_combo", round(total, 2), "поведение: " + names))
        if not add:
            return
        act = cfg.trace == "on" and now >= chat.learning_until
        log = self.tr_log.setdefault(msg.chat_id, deque(maxlen=60))
        log.append({"ts": now, "uid": msg.user_id, "name": msg.name, "kinds": [n[6:] for n, _, _ in add],
                    "w": round(sum(w for _, w, _ in add), 2), "applied": act, "why": add[0][2]})
        if not act:
            return
        a.signals.extend(add)
        self.store.bump(chat, "trace_hit", now=now)
        if strong:
            self.radar_note(msg.chat_id, msg.user_id, "trace", now)

    def _trace_prune(self, now: float) -> None:
        for cid in list(self.tr_book):
            book = self.tr_book[cid]
            while book:
                mid = next(iter(book))
                if now - book[mid].ts <= TRACE_BOOK_TTL:
                    break
                book.pop(mid)
            if not book:
                self.tr_book.pop(cid, None)
        for d, idx in ((self.tr_ts, None), (self.tr_replies, 0), (self.tr_edges, 0)):
            for k in list(d):
                dq = d[k]
                last = dq[-1] if idx is None else dq[-1][idx]
                if now - last > 86400:
                    d.pop(k, None)
        for k in [k for k, t in self.tr_woke.items() if t <= now]:
            self.tr_woke.pop(k, None)
        for k in list(self.tr_case):
            c = self.tr_case[k]
            for kind in list(c):
                c[kind] = [e for e in c[kind] if now - e[0] <= TRACE_CASE_TTL]
                if not c[kind]:
                    c.pop(kind)
            if not c:
                self.tr_case.pop(k, None)
        for cid in [c for c, dq in self.tr_lat.items() if not dq]:
            self.tr_lat.pop(cid, None)


# ══════════════════════════════════════════════════════════════════════════════════════
#  САМООБУЧЕНИЕ
#  Бот учится ТОЛЬКО у владельцев (кнопки в личке или пересланный им спам) и никогда не хранит тексты:
#  в памяти остаются отпечатки (simhash, MinHash-набросок из 32 чисел, хэши слов, контакты).
# ══════════════════════════════════════════════════════════════════════════════════════
log_learn = logging.getLogger("guard.learn")

LEARN_K = 32
LEARN_MIN_STEMS = 6
LEARN_SPAM_MAX, LEARN_HAM_MAX = 200, 120
LEARN_SPAM_TTL, LEARN_HAM_TTL = 60 * 86400, 90 * 86400
LEARN_CONTACT_TTL = 30 * 86400
LEARN_D = 6
LEARN_SIM_HI, LEARN_SIM_MID, LEARN_SIM_LO = 0.65, 0.45, 0.30
LEARN_W = {3: 5.0, 2: 4.2, 1: 3.0}
LEARN_W_SHADOW = 2.2
LEARN_CARD_TTL = 36 * 3600
LEARN_CARD_MAX = 80
LEARN_CARDS_HOUR, LEARN_CARDS_DAY = 5, 20
LEARN_ASK_MIN = 2.5
LEARN_CAL_HALF = 21 * 86400
LEARN_CAL_STEP, LEARN_CAL_CAP = 0.10, 0.30
LEARN_BAYES_CAP = 5000
LEARN_BAYES_MIN_HAM, LEARN_BAYES_MIN_SPAM = 150, 3
LEARN_BAYES_HALF = 45 * 86400
LEARN_HIT_LOG = 400
LEARN_OK_AFTER = 24 * 3600
LEARN_TRUST_START, LEARN_TRUST_OK, LEARN_TRUST_BAD = 3.0, 1.0, 2.5
LEARN_SWEEP_WINDOW = 2 * 3600
LEARN_SWEEP_MAX = 30
LEARN_REPORT_HOUR = 21
LEARN_DAYS_KEEP = 14
LEARN_OKC_TTL = 60 * 86400

LEARN_STOP = frozenset(
    "и в во на не что он она оно они это как так то а но да нет ни за из от до по об о у к ко с со же ли бы вот тут там "
    "для при без под над про или его ее их мне нам вам вас меня тебя тебе себя мой моя мои наш ваш был была было были "
    "быть есть еще уже тоже только очень можно нужно будет ну вы мы ты я уж ей ему им нас этот эта эти тот та те "
    "the and for you are with that this have not but was were".split())
_LEARN_CUT = re.compile(r"https?://\S+|www\.\S+|@\w+")


def learn_stems(n: Norm) -> list:
    """Основы слов для отпечатка: без ссылок и @имён, числа сведены к «#длина»."""
    text = deglyph(n.folded) if n.mixed else n.folded
    text = _LEARN_CUT.sub(" ", text[:3000])
    out: list = []
    for t in TOKEN_RE.findall(text):
        t = collapse(t)
        if t.isdigit():
            out.append("#" + str(min(len(t), 6)))
        elif len(t) >= 2 and t not in LEARN_STOP:
            out.append(t[:5])
        if len(out) >= 300:
            break
    return out


def _h32(s: str) -> int:
    return zlib.crc32(s.encode("utf-8")) & 0xFFFFFFFF


def learn_sketch(stems: list, k: int = LEARN_K) -> list:
    """MinHash-набросок (bottom-k) по двух- и трёхсловным кускам: переживает вставку слов и перестановки."""
    if len(stems) < LEARN_MIN_STEMS:
        return []
    hs: set = set()
    for i in range(len(stems) - 1):
        hs.add(_h32(stems[i] + " " + stems[i + 1]))
        if i + 2 < len(stems):
            hs.add(_h32(stems[i] + " " + stems[i + 1] + " " + stems[i + 2]))
    return sorted(hs)[:k]


def learn_words(stems: list) -> list:
    return sorted({_h32(s) for s in stems})[:60]


def sketch_sim(a: list, b: list, k: int = LEARN_K) -> float:
    sa, sb = set(a), set(b)
    u = sorted(sa | sb)[:k]
    if not u:
        return 0.0
    return sum(1 for h in u if h in sa and h in sb) / len(u)


class LearnCore:

    def init_learn(self) -> None:
        self.learn_on = True
        self._lhits: deque = deque(maxlen=LEARN_HIT_LOG)
        self._lhit_keys: set = set()
        self._lask: dict = {}
        self._lsets: dict = {}
        self._la = None
        self._ldirty_t = 0.0

    # ───────── хранилище (всё лежит в store.meta["learn"] и переживает перезапуск вместе с остальным состоянием)
    def _L(self) -> dict:
        d = self.store.meta.get("learn")
        if d is not None and "g" in d and "cards" in d:
            return d
        d = d if isinstance(d, dict) else {}
        d.setdefault("g", {})
        d["g"].setdefault("spam", {})
        d["g"].setdefault("bs", {})
        d["g"].setdefault("ns", 0.0)
        d["g"].setdefault("gc_t", 0.0)
        d.setdefault("c", {})
        d.setdefault("cards", {})
        d.setdefault("seq", 0)
        self.store.meta["learn"] = d
        return d

    def _lbook(self, chat_id: int, create: bool = True) -> dict | None:
        c = self._L()["c"]
        k = str(chat_id)
        b = c.get(k)
        if b is None:
            if not create:
                return None
            b = c[k] = {"ham": {}, "cal": {}, "bh": {}, "nh": 0.0, "okc": {}, "day": {}}
        return b

    def _lday(self, chat_id: int, now: float) -> dict:
        b = self._lbook(chat_id)
        days = b["day"]
        d = days.setdefault(self.store.day(now), {})
        if len(days) > LEARN_DAYS_KEEP:
            for k in sorted(days)[:-LEARN_DAYS_KEEP]:
                days.pop(k, None)
        return d

    def _lcount(self, chat_id: int, key: str, now: float, n: int = 1) -> None:
        d = self._lday(chat_id, now)
        d[key] = d.get(key, 0) + n
        self.store.dirty = True

    def _ltouch(self, now: float) -> None:
        if now - self._ldirty_t > 300:
            self._ldirty_t = now
            self.store.dirty = True

    def learn_spam_count(self) -> int:
        return len(self._L()["g"]["spam"])

    # ───────── признаки сообщения
    def _lfeat(self, a: "Analysis") -> dict | None:
        n = a.norm
        if n is None:
            return None
        stems = learn_stems(n)
        sk = learn_sketch(stems)
        # шаблон строим только из достаточно длинного текста: по короткой фразе simhash цепляет лишнее
        return {"st": stems, "sk": sk, "sim": a.fp[1] if (sk and a.fp[2] >= 5) else 0, "nt": a.fp[2], "bh": learn_words(stems)}

    def _pset(self, pid: str, p: dict) -> frozenset:
        c = self._lsets.get(pid)
        if c is None or c[0] is not p.get("sk"):
            c = self._lsets[pid] = (p.get("sk"), frozenset(p.get("sk") or ()))
            if len(self._lsets) > 800:
                self._lsets.clear()
        return c[1]

    def _lmatch(self, pats: dict, f: dict) -> tuple:
        """Лучшее совпадение с набором шаблонов → (id, уровень 0..3, сходство MinHash, расстояние simhash)."""
        best: tuple = ("", 0, 0.0, 99)
        sk, sim = f["sk"], f["sim"]
        if not sk and not sim:
            return best
        skset = set(sk)
        for pid, p in pats.items():
            d = hamming(sim, p["sim"]) if sim and p.get("sim") else 99
            s = 0.0
            if skset and p.get("sk") and (skset & self._pset(pid, p)):
                s = sketch_sim(sk, p["sk"])
            if d <= 3 or s >= LEARN_SIM_HI:
                lvl = 3
            elif d <= LEARN_D or s >= LEARN_SIM_MID:
                lvl = 2
            elif s >= LEARN_SIM_LO:
                lvl = 1
            else:
                continue
            if (lvl, s, -d) > (best[1], best[2], -best[3]):
                best = (pid, lvl, s, d)
        return best

    # ───────── сигналы при проверке сообщения
    def _cal_mult(self, book: dict, name: str, now: float) -> float:
        e = book["cal"].get(name)
        if not e:
            return 1.0
        f = 0.5 ** (max(0.0, now - e[2]) / LEARN_CAL_HALF)
        s, h = e[0] * f, e[1] * f
        if s + h < 2.0:
            return 1.0
        return 1.0 + max(-LEARN_CAL_CAP, min(LEARN_CAL_CAP, LEARN_CAL_STEP * (s - h)))

    def _bayes_w(self, book: dict | None, f: dict) -> float:
        """Слова-маркеры: сколько слов сообщения встречалось в отмеченном спаме и почти не встречается в обычной речи чата."""
        g = self._L()["g"]
        ns = g["ns"]
        nh = book["nh"] if book else 0.0
        if ns < LEARN_BAYES_MIN_SPAM or nh < LEARN_BAYES_MIN_HAM or not f["bh"]:
            return 0.0
        bs, bh = g["bs"], book["bh"]
        llr, used = 0.0, 0
        for h in f["bh"]:
            s = bs.get(str(h), 0.0)
            if s < 2.0:
                continue
            ps = (s + 0.5) / (ns + 1.0)
            ph = (bh.get(str(h), 0.0) + 0.5) / (nh + 1.0)
            x = math.log(ps / ph)
            if x > 0.5:
                llr += x
                used += 1
        if used < 3:
            return 0.0
        return round(min(2.0, max(0.0, (llr - 5.0) * 0.25)), 2)

    def _lhit(self, cid: int, msg: "Msg", pid: str, now: float) -> None:
        key = (cid, msg.msg_id)
        if msg.edited or key in self._lhit_keys:
            return
        if len(self._lhits) == self._lhits.maxlen:
            old = self._lhits[0]
            self._lhit_keys.discard((old[1], old[4]))
        self._lhit_keys.add(key)
        self._lhits.append((now, cid, msg.user_id, pid, msg.msg_id))
        p = self._L()["g"]["spam"].get(pid)
        if p is not None:
            p["n"] = p.get("n", 0) + 1
            p["t"] = round(now)
        self._lcount(cid, "hit", now)

    def _learn_signals(self, msg: "Msg", chat: "ChatState", a: "Analysis", tier: str, now: float) -> None:
        cfg = chat.cfg
        if not (self.learn_on and cfg.learn and cfg.scam):
            return
        f = self._lfeat(a)
        a.lf = f
        if f is None:
            return
        sig, cid = a.signals, msg.chat_id
        L = self._L()
        book = self._lbook(cid, create=False)
        if book and book["cal"]:
            for i, (name, w, why) in enumerate(sig):
                if w > 0 and name not in HARD_SIGNALS and not name.startswith("learned"):
                    m = self._cal_mult(book, name, now)
                    if m != 1.0:
                        sig[i] = (name, round(w * m, 2), why)
        hard = sum(w for n, w, _ in sig if n in HARD_SIGNALS)
        soft = sum(w for n, w, _ in sig if w > 0 and n not in HARD_SIGNALS)
        spam = L["g"]["spam"]
        sp_id, sp_lvl, sp_s, sp_d = self._lmatch(spam, f) if spam else ("", 0, 0.0, 99)
        hm_id, hm_lvl, hm_s, hm_d = ("", 0, 0.0, 99)
        if book and book["ham"]:
            hm_id, hm_lvl, hm_s, hm_d = self._lmatch(book["ham"], f)
        okc = book["okc"] if book else None
        if okc and a.contacts and all(t in okc and now - okc[t] <= LEARN_OKC_TTL for t in a.contacts) and hm_lvl < 2:
            hm_id, hm_lvl = "contact", 2
        if sp_lvl and hm_lvl < sp_lvl:
            if sp_lvl >= 2 or soft >= 1.0 or a.has_contact:
                p = spam[sp_id]
                pct = int(round(100 * max(sp_s, 1.0 - sp_d / 64.0)))
                if sp_lvl == 1:
                    # отдалённое сходство: «в тени». Оценку подталкиваем, но сами не решаем, а спрашиваем владельца
                    sig.append(("learned_spam_soft", LEARN_W_SHADOW, f"отдалённо похоже на спам, который вы отметили ({pct}%)"))
                    a.lhit = "spam~" + sp_id
                else:
                    if (p.get("soft") or tier == "veteran") and tier != "new":
                        sig.append(("learned_spam_soft", min(LEARN_W[sp_lvl], 3.2), f"похоже на спам, который вы отметили ({pct}%)"))
                    else:
                        sig.append(("learned_spam", LEARN_W[sp_lvl], f"похоже на спам, который вы отметили ({pct}%)"))
                    a.lhit = "spam:" + sp_id
                self._lhit(cid, msg, sp_id, now)
                self.store.bump(chat, "learn_hit", now=now)
        elif hm_lvl >= 2 and hard == 0 and soft > 0:
            cut = round(min(3.0, soft * 0.85), 2)
            sig.append(("learned_ham", -cut, "вы уже разрешали такое"))
            a.lhit = "ham:" + hm_id
        if not a.lhit:
            w = self._bayes_w(book, f)
            if w > 0 and (soft >= 0.5 or a.has_contact):
                sig.append(("learned_words", w, "слова как в отмеченном вами спаме"))

    # ───────── после проверки: словарь «обычной речи», карточки владельцу
    def _learn_post(self, msg: "Msg", v: "Verdict", la: tuple, now: float) -> None:
        ana, tier, strict, chat, rec = la
        cfg = chat.cfg
        if not (self.learn_on and cfg.learn and cfg.scam) or ana.lf is None:
            return
        if v.ok and not v.category and ana.raw < 0.5:
            if tier != "new" and not msg.edited and len(ana.lf["bh"]) >= 3:
                self._bayes_add_ham(self._lbook(msg.chat_id), ana.lf["bh"], 1.0)
                self._ltouch(now)
            return
        if (v.delete or v.ban) and v.category in ("scam", "scam_ban") and v.score >= STRONG_SCAM and ana.lf["bh"]:
            self._bayes_add_spam(ana.lf["bh"], 1.0)
            self._ltouch(now)
        cid = self._learn_card_for(msg, v, ana, tier, strict, now)
        if cid:
            v.info["learn_card"] = cid

    def _learn_card_for(self, msg: "Msg", v: "Verdict", ana: "Analysis", tier: str, strict: bool, now: float) -> str:
        if v.ban or v.info.get("puppet") or msg.edited or (ana.lhit and not ana.lhit.startswith("spam~")):
            return ""
        if tier != "new" and v.ok:
            return ""
        eff = v.score
        if v.ok:
            ask_min = 1.5 if strict else LEARN_ASK_MIN
            top = (DELETE_T_S if strict else DELETE_T)
            if not (ask_min <= eff < top) or not (ana.has_contact or ana.raw >= 3.0):
                return ""
            kind = "keep"
        else:
            if v.category not in ("scam", "memory", "suspicious") or (v.category == "scam" and eff >= STRONG_SCAM):
                return ""
            kind = "del"
        f = ana.lf
        if not (f["sk"] or f["sim"] or ana.contacts or len(f["bh"]) >= 3):
            return ""
        cid = msg.chat_id
        cards = self._L()["cards"]
        ct = list(ana.contacts)[:6]
        for c in cards.values():
            if c["cid"] != cid or c.get("done") or now - c["t"] > 24 * 3600:
                continue
            same = (c["uid"] == msg.user_id or (f["sim"] and c["sim"] and hamming(f["sim"], c["sim"]) <= LEARN_D)
                    or (f["sk"] and c["sk"] and sketch_sim(f["sk"], c["sk"]) >= LEARN_SIM_LO)
                    or (ct and set(ct) & set(c["ct"])))
            if same:
                c["dup"] = c.get("dup", 0) + 1
                self.store.dirty = True
                return ""
        dq = self._lask.setdefault(cid, deque(maxlen=64))
        while dq and now - dq[0] > 3600:
            dq.popleft()
        day = self._lday(cid, now)
        hour_lim, day_lim, _slow = self._learn_limits(cid, now)
        if len(dq) >= hour_lim or day.get("ask", 0) >= day_lim:
            day["sup"] = day.get("sup", 0) + 1
            return ""
        dq.append(now)
        L = self._L()
        L["seq"] += 1
        card_id = format(L["seq"], "x")
        sg = [[n, round(w, 2)] for n, w, _ in ana.signals if w > 0 and n not in HARD_SIGNALS and not n.startswith("learned")][:8]
        top3 = sorted(ana.signals, key=lambda s: -s[1])[:3]
        cards[card_id] = {"cid": cid, "mid": msg.msg_id, "uid": msg.user_id, "t": round(now), "tier": tier, "eff": round(eff, 2),
                          "kind": kind, "sim": f["sim"], "sk": f["sk"], "bh": f["bh"], "ct": ct, "sg": sg, "own": {}, "dup": 0,
                          "why": "; ".join(s[2] for s in top3 if s[1] > 0)[:200]}
        day["ask"] = day.get("ask", 0) + 1
        if len(cards) > LEARN_CARD_MAX:
            for k in sorted(cards, key=lambda k: cards[k]["t"])[:len(cards) - LEARN_CARD_MAX]:
                cards.pop(k, None)
        self.store.dirty = True
        return card_id

    def _learn_limits(self, chat_id: int, now: float) -> tuple:
        """Если владелец почти не отвечает на карточки, бот сам начинает спрашивать реже (и снова чаще, когда ответы пошли)."""
        b = self._lbook(chat_id, create=False)
        asked = answered = 0
        if b:
            for i in range(3):
                d = b["day"].get(self.store.day(now - i * 86400)) or {}
                asked += d.get("ask", 0)
                answered += d.get("spam", 0) + d.get("ham", 0) + d.get("skip", 0)
        if asked >= 6 and answered < 0.3 * asked:
            return 2, 6, True
        return LEARN_CARDS_HOUR, LEARN_CARDS_DAY, False

    def note_overturn(self, chat_id: int, uid: int) -> None:
        try:
            self.learn_overturn(chat_id, uid, self.clock())
        except Exception:
            log_learn.exception("самообучение: учёт отмены наказания не удался")

    def learn_card(self, card_id: str) -> dict | None:
        return self._L()["cards"].get(card_id)

    # ───────── словари слов
    def _bayes_add_spam(self, hashes: list, w: float) -> None:
        g = self._L()["g"]
        bs = g["bs"]
        for h in hashes:
            k = str(h)
            bs[k] = bs.get(k, 0.0) + w
        g["ns"] = g["ns"] + w
        if len(bs) > LEARN_BAYES_CAP * 1.3:
            self._bayes_trim(bs)

    def _bayes_add_ham(self, book: dict, hashes: list, w: float) -> None:
        bh = book["bh"]
        for h in hashes:
            k = str(h)
            bh[k] = bh.get(k, 0.0) + w
        book["nh"] = book["nh"] + w
        if len(bh) > LEARN_BAYES_CAP * 1.3:
            self._bayes_trim(bh)

    @staticmethod
    def _bayes_trim(d: dict) -> None:
        for k in sorted(d, key=lambda k: d[k])[:max(0, len(d) - LEARN_BAYES_CAP)]:
            d.pop(k, None)

    # ───────── решение владельца
    def _add_pattern(self, pats: dict, f: dict, cap: int, now: float, by: int, why: str, extra: dict | None = None) -> tuple:
        """Добавить шаблон или слить с похожим. → (id, новый_ли)."""
        pid, lvl, _s, _d = self._lmatch(pats, f) if (f["sk"] or f["sim"]) else ("", 0, 0.0, 99)
        if pid and lvl >= 2:
            p = pats[pid]
            p["t"] = round(now)
            p["adm"] = p.get("adm", 0) + 1
            if f["sk"] and len(f["sk"]) >= len(p.get("sk") or ()):
                p["sk"] = f["sk"]
            if extra:
                for k, val in extra.items():
                    if isinstance(val, list):
                        p[k] = list(dict.fromkeys((p.get(k) or []) + val))[:6]
            return pid, False
        if not (f["sk"] or f["sim"]):
            return "", False
        L = self._L()
        L["seq"] += 1
        pid = format(L["seq"], "x")
        pats[pid] = {"t": round(now), "c": round(now), "sim": f["sim"], "sk": f["sk"], "n": 0, "ok": 0, "bad": 0, "adm": 1,
                     "by": by, "w": why[:60]}
        if extra:
            pats[pid].update(extra)
        if len(pats) > cap:
            for k in sorted(pats, key=lambda k: (pats[k].get("n", 0) + 3 * pats[k].get("adm", 0), pats[k]["t"]))[:len(pats) - cap]:
                pats.pop(k, None)
        return pid, True

    def _cal_add(self, book: dict, signals: list, spam: bool, now: float) -> None:
        for name, _w in signals:
            e = book["cal"].get(name)
            if e:
                f = 0.5 ** (max(0.0, now - e[2]) / LEARN_CAL_HALF)
                e[0], e[1] = e[0] * f, e[1] * f
            else:
                e = book["cal"][name] = [0.0, 0.0, now]
            e[0 if spam else 1] += 1.0 if spam else 1.5
            e[2] = now

    def _share_contacts(self, tokens: list, uid: int, now: float, why: str) -> int:
        """Контакты, подтверждённые владельцем, запоминаются во всех чатах бота (на 30 дней, а не на неделю)."""
        n = 0
        tokens = [t for t in tokens if t and t.lower() not in self.mem_protect]
        if not tokens or not self.memory_on:
            return 0
        for cid, st in self.store.chats.items():
            if not st.cfg.spam_memory:
                continue
            self._spam_learn(cid, uid, tokens, now, why)
            book = self._spam_book(cid)
            for t in tokens:
                e = book.get(t) if book else None
                if e is not None:
                    e["ttl"], e["adm"] = LEARN_CONTACT_TTL, 1
            n = len(tokens)
        return n

    def _collateral(self, chat_id: int, sim: int, skip_uid: int, now: float) -> int:
        """«Экзамен» шаблона на истории чата: сколько недавних сообщений ПРОВЕРЕННЫХ участников на него похожи."""
        if not sim:
            return 0
        chat = self.store.chats.get(chat_id)
        n = 0
        for ts, uid, mid, ex, s, nt in self.recent.get(chat_id, ()):
            if uid == skip_uid or nt < 5 or not s or hamming(s, sim) > LEARN_D:
                continue
            rec = chat.users.get(uid) if chat else None
            if rec is not None and self.tier(rec, now) != "new":
                n += 1
        return n

    def _sweep(self, chat_id: int, sim: int, uid0: int, now: float) -> dict:
        """Недавние почти-копии от НОВИЧКОВ: {uid: [id сообщений]}."""
        out: dict = {}
        if not sim:
            return out
        chat = self.store.chats.get(chat_id)
        total = 0
        for ts, uid, mid, ex, s, nt in list(self.recent.get(chat_id, ())):
            if uid == uid0 or nt < 5 or not s or now - ts > LEARN_SWEEP_WINDOW or hamming(s, sim) > LEARN_D:
                continue
            rec = chat.users.get(uid) if chat else None
            if rec is None or rec.vouched or self.tier(rec, now) != "new":
                continue
            out.setdefault(uid, []).append(mid)
            total += 1
            if total >= LEARN_SWEEP_MAX:
                break
        return out

    def learn_decide(self, card_id: str, act: str, by: int, now: float | None = None) -> dict:
        now = self.clock() if now is None else now
        c = self._L()["cards"].get(card_id)
        if c is None:
            return {"ok": False, "why": "gone"}
        if c.get("done"):
            return {"ok": False, "why": "done", "ans": c["done"]}
        cid, uid = c["cid"], c["uid"]
        res: dict = {"ok": True, "act": act, "cid": cid, "uid": uid, "delete": {}, "ban": [], "unmute": [], "notes": [], "cards": c}
        c["done"] = {"act": act, "by": by, "t": round(now)}
        chat = self.store.chat(cid)
        if act in ("s", "sb"):
            self._learn_spam(c, res, chat, now, act == "sb", by)
        elif act == "h":
            self._learn_ham(c, res, chat, now, by)
        else:
            self._lcount(cid, "skip", now)
        self.store.dirty = True
        return res

    def _cal_sub(self, book: dict, signals: list, spam: bool) -> None:
        for name, _w in signals:
            e = book["cal"].get(name)
            if e:
                e[0 if spam else 1] = max(0.0, e[0 if spam else 1] - (1.0 if spam else 1.5))

    def _learn_spam(self, c: dict, res: dict, chat: "ChatState", now: float, ban: bool, by: int) -> None:
        cid, uid = c["cid"], c["uid"]
        book = self._lbook(cid)
        L = self._L()
        fx = c["fx"] = {"k": "s", "rh": [], "ct": [], "okrm": [], "cal": [s[0] for s in c["sg"]], "strike": 0, "ban": []}
        f = {"sk": c["sk"], "sim": c["sim"], "bh": c["bh"]}
        pid = ""
        if f["sk"] or f["sim"]:
            coll = self._collateral(cid, f["sim"], uid, now)
            pid, new = self._add_pattern(L["g"]["spam"], f, LEARN_SPAM_MAX, now, by, "карточка", {"ct": list(c["ct"])})
            if pid:
                p = L["g"]["spam"][pid]
                fx["sp" if new else "spm"] = pid
                if coll:
                    p["soft"] = True
                    res["notes"].append(f"похожие тексты писали проверенные участники ({coll}) — для них шаблон будет только «на заметку»")
                res["notes"].append("шаблон спама запомнил" if new else "такой шаблон уже был — усилил")
                self._lcount(cid, "new" if new else "again", now)
                for k in [k for k, p2 in book["ham"].items() if self._lmatch({k: p2}, f)[1] >= 2]:
                    fx["rh"].append([k, book["ham"].pop(k)])
                    res["notes"].append("убрал противоречащее исключение «нормально»")
        if c["bh"]:
            self._bayes_add_spam(c["bh"], 5.0)
            fx["bs"] = 5.0
        if c["ct"]:
            n = self._share_contacts(c["ct"], uid, now, "владелец: спам")
            if n:
                fx["ct"] = [t for t in c["ct"] if t.lower() not in self.mem_protect]
                res["notes"].append(f"контактов запомнил: {n} (во всех чатах, на 30 дней)")
                self._lcount(cid, "cont", now, n)
            for t in c["ct"]:
                if t in book["okc"]:
                    fx["okrm"].append([t, book["okc"].pop(t)])
        self._cal_add(book, c["sg"], True, now)
        self._lcount(cid, "spam", now)
        rec = chat.users.get(uid)
        if c["mid"] and c.get("kind") == "keep":
            res["delete"].setdefault(cid, []).append(c["mid"])
        sweep = self._sweep(cid, c["sim"], uid, now)
        swept_strikes = []
        for u2, ids in sweep.items():
            res["delete"].setdefault(cid, []).extend(ids)
            r2 = chat.users.get(u2)
            if r2 is not None:
                if ban:
                    r2.banned = True
                    res["ban"].append(u2)
                    fx["ban"].append(u2)
                else:
                    r2.strikes.append([now, 0.8, "learn"])
                    r2.strikes = r2.strikes[-STRIKE_KEEP:]
                    swept_strikes.append(u2)
        fx["sw"] = swept_strikes
        if sweep:
            n = sum(len(v) for v in sweep.values())
            res["notes"].append(f"убрал похожие сообщения: {n} (авторов: {len(sweep)})")
            self._lcount(cid, "swept", now, n)
        if rec is not None:
            if ban and self.tier(rec, now) == "new":
                rec.banned = True
                res["ban"].append(uid)
                fx["ban"].append(uid)
                self.store.bump(chat, "ban", now=now)
            else:
                rec.strikes.append([now, 1.0, "learn"])
                rec.strikes = rec.strikes[-STRIKE_KEEP:]
                fx["strike"] = 1
        res["pid"] = pid

    def _learn_ham(self, c: dict, res: dict, chat: "ChatState", now: float, by: int) -> None:
        cid, uid = c["cid"], c["uid"]
        book = self._lbook(cid)
        L = self._L()
        fx = c["fx"] = {"k": "h", "rs": [], "okc": [], "bk": [], "cal": [s[0] for s in c["sg"]]}
        f = {"sk": c["sk"], "sim": c["sim"], "bh": c["bh"]}
        if f["sk"] or f["sim"]:
            pid, new = self._add_pattern(book["ham"], f, LEARN_HAM_MAX, now, by, "карточка")
            if pid:
                fx["hp" if new else "hpm"] = pid
                res["notes"].append("запомнил: такое — нормально" if new else "такое исключение уже было — усилил")
            spam = L["g"]["spam"]
            for k in [k for k, p in spam.items() if self._lmatch({k: p}, f)[1] >= 2]:
                fx["rs"].append([k, spam.pop(k)])
                res["notes"].append("убрал шаблон спама, который с этим спорил")
                self._lcount(cid, "drop", now)
        for t in c["ct"]:
            book["okc"][t] = round(now)
            fx["okc"].append(t)
            for st in self.store.chats.values():
                b = self._spam_book(st.chat_id)
                if b and t in b:
                    fx["bk"].append([st.chat_id, t, b.pop(t)])
        if c["ct"]:
            res["notes"].append(f"контакты признаны безопасными: {len(c['ct'])}")
        if c["bh"]:
            self._bayes_add_ham(book, c["bh"], 5.0)
            fx["bhw"] = 5.0
        self._cal_add(book, c["sg"], False, now)
        self._lcount(cid, "ham", now)
        rec = chat.users.get(uid)
        if rec is not None and (rec.muted_until > now or rec.banned):
            res["unmute"].append(uid)
        self.forgive(cid, uid)

    def learn_vouch(self, card_id: str) -> dict:
        """После «нормально»: поручиться за автора (бот будет считать его проверенным, как ветерана)."""
        c = self._L()["cards"].get(card_id)
        if c is None or not c.get("done") or c["done"].get("act") != "h" or c.get("fx") is None:
            return {"ok": False}
        rec = self.store.user(self.store.chat(c["cid"]), c["uid"], self.clock())
        if rec.vouched:
            return {"ok": False, "already": True}
        rec.vouched = True
        c["fx"]["vouch"] = True
        self.store.dirty = True
        return {"ok": True, "uid": c["uid"], "cid": c["cid"]}

    def learn_undo_card(self, card_id: str, by: int, now: float | None = None) -> dict:
        """Откатить ответ на карточку (мало ли, нажали не ту кнопку): забыть выученное, вернуть выброшенное."""
        now = self.clock() if now is None else now
        L = self._L()
        c = L["cards"].get(card_id)
        if c is None or not c.get("done") or c.get("kind") == "teach":
            return {"ok": False}
        fx = c.pop("fx", None) or {}
        cid, uid = c["cid"], c["uid"]
        book = self._lbook(cid)
        chat = self.store.chat(cid)
        spam = L["g"]["spam"]
        res = {"ok": True, "cid": cid, "unban": [], "cards": c}
        if fx.get("vouch") and chat.users.get(uid) is not None:
            chat.users[uid].vouched = False
        if fx.get("sp"):
            spam.pop(fx["sp"], None)
        if fx.get("spm") and fx["spm"] in spam:
            spam[fx["spm"]]["adm"] = max(1, spam[fx["spm"]].get("adm", 1) - 1)
        if fx.get("hp"):
            book["ham"].pop(fx["hp"], None)
        if fx.get("hpm") and fx["hpm"] in book["ham"]:
            book["ham"][fx["hpm"]]["adm"] = max(1, book["ham"][fx["hpm"]].get("adm", 1) - 1)
        for k, rec in fx.get("rh", ()):
            book["ham"][k] = rec
        for k, rec in fx.get("rs", ()):
            spam[k] = rec
        for t in fx.get("ct", ()):
            for st in self.store.chats.values():
                b = self._spam_book(st.chat_id)
                if b and b.get(t, {}).get("adm"):
                    b.pop(t, None)
        for t, ts in fx.get("okrm", ()):
            book["okc"][t] = ts
        for t in fx.get("okc", ()):
            book["okc"].pop(t, None)
        for cid2, t, e in fx.get("bk", ()):
            b = self._spam_book(cid2, create=True)
            b[t] = e
        w = fx.get("bs")
        if w:
            g = L["g"]
            for h in c["bh"]:
                k = str(h)
                if k in g["bs"]:
                    g["bs"][k] = max(0.0, g["bs"][k] - w)
                    if g["bs"][k] <= 0:
                        g["bs"].pop(k, None)
            g["ns"] = max(0.0, g["ns"] - w)
        w = fx.get("bhw")
        if w:
            for h in c["bh"]:
                k = str(h)
                if k in book["bh"]:
                    book["bh"][k] = max(0.0, book["bh"][k] - w)
                    if book["bh"][k] <= 0:
                        book["bh"].pop(k, None)
            book["nh"] = max(0.0, book["nh"] - w)
        if fx.get("cal"):
            self._cal_sub(book, [(n, 0) for n in fx["cal"]], fx.get("k") == "s")
        rec = chat.users.get(uid)
        if rec is not None and fx.get("strike") and rec.strikes:
            for i in range(len(rec.strikes) - 1, -1, -1):
                if rec.strikes[i][2] == "learn":
                    rec.strikes.pop(i)
                    break
        for u2 in fx.get("sw", ()):
            r2 = chat.users.get(u2)
            if r2 is not None:
                for i in range(len(r2.strikes) - 1, -1, -1):
                    if r2.strikes[i][2] == "learn":
                        r2.strikes.pop(i)
                        break
        for u2 in fx.get("ban", ()):
            r2 = chat.users.get(u2)
            if r2 is not None:
                r2.banned = False
            res["unban"].append(u2)
        self._lcount(cid, {"s": "spam", "h": "ham"}.get(fx.get("k"), "skip"), now, -1)
        c["done"] = None
        self._lsets.clear()
        self.store.dirty = True
        return res

    # ───────── обучение пересылкой: владелец кидает боту в личку спам
    def learn_from_text(self, text: str, ents, by: int, now: float | None = None) -> dict:
        now = self.clock() if now is None else now
        a = analyze_text(text, ents, ChatCfg())
        f = self._lfeat(a)
        if f is None:
            return {"ok": False, "why": "empty"}
        L = self._L()
        out: dict = {"ok": True, "pid": "", "new": False, "contacts": [], "words": len(f["bh"]), "short": False}
        if not (f["sk"] or f["sim"]):
            out["short"] = True
        else:
            pid, new = self._add_pattern(L["g"]["spam"], f, LEARN_SPAM_MAX, now, by, "пересылка", {"ct": list(a.contacts)})
            out["pid"], out["new"] = pid, new
        cts = [t for t in a.contacts if t.lower() not in self.mem_protect]
        if cts:
            self._share_contacts(cts, by, now, "владелец переслал")
            out["contacts"] = cts
        if f["bh"]:
            self._bayes_add_spam(f["bh"], 3.0)
        first = next(iter(self.store.chats), None)
        if first is not None:
            self._lcount(first, "teach", now)
        L["seq"] += 1
        tid = "t" + format(L["seq"], "x")
        L["cards"][tid] = {"cid": 0, "mid": 0, "uid": 0, "t": round(now), "kind": "teach", "sim": 0, "sk": [], "bh": f["bh"],
                           "ct": cts, "sg": [], "own": {}, "dup": 0, "done": {"act": "t", "by": by, "t": round(now)},
                           "pid": out["pid"] if out["new"] else "", "w": 3.0}
        out["id"] = tid
        self.store.dirty = True
        return out

    def learn_undo(self, tid: str) -> bool:
        L = self._L()
        c = L["cards"].get(tid)
        if c is None or c.get("kind") != "teach" or c.get("undone"):
            return False
        c["undone"] = True
        if c.get("pid"):
            L["g"]["spam"].pop(c["pid"], None)
        for cid in self.store.chats:
            b = self._spam_book(cid)
            for t in c["ct"]:
                if b and b.get(t, {}).get("adm"):
                    b.pop(t, None)
        bs = L["g"]["bs"]
        for h in c["bh"]:
            k = str(h)
            if k in bs:
                bs[k] = max(0.0, bs[k] - c["w"])
                if bs[k] <= 0:
                    bs.pop(k, None)
        L["g"]["ns"] = max(0.0, L["g"]["ns"] - c["w"])
        self.store.dirty = True
        return True

    # ───────── ошибки и самоочистка
    def learn_overturn(self, chat_id: int, uid: int, now: float) -> int:
        """Владелец отменил наказание: шаблоны, которые на этого человека сработали, теряют доверие."""
        spam = self._L()["g"]["spam"]
        n = 0
        for i, (ts, cid, u, pid, mid) in enumerate(list(self._lhits)):
            if cid != chat_id or u != uid or now - ts > LEARN_OK_AFTER or pid == "":
                continue
            p = spam.get(pid)
            self._lhits[i] = (ts, cid, u, "", mid)
            if p is None:
                continue
            p["bad"] = p.get("bad", 0) + 1
            n += 1
            self._lcount(chat_id, "over", now)
            if self._trust(p) < 2.0:
                p["soft"] = True
            if self._trust(p) < 0:
                spam.pop(pid, None)
                self._lcount(chat_id, "drop", now)
        if n:
            self.store.dirty = True
        return n

    @staticmethod
    def _trust(p: dict) -> float:
        return LEARN_TRUST_START * min(2, p.get("adm", 1)) + LEARN_TRUST_OK * min(10, p.get("ok", 0)) - LEARN_TRUST_BAD * p.get("bad", 0)

    def learn_gc(self, now: float) -> dict:
        L = self._L()
        g = L["g"]
        out = {"expired": 0, "dropped": 0, "cards": 0, "words": 0}
        keep: deque = deque(maxlen=LEARN_HIT_LOG)
        for h in self._lhits:
            ts, cid, uid, pid, mid = h
            if now - ts >= LEARN_OK_AFTER:
                p = g["spam"].get(pid) if pid else None
                if p is not None:
                    p["ok"] = p.get("ok", 0) + 1
                self._lhit_keys.discard((cid, mid))
            else:
                keep.append(h)
        self._lhits = keep
        for pid in [k for k, p in g["spam"].items() if now - p.get("t", 0) > LEARN_SPAM_TTL]:
            g["spam"].pop(pid, None)
            out["expired"] += 1
        for pid in [k for k, p in g["spam"].items() if self._trust(p) < 0]:
            g["spam"].pop(pid, None)
            out["dropped"] += 1
        dt = max(0.0, now - (g.get("gc_t") or now))
        g["gc_t"] = now
        f = 0.5 ** (dt / LEARN_BAYES_HALF)
        if f < 0.9999:
            for d in [g["bs"]] + [b["bh"] for b in L["c"].values()]:
                for k in list(d):
                    d[k] *= f
                    if d[k] < 0.15:
                        d.pop(k, None)
                        out["words"] += 1
            g["ns"] *= f
            for b in L["c"].values():
                b["nh"] *= f
        for b in L["c"].values():
            for pid in [k for k, p in b["ham"].items() if now - p.get("t", 0) > LEARN_HAM_TTL]:
                b["ham"].pop(pid, None)
                out["expired"] += 1
            for name in [k for k, e in b["cal"].items() if (e[0] + e[1]) * 0.5 ** (max(0.0, now - e[2]) / LEARN_CAL_HALF) < 0.2]:
                b["cal"].pop(name, None)
            for t in [k for k, ts in b["okc"].items() if now - ts > LEARN_OKC_TTL]:
                b["okc"].pop(t, None)
        cards = L["cards"]
        for k in [k for k, c in cards.items() if now - c["t"] > LEARN_CARD_TTL]:
            c = cards.pop(k)
            if not c.get("done") and c.get("kind") != "teach":
                self._lcount(c["cid"], "exp", now)
                out["cards"] += 1
        self._lsets.clear()
        self.store.dirty = True
        return out

    # ───────── отчёты
    def learn_active_today(self, now: float) -> bool:
        day = self.store.day(now)
        return any(b["day"].get(day) for b in self._L()["c"].values())

    def learn_digest_lines(self, chat_id: int, now: float) -> list:
        b = self._lbook(chat_id, create=False)
        d = (b or {}).get("day", {}).get(self.store.day(now)) or {}
        if not d:
            return []
        bits = []
        if d.get("ask"):
            bits.append(f"карточек владельцу: {d['ask']}")
        if d.get("spam") or d.get("ham"):
            bits.append(f"ответов: спам {d.get('spam', 0)}, нормально {d.get('ham', 0)}")
        if d.get("hit"):
            bits.append(f"сработало выученное: {d['hit']}")
        if d.get("over"):
            bits.append(f"отменено вами: {d['over']}")
        return ["🧠 Самообучение: " + "; ".join(bits)] if bits else []

    def learn_precision(self, now: float) -> tuple:
        ok = bad = 0
        for p in self._L()["g"]["spam"].values():
            ok += p.get("ok", 0)
            bad += p.get("bad", 0)
        return ok, bad

    def learn_report(self, now: float) -> str:
        L = self._L()
        day, yday = self.store.day(now), self.store.day(now - 86400)
        tot: dict = {}
        ytot: dict = {}
        cal_lines: list = []
        for cid, b in L["c"].items():
            for k, v in (b["day"].get(day) or {}).items():
                tot[k] = tot.get(k, 0) + v
            for k, v in (b["day"].get(yday) or {}).items():
                ytot[k] = ytot.get(k, 0) + v
            chat = self.store.chats.get(int(cid))
            for name, e in b["cal"].items():
                m = self._cal_mult(b, name, now)
                if abs(m - 1.0) >= 0.1:
                    cal_lines.append((abs(m - 1.0), f"«{name}» в «{esc(chat.title if chat else cid, 24)}» стал {'строже' if m > 1 else 'мягче'} (×{m:.2f})"))
        lines = ["🧠 <b>Чему я научился сегодня</b>"]
        if tot.get("ask") or tot.get("exp") or tot.get("sup"):
            s = f"Карточек: показал {tot.get('ask', 0)}, ответили на {tot.get('spam', 0) + tot.get('ham', 0) + tot.get('skip', 0)}"
            if tot.get("spam") or tot.get("ham"):
                s += f" (спам {tot.get('spam', 0)}, нормально {tot.get('ham', 0)})"
            if tot.get("exp"):
                s += f", без ответа {tot['exp']}"
            if tot.get("sup"):
                s += f"; ещё {tot['sup']} не показал, чтобы не заспамить вас"
            lines.append(s + ".")
        learned = []
        if tot.get("new"):
            learned.append(f"шаблонов спама: {tot['new']}")
        if tot.get("again"):
            learned.append(f"усилил старых: {tot['again']}")
        if tot.get("cont"):
            learned.append(f"контактов: {tot['cont']}")
        if tot.get("teach"):
            learned.append(f"по вашим пересылкам: {tot['teach']}")
        if tot.get("ham"):
            learned.append(f"исключений «нормально»: {tot['ham']}")
        if learned:
            lines.append("Запомнил — " + ", ".join(learned) + ".")
        if tot.get("hit"):
            s = f"Поймал по выученному: {tot['hit']}"
            if tot.get("over"):
                s += f", из них вы отменили {tot['over']}"
            lines.append(s + ".")
        if tot.get("swept"):
            lines.append(f"Сразу убрал похожие сообщения других аккаунтов: {tot['swept']}.")
        if tot.get("drop") or tot.get("exp"):
            lines.append(f"Прибрал за собой: шаблонов убрано {tot.get('drop', 0)}.")
        for _m, s in sorted(cal_lines, reverse=True)[:3]:
            lines.append("Подстроил: " + s + ".")
        slow = [cid for cid in L["c"] if self._learn_limits(int(cid), now)[2]]
        if slow:
            lines.append("Вы почти не отвечаете на карточки, поэтому я спрашиваю реже (до 2 в час). Начнёте отвечать — снова буду чаще.")
        ok, bad = self.learn_precision(now)
        if ok + bad >= 5:
            lines.append(f"Точность выученного за всё время: {round(100 * ok / (ok + bad))}% ({ok} из {ok + bad}).")
        if ytot.get("ask") and tot.get("ask") is not None:
            lines.append(f"Карточек вчера → сегодня: {ytot['ask']} → {tot.get('ask', 0)}"
                         + (" (меньше — значит учусь)" if tot.get("ask", 0) < ytot["ask"] else ""))
        lines.append(f"В памяти: шаблонов спама {len(L['g']['spam'])}, исключений "
                     f"{sum(len(b['ham']) for b in L['c'].values())}. Тексты не хранятся — только отпечатки.")
        return "\n".join(lines)

    def learn_summary(self, chat_id: int) -> str:
        L = self._L()
        b = self._lbook(chat_id, create=False)
        n_spam = len(L["g"]["spam"])
        n_ham = len(b["ham"]) if b else 0
        if not (n_spam or n_ham):
            return ""
        soft = sum(1 for p in L["g"]["spam"].values() if p.get("soft"))
        return (f"🧠 Самообучение: шаблонов спама {n_spam}" + (f" (из них осторожных {soft})" if soft else "")
                + f", исключений «нормально» в этом чате {n_ham}. Тексты не хранятся, только отпечатки.")

    def learn_reset(self, chat_id: int, whole: bool = False) -> int:
        L = self._L()
        n = 0
        b = L["c"].pop(str(chat_id), None)
        if b:
            n += len(b["ham"]) + len(b["cal"]) + len(b["okc"]) + len(b["bh"])
        if whole:
            n += len(L["g"]["spam"]) + len(L["g"]["bs"])
            L["g"]["spam"].clear()
            L["g"]["bs"].clear()
            L["g"]["ns"] = 0.0
        for k in [k for k, c in L["cards"].items() if c["cid"] == chat_id and not c.get("done")]:
            L["cards"].pop(k, None)
        self._lsets.clear()
        self.store.dirty = True
        return n

    def learn_probe(self, text: str, chat_id: int, a: "Analysis | None" = None) -> list:
        """Для /explain: что сказало бы самообучение об этом тексте."""
        a = a or analyze_text(text, (), ChatCfg())
        f = self._lfeat(a)
        out: list = []
        if f is None:
            return out
        spam = self._L()["g"]["spam"]
        pid, lvl, s, d = self._lmatch(spam, f) if spam else ("", 0, 0.0, 99)
        if lvl:
            out.append(f"похоже на выученный спам-шаблон #{pid} (уровень {lvl}, сходство {int(100 * s)}%, simhash-расстояние {d if d < 99 else '—'})")
        book = self._lbook(chat_id, create=False)
        if book and book["ham"]:
            hid, hl, hs, hd = self._lmatch(book["ham"], f)
            if hl:
                out.append(f"похоже на исключение «нормально» #{hid} (уровень {hl})")
        w = self._bayes_w(book, f)
        if w:
            out.append(f"слова-маркеры: +{w:g}")
        return out


# ══════════════════════════════════════════════════════════════════════════════════════
#  САМООБУЧЕНИЕ+ (4.3). Только добавки к LearnCore: больше уроков прямо из Telegram (реакции, /spam, баны владельца),
#  короткие фразы, «меченые» авторы, осторожное автообучение на волнах, поправки после отмены наказаний.
#  Все новые сигналы мягкие (не в HARD_SIGNALS) и сами ничего не удаляют; тексты по-прежнему не сохраняются.
#  GUARD_LEARN_PLUS=0 выключает всё это, GUARD_LEARN_AUTO=0 — только автообучение.
# ══════════════════════════════════════════════════════════════════════════════════════
LP_CACHE_TOTAL, LP_CACHE_TTL = 3000, 6 * 3600
LP_LESSON_KEEP = 40
LP_TEACH_LIMIT = 12
LP_SHORT_MAX = 5
LP_SS_MAX, LP_SS_TTL = 300, 45 * 86400
LP_HS_MAX = 150
LP_AU_MAX, LP_AU_TTL = 400, 14 * 86400
LP_AUTO_MAX, LP_AUTO_TTL = 150, 5 * 86400
LP_W_SHORT, LP_W_SHORT2, LP_W_AUTHOR, LP_W_AUTHOR2, LP_W_AUTO = 2.4, 3.0, 1.8, 2.4, 2.0
LP_AUTO_HARD = 3.5
LP_IMPL_WINDOW = 1800
LP_REACT_SPAM = frozenset("👎💩🤮🤡")
LP_REACT_BAN = frozenset("🤬")
LP_REACT_OK = frozenset("👍❤🔥🥰👏🙏👌🎉💯😍")


def _lp_flag(name: str, default: bool = True) -> bool:
    v = os.environ.get(name)
    if v is None or str(v).strip() == "":
        return default
    return str(v).strip().lower() not in ("0", "false", "no", "off", "нет", "выкл")


def lp_short_key(stems: list) -> str:
    """Отпечаток короткой фразы (2–5 основ, порядок не важен); у длинных текстов есть обычный шаблон, тут пусто."""
    if not (2 <= len(stems) <= LP_SHORT_MAX):
        return ""
    ws = sorted(set(stems))
    if len(ws) < 2 or sum(len(w) for w in ws) < 7:
        return ""
    return format(_h32(" ".join(ws)), "x")


class LearnPlus:

    def init_learn(self) -> None:
        super().init_learn()
        self.lp_on = _lp_flag("GUARD_LEARN_PLUS", True)
        self.lp_auto_on = _lp_flag("GUARD_LEARN_AUTO", True)
        self._lpc: OrderedDict = OrderedDict()
        self._lpu: dict = {}
        self._lp_acts: deque = deque(maxlen=300)
        self._lp_ahits: deque = deque(maxlen=300)
        self._lp_tlog: dict = {}

    def _lpg(self) -> dict:
        g = self._L()["g"]
        g.setdefault("ss", {})
        g.setdefault("au", {})
        g.setdefault("auto", {})
        g.setdefault("rxm", {})
        return g

    def lp_rxmode(self, uid: int) -> str:
        """Что делать с реакциями владельца: ask — спросить в личке (по умолчанию), auto — учиться сразу, off — реакции ничего не значат."""
        m = self._lpg()["rxm"].get(str(uid), "ask")
        return m if m in ("ask", "auto", "off") else "ask"

    def lp_set_rxmode(self, uid: int, mode: str) -> None:
        if mode == "ask":
            self._lpg()["rxm"].pop(str(uid), None)
        elif mode in ("auto", "off"):
            self._lpg()["rxm"][str(uid)] = mode
        self.store.dirty = True

    @staticmethod
    def _lp_trim(d: dict, cap: int, key=lambda v: v[0] if isinstance(v, list) else v) -> None:
        if len(d) > cap:
            for k in sorted(d, key=lambda k: key(d[k]))[:len(d) - cap]:
                d.pop(k, None)

    # ───────── кэш отпечатков недавних сообщений (только в памяти, нужен, чтобы учить по реакции/команде)
    def _lp_put(self, cid: int, mid: int, uid: int, ent: dict) -> None:
        k = (cid, mid)
        old = self._lpc.get(k)
        if old and old.get("lesson"):
            ent["lesson"] = old["lesson"]
        self._lpc[k] = ent
        self._lpc.move_to_end(k)
        dq = self._lpu.setdefault((cid, uid), deque(maxlen=8))
        if mid not in dq:
            dq.append(mid)
        while len(self._lpc) > LP_CACHE_TOTAL:
            self._lpc.popitem(last=False)
        if len(self._lpu) > 6000:
            self._lp_prune(ent["t"])

    def _lp_prune(self, now: float) -> None:
        for k in [k for k, e in self._lpc.items() if now - e["t"] > LP_CACHE_TTL]:
            self._lpc.pop(k, None)
        for k in [k for k, dq in self._lpu.items() if not any((k[0], m) in self._lpc for m in dq)]:
            self._lpu.pop(k, None)
        while self._lp_acts and now - self._lp_acts[0][0] > LEARN_OK_AFTER:
            self._lp_acts.popleft()
        while self._lp_ahits and now - self._lp_ahits[0][0] > LEARN_OK_AFTER:
            self._lp_ahits.popleft()

    def _learn_post(self, msg: "Msg", v: "Verdict", la: tuple, now: float) -> None:
        super()._learn_post(msg, v, la, now)
        try:
            self._lp_post(msg, v, la, now)
        except Exception:
            log_learn.exception("самообучение+: сбой (модерация не затронута)")

    def _lp_post(self, msg: "Msg", v: "Verdict", la: tuple, now: float) -> None:
        ana, tier, strict, chat, rec = la
        cfg = chat.cfg
        if not (self.lp_on and self.learn_on and cfg.learn and cfg.scam) or ana.lf is None:
            return
        f = ana.lf
        cid = msg.chat_id
        sg = [[n, round(w, 2)] for n, w, _ in ana.signals if w > 0 and n not in HARD_SIGNALS and not n.startswith("learned")][:8]
        top3 = sorted(ana.signals, key=lambda s: -s[1])[:3]
        short = lp_short_key(f["st"]) if not f["sk"] else ""
        self._lp_put(cid, msg.msg_id, msg.user_id, {
            "t": now, "uid": msg.user_id, "f": {"sk": f["sk"], "sim": f["sim"], "bh": f["bh"], "nt": f["nt"], "sh": short},
            "raw": ana.raw, "ct": list(ana.contacts)[:6], "urls": bool(ana.urls), "tier": tier, "eff": v.score,
            "alive": not (v.delete or v.ban), "sg": sg, "snip": msg.text.strip()[:220], "name": msg.name,
            "why": "; ".join(s[2] for s in top3 if s[1] > 0)[:200], "lesson": ""})
        if v.delete and v.category in ("scam", "suspicious", "memory") and sg and not msg.edited:
            self._lp_acts.append((now, cid, msg.user_id, [s[0] for s in sg]))
        if not (self.lp_auto_on and (v.delete or v.ban) and v.category in ("scam", "scam_ban") and v.score >= STRONG_SCAM
                and tier == "new" and ana.hard >= LP_AUTO_HARD and not msg.edited and (f["sk"] or f["sim"])
                and not ana.lhit.startswith("ham")):
            return
        book = self._lbook(cid, create=False)
        if book and book["ham"] and self._lmatch(book["ham"], f)[1] >= 2:
            return
        if self._collateral(cid, f["sim"], msg.user_id, now):
            return
        pid, new = self._add_pattern(self._lpg()["auto"], f, LP_AUTO_MAX, now, 0, "авто")
        if pid and new:
            self._lcount(cid, "auto", now)

    # ───────── мягкие сигналы при проверке
    def _learn_signals(self, msg: "Msg", chat: "ChatState", a: "Analysis", tier: str, now: float) -> None:
        super()._learn_signals(msg, chat, a, tier, now)
        if not (self.lp_on and self.learn_on and chat.cfg.learn and chat.cfg.scam) or a.lf is None or tier != "new":
            return
        if a.lhit.startswith("ham") or a.lhit.startswith("spam:"):
            return
        try:
            self._lp_signals(msg, chat, a, now)
        except Exception:
            log_learn.exception("самообучение+: сигналы не посчитаны (модерация не затронута)")

    def _lp_signals(self, msg: "Msg", chat: "ChatState", a: "Analysis", now: float) -> None:
        f, sig, cid = a.lf, a.signals, msg.chat_id
        g = self._lpg()
        book = self._lbook(cid, create=False)
        base = sum(w for n, w, _ in sig if w > 0 and n not in HARD_SIGNALS and not n.startswith("learned_author"))
        ok = base >= 0.5 or a.has_contact
        if not f["sk"] and ok:
            key = lp_short_key(f["st"])
            e = g["ss"].get(key) if key else None
            if e and now - e[0] <= LP_SS_TTL and not (book and key in book.get("hs", {})):
                sig.append(("learned_short", LP_W_SHORT if e[1] < 2 else LP_W_SHORT2, "такая короткая фраза уже была спамом по вашим отметкам"))
                a.lhit = "short:" + key[:6]
                self._lcount(cid, "shit", now)
                return
        au = g["au"].get(str(msg.user_id))
        if au and ok and now - au[0] <= LP_AU_TTL:
            sig.append(("learned_author", LP_W_AUTHOR if au[1] < 2 else LP_W_AUTHOR2, "этого автора вы уже отмечали как спамера"))
        auto = g["auto"]
        if auto and ok and (f["sk"] or f["sim"]):
            pid, lvl, s, d = self._lmatch(auto, f)
            if lvl >= 2:
                p = auto[pid]
                w = min(3.0, LP_W_AUTO + 0.6 * min(1, p.get("adm", 1) - 1))
                pct = int(round(100 * max(s, 1.0 - d / 64.0)))
                sig.append(("learned_auto", w, f"похоже на спам, пойманный ранее на волне ({pct}%)"))
                p["n"] = p.get("n", 0) + 1
                p["t"] = round(now)
                self._lp_ahits.append((now, cid, msg.user_id, pid))
                self._lcount(cid, "ahit", now)

    # ───────── уроки по сообщению (реакция, /spam, бан владельца)
    def lp_entry_from_text(self, cid: int, mid: int, uid: int, text: str, ents, now: float, tier: str) -> dict | None:
        a = analyze_text(text, ents, ChatCfg())
        f = self._lfeat(a)
        if f is None:
            return None
        ent = {"t": now, "uid": uid, "f": {"sk": f["sk"], "sim": f["sim"], "bh": f["bh"], "nt": f["nt"],
                                          "sh": lp_short_key(f["st"]) if not f["sk"] else ""},
               "raw": a.raw, "ct": list(a.contacts)[:6], "urls": bool(a.urls), "tier": tier, "eff": round(a.raw, 2),
               "alive": True, "sg": [], "snip": text.strip()[:220], "name": "", "why": "отмечено вручную", "lesson": ""}
        self._lp_put(cid, mid, uid, ent)
        return ent

    def lp_teach(self, cid: int, mid: int, act: str, by: int, src: str, now: float | None = None, kind: str = "") -> dict:
        now = self.clock() if now is None else now
        if not (self.lp_on and self.learn_on):
            return {"ok": False, "why": "off"}
        ent = self._lpc.get((cid, mid))
        if ent is None:
            return {"ok": False, "why": "nocache"}
        rl = self._lp_tlog.setdefault(by, deque(maxlen=40))
        while rl and now - rl[0] > 600:
            rl.popleft()
        if len(rl) >= LP_TEACH_LIMIT:
            return {"ok": False, "why": "limit"}
        cards = self._L()["cards"]
        card_id = next((k for k, c in cards.items() if c["cid"] == cid and c["mid"] == mid and not c.get("done")
                        and c.get("kind") != "teach"), "")
        if not card_id:
            if act == "h":
                return {"ok": False, "why": "noopen"}
            old = cards.get(ent.get("lesson") or "")
            if old is not None and old.get("done"):
                return {"ok": False, "why": "dup"}
            f = ent["f"]
            if not (f["sk"] or f["sim"] or ent["ct"] or len(f["bh"]) >= 3):
                return {"ok": False, "why": "empty"}
            L = self._L()
            L["seq"] += 1
            card_id = format(L["seq"], "x")
            cards[card_id] = {"cid": cid, "mid": mid, "uid": ent["uid"], "t": round(now), "tier": ent["tier"],
                              "eff": round(ent["eff"], 2), "kind": kind or ("keep" if ent["alive"] else "del"),
                              "sim": f["sim"], "sk": f["sk"], "bh": f["bh"], "ct": list(ent["ct"]), "sg": [list(x) for x in ent["sg"]],
                              "own": {}, "dup": 0, "why": ent["why"], "src": src, "sh": f.get("sh", "")}
            mine = sorted((k for k, c in cards.items() if c.get("src") and c.get("done")), key=lambda k: cards[k]["t"])
            for k in mine[:max(0, len(mine) - LP_LESSON_KEEP)]:
                cards.pop(k, None)
        res = self.learn_decide(card_id, act, by, now)
        if not res.get("ok"):
            return res
        ent["lesson"] = card_id
        rl.append(now)
        res["card_id"] = card_id
        self._lcount(cid, "src_" + src, now)
        return res

    def lp_implicit(self, cid: int, uid: int, by: int, src: str, now: float) -> dict:
        """Владелец сам забанил человека: его самое «спамное» недавнее сообщение становится уроком."""
        best = None
        for mid in reversed(list(self._lpu.get((cid, uid), ()))):
            e = self._lpc.get((cid, mid))
            if not e or e.get("lesson") or now - e["t"] > LP_IMPL_WINDOW or e["tier"] != "new":
                continue
            if not (e["raw"] >= 1.0 or e["ct"] or e["urls"]) or not (e["f"]["sk"] or e["f"]["sim"] or e["ct"]):
                continue
            key = (bool(e["ct"]), e["raw"])
            if best is None or key > best[0]:
                best = (key, mid)
        if best is None:
            return {"ok": False, "why": "none"}
        return self.lp_teach(cid, best[1], "s", by, src, now, kind="del")

    def learn_decide(self, card_id: str, act: str, by: int, now: float | None = None) -> dict:
        res = super().learn_decide(card_id, act, by, now)
        if res.get("ok") and self.lp_on:
            try:
                self._lp_after_decide(res["cards"], act, self.clock() if now is None else now)
            except Exception:
                log_learn.exception("самообучение+: добавки к ответу не применились")
        return res

    def _lp_after_decide(self, c: dict, act: str, now: float) -> None:
        cid, uid, sh = c["cid"], c["uid"], c.get("sh") or ""
        g, book = self._lpg(), self._lbook(cid)
        x = c["lpx"] = {}
        hs = book.setdefault("hs", {})
        if act in ("s", "sb"):
            if c.get("tier") == "new" and uid > 0:
                old = g["au"].get(str(uid))
                x["au"] = [str(uid), old]
                g["au"][str(uid)] = [round(now), (old[1] if old else 0) + 1]
                self._lp_trim(g["au"], LP_AU_MAX)
                self._lcount(cid, "auth", now)
            if sh:
                old = g["ss"].get(sh)
                x["ss"] = [sh, old]
                g["ss"][sh] = [round(now), (old[1] if old else 0) + 1]
                self._lp_trim(g["ss"], LP_SS_MAX)
                if sh in hs:
                    x["hsrm"] = [sh, hs.pop(sh)]
        elif act == "h":
            if sh:
                x["hs"] = [sh, hs.get(sh)]
                hs[sh] = round(now)
                self._lp_trim(hs, LP_HS_MAX)
                if sh in g["ss"]:
                    x["ssrm"] = [sh, g["ss"].pop(sh)]
            if str(uid) in g["au"]:
                x["aurm"] = [str(uid), g["au"].pop(str(uid))]
        self.store.dirty = True

    def learn_undo_card(self, card_id: str, by: int, now: float | None = None) -> dict:
        c = self._L()["cards"].get(card_id)
        x = c.get("lpx") if (c and c.get("done")) else None
        res = super().learn_undo_card(card_id, by, now)
        if res.get("ok") and x:
            try:
                g, book = self._lpg(), self._lbook(c["cid"])
                hs = book.setdefault("hs", {})
                for key, d in (("au", g["au"]), ("ss", g["ss"]), ("hs", hs)):
                    if key in x:
                        k, old = x[key]
                        if old is None:
                            d.pop(k, None)
                        else:
                            d[k] = old
                for key, d in (("hsrm", hs), ("ssrm", g["ss"]), ("aurm", g["au"])):
                    if key in x:
                        d[x[key][0]] = x[key][1]
            except Exception:
                log_learn.exception("самообучение+: откат добавок не удался")
            c.pop("lpx", None)
            ent = self._lpc.get((c["cid"], c["mid"]))
            if ent is not None:
                ent["lesson"] = ""
        return res

    def _learn_card_for(self, msg: "Msg", v: "Verdict", ana: "Analysis", tier: str, strict: bool, now: float) -> str:
        cid = super()._learn_card_for(msg, v, ana, tier, strict, now)
        if cid:
            c = self._L()["cards"].get(cid)
            if c is not None and ana.lf is not None and not ana.lf["sk"]:
                c["sh"] = lp_short_key(ana.lf["st"])
        return cid

    def learn_from_text(self, text: str, ents, by: int, now: float | None = None) -> dict:
        out = super().learn_from_text(text, ents, by, now)
        if out.get("ok") and out.get("short") and self.lp_on:
            try:
                f = self._lfeat(analyze_text(text, ents, ChatCfg()))
                key = lp_short_key(f["st"]) if f else ""
                if key:
                    g = self._lpg()
                    old = g["ss"].get(key)
                    g["ss"][key] = [round(self.clock() if now is None else now), (old[1] if old else 0) + 1]
                    self._lp_trim(g["ss"], LP_SS_MAX)
                    c = self._L()["cards"].get(out["id"])
                    if c is not None:
                        c["lpss"] = [key, old]
                    out["phrase"] = True
            except Exception:
                log_learn.exception("самообучение+: короткая фраза не запомнилась")
        return out

    def learn_undo(self, tid: str) -> bool:
        c = self._L()["cards"].get(tid)
        x = c.get("lpss") if c else None
        ok = super().learn_undo(tid)
        if ok and x:
            d = self._lpg()["ss"]
            if x[1] is None:
                d.pop(x[0], None)
            else:
                d[x[0]] = x[1]
        return ok

    def learn_overturn(self, chat_id: int, uid: int, now: float) -> int:
        n = super().learn_overturn(chat_id, uid, now)
        try:
            auto = self._lpg()["auto"]
            for h in list(self._lp_ahits):
                if h[1] == chat_id and h[2] == uid and now - h[0] <= LEARN_OK_AFTER:
                    self._lp_ahits.remove(h)
                    if auto.pop(h[3], None) is not None:
                        self._lcount(chat_id, "drop", now)
            for a in list(self._lp_acts):
                if a[1] == chat_id and a[2] == uid and now - a[0] <= LEARN_OK_AFTER:
                    self._lp_acts.remove(a)
                    self._cal_add(self._lbook(chat_id), [(x, 0) for x in a[3]], False, now)
                    self._lcount(chat_id, "calham", now)
            self._lpg()["au"].pop(str(uid), None)
            self.store.dirty = True
        except Exception:
            log_learn.exception("самообучение+: учёт отмены не удался")
        return n

    # ───────── уборка, сброс, отчёты
    def learn_gc(self, now: float) -> dict:
        out = super().learn_gc(now)
        g = self._lpg()
        for d, ttl in ((g["ss"], LP_SS_TTL), (g["au"], LP_AU_TTL)):
            for k in [k for k, v in d.items() if now - v[0] > ttl]:
                d.pop(k, None)
                out["expired"] += 1
        for k in [k for k, p in g["auto"].items() if now - p.get("t", 0) > LP_AUTO_TTL]:
            g["auto"].pop(k, None)
            out["expired"] += 1
        for b in self._L()["c"].values():
            hs = b.get("hs")
            if hs:
                for k in [k for k, ts in hs.items() if now - ts > LEARN_HAM_TTL]:
                    hs.pop(k, None)
        self._lp_prune(now)
        return out

    def learn_reset(self, chat_id: int, whole: bool = False) -> int:
        n = super().learn_reset(chat_id, whole)
        for k in [k for k in self._lpc if k[0] == chat_id]:
            self._lpc.pop(k, None)
        if whole:
            g = self._lpg()
            n += len(g["ss"]) + len(g["au"]) + len(g["auto"])
            g["ss"].clear()
            g["au"].clear()
            g["auto"].clear()
        return n

    def _lp_totals(self, chat_id: int | None, now: float, days: int = 1) -> dict:
        tot: dict = {}
        for cid, b in self._L()["c"].items():
            if chat_id is not None and cid != str(chat_id):
                continue
            for i in range(days):
                for k, v in (b["day"].get(self.store.day(now - i * 86400)) or {}).items():
                    tot[k] = tot.get(k, 0) + v
        return tot

    def lp_lines(self, tot: dict) -> list:
        src = [(tot.get("src_react"), "реакциями"), (tot.get("src_cmd"), "командой /spam"),
               (tot.get("src_ban"), "вашими банами"), (tot.get("src_uiban"), "банами из меню Telegram")]
        bits = [f"{lbl} {n}" for n, lbl in src if n]
        lines = []
        if bits:
            lines.append("Уроков без карточек: " + ", ".join(bits) + ".")
        extra = []
        if tot.get("auto"):
            extra.append(f"автошаблонов с волн: {tot['auto']}")
        if tot.get("ahit"):
            extra.append(f"сработало автообучение: {tot['ahit']}")
        if tot.get("shit"):
            extra.append(f"короткие фразы: {tot['shit']}")
        if tot.get("auth"):
            extra.append(f"отмечено авторов: {tot['auth']}")
        if tot.get("calham"):
            extra.append(f"смягчено правил после ваших отмен: {tot['calham']}")
        if extra:
            lines.append("Ещё: " + ", ".join(extra) + ".")
        return lines

    def learn_report(self, now: float) -> str:
        base = super().learn_report(now)
        try:
            lines = self.lp_lines(self._lp_totals(None, now))
            if lines:
                parts = base.split("\n")
                return "\n".join(parts[:-1] + lines + parts[-1:])
        except Exception:
            log_learn.exception("самообучение+: строки справки не получились")
        return base

    def learn_digest_lines(self, chat_id: int, now: float) -> list:
        out = super().learn_digest_lines(chat_id, now)
        try:
            out = out + self.lp_lines(self._lp_totals(chat_id, now))
        except Exception:
            pass
        return out

    def learn_probe(self, text: str, chat_id: int, a: "Analysis | None" = None) -> list:
        out = super().learn_probe(text, chat_id, a)
        try:
            a = a or analyze_text(text, (), ChatCfg())
            f = self._lfeat(a)
            if f is not None:
                g = self._lpg()
                key = lp_short_key(f["st"]) if not f["sk"] else ""
                if key and key in g["ss"]:
                    out.append("короткая фраза, которую вы отмечали как спам")
                if g["auto"] and (f["sk"] or f["sim"]):
                    pid, lvl, s, d = self._lmatch(g["auto"], f)
                    if lvl >= 2:
                        out.append(f"похоже на автошаблон волны #{pid} (уровень {lvl})")
        except Exception:
            pass
        return out

    def lp_status(self, chat_id: int | None, now: float, uid: int = 0) -> str:
        L, g = self._L(), self._lpg()
        b = self._lbook(chat_id, create=False) if chat_id else None
        ok, bad = self.learn_precision(now)
        w = self._lp_totals(chat_id, now, 7)
        lines = ["🧠 <b>Самообучение</b> (4.3)" + ("" if self.lp_on else " — расширения выключены"),
                 f"Шаблонов спама: {len(L['g']['spam'])} · автошаблонов с волн: {len(g['auto'])} · коротких фраз: {len(g['ss'])} · "
                 f"отмеченных авторов: {len(g['au'])}" + (f" · исключений в этом чате: {len(b['ham'])}" if b else "")]
        if ok + bad >= 5:
            lines.append(f"Точность выученного: {round(100 * ok / (ok + bad))}% ({ok} из {ok + bad}).")
        asked, ans = w.get("ask", 0), w.get("spam", 0) + w.get("ham", 0) + w.get("skip", 0)
        direct = sum(w.get(k, 0) for k in ("src_react", "src_cmd", "src_ban", "src_uiban"))
        lines.append(f"За 7 дней: карточек {asked} (ответов {ans}), уроков прямо из чата {direct}, поймано выученным {w.get('hit', 0)}.")
        rx = {"ask": "спрашиваю в личке, учить ли", "auto": "учусь сразу, без вопросов", "off": "ничего не значат"}[self.lp_rxmode(uid)]
        lines.append("<b>Как меня учить</b>\n• реакция 👎 💩 🤡 🤮 на сообщение в чате (🤬 — с баном новичка): сейчас " + rx +
                     " (/learn react ask | auto | off); 👍 на сообщение с открытой карточкой — «нормально»\n• ответом на спам: /spam или /spam ban\n"
                     "• обычный /ban или бан из меню Telegram: выучу самое «спамное» сообщение забаненного\n"
                     "• пересланный мне в личку спам — выучу сразу\nНа каждый урок приходит сообщение с кнопкой «Это ошибка, отменить».")
        return "\n".join(lines)


class Engine(FortCore, TraceCore, ApCore, LearnPlus, LearnCore):
    def __init__(self, store: Store, clock=time.time, rng: random.Random | None = None):
        self.store = store
        self.clock = clock
        self.rng = rng or random.Random()
        self.rings = RingBook()
        self.recent: dict[int, deque] = {}
        self.glob: deque = deque(maxlen=3000)
        self._gidx: dict = {}
        self._gseq = 0
        self.doms: dict[int, deque] = {}
        self.cnet: dict[str, deque] = {}
        self.ut: dict[tuple, deque] = {}
        self.joins: dict[int, deque] = {}
        self.raid_until: dict[int, float] = {}
        self.raid_notified: set[int] = set()
        self.ring_noise: dict[tuple, deque] = {}
        self.last_msg: dict[tuple, float] = {}
        self.ids: dict[tuple, deque] = {}
        self.tribune_last: dict[tuple, float] = {}
        self.strict_counts: dict[int, dict] = {}
        self.spam_hits: dict[int, deque] = {}
        self.strict_default_min = STRICT_DEFAULT_MIN
        self.strict_auto_on = True
        self.strict_auto_users = STRICT_AUTO_USERS
        self.strict_auto_window = STRICT_AUTO_WINDOW
        self.beats: dict[int, dict[int, Beat]] = {}
        self.scenes: dict[int, dict[int, list]] = {}
        self.busted: dict[int, dict[int, float]] = {}
        self.puppet_on = True
        self.memory_on = True
        self.mem_protect: set = set()
        self.conflicts_on = True
        self.jitter_on = True
        self.talk: dict[int, deque] = {}
        self.baits: dict[int, deque] = {}
        self.prov_hist: dict[tuple, dict] = {}
        self._prov_warned: dict[tuple, float] = {}
        self._dog_last: dict[tuple, float] = {}
        self.events: list = []
        self.init_fort()
        self.init_trace()
        self.init_ap()
        self.init_learn()

    def strike_level(self, rec: UserRec, now: float) -> float:
        lvl, keep = 0.0, []
        for ts, w, why in rec.strikes:
            eff = w * 0.5 ** (max(0.0, now - ts) / HALF_LIFE)
            if eff >= 0.05:
                keep.append([ts, w, why])
                lvl += eff
        if len(keep) != len(rec.strikes):
            rec.strikes = keep[-STRIKE_KEEP:]
        return lvl

    def trust_points(self, rec: UserRec, now: float) -> float:
        base = rec.joined or rec.first_seen or now
        days = max(0.0, (now - base) / 86400)
        # «кредит чистых сообщений» не может обгонять возраст аккаунта в чате: иначе тихая накачка
        # доверия (сообщение раз в 30 с) за ~12 минут делает бота-новичка «участником». У тех, кто
        # в чате давно (≥ 3 дней), потолок выше 40 и ничего не меняется.
        clean_pts = min(40.0, rec.clean * 0.8, TRUST_FARM_BASE + days * TRUST_FARM_PER_DAY)
        pts = min(40.0, days * 4) + clean_pts + (10.0 if rec.verified else 0.0)
        return pts - 15.0 * self.strike_level(rec, now)

    def tier(self, rec: UserRec, now: float) -> str:
        if rec.vouched:
            return "veteran"
        if rec.banned:
            return "new"
        p = self.trust_points(rec, now)
        return "veteran" if p >= 60 else "member" if p >= 20 else "new"

    def add_strike(self, chat_id: int, uid: int, weight: float, why: str, now: float | None = None) -> tuple[float, int]:
        now = self.clock() if now is None else now
        chat = self.store.chat(chat_id)
        rec = self.store.user(chat, uid, now)
        rec.strikes.append([now, float(weight), why])
        rec.strikes = rec.strikes[-STRIKE_KEEP:]
        level = self.strike_level(rec, now)
        mute = next(m for lim, m in LADDER if level < lim)
        if mute:
            rec.muted_until = max(rec.muted_until, now + mute)
        self.store.dirty = True
        return level, mute

    def forgive(self, chat_id: int, uid: int) -> None:
        chat = self.store.chat(chat_id)
        rec = self.store.user(chat, uid)
        rec.strikes, rec.watch, rec.muted_until, rec.banned = [], [], 0.0, False
        self.spam_memory_drop_user(chat_id, uid)
        self.note_overturn(chat_id, uid)
        self.store.dirty = True

    def ring_start(self, chat_id: int, key: str, mode: str, fighters=(), names=(), ttl: float = RING_TTL_DEFAULT,
                   now: float | None = None) -> Ring:
        now = self.clock() if now is None else now
        ttl = max(30.0, min(float(ttl), 7200.0))
        r = self.rings.start(Ring(key=key, chat_id=chat_id, mode=mode, fighters=tuple(int(f) for f in fighters),
                                  names=tuple(names), started=now, expires=now + ttl))
        self.store.rings = self.rings.dump()
        self.store.dirty = True
        return r

    def ring_end(self, key: str) -> Ring | None:
        r = self.rings.end(key)
        self.store.rings = self.rings.dump()
        self.store.dirty = True
        return r

    def ring_end_chat(self, chat_id: int, modes: tuple | None = None) -> list:
        gone = self.rings.end_chat(chat_id, modes)
        if gone:
            self.store.rings = self.rings.dump()
            self.store.dirty = True
        return gone

    def ring_expire(self, now: float | None = None) -> list:
        now = self.clock() if now is None else now
        gone = self.rings.pop_expired(now)
        if gone:
            self.store.rings = self.rings.dump()
            self.store.dirty = True
        return gone

    def ring_touch(self, key: str, ttl: float = RING_TTL_DEFAULT, now: float | None = None) -> bool:
        now = self.clock() if now is None else now
        ok = self.rings.touch(key, max(30.0, min(float(ttl), 7200.0)), now)
        if ok:
            self.store.rings = self.rings.dump()
            self.store.dirty = True
        return ok

    def note_join(self, chat_id: int, now: float | None = None) -> str:
        now = self.clock() if now is None else now
        cfg = self.store.chat(chat_id).cfg
        dq = self.joins.setdefault(chat_id, deque(maxlen=80))
        dq.append(now)
        n = sum(1 for t in dq if now - t <= RAID_WINDOW)
        if cfg.raid and n >= RAID_JOINS:
            was = self.raid_until.get(chat_id, 0) > now
            self.raid_until[chat_id] = now + RAID_HOLD
            self.raid_notified.discard(chat_id)
            return "raid_extend" if was else "raid_on"
        return ""

    def raid_active(self, chat_id: int, now: float | None = None) -> bool:
        now = self.clock() if now is None else now
        return self.raid_until.get(chat_id, 0) > now

    def raid_set(self, chat_id: int, on: bool, now: float | None = None) -> None:
        now = self.clock() if now is None else now
        if on:
            self.raid_until[chat_id] = now + RAID_HOLD
            self.raid_notified.discard(chat_id)
        else:
            self.raid_until.pop(chat_id, None)

    def pop_raid_ended(self, now: float | None = None) -> list[int]:
        now = self.clock() if now is None else now
        ended = [c for c, t in self.raid_until.items() if t <= now]
        for c in ended:
            self.raid_until.pop(c, None)
        return ended

    def strict_active(self, chat_id: int, now: float | None = None) -> bool:
        now = self.clock() if now is None else now
        st = self.store.chats.get(chat_id)
        return bool(st and (st.cfg.strict_until > now or st.cfg.fort_on))

    def strict_left(self, chat_id: int, now: float | None = None) -> float:
        now = self.clock() if now is None else now
        st = self.store.chats.get(chat_id)
        return max(0.0, st.cfg.strict_until - now) if st else 0.0

    def strict_set(self, chat_id: int, seconds: float, now: float | None = None) -> float:
        now = self.clock() if now is None else now
        cfg = self.store.chat(chat_id).cfg
        if seconds and seconds > 0:
            seconds = max(STRICT_MIN_MIN * 60.0, min(float(seconds), STRICT_MAX_MIN * 60.0))
            if cfg.strict_until <= now:
                cfg.strict_started = now
                self.strict_counts[chat_id] = {"del": 0, "ban": 0, "mute": 0}
            cfg.strict_until = now + seconds
        else:
            cfg.strict_until = 0.0
        self.store.dirty = True
        return cfg.strict_until

    def strict_count(self, chat_id: int, key: str, n: int = 1) -> None:
        c = self.strict_counts.setdefault(chat_id, {"del": 0, "ban": 0, "mute": 0})
        c[key] = c.get(key, 0) + n
        st = self.store.chats.get(chat_id)
        if st is not None and st.cfg.fort_on:
            self.fort_count(chat_id, key, n)

    def pop_strict_ended(self, now: float | None = None) -> list:
        now = self.clock() if now is None else now
        done = []
        for cid, st in self.store.chats.items():
            cfg = st.cfg
            if cfg.strict_until and cfg.strict_until <= now:
                done.append((cid, cfg.strict_started, self.strict_counts.pop(cid, {})))
                cfg.strict_until = cfg.strict_started = 0.0
                self.store.dirty = True
        return done

    def _spam_hit(self, chat: ChatState, uid: int, now: float) -> int:
        cfg = chat.cfg
        dq = self.spam_hits.setdefault(chat.chat_id, deque(maxlen=40))
        dq.append((now, uid))
        if not (self.strict_auto_on and cfg.strict_auto and cfg.enabled) or cfg.strict_until > now or cfg.fort_on:
            return 0
        need = self.strict_auto_users
        if self.raid_active(chat.chat_id, now):
            need = max(2, need - 1)
        if len({u for ts, u in dq if now - ts <= self.strict_auto_window}) < need:
            return 0
        dq.clear()
        secs = int(self.strict_default_min * 60)
        self.strict_set(chat.chat_id, secs, now)
        return secs

    def _track_ids(self, msg: Msg, now: float) -> None:
        dq = self.ids.setdefault((msg.chat_id, msg.user_id), deque(maxlen=60))
        dq.append((now, msg.msg_id))

    def recent_ids(self, chat_id: int, uid: int, within: float = 1800.0, now: float | None = None) -> list[int]:
        now = self.clock() if now is None else now
        return [mid for ts, mid in self.ids.get((chat_id, uid), ()) if now - ts <= within]

    def prune(self, now: float | None = None) -> None:
        now = self.clock() if now is None else now
        for d in (self.ut, self.ids):
            for k in [k for k, dq in d.items() if not dq or now - dq[-1][0] > 3600]:
                d.pop(k, None)
        for k in [k for k, dq in self.ring_noise.items() if not dq or now - dq[-1] > 600]:
            self.ring_noise.pop(k, None)
        for k in [k for k, t in self.last_msg.items() if now - t > 3600]:
            self.last_msg.pop(k, None)
        for k in [k for k, t in self.tribune_last.items() if now - t > 3600]:
            self.tribune_last.pop(k, None)
        for c, dq in list(self.recent.items()):
            while dq and now - dq[0][0] > 900:
                dq.popleft()
            if not dq:
                self.recent.pop(c, None)
        while self.glob and now - self.glob[0][0] > 3600:
            self.glob.popleft()
        gidx: dict = {}
        base = self._gseq - len(self.glob) + 1
        for j, ent in enumerate(self.glob):
            sm = ent[3]
            for i in range(4):
                gidx.setdefault((i, (sm >> (16 * i)) & 0xFFFF), []).append((base + j, ent))
        self._gidx = gidx
        for c, dq in list(self.doms.items()):
            while dq and now - dq[0][0] > 900:
                dq.popleft()
            if not dq:
                self.doms.pop(c, None)
        for k in [k for k, dq in self.cnet.items() if not dq or now - dq[-1][0] > CNET_WINDOW]:
            self.cnet.pop(k, None)
        self._puppet_prune(now)
        self._memory_prune(now)
        self._conflict_prune(now)
        self._fort_prune(now)
        self._trace_prune(now)
        self._ap_prune(now)

    def check(self, msg: Msg, is_admin: bool = False, now: float | None = None) -> Verdict:
        self._la = None
        v = self._check_core(msg, is_admin, now)
        la, self._la = self._la, None
        if la is not None:
            try:
                self._learn_post(msg, v, la, self.clock() if now is None else now)
            except Exception:
                log_learn.exception("самообучение: сбой (модерация не затронута)")
        return v

    def _check_core(self, msg: Msg, is_admin: bool = False, now: float | None = None) -> Verdict:
        now = self.clock() if now is None else now
        chat = self.store.chat(msg.chat_id)
        cfg = chat.cfg
        v = Verdict()
        if not cfg.enabled:
            return v
        uid = msg.user_id
        rec = self.store.user(chat, uid, now)
        prev_seen = rec.last_seen
        rec.last_seen = now
        self.store.remember_name(chat, msg.username, uid)

        rings = self.rings.active(msg.chat_id, now) if cfg.ring else []
        fighter = any(r.has(uid) for r in rings)
        if is_admin and msg.text and cfg.puppet and cfg.scam and self.puppet_on:
            self._puppet_note_admin(msg, now)
        if is_admin and cfg.conflicts and self.conflicts_on:
            self._talk_note(msg, now, False)
        if is_admin:
            self._trace_admin(msg, now)
        if is_admin and (not rings or cfg.admins_in_ring or fighter):
            return v
        self._track_ids(msg, now)
        tier = self.tier(rec, now)

        if rings and not fighter:
            tribune = (cfg.tribunes and all(r.mode == "arena" for r in rings) and self._tribune_ok(msg, now))
            if not tribune:
                return self._ring_block(msg, chat, rings, now)

        if rec.banned or rec.muted_until > now:
            self.store.bump(chat, "del_muted", now=now)
            return Verdict(delete=True, category="muted", reasons=["мут"])

        key = (msg.chat_id, uid)
        strict = cfg.strict_until > now or cfg.fort_on
        slow = max(cfg.slow, STRICT_SLOW.get(tier, 0)) if strict else cfg.slow
        if cfg.fort_on:
            slow = max(slow, self.fort_slow(tier, msg.chat_id, now))
        if slow and not msg.edited and not fighter:
            left = slow - (now - self.last_msg.get(key, 0.0))
            if left > 0:
                self.store.bump(chat, "del_slow", now=now)
                return Verdict(delete=True, category="slow", notice="slow", reasons=["медленный режим"],
                               info={"s": int(math.ceil(left))})

        ana = self._analyze(msg, chat, rec, tier, now, strict, prev_seen)
        self._la = (ana, tier, strict, chat, rec)
        if cfg.conflicts and self.conflicts_on:
            t_norm = ana.norm.folded if ana.norm is not None else ""
            bait = bool(t_norm) and any(rx.search(t_norm) for rx in _BAIT_RX)
            self._talk_note(msg, now, bait or bool(ana.found.get("prof") or ana.found.get("hate")))
            if bait and msg.reply_uid and not msg.edited:
                self._bait_note(msg, now)
        raid = self.raid_active(msg.chat_id, now)
        viol: list[tuple] = []

        if cfg.hate and ana.found.get("hate"):
            viol.append(("hate", 2.0, "оскорбление-ярлык или призыв"))
        if cfg.adult and ana.found.get("adult"):
            if ana.found.get("minor"):
                viol.append(("minors", 4.0, "18+ рядом с детской темой"))
            else:
                viol.append(("adult", 2.0, "18+ материалы"))
        if cfg.profanity and ana.found.get("prof"):
            viol.append(("profanity", 0.8, "мат"))

        scam_kind = ""
        if cfg.scam:
            eff = effective(ana, tier, strict)
            eff_own = eff
            if ana.mem_hit:
                raw_all = ana.raw
                ana.raw = round(raw_all - SPAM_MEM_SIGNAL, 2)
                eff_own = effective(ana, tier, strict)
                ana.raw = raw_all
                eff = max(eff_own, min(eff, DELETE_T_S if strict else DELETE_T))
            age = now - (rec.joined or rec.first_seen)
            act = scam_action(eff, tier, age, strict)
            if strict and act == "delete" and tier == "new" and ana.has_contact and eff >= DELETE_T and age <= NEW_BAN_AGE_STRICT:
                act = "ban"
            top = sorted(ana.signals, key=lambda s: -s[1])[:3]
            why = "; ".join(s[2] for s in top) or "подозрительный текст"
            v.score = round(eff, 2)
            if act == "ban":
                viol.append(("scam_ban", 5.0, why)); scam_kind = "ban"
            elif act == "delete" and ana.mem_hit and eff_own < (DELETE_T_S if strict else DELETE_T):
                viol.append(("memory", 1.0, why)); scam_kind = "delete"
            elif act == "delete":
                viol.append(("scam", 2.5, why)); scam_kind = "delete"
            elif act == "watch":
                rec.watch = [t for t in rec.watch if now - t <= WATCH_WINDOW] + [now]
                if len(rec.watch) >= 2:
                    viol.append(("suspicious", 1.0, "второй подозрительный текст подряд: " + why))
                    rec.watch = []

        blocked_link = self._link_violation(ana.urls, cfg, tier, raid, strict)
        if blocked_link:
            viol.append(("link", 1.0, blocked_link))
        if raid and tier == "new" and msg.fwd in ("channel", "chat", "user", "hidden") and not blocked_link:
            viol.append(("link", 1.0, "во время массового входа новичкам запрещены пересылки"))

        if cfg.flood:
            for r in self._flood(msg, rec, tier, now, ana, fighter, raid, strict):
                viol.append(("flood", 1.0, r))
        self._record(msg, ana, now)
        self._cnet_record(msg, ana, tier, now)
        self._trace_record(msg, chat, rec, tier, ana, now)
        if ana.scene.get("kind") == "duo":
            self._puppet_mark_asker(chat, ana.scene, now)
        if viol and cfg.conflicts and self.conflicts_on and msg.reply_uid:
            self._provocation(chat, rec, msg, viol, now)

        if not viol:
            if not msg.edited:
                self.last_msg[key] = now
                if (len(msg.text.strip()) >= 3 and sum(ch.isalnum() for ch in msg.text) >= 3
                        and now - rec.last_clean >= 30 and ana.raw < 1.0):
                    rec.clean += 1
                    rec.last_clean = now
                    self.store.dirty = True
            v.score = v.score or effective(ana, tier, strict)
            return v

        v = self._penalize(msg, chat, rec, tier, now, viol, v, fighter, scam_kind, strict)
        if ana.scene.get("kind") == "full" and any(c in ("scam", "scam_ban") for c, _, _ in viol):
            self._puppet_bust(msg, chat, v, ana.scene, now)
        self._memory_learn_from(chat, msg, ana, v, now)
        if v.ban and v.category == "scam":
            self._event("scam_ban", chat=msg.chat_id, uid=msg.user_id)
        if (self.jitter_on and cfg.jitter and v.category in ("scam", "memory") and not (v.ban or v.alert or v.purge)
                and not strict and not raid and tier == "new" and v.score < STRONG_SCAM):
            v.info["delay"] = round(self.rng.uniform(JITTER_MIN, JITTER_MAX), 1)
        return v

    def _tribune_ok(self, msg: Msg, now: float) -> bool:
        if msg.kind not in ("text", "sticker") or len(msg.text) > 40 or msg.fwd or msg.ents and any(
                e.type in ("url", "text_link", "mention", "text_mention") for e in msg.ents):
            return False
        if msg.text and (extract_urls(msg.text, (), ChatCfg()) or "@" in msg.text):
            return False
        k = (msg.chat_id, msg.user_id)
        if now - self.tribune_last.get(k, 0) < 20:
            return False
        self.tribune_last[k] = now
        return True

    def _ring_block(self, msg: Msg, chat: ChatState, rings: list, now: float) -> Verdict:
        lock = all(r.mode == "lockdown" for r in rings)
        v = Verdict(delete=True, category="ring", notice="lock_hush" if lock else "ring_hush",
                    reasons=["чат закрыт" if lock else "активна сессия"])
        dq = self.ring_noise.setdefault((msg.chat_id, msg.user_id), deque(maxlen=12))
        dq.append(now)
        if sum(1 for t in dq if now - t <= 30) >= 6:
            v.mute_s, v.notice = 180, "ring_mute"
            rec = self.store.user(chat, msg.user_id, now)
            rec.muted_until = max(rec.muted_until, now + 180)
            dq.clear()
        self.store.bump(chat, "del_ring", now=now)
        return v

    def _link_violation(self, urls: list, cfg: ChatCfg, tier: str, raid: bool, strict: bool = False) -> str:
        for u in urls:
            if u.kind == "allowed":
                continue
            if u.kind == "blocked":
                return f"запрещённый домен {u.reg}"
            sketchy = bool(u.flags & {"idn_mixed", "userinfo", "mismatch", "lookalike", "brand_sub", "download", "redirect"}) \
                or u.kind in ("ip", "shortener", "invite")
            restricted = False
            if strict and tier != "veteran":
                restricted = True
            elif strict and (sketchy or u.kind in ("tg_channel", "tg_bot", "invite", "shortener")):
                restricted = True
            elif raid and tier == "new":
                restricted = True
            elif cfg.links == "admins":
                restricted = True
            elif cfg.links == "trusted":
                if tier == "new":
                    restricted = True
                elif tier == "member":
                    restricted = sketchy or u.kind in ("tg_channel", "tg_bot")
                else:
                    restricted = bool(u.flags & {"idn_mixed", "userinfo", "mismatch", "lookalike", "brand_sub", "download"}) \
                        or u.kind in ("invite", "shortener")
            if restricted:
                return f"ссылка от {'новичка' if tier == 'new' else 'участника'}: {u.host}" + (" (строгий режим)" if strict else "")
        return ""

    def _analyze(self, msg: Msg, chat: ChatState, rec: UserRec, tier: str, now: float, strict: bool = False,
                 prev_seen: float = 0.0) -> Analysis:
        a = analyze_text(msg.text, msg.ents, chat.cfg, msg.fwd, known_names=chat.names)
        sig = a.signals
        if rec.clean == 0 and now - rec.first_seen < 600 and a.has_contact:
            sig.append(("first_msg", 1.5, "первое же сообщение — со ссылкой/контактом"))
        exact, sim, ntok = a.fp
        if ntok >= 5 and not msg.edited:
            uid_, cid_ = msg.user_id, msg.chat_id
            users = {u for ts, u, mid, e, s, nt in self.recent.get(cid_, ())
                     if u != uid_ and now - ts <= 300 and (s ^ sim).bit_count() <= 3}
            chats: set = set()
            if len(users) < 2:
                oldest = self._gseq - (self.glob.maxlen or 3000)
                gidx = self._gidx
                for i in range(4):
                    for seq, (ts, c, u, s, nt) in gidx.get((i, (sim >> (16 * i)) & 0xFFFF), ()):
                        if seq > oldest and c != cid_ and now - ts <= 3600 and (s ^ sim).bit_count() <= 3:
                            chats.add(c)
                    if len(chats) >= 2:
                        break
            if (len(users) >= 2 or len(chats) >= 2) and (sum(w for _, w, _ in sig) >= 1.0 or a.has_contact):
                sig.append(("wave", 4.0, "тот же текст у нескольких аккаунтов/чатов"))
        if chat.cfg.smart_links and not msg.edited:
            regs = {u.reg for u in a.urls if u.kind != "allowed" and u.reg}
            if regs:
                others = {u for ts, u, r in self.doms.get(msg.chat_id, ()) if u != msg.user_id and r in regs and now - ts <= 900}
                if len(others) >= 2:
                    sig.append(("campaign", 3.5, "та же ссылка у нескольких аккаунтов подряд"))
        if tier == "new" and a.contacts and not msg.edited and chat.cfg.scam:
            self._cnet_check(msg, a, now)
        if self.puppet_on and chat.cfg.puppet and chat.cfg.scam:
            self._puppet_eval(msg, chat, a, now)
        if self.memory_on and chat.cfg.spam_memory and chat.cfg.scam and a.contacts and tier == "new":
            self._memory_check(msg, chat, a, now)
        self._trace_signals(msg, chat, rec, tier, a, now, strict, prev_seen)
        self._learn_signals(msg, chat, a, tier, now)
        a.raw = round(sum(w for _, w, _ in sig), 2)
        a.hard = round(sum(w for n, w, _ in sig if n in HARD_SIGNALS), 2)
        return a

    def _cnet_others(self, tok: str, uid: int, now: float) -> set:
        return {(c, u) for ts, c, u in self.cnet.get(tok, ()) if u != uid and now - ts <= CNET_WINDOW}

    def _cnet_check(self, msg: Msg, a: Analysis, now: float) -> None:
        """«Сеть контактов»: один и тот же @юзернейм/телефон/инвайт/домен у нескольких НОВЫХ аккаунтов
        (в этом чате и в других чатах бота). Спамеры меняют тексты, но контакт для связи менять дорого."""
        if sum(w for n, w, _ in a.signals if n != "first_msg") < 1.0:
            return
        best: tuple = ()
        for tok in a.contacts:
            if tok.lower() in self.mem_protect:
                continue
            others = self._cnet_others(tok, msg.user_id, now)
            if len(others) >= CNET_MIN_OTHERS and (not best or len(others) > len(best[1])):
                best = (tok, others)
        if best:
            tok, others = best
            chats = {c for c, _ in others} | {msg.chat_id}
            extra = f" в {len(chats)} чатах" if len(chats) > 1 else ""
            a.signals.append(("contact_net", 3.5, f"контакт {tok} у {len(others) + 1} новых аккаунтов{extra}"))

    def _cnet_record(self, msg: Msg, ana: Analysis, tier: str, now: float) -> None:
        if tier != "new" or not ana.contacts or msg.edited:
            return
        for tok in ana.contacts:
            if tok.lower() in self.mem_protect:
                continue
            dq = self.cnet.setdefault(tok, deque(maxlen=40))
            if not dq or dq[-1][1:] != (msg.chat_id, msg.user_id):
                dq.append((now, msg.chat_id, msg.user_id))
        if len(self.cnet) > 5000:
            for k in sorted(self.cnet, key=lambda k: self.cnet[k][-1][0])[:1000]:
                self.cnet.pop(k, None)

    def _record(self, msg: Msg, ana: Analysis, now: float) -> None:
        exact, sim, ntok = ana.fp
        if ana.urls and not msg.edited:
            for u in ana.urls:
                if u.kind != "allowed" and u.reg:
                    self.doms.setdefault(msg.chat_id, deque(maxlen=200)).append((now, msg.user_id, u.reg))
        if ntok and not msg.edited:
            self.recent.setdefault(msg.chat_id, deque(maxlen=250)).append((now, msg.user_id, msg.msg_id, exact, sim, ntok))
            if ntok >= 5:
                ent = (now, msg.chat_id, msg.user_id, sim, ntok)
                self.glob.append(ent)
                self._gseq += 1
                for i in range(4):
                    self._gidx.setdefault((i, (sim >> (16 * i)) & 0xFFFF), []).append((self._gseq, ent))
        if ana.beat is not None:
            self._beat_put(msg.chat_id, msg.msg_id, ana.beat)

    def _young(self, chat: ChatState, uid: int, now: float) -> bool:
        rec = chat.users.get(uid)
        if rec is None:
            return True
        if rec.vouched:
            return False
        return self.tier(rec, now) == "new" or now - (rec.joined or rec.first_seen or now) < PUPPET_YOUNG_AGE

    def _beat_for(self, msg: Msg, roles: int, now: float) -> Beat | None:
        beats = self.beats.get(msg.chat_id, {})
        old = beats.get(msg.msg_id)
        if old is not None:
            return old._replace(roles=roles)
        parent = msg.reply_to
        if not (roles or parent):
            return None
        pb = beats.get(parent) if parent else None
        root = (pb.root if pb is not None else parent) if parent else msg.msg_id
        return Beat(msg.user_id, now, parent, root, roles)

    def _beat_put(self, chat_id: int, mid: int, b: Beat) -> None:
        beats = self.beats.setdefault(chat_id, {})
        fresh = mid not in beats
        beats[mid] = b
        idx = self.scenes.setdefault(chat_id, {})
        lst = idx.get(b.root)
        if b.roles:
            if lst is None:
                lst = idx[b.root] = []
            if mid not in lst:
                lst.append(mid)
                if len(lst) > PUPPET_THREAD_ROLES:
                    del lst[0]
        elif lst and mid in lst:
            lst.remove(mid)
            if not lst:
                idx.pop(b.root, None)
        if fresh and len(beats) > PUPPET_MAX_BEATS:
            self._beat_drop(chat_id, next(iter(beats)))

    def _beat_drop(self, chat_id: int, mid: int) -> None:
        b = self.beats.get(chat_id, {}).pop(mid, None)
        if b is None:
            return
        idx = self.scenes.get(chat_id, {})
        lst = idx.get(b.root)
        if lst and mid in lst:
            lst.remove(mid)
            if not lst:
                idx.pop(b.root, None)

    def _puppet_prune(self, now: float) -> None:
        for c, beats in list(self.beats.items()):
            while beats:
                mid, b = next(iter(beats.items()))
                if now - b.ts <= PUPPET_TTL:
                    break
                self._beat_drop(c, mid)
            if not beats:
                self.beats.pop(c, None)
                self.scenes.pop(c, None)
        for c, d in list(self.busted.items()):
            for root in [r for r, t in d.items() if now - t > PUPPET_TTL]:
                d.pop(root, None)
            if not d:
                self.busted.pop(c, None)

    @staticmethod
    def _under(beats: dict, cur_id: int, cur: Beat, mid: int, anc: int) -> bool:
        for _ in range(PUPPET_DEPTH):
            b = cur if mid == cur_id else beats.get(mid)
            if b is None or not b.parent:
                return False
            if b.parent == anc:
                return True
            mid = b.parent
        return False

    def _scene_find(self, chat: ChatState, cur_id: int, cur: Beat, now: float) -> dict | None:
        cid = chat.chat_id
        beats = self.beats.get(cid, {})
        nodes = {i: beats[i] for i in self.scenes.get(cid, {}).get(cur.root, ()) if i in beats and i != cur_id}
        nodes[cur_id] = cur
        young: dict[int, bool] = {}

        def is_young(uid: int) -> bool:
            if uid not in young:
                young[uid] = self._young(chat, uid, now)
            return young[uid]

        asks = sorted((i for i, b in nodes.items() if b.roles & ROLE_ASK), reverse=True)
        pitches = sorted(i for i, b in nodes.items() if b.roles & ROLE_PITCH)
        confirms = sorted(i for i, b in nodes.items() if b.roles & ROLE_CONFIRM)
        duo = None
        for p in pitches:
            pb = nodes[p]
            if not is_young(pb.uid):
                continue
            for a in asks:
                ab = nodes[a]
                if a >= p or ab.uid == pb.uid or not self._under(beats, cur_id, cur, p, a):
                    continue
                for c in confirms:
                    cb = nodes[c]
                    if (c <= p or cb.uid in (ab.uid, pb.uid) or not is_young(cb.uid)
                            or not self._under(beats, cur_id, cur, c, a)):
                        continue
                    if cur_id in (p, c):
                        return {"kind": "full", "root": cur.root, "ask": a, "pitch": p, "confirm": c,
                                "ask_uid": ab.uid, "pitch_uid": pb.uid, "confirm_uid": cb.uid}
                if duo is None and cur_id == p:
                    duo = {"kind": "duo", "root": cur.root, "ask": a, "pitch": p, "confirm": 0,
                           "ask_uid": ab.uid, "pitch_uid": pb.uid, "confirm_uid": 0}
        return duo

    def _puppet_eval(self, msg: Msg, chat: ChatState, a: Analysis, now: float) -> None:
        n = a.norm
        t = n.folded[:1500] if n is not None else ""
        if n is not None and n.mixed:
            t = deglyph(t)
        t = deleet(t)
        dm = any(s[0] in _DM_SIGNALS for s in a.signals)
        roles = puppet_roles(t, msg.kind, a.has_contact, dm)
        cur = self._beat_for(msg, roles, now)
        if cur is None:
            return
        if roles & ROLE_PITCH and a.contacts:
            cur = cur._replace(contacts=a.contacts)
        a.beat = cur
        if not cur.parent or not roles & (ROLE_PITCH | ROLE_CONFIRM):
            return
        found = self._scene_find(chat, msg.msg_id, cur, now)
        if not found:
            return
        a.scene = found
        if found["kind"] == "full":
            a.signals.append(("puppet", PUPPET_SIGNAL, "постановочный диалог: вопрос → питч со ссылкой → «всё работает» от новых аккаунтов"))
        else:
            a.signals.append(("puppet_duo", PUPPET_DUO_SIGNAL, "похоже на постановку: новичок отвечает на вопрос ссылкой и обещанием выгоды"))

    def _puppet_note_admin(self, msg: Msg, now: float) -> None:
        b = self._beat_for(msg, puppet_roles(fold(msg.text)[:1500], msg.kind), now)
        if b is not None:
            self._beat_put(msg.chat_id, msg.msg_id, b)

    def _puppet_mark_asker(self, chat: ChatState, scene: dict, now: float) -> None:
        uid = scene.get("ask_uid", 0)
        rec = chat.users.get(uid)
        if rec is not None and self._young(chat, uid, now):
            rec.watch = [t for t in rec.watch if now - t <= WATCH_WINDOW] + [now]
            self.store.dirty = True

    def _puppet_bust(self, msg: Msg, chat: ChatState, v: Verdict, scene: dict, now: float) -> None:
        cid, root = msg.chat_id, scene["root"]
        v.alert = True
        v.info["puppet"] = {"ask": scene["ask_uid"], "pitch": scene["pitch_uid"], "confirm": scene["confirm_uid"]}
        done = self.busted.setdefault(cid, {})
        if root in done:
            return
        done[root] = now
        self.store.bump(chat, "puppet", now=now)
        if self.memory_on and chat.cfg.spam_memory:
            toks = [t for b in self.beats.get(cid, {}).values() if b.root == root and b.uid == scene["pitch_uid"]
                    for t in b.contacts]
            self._spam_learn(cid, scene["pitch_uid"], list(dict.fromkeys(toks)), now, "постановочный диалог")
        if v.notice in ("warn", "mute", "ban_spam", "hacked"):
            v.notice = "puppet"
        beats = self.beats.get(cid, {})
        for role, uid in (("pitch", scene["pitch_uid"]), ("confirm", scene["confirm_uid"])):
            orec = chat.users.get(uid)
            if uid == msg.user_id or orec is None or orec.banned:
                continue
            ids = [mid for mid, b in beats.items() if b.root == root and b.uid == uid]
            age = now - (orec.joined or orec.first_seen or now)
            ban = (role == "pitch" and self.tier(orec, now) == "new" and orec.clean <= PUPPET_BAN_CLEAN
                   and age <= NEW_BAN_AGE)
            orec.strikes.append([now, PUPPET_SIGNAL, "puppet"])
            orec.strikes = orec.strikes[-STRIKE_KEEP:]
            if ban:
                orec.banned = True
                ids += self.recent_ids(cid, uid, 1800, now)
                self.store.bump(chat, "ban", now=now)
            else:
                orec.muted_until = max(orec.muted_until, now + PUPPET_MUTE_S)
                self.store.bump(chat, "mute", now=now)
            v.others.append({"uid": uid, "role": role, "ids": sorted(set(ids)), "ban": ban,
                             "mute_s": 0 if ban else PUPPET_MUTE_S})
            self.radar_note(cid, uid, "puppet", now)
        self._puppet_mark_asker(chat, scene, now)
        self.store.dirty = True

    def _spam_book(self, chat_id: int, create: bool = False) -> dict | None:
        mem = self.store.meta.setdefault("spam_memory", {}) if create else self.store.meta.get("spam_memory")
        if mem is None:
            return None
        return mem.setdefault(str(chat_id), {}) if create else mem.get(str(chat_id))

    def _memory_check(self, msg: Msg, chat: ChatState, a: Analysis, now: float) -> None:
        book = self._spam_book(msg.chat_id)
        if not book:
            return
        for tok in a.contacts:
            e = book.get(tok)
            if e is None or now - e.get("t", 0.0) > e.get("ttl", SPAM_MEM_TTL) or e.get("u") == msg.user_id:
                continue
            a.mem_hit = tok
            e["n"] = e.get("n", 0) + 1
            a.signals.append(("known_contact", SPAM_MEM_SIGNAL, f"контакт {tok} уже ловили {human_dur(now - e['t'])} назад"))
            self.store.bump(chat, "memory", now=now)
            self.store.dirty = True
            return

    def _memory_learn_from(self, chat: ChatState, msg: Msg, ana: Analysis, v: Verdict, now: float) -> None:
        if v.category != "scam" or not ana.contacts or not self.memory_on or not chat.cfg.spam_memory:
            return
        if ana.mem_hit:
            return
        if v.score >= STRONG_SCAM:
            self._spam_learn(msg.chat_id, msg.user_id, list(ana.contacts), now, v.reasons[0] if v.reasons else "спам")

    def _spam_learn(self, chat_id: int, uid: int, tokens: list, now: float, why: str) -> None:
        tokens = [t for t in tokens if t and t.lower() not in self.mem_protect][:SPAM_MEM_LEARN]
        if not tokens:
            return
        book = self._spam_book(chat_id, create=True)
        for tok in tokens:
            old = book.get(tok)
            book[tok] = {"t": round(now), "n": old.get("n", 0) if old else 0, "u": uid, "w": why[:60]}
        for tok in sorted(book, key=lambda k: book[k].get("t", 0))[:max(0, len(book) - SPAM_MEM_MAX)]:
            book.pop(tok, None)
        self.store.dirty = True

    def _memory_prune(self, now: float) -> None:
        mem = self.store.meta.get("spam_memory")
        if not mem:
            return
        for cid in list(mem):
            book = mem[cid]
            for tok in [k for k, e in book.items() if now - e.get("t", 0.0) > e.get("ttl", SPAM_MEM_TTL)]:
                book.pop(tok, None)
                self.store.dirty = True
            if not book:
                mem.pop(cid, None)

    def spam_memory_list(self, chat_id: int) -> list:
        book = self._spam_book(chat_id) or {}
        return sorted(book.items(), key=lambda kv: -kv[1].get("t", 0))

    def spam_memory_forget(self, chat_id: int, token: str | None) -> int:
        book = self._spam_book(chat_id)
        if not book:
            return 0
        if token is None:
            n = len(book)
            book.clear()
        else:
            t = token.strip()
            digits = re.sub(r"\D", "", t)
            keys = [t, t.lower(), "@" + t.lower().lstrip("@")]
            if len(digits) >= 10 and not re.search(r"[A-Za-z]", t.replace("tel:", "")):
                keys.append("tel:" + digits[-10:])
            n = sum(1 for k in dict.fromkeys(keys) if book.pop(k, None) is not None)
        if n:
            self.store.dirty = True
        return n

    def spam_memory_drop_user(self, chat_id: int, uid: int) -> int:
        book = self._spam_book(chat_id)
        if not book:
            return 0
        gone = [k for k, e in book.items() if e.get("u") == uid]
        for k in gone:
            book.pop(k, None)
        if gone:
            self.store.dirty = True
        return len(gone)

    def _event(self, kind: str, **kw) -> None:
        if len(self.events) < 200:
            self.events.append({"kind": kind, **kw})

    def _talk_note(self, msg: Msg, now: float, hostile: bool) -> None:
        if not msg.reply_uid or msg.reply_uid == msg.user_id or msg.edited:
            return
        dq = self.talk.setdefault(msg.chat_id, deque(maxlen=TALK_MAX))
        dq.append((now, msg.user_id, msg.reply_uid, msg.msg_id, hostile))
        target, senders, mean = msg.reply_uid, set(), set()
        for ts, a, b, _mid, h in reversed(dq):
            if now - ts > DOGPILE_WINDOW:
                break
            if b == target:
                senders.add(a)
                if h:
                    mean.add(a)
        if len(senders) >= DOGPILE_MIN and len(mean) >= DOGPILE_HOSTILE:
            key = (msg.chat_id, target)
            if now - self._dog_last.get(key, 0.0) >= DOGPILE_COOLDOWN:
                self._dog_last[key] = now
                self.store.bump(self.store.chat(msg.chat_id), "dogpile", now=now)
                self._event("dogpile", chat=msg.chat_id, target=target, n=len(senders), hostile=len(mean),
                            people=sorted(senders)[:8])

    def _bait_note(self, msg: Msg, now: float) -> None:
        self.baits.setdefault(msg.chat_id, deque(maxlen=200)).append((now, msg.user_id, msg.reply_uid, msg.msg_id))

    def _provocation(self, chat: ChatState, rec: UserRec, msg: Msg, viol: list, now: float) -> None:
        cats = {c for c, _w, _r in viol}
        if not cats & {"profanity", "hate"}:
            return
        bait = None
        for ts, a, b, mid in reversed(self.baits.get(msg.chat_id, ())):
            if now - ts > BAIT_WINDOW:
                break
            if a == msg.reply_uid and b == msg.user_id:
                bait = (a, mid)
                break
        if bait is None:
            return
        soft = cats == {"profanity"} and rec.clean >= PROV_MIN_CLEAN
        if soft:
            for i, (c, _w, _r) in enumerate(viol):
                if c == "profanity":
                    viol[i] = (c, PROV_SOFT_STRIKE, "мат (после наживки собеседника: смягчено)")
        self.store.bump(chat, "provocation", now=now)
        self._event("provocation", chat=msg.chat_id, baiter=bait[0], victim=msg.user_id, softened=soft, msg_id=bait[1])
        hist = self.prov_hist.setdefault((msg.chat_id, bait[0]), {})
        hist[bait[1]] = now
        for k in [k for k, t in hist.items() if now - t > 86400]:
            hist.pop(k, None)
        wkey = (msg.chat_id, bait[0])
        if len(hist) >= PROV_REPEAT and now - self._prov_warned.get(wkey, 0.0) > 86400:
            self._prov_warned[wkey] = now
            self._event("provocation_repeat", chat=msg.chat_id, baiter=bait[0], n=len(hist))

    def talk_between(self, chat_id: int, a: int, b: int, now: float, window: float) -> bool:
        for ts, x, y, _m, _h in reversed(self.talk.get(chat_id, ())):
            if now - ts > window:
                break
            if (x == a and y == b) or (x == b and y == a):
                return True
        return False

    def contacts_of(self, chat_id: int, uid: int, now: float, window: float = 86400.0) -> list:
        res: dict[int, dict] = {}
        for ts, a, b, _m, _h in self.talk.get(chat_id, ()):
            if now - ts > window or uid not in (a, b) or a == b:
                continue
            other = b if a == uid else a
            e = res.setdefault(other, {"uid": other, "to": 0, "frm": 0, "last": 0.0})
            e["to" if a == uid else "frm"] += 1
            e["last"] = max(e["last"], ts)
        return sorted(res.values(), key=lambda e: (-(e["to"] + e["frm"]), -e["last"]))

    def report_effective(self, chat_id: int, by: dict, now: float) -> tuple:
        ids = list(by)
        root = {u: u for u in ids}

        def find(x: int) -> int:
            while root[x] != x:
                root[x] = root[root[x]]
                x = root[x]
            return x

        for i, a in enumerate(ids):
            for b in ids[i + 1:]:
                if self.talk_between(chat_id, a, b, now, 86400.0):
                    root[find(a)] = find(b)
        groups: dict[int, float] = {}
        for u in ids:
            r = find(u)
            groups[r] = max(groups.get(r, 0.0), by[u])
        return round(sum(groups.values()), 2), len(ids) - len(groups)

    def report_strikes_recent(self, chat_id: int, uid: int, now: float) -> int:
        chat = self.store.chats.get(chat_id)
        rec = chat.users.get(uid) if chat else None
        return sum(1 for ts, _w, cat in rec.strikes if cat == "report" and now - ts <= 86400) if rec else 0

    def _conflict_prune(self, now: float) -> None:
        for c, dq in list(self.talk.items()):
            while dq and now - dq[0][0] > TALK_TTL:
                dq.popleft()
            if not dq:
                self.talk.pop(c, None)
        for c, dq in list(self.baits.items()):
            while dq and now - dq[0][0] > BAIT_WINDOW:
                dq.popleft()
            if not dq:
                self.baits.pop(c, None)
        for d in (self._dog_last, self._prov_warned):
            for k in [k for k, t in d.items() if now - t > 86400]:
                d.pop(k, None)
        for k, h in list(self.prov_hist.items()):
            for mid in [mid for mid, t in h.items() if now - t > 86400]:
                h.pop(mid, None)
            if not h:
                self.prov_hist.pop(k, None)

    def _flood(self, msg: Msg, rec: UserRec, tier: str, now: float, ana: Analysis, fighter: bool, raid: bool,
               strict: bool = False) -> list[str]:
        out: list[str] = []
        key = (msg.chat_id, msg.user_id)
        dq = self.ut.setdefault(key, deque(maxlen=40))
        text = msg.text
        exact, sim, ntok = ana.fp
        exact = dupkey(ana.norm.folded) if ana.norm else exact
        if not msg.edited:
            lim, win = RATE_RAID_NEW if (raid and tier == "new") else RATE[tier]
            if strict and RATE_STRICT[tier][0] <= lim:
                lim, win = RATE_STRICT[tier]
            if fighter:
                lim = max(lim, 12)
            if 1 + sum(1 for t, k, e in dq if now - t <= win) > lim:
                out.append("слишком часто")
            if msg.kind in STICKER_KINDS and 1 + sum(1 for t, k, e in dq if k in STICKER_KINDS and now - t <= 30) > (STICKER_LIM_STRICT if strict else STICKER_LIM)[tier]:
                out.append("поток стикеров/гифок")
            if msg.kind in MEDIA_KINDS and 1 + sum(1 for t, k, e in dq if k in MEDIA_KINDS and now - t <= 20) > (MEDIA_LIM_STRICT if strict else MEDIA_LIM)[tier]:
                out.append("поток медиа")
            if not fighter:
                alnum = len(re.sub(r"\W+", "", text))
                if exact and alnum >= 4 and 1 + sum(1 for t, k, e in dq if e == exact and now - t <= 90) >= ((3 if strict else 4) if tier == "veteran" else (2 if strict else 3)):
                    out.append("одно и то же снова и снова")
                elif ntok >= 8 and sum(1 for ts, u, mid, e, s, nt in self.recent.get(msg.chat_id, ())
                                       if u == msg.user_id and now - ts <= 60 and (s ^ sim).bit_count() <= 4) >= 2:
                    out.append("почти одинаковые сообщения подряд")
            dq.append((now, msg.kind, exact))
        if not fighter:
            lim = RUN_LIM[tier]
            rx = _RUN_RE.get(lim) or _RUN_RE.setdefault(lim, re.compile(r"([^\s])\1{%d,}" % (lim - 1)))
            if rx.search(text):
                out.append("один символ много раз подряд")
            toks = ana.norm.tokens if ana.norm else []
            if len(toks) >= 8:
                top = max(Counter(toks).values(), default=0)
                if top / len(toks) >= 0.7:
                    out.append("одно слово много раз")
            if count_emoji(text) > (min(EMOJI_LIM[tier], EMOJI_LIM_STRICT) if strict else EMOJI_LIM[tier]):
                out.append("слишком много эмодзи")
            if len(text) > (min(WALL_LIM[tier], WALL_LIM_STRICT) if strict else WALL_LIM[tier]):
                out.append("простыня текста")
            if ana.mentions >= (min(MENTION_LIM[tier], MENTION_LIM_STRICT) if strict else MENTION_LIM[tier]):
                out.append("массовые упоминания")
        return out

    def _penalize(self, msg: Msg, chat: ChatState, rec: UserRec, tier: str, now: float, viol: list, v: Verdict,
                  fighter: bool, scam_kind: str, strict: bool = False) -> Verdict:
        order = ["minors", "hate", "adult", "scam_ban", "scam", "profanity", "link", "flood", "suspicious"]
        viol.sort(key=lambda x: order.index(x[0]) if x[0] in order else 99)
        cat = viol[0][0]
        v.delete = True
        v.category = {"scam_ban": "scam"}.get(cat, cat)
        v.reasons = list(dict.fromkeys(r for _, _, r in viol))[:4]
        weight = max(w for _, w, _ in viol) + 0.25 * (len(viol) - 1)
        if v.category in ("flood", "link", "profanity", "suspicious"):
            weight *= STRIKE_SCALE[tier]
        if strict and v.category in ("scam", "link", "flood", "profanity", "suspicious"):
            weight *= STRICT_STRIKE_MULT
        v.strike = round(weight, 2)
        rec.strikes.append([now, v.strike, v.category])
        rec.strikes = rec.strikes[-STRIKE_KEEP:]
        v.level = round(self.strike_level(rec, now), 2)
        mute = next(m for lim, m in LADDER if v.level < lim)
        floor = STRICT_MIN_MUTE.get(tier, 0) if strict else 0
        if floor and v.category in ("scam", "link", "flood", "profanity", "suspicious"):
            mute = max(mute, floor)
        v.info["n"] = sum(1 for ts, w, _ in rec.strikes if now - ts <= 86400)

        if cat == "minors":
            v.mute_s, v.purge, v.alert, v.notice = 86400, True, True, "mute"
        elif cat == "scam_ban":
            v.ban, v.purge, v.alert, v.notice = True, True, True, "ban_spam"
            rec.banned = True
        elif cat == "scam" and v.score < STRONG_SCAM:
            v.mute_s, v.notice = max(mute, 600), "mute"
        elif cat == "scam":
            v.purge = True
            v.alert = True
            if tier == "new":
                v.mute_s, v.notice = max(mute, 86400), "mute"
            else:
                v.mute_s, v.notice = max(mute, STRICT_HACKED_MUTE if strict else 3600), "hacked"
        elif cat == "hate":
            v.mute_s, v.notice = mute, ("mute" if mute else "warn")
            v.alert = bool(mute)
        else:
            v.mute_s, v.notice = mute, ("mute" if mute else "warn")
        if v.mute_s:
            rec.muted_until = max(rec.muted_until, now + v.mute_s)
        if v.category == "flood" and not fighter:
            v.purge_s = max((FLOOD_PURGE.get(r, 0) for r in v.reasons), default=0)
        if v.category == "scam":
            v.strict_started = self._spam_hit(chat, msg.user_id, now)
        if strict or v.strict_started:
            self.strict_count(msg.chat_id, "del")
            if v.ban:
                self.strict_count(msg.chat_id, "ban")
            elif v.mute_s:
                self.strict_count(msg.chat_id, "mute")
        if fighter and not (v.mute_s or v.ban):
            v.notice = ""
        self.store.bump(chat, "del_" + v.category, now=now)
        if v.ban:
            self.store.bump(chat, "ban", now=now)
        elif v.mute_s:
            self.store.bump(chat, "mute", now=now)
        self.store.dirty = True
        self.radar_note(msg.chat_id, msg.user_id, "scam_ban" if v.ban else v.category, now)
        if v.category in ("scam", "link", "suspicious"):
            self.ap_vec_note(msg.chat_id, msg.user_id, self.ap_vector(msg), now)
        return v

    def explain(self, text: str, chat_id: int = 0, ents=(), fwd: str = "") -> dict:
        cfg = self.store.chat(chat_id).cfg if chat_id in self.store.chats else ChatCfg()
        a = analyze_text(text, ents, cfg, fwd)
        out = {"signals": a.signals, "raw": a.raw, "urls": a.urls, "found": a.found, "tiers": {}, "learned": []}
        try:
            out["learned"] = self.learn_probe(text, chat_id, a)
        except Exception:
            log_learn.exception("самообучение: разбор для /explain не получился")
        for t in ("new", "member", "veteran"):
            eff = effective(a, t)
            out["tiers"][t] = (round(eff, 2), scam_action(eff, t))
        return out


GROUP_TYPES = {"group", "supergroup"}
ANON_ADMIN_ID = 1087968824
NOTICE_TTL = {"warn": 45, "mute": 90, "ban_spam": 120, "hacked": 180, "ring_hush": 10, "lock_hush": 10,
              "ring_mute": 60, "slow": 8, "puppet": 120}
STAT_LABELS = {"del_ring": "удалено во время сессий", "del_scam": "спам и приманки", "del_flood": "флуд",
               "del_link": "ссылки", "del_hate": "оскорбления", "del_adult": "18+", "del_minors": "18+ рядом с детьми",
               "del_profanity": "мат", "del_slow": "медленный режим", "del_muted": "от ограниченных участников",
               "del_suspicious": "подозрительное", "mute": "ограничено", "ban": "заблокировано",
               "captcha_ok": "прошли проверку", "captcha_fail": "не прошли проверку", "captcha_skip": "пропущены без проверки", "reports": "жалоб принято",
               "del_lock": "замки по типам контента", "del_night": "ночной режим", "cas_ban": "заблокировано по базе CAS",
               "gban": "заблокировано по общему списку", "join_decline": "заявок отклонено",
               "impostor": "подмена админов и поддержки", "del_newbie": "ограничения новичков", "name_ban": "имена-рекламы",
               "del_strict": "строгий режим: запрещённый контент", "strict_on": "включений строгого режима",
               "fort_on": "включений полной защиты", "trace_hit": "улики Следопыта в оценке (правки, шаблоны, скорость)",
               "react_spam": "спам реакциями", "puppet": "постановочные диалоги (кукольный театр)",
              "memory": "сработала память о спаме",
              "learn_hit": "сработало выученное по вашим карточкам",
              "del_memory": "удалено только из-за памяти о спаме",
              "provocation": "срыв после наживки (журнал)", "dogpile": "похоже на травлю (сигнал владельцу)",
              "report_blocked": "жалобы, не принятые автоматически"}


def esc(s, n: int = 40) -> str:
    return html.escape(str(s or "")[:n], quote=False)


def mention(uid: int, name: str = "") -> str:
    return f'<a href="tg://user?id={int(uid)}">{esc(name) or int(uid)}</a>'


def status_of(member) -> str:
    s = getattr(member, "status", "")
    return str(getattr(s, "value", s))


def user_name(u) -> str:
    if u is None:
        return ""
    return getattr(u, "full_name", None) or getattr(u, "first_name", "") or str(getattr(u, "id", ""))


def utf16_slice(text: str, off: int, ln: int) -> str:
    raw = text.encode("utf-16-le")
    return raw[off * 2:(off + ln) * 2].decode("utf-16-le", "ignore")


_KINDS = {"text", "photo", "video", "document", "voice", "video_note", "audio", "sticker", "animation"}
_FWD = {"user": "user", "hidden_user": "hidden", "chat": "chat", "channel": "channel"}


def to_msg(m, edited: bool = False, uid: int | None = None, name: str = "") -> Msg:
    text = getattr(m, "text", None) or getattr(m, "caption", None) or ""
    ents = []
    for e in list(getattr(m, "entities", None) or []) + list(getattr(m, "caption_entities", None) or []):
        et = str(getattr(e.type, "value", e.type))
        eu = getattr(e, "user", None)
        ents.append(Ent(type=et, text=utf16_slice(text, e.offset, e.length) if text else "",
                          url=getattr(e, "url", None) or "", user_id=getattr(eu, "id", 0) if eu else 0))
    ct = getattr(m, "content_type", "text")
    kind = str(getattr(ct, "value", ct))
    if kind not in _KINDS:
        kind = "other"
    fwd = ""
    origin = getattr(m, "forward_origin", None)
    if origin is not None:
        fwd = _FWD.get(str(getattr(origin.type, "value", origin.type)), "user")
    elif getattr(m, "forward_date", None):
        fwd = "channel" if getattr(m, "forward_from_chat", None) else "user"
    u = getattr(m, "from_user", None)
    sc = getattr(m, "sender_chat", None)
    chat = getattr(m, "chat", None)
    reply_to = 0
    rm = getattr(m, "reply_to_message", None)
    rid = getattr(rm, "message_id", 0) if rm is not None else 0
    if isinstance(rid, int) and rid > 0:
        topic_root = bool(getattr(m, "is_topic_message", False)) and rid == getattr(m, "message_thread_id", None)
        if not topic_root and not getattr(rm, "forum_topic_created", None):
            reply_to = rid
    ru = getattr(getattr(rm, "from_user", None), "id", 0) if reply_to else 0
    reply_uid = ru if isinstance(ru, int) else 0
    return Msg(chat_id=chat.id, msg_id=m.message_id, user_id=uid if uid is not None else getattr(u, "id", 0),
                 name=name or user_name(u), username=(getattr(u, "username", None) or "") if u else "",
                 text=text, kind=kind, ents=ents, fwd=fwd,
                 sender_chat=bool(sc and sc.id != chat.id), via_bot=bool(getattr(m, "via_bot", None)),
                 edited=edited, ts=time.time(), reply_to=reply_to, reply_uid=reply_uid)


def no_permissions() -> ChatPermissions:
    return ChatPermissions(can_send_messages=False, can_send_audios=False, can_send_documents=False,
                           can_send_photos=False, can_send_videos=False, can_send_video_notes=False,
                           can_send_voice_notes=False, can_send_polls=False, can_send_other_messages=False,
                           can_add_web_page_previews=False, can_change_info=False, can_invite_users=False,
                           can_pin_messages=False, can_manage_topics=False)


def open_permissions() -> ChatPermissions:
    return ChatPermissions(can_send_messages=True, can_send_audios=True, can_send_documents=True,
                           can_send_photos=True, can_send_videos=True, can_send_video_notes=True,
                           can_send_voice_notes=True, can_send_polls=True, can_send_other_messages=True,
                           can_add_web_page_previews=True, can_invite_users=True)


def msg_link(chat, msg_id: int) -> str:
    uname = getattr(chat, "username", None)
    if uname:
        return f"https://t.me/{uname}/{msg_id}"
    cid = str(chat.id)
    return f"https://t.me/c/{cid[4:]}/{msg_id}" if cid.startswith("-100") else ""


log_hook = logging.getLogger("guard.hook")

MAX_HEADER = 8192
MAX_BODY = 4096
REASONS = {200: "OK", 400: "Bad Request", 401: "Unauthorized", 404: "Not Found", 405: "Method Not Allowed",
           408: "Request Timeout", 411: "Length Required", 413: "Payload Too Large", 429: "Too Many Requests",
           431: "Request Header Fields Too Large", 500: "Internal Server Error"}


class HookServer:

    def __init__(self, secret: str, handler, host: str = "127.0.0.1", port: int = 8765, io_timeout: float = 5.0,
                 max_conn: int = 50):
        if not secret or len(secret) < 8:
            raise ValueError("GUARD_SECRET должен быть задан и не короче 8 символов")
        self.secret = secret.encode()
        self.handler = handler
        self.host, self.port = host, port
        self.io_timeout = io_timeout
        self._sem = asyncio.Semaphore(max_conn)
        self._server: asyncio.AbstractServer | None = None
        self._bad: dict[str, list] = {}
        self.served = 0

    async def start(self) -> None:
        self._server = await asyncio.start_server(self._on_conn, self.host, self.port, limit=MAX_HEADER)
        self.port = self._server.sockets[0].getsockname()[1]
        log_hook.info("мост слушает %s:%s", self.host, self.port)

    async def stop(self) -> None:
        if self._server:
            self._server.close()
            await self._server.wait_closed()
            self._server = None

    async def _on_conn(self, reader: asyncio.StreamReader, writer: asyncio.StreamWriter) -> None:
        peer = writer.get_extra_info("peername")
        ip = peer[0] if peer else "?"
        try:
            async with self._sem:
                await asyncio.wait_for(self._serve(reader, writer, ip), timeout=self.io_timeout * 3)
        except asyncio.TimeoutError:
            await self._reply(writer, 408, {"ok": False, "error": "timeout"})
        except (ConnectionError, asyncio.IncompleteReadError):
            pass
        except Exception:
            log_hook.exception("мост: необработанная ошибка")
            await self._reply(writer, 500, {"ok": False, "error": "internal"})
        finally:
            try:
                writer.close()
            except Exception:
                pass

    async def _reply(self, writer, status: int, body: dict | None, head_only: bool = False) -> None:
        try:
            raw = json.dumps(body or {}, ensure_ascii=False).encode()
            head = (f"HTTP/1.1 {status} {REASONS.get(status, 'OK')}\r\nContent-Type: application/json; charset=utf-8\r\n"
                    f"Content-Length: {len(raw)}\r\nConnection: close\r\nCache-Control: no-store\r\n\r\n").encode()
            writer.write(head + (b"" if head_only else raw))
            await asyncio.wait_for(writer.drain(), timeout=self.io_timeout)
        except Exception:
            pass

    def _throttled(self, ip: str) -> bool:
        now = time.monotonic()
        lst = [t for t in self._bad.get(ip, []) if now - t < 60]
        self._bad[ip] = lst
        if len(self._bad) > 500:
            self._bad = {k: v for k, v in self._bad.items() if v}
        return len(lst) >= 10

    async def _serve(self, reader, writer, ip: str) -> None:
        try:
            head = await asyncio.wait_for(reader.readuntil(b"\r\n\r\n"), timeout=self.io_timeout)
        except asyncio.LimitOverrunError:
            return await self._reply(writer, 431, {"ok": False, "error": "headers too large"})
        except asyncio.IncompleteReadError:
            return
        lines = head.decode("latin-1").split("\r\n")
        parts = lines[0].split(" ")
        if len(parts) != 3 or not parts[2].startswith("HTTP/"):
            return await self._reply(writer, 400, {"ok": False, "error": "bad request line"})
        method, target = parts[0].upper(), parts[1].split("?", 1)[0]
        headers: dict[str, str] = {}
        for ln in lines[1:]:
            if ":" in ln:
                k, v = ln.split(":", 1)
                headers[k.strip().lower()] = v.strip()
        self.served += 1

        if target in ("/", "/health"):
            if method in ("GET", "HEAD"):
                return await self._reply(writer, 200, {"ok": True, "service": "guard"}, head_only=method == "HEAD")
            return await self._reply(writer, 405, {"ok": False, "error": "method"})
        if target != "/ring":
            return await self._reply(writer, 404, {"ok": False, "error": "not found"})
        if method != "POST":
            return await self._reply(writer, 405, {"ok": False, "error": "method"})
        if self._throttled(ip):
            return await self._reply(writer, 429, {"ok": False, "error": "too many bad attempts"})

        given = headers.get("x-guard-secret", "")
        if not given and headers.get("authorization", "").lower().startswith("bearer "):
            given = headers["authorization"][7:].strip()
        if not hmac.compare_digest(given.encode(), self.secret):
            self._bad.setdefault(ip, []).append(time.monotonic())
            await asyncio.sleep(0.25)
            return await self._reply(writer, 401, {"ok": False, "error": "unauthorized"})

        if "transfer-encoding" in headers:
            return await self._reply(writer, 400, {"ok": False, "error": "chunked not supported"})
        try:
            n = int(headers.get("content-length", ""))
        except ValueError:
            return await self._reply(writer, 411, {"ok": False, "error": "content-length required"})
        if n < 0 or n > MAX_BODY:
            return await self._reply(writer, 413, {"ok": False, "error": "body too large"})
        body = await asyncio.wait_for(reader.readexactly(n), timeout=self.io_timeout)
        try:
            payload = json.loads(body.decode("utf-8"))
            if not isinstance(payload, dict):
                raise ValueError("ожидался объект")
        except (ValueError, UnicodeDecodeError):
            return await self._reply(writer, 400, {"ok": False, "error": "bad json"})
        try:
            result = await self.handler(payload)
        except Exception:
            log_hook.exception("мост: обработчик упал")
            return await self._reply(writer, 500, {"ok": False, "error": "internal"})
        await self._reply(writer, 200 if result.get("ok") else 400, result)


class GuardClient:

    def __init__(self, url: str = "", secret: str = "", timeout: float = 3.0, retries: int = 2):
        self.url = url.rstrip("/")
        self.secret = secret
        self.timeout = timeout
        self.retries = retries
        self._tasks: set = set()

    @classmethod
    def from_env(cls) -> "GuardClient":
        return cls(os.getenv("GUARD_URL", ""), os.getenv("GUARD_SECRET", ""))

    @property
    def enabled(self) -> bool:
        return bool(self.url and self.secret)

    def _post(self, payload: dict) -> dict | None:
        data = json.dumps(payload, ensure_ascii=False).encode()
        req = urllib.request.Request(self.url + "/ring", data=data, method="POST", headers={
            "Content-Type": "application/json", "X-Guard-Secret": self.secret})
        last = None
        for attempt in range(self.retries + 1):
            try:
                with urllib.request.urlopen(req, timeout=self.timeout) as r:
                    return json.loads(r.read().decode("utf-8") or "{}")
            except urllib.error.HTTPError as e:
                try:
                    return json.loads(e.read().decode("utf-8"))
                except Exception:
                    return {"ok": False, "error": f"http {e.code}"}
            except Exception as e:
                last = e
                if attempt < self.retries:
                    time.sleep(0.4 * (attempt + 1))
        log_hook.warning("охрана недоступна (%s): %s", payload.get("action"), last)
        return None

    async def send(self, payload: dict) -> dict | None:
        if not self.enabled:
            return None
        res = await asyncio.to_thread(self._post, payload)
        if res is not None and not res.get("ok"):
            log_hook.warning("охрана отклонила %s: %s", payload.get("action"), res.get("error"))
        return res

    def fire(self, payload: dict) -> None:
        if not self.enabled:
            return
        try:
            task = asyncio.get_running_loop().create_task(self.send(payload))
        except RuntimeError:
            return
        self._tasks.add(task)
        task.add_done_callback(self._tasks.discard)

    def ring_start(self, key, chat_id: int, fighters, mode: str = "group", names=(), ttl: int = 2700) -> None:
        self.fire({"action": "start", "key": str(key), "chat_id": int(chat_id), "mode": mode,
                   "fighters": [int(f) for f in fighters], "names": [str(n)[:40] for n in names], "ttl": int(ttl)})

    def ring_touch(self, key, ttl: int = 2700, chat_id: int | None = None, fighters=(), mode: str = "group",
                   names=()) -> None:
        p = {"action": "touch", "key": str(key), "ttl": int(ttl)}
        if chat_id is not None and fighters:
            p.update(chat_id=int(chat_id), mode=mode, fighters=[int(f) for f in fighters],
                     names=[str(n)[:40] for n in names])
        self.fire(p)

    def ring_end(self, key) -> None:
        self.fire({"action": "end", "key": str(key)})


log_cmds = logging.getLogger("guard.cmds")

COMMAND_NAMES = ("start", "help", "id", "guard", "status", "shift", "ring", "bell", "lockdown", "open",
                 "slow", "warn", "mute", "unmute", "ban", "unban", "forgive", "purge", "vouch", "unvouch", "allow",
                 "disallow", "block", "unblock", "domains", "explain", "report", "stats", "raid",
                 "panel", "admin", "cancel", "rules", "setrules", "welcome", "notes", "addnote", "delnote", "me", "top",
                 "remind", "poll", "roll", "coin",
                 "gban", "ungban", "gbans", "lock", "unlock", "locks", "night", "filter", "stop", "filters",
                 "repeat", "repeats", "unrepeat", "setlog", "newbie", "digest", "copyset", "strict", "spamlist", "forget", "contacts", "safety", "invite", "links", "revoke",
                 "fullguard", "panic", "trace", "autopilot", "ap", "spam", "learn")
PUBLIC = {"start", "help", "id", "report"}

SETTINGS = [("sh", "Модерация", "enabled"), ("cp", "Проверка при входе", "captcha"), ("sc", "Спам", "scam"),
            ("lk", "Ссылки", "links"), ("ht", "Оскорбления и разжигание", "hate"), ("ad", "18+", "adult"), ("pf", "Мат", "profanity"),
            ("fl", "Флуд", "flood"), ("rd", "Антирейд", "raid"), ("rg", "Ограничение записи во время сессий", "ring"),
            ("tr", "Реплики зрителей (arena)", "tribunes"), ("am", "Запись доверенным во время сессии", "admins_in_ring"),
            ("qt", "Тихий режим", "quiet"), ("cj", "Чистить «вошёл/вышел»", "clean_joins"),
            ("sk", "Адаптивная проверка", "captcha_smart"), ("sl", "Расширенный анализ ссылок", "smart_links"),
            ("cs", "Проверка по базе CAS", "cas"),
            ("im", "Защита от подмены админов", "impostor"),
            ("st", "Автовключение строгого режима при спаме", "strict_auto"),
            ("pt", "Постановочные диалоги (кукольный театр)", "puppet"),
            ("sm", "Память о пойманном спаме", "spam_memory"),
            ("ln", "Самообучение: карточки в личку, шаблоны", "learn"),
            ("cf", "Конфликты: провокации и травля", "conflicts"),
            ("jt", "Случайная задержка удаления спама", "jitter"),
            ("fa", "Автовключение полной защиты при волне", "fort_auto"),
            ("ap", "Автопилот: рефлексы по ситуации", "autopilot")]
LINK_LABEL = {"open": "любые", "trusted": "по доверию", "admins": "только админы"}
ACTION_RU = {"none": "пропустить", "watch": "на заметку", "delete": "удалить", "ban": "удалить и забанить"}
TIER_RU = {"new": "новичок", "member": "участник", "veteran": "ветеран"}
REPORT_WEIGHT = {"new": 0.5, "member": 1.0, "veteran": 1.5}
REPORT_LIMIT = 2.5
_DOMAIN_RE = re.compile(r"^[a-z0-9а-я][a-z0-9а-я\-.]{0,60}\.[a-zа-я0-9\-]{2,24}(?:/[\w\-./]{0,60})?$")


def parse_minutes(tok: str):
    m = re.fullmatch(r"(\d{1,5})\s*(м|мин|m|min|ч|h|д|d)?", tok.lower())
    if not m:
        return None
    n, unit = int(m.group(1)), m.group(2) or "м"
    return n * (60 if unit in ("ч", "h") else 1440 if unit in ("д", "d") else 1)


class Commands:
    def __init__(self):
        self.commands = {n: getattr(self, "cmd_" + n) for n in COMMAND_NAMES}
        self._cmd_last: dict[tuple, float] = {}

    async def on_noop(self, *a, **kw):
        return None

    async def on_command(self, message, command) -> None:
        name = (getattr(command, "command", "") or "").lower()
        args = (getattr(command, "args", "") or "").strip()
        fn = self.commands.get(name)
        if fn is None:
            return
        cu = getattr(message, "from_user", None)
        if cu is not None and not self.cmd_allowed(cu.id):
            return
        if getattr(message.chat, "type", "") in GROUP_TYPES and not self.chat_ok(message.chat.id):
            u = getattr(message, "from_user", None)
            if u is None or u.id not in self.owners:
                return
        try:
            await fn(message, args)
        except Exception:
            log_cmds.exception("команда /%s упала", name)

    async def on_callback(self, cb) -> None:
        data = getattr(cb, "data", "") or ""
        who = getattr(cb, "from_user", None)
        if who is not None and who.id in self.banned_env and who.id not in self.owners:
            return await cb.answer()
        cmsg = getattr(cb, "message", None)
        if cmsg is not None and getattr(cmsg.chat, "type", "") in GROUP_TYPES and not self.chat_ok(cmsg.chat.id):
            return await cb.answer()
        try:
            if data.startswith("cp:"):
                return await self.on_captcha_button(cb)
            if data.startswith("gs:"):
                return await self.on_settings_button(cb)
            if data.startswith("rv:"):
                return await self.on_review_button(cb)
            if data.startswith("ap:"):
                return await self.on_panel_button(cb)
            if data.startswith("pl:"):
                return await self.on_poll_button(cb)
            if data.startswith("fg:"):
                return await self.on_fort_button(cb)
            if data.startswith("ag:"):
                return await self.on_ap_button(cb)
            if data.startswith("ln:"):
                return await self.on_learn_button(cb)
        except Exception:
            log_cmds.exception("кнопка %r упала", data)
        await cb.answer()

    def cmd_allowed(self, uid: int) -> bool:
        if uid in self.owners:
            return True
        if uid in self.banned_env:
            return False
        if self.cmd_limit <= 0 or uid in self.trusted:
            return True
        now = self.now()
        h = self._cmd_hist.setdefault(uid, deque(maxlen=64))
        while h and now - h[0] > 20:
            h.popleft()
        if len(h) >= self.cmd_limit:
            return False
        h.append(now)
        if len(self._cmd_hist) > 3000:
            self._cmd_hist = {k: v for k, v in self._cmd_hist.items() if v and now - v[-1] < 60}
        return True

    def _cool(self, chat_id: int, name: str, secs: float) -> bool:
        now = self.now()
        k = (chat_id, name)
        if now - self._cmd_last.get(k, 0) < secs:
            return False
        self._cmd_last[k] = now
        if len(self._cmd_last) > 2000:
            self._cmd_last = {k: t for k, t in self._cmd_last.items() if now - t < 3600}
        return True

    def thread_of(self, m):
        return getattr(m, "message_thread_id", None) if getattr(m, "is_topic_message", False) else None

    async def out(self, m, text: str, ttl: float = 0, markup=None, reply: bool = False):
        extra = {}
        th = self.thread_of(m)
        if th:
            extra["message_thread_id"] = th
        if reply:
            from aiogram.types import ReplyParameters
            extra["reply_parameters"] = ReplyParameters(message_id=m.message_id, allow_sending_without_reply=True)
        sent = await self.call("send_message", m.chat.id, text, reply_markup=markup, disable_notification=True, **extra)
        if sent is not None and ttl:
            self.later(ttl, self.call, "delete_message", m.chat.id, sent.message_id)
        return sent

    async def say(self, m, key: str, ttl: float = 20, **kw):
        return await self.out(m, self.voice.say(key, **kw), ttl=ttl)

    def in_group(self, m) -> bool:
        return getattr(m.chat, "type", "") in GROUP_TYPES

    async def sender_is_admin(self, m) -> bool:
        u = getattr(m, "from_user", None)
        return u is not None and await self.is_admin(m.chat.id, u.id)

    @staticmethod
    def is_anon_sender(m) -> bool:
        sc = getattr(m, "sender_chat", None)
        u = getattr(m, "from_user", None)
        return (sc is not None and sc.id == m.chat.id) or (u is not None and u.id == ANON_ADMIN_ID)

    async def need_admin(self, m) -> bool:
        if not self.in_group(m):
            await self.out(m, "Эта команда работает в группе.", ttl=0)
            return False
        if await self.sender_is_admin(m):
            return True
        if self.is_anon_sender(m):
            await self.out(m, "Команда отправлена анонимно: личность не определена. Отключите «Оставаться анонимным» "
                              "в правах администратора и повторите.", ttl=20)
        else:
            await self.say(m, "need_admin", ttl=10)
        self.deleter.add(m.chat.id, [m.message_id])
        return False

    def cleanup(self, m) -> None:
        self.deleter.add(m.chat.id, [m.message_id])

    async def resolve_all(self, m, args: str) -> tuple[list, int]:
        out, missing = [], 0
        r = getattr(m, "reply_to_message", None)
        ru = getattr(r, "from_user", None) if r is not None else None
        if ru is not None and ru.id != ANON_ADMIN_ID and not (ru.is_bot and ru.id == self.me_id):
            out.append((ru.id, ru.full_name if hasattr(ru, "full_name") else str(ru.id)))
        names = self.store.chat(m.chat.id).names
        for tok in args.split():
            tok = tok.strip(",;")
            if tok.startswith("@") and len(tok) > 1:
                uid = names.get(tok[1:].lower())
                if uid is None:
                    missing += 1
                elif all(uid != u for u, _ in out):
                    out.append((uid, tok))
            elif tok.lstrip("-").isdigit() and len(tok.lstrip("-")) >= 6:
                uid = int(tok)
                if all(uid != u for u, _ in out):
                    out.append((uid, tok))
        return out, missing

    async def one_target(self, m, args: str, allow_admin: bool = False):
        found, missing = await self.resolve_all(m, args)
        if not found:
            await self.say(m, "unknown_user" if (missing or args) else "need_reply", ttl=15)
            return None
        uid, label = found[0]
        if not allow_admin and (uid in await self.admins(m.chat.id) or uid in self.owners or uid == self.me_id):
            await self.say(m, "target_admin", ttl=10)
            return None
        return uid, label

    async def cmd_start(self, m, args):
        if getattr(m.chat, "type", "") == "private":
            self.store.alert_users.add(m.from_user.id)
            self.store.dirty = True
            await self.out(m, HELP_PRIVATE)
            if m.from_user.id in self.owners:
                await self.out(m, "Вы указаны в списке владельцев. /panel — все чаты, сводка и рассылка.")
        elif self._cool(m.chat.id, "start", 30):
            await self.out(m, HELP_USER, ttl=120)

    async def cmd_help(self, m, args):
        if not self._cool(m.chat.id, "help", 20):
            return
        text = HELP_USER
        if self.in_group(m) and await self.sender_is_admin(m):
            text += "\n\n" + HELP_ADMIN
        await self.out(m, text, ttl=0 if getattr(m.chat, "type", "") == "private" else 180)

    async def cmd_id(self, m, args):
        r = getattr(m, "reply_to_message", None)
        uid = (r.from_user.id if r is not None and r.from_user else m.from_user.id)
        text = f"id: <code>{uid}</code>"
        if self.in_group(m):
            text += f"\nчат: <code>{m.chat.id}</code>"
        await self.out(m, text, ttl=60 if self.in_group(m) else 0)

    def panel(self, chat_id: int):
        from aiogram.types import InlineKeyboardButton, InlineKeyboardMarkup
        st = self.store.chat(chat_id)
        cfg = st.cfg
        rows, row = [], []
        for code, label, attr in SETTINGS:
            if attr == "links":
                txt = f"🔗 Ссылки: {LINK_LABEL.get(cfg.links, cfg.links)}"
            else:
                txt = ("🟢 " if getattr(cfg, attr) else "⚪ ") + label
            row.append(InlineKeyboardButton(text=txt, callback_data=f"gs:{chat_id}:{code}"))
            if len(row) == 2:
                rows.append(row)
                row = []
        if row:
            rows.append(row)
        rows.append([InlineKeyboardButton(text=("🛡 Полная защита: ВКЛ — выключить" if cfg.fort_on else "🛡 Включить полную защиту"),
                                          callback_data=f"fg:tg:{chat_id}")])
        rows.append([InlineKeyboardButton(text="✖ Закрыть", callback_data=f"gs:{chat_id}:x")])
        text = (f"<b>Настройки модерации</b>\n<i>{esc(st.title, 60)}</i>\n🟢 включено · ⚪ выключено\n"
                "Подробности — /status, команды — /help.")
        return text, InlineKeyboardMarkup(inline_keyboard=rows)

    async def cmd_guard(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        text, kb = self.panel(m.chat.id)
        await self.out(m, text, markup=kb, ttl=600)

    async def on_settings_button(self, cb) -> None:
        try:
            _, cid, code = cb.data.split(":")
            cid = int(cid)
        except ValueError:
            return await cb.answer()
        msg = getattr(cb, "message", None)
        if msg is None or msg.chat.id != cid:
            return await cb.answer()
        if not await self.is_admin(cid, cb.from_user.id):
            return await cb.answer("Только для владельца.", show_alert=False)
        if code == "x":
            self.deleter.add(cid, [msg.message_id])
            return await cb.answer()
        cfg = self.store.chat(cid).cfg
        for c, label, attr in SETTINGS:
            if c != code:
                continue
            if attr == "links":
                i = LINK_POLICIES.index(cfg.links) if cfg.links in LINK_POLICIES else 1
                cfg.links = LINK_POLICIES[(i + 1) % len(LINK_POLICIES)]
            else:
                setattr(cfg, attr, not getattr(cfg, attr))
            self.store.dirty = True
            text, kb = self.panel(cid)
            await self.call("edit_message_text", text, chat_id=cid, message_id=msg.message_id, reply_markup=kb)
            break
        await cb.answer()

    async def cmd_status(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cid = m.chat.id
        st = self.store.chat(cid)
        cfg, now = st.cfg, self.now()
        rights = await self.rights(cid)
        rings = self.eng.rings.active(cid, now)
        raid_left = self.eng.raid_until.get(cid, 0) - now
        yes = lambda b: "вкл" if b else "выкл"
        lines = [f"<b>Состояние: {esc(st.title, 60)}</b>",
                 f"Модерация: {'включена' if cfg.enabled else 'отключена (/shift on)'}",
                 f"Права: удалять — {'да' if rights['delete'] else 'НЕТ'}, ограничивать — {'да' if rights['restrict'] else 'НЕТ'}",
                 f"Пропуск: {yes(cfg.captcha)} ({cfg.captcha_timeout} с) · спам: {yes(cfg.scam)} · флуд: {yes(cfg.flood)}",
                 f"Ссылки: {LINK_LABEL.get(cfg.links, cfg.links)} · оскорбления: {yes(cfg.hate)} · 18+: {yes(cfg.adult)} · мат: {yes(cfg.profanity)}",
                 f"Медленный режим: {cfg.slow} с" if cfg.slow else "Медленный режим: выкл"]
        if rings:
            for r in rings:
                lines.append(f"Сейчас: {r.mode} «{esc(', '.join(r.names) or '—', 60)}», ещё {human_dur(r.expires - now)}")
        else:
            lines.append("Активных сессий и закрытий нет")
        if raid_left > 0:
            lines.append(f"Режим наплыва: ещё {human_dur(raid_left)}")
        lines.append(f"Разрешённых доменов: {len(cfg.allow)} · запрещённых: {len(cfg.block)} · участников в памяти: {len(st.users)}")
        night = f"{cfg.night} ({cfg.night_mode})" if cfg.night else "выкл"
        lines.append(f"CAS: {yes(cfg.cas and self.cas_on)} · замков: {len(cfg.locks)} · автоответов: {len(cfg.filters)} · ночь: {night}"
                     f" · журнал: {'есть' if (cfg.logchat or self.log_chat_env) else 'нет'}")
        newbie = human_dur(cfg.newbie_min * 60) if cfg.newbie_min else "выкл"
        digest = f"{cfg.digest_hour:02d}:00" if cfg.digest_hour >= 0 else "выкл"
        lines.append(f"Подмена админов: {yes(cfg.impostor)} · режим новичка: {newbie} · дайджест: {digest}")
        s_left = self.eng.strict_left(cid, now)
        lines.append("Строгий режим: " + (f"включён, ещё {human_dur(s_left)}" if s_left > 0 else "выкл")
                     + f" · автовключение при спаме: {yes(cfg.strict_auto and self.eng.strict_auto_on)}")
        if cfg.fort_on:
            f_left = "без срока" if not cfg.fort_until else f"ещё {human_dur(max(0.0, cfg.fort_until - now))}"
            lines.append(f"Полная защита: включена ({'сама' if cfg.fort_origin == 'auto' else 'вручную'}), {f_left} · угроза: "
                         f"{self.eng.radar_level(cid, now)[2]} {self.eng.radar_level(cid, now)[1]}")
        else:
            lines.append(f"Полная защита: выкл · автовключение при волне: {yes(cfg.fort_auto and self.eng.fort_auto_on)}"
                         f" · радар: {self.eng.radar_level(cid, now)[2]} {self.eng.radar_level(cid, now)[1]}")
        lines.append(f"Следопыт: {({'on': 'вкл', 'log': 'наблюдение', 'off': 'выкл'}).get(cfg.trace, cfg.trace)}"
                     f"{'' if self.eng.trace_on else ' (в настройках бота выключен)'} · решений в журнале: "
                     f"{len(self.eng.tr_log.get(cid) or ())}")
        lines.append(f"Кукольный театр (постановочные диалоги): {yes(cfg.puppet and self.eng.puppet_on)}")
        lines.append(f"Память о пойманном спаме: {yes(cfg.spam_memory and self.eng.memory_on)}")
        lines.append(f"Самообучение (карточки в личку): {yes(cfg.learn and self.eng.learn_on)} · выученных шаблонов спама: {self.eng.learn_spam_count()}")
        lines.append(f"Конфликты (журнал провокаций и травли): {yes(cfg.conflicts and self.eng.conflicts_on)}"
                     f" · задержка удаления пограничного спама: {yes(cfg.jitter and self.eng.jitter_on)}")
        lines.append(self.ap_status_line(cid, now))
        await self.out(m, "\n".join(lines), ttl=120)

    async def cmd_stats(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        st = self.store.chat(m.chat.id)
        days = sorted(st.stats)[-3:]
        if not days:
            return await self.out(m, "Данных для статистики нет.", ttl=30)
        total: dict[str, int] = {}
        for d in days:
            for k, v in st.stats[d].items():
                total[k] = total.get(k, 0) + v
        lines = [f"<b>За последние {len(days)} дн.</b>"]
        for k, v in sorted(total.items(), key=lambda kv: -kv[1]):
            lines.append(f"• {STAT_LABELS.get(k, k)}: {v}")
        await self.out(m, "\n".join(lines), ttl=120)

    async def cmd_shift(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        a = args.lower().strip()
        if a in ("on", "вкл", "1"):
            cfg.enabled = True
        elif a in ("off", "выкл", "0"):
            cfg.enabled = False
        else:
            return await self.out(m, "Модерация: " + ("включена" if cfg.enabled else "отключена") + ". /shift on|off", ttl=20)
        self.store.dirty = True
        await self.say(m, "shift_on" if cfg.enabled else "shift_off", ttl=0)

    async def cmd_raid(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        on = args.lower().strip() in ("on", "вкл", "1")
        if args.lower().strip() not in ("on", "вкл", "1", "off", "выкл", "0"):
            return await self.out(m, "/raid on|off", ttl=15)
        self.eng.raid_set(m.chat.id, on, self.now())
        await self.say(m, "raid_on" if on else "raid_off", ttl=120, mins=human_dur(RAID_HOLD))

    async def cmd_slow(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        a = args.lower().strip()
        if a in ("off", "выкл", "0", ""):
            cfg.slow = 0
        elif a.isdigit():
            cfg.slow = max(3, min(int(a), 3600))
        else:
            return await self.out(m, "/slow 10 — раз в 10 с; /slow off — выключить", ttl=20)
        self.store.dirty = True
        await self.say(m, "slow_on" if cfg.slow else "slow_off", ttl=30, s=cfg.slow)

    async def cmd_ring(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        found, _ = await self.resolve_all(m, args)
        mins = next((x for x in (parse_minutes(t) for t in args.split() if not t.startswith("@")) if x), 20)
        mins = max(1, min(mins, 120))
        if len(found) < 2:
            return await self.say(m, "ring_need_two", ttl=25)
        ids = [u for u, _ in found][:6]
        names = [n.lstrip("@") for _, n in found][:6]
        key = f"manual:{m.chat.id}:" + "-".join(str(i) for i in ids)
        self.eng.ring_start(m.chat.id, key, "manual", ids, names, ttl=mins * 60, now=self.now())
        if not self.store.chat(m.chat.id).cfg.quiet:
            await self.say(m, "ring_start", ttl=0, names=", ".join(esc(n, 24) for n in names), mins=human_dur(mins * 60))

    async def cmd_bell(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        gone = self.eng.ring_end_chat(m.chat.id, ("group", "arena", "manual"))
        if gone:
            await self.say(m, "ring_end", ttl=60)
        else:
            await self.say(m, "ring_none", ttl=10)

    async def cmd_lockdown(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        mins = max(1, min(parse_minutes(args.split()[0]) if args.split() and parse_minutes(args.split()[0]) else 15, 120))
        self.eng.ring_start(m.chat.id, f"lock:{m.chat.id}", "lockdown", (), (), ttl=mins * 60, now=self.now())
        await self.say(m, "lockdown_on", ttl=0, mins=human_dur(mins * 60))

    async def cmd_open(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        if self.eng.ring_end_chat(m.chat.id, ("lockdown",)):
            await self.say(m, "lockdown_off", ttl=60)

    async def cmd_warn(self, m, args):
        if not await self.need_admin(m):
            return
        t = await self.one_target(m, args)
        self.cleanup(m)
        if t is None:
            return
        uid, label = t
        level, mute = self.eng.add_strike(m.chat.id, uid, 1.0, "warn", self.now())
        if mute:
            await self.restrict(m.chat.id, uid, mute)
        await self.say(m, "warned_manual", ttl=60, name=mention(uid, label))

    async def cmd_mute(self, m, args):
        if not await self.need_admin(m):
            return
        t = await self.one_target(m, args)
        self.cleanup(m)
        if t is None:
            return
        uid, label = t
        mins = next((x for x in (parse_minutes(tok) for tok in args.split() if not tok.startswith("@")
                                 and len(tok.lstrip("-")) < 6) if x), 60)
        secs = max(60, min(mins * 60, 7 * 86400))
        await self.restrict(m.chat.id, uid, secs)
        rec = self.store.user(self.store.chat(m.chat.id), uid, self.now())
        rec.muted_until = max(rec.muted_until, self.now() + secs)
        self.store.dirty = True
        await self.say(m, "muted_manual", ttl=60, name=mention(uid, label), dur=human_dur(secs))

    async def cmd_unmute(self, m, args):
        if not await self.need_admin(m):
            return
        t = await self.one_target(m, args, allow_admin=True)
        self.cleanup(m)
        if t is None:
            return
        uid, label = t
        rec = self.store.user(self.store.chat(m.chat.id), uid, self.now())
        rec.muted_until, rec.banned = 0.0, False
        self.store.dirty = True
        self.eng.note_overturn(m.chat.id, uid)
        await self.unrestrict(m.chat.id, uid)
        await self.say(m, "unmuted", ttl=40, name=mention(uid, label))

    async def cmd_ban(self, m, args):
        if not await self.need_admin(m):
            return
        t = await self.one_target(m, args)
        self.cleanup(m)
        if t is None:
            return
        uid, label = t
        secs = next((x * 60 for x in (parse_minutes(tok) for tok in args.split()) if x), 0)
        kw = {"until_date": int(self.now() + max(35, secs))} if secs else {}
        await self.call("ban_chat_member", m.chat.id, uid, **kw)
        rec = self.store.user(self.store.chat(m.chat.id), uid, self.now())
        if secs and secs < 366 * 86400:
            rec.muted_until = max(rec.muted_until, self.now() + max(35, secs))
        else:
            rec.banned = True
        self.store.dirty = True
        await self.say(m, "banned_manual", ttl=60, name=mention(uid, label))
        await self.lp_after_ban(m, uid)
        if secs:
            await self.out(m, f"Бан на {human_dur(secs)}: потом участник сможет вернуться.", ttl=40)

    async def cmd_unban(self, m, args):
        if not await self.need_admin(m):
            return
        t = await self.one_target(m, args, allow_admin=True)
        self.cleanup(m)
        if t is None:
            return
        uid, label = t
        await self.call("unban_chat_member", m.chat.id, uid, only_if_banned=True)
        rec = self.store.user(self.store.chat(m.chat.id), uid, self.now())
        rec.banned, rec.muted_until = False, 0.0
        self.eng.spam_memory_drop_user(m.chat.id, uid)
        self.eng.note_overturn(m.chat.id, uid)
        self.store.dirty = True
        await self.say(m, "unbanned", ttl=40, name=mention(uid, label))

    async def cmd_forgive(self, m, args):
        if not await self.need_admin(m):
            return
        t = await self.one_target(m, args, allow_admin=True)
        self.cleanup(m)
        if t is None:
            return
        uid, label = t
        self.eng.forgive(m.chat.id, uid)
        await self.unrestrict(m.chat.id, uid)
        await self.say(m, "forgiven", ttl=40, name=mention(uid, label))

    async def cmd_purge(self, m, args):
        if not await self.need_admin(m):
            return
        t = await self.one_target(m, args)
        self.cleanup(m)
        if t is None:
            return
        uid, _ = t
        mins = next((x for x in (parse_minutes(tok) for tok in args.split() if not tok.startswith("@")
                                 and len(tok.lstrip("-")) < 6) if x), 30)
        ids = self.eng.recent_ids(m.chat.id, uid, within=min(mins, 1440) * 60, now=self.now())
        r = getattr(m, "reply_to_message", None)
        if r is not None:
            ids.append(r.message_id)
        ids = sorted(set(ids))
        if ids:
            self.deleter.add(m.chat.id, ids)
        await self.say(m, "purged", ttl=20, n=len(ids))

    async def cmd_vouch(self, m, args):
        await self._vouch(m, args, True)

    async def cmd_unvouch(self, m, args):
        await self._vouch(m, args, False)

    async def _vouch(self, m, args, on: bool):
        if not await self.need_admin(m):
            return
        t = await self.one_target(m, args, allow_admin=True)
        self.cleanup(m)
        if t is None:
            return
        uid, label = t
        self.store.user(self.store.chat(m.chat.id), uid, self.now()).vouched = on
        self.store.dirty = True
        await self.say(m, "vouched" if on else "unvouched", ttl=40, name=mention(uid, label))

    def _domain_arg(self, args: str) -> str:
        d = (args.split() or [""])[0].strip().lower()
        d = re.sub(r"^[a-z]+://", "", d)
        d = re.sub(r"^www\.", "", d).rstrip("/")
        return d if _DOMAIN_RE.match(d) else ""

    async def _list_edit(self, m, args, which: str, add: bool):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        d = self._domain_arg(args)
        if not d:
            return await self.say(m, "bad_domain", ttl=20)
        lst = getattr(self.store.chat(m.chat.id).cfg, which)
        if add and d not in lst and len(lst) < 100:
            lst.append(d)
        elif not add and d in lst:
            lst.remove(d)
        self.store.dirty = True
        key = {("allow", True): "allow_added", ("allow", False): "allow_removed", ("block", True): "block_added",
               ("block", False): "block_removed"}[(which, add)]
        await self.say(m, key, ttl=30, domain=esc(d, 80))

    async def cmd_allow(self, m, args):
        await self._list_edit(m, args, "allow", True)

    async def cmd_disallow(self, m, args):
        await self._list_edit(m, args, "allow", False)

    async def cmd_block(self, m, args):
        await self._list_edit(m, args, "block", True)

    async def cmd_unblock(self, m, args):
        await self._list_edit(m, args, "block", False)

    async def cmd_domains(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        fmt = lambda xs: ", ".join(esc(x, 60) for x in xs) or "—"
        await self.out(m, f"<b>Разрешены везде:</b> {fmt(DEFAULT_ALLOW)}\n<b>Добавлены вами:</b> {fmt(cfg.allow)}\n"
                          f"<b>Запрещены:</b> {fmt(cfg.block)}", ttl=120)

    async def cmd_explain(self, m, args):
        if not await self.need_admin(m):
            return
        r = getattr(m, "reply_to_message", None)
        text = args or ((getattr(r, "text", None) or getattr(r, "caption", None) or "") if r is not None else "")
        if not text:
            return await self.out(m, "/explain <i>текст</i> — или ответом на сообщение. Я ничего не удаляю, только объясняю.", ttl=30)
        ents = to_msg(r).ents if (r is not None and not args) else []
        res = self.eng.explain(text[:1500], m.chat.id, ents)
        lines = ["<b>Разбор</b>"]
        for name, w, why in sorted(res["signals"], key=lambda s: -s[1])[:8]:
            lines.append(f"• +{w:g} — {esc(why, 90)}")
        if not res["signals"]:
            lines.append("• сигналов нет")
        found = [k for k, v in res["found"].items() if v and k != "minor"]
        if found:
            lines.append("• слова: " + ", ".join(found))
        for u in res["urls"][:3]:
            lines.append(f"• ссылка: {esc(u.host, 60)} ({u.kind}{', ' + '/'.join(sorted(u.flags)) if u.flags else ''})")
        for s in res.get("learned") or ():
            lines.append(f"• 🧠 {esc(s, 160)} (в оценку выше это не входит)")
        lines.append("")
        for tier, (eff, act) in res["tiers"].items():
            lines.append(f"{TIER_RU[tier]}: {eff:g} → {ACTION_RU[act]}")
        lines.append("<i>Ссылки, флуд и списки — отдельно от этой оценки.</i>")
        await self.out(m, "\n".join(lines), ttl=180)

    async def cmd_report(self, m, args):
        if not self.in_group(m):
            return
        self.cleanup(m)
        u = getattr(m, "from_user", None)
        r = getattr(m, "reply_to_message", None)
        if u is None:
            return
        if r is None or (r.from_user is None and getattr(r, "sender_chat", None) is None):
            return await self.say(m, "report_need_reply", ttl=12)
        target = r.from_user
        if target is not None and target.id == u.id:
            return await self.say(m, "report_self", ttl=10)
        if target is not None and (target.is_bot or target.id in await self.admins(m.chat.id)):
            return
        now = self.now()
        hist = self.report_rate.setdefault(u.id, [])
        hist[:] = [t for t in hist if now - t < 600]
        if len(hist) >= 5:
            return
        hist.append(now)
        state = self.store.chat(m.chat.id)
        admin = await self.sender_is_admin(m)
        rec = self.store.user(state, u.id, now)
        weight = 3.0 if admin else REPORT_WEIGHT[self.eng.tier(rec, now)]
        conflict = False
        if not admin and target is not None and self.eng.talk_between(m.chat.id, u.id, target.id, now, REPORT_CONFLICT_WINDOW):
            weight, conflict = 0.0, True
        key = (m.chat.id, r.message_id)
        rep = self.reports.setdefault(key, {"by": {}, "t": now, "uid": target.id if target else 0,
                                            "name": (target.full_name if target else "канал")})
        if u.id in rep["by"]:
            return await self.say(m, "report_dup", ttl=8)
        rep["by"][u.id] = weight
        if conflict:
            rep["conflict"] = rep.get("conflict", 0) + 1
        self.store.bump(state, "reports", now=now)
        eff, linked = self.eng.report_effective(m.chat.id, rep["by"], now)
        solid = any(w >= 1.0 for w in rep["by"].values())
        notes = []
        if rep.get("conflict"):
            notes.append("жалуется тот, кто недавно переписывался с автором")
        if linked:
            notes.append("часть жалобщиков общается между собой")
        if len(rep["by"]) >= 3 and now - rep["t"] <= 300:
            notes.append("несколько жалоб за считанные минуты")
        if eff >= REPORT_LIMIT and not solid:
            notes.append("все жалобщики — новички")
        rep["note"] = "; ".join(notes)
        if eff >= REPORT_LIMIT and solid:
            self.deleter.add(m.chat.id, [r.message_id])
            if target is not None and self.eng.report_strikes_recent(m.chat.id, target.id, now) < REPORT_STRIKE_CAP:
                self.eng.add_strike(m.chat.id, target.id, 0.8, "report", now)
            self.reports.pop(key, None)
            return await self.say(m, "report_removed", ttl=25)
        if eff >= REPORT_LIMIT:
            self.store.bump(state, "report_blocked", now=now)
        await self.say(m, "report_ack", ttl=10)
        await self._send_review(m, r, rep)

    async def _send_review(self, m, r, rep: dict) -> None:
        from aiogram.types import InlineKeyboardButton, InlineKeyboardMarkup
        cid, mid, uid = m.chat.id, r.message_id, rep["uid"]
        base = f"rv:{cid}:{mid}:{uid}:"
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="🗑 Удалить", callback_data=base + "d"),
            InlineKeyboardButton(text="🔇 Удалить и мут 1 ч", callback_data=base + "m"),
            InlineKeyboardButton(text="✖ Отклонить", callback_data=base + "x")]])
        link = msg_link(m.chat, mid)
        text = (f"Жалоба в «{esc(m.chat.title, 60)}»\nНа: {mention(uid, rep['name'])}\n"
                + (f'<a href="{link}">Перейти к сообщению</a>' if link else ""))
        if rep.get("note"):
            text += f"\n⚠ {esc(rep['note'], 200)}. Решайте сами."
        if await self.alert(cid, text, kb) == 0:
            await self.out(m, f"Жалоба на сообщение {mention(uid, rep['name'])}. Решение за администраторами.", markup=kb, ttl=600)

    async def on_review_button(self, cb) -> None:
        try:
            _, cid, mid, uid, act = cb.data.split(":")
            cid, mid, uid = int(cid), int(mid), int(uid)
        except ValueError:
            return await cb.answer()
        if not await self.is_admin(cid, cb.from_user.id):
            return await cb.answer("Только для владельца.", show_alert=False)
        done = "Отклонено."
        if act in ("d", "m"):
            self.deleter.add(cid, [mid])
            self.eng.add_strike(cid, uid, 0.8, "report", self.now())
            done = "Удалено."
            if act == "m" and uid > 0 and uid not in await self.admins(cid):
                await self.restrict(cid, uid, 3600)
                self.store.user(self.store.chat(cid), uid, self.now()).muted_until = self.now() + 3600
                done = "Удалено, участник на час в тишине."
        self.reports.pop((cid, mid), None)
        msg = getattr(cb, "message", None)
        if msg is not None:
            await self.call("edit_message_text", f"{done} ({esc(getattr(cb.from_user, 'full_name', ''), 30)})",
                            chat_id=msg.chat.id, message_id=msg.message_id)
        await cb.answer(done)


log_extra = logging.getLogger("guard.extra")

VERSION = "5.0"
TZ_HOURS_DEFAULT = 3
NOTE_NAME_RE = re.compile(r"^[a-zа-яе0-9_]{1,24}$")
NOTE_MAX, NOTES_MAX = 1200, 40
RULES_MAX, WELCOME_MAX = 1500, 400
REMIND_PER_USER, REMIND_MAX_MIN = 3, 7 * 1440
POLL_MAX_ACTIVE, POLL_HOURS, POLL_KEEP = 3, 24, 3600
PANEL_PAGE, PANEL_INPUT_TTL, PANEL_BC_DELAY = 8, 300, 0.05


def norm_note(tok: str) -> str:
    return tok.strip().lower().replace("ё", "е").lstrip("#")


def fmt_uptime(sec: float) -> str:
    sec = int(max(0, sec))
    d, r = divmod(sec, 86400)
    h, r = divmod(r, 3600)
    mnt = r // 60
    if d:
        return f"{d} д {h} ч"
    if h:
        return f"{h} ч {mnt} мин"
    return f"{mnt} мин"


def parse_ids(raw: str) -> set:
    out = set()
    for tok in re.split(r"[\s,;]+", raw or ""):
        if tok.isdigit() and int(tok) > 0:
            out.add(int(tok))
    return out


class Extras:
    def init_extras(self) -> None:
        self.owners: set = set()
        self.tz_h: int = TZ_HOURS_DEFAULT
        self.store.tz_h = self.tz_h
        self._pending: dict = {}
        self._names: dict = {}
        self._greeted: dict = {}
        self.started: float = self.now()
        self.panel_hash = None
        self.panel_ttl: float = 1800.0
        self.panel_tries: int = 6
        self._unlocked: dict = {}
        self._guesses: dict = {}
        self._lockout: dict = {}
        self.allowed_env: set = set()
        self.strict_add: bool = False
        self.notify_adds: bool = True
        self.notify_removals: bool = True
        self.captcha_ban_default: int = 15
        self.captcha_min_react: float = 0.0
        self._leaving: set = set()
        self._add_seen: dict = {}
        self.trusted: set = set()
        self.banned_env: set = set()
        self.trust_tg_admins: bool = False
        self.cmd_limit: int = 8
        self._cmd_hist: dict = {}

    @staticmethod
    def _human(u) -> bool:
        return u is not None and not getattr(u, "is_bot", False) and u.id != ANON_ADMIN_ID and u.id > 0

    def _who(self, m) -> str:
        u = m.from_user
        return mention(u.id, user_name(u)) if u is not None else "аноним"

    def _text_arg(self, m, args: str) -> str:
        if args:
            return args.strip()
        r = getattr(m, "reply_to_message", None)
        if r is not None:
            return (getattr(r, "text", None) or getattr(r, "caption", None) or "").strip()
        return ""

    async def announce(self, chat_id: int, text: str, ttl: float = 60, reply_to: int | None = None):
        extra = {}
        if reply_to:
            from aiogram.types import ReplyParameters
            extra["reply_parameters"] = ReplyParameters(message_id=reply_to, allow_sending_without_reply=True)
        sent = await self.call("send_message", chat_id, text, disable_notification=True, **extra)
        if sent is not None and ttl:
            self.later(ttl, self.call, "delete_message", chat_id, sent.message_id)
        return sent

    async def after_message(self, m, msg, state, uid: int, name: str, human: bool) -> None:
        cfg = state.cfg
        if not cfg.enabled or msg.edited or not msg.text:
            return
        if self.eng.rings.active(msg.chat_id, msg.ts):
            return
        if msg.text.startswith("#"):
            if await self._note_trigger(m, state, msg.text):
                return
        await self.plus_filters(m, state, msg.text)

    async def _note_trigger(self, m, state, text: str) -> bool:
        t = text.strip().lower().replace("ё", "е")
        if " " in t or len(t) > 25:
            return False
        key = t[1:]
        note = state.cfg.notes.get(key)
        if not note:
            return False
        if self._cool(state.chat_id, "note:" + key, 20):
            await self.announce(state.chat_id, f"<b>#{esc(key, 24)}</b>\n{esc(note, NOTE_MAX)}", ttl=180,
                                reply_to=m.message_id)
        return True

    async def greet(self, chat_id: int, uid: int, name: str) -> None:
        state = self.store.chat(chat_id, create=False)
        if state is None or not state.cfg.welcome or state.cfg.quiet or not state.cfg.enabled:
            return
        now = self.now()
        if now - self._greeted.get((chat_id, uid), 0) < 6 * 3600:
            return
        self._greeted[(chat_id, uid)] = now
        if len(self._greeted) > 3000:
            self._greeted = {k: t for k, t in self._greeted.items() if now - t < 6 * 3600}
        text = esc(state.cfg.welcome, WELCOME_MAX).replace("{name}", mention(uid, name))
        if state.cfg.rules:
            text += "\n<i>Правила — /rules.</i>"
        await self.announce(chat_id, text, ttl=90)

    async def cmd_rules(self, m, args):
        if not self.in_group(m):
            return await self.out(m, "Правила доступны в группах.")
        if not self._cool(m.chat.id, "rules", 15):
            return
        cfg = self.store.chat(m.chat.id, m.chat.title or "").cfg
        if cfg.rules:
            await self.out(m, f"<b>📜 Правила</b>\n{esc(cfg.rules, RULES_MAX)}", ttl=240)
        else:
            await self.out(m, "Правил пока нет. Задать: /setrules <i>текст</i>.", ttl=30)

    async def cmd_setrules(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        t = self._text_arg(m, args)
        if not t:
            return await self.out(m, "/setrules <i>текст</i> — или ответом на сообщение с текстом. /setrules off — убрать.", ttl=30)
        if t.lower() in ("off", "выкл", "0"):
            cfg.rules, note = "", "Правила убраны."
        else:
            cfg.rules, note = t[:RULES_MAX], "Правила записаны. Показать — /rules."
        self.store.dirty = True
        await self.out(m, note, ttl=20)

    async def cmd_welcome(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        t = self._text_arg(m, args)
        if not t:
            cur = esc(cfg.welcome, WELCOME_MAX) if cfg.welcome else "не задано"
            return await self.out(m, f"<b>Приветствие:</b> {cur}\n/welcome <i>текст</i> — задать ({{name}} — имя новичка), "
                                     "/welcome off — убрать.", ttl=40)
        if t.lower() in ("off", "выкл", "0"):
            cfg.welcome, note = "", "Приветствие убрано."
        else:
            cfg.welcome, note = t[:WELCOME_MAX], "Приветствие записано. Будет показано новичкам после проверки."
        self.store.dirty = True
        await self.out(m, note, ttl=20)

    async def cmd_notes(self, m, args):
        if not self.in_group(m):
            return await self.out(m, "Заметки доступны в группах.")
        if not self._cool(m.chat.id, "notes", 8):
            return
        cfg = self.store.chat(m.chat.id, m.chat.title or "").cfg
        toks = args.split()
        if toks:
            key = norm_note(toks[0])
            note = cfg.notes.get(key)
            if note:
                return await self.out(m, f"<b>#{esc(key, 24)}</b>\n{esc(note, NOTE_MAX)}", ttl=180)
            return await self.out(m, "Такой заметки нет. Список — /notes.", ttl=15)
        if not cfg.notes:
            return await self.out(m, "Заметок пока нет. Добавить: /addnote <i>имя текст</i>.", ttl=30)
        names = " ".join("#" + esc(k, 24) for k in sorted(cfg.notes))
        await self.out(m, f"<b>Заметки</b>\n{names}\n<i>Просмотр: #имя или /notes имя.</i>", ttl=120)

    async def cmd_addnote(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        key, _, body = args.strip().partition(" ")
        key = norm_note(key)
        body = body.strip() or self._text_arg(m, "")
        if not NOTE_NAME_RE.match(key) or not body:
            return await self.out(m, "/addnote <i>имя текст</i> — или ответом на сообщение: /addnote <i>имя</i>. "
                                     "Имя: до 24 букв, цифр и _.", ttl=30)
        if key not in cfg.notes and len(cfg.notes) >= NOTES_MAX:
            return await self.out(m, f"Заметок уже {NOTES_MAX}: удалите лишние (/delnote).", ttl=20)
        cfg.notes[key] = body[:NOTE_MAX]
        self.store.dirty = True
        await self.out(m, f"Заметка #{esc(key, 24)} сохранена.", ttl=20)

    async def cmd_delnote(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        key = norm_note(args.split()[0]) if args.split() else ""
        if key in cfg.notes:
            cfg.notes.pop(key)
            self.store.dirty = True
            return await self.out(m, f"Заметка #{esc(key, 24)} удалена.", ttl=20)
        await self.out(m, "/delnote <i>имя</i>. Список — /notes.", ttl=20)

    async def cmd_me(self, m, args):
        if not self.in_group(m):
            return await self.out(m, "Карточки доступны в группах.")
        if m.from_user is None or not self._cool(m.chat.id, f"me:{m.from_user.id}", 10):
            return
        now = self.now()
        st = self.store.chat(m.chat.id, m.chat.title or "")
        r = getattr(m, "reply_to_message", None)
        ru = getattr(r, "from_user", None) if r is not None else None
        own = ru is None or ru.id == m.from_user.id
        target = m.from_user if own else ru
        if getattr(target, "is_bot", False):
            return await self.out(m, "Карточка недоступна: участник является ботом.", ttl=15)
        if not own and target.id not in st.users:
            return await self.out(m, "Участник не найден в базе бота.", ttl=15)
        rec = self.store.user(st, target.id, now)
        since = rec.joined or rec.first_seen or now
        days = max(0, int((now - since) // 86400))
        lines = [f"<b>Карточка участника: {mention(target.id, user_name(target))}</b>",
                 f"Уровень: <b>{rank_of(rec.clean)}</b>",
                 f"Статус: {TIER_RU[self.eng.tier(rec, now)]} · в чате {days} {plural(days, 'день', 'дня', 'дней')}",
                 f"Сообщений без нарушений: {rec.clean}"]
        if own:
            lvl = sum(1 for s in rec.strikes if now - s[0] < 86400)
            lines.append("Нарушений за сутки: " + (str(lvl) if lvl else "нет"))
        await self.out(m, "\n".join(lines), ttl=120)

    async def display_name(self, chat_id: int, uid: int) -> str:
        now = self.now()
        hit = self._names.get((chat_id, uid))
        if hit and now - hit[0] < 6 * 3600:
            return hit[1]
        mem = await self.call("get_chat_member", chat_id, uid)
        name = user_name(getattr(mem, "user", None)) or f"участник {uid}"
        if len(self._names) > 1000:
            self._names.clear()
        self._names[(chat_id, uid)] = (now, name)
        return name

    async def cmd_top(self, m, args):
        if not self.in_group(m) or not self._cool(m.chat.id, "top", 60):
            return
        st = self.store.chat(m.chat.id, m.chat.title or "")
        people = [(u, r) for u, r in st.users.items() if u > 0]
        by_clean = sorted(((r.clean, u) for u, r in people if r.clean > 0), reverse=True)[:5]
        if not by_clean:
            return await self.out(m, "Данных для рейтинга пока нет.", ttl=20)
        lines = ["<b>Рейтинг активности</b>"]
        for i, (n, u) in enumerate(by_clean, 1):
            lines.append(f"{i}. {mention(u, await self.display_name(m.chat.id, u))} — {n} · {rank_of(n)}")
        await self.out(m, "\n".join(lines), ttl=150)

    async def cmd_remind(self, m, args):
        if m.from_user is None:
            return
        uid, cid = m.from_user.id, m.chat.id
        rems = self.store.meta.setdefault("reminders", [])
        mine = [r for r in rems if r["u"] == uid and r["c"] == cid]
        a = args.strip()
        if a.lower() in ("", "list", "список"):
            if not mine:
                return await self.out(m, "/remind <i>30м текст</i> — напомню через 30 минут. Можно «2ч», «1д».", ttl=30)
            now = self.now()
            lines = [f"⏰ через {human_dur(max(0, r['at'] - now))}: {esc(r['t'], 60)}" for r in sorted(mine, key=lambda r: r["at"])]
            return await self.out(m, "<b>Ваши напоминания</b>\n" + "\n".join(lines) + "\n<i>/remind off — стереть все.</i>", ttl=60)
        if a.lower() in ("off", "выкл", "clear"):
            self.store.meta["reminders"] = [r for r in rems if r not in mine]
            self.store.dirty = True
            return await self.out(m, "Напоминания стёрты.", ttl=15)
        tok, _, text = a.partition(" ")
        mins = parse_minutes(tok)
        if not mins or not text.strip():
            return await self.out(m, "/remind <i>30м текст</i> — время: «30», «30м», «2ч», «1д».", ttl=20)
        if len(mine) >= REMIND_PER_USER:
            return await self.out(m, f"Превышен лимит напоминаний: максимум {REMIND_PER_USER} на пользователя.", ttl=20)
        mins = min(mins, REMIND_MAX_MIN)
        rems.append({"c": cid, "u": uid, "n": user_name(m.from_user)[:40], "at": self.now() + mins * 60,
                     "t": text.strip()[:200], "th": self.thread_of(m) or 0})
        self.store.dirty = True
        await self.out(m, f"⏰ Напомню через {human_dur(mins * 60)}: «{esc(text.strip(), 80)}»", ttl=30)

    async def fire_reminders(self, now: float) -> None:
        rems = self.store.meta.get("reminders")
        if not rems:
            return
        due = [r for r in rems if r["at"] <= now]
        if not due:
            return
        self.store.meta["reminders"] = [r for r in rems if r["at"] > now]
        self.store.dirty = True
        for r in due:
            extra = {"message_thread_id": r["th"]} if r.get("th") else {}
            sent = await self.call("send_message", r["c"], f"⏰ {mention(r['u'], r.get('n', ''))}: {esc(r['t'], 200)}", **extra)
            if sent is not None:
                self.later(900, self.call, "delete_message", r["c"], sent.message_id)

    @staticmethod
    def poll_counts(p: dict) -> list:
        counts = [0] * len(p["o"])
        for i in p["v"].values():
            if 0 <= i < len(counts):
                counts[i] += 1
        return counts

    def poll_text(self, p: dict, closed: bool = False) -> str:
        counts, total = self.poll_counts(p), len(p["v"])
        lines = [f"<b>📊 {esc(p['q'], 150)}</b>", ""]
        for i, o in enumerate(p["o"]):
            pct = round(100 * counts[i] / total) if total else 0
            full = round(pct / 10)
            lines.append(f"{esc(o, 40)}\n{'█' * full}{'░' * (10 - full)} {counts[i]} · {pct}%")
        lines.append("")
        lines.append(f"<i>Опрос закрыт. Голосов: {total}.</i>" if closed
                     else f"<i>Голосов: {total}. Один голос на человека, его можно сменить.</i>")
        return "\n".join(lines)

    @staticmethod
    def poll_kb(pid: str, p: dict):
        from aiogram.types import InlineKeyboardButton, InlineKeyboardMarkup
        rows = [[InlineKeyboardButton(text=o[:40], callback_data=f"pl:{pid}:{i}")] for i, o in enumerate(p["o"])]
        rows.append([InlineKeyboardButton(text="🛑 Закрыть опрос", callback_data=f"pl:{pid}:x")])
        return InlineKeyboardMarkup(inline_keyboard=rows)

    async def _poll_open(self, m, q: str, opts: list, hours: float, preset: str = ""):
        polls = self.store.meta.setdefault("polls", {})
        if sum(1 for p in polls.values() if p["c"] == m.chat.id and not p.get("x")) >= POLL_MAX_ACTIVE:
            return await self.out(m, "Столько опросов сразу — это уже референдум. Закройте старые.", ttl=20)
        pid = secrets.token_hex(3)
        p = {"c": m.chat.id, "m": 0, "q": q, "o": opts, "v": {}, "u": self.now() + hours * 3600,
             "by": m.from_user.id, "x": False, "s": preset}
        polls[pid] = p
        sent = await self.out(m, self.poll_text(p), markup=self.poll_kb(pid, p))
        if sent is None:
            polls.pop(pid, None)
            return
        p["m"] = sent.message_id
        self.store.dirty = True

    async def cmd_poll(self, m, args):
        if not self.in_group(m) or m.from_user is None:
            return
        parts = [x.strip() for x in args.split("|")]
        if len(parts) < 3 or len(parts) > 7 or not all(parts):
            return await self.out(m, "/poll <i>вопрос | вариант | вариант</i> — от 2 до 6 вариантов, опрос живёт сутки.", ttl=25)
        if not self._cool(m.chat.id, f"poll:{m.from_user.id}", 60):
            return
        await self._poll_open(m, parts[0][:150], [x[:40] for x in parts[1:]], POLL_HOURS)

    async def close_poll(self, pid: str, p: dict) -> None:
        p["x"], p["cl"] = True, self.now()
        self.store.dirty = True
        await self.call("edit_message_text", self.poll_text(p, closed=True), chat_id=p["c"], message_id=p["m"])

    async def poll_tick(self, now: float) -> None:
        polls = self.store.meta.get("polls")
        if not polls:
            return
        for pid, p in list(polls.items()):
            if not p.get("x") and now >= p["u"]:
                await self.close_poll(pid, p)
            elif p.get("x") and now - p.get("cl", now) > POLL_KEEP:
                polls.pop(pid, None)
                self.store.dirty = True

    async def on_poll_button(self, cb) -> None:
        try:
            _, pid, act = cb.data.split(":")
        except ValueError:
            return await cb.answer()
        p = (self.store.meta.get("polls") or {}).get(pid)
        msg = getattr(cb, "message", None)
        if p is None or p.get("x") or msg is None or msg.chat.id != p["c"]:
            return await cb.answer("Опрос уже закрыт.")
        uid = cb.from_user.id
        if act == "x":
            if uid == p["by"] or await self.is_admin(p["c"], uid):
                await self.close_poll(pid, p)
                return await cb.answer("Опрос закрыт.")
            return await cb.answer("Закрыть может автор или владелец.")
        if self.now() >= p["u"]:
            await self.close_poll(pid, p)
            return await cb.answer("Опрос закрыт.")
        try:
            i = int(act)
        except ValueError:
            return await cb.answer()
        if not 0 <= i < len(p["o"]):
            return await cb.answer()
        prev = p["v"].get(str(uid))
        if prev == i:
            return await cb.answer("Голос уже учтён.")
        p["v"][str(uid)] = i
        self.store.dirty = True
        popup = "Голос принят." if prev is None else "Голос изменён."
        await self.call("edit_message_text", self.poll_text(p), chat_id=p["c"], message_id=p["m"],
                        reply_markup=self.poll_kb(pid, p))
        await cb.answer(popup)

    async def cmd_roll(self, m, args):
        if m.from_user is None or not self._cool(m.chat.id, f"roll:{m.from_user.id}", 4):
            return
        a = args.strip().lower().replace(" ", "")
        mt = re.fullmatch(r"(?:(\d{1,2})?[dд](\d{1,4})?|(\d{1,4}))?", a)
        if not mt:
            return await self.out(m, "/roll <i>2d6</i> — до 10 кубиков, до 1000 граней. Просто /roll — один d6.", ttl=20)
        n, s = (1, int(mt.group(3))) if mt.group(3) else (int(mt.group(1) or 1), int(mt.group(2) or 6))
        if not (1 <= n <= 10 and 2 <= s <= 1000):
            return await self.out(m, "/roll <i>2d6</i> — до 10 кубиков, до 1000 граней.", ttl=20)
        rolls = [self.voice.rng.randint(1, s) for _ in range(n)]
        body = f"{' + '.join(map(str, rolls))} = <b>{sum(rolls)}</b>" if n > 1 else f"выпало <b>{rolls[0]}</b>"
        text = f"{self._who(m)}: {body} ({n}d{s})"
        await self.out(m, text, ttl=120 if self.in_group(m) else 0)

    async def cmd_coin(self, m, args):
        if m.from_user is None or not self._cool(m.chat.id, f"coin:{m.from_user.id}", 4):
            return
        r = self.voice.rng.random()
        res = "Орёл." if r < 0.5 else "Решка."
        await self.out(m, f"{self._who(m)}: {res}", ttl=90 if self.in_group(m) else 0)


def parse_chat_ids(raw: str) -> set:
    out = set()
    for tok in re.split(r"[\s,;]+", (raw or "").replace("−", "-").replace("—", "-")):
        if re.fullmatch(r"-?\d{5,20}", tok):
            n = int(tok)
            out.add(n if n < 0 else -n)
    return out


def word_hash(word: str) -> bytes:
    norm = " ".join(word.casefold().replace("ё", "е").split())
    return hashlib.sha256(("guard:" + norm).encode("utf-8")).digest()


HASH_SPEC_RX = re.compile(r"[0-9a-f]{64}|pbkdf2:\d{4,7}:[0-9a-f]{16,64}:[0-9a-f]{64}")


def _norm_word(word: str) -> str:
    return " ".join(word.casefold().replace("ё", "е").split())


def make_word_hash(word: str, iters: int = 240_000, salt: bytes | None = None) -> str:
    salt = salt or secrets.token_bytes(16)
    dk = hashlib.pbkdf2_hmac("sha256", _norm_word(word).encode("utf-8"), salt, iters)
    return f"pbkdf2:{iters}:{salt.hex()}:{dk.hex()}"


def verify_word(word: str, spec) -> bool:
    try:
        if isinstance(spec, (bytes, bytearray)):
            return hmac.compare_digest(word_hash(word), bytes(spec))
        if isinstance(spec, str) and spec.startswith("pbkdf2:"):
            _, it, salt, dk = spec.split(":")
            it = int(it)
            if not 1000 <= it <= 2_000_000:
                return False
            calc = hashlib.pbkdf2_hmac("sha256", _norm_word(word).encode("utf-8"), bytes.fromhex(salt), it)
            return hmac.compare_digest(calc, bytes.fromhex(dk))
    except (ValueError, TypeError):
        return False
    return False


def _flag(env, name: str, default: bool) -> bool:
    v = env.get(name)
    if v is None or str(v).strip() == "":
        return default
    return str(v).strip().lower() not in ("0", "false", "no", "off", "нет", "выкл")


def read_secrets(env=None) -> dict:
    env = os.environ if env is None else env
    warns: list = []

    def num(name: str, default, lo, hi, cast=int):
        raw = str(env.get(name, "") or "").strip()
        if not raw:
            return default
        try:
            v = cast(raw.replace(",", "."))
        except ValueError:
            warns.append(f"{name}={raw!r}: нужно число, беру {default}")
            return default
        if not lo <= v <= hi:
            warns.append(f"{name}={raw!r}: вне диапазона {lo}..{hi}, беру {default}")
            return default
        return v

    sec = {
        "owners": parse_ids(env.get("GUARD_ADMIN_IDS", "")),
        "tz_h": num("GUARD_TZ", TZ_HOURS_DEFAULT, -12, 14),
        "panel_word": str(env.get("GUARD_PANEL_WORD", "") or "").strip(),
        "panel_word_hash": str(env.get("GUARD_PANEL_WORD_HASH", "") or "").strip().lower(),
        "panel_ttl_min": num("GUARD_PANEL_TTL", 30, 1, 1440),
        "panel_tries": num("GUARD_PANEL_TRIES", 6, 2, 50),
        "allowed": parse_chat_ids(env.get("GUARD_ALLOWED_CHATS", "")),
        "strict_add": _flag(env, "GUARD_STRICT_ADD", True),
        "notify_adds": _flag(env, "GUARD_NOTIFY_ADDS", True),
        "notify_removals": _flag(env, "GUARD_NOTIFY_REMOVALS", True),
        "captcha_ban_min": num("GUARD_CAPTCHA_BAN_MIN", 15, 1, 10080),
        "captcha_min_react": num("GUARD_CAPTCHA_MIN_REACT", 1.0, 0.0, 10.0, float),
        "trusted": parse_ids(env.get("GUARD_TRUSTED_IDS", "")),
        "banned": parse_ids(env.get("GUARD_BANNED_IDS", "")),
        "trust_chat_admins": _flag(env, "GUARD_TRUST_CHAT_ADMINS", False),
        "cmd_limit": num("GUARD_CMD_LIMIT", 8, 0, 100),
        "cas": _flag(env, "GUARD_CAS", True),
        "log_chat": num("GUARD_LOG_CHAT", 0, -10**15, 10**15),
        "strict_min": num("GUARD_STRICT_MINUTES", STRICT_DEFAULT_MIN, STRICT_MIN_MIN, STRICT_MAX_MIN),
        "strict_auto": _flag(env, "GUARD_STRICT_AUTO", True),
        "strict_auto_users": num("GUARD_STRICT_AUTO_USERS", STRICT_AUTO_USERS, 2, 20),
        "strict_auto_window": num("GUARD_STRICT_AUTO_WINDOW", STRICT_AUTO_WINDOW // 60, 1, 120),
        "foreign_scripts": _flag(env, "GUARD_FOREIGN_SCRIPTS", True),
        "react_guard": _flag(env, "GUARD_REACT_GUARD", True),
        "puppet": _flag(env, "GUARD_PUPPET", True),
        "spam_memory": _flag(env, "GUARD_SPAM_MEMORY", True),
        "learn": _flag(env, "GUARD_LEARN", True),
        "conflicts": _flag(env, "GUARD_CONFLICTS", True),
        "jitter": _flag(env, "GUARD_JITTER", True),
        "fort_auto": _flag(env, "GUARD_FORT_AUTO", True),
        "fort_score": num("GUARD_FORT_SCORE", FORT_TRIP_SCORE, 3.0, 100.0, float),
        "fort_actors": num("GUARD_FORT_ACTORS", FORT_TRIP_ACTORS, 2, 30),
        "fort_hold": num("GUARD_FORT_HOLD", FORT_AUTO_HOLD // 60, 1, 720),
        "trace": _flag(env, "GUARD_TRACE", True),
        "autopilot": _flag(env, "GUARD_AUTOPILOT", True),
        "ap_sens": num("GUARD_AP_SENS", 1.0, 0.4, 3.0, float),
        "ap_calm_hours": num("GUARD_AP_CALM_HOURS", AP_CALM_AFTER // 3600, 0, 720),
        "ap_brain": _flag(env, "GUARD_AP_BRAIN", True),
    }
    h = sec["panel_word_hash"]
    if h and not HASH_SPEC_RX.fullmatch(h):
        warns.append("GUARD_PANEL_WORD_HASH: нужен хэш из команды --hash-word СЛОВО (pbkdf2:… или 64 hex-символа); игнорирую")
        sec["panel_word_hash"] = ""
    elif h and len(h) == 64:
        warns.append("GUARD_PANEL_WORD_HASH: старый лёгкий хэш работает, но лучше получить новый: --hash-word СЛОВО")
    if not sec["owners"]:
        warns.append("GUARD_ADMIN_IDS пуст: у бота нет ни одного админа, панель и команды управления никому не доступны")
    for key, label in (("trusted", "GUARD_TRUSTED_IDS"), ("banned", "GUARD_BANNED_IDS")):
        both = sec[key] & sec["owners"]
        if both:
            sec[key] -= both
            warns.append(f"{label}: владельцев (GUARD_ADMIN_IDS) сюда не вношу")
    both = sec["trusted"] & sec["banned"]
    if both:
        sec["trusted"] -= both
        warns.append("один и тот же id в GUARD_TRUSTED_IDS и GUARD_BANNED_IDS: считаю его забаненным")
    hook_secret = str(env.get("GUARD_SECRET", "") or "")
    if hook_secret and len(hook_secret) < 16:
        warns.append("GUARD_SECRET короче 16 символов: лучше длинный случайный "
                     "(python -c \"import secrets; print(secrets.token_urlsafe(24))\")")
    if sec["panel_word"] and len(sec["panel_word"]) < 4 and not sec["panel_word_hash"]:
        warns.append("GUARD_PANEL_WORD короче 4 символов: такое слово легко подобрать")
    if sec["strict_add"] and not sec["owners"]:
        warns.append("GUARD_STRICT_ADD включён, а GUARD_ADMIN_IDS пуст: отчёты о добавлениях слать некому")
    if sec["allowed"] and not sec["owners"]:
        warns.append("GUARD_ALLOWED_CHATS задан, а GUARD_ADMIN_IDS пуст: о чужих чатах сообщить будет некому")
    sec["warnings"] = warns
    return sec


def apply_secrets(guard, sec: dict) -> None:
    global FOREIGN_SCRIPTS
    guard.owners = set(sec["owners"])
    guard.tz_h = sec["tz_h"]
    guard.store.tz_h = guard.tz_h
    if sec["panel_word_hash"]:
        hh = sec["panel_word_hash"]
        guard.panel_hash = bytes.fromhex(hh) if len(hh) == 64 else hh
    elif sec["panel_word"]:
        guard.panel_hash = word_hash(sec["panel_word"])
    else:
        guard.panel_hash = None
    guard.panel_ttl = sec["panel_ttl_min"] * 60.0
    guard.panel_tries = sec["panel_tries"]
    guard.allowed_env = set(sec["allowed"])
    guard.strict_add = sec["strict_add"]
    guard.notify_adds = sec["notify_adds"]
    guard.notify_removals = sec["notify_removals"]
    guard.captcha_ban_default = sec["captcha_ban_min"]
    guard.captcha_min_react = sec["captcha_min_react"]
    guard.trusted = set(sec["trusted"])
    guard.banned_env = set(sec["banned"])
    guard.trust_tg_admins = sec["trust_chat_admins"]
    guard.cmd_limit = sec["cmd_limit"]
    guard.cas_on = sec["cas"]
    guard.log_chat_env = sec["log_chat"]
    eng = getattr(guard, "eng", None)
    if eng is not None:
        eng.strict_default_min = sec["strict_min"]
        eng.strict_auto_on = sec["strict_auto"]
        eng.strict_auto_users = sec["strict_auto_users"]
        eng.strict_auto_window = sec["strict_auto_window"] * 60.0
        eng.puppet_on = sec["puppet"]
        eng.memory_on = sec["spam_memory"]
        eng.learn_on = sec["learn"]
        eng.conflicts_on = sec["conflicts"]
        eng.jitter_on = sec["jitter"]
        eng.fort_auto_on = sec["fort_auto"]
        eng.fort_trip_score = float(sec["fort_score"])
        eng.fort_trip_actors = sec["fort_actors"]
        eng.fort_hold_s = sec["fort_hold"] * 60.0
        eng.trace_on = sec["trace"]
        eng.ap_on = sec["autopilot"]
        eng.ap_sens = float(sec["ap_sens"])
        eng.ap_calm_after = sec["ap_calm_hours"] * 3600.0
        eng.ap_brain = sec["ap_brain"]
    guard.react_on = sec["react_guard"]
    FOREIGN_SCRIPTS = sec["foreign_scripts"]


ENV_EXAMPLE = """\
# ═══ guard: пример .env (скопируйте в .env рядом с guard.py и измените) ═══

# ── обязательное ──
GUARD_BOT_TOKEN=                  # токен ОТДЕЛЬНОГО бота-сторожа из @BotFather

# ── кто главный ──
GUARD_ADMIN_IDS=                  # id владельцев через запятую (свой id покажет /id в личке с ботом).
                                  # ТОЛЬКО они админы бота: права админа в Telegram-чате ничего не значат
GUARD_TRUSTED_IDS=                # id доверенных: автоматика их не проверяет, но командовать ботом они не могут
GUARD_BANNED_IDS=                 # id из «чёрного списка»: бан сразу при входе или первом сообщении, команды не слушаю
GUARD_TRUST_CHAT_ADMINS=0         # 1: админов Telegram-чата автоматика не проверяет (админами бота они всё равно не станут)
GUARD_CMD_LIMIT=8                 # команд за 20 секунд от одного человека (0 — без лимита; владельцам лимита нет)
GUARD_CAS=1                       # 1: сверять новичков с базой спамеров CAS (api.cas.chat); 0 — не обращаться к сервису
GUARD_LOG_CHAT=                   # id чата или канала для журнала банов и ограничений (общий для всех чатов; в чате — /setlog)
GUARD_PANEL_WORD=                 # секретное слово панели: без него /panel не откроется (пусто — слово не нужно)
# GUARD_PANEL_WORD_HASH=          # то же самое, но хэшем (python guard.py --hash-word СЛОВО): так слово нигде не лежит открытым
GUARD_PANEL_TTL=30                # сколько минут панель остаётся открытой после слова (сбрасывается при каждом нажатии)
GUARD_PANEL_TRIES=6               # неверных слов за 10 минут до блокировки подбора на 15 минут

# ── где боту можно работать ──
GUARD_ALLOWED_CHATS=              # номера чатов через запятую, например -1001234567890,-1009876543210
                                  # пусто — работает везде; задан — в остальных чатах молчит и не работает
GUARD_STRICT_ADD=1                # 1: если бота добавил не владелец (и чат не разрешён заранее) — бот выйдет из чата
GUARD_NOTIFY_ADDS=1               # 1: сообщать владельцам в личку, если бота добавил кто-то другой (даже если он уже вышел)
GUARD_NOTIFY_REMOVALS=1           # 1: сообщать владельцам, если бота убрали из чата

# ── капча ──
GUARD_CAPTCHA_BAN_MIN=15          # на сколько минут убирать из чата за проваленный пропуск
GUARD_CAPTCHA_MIN_REACT=1.0       # быстрее этого (секунд) верный ответ не принимается: так нажимают только скрипты

# ── строгий режим (команда /strict) и дополнительные защиты ──
GUARD_STRICT_MINUTES=120          # на сколько минут включается строгий режим по умолчанию (/strict без срока и автовключение)
GUARD_STRICT_AUTO=1               # 1: включать строгий режим самому, когда в чате волна спама; 0: только вручную
GUARD_STRICT_AUTO_USERS=3         # сколько РАЗНЫХ спамеров должно попасться, чтобы режим включился сам
GUARD_STRICT_AUTO_WINDOW=10       # за сколько минут (во время массового входа хватает на одного меньше)
GUARD_FOREIGN_SCRIPTS=1           # 1: много иероглифов/арабицы/тайского в тексте — лёгкий признак спама (сам не наказывает)
GUARD_REACT_GUARD=1               # 1: ловить спам реакциями (десятки реакций за секунды); нужны права администратора у бота
GUARD_PUPPET=1                    # 1: ловить «кукольный театр» — постановочные диалоги подставных аккаунтов (вопрос → ссылка → «работает»)
GUARD_SPAM_MEMORY=1               # 1: помнить контакты пойманного спама неделю (/spamlist, /forget); 0 — не запоминать и не применять
GUARD_LEARN=1                     # 1: самообучение (карточки в личку «спам / нормально», пересланный спам, вечерняя справка); 0 — выкл
GUARD_LEARN_PLUS=1                # 1: уроки из чата (реакции, /spam, баны владельца), короткие фразы, отмеченные авторы; 0 — только старое самообучение
GUARD_LEARN_AUTO=1                # 1: осторожно учиться на собственных уверенных поимках во время волн (только мягкий сигнал); 0 — выкл
GUARD_CONFLICTS=1                 # 1: следить за конфликтами (журнал провокаций и травли, смягчение для сорвавшегося); 0 — выкл.
GUARD_JITTER=1                    # 1: разрешить случайную задержку удаления пограничного спама (в чате включается отдельно, по умолчанию выкл.)

# ── полная защита (команда /fullguard, она же /panic) ──
GUARD_FORT_AUTO=1                 # 1: радар угроз сам включает и снимает полную защиту при волне; 0: только вручную
GUARD_FORT_SCORE=10               # оценка радара, с которой режим включается сам (спамер-бан ≈ 2.5, наплыв входов ≈ 3)
GUARD_FORT_ACTORS=4               # и сколько РАЗНЫХ источников угрозы при этом нужно (один шумный участник волной не считается)
GUARD_FORT_HOLD=12                # сколько минут режим держится после последней угрозы, прежде чем сам выключиться

# ── «Следопыт» (команда /trace) ──
GUARD_TRACE=1                     # 1: улики из правок, скорости ответов, ритма и связей (в чате режим on/log/off задаёт /trace); 0: датчики выключены

# ── автопилот (команда /autopilot) ──
GUARD_AUTOPILOT=1                 # 1: рефлексы сами усиливают настройки при ситуации (волна спама, наплыв, самозванцы, флуд, накал, 18+) и возвращают их; 0: выкл.
GUARD_AP_SENS=1.0                 # чувствительность: больше единицы — срабатывает раньше, меньше — позже (0.4..3)
GUARD_AP_CALM_HOURS=6             # после скольких спокойных часов автопилот смягчает мелочи, которых владелец не трогал (0 — «затишья» нет)
GUARD_AP_BRAIN=1                  # 1: автопилот делает внутренние поправки к своим решениям (тонкая настройка порогов); 0: чистый автопилот v4.0

# ── расширение 5.0 (файл guard5.py рядом с guard.py) ──
GUARD5=1                          # 0: выключить расширение целиком (бот работает как 4.3)
# GUARD5_CASES=1                  # «дела»: кнопки «↩️ Отменить / ✅ Верно» в тревоге, учёт точности решений
# GUARD5_APPEAL=1                 # «Это не спам» под автоматическим удалением: апелляция владельцу
# GUARD5_LOOK=1                   # «второй взгляд»: проверка ссылок новичков до решения
# GUARD5_NET=1                    # сетевые проверки (возраст домена, сокращалки, описание t.me-ссылки); 0 — бот ничего не запрашивает сам
# GUARD5_KNOWN=1                  # знакомые чату домены меньше штрафуются
# GUARD5_REPORTS=1                # репутация жалобщиков и оценка бота на карточке жалобы
# GUARD5_CMDS=1                   # «1ч30м», «2нед» в /mute /ban /purge и др.
# GUARD5_REPEAT=1                 # /remind «завтра в 10», «каждый день в 9:00»; /repeat с днями недели и окном времени
# GUARD5_JOINREQ=1                # заявки на вход: анализ «о себе»; чистка реакций спамера
# GUARD5_RULES=1                  # правила кнопкой после проверки при входе (удаляются через 6 мин); /setrules gate off — отключить

# ── расширение 6.0 (файл guard6.py рядом с guard.py) ──
GUARD6=1                          # 0: выключить расширение целиком (бот работает как 5.0)
# GUARD6_GOV=1                    # «Дозатор»: все запросы к Telegram идут через регулятор (бан/удаление первыми, «косметика» при перегрузке пропускается)
# GUARD6_CAPQ=1                   # очередь капч при волне входов (человек остаётся «только чтение», пока капча ждёт очереди)
# GUARD6_DIGEST=1                 # сводка волны: сверх 5 тревог в минуту — одна сводка раз в ~25 с
# GUARD6_RESCUE=1                 # после полной защиты — список наказанных без сильных улик и кнопка «Вернуть»
# GUARD6_SOFTNET=1                # «второй взгляд» не ждёт сеть во время волны
# GUARD6_OVERKILL=1               # вопрос «не слишком ли строго?», если в полной защите отменили 2 наказания за 10 минут
# GUARD6_TRACE=1                  # Следопыт: «стая», «обход вопросов», «смена облика»
# GUARD6_PUPPET=1                 # Кукольный театр: «хор», «одна рука», дела для кукол
# GUARD5_RULES_STRICT=0           # 1: вернуть старое — не нажавшего «Показать правила» убирать на 10 минут (по умолчанию только во время тревоги)

# ── языки (файлы guard_es.py / guard_de.py / guard_ar.py / guard_zh.py лежат рядом с guard.py) ──
GUARD_LANGS=all                   # all — все найденные; «es,de» — только эти; off — никакие (останутся русский и английский)
# GUARD_ES=1                      # 0: выключить испанский (так же GUARD_DE / GUARD_AR / GUARD_ZH для немецкого, арабского, китайского)

# ── прочее ──
GUARD_TZ=3                        # часовой пояс в часах от UTC (для времени в журнале)
GUARD_SECRET=                     # секрет моста с игрой (лучше от 16 символов, случайный); пусто — моста нет
GUARD_HOST=127.0.0.1
GUARD_PORT=8765
GUARD_STATE=guard_state.json
GUARD_CUSTOM_WORDS=custom_words.txt
LOG_LEVEL=INFO
"""


def check_config(env=None) -> int:
    env = os.environ if env is None else env
    sec = read_secrets(env)
    token = str(env.get("GUARD_BOT_TOKEN") or env.get("BOT_TOKEN") or "").strip()
    bad = 0
    print(f"guard {VERSION}: проверка настроек")
    if not token:
        print("✗ GUARD_BOT_TOKEN: не задан")
        bad = 1
    elif not re.fullmatch(r"\d{6,}:[A-Za-z0-9_-]{30,}", token):
        print("✗ GUARD_BOT_TOKEN: формат не похож на токен BotFather (число:буквы)")
        bad = 1
    else:
        print("✓ GUARD_BOT_TOKEN: задан")
    print(f"{'✓' if sec['owners'] else '!'} владельцев: {len(sec['owners'])}"
          + ("" if sec["owners"] else " (GUARD_ADMIN_IDS пуст: админов у бота нет вообще, панель и команды недоступны)"))
    if sec["panel_word_hash"]:
        print("✓ слово панели: задано хэшем")
    elif sec["panel_word"]:
        print(f"✓ слово панели: задано ({len(sec['panel_word'])} симв.), открытая сессия {sec['panel_ttl_min']} мин")
    else:
        print("! слово панели не задано: владельцу для /panel хватает номера из GUARD_ADMIN_IDS")
    if sec["allowed"]:
        print(f"✓ разрешённых чатов в окружении: {len(sec['allowed'])} — в остальных бот работать не будет")
    else:
        print("! GUARD_ALLOWED_CHATS пуст: бот работает в любом чате (список можно включить в панели)")
    print(f"{'✓' if sec['strict_add'] else '!'} строгое добавление: {'вкл' if sec['strict_add'] else 'выкл'}"
          f" · уведомления о добавлениях: {'вкл' if sec['notify_adds'] else 'выкл'}")
    print(f"✓ бан за провал капчи: {sec['captcha_ban_min']} мин · мин. время реакции: {sec['captcha_min_react']} с")
    print(f"✓ доверенных: {len(sec['trusted'])} · чёрный список: {len(sec['banned'])} · лимит команд: "
          f"{sec['cmd_limit'] or 'нет'} за 20 с · админы чата не проверяются: {'да' if sec['trust_chat_admins'] else 'нет'}")
    print(f"✓ строгий режим: по умолчанию {sec['strict_min']} мин · автовключение: {'вкл' if sec['strict_auto'] else 'выкл'}"
          f" (от {sec['strict_auto_users']} спамеров за {sec['strict_auto_window']} мин) · спам реакциями: "
          f"{'ловлю' if sec['react_guard'] else 'не ловлю'} · чужие алфавиты: {'признак' if sec['foreign_scripts'] else 'не учитываю'}")
    print(f"✓ полная защита: автовключение {'вкл' if sec['fort_auto'] else 'выкл'} (оценка радара от {sec['fort_score']:g}, "
          f"источников от {sec['fort_actors']}), держится {sec['fort_hold']} мин после последней угрозы")
    print(f"{'✓' if sec['autopilot'] else '!'} автопилот: {'вкл' if sec['autopilot'] else 'выкл'} · чувствительность {sec['ap_sens']:g} · "
          f"затишье: {('после ' + str(sec['ap_calm_hours']) + ' ч спокойствия') if sec['ap_calm_hours'] else 'нет'} · "
          f"внутренние поправки: {'вкл' if sec['ap_brain'] else 'выкл'}")
    print(f"{'✓' if sec['trace'] else '!'} Следопыт (правки, скорость ответов, ритм, связи): {'вкл' if sec['trace'] else 'выкл'}")
    print(f"{'✓' if sec['puppet'] else '!'} кукольный театр (постановочные диалоги): {'вкл' if sec['puppet'] else 'выкл'}")
    print(f"{'✓' if sec['spam_memory'] else '!'} память о пойманном спаме: {'вкл' if sec['spam_memory'] else 'выкл'}")
    print(f"{'✓' if sec['learn'] else '!'} самообучение (карточки владельцу, шаблоны): {'вкл' if sec['learn'] else 'выкл'}")
    print(f"{'✓' if sec['conflicts'] else '!'} конфликты (провокации и травля): {'вкл' if sec['conflicts'] else 'выкл'}")
    try:
        import guard6 as _c6
        _c6.reload_env()
        on6 = [k for k in _c6.FEATS if _c6.feat(k)]
        print(f"{'✓' if on6 else '!'} расширение 6.0 (guard6.py): " + (", ".join(on6) if on6 else "выключено (GUARD6=0)"))
    except ImportError:
        print("! расширение 6.0: файла guard6.py рядом нет — бот работает как 5.0")
    try:
        import guard5 as _c5
        _c5.reload_env()
        on = [k for k in _c5.FEATS if _c5.feat(k)]
        print(f"{'✓' if on else '!'} расширение 5.0 (guard5.py): " + (", ".join(on) if on else "выключено (GUARD5=0)"))
    except ImportError:
        print("! расширение 5.0: файла guard5.py рядом нет — бот работает как 4.3")
    here = os.path.dirname(os.path.abspath(__file__))
    want = _langs_wanted(env)
    for code in LANG_MODULES:
        has = os.path.exists(os.path.join(here, f"guard_{code}.py"))
        off = str(env.get(f"GUARD_{code.upper()}", "1")).strip() == "0"
        if not has:
            print(f"! язык {code}: файла guard_{code}.py рядом нет")
        elif code not in want:
            print(f"! язык {code}: не выбран в GUARD_LANGS")
        elif off:
            print(f"! язык {code}: выключен (GUARD_{code.upper()}=0)")
        else:
            print(f"✓ язык {code}: подключится при запуске")
    for w in sec["warnings"]:
        print("!", w)
    return bad


def cli(argv: list) -> int:
    cmd = argv[0] if argv else ""
    if cmd == "--env-example":
        print(ENV_EXAMPLE, end="")
        return 0
    if cmd == "--check":
        load_env()
        return check_config()
    if cmd == "--hash-word":
        if len(argv) < 2 or not argv[1].strip():
            print("Укажите слово: python guard.py --hash-word «секретное слово»", file=sys.stderr)
            return 2
        print(make_word_hash(" ".join(argv[1:])))
        return 0
    print("Команды: --env-example (шаблон .env), --check (проверить настройки), --hash-word СЛОВО (хэш для .env)")
    return 0 if cmd in ("--help", "-h") else 2


class Gatekeeper:
    def conf(self, key: str, default=None):
        return (self.store.meta.get("conf") or {}).get(key, default)

    def conf_set(self, key: str, val) -> None:
        self.store.meta.setdefault("conf", {})[key] = val
        self.store.dirty = True

    def strict_on(self) -> bool:
        return bool(self.conf("strict_add", self.strict_add))

    def notify_on(self) -> bool:
        return bool(self.conf("notify_adds", self.notify_adds))

    def allow_mode(self) -> bool:
        return bool(self.allowed_env) or bool(self.conf("allow_mode", False))

    def allowed_ids(self) -> set:
        return set(self.allowed_env) | {x for x in (self.store.meta.get("allowed") or ()) if isinstance(x, int)}

    def chat_ok(self, cid: int) -> bool:
        return cid > 0 or not self.allow_mode() or cid in self.allowed_ids()

    def journal(self, kind: str, chat: int = 0, title: str = "", by: int = 0, name: str = "", note: str = "") -> None:
        j = self.store.meta.setdefault("journal", [])
        j.append({"t": round(self.now()), "k": kind, "c": chat, "ti": (title or "")[:60], "by": by,
                  "n": (name or "")[:40], "no": (note or "")[:80]})
        if len(j) > 300:
            del j[:-300]
        self.store.dirty = True

    def fmt_when(self, ts: float) -> str:
        return time.strftime("%d.%m %H:%M", time.gmtime(ts + self.tz_h * 3600))

    def foreign_note(self, cid: int, title: str, by: int) -> None:
        self.store.meta.setdefault("foreign", {})[str(cid)] = {"ti": (title or "")[:60], "by": by, "t": round(self.now())}
        self.store.dirty = True

    def foreign_forget(self, cid: int) -> None:
        if (self.store.meta.get("foreign") or {}).pop(str(cid), None) is not None:
            self.store.dirty = True

    def foreign_list(self) -> list:
        return sorted(((int(c), v) for c, v in (self.store.meta.get("foreign") or {}).items()), key=lambda x: -x[1].get("t", 0))

    async def dm(self, uid: int, text: str, markup=None) -> bool:
        return uid > 0 and await self.call("send_message", uid, text, reply_markup=markup) is not None

    async def notify_owners(self, text: str, markup=None, exclude=()) -> int:
        n = 0
        for uid in sorted(set(self.owners) - set(exclude)):
            if await self.dm(uid, text, markup):
                n += 1
        return n

    @staticmethod
    def who_label(u) -> str:
        if u is None:
            return "неизвестно"
        un = getattr(u, "username", None)
        return f"{esc(user_name(u) or 'без имени', 40)} ({'@' + esc(un, 32) + ', ' if un else ''}id <code>{u.id}</code>)"

    @staticmethod
    def allow_kb(cid: int, can_leave: bool = True):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        row = [Btn(text="✅ Разрешить чат", callback_data=f"ap:ok:{cid}")]
        if can_leave:
            row.append(Btn(text="Покинуть чат", callback_data=f"ap:lv:{cid}"))
        return InlineKeyboardMarkup(inline_keyboard=[row])

    @staticmethod
    def leave_kb(cid: int):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        return InlineKeyboardMarkup(inline_keyboard=[[Btn(text="Покинуть чат", callback_data=f"ap:lv:{cid}")]])

    async def on_bot_added(self, ev) -> bool:
        chat, who = ev.chat, getattr(ev, "from_user", None)
        wid = getattr(who, "id", 0)
        if wid and wid == self.me_id:
            return False
        now = self.now()
        seen = self._add_seen.get((chat.id, wid))
        if seen and now - seen[0] < 30:
            return seen[1]
        is_owner = wid in self.owners
        self._admins.pop(chat.id, None)
        admin_adder = is_owner
        pre_allowed = self.allow_mode() and chat.id in self.allowed_ids()
        outcome, handled = "ok", False
        if self.strict_on() and not admin_adder and not pre_allowed:
            text = "Добавление не авторизовано. Бот покидает чат."
            await self.call("send_message", chat.id, text)
            self._leaving.add(chat.id)
            await self.call("leave_chat", chat.id)
            self.foreign_forget(chat.id)
            self.journal("left", chat.id, chat.title or "", wid, user_name(who) if who else "", "добавил не владелец: бот покинул чат")
            outcome, handled = "left", True
        elif self.allow_mode() and not self.chat_ok(chat.id):
            self.foreign_note(chat.id, chat.title or "", wid)
            self.journal("blocked", chat.id, chat.title or "", wid, user_name(who) if who else "", "чата нет в списке: молчу")
            await self.soft_dm(ev, is_owner)
            outcome, handled = "blocked", True
        else:
            self.foreign_forget(chat.id)
            if not is_owner:
                self.journal("add", chat.id, chat.title or "", wid, user_name(who) if who else "", "добавил не владелец, но чат разрешён или режим не строгий: работаю")
        self._add_seen[(chat.id, wid)] = (now, handled)
        if len(self._add_seen) > 500:
            self._add_seen = {k: v for k, v in self._add_seen.items() if now - v[0] < 300}
        if not is_owner:
            await self.report_add(ev, outcome, admin_adder)
        return handled

    async def soft_dm(self, ev, is_owner: bool) -> None:
        chat, who = ev.chat, ev.from_user
        title = esc(chat.title or "без названия", 60)
        if is_owner:
            text = (f"Бот добавлен в чат «{title}», которого нет в списке разрешённых. Работа в чате не ведётся, "
                    f"бот остаётся в нём. Для разрешения используйте кнопку ниже.")
        else:
            text = (f"Бот добавлен в чат «{title}», которого нет в списке разрешённых. Работа в чате не ведётся. "
                    f"Для разрешения обратитесь к владельцу бота (идентификатор чата: <code>{chat.id}</code>).")
        ok = await self.dm(getattr(who, "id", 0), text, self.allow_kb(chat.id) if is_owner else None)
        if not ok and not is_owner:
            await self.notify_owners(f"Не удалось отправить сообщение пользователю {self.who_label(who)}: диалог с ботом не начат. "
                                     f"В чате «{title}» бот не работает.")

    async def report_add(self, ev, outcome: str, admin_adder: bool) -> None:
        if not self.notify_on() or not self.owners:
            return
        chat, who = ev.chat, ev.from_user
        result = {"left": "бот покинул чат: добавление не авторизовано", "blocked": "бот остался, но не работает: чата нет в списке",
                  "ok": "бот работает"}[outcome]
        text = (f"<b>Бот добавлен в чат</b> «{esc(chat.title or 'без названия', 60)}» (<code>{chat.id}</code>)\n"
                f"Добавил: {self.who_label(who)} — {'владелец' if admin_adder else 'не владелец'}\nРезультат: {result}.")
        kb = None
        if outcome == "blocked":
            kb = self.allow_kb(chat.id)
        elif outcome == "ok":
            kb = self.leave_kb(chat.id)
        await self.notify_owners(text, kb)

    async def on_bot_removed(self, ev) -> None:
        chat, who = ev.chat, getattr(ev, "from_user", None)
        wid = getattr(who, "id", 0)
        if chat.id in self._leaving or (wid and wid == self.me_id):
            self._leaving.discard(chat.id)
            return
        self.foreign_forget(chat.id)
        self.journal("removed", chat.id, chat.title or "", wid, user_name(who) if who else "", "бот удалён из чата")
        if self.owners and wid not in self.owners and (self.conf("notify_removals", self.notify_removals)):
            await self.notify_owners(f"<b>Бот удалён из чата</b> «{esc(chat.title or 'без названия', 60)}» "
                                     f"(<code>{chat.id}</code>)\nУдалил: {self.who_label(who)}.")

    async def notify_unlisted(self) -> None:
        if not self.allow_mode() or not self.owners:
            return
        stale = [c for c, s in self.store.chats.items() if s.active and c < 0 and not self.chat_ok(c)]
        if not stale:
            return
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        lines = ["⛔ <b>Эти чаты не в списке разрешённых</b> — там я теперь молчу:"]
        rows = []
        for c in stale[:8]:
            t = self.store.chats[c].title or str(c)
            lines.append(f"• {esc(t, 40)} (<code>{c}</code>)")
            rows.append([Btn(text=f"✅ {t[:24]}", callback_data=f"ap:ok:{c}")])
        await self.notify_owners("\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows))

    def panel_open(self, uid: int) -> bool:
        if self.panel_hash is None:
            return True
        return self._unlocked.get(uid, 0) > self.now()

    def panel_touch(self, uid: int) -> None:
        if self.panel_hash is not None and uid in self._unlocked:
            self._unlocked[uid] = self.now() + self.panel_ttl

    async def is_staff(self, uid: int) -> bool:
        return uid in self.owners or bool(await self.panel_chats(uid))

    async def try_unlock(self, uid: int, text: str) -> bool:
        if self.panel_hash is None:
            return True
        now = self.now()
        if self._lockout.get(uid, 0) > now:
            return False
        text = (text or "").strip()
        if not text or len(text) > 64 or "\n" in text:
            return False
        if await asyncio.to_thread(verify_word, text, self.panel_hash):
            if not await self.is_staff(uid):
                return False
            self._unlocked[uid] = now + self.panel_ttl
            self._guesses.pop(uid, None)
            self.journal("unlock", by=uid, note="панель открыта словом")
            return True
        g = [t for t in self._guesses.get(uid, []) if now - t < 600] + [now]
        self._guesses[uid] = g
        if len(g) >= self.panel_tries:
            self._lockout[uid] = now + 900
            self._guesses.pop(uid, None)
            self.journal("lockout", by=uid, note="подбор слова: блок на 15 минут")
            log.warning("панель: подбор слова, uid=%s заблокирован на 15 минут", uid)
            await self.notify_owners(f"🔐 Кто-то подбирает слово панели: id <code>{uid}</code>. "
                                     f"Попытки заблокированы на 15 минут.", exclude={uid})
        return False

    def capfail_recent(self, uid: int, now: float) -> int:
        return sum(1 for t in (self.store.meta.get("capfail") or {}).get(str(uid), []) if now - t < 86400)

    def note_capfail(self, uid: int, now: float) -> None:
        d = self.store.meta.setdefault("capfail", {})
        d[str(uid)] = [t for t in d.get(str(uid), []) if now - t < 86400][-4:] + [now]
        self.store.dirty = True

    def prune_gate(self, now: float) -> None:
        d = self.store.meta.get("capfail")
        if d:
            for k in list(d):
                d[k] = [t for t in d[k] if now - t < 86400]
                if not d[k]:
                    d.pop(k)
        for k in [k for k, t in self._lockout.items() if t < now]:
            self._lockout.pop(k, None)
        for k in [k for k, t in self._unlocked.items() if t < now]:
            self._unlocked.pop(k, None)

    def join_risk(self, user, now: float, raid: bool) -> tuple:
        pts, why = 0.0, []
        first = getattr(user, "first_name", "") or ""
        last = getattr(user, "last_name", "") or ""
        uname = getattr(user, "username", "") or ""
        name = (first + " " + last).strip()
        probe = name + (" @" + uname if uname else "")
        if probe.strip():
            a = analyze_text(probe, (), None)
            if a.raw >= 1.0:
                pts += min(4.0, a.raw)
                why.append("имя похоже на рекламу")
            if any(u.kind != "allowed" for u in a.urls):
                pts += 1.5
                why.append("ссылка в имени")
        if len(name) > 40:
            pts += 1.0
            why.append("очень длинное имя")
        if raid:
            pts += 2.0
            why.append("наплыв новичков")
        fails = self.capfail_recent(user.id, now)
        if fails:
            pts += 3.0 * min(2, fails)
            why.append("недавно не прошёл пропуск")
        if getattr(user, "is_premium", False):
            pts -= 1.0
        return round(pts, 2), why

    def verified_elsewhere(self, uid: int, cid: int) -> bool:
        return any(c != cid and uid in s.users and s.users[uid].verified for c, s in self.store.chats.items())

    def captcha_plan(self, chat, user, state, now: float) -> dict:
        if not state.cfg.captcha_smart:
            return {"level": None, "skip": False, "risk": 0.0, "why": []}
        raid = self.eng.raid_active(chat.id, now)
        strict = self.eng.strict_active(chat.id, now)
        risk, why = self.join_risk(user, now, raid or strict)
        level = "hard" if risk >= 3.0 else "normal" if risk >= 1.0 else "easy"
        skip = (not raid) and (not strict) and risk < 1.0 and self.verified_elsewhere(user.id, chat.id)
        return {"level": level, "skip": skip, "risk": risk, "why": why}

    def captcha_ban_minutes(self, cfg) -> int:
        return max(1, int(cfg.captcha_ban_min or self.captcha_ban_default))


class AdminPanel:
    OWNER_ACTS = {"sm", "bc", "se", "cf", "al", "ar", "ai", "fo", "ok", "dn", "lv", "lv2"}
    TIMEOUTS = (30, 60, 90, 180)
    BANS = (0, 5, 15, 60, 1440)
    JOURNAL_ICONS = {"add": "➕", "blocked": "⛔", "removed": "👋", "capfail": "🚫", "unlock": "🔓",
                     "lockout": "🔐", "allow": "✅", "deny": "➖", "leave": "🚪", "fort_on": "🛡", "fort_off": "✅",
                     "fort_sweep": "🔎", "ap": "🤖"}

    @staticmethod
    def _on(b) -> str:
        return "вкл" if b else "выкл"

    @staticmethod
    def _cycle(vals, cur):
        vals = list(vals)
        i = vals.index(cur) if cur in vals else -1
        return vals[(i + 1) % len(vals)]

    def panel_icon(self, cid: int, now: float) -> str:
        if not self.chat_ok(cid):
            return "⛔"
        rings = self.eng.rings.active(cid, now)
        if any(r.mode == "lockdown" for r in rings):
            return "🔒"
        if rings:
            return "⚔"
        if self.eng.raid_active(cid, now):
            return "🚨"
        return "🟢" if self.store.chats[cid].cfg.enabled else "⚪"

    def stat_sum(self, cids, days: int = 3) -> dict:
        tot: dict = {}
        for c in cids:
            st = self.store.chats.get(c)
            if st is None:
                continue
            for d in sorted(st.stats)[-days:]:
                for k, v in st.stats[d].items():
                    tot[k] = tot.get(k, 0) + v
        return tot

    @staticmethod
    def stat_lines(tot: dict, limit: int = 4) -> list:
        return [f"{STAT_LABELS.get(k, k)} {v}" for k, v in sorted(tot.items(), key=lambda kv: -kv[1])[:limit] if v]

    async def panel_chats(self, uid: int) -> list:
        chats = [c for c, s in self.store.chats.items() if s.active and c < 0]
        chats.sort(key=lambda c: ((self.store.chats[c].title or "").lower(), c))
        if uid in self.owners:
            return chats
        return [c for c in chats[:60] if await self.is_admin(c, uid)]

    async def panel_can(self, uid: int, cid: int) -> bool:
        return cid in self.store.chats and await self.is_admin(cid, uid)

    def panel_main(self, uid: int, chats: list, page: int = 0):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        now, owner = self.now(), uid in self.owners
        pages = max(1, (len(chats) + PANEL_PAGE - 1) // PANEL_PAGE)
        page = max(0, min(page, pages - 1))
        busy = sum(1 for c in chats if self.eng.rings.active(c, now))
        raids = sum(1 for c in chats if self.eng.raid_active(c, now))
        sl = self.stat_lines(self.stat_sum(chats))
        lines = [f"<b>Панель управления</b> · {'владелец' if owner else 'администратор'}",
                 f"Чатов под присмотром: <b>{len(chats)}</b>"]
        if busy or raids:
            lines.append(f"Сейчас: активных сессий и закрытий — {busy}, массовый вход — в {raids}")
        lines.append("За 3 дня: " + (" · ".join(sl) if sl else "тихо"))
        if owner and self.foreign_list():
            lines.append(f"⛔ Чужих чатов, где я молчу: {len(self.foreign_list())}")
        if not chats:
            lines.append("<i>Чатов нет. Добавьте бота в группу и назначьте администратором.</i>")
        lines.append(f"<i>Ваш id: <code>{uid}</code></i>")
        rows = [[Btn(text=f"{self.panel_icon(c, now)} {(self.store.chats[c].title or str(c))[:30]}", callback_data=f"ap:c:{c}")]
                for c in chats[page * PANEL_PAGE:(page + 1) * PANEL_PAGE]]
        if pages > 1:
            rows.append([Btn(text="⬅", callback_data=f"ap:m:{page - 1}"), Btn(text=f"{page + 1}/{pages}", callback_data="ap:n"),
                         Btn(text="➡", callback_data=f"ap:m:{page + 1}")])
        if owner:
            rows.append([Btn(text="Сводка", callback_data="ap:sm"), Btn(text="Рассылка", callback_data="ap:bc")])
            rows.append([Btn(text="🔐 Секреты", callback_data="ap:se"), Btn(text="📜 Журнал", callback_data="ap:jr")])
        else:
            rows.append([Btn(text="📜 Журнал", callback_data="ap:jr")])
        tail = [Btn(text="🔄 Обновить", callback_data=f"ap:m:{page}"), Btn(text="✖ Закрыть", callback_data="ap:x")]
        if self.panel_hash is not None:
            tail.append(Btn(text="🔒 Выйти", callback_data="ap:lo"))
        rows.append(tail)
        return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows)

    async def panel_chat(self, cid: int, uid: int = 0):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        st = self.store.chats[cid]
        cfg, now = st.cfg, self.now()
        rights = await self.rights(cid)
        rings = self.eng.rings.active(cid, now)
        lock = any(r.mode == "lockdown" for r in rings)
        fights = [r for r in rings if r.mode != "lockdown"]
        raid_left = self.eng.raid_until.get(cid, 0) - now
        today = st.stats.get(self.store.day(now), {})
        listed = cid in self.allowed_ids()
        access = ("✅ в списке" if listed else "⛔ вне списка: я здесь молчу") if self.allow_mode() else "✅ список выключен, работаю везде"
        lines = [f"<b>{esc(st.title or cid, 60)}</b> {self.panel_icon(cid, now)}",
                 f"Модерация: {'включена' if cfg.enabled else 'отключена'} · допуск: {access}",
                 f"Права: удалять — {'да' if rights['delete'] else 'НЕТ'}, ограничивать — {'да' if rights['restrict'] else 'НЕТ'}"]
        if lock:
            lines.append("Сейчас: чат закрыт, запись только у администраторов")
        for r in fights:
            lines.append(f"Сейчас: ⚔ {r.mode} «{esc(', '.join(r.names) or '—', 50)}», ещё {human_dur(r.expires - now)}")
        if not rings:
            lines.append("Активных сессий и закрытий нет")
        lines.append(f"Наплыв: ещё {human_dur(raid_left)}" if raid_left > 0 else "Наплыв: нет")
        sl = self.stat_lines(today)
        lines.append("Сегодня: " + (" · ".join(sl) if sl else "тихо"))
        lines.append(f"Участников в памяти: {len(st.users)} · пропусков в ожидании: "
                     f"{sum(1 for e in self.store.captchas.values() if e.get('chat') == cid)}")
        rows, row = [], []
        for code, label, attr in SETTINGS:
            txt = (f"🔗 {LINK_LABEL.get(cfg.links, cfg.links)}" if attr == "links"
                   else ("🟢 " if getattr(cfg, attr) else "⚪ ") + label)
            row.append(Btn(text=txt, callback_data=f"ap:t:{cid}:{code}"))
            if len(row) == 2:
                rows.append(row)
                row = []
        if row:
            rows.append(row)
        rows.append([Btn(text="🔓 Открыть" if lock else "🔒 Закрыть на 15 мин", callback_data=f"ap:{'op' if lock else 'lk'}:{cid}"),
                     Btn(text="🚨 Наплыв: выкл" if raid_left > 0 else "🚨 Наплыв: вкл", callback_data=f"ap:rd:{cid}")])
        more = [Btn(text="📢 Объявление", callback_data=f"ap:an:{cid}"), Btn(text="📊 За 3 дня", callback_data=f"ap:st:{cid}")]
        if fights:
            more.insert(0, Btn(text="Завершить сессию", callback_data=f"ap:bl:{cid}"))
        rows.append(more)
        rows.append([Btn(text="🛡 Защита", callback_data=f"ap:pr:{cid}"), Btn(text="📜 Журнал чата", callback_data=f"ap:jr:{cid}")])
        if uid in self.owners:
            rows.append([Btn(text="➖ Убрать из списка" if listed else "✅ Разрешить чат",
                             callback_data=f"ap:{'dn' if listed else 'ok'}:{cid}" + ("" if listed else ":c")),
                         Btn(text="Покинуть чат", callback_data=f"ap:lv:{cid}")])
        rows.append([Btn(text="⬅ Назад", callback_data="ap:m:0"), Btn(text="🔄", callback_data=f"ap:c:{cid}")])
        return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows)

    def panel_prot(self, cid: int):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        st = self.store.chats[cid]
        cfg = st.cfg
        ban = self.captcha_ban_minutes(cfg)
        lines = [f"<b>🛡 Защита · {esc(st.title or cid, 50)}</b>",
                 f"Пропуск: {self._on(cfg.captcha)} · умный (сложность по риску, пропуск прошедшим): {self._on(cfg.captcha_smart)}",
                 f"Время на ответ: {cfg.captcha_timeout} с · за провал убираю из чата на {human_dur(ban * 60)}"
                 + ("" if cfg.captcha_ban_min else " (общее значение)"),
                 f"Ссылки: {LINK_LABEL.get(cfg.links, cfg.links)} · умные признаки (двойники, приманки, редиректы): "
                 f"{self._on(cfg.smart_links)}"]
        rows = [[Btn(text=f"🛂 Пропуск: {self._on(cfg.captcha)}", callback_data=f"ap:pt:{cid}:cp"),
                 Btn(text=f"🧠 Умный: {self._on(cfg.captcha_smart)}", callback_data=f"ap:pt:{cid}:sk")],
                [Btn(text=f"🔗 Ссылки: {LINK_LABEL.get(cfg.links, cfg.links)}", callback_data=f"ap:pt:{cid}:lp"),
                 Btn(text=f"🕵 Умные ссылки: {self._on(cfg.smart_links)}", callback_data=f"ap:pt:{cid}:sl")],
                [Btn(text=f"⏱ Ответ: {cfg.captcha_timeout} с", callback_data=f"ap:pt:{cid}:ct"),
                 Btn(text=f"⛔ Бан: {ban} мин", callback_data=f"ap:pt:{cid}:bm")],
                [Btn(text="⬅ Назад", callback_data=f"ap:c:{cid}")]]
        return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows)

    def panel_secrets(self):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        env_mode = bool(self.allowed_env)
        mode = self.allow_mode()
        panel_n = len([x for x in (self.store.meta.get("allowed") or ()) if isinstance(x, int)])
        foreign = len(self.foreign_list())
        word = "не задано" if self.panel_hash is None else f"задано, сессия {int(self.panel_ttl // 60)} мин"
        lines = ["<b>🔐 Секреты</b>",
                 f"Режим списка: <b>{self._on(mode)}</b>" + (" (из окружения)" if env_mode else ""),
                 f"Разрешено чатов: {len(self.allowed_ids())} (окружение: {len(self.allowed_env)}, панель: {panel_n})",
                 f"Строгое добавление: <b>{self._on(self.strict_on())}</b>"
                 + (" — не-админам отвечаю грубо и выхожу" if self.strict_on() else ""),
                 f"Сообщать о добавлениях: <b>{self._on(self.notify_on())}</b>",
                 f"Слово панели: {word}",
                 f"Бан за капчу по умолчанию: {human_dur(self.captcha_ban_default * 60)} · владельцев: {len(self.owners)}",
                 f"Чужих чатов (я там молчу): {foreign}"]
        rows = [[Btn(text="📋 Разрешённые чаты", callback_data="ap:al"), Btn(text=f"⛔ Чужие чаты ({foreign})", callback_data="ap:fo")],
                [Btn(text=f"Список: {self._on(mode)}", callback_data="ap:cf:allow_mode"),
                 Btn(text=f"Строго: {self._on(self.strict_on())}", callback_data="ap:cf:strict_add")],
                [Btn(text=f"Уведомления: {self._on(self.notify_on())}", callback_data="ap:cf:notify_adds")],
                [Btn(text="⬅ Назад", callback_data="ap:m:0")]]
        return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows)

    def panel_allowed(self):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        ids = sorted(self.allowed_ids())
        lines = ["<b>📋 Разрешённые чаты</b>"]
        rows = []
        if not ids:
            lines.append("Список пуст.")
        for c in ids[:12]:
            st = self.store.chats.get(c)
            t = (st.title if st and st.title else str(c))
            env = c in self.allowed_env
            lines.append(f"• {esc(t, 40)} (<code>{c}</code>){' 🔒 из окружения' if env else ''}")
            if not env:
                rows.append([Btn(text=f"➖ {t[:28]}", callback_data=f"ap:ar:{c}")])
        if len(ids) > 12:
            lines.append(f"… и ещё {len(ids) - 12}")
        rows.append([Btn(text="➕ Добавить по номеру", callback_data="ap:ai")])
        rows.append([Btn(text="⬅ Назад", callback_data="ap:se")])
        return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows)

    def panel_foreign(self):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        items = self.foreign_list()
        lines = ["<b>Чаты вне списка</b> — бот добавлен, но не работает"]
        rows = []
        if not items:
            lines.append("Таких нет.")
        for c, v in items[:6]:
            lines.append(f"• {esc(v.get('ti') or c, 40)} (<code>{c}</code>), добавил id <code>{v.get('by', 0)}</code>, "
                         f"{self.fmt_when(v.get('t', 0))}")
            rows.append([Btn(text=f"✅ {str(v.get('ti') or c)[:16]}", callback_data=f"ap:ok:{c}:fo"),
                         Btn(text=f"Выйти: {str(v.get('ti') or c)[:14]}", callback_data=f"ap:lv:{c}")])
        rows.append([Btn(text="⬅ Назад", callback_data="ap:se")])
        return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows)

    def panel_journal(self, uid: int, chats: list, cid: int | None = None):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        owner, mine = uid in self.owners, set(chats)
        items = []
        for e in reversed(self.store.meta.get("journal") or []):
            if cid is not None and e.get("c") != cid:
                continue
            if not owner and e.get("c") not in mine:
                continue
            items.append(e)
            if len(items) >= 15:
                break
        title = esc(self.store.chats[cid].title or cid, 40) if cid is not None and cid in self.store.chats else ""
        lines = ["<b>📜 Журнал</b>" + (f" · {title}" if title else "")]
        if not items:
            lines.append("Записей нет.")
        for e in items:
            icon = self.JOURNAL_ICONS.get(e.get("k"), "•")
            where = f" «{esc(e['ti'], 22)}»" if e.get("ti") and cid is None else ""
            who = f" {esc(e['n'], 20)}" if e.get("n") else (f" id {e['by']}" if e.get("by") else "")
            lines.append(f"{self.fmt_when(e.get('t', 0))} {icon}{where}{who} — {esc(e.get('no', ''), 60)}")
        back = f"ap:c:{cid}" if cid is not None else "ap:m:0"
        return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=[[Btn(text="⬅ Назад", callback_data=back)]])

    def panel_summary(self) -> str:
        now = self.now()
        active = [c for c, s in self.store.chats.items() if s.active and c < 0]
        dead = sum(1 for s in self.store.chats.values() if not s.active)
        users = sum(len(s.users) for s in self.store.chats.values())
        sl = self.stat_lines(self.stat_sum(active), limit=6)
        per = sorted(((sum(self.stat_sum([c]).values()), c) for c in active), reverse=True)[:5]
        try:
            size = f"{os.path.getsize(self.store.path) / 1024:.0f} КБ"
        except OSError:
            size = "—"
        lines = ["<b>📊 Сводка</b>", f"Версия: {VERSION} · работаю: {fmt_uptime(now - self.started)}",
                 f"Чатов: {len(active)}" + (f" (ушёл из {dead})" if dead else ""),
                 f"Допуск: {'по списку (' + str(len(self.allowed_ids())) + ')' if self.allow_mode() else 'везде'}"
                 f" · чужих чатов: {len(self.foreign_list())}",
                 f"Участников в памяти: {users}",
                 f"Пропусков в ожидании: {len(self.store.captchas)} · напоминаний: {len(self.store.meta.get('reminders') or [])}"
                 f" · опросов: {sum(1 for p in (self.store.meta.get('polls') or {}).values() if not p.get('x'))}",
                 f"Файл состояния: {size} · владельцев: {len(self.owners)} · журнал: {len(self.store.meta.get('journal') or [])}",
                 "За 3 дня: " + (" · ".join(sl) if sl else "тихо")]
        if per and per[0][0]:
            lines.append("<i>Самые беспокойные чаты</i>")
            for n, c in per:
                if n:
                    lines.append(f"• {esc(self.store.chats[c].title or c, 40)} — {n}")
        return "\n".join(lines)

    async def _refuse(self, m, uid: int):
        if self.owners:
            log.info("панель: отказ, uid=%s не владелец", uid)
            return None
        return await self.out(m, f"Владельцы бота не заданы. Ваш id: <code>{uid}</code>. Укажите его в GUARD_ADMIN_IDS "
                                 "и перезапустите бота.")

    async def panel_send_main(self, m, uid: int):
        chats = await self.panel_chats(uid)
        if not chats and uid not in self.owners:
            return await self._refuse(m, uid)
        text, kb = self.panel_main(uid, chats, 0)
        return await self.out(m, text, markup=kb)

    async def cmd_panel(self, m, args):
        if getattr(m.chat, "type", "") != "private":
            if self._cool(m.chat.id, "panel", 30):
                await self.out(m, f"Панель доступна в личных сообщениях: @{self.username}, команда /panel.", ttl=20)
            return
        if m.from_user is None:
            return
        uid = m.from_user.id
        if self.panel_hash is not None and not self.panel_open(uid):
            if args:
                ok = await self.try_unlock(uid, args)
                await self.call("delete_message", m.chat.id, m.message_id)
                if not ok:
                    return await (self.out(m, "🔒 Панель закрыта.") if await self.is_staff(uid) else self._refuse(m, uid))
            elif await self.is_staff(uid):
                return await self.out(m, "Панель закрыта. Отправьте слово доступа отдельным сообщением.")
            else:
                return await self._refuse(m, uid)
        else:
            self.panel_touch(uid)
        await self.panel_send_main(m, uid)

    async def cmd_admin(self, m, args):
        await self.cmd_panel(m, args)

    async def cmd_cancel(self, m, args):
        if getattr(m.chat, "type", "") != "private" or m.from_user is None:
            return
        if self._pending.pop(m.from_user.id, None) is not None:
            await self.out(m, "Отменено. Панель — /panel.")
        else:
            await self.out(m, "Нет активных операций.")

    async def _panel_edit(self, msg, text: str, kb=None) -> None:
        extra = {"reply_markup": kb} if kb is not None else {}
        await self.call("edit_message_text", text, chat_id=msg.chat.id, message_id=msg.message_id, **extra)

    async def _panel_home(self, msg, uid: int, page: int = 0, prefix: str = "") -> None:
        text, kb = self.panel_main(uid, await self.panel_chats(uid), page)
        await self._panel_edit(msg, (prefix + "\n\n" if prefix else "") + text, kb)

    async def _panel_chat_screen(self, msg, cid: int, uid: int = 0) -> None:
        text, kb = await self.panel_chat(cid, uid)
        await self._panel_edit(msg, text, kb)

    async def _panel_back_only(self, msg, text: str, back: str = "ap:m:0") -> None:
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        await self._panel_edit(msg, text, InlineKeyboardMarkup(inline_keyboard=[[Btn(text="⬅ Назад", callback_data=back)]]))

    async def _allow_chat(self, cid: int, uid: int, hello: bool = True) -> None:
        allowed = self.store.meta.setdefault("allowed", [])
        if cid not in allowed:
            allowed.append(cid)
        info = (self.store.meta.get("foreign") or {}).get(str(cid), {})
        self.foreign_forget(cid)
        self.journal("allow", cid, info.get("ti") or (self.store.chats[cid].title if cid in self.store.chats else ""), uid,
                     note="чат разрешён владельцем")
        self.store.dirty = True
        if hello:
            await self.call("send_message", cid, "Чат разрешён. Бот активен.")

    async def on_panel_button(self, cb) -> None:
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        parts = (cb.data or "").split(":")
        msg, uid = getattr(cb, "message", None), cb.from_user.id
        if msg is None or getattr(msg.chat, "type", "") != "private" or msg.chat.id != uid or len(parts) < 2:
            return await cb.answer()
        act, now = parts[1], self.now()
        owner = uid in self.owners
        if act == "n":
            return await cb.answer()
        if not self.panel_open(uid):
            return await cb.answer("Панель закрыта. Отправьте слово доступа отдельным сообщением.", show_alert=True)
        self.panel_touch(uid)
        if act == "x":
            self._pending.pop(uid, None)
            await self.call("delete_message", msg.chat.id, msg.message_id)
            return await cb.answer()
        if act == "lo":
            self._pending.pop(uid, None)
            self._unlocked.pop(uid, None)
            await self.call("delete_message", msg.chat.id, msg.message_id)
            return await cb.answer("Панель закрыта. Чтобы открыть снова — назови слово.")
        if act == "m":
            if not owner and not await self.panel_chats(uid):
                return await cb.answer("Нет доступа.")
            try:
                page = int(parts[2]) if len(parts) > 2 else 0
            except ValueError:
                page = 0
            await self._panel_home(msg, uid, page)
            return await cb.answer()
        if act == "no":
            self._pending.pop(uid, None)
            await self._panel_home(msg, uid)
            return await cb.answer("Отменено.")
        if act == "go":
            return await self._panel_send(cb, msg, uid)
        if act == "jr":
            chats = await self.panel_chats(uid)
            cid = None
            if len(parts) > 2:
                try:
                    cid = int(parts[2])
                except ValueError:
                    return await cb.answer()
                if not await self.panel_can(uid, cid):
                    return await cb.answer("Нет доступа к этому чату.", show_alert=True)
            elif not owner and not chats:
                return await cb.answer("Нет доступа.")
            text, kb = self.panel_journal(uid, chats, cid)
            await self._panel_edit(msg, text, kb)
            return await cb.answer()
        if act in self.OWNER_ACTS:
            if not owner:
                return await cb.answer("Только для владельца бота.", show_alert=True)
            return await self._panel_owner(cb, msg, uid, parts, now)
        try:
            cid = int(parts[2])
        except (ValueError, IndexError):
            return await cb.answer()
        if not await self.panel_can(uid, cid):
            return await cb.answer("Нет доступа к этому чату.", show_alert=True)
        cfg = self.store.chats[cid].cfg
        if act == "c":
            await self._panel_chat_screen(msg, cid, uid)
            return await cb.answer()
        if act == "t":
            code = parts[3] if len(parts) > 3 else ""
            for c, _label, attr in SETTINGS:
                if c != code:
                    continue
                if attr == "links":
                    i = LINK_POLICIES.index(cfg.links) if cfg.links in LINK_POLICIES else 1
                    cfg.links = LINK_POLICIES[(i + 1) % len(LINK_POLICIES)]
                else:
                    setattr(cfg, attr, not getattr(cfg, attr))
                self.store.dirty = True
                break
            await self._panel_chat_screen(msg, cid, uid)
            return await cb.answer()
        if act == "pr":
            text, kb = self.panel_prot(cid)
            await self._panel_edit(msg, text, kb)
            return await cb.answer()
        if act == "pt":
            what = parts[3] if len(parts) > 3 else ""
            if what == "cp":
                cfg.captcha = not cfg.captcha
            elif what == "sk":
                cfg.captcha_smart = not cfg.captcha_smart
            elif what == "sl":
                cfg.smart_links = not cfg.smart_links
            elif what == "lp":
                i = LINK_POLICIES.index(cfg.links) if cfg.links in LINK_POLICIES else 1
                cfg.links = LINK_POLICIES[(i + 1) % len(LINK_POLICIES)]
            elif what == "ct":
                cfg.captcha_timeout = self._cycle(self.TIMEOUTS, cfg.captcha_timeout)
            elif what == "bm":
                cfg.captcha_ban_min = self._cycle(self.BANS, cfg.captcha_ban_min)
            else:
                return await cb.answer()
            self.store.dirty = True
            text, kb = self.panel_prot(cid)
            await self._panel_edit(msg, text, kb)
            return await cb.answer()
        if act == "lk":
            self.eng.ring_start(cid, f"lock:{cid}", "lockdown", (), (), ttl=15 * 60, now=now)
            if not cfg.quiet:
                await self.notice(cid, "lockdown_on", ttl=0, mins=human_dur(900))
            await self._panel_chat_screen(msg, cid, uid)
            return await cb.answer("Чат закрыт на 15 минут.")
        if act == "op":
            if self.eng.ring_end_chat(cid, ("lockdown",)) and not cfg.quiet:
                await self.notice(cid, "lockdown_off", ttl=60)
            await self._panel_chat_screen(msg, cid, uid)
            return await cb.answer("Открыто.")
        if act == "rd":
            on = self.eng.raid_until.get(cid, 0) - now <= 0
            self.eng.raid_set(cid, on, now)
            if not cfg.quiet:
                await self.notice(cid, "raid_on" if on else "raid_off", ttl=120, mins=human_dur(RAID_HOLD))
            await self._panel_chat_screen(msg, cid, uid)
            return await cb.answer("Наплыв включён." if on else "Наплыв выключен.")
        if act == "bl":
            if self.eng.ring_end_chat(cid, ("group", "arena", "manual")) and not cfg.quiet:
                await self.notice(cid, "ring_end", ttl=60)
            await self._panel_chat_screen(msg, cid, uid)
            return await cb.answer("Сессия завершена.")
        if act == "st":
            sl = self.stat_sum([cid])
            body = "\n".join(f"• {STAT_LABELS.get(k, k)}: {v}" for k, v in sorted(sl.items(), key=lambda kv: -kv[1])) or "Тихо."
            await self._panel_back_only(msg, f"<b>{esc(self.store.chats[cid].title or cid, 60)} · за 3 дня</b>\n{body}", f"ap:c:{cid}")
            return await cb.answer()
        if act == "an":
            self._pending[uid] = {"kind": "ann", "cid": cid, "exp": now + PANEL_INPUT_TTL, "stage": "wait", "text": ""}
            await self._panel_edit(msg, f"<b>Объявление в «{esc(self.store.chats[cid].title or cid, 60)}»</b>\n"
                                        "Отправьте текст одним сообщением. Отмена: /cancel.",
                                   InlineKeyboardMarkup(inline_keyboard=[[Btn(text="⬅ Отмена", callback_data=f"ap:c:{cid}")]]))
            return await cb.answer()
        await cb.answer()

    async def _panel_owner(self, cb, msg, uid: int, parts: list, now: float) -> None:
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        act = parts[1]
        if act == "sm":
            await self._panel_back_only(msg, self.panel_summary())
            return await cb.answer()
        if act == "bc":
            self._pending[uid] = {"kind": "bc", "cid": 0, "exp": now + PANEL_INPUT_TTL, "stage": "wait", "text": ""}
            await self._panel_edit(msg, "<b>Рассылка во все чаты</b>\nОтправьте текст одним сообщением. Отмена: /cancel.",
                                   InlineKeyboardMarkup(inline_keyboard=[[Btn(text="⬅ Отмена", callback_data="ap:no")]]))
            return await cb.answer()
        if act == "se":
            text, kb = self.panel_secrets()
            await self._panel_edit(msg, text, kb)
            return await cb.answer()
        if act == "cf":
            key = parts[2] if len(parts) > 2 else ""
            popup = None
            if key == "allow_mode":
                if self.allowed_env:
                    return await cb.answer("Список задан в окружении (GUARD_ALLOWED_CHATS): убери его из .env, чтобы выключить.",
                                           show_alert=True)
                if self.conf("allow_mode", False):
                    self.conf_set("allow_mode", False)
                    popup = "Режим списка выключен: работаю везде."
                else:
                    allowed = self.store.meta.setdefault("allowed", [])
                    seeded = 0
                    for c, s in self.store.chats.items():
                        if s.active and c < 0 and c not in allowed:
                            allowed.append(c)
                            seeded += 1
                    self.conf_set("allow_mode", True)
                    popup = f"Режим списка включён. Действующие чаты внесены в список: {seeded}."
            elif key in ("strict_add", "notify_adds"):
                cur = self.strict_on() if key == "strict_add" else self.notify_on()
                self.conf_set(key, not cur)
                popup = f"{'Строгое добавление' if key == 'strict_add' else 'Уведомления'}: {self._on(not cur)}."
            else:
                return await cb.answer()
            text, kb = self.panel_secrets()
            await self._panel_edit(msg, text, kb)
            return await cb.answer(popup)
        if act == "al":
            text, kb = self.panel_allowed()
            await self._panel_edit(msg, text, kb)
            return await cb.answer()
        if act == "fo":
            text, kb = self.panel_foreign()
            await self._panel_edit(msg, text, kb)
            return await cb.answer()
        if act in ("ar", "ok", "dn", "lv", "lv2"):
            try:
                cid = int(parts[2])
            except (ValueError, IndexError):
                return await cb.answer()
            if act == "ar" or act == "dn":
                if cid in self.allowed_env:
                    return await cb.answer("Этот чат задан в окружении (GUARD_ALLOWED_CHATS).", show_alert=True)
                allowed = self.store.meta.setdefault("allowed", [])
                if cid in allowed:
                    allowed.remove(cid)
                    self.store.dirty = True
                    self.journal("deny", cid, self.store.chats[cid].title if cid in self.store.chats else "", uid,
                                 note="чат убран из списка")
                if act == "ar":
                    text, kb = self.panel_allowed()
                    await self._panel_edit(msg, text, kb)
                else:
                    await self._panel_chat_screen(msg, cid, uid)
                return await cb.answer("Убрано из списка.")
            if act == "ok":
                await self._allow_chat(cid, uid)
                where = parts[3] if len(parts) > 3 else ""
                if where == "fo":
                    text, kb = self.panel_foreign()
                    await self._panel_edit(msg, text, kb)
                elif where == "c" and cid in self.store.chats:
                    await self._panel_chat_screen(msg, cid, uid)
                else:
                    await self._panel_back_only(msg, f"✅ Чат <code>{cid}</code> разрешён. Бот активен.")
                return await cb.answer("Чат разрешён.")
            title = (self.store.chats[cid].title if cid in self.store.chats
                     else (self.store.meta.get("foreign") or {}).get(str(cid), {}).get("ti", "")) or str(cid)
            if act == "lv":
                await self._panel_edit(msg, f"Выйти из «{esc(title, 50)}» (<code>{cid}</code>)? Повторное добавление возможно только администраторами чата.",
                                       InlineKeyboardMarkup(inline_keyboard=[[
                                           Btn(text="✅ Да, выйти", callback_data=f"ap:lv2:{cid}"),
                                           Btn(text="⬅ Нет", callback_data="ap:m:0")]]))
                return await cb.answer()
            self._leaving.add(cid)
            await self.call("leave_chat", cid)
            if cid in self.store.chats:
                self.store.chats[cid].active = False
            self.foreign_forget(cid)
            self.journal("leave", cid, title, uid, note="вышел по команде владельца")
            self.store.dirty = True
            await self._panel_back_only(msg, f"Бот покинул чат «{esc(title, 50)}».")
            return await cb.answer("Вышел.")
        if act == "ai":
            self._pending[uid] = {"kind": "allowid", "cid": 0, "exp": now + PANEL_INPUT_TTL, "stage": "wait", "text": ""}
            await self._panel_edit(msg, "<b>Разрешить чат по номеру</b>\nОтправьте номер чата, например <code>-1001234567890</code> "
                                        "(узнать: команда /id в самом чате). Отмена: /cancel.",
                                   InlineKeyboardMarkup(inline_keyboard=[[Btn(text="⬅ Отмена", callback_data="ap:al")]]))
            return await cb.answer()
        await cb.answer()

    async def on_other(self, m) -> None:
        if getattr(m.chat, "type", "") != "private" or getattr(m, "from_user", None) is None:
            return
        uid = m.from_user.id
        txt = (getattr(m, "text", None) or "").strip()
        if self.panel_hash is not None and not self.panel_open(uid):
            if txt and await self.try_unlock(uid, txt):
                await self.call("delete_message", m.chat.id, m.message_id)
                await self.panel_send_main(m, uid)
            return
        p = self._pending.get(uid)
        if not txt or p is None or p.get("stage") != "wait":
            return
        self.panel_touch(uid)
        if self.now() > p["exp"]:
            self._pending.pop(uid, None)
            return await self.out(m, "Время ввода истекло. Откройте /panel заново.")
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        if p["kind"] == "allowid":
            self._pending.pop(uid, None)
            ids = parse_chat_ids(txt)
            if uid not in self.owners or len(ids) != 1:
                return await self.out(m, "Требуется один номер чата, например <code>-1001234567890</code>. Повторите через /panel.")
            (cid,) = ids
            await self._allow_chat(cid, uid, hello=False)
            return await self.out(m, f"Чат <code>{cid}</code> внесён в список. Если бот уже в чате, он начнёт работу сразу.")
        p["text"], p["stage"] = txt[:1500], "confirm"
        if p["kind"] == "bc":
            n = sum(1 for s in self.store.chats.values() if s.active)
            head = f"Отправить во все чаты ({n})?"
        else:
            head = f"Отправить в «{esc(self.store.chats[p['cid']].title or p['cid'], 60)}»?"
        kb = InlineKeyboardMarkup(inline_keyboard=[[Btn(text="✅ Отправить", callback_data="ap:go"),
                                                    Btn(text="✖ Отмена", callback_data="ap:no")]])
        await self.out(m, f"<b>{head}</b>\n\n{esc(p['text'], 1500)}", markup=kb)

    async def _panel_send(self, cb, msg, uid: int) -> None:
        p = self._pending.pop(uid, None)
        if p is None or p.get("stage") != "confirm" or self.now() > p["exp"]:
            return await cb.answer("Нечего отправлять: ввод устарел.", show_alert=True)
        text = f"📢 <b>Объявление</b>\n{esc(p['text'], 1500)}"
        if p["kind"] == "ann":
            if not await self.panel_can(uid, p["cid"]):
                return await cb.answer("Нет доступа к этому чату.", show_alert=True)
            ok = await self.call("send_message", p["cid"], text) is not None
            result = "Объявление отправлено." if ok else "Ошибка: у бота нет доступа к чату."
        else:
            if uid not in self.owners:
                return await cb.answer("Только для владельца бота.", show_alert=True)
            sent = fail = 0
            for c in [c for c, s in self.store.chats.items() if s.active and c < 0 and self.chat_ok(c)]:
                if await self.call("send_message", c, text) is not None:
                    sent += 1
                else:
                    fail += 1
                if PANEL_BC_DELAY:
                    await asyncio.sleep(PANEL_BC_DELAY)
            result = f"✅ Разослано: {sent}" + (f", не вышло: {fail}" if fail else "") + "."
        await self._panel_home(msg, uid, prefix=result)
        await cb.answer("Готово.")


log_plus = logging.getLogger("guard.plus")

CAS_URL = "https://api.cas.chat/check?user_id={}"
CAS_TTL, CAS_RETRY, CAS_RATE = 12 * 3600, 300, 40

LOCK_LABELS = {
    "voice": "голосовые", "videonote": "кружки", "sticker": "стикеры", "gif": "гифки", "photo": "фото",
    "video": "видео", "audio": "музыка", "document": "файлы", "contact": "контакты", "location": "геопозиции",
    "poll": "опросы", "dice": "кубики и игры-эмодзи", "game": "игры", "forward": "пересылки",
    "inline": "сообщения через inline-ботов", "emoji": "кастомные эмодзи", "cashtag": "кэштеги ($TON)",
    "checklist": "чек-листы", "story": "истории", "invitelink": "ссылки-приглашения в другие чаты",
    "channel": "сообщения от имени каналов",
}
LOCK_GROUPS = {"media": ("photo", "video", "gif", "sticker", "voice", "videonote", "audio", "document")}
NIGHT_MEDIA = frozenset(LOCK_GROUPS["media"])
LOCK_ALIASES = {
    "голосовые": "voice", "голос": "voice", "кружки": "videonote", "кружок": "videonote", "стикеры": "sticker",
    "стикер": "sticker", "гифки": "gif", "гиф": "gif", "фото": "photo", "видео": "video", "музыка": "audio",
    "аудио": "audio", "файлы": "document", "документы": "document", "контакты": "contact", "геопозиции": "location",
    "опросы": "poll", "кубики": "dice", "игры": "game", "пересылки": "forward", "пересылка": "forward",
    "эмодзи": "emoji", "кэштеги": "cashtag", "чеклисты": "checklist", "истории": "story",
    "приглашения": "invitelink", "каналы": "channel", "медиа": "media",
}
INVITE_RE = re.compile(r"(?:t\.me|telegram\.me|telegram\.dog)/(?:\+|joinchat/)", re.I)
CLOCK_RE = re.compile(r"^(\d{1,2})[:.](\d{2})$")
FILTERS_MAX, FILTER_TRIGGER_MAX, FILTER_REPLY_MAX, FILTER_TTL = 30, 40, 800, 600
REPEAT_PER_CHAT, REPEAT_MIN_MIN, REPEAT_MAX_MIN, REPEAT_TEXT_MAX = 5, 30, 30 * 1440, 600
GBANS_SHOW = 15


def cas_lookup(uid: int, timeout: float = 4.0):
    try:
        req = urllib.request.Request(CAS_URL.format(int(uid)), headers={"User-Agent": f"guard-bot/{VERSION}"})
        with urllib.request.urlopen(req, timeout=timeout) as r:
            data = json.loads(r.read(65536).decode("utf-8", "replace"))
        return bool(data.get("ok")) if isinstance(data, dict) else None
    except (urllib.error.URLError, OSError, ValueError, TimeoutError):
        return None


def content_kinds(m, as_channel: bool = False) -> set:
    g = lambda n: getattr(m, n, None)
    k: set = set()
    if g("voice"):
        k.add("voice")
    if g("video_note"):
        k.add("videonote")
    if g("sticker"):
        k.add("sticker")
    if g("animation"):
        k.add("gif")
    elif g("document"):
        k.add("document")
    if g("photo"):
        k.add("photo")
    if g("video"):
        k.add("video")
    if g("audio"):
        k.add("audio")
    if g("contact"):
        k.add("contact")
    if g("location") or g("venue"):
        k.add("location")
    if g("poll"):
        k.add("poll")
    if g("dice"):
        k.add("dice")
    if g("game"):
        k.add("game")
    if g("forward_origin") or g("forward_date"):
        k.add("forward")
    if g("via_bot"):
        k.add("inline")
    if g("story"):
        k.add("story")
    if g("checklist"):
        k.add("checklist")
    if as_channel:
        k.add("channel")
    ents = list(g("entities") or []) + list(g("caption_entities") or [])
    for e in ents:
        t = getattr(e, "type", "")
        t = str(getattr(t, "value", t))
        if t == "custom_emoji":
            k.add("emoji")
        elif t == "cashtag":
            k.add("cashtag")
    text = f"{g('text') or ''} {g('caption') or ''}"
    if INVITE_RE.search(text) or any(INVITE_RE.search(getattr(e, "url", None) or "") for e in ents):
        k.add("invitelink")
    return k


def parse_clock(tok: str):
    mm = CLOCK_RE.match((tok or "").strip())
    if not mm:
        return None
    h, mi = int(mm.group(1)), int(mm.group(2))
    return h * 60 + mi if h < 24 and mi < 60 else None


def fmt_clock(minutes: int) -> str:
    return f"{minutes // 60:02d}:{minutes % 60:02d}"


def parse_night(spec: str):
    a, sep, b = (spec or "").partition("-")
    if not sep:
        return None
    s, e = parse_clock(a), parse_clock(b)
    if s is None or e is None or s == e:
        return None
    return s, e


def in_night(spec: str, now: float, tz_h: int) -> bool:
    w = parse_night(spec)
    if w is None:
        return False
    lm = int(((now + tz_h * 3600) % 86400) // 60)
    s, e = w
    return s <= lm < e if s < e else (lm >= s or lm < e)


def split_filter_args(args: str):
    a = args.strip()
    closers = {'"': '"', "«": "»", "“": "”"}
    if a[:1] in closers:
        j = a.find(closers[a[0]], 1)
        if j > 1:
            return a[1:j].strip(), a[j + 1:].strip()
    trig, _, rest = a.partition(" ")
    return trig, rest.strip()


@lru_cache(maxsize=2048)
def _filter_rx(trig: str):
    return re.compile(r"(?<!\w)" + re.escape(fold(trig)) + r"(?!\w)")


class Plus:

    def init_plus(self) -> None:
        self.cas_on: bool = True
        self.log_chat_env: int = 0
        self._cas_cache: dict = {}
        self._cas_hist: deque = deque(maxlen=200)
        self._night_state: dict = {}

    async def need_owner(self, m) -> bool:
        u = getattr(m, "from_user", None)
        if u is not None and u.id in self.owners and not self.is_anon_sender(m):
            return True
        if self.in_group(m):
            await self.say(m, "need_admin", ttl=10)
            self.deleter.add(m.chat.id, [m.message_id])
        return False

    def gbans(self) -> dict:
        return self.store.meta.setdefault("gbans", {})

    async def plus_cas(self, uid: int) -> bool:
        if not self.cas_on or uid <= 0:
            return False
        now = self.now()
        hit = self._cas_cache.get(uid)
        if hit and now - hit[0] < CAS_TTL:
            return hit[1]
        h = self._cas_hist
        while h and now - h[0] > 60:
            h.popleft()
        if len(h) >= CAS_RATE:
            return False
        h.append(now)
        res = await asyncio.to_thread(cas_lookup, uid)
        if res is None:
            self._cas_cache[uid] = (now - CAS_TTL + CAS_RETRY, False)
            return False
        self._cas_cache[uid] = (now, res)
        if len(self._cas_cache) > 6000:
            self._cas_cache = {k: v for k, v in self._cas_cache.items() if now - v[0] < CAS_TTL}
        return res

    async def plus_screen(self, chat, uid: int, name: str, msg_id: int | None = None, deep: bool = True) -> bool:
        try:
            return await self._plus_screen(chat, uid, name, msg_id, deep)
        except asyncio.CancelledError:
            raise
        except Exception:
            log_plus.exception("проверка по общим спискам: сбой")
            return False

    async def _plus_screen(self, chat, uid: int, name: str, msg_id, deep: bool) -> bool:
        if uid <= 0 or uid in self.owners or self.is_trusted(uid) or uid == self.me_id:
            return False
        state = self.store.chat(chat.id, chat.title or "")
        cfg = state.cfg
        if not cfg.enabled:
            return False
        entry = self.gbans().get(str(uid))
        if entry:
            why = f"общий чёрный список: {entry.get('r') or 'без причины'}"
        elif deep and cfg.cas and await self.plus_cas(uid):
            why = "база спамеров CAS"
        else:
            return False
        rights = await self.rights(chat.id)
        if not rights["restrict"]:
            return False
        if await self.call("ban_chat_member", chat.id, uid, revoke_messages=True) is None:
            return False
        if msg_id and rights["delete"]:
            self.deleter.add(chat.id, [msg_id])
        self.store.user(state, uid, self.now()).banned = True
        self.store.bump(state, "gban" if entry else "cas_ban")
        await self.fort_feed(chat.id, uid, "cas")
        self.journal("gban" if entry else "cas", chat.id, chat.title or "", uid, name, why)
        if not cfg.quiet:
            await self.announce(chat.id, f"🛡 {mention(uid, name)} заблокирован: {esc(why, 90)}.", ttl=60)
        await self.plus_log(chat.id, f"🛡 <b>{esc(chat.title, 60)}</b>\n{mention(uid, name)} (<code>{uid}</code>) — бан: {esc(why, 120)}")
        return True

    async def plus_log(self, chat_id: int, text: str) -> None:
        state = self.store.chat(chat_id, create=False)
        target = (state.cfg.logchat if state else 0) or self.log_chat_env
        if not target or target == chat_id:
            return
        await self.call("send_message", target, text[:3500], disable_notification=True)

    async def cmd_setlog(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        a = args.strip().lower()
        if a in ("off", "выкл", "0"):
            cfg.logchat = 0
            self.store.dirty = True
            return await self.out(m, "Журнал действий для этого чата выключен.", ttl=20)
        try:
            target = int(a)
        except ValueError:
            cur = f"сейчас: <code>{cfg.logchat}</code>" if cfg.logchat else "сейчас выключен"
            return await self.out(m, "/setlog <i>id чата или канала</i> — слать в него журнал банов и ограничений "
                                     f"({cur}). Бота нужно добавить туда с правом публикации. /setlog off — выключить.", ttl=40)
        if target == m.chat.id:
            return await self.out(m, "Журнал должен идти в другой чат или канал, не в этот.", ttl=20)
        ok = await self.call("send_message", target, f"📋 Журнал чата «{esc(m.chat.title, 60)}» подключён.",
                             disable_notification=True)
        if ok is None:
            return await self.out(m, "Не получилось написать туда: добавьте бота в этот чат или канал и дайте право публикации.", ttl=30)
        cfg.logchat = target
        self.store.dirty = True
        await self.out(m, "Журнал подключён: баны, ограничения и срабатывания по общим спискам будут приходить туда.", ttl=30)

    async def cmd_gban(self, m, args):
        if not await self.need_owner(m):
            return
        grp = self.in_group(m)
        if grp:
            self.cleanup(m)
        toks = args.split()
        if grp:
            found, _ = await self.resolve_all(m, args)
        else:
            found = [(int(t), t) for t in toks[:1] if t.isdigit() and len(t) >= 6]
        if not found:
            return await self.out(m, "/gban <i>id</i> [причина] — или ответом на сообщение. Блокирует участника во всех чатах, где бот "
                                     "администратор, и не пускает обратно. Снять: /ungban <i>id</i>. Список: /gbans.",
                                  ttl=40 if grp else 0)
        uid, label = found[0]
        consumed = 1 if toks and (toks[0].startswith("@") or toks[0].lstrip("-").isdigit()) else 0
        reason = " ".join(toks[consumed:])[:100]
        if uid <= 0 or uid in self.owners or self.is_trusted(uid) or uid == self.me_id:
            return await self.out(m, "Этого участника нельзя внести в общий список.", ttl=15 if grp else 0)
        now = self.now()
        done = []
        for cid, st in list(self.store.chats.items()):
            if cid >= 0 or not st.active or not self.chat_ok(cid):
                continue
            if not (await self.rights(cid))["restrict"]:
                continue
            if await self.call("ban_chat_member", cid, uid, revoke_messages=True) is not None:
                done.append(cid)
                self.store.user(st, uid, now).banned = True
            await asyncio.sleep(0.05)
        self.gbans()[str(uid)] = {"r": reason, "t": round(now), "by": m.from_user.id, "n": str(label)[:40], "ch": done}
        self.store.dirty = True
        self.journal("gban_add", 0, "", m.from_user.id, str(label), f"{uid}: {reason or 'без причины'}")
        await self.out(m, f"🛡 <code>{uid}</code> внесён в общий список. Заблокирован в чатах: {len(done)}."
                          + (f"\nПричина: {esc(reason, 100)}" if reason else ""), ttl=60 if grp else 0)

    async def cmd_ungban(self, m, args):
        if not await self.need_owner(m):
            return
        grp = self.in_group(m)
        if grp:
            self.cleanup(m)
        tok = (args.split() or [""])[0]
        if not tok.lstrip("-").isdigit():
            found, _ = await self.resolve_all(m, args) if grp else ([], 0)
            tok = str(found[0][0]) if found else ""
        entry = self.gbans().pop(tok, None) if tok else None
        if entry is None:
            return await self.out(m, "Такого id нет в общем списке. /ungban <i>id</i>; список — /gbans.", ttl=20 if grp else 0)
        for cid in entry.get("ch", []):
            await self.call("unban_chat_member", cid, int(tok), only_if_banned=True)
            await asyncio.sleep(0.05)
        self.store.dirty = True
        self.journal("gban_del", 0, "", m.from_user.id, tok, "")
        await self.out(m, f"Из общего списка убран <code>{esc(tok, 20)}</code>; разблокирован в чатах, где его блокировал список.",
                       ttl=40 if grp else 0)

    async def cmd_gbans(self, m, args):
        if not await self.need_owner(m):
            return
        grp = self.in_group(m)
        if grp:
            self.cleanup(m)
        book = self.gbans()
        if not book:
            return await self.out(m, "Общий чёрный список пуст.", ttl=20 if grp else 0)
        rows = sorted(book.items(), key=lambda kv: -kv[1].get("t", 0))[:GBANS_SHOW]
        lines = [f"<b>Общий чёрный список</b> ({len(book)})"]
        for uid, e in rows:
            lines.append(f"• <code>{esc(uid, 20)}</code> {esc(e.get('n', ''), 30)} — {esc(e.get('r') or 'без причины', 60)} "
                         f"({self.fmt_when(e.get('t', 0))})")
        if len(book) > GBANS_SHOW:
            lines.append(f"<i>…и ещё {len(book) - GBANS_SHOW}</i>")
        await self.out(m, "\n".join(lines), ttl=90 if grp else 0)

    async def cmd_spamlist(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        rows = self.eng.spam_memory_list(m.chat.id)
        learned = self.eng.learn_summary(m.chat.id)
        if not rows:
            return await self.out(m, "Память о пойманном спаме пуста." + (("\n" + learned) if learned else ""), ttl=30)
        now = self.now()
        lines = [f"<b>Память о пойманном спаме</b> ({len(rows)}): контакты, которые бот уже ловил. "
                 f"Новичок с таким контактом — удаление сообщения."]
        for tok, e in rows[:SPAMLIST_SHOW]:
            left = max(0.0, e.get("ttl", SPAM_MEM_TTL) - (now - e.get("t", 0)))
            lines.append(f"• <code>{esc(tok, 60)}</code> — {esc(e.get('w', ''), 50)}; повторов: {e.get('n', 0)}; "
                         f"забуду через {human_dur(left)}")
        if len(rows) > SPAMLIST_SHOW:
            lines.append(f"<i>…и ещё {len(rows) - SPAMLIST_SHOW}</i>")
        lines.append("Убрать одну запись: /forget <i>контакт</i>; всё сразу: /forget all")
        if learned:
            lines.append(learned)
        await self.out(m, "\n".join(lines), ttl=90)

    async def cmd_forget(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        arg = args.strip()
        if not arg:
            return await self.out(m, "/forget <i>контакт</i> — стереть запись (@имя, домен или телефон); /forget all — стереть всё; "
                                     "/forget learn — сбросить самообучение этого чата. Список: /spamlist.", ttl=30)
        low = arg.lower().split()
        if low and low[0] in ("learn", "обучение"):
            whole = len(low) > 1 and low[1] == "all"
            if whole and m.from_user.id not in self.owners:
                return await self.out(m, "Общие шаблоны спама стирает только владелец бота.", ttl=20)
            n = self.eng.learn_reset(m.chat.id, whole)
            return await self.out(m, f"Самообучение этого чата сброшено ({n} записей)" + (" вместе с общими шаблонами спама." if whole else
                                  ". Общие шаблоны спама остались: /forget learn all сотрёт и их."), ttl=30)
        n = self.eng.spam_memory_forget(m.chat.id, None if arg.lower() == "all" else arg)
        await self.out(m, f"Стёрто записей: {n}." if n else "Такой записи нет. Список: /spamlist.", ttl=20)

    async def handle_events(self) -> None:
        evs, self.eng.events = self.eng.events, []
        for ev in evs:
            try:
                await self._one_event(ev)
            except Exception:
                log.exception("событие движка не обработано: %s", ev.get("kind"))

    async def _one_event(self, ev: dict) -> None:
        kind, cid = ev["kind"], ev.get("chat", 0)
        st = self.store.chats.get(cid)
        title = esc(st.title if st else "", 60)
        if kind in ("provocation", "provocation_repeat", "dogpile"):
            self.ap_feed_heat(ev, cid)
        if kind == "scam_ban":
            await self.invite_bad(cid, ev["uid"])
        elif kind == "provocation":
            how = "страйк смягчён: у него чистая история" if ev["softened"] else "страйк обычный"
            await self.plus_log(cid, f"🎭 <b>{title}</b>\nПохоже на провокацию: {mention(ev['baiter'])} задел {mention(ev['victim'])}, "
                                     f"и тот сорвался. Для сорвавшегося: {how}. Задевшего бот не трогал.")
        elif kind == "provocation_repeat":
            await self.alert(cid, f"🎭 <b>{title}</b>\n{mention(ev['baiter'])} за сутки уже {ev['n']} раза задел людей так, что те "
                                  f"срывались. Бот его не наказывал: посмотрите сами.")
        elif kind == "dogpile":
            who = ", ".join(mention(u) for u in ev["people"][:6])
            text = (f"🐺 <b>{title}</b>\nПохоже на травлю: на сообщения {mention(ev['target'])} за пару минут ответили "
                    f"{ev['n']} человек (недружелюбно: {ev['hostile']}): {who}. Бот ничего не делал: загляните в чат.")
            await self.plus_log(cid, text)
            await self.alert(cid, text)
        elif kind == "fort_on":
            await self.fort_on_event(ev)
        elif kind == "fort_off":
            await self.fort_off_event(ev)
        elif kind == "ap":
            await self.ap_event(ev)

    async def _contacts_text(self, chat_id: int, uid: int, exclude=()) -> str:
        now = self.now()
        admins = await self.admins(chat_id)
        names = {u: n for n, u in self.store.chat(chat_id).names.items()}
        rows = [e for e in self.eng.contacts_of(chat_id, uid, now) if e["uid"] not in admins and e["uid"] not in exclude]
        if not rows:
            return ""
        parts = [f"{mention(e['uid'], '@' + names[e['uid']] if e['uid'] in names else '')} (он им: {e['to']}, они ему: {e['frm']})"
                 for e in rows[:CONTACTS_SHOW]]
        return "С ним переписывались за сутки (только список, никому ничего не отправлено): " + "; ".join(parts)

    async def cmd_contacts(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        r = getattr(m, "reply_to_message", None)
        uid = r.from_user.id if r is not None and getattr(r, "from_user", None) is not None else 0
        if not uid and args.strip().lstrip("-").isdigit():
            uid = int(args.strip())
        if not uid:
            return await self.out(m, "Ответьте командой /contacts на сообщение участника (или /contacts <i>id</i>).", ttl=20)
        text = await self._contacts_text(m.chat.id, uid)
        if not text:
            return await self.out(m, "За последние сутки этот участник ни с кем не переписывался ответами.", ttl=20)
        text = f"{mention(uid)}: {text[0].lower() + text[1:]}"
        if await self.alert(m.chat.id, text) == 0:
            await self.out(m, text, ttl=60)
        else:
            await self.out(m, "Список отправил вам в личку.", ttl=10)

    async def cmd_safety(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        res = await self.call("get_chat_administrators", m.chat.id)
        names = [mention(a.user.id, a.user.full_name) for a in (res or []) if not getattr(a.user, "is_bot", False)][:10]
        text = ("🛡 <b>Памятка о мошенниках</b>\n"
                + (f"Администраторы этого чата: {', '.join(names)}.\n" if names else "")
                + "• Никто из нас никогда не просит переводить деньги, называть коды из СМС, платить за «доступ» или «верификацию».\n"
                  "• Если в личные сообщения пишет «поддержка», «админ» или «бот» и зовёт куда-то перейти или заплатить — это обман. "
                  "Настоящих админов можно сверить по списку выше.\n"
                  "• Увидели подозрительное сообщение — ответьте на него командой /report.\n"
                  "Это объявление ничего у вас не просит.")
        sent = await self.call("send_message", m.chat.id, text, disable_notification=True)
        if sent is None:
            return await self.out(m, "Не удалось опубликовать памятку.", ttl=20)
        pinned = await self.call("pin_chat_message", m.chat.id, sent.message_id, disable_notification=True)
        await self.out(m, "Памятка опубликована и закреплена." if pinned is not None
                       else "Памятка опубликована, но закрепить не удалось: у бота нет права закреплять сообщения.", ttl=20)

    def _invites(self, chat_id: int, create: bool = False) -> dict | None:
        root = self.store.meta.setdefault("invites", {}) if create else self.store.meta.get("invites")
        if root is None:
            return None
        return root.setdefault(str(chat_id), {}) if create else root.get(str(chat_id))

    def invite_note(self, chat_id: int, uid: int, il) -> None:
        book = self._invites(chat_id)
        url = getattr(il, "invite_link", "") if il is not None else ""
        if not book or not url:
            return
        e = next((e for e in book.values() if e.get("url") == url), None)
        if e is None:
            return
        e["joined"] = e.get("joined", 0) + 1
        state = self.store.chat(chat_id)
        self.store.user(state, uid, self.now()).src = e["name"].lower()
        self.store.dirty = True

    async def invite_bad(self, chat_id: int, uid: int) -> None:
        state = self.store.chats.get(chat_id)
        rec = state.users.get(uid) if state else None
        book = self._invites(chat_id)
        if rec is None or not rec.src or not book:
            return
        e = book.get(rec.src)
        if e is None or (rec.joined and self.now() - rec.joined > INVITE_BAD_AGE):
            return
        e["bad"] = e.get("bad", 0) + 1
        self.store.dirty = True
        if (not e.get("warned") and not e.get("revoked") and e["bad"] >= INVITE_BAD_MIN
                and e["bad"] >= INVITE_BAD_SHARE * max(1, e.get("joined", 0))):
            e["warned"] = True
            await self.alert(chat_id, f"🔗 <b>{esc(state.title, 60)}</b>\nПо ссылке «{esc(e['name'], 24)}» вошло {e.get('joined', 0)}, "
                                      f"из них {e['bad']} уже забанены за спам. Возможно, ссылка попала не к тем людям. "
                                      f"Отозвать: /revoke {esc(e['name'], 24)} (бот сам ничего не отзывал).")

    async def cmd_invite(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        label = " ".join(args.split())
        if not INVITE_LABEL_RE.match(label):
            return await self.out(m, "Напишите метку: /invite <i>Петров</i> (до 24 символов: буквы, цифры, пробел, _ . -). "
                                     "Каждый, кто войдёт по этой ссылке, будет записан за меткой.", ttl=25)
        book = self._invites(m.chat.id, create=True)
        key = label.lower()
        if key in book and not book[key].get("revoked"):
            return await self.out(m, f"Метка «{esc(label, 24)}» уже занята: /links покажет сводку.", ttl=20)
        res = await self.call("create_chat_invite_link", m.chat.id, name=label)
        url = getattr(res, "invite_link", None) if res is not None else None
        if not url:
            return await self.out(m, "Не вышло создать ссылку: у бота должно быть право «Приглашать пользователей».", ttl=25)
        book[key] = {"name": label, "url": url, "t": self.now(), "joined": 0, "bad": 0, "revoked": False, "warned": False}
        self.store.dirty = True
        text = (f"Ссылка «{esc(label, 24)}»: {url}\nВсе, кто войдёт по ней, будут записаны за этой меткой. "
                f"/links — сводка, /revoke {esc(label, 24)} — отозвать.")
        if await self.alert(m.chat.id, text) == 0:
            await self.out(m, text, ttl=120)
        else:
            await self.out(m, "Ссылку отправил вам в личку.", ttl=10)

    async def cmd_links(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        book = self._invites(m.chat.id)
        if not book:
            return await self.out(m, "Ссылок с метками пока нет. Создать: /invite <i>метка</i>.", ttl=20)
        lines = ["<b>Ссылки с метками</b> (сколько вошло и сколько из них оказались спамерами):"]
        for e in sorted(book.values(), key=lambda e: -e.get("t", 0))[:15]:
            joined, bad = e.get("joined", 0), e.get("bad", 0)
            share = f" ({round(100 * bad / joined)}%)" if joined else ""
            lines.append(f"• «{esc(e['name'], 24)}»: вошло {joined}, спамеров {bad}{share}" + (" — отозвана" if e.get("revoked") else ""))
        await self.out(m, "\n".join(lines), ttl=60)

    async def cmd_revoke(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        book = self._invites(m.chat.id) or {}
        e = book.get(" ".join(args.split()).lower())
        if e is None or e.get("revoked"):
            return await self.out(m, "Такой действующей метки нет. Список: /links.", ttl=20)
        if await self.call("revoke_chat_invite_link", m.chat.id, e["url"]) is None:
            return await self.out(m, "Не удалось отозвать ссылку: проверьте, что у бота есть право «Приглашать пользователей».", ttl=25)
        e["revoked"] = True
        self.store.dirty = True
        await self.out(m, f"Ссылка «{esc(e['name'], 24)}» отозвана.", ttl=20)

    @staticmethod
    def lock_keys(args: str):
        out: list = []
        for tok in args.lower().replace(",", " ").split():
            key = LOCK_ALIASES.get(tok, tok)
            if key in LOCK_GROUPS:
                out += [x for x in LOCK_GROUPS[key] if x not in out]
            elif key in LOCK_LABELS:
                if key not in out:
                    out.append(key)
            else:
                return None
        return out

    def locks_text(self, cfg) -> str:
        now = ", ".join(LOCK_LABELS[k] for k in cfg.locks if k in LOCK_LABELS) or "ничего"
        return (f"<b>🔒 Замки по типам контента</b>\nСейчас закрыто: {now}.\n"
                "/lock <i>тип</i> — закрыть; /unlock <i>тип</i> — открыть; /unlock all — открыть всё.\n"
                f"Типы: <code>{', '.join(LOCK_LABELS)}</code>; <code>media</code> — все медиа сразу.\n"
                "<i>Владельцев и доверенных замки не касаются.</i>")

    async def cmd_lock(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        keys = self.lock_keys(args)
        if not keys:
            return await self.out(m, self.locks_text(cfg), ttl=60)
        for k in keys:
            if k not in cfg.locks:
                cfg.locks.append(k)
        self.store.dirty = True
        await self.out(m, "🔒 Закрыто: " + ", ".join(LOCK_LABELS[k] for k in keys) + ".", ttl=30)

    async def cmd_unlock(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        if args.strip().lower() in ("all", "все", "всё"):
            cfg.locks = []
            self.store.dirty = True
            return await self.out(m, "🔓 Все замки сняты.", ttl=20)
        keys = self.lock_keys(args)
        if not keys:
            return await self.out(m, self.locks_text(cfg), ttl=60)
        cfg.locks = [k for k in cfg.locks if k not in keys]
        self.store.dirty = True
        await self.out(m, "🔓 Открыто: " + ", ".join(LOCK_LABELS[k] for k in keys) + ".", ttl=30)

    async def cmd_locks(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        await self.out(m, self.locks_text(self.store.chat(m.chat.id).cfg), ttl=60)

    async def cmd_night(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        toks = args.replace("—", "-").replace("–", "-").split()
        how = {"media": "без медиа", "all": "писать могут только владельцы"}
        if not toks:
            if cfg.night:
                return await self.out(m, f"🌙 Ночной режим: {cfg.night} ({how.get(cfg.night_mode, cfg.night_mode)}). "
                                         "Изменить: /night 23:00 07:00 [media|all]; выключить: /night off.", ttl=40)
            return await self.out(m, "/night <i>23:00 07:00</i> [media|all] — ночью media: убирать медиа (по умолчанию), "
                                     "all: писать могут только владельцы. Время — по GUARD_TZ. Выключить: /night off.", ttl=40)
        if toks[0].lower() in ("off", "выкл", "0"):
            cfg.night = ""
            self.store.dirty = True
            self._night_state.pop(m.chat.id, None)
            return await self.out(m, "🌙 Ночной режим выключен.", ttl=20)
        mode, rest = cfg.night_mode, []
        for t in toks:
            if t.lower() in ("media", "медиа"):
                mode = "media"
            elif t.lower() in ("all", "все", "всё"):
                mode = "all"
            else:
                rest.append(t)
        if rest:
            spec = "-".join(rest) if len(rest) == 2 else rest[0] if len(rest) == 1 else ""
            win = parse_night(spec)
            if win is None:
                return await self.out(m, "Не понял время. Пример: /night 23:00 07:00", ttl=20)
            cfg.night = f"{fmt_clock(win[0])}-{fmt_clock(win[1])}"
        elif not cfg.night:
            return await self.out(m, "Укажите время: /night 23:00 07:00", ttl=20)
        cfg.night_mode = mode
        self.store.dirty = True
        self._night_state.pop(m.chat.id, None)
        await self.out(m, f"🌙 Ночной режим {cfg.night}: {how[mode]}.", ttl=30)

    async def cmd_filter(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        trig, rest = split_filter_args(args)
        trig = trig.strip().lower()[:FILTER_TRIGGER_MAX]
        reply = self._text_arg(m, rest)
        if len(trig) < 2 or not reply:
            return await self.out(m, "/filter <i>слово ответ</i> — на это слово бот будет отвечать. Несколько слов — в кавычках: "
                                     "/filter «как купить» текст. Ответ можно взять из сообщения, на которое вы отвечаете. "
                                     "Убрать: /stop <i>слово</i>; список: /filters.", ttl=40)
        same = [k for k in cfg.filters if fold(k) == fold(trig)]
        if not same and len(cfg.filters) >= FILTERS_MAX:
            return await self.out(m, f"Слишком много автоответов (максимум {FILTERS_MAX}). Уберите ненужные: /stop.", ttl=20)
        for k in same:
            cfg.filters.pop(k, None)
        cfg.filters[trig] = reply[:FILTER_REPLY_MAX]
        self.store.dirty = True
        await self.out(m, f"Автоответ на «{esc(trig, 40)}» записан.", ttl=20)

    async def cmd_stop(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        trig, _ = split_filter_args(args)
        same = [k for k in cfg.filters if fold(k) == fold(trig)]
        if not trig.strip() or not same:
            return await self.out(m, "Такого автоответа нет. Список: /filters.", ttl=20)
        for k in same:
            cfg.filters.pop(k, None)
        self.store.dirty = True
        await self.out(m, f"Автоответ «{esc(trig, 40)}» убран.", ttl=20)

    async def cmd_filters(self, m, args):
        if not self.in_group(m) or not self._cool(m.chat.id, "filters", 20):
            return
        cfg = self.store.chat(m.chat.id, m.chat.title or "").cfg
        if not cfg.filters:
            return await self.out(m, "Автоответов нет. Добавить: /filter <i>слово ответ</i>.", ttl=20)
        await self.out(m, "<b>Автоответы</b>\n" + "\n".join(f"• {esc(t, 40)}" for t in sorted(cfg.filters)), ttl=90)

    async def plus_filters(self, m, state, text: str) -> None:
        flt = state.cfg.filters
        if not flt or text.startswith("/"):
            return
        f = fold(text)
        for trig, reply in flt.items():
            if _filter_rx(trig).search(f):
                if self._cool(state.chat_id, "flt:" + trig, 30):
                    await self.announce(state.chat_id, esc(reply, FILTER_REPLY_MAX), ttl=FILTER_TTL, reply_to=m.message_id)
                return

    async def cmd_repeat(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        tok, _, rest = args.strip().partition(" ")
        mins = parse_minutes(tok) if tok else None
        text = self._text_arg(m, rest.strip())
        if not mins or not text:
            return await self.out(m, "/repeat <i>6ч текст</i> — публиковать текст регулярно (от 30 минут до 30 дней; «2ч», «1д»). "
                                     "Предыдущее объявление при этом стирается. Список: /repeats; убрать: /unrepeat <i>номер</i>.", ttl=45)
        if mins < REPEAT_MIN_MIN:
            return await self.out(m, f"Слишком часто: минимум раз в {REPEAT_MIN_MIN} минут.", ttl=20)
        reps = self.store.meta.setdefault("repeats", [])
        if sum(1 for r in reps if r["c"] == m.chat.id) >= REPEAT_PER_CHAT:
            return await self.out(m, f"Слишком много объявлений (максимум {REPEAT_PER_CHAT} на чат). Уберите лишние: /unrepeat.", ttl=20)
        seq = self.store.meta["repeat_seq"] = int(self.store.meta.get("repeat_seq", 0)) + 1
        reps.append({"id": seq, "c": m.chat.id, "ev": min(mins, REPEAT_MAX_MIN), "at": self.now(), "t": text[:REPEAT_TEXT_MAX],
                     "th": self.thread_of(m) or 0, "mid": 0, "f": 0})
        self.store.dirty = True
        await self.out(m, f"📣 Объявление №{seq} будет выходить каждые {human_dur(min(mins, REPEAT_MAX_MIN) * 60)}; первое — сейчас.", ttl=30)

    async def cmd_repeats(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        mine = [r for r in self.store.meta.get("repeats", []) if r["c"] == m.chat.id]
        if not mine:
            return await self.out(m, "Регулярных объявлений нет. Добавить: /repeat <i>6ч текст</i>.", ttl=20)
        now = self.now()
        lines = [f"№{r['id']} · каждые {human_dur(r['ev'] * 60)}, следующее через {human_dur(max(0, r['at'] - now))}: {esc(r['t'], 60)}"
                 for r in mine]
        await self.out(m, "<b>Регулярные объявления</b>\n" + "\n".join(lines), ttl=90)

    async def cmd_unrepeat(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        tok = (args.split() or [""])[0].lstrip("№#")
        reps = self.store.meta.get("repeats", [])
        hit = [r for r in reps if r["c"] == m.chat.id and (str(r["id"]) == tok or tok in ("all", "все"))]
        if not hit:
            return await self.out(m, "Укажите номер из /repeats: /unrepeat <i>номер</i> (или /unrepeat all).", ttl=20)
        for r in hit:
            reps.remove(r)
            if r.get("mid"):
                await self.call("delete_message", r["c"], r["mid"])
        self.store.dirty = True
        await self.out(m, f"Убрано объявлений: {len(hit)}.", ttl=20)

    async def plus_tick(self, now: float) -> None:
        try:
            await self._plus_tick(now)
        except asyncio.CancelledError:
            raise
        except Exception:
            log_plus.exception("фоновые задачи расширений: сбой")

    async def _plus_tick(self, now: float) -> None:
        reps = self.store.meta.get("repeats")
        for r in list(reps or []):
            if r["at"] > now or not self.chat_ok(r["c"]):
                continue
            r["at"] = now + r["ev"] * 60
            self.store.dirty = True
            if r.get("mid"):
                await self.call("delete_message", r["c"], r["mid"])
            extra = {"message_thread_id": r["th"]} if r.get("th") else {}
            sent = await self.call("send_message", r["c"], esc(r["t"], REPEAT_TEXT_MAX), disable_notification=True, **extra)
            if sent is None:
                r["f"] = r.get("f", 0) + 1
                if r["f"] >= 5:
                    reps.remove(r)
            else:
                r["mid"], r["f"] = sent.message_id, 0
        for cid, st in list(self.store.chats.items()):
            cfg = st.cfg
            if not cfg.night or not st.active or not cfg.enabled or not self.chat_ok(cid):
                self._night_state.pop(cid, None)
                continue
            night = in_night(cfg.night, now, self.tz_h)
            prev = self._night_state.get(cid)
            self._night_state[cid] = night
            if prev is None or prev == night or cfg.quiet:
                continue
            if night:
                end = fmt_clock((parse_night(cfg.night) or (0, 0))[1])
                tail = "писать могут только владельцы." if cfg.night_mode == "all" else "медиа не принимаются."
                await self.announce(cid, f"🌙 Ночной режим до {end}: {tail}", ttl=900)
            else:
                await self.announce(cid, "☀️ Ночной режим закончился.", ttl=900)

    def plus_violation(self, m, cfg, as_channel: bool, now: float, rec=None):
        kinds = content_kinds(m, as_channel)
        if cfg.locks:
            hit = [k for k in cfg.locks if k in kinds]
            if hit:
                return "lock", hit[0]
        if cfg.night and in_night(cfg.night, now, self.tz_h):
            if cfg.night_mode == "all":
                if not (getattr(m, "text", None) or "").lstrip().startswith("/"):
                    return "night", ""
            elif kinds & NIGHT_MEDIA:
                return "night", ""
        if cfg.strict_until > now or cfg.fort_on:
            tier = self.eng.tier(rec, now) if rec is not None else "new"
            hit = kinds & STRICT_KINDS.get(tier, frozenset())
            if hit:
                return "strict", sorted(hit)[0]
        if cfg.newbie_min and rec is not None and rec.joined and not rec.vouched and now - rec.joined < cfg.newbie_min * 60:
            if kinds & NEWBIE_KINDS:
                return "newbie", ""
        return None

    async def plus_gate(self, m, chat, state, uid: int, name: str, as_channel: bool, rights: dict) -> bool:
        cfg = state.cfg
        rec = state.users.get(uid) if (not as_channel and uid > 0) else None
        if not as_channel and uid > 0:
            if await self.plus_screen(chat, uid, name, m.message_id, deep=rec is None or rec.clean < 3):
                return True
            if cfg.impostor and getattr(m, "from_user", None) is not None and not (rec and rec.vouched) \
                    and (rec is None or rec.clean < 5) and uid not in await self.admins(chat.id):
                why = await self.plus_impostor(chat.id, m.from_user, has_contact_info(m))
                if why:
                    await self.plus_impostor_act(m, chat, uid, name, why, rights)
                    return True
        hit = self.plus_violation(m, cfg, as_channel, self.now(), rec)
        if not hit:
            return False
        kind, key = hit
        if rights["delete"]:
            self.deleter.add(chat.id, [m.message_id])
        else:
            await self.notice(chat.id, "need_rights", ttl=60, cooldown=3600)
        self.store.bump(state, {"lock": "del_lock", "night": "del_night", "newbie": "del_newbie", "strict": "del_strict"}[kind])
        if cfg.fort_on and kind != "strict":
            self.eng.fort_count(chat.id, "del")
        if kind == "strict":
            await self.strict_penalty(chat, state, uid, name, as_channel, key, rights)
        if cfg.quiet or not rights["delete"]:
            return True
        if kind == "lock":
            if self._cool(chat.id, f"lockmsg:{uid}", 60):
                await self.announce(chat.id, f"🔒 {mention(uid, name)}: {LOCK_LABELS.get(key, key)} в этом чате закрыты.", ttl=10)
        elif kind == "newbie":
            if self._cool(chat.id, f"newbiemsg:{uid}", 120):
                await self.announce(chat.id, f"🆕 {mention(uid, name)}: первые {human_dur(cfg.newbie_min * 60)} после входа "
                                             "нельзя присылать медиа, пересылки и приглашения.", ttl=12)
        elif kind == "strict":
            pass
        elif self._cool(chat.id, "nightmsg", 120):
            end = fmt_clock((parse_night(cfg.night) or (0, 0))[1])
            tail = "писать могут только владельцы." if cfg.night_mode == "all" else "медиа не принимаются."
            await self.announce(chat.id, f"🌙 Ночной режим до {end}: {tail}", ttl=15)
        return True

    async def on_join_request(self, ev) -> None:
        chat, user = ev.chat, getattr(ev, "from_user", None)
        if user is None or getattr(chat, "type", "") not in GROUP_TYPES or not self.chat_ok(chat.id) or user.is_bot:
            return
        state = self.store.chat(chat.id, chat.title or "")
        cfg = state.cfg
        uid = user.id
        if not cfg.enabled or uid in self.owners or self.is_trusted(uid):
            return
        if uid in self.banned_env:
            why = "id из GUARD_BANNED_IDS"
        elif str(uid) in self.gbans():
            why = "общий чёрный список"
        elif cfg.cas and await self.plus_cas(uid):
            why = "база спамеров CAS"
        else:
            return
        if await self.call("decline_chat_join_request", chat.id, uid) is not None:
            self.store.bump(state, "join_decline")
            self.journal("join_decline", chat.id, chat.title or "", uid, user_name(user), why)
            await self.plus_log(chat.id, f"🛡 <b>{esc(chat.title, 60)}</b>\nЗаявка {mention(uid, user_name(user))} "
                                         f"(<code>{uid}</code>) отклонена: {esc(why, 100)}")


ROLE_RE = re.compile(r"support|suport|helpdesk|help desk|administrat|admin|moderat|official|security|safeguard|telegram|"
                     r"техподдерж|поддержк|админ|модератор|официальн|безопасност|гарант|служб")
CONTACT_RE = re.compile(r"https?://|www\.|t\.me/|@[a-z0-9_]{4,}|\+?\d[\d\s\-()]{9,}", re.I)
CONTACT_ENTS = {"url", "text_link", "mention", "text_mention", "phone_number", "email"}
CYR2LAT = {v: k for k, v in LAT2CYR.items() if k.isalpha()}
NEWBIE_KINDS = NIGHT_MEDIA | {"forward", "invitelink", "contact", "location", "poll", "game", "inline"}
NEWBIE_MAX_MIN = 7 * 1440
IMPOSTOR_MUTE_S = 24 * 3600
ADMIN_REFS_TTL = 600
COPYSET_SKIP = ("rules", "welcome", "notes", "logchat", "fort_on", "fort_until", "fort_started", "fort_origin",
                "fort_before", "fort_applied", "fort_board", "fort_why")


def skeleton(s: str) -> str:
    out = []
    for ch in fold(s or ""):
        ch = LAT2CYR.get(ch, ch)
        if ch.isalnum():
            out.append(ch)
    return collapse("".join(out))


def similar_names(a: str, b: str) -> bool:
    if not a or not b:
        return False
    if a == b:
        return len(a) >= 4
    return min(len(a), len(b)) >= 6 and difflib.SequenceMatcher(None, a, b).ratio() >= 0.9


def role_name(name: str) -> bool:
    f = fold(name or "")
    views = {f, "".join(LAT2CYR.get(c, c) for c in f), "".join(CYR2LAT.get(c, c) for c in f),
             "".join(LAT_LEET.get(c, c) for c in f)}
    return any(ROLE_RE.search(v) for v in views)


def has_contact_info(m) -> bool:
    text = f"{getattr(m, 'text', None) or ''} {getattr(m, 'caption', None) or ''}"
    if CONTACT_RE.search(text):
        return True
    for e in list(getattr(m, "entities", None) or []) + list(getattr(m, "caption_entities", None) or []):
        t = getattr(e, "type", "")
        if str(getattr(t, "value", t)) in CONTACT_ENTS:
            return True
    return False


class Plus2:

    def init_plus2(self) -> None:
        self._admin_refs: dict = {}

    async def plus_admin_refs(self, chat_id: int) -> list:
        now = self.now()
        hit = self._admin_refs.get(chat_id)
        if hit and now - hit[0] < ADMIN_REFS_TTL:
            return hit[1]
        res = await self._once(("adm", chat_id), lambda: self.call("get_chat_administrators", chat_id))
        if res is None:
            return hit[1] if hit else []
        refs = []
        for mem in res:
            u = getattr(mem, "user", None)
            if u is None or getattr(u, "is_bot", False):
                continue
            un = getattr(u, "username", None) or ""
            refs.append((u.id, skeleton(user_name(u)), skeleton(un), un.lower()))
        self._admin_refs[chat_id] = (now, refs)
        return refs

    async def plus_impostor(self, chat_id: int, user, contact: bool | None) -> str:
        if user is None or getattr(user, "is_bot", False):
            return ""
        refs = await self.plus_admin_refs(chat_id)
        if any(r[0] == user.id for r in refs):
            return ""
        name, un = user_name(user), (getattr(user, "username", None) or "")
        ks, ku = skeleton(name), skeleton(un)
        for _aid, an, au, aun in refs:
            if similar_names(ks, an):
                return "имя совпадает с именем администратора"
            if un and un.lower() != aun and similar_names(ku, au):
                return "ник похож на ник администратора"
        if contact and (role_name(name) or role_name(un)):
            return "имя «поддержки или админа» и контакты в сообщении"
        return ""

    async def plus_impostor_act(self, m, chat, uid: int, name: str, why: str, rights: dict) -> None:
        state = self.store.chat(chat.id, chat.title or "")
        if rights["delete"]:
            self.deleter.add(chat.id, [m.message_id])
        if rights["restrict"]:
            await self.restrict(chat.id, uid, IMPOSTOR_MUTE_S)
        self.store.bump(state, "impostor")
        await self.fort_feed(chat.id, uid, "impostor")
        self.journal("impostor", chat.id, chat.title or "", uid, name, why)
        if not state.cfg.quiet and self._cool(chat.id, f"impostor:{uid}", 300):
            await self.announce(chat.id, f"🛡 {mention(uid, name)}: {esc(why, 80)}. Запись ограничена на сутки.", ttl=60)
        text = (f"🚨 <b>{esc(chat.title, 60)}</b>\nВозможная подмена: {mention(uid, name)} (<code>{uid}</code>)\n"
                f"Причина: {esc(why, 120)}\nЗапись ограничена на сутки. Если это ошибка — /vouch ответом на сообщение участника.")
        await self.alert(chat.id, text)
        await self.plus_log(chat.id, text)

    async def plus_join_checks(self, chat, user) -> bool:
        try:
            state = self.store.chat(chat.id, chat.title or "")
            cfg = state.cfg
            if not cfg.impostor or not cfg.enabled or user.id in self.owners or self.is_trusted(user.id):
                return False
            name = user_name(user)
            if len(name) >= 5:
                res = self.eng.explain(name[:200], chat.id, [])
                act = res["tiers"].get("new", (0.0, "none"))[1]
                if act in ("delete", "ban") and (await self.rights(chat.id))["restrict"]:
                    if await self.call("ban_chat_member", chat.id, user.id, revoke_messages=True) is not None:
                        self.store.bump(state, "name_ban")
                        await self.fort_feed(chat.id, user.id, "namespam")
                        self.journal("name_ban", chat.id, chat.title or "", user.id, name, "имя — реклама или спам")
                        if not cfg.quiet:
                            await self.announce(chat.id, f"🛡 {mention(user.id, name)} заблокирован: имя — реклама.", ttl=60)
                        await self.plus_log(chat.id, f"🛡 <b>{esc(chat.title, 60)}</b>\n{mention(user.id, name)} "
                                                     f"(<code>{user.id}</code>) — бан: имя похоже на рекламу")
                        return True
            why = await self.plus_impostor(chat.id, user, None)
            if why and self._cool(chat.id, f"imp_join:{user.id}", 600):
                text = (f"👀 <b>{esc(chat.title, 60)}</b>\nНовичок {mention(user.id, name)} (<code>{user.id}</code>): "
                        f"{esc(why, 100)}. Его сообщения буду проверять строго.")
                await self.alert(chat.id, text)
                await self.plus_log(chat.id, text)
        except asyncio.CancelledError:
            raise
        except Exception:
            log_plus.exception("проверка имени новичка: сбой")
        return False

    async def cmd_newbie(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cfg = self.store.chat(m.chat.id).cfg
        a = args.strip().lower()
        if a in ("off", "выкл", "0"):
            cfg.newbie_min = 0
            self.store.dirty = True
            return await self.out(m, "Режим новичка выключен.", ttl=20)
        mins = parse_minutes(a) if a else None
        if not mins:
            cur = f"сейчас: {human_dur(cfg.newbie_min * 60)}" if cfg.newbie_min else "сейчас выключен"
            return await self.out(m, "/newbie <i>60м</i> — первые минуты после входа нельзя слать медиа, пересылки, приглашения в чаты, "
                                     f"контакты и опросы (\u00ab2ч\u00bb, \u00ab1д\u00bb; {cur}). Выключить: /newbie off. "
                                     "Поручительство (/vouch) снимает ограничение.", ttl=45)
        cfg.newbie_min = min(mins, NEWBIE_MAX_MIN)
        self.store.dirty = True
        await self.out(m, f"🆕 Режим новичка: {human_dur(cfg.newbie_min * 60)} после входа без медиа, пересылок и приглашений.", ttl=30)

    def digest_text(self, st, now: float) -> str:
        day = self.store.day(now)
        data = st.stats.get(day, {})
        lines = [f"📊 <b>Итоги дня: {esc(st.title, 60)}</b>"]
        rows = sorted(((k, v) for k, v in data.items() if v), key=lambda kv: -kv[1])
        if rows:
            lines += [f"• {STAT_LABELS.get(k, k)}: {v}" for k, v in rows[:12]]
        else:
            lines.append("Нарушений не было.")
        lines.append(f"Участников в памяти: {len(st.users)}")
        try:
            lines += self.eng.learn_digest_lines(st.chat_id, now)
        except Exception:
            log_learn.exception("самообучение: строки для итогов дня не получились")
        return "\n".join(lines)

    async def send_digest(self, st, now: float) -> int:
        text = self.digest_text(st, now)
        target = st.cfg.logchat or self.log_chat_env
        if target:
            return 1 if await self.call("send_message", target, text, disable_notification=True) is not None else 0
        return await self.alert(st.chat_id, text)

    async def cmd_digest(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        st = self.store.chat(m.chat.id)
        a = args.strip().lower()
        if a in ("off", "выкл"):
            st.cfg.digest_hour = -1
            self.store.dirty = True
            return await self.out(m, "Дайджест выключен.", ttl=20)
        if a in ("now", "сейчас"):
            n = await self.send_digest(st, self.now())
            return await self.out(m, "Дайджест отправлен." if n else "Некому отправить: подключите /setlog или нажмите /start у бота в личке.", ttl=30)
        if a.isdigit() and 0 <= int(a) <= 23:
            st.cfg.digest_hour = int(a)
            self.store.dirty = True
            return await self.out(m, f"📊 Дайджест каждый день в {int(a):02d}:00 (GUARD_TZ). Получатель: журнал (/setlog) или владельцы в личке.", ttl=40)
        cur = f"{st.cfg.digest_hour:02d}:00" if st.cfg.digest_hour >= 0 else "выключен"
        await self.out(m, f"/digest <i>21</i> — слать итоги дня каждый день в этот час; /digest now — сейчас; /digest off. Сейчас: {cur}.", ttl=40)

    async def plus2_tick(self, now: float) -> None:
        try:
            local = time.gmtime(now + self.tz_h * 3600)
            today = time.strftime("%Y-%m-%d", local)
            sent = self.store.meta.setdefault("digest_sent", {})
            for cid, st in list(self.store.chats.items()):
                if st.cfg.digest_hour < 0 or st.cfg.digest_hour != local.tm_hour or not st.active or not self.chat_ok(cid):
                    continue
                if sent.get(str(cid)) == today:
                    continue
                sent[str(cid)] = today
                self.store.dirty = True
                await self.send_digest(st, now)
        except asyncio.CancelledError:
            raise
        except Exception:
            log_plus.exception("дайджест: сбой")

    async def cmd_copyset(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        tok = (args.split() or [""])[0]
        try:
            src_id = int(tok)
        except ValueError:
            return await self.out(m, "/copyset <i>id другого чата бота</i> — перенести сюда его настройки (замки, ночной режим, автоответы, "
                                     "списки доменов и т. д.). Правила, приветствие, заметки и журнал не копируются.", ttl=40)
        src = self.store.chat(src_id, create=False)
        if src is None or src_id == m.chat.id:
            return await self.out(m, "Такого чата в памяти бота нет (или это этот же чат).", ttl=20)
        cfg = self.store.chat(m.chat.id).cfg
        data = asdict(src.cfg)
        if src.cfg.fort_on:
            data.update(self.eng.fort_revert_values(src.cfg)[0])
        for k in COPYSET_SKIP:
            data.pop(k, None)
        new = _load(ChatCfg, data)
        for f in fields(ChatCfg):
            if f.name not in COPYSET_SKIP:
                setattr(cfg, f.name, getattr(new, f.name))
        self.store.dirty = True
        await self.out(m, f"Настройки перенесены из «{esc(src.title, 40)}».", ttl=30)


log_strict = logging.getLogger("guard.strict")

STRICT_KINDS = {
    "new": NIGHT_MEDIA | {"forward", "invitelink", "contact", "location", "poll", "game", "inline", "story", "channel", "dice"},
    "member": frozenset({"forward", "invitelink", "contact", "story", "channel", "poll", "game"}),
    "veteran": frozenset({"invitelink", "story"}),
}
REACT_LIMIT = {"new": (10, 15), "member": (14, 15), "veteran": (25, 15)}
REACT_MUTE = {"new": 1800, "member": 600, "veteran": 300}
STRICT_UNITS = ("м", "мин", "m", "min", "ч", "h", "д", "d")


class Strict:

    def init_strict(self) -> None:
        self._react: dict = {}
        self._react_prune: float = 0.0
        self.react_on: bool = True

    def strict_text(self, cid: int, now: float) -> str:
        cfg = self.store.chat(cid).cfg
        left = self.eng.strict_left(cid, now)
        auto = "вкл" if (cfg.strict_auto and self.eng.strict_auto_on) else "выкл"
        if left <= 0:
            return (f"🛡 Строгий режим выключен.\n/strict — включить на {human_dur(self.eng.strict_default_min * 60)}; "
                    "/strict <i>3ч</i> — на другой срок («90м», «2ч», «1д»); /strict off — выключить.\n"
                    f"Автовключение при волне спама: {auto} (/strict auto on|off).")
        c = self.eng.strict_counts.get(cid) or {}
        return (f"🛡 Строгий режим: ещё {human_dur(left)}.\n"
                f"За это время: удалено — {c.get('del', 0)}, заблокировано — {c.get('ban', 0)}, ограничено — {c.get('mute', 0)}.\n"
                f"Автовключение при волне спама: {auto}. Выключить: /strict off.")

    @staticmethod
    def strict_tail(counts: dict) -> str:
        if not counts or not any(counts.values()):
            return ""
        return (f" За это время: удалено — {counts.get('del', 0)}, заблокировано — {counts.get('ban', 0)}, "
                f"ограничено — {counts.get('mute', 0)}.")

    async def strict_announce(self, chat, auto: bool, why: str = "", by: int = 0) -> None:
        cid = chat.id
        state = self.store.chat(cid)
        dur = human_dur(self.eng.strict_left(cid, self.now()))
        self.store.bump(state, "strict_on")
        self.journal("strict_on", cid, chat.title or "", by, "", ("авто: " + why) if auto else "вручную")
        log_strict.info("chat=%s: строгий режим на %s (%s)", cid, dur, ("авто: " + why) if auto else "вручную")
        if not state.cfg.quiet:
            await self.announce(cid, f"🛡 Строгий режим на {dur}: ссылки, медиа и пересылки от новичков запрещены, пороги "
                                     "спама снижены, нарушители блокируются сразу. Выключить: /strict off.", ttl=900)
        if auto:
            await self.alert(cid, f"🚨 <b>{esc(chat.title, 60)}</b>\nВолна спама: строгий режим включён на {dur}.\n"
                                  f"Причина: {esc(why, 150)}\nВыключить: /strict off в чате.")
        await self.plus_log(cid, f"🛡 <b>{esc(chat.title, 60)}</b>\nСтрогий режим на {dur} "
                                 f"({'включился сам' if auto else 'включён вручную'}).")

    async def cmd_strict(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cid, now = m.chat.id, self.now()
        cfg = self.store.chat(cid).cfg
        toks = [t.lower() for t in args.replace(",", " ").split()]
        word = toks[0] if toks else ""
        if len(toks) > 1 and toks[1] in STRICT_UNITS and word.isdigit():
            word += toks[1]
        if word in ("off", "выкл", "0", "stop", "стоп", "конец"):
            if not self.eng.strict_active(cid, now):
                return await self.out(m, "Строгий режим и так выключен.", ttl=15)
            counts = dict(self.eng.strict_counts.get(cid) or {})
            self.eng.strict_set(cid, 0, now)
            self.eng.strict_counts.pop(cid, None)
            self.journal("strict_off", cid, m.chat.title or "", m.from_user.id, "", "вручную")
            return await self.out(m, "✅ Строгий режим выключен." + self.strict_tail(counts), ttl=60)
        if word == "auto":
            val = toks[1] if len(toks) > 1 else ""
            if val in ("on", "вкл", "1"):
                cfg.strict_auto = True
            elif val in ("off", "выкл", "0"):
                cfg.strict_auto = False
            else:
                return await self.out(m, "/strict auto on — включать строгий режим самому при волне спама; /strict auto off — только вручную.", ttl=30)
            self.store.dirty = True
            tail = "" if self.eng.strict_auto_on else " (но в настройках бота GUARD_STRICT_AUTO=0, поэтому сам он не включится)"
            return await self.out(m, f"Автовключение строгого режима: {'вкл' if cfg.strict_auto else 'выкл'}.{tail}", ttl=30)
        if word in ("status", "статус", "?"):
            return await self.out(m, self.strict_text(cid, now), ttl=60)
        mins = None
        if word:
            mins = parse_minutes(word)
            if mins is None:
                return await self.out(m, "Не понял срок. Примеры: /strict 2ч, /strict 90м, /strict 1д, /strict off", ttl=25)
        elif self.eng.strict_active(cid, now):
            return await self.out(m, self.strict_text(cid, now), ttl=60)
        mins = max(STRICT_MIN_MIN, min(mins or self.eng.strict_default_min, STRICT_MAX_MIN))
        self.eng.strict_set(cid, mins * 60.0, now)
        await self.strict_announce(m.chat, auto=False, by=m.from_user.id)

    async def strict_tick(self, now: float) -> None:
        try:
            for cid, started, counts in self.eng.pop_strict_ended(now):
                st = self.store.chats.get(cid)
                log_strict.info("chat=%s: строгий режим закончился", cid)
                self.journal("strict_off", cid, st.title if st else "", 0, "", "срок вышел")
                if st is None or st.cfg.quiet or not st.active or not self.chat_ok(cid):
                    continue
                await self.announce(cid, "✅ Строгий режим закончился." + self.strict_tail(counts), ttl=600)
            if now - self._react_prune > 60:
                self._react_prune = now
                for k in [k for k, dq in self._react.items() if not dq or now - dq[-1] > 120]:
                    self._react.pop(k, None)
        except asyncio.CancelledError:
            raise
        except Exception:
            log_strict.exception("строгий режим: сбой фоновой задачи")

    async def strict_penalty(self, chat, state, uid: int, name: str, as_channel: bool, key: str, rights: dict) -> None:
        self.eng.strict_count(chat.id, "del")
        if as_channel or uid <= 0:
            return
        now = self.now()
        rec = self.store.user(state, uid, now)
        tier = self.eng.tier(rec, now)
        level, mute = self.eng.add_strike(chat.id, uid, {"new": 1.5, "member": 1.0}.get(tier, 0.5), "strict", now)
        quiet = state.cfg.quiet or not rights["delete"]
        who = mention(uid, name)
        if mute and rights["restrict"]:
            await self.restrict(chat.id, uid, mute)
            self.eng.strict_count(chat.id, "mute")
            if not quiet:
                await self.notice(chat.id, "mute", ttl=NOTICE_TTL.get("mute", 90), name=who, dur=human_dur(mute))
        elif not quiet and self._cool(chat.id, f"strictmsg:{uid}", 60):
            await self.announce(chat.id, f"🛡 {who}: в строгом режиме {LOCK_LABELS.get(key, key)} запрещены.", ttl=10)

    async def on_reaction(self, ev) -> None:
        try:
            await self._on_reaction(ev)
        except asyncio.CancelledError:
            raise
        except Exception:
            log_strict.exception("реакции: сбой")

    async def _on_reaction(self, ev) -> None:
        if not self.react_on:
            return
        chat, user = getattr(ev, "chat", None), getattr(ev, "user", None)
        if chat is None or user is None or getattr(chat, "type", "") not in GROUP_TYPES or not self.chat_ok(chat.id):
            return
        uid = user.id
        if getattr(user, "is_bot", False) or uid in self.owners or self.is_trusted(uid):
            return
        added = len(getattr(ev, "new_reaction", None) or []) - len(getattr(ev, "old_reaction", None) or [])
        if added <= 0:
            return
        state = self.store.chat(chat.id, create=False)
        if state is None or not state.cfg.enabled or not state.active:
            return
        now = self.now()
        rec = state.users.get(uid)
        if rec is not None and rec.vouched:
            return
        tier = self.eng.tier(rec, now) if rec is not None else "new"
        lim, win = REACT_LIMIT[tier]
        strict = self.eng.strict_active(chat.id, now)
        if strict:
            lim = max(4, lim // 2)
        dq = self._react.setdefault((chat.id, uid), deque(maxlen=80))
        dq.append(now)
        if sum(1 for t in dq if now - t <= win) < lim:
            return
        dq.clear()
        rights = await self.rights(chat.id)
        if not rights["restrict"] or uid in await self.admins(chat.id):
            return
        rec = self.store.user(state, uid, now)
        _, mute = self.eng.add_strike(chat.id, uid, 1.5 if tier == "new" else 1.0, "реакции", now)
        mute = max(mute, REACT_MUTE[tier] * (3 if strict else 1))
        ban = strict and tier == "new"
        if ban:
            await self.call("ban_chat_member", chat.id, uid)
            rec.banned = True
        else:
            await self.restrict(chat.id, uid, mute)
        self.store.bump(state, "react_spam", now=now)
        await self.fort_feed(chat.id, uid, "react")
        if strict:
            self.eng.strict_count(chat.id, "ban" if ban else "mute")
        name = user_name(user)
        what = "заблокирован" if ban else f"запись ограничена на {human_dur(mute)}"
        self.journal("react_spam", chat.id, chat.title or "", uid, name, "бан" if ban else f"мут {human_dur(mute)}")
        if not state.cfg.quiet:
            await self.announce(chat.id, f"🛡 {mention(uid, name)}: {what}. Причина: поток реакций.", ttl=60)
        await self.plus_log(chat.id, f"🛡 <b>{esc(chat.title, 60)}</b>\n{mention(uid, name)} (<code>{uid}</code>): {what}\n"
                                     "Причина: поток реакций")


TRACE_MODES = {"on": "вкл — улики входят в оценку", "log": "наблюдение — только журнал «что бы сделал»", "off": "выкл"}
_SPARK = "▁▂▃▄▅▆▇█"


class Tracker:

    @staticmethod
    def trace_spark(prof: str) -> str:
        if len(prof) != 24 or not all(x in _B36 for x in prof):
            return ""
        c = [int(x, 36) for x in prof]
        top = max(c) or 1
        return "".join(_SPARK[min(7, int(x * 7 / top + 0.5))] if x else "·" for x in c)

    def trace_summary(self, cid: int, now: float) -> str:
        st = self.store.chat(cid)
        cfg, eng = st.cfg, self.eng
        mode = TRACE_MODES.get(cfg.trace, cfg.trace)
        lines = [f"🔎 <b>Следопыт</b>: {mode}."]
        if not eng.trace_on:
            lines.append("Но в настройках бота GUARD_TRACE=0: датчики выключены совсем.")
        if cfg.trace == "on" and now < st.learning_until:
            lines.append(f"Первые сутки после добавления бот только наблюдает (ещё {human_dur(st.learning_until - now)}): улики пишутся в журнал.")
        samples = len(eng.tr_lat.get(cid) or ())
        lines.append(f"Быстрым ответом на вопрос здесь считается быстрее {eng.trace_fast_thr(cid):.0f} с"
                     + (f" (по {samples} ответам постоянных участников)." if samples >= 30 else " (пока мало данных, стандарт)."))
        log = list(eng.tr_log.get(cid) or ())
        if log:
            lines.append("Последние решения:")
            for e in log[-6:]:
                kinds = ", ".join(TRACE_LABEL.get(k, k) for k in e["kinds"])
                lines.append(f"• {human_dur(now - e['ts'])} назад — {esc(e['name'], 24) or e['uid']}: {kinds} "
                             f"({'в оценке' if e['applied'] else 'наблюдение'}, +{e['w']:g})")
        else:
            lines.append("Решений пока нет: улик, которые что-то меняют, не было.")
        lines.append("Досье участника: /trace ответом на его сообщение. Режим: /trace on | log | off.")
        return "\n".join(lines)

    def trace_dossier(self, cid: int, uid: int, label: str, now: float) -> str:
        st, eng = self.store.chat(cid), self.eng
        rec = st.users.get(uid)
        lines = [f"🔎 <b>Досье</b>: {label}"]
        if rec is None:
            return lines[0] + "\nПро этого участника бот ничего не знает."
        tier = {"new": "новичок", "member": "участник", "veteran": "ветеран"}[eng.tier(rec, now)]
        days = max(0.0, (now - (rec.joined or rec.first_seen)) / 86400)
        lines.append(f"{tier}, в чате ≈{days:.0f} дн., чистых сообщений: {rec.clean}, страйков за сутки: "
                     f"{sum(1 for ts, w, _ in rec.strikes if now - ts <= 86400)}.")
        case = eng.tr_case.get((cid, uid)) or {}
        if case:
            lines.append("Улики за сутки:")
            for kind, items in sorted(case.items(), key=lambda kv: -kv[1][-1][0]):
                ts, why = items[-1]
                scoring = "считается" if kind in TRACE_STRONG or kind in TRACE_SOFT else "только в досье"
                lines.append(f"• {TRACE_LABEL.get(kind, kind)} ×{len(items)} — {human_dur(now - ts)} назад: {esc(why, 90)} ({scoring})")
        else:
            lines.append("Улик за сутки нет.")
        spark = self.trace_spark(rec.hours)
        if spark:
            lines.append(f"Часы активности (UTC, 0–23): {spark}")
        edges = [e for e in (eng.tr_edges.get((cid, uid)) or ()) if now - e[0] <= 86400]
        if edges:
            lines.append(f"Общение за сутки: с постоянными — {sum(1 for e in edges if e[2])}, с новичками — {sum(1 for e in edges if not e[2])}.")
        lines.append("Поведенческие улики (ритм, связи) сами ничего не весят: они усиливают подозрение, только если в сообщении есть ссылка, "
                     "контакт или спам-оценка.")
        return "\n".join(lines)

    async def cmd_trace(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cid, now = m.chat.id, self.now()
        cfg = self.store.chat(cid, m.chat.title or "").cfg
        word = (args.split() or [""])[0].lower()
        if word in TRACE_MODES or word in ("вкл", "выкл", "наблюдение"):
            cfg.trace = {"вкл": "on", "выкл": "off", "наблюдение": "log"}.get(word, word)
            self.store.dirty = True
            return await self.out(m, f"🔎 Следопыт: {TRACE_MODES[cfg.trace]}.", ttl=30)
        if word or getattr(m, "reply_to_message", None) is not None:
            t = await self.one_target(m, args, allow_admin=True)
            if t is None:
                return
            return await self.out(m, self.trace_dossier(cid, t[0], esc(t[1], 40), now), ttl=90)
        await self.out(m, self.trace_summary(cid, now), ttl=90)


log_fort = logging.getLogger("guard.fort")

FORT_LABELS = {
    "enabled": "модерация", "captcha": "проверка при входе", "captcha_smart": "адаптивная проверка", "smart_links": "анализ ссылок",
    "scam": "спам", "hate": "оскорбления", "adult": "18+", "profanity": "мат", "flood": "флуд", "raid": "антирейд",
    "impostor": "защита от подмены админов", "cas": "база CAS", "puppet": "кукольный театр", "spam_memory": "память о спаме",
    "jitter": "задержка удаления", "clean_joins": "чистка «вошёл/вышел»", "tribunes": "реплики зрителей", "quiet": "тихий режим",
    "links": "ссылки", "captcha_timeout": "время на проверку", "captcha_ban_min": "бан за провал проверки",
    "newbie_min": "режим новичка", "locks": "замки",
}
FORT_OFF_WORDS = ("off", "выкл", "0", "stop", "стоп", "конец")
FORT_ON_WORDS = ("on", "вкл", "1")


class Fortress:

    def init_fort_ui(self) -> None:
        self._fort_sig: dict[int, str] = {}
        self._fort_board_t: dict[int, float] = {}
        self._fort_fail: dict[int, int] = {}
        self._fort_remind_t: dict[int, float] = {}

    @staticmethod
    def fort_bar(score: float) -> str:
        n = max(0, min(10, int(round(score / 1.2))))
        return "▰" * n + "▱" * (10 - n)

    @staticmethod
    def fort_fmt(key: str, val) -> str:
        if isinstance(val, bool):
            return "вкл" if val else "выкл"
        if key == "links":
            return LINK_LABEL.get(val, str(val))
        if key == "captcha_timeout":
            return f"{val} с"
        if key == "captcha_ban_min":
            return f"{val} мин" if val else "по умолчанию"
        if key == "newbie_min":
            return human_dur(val * 60) if val else "выкл"
        if key == "locks":
            return ", ".join(LOCK_LABELS.get(x, x) for x in val) or "нет"
        return str(val)

    def fort_changes(self, before: dict, applied: dict) -> list:
        return [f"{FORT_LABELS.get(k, k)}: {self.fort_fmt(k, v)} → {self.fort_fmt(k, applied.get(k))}" for k, v in before.items()]

    def fort_text(self, cid: int, now: float) -> str:
        cfg = self.store.chat(cid).cfg
        auto = "вкл" if (cfg.fort_auto and self.eng.fort_auto_on) else "выкл"
        idx, name, icon, score, actors = self.eng.radar_level(cid, now)
        if not cfg.fort_on:
            return (f"🛡 Полная защита выключена. Радар: {icon} {name}.\n"
                    "/fullguard — включить (до /fullguard off); /fullguard <i>2ч</i> — на срок («90м», «2ч», «1д»).\n"
                    f"Автовключение при волне: {auto} (/fullguard auto on|off). Что видит радар: /fullguard radar.")
        left = "без срока" if not cfg.fort_until else f"ещё {human_dur(max(0.0, cfg.fort_until - now))}"
        who = "включилась сама" if cfg.fort_origin == "auto" else "включена вручную"
        c = self.eng.fort_counts.get(cid) or {}
        return (f"🛡 Полная защита: {who}, {left}.\n{icon} Угроза: {name} {self.fort_bar(score)}\n"
                f"За это время: убрано — {c.get('del', 0)}, заблокировано — {c.get('ban', 0)}, ограничено — {c.get('mute', 0)}.\n"
                f"Автовключение при волне: {auto}. Выключить: /fullguard off.")

    def fort_radar_text(self, cid: int, now: float) -> str:
        eng, cfg = self.eng, self.store.chat(cid).cfg
        idx, name, icon, score, actors = eng.radar_level(cid, now)
        kinds = eng.radar_kinds(cid, now)
        lines = [f"📡 <b>Радар угроз</b>: {icon} {name} {self.fort_bar(score)} ({score:g})",
                 f"Источников за последние {human_dur(RADAR_WINDOW)}: {actors}."]
        lines.append(("Что видно: " + "; ".join(f"{RADAR_LABEL.get(k, k)}{'' if k.startswith('raid') else f' — {n}'}"
                                                 for k, n in kinds[:6]) + ".") if kinds else "Угроз не видно.")
        if cfg.fort_on:
            lines.append("Режим включён: «мягкие» события (мат, ссылки, флуд) радар сейчас не считает.")
        elif cfg.fort_auto and eng.fort_auto_on:
            lines.append(f"Включится сам при оценке от {eng.fort_trip_score:g} и не меньше {eng.fort_trip_actors} источников "
                         f"(сейчас {score:g} и {actors}).")
        else:
            lines.append("Автовключение выключено: режим только вручную.")
        return "\n".join(lines)

    def fort_board_text(self, cid: int, now: float) -> str:
        cfg = self.store.chat(cid).cfg
        idx, name, icon, score, actors = self.eng.radar_level(cid, now)
        c = self.eng.fort_counts.get(cid) or {}
        left = "без срока" if not cfg.fort_until else f"ещё {human_dur(max(0.0, cfg.fort_until - now))}"
        who = "включилась сама" if cfg.fort_origin == "auto" else "включена вручную"
        lines = [f"🛡 <b>Полная защита</b>: {who}, {left}",
                 f"{icon} Угроза: <b>{name}</b> {self.fort_bar(score)}",
                 f"Убрано: {c.get('del', 0)} · заблокировано: {c.get('ban', 0)} · ограничено: {c.get('mute', 0)}"]
        if c.get("capfail") or c.get("sweep"):
            lines.append(f"Проверка при входе: не прошли — {c.get('capfail', 0)}, перепроверено — {c.get('sweep', 0)}")
        lines.append("<i>Новичкам закрыты ссылки, медиа и пересылки; вход — только через проверку.</i>")
        return "\n".join(lines)

    def fort_wave_text(self, cid: int, now: float) -> str:
        st = self.store.chats.get(cid)
        if st is None:
            return ""
        tot, bad, labels = 0, 0, {}
        for r in st.users.values():
            if not r.joined or now - r.joined > FORT_SOURCE_WINDOW:
                continue
            tot += 1
            if r.banned or r.muted_until > now:
                bad += 1
                if r.src:
                    labels[r.src] = labels.get(r.src, 0) + 1
        if tot < 3 or bad < 2:
            return ""
        window = human_dur(FORT_SOURCE_WINDOW)
        if labels:
            lab, n = max(labels.items(), key=lambda kv: kv[1])
            if n >= 2 and n * 2 >= bad:
                nm = esc(((self._invites(cid) or {}).get(lab) or {}).get("name") or lab, 24)
                return (f"🔗 Откуда волна: по ссылке «{nm}» вошло {n} из {bad} нарушителей за последние {window}. "
                        f"Отозвать ссылку: /revoke {nm} (бот сам ничего не отзывает).")
        return (f"За последние {window} вошло {tot}, нарушителей среди них {bad}."
                + ("" if labels else " Ссылки с метками (/invite) помогут найти источник следующей волны."))

    async def fort_feed(self, chat_id: int, uid: int, kind: str) -> None:
        try:
            self.eng.radar_note(chat_id, uid, kind, self.now())
            if self.eng.events:
                await self.handle_events()
        except asyncio.CancelledError:
            raise
        except Exception:
            log_fort.exception("радар: сбой")

    async def cmd_fullguard(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cid, now = m.chat.id, self.now()
        cfg = self.store.chat(cid, m.chat.title or "").cfg
        by = m.from_user.id
        toks = [t.lower() for t in args.replace(",", " ").split()]
        word = toks[0] if toks else ""
        if len(toks) > 1 and toks[1] in STRICT_UNITS and word.isdigit():
            word += toks[1]
        if word in FORT_OFF_WORDS:
            if not cfg.fort_on:
                return await self.out(m, "Полная защита и так выключена.", ttl=15)
            self.eng.fort_disable(cid, now, how="manual", by=by)
            return await self.handle_events()
        if word == "auto":
            val = toks[1] if len(toks) > 1 else ""
            if val in FORT_ON_WORDS:
                cfg.fort_auto = True
            elif val in FORT_OFF_WORDS:
                cfg.fort_auto = False
            else:
                return await self.out(m, "/fullguard auto on — включать полную защиту самому при волне (радар угроз); "
                                         "/fullguard auto off — только вручную.", ttl=30)
            self.store.dirty = True
            tail = "" if self.eng.fort_auto_on else " (но в настройках бота GUARD_FORT_AUTO=0, поэтому сам он не включится)"
            return await self.out(m, f"Автовключение полной защиты: {'вкл' if cfg.fort_auto else 'выкл'}.{tail}", ttl=30)
        if word in ("radar", "радар"):
            return await self.out(m, self.fort_radar_text(cid, now), ttl=60)
        if word in ("status", "статус", "?"):
            return await self.out(m, self.fort_text(cid, now), ttl=60)
        secs = 0.0
        if word and word not in FORT_ON_WORDS:
            mins = parse_minutes(word)
            if mins is None:
                return await self.out(m, "Не понял срок. Примеры: /fullguard 2ч, /fullguard 90м, /fullguard 1д, /fullguard off", ttl=25)
            secs = max(FORT_MIN_MIN, min(mins, FORT_MAX_MIN)) * 60.0
        elif cfg.fort_on and not word:
            return await self.out(m, self.fort_text(cid, now), ttl=60)
        rights = await self.rights(cid)
        if not (rights["delete"] and rights["restrict"]):
            await self.out(m, "⚠ У бота нет прав «удалять сообщения» и «ограничивать участников»: режим включу, но исполнять нечем.", ttl=25)
        if not self.eng.fort_enable(cid, origin="manual", seconds=secs, now=now, by=by):
            left = "без срока" if not cfg.fort_until else f"ещё {human_dur(max(0.0, cfg.fort_until - now))}"
            return await self.out(m, f"🛡 Полная защита уже включена: теперь {left} (управление у вас, сама она не снимется).", ttl=30)
        await self.handle_events()

    cmd_panic = cmd_fullguard

    async def fort_on_event(self, ev: dict) -> None:
        cid = ev["chat"]
        st = self.store.chats.get(cid)
        if st is None:
            return
        cfg, now = st.cfg, self.now()
        auto = ev.get("origin") == "auto"
        title = esc(st.title, 60)
        self.journal("fort_on", cid, st.title, ev.get("by", 0), "", ("авто: " + ev.get("why", "")) if auto else "вручную")
        log_fort.info("chat=%s: полная защита (%s) %s", cid, "сама" if auto else "вручную", ev.get("why", ""))
        self._fort_sig.pop(cid, None)
        self._fort_board_t[cid] = 0.0
        self._fort_fail.pop(cid, None)
        self._fort_remind_t[cid] = now
        if self.chat_ok(cid) and st.active:
            await self.fort_board_one(cid, now)
        chg = self.fort_changes(cfg.fort_before, cfg.fort_applied)
        until = "без срока" if not cfg.fort_until else f"на {human_dur(cfg.fort_until - now)}"
        lines = [f"🛡 <b>{title}</b>",
                 "Полная защита включилась сама." if auto else "Полная защита включена вручную."]
        if auto and ev.get("why"):
            lines.append(f"Что увидел радар: {esc(ev['why'], 160)}.")
        lines.append(f"Срок: {until}" + (" (пока идёт волна, продлевается сам)." if auto else ". Выключить: /fullguard off в чате."))
        if chg:
            lines.append("Изменено на время режима: " + "; ".join(chg[:8]) + (" …" if len(chg) > 8 else "")
                         + ". При выключении вернётся как было.")
        else:
            lines.append("Настройки и так были на максимуме: менять ничего не пришлось.")
        wave = self.fort_wave_text(cid, now)
        if wave:
            lines.append(wave)
        text = "\n".join(lines)
        if auto:
            from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
            kb = InlineKeyboardMarkup(inline_keyboard=[[
                Btn(text="🔓 Выключить", callback_data=f"fg:off:{cid}"),
                Btn(text="⏱ +1 час", callback_data=f"fg:ext:{cid}"),
                Btn(text="📌 Оставить", callback_data=f"fg:keep:{cid}")]])
            await self.alert(cid, text, kb)
        await self.plus_log(cid, text)
        if self.chat_ok(cid):
            self.later(1.0, self.fort_sweep, cid)

    async def fort_off_event(self, ev: dict) -> None:
        cid, rep, how = ev["chat"], ev["report"], ev.get("how", "manual")
        st = self.store.chats.get(cid)
        if st is None:
            return
        cfg, now = st.cfg, self.now()
        title = esc(st.title, 60)
        dur = human_dur(max(0.0, rep["ended"] - rep["started"]))
        why = {"auto": "угроза схлынула", "timer": "срок вышел"}.get(how, "выключена вручную")
        _, pname, picon = radar_name(rep.get("peak", 0.0))
        c = rep.get("counts") or {}
        summary = (f"Убрано: {c.get('del', 0)}, заблокировано: {c.get('ban', 0)}, ограничено: {c.get('mute', 0)}; "
                   f"не прошли проверку: {c.get('capfail', 0)}, перепроверено новичков: {c.get('sweep', 0)}.")
        self.journal("fort_off", cid, st.title, ev.get("by", 0), "", f"{why}; {dur}")
        log_fort.info("chat=%s: полная защита выключена (%s), %s", cid, why, dur)
        self._fort_sig.pop(cid, None)
        self._fort_board_t.pop(cid, None)
        self._fort_fail.pop(cid, None)
        self._fort_remind_t.pop(cid, None)
        board = rep.get("board") or 0
        if board and self.chat_ok(cid):
            final = (f"✅ <b>Полная защита выключена</b> ({why}, длилась {dur}). Пик угрозы: {picon} {pname}.\n"
                     f"{summary}\n<i>Настройки чата вернулись к прежним.</i>")
            if await self.call("edit_message_text", final, chat_id=cid, message_id=board) is not None:
                self.later(600, self.call, "delete_message", cid, board)
            else:
                self.deleter.add(cid, [board])
        restored = rep.get("restored") or {}
        kept = rep.get("kept") or []
        lines = [f"✅ <b>{title}</b>", f"Полная защита выключена ({why}). Длилась {dur}, пик угрозы: {picon} {pname}.", summary]
        back = [f"{FORT_LABELS.get(k, k)} — {self.fort_fmt(k, v)}" for k, v in restored.items()]
        if back:
            lines.append("Вернул: " + "; ".join(back[:10]) + (" …" if len(back) > 10 else "") + ".")
        if kept:
            lines.append("Оставил, как поставили вы сами во время режима: " + ", ".join(FORT_LABELS.get(k, k) for k in kept) + ".")
        wave = self.fort_wave_text(cid, now)
        if wave:
            lines.append(wave)
        text = "\n".join(lines)
        await self.alert(cid, text)
        await self.plus_log(cid, text)

    async def fort_board_one(self, cid: int, now: float) -> None:
        st = self.store.chats.get(cid)
        if st is None or not st.cfg.fort_on:
            return
        cfg = st.cfg
        if cfg.fort_before.get("quiet", cfg.quiet):
            return
        if now - self._fort_board_t.get(cid, 0.0) < FORT_BOARD_EVERY:
            return
        text = self.fort_board_text(cid, now)
        if cfg.fort_board and self._fort_sig.get(cid) == text:
            return
        self._fort_board_t[cid] = now
        self._fort_sig[cid] = text
        if cfg.fort_board:
            if await self.call("edit_message_text", text, chat_id=cid, message_id=cfg.fort_board) is not None:
                self._fort_fail[cid] = 0
                return
            self._fort_fail[cid] = self._fort_fail.get(cid, 0) + 1
            if self._fort_fail[cid] < 2:
                return
            self.deleter.add(cid, [cfg.fort_board])
        sent = await self.call("send_message", cid, text, disable_notification=True)
        if sent is not None:
            cfg.fort_board = sent.message_id
            self._fort_fail[cid] = 0
            self.store.dirty = True

    async def fort_tick(self, now: float) -> None:
        try:
            for cid in self.eng.fort_expired(now):
                st = self.store.chats.get(cid)
                self.eng.fort_disable(cid, now, how="auto" if st is not None and st.cfg.fort_origin == "auto" else "timer")
            if self.eng.events:
                await self.handle_events()
            for cid, st in list(self.store.chats.items()):
                cfg = st.cfg
                if not cfg.fort_on or not st.active or not self.chat_ok(cid):
                    continue
                await self.fort_board_one(cid, now)
                if not cfg.fort_until:
                    last = self._fort_remind_t.setdefault(cid, now)
                    if now - last >= FORT_REMIND:
                        self._fort_remind_t[cid] = now
                        await self.alert(cid, f"🛡 <b>{esc(st.title, 60)}</b>\nПолная защита включена уже "
                                              f"{human_dur(now - cfg.fort_started)} и без срока. Выключить: /fullguard off в чате.")
        except asyncio.CancelledError:
            raise
        except Exception:
            log_fort.exception("полная защита: сбой фоновой задачи")

    async def fort_sweep(self, cid: int) -> None:
        try:
            await self._fort_sweep(cid)
        except asyncio.CancelledError:
            raise
        except Exception:
            log_fort.exception("переаттестация: сбой")

    async def _fort_sweep(self, cid: int) -> None:
        from types import SimpleNamespace
        st = self.store.chats.get(cid)
        if st is None or not st.cfg.fort_on or not st.cfg.captcha or not self.chat_ok(cid):
            return
        if not (await self.rights(cid))["restrict"]:
            return
        now = self.now()
        admins = await self.admins(cid)
        cand = sorted((u for u, r in st.users.items()
                       if u > 0 and r.joined and now - r.joined <= FORT_SWEEP_WINDOW and not r.verified and not r.vouched
                       and not r.banned and r.clean < 3 and r.muted_until <= now and u not in admins and u != self.me_id
                       and not self.is_trusted(u) and f"{cid}:{u}" not in self.store.captchas),
                      key=lambda u: -st.users[u].joined)[:FORT_SWEEP_MAX]
        chat = SimpleNamespace(id=cid, title=st.title)
        done = 0
        for uid in cand:
            if not self.fort_active_now(cid):
                break
            mem = await self.call("get_chat_member", cid, uid)
            if mem is None or status_of(mem) != "member" or getattr(mem.user, "is_bot", False):
                continue
            plan = self.captcha_plan(chat, mem.user, st, self.now())
            await self.start_captcha(chat, mem.user, None, plan)
            self.eng.fort_count(cid, "sweep")
            done += 1
            await asyncio.sleep(0.5)
        if done:
            self.journal("fort_sweep", cid, st.title, 0, "", f"перепроверено новичков: {done}")

    def fort_active_now(self, cid: int) -> bool:
        return self.eng.fort_active(cid)

    async def on_fort_button(self, cb) -> None:
        try:
            _, act, cid = (cb.data or "").split(":")
            cid = int(cid)
        except ValueError:
            return await cb.answer()
        who = getattr(cb, "from_user", None)
        if who is None or who.id not in self.owners:
            return await cb.answer("Только для владельца.", show_alert=False)
        st = self.store.chats.get(cid)
        if st is None or not self.chat_ok(cid):
            return await cb.answer()
        now = self.now()
        cfg = st.cfg
        popup = ""
        if act == "tg":
            if cfg.fort_on:
                self.eng.fort_disable(cid, now, how="manual", by=who.id)
                popup = "Полная защита выключена, настройки вернулись."
            else:
                self.eng.fort_enable(cid, origin="manual", now=now, by=who.id)
                popup = "Полная защита включена."
        elif not cfg.fort_on:
            popup = "Режим уже выключен."
        elif act == "off":
            self.eng.fort_disable(cid, now, how="manual", by=who.id)
            popup = "Полная защита выключена, настройки вернулись."
        elif act == "ext":
            if self.eng.fort_extend(cid, 3600, now):
                popup = f"Продлено: ещё {human_dur(max(0.0, cfg.fort_until - now))}."
            else:
                popup = "У режима нет срока: он и так до ручного выключения."
        elif act == "keep":
            self.eng.fort_keep(cid)
            popup = "Оставил до ручного выключения: /fullguard off."
        if self.eng.events:
            await self.handle_events()
        cmsg = getattr(cb, "message", None)
        if cmsg is not None:
            if act == "tg" and cmsg.chat.id == cid:
                text, kb = self.panel(cid)
                await self.call("edit_message_text", text, chat_id=cid, message_id=cmsg.message_id, reply_markup=kb)
            elif act != "tg":
                await self.call("edit_message_reply_markup", chat_id=cmsg.chat.id, message_id=cmsg.message_id, reply_markup=None)
        await cb.answer(popup or None, show_alert=False)


log_ap = logging.getLogger("guard.autopilot")

AP_LABELS = {**FORT_LABELS, "slow": "медленный режим", "trace": "Следопыт", "conflicts": "конфликты"}
AP_ON_WORDS = FORT_ON_WORDS
AP_OFF_WORDS = FORT_OFF_WORDS


class Autopilot:

    def init_ap_ui(self) -> None:
        self._ap_alert_t: dict[tuple, tuple] = {}

    def ap_fmt(self, key: str, val) -> str:
        if key == "slow":
            return f"{val} с" if val else "выкл"
        if key == "trace":
            return {"on": "вкл", "log": "наблюдение", "off": "выкл"}.get(val, str(val))
        return self.fort_fmt(key, val)

    def ap_changes(self, changes: list, limit: int = 8) -> str:
        rows = [f"{AP_LABELS.get(k, k)}: {self.ap_fmt(k, a)} → {self.ap_fmt(k, b)}" for k, a, b in changes]
        return "; ".join(rows[:limit]) + (" …" if len(rows) > limit else "")

    def ap_reflex_by_name(self, word: str) -> str:
        w = (word or "").lower().strip()
        for key, spec in AP_REFLEXES.items():
            if w == key or w in spec["alias"]:
                return key
        return ""

    def ap_status_line(self, cid: int, now: float) -> str:
        cfg = self.store.chat(cid).cfg
        if not (cfg.autopilot and self.eng.ap_on):
            return "Автопилот: выкл" + ("" if self.eng.ap_on else " (в настройках бота GUARD_AUTOPILOT=0)")
        lv = self.eng.ap_levels(cid)
        if lv:
            what = ", ".join(f"{AP_REFLEXES[r]['icon']} {AP_LEVEL_NAME[n]}" for r, n in lv.items())
            return f"Автопилот: работает ({what}) · настройки временно усилены, вернутся сами · /autopilot"
        if "calm" in cfg.ap_state:
            return "Автопилот: затишье (мелочи смягчены, вернутся при первой угрозе) · /autopilot"
        return "Автопилот: наготове · /autopilot"

    def ap_text(self, cid: int, now: float) -> str:
        cfg, eng = self.store.chat(cid).cfg, self.eng
        lines = [f"🤖 <b>Автопилот</b>: {'вкл' if cfg.autopilot else 'выкл'}"
                 + ("" if eng.ap_on else " (но в настройках бота GUARD_AUTOPILOT=0, поэтому он не работает)")]
        if cfg.fort_on:
            lines.append("Полная защита включена: она главнее, автопилот пока ждёт.")
        act = []
        for r, s in list(cfg.ap_state.items()):
            if r in AP_REFLEXES and _ap_lvl(s) > 0:
                spec = AP_REFLEXES[r]
                eta = eng.ap_eta(cid, r, now)
                act.append(f"{spec['icon']} {spec['label']}: <b>{AP_LEVEL_NAME[_ap_lvl(s)]}</b> с {self.fmt_when(s.get('since', now))}"
                           + (f" — {esc(s.get('why', ''), 80)}" if s.get("why") else "")
                           + (f" · если новых угроз не будет, ступень снизится примерно через {human_dur(eta)}" if eta else ""))
        lines += (["Сейчас работает:"] + act) if act else ["Сейчас спокойно: рефлексы наготове."]
        if "calm" in cfg.ap_state:
            lines.append(f"🕊 Затишье: смягчил только то, что вы не трогали ({'; '.join(AP_LABELS.get(k, k) for k in AP_CALM)}).")
        if cfg.ap_applied:
            lines.append("Временно изменено: " + self.ap_changes(
                [(k, cfg.ap_before.get(k), v) for k, v in cfg.ap_applied.items()]) + ". Вернётся само.")
        scar = eng.ap_scar_now(cfg, now)
        if scar >= 0.5:
            lines.append(f"🔧 Закалка {scar:.1f}: чат уже атаковали, поэтому рефлексы срабатывают раньше и держатся дольше.")
        hrs = cfg.ap_hours
        if len(hrs) == 24 and sum(hrs) >= 4:
            top = sorted(range(24), key=lambda h: -hrs[h])[:2]
            lines.append("⏰ Волны чаще бывают около: " + ", ".join(f"{(h + self.tz_h) % 24:02d}:00" for h in sorted(top))
                         + " — в эти часы бот настороже.")
        cool = [f"{AP_REFLEXES[r]['label']} (ещё {human_dur(t - now)})" for r, t in cfg.ap_cool.items()
                if r in AP_REFLEXES and t > now]
        if cool:
            lines.append("Отступил после вашего возражения: " + "; ".join(cool) + ".")
        if cfg.ap_off:
            lines.append("Выключено вами: " + ", ".join(AP_REFLEXES[r]["label"] for r in cfg.ap_off if r in AP_REFLEXES) + ".")
        lines.append("<i>/autopilot why — что решил и почему · /autopilot off|on [имя] · имена: волна, наплыв, самозванцы, "
                     "флуд, накал, 18+ · /autopilot forget — забыть «закалку»</i>")
        return "\n".join(lines)

    def ap_why_text(self, cid: int) -> str:
        notes = list(self.eng.ap_log.get(cid) or ())[-12:]
        if not notes:
            return "Автопилот пока ничего не решал в этом чате."
        return "🤖 <b>Что решил автопилот</b> (последние):\n" + "\n".join(f"{self.fmt_when(t)} — {esc(x, 160)}" for t, x in notes)

    def ap_dbg_text(self, cid: int, now: float) -> str:
        eng, cfg = self.eng, self.store.chat(cid).cfg
        if not eng.ap_brain:
            return "🧠 Внутренние поправки выключены (GUARD_AP_BRAIN=0): работает чистый автопилот."
        lines = ["🧠 <b>Внутренние поправки автопилота</b>"]
        doubt = [f"{r} {eng.ap_doubt_now(cfg, r, now):.2f}" for r in AP_REFLEXES if eng.ap_doubt_now(cfg, r, now) > 0.05]
        lines.append("сомнение владельца: " + (", ".join(doubt) or "нет"))
        vig = [f"{r} ещё {human_dur(t - now)}" for (c, r), t in eng.ap_vigil.items() if c == cid and t > now]
        aft = [f"{r} ещё {human_dur(t - now)}" for (c, r), t in eng.ap_after.items() if c == cid and t > now]
        lines.append("настороже: " + ("; ".join(vig) or "нет") + " · эхо-волна: " + ("; ".join(aft) or "нет"))
        nb = [f"{r}: {eng.ap_neighbors(cid, r, now)}" for r in AP_COMBO if eng.ap_neighbors(cid, r, now)]
        lines.append("соседние чаты на уровне 2+: " + (", ".join(nb) or "нет"))
        t = eng.ap_admin_t.get(cid)
        lines.append("админ писал: " + (f"{human_dur(now - t)} назад" if t else "не видел с запуска"))
        vec = eng.ap_vec_hot(cid, now)
        lines.append("чем бьют (3+ источника): " + (", ".join(vec) or "ничем одним"))
        bgs = [f"{r} {float(v[0]):.2f}→×{eng.ap_bg_factor(cfg, r, now):.2f}" for r, v in (cfg.ap_bg or {}).items()
               if r in AP_REFLEXES and isinstance(v, (list, tuple)) and len(v) == 3 and eng.ap_bg_factor(cfg, r, now) != 1.0]
        lines.append("обычный фон сдвигает пороги: " + (", ".join(bgs) or "нет") + f" · знакомых лиц в памяти: {len(eng.ap_known)}")
        saved = [f"{r}: {', '.join(s.get('vec') or ())}" for r, s in cfg.ap_state.items() if r in AP_REFLEXES and isinstance(s, dict) and s.get("vec")]
        if saved:
            lines.append("адресные замки: " + "; ".join(saved))
        notes = list(eng.ap_dbg.get(cid) or ())[-10:]
        lines.append("<b>Где поправки изменили решение:</b>" if notes else "Поправки пока не меняли решений.")
        lines += [f"{self.fmt_when(ts)} — {esc(x, 200)}" for ts, x in notes]
        return "\n".join(lines)

    def ap_feed_heat(self, ev: dict, cid: int) -> None:
        now, kind = self.now(), ev.get("kind")
        if kind == "dogpile":
            for u in list(ev.get("people") or [])[:6]:
                self.eng.ap_pulse(cid, u, "heat", now=now)
        elif kind == "provocation":
            self.eng.ap_pulse(cid, ev["baiter"], "heat_bait", now=now)
            self.eng.ap_pulse(cid, ev["victim"], "heat_bait", now=now)
        elif kind == "provocation_repeat":
            self.eng.ap_pulse(cid, ev["baiter"], "heat", 1.0, now)

    async def ap_tick(self, now: float) -> None:
        try:
            self.eng.ap_tz_h = self.tz_h
            for cid, st in list(self.store.chats.items()):
                if not st.active or not self.chat_ok(cid):
                    continue
                try:
                    self.eng.ap_step(cid, now)
                except Exception:
                    log_ap.exception("автопилот: сбой в чате %s", cid)
            if self.eng.events:
                await self.handle_events()
        except asyncio.CancelledError:
            raise
        except Exception:
            log_ap.exception("автопилот: сбой фоновой задачи")

    async def ap_event(self, ev: dict) -> None:
        cid = ev["chat"]
        st = self.store.chats.get(cid)
        if st is None:
            return
        now, title = self.now(), esc(st.title, 60)
        lines, rows, loud = [], [], False
        for reflex, old, new, why, score, actors in ev.get("trans") or ():
            if reflex == "calm":
                self.journal("ap", cid, st.title, 0, "", "затишье: смягчаю мелочи" if new else "затишье кончилось")
                continue
            spec = AP_REFLEXES[reflex]
            if new == 0 and why == "done":
                text = (f"{spec['icon']} {spec['label']}: отбой (дошло до уровня «{AP_LEVEL_NAME[int(score)]}», "
                        f"длилось {human_dur(actors)}); настройки возвращены")
                loud = loud or score >= 2
            else:
                text = f"{spec['icon']} " + ApCore._ap_note_text(reflex, old, new, why, score, actors)
            self.journal("ap", cid, st.title, 0, "", text[:78])
            log_ap.info("chat=%s: %s", cid, text)
            lines.append(esc(text, 220))
            if new >= 2 and new > old:
                last = self._ap_alert_t.get((cid, reflex))
                if not last or new > last[1] or now - last[0] >= AP_ALERT_COOL:
                    self._ap_alert_t[(cid, reflex)] = (now, new)
                    loud = True
                    rows.append((reflex, spec["label"]))
        for reflex, lvl, secs in ev.get("stale") or ():
            spec = AP_REFLEXES.get(reflex)
            if spec is None:
                continue
            text = (f"{spec['icon']} {spec['label']}: уровень «{AP_LEVEL_NAME[lvl]}» держится уже {human_dur(secs)}. "
                    f"Если угроза давно миновала — нажмите «Откатить»; если нет, всё снимется само, когда спадёт.")
            self.journal("ap", cid, st.title, 0, "", text[:78])
            log_ap.info("chat=%s: %s", cid, text)
            lines.append(esc(text, 260))
            loud = True
            rows.append((reflex, spec["label"]))
        if not lines and not ev.get("changes"):
            return
        ch = self.ap_changes(ev.get("changes") or [])
        body = "\n".join(lines) + (f"\nИзменено: {ch}." if ch else "")
        await self.plus_log(cid, f"🤖 <b>{title}</b>\n{body}")
        if loud:
            kb = None
            if rows:
                from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
                kb = InlineKeyboardMarkup(inline_keyboard=[
                    [Btn(text=f"↩️ Откатить: {label[:22]}", callback_data=f"ag:undo:{cid}:{r}"),
                     Btn(text="🔕 Не включать", callback_data=f"ag:off:{cid}:{r}")] for r, label in rows[:2]])
            await self.alert(cid, f"🤖 <b>{title}</b>\n{body}\n<i>Вернётся само, когда спадёт. Подробности: /autopilot в чате.</i>", kb)
        if ev.get("strict") and st.cfg.strict_auto and self.eng.strict_auto_on and not self.eng.strict_active(cid, now):
            from types import SimpleNamespace
            self.eng.strict_set(cid, AP_STRICT_MIN * 60.0, now)
            await self.strict_announce(SimpleNamespace(id=cid, title=st.title), auto=True,
                                       why="автопилот: волна спама дошла до жёсткого уровня")

    async def cmd_autopilot(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        cid, now = m.chat.id, self.now()
        cfg = self.store.chat(cid, m.chat.title or "").cfg
        toks = args.lower().replace(",", " ").split()
        word = toks[0] if toks else ""
        name = self.ap_reflex_by_name(toks[1]) if len(toks) > 1 else ""
        if len(toks) > 1 and not name and word in AP_ON_WORDS + AP_OFF_WORDS:
            return await self.out(m, "Не знаю такого рефлекса. Имена: волна, наплыв, самозванцы, флуд, накал, 18+.", ttl=25)
        if word in AP_OFF_WORDS:
            if name:
                if name not in cfg.ap_off:
                    cfg.ap_off.append(name)
                cfg.ap_state.pop(name, None)
                self.eng.ap_doubt_add(cfg, name, now, 1.0)
                self.eng.ap_note(cid, now, f"{AP_REFLEXES[name]['label']}: выключен владельцем")
                self.store.dirty = True
                self.eng.ap_step(cid, now)
                if self.eng.events:
                    await self.handle_events()
                return await self.out(m, f"{AP_REFLEXES[name]['icon']} Рефлекс «{AP_REFLEXES[name]['label']}» выключен. "
                                         f"Включить: /autopilot on {name}.", ttl=30)
            cfg.autopilot = False
            self.store.dirty = True
            if cfg.fort_on:
                return await self.out(m, "🤖 Автопилот выключен; настройки вернутся, когда выключится полная защита.", ttl=30)
            self.eng.ap_release_all(cid, now, "off")
            if self.eng.events:
                await self.handle_events()
            return await self.out(m, "🤖 Автопилот выключен, настройки вернулись как были.", ttl=30)
        if word in AP_ON_WORDS:
            if name:
                if name in cfg.ap_off:
                    cfg.ap_off.remove(name)
                cfg.ap_cool.pop(name, None)
                self.store.dirty = True
                return await self.out(m, f"{AP_REFLEXES[name]['icon']} Рефлекс «{AP_REFLEXES[name]['label']}» снова включён.", ttl=30)
            cfg.autopilot = True
            self.store.dirty = True
            tail = "" if self.eng.ap_on else " (но в настройках бота GUARD_AUTOPILOT=0, поэтому он не заработает)"
            return await self.out(m, f"🤖 Автопилот включён.{tail}", ttl=30)
        if word in ("dbg", "debug"):
            return await self.out(m, self.ap_dbg_text(cid, now), ttl=90)
        if word in ("why", "почему", "log", "журнал"):
            return await self.out(m, self.ap_why_text(cid), ttl=90)
        if word in ("forget", "забыть", "reset", "сброс"):
            cfg.ap_scar, cfg.ap_scar_t, cfg.ap_hours, cfg.ap_cool = 0.0, 0.0, [], {}
            cfg.ap_doubt, cfg.ap_dow, cfg.ap_bg = {}, [], {}
            self.store.dirty = True
            return await self.out(m, "🤖 Забыл «закалку» и «чуйку на время»: пороги снова обычные.", ttl=30)
        return await self.out(m, self.ap_text(cid, now), ttl=90)

    cmd_ap = cmd_autopilot

    async def on_ap_button(self, cb) -> None:
        parts = (getattr(cb, "data", "") or "").split(":")
        if len(parts) != 4:
            return await cb.answer()
        _, act, cid_s, reflex = parts
        try:
            cid = int(cid_s)
        except ValueError:
            return await cb.answer()
        who = getattr(cb, "from_user", None)
        if who is None or who.id not in self.owners:
            return await cb.answer("Только для владельца.", show_alert=False)
        st = self.store.chats.get(cid)
        if st is None or not self.chat_ok(cid) or reflex not in AP_REFLEXES:
            return await cb.answer()
        cfg, now = st.cfg, self.now()
        label = AP_REFLEXES[reflex]["label"]
        if act == "undo":
            cool = self.eng.ap_rollback(cfg, reflex, now)
            cfg.ap_state.pop(reflex, None)
            self.eng.ap_note(cid, now, f"{label}: владелец откатил кнопкой, не включаю {human_dur(cool)}")
            popup = f"Откатил. Не включу «{label}» ещё {human_dur(cool)}."
        elif act == "off":
            if reflex not in cfg.ap_off:
                cfg.ap_off.append(reflex)
            cfg.ap_state.pop(reflex, None)
            self.eng.ap_doubt_add(cfg, reflex, now, 1.5)
            self.eng.ap_note(cid, now, f"{label}: выключен владельцем кнопкой")
            popup = f"Рефлекс «{label}» выключен. Вернуть: /autopilot on {reflex}."
        else:
            return await cb.answer()
        self.store.dirty = True
        self.eng.ap_step(cid, now)
        if self.eng.events:
            await self.handle_events()
        cmsg = getattr(cb, "message", None)
        if cmsg is not None:
            await self.call("edit_message_reply_markup", chat_id=cmsg.chat.id, message_id=cmsg.message_id, reply_markup=None)
        await cb.answer(popup, show_alert=False)


log = logging.getLogger("guard")

ALLOWED_UPDATES = ["message", "edited_message", "callback_query", "chat_member", "my_chat_member", "chat_join_request",
                   "message_reaction"]


class LearnUI:
    """Самообучение, часть для Telegram: карточки владельцу, кнопки, обучение пересылкой, вечерняя справка."""

    LEARN_ACT_RU = {"s": "спам", "sb": "спам, автор забанен", "h": "нормально", "x": "не учить"}

    @staticmethod
    def learn_kb(card_id: str):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        return InlineKeyboardMarkup(inline_keyboard=[
            [Btn(text="🚫 Спам", callback_data=f"ln:{card_id}:s"), Btn(text="✅ Нормально", callback_data=f"ln:{card_id}:h")],
            [Btn(text="🚫🔨 Спам + бан автора", callback_data=f"ln:{card_id}:sb"),
             Btn(text="🤷 Не учить", callback_data=f"ln:{card_id}:x")]])

    @staticmethod
    def learn_undo_kb(tid: str):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        return InlineKeyboardMarkup(inline_keyboard=[[Btn(text="↩ Отменить", callback_data=f"ln:{tid}:u")]])

    def learn_card_text(self, c: dict, title: str, name: str, text: str, link: str, deleted: bool) -> str:
        lines = [f"🧠 <b>Проверь меня</b> · «{esc(title, 40)}»",
                 f"Автор: {mention(c['uid'], name)} · {TIER_RU.get(c['tier'], c['tier'])}",
                 (f"Я <b>удалил</b> это сообщение (оценка {c['eff']:g})" if deleted
                  else f"Я <b>оставил</b> это сообщение, но оно подозрительное (оценка {c['eff']:g})")
                 + (f": {esc(c['why'], 160)}" if c.get("why") else "")]
        if text:
            lines.append("«" + esc(text.strip(), 420) + "»")
        if link:
            lines.append(f'<a href="{link}">Перейти к сообщению</a>')
        if c.get("dup"):
            lines.append(f"Ещё {c['dup']} похожих я уже не показываю.")
        lines.append("Это спам?")
        return "\n".join(lines)

    async def learn_offer(self, m, msg: Msg, v: Verdict) -> None:
        card_id = v.info.get("learn_card")
        c = self.eng.learn_card(card_id) if card_id else None
        if c is None:
            return
        owners = sorted(self.store.alert_users & self.owners)
        if not owners:
            return
        deleted = not v.ok
        text = self.learn_card_text(c, m.chat.title or "", msg.name, msg.text, "" if deleted else msg_link(m.chat, msg.msg_id), deleted)
        kb = self.learn_kb(card_id)
        quiet = time.gmtime(self.now() + self.tz_h * 3600).tm_hour < 8
        for uid in owners:
            sent = await self.call("send_message", uid, text, reply_markup=kb, disable_notification=quiet)
            if sent is not None:
                c["own"][str(uid)] = sent.message_id
        self.store.dirty = True

    async def learn_apply(self, res: dict) -> None:
        cid = res["cid"]
        if not cid:
            return
        rights = await self.rights(cid)
        for chat_id, ids in res["delete"].items():
            ids = sorted(set(ids))
            if ids and rights["delete"]:
                self.deleter.add(chat_id, ids)
        if not rights["restrict"]:
            return
        admins = await self.admins(cid)
        for uid in res["ban"]:
            if uid in admins or self.is_trusted(uid) or uid == self.me_id:
                self.eng.forgive(cid, uid)
                continue
            await self.call("ban_chat_member", cid, uid, revoke_messages=True)
        for uid in res["unmute"]:
            await self.unrestrict(cid, uid)

    async def on_learn_button(self, cb) -> None:
        parts = (getattr(cb, "data", "") or "").split(":")
        if len(parts) != 3:
            return await cb.answer()
        _, card_id, act = parts
        uid = cb.from_user.id
        if uid not in self.owners:
            return await cb.answer("Только для владельца.", show_alert=False)
        msg = getattr(cb, "message", None)
        orig = ((getattr(msg, "html_text", None) or getattr(msg, "text", None) or "") if msg is not None else "").split("\n\n▬")[0]
        who = esc(getattr(cb.from_user, "full_name", "") or uid, 30)
        if act == "u":
            ok = self.eng.learn_undo(card_id)
            if ok and msg is not None:
                await self.call("edit_message_text", "↩ Отменил: забыл то, что выучил из этой пересылки.",
                                chat_id=msg.chat.id, message_id=msg.message_id)
            return await cb.answer("Отменено." if ok else "Уже нельзя отменить.")
        if act == "z":
            res = self.eng.learn_undo_card(card_id, uid, self.now())
            if not res["ok"]:
                return await cb.answer("Уже нельзя отменить.")
            for u2 in res["unban"]:
                await self.call("unban_chat_member", res["cid"], u2, only_if_banned=True)
            c = res["cards"]
            for ouid, mid in (c.get("own") or {}).items():
                if msg is not None and int(ouid) == msg.chat.id and mid == msg.message_id and orig:
                    await self.call("edit_message_text", orig, chat_id=int(ouid), message_id=mid, reply_markup=self.learn_kb(card_id))
                else:
                    await self.call("edit_message_text", f"↩ Ответ отменён ({who}). Удалённые сообщения вернуть нельзя.",
                                    chat_id=int(ouid), message_id=mid, reply_markup=self.learn_kb(card_id))
            return await cb.answer("Отменил, можно ответить заново.")
        if act == "v":
            r = self.eng.learn_vouch(card_id)
            if not r["ok"]:
                return await cb.answer("Уже поручились." if r.get("already") else "Сейчас нельзя.")
            if msg is not None:
                await self.call("edit_message_reply_markup", chat_id=msg.chat.id, message_id=msg.message_id,
                                reply_markup=self.learn_after_kb(card_id))
            return await cb.answer("Поручился: бот будет считать автора проверенным.")
        if act == "r":
            c = self.eng.learn_card(card_id)
            found = re.search(r"«(.*)»", orig, re.S) if orig else None
            if not c or not c.get("done") or c["done"].get("act") != "h" or c.get("kind") != "del" or c.get("restored") or not found:
                return await cb.answer("Вернуть нельзя: текста нет или уже возвращено.")
            c["restored"] = True
            await self.call("send_message", c["cid"], f"↩ Сообщение {mention(c['uid'], 'участника')} удалено по ошибке, возвращаю:\n«{found.group(1)}»")
            if msg is not None:
                await self.call("edit_message_reply_markup", chat_id=msg.chat.id, message_id=msg.message_id,
                                reply_markup=self.learn_after_kb(card_id))
            return await cb.answer("Вернул в чат.")
        if act not in self.LEARN_ACT_RU:
            return await cb.answer()
        res = self.eng.learn_decide(card_id, act, uid, self.now())
        if not res["ok"]:
            return await cb.answer("Уже отвечено." if res["why"] == "done" else "Карточка устарела.")
        await self.learn_apply(res)
        c = res["cards"]
        head = {"s": "🚫 Запомнил: это спам", "sb": "🚫🔨 Запомнил: спам, автор забанен", "h": "✅ Запомнил: это нормально",
                "x": "🤷 Не учусь на этом"}[act]
        extra = ("\n• " + "\n• ".join(esc(n, 200) for n in res["notes"])) if res["notes"] else ""
        tail = f"{head} ({who}){extra}"
        undo = self.learn_after_kb(card_id)
        for ouid, mid in (c.get("own") or {}).items():
            if msg is not None and int(ouid) == msg.chat.id and mid == msg.message_id and orig:
                await self.call("edit_message_text", (orig[:3500] + "\n\n▬ " + tail)[:4000], chat_id=int(ouid), message_id=mid,
                                reply_markup=undo)
            else:
                await self.call("edit_message_text", tail, chat_id=int(ouid), message_id=mid)
        await cb.answer("Запомнил." if act != "x" else "Ок.")

    def learn_after_kb(self, card_id: str):
        """Кнопки под уже отвеченной карточкой: после «нормально» можно поручиться за автора и вернуть удалённое сообщение."""
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        c = self.eng.learn_card(card_id) or {}
        rows = []
        if (c.get("done") or {}).get("act") == "h":
            row = []
            if not (c.get("fx") or {}).get("vouch"):
                row.append(Btn(text="🤝 Поручиться за автора", callback_data=f"ln:{card_id}:v"))
            if c.get("kind") == "del" and not c.get("restored"):
                row.append(Btn(text="📩 Вернуть в чат", callback_data=f"ln:{card_id}:r"))
            if row:
                rows.append(row)
        rows.append([Btn(text="↩ Это ошибка, отменить", callback_data=f"ln:{card_id}:z")])
        return InlineKeyboardMarkup(inline_keyboard=rows)

    async def learn_private(self, m) -> bool:
        """Владелец пересылает боту спам в личку — бот выучивает его сразу, даже если сам его не заметил."""
        u = getattr(m, "from_user", None)
        if u is None or u.id not in self.owners:
            return False
        fwd = (getattr(m, "forward_origin", None) or getattr(m, "forward_date", None)
               or getattr(m, "forward_from", None) or getattr(m, "forward_from_chat", None))
        if not fwd:
            return False
        p = self._pending.get(u.id)
        if p is not None and p.get("stage") == "wait":
            return False
        text = (getattr(m, "text", None) or getattr(m, "caption", None) or "").strip()
        if len(text) < 12 or text.startswith("/"):
            return False
        msg = to_msg(m, uid=u.id, name=user_name(u))
        res = self.eng.learn_from_text(text[:3000], msg.ents, u.id, self.now())
        if not res.get("ok"):
            return False
        lines = ["🧠 <b>Выучил этот спам.</b>"]
        if res["short"]:
            lines.append("• текст короткий — отпечаток шаблона не делаю, запомнил только слова и контакты")
        elif res["new"]:
            lines.append("• новый шаблон: ловлю похожие тексты, в том числе переписанные")
        else:
            lines.append("• такой шаблон уже был — усилил")
        if res["contacts"]:
            lines.append("• контакты (во всех чатах, на 30 дней): " + ", ".join(f"<code>{esc(t, 40)}</code>" for t in res["contacts"][:4]))
        lines.append(f"• слов-маркеров: {res['words']}")
        lines.append("<i>Сам текст не сохранён, только отпечаток.</i>")
        await self.out(m, "\n".join(lines), markup=self.learn_undo_kb(res["id"]))
        return True

    async def learn_tick(self, now: float) -> None:
        try:
            L = self.eng._L()
            if now - L["g"].get("gc_t", 0.0) > 6 * 3600:
                r = self.eng.learn_gc(now)
                if r["expired"] or r["dropped"]:
                    log_learn.info("самообучение: прибрал шаблонов %d (устарели), %d (ошибались)", r["expired"], r["dropped"])
            local = time.gmtime(now + self.tz_h * 3600)
            today = time.strftime("%Y-%m-%d", local)
            if local.tm_hour != LEARN_REPORT_HOUR or L.get("rep") == today:
                return
            L["rep"] = today
            self.store.dirty = True
            if not self.eng.learn_active_today(now):
                return
            await self.notify_alert_owners(self.eng.learn_report(now))
        except asyncio.CancelledError:
            raise
        except Exception:
            log_learn.exception("самообучение: вечерняя справка не удалась")

    async def notify_alert_owners(self, text: str) -> int:
        n = 0
        for uid in sorted(self.store.alert_users & self.owners):
            if await self.call("send_message", uid, text, disable_notification=True) is not None:
                n += 1
        return n


class LearnTG:
    """Самообучение+, часть для Telegram: реакции, /spam, баны владельца (командой и из меню Telegram), /learn."""

    def init_learn_tg(self) -> None:
        self._lp_hint: dict = {}
        self._lp_rq: dict = {}
        self._lp_rqn = 0
        self._lp_qlog: dict = {}

    def _lp_tier(self, rec, now: float) -> str:
        if rec is None:
            return "new"
        if rec.vouched:
            return "veteran"
        p = self.eng.trust_points(rec, now)
        return "veteran" if p >= 60 else "member" if p >= 20 else "new"

    @staticmethod
    def _lp_emoji(rx) -> set:
        out = set()
        for r in rx or ():
            e = getattr(r, "emoji", None)
            if e:
                out.add(str(e).replace("\ufe0f", ""))
        return out

    async def lp_finish(self, res: dict, act: str, user, label: str) -> None:
        """Применить урок и сообщить владельцам (с кнопкой отмены, как у обычных карточек)."""
        await self.learn_apply(res)
        c = res["cards"]
        card_id = res["card_id"]
        ent = self.eng._lpc.get((c["cid"], c["mid"])) or {}
        st = self.store.chats.get(c["cid"])
        head = self.learn_card_text(c, st.title if st else "", ent.get("name") or "участник", ent.get("snip", ""), "", c.get("kind") == "del")
        who = esc(getattr(user, "full_name", "") or getattr(user, "id", ""), 30)
        lead = {"s": "🚫 Запомнил: это спам", "sb": "🚫🔨 Запомнил: спам, автор забанен", "h": "✅ Запомнил: это нормально"}.get(act, "🧠 Запомнил")
        extra = ("\n• " + "\n• ".join(esc(n, 200) for n in res["notes"])) if res.get("notes") else ""
        text = (head + f"\n\n▬ {lead} ({label}, {who})" + extra)[:4000]
        kb = self.learn_after_kb(card_id)
        for uid in sorted(self.store.alert_users & self.owners):
            mid = (c.get("own") or {}).get(str(uid))
            if mid:
                await self.call("edit_message_text", text, chat_id=uid, message_id=mid, reply_markup=kb)
                continue
            sent = await self.call("send_message", uid, text, reply_markup=kb, disable_notification=True)
            if sent is not None:
                c["own"][str(uid)] = sent.message_id
        self.store.dirty = True

    # ───────── реакции владельца
    async def on_reaction(self, ev) -> None:
        try:
            await self.lp_reaction(ev)
        except asyncio.CancelledError:
            raise
        except Exception:
            log_learn.exception("самообучение+: реакция не обработана")
        return await super().on_reaction(ev)

    async def lp_reaction(self, ev) -> None:
        chat, user = getattr(ev, "chat", None), getattr(ev, "user", None)
        if (chat is None or user is None or user.id not in self.owners or getattr(chat, "type", "") not in GROUP_TYPES
                or not self.eng.lp_on or not self.eng.learn_on or not self.chat_ok(chat.id)):
            return
        st = self.store.chat(chat.id, create=False)
        if st is None or not st.cfg.learn or not st.cfg.scam:
            return
        new = self._lp_emoji(getattr(ev, "new_reaction", None)) - self._lp_emoji(getattr(ev, "old_reaction", None))
        act = "sb" if new & LP_REACT_BAN else "s" if new & LP_REACT_SPAM else "h" if new & LP_REACT_OK else ""
        if not act:
            return
        now = self.now()
        mode = self.eng.lp_rxmode(user.id)
        if mode == "off":
            return
        if act != "h" and mode == "ask":
            return await self.lp_ask(chat, ev.message_id, act, user, sorted(new)[0], now)
        res = self.eng.lp_teach(chat.id, ev.message_id, act, user.id, "react", now)
        if not res["ok"]:
            if res["why"] == "nocache" and act != "h":
                await self.lp_nocache_hint(user.id, now)
            return
        await self.lp_finish(res, act, user, "реакция")

    async def lp_nocache_hint(self, uid: int, now: float) -> None:
        if now - self._lp_hint.get(uid, 0) > 6 * 3600:
            self._lp_hint[uid] = now
            await self.call("send_message", uid, "🧠 Реакцию вижу, но этого сообщения уже не помню (держу только последние "
                            "несколько часов). Ответьте на него командой /spam — выучу и так.", disable_notification=True)

    async def lp_ask(self, chat, mid: int, act: str, user, emoji: str, now: float) -> None:
        """Реакция могла быть просто эмоцией: сначала спрашиваем владельца в личке."""
        ent = self.eng._lpc.get((chat.id, mid))
        if ent is None:
            return await self.lp_nocache_hint(user.id, now)
        if ent.get("lesson") or any(q["cid"] == chat.id and q["mid"] == mid and q["by"] == user.id for q in self._lp_rq.values()):
            return
        ql = self._lp_qlog.setdefault(user.id, deque(maxlen=20))
        while ql and now - ql[0] > 600:
            ql.popleft()
        if len(ql) >= 6:
            return
        for k in [k for k, q in self._lp_rq.items() if now - q["t"] > LP_CACHE_TTL]:
            self._lp_rq.pop(k, None)
        self._lp_rqn += 1
        token = format(self._lp_rqn, "x")
        st = self.store.chats.get(chat.id)
        snip = esc(ent.get("snip", ""), 220)
        text = (f"👀 Вы поставили {esc(emoji)} на сообщение в «{esc(st.title if st else '', 40)}»:\n"
                f"{esc(ent.get('name') or 'участник', 40)}: <i>«{snip}»</i>\n\n"
                "Это вы по приколу или считать, что такие сообщения в чате нельзя? Если нельзя — удалю это и буду ловить похожие.")
        sent = await self.call("send_message", user.id, text[:4000], reply_markup=self.lp_ask_kb(token, act), disable_notification=True)
        if sent is not None:
            ql.append(now)
            self._lp_rq[token] = {"cid": chat.id, "mid": mid, "act": act, "by": user.id, "t": now}

    @staticmethod
    def lp_ask_kb(token: str, act: str):
        from aiogram.types import InlineKeyboardButton as Btn, InlineKeyboardMarkup
        return InlineKeyboardMarkup(inline_keyboard=[
            [Btn(text="🚫🔨 Спам, забанить" if act == "sb" else "🚫 Да, это спам", callback_data=f"lr:{token}:y"),
             Btn(text="😄 По приколу", callback_data=f"lr:{token}:n")],
            [Btn(text="🔕 Не спрашивать, учись сразу", callback_data=f"lr:{token}:a")],
            [Btn(text="🤷 Эмоции ничего не значат", callback_data=f"lr:{token}:o")]])

    async def on_callback(self, cb) -> None:
        data = getattr(cb, "data", "") or ""
        if data.startswith("lr:"):
            try:
                return await self.lp_callback(cb)
            except asyncio.CancelledError:
                raise
            except Exception:
                log_learn.exception("самообучение+: кнопка вопроса про реакцию упала")
            return await cb.answer()
        return await super().on_callback(cb)

    async def lp_callback(self, cb) -> None:
        parts = (getattr(cb, "data", "") or "").split(":")
        user = cb.from_user
        if len(parts) != 3 or user.id not in self.owners:
            return await cb.answer("Только для владельца." if len(parts) == 3 else "")
        _, token, a = parts
        msg = getattr(cb, "message", None)

        async def edit(text: str) -> None:
            if msg is not None:
                await self.call("edit_message_text", text, chat_id=msg.chat.id, message_id=msg.message_id)

        q = self._lp_rq.pop(token, None)
        if a == "o":
            self.eng.lp_set_rxmode(user.id, "off")
            await edit("🤷 Понял: ваши реакции в чате ничего не значат, больше не спрашиваю. Вернуть: /learn react ask")
            return await cb.answer("Реакции отключены.")
        if a == "a":
            self.eng.lp_set_rxmode(user.id, "auto")
        if q is None or q["by"] != user.id:
            if a == "a":
                await edit("🔕 Ок, дальше учусь по вашим реакциям сразу, без вопросов (вернуть вопросы: /learn react ask). "
                           "Это сообщение уже не помню — ответьте на него /spam, если нужно.")
                return await cb.answer("Готово.")
            await edit("Это сообщение я уже не помню. Ответьте на него командой /spam, если это спам.")
            return await cb.answer()
        if a == "n":
            await edit("😄 Ок, по приколу — ничему не учусь.")
            return await cb.answer("Не учу.")
        now = self.now()
        res = self.eng.lp_teach(q["cid"], q["mid"], q["act"], user.id, "react", now)
        if not res["ok"]:
            await edit({"dup": "Это сообщение я уже разобрал.", "limit": "Слишком много уроков за 10 минут — подождите."}.get(
                res["why"], "Не получилось: сообщение уже не помню. Ответьте на него командой /spam."))
            return await cb.answer()
        if msg is not None:
            res["cards"]["own"][str(user.id)] = msg.message_id
        await self.lp_finish(res, q["act"], user, "реакция" + (", дальше без вопросов" if a == "a" else ""))
        await cb.answer("Запомнил." + (" Дальше учусь по реакциям сразу." if a == "a" else ""))

    # ───────── /spam ответом на сообщение
    async def cmd_spam(self, m, args):
        if not await self.need_admin(m):
            return
        self.cleanup(m)
        r = getattr(m, "reply_to_message", None)
        if r is None or not self.eng.lp_on or not self.eng.learn_on:
            return await self.out(m, "Ответьте командой /spam на спам-сообщение (/spam ban — ещё и забанить автора).", ttl=15)
        tu = getattr(r, "from_user", None)
        if tu is None or tu.is_bot or tu.id in self.owners or self.is_trusted(tu.id) or tu.id in await self.admins(m.chat.id):
            return await self.out(m, "Это сообщение бота, владельца или администратора — на нём не учусь.", ttl=10)
        cid, now = m.chat.id, self.now()
        if (cid, r.message_id) not in self.eng._lpc:
            msg = to_msg(r, uid=tu.id, name=user_name(tu))
            if len(msg.text.strip()) < 5:
                return await self.out(m, "В сообщении нет текста, учиться не на чем.", ttl=10)
            rec = self.store.chat(cid).users.get(tu.id)
            self.eng.lp_entry_from_text(cid, r.message_id, tu.id, msg.text, msg.ents, now, self._lp_tier(rec, now))
        act = "sb" if re.search(r"(?:^|\s)(?:ban|бан)", (args or "").lower()) else "s"
        res = self.eng.lp_teach(cid, r.message_id, act, m.from_user.id, "cmd", now)
        if not res["ok"]:
            why = {"dup": "Это сообщение я уже разобрал.", "empty": "Слишком мало текста для отпечатка.",
                   "limit": "Слишком много уроков за 10 минут — подождите."}.get(res["why"], "Не получилось выучить это сообщение.")
            return await self.out(m, why, ttl=10)
        await self.lp_finish(res, act, m.from_user, "/spam")
        if not self.store.chat(cid).cfg.quiet:
            await self.out(m, "🧠 Запомнил как спам, сообщение удалено.", ttl=8)

    # ───────── баны владельца → уроки
    async def lp_after_ban(self, m, uid: int) -> None:
        try:
            if not (self.eng.lp_on and self.eng.learn_on):
                return
            cid, now = m.chat.id, self.now()
            r = getattr(m, "reply_to_message", None)
            ru = getattr(r, "from_user", None) if r is not None else None
            if ru is not None and ru.id == uid and (cid, r.message_id) not in self.eng._lpc:
                msg = to_msg(r, uid=uid, name=user_name(ru))
                if len(msg.text.strip()) >= 5:
                    rec = self.store.chat(cid).users.get(uid)
                    self.eng.lp_entry_from_text(cid, r.message_id, uid, msg.text, msg.ents, now, self._lp_tier(rec, now))
            res = self.eng.lp_implicit(cid, uid, m.from_user.id, "ban", now)
            if res.get("ok"):
                await self.lp_finish(res, "s", m.from_user, "ваш бан")
        except asyncio.CancelledError:
            raise
        except Exception:
            log_learn.exception("самообучение+: урок из бана не получился")

    async def lp_member_event(self, ev, old: str, new: str) -> None:
        try:
            by = getattr(ev, "from_user", None)
            if by is None or by.id not in self.owners or by.id == self.me_id or not self.eng.lp_on:
                return
            uid, cid, now = ev.new_chat_member.user.id, ev.chat.id, self.now()
            if new == "kicked" and old in ("member", "restricted") and self.eng.learn_on:
                res = self.eng.lp_implicit(cid, uid, by.id, "uiban", now)
                if res.get("ok"):
                    await self.lp_finish(res, "s", by, "бан из меню Telegram")
            elif (old == "kicked" and new in ("left", "member")) or (old == "restricted" and new == "member"):
                self.eng.note_overturn(cid, uid)
        except asyncio.CancelledError:
            raise
        except Exception:
            log_learn.exception("самообучение+: событие участника не обработано")

    async def cmd_learn(self, m, args):
        u = getattr(m, "from_user", None)
        if u is None or u.id not in self.owners:
            return
        grp = self.in_group(m)
        w = (args or "").strip().lower().split()
        if w and w[0] in ("react", "реакции", "реакция"):
            mode = {"ask": "ask", "спрашивать": "ask", "auto": "auto", "сразу": "auto", "off": "off", "выкл": "off", "ничего": "off"}.get(w[1] if len(w) > 1 else "")
            if mode:
                self.eng.lp_set_rxmode(u.id, mode)
                txt = {"ask": "Реакции: спрашиваю в личке, учить ли.", "auto": "Реакции: учусь сразу, без вопросов.",
                       "off": "Реакции в чате ничего не значат."}[mode]
            else:
                txt = "Режим реакций: /learn react ask (спрашивать), auto (учиться сразу) или off (ничего не значат)."
            return await self.out(m, txt, ttl=15 if grp else 0)
        await self.out(m, self.eng.lp_status(m.chat.id if grp else None, self.now(), u.id), ttl=90 if grp else 0)
        if grp:
            self.cleanup(m)


class Deleter:

    DELAY = 0.12

    def __init__(self, guard: "Guard"):
        self.g = guard
        self.pending: dict[int, set] = defaultdict(set)
        self._task: asyncio.Task | None = None

    def add(self, chat_id: int, ids) -> None:
        self.pending[chat_id].update(int(i) for i in ids)
        if self._task is None or self._task.done():
            self._task = asyncio.get_running_loop().create_task(self._run())

    async def _run(self) -> None:
        await asyncio.sleep(self.DELAY)
        while self.pending:
            batch = dict(self.pending)
            self.pending.clear()
            await asyncio.gather(*(self._chat(c, i) for c, i in batch.items()), return_exceptions=True)

    async def _chat(self, chat_id: int, ids) -> None:
        ids = sorted(ids)
        for i in range(0, len(ids), 100):
            chunk = ids[i:i + 100]
            if len(chunk) == 1:
                await self.g.call("delete_message", chat_id, chunk[0])
                continue
            if await self.g.call("delete_messages", chat_id, chunk) is None:
                for mid in chunk:
                    await self.g.call("delete_message", chat_id, mid)

    async def flush(self) -> None:
        while self._task is not None and not self._task.done():
            await self._task


class Guard(LearnTG, Commands, Extras, Gatekeeper, AdminPanel, Plus, Plus2, Strict, Fortress, Tracker, Autopilot, LearnUI):
    def __init__(self, bot, store: Store, engine: Engine, voice: Voice | None = None):
        self.bot = bot
        self.store = store
        self.eng = engine
        self.voice = voice or Voice()
        self.me_id = 0
        self.username = ""
        self.deleter = Deleter(self)
        self._admins: dict[int, tuple] = {}
        self._rights: dict[int, tuple] = {}
        self._defperms: dict[int, tuple] = {}
        self._notice_last: dict[tuple, float] = {}
        self._joined: dict[tuple, float] = {}
        self._tasks: set = set()
        self._stop = asyncio.Event()
        self.reports: dict[tuple, dict] = {}
        self.report_rate: dict[int, list] = {}
        self._last_tick = {"prune": 0.0, "store": 0.0}
        Extras.init_extras(self)
        Plus.init_plus(self)
        Plus2.init_plus2(self)
        Strict.init_strict(self)
        Fortress.init_fort_ui(self)
        Autopilot.init_ap_ui(self)
        LearnTG.init_learn_tg(self)
        Commands.__init__(self)

    def now(self) -> float:
        return time.time()

    def later(self, delay: float, fn, *args, **kw) -> None:
        async def run():
            try:
                await asyncio.sleep(delay)
                await fn(*args, **kw)
            except asyncio.CancelledError:
                raise
            except Exception:
                log.exception("отложенное действие не удалось")
        t = asyncio.get_running_loop().create_task(run())
        self._tasks.add(t)
        t.add_done_callback(self._tasks.discard)

    async def start(self) -> None:
        me = await self.bot.get_me()
        self.me_id, self.username = me.id, (me.username or "")
        if self.username:
            self.eng.mem_protect.add("@" + self.username.lower())
        self.eng.rings.load(self.store.rings)
        log.info("Бот запущен: @%s (%s), колец восстановлено: %d", self.username, self.me_id, len(self.eng.rings.rings))

    async def call(self, method: str, *a, **kw):
        for attempt in range(3):
            try:
                return await getattr(self.bot, method)(*a, **kw)
            except TelegramRetryAfter as e:
                await asyncio.sleep(min(float(getattr(e, "retry_after", 1)), 30.0) + 0.2)
            except (TelegramBadRequest, TelegramForbiddenError) as e:
                log.debug("%s: %s", method, e)
                return None
            except (TelegramNetworkError, TelegramServerError) as e:
                log.warning("%s: сеть/сервер (%s), попытка %d", method, e, attempt + 1)
                await asyncio.sleep(0.6 * (attempt + 1))
            except TelegramAPIError as e:
                log.warning("%s: %s", method, e)
                return None
        return None

    async def _once(self, key, factory):
        inflight = self.__dict__.setdefault("_inflight", {})
        t = inflight.get(key)
        if t is None:
            t = inflight[key] = asyncio.ensure_future(factory())
            t.add_done_callback(lambda _f, k=key: inflight.pop(k, None))
        return await asyncio.shield(t)

    async def admins(self, chat_id: int) -> set:
        hit = self._admins.get(chat_id)
        now = self.now()
        if hit and now - hit[0] < 300:
            return hit[1]
        res = await self._once(("adm", chat_id), lambda: self.call("get_chat_administrators", chat_id))
        if res is None:
            return hit[1] if hit else set()
        ids = {m.user.id for m in res}
        self._admins[chat_id] = (now, ids)
        return ids

    async def is_admin(self, chat_id: int, uid: int) -> bool:
        return uid in self.owners

    def is_trusted(self, uid: int) -> bool:
        return uid in self.owners or uid in self.trusted

    async def rights(self, chat_id: int) -> dict:
        hit = self._rights.get(chat_id)
        now = self.now()
        if hit and now - hit[0] < 300:
            return hit[1]
        m = await self._once(("rt", chat_id), lambda: self.call("get_chat_member", chat_id, self.me_id))
        r = {"admin": False, "delete": False, "restrict": False}
        if m is not None:
            st = status_of(m)
            if st == "creator":
                r = {"admin": True, "delete": True, "restrict": True}
            elif st == "administrator":
                r = {"admin": True, "delete": bool(getattr(m, "can_delete_messages", False)),
                     "restrict": bool(getattr(m, "can_restrict_members", False))}
            self._rights[chat_id] = (now, r)
        elif hit:
            self._rights[chat_id] = (now - 285, hit[1])
            return hit[1]
        else:
            self._rights[chat_id] = (now - 285, r)
        return r

    async def default_permissions(self, chat_id: int):
        hit = self._defperms.get(chat_id)
        now = self.now()
        if hit and now - hit[0] < 600:
            return hit[1]
        chat = await self._once(("gc", chat_id), lambda: self.call("get_chat", chat_id))
        perms = getattr(chat, "permissions", None) if chat is not None else None
        perms = perms or open_permissions()
        self._defperms[chat_id] = (now, perms)
        return perms

    async def restrict(self, chat_id: int, uid: int, seconds: float | None):
        kw = {}
        if seconds is not None:
            kw["until_date"] = int(self.now() + max(35, seconds))
        return await self.call("restrict_chat_member", chat_id, uid, permissions=no_permissions(), **kw)

    async def unrestrict(self, chat_id: int, uid: int):
        return await self.call("restrict_chat_member", chat_id, uid, permissions=await self.default_permissions(chat_id))

    async def kick(self, chat_id: int, uid: int, seconds: int = 90):
        return await self.call("ban_chat_member", chat_id, uid, until_date=int(self.now() + max(40, seconds)))

    async def notice(self, chat_id: int, key: str, ttl: float = 30, cooldown: float = 0, cd_key=None, thread=None, **kw):
        now = self.now()
        if cooldown:
            k = (chat_id, cd_key or key)
            if now - self._notice_last.get(k, 0) < cooldown:
                return None
            self._notice_last[k] = now
        text = self.voice.say(key, **kw)
        if not text:
            return None
        extra = {"message_thread_id": thread} if thread else {}
        sent = await self.call("send_message", chat_id, text, disable_notification=True, **extra)
        if sent is not None and ttl:
            self.later(ttl, self.call, "delete_message", chat_id, sent.message_id)
        return sent

    async def alert(self, chat_id: int, text: str, markup=None) -> int:
        sent = 0
        for uid in sorted(self.store.alert_users & self.owners):
            if await self.call("send_message", uid, text, reply_markup=markup) is not None:
                sent += 1
        return sent

    def ring_names(self, chat_id: int) -> str:
        names = []
        for r in self.eng.rings.active(chat_id, self.now()):
            names += [n for n in r.names if n and n not in names]
        names = [esc(n, 24) for n in names[:4]]
        if not names:
            return "участники"
        return names[0] if len(names) == 1 else ", ".join(names[:-1]) + " и " + names[-1]

    async def on_message(self, m) -> bool:
        chat = m.chat
        if getattr(chat, "type", "") == "private":
            try:
                return await self.learn_private(m)
            except asyncio.CancelledError:
                raise
            except Exception:
                log_learn.exception("самообучение: пересылка в личку не обработана")
                return False
        if getattr(chat, "type", "") not in GROUP_TYPES:
            return False
        ct = str(getattr(getattr(m, "content_type", ""), "value", getattr(m, "content_type", "")))
        if getattr(m, "migrate_to_chat_id", None):
            self.migrate_chat(chat.id, m.migrate_to_chat_id)
            return False
        if not self.chat_ok(chat.id):
            return False
        state = self.store.chat(chat.id, chat.title or "")
        cfg = state.cfg
        if not state.active:
            state.active = True
            self.store.dirty = True

        if getattr(m, "new_chat_members", None):
            for u in m.new_chat_members:
                await self.on_join(chat, u, join_msg_id=m.message_id)
            if cfg.clean_joins and cfg.enabled and (await self.rights(chat.id))["delete"]:
                self.deleter.add(chat.id, [m.message_id])
                return True
            return False
        if getattr(m, "left_chat_member", None):
            await self.on_leave(chat, m.left_chat_member.id)
            if cfg.clean_joins and cfg.enabled and (await self.rights(chat.id))["delete"]:
                self.deleter.add(chat.id, [m.message_id])
                return True
            return False
        if getattr(m, "is_automatic_forward", None) or ct in ("pinned_message", "new_chat_title", "new_chat_photo",
                                                               "delete_chat_photo", "forum_topic_created"):
            if getattr(m, "is_automatic_forward", None):
                self.eng.trace_post(chat.id, m.message_id, self.now())
            return False

        u = getattr(m, "from_user", None)
        sc = getattr(m, "sender_chat", None)
        if u is None and sc is None:
            return False
        anonymous = bool(sc and sc.id == chat.id) or (u is not None and u.id == ANON_ADMIN_ID)
        as_channel = bool(sc and sc.id != chat.id)
        if u is not None and u.is_bot and not anonymous and not as_channel:
            return False
        uid = sc.id if as_channel else (u.id if u is not None else 0)
        name = (sc.title if as_channel else user_name(u)) or ""
        rights = await self.rights(chat.id)
        if not rights["admin"]:
            return False
        if uid in self.banned_env and uid > 0 and not as_channel and not anonymous and uid not in self.owners:
            if rights["delete"]:
                self.deleter.add(chat.id, [m.message_id])
            if rights["restrict"]:
                await self.call("ban_chat_member", chat.id, uid, revoke_messages=True)
            self.journal("banned_env", chat.id, chat.title or "", uid, name, "id из GUARD_BANNED_IDS: бан")
            return True
        exempt = anonymous or (not as_channel and (self.is_trusted(uid) or (
            self.trust_tg_admins and uid in await self.admins(chat.id))))
        if exempt:
            self.eng.ap_admin_seen(chat.id, self.now())

        if not exempt and cfg.enabled:
            try:
                if await self.plus_gate(m, chat, state, uid, name, as_channel, rights):
                    return True
            except asyncio.CancelledError:
                raise
            except Exception:
                log.exception("расширения: сбой при проверке сообщения")

        msg = to_msg(m, edited=bool(getattr(m, "edit_date", None)), uid=uid, name=name)
        rec0 = state.users.get(uid)
        prev = (rec0.muted_until, rec0.banned) if rec0 is not None else (0.0, False)
        v = self.eng.check(msg, is_admin=exempt, now=msg.ts)
        if v.info.get("learn_card"):
            self.later(0, self.learn_offer, m, msg, v)
        if self.eng.events:
            await self.handle_events()
        if (v.ban or v.mute_s) and not as_channel and uid > 0 and uid in await self.admins(chat.id):
            v.ban, v.mute_s, v.delete, v.alert, v.notice = False, 0, True, True, ""
            rec1 = state.users.get(uid)
            if rec1 is not None:
                rec1.muted_until, rec1.banned = prev
            v.reasons = list(v.reasons) + ["автор — админ чата: наказать не могу, только удалил"]
        if v.delete or v.ban or v.mute_s:
            await self.apply(m, msg, v, name, rights)
            return bool(v.delete)

        try:
            await self.after_message(m, msg, state, uid, name, human=not anonymous and not as_channel)
        except Exception:
            log.exception("обработка заметок: сбой")
        return False

    async def apply(self, m, msg: Msg, v: Verdict, name: str, rights: dict) -> None:
        delay = v.info.get("delay", 0)
        if delay:
            v.info = {**v.info, "delay": 0}
            self.later(delay, self.apply, m, msg, v, name, rights)
            return
        chat_id, uid = msg.chat_id, msg.user_id
        cfg = self.store.chat(chat_id).cfg
        thread = getattr(m, "message_thread_id", None) if getattr(m, "is_topic_message", False) else None
        ids = [msg.msg_id]
        if v.purge:
            ids += self.eng.recent_ids(chat_id, uid, within=1800, now=msg.ts)
        elif v.purge_s:
            ids += self.eng.recent_ids(chat_id, uid, within=v.purge_s, now=msg.ts)
        if v.delete and rights["delete"]:
            self.deleter.add(chat_id, ids)
        elif v.delete:
            await self.notice(chat_id, "need_rights", ttl=60, cooldown=3600)

        who = mention(uid, name)
        if rights["restrict"]:
            if v.ban:
                if msg.sender_chat:
                    await self.call("ban_chat_sender_chat", chat_id, uid)
                else:
                    await self.call("ban_chat_member", chat_id, uid, revoke_messages=True)
            elif v.mute_s and not msg.sender_chat:
                await self.restrict(chat_id, uid, v.mute_s)
        log.info("chat=%s user=%s %s score=%s strike=%s mute=%s ban=%s: %s", chat_id, uid, v.category, v.score,
                 v.strike, v.mute_s, v.ban, v.why())
        if v.others:
            await self.puppet_others(m, chat_id, v.others, rights)

        if v.notice and not cfg.quiet:
            kw: dict = {}
            ttl = NOTICE_TTL.get(v.notice, 30)
            cooldown, cd_key = 0.0, None
            if v.notice in ("ring_hush", "lock_hush"):
                cooldown = 40.0
                kw["names"] = self.ring_names(chat_id)
            elif v.notice == "slow":
                cooldown, cd_key = 20.0, ("slow", uid)
                kw.update(name=who, s=v.info.get("s", 1))
            elif v.notice in ("mute", "hacked"):
                kw.update(name=who, dur=human_dur(v.mute_s))
            elif v.notice in ("warn", "ban_spam", "ring_mute"):
                kw["name"] = who
            await self.notice(chat_id, v.notice, ttl=ttl, cooldown=cooldown, cd_key=cd_key, thread=thread, **kw)

        if v.alert:
            link = msg_link(m.chat, msg.msg_id)
            lines = [f"🚨 <b>{esc(m.chat.title, 60)}</b>", f"Участник: {who} (<code>{uid}</code>)",
                     f"Причина: {esc(v.why(), 200)}"]
            action = "бан и стирание сообщений" if v.ban else f"запись ограничена на {human_dur(v.mute_s)}" if v.mute_s else "сообщение удалено"
            lines.append(f"Что сделал: {action}")
            if v.category == "scam" and (v.ban or v.info.get("puppet")):
                cl = await self._contacts_text(chat_id, uid, exclude={o["uid"] for o in v.others})
                if cl:
                    lines.append(cl)
            if v.info.get("puppet"):
                who_all = ", ".join(mention(o["uid"]) for o in v.others)
                lines.append("Постановочный диалог: вопрос → питч → подтверждение от подставных аккаунтов."
                             + (f" Вместе с ним: {who_all}." if who_all else ""))
            elif v.category == "scam" and not v.ban:
                lines.append("Вероятна компрометация аккаунта. Если это ошибка — /forgive ответом на сообщение участника.")
            await self.alert(chat_id, "\n".join(lines))

        if v.ban or v.mute_s:
            what = "бан" if v.ban else f"запись ограничена на {human_dur(v.mute_s)}"
            await self.plus_log(chat_id, f"🛡 <b>{esc(m.chat.title, 60)}</b>\n{who} (<code>{uid}</code>): {what}\n"
                                         f"Причина: {esc(v.why(), 160)}")
        if v.strict_started:
            await self.strict_announce(m.chat, auto=True, why=v.why())

    async def puppet_others(self, m, chat_id: int, others: list, rights: dict) -> None:
        admins = await self.admins(chat_id)
        for o in others:
            uid = o["uid"]
            if uid in admins or self.is_trusted(uid):
                self.eng.forgive(chat_id, uid)
                continue
            if o["ids"] and rights["delete"]:
                self.deleter.add(chat_id, o["ids"])
            if rights["restrict"]:
                if o["ban"]:
                    await self.call("ban_chat_member", chat_id, uid, revoke_messages=True)
                    await self.invite_bad(chat_id, uid)
                elif o["mute_s"]:
                    await self.restrict(chat_id, uid, o["mute_s"])
            what = "бан" if o["ban"] else f"запись ограничена на {human_dur(o['mute_s'])}"
            role = "питч" if o["role"] == "pitch" else "подтверждение"
            await self.plus_log(chat_id, f"🛡 <b>{esc(m.chat.title, 60)}</b>\n{mention(uid)} (<code>{uid}</code>): {what}\n"
                                         f"Причина: постановочный диалог ({role})")

    async def on_join(self, chat, user, join_msg_id: int | None = None) -> None:
        if getattr(user, "is_bot", False) or not self.chat_ok(chat.id):
            return
        now = self.now()
        key = (chat.id, user.id)
        if now - self._joined.get(key, 0) < 60:
            return
        self._joined[key] = now
        state = self.store.chat(chat.id, chat.title or "")
        cfg = state.cfg
        if not cfg.enabled:
            return
        if user.id in self.banned_env and user.id not in self.owners:
            if (await self.rights(chat.id))["restrict"]:
                await self.call("ban_chat_member", chat.id, user.id, revoke_messages=True)
                self.journal("banned_env", chat.id, chat.title or "", user.id, user_name(user), "id из GUARD_BANNED_IDS: бан при входе")
            return
        if await self.plus_screen(chat, user.id, user_name(user)):
            return
        if await self.plus_join_checks(chat, user):
            return
        rec = self.store.user(state, user.id, now)
        rec.joined, rec.last_seen = now, now
        self.store.dirty = True
        res = self.eng.note_join(chat.id, now)
        if res in ("raid_on", "raid_extend"):
            await self.fort_feed(chat.id, 0, "raid" if res == "raid_on" else "raid_more")
        if res == "raid_on" and not cfg.quiet:
            await self.notice(chat.id, "raid_on", ttl=300, mins=human_dur(RAID_HOLD))
            await self.alert(chat.id, f"🚨 <b>{esc(chat.title, 60)}</b>\nНаплыв новичков: включил усиленную проверку на "
                                      f"{human_dur(RAID_HOLD)}.")
        if rec.verified or rec.vouched or not (cfg.captcha or self.eng.raid_active(chat.id, now)
                                               or self.eng.strict_active(chat.id, now)):
            await self.greet(chat.id, user.id, user_name(user))
            return
        if self.is_trusted(user.id) or user.id in await self.admins(chat.id):
            return
        if not (await self.rights(chat.id))["restrict"]:
            await self.notice(chat.id, "need_rights", ttl=60, cooldown=3600)
            return
        plan = self.captcha_plan(chat, user, state, now)
        if plan["skip"]:
            rec.verified = True
            self.store.bump(state, "captcha_skip")
            await self.greet(chat.id, user.id, user_name(user))
            return
        if plan["level"] == "hard":
            log.info("chat=%s user=%s: усложнённая капча (%s)", chat.id, user.id, "; ".join(plan["why"]))
        await self.start_captcha(chat, user, join_msg_id, plan)

    async def on_leave(self, chat, uid: int) -> None:
        e = self.store.captchas.pop(f"{chat.id}:{uid}", None)
        if e:
            self.deleter.add(chat.id, [i for i in (e.get("msg_id"), e.get("join_msg")) if i])
            self.store.dirty = True

    def migrate_chat(self, old: int, new: int) -> None:
        allowed = self.store.meta.get("allowed")
        if allowed is not None and old in allowed and int(new) not in allowed:
            allowed.append(int(new))
        if old in self.allowed_env:
            self.allowed_env.add(int(new))
        st = self.store.chats.pop(old, None)
        if st is not None:
            st.chat_id = int(new)
            self.store.chats[int(new)] = st
        for r in self.eng.rings.rings.values():
            if r.chat_id == old:
                r.chat_id = int(new)
        self.store.rings = self.eng.rings.dump()
        self.store.dirty = True

    @staticmethod
    def _captcha_rows(chat_id: int, uid: int, cap: dict) -> list:
        from aiogram.types import InlineKeyboardButton
        cols = max(1, int(cap.get("cols") or len(cap["options"])))
        btns = [InlineKeyboardButton(text=o, callback_data=f"cp:{chat_id}:{uid}:{i}") for i, o in enumerate(cap["options"])]
        return [btns[i:i + cols] for i in range(0, len(btns), cols)]

    async def start_captcha(self, chat, user, join_msg_id=None, plan: dict | None = None) -> None:
        from aiogram.types import InlineKeyboardMarkup
        cfg = self.store.chat(chat.id).cfg
        level = (plan or {}).get("level")
        cap = make_captcha(self.eng.rng, level)
        tmo = min(cfg.captcha_timeout, 45) if level == "hard" else cfg.captcha_timeout
        if await self.restrict(chat.id, user.id, None) is None:
            return
        kb = InlineKeyboardMarkup(inline_keyboard=self._captcha_rows(chat.id, user.id, cap))
        text = self.voice.say("captcha_prompt", name=mention(user.id, user_name(user)), q=esc(cap["q"], 80), sec=tmo)
        sent = await self.call("send_message", chat.id, text, reply_markup=kb, disable_notification=True)
        if sent is None:
            await self.unrestrict(chat.id, user.id)
            return
        now = self.now()
        self.store.captchas[f"{chat.id}:{user.id}"] = {
            "chat": chat.id, "user": user.id, "name": user_name(user)[:40], "answer": cap["answer"], "tries": 0,
            "deadline": now + tmo, "msg_id": sent.message_id, "join_msg": join_msg_id or 0,
            "level": level, "t0": now, "max_tries": 1 if level == "hard" else 2}
        self.store.dirty = True

    async def captcha_pass(self, entry: dict) -> bool:
        chat_id, uid = entry["chat"], entry["user"]
        self.store.captchas.pop(f"{chat_id}:{uid}", None)
        state = self.store.chat(chat_id)
        rec = self.store.user(state, uid, self.now())
        rec.verified = True
        self.store.bump(state, "captcha_ok")
        ok = await self.unrestrict(chat_id, uid) is not None
        self.deleter.add(chat_id, [entry["msg_id"]])
        if ok and not state.cfg.quiet:
            await self.notice(chat_id, "captcha_ok", ttl=20, name=mention(uid, entry.get("name", "")))
        if ok:
            await self.greet(chat_id, uid, entry.get("name", ""))
        self.store.dirty = True
        return ok

    async def captcha_fail(self, entry: dict, timeout: bool = False) -> None:
        chat_id, uid = entry["chat"], entry["user"]
        self.store.captchas.pop(f"{chat_id}:{uid}", None)
        state = self.store.chat(chat_id)
        self.store.bump(state, "captcha_fail")
        mins = self.captcha_ban_minutes(state.cfg)
        await self.kick(chat_id, uid, seconds=mins * 60)
        self.note_capfail(uid, self.now())
        await self.fort_feed(chat_id, uid, "capfail")
        self.journal("capfail", chat_id, state.title or "", uid, entry.get("name", ""),
                     ("не ответил" if timeout else "не прошёл") + f": убран на {mins} мин")
        self.deleter.add(chat_id, [i for i in (entry.get("msg_id"), entry.get("join_msg")) if i])
        if not state.cfg.quiet:
            await self.notice(chat_id, "captcha_timeout" if timeout else "captcha_fail", ttl=30,
                              name=mention(uid, entry.get("name", "")), mins=human_dur(mins * 60))
        self.store.dirty = True

    async def on_captcha_button(self, cb) -> None:
        from aiogram.types import InlineKeyboardMarkup
        try:
            _, cid, uid, idx = cb.data.split(":")
            cid, uid, idx = int(cid), int(uid), int(idx)
        except (ValueError, AttributeError):
            return await cb.answer()
        if cb.from_user.id != uid:
            return await cb.answer("Проверка предназначена другому участнику.", show_alert=False)
        entry = self.store.captchas.get(f"{cid}:{uid}")
        if not entry:
            return await cb.answer("Проверка недействительна.", show_alert=False)
        now = self.now()
        too_fast = bool(self.captcha_min_react) and now - entry.get("t0", 0) < self.captcha_min_react
        if idx == entry["answer"] and not too_fast:
            if await self.captcha_pass(entry):
                return await cb.answer("Проверка пройдена.")
            return await cb.answer("Не удалось снять ограничение. Обратитесь к администратору.", show_alert=True)
        entry["tries"] += 1
        if entry["tries"] >= entry.get("max_tries", 2):
            await cb.answer("Неверно.", show_alert=False)
            return await self.captcha_fail(entry)
        cap = make_captcha(self.eng.rng, entry.get("level"))
        entry["answer"], entry["t0"] = cap["answer"], now
        kb = InlineKeyboardMarkup(inline_keyboard=self._captcha_rows(cid, uid, cap))
        text = self.voice.say("captcha_prompt", name=mention(uid, entry.get("name", "")), q=esc(cap["q"], 80),
                              sec=max(10, int(entry["deadline"] - now)))
        await self.call("edit_message_text", text, chat_id=cid, message_id=entry["msg_id"], reply_markup=kb)
        self.store.dirty = True
        await cb.answer("Неверно. Вопрос заменён, осталась последняя попытка.", show_alert=False)

    async def on_chat_member(self, ev) -> None:
        chat = ev.chat
        if getattr(chat, "type", "") not in GROUP_TYPES or not self.chat_ok(chat.id):
            return
        old, new = status_of(ev.old_chat_member), status_of(ev.new_chat_member)
        user = ev.new_chat_member.user
        await self.lp_member_event(ev, old, new)
        if old in ("administrator", "creator") or new in ("administrator", "creator"):
            self._admins.pop(chat.id, None)
        if old in ("left", "kicked") and new in ("member", "restricted") and getattr(ev.new_chat_member, "is_member", True):
            await self.on_join(chat, user)
            self.invite_note(chat.id, user.id, getattr(ev, "invite_link", None))
        elif new in ("left", "kicked"):
            await self.on_leave(chat, user.id)

    async def on_my_chat_member(self, ev) -> None:
        chat = ev.chat
        old, new = status_of(ev.old_chat_member), status_of(ev.new_chat_member)
        if getattr(chat, "type", "") == "private":
            if new == "kicked":
                self.store.alert_users.discard(ev.from_user.id)
                self.store.dirty = True
            return
        if getattr(chat, "type", "") not in GROUP_TYPES:
            return
        self._rights.pop(chat.id, None)
        self._admins.pop(chat.id, None)
        if new in ("left", "kicked"):
            st = self.store.chats.get(chat.id)
            if st is not None:
                st.active = False
                self.store.dirty = True
            self.eng.ring_end_chat(chat.id)
            await self.on_bot_removed(ev)
            return
        if old in ("left", "kicked") and new in ("member", "administrator", "restricted"):
            if await self.on_bot_added(ev):
                return
        elif not self.chat_ok(chat.id):
            return
        state = self.store.chat(chat.id, chat.title or "")
        state.active = True
        self.store.dirty = True
        can = bool(getattr(ev.new_chat_member, "can_delete_messages", False)) and bool(
            getattr(ev.new_chat_member, "can_restrict_members", False))
        was_admin = old in ("administrator", "creator")
        if new in ("administrator", "creator"):
            if can and not was_admin:
                await self.notice(chat.id, "added_ok", ttl=0)
            elif not can:
                await self.notice(chat.id, "added_no_rights", ttl=0, cooldown=600)
        elif was_admin:
            await self.notice(chat.id, "rights_lost", ttl=0, cooldown=600)
        elif old in ("left", "kicked"):
            await self.notice(chat.id, "added_no_rights", ttl=0)
        _ = state

    async def on_hook(self, p: dict) -> dict:
        action = str(p.get("action", ""))
        key = str(p.get("key", ""))[:64]
        if not key:
            return {"ok": False, "error": "key required"}
        try:
            if action in ("start", "touch"):
                ttl = float(p.get("ttl", RING_TTL_DEFAULT))
                if action == "touch" and self.eng.ring_touch(key, ttl, now=self.now()):
                    return {"ok": True, "touched": True}
                if action == "touch" and not (p.get("chat_id") and p.get("fighters")):
                    return {"ok": False, "error": "no_such_ring"}
                chat_id = int(p["chat_id"])
                mode = str(p.get("mode", "group"))
                fighters = [int(f) for f in p["fighters"]]
                if mode not in ("group", "arena"):
                    return {"ok": False, "error": "mode must be group or arena"}
                if not 1 <= len(fighters) <= 6:
                    return {"ok": False, "error": "fighters: 1..6 ids"}
                if chat_id not in self.store.chats or not self.chat_ok(chat_id):
                    return {"ok": False, "error": "unknown_chat"}
                names = [str(n)[:40] for n in (p.get("names") or [])][:6]
                self.eng.ring_start(chat_id, key, mode, fighters, names, ttl, now=self.now())
                return {"ok": True, "started": True}
            if action == "end":
                r = self.eng.ring_end(key)
                return {"ok": True, "ended": r is not None}
        except (KeyError, TypeError, ValueError):
            return {"ok": False, "error": "bad payload"}
        return {"ok": False, "error": "unknown action"}

    async def tick(self, now: float | None = None) -> None:
        now = self.now() if now is None else now
        for r in self.eng.ring_expire(now):
            log.info("кольцо %s истекло (игра не сообщила об окончании)", r.key)
            cfg = self.store.chat(r.chat_id).cfg
            if r.mode in ("manual", "lockdown") and not cfg.quiet:
                await self.notice(r.chat_id, "lockdown_off" if r.mode == "lockdown" else "ring_end", ttl=60)
        for cid in self.eng.pop_raid_ended(now):
            cfg = self.store.chat(cid).cfg
            if cfg.raid and not cfg.quiet:
                await self.notice(cid, "raid_off", ttl=120)
        for key, e in list(self.store.captchas.items()):
            if e.get("deadline", 0) <= now:
                await self.captcha_fail(e, timeout=True)
        await self.fire_reminders(now)
        await self.poll_tick(now)
        await self.plus_tick(now)
        await self.plus2_tick(now)
        await self.strict_tick(now)
        await self.fort_tick(now)
        await self.ap_tick(now)
        await self.learn_tick(now)
        if now - self._last_tick["prune"] > 60:
            self._last_tick["prune"] = now
            self.eng.prune(now)
            self.prune_local(now)
            self.prune_gate(now)
        if now - self._last_tick["store"] > 3600:
            self._last_tick["store"] = now
            self.store.prune(now)
        await self.store.flush()

    def prune_local(self, now: float) -> None:
        for k in [k for k, v in self.reports.items() if now - v["t"] > 6 * 3600]:
            self.reports.pop(k, None)
        for k in [k for k, t in self._notice_last.items() if now - t > 7200]:
            self._notice_last.pop(k, None)
        for k in [k for k, t in self._joined.items() if now - t > 600]:
            self._joined.pop(k, None)
        for u, lst in list(self.report_rate.items()):
            lst[:] = [t for t in lst if now - t < 600]
            if not lst:
                self.report_rate.pop(u, None)
        for k in [k for k, v in self._admins.items() if now - v[0] > 3600]:
            self._admins.pop(k, None)

    async def janitor(self) -> None:
        while not self._stop.is_set():
            try:
                await asyncio.wait_for(self._stop.wait(), timeout=5)
            except asyncio.TimeoutError:
                pass
            try:
                await self.tick()
            except asyncio.CancelledError:
                raise
            except Exception:
                log.exception("ночная смена: сбой")

    async def shutdown(self) -> None:
        self._stop.set()
        await self.deleter.flush()
        for t in list(self._tasks):
            t.cancel()
        self.store.save_now()


# ══════════════════════════════════════════════════════════════════════════════════════════════
#  GUARD 5 · АВТОНОМНОЕ ЯДРО  (всё ниже — ДОБАВКА: код выше не менялся)
#  ─ Vault        SQLite: сюда уезжает всё тяжёлое (участники, самообучение, журнал), JSON остаётся маленьким
#  ─ Upstash      REST-клиент Redis: резервная копия «на чужом диске», общая база угроз, замок деплоя
#  ─ VaultStore   подкласс Store: то же самое поведение, но с SQLite под капотом (при сбое сам откатывается на JSON)
#  ─ Cortex       подкласс движка: ретро-обучение, авто-карточки, лаборатория самонастройки, прогноз, предохранитель…
#  ─ Sentinel     подкласс Guard: исполнение решений Cortex в Telegram, самолечение, отчёты, /brain и /vault
#  Любое включение выключается переменной окружения (GUARD_AX=0 — всё сразу); сбой любого узла НЕ ломает бота.
# ══════════════════════════════════════════════════════════════════════════════════════════════
import sqlite3
import base64
import contextlib

log_ax = logging.getLogger("guard.ax")
log_vault = logging.getLogger("guard.vault")
log_up = logging.getLogger("guard.upstash")


def _axf(name: str, default: bool = True) -> bool:
    v = os.getenv(name)
    if v is None or not v.strip():
        return default
    return v.strip().lower() not in ("0", "off", "no", "false", "нет", "выкл")


def _axn(name: str, default: float) -> float:
    try:
        return float(os.getenv(name, "") or default)
    except ValueError:
        return float(default)


AX_ON = _axf("GUARD_AX")                      # главный выключатель автономного ядра
AX_VAULT_ON = _axf("GUARD_VAULT")             # SQLite под капотом
AX_FEATS = {k: _axf("GUARD_AX_" + k.upper()) for k in (
    "hindsight", "cards", "autoham", "tune", "forecast", "shape", "cohort", "reactions", "dissonance", "media",
    "federation", "fuse", "doubt", "shadow", "invite", "combo", "debrief", "audit", "ti")}
AX_CARD_WAIT = _axn("GUARD_AX_CARD_WAIT_MIN", 20) * 60       # сколько ждать владельца, прежде чем решить самому
AX_CARD_DAILY = int(_axn("GUARD_AX_CARD_DAILY", 15))         # потолок самостоятельных решений в сутки на чат
AX_HAM_AFTER = _axn("GUARD_AX_HAM_AFTER_MIN", 120) * 60      # через сколько тихое сообщение считается «нормальным»
AX_FED_TTL = int(_axn("GUARD_AX_FED_DAYS", 30)) * 86400      # срок жизни автоматического общего бана
AX_VAULT_EVERY = _axn("GUARD_VAULT_EVERY", 20)                # не чаще чем раз в N секунд сверять изменения
AX_META_ALWAYS = ("learn", "journal", "spam_memory", "ax")   # ключи meta, которые всегда живут в SQLite
AX_META_DEPTH = {"learn": 4, "ax": 4}                         # на сколько уровней дробить на строки
AX_META_AUTO_BYTES = 24_000                                   # любой другой ключ толще — тоже уезжает в SQLite
_SEP = "\x1f"


def ax_reload_env() -> None:
    """Перечитать настройки автономного ядра из окружения. main() зовёт это сразу после load_env(), чтобы .env тоже работал."""
    global AX_ON, AX_VAULT_ON, AX_CARD_WAIT, AX_CARD_DAILY, AX_HAM_AFTER, AX_FED_TTL, AX_VAULT_EVERY
    AX_ON = _axf("GUARD_AX")
    AX_VAULT_ON = _axf("GUARD_VAULT")
    for k in list(AX_FEATS):
        AX_FEATS[k] = _axf("GUARD_AX_" + k.upper())
    AX_CARD_WAIT = _axn("GUARD_AX_CARD_WAIT_MIN", 20) * 60
    AX_CARD_DAILY = int(_axn("GUARD_AX_CARD_DAILY", 15))
    AX_HAM_AFTER = _axn("GUARD_AX_HAM_AFTER_MIN", 120) * 60
    AX_FED_TTL = int(_axn("GUARD_AX_FED_DAYS", 30)) * 86400
    AX_VAULT_EVERY = _axn("GUARD_VAULT_EVERY", 20)


# ───────────────────────────── Vault: SQLite ─────────────────────────────
def _ax_shard(top: str, v, depth: int):
    """Нарезка значения на (путь, кусок): словарь дробится на строки до заданной глубины, остальное — одним куском."""
    def rec(path, val, d):
        if d > 0 and isinstance(val, dict) and val and not any(_SEP in str(k) for k in val):
            for ck, cv in list(val.items()):
                yield from rec(path + [str(ck)], cv, d - 1)
        else:
            yield _SEP.join(path), val
    yield from rec([top], v, depth)


def _ax_put(root: dict, path: list, val) -> None:
    d = root
    for p in path[:-1]:
        nxt = d.get(p)
        if not isinstance(nxt, dict):
            nxt = d[p] = {}
        d = nxt
    d[path[-1]] = val


class Vault:
    """SQLite-сейф. Все методы синхронные и потокобезопасные (один замок): из asyncio вызываются через to_thread."""

    SCHEMA = """
    CREATE TABLE IF NOT EXISTS kv(ns TEXT NOT NULL, k TEXT NOT NULL, z INTEGER NOT NULL DEFAULT 0, v BLOB NOT NULL,
                                  PRIMARY KEY(ns, k)) WITHOUT ROWID;
    CREATE TABLE IF NOT EXISTS journal(id INTEGER PRIMARY KEY AUTOINCREMENT, ts INTEGER NOT NULL, kind TEXT, chat INTEGER,
                                       uid INTEGER, name TEXT, title TEXT, note TEXT, sig TEXT UNIQUE);
    CREATE INDEX IF NOT EXISTS j_ts ON journal(ts);
    CREATE INDEX IF NOT EXISTS j_chat ON journal(chat, ts);
    CREATE TABLE IF NOT EXISTS aphist(id INTEGER PRIMARY KEY AUTOINCREMENT, ts REAL, chat INTEGER, reflex TEXT,
                                      old INTEGER, new INTEGER, score REAL, actors INTEGER, why TEXT);
    CREATE INDEX IF NOT EXISTS ap_ts ON aphist(ts);
    CREATE TABLE IF NOT EXISTS traces(id INTEGER PRIMARY KEY AUTOINCREMENT, chat INTEGER, t0 REAL, t1 REAL, label TEXT,
                                      peak REAL, n INTEGER, data BLOB);
    CREATE INDEX IF NOT EXISTS tr_chat ON traces(chat, id);
    CREATE TABLE IF NOT EXISTS ti(kind TEXT NOT NULL, key TEXT NOT NULL, ts REAL NOT NULL, n INTEGER NOT NULL DEFAULT 1,
                                  src TEXT, PRIMARY KEY(kind, key)) WITHOUT ROWID;
    CREATE INDEX IF NOT EXISTS ti_ts ON ti(kind, ts);
    CREATE TABLE IF NOT EXISTS ledger(day TEXT NOT NULL, chat INTEGER NOT NULL, key TEXT NOT NULL, n INTEGER NOT NULL,
                                      PRIMARY KEY(day, chat, key)) WITHOUT ROWID;
    CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY, v TEXT);
    """

    def __init__(self, path: str | os.PathLike = "guard_vault.db", clock=time.time):
        self.path = Path(path)
        self.clock = clock
        self._lock = threading.RLock()
        self._cx: sqlite3.Connection | None = None
        self.ok = False
        self.err = ""
        self.recovered = ""
        self.open()

    # соединение ---------------------------------------------------------------------------
    def _connect(self) -> sqlite3.Connection:
        if self.path.parent and str(self.path.parent) not in ("", "."):
            self.path.parent.mkdir(parents=True, exist_ok=True)
        cx = sqlite3.connect(str(self.path), timeout=10.0, check_same_thread=False, isolation_level=None)
        cx.execute("PRAGMA auto_vacuum=INCREMENTAL")   # действует только на новой базе — это нормально
        cx.execute("PRAGMA journal_mode=WAL")
        cx.execute("PRAGMA synchronous=NORMAL")
        cx.execute("PRAGMA temp_store=MEMORY")
        cx.execute("PRAGMA busy_timeout=8000")
        cx.execute("PRAGMA journal_size_limit=33554432")   # журнал WAL после контрольной точки не раздувается выше 32 МБ
        return cx

    def open(self) -> bool:
        with self._lock:
            self.close()
            for attempt in (1, 2):
                cx = None
                try:
                    existed = self.path.exists()
                    cx = self._connect()
                    if existed and attempt == 1:
                        r = cx.execute("PRAGMA quick_check").fetchone()
                        if not r or r[0] != "ok":
                            raise sqlite3.DatabaseError("quick_check: %s" % (r[0] if r else "?"))
                    cx.executescript(self.SCHEMA)
                    self._cx, self.ok, self.err = cx, True, ""
                    return True
                except sqlite3.DatabaseError as e:
                    if cx is not None:
                        with contextlib.suppress(Exception):
                            cx.close()
                    if attempt == 2:
                        self.ok, self.err = False, str(e)
                        log_vault.error("SQLite не открылся: %s", e)
                        return False
                    bad = "%s.corrupt-%d" % (self.path, int(self.clock()))
                    log_vault.error("SQLite-файл повреждён (%s) — переименовываю в %s и начинаю заново", e, bad)
                    for suf in ("", "-wal", "-shm"):
                        with contextlib.suppress(OSError):
                            os.replace(str(self.path) + suf, bad + suf)
                    self.recovered = bad
                except Exception as e:                                   # noqa: BLE001
                    if cx is not None:
                        with contextlib.suppress(Exception):
                            cx.close()
                    self.ok, self.err = False, str(e)
                    log_vault.exception("SQLite не открылся")
                    return False
            return False

    def close(self) -> None:
        with self._lock:
            if self._cx is not None:
                with contextlib.suppress(Exception):
                    self._cx.close()
            self._cx, self.ok = None, False

    @contextlib.contextmanager
    def _tx(self):
        with self._lock:
            cx = self._cx
            if cx is None:
                raise sqlite3.OperationalError("vault закрыт")
            cx.execute("BEGIN IMMEDIATE")
            try:
                yield cx
            except BaseException:
                with contextlib.suppress(Exception):
                    cx.execute("ROLLBACK")
                raise
            else:
                cx.execute("COMMIT")

    def _q(self, sql: str, args: tuple = ()) -> list:
        with self._lock:
            if self._cx is None:
                raise sqlite3.OperationalError("vault закрыт")
            return self._cx.execute(sql, args).fetchall()

    def probe(self) -> bool:
        try:
            if self._cx is None and not self.open():
                return False
            self._q("SELECT 1")
            self.ok = True
            return True
        except Exception as e:                                           # noqa: BLE001
            self.ok, self.err = False, str(e)
            return False

    # кодирование значений ------------------------------------------------------------------
    @staticmethod
    def _enc(text: str) -> tuple:
        b = text.encode("utf-8")
        return (1, zlib.compress(b, 6)) if len(b) > 400 else (0, b)

    @staticmethod
    def _dec(z: int, v) -> str:
        b = bytes(v)
        return (zlib.decompress(b) if z else b).decode("utf-8")

    # основное состояние ---------------------------------------------------------------------
    def commit(self, ups: list, dels: list, replace_all: bool = False, jrows=(), core: str | None = None) -> None:
        rows = []
        for ns, k, text in ups:
            z, b = self._enc(text)
            rows.append((ns, k, z, b))
        if core is not None:
            z, b = self._enc(core)
            rows.append(("core", "json", z, b))
        with self._tx() as cx:
            if replace_all:
                cx.execute("DELETE FROM kv")
            if rows:
                cx.executemany("INSERT INTO kv(ns,k,z,v) VALUES(?,?,?,?) ON CONFLICT(ns,k) DO UPDATE SET z=excluded.z, v=excluded.v", rows)
            if dels:
                cx.executemany("DELETE FROM kv WHERE ns=? AND k=?", dels)
            if jrows:
                cx.executemany("INSERT OR IGNORE INTO journal(ts,kind,chat,uid,name,title,note,sig) VALUES(?,?,?,?,?,?,?,?)", list(jrows))
            cx.execute("INSERT INTO meta(k,v) VALUES('commit_t',?) ON CONFLICT(k) DO UPDATE SET v=excluded.v", (str(self.clock()),))
        if replace_all or len(rows) > 20_000:                            # после большой записи сразу сжимаем журнал
            with self._lock, contextlib.suppress(Exception):
                self._cx.execute("PRAGMA wal_checkpoint(TRUNCATE)")

    def iter_rows(self, where: str = "", args: tuple = ()):
        """Все строки kv (ns, k, text) — по одной, чтобы не держать всё в памяти дважды."""
        with self._lock:
            if self._cx is None:
                return
            cur = self._cx.execute("SELECT ns,k,z,v FROM kv" + (" WHERE " + where if where else ""), args)
            for ns, k, z, v in cur:
                try:
                    yield ns, k, self._dec(z, v)
                except Exception:                                        # noqa: BLE001
                    log_vault.warning("строка %s/%s не расшифровалась — пропускаю", ns, k)

    def get_kv(self, ns: str, k: str) -> str | None:
        r = self._q("SELECT z,v FROM kv WHERE ns=? AND k=?", (ns, k))
        return self._dec(*r[0]) if r else None

    def put_kv(self, ns: str, k: str, text: str) -> None:
        z, b = self._enc(text)
        with self._tx() as cx:
            cx.execute("INSERT INTO kv(ns,k,z,v) VALUES(?,?,?,?) ON CONFLICT(ns,k) DO UPDATE SET z=excluded.z, v=excluded.v", (ns, k, z, b))

    def meta_get(self, k: str, default: str = "") -> str:
        r = self._q("SELECT v FROM meta WHERE k=?", (k,))
        return r[0][0] if r else default

    def meta_set(self, k: str, v: str) -> None:
        with self._tx() as cx:
            cx.execute("INSERT INTO meta(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v", (k, str(v)))

    # журнал, история автопилота, следы атак, база угроз, учёт «спасено» ------------------------
    def journal_tail(self, chat: int = 0, limit: int = 15, before: float = 0) -> list:
        sql, args = "SELECT ts,kind,chat,uid,name,title,note FROM journal", []
        cond = []
        if chat:
            cond.append("chat=?")
            args.append(chat)
        if before:
            cond.append("ts<?")
            args.append(int(before))
        if cond:
            sql += " WHERE " + " AND ".join(cond)
        return self._q(sql + " ORDER BY ts DESC, id DESC LIMIT ?", tuple(args) + (int(limit),))

    def aphist_add(self, rows: list) -> None:
        if rows:
            with self._tx() as cx:
                cx.executemany("INSERT INTO aphist(ts,chat,reflex,old,new,score,actors,why) VALUES(?,?,?,?,?,?,?,?)", rows)

    def trace_add(self, chat: int, t0: float, t1: float, label: str, peak: float, events: list) -> None:
        data = zlib.compress(json.dumps(events, separators=(",", ":")).encode(), 6)
        with self._tx() as cx:
            cx.execute("INSERT INTO traces(chat,t0,t1,label,peak,n,data) VALUES(?,?,?,?,?,?,?)", (chat, t0, t1, label, peak, len(events), data))

    def traces_for(self, chat: int, limit: int = 40) -> list:
        out = []
        for tid, t0, t1, label, peak, data in self._q(
                "SELECT id,t0,t1,label,peak,data FROM traces WHERE chat=? ORDER BY id DESC LIMIT ?", (chat, int(limit))):
            try:
                out.append({"id": tid, "t0": t0, "t1": t1, "label": label, "peak": peak,
                            "ev": json.loads(zlib.decompress(bytes(data)).decode())})
            except Exception:                                            # noqa: BLE001
                continue
        return out

    def trace_relabel(self, tid: int, label: str) -> None:
        with self._tx() as cx:
            cx.execute("UPDATE traces SET label=? WHERE id=?", (label, tid))

    def ti_put(self, rows: list) -> None:
        """rows: (kind, key, ts, src). Повтор увеличивает счётчик n и обновляет время."""
        if rows:
            with self._tx() as cx:
                cx.executemany("INSERT INTO ti(kind,key,ts,n,src) VALUES(?,?,?,1,?) ON CONFLICT(kind,key) DO UPDATE "
                               "SET ts=max(ts,excluded.ts), n=n+1", rows)

    def ti_load(self, kind: str, since: float = 0.0, limit: int = 20000) -> list:
        return self._q("SELECT key,ts,n,src FROM ti WHERE kind=? AND ts>=? ORDER BY ts DESC LIMIT ?", (kind, since, int(limit)))

    def ledger_add(self, day: str, chat: int, key: str, n: int) -> None:
        if n:
            with self._tx() as cx:
                cx.execute("INSERT INTO ledger(day,chat,key,n) VALUES(?,?,?,?) ON CONFLICT(day,chat,key) DO UPDATE SET n=n+excluded.n",
                           (day, chat, key, int(n)))

    def ledger_range(self, day_from: str, chat: int = 0) -> dict:
        sql, args = "SELECT key, SUM(n) FROM ledger WHERE day>=?", [day_from]
        if chat:
            sql += " AND chat=?"
            args.append(chat)
        return {k: int(n) for k, n in self._q(sql + " GROUP BY key", tuple(args))}

    # обслуживание ----------------------------------------------------------------------------
    def maintain(self, now: float, journal_days: int = 120, hist_days: int = 180, traces_keep: int = 500, ti_days: int = 60) -> dict:
        out = {}
        with self._tx() as cx:
            out["journal"] = cx.execute("DELETE FROM journal WHERE ts<?", (int(now - journal_days * 86400),)).rowcount
            out["aphist"] = cx.execute("DELETE FROM aphist WHERE ts<?", (now - hist_days * 86400,)).rowcount
            out["traces"] = cx.execute("DELETE FROM traces WHERE id NOT IN (SELECT id FROM traces ORDER BY id DESC LIMIT ?)",
                                       (traces_keep,)).rowcount
            out["ti"] = cx.execute("DELETE FROM ti WHERE ts<?", (now - ti_days * 86400,)).rowcount
            day = time.strftime("%Y-%m-%d", time.gmtime(now - 120 * 86400))
            out["ledger"] = cx.execute("DELETE FROM ledger WHERE day<?", (day,)).rowcount
        with self._lock:
            if self._cx is not None:
                with contextlib.suppress(Exception):
                    self._cx.execute("PRAGMA incremental_vacuum(400)")
                with contextlib.suppress(Exception):
                    self._cx.execute("PRAGMA wal_checkpoint(PASSIVE)")
        return out

    def backup_to(self, dest: str | os.PathLike) -> int:
        """Целая копия базы (штатный backup-API SQLite: безопасно при работе). → размер файла."""
        dest = Path(dest)
        tmp = Path(str(dest) + ".tmp")
        with contextlib.suppress(OSError):
            tmp.unlink()
        with self._lock:
            if self._cx is None:
                raise sqlite3.OperationalError("vault закрыт")
            dst = sqlite3.connect(str(tmp))
            try:
                self._cx.backup(dst)
            finally:
                dst.close()
        os.replace(tmp, dest)
        return dest.stat().st_size

    def size(self) -> int:
        n = 0
        for suf in ("", "-wal"):
            with contextlib.suppress(OSError):
                n += os.path.getsize(str(self.path) + suf)
        return n

    def stats(self) -> dict:
        out = {"ok": self.ok, "bytes": self.size(), "tables": {}, "kv": {}}
        if not self.ok:
            return out
        for t in ("journal", "aphist", "traces", "ti", "ledger"):
            out["tables"][t] = self._q("SELECT COUNT(*) FROM " + t)[0][0]
        for ns, n, b in self._q("SELECT CASE WHEN ns LIKE 'u:%' THEN 'users' ELSE ns END, COUNT(*), SUM(LENGTH(v)) FROM kv GROUP BY 1"):
            out["kv"][ns] = (n, int(b or 0))
        return out


# ───────────────────────────── Upstash: Redis по REST ─────────────────────────────
class UpstashError(Exception):
    pass


class Upstash:
    """Минимальный клиент Upstash Redis REST (только stdlib). Свой лимит команд в сутки и «автомат» при сбоях сети."""

    CHUNK = 180_000                 # байт сырых данных в одном куске резервной копии (в base64 ≈ 240 КБ)
    REQ_MAX = 700_000               # потолок тела одного запроса (у бесплатного тарифа — 1 МБ)

    def __init__(self, url: str = "", token: str = "", prefix: str = "guard", budget: int = 7000, timeout: float = 6.0,
                 clock=time.time, opener=None):
        self.url = (url or "").rstrip("/")
        self.token = token or ""
        self.prefix = prefix
        self.budget = int(budget)
        self.timeout = timeout
        self.clock = clock
        self._opener = opener                      # для тестов: f(req, timeout) → bytes
        self._day, self._used = "", 0
        self._fails, self._open_until = 0, 0.0
        self.last_err = ""
        self.sent = 0

    @classmethod
    def from_env(cls, bot_id: str = "") -> "Upstash":
        url = os.getenv("UPSTASH_REDIS_REST_URL") or os.getenv("KV_REST_API_URL") or ""
        tok = os.getenv("UPSTASH_REDIS_REST_TOKEN") or os.getenv("KV_REST_API_TOKEN") or ""
        pre = os.getenv("GUARD_UPSTASH_PREFIX") or "guard"
        return cls(url, tok, pre, int(_axn("GUARD_UPSTASH_BUDGET", 7000)))

    @property
    def enabled(self) -> bool:
        return bool(self.url and self.token)

    def k(self, *parts) -> str:
        return ":".join([self.prefix, *[str(p) for p in parts]])

    def _charge(self, n: int) -> None:
        now = self.clock()
        if now < self._open_until:
            raise UpstashError("пауза после сбоев до %s" % time.strftime("%H:%M", time.gmtime(self._open_until)))
        day = time.strftime("%Y-%m-%d", time.gmtime(now))
        if day != self._day:
            self._day, self._used = day, 0
        if self._used + n > self.budget:
            raise UpstashError("суточный лимит команд (%d) исчерпан" % self.budget)
        self._used += n

    def _post(self, path: str, payload) -> Any:
        body = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        req = urllib.request.Request(self.url + path, data=body, method="POST",
                                     headers={"Authorization": "Bearer " + self.token, "Content-Type": "application/json"})
        try:
            raw = self._opener(req, self.timeout) if self._opener else urllib.request.urlopen(req, timeout=self.timeout).read()
            data = json.loads(raw.decode("utf-8") if isinstance(raw, (bytes, bytearray)) else raw)
        except Exception as e:                                           # noqa: BLE001
            self._fails += 1
            if self._fails >= 4:
                self._open_until = self.clock() + 300
                self._fails = 0
            self.last_err = type(e).__name__
            raise UpstashError("сеть: %s" % type(e).__name__) from None
        self._fails = 0
        self.sent += 1
        return data

    def cmd(self, *args) -> Any:
        """Одна команда: cmd("SET", "k", "v"). Исключение UpstashError при любой проблеме."""
        if not self.enabled:
            raise UpstashError("Upstash не настроен")
        self._charge(1)
        data = self._post("", [str(a) if not isinstance(a, (int, float)) else a for a in args])
        if isinstance(data, dict) and data.get("error"):
            self.last_err = str(data["error"])[:80]
            raise UpstashError(str(data["error"])[:120])
        return data.get("result") if isinstance(data, dict) else data

    def pipeline(self, cmds: list) -> list:
        if not self.enabled:
            raise UpstashError("Upstash не настроен")
        if not cmds:
            return []
        self._charge(len(cmds))
        data = self._post("/pipeline", [[str(a) if not isinstance(a, (int, float)) else a for a in c] for c in cmds])
        out = []
        for item in data if isinstance(data, list) else []:
            if isinstance(item, dict) and item.get("error"):
                self.last_err = str(item["error"])[:80]
                raise UpstashError(str(item["error"])[:120])
            out.append(item.get("result") if isinstance(item, dict) else item)
        return out

    async def acmd(self, *args):
        return await asyncio.to_thread(self.cmd, *args)

    async def apipe(self, cmds: list):
        return await asyncio.to_thread(self.pipeline, cmds)

    # резервная копия большого файла кусками ---------------------------------------------------
    def backup_put(self, name: str, blob: bytes, info: dict | None = None, ttl: int = 30 * 86400) -> dict:
        gen = format(int(self.clock()), "x")
        packed = zlib.compress(blob, 6)
        parts = [packed[i:i + self.CHUNK] for i in range(0, len(packed), self.CHUNK)] or [b""]
        batch, size = [], 0
        for i, p in enumerate(parts):
            s = base64.b64encode(p).decode("ascii")
            if batch and size + len(s) > self.REQ_MAX:
                self.pipeline(batch)
                batch, size = [], 0
            batch.append(["SET", self.k("bk", name, gen, i), s, "EX", ttl])
            size += len(s)
        if batch:
            self.pipeline(batch)
        meta = {"gen": gen, "n": len(parts), "sha": hashlib.sha256(blob).hexdigest(), "size": len(blob), "t": int(self.clock()), **(info or {})}
        old = self.cmd("GET", self.k("bk", name, "meta"))
        self.cmd("SET", self.k("bk", name, "meta"), json.dumps(meta, separators=(",", ":")), "EX", ttl)
        if old:
            with contextlib.suppress(Exception):
                o = json.loads(old)
                if o.get("gen") and o["gen"] != gen:
                    self.pipeline([["DEL", self.k("bk", name, o["gen"], i)] for i in range(int(o.get("n", 0)))])
        return meta

    def backup_meta(self, name: str) -> dict | None:
        raw = self.cmd("GET", self.k("bk", name, "meta"))
        return json.loads(raw) if raw else None

    def backup_get(self, name: str) -> tuple | None:
        meta = self.backup_meta(name)
        if not meta:
            return None
        parts = []
        keys = [self.k("bk", name, meta["gen"], i) for i in range(int(meta["n"]))]
        for i in range(0, len(keys), 3):
            for v in self.pipeline([["GET", k] for k in keys[i:i + 3]]):
                if v is None:
                    raise UpstashError("в резервной копии не хватает куска")
                parts.append(base64.b64decode(v))
        blob = zlib.decompress(b"".join(parts))
        if hashlib.sha256(blob).hexdigest() != meta.get("sha"):
            raise UpstashError("контрольная сумма копии не сошлась")
        return blob, meta


# контейнер резервной копии: [GXB1][len json][json: ядро][db-файл]
def ax_pack_backup(core_json: bytes, db_bytes: bytes) -> bytes:
    return b"GXB1" + len(core_json).to_bytes(4, "big") + core_json + db_bytes


def ax_unpack_backup(blob: bytes) -> tuple:
    if blob[:4] != b"GXB1":
        raise ValueError("это не резервная копия guard")
    n = int.from_bytes(blob[4:8], "big")
    return blob[8:8 + n], blob[8 + n:]


# ───────────────────────────── VaultStore: Store + SQLite ─────────────────────────────
class VaultStore(Store):
    """Store, у которого тяжёлое лежит в SQLite, а JSON хранит только «ядро» (настройки чатов, счётчики, мелочь).

    Гарантии:
    • интерфейс и поведение Store не меняются (chats/users/meta в памяти те же самые);
    • SQLite пишется первым; JSON урезается ТОЛЬКО после успешной записи в SQLite;
    • если SQLite сломался — следующий снимок снова полный JSON, как раньше (ничего не теряется);
    • изменения пишутся построчно: переписывается только то, что реально изменилось.
    """

    def __init__(self, path: str | os.PathLike = "guard_state.json", clock=time.time, vault: Vault | None = None):
        super().__init__(path, clock)
        self.vault = vault
        self.slim = AX_VAULT_ON
        self._vh: dict = {}                    # (ns, k) → хэш последнего записанного текста
        self._vlock = threading.Lock()
        self._off: set = set()                 # ключи meta, живущие в SQLite
        self._pend: dict | None = None
        self._replace_all = False
        self._vfail = 0
        self._vretry = 0.0
        self._first_slim = False
        self._jlast = 0
        self.loaded_from = ""                  # откуда поднято состояние: json / vault-core / пусто
        self.hydrated = (0, 0)
        self.vault_lost = False                # JSON урезан, а в SQLite пусто — участники/самообучение потеряны

    # ---- загрузка ----
    def load(self) -> None:
        v = self.vault
        if v is not None and v.ok and not self.path.exists():
            try:
                core = v.get_kv("core", "json")
            except Exception:                                            # noqa: BLE001
                core = None
            if core:
                log_vault.warning("JSON-файла нет, но в SQLite есть копия ядра — поднимаю из неё")
                tmp = Path(str(self.path) + ".restore")
                tmp.write_text(core, encoding="utf-8")
                os.replace(tmp, self.path)
                self.loaded_from = "vault-core"
        super().load()
        info = self.meta.pop("_vault", None)
        slim_json = isinstance(info, dict) and bool(info.get("slim"))
        self._off = set(info.get("off", [])) if isinstance(info, dict) else set()
        if not self.loaded_from:
            self.loaded_from = "json" if self.chats or self.meta else ""
        if v is None or not v.ok:
            if slim_json:
                log_vault.error("JSON урезан (участники/самообучение лежат в SQLite), а SQLite недоступен — они НЕ загружены!")
            return
        if slim_json:
            self._hydrate()
            self.vault_lost = self.hydrated == (0, 0) and bool(self.chats)
        else:
            self._replace_all = True            # JSON полный: он главный, SQLite перезапишется целиком
            self._first_slim = bool(self.chats)
            self._vh = {}

    def _hydrate(self) -> None:
        nu = nm = 0
        for ns, k, text in self.vault.iter_rows():
            try:
                if ns.startswith("u:"):
                    st = self.chats.get(int(ns[2:]))
                    if st is not None:
                        st.users[int(k)] = _load(UserRec, json.loads(text))
                        nu += 1
                elif ns == "m":
                    _ax_put(self.meta, k.split(_SEP), json.loads(text))
                    nm += 1
            except Exception:                                            # noqa: BLE001
                log_vault.warning("строка %s/%s не разобралась — пропускаю", ns, k[:40])
        self.hydrated = (nu, nm)
        self._prime()
        log_vault.info("из SQLite поднято: участников %d, кусков самообучения/журнала %d", nu, nm)

    def _prime(self) -> None:
        """Запомнить хэши загруженного, чтобы первый же снимок не переписывал всю базу."""
        enc = json.JSONEncoder(ensure_ascii=False, default=_jdefault).encode
        vh = {}
        for cid, st in self.chats.items():
            ns = "u:%d" % cid
            for uid, r in st.users.items():
                vh[(ns, str(uid))] = hash(enc(r.__dict__ if type(r) is UserRec and len(r.__dict__) == _UREC_N else r))
        for k in self._off | set(AX_META_ALWAYS):
            if k in self.meta:
                for path, val in _ax_shard(k, self.meta[k], AX_META_DEPTH.get(k, 1)):
                    vh[("m", path)] = hash(enc(val))
        with self._vlock:
            self._vh = vh

    # ---- снимок ----
    def _slim_now(self) -> bool:
        return self.slim and self.vault is not None and self.vault.ok and self._vfail < 2

    def heal(self, now: float | None = None) -> bool:
        """Попытка вернуться в «тонкий» режим после сбоя SQLite (вызывается из тика)."""
        now = time.time() if now is None else now
        if self.vault is None or self._vfail < 2 or now < self._vretry:
            return False
        self._vretry = now + 300
        if self.vault.probe():
            self._vfail = 0
            self._replace_all = True
            self._vh = {}
            self._first_slim = False
            self.dirty = True
            log_vault.warning("SQLite снова работает — возвращаюсь к тонкому JSON")
            return True
        return False

    def _snap_parts(self, parts: list, step: int = 400):
        if not self._slim_now():
            self._pend = None
            yield from super()._snap_parts(parts, step)
            return
        enc = json.JSONEncoder(ensure_ascii=False, default=_jdefault).encode
        ups: list = []
        newh: dict = {}
        seen: set = set()
        n = 0
        for cid, st in list(self.chats.items()):
            ns = "u:%d" % cid
            for uid, r in list(st.users.items()):
                s = enc(r.__dict__ if type(r) is UserRec and len(r.__dict__) == _UREC_N else r)
                key = (ns, str(uid))
                seen.add(key)
                h = hash(s)
                if self._vh.get(key) != h:
                    ups.append((ns, key[1], s))
                    newh[key] = h
                n += 1
                if n % 1500 == 0:
                    yield
        slim_meta: list = []
        for k, v in list(self.meta.items()):
            k = str(k)
            off = k in self._off or k in AX_META_ALWAYS
            s = None
            if not off:
                s = enc(v)
                if len(s) > AX_META_AUTO_BYTES:
                    self._off.add(k)
                    off = True
            if off:
                for path, val in _ax_shard(k, v, AX_META_DEPTH.get(k, 1)):
                    t = enc(val)
                    key = ("m", path)
                    seen.add(key)
                    h = hash(t)
                    if self._vh.get(key) != h:
                        ups.append(("m", path, t))
                        newh[key] = h
                    n += 1
                    if n % 1500 == 0:
                        yield
                yield
            else:
                slim_meta.append(enc(k) + ": " + s)
        with self._vlock:
            dels = [key for key in self._vh if key not in seen]
        jrows = []
        for e in list(self.meta.get("journal") or ())[-300:]:
            try:
                t = int(e.get("t", 0))
                sig = "%d|%s|%s|%s|%s" % (t, e.get("k"), e.get("c"), e.get("by"), (e.get("no") or "")[:24])
                jrows.append((t, e.get("k"), e.get("c"), e.get("by"), e.get("n"), e.get("ti"), e.get("no"), sig))
            except Exception:                                            # noqa: BLE001
                continue
        self._pend = {"ups": ups, "dels": dels, "newh": newh, "jrows": jrows, "replace": self._replace_all}
        # ядро JSON: чаты без участников + мелкая meta + метка «урезано»
        parts.append('{"v": 1, "chats": {')
        first = True
        for cid, st in list(self.chats.items()):
            head = enc({f: getattr(st, f) for f in _field_names(ChatState) if f != "users"})[1:-1]
            parts.append(("" if first else ", ") + enc(str(cid)) + ": {" + head + (", " if head else "") + '"users": {}}')
            first = False
        parts.append('}, "captchas": ' + enc(dict(self.captchas)) + ', "rings": ' + enc(dict(self.rings))
                     + ', "alert_users": ' + enc(sorted(self.alert_users)) + ', "meta": {')
        slim_meta.append('"_vault": ' + enc({"slim": True, "off": sorted(self._off), "t": round(self.clock())}))
        parts.append(", ".join(slim_meta))
        parts.append("}}")
        yield

    def _write(self, data) -> None:
        pend, self._pend = self._pend, None
        if pend is not None:
            core = "".join(data) if isinstance(data, list) else None
            try:
                self.vault.commit(pend["ups"], pend["dels"], pend["replace"], pend["jrows"], core)
            except Exception:
                self._vfail += 1
                log_vault.exception("запись в SQLite не удалась (%d подряд) — JSON не урезаю", self._vfail)
                raise
            with self._vlock:
                if pend["replace"]:
                    self._vh = {}
                self._vh.update(pend["newh"])
                for key in pend["dels"]:
                    self._vh.pop(key, None)
            self._vfail = 0
            self._replace_all = False
            if self._first_slim and self.path.exists():
                self._first_slim = False
                try:
                    import shutil
                    shutil.copy2(self.path, str(self.path) + ".pre-vault")
                    log_vault.info("полный JSON сохранён как %s.pre-vault (откат: верни его на место и GUARD_VAULT=0)", self.path)
                except OSError:
                    pass
        super()._write(data)

    # ---- выгрузка обратно в один полный JSON (для отката) ----
    def export_json(self, dest: str | os.PathLike) -> int:
        parts: list = []
        for _ in Store._snap_parts(self, parts):
            pass
        text = "".join(parts)
        Path(dest).write_text(text, encoding="utf-8")
        return len(text)

    def sizes(self) -> dict:
        out = {"json": 0, "vault": 0}
        with contextlib.suppress(OSError):
            out["json"] = self.path.stat().st_size
        if self.vault is not None:
            out["vault"] = self.vault.size()
        return out


def ax_restore_from_upstash(up: Upstash, json_path: str, db_path: str, name: str) -> str:
    """Свежий диск (редеплой на бесплатном хостинге): тянем копию из Upstash. → '' если всё хорошо, иначе причина."""
    try:
        got = up.backup_get(name)
    except Exception as e:                                               # noqa: BLE001
        return "не получилось скачать копию: %s" % e
    if not got:
        return "в Upstash нет копии"
    blob, meta = got
    try:
        core, db = ax_unpack_backup(blob)
    except Exception as e:                                               # noqa: BLE001
        return "копия повреждена: %s" % e
    Path(json_path).parent.mkdir(parents=True, exist_ok=True)
    for path, data in ((db_path, db), (json_path, core)):
        tmp = path + ".restore"
        with open(tmp, "wb") as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    log_vault.warning("состояние восстановлено из Upstash (копия от %s, %d КБ)",
                      time.strftime("%d.%m %H:%M", time.gmtime(meta.get("t", 0))), int(meta.get("size", 0)) // 1024)
    return ""



# ───────────────────────────── Cortex: автономный мозг движка ─────────────────────────────
import copy

# новые виды сигналов для автопилота (читаются в рантайме, поэтому достаточно дополнить словари)
AP_REFLEXES["wave"]["soft"] = AP_REFLEXES["wave"]["soft"] | {"firstpost", "crowd"}
AP_REFLEXES["raid"]["soft"] = AP_REFLEXES["raid"]["soft"] | {"raid_early", "cohort"}
AP_PULSE_WEIGHT.update({"firstpost": 0.7, "crowd": 0.5, "raid_early": 0.45, "cohort": 0.6})
AP_KIND_LABEL.update({"firstpost": "ссылка в первую минуту", "crowd": "участники метят как спам",
                      "raid_early": "аномальный приток", "cohort": "когорта свежих аккаунтов"})
_AX_HARD_ALL = frozenset().union(*[s["hard"] for s in AP_REFLEXES.values()])
_AX_ALL_KINDS = frozenset().union(*[s["hard"] | s["soft"] for s in AP_REFLEXES.values()])

AX_GRID = (0.8, 0.9, 1.0, 1.12, 1.25)          # множитель порогов автопилота: больше = спокойнее
AX_LAG_MISS = 900.0                             # атака, которую порог так и не заметил, «стоит» 15 минут опоздания
AX_COST_QUIET, AX_COST_FALSE = 8.0, 12.0       # цена ложной тревоги на тихом / на отменённом владельцем эпизоде
AX_STAT_KEYS = ("hind", "cards", "ham", "ti", "media", "fed", "tune", "doubt", "fuse")


def ax_pscore_series(ev: list, step: float = 10.0) -> list:
    """Чистая (без состояния движка) оценка угрозы по следу: [(t, {reflex: (score, actors)})].
    Та же математика, что в ap_score (окно, полураспад, потолок на источник), без поправок по людям."""
    if not ev:
        return []
    evs = sorted(ev, key=lambda e: e[0])
    t_end = evs[-1][0] + 60.0
    out, t = [], evs[0][0]
    while t <= t_end:
        row = {}
        for reflex, spec in AP_REFLEXES.items():
            kinds = spec["hard"] | spec["soft"]
            per: dict = {}
            for ts, who, w, kind in evs:
                if ts > t:
                    break
                age = t - ts
                if age > RADAR_WINDOW or kind not in kinds:
                    continue
                per[who] = per.get(who, 0.0) + w * 0.5 ** (age / RADAR_HALF)
            row[reflex] = (round(sum(min(s, RADAR_ACTOR_CAP) for s in per.values()), 2),
                           sum(1 for s in per.values() if s >= RADAR_ACTOR_MIN))
        out.append((t, row))
        t += step
    return out


def ax_trip_time(series: list, k: float):
    """Первый момент, когда хоть один рефлекс перешагнул порог 1-го уровня при множителе k. None — не заметил."""
    for t, row in series:
        for reflex, (score, actors) in row.items():
            s1, a1 = AP_TRIP[reflex][0]
            if score >= s1 * k and actors >= a1:
                return t
    return None


def ax_lab_eval(traces: list, cur_k: float = 1.0, grid=AX_GRID) -> dict:
    """Лаборатория самонастройки: прогоняет архив эпизодов («атака» / «тихо» / «ложная тревога») через разные пороги
    и выбирает такой, что ловит атаки раньше и не даёт новых ложных тревог. Работает только на сохранённых следах."""
    prep = []
    for tr in traces:
        ev = [(float(e[0]), int(e[1]), float(e[2]), str(e[3])) for e in tr.get("ev", ()) if len(e) >= 4]
        if not ev:
            continue
        first_hard = next((e[0] for e in sorted(ev) if e[3] in _AX_HARD_ALL), ev[0][0])
        prep.append((tr.get("label", "quiet"), first_hard, ax_pscore_series(ev)))
    n_att = sum(1 for p in prep if p[0] == "attack")
    n_quiet = sum(1 for p in prep if p[0] == "quiet")
    n_false = sum(1 for p in prep if p[0] == "false")
    res = {"n_attack": n_att, "n_quiet": n_quiet, "n_false": n_false, "loss": {}, "fp": {}, "miss": {}, "lag": {},
           "k_cur": cur_k, "k_best": cur_k, "k_new": cur_k, "why": ""}
    if n_att < 3 or (n_quiet + n_false) < 2:
        res["why"] = "мало данных (нужно ≥3 атак и ≥2 тихих/ложных эпизодов)"
        return res
    for k in grid:
        loss = lag_sum = 0.0
        fp = miss = 0
        for label, first_hard, series in prep:
            tt = ax_trip_time(series, k)
            if label == "attack":
                lag = AX_LAG_MISS if tt is None else max(0.0, tt - first_hard)
                miss += tt is None
                lag_sum += lag
                loss += lag / 60.0
            elif tt is not None:
                fp += 1
                loss += AX_COST_FALSE if label == "false" else AX_COST_QUIET
        loss += 0.3 * abs(math.log(k))
        res["loss"][k], res["fp"][k], res["miss"][k], res["lag"][k] = round(loss, 2), fp, miss, round(lag_sum / max(1, n_att), 1)
    cur = min(grid, key=lambda g: abs(g - cur_k))
    best = min(grid, key=lambda g: (res["loss"][g], abs(g - 1.0)))
    res["k_best"] = best
    gain = res["loss"][cur] - res["loss"][best]
    if best == cur or gain < max(1.0, 0.1 * res["loss"][cur]):
        res["why"] = "текущие пороги уже лучшие или выигрыш мал"
        return res
    i, j = grid.index(cur), grid.index(best)
    nxt = grid[i + (1 if j > i else -1)]                # на один шаг, не прыжком
    if res["fp"][nxt] > res["fp"][cur] or res["miss"][nxt] > res["miss"][cur]:
        res["why"] = "шаг дал бы новые ложные тревоги или пропуски — не трогаю"
        return res
    res["k_new"] = nxt
    bits = []
    if res["fp"][cur] > res["fp"][nxt]:
        bits.append("убирает ложных тревог: %d" % (res["fp"][cur] - res["fp"][nxt]))
    if res["lag"][nxt] < res["lag"][cur] - 1:
        bits.append("ловит атаки раньше на %.0f с" % (res["lag"][cur] - res["lag"][nxt]))
    res["why"] = ", ".join(bits) + " (регрессий нет)" if bits else "выигрыш по совокупной цене ошибок"
    return res


_AX_STRIP = re.compile(r"https?://\S+|(?:t|telegram)\.me/\S+|www\.\S+|@\w+|\b[\w-]+\.(?:com|ru|org|net|io|me|top|xyz|cc|to)\S*", re.I)
_AX_TI_TOKEN = re.compile(r"^(@[a-z0-9_]{4,32}|(?:t|telegram)\.me/\S+|\+?\d[\d\-\s()]{9,})$", re.I)


def ax_style_vec(text: str):
    """Грубый «почерк» сообщения: длина, доля кириллицы, капс, цифры, символы/эмодзи. None — слишком коротко."""
    t = _AX_STRIP.sub(" ", (text or "")).strip()                      # ссылки и @ники — не «почерк» (иначе цифры в URL ломают оценку)
    letters = [ch for ch in t if ch.isalpha()]
    if len(t) < 8 or len(letters) < 5:
        return None
    n = len(t)
    cyr = sum(1 for ch in letters if "а" <= ch.lower() <= "я" or ch.lower() == "ё") / len(letters)
    caps = sum(1 for ch in letters if ch.isupper()) / len(letters)
    dig = sum(ch.isdigit() for ch in t) / n
    emo = sum(1 for ch in t if ord(ch) > 0x2000 and not ch.isalpha()) / n
    return (min(n, 400) / 400.0, cyr, caps, dig, min(1.0, emo * 5.0))


def ax_style_update(prof: list | None, vec: tuple, link: bool, now: float) -> list:
    """Профиль: [ts, n, m0..m5, d0..d4] — скользящие средние почерка + доля сообщений со ссылкой + разброс."""
    x = list(vec) + [1.0 if link else 0.0]
    if not prof:
        return [round(now), 1] + [round(v, 3) for v in x] + [0.0] * 5
    n = int(prof[1])
    a = 1.0 / (n + 1) if n < 8 else 0.12
    m, d = prof[2:8], prof[8:13]
    for i in range(6):
        if i < 5:
            d[i] = d[i] + a * (abs(x[i] - m[i]) - d[i])
        m[i] = m[i] + a * (x[i] - m[i])
    return [round(now), min(n + 1, 10_000)] + [round(v, 3) for v in m] + [round(v, 3) for v in d]


def ax_dissonance(prof: list | None, vec: tuple, link: bool) -> tuple:
    """Насколько сообщение «не в почерке» давнего участника. → (баллы 0..3, какие признаки сработали)."""
    if not prof or int(prof[1]) < 12:
        return 0.0, []
    m, d = prof[2:8], prof[8:13]
    hits = []
    if link and m[5] < 0.06:
        hits.append("ссылка/контакт впервые")
    if abs(vec[1] - m[1]) >= 0.6 and d[1] < 0.25:
        hits.append("смена языка")
    drift = sum(abs(vec[i] - m[i]) / (d[i] + 0.12) for i in (0, 2, 3, 4)) / 4.0
    if drift >= 2.5:
        hits.append("другой стиль")
    if "ссылка/контакт впервые" in hits:
        if "смена языка" in hits and "другой стиль" in hits:
            return 3.0, hits
        if "смена языка" in hits:
            return 2.2, hits
        if "другой стиль" in hits:
            return 1.2, hits                                          # только лёгкий намёк, без действий
    return 0.0, hits


class _AxSimIdx:
    """Быстрый поиск похожего simhash (расстояние ≤3) по 4 полосам по 16 бит."""

    def __init__(self, cap: int = 6000):
        self.cap = cap
        self.items: dict = {}
        self.bands = [defaultdict(set) for _ in range(4)]

    def add(self, sim: int, ts: float) -> None:
        if not sim:
            return
        if sim not in self.items:
            if len(self.items) >= self.cap:
                old = sorted(self.items, key=self.items.get)[:self.cap // 10]
                for s in old:
                    self._rm(s)
            for i in range(4):
                self.bands[i][(sim >> (16 * i)) & 0xFFFF].add(sim)
        self.items[sim] = ts

    def _rm(self, sim: int) -> None:
        self.items.pop(sim, None)
        for i in range(4):
            b = self.bands[i].get((sim >> (16 * i)) & 0xFFFF)
            if b is not None:
                b.discard(sim)

    def find(self, sim: int, d: int = 3):
        if not sim:
            return None
        for i in range(4):
            for c in self.bands[i].get((sim >> (16 * i)) & 0xFFFF, ()):
                if (c ^ sim).bit_count() <= d:
                    return c
        return None

    def prune(self, before: float) -> None:
        for s in [s for s, t in self.items.items() if t < before]:
            self._rm(s)

    def __len__(self) -> int:
        return len(self.items)


class Cortex:
    """Автономная надстройка движка. Всё, что она делает, — через уже существующие и проверенные механизмы
    (сигналы анализа, уроки самообучения, множители автопилота). Любой сбой изолирован и не доходит до модерации."""

    ax_on = False

    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        self.init_ax()

    # ───────── состояние ─────────
    def init_ax(self) -> None:
        self.ax_on = AX_ON
        self.ax_out: list = []                                   # решения для Sentinel (то, что требует Telegram)
        self.ax_q = {"aphist": [], "traces": [], "ti": [], "ledger": []}
        self.ax_blind: set = set()                               # чаты, где бот не видит/не может удалять
        self._ax_dis: dict = {}
        self._ax_errs: dict = {}
        self._axev: dict = {}
        self._axep: dict = {}
        self._ax_acc: dict = {}
        self._ax_slot: dict = {}
        self._ax_over: dict = {}
        self._ax_cidmap: dict = {}
        self._ax_hind: deque = deque(maxlen=200)
        self._ax_hamq: deque = deque(maxlen=400)
        self._ax_effq: list = []
        self._axj: dict = {}
        self._axjb: dict = {}
        self._axj_fired: dict = {}
        self._axr: dict = {}
        self._axr_fire: dict = {}
        self._ax_sh: dict = {}
        self._ax_last_card = 0.0
        self.ti_sim = _AxSimIdx()
        self.ti_ct: dict = {}
        self.ti_fu: dict = {}
        self.ti_uid: dict = {}
        self._sty_n = 0
        self._ti_pend: dict = {}
        self._ax_hs_pend: list = []

    def _axm(self) -> dict:
        d = self.store.meta.get("ax")
        if not isinstance(d, dict) or "c" not in d:
            d = self.store.meta["ax"] = {"v": 1, "c": {}, "g": {"src": {}, "dec": [], "day": {}}, "sty": {}}
        d.setdefault("g", {"src": {}, "dec": [], "day": {}})
        d.setdefault("sty", {})
        return d

    def _ax_c(self, chat_id: int) -> dict:
        return self._axm()["c"].setdefault(str(chat_id), {})

    def _ax_fail(self, name: str) -> None:
        now = time.time()
        dq = self._ax_errs.setdefault(name, deque(maxlen=8))
        dq.append(now)
        log_ax.exception("автономное ядро: сбой в «%s» (модерация не затронута)", name)
        if len(dq) >= 5 and now - dq[0] < 600:
            self._ax_dis[name] = now + 1800
            self.ax_out.append(("breaker", name))
            dq.clear()

    def _axg(self, name: str, fn, *a):
        """Вызов узла под «автоматом»: ошибка не пробрасывается, а пять подряд — отключают узел на 30 минут."""
        if not self.ax_on or self._ax_dis.get(name, 0) > time.time():
            return None
        try:
            return fn(*a)
        except Exception:                                            # noqa: BLE001
            self._ax_fail(name)
            return None

    def _ax_on(self, feat: str) -> bool:
        return self.ax_on and AX_FEATS.get(feat, False) and self._ax_dis.get(feat, 0) <= time.time()

    def ax_count(self, chat_id: int, key: str, n: int = 1, now: float | None = None) -> None:
        now = self.clock() if now is None else now
        day = self._axm()["g"].setdefault("day", {})
        d = day.setdefault(self.store.day(now), {})
        d[key] = d.get(key, 0) + n
        if len(day) > 14:
            for k in sorted(day)[:-14]:
                day.pop(k, None)
        self.ax_q["ledger"].append((self.store.day(now), chat_id, key, n))
        if chat_id:                                                  # суточные счётчики чата (для потолков) переживают запись в SQLite
            dd = self._ax_c(chat_id).setdefault("dd", {})
            if dd.get("_d") != self.store.day(now):
                dd.clear()
                dd["_d"] = self.store.day(now)
            dd[key] = dd.get(key, 0) + n
        self.store.dirty = True

    def _ax_src(self, name: str, ok: bool = True) -> None:
        s = self._axm()["g"].setdefault("src", {}).setdefault(name, [0, 0])
        s[0 if ok else 1] += 1

    def _ax_cid(self, cfg) -> int:
        cid = self._ax_cidmap.get(id(cfg))
        st = self.store.chats.get(cid) if cid else None
        if cid and ((st is not None and st.cfg is cfg) or self._ax_sh.get(cid, {}).get("cfg") is cfg):
            return cid
        self._ax_cidmap = {id(s.cfg): c for c, s in self.store.chats.items()}
        for c, sh in self._ax_sh.items():
            if sh.get("cfg") is not None:
                self._ax_cidmap[id(sh["cfg"])] = c
        return self._ax_cidmap.get(id(cfg), 0)

    # ───────── зеркало событий (для прогноза, следов атак и лаборатории) ─────────
    def _ax_mirror(self, chat_id: int, who: int, w: float, kind: str, now: float) -> None:
        dq = self._axev.setdefault(chat_id, deque(maxlen=1200))
        dq.append((now, who, w, kind))
        if kind in _AX_HARD_ALL:
            self._ax_acc[chat_id] = self._ax_acc.get(chat_id, 0.0) + w

    def radar_note(self, chat_id: int, uid: int, kind: str, now: float | None = None) -> bool:
        r = super().radar_note(chat_id, uid, kind, now)
        if self.ax_on:
            w = RADAR_WEIGHT.get(kind, 0.0)
            if w > 0 and kind in _AX_ALL_KINDS:
                self._ax_mirror(chat_id, int(uid), w, kind, self.clock() if now is None else now)
        return r

    def ap_pulse(self, chat_id: int, who: int, kind: str, w: float | None = None, now: float | None = None) -> None:
        super().ap_pulse(chat_id, who, kind, w, now)
        if self.ax_on:
            w2 = AP_PULSE_WEIGHT.get(kind, 0.0) if w is None else w
            if w2 > 0 and kind in _AX_ALL_KINDS:
                self._ax_mirror(chat_id, int(who), float(w2), kind, self.clock() if now is None else now)

    def note_overturn(self, chat_id: int, uid: int) -> None:
        super().note_overturn(chat_id, uid)
        if self.ax_on:
            now = self.clock()
            self._ax_over.setdefault(chat_id, deque(maxlen=20)).append(now)
            self._axg("fuse", self.ax_fuse_note, chat_id, now, "overturn")

    # ───────── сигналы анализа сообщения ─────────
    def _learn_signals(self, msg, chat, a, tier: str, now: float) -> None:
        super()._learn_signals(msg, chat, a, tier, now)
        if self.ax_on:
            try:
                self._ax_signals(msg, chat, a, tier, now)
            except Exception:                                        # noqa: BLE001
                self._ax_fail("signals")

    def _ax_ti_safe(self, chat_id: int, tok: str) -> bool:
        if not tok or tok.lower() in self.mem_protect:
            return False
        book = self._lbook(chat_id, create=False)
        return not (book and tok in (book.get("okc") or {}))

    def _ax_signals(self, msg, chat, a, tier: str, now: float) -> None:
        sig, cid, uid = a.signals, msg.chat_id, msg.user_id
        rec = chat.users.get(uid)
        vouched = bool(rec and rec.vouched)
        if self._ax_on("ti") and not vouched and tier != "veteran":
            exact, sim, ntok = a.fp
            if sim and ntok >= 5 and self.ti_sim.find(sim) is not None:
                sig.append(("ax_ti", 3.2, "шаблон уже известен по общей базе угроз"))
            hit = [t for t in a.contacts if t in self.ti_ct and self._ax_ti_safe(cid, t)]
            if hit:
                sig.append(("ax_ti_ct", 2.6, "контакт из общей базы угроз: " + hit[0][:40]))
            if tier == "new" and uid in self.ti_uid:
                sig.append(("ax_xrep", 2.0, "уже забанен за спам в другом чате"))
        if self._ax_on("dissonance") and tier != "new" and not msg.edited:
            vec = ax_style_vec(msg.text)
            if vec is not None:
                prof = self._axm()["sty"].get(str(cid), {}).get(str(uid))
                score, hits = ax_dissonance(prof, vec, bool(a.urls or a.contacts))
                if score:
                    sig.append(("ax_dissonance", score, "резкая смена почерка у давнего участника: " + ", ".join(hits)))

    # ───────── после проверки ─────────
    def _learn_post(self, msg, v, la, now: float) -> None:
        super()._learn_post(msg, v, la, now)
        if self.ax_on:
            self._axg("post", self._ax_post, msg, v, la, now)

    def _ax_post(self, msg, v, la, now: float) -> None:
        ana, tier, strict, chat, rec = la
        cid, uid = msg.chat_id, msg.user_id
        cfg = chat.cfg
        if not msg.edited and uid > 0:                               # 1) почерк участника
            vec = ax_style_vec(msg.text)
            if vec is not None and v.ok:
                sty = self._axm()["sty"].setdefault(str(cid), {})
                sty[str(uid)] = ax_style_update(sty.get(str(uid)), vec, bool(ana.urls or ana.contacts), now)
                self._sty_n += 1
                if self._sty_n % 400 == 0:
                    self.store.dirty = True
        strong = (v.ban or v.delete) and v.category in ("scam", "scam_ban") and v.score >= STRONG_SCAM
        if strong and tier == "new" and uid > 0:                     # 2) ретро-обучение и общая база угроз
            if self._ax_on("hindsight"):
                self._ax_hind.append((cid, uid, now))
            if (self._ax_on("ti") and (v.ban or ana.hard >= LP_AUTO_HARD) and not msg.edited
                    and not str(ana.lhit).startswith("ham")):
                self._ax_ti_confirm(cid, msg, ana, v, now)
            if v.ban and self._ax_on("ti") and not msg.edited:
                self.ti_uid[uid] = now
                self.ax_q["ti"].append(("uid", str(uid), now))
        if self._ax_on("dissonance") and tier != "new" and v.ok and not msg.edited and uid > 0:
            dis = sum(w for n, w, _ in ana.signals if n == "ax_dissonance")
            static = ana.raw - sum(w for n, w, _ in ana.signals if n.startswith("ax_"))
            if dis >= 2.2 and static >= 1.0 and ana.contacts:         # «взломали ветерана»: почерк сменился + сам текст подозрителен
                v.delete, v.category, v.alert = True, "scam", True
                v.mute_s = 1800 if (dis >= 3.0 or static >= 2.0) else 0
                v.score = max(v.score, round(dis + static, 2))
                v.reasons = list(v.reasons) + ["похоже на взлом аккаунта: давний участник резко сменил почерк и дал ссылку/контакт"]
                if v.mute_s and rec is not None:
                    rec.muted_until = max(rec.muted_until, now + v.mute_s)
                self.radar_note(cid, uid, "scam", now)
                self.ax_count(cid, "hacked", now=now)
                self.store.dirty = True
        if (self._ax_on("autoham") and v.ok and tier in ("member", "veteran") and not msg.edited and ana.lf is not None
                and (ana.lf["sk"] or ana.lf["sim"]) and ana.raw >= 1.2 and not ana.contacts and not ana.urls
                and cfg.learn and cfg.scam):                         # 3) тихое одобрение: подозрительное, но прошло
            self._ax_hamq.append((now + AX_HAM_AFTER, cid, msg.msg_id, uid, now))
        if (self._ax_on("cohort") and tier == "new" and rec is not None and rec.clean == 0 and not msg.edited
                and (ana.urls or ana.contacts) and now - (rec.joined or rec.first_seen) <= 60):
            self.ap_pulse(cid, uid, "firstpost", now=now)             # 4) ссылка в первую минуту после входа

    def _ax_ti_vote(self, kind: str, key: str, uid: int, now: float) -> bool:
        """Запись попадает в общую базу только когда её подтвердили ДВА РАЗНЫХ забаненных аккаунта (защита от отравления)."""
        ent = self._ti_pend.setdefault((kind, key), [set(), now])
        ent[0].add(uid)
        ent[1] = now
        if len(self._ti_pend) > 2000:
            for k in [k for k, e in self._ti_pend.items() if now - e[1] > 86400][:500]:
                self._ti_pend.pop(k, None)
        return len(ent[0]) >= 2

    def _ax_ti_confirm(self, cid: int, msg, ana, v, now: float) -> None:
        uid = msg.user_id
        sim = ana.fp[1] if ana.fp[2] >= 5 else 0
        if sim and not self._collateral(cid, sim, uid, now) and self.ti_sim.find(sim) is None and self._ax_ti_vote("sim", format(sim, "x"), uid, now):
            self.ti_sim.add(sim, now)
            self.ax_q["ti"].append(("sim", format(sim, "x"), now))
        for t in list(ana.contacts)[:4]:
            if (_AX_TI_TOKEN.match(t) and t not in self.ti_ct and self._ax_ti_safe(cid, t)
                    and self._ax_ti_vote("ct", t, uid, now)):
                self.ti_ct[t] = now
                self.ax_q["ti"].append(("ct", t, now))

    # ───────── приток: z-оценка скорости и когорты свежих аккаунтов ─────────
    def ax_join(self, chat_id: int, uid: int, now: float | None = None) -> None:
        if self._ax_on("cohort"):
            self._axg("cohort", self._ax_join, chat_id, uid, self.clock() if now is None else now)

    def _ax_join(self, cid: int, uid: int, now: float) -> None:
        dq = self._axj.setdefault(cid, deque(maxlen=120))
        dq.append((now, uid))
        bucket = int(now // 120)
        b = self._axjb.get(cid)
        if b is None:
            saved = self._ax_c(cid).get("jb") or [0.3, 0.3]
            b = self._axjb[cid] = {"mean": float(saved[0]), "var": float(saved[1]), "cur": bucket, "n": 0}
        if bucket > b["cur"]:
            al, x = 0.03, b["n"]
            d = x - b["mean"]
            b["mean"] += al * d
            b["var"] = (1 - al) * (b["var"] + al * d * d)
            gap = min(bucket - b["cur"] - 1, 720)
            if gap:
                f = (1 - al) ** gap
                b["mean"] *= f
                b["var"] *= f
            b["cur"], b["n"] = bucket, 0
            self._ax_c(cid)["jb"] = [round(b["mean"], 3), round(b["var"], 3)]
        b["n"] += 1
        recent = [(t, u) for t, u in dq if now - t <= 120]
        n2 = len(recent)
        z = (n2 - b["mean"]) / math.sqrt(b["var"] + b["mean"] + 0.5)
        fired = self._axj_fired.setdefault(cid, {})
        for u in [u for u, t in fired.items() if now - t > 900]:
            fired.pop(u, None)
        if n2 >= 5 and z >= 3.0 and not self.raid_active(cid, now):
            for t, u in recent:
                if u not in fired:
                    fired[u] = now
                    self.ap_pulse(cid, u, "raid_early", now=now)
        ids = sorted(u for t, u in dq if now - t <= 300 and u > 0)
        best, bi, j = 0, 0, 0                                         # самое плотное скопление id (разброс ≤ 0,4%)
        for i in range(len(ids)):
            j = max(j, i)
            while j + 1 < len(ids) and (ids[j + 1] - ids[i]) / ids[j + 1] <= 0.004:
                j += 1
            if j - i + 1 > best:
                best, bi = j - i + 1, i
        if best >= 5:
            cl = ids[bi:bi + best]
            st = self.store.chats.get(cid)
            known = sorted(u for u, r in (st.users.items() if st else ()) if r.clean >= 5 and u > 0 and u not in cl)
            ref = known[int(len(known) * 0.7)] if len(known) >= 30 else 0
            if ref == 0 or cl[0] >= ref:                              # и все они «моложе» большинства старожилов чата
                for u in cl:
                    if ("c", u) not in fired:
                        fired[("c", u)] = now
                        self.ap_pulse(cid, u, "cohort", now=now)
                if ("cohort", cid) not in fired or now - fired[("cohort", cid)] > 900:
                    fired[("cohort", cid)] = now
                    self.ax_out.append(("note", cid, "когорта свежих аккаунтов: %d входов подряд с почти одинаковыми id" % best))

    # ───────── реакции как радар ─────────
    def ax_react(self, chat_id: int, mid: int, reactor: int, emojis: set, now: float | None = None) -> None:
        if not self._ax_on("reactions") or not emojis:
            return
        self._axg("reactions", self._ax_react, chat_id, mid, reactor, emojis, self.clock() if now is None else now)

    def _ax_react(self, cid: int, mid: int, rid: int, emojis: set, now: float) -> None:
        ent = self._lpc.get((cid, mid))
        if not ent or not (emojis & (LP_REACT_SPAM | LP_REACT_BAN)):
            return
        target = ent["uid"]
        if target <= 0 or rid == target:
            return
        d = self._axr.setdefault((cid, target), {})
        d[rid] = now
        for u in [u for u, t in d.items() if now - t > 600]:
            d.pop(u, None)
        if len(d) >= 3 and now - self._axr_fire.get((cid, target), 0) > 900:
            self._axr_fire[(cid, target)] = now
            kind = "crowd" if ent.get("tier") == "new" else "heat"
            for u in d:
                self.ap_pulse(cid, u, kind, 0.6, now)

    # ───────── автопилот: множители, прогноз, форма угрозы, предохранитель ─────────
    def ap_mult(self, cfg, now: float) -> tuple:
        m, hold, why = super().ap_mult(cfg, now)
        if self.ax_on and AX_FEATS["tune"]:
            cid = self._ax_cid(cfg)
            k = float(self._ax_c(cid).get("k", 1.0)) if cid else 1.0
            if k != 1.0:
                m = max(AP_MULT_MIN, min(AP_MULT_MAX, m * k))
                why = list(why) + ["автонастройка ×%.2f" % k]
        return m, hold, why

    def _ax_fc_slot(self, now: float) -> int:
        return int(((now + self.ap_tz_h * 3600) // 3600) % 168)

    def ax_fc_tick(self, chat_id: int, now: float) -> None:
        slot = self._ax_fc_slot(now)
        prev = self._ax_slot.get(chat_id)
        if prev is None:
            self._ax_slot[chat_id] = slot
            return
        if slot == prev:
            return
        c = self._ax_c(chat_id)
        fc = c.get("fc")
        if not isinstance(fc, list) or len(fc) != 168:
            fc = c["fc"] = [0.0] * 168
        acc = self._ax_acc.pop(chat_id, 0.0)
        fc[prev] = round(0.75 * fc[prev] + 0.25 * acc if c.get("fcn", 0) >= 168 else max(fc[prev], acc), 3)
        c["fcn"] = c.get("fcn", 0) + 1
        self._ax_slot[chat_id] = slot
        self.store.dirty = True

    def ax_forecast(self, chat_id: int, now: float) -> tuple:
        """→ (множитель порогов, пояснение, ожидаемый риск сейчас, пик ближайших 6 часов или None)."""
        c = self._ax_c(chat_id)
        fc = c.get("fc")
        if not isinstance(fc, list) or len(fc) != 168 or c.get("fcn", 0) < 168:
            return 1.0, "", 0.0, None
        slot = self._ax_fc_slot(now)
        nxt = fc[(slot + 1) % 168] if (now % 3600) >= 3000 else 0.0     # за 10 минут до «опасного» часа
        cur = max(fc[slot], nxt)
        mean = sum(fc) / 168.0
        rel = cur / max(0.8, mean)
        peak = max(range(6), key=lambda i: fc[(slot + i) % 168])
        peak_info = (peak, fc[(slot + peak) % 168]) if fc[(slot + peak) % 168] >= 1.5 else None
        if cur >= 1.5 and rel >= 4.0:
            return 0.85, "прогноз: в этот час обычно тяжело", cur, peak_info
        if cur >= 1.5 and rel >= 2.5:
            return 0.9, "прогноз: час повышенного риска", cur, peak_info
        return 1.0, "", cur, peak_info

    def ax_shape(self, chat_id: int, reflex: str, now: float) -> dict:
        spec = AP_REFLEXES[reflex]
        per: dict = {}
        hard = soft = 0.0
        for ts, who, w, kind in self._axev.get(chat_id, ()):
            age = now - ts
            if age < 0 or age > RADAR_WINDOW or kind not in spec["hard"] | spec["soft"]:
                continue
            x = w * 0.5 ** (age / RADAR_HALF)
            per[who] = per.get(who, 0.0) + x
            if kind in spec["hard"]:
                hard += x
            else:
                soft += x
        tot = sum(per.values())
        return {"total": tot, "actors": sum(1 for s in per.values() if s >= RADAR_ACTOR_MIN),
                "top": (max(per.values()) / tot) if tot > 0 else 0.0, "hard": (hard / (hard + soft)) if hard + soft > 0 else 0.0}

    def ap_hidden(self, chat_id, cfg, reflex, s, score, actors, now, cur) -> tuple:
        m, h, nk, keep, why = super().ap_hidden(chat_id, cfg, reflex, s, score, actors, now, cur)
        if not (self.ax_on and self.ap_brain):
            return m, h, nk, keep, why
        try:
            m2, h2, w2 = 1.0, 1.0, []
            if AX_FEATS["forecast"]:
                f, fw, _cur, _pk = self.ax_forecast(chat_id, now)
                if f != 1.0:
                    m2 *= f
                    w2.append(fw)
            if AX_FEATS["shape"] and score >= 0.8:
                sh = self.ax_shape(chat_id, reflex, now)
                s1 = AP_TRIP[reflex][0][0]
                if reflex in ("wave", "fakes", "noise", "adult", "heat") and cur == 0 and sh["actors"] <= 2 and sh["top"] >= 0.75 and score < 1.6 * s1:
                    m2 *= 1.2
                    w2.append("локальная угроза: бью по нарушителю, не по всему чату")
                elif sh["hard"] < 0.3 and sh["total"] > 0:
                    m2 *= 1.1
                    w2.append("мало прямых улик")
                elif sh["actors"] >= 6 and sh["hard"] >= 0.6:
                    m2 *= 0.9
                    w2.append("массовая и уверенная")
            if AX_FEATS["fuse"] and cur == 0 and float(self._ax_c(chat_id).get("fu", 0)) > now:
                m2 *= 1.35
                w2.append("предохранитель")
            if m2 != 1.0 or h2 != 1.0:
                m = _clamp(m * m2, AP_HID_MIN, AP_HID_MAX)
                h = _clamp(h * h2, AP_HID_HOLD_MIN, AP_HID_HOLD_MAX)
                why = list(why) + w2
        except Exception:                                            # noqa: BLE001
            self._ax_fail("hidden")
        return m, h, nk, keep, why

    def ap_vec_hot(self, chat_id: int, now: float, need: int = AP_VEC_SRC) -> list:
        if self._ax_on("shape"):
            st = self.store.chats.get(chat_id)
            if st is not None and any(isinstance(s, dict) and _ap_lvl(s) >= 2 and s.get("vec")
                                      for r, s in st.cfg.ap_state.items() if r in AP_REFLEXES):
                need = max(2, need - 1)                              # атакующие сменили тактику: замок ставим по 2 источникам
        return super().ap_vec_hot(chat_id, now, need)

    def _ap_overrides(self, chat_id: int, cfg, now: float, trans: list) -> bool:
        cut = []
        if self._ax_on("doubt"):
            for key, applied in list(cfg.ap_applied.items()):
                cur = getattr(cfg, key, None)
                if cur is None or _ap_eq(key, cur, applied) or _ap_eq(key, ap_merge(key, cur, applied), cur):
                    continue
                cfg.ap_applied.pop(key, None)                         # владелец вернул именно эту меру: рефлекс не рушим,
                cfg.ap_before.pop(key, None)                          # а саму меру на время не трогаем
                self._ax_c(chat_id).setdefault("md", {})[key] = now + AP_OVERRIDE_COOL
                self.ap_note(chat_id, now, f"{key}: владелец вернул — эту меру не трогаю {human_dur(AP_OVERRIDE_COOL)}, остальные держу")
                self._ax_over.setdefault(chat_id, deque(maxlen=20)).append(now)
                self.ax_count(chat_id, "doubt", now=now)
                self._axg("fuse", self.ax_fuse_note, chat_id, now, "owner")
                cut.append(key)
        return super()._ap_overrides(chat_id, cfg, now, trans) or bool(cut)

    def ap_desired(self, cfg, levels: dict, calm: bool) -> dict:
        des = super().ap_desired(cfg, levels, calm)
        if self.ax_on:
            cid = self._ax_cid(cfg)
            md = self._ax_c(cid).get("md") if cid else None
            if md:
                now = self.clock()
                for key in [k for k, u in md.items() if u <= now]:
                    md.pop(key, None)
                for key in [k for k in des if k in md]:
                    des.pop(key, None)
        return des

    def ax_fuse_note(self, chat_id: int, now: float, why: str) -> None:
        if not AX_FEATS["fuse"]:
            return
        c = self._ax_c(chat_id)
        ev = [t for t in c.get("fuse", []) if now - t < 3 * 3600] + [now]
        c["fuse"] = ev[-8:]
        if len(ev) >= 3 and float(c.get("fu", 0)) <= now:
            c["fu"] = now + 3 * 3600
            self.ax_count(chat_id, "fuse", now=now)
            self.ax_out.append(("fuse", chat_id, why))
        self.store.dirty = True

    # ───────── шаг автопилота: слепота, обкатка, эпизоды, эффективность, разбор полётов ─────────
    def ap_step(self, chat_id: int, now: float | None = None):
        if not self.ax_on:
            return super().ap_step(chat_id, now)
        now = self.clock() if now is None else now
        st = self.store.chats.get(chat_id)
        if st is None or self._ax_c(chat_id).get("off"):
            return super().ap_step(chat_id, now)
        saved = self.ap_calm_after
        if chat_id in self.ax_blind:
            self.ap_calm_after = 0.0                                  # не видим чат — тишину спокойствием не считаем
        try:
            if AX_FEATS["shadow"] and float(self._ax_c(chat_id).get("sh", 0)) > now:
                rep = self._ax_shadow_step(chat_id, st, now)
            else:
                self._ax_sh.pop(chat_id, None)
                rep = super().ap_step(chat_id, now)
        finally:
            self.ap_calm_after = saved
        self._axg("after_step", self._ax_after_step, chat_id, st, rep, now)
        return rep

    def _ax_shadow_step(self, chat_id: int, st, now: float):
        """«Теневой автопилот»: решения считаются на копии настроек, в чате ничего не меняется; записывается, что бы он сделал."""
        sh = self._ax_sh.get(chat_id)
        real = st.cfg
        if sh is None:
            clone = copy.deepcopy(real)
            for f in ("ap_state", "ap_before", "ap_applied", "ap_cool"):
                setattr(clone, f, {})
            sh = self._ax_sh[chat_id] = {"cfg": clone, "rearm": {}, "after": {}, "log": deque(maxlen=60)}
        clone = sh["cfg"]
        for f in fields(ChatCfg):                                     # настройки владельца подтягиваем, кроме тех, что «сделал» теневой автопилот
            if not f.name.startswith("ap_") and f.name not in clone.ap_applied:
                setattr(clone, f.name, copy.deepcopy(getattr(real, f.name)))
        for r, t in sh["rearm"].items():
            self.ap_rearm[(chat_id, r)] = t
        for r, t in sh["after"].items():
            self.ap_after[(chat_id, r)] = t
        log0 = list(self.ap_log.get(chat_id, ()))
        dbg0 = list(self.ap_dbg.get(chat_id, ()))
        n_ev = len(self.events)
        hot0 = {k: v for k, v in self.ap_hot.items() if k[0] == chat_id}
        st.cfg = clone
        try:
            rep = super().ap_step(chat_id, now)
        finally:
            st.cfg = real
        sh["rearm"] = {k[1]: self.ap_rearm.pop(k) for k in [k for k in self.ap_rearm if k[0] == chat_id]}
        sh["after"] = {k[1]: self.ap_after.pop(k) for k in [k for k in self.ap_after if k[0] == chat_id]}
        for k in [k for k in self.ap_hot if k[0] == chat_id]:
            self.ap_hot.pop(k, None)
        self.ap_hot.update(hot0)
        new_notes = [t for ts, t in list(self.ap_log.get(chat_id, ()))[len(log0):]] if len(log0) < AP_NOTES_KEEP else []
        if chat_id in self.ap_log:
            self.ap_log[chat_id].clear()
            self.ap_log[chat_id].extend(log0)
        if chat_id in self.ap_dbg:
            self.ap_dbg[chat_id].clear()
            self.ap_dbg[chat_id].extend(dbg0)
        del self.events[n_ev:]
        for text in new_notes:
            sh["log"].append((now, text))
        if rep and rep.get("trans") and not new_notes:
            for reflex, old, new, why, score, actors in rep["trans"]:
                sh["log"].append((now, self._ap_note_text(reflex, old, new, why, score, actors)))
        return None                                                   # наружу ничего не уходит: ни событий, ни оповещений

    def _ax_after_step(self, chat_id: int, st, rep, now: float) -> None:
        cfg = st.cfg
        if self._ax_on("forecast"):
            self.ax_fc_tick(chat_id, now)
        lvls = {r: _ap_lvl(s) for r, s in cfg.ap_state.items() if r in AP_REFLEXES and isinstance(s, dict)}
        top = max(lvls.values(), default=0)
        if rep and rep.get("trans"):
            for reflex, old, new, why, score, actors in rep["trans"]:
                self.ax_q["aphist"].append((now, chat_id, reflex, old, new, float(score), int(actors), str(why)[:120]))
                if why == AP_OWNER_WHY:
                    self._ax_over.setdefault(chat_id, deque(maxlen=20)).append(now)
                if reflex in AP_REFLEXES and new > old:                     # замер: помогла ли мера (через ~4 мин)
                    self._ax_effq.append((now + 270, chat_id, reflex, new, self._ax_rate(chat_id, reflex, now - 240, now)))
                if reflex in AP_REFLEXES and new == 0 and why == "done" and int(score) >= 2 and self._ax_on("debrief"):
                    self.ax_out.append(("debrief", chat_id, self._ax_debrief(chat_id, reflex, int(score), int(actors), now, rep)))
            if self._ax_on("combo") and lvls.get("wave", 0) >= 2 and lvls.get("raid", 0) >= 2 and not self.strict_active(chat_id, now):
                for ev in reversed(self.events):
                    if ev.get("kind") == "ap" and ev.get("chat") == chat_id:
                        if not ev.get("strict"):
                            ev["strict"] = True
                            self.ap_note(chat_id, now, "волна и наплыв вместе: включаю строгий режим")
                        break
        for item in [e for e in self._ax_effq if e[0] <= now]:
            self._ax_effq.remove(item)
            _, cid, reflex, lvl, before = item
            if before >= 1.0:
                after = self._ax_rate(cid, reflex, item[0] - 240 + 30, item[0])
                e = self._ax_c(cid).setdefault("eff", {}).setdefault("%s:%d" % (reflex, lvl), [0.0, 0])
                drop = max(-1.0, min(1.0, 1.0 - after / before))
                e[0] = round(drop if e[1] == 0 else 0.7 * e[0] + 0.3 * drop, 3)
                e[1] += 1
        self._ax_episode(chat_id, st, lvls, top, now)

    def _ax_rate(self, chat_id: int, reflex: str, t0: float, t1: float) -> float:
        kinds = AP_REFLEXES[reflex]["hard"]
        return sum(w for ts, who, w, kind in self._axev.get(chat_id, ()) if t0 <= ts <= t1 and kind in kinds)

    def _ax_debrief(self, chat_id: int, reflex: str, peak: int, dur: int, now: float, rep: dict) -> dict:
        t0 = now - dur - 60
        kinds = AP_REFLEXES[reflex]["hard"] | AP_REFLEXES[reflex]["soft"]
        evs = [e for e in self._axev.get(chat_id, ()) if e[0] >= t0 and e[3] in kinds]
        by: dict = {}
        for ts, who, w, kind in evs:
            by.setdefault(kind, set()).add(who)
        eff = self._ax_c(chat_id).get("eff", {}).get("%s:%d" % (reflex, peak))
        return {"reflex": reflex, "peak": peak, "dur": dur, "actors": len({e[1] for e in evs}), "events": len(evs),
                "kinds": {k: len(v) for k, v in by.items()}, "changes": [str(c) for c in (rep.get("changes") or ())][:6],
                "eff": eff, "over": bool(self._ax_over.get(chat_id) and now - self._ax_over[chat_id][-1] <= dur + 60)}

    # ───────── эпизоды → архив следов для лаборатории ─────────
    def _ax_heat(self, chat_id: int, now: float) -> float:
        dq = self._axev.get(chat_id)
        if not dq or now - dq[-1][0] > RADAR_WINDOW:
            return 0.0
        best = 0.0
        for reflex in AP_REFLEXES:
            score, actors = self.ap_score(chat_id, reflex, now, False)
            best = max(best, score / AP_TRIP[reflex][0][0])
        return best

    def _ax_episode(self, chat_id: int, st, lvls: dict, top: int, now: float) -> None:
        if not self._ax_on("tune"):
            return
        ratio = self._ax_heat(chat_id, now)
        ep = self._axep.get(chat_id)
        if ep is None:
            if ratio >= 0.3:
                self._axep[chat_id] = {"t0": now, "peak": ratio, "cool": 0.0, "last": now, "reach": top}
            return
        ep["peak"], ep["reach"] = max(ep["peak"], ratio), max(ep["reach"], top)
        ep["cool"] = ep["cool"] + (now - ep["last"]) if ratio < 0.12 else 0.0
        ep["last"] = now
        if ep["cool"] < 300 and now - ep["t0"] < 7200:
            return
        self._axep.pop(chat_id, None)
        evs = [e for e in self._axev.get(chat_id, ()) if ep["t0"] - 90 <= e[0] <= now][-400:]
        if not evs:
            return
        t0 = evs[0][0]
        idx: dict = {}
        rel = [[round(ts - t0, 1), idx.setdefault(who, len(idx)), round(w, 2), kind] for ts, who, w, kind in evs]
        hard = [e for e in evs if e[3] in _AX_HARD_ALL]
        actors = len({e[1] for e in hard})
        over = any(ep["t0"] - 60 <= t <= now for t in self._ax_over.get(chat_id, ()))
        label = "false" if over else "attack" if (actors >= 2 and sum(e[2] for e in hard) >= 3.0) else "quiet"
        self.ax_q["traces"].append((chat_id, t0, now, label, round(ep["peak"], 2), rel))

    # ───────── самостоятельное обучение: ретро-уроки, решения по карточкам, тихое одобрение ─────────
    def ax_tick(self, now: float) -> None:
        """Раз в несколько секунд. Всё синхронное; то, что требует Telegram, кладётся в ax_out."""
        if not self.ax_on:
            return
        self._axg("hindsight", self._ax_run_hindsight, now)
        self._axg("autoham", self._ax_run_ham, now)
        if now - self._ax_last_card >= 30:
            self._ax_last_card = now
            self._axg("cards", self._ax_run_cards, now)

    def _ax_day_used(self, chat_id: int, key: str, now: float) -> int:
        dd = self._ax_c(chat_id).get("dd") or {}
        return int(dd.get(key, 0)) if dd.get("_d") == self.store.day(now) else 0

    def _ax_run_hindsight(self, now: float) -> None:
        """Бот сам забанил спамера → его ЕЩЁ не пойманные ранние сообщения становятся уроками (то, что бот пропустил).
        Сообщение с признаками подозрительности учится сразу; совсем «чистая» наживка — только по кворуму: такой же
        текст раньше писали минимум ДВА разных забаненных аккаунта (так безобидная фраза не усваивается как спам)."""
        done = 0
        while self._ax_hind and done < 4:
            cid, uid, t = self._ax_hind.popleft()
            done += 1
            if not self.lp_on or not self.learn_on:
                continue
            taught = 0
            for mid in reversed(list(self._lpu.get((cid, uid), ()))):
                e = self._lpc.get((cid, mid))
                if not e or not e.get("alive") or e.get("lesson") or e.get("tier") != "new" or now - e["t"] > LP_IMPL_WINDOW:
                    continue
                f = e["f"]
                if (e["raw"] >= 0.8 or e["ct"] or e["urls"]) and (f["sk"] or f["sim"] or e["ct"]):
                    batch = [(cid, mid)]
                elif f["sim"] and len(f["sk"]) >= 6:
                    batch = self._ax_quorum(cid, mid, uid, f["sim"], now)
                else:
                    continue
                for c2, m2 in batch:
                    e2 = self._lpc.get((c2, m2))
                    if not e2 or e2.get("lesson") or taught >= 3:
                        continue
                    res = self.lp_teach(c2, m2, "s", 0, "ax", now, kind="del")
                    if res.get("ok"):
                        res["ban"], res["unmute"] = [], []             # автономно только учимся и чистим, не банимся
                        self.ax_out.append(("learn_apply", res, "ретро"))
                        self.ax_count(c2, "hind", now=now)
                        self._ax_src("hind")
                        taught += 1
                if taught >= 3:
                    break

    def _ax_quorum(self, cid: int, mid: int, uid: int, sim: int, now: float) -> list:
        pend = self._ax_hs_pend
        for p in [p for p in pend if now - p["t"] > 21600]:
            pend.remove(p)
        hit = next((p for p in pend if (p["sim"] ^ sim).bit_count() <= 8), None)
        if hit is None:
            pend.append({"sim": sim, "uids": {uid}, "mids": [(cid, mid)], "t": now})
            del pend[:-200]
            return []
        if uid in hit["uids"]:
            return []
        hit["uids"].add(uid)
        hit["mids"].append((cid, mid))
        hit["t"] = now
        if len(hit["uids"]) < 2:
            return []
        pend.remove(hit)
        return hit["mids"][:3]

    def _ax_run_ham(self, now: float) -> None:
        while self._ax_hamq and self._ax_hamq[0][0] <= now:
            _due, cid, mid, uid, t0 = self._ax_hamq.popleft()
            st = self.store.chats.get(cid)
            e = self._lpc.get((cid, mid))
            rec = st.users.get(uid) if st else None
            if st is None or e is None or rec is None or rec.banned or rec.muted_until > now or not e.get("alive") or e.get("lesson"):
                continue
            if any(s >= t0 - 60 for s in rec.strikes if isinstance(s, (int, float))):
                continue                                              # за это время автора наказывали — не «нормально»
            if self._ax_day_used(cid, "ham", now) >= 40:
                continue
            f = e["f"]
            if self._lmatch(self._L()["g"]["spam"], {"sk": f["sk"], "sim": f["sim"]})[1] >= 2:
                continue                                              # похоже на известный спам — не учим как «нормально»
            book = self._lbook(cid)
            pid, new = self._add_pattern(book["ham"], {"sk": f["sk"], "sim": f["sim"]}, LEARN_HAM_MAX, now, 0, "авто-ок")
            if pid:
                if len(f["bh"]) >= 3:
                    self._bayes_add_ham(book, f["bh"], 1.0)
                self._lcount(cid, "auto_ham", now)
                self.ax_count(cid, "ham", now=now)
                self._ax_src("ham")

    def _ax_run_cards(self, now: float) -> None:
        """Карточки «спам / нормально», на которые владелец долго не отвечает, решаются сами — но только при явных уликах."""
        cards = self._L()["cards"]
        for card_id, c in list(cards.items()):
            if c.get("done") or c.get("src") or c.get("kind") not in ("keep", "del"):
                continue
            age = now - c["t"]
            if age < AX_CARD_WAIT or age > LEARN_CARD_TTL:
                continue
            cid, uid = c["cid"], c["uid"]
            st = self.store.chats.get(cid)
            rec = st.users.get(uid) if st else None
            if st is None or self._ax_day_used(cid, "cards", now) >= AX_CARD_DAILY:
                continue
            eff, tier, ct = float(c.get("eff", 0)), c.get("tier", "new"), c.get("ct") or []
            act = ""
            if tier == "new" and not (rec and rec.vouched):
                banned = bool(rec and (rec.banned or rec.muted_until > now))
                if (c["kind"] == "del" and (eff >= 0.8 * STRONG_SCAM or (ct and eff >= 3.5))) or (banned and eff >= 3.0) or eff >= STRONG_SCAM:
                    act = "s"
            elif tier in ("member", "veteran") and rec is not None and not ct and eff < 4.0 and rec.clean >= 30 and not rec.banned \
                    and not any(s >= now - 86400 for s in rec.strikes if isinstance(s, (int, float))):
                act = "h"
            if not act:
                continue
            res = self.learn_decide(card_id, act, 0, now)
            if not res.get("ok"):
                continue
            c["ax"] = 1
            res["ban"] = []
            self.ax_out.append(("learn_apply", res, "карточка"))
            dec = self._axm()["g"].setdefault("dec", [])
            dec.append([card_id, act, round(now), cid])
            del dec[:-40]
            self.ax_count(cid, "cards", now=now)
            self._ax_src("cards")

    # ───────── база угроз (локальная часть) ─────────
    def ax_ti_load(self, rows_by_kind: dict) -> None:
        for key, ts, n, src in rows_by_kind.get("sim", ()):
            with contextlib.suppress(ValueError):
                self.ti_sim.add(int(key, 16), ts)
        for key, ts, n, src in rows_by_kind.get("ct", ()):
            self.ti_ct[key] = ts
        for key, ts, n, src in rows_by_kind.get("fu", ()):
            self.ti_fu[key] = ts
        for key, ts, n, src in rows_by_kind.get("uid", ()):
            with contextlib.suppress(ValueError):
                self.ti_uid[int(key)] = ts

    def ax_ti_add(self, kind: str, key: str, ts: float) -> bool:
        """Принять запись из сети (Upstash). → True, если она новая."""
        if kind == "sim":
            try:
                s = int(key, 16)
            except ValueError:
                return False
            new = s not in self.ti_sim.items
            self.ti_sim.add(s, ts)
            return new
        book = {"ct": self.ti_ct, "fu": self.ti_fu}.get(kind)
        if kind == "uid":
            try:
                u = int(key)
            except ValueError:
                return False
            new = u not in self.ti_uid
            self.ti_uid[u] = ts
            return new
        if book is None or not key:
            return False
        if kind == "ct" and key.lower() in self.mem_protect:
            return False
        new = key not in book
        book[key] = ts
        return new

    def ax_ti_prune(self, now: float) -> None:
        cut = now - 45 * 86400
        self.ti_sim.prune(cut)
        for d in (self.ti_ct, self.ti_fu, self.ti_uid):
            for k in [k for k, t in d.items() if t < cut]:
                d.pop(k, None)
        for d_ in (self._axr_fire,):
            for k in [k for k, t in d_.items() if now - t > 3600]:
                d_.pop(k, None)
        for k in [k for k, d_ in self._axr.items() if not d_ or now - max(d_.values()) > 900]:
            self._axr.pop(k, None)
        for f_ in self._axj_fired.values():
            for k in [k for k, t in f_.items() if now - t > 3600]:
                f_.pop(k, None)
        sty = self._axm()["sty"]                                      # старые «почерки» тоже забываем
        for cid in list(sty):
            book = sty[cid]
            for u in [u for u, p in book.items() if now - p[0] > 60 * 86400]:
                book.pop(u, None)
            if len(book) > 30_000:
                for u in sorted(book, key=lambda u: book[u][0])[:len(book) - 30_000]:
                    book.pop(u, None)
            if not book:
                sty.pop(cid, None)

    # ───────── пояснения ─────────
    def ax_why_keys(self, cfg) -> list:
        """Происхождение изменений: какая мера включена каким рефлексом и почему всё ещё нужна."""
        out = []
        for key, val in cfg.ap_applied.items():
            who = [AP_REFLEXES[r]["icon"] + AP_LEVEL_NAME[_ap_lvl(s)] for r, s in cfg.ap_state.items()
                   if r in AP_REFLEXES and isinstance(s, dict) and _ap_lvl(s) > 0 and key in ap_want(r, _ap_lvl(s))]
            out.append((key, val, who))
        return out

    def ax_eff_text(self, chat_id: int, reflex: str, lvl: int) -> str:
        e = self._ax_c(chat_id).get("eff", {}).get("%s:%d" % (reflex, lvl))
        if not e or e[1] < 1:
            return ""
        return "обычно спад %+d%% за ~4 мин (по %d случ.)" % (round(e[0] * 100), e[1])


class EngineX(Cortex, Engine):
    """Движок + автономное ядро. Engine остаётся нетронутым (его можно по-прежнему использовать отдельно)."""



# ───────────────────────────── Sentinel: Telegram-сторона автономного ядра ─────────────────────────────
COMMAND_NAMES = tuple(COMMAND_NAMES) + tuple(n for n in ("brain", "vault") if n not in COMMAND_NAMES)


class _AxErrCounter(logging.Handler):
    """Считает ошибки по подсистемам (для самодиагностики). Ничего не печатает и не пишет на диск."""

    def __init__(self):
        super().__init__(level=logging.ERROR)
        self.recent: deque = deque(maxlen=600)

    def emit(self, record: logging.LogRecord) -> None:
        self.recent.append((time.time(), record.name))

    def top(self, since: float, n: int = 3) -> list:
        c = Counter(name for t, name in self.recent if t >= since)
        return c.most_common(n)


def _ax_fmt_k(k: float) -> str:
    return "×%.2f" % k


class Sentinel:
    """Надстройка Guard: исполняет решения Cortex в Telegram и следит за здоровьем. Подмешивается ПЕРЕД Guard."""

    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        self.up: Upstash = Upstash()
        self.vault: Vault | None = getattr(self.store, "vault", None)
        self._ax_t: dict = {}
        self._ax_led: dict = {}
        self._ax_alerted: dict = {}
        self._ax_last_tick = 0.0
        self._ax_lags: deque = deque(maxlen=20)
        self._ax_errc = _AxErrCounter()
        self._ax_fed: deque = deque(maxlen=40)
        self._ax_ti_retry: list = []
        self._ax_bk_commit = ""
        self._ax_token = secrets.token_hex(8)
        self._ax_leader = False
        self._ax_ready = False

    # ───────── запуск / остановка ─────────
    async def start(self) -> None:
        await super().start()
        if not self.eng.ax_on:
            return
        logging.getLogger().addHandler(self._ax_errc)
        try:
            await self.ax_start()
        except asyncio.CancelledError:
            raise
        except Exception:                                            # noqa: BLE001
            log_ax.exception("автономное ядро: запуск не полностью удался (бот работает как раньше)")
        self._ax_ready = True

    async def ax_start(self) -> None:
        eng, v = self.eng, self.vault
        if v is not None and v.ok:
            rows = {}
            cut = self.now() - 45 * 86400
            for kind in ("sim", "ct", "fu", "uid"):
                rows[kind] = await asyncio.to_thread(v.ti_load, kind, cut)
            eng.ax_ti_load(rows)
        bits = ["SQLite: %s" % ("да" if v is not None and v.ok else "нет"), "Upstash: %s" % ("да" if self.up.enabled else "нет"),
                "угроз в базе: шаблонов %d, контактов %d, файлов %d" % (len(eng.ti_sim), len(eng.ti_ct), len(eng.ti_fu))]
        log_ax.info("автономное ядро запущено · %s", " · ".join(bits))
        if self.up.enabled and _axf("GUARD_UPSTASH_LEADER", False):
            await self.ax_leader_wait()
        if v is not None and v.recovered:
            await self.alert(0, "⚠️ <b>SQLite-файл был повреждён</b> и пересоздан (старый сохранён как <code>%s</code>). "
                                "Состояние поднято из JSON и резервной копии; проверьте /vault." % esc(os.path.basename(v.recovered), 80))
        if getattr(self.store, "vault_lost", False):
            await self.alert(0, "🚨 <b>SQLite пуст, а JSON «тонкий»</b>: участники и самообучение не загружены (файл базы потерян?). "
                                "Если включён Upstash — остановите бота, удалите файлы состояния (JSON и .db) и запустите снова: "
                                "бот сам восстановится из облачной копии.")
        await self.ax_audit(self.now(), first=True)

    async def shutdown(self) -> None:
        try:
            if self.eng.ax_on:
                await self.ax_drain(self.now(), force=True)
                if self._ax_leader and self.up.enabled:
                    with contextlib.suppress(Exception):
                        if await self.up.acmd("GET", self.up.k("leader")) == self._ax_token:
                            await self.up.acmd("DEL", self.up.k("leader"))
        except Exception:                                            # noqa: BLE001
            log_ax.exception("автономное ядро: сбой при остановке")
        logging.getLogger().removeHandler(self._ax_errc)
        await super().shutdown()
        if self.vault is not None:
            self.vault.close()

    async def ax_leader_wait(self) -> None:
        """Замок деплоя: пока старый экземпляр бота не отпустит ключ, не лезем в чаты (не дольше 100 секунд)."""
        key = self.up.k("leader")
        t0 = time.time()
        while time.time() - t0 < 100:
            try:
                if await self.up.acmd("SET", key, self._ax_token, "NX", "EX", 240) == "OK":
                    self._ax_leader = True
                    return
            except Exception as e:                                   # noqa: BLE001
                log_ax.warning("замок деплоя недоступен (%s) — продолжаю без него", e)
                return
            await asyncio.sleep(5)
        log_ax.warning("предыдущий экземпляр не отпустил замок за 100 с — продолжаю")
        self._ax_leader = False

    # ───────── тик ─────────
    async def tick(self, now: float | None = None) -> None:
        now = self.now() if now is None else now
        await super().tick(now)
        if not (self.eng.ax_on and self._ax_ready):
            return
        try:
            await self.ax_tick(now)
        except asyncio.CancelledError:
            raise
        except Exception:                                            # noqa: BLE001
            log_ax.exception("автономное ядро: сбой тика (модерация не затронута)")

    def _due(self, name: str, every: float, now: float) -> bool:
        if now - self._ax_t.get(name, 0.0) >= every:
            self._ax_t[name] = now
            return True
        return False

    async def ax_tick(self, now: float) -> None:
        eng = self.eng
        last, self._ax_last_tick = self._ax_last_tick, now
        if last and now - last > 30:
            self._ax_lags.append((now, now - last))
        eng.ax_tick(now)
        await self.ax_drain(now)
        if self._due("heal", 60, now) and isinstance(self.store, VaultStore):
            self.store.heal(now)
        if self._due("ledger", 60, now):
            self.ax_counterfactual(now)
        if self._due("pull", _axn("GUARD_UPSTASH_PULL_MIN", 5) * 60, now):
            await self.ax_ti_pull(now)
        if self._due("leader", 90, now) and self._ax_leader and self.up.enabled:
            with contextlib.suppress(Exception):
                if await self.up.acmd("GET", self.up.k("leader")) == self._ax_token:
                    await self.up.acmd("EXPIRE", self.up.k("leader"), 240)
        if self._due("audit", 1800, now):
            await self.ax_audit(now)
        if self._due("backup", _axn("GUARD_UPSTASH_BACKUP_MIN", 60) * 60, now):
            await self.ax_backup(now)
        if self._due("maintain", 3600, now):
            await self.ax_maintain(now)
        if self._due("health", 600, now):
            await self.ax_health(now)
        h = int(((now + self.tz_h * 3600) % 86400) // 3600)
        day = self.store.day(now)
        if h == 4 and self._ax_t.get("lab_day") != day:
            self._ax_t["lab_day"] = day
            await self.ax_lab_all(now)
        if h == 21 and (now % 3600) >= 300 and self._ax_t.get("digest_day") != day:
            self._ax_t["digest_day"] = day
            await self.ax_digest(now)

    # ───────── выгрузка решений ядра ─────────
    async def ax_drain(self, now: float, force: bool = False) -> None:
        eng = self.eng
        out, eng.ax_out = eng.ax_out, []
        for item in out:
            try:
                kind = item[0]
                if kind == "learn_apply":
                    await self.learn_apply(item[1])
                elif kind == "note":
                    st = self.store.chats.get(item[1])
                    self.journal("ax", item[1], st.title if st else "", 0, "", item[2][:78])
                    await self.plus_log(item[1], "🧠 " + esc(item[2], 200))
                elif kind == "fuse":
                    st = self.store.chats.get(item[1])
                    await self.alert(item[1], "🧯 <b>%s</b>\nВладелец трижды за 3 часа отменял решения бота (%s). Включила предохранитель: "
                                              "на 3 часа автопилот не будет подниматься с нуля (уже включённое держится как раньше). "
                                              "Снять: /brain fuse reset в чате." % (esc(st.title if st else "", 60), esc(item[2], 20)))
                elif kind == "debrief":
                    await self.ax_send_debrief(item[1], item[2])
                elif kind == "breaker":
                    if self._once_per("breaker:" + item[1], 6 * 3600, now):
                        await self.alert(0, "🧠 Узел автономного ядра «%s» сбоил 5 раз за 10 минут — отключила его на 30 минут. "
                                            "Бот и модерация работают как обычно." % esc(item[1], 30))
            except asyncio.CancelledError:
                raise
            except Exception:                                        # noqa: BLE001
                log_ax.exception("не удалось выполнить решение ядра: %s", item[0] if item else "?")
        if force or self._due("persist", 15, now):
            await self.ax_persist(now)

    def _once_per(self, key: str, secs: float, now: float) -> bool:
        if now - self._ax_alerted.get(key, 0.0) >= secs:
            self._ax_alerted[key] = now
            return True
        return False

    async def ax_persist(self, now: float) -> None:
        q = self.eng.ax_q
        hist, q["aphist"] = q["aphist"], []
        traces, q["traces"] = q["traces"], []
        ti, q["ti"] = q["ti"], []
        led, q["ledger"] = q["ledger"], []
        v = self.vault
        if v is not None and v.ok:
            try:
                if hist:
                    await asyncio.to_thread(v.aphist_add, hist)
                for cid, t0, t1, label, peak, ev in traces:
                    await asyncio.to_thread(v.trace_add, cid, t0, t1, label, peak, ev)
                if ti:
                    await asyncio.to_thread(v.ti_put, [(k, key, ts, "local") for k, key, ts in ti])
                agg: dict = {}
                for d, c, k, n in led:
                    agg[(d, c, k)] = agg.get((d, c, k), 0) + n
                for (d, c, k), n in agg.items():
                    await asyncio.to_thread(v.ledger_add, d, c, k, n)
            except Exception:                                        # noqa: BLE001
                log_ax.exception("не удалось записать историю автономного ядра в SQLite")
        if (ti or self._ax_ti_retry) and self.up.enabled and AX_FEATS["ti"]:
            await self.ax_ti_push(ti + self._ax_ti_retry)

    # ───────── общая база угроз (Upstash) ─────────
    async def ax_ti_push(self, items: list) -> None:
        self._ax_ti_retry = []
        cmds = [["ZADD", self.up.k("ti", k), round(ts), key] for k, key, ts in items[:300]]
        try:
            if cmds:
                await self.up.apipe(cmds)
        except Exception as e:                                       # noqa: BLE001
            log_up.warning("база угроз: не отправилось (%s), повторю позже", e)
            self._ax_ti_retry = items[-300:]

    async def ax_ti_pull(self, now: float) -> None:
        if not (self.up.enabled and AX_FEATS["ti"]):
            return
        v, kinds = self.vault, ("sim", "ct", "fu", "uid")
        last = {}
        for k in kinds:
            try:
                last[k] = float(v.meta_get("ti_last:" + k, "0")) if v is not None and v.ok else 0.0
            except Exception:                                        # noqa: BLE001
                last[k] = 0.0
        try:
            res = await self.up.apipe([["ZRANGEBYSCORE", self.up.k("ti", k), "(%d" % last[k], "+inf", "WITHSCORES", "LIMIT", 0, 300]
                                       for k in kinds])
        except Exception as e:                                       # noqa: BLE001
            log_up.debug("база угроз: не удалось получить (%s)", e)
            return
        fresh, rows = 0, []
        for k, arr in zip(kinds, res):
            top = last[k]
            for i in range(0, len(arr or ()) - 1, 2):
                key, ts = str(arr[i]), float(arr[i + 1])
                top = max(top, ts)
                if self.eng.ax_ti_add(k, key, ts):
                    fresh += 1
                    rows.append((k, key, ts, "net"))
            if v is not None and v.ok and top > last[k]:
                with contextlib.suppress(Exception):
                    await asyncio.to_thread(v.meta_set, "ti_last:" + k, "%.0f" % top)
        if rows and v is not None and v.ok:
            with contextlib.suppress(Exception):
                await asyncio.to_thread(v.ti_put, rows)
        if fresh:
            self.eng.ax_count(0, "ti", fresh, now)
            log_ax.info("база угроз: получено новых записей %d", fresh)

    # ───────── резервная копия в Upstash ─────────
    def _ax_instance(self) -> str:
        return "bot%d" % self.me_id

    def _ax_blob(self) -> bytes:
        tmp = str(self.store.path) + ".bk.db"
        try:
            self.vault.backup_to(tmp)
            db = Path(tmp).read_bytes()
        finally:
            with contextlib.suppress(OSError):
                os.unlink(tmp)
        core = Path(self.store.path).read_bytes() if Path(self.store.path).exists() else b"{}"
        return ax_pack_backup(core, db)

    async def ax_backup(self, now: float) -> None:
        v = self.vault
        if v is None or not v.ok:
            return
        with contextlib.suppress(Exception):                          # локальная копия SQLite рядом с файлом
            await asyncio.to_thread(v.backup_to, str(v.path) + ".bak")
        if not self.up.enabled:
            return
        try:
            commit = await asyncio.to_thread(v.meta_get, "commit_t", "")
            if commit and commit == self._ax_bk_commit:
                return
            await self.store.flush(force=True)
            blob = await asyncio.to_thread(self._ax_blob)
            if len(blob) > _axn("GUARD_UPSTASH_MAX_MB", 8) * 1_000_000:
                if self._once_per("bk_big", 86400, now):
                    await self.alert(0, "☁️ Резервная копия в Upstash пропущена: %.1f МБ больше лимита %d МБ "
                                        "(GUARD_UPSTASH_MAX_MB)." % (len(blob) / 1e6, _axn("GUARD_UPSTASH_MAX_MB", 8)))
                return
            meta = await asyncio.to_thread(self.up.backup_put, self._ax_instance(), blob, {"ver": VERSION})
            self._ax_bk_commit = commit
            log_up.info("резервная копия в Upstash: %.0f КБ", meta["size"] / 1024)
        except Exception as e:                                       # noqa: BLE001
            log_up.warning("резервная копия в Upstash не получилась: %s", e)

    # ───────── обслуживание ─────────
    async def ax_maintain(self, now: float) -> None:
        eng = self.eng
        eng.ax_ti_prune(now)
        v = self.vault
        if v is not None and v.ok:
            try:
                r = await asyncio.to_thread(v.maintain, now)
                await asyncio.to_thread(lambda: v._q("PRAGMA wal_checkpoint(TRUNCATE)"))
                if any(r.values()):
                    log_vault.info("уборка SQLite: %s", ", ".join("%s −%d" % kv for kv in r.items() if kv[1]))
            except Exception:                                        # noqa: BLE001
                log_vault.exception("уборка SQLite не удалась")
        for uid, e in list(self.gbans().items()):                     # автоматические общие баны живут ограниченно
            if e.get("auto") and now - e.get("t", now) > AX_FED_TTL:
                self.gbans().pop(uid, None)
                for cid in e.get("ch", []):
                    await self.call("unban_chat_member", cid, int(uid), only_if_banned=True)
                self.journal("gban_del", 0, "", 0, str(uid), "срок авто-бана вышел")
                self.store.dirty = True
        if self.up.enabled and self._due("up_trim", 86400, now):
            with contextlib.suppress(Exception):
                await self.up.apipe([["ZREMRANGEBYSCORE", self.up.k("ti", k), "-inf", "(%d" % (now - 45 * 86400)]
                                     for k in ("sim", "ct", "fu", "uid")])

    async def ax_audit(self, now: float, first: bool = False) -> None:
        """Сверка прав: где бот «слепой» (не админ / не может удалять), там тишину нельзя считать спокойствием."""
        blind = set()
        for cid, st in list(self.store.chats.items()):
            if cid >= 0 or not st.active or not self.chat_ok(cid) or not st.cfg.enabled:
                continue
            try:
                r = await self.rights(cid)
            except Exception:                                        # noqa: BLE001
                continue
            if not r.get("admin") or not r.get("delete"):
                blind.add(cid)
                if AX_FEATS["audit"] and self._once_per("blind:%d" % cid, 86400, now):
                    await self.alert(cid, "👁 <b>%s</b>\nУ бота нет прав %s — защита здесь «слепая». Автопилот не будет считать тишину "
                                          "спокойствием. Выдайте права администратора (удаление сообщений, блокировка)." %
                                     (esc(st.title, 60), "администратора" if not r.get("admin") else "удалять сообщения"))
            await asyncio.sleep(0.05)
        self.eng.ax_blind = blind

    async def ax_health(self, now: float) -> None:
        """Самодиагностика: отставание цикла, всплеск ошибок."""
        lags = [d for t, d in self._ax_lags if now - t < 600]
        if len(lags) >= 3 and self._once_per("lag", 6 * 3600, now):
            await self.alert(0, "🐢 Бот притормаживает: цикл обслуживания отставал %d раза за 10 минут (до %d с). "
                                "Проверьте нагрузку хостинга." % (len(lags), max(lags)))
        top = self._ax_errc.top(now - 3600)
        n = sum(c for _, c in top)
        if n >= 25 and self._once_per("errs", 6 * 3600, now):
            await self.alert(0, "🩺 За час в логах %d ошибок: %s. Бот продолжает работать; детали — в логах." %
                             (n, ", ".join("%s ×%d" % (esc(name, 30), c) for name, c in top)))
        if isinstance(self.store, VaultStore) and self.store._vfail >= 2 and self._once_per("vfail", 6 * 3600, now):
            await self.alert(0, "💾 SQLite не отвечает: состояние временно пишется в полный JSON, как раньше. Пробую вернуться каждые 5 минут.")

    # ───────── «спасено автопилотом» (счётчик контрафакта) ─────────
    def ax_counterfactual(self, now: float) -> None:
        day = self.store.day(now)
        for cid, st in self.store.chats.items():
            today = st.stats.get(day) or {}
            applied = st.cfg.ap_applied
            for stat, key in (("del_lock", "locks"), ("del_newbie", "newbie_min"), ("del_slow", "slow")):
                cur = int(today.get(stat, 0))
                prev = self._ax_led.get((cid, day, stat))
                self._ax_led[(cid, day, stat)] = cur
                if prev is not None and cur > prev and key in applied:
                    self.eng.ax_count(cid, "saved", cur - prev, now)
        for k in [k for k in self._ax_led if k[1] != day]:
            self._ax_led.pop(k, None)

    # ───────── лаборатория самонастройки ─────────
    async def ax_lab_chat(self, cid: int, now: float, force: bool = False) -> dict | None:
        v = self.vault
        if v is None or not v.ok or not AX_FEATS["tune"]:
            return None
        c = self.eng._ax_c(cid)
        if not force and (now - float(c.get("kt", 0)) < 20 * 3600 or float(c.get("fu", 0)) > now):
            return None
        traces = await asyncio.to_thread(v.traces_for, cid, 40)
        res = await asyncio.to_thread(ax_lab_eval, traces, float(c.get("k", 1.0)))
        c["lab"] = {"t": round(now), "n": [res["n_attack"], res["n_quiet"], res["n_false"]], "why": res["why"]}
        if res["k_new"] != float(c.get("k", 1.0)):
            old = float(c.get("k", 1.0))
            c["k"], c["kt"] = res["k_new"], round(now)
            self.eng.ax_count(cid, "tune", now=now)
            st = self.store.chats.get(cid)
            self.journal("ax", cid, st.title if st else "", 0, "", "автонастройка %s → %s" % (_ax_fmt_k(old), _ax_fmt_k(res["k_new"])))
            await self.alert(cid, "🧪 <b>%s</b>\nАвтонастройка: пороги автопилота %s → <b>%s</b>.\nПроверила на архиве: атак %d, тихих %d, "
                                  "ложных %d. %s.\nВернуть как было: /brain tune reset в чате." %
                             (esc(st.title if st else "", 60), _ax_fmt_k(old), _ax_fmt_k(res["k_new"]), res["n_attack"], res["n_quiet"],
                              res["n_false"], esc(res["why"], 140)))
        self.store.dirty = True
        return res

    async def ax_lab_all(self, now: float) -> None:
        for cid, st in list(self.store.chats.items()):
            if cid < 0 and st.active and st.cfg.autopilot:
                try:
                    await self.ax_lab_chat(cid, now)
                except Exception:                                    # noqa: BLE001
                    log_ax.exception("лаборатория: чат %s не обработан", cid)

    # ───────── отчёты ─────────
    async def ax_send_debrief(self, cid: int, d: dict) -> None:
        st = self.store.chats.get(cid)
        spec = AP_REFLEXES[d["reflex"]]
        kinds = ", ".join("%s: %d" % (AP_KIND_LABEL.get(k) or RADAR_LABEL.get(k, k), n) for k, n in sorted(d["kinds"].items(), key=lambda x: -x[1])[:3])
        lines = ["📋 <b>Разбор полётов · %s</b>" % esc(st.title if st else "", 60),
                 "%s %s: дошло до «%s», длилось %s" % (spec["icon"], spec["label"], AP_LEVEL_NAME[d["peak"]], human_dur(d["dur"])),
                 "• участников в волне: %d, событий: %d%s" % (d["actors"], d["events"], (" (%s)" % esc(kinds, 120)) if kinds else "")]
        if d["changes"]:
            lines.append("• что менял: " + esc("; ".join(d["changes"]), 180))
        eff = d.get("eff")
        if eff and eff[1] >= 2:
            lines.append("• эффект: после включения спад обычно %+d%% (по %d случаям)" % (round(eff[0] * 100), eff[1]))
        if d["over"]:
            lines.append("• владелец отменял меры — учтено: именно эту меру бот не трогает, остальные держит")
        await self.alert(cid, "\n".join(lines))
        self.journal("ax", cid, st.title if st else "", 0, "", "разбор: %s до L%d, %s" % (d["reflex"], d["peak"], human_dur(d["dur"])))

    def ax_day_sum(self, now: float) -> dict:
        return dict(self.eng._axm()["g"].get("day", {}).get(self.store.day(now), {}))

    async def ax_digest(self, now: float) -> None:
        s = self.ax_day_sum(now)
        if not any(s.get(k, 0) for k in ("hind", "cards", "ham", "hacked", "tune", "ti", "saved", "doubt", "fuse", "media", "fed")):
            return
        bits = []
        learn = []
        if s.get("hind"):
            learn.append("ретро-уроков %d" % s["hind"])
        if s.get("cards"):
            learn.append("решений по карточкам %d" % s["cards"])
        if s.get("ham"):
            learn.append("«это нормально» %d" % s["ham"])
        if learn:
            bits.append("🎓 Сама научилась: " + ", ".join(learn))
        prot = []
        if s.get("hacked"):
            prot.append("взломанных аккаунтов остановлено %d" % s["hacked"])
        if s.get("media"):
            prot.append("повторов спам-картинок %d" % s["media"])
        if s.get("fed"):
            prot.append("спамеров убрано из других чатов %d" % s["fed"])
        if s.get("ti"):
            prot.append("новых записей в общей базе угроз %d" % s["ti"])
        if prot:
            bits.append("🛡 " + ", ".join(prot))
        ap = []
        if s.get("saved"):
            ap.append("сообщений остановлено мерами автопилота ≈ %d" % s["saved"])
        if s.get("doubt"):
            ap.append("мер, отменённых вами и учтённых: %d" % s["doubt"])
        if s.get("tune"):
            ap.append("пороги подстроены: %d" % s["tune"])
        if s.get("fuse"):
            ap.append("предохранитель сработал: %d" % s["fuse"])
        if ap:
            bits.append("🤖 " + "; ".join(ap))
        if bits:
            await self.alert(0, "🧠 <b>Автономия за сутки</b>\n" + "\n".join(bits) + "\n<i>Подробности: /brain · откат решений: /brain undo</i>")

    # ───────── хуки в события Telegram ─────────
    async def on_join(self, chat, user, join_msg_id=None) -> None:
        if self.eng.ax_on and getattr(user, "id", 0) > 0:
            self.eng.ax_join(chat.id, user.id, self.now())
        return await super().on_join(chat, user, join_msg_id)

    async def on_reaction(self, ev) -> None:
        try:
            if self.eng.ax_on:
                chat, user = getattr(ev, "chat", None), getattr(ev, "user", None)
                if chat is not None and user is not None and getattr(chat, "type", "") in GROUP_TYPES:
                    new = self._lp_emoji(getattr(ev, "new_reaction", None)) - self._lp_emoji(getattr(ev, "old_reaction", None))
                    if new:
                        self.eng.ax_react(chat.id, ev.message_id, user.id, new, self.now())
        except Exception:                                            # noqa: BLE001
            log_ax.exception("реакции как радар: сбой")
        return await super().on_reaction(ev)

    @staticmethod
    def ax_fuids(m) -> list:
        out = []
        ph = getattr(m, "photo", None)
        if ph:
            out.append(getattr(ph[-1], "file_unique_id", None))
        for attr in ("video", "animation", "document"):
            o = getattr(m, attr, None)
            out.append(getattr(o, "file_unique_id", None) if o else None)
        return [x for x in out if isinstance(x, str) and x][:3]

    async def plus_gate(self, m, chat, state, uid: int, name: str, as_channel: bool, rights: dict) -> bool:
        if self.eng.ax_on and AX_FEATS["media"] and self.eng.ti_fu and not as_channel and uid > 0:
            try:
                fus = [f for f in self.ax_fuids(m) if f in self.eng.ti_fu]
                if fus:
                    rec = state.users.get(uid)
                    if not (rec and (rec.vouched or rec.clean >= 10)):
                        now = self.now()
                        if rights.get("delete"):
                            self.deleter.add(chat.id, [m.message_id])
                        if rights.get("restrict") and (rec is None or rec.clean < 3):
                            await self.restrict(chat.id, uid, 3600)
                        self.eng.radar_note(chat.id, uid, "scam", now)
                        self.eng.ax_count(chat.id, "media", now=now)
                        self.journal("ax", chat.id, chat.title or "", 0, name, "повтор известной спам-картинки")
                        return True
            except asyncio.CancelledError:
                raise
            except Exception:                                        # noqa: BLE001
                log_ax.exception("память о спам-картинках: сбой")
        return await super().plus_gate(m, chat, state, uid, name, as_channel, rights)

    async def apply(self, m, msg, v, name: str, rights: dict) -> None:
        delayed = bool(v.info.get("delay"))
        await super().apply(m, msg, v, name, rights)
        if delayed or not self.eng.ax_on:
            return
        try:
            strong = (v.ban or v.delete) and v.category in ("scam", "scam_ban") and v.score >= STRONG_SCAM
            if strong and AX_FEATS["media"] and not msg.sender_chat:
                now = self.now()
                for fu in self.ax_fuids(m):
                    if fu not in self.eng.ti_fu:
                        self.eng.ti_fu[fu] = now
                        self.eng.ax_q["ti"].append(("fu", fu, now))
            if (v.ban and strong and AX_FEATS["federation"] and rights.get("restrict") and not msg.sender_chat
                    and msg.user_id > 0 and v.category in ("scam", "scam_ban")):
                await self.ax_federate(msg.chat_id, msg.user_id, name, v.why())
        except asyncio.CancelledError:
            raise
        except Exception:                                            # noqa: BLE001
            log_ax.exception("автономное ядро: действия после наказания не выполнены")

    async def ax_federate(self, cid: int, uid: int, name: str, why: str) -> None:
        """Спамер пойман в одном чате → общий список (бот не пустит его и в остальные чаты) + бан там, где он уже есть."""
        if uid in self.owners or self.is_trusted(uid) or uid == self.me_id or str(uid) in self.gbans():
            return
        now = self.now()
        st0 = self.store.chats.get(cid)
        rec0 = st0.users.get(uid) if st0 else None
        if rec0 is not None and (rec0.vouched or rec0.clean >= 5):
            return                                                    # у «своего» участника вердикт мог быть ошибочным
        while self._ax_fed and now - self._ax_fed[0] > 3600:
            self._ax_fed.popleft()
        if len(self._ax_fed) >= 8:
            return
        self._ax_fed.append(now)
        done = []
        for c2, st in list(self.store.chats.items()):
            if c2 == cid or c2 >= 0 or not st.active or not self.chat_ok(c2):
                continue
            rec = st.users.get(uid)
            if rec is None or rec.vouched or rec.clean >= 5 or not (await self.rights(c2))["restrict"]:
                continue
            if await self.call("ban_chat_member", c2, uid, revoke_messages=True) is not None:
                done.append(c2)
                rec.banned = True
            await asyncio.sleep(0.05)
        self.gbans()[str(uid)] = {"r": ("авто: " + why)[:100], "t": round(now), "by": 0, "n": (name or str(uid))[:40],
                                  "ch": done, "auto": 1}
        self.store.dirty = True
        self.eng.ax_count(cid, "fed", now=now)
        self.journal("gban_add", cid, st0.title if st0 else "", 0, name, "авто: %s" % why[:60])
        if done:
            await self.alert(cid, "🕸 Спамер <code>%d</code> пойман в «%s» → заблокирован ещё в чатах: %d, внесён в общий список на %d дн.\n"
                                  "Ошибка? /ungban %d" % (uid, esc(st0.title if st0 else "", 40), len(done), AX_FED_TTL // 86400, uid))

    async def invite_bad(self, chat_id: int, uid: int) -> None:
        await super().invite_bad(chat_id, uid)
        if not (self.eng.ax_on and AX_FEATS["invite"]):
            return
        try:
            state = self.store.chats.get(chat_id)
            rec = state.users.get(uid) if state else None
            book = self._invites(chat_id)
            e = book.get(rec.src) if (rec is not None and rec.src and book) else None
            if e and e.get("warned") and not e.get("revoked") and not e.get("ax_tried"):
                e["ax_tried"] = True
                if await self.call("revoke_chat_invite_link", chat_id, e["url"]) is not None:
                    e["revoked"] = True
                    self.store.dirty = True
                    self.eng.ax_count(chat_id, "invite", now=self.now())
                    await self.alert(chat_id, "🔗 Ссылку «%s» в «%s» отозвала сама: %d из %d вошедших по ней — спамеры. Новую: /invite <i>метка</i>." %
                                     (esc(e["name"], 24), esc(state.title, 40), e.get("bad", 0), e.get("joined", 0)))
        except asyncio.CancelledError:
            raise
        except Exception:                                            # noqa: BLE001
            log_ax.exception("авто-отзыв ссылки: сбой")

    # ───────── команды ─────────
    def ax_status_text(self, cid: int = 0, now: float | None = None) -> str:
        now = self.now() if now is None else now
        eng = self.eng
        s = self.ax_day_sum(now)
        lines = ["🧠 <b>Автономное ядро</b>" + ("" if eng.ax_on else " — выключено (GUARD_AX=0)")]
        if cid and cid in self.store.chats:
            st = self.store.chats[cid]
            c = eng._ax_c(cid)
            lines.append("<b>%s</b>%s" % (esc(st.title, 50), " · ⛔ ядро отключено для чата" if c.get("off") else ""))
            k = float(c.get("k", 1.0))
            lab = c.get("lab")
            lines.append("• Пороги автопилота: %s%s" % (_ax_fmt_k(k), (" (по %d атак/%d тихих/%d ложных, %s)" % (*lab["n"], esc(lab["why"], 70))) if lab else " (архива пока мало)"))
            f, fw, cur, pk = eng.ax_forecast(cid, now)
            if c.get("fcn", 0) < 168:
                lines.append("• Прогноз волн: копится (%d из 168 часов)" % c.get("fcn", 0))
            else:
                lines.append("• Прогноз: %s" % (fw or "сейчас спокойный час") + (", пик через ~%d ч" % pk[0] if pk and pk[0] else ""))
            if float(c.get("fu", 0)) > now:
                lines.append("• 🧯 Предохранитель включён ещё на %s" % human_dur(float(c["fu"]) - now))
            md = {k2: u for k2, u in (c.get("md") or {}).items() if u > now}
            if md:
                lines.append("• Меры, которые вы отменили (не трогаю): " + ", ".join("%s (ещё %s)" % (k2, human_dur(u - now)) for k2, u in md.items()))
            if float(c.get("sh", 0)) > now:
                lines.append("• 👻 Обкатка: автопилот только наблюдает ещё %s" % human_dur(float(c["sh"]) - now))
            if cid in eng.ax_blind:
                lines.append("• 👁 Бот здесь «слепой» (нет прав удалять) — тишину спокойствием не считаю")
        g = eng._axm()["g"]
        src = g.get("src", {})
        lines.append("• Самообучение сегодня: ретро %d · карточки %d · «нормально» %d · взломов %d" %
                     (s.get("hind", 0), s.get("cards", 0), s.get("ham", 0), s.get("hacked", 0)))
        lines.append("• Общая база угроз: шаблонов %d · контактов %d · файлов %d · аккаунтов %d" %
                     (len(eng.ti_sim), len(eng.ti_ct), len(eng.ti_fu), len(eng.ti_uid)))
        if src:
            lines.append("• Источники уроков (верно/спорно): " + ", ".join("%s %d/%d" % (n, a, b) for n, (a, b) in src.items()))
        if s.get("saved"):
            lines.append("• Мерами автопилота остановлено ≈ %d сообщений" % s["saved"])
        st_ = self.store
        sz = st_.sizes() if isinstance(st_, VaultStore) else {}
        if sz:
            lines.append("• Хранилище: JSON %.0f КБ · SQLite %.1f МБ · Upstash: %s" %
                         (sz["json"] / 1024, sz["vault"] / 1e6, "подключён" if self.up.enabled else "не настроен"))
        lines.append("<i>/brain why · /brain lab · /brain undo · /brain shadow on|off · /vault</i>")
        return "\n".join(lines)

    def ax_why_text(self, cid: int, now: float) -> str:
        eng, st = self.eng, self.store.chats.get(cid)
        if st is None:
            return "Чат не найден."
        cfg, lines = st.cfg, ["🔍 <b>Почему автопилот сделал так</b> · %s" % esc(st.title, 50)]
        why = eng.ax_why_keys(cfg)
        if not why:
            lines.append("Сейчас автопилот ничего не менял в настройках чата.")
        for key, val, who in why[:10]:
            lines.append("• <code>%s</code> = %s ← %s" % (esc(key, 20), esc(str(val), 30), ", ".join(who) or "затишье"))
        for r, s in cfg.ap_state.items():
            if r in AP_REFLEXES and isinstance(s, dict) and _ap_lvl(s) > 0:
                eta = eng.ap_eta(cid, r, now)
                eff = eng.ax_eff_text(cid, r, _ap_lvl(s))
                lines.append("%s %s: уровень %d%s%s" % (AP_REFLEXES[r]["icon"], AP_REFLEXES[r]["label"], _ap_lvl(s),
                                                       (" · снимется примерно через %s" % human_dur(eta)) if eta else "",
                                                       (" · " + eff) if eff else ""))
        sh = eng._ax_sh.get(cid)
        if sh and sh["log"]:
            lines.append("👻 Что сделала бы в обкатке:")
            lines += ["  %s %s" % (self.fmt_when(t), esc(txt, 110)) for t, txt in list(sh["log"])[-4:]]
        return "\n".join(lines)

    async def cmd_brain(self, m, args):
        u = getattr(m, "from_user", None)
        if u is None:
            return
        grp = self.in_group(m)
        w = (args or "").strip().lower().split()
        sub = w[0] if w else ""
        now = self.now()
        if grp:
            if not await self.need_admin(m):
                return
            self.cleanup(m)
        elif u.id not in self.owners:
            return
        cid = m.chat.id if grp else 0
        ttl = 60 if grp else 0
        if sub in ("", "status", "статус"):
            return await self.out(m, self.ax_status_text(cid, now), ttl=ttl)
        if sub in ("why", "почему"):
            return await self.out(m, self.ax_why_text(cid, now) if cid else "Спросите в чате: /brain why", ttl=ttl)
        if sub in ("lab", "лаб") and cid:
            res = await self.ax_lab_chat(cid, now, force=True)
            if res is None:
                return await self.out(m, "Лаборатория недоступна: нужен SQLite и включённая автонастройка.", ttl=ttl)
            loss = ", ".join("%s: %.1f" % (_ax_fmt_k(k), v) for k, v in res["loss"].items()) or "—"
            return await self.out(m, "🧪 Лаборатория: атак %d · тихих %d · ложных %d\nЦена ошибок по порогам: %s\nИтог: %s" %
                                  (res["n_attack"], res["n_quiet"], res["n_false"], loss, esc(res["why"], 160)), ttl=ttl)
        if sub == "tune" and cid and len(w) > 1 and w[1] == "reset":
            c = self.eng._ax_c(cid)
            c["k"], c["kt"] = 1.0, round(now)
            self.store.dirty = True
            return await self.out(m, "Пороги автопилота возвращены (×1.00). Автонастройка не будет менять их ближайшие 20 часов.", ttl=ttl)
        if sub in ("undo", "откат"):
            if u.id not in self.owners:
                return await self.out(m, "Откат решений — только для владельца.", ttl=ttl)
            dec = self.eng._axm()["g"].get("dec", [])
            if not dec:
                return await self.out(m, "Самостоятельных решений по карточкам пока не было.", ttl=ttl)
            card_id, act, t, c0 = dec.pop()
            res = self.eng.learn_undo_card(card_id, u.id, now)
            self.eng._ax_src("cards", False)
            self.store.dirty = True
            return await self.out(m, ("↩️ Отменила своё решение (%s по карточке %s, %s)." % ("«спам»" if act == "s" else "«нормально»", card_id, self.fmt_when(t)))
                                  if res.get("ok") else "Это решение уже нельзя отменить (карточка устарела).", ttl=ttl)
        if sub in ("shadow", "тень") and cid:
            on = len(w) > 1 and w[1] in ("on", "вкл", "1")
            hours = float(w[2]) if len(w) > 2 and w[2].replace(".", "").isdigit() else 24.0
            c = self.eng._ax_c(cid)
            c["sh"] = round(now + hours * 3600) if on else 0
            self.store.dirty = True
            return await self.out(m, ("👻 Обкатка на %s: автопилот считает и записывает, что бы сделал, но в чате ничего не меняет. Итог: /brain why." % human_dur(hours * 3600))
                                  if on else "Обкатка выключена: автопилот работает по-настоящему.", ttl=ttl)
        if sub == "fuse" and cid and len(w) > 1 and w[1] == "reset":
            c = self.eng._ax_c(cid)
            c["fu"], c["fuse"] = 0, []
            self.store.dirty = True
            return await self.out(m, "Предохранитель снят.", ttl=ttl)
        if sub in ("off", "выкл", "on", "вкл") and cid:
            self.eng._ax_c(cid)["off"] = 1 if sub in ("off", "выкл") else 0
            self.store.dirty = True
            return await self.out(m, "Автономное ядро для этого чата: %s." % ("выключено" if sub in ("off", "выкл") else "включено"), ttl=ttl)
        if sub in ("public", "публично") and cid:
            today = (self.store.chats[cid].stats.get(self.store.day(now)) or {})
            gone = sum(v for k, v in today.items() if k.startswith("del_")) + today.get("ban", 0)
            await self.call("send_message", cid, "🛡 <b>Защита чата</b>\nСегодня остановлено сообщений: %d (спам, ссылки, нарушения), заблокировано: %d.\n"
                                                  "Автопилот на страже: он сам усиливает защиту при атаках и смягчает, когда спокойно." % (gone, today.get("ban", 0)),
                            disable_notification=True)
            return
        await self.out(m, "Команды: /brain · why · lab · undo · tune reset · shadow on|off [часов] · fuse reset · on|off · public", ttl=ttl)

    async def cmd_vault(self, m, args):
        if not await self.need_owner(m):
            return
        grp = self.in_group(m)
        if grp:
            self.cleanup(m)
        ttl = 40 if grp else 0
        w = (args or "").strip().lower().split()
        sub = w[0] if w else ""
        v, now = self.vault, self.now()
        if sub == "backup":
            await self.ax_backup(now)
            self._ax_bk_commit = ""
            return await self.out(m, "💾 Копия сделана: локально %s, Upstash: %s." % ("да" if v is not None and v.ok else "нет",
                                                                                   "да" if self.up.enabled else "не настроен"), ttl=ttl)
        if sub in ("compact", "clean", "уборка") and v is not None and v.ok:
            r = await asyncio.to_thread(v.maintain, now)
            return await self.out(m, "🧹 Уборка SQLite: " + (", ".join("%s −%d" % kv for kv in r.items() if kv[1]) or "убирать нечего"), ttl=ttl)
        if sub == "export" and isinstance(self.store, VaultStore):
            dest = str(self.store.path) + ".export.json"
            n = await asyncio.to_thread(self.store.export_json, dest)
            return await self.out(m, "📤 Полный JSON выгружен: <code>%s</code> (%.1f МБ)." % (esc(os.path.basename(dest), 60), n / 1e6), ttl=ttl)
        sz = self.store.sizes() if isinstance(self.store, VaultStore) else {"json": 0, "vault": 0}
        lines = ["💾 <b>Хранилище</b>", "• JSON-ядро: %.0f КБ (раньше здесь было всё)" % (sz["json"] / 1024)]
        if v is not None and v.ok:
            stt = await asyncio.to_thread(v.stats)
            kv = stt["kv"]
            lines.append("• SQLite: %.1f МБ · участников %d · кусков самообучения %d" % (stt["bytes"] / 1e6, kv.get("users", (0, 0))[0], kv.get("m", (0, 0))[0]))
            lines.append("• История: журнал %d · автопилот %d · следов атак %d · база угроз %d" %
                         (stt["tables"]["journal"], stt["tables"]["aphist"], stt["tables"]["traces"], stt["tables"]["ti"]))
        else:
            lines.append("• SQLite: ⛔ недоступен%s" % ((" (%s)" % esc(v.err, 60)) if v is not None and v.err else " (выключен)"))
        if self.up.enabled:
            lines.append("• Upstash: подключён · команд сегодня %d из %d%s" % (self.up._used, self.up.budget,
                                                                             (" · последняя ошибка: " + esc(self.up.last_err, 40)) if self.up.last_err else ""))
            try:
                meta = await asyncio.to_thread(self.up.backup_meta, self._ax_instance())
                lines.append("• Облачная копия: " + ("%s, %.0f КБ" % (self.fmt_when(meta["t"]), meta["size"] / 1024) if meta else "ещё нет"))
            except Exception as e:                                   # noqa: BLE001
                lines.append("• Облачная копия: не проверить (%s)" % esc(str(e), 50))
        else:
            lines.append("• Upstash: не настроен (UPSTASH_REDIS_REST_URL / _TOKEN)")
        lines.append("<i>/vault backup · /vault compact · /vault export</i>")
        await self.out(m, "\n".join(lines), ttl=ttl)


class GuardX(Sentinel, Guard):
    """Guard + автономное ядро."""


async def _ax_cmd_stub(self, m, args):                                # обычный Guard (GUARD_AX=0) эти команды просто не знает
    return None


Guard.cmd_brain = Guard.cmd_vault = _ax_cmd_stub


# ───────────────────────────── запуск: сборка хранилища и CLI ─────────────────────────────
def ax_make_store(token: str = "") -> tuple:
    """→ (store, vault|None, upstash). Подбирает Store/VaultStore, при пустом диске пробует восстановиться из Upstash."""
    json_path = os.getenv("GUARD_STATE", "guard_state.json")
    db_path = os.getenv("GUARD_VAULT_DB") or (os.path.splitext(json_path)[0] + ".db")
    up = Upstash.from_env()
    if not AX_VAULT_ON:
        try:
            head = Path(json_path).read_text(encoding="utf-8", errors="ignore") if Path(json_path).exists() else ""
        except OSError:
            head = ""
        if '"_vault"' in head:
            raise SystemExit("Файл %s «тонкий»: участники и самообучение лежат в SQLite (%s). Чтобы вернуться к одному JSON, сначала: "
                             "python guard.py --vault-export, затем замените файл выгрузкой и поставьте GUARD_VAULT=0." % (json_path, db_path))
        return Store(json_path), None, up
    if up.enabled and not Path(json_path).exists() and not Path(db_path).exists() and token:
        why = ax_restore_from_upstash(up, json_path, db_path, "bot%s" % token.split(":")[0])
        if why:
            log_vault.info("восстановление из Upstash не понадобилось/не удалось: %s", why)
    vault = Vault(db_path)
    return VaultStore(json_path, vault=vault), vault, up


def ax_cli(argv: list):
    """--vault-info / --vault-export: служебные команды без запуска бота. None — это не наши флаги."""
    if not argv or argv[0] not in ("--vault-info", "--vault-export"):
        return None
    load_env()
    ax_reload_env()
    json_path = os.getenv("GUARD_STATE", "guard_state.json")
    db_path = os.getenv("GUARD_VAULT_DB") or (os.path.splitext(json_path)[0] + ".db")
    vault = Vault(db_path)
    store = VaultStore(json_path, vault=vault)
    store.load()
    if argv[0] == "--vault-info":
        st = vault.stats()
        print("JSON: %d КБ · SQLite: %.1f МБ · участников в памяти: %d · чатов: %d" %
              (store.sizes()["json"] // 1024, st["bytes"] / 1e6, sum(len(c.users) for c in store.chats.values()), len(store.chats)))
        print("таблицы:", st["tables"], "· kv:", st["kv"])
        return 0
    dest = json_path + ".export.json"
    n = store.export_json(dest)
    print("Полный JSON выгружен: %s (%.1f МБ). Чтобы вернуться к одному файлу: замените %s этим файлом и поставьте GUARD_VAULT=0." %
          (dest, n / 1e6, json_path))
    return 0


class GuardMiddleware(BaseMiddleware):

    def __init__(self, guard: Guard):
        self.guard = guard

    async def __call__(self, handler, event, data):
        try:
            if await self.guard.on_message(event):
                return None
        except Exception:
            log.exception("охрана: сбой при проверке сообщения")
        return await handler(event, data)


BOT_TOKEN_RE = re.compile(r"(?<!\d)\d{6,}:[A-Za-z0-9_-]{30,}")


class RedactFilter(logging.Filter):

    def __init__(self, secrets_=()):
        super().__init__()
        self.secrets_ = [s for s in secrets_ if s and len(s) >= 6]

    def redact(self, s: str) -> str:
        s = BOT_TOKEN_RE.sub("<токен скрыт>", s)
        for x in self.secrets_:
            s = s.replace(x, "<секрет скрыт>")
        return s

    def filter(self, record: logging.LogRecord) -> bool:
        try:
            msg = record.getMessage()
            red = self.redact(msg)
            if red != msg:
                record.msg, record.args = red, ()
            if record.exc_info and not record.exc_text:
                record.exc_text = logging.Formatter().formatException(record.exc_info)
            if record.exc_text:
                record.exc_text = self.redact(record.exc_text)
        except Exception:
            pass
        return True


def build_router(guard: Guard) -> Router:
    r = Router(name="guard")
    mw = GuardMiddleware(guard)
    r.message.outer_middleware(mw)
    r.edited_message.outer_middleware(mw)
    r.message.register(guard.on_command, Command(*COMMAND_NAMES))
    r.message.register(guard.on_other)
    r.edited_message.register(guard.on_noop)
    r.callback_query.register(guard.on_callback)
    r.chat_member.register(guard.on_chat_member)
    r.my_chat_member.register(guard.on_my_chat_member)
    r.chat_join_request.register(guard.on_join_request)
    r.message_reaction.register(guard.on_reaction)
    return r


def load_env(path: str = ".env") -> None:
    try:
        from dotenv import load_dotenv
        load_dotenv(path)
    except ImportError:
        if os.path.exists(path):
            for line in open(path, encoding="utf-8"):
                line = line.strip()
                if line and not line.startswith("#") and "=" in line:
                    k, v = line.split("=", 1)
                    os.environ.setdefault(k.strip(), v.strip().strip('"').strip("'"))


try:
    import guard5 as _g5                                 # расширение 5.0 лежит рядом с guard.py; нет файла — работаем как 4.3
    _g5.bind(globals())
except ImportError:
    _g5 = None
except Exception:                                        # noqa: BLE001
    logging.getLogger("guard").exception("guard5.py не загрузился — работаю как 4.3")
    _g5 = None

try:
    import guard6 as _g6                                 # расширение 6.0 лежит рядом с guard.py; нет файла — работаем как 5.0
    _g6.bind(globals())
except ImportError:
    _g6 = None
except Exception:                                        # noqa: BLE001
    logging.getLogger("guard").exception("guard6.py не загрузился — работаю как 5.0")
    _g6 = None


LANG_MODULES = ("es", "de", "ar", "zh")                  # guard_<код>.py рядом с guard.py; порядок — порядок подключения
LANGS_ON: list = []                                      # какие языки реально подключены (заполняет install_languages)
_LANG_FLAG = {"es": "_ES_INSTALLED", "de": "_de_installed", "ar": "_guard_ar_installed", "zh": "_guard_zh_installed"}   # флаги, которые ставят сами модули


def _langs_wanted(env=None) -> list:
    """GUARD_LANGS: пусто/all — все найденные; «es,de» — только эти; off/0/none — ни один."""
    raw = str((os.environ if env is None else env).get("GUARD_LANGS", "all") or "all").strip().lower()
    if raw in ("0", "off", "none", "no", "false"):
        return []
    if raw in ("all", "*", "1", "on"):
        return list(LANG_MODULES)
    want = [x.strip() for x in re.split(r"[,\s;]+", raw) if x.strip()]
    return [c for c in LANG_MODULES if c in want]


def install_languages() -> list:
    """Подключает языковые модули. Вызывать ПОСЛЕ load_env(): модули читают свои настройки (GUARD_ES, GUARD_DE…) при подключении.
    Нет файла — язык просто не подключается; сбой в одном модуле не мешает остальным и самому боту. Повторный вызов безопасен."""
    me = sys.modules[__name__]
    for code in _langs_wanted():
        if code in LANGS_ON:
            continue
        try:
            mod = __import__(f"guard_{code}")
        except ImportError:
            log.info("язык %s: файла guard_%s.py рядом нет — не подключаю", code, code)
            continue
        except Exception:                                # noqa: BLE001
            log.exception("язык %s: guard_%s.py не загрузился — пропускаю", code, code)
            continue
        try:
            mod.install(me)
        except Exception:                                # noqa: BLE001
            log.exception("язык %s: подключение не удалось — пропускаю", code)
            continue
        if not getattr(me, _LANG_FLAG[code], False):     # install() вернул «нет» и флага нет — модуль выключен своей настройкой
            log.info("язык %s: модуль выключен настройкой (GUARD_%s=0)", code, code.upper())
            continue
        LANGS_ON.append(code)
    if LANGS_ON:
        log.info("языки: %s", ", ".join(LANGS_ON))
    return list(LANGS_ON)


async def main() -> None:
    load_env()
    ax_reload_env()                                      # настройки автономного ядра из .env
    logging.basicConfig(level=os.getenv("LOG_LEVEL", "INFO"), format="%(asctime)s %(levelname)s %(name)s: %(message)s")
    install_languages()                                  # es/de/ar/zh: guard_<код>.py рядом; нет файла — язык просто не подключается
    token = os.getenv("GUARD_BOT_TOKEN") or os.getenv("BOT_TOKEN", "")
    _flt = RedactFilter([token, os.getenv("GUARD_SECRET", ""), os.getenv("GUARD_PANEL_WORD", "")])
    for _h in logging.getLogger().handlers:
        _h.addFilter(_flt)
    if not token:
        raise SystemExit("Нет токена: задай GUARD_BOT_TOKEN в .env (это токен ОТДЕЛЬНОГО бота-сторожа, не игрового)")
    store, _ax_vault, _ax_up = ax_make_store(token)      # Store или VaultStore (SQLite) + Upstash; при GUARD_VAULT=0 — как раньше
    store.load()
    words = os.getenv("GUARD_CUSTOM_WORDS", "custom_words.txt")
    if os.path.exists(words):
        log.info("свои слова: загружено %d", load_custom(words))
    _E, _G = (EngineX, GuardX) if AX_ON else (Engine, Guard)   # EngineX = Engine + автономное ядро (GUARD_AX=0 — выключить)
    if _g5 is not None:
        try:
            _E, _G = _g5.build(_E, _G)                   # 5.0: подмешивает расширение; при GUARD5=0 возвращает классы как есть
        except Exception:                                # noqa: BLE001
            log.exception("guard5: сборка не удалась — работаю как 4.3")
    if _g6 is not None:
        try:
            _E, _G = _g6.build(_E, _G)                   # 6.0: подмешивается ПОСЛЕ 5.0; при GUARD6=0 возвращает классы как есть
        except Exception:                                # noqa: BLE001
            log.exception("guard6: сборка не удалась — работаю как 5.0")
    engine = _E(store)
    bot = Bot(token, default=DefaultBotProperties(parse_mode=ParseMode.HTML, link_preview_is_disabled=True))
    guard = _G(bot, store, engine, Voice())
    if AX_ON:
        guard.up = _ax_up
    sec = read_secrets()
    apply_secrets(guard, sec)
    for w in sec["warnings"]:
        log.warning("настройки: %s", w)
    await guard.start()
    log.info("версия %s; владельцев: %d (доверенных %d, в чёрном списке %d); слово панели: %s; допуск: %s; строго: %s; "
             "бан за капчу: %d мин", VERSION, len(guard.owners), len(guard.trusted), len(guard.banned_env),
             "задано" if guard.panel_hash is not None else "нет",
             f"по списку ({len(guard.allowed_ids())})" if guard.allow_mode() else "везде",
             "да" if guard.strict_on() else "нет", guard.captcha_ban_default)
    log.info("CAS: %s; общий журнал: %s", "вкл" if guard.cas_on else "выкл", guard.log_chat_env or "нет")
    log.info("полная защита: автовключение %s (оценка от %g, источников от %d)", "да" if guard.eng.fort_auto_on else "нет",
             guard.eng.fort_trip_score, guard.eng.fort_trip_actors)
    log.info("автопилот: %s (чувствительность %g, затишье: %s, внутренние поправки: %s)", "работает" if guard.eng.ap_on else "выключен",
             guard.eng.ap_sens, f"после {guard.eng.ap_calm_after / 3600:g} ч" if guard.eng.ap_calm_after else "нет",
             "вкл" if guard.eng.ap_brain else "выкл")
    log.info("кукольный театр (постановочные диалоги): %s", "ловлю" if guard.eng.puppet_on else "не ловлю")
    log.info("память о пойманном спаме: %s", "помню" if guard.eng.memory_on else "не помню")
    log.info("самообучение: %s (шаблонов спама в памяти: %d)", "учусь" if guard.eng.learn_on else "выключено", guard.eng.learn_spam_count())
    log.info("строгий режим: по умолчанию %d мин, автовключение: %s; спам реакциями: %s", guard.eng.strict_default_min,
             "да" if guard.eng.strict_auto_on else "нет", "ловлю" if guard.react_on else "не ловлю")
    await guard.notify_unlisted()

    hook = None
    secret = os.getenv("GUARD_SECRET", "")
    if secret:
        hook = HookServer(secret, guard.on_hook, host=os.getenv("GUARD_HOST", "127.0.0.1"),
                          port=int(os.getenv("GUARD_PORT", "8765")))
        await hook.start()
    else:
        log.warning("GUARD_SECRET не задан — мост с игрой выключен (бои вручную: /ring)")

    dp = Dispatcher()
    dp.include_router(build_router(guard))
    janitor = asyncio.create_task(guard.janitor())
    try:
        await dp.start_polling(bot, allowed_updates=ALLOWED_UPDATES)
    finally:
        await guard.shutdown()
        janitor.cancel()
        if hook:
            await hook.stop()
        await bot.session.close()


if __name__ == "__main__":
    _ax_r = ax_cli(sys.argv[1:])
    if _ax_r is not None:
        raise SystemExit(_ax_r)
    if len(sys.argv) > 1 and sys.argv[1].startswith("-"):
        raise SystemExit(cli(sys.argv[1:]))
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        pass
    except SystemExit as e:
        if e.code not in (None, 0):
            print(e.code, file=sys.stderr)
            raise
