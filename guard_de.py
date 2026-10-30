#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
guard_de.py — немецкий модуль для guard.py (guard.py НЕ изменяется).

Как подключить (любой из способов):
  1) Запуск вместо guard.py:            python guard_de.py
  2) Одна строка в своём лаунчере:       import guard, guard_de; guard_de.install(guard); asyncio.run(guard.main())
  3) Рядом с испанским модулем: install() можно вызывать в любом порядке — модули не мешают друг другу
     (каждый оборачивает guard.analyze_text цепочкой, повторный вызов безопасен).

Что делает:
  • мат / оскорбления / ненависть / 18+ / дети / угрозы на немецком (с составными словами, умляутами, ß, leet,
    кириллическими «двойниками», разнесёнными буквами, масками f*ck, молодёжным сленгом 2025–2026);
  • немецкий спам и скам: «Nebenverdienst / Task-Scam / Finanzagent / Casino ohne OASIS / Kredit ohne Schufa /
    DHL- и Sparkasse-фишинг / Hallo-Mama / Führerschein kaufen / Krypto-Signale …»;
  • телефоны (+49 15x/16x/17x), IBAN (с проверкой контрольной суммы), премиум-номера — в «сеть контактов» guard;
  • бренды DACH для детектора поддельных ссылок (Sparkasse, DHL, Postbank, Klarna, Kleinanzeigen …);
  • защита от ложных срабатываний: «Fagott», «Kikeriki», «Fukushima», «heil angekommen», «Marsch», «Barsch»,
    «behindertengerecht», «Nazi-Zeit / Nazis raus» и т.п.

Фишки, которых нет у обычных антиспам-ботов:
  1) Зерлегер составных слов (Kompositum-Zerleger) — «Scheißdreckskerl» ловится, «Marsch/Barsch/Kirsch» — нет.
  2) Фонетика Köln (Kölner Phonetik) + расстояние Дамерау — ловит «Hurensonn», «Wixxer», «Schlampee»,
     «Arschlooch» без тысячи ручных вариантов, не трогая обычные слова.
  3) «Письмо на Вы» — детектор фишинга по регистру: формальное «Sehr geehrter Kunde … Ihr Konto … innerhalb von 24
     Stunden» в чате, где все на «du», — сильный сигнал (бот сам учит регистр каждого чата).
  4) Щит контекста — «Nazis raus», «Nazi-Deutschland», «das Wort „Hurensohn“ ist eine Beleidigung» не наказываются,
     а «du Nazi», «Hurensohn» — да.
  5) Проверка IBAN по mod-97 и разбор немецких номеров → контакты идут в общую «сеть контактов» guard
     (один и тот же IBAN/номер у нескольких новых аккаунтов = кампания).

Переменные окружения (необязательно):
  GUARD_DE=0          выключить модуль
  GUARD_DE_MILD=1     считать «мат» и мягкие ругательства (Kacke, Idiot, Depp, Vollidiot …)
  GUARD_DE_FUZZY=0    выключить фонетический поиск опечаток
  GUARD_DE_SHIELD=0   выключить щит контекста
  GUARD_DE_REGISTER=0 не учить du/Sie-регистр чатов
Свои слова можно добавлять как обычно через custom_words.txt guard.py (prof:/hate:/adult:/allow:) —
они работают и для немецкого (по основе слова), а «allow:» дополнительно снимает срабатывание модуля.
"""
from __future__ import annotations

import os
import re
import sys
import unicodedata
from collections import OrderedDict
from functools import lru_cache

VERSION_DE = "1.0"

MILD = os.getenv("GUARD_DE_MILD", "0") == "1"
FUZZY_ON = os.getenv("GUARD_DE_FUZZY", "1") != "0"
SHIELD_ON = os.getenv("GUARD_DE_SHIELD", "1") != "0"
REGISTER_ON = os.getenv("GUARD_DE_REGISTER", "1") != "0"

# ─────────────────────────────────────────────────────────────────────────────
#  Нормализация немецкого текста
# ─────────────────────────────────────────────────────────────────────────────

_ZW = set("​‌‍‎‏⁠⁡⁢⁣⁤﻿­᠎"
          "‪‫‬‭‮⁦⁧⁨⁩")
_ZW_TR = {ord(c): None for c in _ZW}
_UML = str.maketrans({"ä": "ae", "ö": "oe", "ü": "ue", "ß": "ss", "ẞ": "ss"})

# кириллические/греческие «двойники» → латиница (только внутри слов, где уже есть латиница)
_HOMO = {
    "а": "a", "в": "b", "е": "e", "ё": "e", "к": "k", "м": "m", "н": "h", "о": "o", "р": "p", "с": "c",
    "т": "t", "у": "y", "х": "x", "і": "i", "ј": "j", "ѕ": "s", "ԁ": "d", "ɡ": "g", "ӏ": "l",
    "α": "a", "β": "b", "ε": "e", "ι": "i", "κ": "k", "ν": "v", "ο": "o", "ρ": "p", "τ": "t", "υ": "u", "χ": "x",
}
_LEET = {"0": "o", "1": "i", "3": "e", "4": "a", "5": "s", "7": "t", "8": "b", "@": "a", "$": "s", "!": "i", "|": "l",
         "€": "e", "§": "s", "ј": "j"}
_LEET_TR = str.maketrans(_LEET)
_TOK_RE = re.compile(r"[a-z0-9@$!|€§]+")
_PLAIN_TOK = re.compile(r"[a-z]+")
_MASK_RE = re.compile(r"(?<![a-z0-9])[a-z][a-z*#]{0,12}[*#]+[a-z*#]*(?![a-z0-9])")


def collapse(w: str) -> str:
    return re.sub(r"(.)\1+", r"\1", w)


class DeNorm:
    """Результат нормализации: канонический текст и разные «виды» токенов."""
    __slots__ = ("text", "plain", "tokens", "deleet", "spaced", "masks", "homo", "zw", "leet_n", "raw_len")

    def __init__(self):
        self.text = ""        # lower, ä→ae, ß→ss, без акцентов, «двойники» → латиница
        self.plain = ""       # то же, только a-z и пробелы (для регексов по фразам)
        self.tokens = []      # токены a-z
        self.deleet = []      # токены с цифрами/символами, преобразованные «0→o, 3→e…»
        self.spaced = []      # склеенные «h u r e n s o h n»
        self.masks = []       # сырые маски f*ck, sch***e
        self.homo = 0         # сколько слов смешаны с кириллицей/греческим
        self.zw = 0
        self.leet_n = 0
        self.raw_len = 0


def _fix_homoglyphs(tok: str) -> tuple[str, bool]:
    has_lat = any("a" <= c <= "z" for c in tok)
    if not has_lat:
        return tok, False
    changed = False
    out = []
    for c in tok:
        h = _HOMO.get(c)
        if h:
            out.append(h)
            changed = True
        else:
            out.append(c)
    return "".join(out), changed


@lru_cache(maxsize=4096)
def _prep(text: str) -> DeNorm:
    n = DeNorm()
    t = text[:4500]
    n.raw_len = len(t)
    n.zw = len(t) - len(t.translate(_ZW_TR))
    t = unicodedata.normalize("NFC", t.translate(_ZW_TR)).lower().translate(_UML)
    t = unicodedata.normalize("NFKD", t)
    t = "".join(ch for ch in t if unicodedata.category(ch) not in ("Mn", "Me", "Cf"))
    # смешанные слова: чиним «двойники»
    parts = re.split(r"(\s+)", t)
    for i, p in enumerate(parts):
        if p and not p.isspace() and re.search(r"[а-яёіїєґͰ-Ͽ]", p) and re.search(r"[a-z]", p):
            fixed, ch = _fix_homoglyphs(p)
            if ch:
                parts[i] = fixed
                n.homo += 1
    t = "".join(parts)
    n.text = t
    n.plain = re.sub(r"\s+", " ", re.sub(r"[^a-z]+", " ", t)).strip()

    base, deleet = [], []
    for m in _TOK_RE.finditer(t):
        tok = m.group(0)
        if tok.isdigit():
            continue
        if _PLAIN_TOK.fullmatch(tok):
            base.append(tok)
        else:
            core = tok.strip("!|@$€§")
            if re.search(r"[a-z]", core) and len(core) >= 3 and re.search(r"[0-9@$€§|!]", core):
                d = core.translate(_LEET_TR)
                if re.fullmatch(r"[a-z]+", d):
                    deleet.append(d)
                    n.leet_n += 1
            # "!" в конце слова — пунктуация, а не буква: «Hure!» → «hure»
            plain = re.sub(r"[^a-z]+", "", core)
            if plain and len(plain) >= 3 and not any(c.isdigit() for c in core):
                base.append(plain)
    n.tokens = base
    n.deleet = deleet

    # разнесённые буквы: «h u r e n s o h n», «f.i.c.k», «s-c-h-e-i-ß-e»
    for m in re.finditer(r"(?<![a-z])(?:[a-z][\s.\-_*·]{1,2}){3,}[a-z](?![a-z])", t):
        joined = re.sub(r"[^a-z]", "", m.group(0))
        if 4 <= len(joined) <= 20:
            n.spaced.append(joined)
        if len(n.spaced) >= 6:
            break

    # маски f*ck, sch***e
    for m in _MASK_RE.finditer(t):
        raw = m.group(0)
        if sum(1 for c in raw if c.isalpha()) < 2 or len(raw) < 4 or len(raw) > 18:
            continue
        n.masks.append(raw)
        if len(n.masks) >= 8:
            break
    return n


def dnorm(text: str) -> DeNorm:
    return _prep(text or "")


# ─────────────────────────────────────────────────────────────────────────────
#  Определение немецкого языка
# ─────────────────────────────────────────────────────────────────────────────

DE_WORDS = frozenset("""
der die das den dem des ein eine einen einem einer eines und oder aber doch denn weil dass ob wenn als wie wo was wer
wem wen wann warum wieso weshalb ich du er sie es wir ihr mich dich sich uns euch ihm ihn ihnen mir dir mein meine
meinen meinem meiner dein deine deinen deinem deiner sein seine unser unsere euer eure ist bin bist sind seid war waren
hat habe hast haben habt hatte wird werde wirst werden wurde wurden kann kannst koennen konnte muss musst muessen soll
sollst sollen will willst wollen mag darf nicht kein keine keinen keinem nie nichts nur auch noch schon mal immer
wieder sehr ganz gar so dann da hier dort jetzt heute morgen gestern bitte danke hallo moin servus tschuess ja nein
vielleicht gerne gern und mit von zu bei nach aus auf an in im am zum zur vom beim fuer ueber unter vor hinter neben
zwischen durch gegen ohne um bis seit waehrend wegen trotz alle alles viel viele mehr wenig etwas jeder jede jedes
man gut schlecht neu alt gross klein lange kurz heisst gibt geht gehen komm kommt kommen mach machen macht sag sagen
sagt weiss wissen denke glaube finde sieht sehen siehe lass lasst moechte moechten
""".split())

_DE_CHARS = re.compile(r"[äöüß]")
# слова, которые есть и в английском/других языках — в «счёт немецкого» не идут
_AMBIG = frozenset("in an am so was will man die war bin hat gar mag also da als wie wo um bis mal ex hand rock "
                   "gift hell arm fast rat bad wort mist kind fall land see name".split())
EN_WORDS = frozenset("the and is are you for with this that have it to of on at be not but what your from they "
                     "we will can just all out up about so if my me do no yes hello hi please thanks looking "
                     "job work money join now free get".split())


@lru_cache(maxsize=2048)
def de_score(text: str) -> float:
    """0..1 — насколько текст похож на немецкий (стоп-слова, ä/ö/ü/ß, типичные суффиксы)."""
    n = dnorm(text)
    toks = n.tokens
    if not toks:
        return 0.0
    de_hits = sum(1 for t in toks if t in DE_WORDS and t not in _AMBIG)
    en_hits = sum(1 for t in toks if t in EN_WORDS)
    uml = bool(_DE_CHARS.search(text[:2000].lower()))
    score = min(1.0, de_hits / len(toks) * 2.5)
    if de_hits < 2 and len(toks) > 4 and not uml:
        score = min(score, 0.3)
    if uml:
        score += 0.25
    low = n.plain
    score += 0.04 * min(5, sum(1 for g in ("sch", "ung", "keit", "lich", "cht", "ueber", "nicht") if g in low))
    if en_hits > de_hits:
        score *= 0.5
    cyr = sum(1 for c in text[:1000] if "а" <= c.lower() <= "я")
    if cyr > 0.5 * max(1, len(text[:1000].replace(" ", ""))):
        score *= 0.2
    if de_hits == 0 and not uml:
        score = min(score, 0.2)
    return round(min(1.0, score), 2)


def is_german(text: str, thr: float = 0.35) -> bool:
    return de_score(text) >= thr


# ─────────────────────────────────────────────────────────────────────────────
#  Kölner Phonetik + расстояние Дамерау (OSA)
# ─────────────────────────────────────────────────────────────────────────────

def koelner(word: str) -> str:
    w = re.sub(r"[^A-Z]", "", word.upper())
    codes = []
    for i, c in enumerate(w):
        prev = w[i - 1] if i else ""
        nxt = w[i + 1] if i + 1 < len(w) else ""
        if c in "AEIJOUY":
            d = "0"
        elif c == "H":
            d = ""
        elif c == "B":
            d = "1"
        elif c == "P":
            d = "3" if nxt == "H" else "1"
        elif c in "DT":
            d = "8" if nxt in ("C", "S", "Z") and nxt else "2"
        elif c in "FVW":
            d = "3"
        elif c in "GKQ":
            d = "4"
        elif c == "C":
            if i == 0:
                d = "4" if nxt and nxt in "AHKLOQRUX" else "8"
            else:
                d = "8" if prev in ("S", "Z") else ("4" if nxt and nxt in "AHKOQUX" else "8")
        elif c == "X":
            d = "8" if prev in ("C", "K", "Q") and prev else "48"
        elif c == "L":
            d = "5"
        elif c in "MN":
            d = "6"
        elif c == "R":
            d = "7"
        elif c in "SZ":
            d = "8"
        else:
            d = ""
        codes.append(d)
    s = "".join(codes)
    out = ""
    for ch in s:
        if not out or ch != out[-1]:
            out += ch
    return (out[0] + out[1:].replace("0", "")) if out else ""


def osa(a: str, b: str, limit: int = 3) -> int:
    """Расстояние Дамерау–Левенштейна (OSA) с ранним выходом."""
    if abs(len(a) - len(b)) > limit:
        return limit + 1
    prev2 = None
    prev = list(range(len(b) + 1))
    for i in range(1, len(a) + 1):
        cur = [i] + [0] * len(b)
        best = cur[0]
        for j in range(1, len(b) + 1):
            cost = 0 if a[i - 1] == b[j - 1] else 1
            v = min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + cost)
            if prev2 is not None and i > 1 and j > 1 and a[i - 1] == b[j - 2] and a[i - 2] == b[j - 1]:
                v = min(v, prev2[j - 2] + 1)
            cur[j] = v
            best = min(best, v)
        if best > limit:
            return limit + 1
        prev2, prev = prev, cur
    return prev[-1]


# ─────────────────────────────────────────────────────────────────────────────
#  Лексикон со «слоговой» логикой составных слов
# ─────────────────────────────────────────────────────────────────────────────
#  Немецкие сложные слова склеивают всё в одно: «Scheißdreckskerl». Поиск «подстрокой» даёт
#  Scunthorpe-ложняки (Marsch ⊃ arsch, Barsch, Kirsch), поиск «только с начала слова» пропускает составные.
#  Решение: корень засчитывается, если он в начале слова ИЛИ всё, что стоит перед ним, целиком раскладывается на
#  известные «головы» (усилители, глагольные приставки, родственники, другие ругательные корни).

HEADS = {
    # усилители и бытовые первые части
    "dumm", "fett", "voll", "total", "mega", "riesen", "super", "ober", "unter", "sau", "mist", "dreck", "drecks",
    "scheiss", "kack", "fick", "wichs", "arsch", "fotz", "fotzen", "hur", "huren", "hure", "nutt", "nutten", "schlamp",
    "schlampen", "spast", "spasten", "kanak", "kanaken", "hunde", "hund", "schweine", "schwein", "affen", "affe", "ratten",
    "mutter", "vater", "bruder", "schwester", "oma", "opa", "eltern", "familie", "tante", "onkel", "cousin", "cousine",
    "dein", "deine", "deiner", "deinem", "deinen", "euer", "eure", "ganz", "echt", "so", "du", "ihr", "wir", "ich",
    "fress", "frass", "kotz", "pimmel", "penis", "schwanz", "eier", "titten", "pisse", "pisser", "zecken", "zecke",
    "juden", "tuerken", "russen", "polen", "araber", "neger", "asylanten", "auslaender", "fluechtlinge", "muslim",
    "moslem", "nazi", "nazis", "hitler", "bastard", "mongo", "behindert", "krank", "kranke", "gestoert", "bloed",
    "bloede", "idioten", "idiot", "depp", "deppen", "lappen", "penner", "opfer", "vollidioten", "gesicht", "schwul",
    "schwule", "homo", "lesben", "lesbe", "transen", "trans", "hasen", "kaputt", "tot", "blut", "fies", "elend",
    "miese", "mieses", "mies", "fuehrer", "gross", "klein", "alt", "alte", "alter", "junge", "junger", "maedchen",
    "heiss", "geil", "scheiss", "scheisse", "drecks", "dreck", "verdammt", "verfluchte", "verfickte", "verficke",
    "gott", "gottes", "mama", "papa", "mamas", "papas", "freundin", "freund", "ex", "chef", "boss", "anti", "pro",
}
LINKS = ("", "s", "es", "n", "en", "e", "er", "ens")
VERB_PREFIX = ("", "ge", "ver", "be", "ab", "an", "auf", "aus", "ein", "her", "hin", "nach", "vor", "um", "rum", "raus",
               "rein", "weg", "durch", "zer", "ent", "er", "mit", "zu", "los", "fest", "voll", "weiter", "zurueck")
_HEADS_C = {collapse(h) for h in HEADS}
_PREF_C = {collapse(h) for h in VERB_PREFIX if h}


@lru_cache(maxsize=20000)
def _decomp(p: str) -> bool:
    """Можно ли целиком разложить p на «головы» с соединительными элементами (s, n, en, e …)?"""
    if not p:
        return True
    if len(p) > 24:
        return False
    for h in _HEADS_C | _PREF_C:
        if p.startswith(h):
            rest = p[len(h):]
            for lk in LINKS:
                if rest.startswith(lk) and _decomp(rest[len(lk):]):
                    return True
    return False


class DeLex:
    """Корни слов (подстрока с проверкой составных), точные слова и исключения."""

    def __init__(self, roots=(), exact=(), exceptions=(), anywhere=()):
        self.roots = sorted({collapse(r) for r in roots if r}, key=len, reverse=True)
        self.anywhere = sorted({collapse(r) for r in anywhere if r}, key=len, reverse=True)  # длинные: подстрока ок
        self.exact = {collapse(w) for w in exact if w}
        self.exc = tuple({collapse(e) for e in exceptions if e})
        alls = self.roots + self.anywhere
        self._rx = re.compile("|".join(map(re.escape, alls))) if alls else None
        self._memo: dict = {}

    def hit(self, tok: str) -> bool:
        r = self._memo.get(tok)
        if r is None:
            r = self._hit(tok)
            if len(self._memo) > 40000:
                self._memo.clear()
            self._memo[tok] = r
        return r

    def _hit(self, tok: str) -> bool:
        t = collapse(tok)
        if len(t) < 3 or len(t) > 45:
            return False
        if t in self.exact:
            return True
        if self._rx is None or not self._rx.search(t):
            return False
        for e in self.exc:
            if e in t:
                return False
        for r in self.anywhere:
            if r in t:
                return True
        for r in self.roots:
            i = t.find(r)
            while i != -1:
                if i == 0 or _decomp(t[:i]):
                    return True
                i = t.find(r, i + 1)
        return False


# ─────────────────────────────────────────────────────────────────────────────
#  Лексиконы: мат, ненависть, 18+, дети  (все слова — в канонической записи: ae/oe/ue/ss)
# ─────────────────────────────────────────────────────────────────────────────
#  Принцип «как у русского»: в prof — только настоящий мат и персональные оскорбления; бытовое «Scheiße!»,
#  «Mist», «Kacke», «verdammt», «Idiot» ловится лишь при GUARD_DE_MILD=1 — иначе ложняков море.

PROF_ROOTS = """fick wichs fotz nutte schlampe hurenbock hurentochter hurenkind verpiss
pissnelke pisser pissbirne pissfotze arschgeige arschgesicht arschkriecher arschlecker arschficker
beschiss bescheiss scheisskerl scheissweib scheisstyp scheissfotze scheisshure scheisshund scheissnazi
scheissausl scheissdeutsch scheisstuerk scheissrussen scheissamerikaner scheissbulle scheissbullen scheissjude
hundesohn missgeburt mutterfick mutterfotz mutterhure kackhure kackfotze
drecksau dreckssau drecksack dreckskerl dreckstueck dreckschwein drecksfotze dreckshure drecksweib dreckspack dreckshund
schwanzlutsch schwanzlurch fotzenlecker vollwichs dummfotze fettfotze""".split()
PROF_ANY = """hurensohn hurensoehn arschloch arschlooch wichser wixer wixxer scheisskerl schwanzlutscher
mutterficker fotzenlecker missgeburt""".split()
PROF_EXACT = """hure huren hurerei nutte nutten fotze fotzen fresse huso husos hurso ficko fickos fick ficken ficker fickt gefickt
verfickt verficktes abgefickt aufgefickt wichse wixen wichsen wichst""".split()
PROF_EXC = """fickle fickel nuttall nuttin wichsenstein wichsberg pisserberg fotzelschnitt""".split()  # «Fichte», «Ficus» и т.п. не начинаются на «fick», но на всякий случай

# мягкие ругательства — только при GUARD_DE_MILD=1
MILD_ROOTS = """scheiss scheis kack mist verdammt verflucht verfickt depp idiot vollidiot trottel penner lappen
blödmann bloedmann bloedmann dummkopf schwachkopf pimmel pissen pisse bumsen arsch dreck sacklaus laber halt maul""".split()
MILD_EXACT = """opfer mist kacke kackt scheisse scheiss scheisse depp deppen idiot idioten pisse pissen arsch""".split()

HATE_ROOTS = """kanak kanack itaker polack kuemmeltuerk kameltreiber ziegenficker schlitzaug
judensch judensau judenpack judenhur judenbrut judenratte judenknecht
tuerkensau tuerkenpack tuerkenschlampe russensau russenschlampe russenpack polenpack araberpack
negersau negerschwein negerhur schwarzenhasser asylantenschwein auslaenderschwein fluechtlingsschwein
moslemschwein muslimschwein kopftuchschlampe schwulensau schwulette hurenschwul
spast spasti kruepp mongoloid mongolid untermensch ungeziefer volksschaedling
nigger niggar zigeunerschlampe zigeunerpack""".split()
HATE_ANY = """schwuchtel judenschwein negerschwein""".split()
HATE_EXACT = """tunte tunten transe transen behindi behindis mongo mongos kanaken itakern fidschi fidschis
zigeuner zigeunerin zigeunern zigeunerinnen neger negerin negern negerinnen""".split()
HATE_EXC = """spastisch spastik spastiker spastiken zigeunerschnitzel zigeunersauce zigeunersosse zigeunerbaron
zigeunerweisen zigeunerleben zigeunerpfanne zigeunergulasch zigeunerhut zigeunerkapelle zigeunerlied
negerkuss negerkuesse negerkoenig negerl krueppelkiefer kruepplig kanakmelas""".split()

ADULT_ROOTS = """porn titte tittenfick moese nacktbild nacktfoto nacktvideo nacktselfie sexvideo sexfilm sexbild sexfoto
sexcam sexchat sexdate sextreff sexkontakt sexanzeig sexting wichsvorlage gangbang creampie cumshot sperma
schwanzbild dickpic xhamster redtube youporn pornhub xvideos onlyfans fansly kinderporno kinderfick
paedo pedo paedophil escortservice escortagentur escortdame escortgirl callgirl callboy nacktbilder
hardcorepor spermaschluck fickfilm fickvideo fickbild fickkontakt fickanzeig bumskontakt bumsanzeig""".split()
ADULT_EXACT = """kipo kipos pornos porno pornografie pornos nude nudes nsfw dickpics hentai bukkake milf milfs
camgirl camgirls camshow cumshots orgie orgien sexsklave sexsklavin escort""".split()
ADULT_EXC = """tittel tittling tittmoning pornhubert pedometer pedoman pedocal pedologie pedal pedantisch sexismus sexistisch sexuell pornoton""".split()

MINOR_ROOTS = """kind minderjaehr schueler schuelerin teenie teenager kleinkind jugendlich kleinmaedchen maedchen
baby babys lolita lolis unter18 u18 grundschul kindergarten schulkind""".split()
MINOR_EXACT = """teen teens loli shota kids kid cp u16 u14 u12 u13 u15 u17""".split()
MINOR_EXC = """kindle kindergeld kindle kinderschokolade""".split()

# слова-«цели» для масок (f*ck) и для фонетического поиска
MASK_TARGETS = {
    "arschloch": "prof", "hurensohn": "prof", "ficken": "prof", "fick": "prof", "ficker": "prof", "gefickt": "prof",
    "wichser": "prof", "fotze": "prof", "schlampe": "prof", "nutte": "prof", "hure": "prof", "missgeburt": "prof",
    "verpiss": "prof", "schwuchtel": "hate", "kanake": "hate", "neger": "hate", "spast": "hate",
    "scheisse": "mild", "scheiss": "mild", "porno": "adult", "titten": "adult", "nigger": "hate", "judensau": "hate",
}
FUZZY_TARGETS = {
    "hurensohn": "prof", "arschloch": "prof", "schlampe": "prof", "wichser": "prof", "missgeburt": "prof",
    "schwuchtel": "hate", "mutterficker": "prof", "schwanzlutscher": "prof", "arschgeige": "prof",
    "fotzenlecker": "prof", "kinderporno": "adult", "judensau": "hate", "hurenkind": "prof", "arschkriecher": "prof",
}
# слова, которые случайно «близки» к целям (никогда не считаем ругательством при нечётком поиске)
FUZZY_SAFE = frozenset("""wichtel wichtig wichteln wechsler schlange schlampig schlimme schlamm arschlos arbeiter
wachter wachsen wischer wischen wasche hurensohnen kinderparty kinderporto kinderportal kinderpornos""".split())

# ─────────────────────────────────────────────────────────────────────────────
#  Фразы (ненависть, угрозы, 18+) — на plain-тексте (a-z и пробелы)
# ─────────────────────────────────────────────────────────────────────────────

def _rx(*parts: str) -> "re.Pattern":
    return re.compile("|".join(parts))


HATE_PHRASES = [
    (re.compile(r"\b(?:sieg|zieg|seig|sig)\s*heil\b"), "Sieg Heil"),
    (re.compile(r"\bheil\s+hitler\b|\bhail\s+hitler\b|\bhitlergruss\b|\bheil\s+h\b"), "Heil Hitler"),
    (re.compile(r"\b(?:juden|auslaender|tuerken|muslime|moslems|fluechtlinge|asylanten|neger|schwule|schwuchteln|araber|russen)\s+raus\b"), "«… raus»"),
    (re.compile(r"\bdeutschland\s+den\s+deutschen\b|\bblut\s+und\s+boden\b|\bauslaender\s+(?:raus|loswerden)\b|\bremigration\s+jetzt\b"), "лозунг"),
    (re.compile(r"\b(?:alle|diese|die)\s+(?:juden|muslime|moslems|tuerken|auslaender|fluechtlinge|asylanten|schwulen|schwuchteln|neger|schwarzen|araber|russen|polen|behinderten|transen|lesben)\s+(?:muessen|sollten|gehoeren|sollen)\s+\w*\s*(?:sterben|vergast|abgeschoben|aufgehaengt|erschossen|verrecken|erschlagen|ausgerottet|weg|verbrannt)\b"), "призыв к насилию"),
    (re.compile(r"\b(?:ab\s+(?:in|ins|nach)\s+(?:die\s+)?(?:gaskammer|gas|auschwitz|dachau|buchenwald|treblinka)|vergasen|vergast\s+(?:sie|ihn|alle|euch|dich)|in\s+die\s+gaskammer)\b"), "газовая камера"),
    (re.compile(r"\b(?:auschwitzluege|holocaustluege|holocaust\s+(?:ist\s+)?(?:eine\s+)?luege|holocaustleugn\w*|holocaust\s+gab\s+es\s+nie)\b"), "отрицание Холокоста"),
    (re.compile(r"\b(?:du|ihr|ey|alter|so\s+ein|dieser|diese|der|die)\s+(?:dreckige[rn]?\s+|scheiss\s+|elende[rn]?\s+|fette[rn]?\s+)?jude(?:n)?\b"), "«Jude» как ругательство"),
    (re.compile(r"\b(?:du|ihr|ey|alter|bist|seid|biste|bisch|so|voll|total|echt|komplett)\s+(?:so\s+|voll\s+|total\s+|echt\s+|komplett\s+|richtig\s+)?(?:behindert(?:e|er|es)?|gestoert|mongo)\b(?!\s*(?:gerecht|en\s*gerecht|parkplatz|toilette|aufzug|fahrzeug))"), "«behindert» как ругательство"),
    (re.compile(r"\b(?:du|ihr|ey|alter)\s+(?:schwule[rn]?|schwuchtel|homo)\b|\b(?:schwule|schwuler)\s+(?:sau|sack|hund|bastard|hurensohn|nutte|fotze|opfer)\b|\bdas\s+ist\s+(?:so\s+|voll\s+|total\s+)?schwul\b"), "«schwul» как ругательство"),
    (re.compile(r"\b(?:du|ihr|ey|alter|bist|seid|biste|dieser|diese|so\s+ein(?:e)?)\s+(?:(?:ein|eine)\s+)?(?:dreckige[rn]?\s+|scheiss\s+|elende[rn]?\s+|verdammte[rn]?\s+|fette[rn]?\s+|stinkende[rn]?\s+)?(?:nazi|nazis|nazischwein|nazihure|nazisau|nazipack)\b|\b(?:nazi|nazis)(?:schwein|sau|hure|pack|schlampe|bastard|opfer|hurensohn|fotze)\b"), "«Nazi» как ругательство"),
    (re.compile(r"\b(?:du|ihr|ey|alter|dieser|diese)\s+(?:dreckige[rn]?\s+|scheiss\s+|elende[rn]?\s+)?(?:affe|affen|ratte|ratten|parasit|parasiten|ungeziefer|abschaum|gesindel|untermensch(?:en)?)\b"), "расовое оскорбление"),
]

THREAT_PHRASES = [
    re.compile(r"\bich\s+(?:bring|bringe|werde|werd|will|muss|moechte)\s+(?:dich|euch|ihn|sie)\s+(?:\w+\s+){0,2}(?:um|tot|kalt|ab)\b"),
    re.compile(r"\bich\s+(?:toete|erstech\w*|erschiess\w*|erwuerg\w*|zerstueck\w*|vergewaltig\w*|abstech\w*|abknall\w*|abmurks\w*|aufschlitz\w*|erschlag\w*|zerleg\w*|schlitz\w*)\s+(?:dich|euch|ihn|sie)\b"),
    re.compile(r"\bich\s+(?:werde|werd|will|werde\s+dich)\s+(?:dich\s+)?(?:finden|toeten|umbringen|fertigmachen|vernichten|zerstoeren|killen|abstechen|erschiessen)\b"),
    re.compile(r"\b(?:stirb|stirbst\s+hoffentlich|verreck|verrecke|krepier|krepiere|erhaenge\s+dich|haeng\s+dich\s+auf|erschiess\s+dich|bring\s+dich\s+um|toete\s+dich|bringt\s+euch\s+um|nimm\s+(?:dir\s+)?(?:den\s+)?strick|such\s+dir\s+(?:einen\s+|nen\s+)?strick|geh\s+sterben|geh\s+und\s+stirb|spring\s+(?:von|aus|vor)\s+(?:der|dem|die|den)\s+\w+)\b"),
    re.compile(r"\b(?:ich\s+)?(?:wuensch\w*|hoffe?)\s+(?:dir|euch|dass\s+(?:du|ihr)|du|ihr)\b[^.!?]{0,30}\b(?:krebs|sterb\w*|stirbst|verreck\w*|aids|krepier\w*|den\s+tod|unfall)\b"),
    re.compile(r"\bhoffentlich\s+(?:stirbst|verreckst|krepierst|erkrankst|bekommst\s+du\s+krebs|kriegst\s+du\s+krebs)\b"),
    re.compile(r"\bich\s+(?:weiss|kenn\w*|find\w*)\s+(?:wo\s+du\s+(?:wohnst|lebst|arbeitest)|deine\s+(?:adresse|wohnung|familie|schule))\b"),
    re.compile(r"\b(?:ich\s+)?(?:schick\w*|hetz\w*)\s+(?:dir|euch)\s+(?:die\s+)?(?:polizei|jungs|leute|mafia|clan|bande)\s+(?:auf\s+den\s+hals|vorbei)\b"),
    re.compile(r"\b(?:deine|eure)\s+(?:mutter|familie|eltern|schwester|oma)\b[^.!?]{0,25}\b(?:vergewaltig\w*|abstech\w*|umbringen|toeten|anzuenden|erschiessen)\b"),
]
KYS_RX = re.compile(r"(?<![a-z])k\s?y\s?s(?![a-z])")
BANTER_RX = re.compile(r"\b(?:ha(?:ha)+|hihi|hehe|lol|lmao|rofl|xd+|kek|scherz|joke|spass|witz|ironie|nur\s+spass|jk|"
                       r"nicht\s+ernst|war\s+nur\s+ein\s+witz|im\s+spiel|ingame|boss|lobby|noob|tryhard|ranked|1v1|cs2?|valorant|fortnite|minecraft|zocken|gamen)\b|[😂🤣😅😆😜😝]")

ADULT_PHRASES = [
    re.compile(r"\b(?:feuchte|nasse|geile|enge|rasierte|kleine|heisse)\s+muschi\b|\bmuschi\s+(?:lecken|fick\w*|bild\w*|video\w*)\b"),
    re.compile(r"\b(?:schick|sende|zeig|verkaufe|kaufe|tausche|biete)\w*\s+(?:mir\s+|dir\s+|uns\s+)?(?:deine?\s+|meine?\s+|geile\s+)?(?:nudes?|nacktbilder|nacktfotos|titten|dickpics?)\b"),
    re.compile(r"\b(?:geile|heisse|nackte|junge)\s+(?:frauen|maedels|girls|hausfrauen|omas|teens|milfs|schlampen|muttis)\s+(?:in\s+deiner\s+naehe|warten|suchen|wollen|zeigen)\b"),
]


# ─────────────────────────────────────────────────────────────────────────────
#  Сборка словарей и функция сканирования
# ─────────────────────────────────────────────────────────────────────────────

_custom_allow: set = set()           # слова из «allow:» guard (добавляются при install)

PROF = DeLex(PROF_ROOTS, PROF_EXACT, PROF_EXC, anywhere=PROF_ANY)
HATE = DeLex(HATE_ROOTS, HATE_EXACT, HATE_EXC, anywhere=HATE_ANY)
ADULT = DeLex(ADULT_ROOTS, ADULT_EXACT, ADULT_EXC)
MINOR = DeLex(MINOR_ROOTS, MINOR_EXACT, MINOR_EXC)
MILD_LEX = DeLex(MILD_ROOTS, MILD_EXACT, ())
_AGE_RX = re.compile(r"\b(?:[89]|1[0-7])[\s-]*(?:jaehrig\w*|jahre\s+alt|j)\b|\b(?:unter|u)\s*18\b")
_FZ = {t: (koelner(t), collapse(t)) for t in FUZZY_TARGETS}


@lru_cache(maxsize=30000)
def _fuzzy(tok: str):
    if not (7 <= len(tok) <= 16) or tok in FUZZY_SAFE:
        return None
    c = collapse(tok)
    k = koelner(tok)
    for tgt, (code, tc) in _FZ.items():
        if abs(len(c) - len(tc)) > 2:
            continue
        if k == code:
            lim = 1 if len(tc) <= 8 else 2
        elif len(tc) >= 9:
            lim = 1                                  # длинные цели: одна подмена буквы («hvrensohn») без совпадения фонетики
        else:
            continue
        if osa(c, tc, lim) <= lim:
            return FUZZY_TARGETS[tgt]
    return None


@lru_cache(maxsize=2048)
def _mask_regex(raw: str):
    parts, i = [], 0
    while i < len(raw):
        if raw[i] in "*#":
            j = i
            while j < len(raw) and raw[j] in "*#":
                j += 1
            k = j - i
            parts.append("[a-z]{%d,%d}" % (max(1, k - 1), k + 2))
            i = j
        else:
            parts.append(re.escape(raw[i]))
            i += 1
    return re.compile("^" + "".join(parts) + "$")


def _mask_hits(raw: str):
    rx = _mask_regex(raw)
    hits = [(tgt, cat) for tgt, cat in MASK_TARGETS.items() if rx.match(tgt)]
    if any(c == "mild" for _, c in hits):          # «sch***e» — скорее «Scheiße», чем «Schlampe»
        yield hits[[c for _, c in hits].index("mild")]
    else:
        yield from hits[:1]


@lru_cache(maxsize=4096)
def scan_de(text: str) -> dict:
    """Сканирование немецкого текста. Возвращает {'prof','hate','adult','minor','threat','mild','notes'}."""
    n = dnorm(text)
    out = {"prof": [], "hate": [], "adult": [], "minor": False, "threat": [], "mild": [], "notes": []}
    seen = set()
    views = n.tokens + n.deleet + n.spaced
    for tok in views:
        if tok in seen:
            continue
        seen.add(tok)
        if tok in _custom_allow:
            continue
        got = False
        if PROF.hit(tok):
            out["prof"].append(tok); got = True
        if HATE.hit(tok):
            out["hate"].append(tok); got = True
        if ADULT.hit(tok):
            out["adult"].append(tok); got = True
        if MINOR.hit(tok):
            out["minor"] = True
        if MILD and MILD_LEX.hit(tok):
            out["mild"].append(tok); got = True
        if not got and FUZZY_ON and len(tok) >= 7:
            cat = _fuzzy(tok)
            if cat in ("prof", "hate", "adult"):
                out[cat].append(tok)
                out["notes"].append("фонетика: " + tok)
    for raw in n.masks:
        for tgt, cat in _mask_hits(raw):
            if cat == "mild":
                if MILD:
                    out["mild"].append(raw)
            else:
                out[cat].append(raw)
            break
    plain = n.plain
    for rx, why in HATE_PHRASES:
        if rx.search(plain):
            out["hate"].append(why)
    for rx in ADULT_PHRASES:
        if rx.search(plain):
            out["adult"].append("18+ фраза")
    if _AGE_RX.search(plain):
        out["minor"] = True
    banter = bool(BANTER_RX.search(text.lower()))
    if not banter or out["prof"] or out["hate"]:
        for rx in THREAT_PHRASES:
            if rx.search(plain):
                out["threat"].append("угроза/призыв")
                break
        if KYS_RX.search(plain) and "угроза/призыв" not in out["threat"]:
            out["threat"].append("kys")
    for k in ("prof", "hate", "adult", "mild"):
        out[k] = list(dict.fromkeys(out[k]))
    return out


# ─────────────────────────────────────────────────────────────────────────────
#  Немецкие спам-правила для guard.SPAM_RULES  (формат: имя, группа, вес, regex, причина)
# ─────────────────────────────────────────────────────────────────────────────
#  guard сам прогоняет их по fold()-тексту (ä→a, ü→u, ö→o, ß остаётся). Люди пишут и «für», и «fuer», и «fur»,
#  поэтому G() раскрывает умляуты в альтернативы. Правила специально узкие: «слово + контекст», а не одно слово.

def G(p: str) -> "re.Pattern":
    p = (p.replace("ä", "(?:ae|a)").replace("ö", "(?:oe|o)").replace("ü", "(?:ue|u)").replace("ß", "(?:ß|ss)"))
    return re.compile(p)


_DE_RULES_SRC = [
    # ── работа / «лёгкие деньги» ────────────────────────────────────────────────────────────────────────
    ("de_earn_pitch", "job", 2.5, r"\b(?:verdien\w*|einkommen|einnahmen|gewinn\w*)\b[^.!?\n]{0,60}\b(?:ohne\s+(?:startkapital|eigenkapital|erfahrung|vorkenntnisse|investition\w*|risiko|einlage)|pro\s+(?:tag|woche|stunde)|täglich|wöchentlich|am\s+tag|von\s+zu\s?hause|per\s+handy|mit\s+dem\s+(?:handy|smartphone))", "обещание лёгкого заработка"),
    ("de_earn_online", "job", 2.5, r"\bverdien\w*\s+(?:dein\s+|mehr\s+|echtes\s+|schnell\s+)?(?:geld|euro)\s+(?:online|im\s+internet|per\s+handy|von\s+zu\s?hause|nebenbei|bei\s+telegram)|\bgeld\s+(?:verdien\w+|machen)\s+(?:online|im\s+internet|per\s+handy|mit\s+dem\s+(?:handy|smartphone)|von\s+zu\s?hause|bei\s+telegram|über\s+telegram|nebenbei|im\s+schlaf)|\bonline\s+(?:geld\s+)?verdienen\b|\bgeld\s+(?:im\s+schlaf|ohne\s+arbeit)\b", "заработок онлайн / с телефона"),
    ("de_earn_word", "job", 1.5, r"\b(?:nebenverdienst\w*|dazuverdien\w*|dazu\s+verdien\w*|zusatzverdienst\w*|nebeneinkommen)\b", "разговор о подработке"),
    ("de_extra_income", "job", 2.0, r"\b(?:zusätzliche[sn]?\s+(?:einkommen|einnahmen|verdienst)|zusatzeinkommen|zweites\s+standbein|finanzielle\s+(?:freiheit|unabhängigkeit)|finanziell\s+unabhängig)", "«дополнительный доход / финансовая свобода»"),
    ("de_passive", "job", 2.0, r"\bpassive[sn]?\s+(?:einkommen|einnahmen)\b|\bgeld\s+für\s+(?:sich\s+)?arbeiten\s+lassen\b|\bgeld\s+arbeiten\s+lassen\b", "пассивный доход"),
    ("de_phone_work", "job", 2.5, r"\b(?:arbeit|job|verdienst|nebenjob|geld)\s+(?:nur\s+)?(?:per|mit|am|vom|über)\s+(?:dem\s+)?(?:handy|smartphone|telefon)\b|\bnur\s+(?:ein\s+)?(?:handy|smartphone)\s+(?:und|benötigt|nötig|brauch)", "работа «только с телефона»"),
    ("de_no_exp", "job", 2.0, r"\bohne\s+(?:vorkenntnisse|erfahrung|startkapital|eigenkapital|investition\w*|vorerfahrung|eigenes\s+geld|berufserfahrung|einlage)\b", "«без опыта/вложений»"),
    ("de_hours_day", "job", 2.0, r"\b(?:nur\s+|schon\s+|bereits\s+|ca\.?\s+|circa\s+)?\d[\d\-–]*\s*stunden?\s+(?:am\s+tag|pro\s+tag|täglich)\b[^.!?\n]{0,40}(?:verdien|einkommen|euro|€)", "«пара часов в день» + доход"),
    ("de_income_num", "job", 3.0, r"(?<![\d.,])\d[\d.,\s]{1,6}\s*(?:€|euro|eur|usd|\$|dollar)\s*(?:am\s+tag|pro\s+(?:tag|woche|stunde)|täglich|wöchentlich|/\s*(?:tag|woche|std))", "сумма «в день/неделю»"),
    ("de_income_goal", "job", 2.5, r"\b(?:bis\s+zu|ab|von)\s+\d[\d.,\s]{1,6}\s*(?:€|euro|eur)\b[^.!?\n]{0,25}(?:verdien|täglich|pro\s+(?:tag|woche)|am\s+tag|nebenbei)|\bverdien\w*\s+(?:bis\s+zu|ab|von|mindestens|etwa|ca\.?|circa)\s*\d[\d.,\s]{1,6}\s*(?:€|euro|eur|\$)", "обещание дохода в цифрах"),
    ("de_task_scam", "job", 3.0, r"\b(?:aufgaben|tasks?|bewertungen|bewerten|liken|likes|kommentare?|videos?\s+(?:liken|anschauen|ansehen)|hotels?\s+bewerten|produkte\s+bewerten|apps?\s+(?:bewerten|testen)|bestellungen\s+(?:optimieren|bestätigen)|daten\s+optimieren)\b[^.!?\n]{0,60}\b(?:verdien\w*|bezahl\w*|vergüt\w*|provision\w*|belohn\w*|lohn|euro|€|pro\s+(?:aufgabe|task|bewertung|like|video)|täglich)|\b\d+\s*(?:€|euro)\s*(?:für|pro|je)\s+(?:jede[ns]?\s+)?(?:like|bewertung|aufgabe|task|video|kommentar|klick|stern)\b", "Task-Scam: деньги за лайки/оценки/задания"),
    ("de_hiring", "job", 2.0, r"\b(?:wir\s+suchen|suche|gesucht|stellen\s+ein|biete)\s+(?:dringend\s+)?(?:(?:noch\s+)?(?:weitere\s+)?(?:motivierte|zuverlässige|fleißige|seriöse|engagierte|aktive)\s+)?(?:mitarbeiter\w*|personal|teammitglieder\w*|helfer\w*|partner\w*|leute|personen|mädels|frauen|damen|jungs|studenten|schüler|rentner|hausfrauen)\b[^.!?\n]{0,60}\b(?:online|home\s*office|handy|remote|nebenbei|verdien\w*|heimarbeit|telegram|whatsapp|flexibel)", "набор сотрудников «онлайн»"),
    ("de_side_job", "job", 1.5, r"\b(?:nebenjob\w*|minijob\w*|heimarbeit|online\s*job\w*|remote\s*job\w*|job\s+von\s+zu\s?hause|arbeit\s+von\s+zu\s?hause|jobangebot\w*|stellenangebot\w*)\b", "подработка / удалёнка"),
    ("de_target", "job", 2.0, r"\b(?:für|geeignet\s+für|ideal\s+für|auch\s+für)\s+(?:studenten|schüler|rentner|hausfrauen|mütter|mamas|alleinerziehende|arbeitslose|berufstätige|quereinsteiger|anfänger)\b[^.!?\n]{0,50}(?:job|verdien|einkommen|nebenverdienst|geld|euro)", "«для студентов/мам» + заработок"),
    ("de_proven", "job", 1.5, r"\b(?:bewährte[rn]?|erprobte[rn]?|funktionierende[rn]?)\s+(?:methode|system|strategie|geschäftsmodell)\b|\bgeheime[rn]?\s+(?:methode|strategie|trick)\b|\bergebnisse?\s+(?:ab|schon\s+nach)\s+(?:dem\s+)?ersten\s+tag", "«проверенный метод»"),
    ("de_daily_pay", "job", 2.0, r"\b(?:auszahlung|bezahlung|lohn|gehalt)\s+(?:täglich|jeden\s+tag|sofort|nach\s+(?:jeder\s+)?(?:aufgabe|schicht))|\btägliche\s+(?:auszahlung|bezahlung|lohnauszahlung)|\bbezahlung\s+(?:am\s+selben|noch\s+am)\s+tag", "оплата каждый день"),
    ("de_collab", "job", 1.5, r"\b(?:suche|suchen|biete)\s+(?:seriöse|zuverlässige|motivierte|ehrliche|engagierte)\s+(?:leute|menschen|personen|partner|zusammenarbeit)|\bseriöse\s+zusammenarbeit\b", "«ищу людей для сотрудничества»"),
    ("de_closed", "job", 2.0, r"\b(?:exklusive?|geschlossene?|private?|vip)\s+(?:gruppe|community|kanal|chat|team|zugang|plätze)\b[^.!?\n]{0,40}(?:beitreten|zugang|platz|plätze|anmeld|aufnahme|kostenlos|gratis)|\bnur\s+noch\s+\d+\s+(?:freie\s+)?(?:plätze|stellen)\b", "набор в закрытое сообщество"),
    ("de_hallo_mama_strong", "illegal", 4.0, r"\bhallo\s+(?:mama|papa|mutti|vati|oma|opa)\b[^.!?\n]{0,80}\b(?:neue\s+(?:handy)?nummer|nummer\s+gewechselt|speicher\w*\s+(?:die|meine|diese)\s+(?:neue\s+)?nummer)", "«Hallo Mama»: мошенник с «новым номером»"),
    ("de_hallo_mama", "illegal", 2.5, r"\bhallo\s+(?:mama|papa|mutti|vati|oma|opa)\b[^.!?\n]{0,70}\b(?:neue\s+nummer|handy\s+(?:kaputt|verloren|gestohlen)|nummer\s+gewechselt|speicher\w*\s+(?:die|meine)|neues\s+handy)", "«Hallo Mama»: мошенник с «новым номером»"),

    # ── призывы написать / перейти ──────────────────────────────────────────────────────────────────────────
    ("de_cta_dm", "cta", 2.0, r"\b(?:schreib\w*|meld\w*|kontaktier\w*|wende\w*)\b[^.!?\n]{0,25}\b(?:pn|dm|dms|privat\w*|whatsapp|telegram|inbox|privatnachricht\w*|direktnachricht\w*)\b", "зовёт в личку"),
    ("de_dm_hint", "cta", 0.8, r"(?:^|[\s,.;:!?])(?:per\s+)?pn(?=$|[\s,.;:!?)])|\bschreib(?:t)?\s+(?:mir|uns)\W*$", "«пиши / PN»"),
    ("de_cta_word", "cta", 2.5, r"\b(?:schreib\w*|sende\w*|schick\w*)\s+(?:mir\s+|uns\s+)?(?:einfach\s+|kurz\s+|nur\s+)?(?:das\s+)?(?:stich|code|schlüssel|kenn)?wort\s*[«\"“„']?\w+|\bschreib\w*\s+(?:mir\s+|uns\s+)?(?:einfach\s+|kurz\s+)?[«\"“„'](?:info|infos|job|jobs|start|bereit|interesse|dabei|plus|geld)[»\"”“']", "«напиши слово …»"),
    ("de_cta_plus", "cta", 2.0, r"\b(?:schreib\w*)\s*(?:mir\s+)?\+(?!\w)|(?:^|\s)\+\s*(?:in|per)?\s*(?:pn|dm|privat)\b", "«пиши +»"),
    ("de_cta_detail", "cta", 1.8, r"\b(?:details?|infos?|informationen|einzelheiten|anleitung|bedingungen)\b[^.!?\n]{0,25}\b(?:nur\s+)?(?:per|über|via|in|im)\s+(?:pn|dm|privat\w*|whatsapp|telegram|direkt\w*)\b", "детали — только в личке"),
    ("de_cta_profile", "cta", 2.5, r"\b(?:klick\w*|tipp\w*|geh\w*|schau\w*|guck\w*|check\w*)\s+(?:auf\s+|in\s+|mal\s+|einfach\s+)*(?:mein\w*\s+)?(?:profil|bio|avatar|profilbild|beschreibung)\b|\blink\s+(?:in|im|ist\s+in)\s+(?:meiner\s+|der\s+|meinem\s+|meine\s+)?(?:bio|profil|beschreibung)", "«ссылка в профиле»"),
    ("de_subscribe", "cta", 1.2, r"\b(?:abonnier\w*|folg\w*)\s+(?:mir|uns|meinem|unserem|jetzt)\s*(?:kanal|channel|gruppe|chat|seite)?|\b(?:tritt|tretet|komm|kommt)\s+(?:jetzt\s+)?(?:in\s+)?(?:meinen|unseren|meine|unsere|mein|unser)\s+(?:kanal|channel|gruppe|chat|community|team)\b", "зовёт подписаться"),
    ("de_tg_promo", "cta", 1.5, r"\b(?:mein|unser)\w*\s+(?:telegram\s*)?(?:kanal|channel|bot)\b(?=[^.!?\n]{0,30}(?:t\.me|@|link|beitreten|join|klick))", "реклама канала/бота"),
    ("de_cta_formal", "cta", 1.5, r"\b(?:kontaktieren\s+sie\s+(?:uns|mich)|melden\s+sie\s+sich|rufen\s+sie\s+(?:uns|mich)?\s*(?:an|unter)|antworten\s+sie\s+(?:auf\s+diese|mit)\b)", "формальный призыв связаться"),

    # ── срочность ──────────────────────────────────────────────────────────────────────────────────────────
    ("de_urgency", "urgency", 1.5, r"\b(?:nur\s+(?:noch\s+)?heute|nur\s+noch\s+\d+\s+(?:plätze|stück|tage|stunden|std)|jetzt\s+(?:handeln|zugreifen|sichern)|letzte\s+chance|solange\s+(?:der\s+)?vorrat|begrenzte[rs]?\s+(?:angebot|plätze|anzahl|zeit)|angebot\s+(?:endet|läuft\s+ab)|beeil\w*\s+(?:dich|euch|sie)|nicht\s+verpassen|zeitlich\s+begrenzt|nur\s+für\s+kurze\s+zeit|sichere?\s+dir\s+(?:jetzt|deinen|deine)|nur\s+noch\s+heute)", "давление срочностью"),

    # ── инвестиции / кредиты ──────────────────────────────────────────────────────────────────────────────
    ("de_crypto", "invest", 1.2, r"\b(?:krypto\w*|bitcoin\w*|btc|ethereum|usdt|trading\w*|trader\w*|daytrading|forex|binäre\s+optionen|cfd\w*|handelssignal\w*|staking|airdrop\w*)\b", "крипта / трейдинг"),
    ("de_invest_promise", "invest", 3.0, r"\b(?:garantiert\w*|risikolos\w*|risikofrei\w*|verdopp\w*|vervielfach\w*|verdreifach\w*)\b[^.!?\n]{0,40}\b(?:gewinn\w*|rendite\w*|profit\w*|einkommen|ertrag|erträge|zinsen|verdienst|einsatz|investition|einlage|krypto\w*|bitcoin\w*)|\b\d{2,4}\s?%\s+(?:rendite|gewinn|profit|zinsen|ertrag|pro\s+(?:tag|woche|monat)|täglich|wöchentlich|am\s+tag|in\s+\d+\s+(?:tagen|stunden|wochen))|\b(?:verdopple|verdopplung|verdoppeln)\s+(?:dein|ihr|euer|das)\w*\s+(?:geld|kapital|investition|einsatz|bitcoin)", "гарантированная прибыль"),
    ("de_invest_signals", "invest", 2.0, r"\b(?:vip|premium|kostenlose[rn]?|geheime[rn]?|kostenpflichtige[rn]?|profi|insider)[\s-]+(?:signale|signal|trading[\s-]?signale|tipps|handelssignale|kursziele)\b|\bsignale\s+(?:gruppe|kanal|abo)\b|\binsider\s*(?:tipp|info\w*)", "платные/«инсайдерские» сигналы"),
    ("de_loan", "sale", 3.0, r"\b(?:kredit\w*|darlehen|sofortkredit|privatkredit|geld|kleinkredit|ratenkredit)\s+(?:ohne|trotz)\s+(?:schufa|bonitätsprüfung|bonität|vorkosten|sicherheiten|absage|einkommensnachweis|bürgen)|\b(?:schufa|bonitäts?)[\s-]*(?:frei\w*|neutral\w*|unabhängig)\b[^.!?\n]{0,30}(?:kredit|darlehen)|\bohne\s+(?:schufa|bonitätsprüfung)\b|\b(?:kredit|darlehen)\s+(?:sofort|schnell)\s+auf[s]?\s+(?:dein|das|ihr)?\s*konto", "«кредит без Schufa/отказа»"),
    ("de_prize_fee", "illegal", 3.0, r"\b(?:gewinn|gewonnen|erbschaft|lotterie|darlehen|kredit|auszahlung)\b[^.!?\n]{0,60}\b(?:bearbeitungsgebühr\w*|freigabegebühr\w*|vorauszahlung|anzahlung|vorkasse|vorab\s+(?:bezahlen|überweisen|zahlen)|kaution)\b", "«выигрыш/кредит» за предоплату"),
    ("de_finance_agent", "illegal", 3.0, r"\b(?:finanz|paket|waren|zahlungs|zahlungsverkehrs|geld|krypto|crypto|handels)[\s-]*(?:agent|agenten|agentin|assistent|assistenten|assistentin|kurier|vermittler)\b|\breship\w*|\btreuhand[\s-]*(?:service|dienst|konto)\b|\b(?:pakete?|waren|sendungen)\s+(?:annehmen|weiterleiten|weiterversenden|umpacken)\b[^.!?\n]{0,40}(?:verdien\w*|provision|euro|€|bezahl\w*|vergütung|nebenjob|nebenverdienst)|\bkonto\s+(?:zur\s+verfügung\s+stellen|vermieten|verleihen|ausleihen)", "Finanz-/Paketagent: схема отмывания"),

    # ── казино / ставки ────────────────────────────────────────────────────────────────────────────────────
    ("de_casino", "gamble", 2.5, r"\b(?:online[\s-]*casino\w*|casino[\s-]*(?:bonus|online|app|spiele\w*|empfehlung\w*|test|vergleich|neu\w*|ohne)|spielothek\w*|sportwetten|wettanbieter|wettbonus|freispiele?|free\s*spins?|einzahlungsbonus|willkommensbonus|roobet|mostbet|bet365|tipico|lapalingo|crypto[\s-]*casino|slots?\s+(?:spielen|bonus|casino))\b", "казино / ставки"),
    ("de_oasis", "gamble", 3.0, r"\b(?:ohne|umgeh\w+|trotz)\s+(?:oasis|sperrdatei|spielersperre|lugas)\b|\boasis[\s-]*(?:frei|free)\b|\bohne\s+(?:einzahlungslimit|limit)\b[^.!?\n]{0,30}casino", "«казино без OASIS» (обход самозапрета)"),
    ("de_bonus_dep", "gamble", 2.0, r"\b(?:bonus|freispiele?|free\s*spins?|cashback|gutschein|willkommensgeschenk)\b[^.!?\n]{0,40}\b(?:einzahlung|einzahl\w*|anmeldung|registrier\w*|ersteinzahlung|deposit|ohne\s+einzahlung)|\bohne\s+(?:einzahlung|deposit)\b[^.!?\n]{0,25}bonus", "бонус за депозит/регистрацию"),
    ("de_promo_weak", "gamble", 1.2, r"\b(?:promo\s*code|promocode|bonuscode|aktionscode|einladungscode|referral)\b|\bbonus\s+(?:bei|für|nach)\s+(?:registrierung|anmeldung)\b", "промокод / бонус за регистрацию"),

    # ── 18+ ────────────────────────────────────────────────────────────────────────────────────────────────
    ("de_adult_ad", "adult_ad", 2.5, r"\b(?:erotik\w*\s*(?:massage|kontakte|treffen|anzeigen)|sex[\s-]*(?:kontakte?|treffen|anzeigen|dates?|chat|cam|video\w*|bilder|fotos?)|sexcam\w*|escort[\s-]*(?:service|girl|damen|agentur|dame)|callgirl\w*|begleitservice|diskrete?\s+(?:treffen|abenteuer|dates?|kontakte?)|casual\s*dating|one[\s-]*night[\s-]*stand|(?:geile|heiße|junge|einsame)\s+(?:frauen|mädels|girls|hausfrauen|damen|muttis|milfs?)\b[^.!?\n]{0,30}(?:in\s+deiner\s+nähe|suchen|warten|wollen|treffen|dich)|(?:verkaufe|biete)\s+(?:nudes?|nacktfotos|nacktbilder|fotos|bilder|videos|inhalte)\b|onlyfans|fansly|privatsex)", "реклама 18+"),
    ("de_age18", "adult_ad", 1.0, r"(?:^|\s)18\s?\+|\bnur\s+für\s+erwachsene\b", "метка 18+"),
    ("de_webcam", "adult_ad", 2.5, r"\b(?:webcam[\s-]*(?:job|model|modell|arbeit)|camgirl|cam[\s-]*model|livecam[\s-]*job|erotik[\s-]*(?:job|model|modell)|für\s+(?:mädels|frauen|damen|girls)\s+(?:ab\s+\d+\s+)?(?:gesucht|online)\b[^.!?\n]{0,40}(?:verdien|nebenjob|job|geld))", "вебкам / работа для девушек"),

    # ── продажа / серые схемы / запрещёнка ──────────────────────────────────────────────────────────────
    ("de_sale_spam", "sale", 2.0, r"\b(?:verkaufe|biete|kaufe|ankauf)\s+(?:(?:fertige|gehackte|verifizierte|alte|neue|echte|geprüfte)\s+)?(?:accounts?|konten|follower|abonnenten|likes|views|datenbank\w*|traffic|logins?|zugangsdaten|kreditkarten|dumps?|cvv|kontodaten|kundendaten|leads?)\b|\b(?:follower|likes|abonnenten|views|kommentare)\s+(?:kaufen|bestellen|steigern|boost\w*)\b|\binstagram[\s-]*follower\b", "продажа аккаунтов / накрутка"),
    ("de_docs_sale", "illegal", 3.5, r"\b(?:führerschein|ausweis|reisepass|personalausweis|diplom|zeugnis|attest|krankschreibung|gelbe[rn]?\s+schein|au[\s-]?bescheinigung|impfpass|impfausweis)\s+(?:kaufen|bestellen|ohne\s+prüfung|fälschung|fälschen|registriert|online\s+bestellen)\b|\b(?:gefälschte|falsche|echte\s+registrierte)\s+(?:führerschein\w*|ausweis\w*|papiere|dokumente|reisepässe|euro|geldscheine|rezepte|impfpässe)\b|\bfalschgeld\b|\bblüten\b[^.!?\n]{0,15}(?:euro|kaufen)|\bkrankschreibung\s+(?:ohne\s+arzt|kaufen|sofort\s+per)", "поддельные документы / фальшивые деньги"),
    ("de_docs_real", "illegal", 2.0, r"\b(?:führerschein|ausweis|reisepass|impfpass|impfausweis|zeugnis|diplom|attest)\w*\b[^.!?\n]{0,50}\b(?:echte?[rn]?\s+(?:und\s+)?registriert\w*|registriert\w*\s+und\s+echt\w*|alles\s+registriert|ohne\s+prüfung|ohne\s+theorie|ohne\s+fahrschule|ohne\s+untersuchung)\b|\b(?:echte?[rn]?\s+(?:und\s+)?registriert\w*|ohne\s+prüfung|ohne\s+fahrschule)\b[^.!?\n]{0,50}\b(?:führerschein|ausweis|reisepass|impfpass|impfausweis|zeugnis|diplom|attest)", "«настоящие/зарегистрированные» документы"),
    ("de_cashout", "illegal", 3.0, r"\b(?:geldwäsche|geld\s*waschen|schwarzgeld|carding|(?:kreditkarten|cvv)[\s-]*(?:daten|dumps|shop)|bankdrop\w*|bank[\s-]*drops?|drop[\s-]*konten|konten?\s+(?:mieten|kaufen)\s*(?:für|gegen)|ec[\s-]*karten?\s+(?:gegen|verkaufen|mieten)|sim[\s-]*karten?\s+(?:registrieren\s+)?(?:verkaufe\w*|gegen\s+geld)|paysafecard[\s-]*(?:codes?|pins?)\s+(?:kaufen|verkaufe\w*|tausch\w*|gegen))\b", "обнал / серые схемы"),
    ("de_occult", "sale", 2.0, r"\b(?:liebeszauber|partnerrückführung|ex[\s-]*partner\s+zurück\w*|schwarze\s+magie|voodoo|wahrsager\w*|kartenleger\w*|hellseher\w*|fluch\w*\s+(?:aufheben|entfernen|lösen)|geisterheiler|geistheiler|marabout)\b", "услуги «магов»"),
    ("de_drugs_sale", "illegal", 3.5, r"\b(?:kokain\w*|koks|mdma|ecstasy|xtc|lsd|ketamin\w*|crystal\s*meth|heroin|amphetamin\w*|subutex|oxycodon\w*|tilidin|tramadol|xanax|benzos?|ritalin|adderall|pillen|2c-?b|pregabalin|lyrica)\b[^.!?\n]{0,60}\b(?:kaufen|bestell\w*|verkaufe\w*|zu\s+verkaufen|lieferung|liefere\w*|versand|diskret\w*|express|anonym|ohne\s+rezept|vorkasse|dealer|shop|großhandel|ankauf)|\b(?:kaufen|bestell\w*|verkaufe\w*|liefere\w*|lieferung)\b[^.!?\n]{0,60}\b(?:kokain\w*|koks|mdma|ecstasy|xtc|lsd|ketamin\w*|crystal\s*meth|heroin|amphetamin\w*|subutex|oxycodon\w*|tilidin|tramadol|xanax|benzos?|ritalin|adderall|pillen|pregabalin|lyrica)\b", "продажа запрещённых веществ"),
    ("de_vendor_contact", "illegal", 3.0, r"\b(?:kokain|koks|mdma|ecstasy|xtc|lsd|ketamin\w*|heroin|amphetamin\w*|meth|pillen|weed|gras|cannabis|haschisch|marihuana|bubatz|pregabalin|xanax|tilidin)\b[^\n]{0,80}\b(?:diskret\w*|express|anonym\w*|vorkasse|lieferung|versand)\b[^\n]{0,60}(?:telegram|wickr|threema|signal|whatsapp|@\w{4,}|\bpn\b)", "анонимная доставка запрещённого + контакт"),
    ("de_drugs_weed", "illegal", 2.5, r"\b(?:weed|gras|cannabis|haschisch|hasch|marihuana|bubatz|cbd|thc|vapes?)\b[^.!?\n]{0,50}\b(?:versand|lieferung|diskret\w*|anonym|express|dealer|vorkasse|wickr|menge|großhandel|ohne\s+rezept)\b|\b(?:versand|lieferung|diskret\w*|anonym|dealer|vorkasse|wickr)\b[^.!?\n]{0,50}\b(?:weed|cannabis|haschisch|marihuana|bubatz)\b", "продажа каннабиса"),
    ("de_darknet", "illegal", 2.0, r"\b(?:darknet|darkweb|dark\s*web|onion[\s-]*(?:shop|link))\b[^.!?\n]{0,40}\b(?:shop|markt|kaufen|bestell\w*|link|adresse|vendor)\b", "даркнет-магазин"),
    ("de_weapons", "illegal", 3.0, r"\b(?:scharfe?|echte?|ungeregistrierte?|illegale?)\s+(?:waffen|pistolen?|schreckschuss\w*|glock\w*|munition)\b[^.!?\n]{0,40}\b(?:kaufen|verkaufe\w*|bestell\w*|lieferung|ohne\s+(?:waffenschein|papiere|kontrolle))|\b(?:waffen|pistolen?|munition|granaten?)\b[^.!?\n]{0,30}\b(?:ohne\s+(?:waffenschein|papiere|kontrolle|ausweis)|schwarzmarkt|illegal\s+kaufen)", "продажа оружия"),

    # ── розыгрыши / фишинг ─────────────────────────────────────────────────────────────────────────────────
    ("de_giveaway", "promo", 1.2, r"\b(?:gewinnspiel\w*|verlosung\w*|verlosen|giveaway\w*|gratis\s+(?:geschenk|iphone|ps5|gutschein|geld)|du\s+hast\s+gewonnen|sie\s+haben\s+gewonnen|herzlichen\s+glückwunsch\W+(?:du|sie|ihr)\s+(?:hast|haben|habt)|gewinner\s+(?:ausgewählt|gezogen)|iphone\s+\d+\s+(?:gewonnen|gratis|geschenkt)|gutschein\w*\s+(?:im\s+wert|über)\s+\d+|\d+\s*(?:€|euro)\s+(?:gutschein|geschenkt|startguthaben)\b)", "розыгрыш-приманка"),
    ("de_phish_account", "promo", 2.5, r"\b(?:ihr|dein|euer)\w*\s+(?:konto|account|paypal|bankkonto|zugang|karte|amazon[\s-]*konto|apple[\s-]*id|steam[\s-]*konto|telegram[\s-]*konto|whatsapp)\b[^.!?\n]{0,60}\b(?:gesperrt|eingeschränkt|deaktiviert|gehackt|kompromittiert|ungewöhnlich\w*|verdächtig\w*|abgelaufen|suspendiert|gelöscht|limitiert|vorläufig|verifizier\w*|bestätig\w*)\b|\b(?:konto|account)\w*\s+(?:wurde|wird|werden|wurden)\s+(?:gesperrt|eingeschränkt|deaktiviert|gehackt|gelöscht|limitiert)\b", "«ваш аккаунт заблокирован» (фишинг)"),
    ("de_phish_action", "promo", 2.5, r"\b(?:bestätig\w*|verifizier\w*|aktualisier\w*|entsperr\w*|freischalt\w*|reaktivier\w*)\s+(?:sie\s+)?(?:jetzt\s+|umgehend\s+|sofort\s+|bitte\s+|hier\s+|ihre?\s+|deine?\s+|die\s+)*(?:daten|identität|konto|account|zugang|zahlungsdaten|bankdaten|kartendaten|tan|pushtan|sicherheitsapp|sicherheitsverfahren|kundennummer|mobilnummer)\b", "просьба «подтвердить данные»"),
    ("de_smishing_parcel", "promo", 3.0, r"\b(?:ihr|dein)\w*\s+(?:paket|sendung|lieferung|pakete)\b[^.!?\n]{0,70}\b(?:zurückgestellt|zurückgehalten|konnte\s+nicht\s+zugestellt|nicht\s+zugestellt|zustellung\s+(?:fehlgeschlagen|nicht\s+möglich)|hängt\s+fest|adresse\s+(?:unvollständig|fehlt|ungültig|bestätigen)|hausnummer|lagergebühr\w*|nachporto|zollgebühr\w*|zustellgebühr\w*)|\b(?:dhl|hermes|dpd|gls|ups|deutsche\s+post)\b[^.!?\n]{0,50}\b(?:paket|sendung)\b[^.!?\n]{0,50}\b(?:gebühr\w*|adresse|hausnummer|bestätig\w*|zurückgestellt|aktualisier\w*)|\b(?:fehlende[rn]?|unvollständige[rn]?)\s+(?:hausnummer|adresse|zustelladresse)\b", "DHL/Post-фишинг (посылка, адрес, пошлина)"),
    ("de_bank_push", "promo", 2.5, r"\b(?:pushtan|push[\s-]?tan|s[\s-]?pushtan|securego|tan[\s-]?verfahren|tan[\s-]?app|girocard|sparkasse|volksbank|raiffeisenbank|postbank|commerzbank|deutsche\s+bank|ing[\s-]?diba|dkb|n26|comdirect|targobank|hypovereinsbank|paydirekt|klarna|paypal|santander)\b[^.!?\n]{0,70}\b(?:auslaufen|ablaufen|läuft\s+ab|abgelaufen|erneuer\w*|umstellung|aktivier\w*|reaktivier\w*|freischalt\w*|gesperrt|sperrung|abgeschaltet|deaktivier\w*|sicherheitsupdate|verifizier\w*|legitimation|bestätigung|unberechtigt\w*|betrugsversuch|verdächtig\w*|ungewöhnlich\w*)", "банк/PushTAN-фишинг"),
    ("de_authority", "promo", 2.0, r"(?=[^\n]*\b(?:sie|ihre?[nmrs]?|ihnen)\b)\b(?:polizei|kripo|staatsanwaltschaft|bka|europol|zoll|finanzamt|bundesamt|arbeitsagentur|jobcenter|gericht|inkasso|rechtsanwalt|anwaltskanzlei|gerichtsvollzieher|bundesnetzagentur)\b[^.!?\n]{0,70}\b(?:ermittlungsverfahren|strafanzeige|haftbefehl|vorladung|mahnbescheid|pfändung|zwangsvollstreckung|bußgeld|strafbefehl|geldstrafe|letzte[rn]?\s+mahnung|zahlungsaufforderung|steuerrückerstattung|rückerstattung|unverzüglich|umgehend)", "«письмо от ведомства» (полиция/налоговая/коллекторы)"),
    ("de_support_impersonation", "promo", 2.5, r"\b(?:telegram|whatsapp|paypal|amazon|steam|discord|apple|google|microsoft)[\s-]*(?:support|team|sicherheit\w*|service|kundenservice)\b[^.!?\n]{0,50}(?:konto|account|verifizier|sperr|code|passwort|bestät)", "«поддержка сервиса» просит данные"),
    ("de_code_ask", "promo", 4.0, r"\b(?:sende|schick\w*|gib|nenne|teile|schreib|übermittle)\w*\s+(?:mir\s+|uns\s+)?(?:den\s+|deinen\s+|dein\s+|ihren?\s+)?(?:sms[\s-]?code|bestätigungscode|verifizierungscode|login[\s-]?code|telegram[\s-]?code|seed[\s-]?phrase|wiederherstellungsphrase)\b", "просит SMS-код/seed-фразу"),
    ("de_pass_ask", "promo", 2.5, r"\b(?:sende|schick\w*|gib|nenne|teile|schreib)\w*\s+(?:mir\s+|uns\s+)?(?:den\s+|deinen\s+|dein\s+|ihren?\s+)?(?:tan|passwort|kennwort|zugangsdaten)\b", "просит пароль/TAN"),
]

DE_SPAM_RULES = [(n, g, w, G(p), why) for n, g, w, p, why in _DE_RULES_SRC]

# немецкие «приметы» для FAMILIES guard (две приметы подряд = слабый сигнал, три = сильный)
DE_FAMILIES = {
    "money": r"\b(?:geld\w*|verdien\w*|einkommen|einnahmen|gewinn\w*|rendite\w*|profit\w*|kredit\w*|darlehen|krypto\w*|bitcoin\w*|einzahl\w*|auszahl\w*|gehalt|provision\w*|passiv\w*|€\s?\d+|\d+\s?€|\d+\s?(?:euro|eur)\b)",
    "work": r"\b(?:nebenjob\w*|nebenverdienst\w*|heimarbeit|homeoffice|home-office|stellenangebot\w*|minijob\w*|bewerb\w*|mitarbeiter\w*|ohne\s+erfahrung|ohne\s+vorkenntnisse|quereinsteiger\w*|selbstständig\w*|geschäftsmodell|geschäftsidee|partnerprogramm|remote)",
    "cta": r"\b(?:schreib\w*\s+(?:mir|uns|mich)|schreibt\s+mir|melde\w*\s+(?:dich|euch)\s+(?:bei\s+mir|per|über|via)|kontaktier\w*\s+(?:mich|uns)|whatsapp|link\s+in\s+(?:der\s+)?bio|klick\w*\s+(?:auf|hier)|jetzt\s+(?:anmelden|registrieren|beitreten)|\bpn\b|privat\w*\s+nachricht)",
    "hype": r"\b(?:gratis|kostenlos\w*|umsonst|garantiert\w*|risikofrei|bonus\w*|geschenk\w*|gutschein\w*|nur\s+heute|begrenzt\w*|limitiert\w*|100\s?%|reich\s+werden|schnelles\s+geld)",
    "sale": r"\b(?:verkaufe|ankauf|accounts?\s+(?:kaufen|verkauf)|follower\s+kaufen|likes\s+kaufen|abonnenten\s+kaufen|zugangsdaten)",
}

DE_BRANDS = {
    "sparkasse": {"sparkasse.de", "s-pushtan.de", "sparkasse.com"},
    "postbank": {"postbank.de"},
    "commerzbank": {"commerzbank.de"},
    "deutschebank": {"deutsche-bank.de", "db.com"},
    "volksbank": {"vr.de", "volksbank.de", "raiffeisenbank.de", "vr-bank.de"},
    "comdirect": {"comdirect.de"},
    "targobank": {"targobank.de"},
    "paydirekt": {"paydirekt.de"},
    "klarna": {"klarna.com", "klarna.de"},
    "dhl": {"dhl.de", "dhl.com", "deutschepost.de", "paket.de"},
    "deutschepost": {"deutschepost.de", "deutsche-post.de"},
    "hermes": {"myhermes.de", "hermesworld.com", "hermes-europe.co.uk"},
    "kleinanzeigen": {"kleinanzeigen.de", "ebay-kleinanzeigen.de"},
    "ebay": {"ebay.de", "ebay.com", "ebaycdn.net"},
    "vinted": {"vinted.de", "vinted.com"},
    "zalando": {"zalando.de", "zalando.com"},
    "telekom": {"telekom.de", "t-online.de", "magenta.de"},
    "vodafone": {"vodafone.de", "vodafone.com"},
    "elster": {"elster.de"},
    "arbeitsagentur": {"arbeitsagentur.de"},
    "finanzamt": {"finanzamt.de"},
    "lieferando": {"lieferando.de"},
    "booking": {"booking.com"},
    "disney": {"disney.com", "disneyplus.com"},
    "paysafecard": {"paysafecard.com"},
}
DE_BAIT = set("gewinnspiel gutschein geschenk gratis kostenlos gewinn freispiele willkommensbonus verlosung geldgeschenk "
              "kredit sofortkredit nebenjob verdienen".split())
DE_SENSITIVE = set("verifizierung verifizieren sicherheitscheck freischaltung freischalten pushtan tanfreigabe "
                   "kontosperrung sperrung entsperren legitimation reaktivierung kundenkonto kontoverifizierung".split())

DE_STOP = frozenset("""der die das den dem des ein eine einen einem einer und oder aber doch denn weil dass ob wenn als wie wo
was wer ich du er sie es wir ihr mich dich sich uns euch ihm ihn mir dir mein meine dein deine ist bin bist sind seid war
waren hat habe hast haben habt wird werde wirst werden kann muss soll will nicht kein keine nur auch noch schon mal immer
wieder sehr so dann da hier jetzt heute mit von zu bei nach aus auf an in im am zum zur vom beim fur uber unter vor durch
gegen ohne um bis alle alles viel mehr man""".split())

# конфликт-приманки (провокации) на немецком — для guard._BAIT_RX (fold-текст без умляутов)
DE_BAIT_RX = tuple(G(p) for p in (
    r"\bniemand\s+(?:hat\s+)?(?:dich\s+)?(?:gefragt|interessiert|will\s+das\s+(?:hören|wissen))\b|\bkeinen\s+interessiert\s+(?:es|das)\b",
    r"\bberuhig\s+dich\b|\bkomm\s+(?:mal\s+)?runter\b|\bganz\s+ruhig\b|\bentspann\s+dich\b|\bkühl\s+dich\s+ab\b",
    r"\bwas\s+ist\s+(?:denn\s+)?(?:los\s+)?mit\s+dir\b|\bhast\s+du\s+(?:heute\s+)?(?:schlecht\s+geschlafen|probleme|stress)\b|\bprobleme\s+(?:zu\s+hause|zuhause|in\s+der\s+familie)\b",
    r"\bgeh\s+(?:mal\s+)?(?:an\s+die\s+frische\s+luft|raus|spielen|schlafen)\b|\bsuch\s+dir\s+(?:ein\s+)?(?:hobby|leben|freunde|job)\b|\btouch\s+grass\b",
    r"\bwie\s+alt\s+bist\s+du\b|\bkindergarten\b|\bdu\s+bist\s+(?:doch\s+)?(?:noch\s+)?(?:ein\s+)?kind\b|\bhast\s+du\s+nichts\s+besseres\s+zu\s+tun\b",
    r"\bheul\s+doch\b|\bnimm\s+(?:es\s+)?nicht\s+so\s+ernst\b|\bcry\s+about\s+it\b|\bcope\b|\bseethe\b|\bmad\s+(?:bro|weil)\b|\bgetroffene\s+hunde\s+bellen\b",
    r"\bdu\s+bist\s+(?:so\s+)?(?:ein\s+)?(?:clown|witzfigur|witz|lachnummer|schwätzer|labertasche)\b|\bpeinlich\b[^.!?\n]{0,20}\bdu\b",
    r"\bimmer\s+(?:du|dasselbe)\b|\btypisch\s+du\b|\bwie\s+immer\b[^.!?\n]{0,25}\bdu\b|\bdu\s+(?:schon\s+)?wieder\b",
))

# «кукольный театр»: вопросы/подтверждения (puppet-детектор guard) на немецком
DE_ASK_RX = tuple(G(p) for p in (
    r"\b(?:hat|kennt|weiß|weiss)\s+(?:jemand|wer|einer|irgendwer)\b[^.!?\n]{0,50}\b(?:erfahrung|probiert|getestet|benutzt|genutzt|gehört|schon\s+mal|ausgezahlt|ausbezahlt|bekommen)",
    r"\bist\s+(?:das|es|der|die)\b[^.!?\n]{0,25}\b(?:seriös|legit|sicher|echt|abzocke|betrug|fake|scam|vertrauenswürdig)\b|\b(?:seriös|legit|abzocke|betrug|fake)\s*\?",
    r"\b(?:lohnt|lohnt\s+sich)\b[^.!?\n]{0,20}\?|\bsinnvoll\s*\?|\bfunktioniert\s+(?:das|es)\s+(?:wirklich|überhaupt)\b|\bzahlt\s+(?:das|es|die)\s+(?:wirklich|überhaupt)\b",
    r"\b(?:könnt|kannst)\s+(?:ihr|du)\s+(?:mir\s+)?(?:empfehlen|helfen)\b[^.!?\n]{0,50}\b(?:broker|börse|plattform|seite|bot|app|krypto|geld|verdien)",
    r"\bwo\s+(?:kann\s+man|bekomme\s+ich|finde\s+ich)\b[^.!?\n]{0,40}\b(?:geld\s+verdienen|krypto\s+kaufen|usdt|bitcoin|auszahlen|umtauschen)",
))
DE_CLAIM_RX = G(r"\b(?:ausgezahlt|ausbezahlt|auszahlung\s+(?:bekommen|erhalten|erhalten)|bekommen|erhalten|verdient|abgehoben|angekommen|eingegangen|gutgeschrieben|funktioniert|seriös|legit|empfehle|empfehlen|empfohlen|benutze|nutze|vertrauenswürdig|kein\s+betrug|keine\s+abzocke|garantiert|geprüft|getestet)\b")
DE_CONFIRM_RX = tuple(G(p) for p in (
    r"(?<!nicht\s)\b(?:funktioniert|klappt|geklappt|ausgezahlt|ausbezahlt|angekommen|eingegangen|gutgeschrieben|bestätige|bestätigt|seriös|legit|kein\s+betrug|keine\s+abzocke)\b",
    r"\b(?:danke|vielen\s+dank|dankeschön)\b[^.!?\n]{0,25}\b(?:für\s+(?:den\s+)?(?:link|tipp|hinweis|info|infos|empfehlung)|dir|euch)\b|\bhabe\s+(?:auch|ebenfalls)\s+(?:bekommen|verdient|ausgezahlt|erhalten)\b|\bbei\s+mir\s+(?:auch|ebenfalls)\b[^.!?\n]{0,20}\b(?:geklappt|funktioniert|angekommen)",
))
DE_VERIFY_RX = G(r"\b(?:verifizier\w*|verifikation|bestätige?\s+(?:deine|ihre)\s+(?:identität|daten|konto)|bonus\s+(?:aktivier\w*|abholen|sichern)|drück\w*\s+(?:auf\s+)?(?:start|starten)|schreib\w*\s+(?:dem\s+)?bot\b|abonnier\w+\s+(?:unseren|meinen|diesen)\s+kanal|(?:hol|sicher)\w*\s+dir\s+(?:deinen\s+)?(?:bonus|gewinn|preis|auszahlung))")
DE_GIVE_BRAND_RX = G(r"\b(?:telegram|premium|toncoin|ton|durov|elon|musk|usdt|bitcoin|nft|paypal|amazon|apple|iphone|ps5|playstation|xbox|tesla)\b")
DE_GIVE_WALLET_RX = G(r"\b(?:wallet|geldbörse|verbind\w+|connect|seed|seed[\s-]?phrase|wiederherstellungsphrase|anmelden\s+mit\s+wallet)\b")


# ─────────────────────────────────────────────────────────────────────────────
#  Контакты: немецкие номера и IBAN  (идут в «сеть контактов» guard)
# ─────────────────────────────────────────────────────────────────────────────

_SEP = r"[\s\-./()]*"
_DE_MOBILE = re.compile(r"(?<![\d\w])(?:(?:\+|00)\s?49" + _SEP + r"\(?0?\)?" + _SEP + r"|0\s?)1[5-7]\d" + _SEP +
                        r"(?:\d" + _SEP + r"){7,9}(?!\d)")
_DE_PREMIUM = re.compile(r"(?<![\d\w])(?:0\s?900|0\s?137|0\s?180[1-9]?|0\s?190)[\s\-./]?\d[\d\s\-./]{3,9}\d(?!\d)")
_IBAN_RE = re.compile(r"(?<![A-Za-z0-9])[A-Za-z]{2}\d{2}(?:[ ]?[A-Za-z0-9]{4}){3,7}(?:[ ]?[A-Za-z0-9]{1,4})?(?![A-Za-z0-9])")


def iban_ok(s: str) -> bool:
    s = re.sub(r"\s+", "", s).upper()
    if not (15 <= len(s) <= 34) or not re.fullmatch(r"[A-Z]{2}\d{2}[A-Z0-9]+", s):
        return False
    if s.startswith("DE") and len(s) != 22:
        return False
    num = "".join(str(int(c, 36)) for c in s[4:] + s[:4])
    return int(num) % 97 == 1


def find_ibans(text: str) -> list:
    out = []
    for m in _IBAN_RE.finditer(text[:3000]):
        if iban_ok(m.group(0)):
            out.append(re.sub(r"\s+", "", m.group(0)).upper())
    return out


# ─────────────────────────────────────────────────────────────────────────────
#  «Письмо на Вы»: регистр чата (du / Sie) и формальный фишинг
# ─────────────────────────────────────────────────────────────────────────────

_REG: "OrderedDict[int, list]" = OrderedDict()      # id(cfg) → [du, sie]  (счётчики с затуханием)
_DU_RX = re.compile(r"\b(?:du|dich|dir|dein|deine|deinen|deinem|deiner|bist|hast|kannst|willst|musst|machst|gehst|"
                    r"weisst|brauchst|ihr|euch|eure|seid|habt)\b")
_SIE_RX = re.compile(r"\bsie\s+(?:koennen|haben|sind|muessen|moechten|werden|wurden|bitte|erhalten|wollen|duerfen|sollten)\b|"
                     r"\b(?:koennen|haben|moechten|duerfen|sollten|wuerden)\s+sie\b|\b(?:ihnen|ihrem|ihrer)\b")
_F_SALUT = re.compile(r"\bsehr\s+geehrte[rs]?\s+(?:damen|herr|frau|kunde|kundin|kunden|nutzer|user|mitglied|teilnehmer)\w*|"
                      r"\bliebe[rs]?\s+(?:kunde|kundin|kunden|nutzer|user)\b|\bhallo\s+kunde\b")
_F_POSS = re.compile(r"\bihre?[nmrs]?\s+(?:konto|account|paket|sendung|daten|zahlung|bestellung|karte|tan|zugang|rechnung|vertrag|"
                     r"identitaet|bankverbindung|adresse|nummer|kundennummer|sparkasse|postbank)\b|"
                     r"\b(?:bestaetigen|pruefen|aktualisieren|verifizieren|loggen|melden|klicken|rufen|zahlen|ueberweisen|handeln|"
                     r"antworten|folgen)\s+sie\b")
_F_DEAD = re.compile(r"\binnerhalb\s+von\s+\d+\s*(?:stunden|std|tagen|werktagen)\b|\bumgehend\b|\bunverzueglich\b|\bandernfalls\b|"
                     r"\bansonsten\s+(?:wird|werden|muessen)\b|\bletzte[rn]?\s+(?:mahnung|warnung|aufforderung|frist)\b|\bfrist\b|"
                     r"\bzwangsvollstreckung\b|\binkasso\b|\bpfaendung\b|\bstrafanzeige\b|\bkonto\s+(?:wird|wurde)\s+(?:gesperrt|geschlossen)\b|"
                     r"\bbis\s+(?:spaetestens\s+)?(?:zum\s+)?\d{1,2}\.\s?\d{1,2}\.")


def _reg_note(cfg, text_plain: str) -> None:
    if not REGISTER_ON or cfg is None:
        return
    du = len(_DU_RX.findall(text_plain))
    sie = len(_SIE_RX.findall(text_plain))
    if not (du or sie):
        return
    k = id(cfg)
    rec = _REG.get(k)
    if rec is None:
        rec = _REG[k] = [0.0, 0.0]
        if len(_REG) > 1500:
            _REG.popitem(last=False)
    else:
        _REG.move_to_end(k)
    rec[0] += min(du, 3)
    rec[1] += min(sie, 3)
    if rec[0] + rec[1] > 400:
        rec[0] /= 2
        rec[1] /= 2


def chat_is_du(cfg) -> bool:
    """В чате общаются на «du» (достаточно данных и перевес ≥ 80 %)."""
    rec = _REG.get(id(cfg)) if cfg is not None else None
    if not rec:
        return False
    tot = rec[0] + rec[1]
    return tot >= 25 and rec[0] / tot >= 0.8


def formal_phish(plain: str, has_link_or_phone: bool) -> tuple:
    """Возвращает (число признаков, список)."""
    feats = []
    if _F_SALUT.search(plain):
        feats.append("обращение «Sehr geehrte…»")
    if _F_POSS.search(plain):
        feats.append("«Ihr Konto / bestätigen Sie»")
    if _F_DEAD.search(plain):
        feats.append("срок/угроза последствий")
    if has_link_or_phone:
        feats.append("ссылка/телефон")
    return len(feats), feats


# ─────────────────────────────────────────────────────────────────────────────
#  Щит контекста (меньше ложных срабатываний)
# ─────────────────────────────────────────────────────────────────────────────

_BENIGN_TOKENS = frozenset("fagot kikeriki fukushima fukuoka fukuyama fukui".split())    # уже «collapse»-формы guard
_HEIL_OK = re.compile(r"\bheil\s+(?:angekommen|geblieben|zurueck|davon|ueberstanden|nach\s+hause|und\s+gesund|und\s+munter|"
                      r"wieder|gelandet|durchgekommen)\b|\bpetri\s+heil\b|\bheile?\s+welt\b|\bganz\s+und\s+heil\b|\bheil\s+und\b")
_HEIL_BAD = re.compile(r"\b(?:sieg|zieg|seig)\s*heil\b|\bheil\s+(?:hitler|h)\b|\bhail\b")
_NAZI_CTX = re.compile(r"\bnazis?\s+raus\b|\bgegen\s+(?:die\s+)?nazis?\b|\bkein\s+platz\s+fuer\s+nazis?\b|\bnie\s+wieder\b|"
                       r"\bnazi[\s-]*(?:deutschland|zeit|regime|diktatur|herrschaft|gold|verbrechen|vergleich|keule|symbol\w*|propaganda|"
                       r"partei|ideologie|verbrecher)\b|\bnationalsozialis\w*|\bdritte[nm]?\s+reich\b|\bweltkrieg\b|\bgedenk\w*|"
                       r"\bstolperstein\w*|\bgeschichte\b|\bdemo\b|\bdemonstration\b|\bafd\b|\bantifa\w*|\bfaschis\w*")
_CASINO_BENIGN = re.compile(r"\b(?:film|kino|royale|bond|serie|dokumentation|doku|besucht\w*|besuch|ausflug|gebaeude|schloss|hotel|restaurant|"
                            r"spielbank|las\s+vegas|monaco|monte\s+carlo|urlaub|gestern|waren|war\s+im|im\s+casino|haus\s+des\s+geldes|"
                            r"mensa|kantine|uni|campus)\b")
_WARN_RX = re.compile(r"\bwarnt\b|\bwarnung\s+vor\b|\bvorsicht\s+vor\b|\bbetrugsmasche\w*|\bphishing\w*|\babzocke\b|\bscam\b|\bfake\b|"
                      r"\bnicht\s+(?:auf\s+den\s+link\s+)?klick\w*|\bklickt\s+nicht\b|\bnicht\s+darauf\s+rein|\bfaellt\s+nicht\s+rein|"
                      r"\bverbraucherzentrale\b|\bpolizei\s+warnt\b|\bso\s+erkennt\b|\bbetrueger\b|\bhabe\s+(?:gerade\s+)?eine\s+(?:mail|sms|nachricht)\s+bekommen|"
                      r"\bist\s+das\s+(?:echt|fake|betrug|seriös|serioes)\b|\bsteht\s+in\s+der\s+(?:mail|sms)\b")
_WARN_SIGS = frozenset("de_phish_account de_phish_action de_smishing_parcel de_bank_push de_authority de_support_impersonation "
                       "de_pass_ask de_code_ask de_sie_soft de_giveaway promo".split())
_CASINO_INTENT = re.compile(r"\b(?:bonus|einzahl\w*|registrier\w*|jetzt|gratis|kostenlos|freispiel\w*|echtgeld|gewinn\w*|spiel\w*|wett\w*|"
                            r"setz\w*|verlier\w*|chips|roulette|poker|blackjack|automat\w*|anmeld\w*|schreib\w*|link)\b")
_REPORT_RX = re.compile(r"\b(?:sagt|sagte|sagen|rief|ruft|schrie|nannte|nennt|genannt|beschimpft\w*|beleidigt\w*|zitat|steht|stand|schrieb|"
                        r"schreibt|meinte|antwortete|hat\s+gesagt|singt|text|lied|song|film|serie|szene|video|schiri|schiedsrichter|kommentar)\b")
_META_RX = re.compile(r"\b(?:das\s+wort|der\s+begriff|ausdruck|schimpfwort|beleidigung\w*|beleidigt\w*|beschimpf\w*|zitat|zitiert|"
                      r"bedeutet|heisst\s+auf|uebersetz\w*|nennt\s+man|genannt|rassistisch\w*|sexistisch\w*|diskriminier\w*|"
                      r"verboten|gesperrt\s+(?:weil|wegen)|filter|zensur)\b")
_QUOTE_RX = re.compile(r"[„“\"»«'‚‘’](.{1,60}?)[“\"«»'‘’]")


def _in_quotes(text_l: str, toks: list) -> bool:
    spans = [m.group(1) for m in _QUOTE_RX.finditer(dnorm(text_l).text)]
    if not spans:
        return False
    joined = " ".join(spans)
    jc = collapse(re.sub(r"[^a-z]", "", joined))
    return all(collapse(t) in jc for t in toks)


# ─────────────────────────────────────────────────────────────────────────────
#  Подготовка текста: «двойники» букв и разнесённые буквы
# ─────────────────────────────────────────────────────────────────────────────

_CYR_ANY = re.compile(r"[а-яёіїєґͰ-Ͽ]", re.I)
_LAT_ANY = re.compile(r"[A-Za-zÄÖÜäöüß]")
_SPACED_RX = re.compile(r"(?<![\w])(?:[A-Za-zÄÖÜäöüß] ){3,}[A-Za-zÄÖÜäöüß](?![\w])")


def _deobf(text: str) -> tuple:
    """(текст, число слов с «двойниками», число склеенных разнесённых слов). URL/@/домены не трогаем."""
    homo = joined = 0
    out = text
    if _CYR_ANY.search(out) and _LAT_ANY.search(out):
        parts = re.split(r"(\s+)", out)
        for i, p in enumerate(parts):
            if not p or p.isspace() or re.search(r"[/@.:]", p):
                continue
            if _CYR_ANY.search(p) and _LAT_ANY.search(p):
                fixed = "".join(_HOMO.get(c, _HOMO.get(c.lower(), c)) if c.lower() in _HOMO else c for c in p)
                if fixed != p and re.fullmatch(r"[A-Za-zÄÖÜäöüß0-9'’\-!?,;:*]+", fixed):
                    parts[i] = fixed
                    homo += 1
        out = "".join(parts)
    if " " in out and _SPACED_RX.search(out):
        cnt = 0

        def j(m):
            nonlocal cnt
            cnt += 1
            return m.group(0).replace(" ", "")
        cand = _SPACED_RX.sub(j, out)
        if cnt and (cnt >= 2 or is_german(cand, 0.2)):          # одиночное «a b c d» в обычной речи не трогаем
            out, joined = cand, cnt
    return out, homo, joined


# ─────────────────────────────────────────────────────────────────────────────
#  Обёртка над guard.analyze_text
# ─────────────────────────────────────────────────────────────────────────────

_G = {"mod": None, "allow_n": -1}
_RULE_GIVEAWAY = next(r for r in DE_SPAM_RULES if r[0] == "de_giveaway")[3]
_HAS_HARD = {"de_sie_phish", "de_giveaway_combo"}


def _sync_allow(g) -> None:
    allow = getattr(g, "_custom", {}).get("allow", [])
    if len(allow) != _G["allow_n"]:
        _G["allow_n"] = len(allow)
        _custom_allow.clear()
        for w in allow:
            w = (w or "").strip().lower().lstrip("=")
            if w:
                _custom_allow.add(w)
                _custom_allow.add(dnorm(w).plain.replace(" ", ""))
        scan_de.cache_clear()


def _add_contact(a, tok: str) -> None:
    if tok not in a.contacts:
        a.contacts = tuple(dict.fromkeys(tuple(a.contacts) + (tok,)))[:8]


def _post(g, a, text: str, cfg, joined: int, homo: int) -> None:
    _sync_allow(g)
    dn = dnorm(text)
    ger = is_german(text)
    found = a.found if isinstance(a.found, dict) else {}
    found.setdefault("prof", []); found.setdefault("hate", []); found.setdefault("adult", []); found.setdefault("minor", False)
    sig = a.signals
    de = scan_de(text)

    # 1) ложные срабатывания «русских/английских» корней guard на немецких словах
    if found["prof"]:
        found["prof"] = [t for t in found["prof"] if t not in _BENIGN_TOKENS]
    if found["hate"]:
        keep = []
        for t in found["hate"]:
            if t in _BENIGN_TOKENS and not re.search(r"\bfagg?ot\b|\bfagot\b", dn.text):
                continue
            if t == "fagot" and re.search(r"\bfagott", dn.text):
                continue
            if t == "heil":
                if _HEIL_OK.search(dn.plain) or (ger and not _HEIL_BAD.search(dn.plain)):
                    continue
            if t in ("nazi", "nazis") and SHIELD_ON and (ger or _NAZI_CTX.search(dn.plain)):
                if not any("Nazi" in h for h in de["hate"]):
                    continue
            keep.append(t)
        found["hate"] = keep

    # 2) добавляем немецкие находки
    for cat in ("prof", "hate", "adult"):
        for t in de[cat]:
            if t not in found[cat]:
                found[cat].append(t)
    if MILD:
        for t in de["mild"]:
            if t not in found["prof"]:
                found["prof"].append(t)
    for t in de["threat"]:
        found["hate"].append(t)
    if de["minor"]:
        found["minor"] = True

    # 3) щит «обсуждение слова»: «Das Wort „Hurensohn“ ist eine Beleidigung»
    if SHIELD_ON and found["prof"] and ger and (_META_RX.search(dn.plain) or _REPORT_RX.search(dn.plain)):
        toks = [t for t in found["prof"] if re.fullmatch(r"[a-z]+", t)]
        outside = _QUOTE_RX.sub(" ", dn.text)
        if toks and len(toks) <= 2 and _in_quotes(text, toks) and not de["threat"] \
                and not re.search(r"\b(?:du|dich|dir|dein\w*)\b", dnorm(outside).plain):
            found["prof"] = [t for t in found["prof"] if t not in toks]
    for k in ("prof", "hate", "adult"):
        found[k] = list(dict.fromkeys(found[k]))
    a.found = found

    # 4) сигналы: «двойники» и разнесённые буквы, которые мы склеили до guard
    if homo >= 3:
        sig.append(("homoglyph", 3.0, "буквы-двойники внутри слов"))
    elif homo >= 1:
        sig.append(("homoglyph", 1.5, "буквы-двойники внутри слова"))
    if joined:
        sig.append(("spaced", 1.5, "слова «р а з н е с е н ы» буквами"))

    # 5) контакты: немецкие номера, IBAN
    raw = text[:3000]
    names = {n for n, _, _ in sig}
    if _DE_MOBILE.search(raw):
        digits = re.sub(r"\D", "", _DE_MOBILE.search(raw).group(0))
        if "phone" not in names:
            sig.append(("phone_de", 1.2, "немецкий мобильный номер"))
        a.has_contact = True
        if len(digits) >= 10:
            _add_contact(a, "tel:" + digits[-10:])
    if _DE_PREMIUM.search(raw):
        sig.append(("premium_nr", 1.5, "платный номер (0900/0137/0180)"))
    ibans = find_ibans(raw)
    if ibans:
        sig.append(("iban", 1.5, "в сообщении IBAN"))
        a.has_contact = True
        _add_contact(a, "iban:" + ibans[0][:4] + ibans[0][-8:])

    # 6) «письмо на Вы»
    contact_like = bool(a.has_contact or any(getattr(u, "kind", "") != "allowed" for u in a.urls))
    cnt, feats = formal_phish(dn.plain, contact_like)
    if cnt >= 2 and (_F_SALUT.search(dn.plain) or _F_POSS.search(dn.plain)):
        mismatch = chat_is_du(cfg)
        why = "формальное письмо: " + ", ".join(feats)
        if mismatch:
            why += " — а в этом чате все на «du»"
        if cnt >= 3:
            sig.append(("de_sie_phish", 3.0 + (1.0 if mismatch else 0.0), why))
        elif _F_DEAD.search(dn.plain):
            sig.append(("de_sie_soft", 1.8 + (0.8 if mismatch else 0.0), why))

    # 7) раздача + громкий бренд + кошелёк
    if ger and _RULE_GIVEAWAY.search(" ".join(a.norm.folded.split()) if a.norm is not None else raw.lower()):
        if DE_GIVE_BRAND_RX.search(dn.text) and (DE_GIVE_WALLET_RX.search(dn.text) or "wallet" in names):
            sig.append(("de_giveaway_combo", 3.0, "раздача + громкий бренд + кошелёк: фишинг под розыгрыш"))

    # 7b) бытовой разговор о казино («Casino Royale», «Casino in Baden-Baden») и предупреждения о фишинге
    if SHIELD_ON and ger and not a.urls and not a.has_contact:
        names2 = {n for n, _, _ in sig}
        if "casino" in names2 and not any(n.startswith("de_") for n in names2) and not _CASINO_INTENT.search(dn.plain):
            sig[:] = [s for s in sig if s[0] != "casino"]
        if _WARN_RX.search(dn.plain) and names2 & _WARN_SIGS:
            sig[:] = [s for s in sig if s[0] not in _WARN_SIGS]

    # 8) учим регистр чата только на «чистых» сообщениях
    if ger and sum(w for _, w, _ in sig if w > 0) < 1.5:
        _reg_note(cfg, dn.plain)

    a.raw = round(sum(w for _, w, _ in sig), 2)
    hs = g.HARD_SIGNALS
    a.hard = round(sum(w for n, w, _ in sig if n in hs), 2)


def _make_wrapper(g, orig):
    def analyze_text(text, ents=(), cfg=None, fwd="", known_names=()):
        if not text or not isinstance(text, str):
            return orig(text, ents, cfg, fwd, known_names)
        try:
            src, homo, joined = _deobf(text)
        except Exception:
            src, homo, joined = text, 0, 0
        a = orig(src, ents, cfg, fwd, known_names)
        try:
            _post(g, a, text, cfg, joined, homo)
        except Exception:                              # модуль не имеет права ломать модерацию
            if os.getenv("GUARD_DE_DEBUG") == "1":
                raise
        return a
    analyze_text._guard_de = True
    analyze_text._orig = orig
    analyze_text.__doc__ = getattr(orig, "__doc__", None)
    return analyze_text


# ─────────────────────────────────────────────────────────────────────────────
#  Установка
# ─────────────────────────────────────────────────────────────────────────────

def _or(old, new_pattern: str, flags: int = 0):
    return re.compile("(?:" + old.pattern + ")|(?:" + new_pattern + ")", old.flags | flags)


def install(g=None, quiet: bool = False) -> bool:
    """Подключает немецкий к модулю guard. Безопасно вызывать повторно и вместе с другими языковыми модулями."""
    if os.getenv("GUARD_DE", "1") == "0":
        return False
    if g is None:
        import guard as g                              # noqa: WPS433
    if getattr(g, "_de_installed", False):
        return False
    _G["mod"] = g
    names = {r[0] for r in g.SPAM_RULES}
    g.SPAM_RULES.extend(r for r in DE_SPAM_RULES if r[0] not in names)
    for k, pat in DE_FAMILIES.items():
        if k in g.FAMILIES:
            g.FAMILIES[k] = _or(g.FAMILIES[k], G(pat).pattern)
    g.SHADOWS.update({
        "de_dm_hint": {"de_cta_dm", "de_cta_profile", "de_cta_plus", "de_cta_formal"},
        "de_earn_word": {"de_earn_pitch", "de_earn_online", "de_income_num", "de_passive", "de_income_goal"},
        "de_promo_weak": {"de_casino", "de_oasis"},
    })
    g.HARD_SIGNALS.update(_HAS_HARD)
    for brand, hosts in DE_BRANDS.items():
        g.BRANDS.setdefault(brand, set()).update(hosts)
        g._OFFICIAL.update(hosts)
    g.BAIT.update(DE_BAIT)
    g.SENSITIVE.update(DE_SENSITIVE)
    g.LEARN_STOP = frozenset(g.LEARN_STOP) | DE_STOP
    g._BAIT_RX = tuple(g._BAIT_RX) + DE_BAIT_RX
    g._ASK_RX = tuple(g._ASK_RX) + DE_ASK_RX
    g._CONFIRM_RX = tuple(g._CONFIRM_RX) + DE_CONFIRM_RX
    g._CLAIM_RX = _or(g._CLAIM_RX, DE_CLAIM_RX.pattern)
    g._VERIFY_RX = _or(g._VERIFY_RX, DE_VERIFY_RX.pattern)
    g._GIVE_BRAND_RX = _or(g._GIVE_BRAND_RX, DE_GIVE_BRAND_RX.pattern)
    g._GIVE_WALLET_RX = _or(g._GIVE_WALLET_RX, DE_GIVE_WALLET_RX.pattern)
    g.analyze_text = _make_wrapper(g, g.analyze_text)
    g._de_installed = True
    _sync_allow(g)
    if not quiet:
        import logging
        logging.getLogger("guard").info("guard_de %s: немецкий подключён (правил спама: %d, мат/ненависть/18+/угрозы, "
                                        "фонетика: %s, щит контекста: %s, мягкие слова: %s)", VERSION_DE,
                                        len(DE_SPAM_RULES), "да" if FUZZY_ON else "нет", "да" if SHIELD_ON else "нет",
                                        "да" if MILD else "нет")
    return True


def explain(text: str, g=None) -> dict:
    """Быстрая диагностика: что видит немецкий модуль (без запуска бота)."""
    if g is None:
        import guard as g                              # noqa: WPS433
    install(g, quiet=True)
    a = g.analyze_text(text)
    out = {"german": de_score(text), "signals": a.signals, "raw": a.raw, "found": a.found, "de_scan": scan_de(text)}
    tiers = {}
    for t in ("new", "member", "veteran"):
        eff = g.effective(a, t)
        tiers[t] = (round(eff, 2), g.scam_action(eff, t))
    out["tiers"] = tiers
    return out


def main() -> None:
    """python guard_de.py            — запустить бота с немецким модулем
       python guard_de.py --explain "текст"   — разобрать сообщение и выйти"""
    import asyncio
    import guard as g                                  # noqa: WPS433
    install(g)
    args = sys.argv[1:]
    if args[:1] == ["--explain"]:
        res = explain(" ".join(args[1:]), g)
        print(f"немецкий: {res['german']}")
        for n, w, why in res["signals"]:
            print(f"  {w:>5}  {n:<22} {why}")
        print("raw =", res["raw"], "| found =", res["found"], "| tiers =", res["tiers"])
        return
    r = g.ax_cli(args) if hasattr(g, "ax_cli") else None
    if r is not None:
        raise SystemExit(r)
    if args and args[0].startswith("-") and hasattr(g, "cli"):
        raise SystemExit(g.cli(args))
    try:
        asyncio.run(g.main())
    except KeyboardInterrupt:
        pass
    except SystemExit as e:
        if e.code not in (None, 0):
            print(e.code, file=sys.stderr)
            raise


if __name__ == "__main__":
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    main()
