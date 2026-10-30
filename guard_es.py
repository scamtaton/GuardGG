#!/usr/bin/env python3
# guard_es.py — испанский модуль для guard.py (4.3+). Ловит на испанском то же, что guard ловит на русском:
# мат, ярлыки-оскорбления и призывы, 18+ (и «18+ рядом с детской темой»), спам/скам/«лёгкие деньги»,
# казино, займы, «task scam» (лайки за USDT), фишинг, продажу аккаунтов/карт, вебкам, провокации и «кукольный театр».
#
# ПОДКЛЮЧЕНИЕ (один раз, 4 строки в самом конце guard.py, ПЕРЕД блоком `if __name__ == "__main__":`):
#       try:
#           import guard_es
#           guard_es.install(sys.modules[__name__])
#       except ImportError:
#           pass
# Либо без правки guard.py вообще:  python guard_es.py   (запускает guard с испанским модулем).
# Проверка текста вручную:           python guard_es.py --check "gana 500 dolares al dia, escribeme al privado"
#
# Настройки (.env):  GUARD_ES=0 — выключить всё;  GUARD_ES_SPAM=0 — не трогать спам-правила (только мат/ненависть/18+);
#                    GUARD_ES_FRIENDS=0 — строгий режим (мягкий мат считать всегда);  GUARD_ES_THREATS=0 — не считать призывы
#                    к суициду/насилию «ненавистью»;  GUARD_ES_BAIT=0 — без «провокаций».
# Исключения: в custom_words.txt строка `allow: слово` работает и для испанских слов (например `allow: verga`).
#
# ФИШКИ (того, что обычно нет у антиспам-ботов на списках слов):
#  1) РЕЖИМ «ДРУЗЕЙ»: weón / cabrón / boludo / carajo / joder / mierda / no mames — в Латинской Америке и Испании это междометия и
#     дружеский трёп. Такие «мягкие» слова считаются, только если адресованы человеку (eres/sos/tú…, «de mierda», «vete a…»)
#     или их ≥2. Жёсткое (hijo de puta, concha de tu madre, chinga tu madre, hdp, ctm…) — всегда. Ловит злость, а не акцент.
#  2) ДВОЙНОЙ СМЫСЛ ПО КОНТЕКСТУ: polla (лотерея в Чили), pinche de cocina, hostia consagrada, gonorrea (болезнь), verga del barco,
#     concha de mar, perra-собака, Vergara, Culiacán, Putaendo, «huevos», имя Kike — не мат. Исправлены и 2 ложных у самого guard.py.
#  3) ПРАВДОПОДОБНОСТЬ ЗАРАБОТКА: «gana 3000 pesos al día» переводится в доллары по курсу страны (MXN/COP/ARS/CLP/PEN/EUR);
#     $100+/день за «лёгкую работу» — подозрительно, $300+ — абсурд (сигнал es_income_absurd). Курсы — в словаре RATES.
#  4) СЕТЬ РЕКВИЗИТОВ: IBAN / CLABE / CBU-CVU / карта (по контрольным суммам) и кошельки становятся «контактами» — один и тот же
#     реквизит у нескольких новых аккаунтов выдаёт кампанию (contact_net guard). В память идёт только хэш.
#  + нечёткий поиск длинных ругательств (gilopollas, hijoeputa), и объяснялка: `--check` показывает, ПОЧЕМУ сработало.
#
# Как это устроено (коротко): текст приводится к «испанскому скелету» (ñ сохраняется, акценты долой, v=b, c/k/qu=k, ll=y,
# h немая, z=s, ge/gi=x, удвоения гласных схлопнуты): каброн = cabrón = kabron = cabrooon, bergon = vergón, gilipoyas = gilipollas.
# Поверх: leet (p3nd3j0, put@, pvta), маски (p*ta, m!erda), разрядка (p u t a, p.u.t.a), слитно (hijodeputa, conchatumadre),
# кириллица вместо латиницы (рutа). Всё, что опасно похоже на обычные слова (computadora, disputa, reputación, Vergara,
# vergonzoso, huevos, Kike, concha-ракушка, perra-собака, forro-обивка…), НЕ считается: см. исключения и контекстные правила.
from __future__ import annotations

import logging
import os
import re
import sys
import unicodedata
from functools import lru_cache
from typing import NamedTuple

VERSION_ES = "1.0"
log_es = logging.getLogger("guard.es")


def _flag(name: str, default: bool = True) -> bool:
    v = os.getenv(name)
    if v is None or v.strip() == "":
        return default
    return v.strip().lower() not in ("0", "false", "no", "off", "нет")


ES_ON = _flag("GUARD_ES", True)
ES_SPAM = _flag("GUARD_ES_SPAM", True)
ES_THREATS = _flag("GUARD_ES_THREATS", True)
ES_BAIT = _flag("GUARD_ES_BAIT", True)


def es_reload_env() -> None:
    """Перечитать настройки (guard вызывает ax_reload_env() после загрузки .env — мы встроены в этот вызов)."""
    global ES_ON, ES_SPAM, ES_THREATS, ES_BAIT
    ES_ON = _flag("GUARD_ES", True)
    ES_SPAM = _flag("GUARD_ES_SPAM", True)
    ES_THREATS = _flag("GUARD_ES_THREATS", True)
    ES_BAIT = _flag("GUARD_ES_BAIT", True)


# ══════════════════════════════════════════════════════════════════════════════════════
#  НОРМАЛИЗАЦИЯ
# ══════════════════════════════════════════════════════════════════════════════════════
ENYE = "ŋ"          # внутренний знак для «ñ»: coño ≠ cono (без ñ — «конус»), año ≠ ano
_ZW = set("\u200b\u200c\u200d\u200e\u200f\u2060\u2061\u2062\u2063\u2064\ufeff\u00ad\u180e"
          "\u202a\u202b\u202c\u202d\u202e\u2066\u2067\u2068\u2069")
_ZW_DEL = {ord(c): None for c in _ZW}

# кириллица/греческий, похожие на латиницу (работает только внутри «смешанных» слов)
_LOOK = {"а": "a", "е": "e", "о": "o", "р": "p", "с": "c", "х": "x", "у": "y", "к": "k", "т": "t", "м": "m",
         "н": "h", "в": "b", "і": "i", "ј": "j", "ѕ": "s", "ԛ": "q", "ԝ": "w", "һ": "h", "ԁ": "d",
         "α": "a", "ε": "e", "ι": "i", "κ": "k", "ν": "v", "ο": "o", "ρ": "p", "τ": "t", "υ": "u", "χ": "x", "ω": "w"}
_LOOK_TR = str.maketrans(_LOOK)
_LOOK_CLASS = "".join(_LOOK)
_SYM = "@$!|*#%^~"
_LET = "a-z0-9" + ENYE + _LOOK_CLASS
_TOK_RE = re.compile(r"(?<![@\w])[" + _LET + r"][" + _LET + re.escape(_SYM) + r"]*")
_ASCII_L = re.compile(r"[a-z]")
_NONLAT = re.compile(r"[^\x00-\x7f" + ENYE + "]")
_SPLIT_SYM = re.compile("[" + re.escape(_SYM) + "]+")
_SPLIT_NON = re.compile(r"[^a-z" + ENYE + r"0-9]+")
# «p u t a», «p.u.t.a», «p-u-t-a», «p_u_t_a», «p*u*t*a»  (≥3 одиночных букв подряд)
_SPACED_RE = re.compile(r"(?<![a-z0-9" + ENYE + r"])(?:[a-z" + ENYE + r"][ \t.\-_·*]){2,}[a-z" + ENYE + r"](?![a-z0-9" + ENYE + r"])")
# «pu.ta», «pu-ta», «pu_ta», «mier·da»
_INNER_RE = re.compile(r"(?<![a-z0-9" + ENYE + r"])[a-z" + ENYE + r"]+(?:[.\-_·][a-z" + ENYE + r"]+){1,4}(?![a-z0-9" + ENYE + r"])")


@lru_cache(maxsize=20000)
def fold_word(w: str) -> str:
    """Свёртка отдельного слова (для словарей): акценты долой, ñ → ŋ, нижний регистр."""
    w = w.replace("ñ", ENYE).replace("Ñ", ENYE)
    w = unicodedata.normalize("NFKD", w)
    return "".join(c for c in w if not unicodedata.combining(c)).lower()


def es_fold(text: str, keep_enye: bool = True) -> str:
    """Свёртка текста: ZW долой, NFKD (жирные/полноширинные/кружочки → обычные буквы), акценты долой, нижний регистр.
    keep_enye=True: ñ → ŋ (для слов); False: ñ → n (для фраз и совместимости с guard.fold)."""
    text = text[:4500].translate(_ZW_DEL)
    text = text.replace("ñ", ENYE if keep_enye else "n").replace("Ñ", ENYE if keep_enye else "n")
    text = unicodedata.normalize("NFKD", text)
    return "".join(c for c in text if not unicodedata.combining(c)).lower()


@lru_cache(maxsize=80000)
def skel(w: str) -> str:
    """«Испанский скелет»: слова, звучащие/пишущиеся похоже, дают один и тот же скелет."""
    w = w.replace(ENYE, "ñ")
    w = w.replace("ch", "ĉ").replace("ll", "y").replace("qu", "k")
    w = re.sub(r"c(?=[ei])", "s", w)
    w = w.replace("c", "k").replace("z", "s")
    w = re.sub(r"gu(?=[ei])", "Ğ", w)
    w = re.sub(r"g(?=[ei])", "x", w).replace("Ğ", "g")
    w = w.replace("j", "x").replace("h", "")
    w = re.sub(r"(?<=[aeiou])rr(?=[aeiou])", "R", w)          # perra ≠ pera
    w = re.sub(r"r+", "r", w)
    w = re.sub(r"([aeiou])\1+", r"\1", w)                      # puuuta, joooder
    w = re.sub(r"([^aeiouR])\1+", r"\1", w)                    # putta, mierdaaa → mierda
    return w


class _Lex:
    """Словарь по скелетам: roots — начало слова (хвост ≤ tail букв), exact — слово целиком, exc — исключения."""
    __slots__ = ("exact", "rx", "exc", "tail")

    def __init__(self, roots=(), exact=(), exc=(), tail: int = 8):
        self.exact = {skel(fold_word(w)) for w in exact if w}
        rs = sorted({skel(fold_word(r)) for r in roots if r}, key=len, reverse=True)
        self.rx = re.compile("|".join(map(re.escape, rs))) if rs else None
        self.exc = tuple(sorted({skel(fold_word(e)) for e in exc if e}, key=len, reverse=True))
        self.tail = tail

    def excluded(self, s: str) -> bool:
        for e in self.exc:
            if s.startswith(e) and len(s) - len(e) <= 8:
                return True
        return False

    def hit(self, s: str, allow: tuple = ()) -> bool:
        if not s:
            return False
        if self.excluded(s):
            return False
        for e in allow:
            if s.startswith(e) and len(s) - len(e) <= 6:
                return False
        if s in self.exact:
            return True
        if self.rx is not None:
            m = self.rx.match(s)
            if m and len(s) - m.end() <= self.tail:
                return True
        return False


_LEET_MAIN = str.maketrans({"0": "o", "3": "e", "4": "a", "5": "s", "7": "t", "@": "a", "$": "s", "!": "i"})
_ALPHA = "abcdefghijklmnopqrstuvwxyz" + ENYE


@lru_cache(maxsize=60000)
def variants(tok: str) -> tuple:
    """Все «прочтения» одного слова из чата: ((вариант, способ), …).
    способ: plain · leet · mask · homoglyph · vu (v вместо u)."""
    b = tok
    homo = False
    if _NONLAT.search(b):
        if _ASCII_L.search(b) or any(c.isdigit() for c in b):
            b = b.translate(_LOOK_TR)
            homo = True
        if _NONLAT.search(b):
            return ()
    out: list = []
    seen: set = set()

    def add(x: str, mode: str) -> None:
        if len(x) >= 2 and x not in seen and len(out) < 64:
            seen.add(x)
            out.append((x, "homoglyph" if homo and mode == "plain" else mode))

    has_sym = any(c in _SYM for c in b)
    pieces = [p for p in _SPLIT_SYM.split(b) if p] if has_sym else [b]
    for p in pieces:
        if p.isdigit():
            continue
        if p.isalpha():
            add(p, "plain")
            continue
        add(re.sub(r"\d+", "", p), "leet")
        lp = p.translate(_LEET_MAIN)
        add(lp, "leet")
        if "1" in p:
            add(lp.replace("1", "i"), "leet")
            add(lp.replace("1", "l"), "leet")
        add(re.sub(r"[^a-z" + ENYE + "]", "", lp), "leet")
    if has_sym:
        add(re.sub("[" + re.escape(_SYM) + "]", "", b), "mask")             # p*ta → pta
        add(_SPLIT_NON.sub("", b.translate(_LEET_MAIN)), "leet")            # put@ → puta, m!erda → mierda
        runs = list(re.finditer("[" + re.escape(_SYM) + "]+", b))
        if len(runs) == 1 and len(runs[0].group(0)) <= 2 and len(b) >= 4 and b[0] not in _SYM and b[-1] not in _SYM:
            pre, suf = b[:runs[0].start()], b[runs[0].end():]
            if pre.isalpha() and suf.isalpha():
                for ch in _ALPHA:                                           # p*ta → puta, c*ño → coño, ca*rón → cabrón
                    add(pre + ch + suf, "mask")
    for x, m in list(out):
        if "v" in x:
            add(x.replace("v", "u"), "vu")                                  # pvta → puta
    return tuple(out)


def candidates(fp: str) -> list:
    """Кандидаты из свёрнутого текста: [(слово, исходный_кусок, способ)]."""
    out: list = []
    seen: set = set()

    def put(vs, surface: str, force: str = "") -> None:
        for v, mode in vs:
            if v not in seen:
                seen.add(v)
                out.append((v, surface, force or mode))

    n = 0
    for m in _TOK_RE.finditer(fp):
        put(variants(m.group(0)), m.group(0))
        n += 1
        if n >= 400:
            break
    for m in _SPACED_RE.finditer(fp):
        j = re.sub(r"[^a-z" + ENYE + "]", "", m.group(0))
        put(((j, "spaced"),) + tuple(v for v in variants(j) if v[0] != j), m.group(0), "spaced")
    for m in _INNER_RE.finditer(fp):
        j = re.sub(r"[^a-z" + ENYE + "]", "", m.group(0))
        if 3 <= len(j) <= 18:
            put(variants(j), m.group(0), "joined")
    return out


# ══════════════════════════════════════════════════════════════════════════════════════
#  СЛОВАРИ  (пишем нормально, с ñ и акцентами — всё проходит через fold_word + skel)
#  roots — начало слова (хвост ≤ 8 букв), exact — слово целиком, exc — НЕ считать.
# ══════════════════════════════════════════════════════════════════════════════════════
def _w(s: str) -> list:
    return s.split()


# ---- ЖЁСТКИЙ мат: считаем всегда (оскорбления по природе, «мать», гениталии, шлюха) ----
HARD_ROOTS = _w("""puta puto pute hijueput hijoput hijaput hijosdeput hijadeput malparid gilipoll gilipoy capull
pendej chupapij chupapoll chupaverg comepoll comemierd lameculo tragalech careverg carechimb caremond pichul
pelotud pajer mamaguev mamahuev mamawev mamagüev culer cojud sorete garca ramera""")
HARD_EXACT = _w("""gonorrea gonorea hdp hdlgp hdtpm hdspm hpta hijodeputa ctm ctmr ctmre csm csmr csmtm ctmtm
zorra zorras guarra guarras follar follo folla follas follan follen follad follada follado follando follame follarte
follarme follarla follarlo follaria follaste follaron chucha chuchas chuchesumadre chuchetumadre
pirobo pirobos qlo qlos culiao culiaos culiada culiado culiá reputa reputas""")
# ---- МЯГКИЙ мат: тут «друзья-латинос» — считаем только если адресовано человеку или слов несколько ----
SOFT_ROOTS = _w("""mierd cagad cagon cagarr cojon pinche chingue chinga chingo chingon verga vergon vergud vergaz vergazo culo
mamon weon huevon wevon weona huevona""")
SOFT_EXACT = _w("""polla pollas joder jode jodes jodo joden jodido jodida jodidos jodidas jodete jodanse jodan jodas jodiste jodio jodieron
jodiendo jodemos cabron cabrona cabrones cabronazo coño coños coñazo coñazos carajo carajos carajazo ostia ostias hostia
hostias cagar caga cagas cago cagan cagaste cagaron cagarse boludo boluda boludos boludas boludez boludear boludeo
marica maricas marico maricos mames mamada mamadas mamones wea weas weá weaa weada weadas huevada huevadas wevada
puñeta puñetas puñetero puñetera puñeteros puñeteras puneta punetas punetero punetera chimba
ptm ptmr mrd mrda alv alvr mvv nmms pndj pndjo vrg kbron kbrona kbrones cbron cbrona hdmp""")
HARD_EXC = _w("""putativ putamen putaend vergar vergonz chingana culot culomb culiacan cagarrut""")
# NB: «cagarrut» (помёт) — не мат, поэтому исключён из мягкого; «vergonz» — «позорный».

HATE_ROOTS = _w("maricon")
HATE_EXACT = _w("""joto jotos jotito jotitos trolo trolos sarasa sarasas julandron julandrones bujarron bujarrones
bugarron bugarrones mariposon mariposones maraco maracos travelo travelos travolo tortillera tortilleras bollera
bolleras machorra machorras marimacho marimachos sudaca sudacas negrata negratas sionazi sionazis moromierda""")

ADULT_ROOTS = _w("porn xvideos hentai masturb")
ADULT_EXACT = _w("""pornhub tetas tetitas tetona tetonas tetazas vibrador vibradores pene penes sexting
onlyfans mamada felacion cunnilingus cunilingus nudes nude""")
MINOR_ROOTS = _w("""niñ adolescent preadolescent colegial chamaquit chamaquit pibit jovencit chiquill menorcit""")
MINOR_EXACT = _w("""nino nina ninos ninas ninito ninita ninitos ninitas ninez chamaco chamaca chamacos chamacas
lolita lolitas loli lolis shota shotas crio crios""")

_PROF_HARD = _Lex(HARD_ROOTS, HARD_EXACT, HARD_EXC)
_PROF_SOFT = _Lex(SOFT_ROOTS, SOFT_EXACT, HARD_EXC)
_HATE = _Lex(HATE_ROOTS, HATE_EXACT)
_ADULT = _Lex(ADULT_ROOTS, ADULT_EXACT)
_MINOR = _Lex(MINOR_ROOTS, MINOR_EXACT)

# слитно: hijodeputa, conchatumadre, vetealamierda … (ищем внутри длинного слова; только то, чего нет в обычных словах)
GLUED = _w("""hijodeputa hijadeputa hijoputa hijaputa hijueputa jijueputa hijuepucha hijosdeputa putamadre tuputamadre laputamadre
deputamadre laputaquetepario laputaquelopario conchatumadre conchadetumadre conchetumadre conchesumadre conchadesumadre
chuchatumadre chuchetumadre chuchesumadre chingatumadre chingasumadre chinguesumadre chingatumare vetealamierda vetealaverga
vayasealamierda andatealamierda andaalamierda hijodelagranputa hijoderemilputas hijodemilputas comemierda comeverga lameculo
chupapija chupapolla chupaverga tragaleche mamaguevo mamahuevo careverga carechimba caremonda sacowea sacodewea""")
_GLUED_SK = tuple(sorted({skel(fold_word(g)) for g in GLUED}, key=len, reverse=True))

# нечёткий поиск (опечатка в 1 букву/перестановка) — ТОЛЬКО для длинных, очень «своих» ругательств
FUZZY_HARD = _w("""gilipollas hijueputa hijoputa malparido malparida conchatumadre conchetumadre chupapijas comemierda lameculos
mamaguevo mamahuevo tragaleche chupapollas pelotudo gonorrea pendejada""")
FUZZY_HATE = _w("maricones mariconazo")
_FZ_HARD = {skel(fold_word(w)) for w in FUZZY_HARD}
_FZ_HATE = {skel(fold_word(w)) for w in FUZZY_HATE}


def _d1(a: str, b: str) -> bool:
    """Расстояние Дамерау–Левенштейна ≤ 1 (замена, вставка, удаление, перестановка соседних), a != b."""
    la, lb = len(a), len(b)
    if a == b or abs(la - lb) > 1:
        return False
    if la == lb:
        diff = [i for i in range(la) if a[i] != b[i]]
        if len(diff) == 1:
            return True
        return len(diff) == 2 and diff[1] == diff[0] + 1 and a[diff[0]] == b[diff[1]] and a[diff[1]] == b[diff[0]]
    if la > lb:
        a, b = b, a
    return any(b[:i] + b[i + 1:] == a for i in range(len(b)))


def _fuzzy(s: str) -> str:
    """'' / 'prof' / 'hate'."""
    if len(s) < 7 or s in _FZ_HARD or s in _FZ_HATE:
        return ""
    for t in _FZ_HARD:
        if t[0] == s[0] and abs(len(t) - len(s)) <= 1 and _d1(s, t):
            return "prof"
    for t in _FZ_HATE:
        if t[0] == s[0] and abs(len(t) - len(s)) <= 1 and _d1(s, t):
            return "hate"
    return ""


# ---- «Ложные друзья»: слово с двойным смыслом НЕ считаем, если рядом невинный контекст ----
_FF_SRC = [
    ("poya", r"\bpollas?\s+(?:gol|chilena|de\s+(?:loteria|beneficencia|navidad)|ganadora|millonaria)\b|\b(?:la|una|mi)\s+polla\s+(?:loto|chilena)\b|\bjugar\s+(?:a\s+)?la\s+polla\b"),
    ("pinche", r"\bpinche\s+de\s+(?:cocina|restaurante)\b|\bpinches\s+de\s+cocina\b"),
    ("ostia", r"\bhostias?\s+(?:consagrad\w+|sagrad\w+|de\s+comunion)\b|\b(?:comulgar|comunion|eucaristia|sacerdote|misa|cura)\b.{0,30}\bhostia\b"),
    ("gonorrea", r"\b(?:enfermedad|infeccion|sintomas?|tratamiento|antibioticos?|ets|its|transmision|contagio|contagiar|clamidia|sifilis|medico|doctor|salud)\b"),
    ("gonorea", r"\b(?:enfermedad|infeccion|sintomas?|tratamiento|antibioticos?|ets|its|transmision|contagio|contagiar|clamidia|sifilis|medico|doctor|salud)\b"),
    ("berga", r"\bverga\s+(?:del|de\s+la)\s+(?:barco|barca|vela|mastil|mastelero|nave)\b|\bvergas\s+del?\s+(?:barco|velero)\b"),
    ("kabron", r"\bcabr[oó]n\s+(?:cabrio|montes|macho)\b|\bmacho\s+cabrio\b"),
]
_FF = [(skel(fold_word(k)), re.compile(v)) for k, v in _FF_SRC]


def _false_friend(s: str, fn: str) -> bool:
    for k, rx in _FF:
        if s.startswith(k) and rx.search(fn):
            return True
    return False


# ---- Адресность (режим «друзей»): 2-е лицо или враждебные слова рядом ----
DIRECT_RX = re.compile(
    r"\b(?:ti|contigo|eres|eras|sos|vos|usted|ustedes|vete|andate|callate|cayate|cierra\s+la\s+boca|jodete|largate|a\s+ti|que\s+te|ojala\s+te|"
    r"hijo\s+de\s+tu|tu\s+(?:madre|puta\s+madre|abuela|mama|vieja|hermana)|dejate\s+de)\b")
HOSTILE_RX = re.compile(
    r"\bde\s+mierda\b|\bmierda\s+de\s+(?:persona|gente|ser|humano|jugador\w*|moderador\w*|admin\w*|bot|mod)\b|\b(?:asqueros\w+|basura|escoria|idiota\w*|imbecil\w*|estupid\w+|inutil\w*|payas\w+|subnormal\w*|"
    r"retrasad\w+|mongol\w*|tarad\w+|lacra|parasit\w+|fracasad\w+|perdedor\w*|desgraciad\w+|maldit\w+|sucio|sucia|cerdo|cerda)\b")
FRIENDS_ON = _flag("GUARD_ES_FRIENDS", True)


def _soft_counts(soft_hits: list, fn: str) -> bool:
    """Мягкий мат засчитываем, если он адресован, рядом враждебность, или слов ≥ 2 разных."""
    if not FRIENDS_ON:
        return True
    stems = {h[1] for h in soft_hits}
    if len(stems) >= 2:
        return True
    fn2 = fn.translate(_LEET_MAIN).replace("1", "i")                       # m1erd4 de persona → mierda de persona
    return bool(DIRECT_RX.search(fn) or HOSTILE_RX.search(fn) or DIRECT_RX.search(fn2) or HOSTILE_RX.search(fn2))


# ══════════════════════════════════════════════════════════════════════════════════════
#  ФРАЗЫ (на тексте без акцентов, ñ → n)
# ══════════════════════════════════════════════════════════════════════════════════════
_TARGETS = (r"(?:negros?|negras?|negratas?|morenos?|moros?|moras?|arabes?|musulman\w+|islamicos?|judios?|judias?|sionistas?|"
            r"gitanos?|gitanas?|chinos?|chinas?|asiaticos?|indios?|indias?|indigenas?|latinos?|latinas?|sudacas?|panchitos?|"
            r"mexicanos?|mexicanas?|venezolanos?|venezolanas?|colombianos?|colombianas?|peruanos?|peruanas?|bolivianos?|"
            r"ecuatorianos?|dominicanos?|cubanos?|argentinos?|chilenos?|espanoles?|gringos?|yankis?|rusos?|rusas?|ucranianos?|"
            r"extranjeros?|inmigrantes?|migrantes?|refugiados?|gays?|homosexuales?|lesbianas?|bisexuales?|trans|transexuales?|"
            r"transgeneros?|travestis?|discapacitados?|autistas?|ancianos?)")
_TAIL = (r"(?:de\s+mierda|asquerosos?|asquerosas?|cochinos?|cochinas?|sucios?|sucias?|inmundos?|inmundas?|basura|escoria|plaga|"
         r"parasitos?|animales|bichos|ratas?|cucarachas?|mierdas?|deberian\s+(?:morir|desaparecer|ser\s+(?:exterminad\w+|eliminad\w+|deportad\w+))|"
         r"a\s+las\s+camaras\s+de\s+gas|fuera\s+de\s+(?:aqui|espana|mi\s+pais|nuestro\s+pais|mexico|argentina|chile))")
_PRE = r"(?:put[oa]s?|maldit[oa]s?|sucios?|sucias?|asquerosos?|asquerosas?|cochinos?|cochinas?|inmundos?|inmundas?|apestosos?)"

_PHRASES_SRC = [
    # (категория, регулярка, подпись)
    ("hate", r"\b" + _TARGETS + r"\s+" + _TAIL + r"\b", "ярлык-оскорбление группы"),
    ("hate", r"\b" + _PRE + r"\s+" + _TARGETS + r"\b", "ярлык-оскорбление группы"),
    ("hate", r"\b(?:muerte\s+a|que\s+mueran|mueran|hay\s+que\s+(?:matar|exterminar|eliminar|quemar|gasear|echar)\s+a|"
             r"a\s+matar\s+a|vamos\s+a\s+matar\s+a|exterminio\s+de)\s+(?:todos\s+)?(?:a\s+)?(?:los|las|esos|esas)?\s*" + _TARGETS + r"\b",
     "призыв к насилию против группы"),
    ("hate", r"\b(?:hitler\s+(?:tenia\s+razon|debio\s+(?:terminar|acabar)|no\s+(?:termino|acabo)\s+el\s+trabajo|vuelve|volvera)|"
             r"viva\s+(?:hitler|el\s+nazismo)|gloria\s+a\s+hitler|el\s+holocausto\s+(?:fue\s+mentira|no\s+existio|es\s+mentira|nunca\s+ocurrio)|"
             r"volvere?mos\s+a\s+gasear)\b", "нацистский призыв"),
    ("prof_hard", r"\b(?:la\s+)?(?:re)?concha\s+(?:de\s+)?(?:tu|su|la)\s+(?:madre|lora|hermana|abuela)\b|\bla\s+concha\s+(?:tuya|suya)\b|"
                  r"\breconcha\w*|\bconchud[oa]s?\b", "оскорбление через «мать»"),
    ("prof_hard", r"\b(?:chupa|chupame|chupalo|chupamela|chupale|mamame|mamamela|mamalo)\s*(?:la\s+|el\s+|mi\s+|mis\s+)?"
                  r"(?:pija|pico|pinga|tula|pito|nepe|poronga|pene|polla|verga|bolas|huevos|cojones|culo)\b", "грубая сексуальная формула"),
    ("prof_hard", r"\b(?:tomar|vete\s+a\s+tomar|que\s+te\s+den)\s+por\s+(?:el\s+)?culo\b|\bmetetelo\s+(?:por|en)\s+el\s+culo\b|"
                  r"\bchupame\s+el\s+culo\b", "грубая формула"),
    ("prof_hard", r"\b(?:tu|su)\s+(?:madre|mama|vieja|jefa|mami|hermana)\s+(?:es\s+(?:una\s+)?(?:puta|zorra|perra|golfa|ramera|cualquiera|prostituta)|"
                  r"la\s+(?:chupa|mama)|se\s+(?:acuesta|coge|folla)|trabaja\s+(?:de|en)\s+(?:la\s+)?(?:esquina|calle|burdel))\b", "оскорбление через «мать»"),
    ("prof_hard", r"\bhij[oa]s?\s+de\s+(?:la\s+)?(?:gran\s+|re|mil\s+|remil\s+)?(?:perr\w+|zorr\w+|cabr\w+|mierd\w+|fruta|"
                  r"su\s+madre|tu\s+madre|la\s+chingada|la\s+gran\s+chingada)\b", "оскорбление «hijo de…»"),
    ("prof_hard", r"\b(?:maldit[ao]|sucia|asquerosa|puta|tremenda|reputa|pinche|mugrosa|cochina)\s+perr[ao]s?\b|"
                  r"\bperr[ao]s?\s+(?:asquerosa|sucia|maldita|de\s+mierda)\b|\bhija\s+de\s+perra\b", "«perra» как оскорбление"),
    ("prof_hard", r"\bme\s+cago\s+en\s+(?:tu|su|vuestra|tus|sus|ti|vuestros)\b", "грубая формула"),
    ("prof_soft", r"\bme\s+cago\s+en\s+(?:dios|diox|la\s+hostia|la\s+leche|todo|jesus|cristo|la\s+puta|los\s+muertos)\b", "мягкая грубость"),
    ("prof_soft", r"\b(?:que|ni|donde|como|quien|cuando|por\s+que|adonde)\s+cono\b", "«cono» как coño"),
    ("prof_soft", r"\bme\s+vale\s+(?:madres?|verga|vergas)\b|\bvale\s+madres\b|\bni\s+madres\b|\bhasta\s+la\s+madre\b|\ba\s+la\s+(?:verga|chingada)\b", "мягкая грубость"),
    ("adult", r"\bsexo\s+(?:oral|anal|duro|salvaje|en\s+grupo|en\s+vivo|virtual|telefonico|casual|gratis)\b|"
              r"\bvideos?\s+(?:xxx|porno\w*|x)\b|\bfotos?\s+(?:hot|intim\w+|desnud\w+|calientes)\b|\bchats?\s+(?:erotic\w+|de\s+sexo|calientes?|hot)\b|"
              r"\bcontenido\s+(?:explicito|para\s+adultos|xxx)\b|\bmeter(?:te|la|lo)\s+(?:la\s+)?(?:pija|verga|polla)\b", "18+"),
    ("minor", r"\bmenor(?:es)?\s+de\s+(?:edad|1\d)\b|\b(?:de|tiene|tengo|tienen)\s+(?:1[0-7]|[5-9])\s+anos\b|\bde\s+(?:1[0-7]|[5-9])\s+anitos\b", "несовершеннолетний"),
]
# угрозы/призывы к суициду и доксингу — отдельная категория (включается GUARD_ES_THREATS)
if True:
    _PHRASES_SRC += [
        ("threat", r"\bsuicidate\b|\bsuicidese\b|\bmatate\b(?!\s+(?:de\s+)?(?:la\s+)?(?:risa|trabajar|estudiar))|\bmuerete\b|\bahorcate\b|"
                   r"\bcortate\s+(?:las\s+venas|el\s+cuello|las\s+munecas)\b|\btirate\s+(?:de|por)\s+(?:un|el|la)\s+(?:puente|balcon|edificio|ventana|techo|terraza)\b|"
                   r"\b(?:vete|andate|anda)\s+a\s+morir(?:te)?\b|\b(?:ojala|espero)\s+(?:que\s+)?(?:te\s+)?(?:mueras|mates|te\s+mueras|te\s+mates|te\s+maten|te\s+violen|"
                   r"te\s+atropellen|te\s+de\s+(?:cancer|un\s+infarto))\b|\bdeberias\s+(?:morir|matarte|suicidarte)\b|\bno\s+mereces\s+vivir\b|\bkys\b",
         "призыв к суициду"),
        ("threat", r"\bte\s+voy\s+a\s+violar\b|\bvoy\s+a\s+violar(?:te|la|los)?\b|\bte\s+(?:violo|violare|violaran)\b|"
                   r"\b(?:se|sé)\s+donde\s+vives\b|\bse\s+donde\s+vive\s+tu\b|\bte\s+voy\s+a\s+doxear\b|\bvoy\s+a\s+(?:doxear|filtrar)\s+(?:tu|tus)\b|"
                   r"\bfiltrar\s+(?:tu|tus)\s+(?:ip|direccion|numero|datos|fotos)\b", "угроза/доксинг"),
    ]
_PHRASES = [(c, re.compile(p), why) for c, p, why in _PHRASES_SRC]


# ══════════════════════════════════════════════════════════════════════════════════════
#  «Похоже на испанский?»  (нужно только для защиты от ложных срабатываний чужих правил guard.py)
# ══════════════════════════════════════════════════════════════════════════════════════
_ES_COMMON = frozenset(_w("""de la que el en y a los se del las un por con no una su para es al lo como mas pero sus le ya o fue este ha si
porque esta entre cuando muy sin sobre tambien me hasta hay donde quien desde todo nos durante todos uno les ni contra otros ese eso
ante ellos e esto mi antes algunos que unos yo otro otras otra tanto esa estos mucho quienes nada muchos cual poco ella estar estas
algo nosotros mis tu te ti tus ellas vosotros os mio mia tuyo suyo nuestro nuestra hola gracias bueno vale pues si ok eres soy estoy
estan voy vas va vamos quiero quieres puedo puedes puede tengo tienes tiene hace hago haces hacer ser tener ir ahora hoy ayer manana
aqui alli aca alla bien mal mejor peor siempre nunca jamas casi tampoco aun todavia luego despues mientras aunque sino
buenas buenos dias noches tardes amigo amigos gente chicos chicas jugar juego partida gano gane perdi perdimos ganar perder
tengo tenemos necesito necesitamos quiero queremos busco buscamos alguien algun alguna ninguno ninguna cada otro mismo misma
cuanto cuanta cuantos cuantas donde adonde cuando como porque entonces vez veces cosa cosas persona personas casa mundo vida
dia noche tiempo ano anos trabajo dinero favor problema pregunta respuesta ayuda gracias perdon disculpa saludos""".replace("\n", " ")))
_WORD_RE = re.compile(r"[a-z]+")


def looks_spanish(text: str) -> bool:
    """Грубая оценка: есть ñ/¿/¡ или ≥2 частых испанских слов (или 1 в очень коротком тексте)."""
    if "ñ" in text.lower() or "¿" in text or "¡" in text:
        return True
    toks = _WORD_RE.findall(es_fold(text, False))
    hits = sum(1 for t in toks if t in _ES_COMMON)
    return hits >= 2 or (hits >= 1 and len(toks) <= 3)


# ══════════════════════════════════════════════════════════════════════════════════════
#  ГЛАВНЫЙ РАЗБОР ТЕКСТА
# ══════════════════════════════════════════════════════════════════════════════════════
class ESScan(NamedTuple):
    prof: tuple = ()          # слова, засчитанные как мат
    hate: tuple = ()
    adult: tuple = ()
    minor: bool = False
    threat: tuple = ()
    skipped: tuple = ()       # мягкие слова, которые НЕ засчитаны (режим «друзей»)
    hits: tuple = ()          # подробности для explain(): (категория, слово, исходный_кусок, способ)
    spanish: bool = False


_EMPTY = ESScan()
_LEXES = (("prof_hard", _PROF_HARD), ("prof_soft", _PROF_SOFT), ("hate", _HATE), ("adult", _ADULT), ("minor", _MINOR))


@lru_cache(maxsize=4096)
def _scan(text: str, allow: tuple) -> ESScan:
    fp = es_fold(text, True)
    if not _ASCII_L.search(fp):
        return _EMPTY
    fn = es_fold(text, False)
    hits: list = []
    seen: set = set()

    def note(cat, word, surface, mode):
        k = (cat, word)
        if k not in seen and not (mode == "mask" and any(h[0] == cat and h[2] == surface for h in hits)):
            seen.add(k)
            hits.append((cat, word, surface, mode))

    for cand, surface, mode in candidates(fp):
        s = skel(cand)
        if not 1 <= len(s) <= 60:
            continue
        if mode in ("vu", "leet", "mask") and _PROF_HARD.excluded(skel(re.sub(r"[^a-z" + ENYE + "]", "", surface))):
            continue                                              # putativo → putatiuo не должно обходить исключение
        got = False
        for cat, lex in _LEXES:
            if lex.hit(s, allow) and not _false_friend(s, fn):
                note(cat, cand, surface, mode)
                got = True
        if got:
            continue
        if len(s) >= 8 and any(g in s for g in _GLUED_SK):
            note("prof_hard", cand, surface, "слитно")
            continue
        z = _fuzzy(s)
        if z:
            note("hate" if z == "hate" else "prof_hard", cand, surface, "опечатка")

    for cat, rx, why in _PHRASES:
        m = rx.search(fn)
        if m:
            note(cat, m.group(0)[:40], m.group(0)[:40], why)

    hard = [h for h in hits if h[0] == "prof_hard"]
    soft = [h for h in hits if h[0] == "prof_soft"]
    prof = [h[1] for h in hard]
    skipped: list = []
    if soft:
        if hard or _soft_counts(soft, fn):
            prof += [h[1] for h in soft]
        else:
            skipped = [h[1] for h in soft]
    hate = tuple(dict.fromkeys(h[1] for h in hits if h[0] == "hate"))
    adult = tuple(dict.fromkeys(h[1] for h in hits if h[0] == "adult"))
    threat = tuple(dict.fromkeys(h[1] for h in hits if h[0] == "threat")) if ES_THREATS else ()
    minor = any(h[0] == "minor" for h in hits)
    return ESScan(tuple(dict.fromkeys(prof)), hate, adult, minor, threat, tuple(dict.fromkeys(skipped)), tuple(hits),
                  looks_spanish(text))


def es_scan(text: str, allow: tuple = ()) -> ESScan:
    """Разбор текста на испанский мат / ненависть / 18+ / детскую тему / угрозы. Результат кэшируется."""
    if not text:
        return _EMPTY
    return _scan(text[:4500], allow)


# ══════════════════════════════════════════════════════════════════════════════════════
#  СПАМ-ПРАВИЛА  (формат guard: имя, группа, вес, regex, причина). Работают на тексте guard.fold():
#  без акцентов, ñ → n, нижний регистр; leet (4→a, 3→e, 0→o, @→a) guard разворачивает сам.
#  Группы те же, что у русских правил (job/cta/invest/gamble/promo/sale/illegal/adult_ad/urgency) — поэтому «предложение +
#  призыв писать» (pitch_cta) и «три семейства» (families3) работают на испанском так же, как на русском.
# ══════════════════════════════════════════════════════════════════════════════════════
_NUM = r"\d[\d.,]*(?:\s\d{3})*"
_CURR = (r"(?:usdt?|us\$|dolar(?:es)?|dls|euros?|eur|€|pesos?(?:\s+(?:mexicanos?|colombianos?|argentinos?|chilenos?))?|"
         r"mxn|cop|ars|clp|soles?|pen|bs|bolivares|\$)")
_PER = r"(?:al|por|x|/|cada)\s*(?:dia|semana|mes|hora)\b"
_EARN_V = r"(?:gana(?:r|s|mos|ndo)?|generar?|obtener|consigue|cobrar?|ingresos?)"


def _rx(p: str):
    return re.compile(p)


ES_SPAM_RULES = [
    # ── работа / заработок ──
    ("es_earn_pitch", "job", 2.5, _rx(r"\b" + _EARN_V + r"\b[^.!?\n]{0,50}\b(?:sin\s+(?:inversion|experiencia|invertir)|desde\s+(?:casa|tu\s+(?:celular|casa|movil|telefono))|"
        r"(?:al|por|cada)\s+(?:dia|semana|mes|hora)|diari\w+|a\s+diario|todos\s+los\s+dias|(?:en|por)\s+internet|online|en\s+linea|por\s+whatsapp|por\s+telegram)"),
     "обещание лёгкого заработка (исп.)"),
    ("es_earn_online", "job", 2.5, _rx(r"\b(?:gana(?:r|s|mos)?|ganando)\s+(?:dinero|plata|lana|pasta|guita|billete|dolares|euros|efectivo)\s+(?:facil|rapido|extra|online|"
        r"desde\s+(?:casa|tu\s+celular)|en\s+linea|por\s+internet|con\s+tu\s+(?:celular|telefono|movil)|sin\s+(?:salir|invertir|experiencia))"),
     "заработок в сети / с телефона (исп.)"),
    ("es_earn_word", "job", 1.5, _rx(r"\b(?:gana(?:r|s|mos|ndo)?\s+(?:dinero|plata|lana|pasta|guita|billete|dolares|euros)|ganancias?\s+(?:diari\w+|semanal\w*|garantizad\w+)|"
        r"ingresos?\s+extra|dinero\s+extra|plata\s+extra)\b"), "разговор о заработке (исп.)"),
    ("es_phone_work", "job", 2.5, _rx(r"\b(?:trabaj\w+|chamb\w+|laburo|curro|ganar|gana|ingresos?)\s+(?:desde|con|en|por)\s+(?:tu\s+|el\s+|su\s+|un\s+)?"
        r"(?:celular|movil|telefono|smartphone|whatsapp|telegram|tiktok|instagram)\b|\b(?:solo|unicamente|apenas)\s+(?:necesitas|necesitan|requieres)\s+(?:un\s+|tu\s+)?"
        r"(?:celular|telefono|movil|smartphone|internet)\b"), "работа «только с телефона» (исп.)"),
    ("es_remote", "job", 1.5, _rx(r"\b(?:trabajo|empleo|chamba|vacante|oferta\s+laboral|oportunidad\s+laboral)\s+(?:remot\w+|online|en\s+linea|desde\s+casa|a\s+distancia|"
        r"virtual|por\s+internet|medio\s+tiempo|part[\s-]?time|flexible)\b|\b(?:teletrabajo|trabajo\s+en\s+casa|trabaja\s+desde\s+casa|trabajar\s+desde\s+casa|home\s+office)\b"),
     "удалённая работа / подработка (исп.)"),
    ("es_no_exp", "job", 1.8, _rx(r"\bsin\s+(?:experiencia|inversion|invertir|riesgos?|capital)\b"), "«без вложений/опыта» (исп.)"),
    ("es_passive", "job", 2.0, _rx(r"\b(?:ingresos?|dinero|renta|entradas?)\s+pasiv\w+|\bvivir\s+de\s+(?:tus\s+)?(?:inversion\w*|trading|cripto\w*|rentas)\b"),
     "пассивный доход (исп.)"),
    ("es_freedom", "job", 0.8, _rx(r"\b(?:libertad|independencia)\s+financiera\b"), "«финансовая независимость» (исп.)"),
    ("es_task_scam", "job", 3.0, _rx(
        r"\b(?:dar|dando|da|dale|dejar|poner|ponga|ver|mirar|reproducir|seguir|siguiendo|comentar)\s+(?:likes?|me\s+gusta|corazones|reacciones|seguidores|"
        r"comentarios?|resenas?|estrellas|valoraciones|videos?|anuncios?|publicidad)\b[^.!?\n]{0,60}\b(?:gana\w*|pag\w+|dinero|plata|cobr\w+|remunera\w*|"
        r"ingresos?|usdt|dolares|pesos|soles|euros|recompensa\w*|comision\w*)\b"
        r"|\b(?:gana\w*|pag\w+|dinero|plata|cobr\w+|usdt|dolares|pesos|recompensa\w*)\b[^.!?\n]{0,60}\b(?:por\s+(?:dar|ver|mirar|seguir|comentar)\s+"
        r"(?:likes?|me\s+gusta|videos?|cuentas?|publicaciones|anuncios)|dando\s+(?:likes?|me\s+gusta)|viendo\s+(?:videos?|anuncios))\b"
        r"|\b(?:tareas?|misiones?)\s+(?:simples?|sencillas?|faciles|diarias?|en\s+linea|online)\b[^.!?\n]{0,60}\b(?:pag\w+|gana\w*|cobr\w+|usdt|dolares|\$|recompensa\w*)\b"
        r"|\bgrupo\s+(?:vip|privado)\s+(?:de\s+)?(?:trabajo|tareas|inversion|senales|ganancias)\b"
        r"|\b(?:soy|somos)\s+(?:reclutador\w*|(?:del\s+)?(?:equipo|departamento)\s+de\s+(?:reclutamiento|rrhh|recursos\s+humanos))\b"
        r"|\bcaptura\s+de\s+pantalla\b[^.!?\n]{0,50}\b(?:pago|primer\s+pago|cobrar|cobro)\b"),
     "«task scam»: деньги за лайки/задания"),
    ("es_paid_daily", "job", 2.0, _rx(r"\b(?:pagamos|pagan|paga|cobras|cobra)\s+(?:todos\s+los\s+dias|cada\s+dia|a\s+diario|diari\w+|al\s+instante|de\s+inmediato|"
        r"el\s+mismo\s+dia|semanalmente|por\s+hora)\b"), "«платят каждый день» (исп.)"),
    ("es_income_day", "job", 3.0, _rx(r"(?<![\d.,])(?:\$\s?" + _NUM + r"(?:\s?(?:k|mil|usd|dolares))?|" + _NUM + r"\s?(?:k|mil)?\s?" + _CURR + r")\s*(?:al|por|x|/|cada)\s*"
        r"(?:dia|semana)\b|\b" + _NUM + r"\s?" + _CURR + r"\s*(?:diarios|diarias|semanales|a\s+diario)\b"), "сумма «в день/неделю» (исп.)"),
    ("es_income_month", "job", 2.0, _rx(r"\b(?:gana(?:r|s|mos|ndo)?|ingresos?|generar?|generas|genera)\b[^.!?\n]{0,60}(?<![\d.,])(?:\$\s?" + _NUM +
        r"|" + _NUM + r"\s?(?:k|mil)?\s?" + _CURR + r")\s*(?:al|por|cada)\s*mes\b"), "сумма «в месяц» рядом со словом о заработке"),
    ("es_income_goal", "job", 2.5, _rx(r"\b(?:ingresos?|ganancias?)\s+(?:de|desde|hasta|entre|a\s+partir\s+de)\s+\$?" + _NUM + r"(?:\s?(?:k|mil))?\b[^.!?\n]{0,15}"
        r"(?:al|por|cada|diari\w+|semanal\w*)"), "обещание дохода в цифрах (исп.)"),
    ("es_hours", "job", 2.0, _rx(r"\b(?:solo|solamente|apenas|dedicando|tan\s+solo)\s+\d[\d\-]*\s*(?:horas?|hrs?|minutos?)\s+(?:al|por|de)\s+dia\b[^.!?\n]{0,50}"
        r"\b(?:gana\w*|ingres\w*|dinero|plata|\$)"), "«пара часов в день» + доход (исп.)"),
    ("es_target", "job", 2.0, _rx(r"\b(?:para|ideal\s+para|apto\s+para)\s+(?:estudiantes?|amas\s+de\s+casa|madres|mamas|jubilad\w+|desemplead\w+|cualquier\s+persona|"
        r"todas?\s+las\s+personas)\b[^.!?\n]{0,40}\b(?:trabajo|ingreso\w*|gana\w*|dinero|empleo)"), "«для студентов и мам» (исп.)"),
    # ВАЖНО: «busco gente / personas / chicos» в играх — это поиск команды, поэтому тут только рабочие должности
    ("es_hiring", "job", 2.0, _rx(r"\b(?:se\s+busc(?:an?|o)|busco|buscamos|necesito|necesitamos|solicito|solicitamos|reclutamos|contratamos)\s+(?:personal|"
        r"colaboradores|asesores|vendedores|promotores|trabajadores|empleados|repartidores|mensajeros|agentes|operadores)\b|\b(?:gente|personas|chicas|chicos|jovenes)\s+"
        r"(?:para|que\s+quieran)\s+(?:trabajar|ganar|ingresos|un\s+negocio|el\s+negocio|empleo)\b"), "набор сотрудников (исп.)"),
    ("es_collab", "job", 1.5, _rx(r"\bbusco\s+(?:personas|gente|socios|colaboradores)\s+(?:serias?|responsables?|comprometid\w+|motivad\w+|ambiciosas?|emprendedor\w*)\b|"
        r"\bnegocio\s+(?:rentable|probado|seguro|digital|online)\b"), "«ищу людей для сотрудничества» (исп.)"),
    ("es_proven", "job", 1.5, _rx(r"\b(?:metodo|sistema|formula|estrategia|esquema)\s+(?:probad\w+|comprobad\w+|garantizad\w+|infalible)\b|"
        r"\bresultados?\s+(?:desde|en)\s+(?:el\s+)?(?:primer|1er|1)\s+(?:dia|semana)\b"), "«проверенный способ» (исп.)"),
    ("es_mlm", "job", 1.5, _rx(r"\b(?:multinivel|network\s+marketing|mlm)\b"), "сетевой маркетинг"),
    # ── призывы (cta) ──
    ("es_cta_dm", "cta", 2.0, _rx(r"\b(?:escrib\w+|mand\w+|envi\w+|contact\w+|habla\w*|comunica\w+|avisa\w*|ponte\s+en\s+contacto)\s+(?:me\s+|nos\s+|al\s+|a\s+|mi\s+|"
        r"por\s+|en\s+|el\s+|un\s+|mensaje\s+)*(?:privado|priv|pv|pvt|dm|md|inbox|mensaje\s+directo|mensaje\s+privado|chat\s+privado|directo|whats?app|wsp|wpp|"
        r"wasap|guasap|telegram|tg)\b"), "зовёт в личку (исп.)"),
    ("es_dm_hint", "cta", 1.2, _rx(r"(?:^|[\s,.;:!?¡¿])(?:al\s+|por\s+)?(?:privado|priv|pv|dm|md|inbox)(?=$|[\s,.;:!?)])|\b(?:escribeme|escribenos|mandame|hablame|contactame)\W*$"),
     "«в лс» / «пиши» (исп.)"),
    ("es_cta_plus", "cta", 2.0, _rx(r"\b(?:escrib\w+|pon\w*|mand\w+|comenta\w*|deja\w*)\s+(?:la\s+palabra\s+|el\s+codigo\s+|un\s+|una\s+)?[\"'«“]?"
        r"(?:\+|info|informacion|quiero|interesad[oa]|listo)[\"'»”]?(?=\s|$|[.!,])"), "«пиши +» / «напиши слово» (исп.)"),
    ("es_detail_dm", "cta", 2.0, _rx(r"\b(?:detalles|informacion|info|mas\s+info|explico|te\s+explico|les\s+explico|te\s+cuento|te\s+paso|te\s+envio|te\s+mando|instrucciones|"
        r"condiciones)\b[^.!?\n]{0,25}\b(?:por|al|en|via|mediante)\s+(?:el\s+)?(?:privado|priv|dm|inbox|mensaje\s+directo|whatsapp|wasap|telegram|tg)\b"),
     "детали — только в личке (исп.)"),
    ("es_interested", "cta", 1.5, _rx(r"\b(?:interesad[oa]s?|quien\s+quiera|quienes\s+quieran|si\s+te\s+interesa|los\s+interesados|las\s+interesadas)\W+"
        r"(?:escrib\w+|manda\w*|contacta\w*|habla\w*|pon\w*|comenta\w*)\W*$"), "«интересно — напишите» (исп.)"),
    ("es_cta_profile", "cta", 2.5, _rx(r"\b(?:link|enlace|liga)\s+(?:en|de)\s+(?:mi\s+)?(?:bio|perfil|biografia|descripcion|historia)\b|"
        r"\b(?:clic|click|pulsa|toca|presiona|da\s+click|haz\s+click|entra\s+en|entra\s+al)\s+(?:en\s+|al\s+|el\s+|aqui\s+)?(?:link|enlace|boton|perfil|aqui|bio)\b|"
        r"\bmira\s+mi\s+(?:perfil|bio)\b"), "«ссылка в профиле» (исп.)"),
    ("es_subscribe", "cta", 1.2, _rx(r"\b(?:suscrib\w+|subscribete|siguenos|sigueme|sigan\s+(?:mi|el)\s+canal|unete\s+a\s+(?:mi|nuestro|el)\s+(?:canal|grupo|chat|comunidad)|"
        r"entra\s+(?:a|en)\s+(?:mi|nuestro|el)\s+(?:canal|grupo|chat))\b"), "зовёт подписаться (исп.)"),
    ("es_tg_promo", "cta", 1.5, _rx(r"\bmi\s+(?:canal|grupo|chat|bot)\b|\bnuestro\s+(?:canal|grupo|chat|bot)\b|\b(?:unete|unanse|entra|entren|ingresa|accede)\s+"
        r"(?:al|a\s+mi|a\s+nuestro|a\s+este|en)\s+(?:canal|grupo|chat|comunidad)\b"), "реклама канала/чата (исп.)"),
    ("es_register", "cta", 2.0, _rx(r"\b(?:registr\w+|inscrib\w+|crea\s+tu\s+cuenta)\s+(?:aqui|ahora|con\s+mi|en\s+(?:este|el)\s+(?:link|enlace)|gratis)\b|"
        r"\b(?:mi|con\s+mi|usa\s+mi)\s+(?:codigo|link|enlace)\s+(?:de\s+)?(?:referid\w+|invitacion|promo\w*|afiliad\w+|descuento)\b"), "регистрация по моей ссылке/коду"),
    ("es_urgency", "urgency", 1.5, _rx(r"\b(?:solo\s+hoy|solo\s+por\s+hoy|aprovecha\w*|ultimos?\s+(?:cupos?|lugares?|espacios?|dias?)|cupos?\s+limitad\w+|lugares?\s+limitad\w+|"
        r"oferta\s+limitada|oportunidad\s+unica|no\s+te\s+lo\s+pierdas|no\s+dejes\s+pasar|por\s+tiempo\s+limitado|termina\s+hoy|ultima\s+oportunidad|"
        r"quedan\s+(?:pocos|\d+)\s+(?:cupos|lugares|espacios)|date\s+prisa|apresurate|solo\s+\d+\s+(?:cupos|lugares))\b"), "давление срочностью (исп.)"),
    # ── инвестиции / займы / казино ──
    ("es_crypto", "invest", 1.2, _rx(r"\b(?:cripto\w*|criptomoneda\w*|bitcoin|btc|ethereum|usdt|tether|trading|trader\w*|forex|binance|bybit|okx|kucoin|nft|airdrops?|"
        r"invertir|inversion\w*|broker\w*|staking|arbitraje|apalancamiento|opciones\s+binarias)\b"), "крипта / инвестиции (исп.)"),
    ("es_invest_promise", "invest", 3.0, _rx(r"\b(?:dupli\w+|tripli\w+|multipli\w+|garantiz\w+|garantia\s+de|asegur\w+|rentabilidad\s+(?:garantizada|asegurada)|"
        r"ganancias?\s+(?:garantizadas?|aseguradas?|seguras?))\b[^.!?\n]{0,40}\b(?:inversion\w*|dinero|capital|deposito|ganancia\w*|rentabilidad|cripto\w*|bitcoin|usdt|plata)\b|"
        r"\b\d{2,4}\s?%\s+(?:al|por|en|cada|de\s+(?:ganancia|rentabilidad|beneficio))\s*(?:dia|semana|mes|diari\w+|semanal\w*|mensual\w*)?|"
        r"\b(?:rentabilidad|ganancia|retorno|rendimiento)\s+(?:diari\w+|semanal\w*|del?\s+\d+\s?%)"), "гарантированная прибыль (исп.)"),
    ("es_signals", "invest", 2.0, _rx(r"\b(?:senales?|signals?)\s+(?:de\s+)?(?:trading|cripto\w*|forex|vip|gratis|gratuitas|premium|binarias|de\s+inversion)\b|"
        r"\bgrupo\s+(?:vip|premium)\b|\b(?:bot|robot|ia|inteligencia\s+artificial)\s+(?:de\s+)?(?:trading|inversion|arbitraje|cripto\w*|que\s+(?:gana|genera|paga))\b|"
        r"\bgestor\w*\s+de\s+(?:inversion\w*|cuentas?|fondos?|cripto\w*)\b|\bmanejo\s+de\s+(?:cuentas?|capital|inversion\w*)\b"), "платные сигналы / бот-трейдер (исп.)"),
    ("es_advance_fee", "invest", 3.0, _rx(r"\b(?:deposita|transfiere|envia|paga|abona)\w*\s+(?:una\s+|la\s+|el\s+|su\s+|tu\s+)?(?:cuota|comision|tasa|garantia|fianza|deposito|monto)\b[^.!?\n]{0,80}"
        r"\b(?:para\s+(?:poder\s+)?(?:retirar|desbloquear|activar|liberar|cobrar|recibir)|y\s+(?:podras|podra)\s+(?:retirar|cobrar|recibir))\b"), "предоплата «для вывода/активации»"),
    ("es_loan", "sale", 3.0, _rx(r"\b(?:prestamos?|creditos?|financiamiento|dinero|efectivo)\s+(?:rapidos?|inmediatos?|faciles?|al\s+instante|en\s+\d+\s+(?:minutos|horas)|"
        r"sin\s+(?:buro|aval\w*|garantia\w*|revision|verificacion|consulta|historial|papeleos?|tramites?|requisitos|fiador|intereses|cobros)|aprobad\w+\s+(?:al\s+instante|hoy)|"
        r"con\s+(?:datacredito|veraz|dicom|asnef|badexcug|ficha))\b|\b(?:aunque|incluso\s+si)\s+(?:estes|este)\s+(?:reportad\w+|en\s+(?:buro|asnef|dicom|veraz|datacredito))\b"),
     "«кредит без проверок/бюро» (исп.)"),
    ("es_gamble", "gamble", 2.5, _rx(r"\b(?:apuestas?\s+(?:deportivas?|online|en\s+linea|gratis|seguras?)|bookmaker|1win|1xbet|melbet|mostbet|"
        r"betano|betway|bet365|codere|pin[\s-]?up|vulkan|joycasino|bono\s+de\s+bienvenida|giros\s+gratis|free\s?spins?|fortune\s+tiger|jogo\s+do\s+tigre|"
        r"aviator|casino\s+(?:online|en\s+linea|gratis|con\s+bono)|tragamonedas\s+(?:online|gratis|con\s+bono))\b"), "казино / ставки (исп.)"),
    ("es_casino_word", "gamble", 1.0, _rx(r"\b(?:casinos?|tragamonedas|jackpot|apuestas?)\b"), "упоминание казино/ставок (исп.)"),
    ("es_bonus_dep", "gamble", 2.0, _rx(r"\b(?:bono|bonos|bonus|bonificacion|cashback|giros|tiradas|freebet)\b[^.!?\n]{0,40}\b(?:deposito|registro|registrate|registrarte|recarga|"
        r"primer\s+deposito|bienvenida|primera\s+recarga|sin\s+deposito)\b"), "бонус за депозит/регистрацию (исп.)"),
    ("es_promo_weak", "gamble", 1.2, _rx(r"\b(?:codigo\s+promocional|codigo\s+promo|promo\s?code|bono\s+(?:por|al|de)\s+(?:registro|registrarte|bienvenida))\b"), "промокод (исп.)"),
    ("es_giveaway", "promo", 1.2, _rx(r"\b(?:sorteo|sorteamos|sorteando|rifa|rifamos|regalamos|regalo\s+(?:de\s+)?(?:dinero|premios?)|ganaste|has\s+ganado|felicidades\s+(?:has|ha)\s+ganado|"
        r"eres\s+(?:el\s+)?ganador|fuiste\s+seleccionad\w+|premio\s+gratis|reclama\w*\s+(?:tu\s+)?(?:premio|regalo|bono|recompensa)|reparto\s+de\s+(?:dinero|premios)|"
        r"recoge\s+tu\s+premio|(?:robux|vbucks|v-bucks|pavos|diamantes|nitro|skins?)\s+gratis|gratis\s+(?:robux|vbucks|pavos|diamantes|nitro|skins?|iphone|dinero)|"
        r"generador\s+de\s+(?:robux|pavos|diamantes|vbucks|nitro|dinero))\b"), "розыгрыш-приманка (исп.)"),
    # ── 18+ / продажи / серые схемы ──
    ("es_adult_ad", "adult_ad", 2.5, _rx(r"\b(?:servicios?\s+(?:sexuales?|intimos?|para\s+adultos|eroticos?)|masajes?\s+(?:eroticos?|sensuales?|con\s+final\s+feliz)|escorts?|"
        r"acompanantes?\s+(?:de\s+lujo|vip|para\s+adultos)|damas?\s+de\s+compania|chicas?\s+(?:calientes?|disponibles?|solas?|cerca\s+de\s+ti|de\s+compania|para\s+adultos|vip|sexys?)|"
        r"solteras?\s+(?:cerca|calientes|en\s+tu\s+(?:zona|ciudad))|contenido\s+(?:para\s+adultos|adulto|explicito)|onlyfans|only\s+fans|fansly|cam\s?girls?|"
        r"sexo\s+(?:en\s+vivo|casual|virtual|por\s+(?:camara|webcam|videollamada))|videollamadas?\s+(?:eroticas?|hot|calientes|sexuales|intimas?)|sexting|"
        r"packs?\s+(?:de\s+)?(?:fotos?|videos?|nudes?|intim\w+|hot|\+?18|completos?|de\s+ella)|vendo\s+packs?|venta\s+de\s+packs?|pack\s+\+?18)\b"), "реклама 18+ (исп.)"),
    ("es_age18", "adult_ad", 1.0, _rx(r"(?:^|\s)(?:\+\s?18|18\s?\+)(?!\w)"), "метка 18+"),
    ("es_webcam", "adult_ad", 2.5, _rx(r"\btrabajo\s+(?:para|de)\s+(?:chicas?|mujeres|modelos?)\b|\bse\s+buscan?\s+(?:chicas?|modelos?|mujeres)\b|\bmodelos?\s+webcam\b|"
        r"\bgana\s+(?:dinero\s+)?como\s+modelo\s+(?:webcam|online|virtual)\b"), "вебкам / работа для девушек (исп.)"),
    ("es_sale_spam", "sale", 2.0, _rx(r"\b(?:vendo|compro|vendemos|compramos|alquilo|rento|rentamos|se\s+venden?)\s+(?:cuentas?|accounts?|bases?\s+de\s+datos|seguidores|followers|likes|"
        r"visitas|trafico|logins?|tarjetas?|cvv|dumps?|fullz|accesos?|numeros\s+virtuales|cuentas\s+bancarias?)\b"), "продажа аккаунтов/баз/карт (исп.)"),
    ("es_followers", "sale", 2.0, _rx(r"\b(?:comprar|compra|vendo|aumenta\w*|consigue|obten\w*)\s+(?:mas\s+|miles\s+de\s+|\d+\s+)?(?:seguidores|followers|likes|vistas|visitas|"
        r"suscriptores|reproducciones)\b|\b(?:seguidores|likes|suscriptores)\s+(?:baratos|reales|garantizados|a\s+bajo\s+costo)\b|\bpanel\s+smm\b"), "накрутка (исп.)"),
    ("es_cashout", "illegal", 3.0, _rx(r"\b(?:lavado\s+de\s+(?:dinero|activos)|blanqueo\s+de\s+capitales|clonacion\s+de\s+tarjetas?|tarjetas?\s+clonadas?|carding|cardeo|"
        r"cvv\s+(?:vivos?|frescos?|nuevos?)|dumps?\s+(?:con|y)\s+pin|fullz|bins?\s+(?:nuevos?|frescos?|vivos?)|cuentas?\s+(?:bancarias?\s+)?(?:rentadas?|mulas?)|"
        r"mulas?\s+bancari\w+|cheques?\s+falsos?|billetes?\s+falsos?|dolares?\s+falsos?|documentos?\s+falsos?|pasaportes?\s+falsos?|"
        r"licencias?\s+(?:de\s+conducir\s+)?sin\s+(?:examen|curso)|titulos?\s+(?:universitarios?\s+)?(?:falsos?|sin\s+estudiar)|diploma\s+(?:falso|sin\s+estudiar)|"
        r"certificados?\s+(?:falsos?|sin\s+examen))\b"), "обнал / серые схемы (исп.)"),
    ("es_drugs_sale", "illegal", 2.5, _rx(
        r"\b(?:mefedrona|cocaina|marihuana|hachis|extasis|mdma|lsd|ketamina|anfetamina\w*|metanfetamina|tusi|tusibi|fentanilo|heroina|setas\s+magicas|dmt|pastillas|pepas)\b"
        r"[^.!?\n]{0,60}\b(?:venta|vendo|vendemos|delivery|entrega\w*|envios?|a\s+domicilio|pedidos?|comprar|mayoreo|menudeo|por\s+gramo|calidad|pureza|disponible|stock|"
        r"catalogo|encargos?)\b|\b(?:venta|vendo|vendemos|delivery|entrega\w*|envios?|a\s+domicilio|pedidos?|catalogo)\b[^.!?\n]{0,60}\b(?:mefedrona|cocaina|marihuana|"
        r"hachis|extasis|mdma|lsd|ketamina|anfetamina\w*|metanfetamina|tusi|tusibi|fentanilo|heroina|dmt)\b"), "продажа запрещённых веществ (исп.)"),
    ("es_drugs", "illegal", 2.0, _rx(r"\b(?:mefedrona|alfa[\s-]?pvp|flakka|tusibi|3mmc|4mmc)\b"), "запрещённые вещества (исп.)"),
    ("es_recovery", "illegal", 3.0, _rx(r"\brecuper\w+\s+(?:de\s+)?(?:tus\s+|su\s+|los\s+)?(?:fondos|dinero|criptomonedas|cripto|bitcoins?|perdid\w+|estafad\w+)\b|"
        r"\bhackers?\s+(?:profesional|etico|certificado|para\s+recuper|para\s+hackear|confiable)\b|\b(?:hackeo|hackear|hackeamos)\s+(?:de\s+)?(?:cuentas?|instagram|"
        r"facebook|whatsapp|celular\w*|telefon\w*|tiktok|telegram|correos?)\b|\b(?:espiar|rastrear|monitorear|intervenir)\s+(?:el\s+)?(?:whatsapp|celular|telefono|movil|pareja|"
        r"esposo|esposa|novio|novia)\b"), "«вернём деньги» / взлом / слежка (исп.)"),
    ("es_occult", "sale", 2.0, _rx(r"\bamarres?\s+(?:de\s+amor)?\b|\b(?:recuper\w+|regres\w+)\s+(?:a\s+)?tu\s+(?:pareja|amor|ex)\b|\b(?:trabajos?|limpias?|rituales?)\s+espirituales?\b|"
        r"\b(?:maestro|brujo|vidente)\s+(?:espiritual|africano|del\s+amor|vidente)\b|\bendulzamiento\b|\bhechizos?\s+de\s+amor\b|\bleo\s+tarot\b|\btarotista\b"), "услуги «магов» (исп.)"),
    ("es_courses", "sale", 1.5, _rx(r"\b(?:curso|mentoria|mentor|academia|masterclass|webinar|coaching)\s+(?:de\s+|en\s+|gratis\s+de\s+)?(?:trading|cripto\w*|forex|inversion\w*|"
        r"libertad\s+financiera|negocios?\s+online|marketing\s+digital|dropshipping|afiliados?)\b"), "курсы «как разбогатеть» (исп.)"),
    # ── фишинг ──
    ("es_phish", "promo", 3.0, _rx(r"\b(?:tu|su)\s+cuenta\s+(?:sera|ha\s+sido|fue|esta)\s+(?:suspendid\w+|bloquead\w+|eliminad\w+|restringid\w+|limitad\w+|hackead\w+)\b|"
        r"\bverifica\s+tu\s+(?:cuenta|identidad)\s+(?:ahora|aqui|inmediatamente)\b|\bconect\w+\s+(?:tu\s+)?(?:billetera|wallet|cartera)\b|"
        r"\b(?:frase|palabras)\s+(?:semilla|secret\w+|de\s+recuperacion)\b|\bseed\s*phrase\b"), "фишинг: «аккаунт будет заблокирован / подключите кошелёк»"),
    ("es_premium_free", "promo", 2.0, _rx(r"\btelegram\s+premium\s+(?:gratis|gratuito|regalo)\b|\bpremium\s+gratis\b|\bestrellas\s+(?:de\s+telegram\s+)?gratis\b"), "«Telegram Premium бесплатно»"),
]

ES_SQUASH_RULES = [
    ("es_sq_earn", "job", 1.5, _rx(r"ganardinero|ganarplata|ganadinero|ganaplata"), "заработок (буквы разнесены, исп.)"),
    ("es_sq_nodep", "job", 2.0, _rx(r"sinexperiencia|sininversion|sininvertir"), "«без вложений» (буквы разнесены, исп.)"),
    ("es_sq_income", "job", 2.0, _rx(r"(?:dolares|usd|usdt|pesos|euros)(?:aldia|diarios|alasemana)|ingresospasivos|dineroextra"), "сумма «в день» (буквы разнесены, исп.)"),
    ("es_sq_cta", "cta", 2.0, _rx(r"escribeme(?:al|a|por)?(?:privado|dm|inbox|whatsapp|telegram)|mandame(?:al|a)?(?:privado|dm|inbox)|(?:al|por)privado|contactame(?:por)?(?:privado|whatsapp)"),
     "зовёт в личку (буквы разнесены, исп.)"),
    ("es_sq_gamble", "gamble", 2.5, _rx(r"casino|tragamonedas|apuestasdeportivas|girosgratis|frespins"), "казино/ставки (буквы разнесены, исп.)"),
]

ES_FAMILIES = {
    # Только «специфичные» слова: обычные «cuenta», «pasta», «único», «lana», «billete» сюда не входят — они и в нормальной речи на каждом шагу.
    "money": _rx(r"\b(?:dinero|plata|efectivo|ganancia\w*|ingresos?|sueldo|salario|cobr\w+|pagos?|pagan|pagamos|usdt|dolar\w*|euros?|pesos|soles|"
                 r"cripto\w*|bitcoin|inversion\w*|invertir|deposit\w+|prestamo\w*|credito\w*|rentabilidad|retiro|bizum|nequi|yape|plin|binance)\b"),
    "work": _rx(r"\b(?:trabajos?|empleos?|chambas?|laburo|curro|vacante\w*|reclut\w*|teletrabajo|negocio\w*|emprend\w+|sin\s+experiencia|sin\s+inversion|home\s*office|"
                r"medio\s+tiempo|tiempo\s+completo|colaborador\w*)\b"),
    "cta": _rx(r"\b(?:escrib\w+|mandame|mandanos|contact\w+|hablame|privado|priv|pv|dm|inbox|mensaje\s+directo|whats?app|wasap|wsp|telegram|tg|link|enlace|bio|"
               r"perfil|clic|click|suscrib\w+|unete|canal|registr\w+|inscrib\w+|interesad\w+)\b"),
    "hype": _rx(r"\b(?:gratis|regalo\w*|oferta\w*|descuento\w*|promo\w*|bono\w*|bonus|garantiz\w+|garantia|100\s?%|urgente|solo\s+hoy|cupos?|limitad\w+|rapido|facil|"
                r"sin\s+riesgo|exclusiv\w+|premio\w*|sorteo\w*|ganaste|felicidades)\b"),
    "sale": _rx(r"\b(?:vendo|vendemos|se\s+vende|alquilo|rento|seguidores|followers|bases?\s+de\s+datos|catalogo|pedidos?|domicilio|packs?|clonad\w+|cvv)\b"),
}
ES_SHADOWS = {
    "es_dm_hint": {"es_cta_dm", "es_cta_profile", "es_cta_plus", "es_sq_cta", "es_detail_dm"},
    "es_earn_word": {"es_earn_pitch", "es_earn_online", "es_income_day", "es_income_month", "es_task_scam", "es_passive", "es_sq_income", "es_paid_daily",
                     "es_phone_work", "es_income_goal"},
    "es_promo_weak": {"es_gamble", "es_sq_gamble", "es_bonus_dep"},
    "es_casino_word": {"es_gamble", "es_sq_gamble", "es_bonus_dep", "es_promo_weak"},
}

# «кукольный театр» (ask → pitch → confirm), провокации, верификация, телефоны, деньги
ES_ASK = (
    _rx(r"\b(?:alguien|alguno|alguna|quien|quienes|cualquiera)\b[^.!?\n]{0,40}\b(?:probo|probado|probaron|ha\s+probado|uso|usado|ha\s+usado|conoce|sabe|escucho|"
        r"ha\s+escuchado|trabajo|ha\s+trabajado|retiro|ha\s+retirado|cobro|ha\s+cobrado|invirtio|ha\s+invertido|tiene\s+experiencia|esta\s+al\s+tanto|sabe\s+algo)"),
    _rx(r"\b(?:es|sera|esta)\s+(?:confiable|segur[oa]|legit|legitim[oa]|real|verdader[oa]|fiable|de\s+fiar)\b|\b(?:es|sera)\s+(?:una\s+)?(?:estafa|fraude|engano|scam|timo|"
        r"mentira|piramide)\b|\bno\s+(?:sera|es)\s+(?:una\s+)?(?:estafa|fraude|engano|timo)\b|\b(?:confiable|segur[oa]|fiable|legitim[oa])\s*\?"),
    _rx(r"\b(?:vale|merece)\s+la\s+pena\b|\b(?:funciona|paga|pagan|cumple|retira|retiran|responde)\s*\?|\b(?:de\s+verdad|en\s+serio|realmente)\s+(?:funciona|paga|pagan|sirve)\b"),
    _rx(r"\b(?:recomiend\w+|sugier\w+|aconsej\w+|diganme|dime)\b[^.!?\n]{0,50}\b(?:casa\s+de\s+cambio|exchange|plataforma|pagina|sitio|bot|app|aplicacion|broker|trader|"
        r"billetera|wallet|casino|metodo|trabajo|inversion|proyecto|servicio|prestamo)"),
    _rx(r"\bdonde\s+(?:puedo|se\s+puede|puedes|pueden|conviene|me\s+conviene|es\s+mejor|es\s+seguro)\s+(?:cambiar|retirar|ganar|comprar\s+(?:usdt|cripto\w*|bitcoin)|invertir|sacar|cobrar|depositar)"),
)
ES_CLAIM = _rx(r"\b(?:cobre|cobraron|me\s+pagaron|me\s+pago|me\s+pagan|retire|retiraron|me\s+llego|me\s+llegaron|me\s+deposito|me\s+depositaron|me\s+transfirieron|ya\s+cobre|"
               r"ya\s+retire|ganamos|funciona|paga|pagan|confiable|legit|recomiendo|recomendado|recomiendan|lo\s+recomiendo|comprobado|verificado|"
               r"no\s+es\s+(?:estafa|fraude|mentira|engano)|sin\s+(?:estafa|fraude|engano)|pagina\s+seria|persona\s+seria)\b")
ES_CONFIRM = (
    _rx(r"(?<!no\s)\b(?:funciona|funciono|paga|pagan|cumple|cumplio|retire|cobre|cobramos|me\s+(?:pagaron|llego|llegaron|deposito|depositaron)|ya\s+(?:cobre|retire|me\s+llego|"
        r"me\s+pagaron)|recibi\s+(?:mi\s+)?pago|comprobado|confirmo|confirmado|todo\s+(?:real|legal|legit)|es\s+(?:real|legit|legitim[oa]|seguro|confiable))\b|"
        r"\bno\s+es\s+(?:estafa|fraude|mentira|engano|timo)\b|\bsin\s+(?:estafa|fraude|engano)\b"),
    _rx(r"\bgracias\s+(?:por\s+(?:el|la|los|las)\s+(?:link|enlace|dato|datos|info|informacion|consejo|recomendacion|contacto|ayuda|aviso)|hermano|bro|amigo|compa|crack|capo|maquina)\b|"
        r"\bagradezco\s+(?:el|la)\s+(?:dato|info|consejo)\b|\byo\s+(?:tambien\s+)?(?:cobre|retire|probe|pruebo|uso|lo\s+uso|lo\s+use)\b|\btambien\s+(?:cobre|retire|probe|me\s+(?:pagaron|llego))\b"),
)
ES_BAIT_RX = (
    _rx(r"\bnadie\s+(?:te\s+)?(?:pregunto|pidio|necesita|quiere|ha\s+preguntado|te\s+ha\s+preguntado)\b|\ba\s+nadie\s+le\s+importa\b"),
    _rx(r"\b(?:cal+mate|tranquilizate|relajate|no\s+llores|llorona|llorica|dejate\s+de\s+llorar|deja\s+de\s+llorar|enojon|amargad[oa])\b"),
    _rx(r"\b(?:tienes|tiene|tendras)\s+(?:problemas|algun\s+problema)\s+(?:mentales|psicologicos|de\s+cabeza|en\s+la\s+cabeza|de\s+ira|en\s+casa|con\s+la\s+vida)\b"),
    _rx(r"\b(?:ve|anda|vete|andate)\s+(?:a|al)\s+(?:un\s+)?(?:psicolog\w+|psiquiatr\w+|medico|doctor|terapeuta)\b"),
    _rx(r"\bno\s+(?:hagas|hagan)\s+(?:el|la)\s+(?:ridicul\w+|payas\w+|papelon)\b|\bque\s+(?:verguenza|asco|pena)\s+(?:das|dan|de\s+persona)\b"),
    _rx(r"\bsabelotodo\b|\bse\s+cree(?:s)?\s+(?:muy\s+)?(?:listo|vivo|importante|gracioso)\b"),
    _rx(r"\b(?:eres|sos)\s+(?:un|una)?\s*(?:payas\w+|ridicul\w+|inutil|basura|escoria|parasit\w+|fracasad\w+|perdedor|loser|idiota|imbecil|estupid\w+|subnormal|retrasad\w+|"
        r"mongol\w*|tarad\w+|bobo|tonto|lerdo|cretino)\b"),
    _rx(r"\b(?:callate|cayate|cierra\s+la\s+boca|cierra\s+el\s+pico|cierren\s+la\s+boca)\b"),
    _rx(r"\btoca\s+(?:pasto|cesped)\b|\btouch\s+grass\b|\bcry\s+about\s+it\b|\bskill\s+issue\b|\bratio\b"),
)
ES_VERIFY = _rx(r"\b(?:verific\w+\s+(?:tu\s+)?(?:cuenta|identidad)|confirm\w+\s+(?:tu\s+)?(?:cuenta|identidad)|activ\w+\s+(?:tu\s+)?(?:bono|cuenta|premio)|"
                r"(?:pulsa|presiona|toca|dale)\s+(?:start|iniciar|comenzar)|escrib\w+\s+(?:al|a)\s+(?:bot)|suscrib\w+\s+(?:a\s+)?(?:mi|nuestro|este)\s+canal|"
                r"(?:obten|reclama|recibe|retira|recoge|cobra)\w*\s+(?:tu\s+)?(?:bono|premio|pago|recompensa|regalo))\b")
ES_GIVE_BRAND = _rx(r"\b(?:telegram|premium|ton|toncoin|durov|elon|musk|mrbeast|mr\s+beast|usdt|bitcoin|nft|dolares)\b")
ES_GIVE_WALLET = _rx(r"\b(?:billetera|cartera|wallet|conect\w+|seed|frase\s+semilla)\b")
ES_GIVE_RX = _rx(r"\b(?:sorteo|sorteamos|rifa|regalamos|ganaste|has\s+ganado|premio\s+gratis|reparto\s+de\s+(?:dinero|premios)|reclama\w*\s+(?:tu\s+)?(?:premio|regalo|bono|recompensa))\b")
ES_MONEY = r"(?<![\d\s.,])(?=([\s.,]*\d[\d\s.,]*))\1(?:pesos?|soles?|dolar\w*|dls|lucas|mil\s+(?:pesos|soles|dolares|euros))|\bs/\s?\d+"
ES_PHONE = (r"(?<![\d\w])(?:\+\s?(?:34|52|54|56|57|51|58|593|591|595|598|506|507|503|502|504|505|53)[\s.\-]?(?:9[\s.\-]?)?(?:\d[\s.\-]?){7,10}\d|"
            r"[67]\d{2}[\s.\-]?\d{3}[\s.\-]?\d{3}|[67]\d{2}[\s.\-]?\d{2}[\s.\-]?\d{2}[\s.\-]?\d{2}|9\d{2}[\s.\-]?\d{3}[\s.\-]?\d{3}|9[\s.\-]?\d{4}[\s.\-]?\d{4})(?![\d\w])")
ES_BAIT_URL = _w("""gratis regalo regalos premio premios bono bonos ganar dinero retiro prestamo prestamos sorteo oferta cripto verificar billetera recompensa
descuento apuestas tragamonedas ganancias airdrop""")
ES_BRANDS = {
    "mercadopago": {"mercadopago.com", "mercadopago.com.ar", "mercadopago.com.mx", "mercadopago.cl", "mercadopago.com.co", "mercadopago.com.pe", "mercadopago.com.uy"},
    "mercadolibre": {"mercadolibre.com", "mercadolibre.com.ar", "mercadolibre.com.mx", "mercadolibre.cl", "mercadolibre.com.co", "mercadolibre.com.pe"},
    "santander": {"santander.com", "santander.es", "santander.com.mx", "santander.cl", "santander.com.ar"},
    "caixabank": {"caixabank.es", "caixabank.com"}, "bancolombia": {"bancolombia.com", "grupobancolombia.com"}, "nequi": {"nequi.com.co", "nequi.com"},
    "daviplata": {"daviplata.com"}, "banorte": {"banorte.com"}, "banamex": {"banamex.com", "citibanamex.com"}, "bancoestado": {"bancoestado.cl"},
    "scotiabank": {"scotiabank.com", "scotiabank.cl", "scotiabank.com.mx", "scotiabank.com.pe", "scotiabank.com.co"}, "interbank": {"interbank.pe"},
    "correos": {"correos.es"}, "sabadell": {"bancsabadell.com", "sabadell.com"}, "revolut": {"revolut.com"}, "westernunion": {"westernunion.com"},
    "telcel": {"telcel.com"}, "movistar": {"movistar.es", "movistar.com.ar", "movistar.cl", "movistar.com.mx", "movistar.com.co", "movistar.com.pe", "telefonica.com"},
}
ES_ROLE = (r"soporte|atencion\s*al\s*cliente|servicio\s*al\s*cliente|asistencia|administrad|moderad|oficial|seguridad|verificad|verificacion")
ES_STOP = _w("""de la que el en y a los se del las un por con no una su para es al lo como mas pero sus le ya o fue este ha si porque esta entre cuando muy sin sobre
tambien me hasta hay donde quien desde todo nos todos uno les ni contra otros ese eso ante ellos e esto mi antes algunos unos yo otro otra tanto esa estos mucho nada
muchos cual poco ella estar estas algo mis tu te ti tus eres soy estoy voy vas va vamos quiero puedo puede tengo tienes tiene hola gracias bueno vale pues ok""")


# ══════════════════════════════════════════════════════════════════════════════════════
#  ФИШКА 2: правдоподобность заработка («gana 3000 pesos al día» → сколько это в долларах?)
#  Курсы — ориентировочные (окт. 2026), нужны только чтобы отличить «500 pesos в день» от «500 dólares в день».
# ══════════════════════════════════════════════════════════════════════════════════════
RATES = {"usd": 1.0, "eur": 1.14, "mxn": 1 / 18.7, "cop": 1 / 3300, "ars": 1 / 1500, "clp": 1 / 970, "pen": 1 / 3.44, "ves": 1 / 855}
_COUNTRY_HINT = (
    ("mxn", re.compile(r"\b(?:mexico|mexicano\w*|mx|cdmx|oxxo|spei|clabe|telcel|guadalajara|monterrey)\b")),
    ("cop", re.compile(r"\b(?:colombia\w*|bogota|medellin|cali|nequi|daviplata|bancolombia|cop)\b")),
    ("ars", re.compile(r"\b(?:argentin\w+|buenos\s+aires|cbu|cvu|mercado\s*pago|ars)\b")),
    ("clp", re.compile(r"\b(?:chile\w*|santiago|clp|rut|webpay)\b")),
    ("pen", re.compile(r"\b(?:peru\w*|lima|yape|plin|soles?|pen)\b")),
    ("eur", re.compile(r"\b(?:espana|espanol\w*|bizum|iban|madrid|barcelona|euros?)\b")),
)
_EARN_CTX = re.compile(r"\b(?:gana\w*|ganancia\w*|ingres\w*|genera\w*|cobra\w*|pagan|paga|retiro\w*|sueldo|salario|trabaj\w+)\b")
_AMT_RX = re.compile(
    r"(?<![\w.,])(?:(?P<pre>\$|us\$|€)\s?)?(?P<n>\d{1,3}(?:[.,\s]\d{3})+|\d+(?:[.,]\d{1,2})?)\s?(?P<k>k|mil)?\s?"
    r"(?P<cur>usdt?|dolar(?:es)?|dls|euros?|eur|€|pesos?(?:\s+(?:mexicanos?|colombianos?|argentinos?|chilenos?))?|mxn|cop|ars|clp|soles?|pen|\$)?\s*"
    r"(?:(?:al|por|x|cada|/)\s*(?P<per>dia|semana|mes|hora)\b|(?P<adv>diarios?|diarias?|semanales|mensuales|a\s+diario)\b)")


def _num(s: str) -> float:
    s = s.replace(" ", "")
    if re.fullmatch(r"\d{1,3}(?:[.,]\d{3})+", s):
        return float(re.sub(r"[.,]", "", s))
    return float(s.replace(",", "."))


def income_usd_per_day(fn: str) -> tuple:
    """(лучшая оценка $/день, фрагмент, валюта) по самой «щедрой» сумме в тексте; (0, '', '') если нет."""
    if not _EARN_CTX.search(fn):
        return 0.0, "", ""
    hint = next((c for c, rx in _COUNTRY_HINT if rx.search(fn)), "")
    best = (0.0, "", "")
    for m in _AMT_RX.finditer(fn):
        try:
            n = _num(m.group("n"))
        except ValueError:
            continue
        if m.group("k"):
            n *= 1000
        cur = (m.group("cur") or "").strip()
        pre = m.group("pre") or ""
        if cur.startswith(("usd", "dol", "dls")) or pre == "us$":
            code = "usd"
        elif cur.startswith("eur") or "€" in (cur + pre):
            code = "eur"
        elif cur in ("mxn", "cop", "ars", "clp", "pen") or cur.startswith("sol"):
            code = "pen" if cur.startswith("sol") else cur
        elif cur.startswith("peso") or cur == "$" or pre == "$" or not cur:
            if cur.startswith("peso") and "mexican" in cur:
                code = "mxn"
            elif cur.startswith("peso") and "colombian" in cur:
                code = "cop"
            elif cur.startswith("peso") and "argentin" in cur:
                code = "ars"
            elif cur.startswith("peso") and "chilen" in cur:
                code = "clp"
            elif hint in ("mxn", "cop", "ars", "clp", "pen") and (cur.startswith("peso") or n >= 1000):
                code = hint
            elif cur.startswith("peso") or n >= 1000:
                code = "mxn" if n < 20000 else "clp" if n < 80000 else "cop"   # осторожно: «много нулей» = местная валюта
            else:
                code = "usd"
        else:
            continue
        per = m.group("per") or ""
        adv = (m.group("adv") or "")
        if per == "dia" or adv.startswith(("diari", "a diario")):
            div = 1.0
        elif per == "semana" or adv.startswith("semanal"):
            div = 7.0
        elif per == "mes" or adv.startswith("mensual"):
            div = 30.0
        elif per == "hora":
            div = 1 / 8
        else:
            continue
        usd_day = n * RATES[code] / div
        if usd_day > best[0]:
            best = (usd_day, m.group(0).strip(), code.upper())
    return best


# ══════════════════════════════════════════════════════════════════════════════════════
#  ФИШКА 3: сеть реквизитов. IBAN / CLABE / CBU / карта / кошелёк → «контакт» для связи аккаунтов (contact_net guard)
#  Реквизиты проверяются контрольными суммами (меньше ложных), в память идёт только хэш.
# ══════════════════════════════════════════════════════════════════════════════════════
import hashlib

_IBAN_LEN = {"ES": 24, "PT": 25, "FR": 27, "IT": 27, "DE": 22, "GB": 22, "NL": 18, "BE": 16, "AR": 28, "CR": 22, "DO": 28, "GT": 28, "SV": 28,
             "BR": 29, "PL": 28, "CH": 21, "AT": 20, "IE": 22, "LU": 20, "AD": 24, "MT": 31, "LT": 20, "LV": 21, "EE": 20, "UA": 29, "TR": 26, "AE": 23,
             "SA": 24, "GR": 27, "SE": 24, "NO": 15, "DK": 18, "FI": 18, "CZ": 24, "RO": 24, "BG": 22, "HU": 28}
_IBAN_RX = re.compile(r"(?<![A-Za-z0-9])[A-Za-z]{2}\d{2}(?:[ \-]?[A-Za-z0-9]{4}){2,7}(?:[ \-]?[A-Za-z0-9]{1,4})?(?![A-Za-z0-9])")
_DIG_RX = re.compile(r"(?<![\d])(?:\d[ \-]?){12,21}\d(?![\d])")


def _iban_ok(s: str) -> bool:
    s = re.sub(r"[ \-]", "", s).upper()
    if not (15 <= len(s) <= 34 and s[:2].isalpha() and s[2:4].isdigit()):
        return False
    r = s[4:] + s[:4]
    try:
        return int("".join(str(int(c, 36)) for c in r)) % 97 == 1
    except ValueError:
        return False


def _clabe_ok(d: str) -> bool:
    if len(d) != 18:
        return False
    w = [3, 7, 1] * 6
    s = sum((int(d[i]) * w[i]) % 10 for i in range(17))
    return (10 - s % 10) % 10 == int(d[17])


def _cbu_ok(d: str) -> bool:
    if len(d) != 22:
        return False
    w1, w2 = [7, 1, 3, 9, 7, 1, 3], [3, 9, 7, 1, 3, 9, 7, 1, 3, 9, 7, 1, 3]
    c1 = (10 - sum(int(d[i]) * w1[i] for i in range(7)) % 10) % 10 == int(d[7])
    c2 = (10 - sum(int(d[8 + i]) * w2[i] for i in range(13)) % 10) % 10 == int(d[21])
    return c1 and c2


def _luhn_ok(d: str) -> bool:
    if not 13 <= len(d) <= 19:
        return False
    s, alt = 0, False
    for ch in reversed(d):
        n = int(ch)
        if alt:
            n *= 2
            if n > 9:
                n -= 9
        s += n
        alt = not alt
    return s % 10 == 0 and len(set(d)) > 2


def _h(kind: str, v: str) -> str:
    return kind + ":" + hashlib.sha1(v.encode()).hexdigest()[:12]


@lru_cache(maxsize=2048)
def pay_ids(raw: str) -> tuple:
    """Реквизиты для перевода в тексте: ((вид, хэш-токен), …). Виды: iban, clabe, cbu, card."""
    out: list = []
    t = raw[:3000]
    for m in _IBAN_RX.finditer(t):
        comp = re.sub(r"[ \-]", "", m.group(0)).upper()
        n = _IBAN_LEN.get(comp[:2])
        if n and len(comp) >= n and _iban_ok(comp[:n]):       # длина строго по стране: хвост-«слово» не мешает
            out.append(("iban", _h("pay", comp[:n])))
    low = t.lower()
    kw_cbu = bool(re.search(r"\b(?:cbu|cvu)\b", low))
    for m in _DIG_RX.finditer(t):
        d = re.sub(r"\D", "", m.group(0))
        if len(d) == 18 and _clabe_ok(d):
            out.append(("clabe", _h("pay", d)))
        elif len(d) == 22 and (_cbu_ok(d) or kw_cbu):
            out.append(("cbu", _h("pay", d)))
        elif 13 <= len(d) <= 19 and _luhn_ok(d):
            out.append(("card", _h("pay", d)))
    return tuple(dict.fromkeys(out))


_PAY_ASK = re.compile(r"\b(?:transfiere|transfieran|deposita|depositen|envia|envien|abona|paga|pagan|manda)\w*\b[^.!?\n]{0,100}\b(?:cuenta|clabe|cbu|cvu|iban|tarjeta|titular|a\s+nombre\s+de|alias)\b")


def wallet_ids(g, raw: str) -> tuple:
    try:
        return tuple(_h("wal", m.group(0).lower()) for m in g._WALLET_RE.finditer(raw[:3000]))
    except Exception:
        return ()


# ══════════════════════════════════════════════════════════════════════════════════════
#  «ОБЪЯСНЯЛКА»: почему бот сработал (для админов и для отладки)
# ══════════════════════════════════════════════════════════════════════════════════════
_MODE_RU = {"plain": "как написано", "leet": "маскировка цифрами/символами", "mask": "звёздочки/маска", "homoglyph": "кириллица вместо латиницы",
            "vu": "v вместо u", "spaced": "буквы разнесены", "joined": "точки/дефисы внутри слова", "слитно": "слитное написание",
            "опечатка": "опечатка (1 буква)"}


def explain(text: str, g=None) -> list:
    """Человекочитаемый разбор (на русском): что нашли в словарях, что пропустили и почему, какие спам-сигналы и итоговая оценка."""
    lines: list = []
    r = es_scan(text)
    names = {"prof_hard": "МАТ (жёсткий)", "prof_soft": "мат (мягкий)", "hate": "НЕНАВИСТЬ", "adult": "18+", "minor": "детская тема", "threat": "ПРИЗЫВ/УГРОЗА"}
    for cat, word, surface, mode in r.hits:
        how = _MODE_RU.get(mode, mode)
        extra = "" if surface == word else f" (в тексте: «{surface}»)"
        lines.append(f"{names.get(cat, cat)}: «{word}»{extra} — {how}")
    if r.skipped:
        lines.append("РЕЖИМ «ДРУЗЕЙ»: мягкие слова %s не засчитаны — не адресованы человеку и их меньше двух" % ", ".join("«%s»" % w for w in r.skipped))
    if not r.hits:
        lines.append("словари: ничего не найдено")
    if g is not None:
        a = g.analyze_text(text)
        for n, w, why in sorted(a.signals, key=lambda s: -s[1]):
            lines.append(f"сигнал {n} (+{w:g}): {why}")
        lines.append("ИТОГО: raw=%g, из них «жёстких»=%g; пороги guard: наблюдать ≥%g, удалить ≥%g, бан новичку ≥%g" % (a.raw, a.hard, g.WATCH_T, g.DELETE_T, g.BAN_T))
        lines.append("найдено guard'ом: мат=%s ненависть=%s 18+=%s дети=%s" % (a.found.get("prof"), a.found.get("hate"), a.found.get("adult"), a.found.get("minor")))
    return lines


# ══════════════════════════════════════════════════════════════════════════════════════
#  УСТАНОВКА В guard.py
# ══════════════════════════════════════════════════════════════════════════════════════
_CYR_RE = re.compile(r"[а-яё]")
_KIKE_CTX = re.compile(r"\b(?:sucio|puto|asqueroso|maldito|judio|dirty|filthy)\W+kikes?\b|\bkikes?\W+(?:de\s+mierda|sucio|asqueroso|filthy|dirty)\b")


def _fix_guard_fp(a, text: str, fn: str) -> None:
    """У самого guard.py на испанском есть ложные срабатывания: «huevos» (huev- = транслит русского «хуев-») и имя «Kike» (кайк)."""
    f = a.found
    if f.get("prof"):
        f["prof"] = [t for t in f["prof"] if not (t.startswith("huevo") and not _CYR_RE.search(text))]
    hate = f.get("hate")
    if hate and any(t.startswith("kike") for t in hate):
        if not _KIKE_CTX.search(fn) and (looks_spanish(text) or len(fn.split()) <= 3):
            f["hate"] = [t for t in hate if not t.startswith("kike")]


_CASINO_STRONG = re.compile(r"\b(?:bono|bonos|giros|regist\w+|deposit\w+|gratis|apuest\w+|promo\w*|codigo|cashback|1win|1xbet|bet365|melbet|mostbet|"
                            r"escrib\w+|privado|whats\w*|telegram|link|enlace|unete|gana\w*|dinero|premio\w*)\b")


def _soften_casino(a, text: str, fn: str) -> None:
    """Правило «casino/jackpot» в самом guard.py не знает языка: «mi hermano trabaja en un casino de Las Vegas» — не реклама.
    В испанском тексте без промо-слов (бонус, регистрация, пиши в лс…) считаем это слабым признаком."""
    if not any(s[0] == "gamble" for s in a.signals) or not looks_spanish(text) or _CASINO_STRONG.search(fn):
        return
    a.signals[:] = [(n, 1.0, w) if n == "gamble" else (n, v, w) for n, v, w in a.signals]
    a.raw = round(sum(v for _, v, _ in a.signals), 2)


def _allow_of(g) -> tuple:
    try:
        return tuple(skel(fold_word(w)) for w in g._custom.get("allow", ()) if w)
    except Exception:
        return ()


def _merge(g, a, text: str) -> None:
    fn = es_fold(text, False)
    _fix_guard_fp(a, text, fn)
    _soften_casino(a, text, fn)
    r = es_scan(text, _allow_of(g))
    f = a.found
    if r.prof:
        f["prof"] = list(dict.fromkeys(list(f.get("prof", [])) + list(r.prof)))
    hate = list(r.hate) + (list(r.threat) if ES_THREATS else [])
    if hate:
        f["hate"] = list(dict.fromkeys(list(f.get("hate", [])) + hate))
    if r.adult:
        f["adult"] = list(dict.fromkeys(list(f.get("adult", [])) + list(r.adult)))
    if r.minor:
        f["minor"] = True
    extra: list = []
    if ES_SPAM:
        have = {s[0] for s in a.signals}
        usd, frag, cur = income_usd_per_day(fn)
        if usd >= 300:
            extra.append(("es_income_absurd", 2.5, f"«{frag[:40]}» ≈ ${usd:,.0f}/день ({cur}) — нереалистичный заработок"))
        elif usd >= 100:
            extra.append(("es_income_absurd", 1.5, f"«{frag[:40]}» ≈ ${usd:,.0f}/день ({cur}) — слишком щедро для «лёгкой работы»"))
        pays = pay_ids(text)
        if pays:
            kinds = "/".join(sorted({k.upper() for k, _ in pays}))
            extra.append(("es_pay_details", 1.5, f"реквизиты для перевода в чате ({kinds})"))
            if _PAY_ASK.search(fn):
                extra.append(("es_pay_ask", 1.0, "просит перевести деньги на реквизиты"))
        if "giveaway_combo" not in have and ES_GIVE_RX.search(fn) and ES_GIVE_BRAND.search(fn) and (g._WALLET_RE.search(text) or ES_GIVE_WALLET.search(fn)):
            extra.append(("giveaway_combo", 3.0, "раздача + громкий бренд + кошелёк: фишинг под розыгрыш (исп.)"))
    if extra:
        a.signals.extend(extra)
        a.raw = round(sum(w for _, w, _ in a.signals), 2)
        a.hard = round(sum(w for n, w, _ in a.signals if n in g.HARD_SIGNALS), 2)
    if any(str(t).startswith(("pay:", "wal:")) for t in (a.contacts or ())):
        a.has_contact = True


def _wrap_analyze(g, orig):
    def analyze_text(text, ents=(), cfg=None, fwd="", known_names=()):
        a = orig(text, ents, cfg, fwd, known_names=known_names)
        if ES_ON and text:
            try:
                _merge(g, a, text)
            except Exception:
                log_es.exception("guard_es: сбой разбора, оставляю результат guard как есть")
        return a
    analyze_text.__wrapped__ = orig
    return analyze_text


def _wrap_contacts(g, orig):
    def contact_tokens(urls, handles, raw_text):
        out = list(orig(urls, handles, raw_text))
        if ES_ON and ES_SPAM and raw_text:
            try:
                extra = [t for _, t in pay_ids(raw_text)] + list(wallet_ids(g, raw_text))
                for mt in _ES_PHONE_RX.finditer(raw_text[:3000]):
                    d = re.sub(r"\D", "", mt.group(0))
                    if len(d) == 9:
                        extra.append("tel:" + d)
                out = list(dict.fromkeys(out + extra))[:10]
            except Exception:
                log_es.exception("guard_es: сбой разбора контактов")
        return tuple(out)
    contact_tokens.__wrapped__ = orig
    return contact_tokens


_ES_PHONE_RX = re.compile(ES_PHONE)


def _or(old, new: str, extra_flags: int = 0):
    return re.compile("(?:%s)|(?:%s)" % (old.pattern, new), old.flags | extra_flags)


def install(g, quiet: bool = False) -> bool:
    """Подключить испанский модуль к модулю guard (g). Безопасно вызывать повторно."""
    if getattr(g, "_ES_INSTALLED", False):
        return False
    try:
        g.load_env()
    except Exception:
        pass
    es_reload_env()
    if not ES_ON:
        if not quiet:
            log_es.info("испанский модуль выключен (GUARD_ES=0)")
        return False
    # 1) ложные срабатывания английского правила на «investigación / investigar»
    for i, (name, group, w, rx, why) in enumerate(list(g.SPAM_RULES)):
        if name == "en_invest" and r"invest\w*" in rx.pattern:
            g.SPAM_RULES[i] = (name, group, w, re.compile(rx.pattern.replace(r"invest\w*", r"invest(?!ig)\w*"), rx.flags), why)
    g.FAMILIES["money"] = re.compile(g.FAMILIES["money"].pattern.replace(r"invest\w*", r"invest(?!ig)\w*"), g.FAMILIES["money"].flags)
    # 2) спам-правила, семейства, «кукольный театр», провокации
    if ES_SPAM:
        g.SPAM_RULES.extend(ES_SPAM_RULES)
        g.SQUASH_RULES.extend(ES_SQUASH_RULES)
        for k, rx in ES_FAMILIES.items():
            g.FAMILIES[k] = _or(g.FAMILIES[k], rx.pattern)
        for k, v in ES_SHADOWS.items():
            g.SHADOWS[k] = set(v)
        g._ASK_RX = tuple(g._ASK_RX) + ES_ASK
        g._CONFIRM_RX = tuple(g._CONFIRM_RX) + ES_CONFIRM
        g._CLAIM_RX = _or(g._CLAIM_RX, ES_CLAIM.pattern)
        g._MONEY_RX = re.compile(g._MONEY_RX.pattern + "|" + ES_MONEY.replace(r"\1", r"\2"), g._MONEY_RX.flags)
        g._VERIFY_RX = _or(g._VERIFY_RX, ES_VERIFY.pattern)
        g._GIVE_BRAND_RX = _or(g._GIVE_BRAND_RX, ES_GIVE_BRAND.pattern)
        g._PHONE_RE = _or(g._PHONE_RE, ES_PHONE)
        g.BAIT.update(ES_BAIT_URL)
        for k, v in ES_BRANDS.items():
            g.BRANDS.setdefault(k, set()).update(v)
            g._OFFICIAL.update(v)
        g.ROLE_RE = re.compile(g.ROLE_RE.pattern + "|" + ES_ROLE)
        g.contact_tokens = _wrap_contacts(g, g.contact_tokens)
    if ES_BAIT:
        g._BAIT_RX = tuple(g._BAIT_RX) + ES_BAIT_RX
    g.LEARN_STOP = frozenset(g.LEARN_STOP) | frozenset(ES_STOP)
    # 3) главный разбор: мат / ненависть / 18+ / дети / призывы + фишки
    g.analyze_text = _wrap_analyze(g, g.analyze_text)
    orig_reload = getattr(g, "ax_reload_env", None)
    if orig_reload is not None:
        def ax_reload_env():
            orig_reload()
            es_reload_env()
        g.ax_reload_env = ax_reload_env
    g._ES_INSTALLED = True
    g.ES_VERSION = VERSION_ES
    if not quiet:
        log_es.info("guard_es %s подключён: мат/ненависть/18+ %s, спам-правила %d, режим «друзей»: %s, призывы: %s",
                    VERSION_ES, "вкл", len(ES_SPAM_RULES) if ES_SPAM else 0, "вкл" if FRIENDS_ON else "выкл", "вкл" if ES_THREATS else "выкл")
    return True


# ══════════════════════════════════════════════════════════════════════════════════════
#  ЗАПУСК:  python guard_es.py            — guard с испанским модулем (без правки guard.py)
#           python guard_es.py --check "текст"   — разбор вручную;  --selftest — быстрая самопроверка
# ══════════════════════════════════════════════════════════════════════════════════════
def _import_guard():
    here = os.path.dirname(os.path.abspath(__file__))
    if here not in sys.path:
        sys.path.insert(0, here)
    import importlib
    return importlib.import_module("guard")


def _selftest() -> int:
    ok = [("eres un hijo de puta", "prof"), ("p*ta madre", "prof"), ("maricón de mierda", "hate"), ("videos porno gratis", "adult"), ("suicídate", "threat")]
    bad = ["computadora", "Vergara", "compré huevos", "Kike", "hola weón, cómo estás", "la perra de mi vecina", "Culiacán"]
    fails = 0
    for t, cat in ok:
        r = es_scan(t)
        if not getattr(r, cat):
            print("НЕ поймал:", t)
            fails += 1
    for t in bad:
        r = es_scan(t)
        if r.prof or r.hate or r.adult or r.threat:
            print("ЛОЖНОЕ срабатывание:", t, r.prof, r.hate)
            fails += 1
    print("самопроверка: %s" % ("ОК" if not fails else "ЕСТЬ ОШИБКИ (%d)" % fails))
    return 1 if fails else 0


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv and argv[0] == "--selftest":
        return _selftest()
    if argv and argv[0] == "--check":
        text = " ".join(argv[1:]) or sys.stdin.read()
        g = None
        try:
            g = _import_guard()
            install(g, quiet=True)
        except Exception as e:                       # guard/aiogram недоступны — покажем хотя бы словари
            print("(guard.py не загрузился: %s — показываю только словари)" % e)
        print("\n".join("• " + x for x in explain(text, g)))
        return 0
    import asyncio
    g = _import_guard()
    install(g)
    r = g.ax_cli(argv) if hasattr(g, "ax_cli") else None
    if r is not None:
        return r
    if argv and argv[0].startswith("-"):
        return g.cli(argv)
    try:
        asyncio.run(g.main())
    except KeyboardInterrupt:
        pass
    except SystemExit as e:
        if e.code not in (None, 0):
            print(e.code, file=sys.stderr)
            raise
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
