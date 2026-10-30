#!/usr/bin/env python3
# guard_ar 1.0 — арабский модуль для guard.py. Отдельный файл: guard.py не правится.
#
# Что делает (то же, что guard делает с русским, только для арабского):
#   • мат/оскорбления (prof), ненависть (hate), 18+ (adult), детская тема (minor) — на словах, фразах и «обходах»;
#   • спам-правила (заработок, инвестиции, кредиты, казино, 18+, взлом, накрутка, фишинг, «пришли код» и т.д.)
#     с теми же группами/весами, что у русских правил guard, и теми же комбинациями (pitch+cta, families);
#   • обходы: огласовки, татвиль «ـــ», растяжки «كلللب», разные формы алефа/йа/та-марбуты, персидские буквы
#     (ک ی ہ گ چ پ ڤ), арабо-индийские цифры, буквы «через пробел/точку/звёздочку», цифровой «лит» (3=ع 7=ح 5=خ 9=ص …),
#     «точечные» подмены (ب↔ن↔ت), приставки و/ف/ب/ل/ك/ال и суффиксы-местоимения;
#   • арабизи (латиницей: sharmouta, 3ars, 9a7ba, kos omak …) — для самого опасного и самого частого;
#   • свои слова без правки кода: custom_words_ar.txt (формат ниже), перечитывается командой reload().
#
# Подключение (одна строка в guard.py, ближе к концу, перед main(); guard при этом не меняется «по смыслу»):
#       import guard_ar; guard_ar.install(sys.modules[__name__])
# Проверка руками:  python guard_ar.py "نص"      ·      python guard_ar.py --selftest
#
# Переменные окружения (.env):
#   GUARD_AR=0            выключить модуль целиком
#   GUARD_AR_NATIVE=0     не снимать с арабского «чужой алфавит» (по умолчанию снимаю: для арабоязычного чата это норма)
#   GUARD_AR_ARABIZI=0    не смотреть арабизи (латиницу)
#   GUARD_AR_SECT=0       не считать «ненавистью» сектантские ярлыки (رافضي، مجوسي، نصيري …)
#   GUARD_AR_WORDS=путь   файл со своими словами (по умолчанию custom_words_ar.txt рядом с запуском)
#
# Формат custom_words_ar.txt (как custom_words.txt у guard; «#» — комментарий):
#       prof:  كلمة            слово целиком (+ местоимения: كلبك، كلبه …)
#       prof:  كلمة*           основа (любое окончание до 5 букв)
#       prof:  =كلمة           ровно это слово (с приставкой «ال/و/ف»)
#       hate:  …   adult:  …   minor:  …
#       allow: كلمة            слово-исключение (не считать нарушением)
#       spam:  фраза           фраза-приманка, +2.0 к оценке     ·   spam: фраза | 3.5   — со своим весом
from __future__ import annotations

import logging
import os
import re
import sys
import unicodedata
from dataclasses import dataclass, field
from pathlib import Path

VERSION = "1.0"
log = logging.getLogger("guard.ar")


def _env_flag(name: str, default: bool = True) -> bool:
    raw = os.getenv(name)
    if raw is None or not raw.strip():
        return default
    return raw.strip().lower() not in ("0", "false", "no", "off", "нет")


def enabled() -> bool:
    return _env_flag("GUARD_AR", True)


# ───────────────────────────── нормализация ─────────────────────────────
AR = "\u0621-\u064A"                      # арабские буквы после нормализации
_ARL = re.compile("[\u0621-\u064A\u066E-\u06D3\u06FA-\u06FF\u0750-\u077F]")
_SRC: dict = {}


def _reg(src: str, dst: str) -> None:
    for ch in src:
        _SRC[ord(ch)] = dst


_reg("أإآٱٲٳ", "ا")                        # все алефы → ا
_reg("ىیېۍێےئؠٸ", "ي")                    # ى ی ئ … → ي
_reg("ؤۆۇۈۉۊۏ", "و")
_reg("ةہھۃەۀۂۿ", "ه")                     # та-марбута и «ха» разных письменностей → ه
_reg("کڪګڬڭڮݢݣݤچ", "ك")                  # ک ڭ … и иракское «چ» (چلب = كلب) → ك
_reg("ڤڥڦڡڢڣ", "ف")
_reg("ڨڧ", "ق")
_reg("پڀٻݐݑ", "ب")
_reg("ٹٺټٿ", "ت")
_reg("ڈڊڌڍڎڏڐ", "د")
_reg("ڑڕږڙ", "ر")
_reg("ژ", "ز")
_reg("ڠ", "غ")
_reg("ڱںڻڼڽ", "ن")
_reg("ڵڶڷڸ", "ل")
_reg("،٬", ",")
_reg("؛", ";")
_reg("؟", "?")
_reg("٪", "%")
_reg("٫", ".")
_reg("«»“”„", '"')
_reg("‘’‚", "'")
_GAF = "گڳڰڲڴ"                            # «گ»: в Ираке/Заливе = ق (گلب), в персидском = ك


def _base_map(gaf: str) -> dict:
    m = {k: ord(v) for k, v in _SRC.items()}
    for ch in _GAF:
        m[ord(ch)] = ord(gaf)
    return m


def _table(gaf: str):
    class _T(dict):
        def __missing__(self, cp: int):
            ch = chr(cp)
            cat = unicodedata.category(ch)
            if cp == 0x640:                                    # татвиль «ـ»
                val = None
            elif cat in ("Mn", "Me", "Cf") or (cat == "Cc" and ch not in "\n\t"):
                val = None                                     # огласовки, невидимые, bidi-метки
            elif cat == "Nd":
                d = unicodedata.decimal(ch, None)              # ٠-٩ ۰-۹ → 0-9
                val = ord(str(d)) if d is not None else cp
            else:
                val = cp
            self[cp] = val
            return val
    return _T(_base_map(gaf))


_T_Q, _T_K = _table("ق"), _table("ك")


def ar_fold(text: str, gaf: str = "q") -> str:
    """Приводит арабский текст к «каноническому» виду: без огласовок/татвиля/невидимых, единые буквы, цифры 0-9, нижний регистр."""
    t = _T_Q if gaf == "q" else _T_K
    if len(t) > 60000:
        t.clear()
        t.update(_base_map(gaf))
    return unicodedata.normalize("NFKD", text).translate(t).lower()


def collapse(w: str) -> str:
    return re.sub(r"(.)\1+", r"\1", w)


def arabic_count(s: str) -> int:
    return len(_ARL.findall(s))


# «точечный» остов письма: ب ت ث ن ي → ب, ج ح خ → ح … (против подмены точек: كلب → كلت)
_RASM = str.maketrans({**{c: "ب" for c in "تثني"}, **{c: "ح" for c in "جخ"}, "ذ": "د", "ز": "ر", "ش": "س",
                       "ض": "ص", "ظ": "ط", "غ": "ع", "ق": "ف"})

# цифровой «лит»: 3يب → عيب (Ирак/Залив/Левант/Магриб)
LEET_AR = {"2": "ا", "3": "ع", "4": "غ", "5": "خ", "6": "ط", "7": "ح", "8": "ق", "9": "ص", "0": "و", "@": "ا", "$": "س"}

_TOK = re.compile("[" + AR + "]+")
_LEETTOK = re.compile("[" + AR + "0-9@$]{3,24}")
_MASK = re.compile("[" + AR + "]+(?:[*_#@%^~.\\-·]{1,2}[" + AR + "]+){1,2}")
_SEPJ = re.compile("(?<![" + AR + "])[" + AR + "](?:[ \\t]*[.\\-_*#@^~·,'\"|/\\\\+][ \\t]*[" + AR + "]){2,}(?![" + AR + "])")
_SYM = re.compile("(?<=[" + AR + "])(?:[^\\w\\s]|_){1,3}(?=[" + AR + "])")      # символы/эмодзи ВНУТРИ слова: قحـ✨ـبة
_FILL = tuple("ابتثجحخدذرزسشصضطظعغفقكلمنهوي")

# ───────────────────────────── словарный матчер ─────────────────────────────
_PRE_FULL = "(?:يا)?[وف]?[بلكس]?(?:ال)?"        # приставки: يا / و ف / ب ل ك س / ال (в схлопнутом виде «لل» = «ل»)
_PRE_LITE = "(?:يا)?و?(?:ال)?"                  # для коротких корней: без ب/ل/ك/س (иначе كزب «ложь» = ك+زب)
_PRON = "(?:ها|هم|هن|هما|كم|كن|كما|ني|نا|ك|ه|ي)?"
_NUM = "(?:ات|ين|ون|ان|ه|ا)?"


def _compile_group(E, P, S, T, pre):
    parts = []
    if E:
        parts.append("(?:" + "|".join(E) + ")")
    if P:
        parts.append("(?:" + "|".join(P) + ")" + _PRON)
    if S:
        parts.append("(?:" + "|".join(S) + ")" + _NUM + _PRON)
    if T:
        parts.append("(?:" + "|".join(T) + ")[" + AR + "]{0,5}")
    if not parts:
        return None
    return re.compile("^" + pre + "(?:" + "|".join(parts) + ")$")


class _Core:
    """Один набор слов одного уровня. Запись: «=слово» точно · «слово» + местоимения · «+слово» + число/род · «слово*» основа."""

    def __init__(self, entries):
        short = {"E": [], "P": [], "S": [], "T": []}
        long_ = {"E": [], "P": [], "S": [], "T": []}
        rasm_roots = []
        for ent in entries:
            mode = "P"
            if ent.startswith("="):
                mode, ent = "E", ent[1:]
            elif ent.startswith("+"):
                mode, ent = "S", ent[1:]
            elif ent.endswith("*"):
                mode, ent = "T", ent[:-1]
            w = collapse(ar_fold(ent).replace("_", ""))
            if not w:
                continue
            (short if len(w) <= 3 and mode != "T" else long_)[mode].append(re.escape(w))
            if mode == "T" and len(w) >= 5:
                rasm_roots.append(re.escape(collapse(w.translate(_RASM))))
        for g in (short, long_):
            for k in g:
                g[k] = sorted(set(g[k]), key=len, reverse=True)
        self.rx = [r for r in (_compile_group(short["E"], short["P"], short["S"], short["T"], _PRE_LITE),
                               _compile_group(long_["E"], long_["P"], long_["S"], long_["T"], _PRE_FULL)) if r]
        rr = sorted(set(rasm_roots), key=len, reverse=True)
        self.rasm = (re.compile("^" + _PRE_FULL.translate(_RASM) + "(?:" + "|".join(rr) + ")[" + AR + "]{0,4}$")
                     if rr else None)

    def match(self, tok: str) -> str:
        for rx in self.rx:
            if rx.match(tok):
                return "w"
        if self.rasm and len(tok) >= 5 and self.rasm.match(collapse(tok.translate(_RASM))):
            return "r"
        return ""


class ArLex:
    """Словарь с уровнями. «~слово» — мягкий (глушится в религиозном/новостном контексте), «слово@L» — только в диалекте L
    (G залив · E египет · L левант · I ирак · M магриб)."""

    def __init__(self, spec, allow=()):
        ents = spec.split() if isinstance(spec, str) else list(spec)
        buckets: dict = {}
        for e in ents:
            tier, gate = "hard", ""
            if e.startswith("~"):
                tier, e = "soft", e[1:]
            if "@" in e:
                e, gate = e.rsplit("@", 1)
            if e:
                buckets.setdefault((tier, gate), []).append(e)
        order = sorted(buckets, key=lambda k: (k[0] != "hard", k[1] != ""))
        self.cores = [(t, g, _Core(buckets[(t, g)])) for t, g in order]
        al = []
        for a in allow:
            w = collapse(ar_fold(a.lstrip("=").rstrip("*")).replace(" ", ""))
            if w:
                al.append(re.escape(w))
        self.allow = (re.compile("^" + _PRE_FULL + "(?:" + "|".join(sorted(set(al), key=len, reverse=True)) + ")" + _PRON + "$")
                      if al else None)
        self._memo: dict = {}

    def hit(self, tok: str):
        """() — нет; (tier, how, gate): tier hard/soft, how w/r (r — найдено по «остову» букв), gate — требуемый диалект."""
        r = self._memo.get(tok)
        if r is None:
            r = ()
            if tok and not (self.allow and self.allow.match(tok)):
                for tier, gate, core in self.cores:
                    how = core.match(tok)
                    if how:
                        r = (tier, how, gate)
                        break
            if len(self._memo) > 30000:
                self._memo.clear()
            self._memo[tok] = r
        return r


# ───────────────────────────── DSL для регулярок ─────────────────────────────
_B0 = "(?<![" + AR + "0-9a-z])"
_B1 = "(?![" + AR + "0-9a-z])"
_PRE = "(?:[وف]?[بلكس]?(?:ال)?)"
_SUF = "(?:ات|ين|ون|ان|ه|ا|يه)?(?:ها|هم|هن|هما|ك|كم|كن|كما|ه|ي|ني|نا)?"
_GAPCH = r"[^.!?\n]"


def G(n: int) -> str:
    return _GAPCH + "{0," + str(n) + "}?"


def _units(phrase: str) -> tuple:
    out = []
    for tok in ar_fold(phrase).split():
        if out:
            out.append(r"\s+")
        for c in tok:
            out.append(re.escape(c) + "+" if "\u0621" <= c <= "\u064A" else re.escape(c))
    return tuple(out)


def _trie_rx(words) -> str:
    root: dict = {}
    for w in words:
        n = root
        for u in _units(w):
            n = n.setdefault(u, {})
        n[""] = True

    def emit(n) -> str:
        alts = [k + emit(v) for k, v in sorted(n.items()) if k != ""]
        if not alts:
            return ""
        body = alts[0] if len(alts) == 1 else "(?:" + "|".join(alts) + ")"
        return "(?:" + body + ")?" if "" in n else body
    return emit(root)


def W(words: str, pre: bool = True, suf: bool = True) -> str:
    """Слова/фразы через «|» → регулярка с растяжками букв, приставками и суффиксами. Пишите в любой орфографии: приведу сам."""
    alts = [a.strip() for a in words.split("|") if a.strip()]
    return _B0 + (_PRE if pre else "") + "(?:" + _trie_rx(alts) + ")" + (_SUF if suf else "") + _B1


def PAIR(a: str, b: str, gap: int = 40) -> str:
    return "(?:" + W(a) + G(gap) + W(b, pre=False) + "|" + W(b) + G(gap) + W(a, pre=False) + ")"


def after(a: str, b: str, gap: int = 40) -> str:
    return W(a) + G(gap) + W(b, pre=False)


def rx(p: str):
    return re.compile(p)


# ═════════════════════════════ СЛОВАРИ ═════════════════════════════
# Орфография любая: всё приводится к единому виду. Уровни: без метки — «жёсткий» (ловится всегда),
# «~» — «мягкий» (двусмысленное слово: глушится в религиозном/новостном/учебном контексте),
# «@L» — только если сообщение звучит в этом диалекте (G залив · E египет · L левант · I ирак · M магриб).
# Я сознательно НЕ кладу сюда мягкие бытовые слова (كلب، حمار، غبي …) — так же, как guard не ловит «дурак»:
# ловим настоящую брань, оскорбления «через мать/сестру/честь/веру» и ярлыки ненависти.

PROF_SPEC = """
كس كسم كسمك كسمه كسامك كسختك زب طيز نيك نيكو نيكوا ناك ناكوا
ينيك* تنيك* انيك* هنيك* منيك*
شرموط* شرمط* شراميط* قحب* قحاب* كحب* كحاب* عاهر* ديوث* دياث* معرص* منيوك* متناك*
فشخ* فاشخ* مفشخ* بعبص* بعبوص* مومس* +بغايا
=عرص =خول =خولات =خرا
عير@L ايري@L زامل@M
"""
# слова «в положительном смысле» у молодёжи: فشخ = «круто» (египет). В похвале не считаем матом.
SLANG_VULGAR = ("فشخ", "فاشخ", "مفشخ")
PRAISE = r"(?:روع|تحف|جامد|حلو|عظيم|ممتاز|خرافي|اسطور|ابداع|مبدع|برافو|بطل|جميل|يجنن|فنان|كوول|كول)"

HATE_SPEC = """
لوطي* لواطي* مخنث* =خول زنجي* =زنوج
"""
HATE_SECT_SPEC = """
~رافضي* ~روافض ~مجوس* ~صفوي* ~صفويين ~نواصب ~ناصبي* ~نصيري*
"""

ADULT_SPEC = """
سكس سكسي* بورنو* =بورن بورنوغراف* ممحون*
~اباحي* ~بزاز ~عاريات ~عاري ~عاريه ~عريان* ~عراه
"""

MINOR_SPEC = """
طفل* اطفال* صغيره صغير* صغار صغيرات قاصر* مراهق* تلميذ* ابتدائي* اعدادي* يافع* رضيع*
"""

# тексты-исключения (вырезаются до проверки слов)
EXC_RX = re.compile(ar_fold(
    r"سكس\s*(?:باك|سيجما|بكس|ستين)|سيكس\s*باك|نيك\s*(?:نيم|نايم|نيمز)|نيكنيم|عار(?:ي|يه)?\s*(?:عن|من)\s*(?:ال)?(?:صحه|صحة)"
    r"|نيك\s*(?:جوناس|كيرجيوس|ميناج|فيوري|كانون|جاغر|كارتر|روبنسون|ولد)"))

# ── фразы-брань (всегда «жёсткие»), любые растяжки/приставки ──
_FAM = "امك|امكم|امه|امها|امي|امهم|اخت|اختك|اخته|اختكم|ابو|ابوك|دين|دينك|رب|ربك|عرض|عرضك|شرف|شرفك|اهل|اهلك|عمك|خالتك|عمتك|جدك|جدتك"
PH_PROF = [
    (rx(_B0 + _PRE + r"ك+س+\s+(?:" + _trie_rx(_FAM.split("|")) + r")" + _B1), "брань «через мать/сестру/веру»"),
    (rx(_B0 + r"يلعن+\s+(?:" + _trie_rx("ابو|ابوك|ابوه|ابوها|ابوكم|ابوهم|دين|دينك|دينه|دينكم|ام|امك|امه|امكم|ربك|رب|شرف|شرفك|عرض|عرضك|اهل|اهلك|روح|روحك|روحه".split("|")) + r")" + _B1), "проклятие отца/матери/веры"),
    (rx(_B0 + r"(?:ابن|ولد|بنت|اولاد|ولاد|ابناء)\s+(?:ال)?(?:كلب\w*|كلاب|زنا|زانيه|شرموط\w*|قحب\w*|كحب\w*|عاهر\w*|متناك\w*|منيوك\w*|ستين\s+كلب)" + _B1), "оскорбление родителей («сын собаки/шлюхи»)"),
    (rx(_B0 + r"(?:اخو|اخ|اخت|ام|اب|ابو)\s+(?:ال)?(?:شرموط\w*|قحب\w*|عاهر\w*|كحب\w*|متناك\w*)" + _B1), "оскорбление родни"),
    (rx(_B0 + r"ن+ي+ك+\s*(?:مك|امك|ام|امه|امو|امكم|ربك|رب|دين|دينك|دينمك|ختك|اختك|امها|ابوك|عرضك|شرفك)" + _B1), "брань на «ник…»"),
]

# ── фразы-ненависть ──
_GRP = (r"(?:ال)?(?:يهود\w*|نصارى|نصراني\w*|مسيحي\w*|شيع\w*|رواف\w*|سن[هة]|عرب|اكراد|كرد\w*|فلسطين\w*|سوري\w*|مصري\w*|سوداني\w*|يمني\w*"
        r"|اجانب|لاجئ\w*|مهاجر\w*|هنود|هندوس|افارق\w*|سود|مثلي\w*|شواذ|علويين|دروز|يزيدي\w*|اقباط|قبط|بدو|فلاحين|عمال)")
_GRP_STRICT = (r"(?:ال)?(?:يهود\w*|نصارى|مسيحي\w*|شيع\w*|رواف\w*|سن[هة]|اكراد|كرد\w*|علويين|دروز|يزيدي\w*|اقباط|قبط|مثلي\w*|شواذ"
               r"|لاجئ\w*|اجانب|افارق\w*|سود)")
_DEHUM = r"(?:نجس\w*|اوساخ|قمامه|حثاله|حيوانات|خنازير|قرود|قرده|كلاب|جرذان|فئران|صراصير|سرطان|وباء|طاعون|حشرات|دود)"
PH_HATE = [
    (rx(_B0 + r"(?:ابناء|احفاد|يا|ي)?\s*(?:ال)?قرد+ه?\s+(?:و?(?:ال)?)\s*خنازير" + _B1), "«обезьяны и свиньи» — ярлык против верующих"),
    (rx(_B0 + r"كلاب\s+" + _GRP + _B1), "дегуманизация: «собаки + группа»"),
    (rx(_B0 + _GRP + r"\s+" + _DEHUM + _B1), "дегуманизация группы"),
    (rx(_B0 + r"(?:اقتلوا|اذبحوا|ابيدوا|ابيدو|حرقوا|احرقوا|اطردوا|اقتل|اذبح|فجروا|ذبح|قتل|ابادة|ابادة|ابيد|تصفية|تصفيه)\s+" + _GRP_STRICT + _B1), "призыв к насилию против группы"),
    (rx(_B0 + r"الموت\s+(?:لل|ل)(?:يهود\w*|شيع\w*|رواف\w*|اكراد|سنه|اقباط|مثلي\w*|مسيحي\w*|نصارى|شواذ)" + _B1), "«смерть + группа»"),
    (rx(_B0 + r"يا\s+(?:ال)?(?:شاذ|شواذ|لوطي|مخنث|زنجي|عبد\s+اسود)" + _B1), "ярлык в обращении"),
    (rx(_B0 + r"(?:هيل|هايل|هيل\s+ال)\s*هتلر|تحيا\s+هتلر|عاش\s+هتلر|هتلر\s+(?:كان\s+)?(?:على\s+حق|فعل\s+الصواب)" + _B1), "восхваление Гитлера"),
    (rx(_B0 + r"(?:ال)?(?:محرقه|هولوكوست)\s+(?:كذبه|اكذوبه|مزيفه|مختلقه)|(?:كذبه|اكذوبه)\s+(?:ال)?(?:محرقه|هولوكوست)" + _B1), "отрицание Холокоста"),
    (rx(_B0 + r"عبيد\s+سود|عبد\s+اسود|عبيد\s+افريقيا" + _B1), "расовый ярлык"),
    (rx(_B0 + r"يا\s+(?:ال)?كافر" + _B1), "ярлык «неверный» в обращении (сектантский)"),
]
SECT_WHYS = ("«неверный»",)

# ── 18+ фразы ──
PH_ADULT = [
    rx(W("سكس محارم|نيك محارم|محارم سكس|افلام محارم|قصص محارم|محارم نيك|سكس سحاق|سحاق سكس|سحاقيات سكس|نيك سحاق|قصص جنسيه|قصص ممحونه|روايات جنسيه|مجلات اباحيه"
         "|محتوى للكبار|قنوات للكبار|قروبات للكبار|افلام للكبار|فيديوهات للكبار|صور للكبار|مقاطع للكبار|فيديوهات ساخنه|صور ساخنه|مقاطع ساخنه|قنوات ساخنه|اونلي فانز|اونليفانز"
         "|ديلدو|دلدو|قضيب صناعي|قضيب اصطناعي|العاب جنسيه|ادوات جنسيه")),
    rx(PAIR("صور|فيديوهات|فيديو|مقاطع|افلام|فلم|قنوات|قناه|قروبات|كروبات|جروبات|روابط|رابط|قصص|روايات|محتوى|بوت|بوتات|مواقع|موقع",
            "سكس|نيك|بورنو|اباحيه|اباحي|اباحيات|للكبار|محارم|ممحونات|ممحونه|عاريات|سكسي|سكسيه", 8)),
]
# «возраст до 18» рядом с 18+ → детская тема
AGE_MINOR = re.compile(r"(?<!\d)(?:بعمر|عمر(?:ها|ه|ي)?|عمري|سنه|سن)\s*(?:ال)?(?:[7-9]|1[0-7])(?!\d)\s*(?:سنه|سنوات|سنين|عام|سنة)?"
                       r"|(?<!\d)(?:[7-9]|1[0-7])\s*(?:سنه|سنوات|سنين|عام|اعوام)(?![\d])")

# ═════════════════════════════ ДИАЛЕКТНЫЙ РАДАР ═════════════════════════════
# Маркерные слова (в нормализованном виде). Нужны, чтобы (1) слова «@L/@M» ловились только в «своём» диалекте,
# (2) в причине показывать, на каком диалекте писал человек.
DIALECT_MARK = {
    "G": "شلونك شخبارك وش ابغى ابغا ابي ودي زين هلا حياك وايد مره الحين دحين شفيك يبه يمه ياخوي خوي ياعيال عيال اللي شحالك شخبار ابشر طيب بعدين ويش",
    "E": "ازيك ايه ازاي عايز عايزه دلوقتي كده مش اوي ده دي دا ليه فين بقى معلش يابني ياباشا يسطا ياعم احنا انتو ايوه لسه برضه خالص قوي",
    "L": "شو كيفك هلق كتير بدي بدك ليش لسا هيك هاد هاي زلمه زلمة شب مشان اشي منيح هلأ كيفكن بشو",
    "I": "شلون شنو اكو ماكو هسه گلت چنت هواي يمعود خوش شكد شبيك يابه اريد اشكد",
    "M": "واش بزاف ديال دابا كيفاش علاش غادي هادشي مزيان خويا ساحبي لاباس بصح برك توا باهي نوض فين_ كاين مكاين",
}
_DM = {d: {collapse(ar_fold(w)) for w in v.split() if not w.endswith("_")} for d, v in DIALECT_MARK.items()}
DIALECT_RU = {"G": "залив", "E": "египетский", "L": "левантийский", "I": "иракский", "M": "магрибский", "": "литературный/неясно"}


def dialect_of(tokens) -> tuple:
    """(код, очки). Нужно ≥2 маркеров и перевес над вторым местом; иначе ('', 0)."""
    toks = set(tokens)
    sc = sorted(((len(toks & m), d) for d, m in _DM.items()), reverse=True)
    if sc and sc[0][0] >= 2 and sc[0][0] > (sc[1][0] if len(sc) > 1 else 0):
        return sc[0][1], sc[0][0]
    return "", sc[0][0] if sc else 0


# ═════════════════════════════ КОНТЕКСТНЫЙ ЩИТ ═════════════════════════════
# Религиозный/новостной/учебный контекст: «мягкие» слова внутри него не считаются нарушением. «Жёсткая» брань — всегда.
_SHIELD_OPEN = re.compile(ar_fold(
    r"قال\s+(?:الله\s+)?تعالى|قال\s+رسول\s+الله|قال\s+النبي|صلى\s+الله\s+عليه\s+و?سلم|رواه\s+(?:ال)?(?:بخاري|مسلم|ابو\s+داود|ترمذي|احمد)"
    r"|في\s+(?:ال)?(?:قران|حديث|تفسير|سيره|فقه|تاريخ)|ما\s+حكم|حكم\s+(?:ال)?\w+\s+في\s+الاسلام|فتوى|الشيخ\s+\w+\s+يقول|سوره\s+\w+"
    r"|معنى\s+كلمه|ما\s+معنى|تعني\s+كلمه|مصطلح|يسمى|تعريف|المقصود\s+ب|في\s+اللغه|في\s+القاموس|في\s+علم|بحث\s+علمي|دراسه\s+(?:علميه|حديثه)"
    r"|خبر\s+عاجل|نقلا\s+عن|وكاله\s+\w+|صرح|اعلنت|افادت|وزاره|المحكمه|القضاء|منظمه|الامم\s+المتحده|تقرير|حقوق\s+الانسان|مكافحه|محاربه|ضحايا|جريمه|قانون"))
_QURAN = re.compile("[\u06D6-\u06DC\u06DF-\u06E8\ufd3e\ufd3f]|﴿|﴾")
_SHIELD_SPAN = 220


def shield_spans(raw: str, F: str) -> list:
    """Диапазоны (в F), где «мягкие» слова глушатся: после маркера и до конца предложения, но не дальше _SHIELD_SPAN знаков."""
    out = []
    for m in _SHIELD_OPEN.finditer(F):
        end = len(F)
        for stop in (".", "!", "?", "\n"):
            p = F.find(stop, m.end())
            if p != -1:
                end = min(end, p)
        out.append((m.start(), min(end, m.end() + _SHIELD_SPAN)))
    return out


# ═════════════════════════════ АРАБИЗИ (латиница) ═════════════════════════════
_V = "[aeiouwy']{0,3}"
_AZC = {"S": "(?:sh|ch|s)", "X": "(?:kh|5|x)", "G": "(?:gh|3')", "H": "[h7]", "Q": "(?:q|9|k|g|8)", "T": "(?:t|6)", "D": "(?:d|dh)",
        "B": "[bp]", "F": "[fv]", "K": "(?:k|c)"}


def az(spec: str, tail: str = "[aeiouyh]{0,3}") -> str:
    parts = []
    for t in spec.split():
        parts.append(_AZC.get(t, re.escape(t.lower())))
    return r"(?<![a-z0-9])(?=[a-z0-9']{4,})" + _V.join(parts) + tail + r"(?![a-z0-9])"


_AZ_FAM = (r"(?:" + az("K L B", "(?:a|e|eh)?") + "|" + az("S R M T") + "|" + az("Q H B") + "|" + az("3 H R") + "|" + az("M T N K") + ")")
AZ_PROF = [
    (rx(az("S R M T")), "арабизи: sharmouta"),
    (rx(az("3 R S", "[aeiouyh]{0,2}")), "арабизи: 3ars"),
    (rx(az("3 H R")), "арабизи: 3ahra"),
    (rx(az("Q H B")), "арабизи: 9a7ba/qahba"),
    (rx(az("M T N K")), "арабизи: metnaka"),
    (rx(az("X W L", "[aeiouyh]{0,2}").replace("(?:kh|5|x)", "(?:kh|5)")), "арабизи: khawal"),
    (rx(r"(?<![a-z0-9])many[ou]{1,2}k[a]?(?![a-z0-9])"), "арабизи: manyouk"),
    (rx(r"(?<![a-z0-9])z[eo]b{1,2}i(?![a-z0-9])"), "арабизи: zebi"),
    (rx(r"(?<![a-z0-9])(?:ya|y)\s+(?:el\s+|al\s+)?(?:k|c)[ae]l[ae]?b(?:a|e|eh)?(?![a-z0-9i])"), "арабизи: ya kalb"),
    (rx(r"(?<![a-z0-9])(?:ib[nm]|ibin|wl[ae]d|walad|weld|ouled|bint)\s*(?:el|al|il|l)?\s*" + _AZ_FAM), "арабизи: «сын …»"),
    (rx(r"(?<![a-z0-9])k[oue]?s{1,2}\s*[oeu]m{1,2}[ae]?[kq](?![a-z0-9])"), "арабизи: kos omak"),
    (rx(r"(?<![a-z0-9])k[oue]?s{1,2}\s*[oeu](?:kh|5)[ae]?t[ae]?[kq](?![a-z0-9])"), "арабизи: kos okhtak"),
    (rx(r"(?<![a-z0-9])n[iy]k\s*(?:m[oua]k|[oue]m{1,2}[ae]?k|[oeu]mm?ek|tmek|mak|mok|rabak|rabbak|din\w*)(?![a-z0-9])"), "арабизи: nik mok"),
    (rx(r"(?<![a-z0-9])(?:yel3an|yil3an|yl3an|yel3en)\s+(?:abo|abook|abuk|din\w*|omak|ommak)(?![a-z0-9])"), "арабизи: проклятие"),
]
AZ_HATE = [
    (rx(r"(?<![a-z0-9])(?:louti|loutiy|louty|luti)(?![a-z0-9])"), "арабизи: ярлык"),
    (rx(r"(?<![a-z0-9])(?:zan[gj]i|zenj\w*)(?![a-z0-9])"), "арабизи: расовый ярлык"),
]
AZ_ADULT = [
    (rx(r"(?<![a-z0-9])(?:sks|sex)\s*(?:3rby|3arabi|arabi|masri|khaleeji|khalegy|3arab|msry|ksa)(?![a-z0-9])"), "арабизи: 18+"),
    (rx(r"(?<![a-z0-9])(?:xnxx|pornhub|xhamster|redtube|youporn|brazzers|sexmex|arabsex)(?![a-z0-9])"), "сайт 18+"),
]
# арабизи-спам (вес, текст): мало, но самое частое
AZ_SPAM = [
    ("ar_az_earn", "job", 2.2, rx(r"(?<![a-z0-9])(?:arb[a7]h?|rb[a7]|kasb|ksb)\s*(?:yawm\w*|youm\w*|yom\w*|mdmon\w*|madmoon\w*|madmun\w*|mdmun\w*)(?![a-z0-9])"), "арабизи: «прибыль в день/гарантия»"),
    ("ar_az_nocap", "job", 2.0, rx(r"(?<![a-z0-9])(?:bdo?u?n|bidoun|bedoun)\s+r[a7]?[a2']?s\s*(?:el\s*)?mal(?![a-z0-9])"), "арабизи: «без вложений»"),
    ("ar_az_dm", "cta", 2.0, rx(r"(?<![a-z0-9])(?:kalimni|kalemni|raslni|rasilni|rasel(?:ni)?|ktbli|ktoblna|ktoub\s*li)\s*(?:3al\s*|3la\s*|fi\s*|f\s*)?(?:khas|5as|private|whats(?:app)?|wtsp|tele(?:gram)?)(?![a-z0-9])"), "арабизи: «пиши в личку»"),
    ("ar_az_dm2", "cta", 1.2, rx(r"(?<![a-z0-9])(?:3al|3la|fi|f)\s*(?:el\s*)?(?:5as|khas|khass)(?![a-z0-9])"), "арабизи: «в личку»"),
]

# ═════════════════════════════ КИРИЛЛИЧЕСКАЯ ТРАНСЛИТЕРАЦИЯ ═════════════════════════════
# Русскоязычные арабы/кавказцы пишут арабскую брань кириллицей. Только самое однозначное (чтобы не плодить ложные).
CYR_PROF = [
    (rx(r"(?<![а-я])ш[аеи]рм[ауо]+т[аыеу]?(?![а-я])|(?<![а-я])шарам[иы]т(?![а-я])"), "кириллицей: «шармута»"),
    (rx(r"(?<![а-я])к[ауо]х?б[аеи]?(?![а-я])(?=.{0,20}(?:ибн|йа|я )|$)"), "кириллицей: «кахба»"),
    (rx(r"(?<![а-я])(?:кус|кос|кюс)\s*(?:умак|уммак|омак|ухтак|охтак|умм?ак)(?![а-я])"), "кириллицей: «кус умак»"),
    (rx(r"(?<![а-я])(?:ибн|ибен|вальд)\s*(?:эль|аль|ал|эл)?[\s\-]*(?:кальб|кяльб|шармута|кахба|ахра)(?![а-я])"), "кириллицей: «ибн аль-кальб»"),
    (rx(r"(?<![а-я])(?:йа|я|йя)\s+(?:кальб|кяльб|хмар|химар|ибн\s+кальб)(?![а-я])"), "кириллицей: «йа кальб»"),
    (rx(r"(?<![а-я])мень?ю?к(?:а|и)?(?![а-я])(?=.{0,20}(?:ибн|йа))"), "кириллицей: «манюк»"),
]


# ═════════════════════════════ СКАНЕР СЛОВ ═════════════════════════════
_custom = {"prof": [], "hate": [], "adult": [], "minor": [], "allow": [], "spam": []}
PROF = HATEL = ADULT = MINOR = None


def build() -> None:
    """Собирает словари (вызывается при импорте и после reload())."""
    global PROF, HATEL, ADULT, MINOR
    allow = _custom["allow"]
    PROF = ArLex(PROF_SPEC + " " + " ".join(_custom["prof"]), allow)
    HATEL = ArLex(HATE_SPEC + " " + HATE_SECT_SPEC + " " + " ".join(_custom["hate"]), allow)
    ADULT = ArLex(ADULT_SPEC + " " + " ".join(_custom["adult"]), allow)
    MINOR = ArLex(MINOR_SPEC + " " + " ".join(_custom["minor"]), allow)


build()
_SECT_TOK = None


def _sect_on() -> bool:
    return _env_flag("GUARD_AR_SECT", True)


def _in_spans(pos: int, spans) -> bool:
    return any(a <= pos < b for a, b in spans)


def _praise_near(F: str, a: int, b: int) -> bool:
    return bool(re.search(PRAISE, F[max(0, a - 30):b + 30]))


@dataclass
class Found:
    prof: list = field(default_factory=list)
    hate: list = field(default_factory=list)
    adult: list = field(default_factory=list)
    minor: bool = False
    why: list = field(default_factory=list)       # (категория, пояснение)
    shielded: int = 0                              # сколько «мягких» слов заглушил контекстный щит
    dialect: str = ""

    def as_dict(self) -> dict:
        return {"prof": list(dict.fromkeys(self.prof)), "hate": list(dict.fromkeys(self.hate)),
                "adult": list(dict.fromkeys(self.adult)), "minor": self.minor}


def _extra_views(F: str, toks: list, raw: str) -> list:
    """Обходы без позиций: буквы через пробел/точку, цифровой лит, маски со звёздочкой, «گ» как ك."""
    out = []
    run: list = []
    for t in toks + [""]:
        if len(t) == 1:
            run.append(t)
            continue
        if len(run) >= 3:
            out.append(("spaced", collapse("".join(run))))
        run = []
    for m in _SEPJ.finditer(F):
        j = "".join(ch for ch in m.group(0) if "\u0621" <= ch <= "\u064A")
        if len(j) >= 3:
            out.append(("sep", collapse(j)))
    for m in _LEETTOK.finditer(F):
        t = m.group(0)
        letters = sum(1 for c in t if "\u0621" <= c <= "\u064A")
        extra = len(t) - letters
        if letters >= 2 and 1 <= extra <= 3:
            out.append(("leet", collapse("".join(LEET_AR.get(c, c) for c in t))))
    for m in _MASK.finditer(F):
        parts = re.split("[*_#@%^~.\\-·]+", m.group(0))
        joined = "".join(parts)
        if not 3 <= len(joined) <= 14:
            continue
        out.append(("mask", collapse(joined)))
        if len(parts) == 2:
            for f in _FILL:
                out.append(("mask", collapse(parts[0] + f + parts[1])))
    if "گ" in raw or "ڭ" in raw:
        F2 = ar_fold(raw, "k")
        out += [("gaf", collapse(t)) for t in _TOK.findall(F2)]
    return out[:400]


def lex_scan(raw: str, F: str | None = None, shield: bool = True, contactish: bool = False) -> Found:
    """Мат / ненависть / 18+ / дети в арабском тексте. Возвращает Found."""
    fd = Found()
    raw = raw[:3000]
    F = F if F is not None else ar_fold(raw)
    F = EXC_RX.sub(lambda m: " " * len(m.group(0)), F)
    metas = [(m.start(), m.end(), m.group(0)) for m in _TOK.finditer(F)][:600]
    toks = [collapse(t) for _, _, t in metas]
    dial, _ = dialect_of(toks)
    fd.dialect = dial
    spans = shield_spans(raw, F) if shield else []
    sect_on = _sect_on()
    lexes = (("prof", PROF), ("hate", HATEL), ("adult", ADULT))
    soft_buf: dict = {"prof": [], "hate": [], "adult": []}

    def take(cat, shown, tier, how, gate, pos, orig_tok, evasion=False):
        if gate and gate != dial:
            return
        if tier == "soft":
            if evasion:
                return
            if pos is not None and _in_spans(pos, spans):
                fd.shielded += 1
                return
        if cat == "hate" and tier == "soft" and not sect_on:
            return
        if cat == "prof" and any(orig_tok.startswith(collapse(ar_fold(p))) or collapse(orig_tok).lstrip("وفالب").startswith(collapse(ar_fold(p)))
                                 for p in SLANG_VULGAR):
            if pos is not None and (_praise_near(F, pos, pos + len(orig_tok)) or dial == "E" and not re.search(r"\bيا\s*\w+\s*$", F[:pos])):
                return
        if tier == "soft":
            soft_buf[cat].append((shown, pos))                  # «мягкое» слово — улика слабая, решаем ниже
            return
        getattr(fd, cat).append(shown + ("" if how == "w" else "~"))
        if how == "r":
            fd.why.append((cat, "слово с подменой точек букв"))

    seen = set()
    for (a, b, orig), tok in zip(metas, toks):
        if tok in seen:
            continue
        seen.add(tok)
        for cat, lx in lexes:
            r = lx.hit(tok)
            if r:
                take(cat, orig, r[0], r[1], r[2], a, orig)
        if MINOR.hit(tok):
            fd.minor = True
    F3 = _SYM.sub("", F)
    views = _extra_views(F, toks, raw)
    if F3 != F:
        views += [("sym", collapse(t)) for t in _TOK.findall(F3)][:300]
    mask_done = False
    for kind, tok in views:
        if tok in seen or len(tok) < 3:
            continue
        seen.add(tok)
        if kind == "mask" and mask_done:
            continue
        for cat, lx in lexes:
            r = lx.hit(tok)
            if r and r[0] == "hard" and (len(tok) >= 4 or kind in ("spaced", "sep", "leet")) and not (kind == "mask" and r[1] != "w"):
                take(cat, tok + "(" + kind + ")", "hard", r[1], r[2], None, tok, evasion=True)
                if kind == "mask":
                    mask_done = True
        if MINOR.hit(tok):
            fd.minor = True

    for cat, buf in soft_buf.items():
        # одно двусмысленное слово само по себе не нарушение. Считаем, если: уже есть «жёсткая» находка, слов ≥2,
        # есть контакт/ссылка, или слово направлено на человека («يا …», «انت …»).
        if not buf:
            continue
        distinct = {s for s, _ in buf}
        direct = any(p is not None and re.search(r"(?:يا|انت|انتي|انتم|ايها)\s*(?:ال)?\s*$", F[max(0, p - 14):p]) for _, p in buf)
        if getattr(fd, cat) or len(distinct) >= 2 or contactish or direct:
            getattr(fd, cat).extend(sorted(distinct))
    pviews = [F] if F3 == F else [F, F3]
    for p, why in PH_PROF:
        for V in pviews:
            m = p.search(V)
            if m:
                fd.prof.append(m.group(0)[:30]); fd.why.append(("prof", why))
                break
    for p, why in PH_HATE:
        for V in pviews:
            m = p.search(V)
            if not m:
                continue
            if V is F and (why.startswith("ярлык «неверный»") or why.startswith("ярлык в обращении")):
                if not sect_on and "сектант" in why:
                    break
                if _in_spans(m.start(), spans):
                    fd.shielded += 1
                    break
            fd.hate.append(m.group(0)[:30]); fd.why.append(("hate", why))
            break
    for p in PH_ADULT:
        for V in pviews:
            m = p.search(V)
            if m:
                fd.adult.append(m.group(0)[:30])
                break
    if AGE_MINOR.search(F):
        fd.minor = True

    if _env_flag("GUARD_AR_ARABIZI", True):
        low = re.sub(r"(.)\1{2,}", r"\1\1", raw.lower())
        if re.search(r"[a-z]", low) and len(low) >= 4:
            for lst, cat in ((AZ_PROF, fd.prof), (AZ_HATE, fd.hate), (AZ_ADULT, fd.adult)):
                for p, why in lst:
                    m = p.search(low)
                    if m:
                        cat.append(m.group(0)[:30]); fd.why.append(("az", why))
    cyr = re.sub(r"(.)\1{2,}", r"\1\1", raw.lower().replace("ё", "е"))
    if re.search(r"[а-я]{3}", cyr):
        for p, why in CYR_PROF:
            m = p.search(cyr)
            if m:
                fd.prof.append(m.group(0)[:30]); fd.why.append(("cyr", why))
    return fd


# ═════════════════════════════ СПАМ-ПРАВИЛА ═════════════════════════════
PITCH_GROUPS = {"job", "invest", "gamble", "sale", "adult_ad", "illegal", "promo"}
RULES: list = []
SEASONAL: set = set()


def _r(name, group, w, pattern, why, flag="", season=False):
    RULES.append((name, group, w, re.compile(pattern), why, flag))
    if season:
        SEASONAL.add(name)


_CONTACT = ("خاص|الخاص|واتس|واتساب|واتس اب|وتس|وتساب|تلجرام|تليجرام|تلغرام|تيليجرام|تيلجرام|سناب|سناب شات|ماسنجر|انستا|انستقرام|دايركت|بالخاص|للخاص|على الخاص|ع الخاص|في الخاص"
            "|البروفايل|بروفايلي|ملفي الشخصي|الرقم|رقمي|رقم الواتس|رقم الواتساب|هذا الرقم|الرقم التالي")

# ── заработок / работа ──
_r("ar_earn_pitch", "job", 2.5, after("ربح|ارباح|الربح|كسب|مكاسب|دخل|عائد|عوائد|اربح|تربح|اكسب|تكسب|ربحك|ربحي",
    "بدون راس مال|بدون رأس مال|بدون خبره|بدون استثمار|بدون ايداع|يوميا|في اليوم|كل يوم|باليوم|اسبوعيا|في الاسبوع|شهريا|في الشهر|من البيت|من المنزل|من الجوال|من الهاتف|بالجوال|اونلاين|اون لاين|عبر الانترنت|من الانترنت|عن بعد|في وقت فراغك|بوقت فراغك|بدون مجهود|بدون تعب|بدون مخاطره|بدون مخاطر", 60),
    "обещание лёгкого заработка")
_r("ar_earn_online", "job", 2.5, after("الربح|ربح|اربح|تربح|كسب|اكسب|تكسب|العمل|اعمل|تعمل|اشتغل|تشتغل|الدخل|دخل|مصدر دخل|ارباح",
    "من الانترنت|من النت|عبر الانترنت|عبر النت|اونلاين|اون لاين|من الجوال|بالجوال|من الهاتف|عبر الهاتف|من المنزل|من البيت|في المنزل|في البيت|من تلجرام|عبر تلجرام|من تيليجرام|عبر تيليجرام|من تلغرام|عبر تلغرام|بالتلجرام|بالتليجرام|من واتساب|عبر واتساب|من الموبايل|بالموبايل|وانت في بيتك|وانت بالبيت|وانت في المنزل", 25),
    "заработок в сети / с телефона")
_r("ar_earn_word", "job", 1.5, W("اربح|ارباح|تربح|اكسب|تكسب|اربحوا|اكسبوا|كسب المال|ربح المال|الثراء|تصبح مليونير|الاف الدولارات|الاف الريالات|الاف الدراهم"),
   "разговор о заработке")
_r("ar_extra_income", "job", 2.0, W("دخل اضافي|دخل ثانوي|دخل شهري ثابت|دخل ثابت|دخل يومي|مصدر دخل|مصدر رزق اضافي|راتب اضافي|زياده دخلك|تحسين دخلك|تحسين وضعك المادي|تحسين الوضع المادي|تحسين وضعك المالي|الاستقلال المالي|الحريه الماليه|الاستقلال المادي"),
   "«дополнительный доход / финансовая свобода»")
_r("ar_passive", "job", 2.0, W("دخل سلبي|دخل مستمر|دخل مدى الحياه|دخل دائم|دخل بدون مجهود|ارباح بدون مجهود"), "пассивный доход")
_r("ar_no_capital", "job", 2.0, W("بدون راس مال|بدون رأس مال|من غير راس مال|بدون رأسمال|بدون راسمال|راس مال صفر|بدون استثمار|بدون ايداع|بدون خبره|بدون خبره سابقه|بدون مجهود|بدون تعب|بدون مخاطره|بدون مخاطر"),
   "«без вложений / без опыта»")
_NUM = r"\d[\d.,]*"
_CUR = r"(?:دولار\w*|\$|usd|usdt|ريال\w*|درهم|دراهم|دينار|دنانير|جنيه|جنيها|يورو|الف|k)"
_PER = r"(?:في|ب|\/|كل|ل)?\s*(?:ال)?(?:يوم|يوميا|اسبوع|اسبوعيا|شهر|شهريا|ساعه)"
_NUMPAT = r"(?<![\d.,])" + _NUM + r"\s*(?:-|–|الى|الي|ل)?\s*(?:" + _NUM + r"\s*)?" + _CUR + r"\s*" + _PER + _B1
_r("ar_income_num", "job", 1.5, _NUMPAT, "сумма «в день/месяц»")
_r("ar_income_pitch", "job", 3.0, W("ربح|ارباح|دخل|عائد|اربح|تربح|اكسب|تكسب|مضمون|مضمونه|بدون راس مال|بدون خبره|عمل من|من البيت|من المنزل|اونلاين|فرصه") + G(70) + _NUMPAT,
   "доход «сумма в день/месяц»")
_r("ar_income_num2", "job", 2.5, W("يوميا|في اليوم|كل يوم|اسبوعيا|شهريا", pre=False, suf=False) + r"\s*(?:ب|من|حتى|الى)?\s*" + _NUM + r"\s*" + _CUR,
   "«ежедневно + сумма»")
_r("ar_hiring", "job", 2.0, after("مطلوب|مطلوبه|مطلوبين|نطلب|نبحث عن|نحتاج|فرصه عمل|فرص عمل|وظائف شاغره|وظيفه شاغره|وظائف متاحه|توظيف فوري|توظيف مباشر",
    "موظفين|موظفات|بنات|شباب|مندوب|مندوبين|مندوبات|مسوقين|مسوقات|مشرفين|عمال|سائقين|كاشير|سكرتيره|مدخلي بيانات|ادخال بيانات|وكلاء|شركاء|للعمل|براتب", 30),
    "набор сотрудников")
_r("ar_remote_job", "job", 2.0, after("عمل|وظيفه|وظائف|توظيف|دوام|شغل|فرصه عمل|فرص عمل",
    "عن بعد|من المنزل|من البيت|اونلاين|اون لاين|بدوام جزئي|دوام جزئي|دوام مرن|بوقت فراغك|في وقت فراغك|ساعتين يوميا|ساعتين في اليوم|بدون دوام", 25),
    "удалённая работа / подработка")
_r("ar_hours_day", "job", 2.0, r"(?:ساعتين|ساعه|\d+\s*ساعات?)\s*(?:فقط\s*)?(?:في\s+اليوم|يوميا|باليوم)" + G(40) + W("ربح|ارباح|دخل|راتب|اربح|تربح|دولار|ريال", pre=False),
   "«пара часов в день» + доход")
_r("ar_target_group", "job", 2.0, after("للطلاب|للطالبات|ربات البيوت|لربات البيوت|للامهات|للموظفين|للمتقاعدين|للعاطلين عن العمل|للخريجين|للمغتربين",
    "عمل|دخل|ربح|فرصه|وظيفه|راتب|مشروع", 40), "«для студентов / домохозяек» + доход")
_r("ar_closed_set", "job", 2.0, after("فتح باب التسجيل|باب التسجيل مفتوح|عدد المقاعد محدود|مقاعد محدوده|الاماكن محدوده|قروب خاص|كروب خاص|جروب خاص|قناه خاصه|قناه vip|قروب vip|كروب vip|مجموعه vip|مجموعه خاصه",
    "ربح|ارباح|تداول|توصيات|دخل|استثمار|فوركس|عملات|اسهم", 50), "закрытое сообщество про деньги")
_r("ar_proven", "job", 1.5, W("طريقه مضمونه|طريقه مجربه|نظام مضمون|نظام مجرب|نتائج مضمونه|مصداقيه 100|مضمون 100|مجرب ومضمون|ربح حلال|عمل حلال|ارباح حلال|شغل نظيف"),
   "«проверенный способ / халяльный заработок»")
_r("ar_collab", "job", 1.5, W("نبحث عن شركاء|ابحث عن شريك|ابحث عن شركاء|نبحث عن شريك|اشخاص جادين|للجادين فقط|للجادين|اشخاص طموحين|لمن يبحث عن دخل|من يريد الربح|غير حياتك|غيّر حياتك|من يريد تغيير حياته"),
   "«ищу серьёзных людей»")

# ── кредиты / инвестиции / крипта ──
_r("ar_loan", "invest", 3.0, after("قروض|قرض|تمويل|تمويل شخصي|تمويل فوري|سلف|سلفه|كاش|كاش فوري|تسهيلات|تسهيلات ماليه",
    "بدون كفيل|بدون تحويل راتب|بدون تحويل|بدون فوائد|بدون فوايد|بدون ضمانات|بدون ضمان|بدون كفاله|بدون مقدم|بدون سجل|بدون استعلام|بدون سمه|بدون رفض|بدون اوراق|بدون مستندات|لجميع الجنسيات|لكل الجنسيات|للمقيمين|للمتقاعدين|دون كفيل|دون تحويل راتب|في نفس اليوم|خلال ساعه|خلال ساعات|خلال 24 ساعه", 40),
    "«кредит без поручителя/проверок»", season=True)
_r("ar_debt_pay", "invest", 2.5, W("تسديد قروض|سداد القروض|سداد المديونيات|تسديد المديونيات|تسديد الديون|سداد الديون|شراء مديونيات|جدوله القروض|جدوله الديون|توحيد القروض|اعاده تمويل|ايقاف المطالبات|فك الحجز|رفع الحظر عن|رفع الايقاف|رفع المنع|فك المنع|فك الايقاف"),
   "«погашение долгов / снятие запретов»", season=True)
_r("ar_signals", "invest", 2.0, after("توصيات|توصيه|اشارات|اشارات تداول|توصيات تداول|توصيات الاسهم|توصيات الفوركس|توصيات الذهب|توصيات العملات",
    "vip|فيب|مجانيه|مجانا|مضمونه|يوميه|حصريه|مدفوعه|اشتراك|قناه|ارباح|نسبه نجاح|نسبه ربح", 30), "платные/«проверенные» сигналы")
_r("ar_winrate", "invest", 2.0, r"\d{2,3}\s*%\s*(?:نجاح|ربح|دقه|نسبه\s+(?:نجاح|ربح))|نسبه\s+(?:نجاح|ربح)\s*\d{2,3}\s*%", "«90% успеха»")
_r("ar_trade", "invest", 1.2, W("تداول|فوركس|forex|عملات رقميه|العملات الرقميه|العملات المشفره|كريبتو|كربتو|crypto|بيتكوين|بتكوين|bitcoin|ايثريوم|باينانس|بينانس|binance|بايبت|bybit|تيثر|usdt|محفظه رقميه|ترست والت|trust wallet|نسخ صفقات|نسخ التداول|مضاربه|سكالبينج|خيارات ثنائيه|بروكر|broker|رافعه ماليه|منصه تداول|منصه استثمار|منصه ارباح|استثمار|استثمارات|استثمر"),
   "крипта / трейдинг / инвестиции")
_r("ar_invest_promise1", "invest", 3.0, after("ارباح|ربح|عائد|عوائد|مكسب|مكاسب|نسبه ارباح|ارباحك",
    "مضمونه|مضمون|مؤكده|مؤكد|ثابته|ثابت|يوميه|اسبوعيه|شهريه|بدون خساره|بدون مخاطر|خاليه من المخاطر|خالي من المخاطر", 25), "гарантированная прибыль")
_r("ar_invest_promise2", "invest", 3.0, after("مضمون|مضمونه|مؤكد|مؤكده|بدون خساره", "ربح|ارباح|عائد|عوائد|مكسب|مكاسب", 15), "гарантированная прибыль")
_r("ar_invest_double", "invest", 3.0, after("ضاعف|تضاعف|نضاعف|مضاعفه|اضاعف|ضاعفوا|يضاعف|اضعاف",
    "راس المال|رصيدك|محفظتك|مبلغك|ايداعك|اموالك|فلوسك|ارباحك|استثمارك|مالك|الايداع|المبلغ|الرصيد", 30), "«удвоим депозит»")
_r("ar_invest_pct", "invest", 3.0, r"(?<!\d)\d{2,4}\s*%\s*(?:ارباح|ربح|عائد|يوميا|في\s+اليوم|اسبوعيا|في\s+الاسبوع|شهريا|في\s+الشهر|باليوم|بالاسبوع|بالشهر)", "«100% в день/неделю»")
_r("ar_recovery", "illegal", 3.0, W("استرجاع الاموال|استرداد الاموال|استرجاع اموالك|استرداد اموالك|استرجاع المبالغ|استرداد المبالغ|استعاده الاموال|استرجاع الحسابات|استرجاع حسابك|استعاده حسابك|استرجاع المحافظ|استرجاع محفظتك|استرجاع العملات|استرجاع الاموال المسروقه|استرجاع المبالغ المنصوبه|ضحايا النصب|ضحايا الاحتيال|ضحيه نصب|ضحيه احتيال|نسترجع اموالك|نسترجع لك|نستعيد اموالك|نساعدك في استرجاع|نساعدك على استرجاع|ضحايا التداول|ضحايا المنصات"),
   "«вернём украденные деньги» (скам-рекавери)")
_r("ar_airdrop", "invest", 2.0, W("ايردروب|اير دروب|airdrop|عمله مجانيه|عملات مجانيه|توكن مجاني|توكنات مجانيه|تعدين مجاني|تعدين سحابي|ماينينج|تعدين على الجوال|قبل الادراج|قبل الانفجار|ستنفجر|100x|1000x|انفجار سعري|ضخ جماعي|صفقه رابحه|صفقات رابحه|فرصه ذهبيه|فرصه لا تعوض|لا تفوت الفرصه"),
   "airdrop / «взрывной рост»")

# ── азарт / бонусы / розыгрыши ──
_r("ar_gamble", "gamble", 2.5, W("كازينو|كازينوهات|كازينو اونلاين|الكازينو|مراهنات|مراهنه|المراهنات|بيتنج|قمار|القمار|مقامره|روليت|بلاك جاك|بوكر|سلوت|سلوتس|سلوتات|لعبه الطياره|لعبه الطائره|افياتور|aviator|ون اكس بيت|ون اكس بت|1xbet|1x bet|melbet|ميل بيت|1win|وان وين|mostbet|موستبيت|bet365|بيت365|بيت 365|parimatch|باري ماتش|linebet|لاين بيت|22bet|betway|بيتواي|ماتش بيت|جاكبوت|فري سبين|فري سبينز|دوران مجاني|لفات مجانيه|رهان رياضي|رهانات رياضيه|مراهنات رياضيه|مراهنه على المباريات|مباريات مضمونه|كوبون مضمون|كوبونات مضمونه|مباريات مفبركه|مباريات ثابته|سكور مضمون"),
   "казино / ставки")
_r("ar_bonus", "gamble", 2.0, after("بونص|بونس|بونوس|مكافاه ترحيبيه|مكافاه التسجيل|مكافاه الايداع|بونص ترحيبي|بونص الايداع|بونص التسجيل|كاش باك|كاشباك|عرض ترحيبي|هديه ترحيبيه|هديه التسجيل|رصيد مجاني|رصيد هديه|رصيد ترحيبي",
    "ايداع|الايداع|اول ايداع|تسجيل|التسجيل|سجل|اشحن|شحن|بروموكود|كود|كود خصم|كود برومو|كود ترويجي|رمز ترويجي|رمز برومو|ادخل الكود|استخدم الكود|استخدم كود|بالكود", 40), "бонус за депозит/регистрацию")
_r("ar_promocode", "gamble", 1.2, W("بروموكود|برومو كود|كود برومو|كود ترويجي|رمز ترويجي|رمز برومو|promo code|promocode"), "промокод")
_r("ar_giveaway", "promo", 1.5, after("سحب|سحوبات|مسابقه|مسابقات|هديه|هدايا|جائزه|جوائز|جايزه|فزت|ربحت|فائزين|فائز|تهانينا",
    "مجاني|مجانا|مجانيه|بدون مقابل|للاعضاء|للمشتركين|للمتابعين|حصريا|ايفون|سياره|رحله|عمره|تذاكر|بطاقه هدايا|كروت هدايا|بطاقات هدايا|رصيد|نقاط|ريال|دولار|درهم|بيتكوين|بريميوم|نجوم|ستارز|ذهب|سبائك", 30),
    "розыгрыш-приманка", season=True)
_r("ar_free_gift", "promo", 2.5, W("تلجرام بريميوم مجانا|تيليجرام بريميوم مجانا|بريميوم مجانا|بريميوم مجاني|نجوم مجانا|نجوم مجانيه|ستارز مجانا|هديه من تلجرام|هديه من تيليجرام|هدايا تلجرام|هدايا تيليجرام|ايفون مجانا|ايفون مجاني|ايفون هديه"),
   "«бесплатный Premium/звёзды/iPhone»", season=True)
_r("ar_prize_notice", "promo", 3.0, W("مبروك لقد فزت|مبروك فزت|لقد ربحت|تم اختيارك|تم اختيار رقمك|تم اختيار حسابك|انت الفائز|انت الفائزه|اخترنا رقمك|فزت بجائزه|حصلت على جائزه|ربحت جائزه|ربحت مبلغ|مبروك ربحت"),
   "«вы выиграли»", season=True)

# ── призывы писать / переходить ──
_r("ar_cta_dm", "cta", 2.0, after("راسلني|راسلنا|راسلوني|راسلونا|راسلي|تواصل معي|تواصل معنا|تواصلوا معنا|تواصلوا معي|تواصلو معي|تواصلو معنا|كلمني|كلمنا|كلموني|كلمونا|ارسل لي|ارسلي لي|ارسلوا لي|ارسل لنا|اكتب لي|اكتبلي|اكتبوا لي|ضيفني|ضيفوني|ضيفنا|ابعث لي|ابعثلي|تعال خاص|تعالوا خاص|ادخل الخاص",
    _CONTACT, 25), "зовёт в личку/мессенджер")
_r("ar_dm_hint", "cta", 1.2, r"(?:^|\s)(?:على|ع|في|ب|ل)\s*(?:ال)?خاص(?![" + AR + r"])|(?:^|\s)(?:راسلني|كلمني|راسلنا)\s*$", "«в личку»")
_r("ar_detail_dm", "cta", 2.0, after("للتواصل|للاستفسار|للتفاصيل|للمزيد|لمعرفه التفاصيل|للحجز|للطلب|للاشتراك|للتسجيل|للانضمام|للتقديم",
    "خاص|الخاص|واتس|واتساب|واتس اب|تلجرام|تليجرام|تلغرام|تيليجرام|سناب|رقم|الرقم|الرابط|رابط|اتصل|راسلني|راسلنا|البروفايل|بايو", 30), "детали — только в личке")
_r("ar_cta_word", "cta", 2.5, after("اكتب|ارسل|ارسلوا|اكتبوا|اكتبي|ارسلي|ضع|ضعوا",
    "مهتم|مهتمه|مهتمين|تم|اريد|ابي|ابغى|ابغا|عايز|عايزه|حاب|حابب|ابي التفاصيل|اريد التفاصيل|+", 12), "«напиши слово/плюс»")
_r("ar_cta_link", "cta", 2.5, after("اضغط|اضغطوا|اضغطي|ادخل|ادخلوا|ادخلي|افتح|افتحوا|حمل|حملوا|حملي|سجل|سجلوا|انقر|انقروا|دوس|دوسوا|اكبس|اكبسوا",
    "الرابط|رابط|اللينك|لينك|الصوره|هنا|الموقع|التطبيق|الحساب|الصفحه|البروفايل|الملف الشخصي|البوت|الزر|في الاسفل|بالاسفل", 20), "«нажми на ссылку/кнопку»")
_r("ar_cta_profile", "cta", 2.5, after("الرابط|رابط|لينك|اللينك|الروابط",
    "في البايو|بالبايو|في البروفايل|بالبروفايل|في الوصف|بالوصف|في التعليق|بالتعليقات|في التعليقات|اول تعليق|اول كومنت|في القناه|في قناتي|في المنشور|في الملف الشخصي", 15), "«ссылка в профиле/комментарии»")
_r("ar_join", "cta", 1.5, after("انضم|انضموا|انضمو|انضمي|ادخل|ادخلوا|اشترك|اشتركوا|اشتركي|تابعنا|تابعوني|الحقوا|الحقونا|تعالوا",
    "قناتنا|قناتي|قنواتنا|قروبنا|قروبي|جروبنا|جروبي|مجموعتنا|مجموعتي|كروبنا|كروبي|بوتنا|بوتي|عائلتنا|فريقنا|مجتمعنا|قروب واتساب|جروب واتساب|مجموعه واتساب", 15),
    "зовёт вступить в канал/чат")
_r("ar_link_word", "cta", 1.5, W("رابط القناه|رابط القروب|رابط الجروب|رابط الكروب|رابط المجموعه|رابط قناتنا|رابط قروبنا|رابط الانضمام|رابط التسجيل|رابط الاشتراك|رابط التفعيل"), "«ссылка на канал/регистрацию»")
_r("ar_urgency", "urgency", 1.5, W("سارع|سارعوا|بادر|بادروا|لا تفوت|لاتفوت|لا تضيع|فرصه لا تعوض|فرصه ذهبيه|فرصه العمر|لفتره محدوده|لفتره قصيره|العرض محدود|عرض محدود|الاماكن محدوده|الاماكن المتبقيه|المقاعد محدوده|عدد محدود|اخر فرصه|اخر مقاعد|اليوم فقط|ينتهي العرض|قبل انتهاء العرض|قبل فوات الاوان|الفرصه لن تتكرر")
   + "|" + r"(?:متبقي|بقي|باقي)\s*\d+\s*(?:مقعد|مقاعد|مكان|اماكن|قطعه|قطع|شخص|اشخاص)", "давление срочностью")

# ── 18+ ──
_r("ar_adult_numbers", "adult_ad", 2.5, after("ارقام|اراقام|نمر|ارقام واتس|ارقام واتساب|ارقام جوال|ارقام جوالات|ارقام تعارف",
    "بنات|فتيات|مطلقات|ارامل|سيدات|نساء|سعوديات|مصريات|خليجيات|كويتيات|اماراتيات|قطريات|عراقيات|سوريات|لبنانيات|اردنيات|فلسطينيات|مغربيات|جزائريات|تونسيات|سودانيات|اجنبيات|روسيات|اوكرانيات|للتعارف|للمتعه", 15),
    "номера «девушек» / знакомства 18+")
_r("ar_adult_dating", "adult_ad", 2.5, after("تعارف|صداقه|علاقات|علاقه|دردشه",
    "بدون التزام|بدون التزامات|بدون قيود|حميمه|ساخنه|جنسيه|جنسي|للكبار|بدون حدود|متحرره|للمتزوجين|للمتزوجات|سريه تامه|خصوصيه تامه", 10), "знакомства без обязательств")
_r("ar_adult_massage", "adult_ad", 2.5, after("مساج|تدليك|مساج رجالي|مساج نسائي|جلسات مساج",
    "جنسي|ساخن|حار|مثير|رومانسي|مع نهايه سعيده|نهايه سعيده|اكستر|هابي اند|بودي تو بودي", 15), "«массаж» 18+")
_r("ar_misyar", "adult_ad", 1.8, W("زواج مسيار|زواج المسيار|زواج متعه|زواج المتعه|نكاح المتعه|زواج فريند|زواج فرند|زواج صيغه|زواج سري"), "«брак-мисьяр / мутъа» (реклама)")
_r("ar_escort", "adult_ad", 3.0, W("خدمات جنسيه|خدمات للكبار|خدمات خاصه للرجال|متعه جنسيه|متعه حلال|ليله حمراء|ليله ساخنه|سهره حمراء|سهره ساخنه|فتيات ليل|بنات ليل|بنات للمتعه|بنات للايجار|بنات للسهر|بنات جاهزات|فتيات جاهزات|فتيات متاحات|بنات متاحات|بنات تحت الطلب|فتيات تحت الطلب|بنات حسب الطلب|فتيات حسب الطلب|اسكورت|escort|دعاره|عاهرات|جيجولو|جيغولو"),
   "эскорт / секс-услуги")
_r("ar_adult_content", "adult_ad", 2.5, after("قنوات|قناه|قروبات|قروب|كروبات|جروبات|روابط|رابط|قصص|روايات|فيديوهات|فيديو|صور|مقاطع|افلام|مجلات|محتوى|بوت|بوتات",
    "سكس|نيك|بورنو|اباحيه|اباحي|اباحيات|ساخنه|جنسيه|للكبار|محارم|ممحونات|ممحونه|عاريات|سكسي|سكسيه", 8), "канал/ссылки 18+")
_r("ar_age18", "adult_ad", 1.0, r"(?:^|[\s(])(?:\+\s?18|18\s?\+)(?!\d)|فوق\s*(?:ال)?18(?!\d)|للكبار\s+فقط|للبالغين\s+فقط", "метка 18+")
_r("ar_webcam", "adult_ad", 2.5, W("شات جنسي|شات ساخن|شات كام|كام جنسي|كام ساخن|فيديو كول جنسي|فيديو كول ساخن|مكالمات فيديو ساخنه|مكالمات ساخنه|مكالمات جنسيه|بث مباشر ساخن|بث ساخن|رقص مثير|اونلي فانز|onlyfans|اونليفانز|سناب مفتوح|سناب ساخن|سناب بنات|سنابات بنات|سنابات مفتوحه|سنابات ساخنه|يوزرات بنات|يوزرات سناب"),
   "вебкам / 18+ контент")
_r("ar_pharma_sex", "sale", 2.5, W("حبوب الانتصاب|حبوب انتصاب|منشطات جنسيه|منشط جنسي|مقويات جنسيه|مقوي جنسي|حبوب تقويه|حبوب الفحوله|حبوب الرجوله|فياجرا|فياغرا|سياليس|كيالس|بخاخ تاخير|بخاخ التاخير|سبراي تاخير|كريم تاخير|كريم تكبير|تكبير القضيب|تكبير العضو|تطويل القضيب|تكبير الذكر|تكبير الثدي|تضيق المهبل|كريم تضييق|علاج سرعه القذف|علاج الضعف الجنسي|علاج ضعف الانتصاب|زياده الرغبه|عطور جنسيه|حبوب تخسيس|حبوب التخسيس|كبسولات تخسيس|كبسولات التنحيف|حبوب التنحيف|حبوب تسمين|حبوب زياده الطول|حبوب تفتيح|حبوب التبييض|ابر التبييض|ابر التخسيس|حقن التبييض|حقن التخسيس"),
   "«таблетки/средства»: сексуальные и для похудения")

# ── продажи / серые схемы ──
_r("ar_followers", "sale", 2.0, after("زياده|شحن|رشق|بيع|شراء|اشتري|ابيع|تنزيل|ارشاق|نزود|نزيد|نوفر|خدمات",
    "متابعين|متابع|مشتركين|لايكات|لايك|مشاهدات|اعضاء|ممبرز|ممبرات|اعجابات|فولورز|ريتويت|اشتراكات|زوار|ترافيك", 25), "накрутка подписчиков/лайков")
_r("ar_sell_account", "sale", 2.5, W("حسابات للبيع|حساب للبيع|قنوات للبيع|قناه للبيع|قروبات للبيع|بيع حسابات|بيع حساب|بيع قنوات|بيع ارقام|ارقام للبيع|ارقام وهميه|ارقام مؤقته|ارقام افتراضيه|ارقام امريكيه|ارقام اجنبيه|تفعيل واتساب|تفعيل واتس|تفعيل تلجرام|تفعيل تيليجرام|حسابات جاهزه|حسابات مفعله|حسابات قديمه|حسابات مضمونه|بيع بريميوم|تلجرام بريميوم رخيص|تيليجرام بريميوم رخيص|شراء نجوم|بيع نجوم|اشتراكات رخيصه|اشتراك نتفلكس|اشتراك شاهد|اشتراك سبوتيفاي|بيع اشتراكات|ايجار حسابات|تاجير حسابات"),
   "продажа аккаунтов/номеров/подписок")
_r("ar_mule", "illegal", 3.5, W("ايجار حساب بنكي|تاجير حساب بنكي|ايجار حسابات بنكيه|تاجير حسابات بنكيه|حساب بنكي للايجار|حسابات بنكيه للايجار|اجر حسابك|ايجار بطاقتك|تاجير بطاقتك|مقابل حسابك|مقابل بطاقتك|مقابل استخدام حسابك|استقبال حوالات مقابل|غسيل اموال|تبييض اموال"),
   "аренда банковских счетов / отмывание (мулы)")
_r("ar_carding", "illegal", 3.5, W("فيزا مسروقه|بطاقات مسروقه|كروت مسروقه|فيزات مسروقه|فيزا مهكره|كروت مهكره|سي في في|cvv|فيزا جاهزه|فيزات جاهزه|بيع فيزا|سحب بطاقات|سحب فيزا|كاردينج|carding|بطاقات مهكره|اكواد مسروقه"),
   "краденые карты / кардинг")
_r("ar_forge", "illegal", 3.5, W("شهادات مزوره|شهاده مزوره|جواز مزور|جوازات مزوره|اقامه مزوره|هويه مزوره|رخصه مزوره|وثائق مزوره|اوراق مزوره|تزوير شهادات|تزوير وثائق|تزوير جوازات|تزوير هويات|تزوير اقامات|شهادات بدون دراسه|شهاده بدون دراسه|رخصه قياده بدون اختبار|رخصه بدون اختبار"),
   "поддельные документы")
_r("ar_medreport", "sale", 2.5, after("تقارير طبيه|تقرير طبي|اجازه مرضيه|اجازات مرضيه|اعذار طبيه|عذر طبي|سكليف|سكليفات|تقارير مرضيه|اجازات طبيه",
    "معتمده|معتمد|مضمونه|مضمون|للبيع|متوفره|متوفر|توصيل|خلال ساعه|خلال دقائق|فوري|واتساب|خاص|تواصل|راسلني|سعر|ريال", 40), "продажа справок/больничных")
_r("ar_homework", "sale", 2.0, W("حل واجبات|حل الواجبات|حل واجب|حل اسايمنت|حل اسايمنتات|حل اختبارات|حل الاختبارات|حل كويزات|حل الكويزات|حل البلاك بورد|حل بلاك بورد|تسليم بحوث|كتابه بحوث|كتابه البحوث|عمل بحوث|بحوث جاهزه|مشاريع تخرج|مشروع تخرج|رسائل ماجستير|رسائل دكتوراه|مساعده في الواجبات|مساعده في الاختبارات|مساعده في البحوث|خدمات طلابيه|خدمات اكاديميه|خدمات جامعيه|حل واجبات جامعيه|assignment|assignments|thesis|dissertation"),
   "решение домашек/курсовых на заказ")
_r("ar_sell_misc", "sale", 1.5, after("للبيع|للتنازل", "حساب|حسابات|قناه|قنوات|سيرفر|بوت|سكربت|اسكربت|سورس|يوزر|يوزرات|قروب|كروب|جروب|شهاده|شهادات", 15), "продажа аккаунтов/каналов")
_r("ar_services_ad", "sale", 1.2, W("اعلن معنا|اعلن عندنا|مساحه اعلانيه|نشر اعلانات|خدمات اعلانيه|خدمات تسويقيه|تسويق الكتروني|ادارة حسابات|تصميم شعارات|تصميم لوجو|خدمات تصميم"), "реклама услуг")
_r("ar_occult", "sale", 2.0, W("فك السحر|فك العين|فك الربط|جلب الحبيب|جلب المحبه|جلب الزوج|جلب الزوجه|جلب الرزق|جلب المال|جلب الحظ|جلب الغائب|رد المطلقه|رد الزوج|رد الغائب|ربط الزوج|ربط الزوجه|عمل سفلي|اعمال سفليه|سحر اسود|سحر ازرق|سحر المحبه|سحر التفريق|سحر الجلب|علاج روحاني|معالج روحاني|شيخ روحاني|راقي روحاني|شيخ معالج|شيخ مغربي|شيخ سوداني|تحضير الجن|تحضير الارواح|خدام الجن|خاتم سليمان|خاتم سليماني|حجاب المحبه|حجاب الحظ|حجاب الرزق|طلاسم|فتح الحظ|فتح المندل|فتح الرزق|قراءه الفنجان|قراءه الطالع|كشف المسحور"),
   "услуги «колдунов/шейхов-целителей»")
_DRUGS = ("حشيش|حشيشه|ماريجوانا|ماريوانا|كوكايين|كوكاين|هيروين|هروين|شبو|كريستال ميث|ميثامفيتامين|كبتاجون|كبتاغون|امفيتامين|امفيتامينات|ترامادول|ترمادول|ترامدول|ليريكا|بريجابالين|زاناكس|زانكس|اكستاسي|ايكستسي|ايكستاسي|lsd|بانجو|سايتوتك|ميفيبريستون|حبوب الاجهاض|حبوب اجهاض|كبسولات الاجهاض|حبوب مخدره|اقراص مخدره|مخدرات|مورفين|كراتوم")
_DRUG_SALE = ("للبيع|متوفر|متوفره|توصيل|نوصل|اوصل|ارسال|نرسل|شحن|طلب|اطلب|اطلبوا|سعر|اسعار|خصم|تواصل|راسلني|راسلنا|مضمون|مضمونه|اصلي|اصليه|جوده عاليه|كيلو|جرام|غرام|اوقيه|ربع|حبه|حبات|شريط|اشرطه|عبوه|عبوات|دفع عند الاستلام|الدفع عند الاستلام|واتساب|تلجرام|خاص|الخاص|سريه تامه|بسريه|تعبئه سريه|جميع الدول|كل الدول")
_r("ar_drugs_sale", "illegal", 3.5, PAIR(_DRUGS, _DRUG_SALE, 60), "продажа запрещённых веществ")
_r("ar_drug_word", "illegal", 2.0, W("حبوب الاجهاض|حبوب اجهاض|سايتوتك|كبتاجون|كبتاغون|ترامادول|ترمادول|هيروين|كوكايين|كوكاين|شبو|كريستال ميث|ماريجوانا|حشيش"), "запрещённые вещества")
_r("ar_hack", "illegal", 3.0, PAIR("اختراق|تهكير|هكر|هاكر|تجسس|مراقبه|تتبع|سحب|كشف|فك|استرجاع|فتح",
    "حسابات|حساب|واتساب|واتس|سناب|انستقرام|انستا|فيسبوك|فيس بوك|تيك توك|تلجرام|تليجرام|جوال|هاتف|موبايل|كاميرا|صور|محادثات|رسائل|الزوج|الزوجه|الحبيب|الخيانه|خيانه|ايميل|البريد|ايفون|اندرويد", 20),
   "взлом/слежка за аккаунтами")
_r("ar_hack2", "illegal", 3.0, W("هكر محترف|هاكر محترف|خدمات اختراق|خدمات هكر|خدمات هاكر|هكر سعودي|هكر مصري|هكر عربي|هاكر عربي|اختراق مضمون|كشف الخيانه|كشف خيانه الزوج|كشف خيانه الزوجه|مراقبه جوال الزوج|مراقبه هاتف الزوج"), "услуги хакера / слежка")

# ── фишинг / «пришли код» ──
_r("ar_send_code", "invest", 3.5, W("ارسل لي الكود|ارسل الكود|ارسل لي رمز|ارسل لي الرمز|ارسل الرمز|ارسلي الكود|ارسل كود التحقق|ارسل رمز التحقق|ارسل كود التفعيل|ارسل رمز التفعيل|الكود الذي وصلك|الكود اللي وصلك|الكود الي وصلك|رمز التحقق الذي|كود التحقق الذي|اعطني الكود|اعطني الرمز|اعطيني الكود|اعطيني الرمز|ابغى الكود|ابي الكود|ابغا الكود|عايز الكود|احتاج الكود|احتاج الرمز|الكود وصلك|وصلك كود|وصلك رمز|ارسل لي ما وصلك|ارسل ما وصلك"),
   "просит прислать код из SMS/Telegram (угон аккаунта)")
_r("ar_account_threat", "invest", 3.0, W("تم تعليق حسابك|تم ايقاف حسابك|تم حظر حسابك|سيتم حظر حسابك|سيتم تعليق حسابك|سيتم ايقاف حسابك|سيتم اغلاق حسابك|سيتم تجميد حسابك|تم تجميد حسابك|حسابك مهدد|حسابك معرض للحظر|حسابك معرض للايقاف|حسابك سيحظر|حسابك سيغلق|تم اختراق حسابك|نشاط مشبوه في حسابك|محاوله دخول مشبوهه|تحقق من حسابك|توثيق حسابك|تحديث بياناتك|تحديث بيانات حسابك|حدث بياناتك|تحديث معلومات حسابك|والا سيتم|والا ستفقد|والا ستخسر"),
   "«аккаунт будет заблокирован — подтвердите»")
_r("ar_credentials", "invest", 3.0, PAIR("رقم بطاقتك|رقم البطاقه|رقم الكرت|رقم الفيزا|الرقم السري|كلمه السر|كلمه المرور|رمز otp|otp|رمز التحقق|cvv|سي في في|تاريخ انتهاء البطاقه|رقم الهويه|رقم الاقامه|رمز الامان",
    "ارسل|ارسلوا|ارسلي|ادخل|ادخلوا|اكتب|اكتبوا|اعطني|اعطيني|زودنا|زودني|ادخال|تاكيد|تحديث|مطلوب|المطلوب|لاتمام|لتاكيد|لتفعيل|لاستلام|لسحب|لاسترداد|للتحقق|للتوثيق", 25),
   "просит данные карты/пароль/OTP")
_BRANDS = ("ابشر|نفاذ|توكلنا|اعتمدنا|صحتي|الجوازات|المرور|وزاره الداخليه|وزاره العمل|مكتب العمل|التامينات|حساب المواطن|الضمان الاجتماعي|سداد|البنك الاهلي|الراجحي|مصرف الراجحي|الانماء|بنك الجزيره|stc pay|اس تي سي باي|stc|موبايلي|اتصالات|فودافون|اورانج|البريد السعودي|ارامكس|سمسا|ناقل|dhl|فيدكس|امازون|نون|جرير|انستاباي|فودافون كاش")
_ACTS = ("تحديث|تحقق|توثيق|تفعيل|ايقاف|تعليق|حظر|مخالفه|مخالفات|رسوم|سداد|دفع|استرداد|استرجاع|مكافاه|جائزه|هديه|رصيد|نقاط|فاتورتك|طرد|شحنتك|الشحنه|رسوم التوصيل|رسوم الشحن|تعذر التسليم|فشل التسليم|اكمل|بياناتك|حسابك")
_BRAND_RX = after(_BRANDS, _ACTS, 40)
_r("ar_brand_phish", "invest", 1.0, _BRAND_RX, "бренд банка/госсервиса + «обновите/оплатите»", flag="nourl", season=True)
_r("ar_brand_link", "invest", 3.0, _BRAND_RX, "бренд банка/госсервиса + ссылка (фишинг)", flag="url", season=True)
_r("ar_charity", "promo", 2.0, after("تبرع|تبرعات|تبرعوا|ساعدونا|ساعدوني|حاله انسانيه|حاله مرضيه|حاله مستعجله|اسره محتاجه|اسره فقيره|اسره متعففه|كفاله يتيم|كفاله ايتام|مساعده عاجله|نداء انساني|نداء عاجل|زكاه|صدقه جاريه|سله غذائيه|سلال غذائيه|كسوه العيد|افطار صائم",
    "رقم الحساب|حساب بنكي|الايبان|ايبان|iban|رقم المحفظه|تحويل|حوالات|واتساب|للتبرع|راسلني|خاص|الخاص|اس تي سي باي|فودافون كاش|انستاباي|usdt|بيتكوين", 80),
   "сбор «пожертвований» с реквизитами", season=True)

# слабый сигнал: Арабский текст, но есть число-реквизит и призыв — обрабатывается в analyze()

SHADOW = {"ar_dm_hint": {"ar_cta_dm", "ar_cta_link", "ar_cta_profile", "ar_detail_dm", "ar_az_dm"},
          "ar_earn_word": {"ar_earn_pitch", "ar_earn_online", "ar_income_pitch", "ar_income_num2", "ar_passive"},
          "ar_promocode": {"ar_gamble", "ar_bonus"},
          "ar_drug_word": {"ar_drugs_sale"}, "ar_az_dm2": {"ar_az_dm", "ar_cta_dm"},
          "ar_hack2": {"ar_hack"}}

FAM_RX = {
    "money": rx(W("فلوس|اموال|دولار|دولارات|ريال|ريالات|درهم|دراهم|دينار|جنيه|راتب|اربح|ارباح|ربح|دخل|كسب|عمولات|استثمار|تداول|فوركس|كريبتو|عملات رقميه|بيتكوين|بتكوين|usdt|ايداع|سحب|محفظه|قرض|قروض|تمويل|سلف|عائد|عوائد|مكسب") + r"|\$\s?\d+|\d+\s?\$"),
    "work": rx(W("وظيفه|وظائف|فرصه عمل|فرص عمل|توظيف|دوام|مطلوب|نبحث|نطلب|بدون خبره|عن بعد|من المنزل|من البيت|شراكه|مشروع|تجاره|بزنس")),
    "cta": rx(W("راسلني|راسلنا|تواصل معي|تواصل معنا|تواصلوا|كلمني|خاص|الخاص|واتساب|واتس|تلجرام|تليجرام|رابط|الرابط|اضغط|ادخل|انضم|اشترك|سجل|التسجيل|بايو|البروفايل|قناتنا|للتواصل|للاستفسار|للتفاصيل")),
    "hype": rx(W("مجانا|مجاني|مجانيه|رخيص|ارخص|مضمون|مضمونه|بونص|بونس|مكافاه|هديه|هدايا|جائزه|جوائز|سحب|حصريا|حصري|فرصه|محدود|محدوده|سارع|فورا|100%")),
    "sale": rx(W("للبيع|بيع|شراء|ابيع|حسابات|متابعين|ارقام|اشتراكات|خدمات|توصيل|حل واجبات|بحوث|شهادات")),
}


# ═════════════════════════════ ФИШКА 1: числа прописью / эмодзи-цифры ═════════════════════════════
_NUMW = {}
for _d, _ws in enumerate(("صفر سفر", "واحد واحده وحده", "اثنين اتنين اثنان اثنتين اثنين", "ثلاثه تلاته ثلاث تلات", "اربعه اربع",
                          "خمسه خمس", "سته ست", "سبعه سبع", "ثمانيه تمانيه ثمان تمان ثمنيه", "تسعه تسع")):
    for _w in _ws.split():
        _NUMW[collapse(ar_fold(_w))] = str(_d)
_NUMTOK = re.compile("[" + AR + "]+|\\d+")


def spelled_phones(F: str) -> list:
    """Телефон, записанный словами («صفر خمسة صفر …»), цифрами через слова или смешанно → строка цифр. Обычные цифры не трогаем (это дело guard)."""
    out, cur, words = [], [], 0

    def flush():
        nonlocal cur, words
        s = "".join(cur)
        if len(s) >= 8 and words >= 3:
            out.append(s)
        cur, words = [], 0
    for t in _NUMTOK.findall(F):
        if t.isdigit():
            cur.append(t)
            continue
        ct = collapse(t)
        d = _NUMW.get(ct) or (_NUMW.get(ct[1:]) if ct.startswith("و") else None)
        if d is not None:
            cur.append(d)
            words += 1
        elif ct in ("و",):
            continue
        else:
            flush()
    flush()
    return out


_AR_PHONE = re.compile(r"(?<![\d.,])(?:(?:\+|00)(?:966|971|965|974|973|968|962|961|963|964|967|970|20|212|213|216|218|249)[\s\-.]?\d[\d\s\-.]{7,12}\d"
                       r"|0?5\d[\s\-.]?\d{3}[\s\-.]?\d{4}|01[0125][\s\-.]?\d{4}[\s\-.]?\d{4}|07[3-9]\d[\s\-.]?\d{3}[\s\-.]?\d{3}|0[67]\d{2}[\s\-.]?\d{2}[\s\-.]?\d{2}[\s\-.]?\d{2})(?![\d])")


# ═════════════════════════════ ФИШКА 2: сезон по хиджре ═════════════════════════════
def hijri(y: int, m: int, d: int) -> tuple:
    """Григорианская → хиджра (табличный «кувейтский» алгоритм, ±1 день — для сезона этого достаточно)."""
    if m < 3:
        y -= 1
        m += 12
    a = y // 100
    b = 2 - a + a // 4
    jd = int(365.25 * (y + 4716)) + int(30.6001 * (m + 1)) + d + b - 1524
    l = jd - 1948440 + 10632
    n = (l - 1) // 10631
    l = l - 10631 * n + 354
    j = ((10985 - l) // 5316) * ((50 * l) // 17719) + (l // 5670) * ((43 * l) // 15238)
    l = l - ((30 - j) // 15) * ((17719 * j) // 50) - (j // 16) * ((15238 * j) // 43) + 29
    mm = (24 * l) // 709
    dd = l - (709 * mm) // 24
    yy = 30 * n + j - 30
    return yy, mm, dd


def season(now: float | None = None) -> str:
    """'' или название «скам-сезона»: Рамадан / Ид аль-Фитр / Хадж и Ид аль-Адха / канун Рамадана. Скаммеры в это время активнее."""
    if not _env_flag("GUARD_AR_SEASON", True):
        return ""
    import time as _t
    tm = _t.gmtime(now if now is not None else _t.time())
    _, hm, hd = hijri(tm.tm_year, tm.tm_mon, tm.tm_mday)
    if hm == 9:
        return "Рамадан"
    if hm == 10 and hd <= 10:
        return "Ид аль-Фитр"
    if hm == 12 and hd <= 13:
        return "Хадж / Ид аль-Адха"
    if hm == 8 and hd >= 20:
        return "канун Рамадана"
    return ""
SEASON_BOOST = 1.25


# ═════════════════════════════ АНАЛИЗ ═════════════════════════════
_FUSE = re.compile("(?<![" + AR + "])[" + AR + "](?:[ \\t.\\-_*]+[" + AR + "]){2,}(?![" + AR + "])")
_HANDLE = re.compile(r"@[a-z0-9_]{4,32}")
_OTHER_FOREIGN = re.compile("[\u0900-\u097F\u0E00-\u0E7F\u3040-\u30FF\u3400-\u9FFF\uAC00-\uD7AF]")
_custom_spam: list = []


@dataclass
class ArResult:
    found: Found = field(default_factory=Found)
    signals: list = field(default_factory=list)      # (имя, вес, причина) — как у guard
    phones: list = field(default_factory=list)       # "tel:XXXXXXXXXX" для «сети контактов»
    letters: int = 0
    season: str = ""

    @property
    def score(self) -> float:
        return round(sum(w for _, w, _ in self.signals), 2)


def analyze(text: str, has_url: bool = False, now: float | None = None) -> ArResult:
    res = ArResult()
    if not text or not enabled():
        return res
    raw = text[:3000]
    res.letters = arabic_count(raw)
    F = ar_fold(raw)
    digits_phone = _AR_PHONE.search(F)
    spelled = spelled_phones(F)
    contactish = has_url or bool(digits_phone) or bool(spelled) or bool(_HANDLE.search(F))
    fd = lex_scan(raw, F, shield=not contactish, contactish=contactish)           # контекстный щит выключается, если в тексте есть контакт/ссылка
    res.found = fd
    sig = res.signals

    if res.letters >= 4:
        F2 = _FUSE.sub(lambda m: re.sub("[^" + AR + "]", "", m.group(0)), F)
        cands = [F] if F2 == F else [F, F2]
        res.season = season(now)
        hit: dict = {}
        for name, group, w, crx, why, flag in RULES:
            if (flag == "url" and not has_url) or (flag == "nourl" and has_url):
                continue
            if any(crx.search(c) for c in cands):
                if res.season and name in SEASONAL:
                    w, why = round(w * SEASON_BOOST, 2), why + " · сезон: " + res.season
                hit[name] = (group, w, why)
        for crx, w, why in _custom_spam:
            if any(crx.search(c) for c in cands):
                hit["ar_custom"] = ("promo", w, why)
        _group_signals(hit, sig, F)
    low = raw.lower()
    if _env_flag("GUARD_AR_ARABIZI", True) and re.search(r"[a-z0-9]{3}", low):
        hit = {name: (group, w, why) for name, group, w, crx, why in AZ_SPAM if crx.search(low)}
        for k in list(hit):
            if SHADOW.get(k) and SHADOW[k] & hit.keys():
                del hit[k]
        _group_signals(hit, sig, low, fam=False)

    if digits_phone:
        sig.append(("ar_phone", 1.2, "номер телефона (арабский формат)"))
        d = re.sub(r"\D", "", digits_phone.group(0))
        if len(d) >= 9:
            res.phones.append("tel:" + d[-10:])
    for s in spelled:
        sig.append(("ar_phone_words", 2.0, "телефон, записанный словами — обход фильтра контактов"))
        res.phones.append("tel:" + s[-10:])
        break
    if sig or fd.prof or fd.hate or fd.adult:
        if fd.dialect:
            sig.append(("ar_dialect", 0.0, "диалект: " + DIALECT_RU[fd.dialect]))
        if fd.shielded:
            sig.append(("ar_shield", 0.0, "смягчено: религиозный/новостной контекст (%d сл.)" % fd.shielded))
    return res


def _group_signals(hit: dict, sig: list, text: str, fam: bool = True) -> None:
    by_group: dict = {}
    names = set(hit)
    for name, (group, w, why) in hit.items():
        if SHADOW.get(name) and SHADOW[name] & names:
            continue
        by_group.setdefault(group, []).append((w, name, why))
    pitch = cta = False
    for group, items in by_group.items():
        items.sort(reverse=True)
        w = items[0][0] + (0.5 * items[1][0] if len(items) > 1 else 0.0)
        sig.append((items[0][1] if len(items) == 1 else "ar_" + group, round(w, 2),
                    items[0][2] + (" (+%d)" % (len(items) - 1) if len(items) > 1 else "")))
        pitch |= group in PITCH_GROUPS
        cta |= group == "cta"
    if pitch and cta:
        sig.append(("ar_pitch_cta", 2.0, "предложение + призыв писать/переходить"))
    if not fam or len(text) < 20:
        return
    fams = {k for k, r_ in FAM_RX.items() if r_.search(text)}
    overlap = 2.0 if (pitch and cta) else 0.0
    if len(fams) >= 3:
        if 3.0 - overlap > 0:
            sig.append(("ar_families3", 3.0 - overlap, "сразу три приметы: деньги/работа, выгода, призыв"))
    elif len(fams) == 2:
        strong = "cta" in fams and bool(fams & {"money", "work", "sale"})
        w2 = (1.5 if strong else 0.8) - overlap
        if w2 > 0:
            sig.append(("ar_families2", w2, "две приметы рекламы подряд"))


# ═════════════════════════════ СВОИ СЛОВА ═════════════════════════════
def load_custom(path) -> int:
    """custom_words_ar.txt → слова/фразы. Возвращает число принятых строк."""
    for k in _custom:
        _custom[k] = []
    _custom_spam.clear()
    p = Path(path)
    n = 0
    if p.exists():
        for line in p.read_text(encoding="utf-8").splitlines():
            line = line.split("#", 1)[0].strip()
            if ":" not in line:
                continue
            cat, word = (x.strip() for x in line.split(":", 1))
            if not word:
                continue
            if cat == "spam":
                w = 2.0
                if "|" in word:
                    word, ws = word.rsplit("|", 1)
                    try:
                        w = float(ws)
                    except ValueError:
                        pass
                _custom_spam.append((re.compile(W(word.strip())), w, "своя фраза: " + word.strip()[:40]))
                n += 1
            elif cat in ("prof", "hate", "adult", "minor", "allow"):
                _custom[cat].append(word.replace(" ", "_") if cat != "allow" else word)
                n += 1
    build()
    return n


def reload() -> int:
    return load_custom(os.getenv("GUARD_AR_WORDS", "custom_words_ar.txt"))


# ═════════════════════════════ ПОДКЛЮЧЕНИЕ К guard.py ═════════════════════════════
_MY_HARD = {"ar_pitch_cta", "ar_families3", "ar_send_code", "ar_phone_words"}


def merge(a, text: str, g=None) -> None:
    """Добавляет арабские находки в результат guard.analyze_text (a — его Analysis)."""
    if not enabled() or not text:
        return
    F0 = text[:3000]
    if not (_ARL.search(F0) or re.search(r"[a-z]{3}|[а-я]{3}", F0.lower())):
        return
    urls = getattr(a, "urls", ()) or ()
    has_url = any(getattr(u, "kind", "allowed") != "allowed" for u in urls)
    r = analyze(text, has_url=has_url)
    if r.letters == 0 and not (r.found.prof or r.found.hate or r.found.adult or r.signals):
        return
    fnd = getattr(a, "found", None)
    if not isinstance(fnd, dict):
        fnd = a.found = {"prof": [], "hate": [], "adult": [], "minor": False}
    for k, vals in r.found.as_dict().items():
        if k == "minor":
            fnd["minor"] = bool(fnd.get("minor")) or bool(vals)
        else:
            cur = fnd.setdefault(k, [])
            cur.extend(v for v in vals if v not in cur)
    names = {s[0] for s in a.signals}
    for s in r.signals:
        if s[0] == "ar_phone" and "phone" in names:           # номер уже посчитал guard
            continue
        if s[0] not in names or s[0] == "ar_phone_words":
            a.signals.append(s)
    if _env_flag("GUARD_AR_NATIVE", True) and r.letters >= 10 and len(_OTHER_FOREIGN.findall(text)) < 10:
        a.signals[:] = [s for s in a.signals if s[0] != "foreign_script"]      # для арабского чата арабица — не «чужой алфавит»
    if r.phones:
        a.has_contact = True
        a.contacts = tuple(dict.fromkeys(list(getattr(a, "contacts", ()) or ()) + r.phones))[:8]
    hard = getattr(g, "HARD_SIGNALS", set()) if g is not None else set()
    a.raw = round(sum(w for _, w, _ in a.signals), 2)
    a.hard = round(sum(w for n, w, _ in a.signals if n in hard), 2)


def _find_guard():
    for name in ("__main__", "guard"):
        m = sys.modules.get(name)
        if m is not None and hasattr(m, "analyze_text") and hasattr(m, "HARD_SIGNALS"):
            return m
    return None


def install(g=None):
    """Подвешивает арабский модуль на analyze_text guard. Вызов: guard_ar.install(sys.modules[__name__])."""
    g = g or _find_guard()
    if g is None:
        raise RuntimeError("guard_ar.install: не нашёл модуль guard (нужен analyze_text и HARD_SIGNALS)")
    if getattr(g, "_guard_ar_installed", False):
        return g
    orig = g.analyze_text
    g.HARD_SIGNALS.update(_MY_HARD)

    def analyze_text(text, ents=(), cfg=None, fwd="", known_names=()):
        a = orig(text, ents, cfg, fwd, known_names)
        try:
            merge(a, text, g)
        except Exception:
            log.exception("guard_ar: сбой в арабском модуле (сообщение проверено без него)")
        return a
    analyze_text.__wrapped__ = orig
    g.analyze_text = analyze_text
    g._guard_ar_installed = True
    n = reload()
    log.info("арабский модуль %s: %s; правил %d (+%d арабизи); свои слова: %d; сезон сейчас: %s",
             VERSION, "включён" if enabled() else "выключен", len(RULES), len(AZ_SPAM), n, season() or "обычный")
    return g


# ═════════════════════════════ CLI / САМОПРОВЕРКА ═════════════════════════════
_BAD = [   # (текст, что должно найтись)
    ("يا ابن الكلب", "prof"), ("كس امك", "prof"), ("ياخي انت شرموطه", "prof"), ("كـــسـمك", "prof"), ("كسسسسس اختك", "prof"),
    ("ك س ا م ك", "prof"), ("ك.س.م.ك", "prof"), ("يا مَنْيُوك", "prof"), ("يا ابن المتناكه", "prof"), ("قحبة", "prof"),
    ("گحبه", "prof"), ("يلعن دينك", "prof"), ("نيكمك", "prof"), ("يا 3رص", "prof"), ("ياعرص", "prof"), ("كسم", "prof"),
    ("ك*س امك", "prof"), ("قحـ✨ـبة", "prof"), ("ش*رموطة", "prof"), ("sharmouta", "prof"), ("kos omak", "prof"), ("ya kalb", "prof"), ("ibn el sharmouta", "prof"), ("9a7ba", "prof"),
    ("шармута", "prof"), ("кус умак", "prof"), ("идите ибн аль кальб", "prof"),
    ("يا لوطي", "hate"), ("كلاب اليهود", "hate"), ("اقتلوا الشيعة", "hate"), ("ابناء القردة والخنازير", "hate"),
    ("زنجي وسخ", "hate"), ("هيل هتلر", "hate"), ("يا شاذ", "hate"), ("الموت للمسيحيين", "hate"),
    ("سكس عربي", "adult"), ("افلام سكس", "adult"), ("قنوات للكبار", "adult"), ("بورنو", "adult"), ("سكس اطفال", "adult+minor"),
    ("صور عاريات", "adult"), ("يا رافضي", "hate"), ("الروافض والمجوس", "hate"), ("اباحي 0501234567", "adult"), ("sks 3rby", "adult"),
]
_BAD_SPAM = [   # (текст, минимальная оценка ar-спама)
    ("اربح 500 دولار يوميا بدون راس مال، راسلني خاص", 4.0),
    ("فرصة عمل من المنزل، دخل اضافي ثابت. للتواصل واتساب 0501234567", 4.0),
    ("تمويل شخصي بدون كفيل وبدون تحويل راتب خلال ساعه، راسلنا واتساب", 4.0),
    ("ضاعف رصيدك في اسبوع! ارباح مضمونة 100%، تواصل معي في الخاص", 5.0),
    ("كازينو 1xbet بونص ترحيبي عند اول ايداع، بروموكود VIP", 4.0),
    ("ارسل لي الكود الذي وصلك على الواتس", 3.4),
    ("تم تعليق حسابك، سيتم حظر حسابك خلال 24 ساعه، تحقق من حسابك الان", 3.0),
    ("خدمات اختراق حسابات الواتساب والسناب، هكر محترف، راسلني خاص", 4.0),
    ("زيادة متابعين انستقرام وتيك توك، رشق لايكات رخيص، كلمني خاص", 3.5),
    ("حبوب الاجهاض سايتوتك متوفره توصيل سريع، تواصل واتساب", 3.5),
    ("بنات للتعارف بدون التزام، ارقام بنات واتساب، تواصل خاص", 4.0),
    ("شيخ روحاني جلب الحبيب وفك السحر، تواصل واتساب", 3.5),
    ("حل واجبات وبحوث ومشاريع تخرج بأسعار رخيصة، خاص", 3.0),
    ("0️⃣5️⃣0️⃣ صفر خمسة صفر واحد اثنين ثلاثة اربعة خمسة ستة، راسلني واتساب", 3.5),
    ("arba7 yawmiya bdon ra2s mal kalimni 3al khas", 3.5),
    ("تبرع للاسرة المحتاجة رقم الحساب IBAN SA00 تواصل واتساب", 2.0),
]
_GOOD = [   # обычный арабский — не должно быть ни находок, ни оценки ≥ 2.5
    "السلام عليكم ورحمة الله وبركاته", "كيف حالكم يا شباب؟ ان شاء الله بخير", "اريد شراء هاتف جديد، ما رايكم في سامسونج؟",
    "كسر الزجاج بالامس وتأخرت عن الدوام", "كسب الفريق المباراة بهدفين", "الكتاب جميل جدا شكرا لك", "هذا الكلام عاري عن الصحة تماما",
    "الطفل نائم الان لا تزعجوه", "رايحين المدرسة الابتدائية بكرة", "الاسعار ارتفعت هذا الشهر في السوق", "انا ابحث عن عمل مناسب لخبرتي",
    "ما رأيكم في كأس العالم؟ مين راح يفوز؟", "مبروك النجاح يا بطل، الله يوفقك", "شفت فيلم نيك جوناس امس", "فشخ يا باشا الاغنية دي جامد",
    "قال تعالى: ﴿ولا تقربوا الزنا﴾ صدق الله العظيم", "تعريف كلمة اباحي في القاموس", "خبر عاجل: وزارة الداخلية تعلن القبض على شبكة",
    "ما حكم السحر في الاسلام؟", "كزب الكذاب ولو صدق", "الرجاء ارسال رقم الطلب لنتابع معك", "السعر 50 ريال فقط للقطعة الواحدة",
    "تحياتي لكم من القاهرة، ازيك يا صاحبي؟", "شو اخبارك؟ كيفك اليوم؟ هلق وصلت", "لا تنسوا الصلاة على النبي صلى الله عليه وسلم",
    "الحمد لله على كل حال، نسأل الله العافية", "اجتماع الفريق الساعة العاشرة صباحا", "الراجحي فتح فرع جديد في الرياض",
    "يا زلمة شو هالحكي، ما بدي اروح", "الدولار ارتفع مقابل الجنيه اليوم", "عندي سؤال عن التقديم على الجامعة", "قصة نبي الله لوط في القران الكريم",
    "الله يرحمه ويغفر له", "الاباحية ليست حلا — مقال عن الاثار الاجتماعية", "نيكول كيدمان ممثلة رائعة", "راتب الوظيفة 8000 ريال شهريا حسب الخبرة", "الصفويين حكموا ايران قديما", "قناة الجزيرة نقلت الخبر", "اللاجئين السوريين في تركيا ضحايا الحرب",
]


def _check(text: str) -> dict:
    r = analyze(text)
    d = r.found.as_dict()
    return {"found": d, "spam": r.score, "signals": r.signals, "dialect": r.found.dialect, "season": r.season, "phones": r.phones}


def selftest(verbose: bool = False) -> int:
    bad = 0
    for t, want in _BAD:
        c = _check(t)["found"]
        ok = all(c[k] for k in want.split("+") if k != "minor") and (("minor" not in want) or c["minor"])
        if not ok:
            bad += 1
        if verbose or not ok:
            print(("OK  " if ok else "ПРОПУСК ") + t, c if not ok else "")
    for t, mn in _BAD_SPAM:
        c = _check(t)
        ok = c["spam"] >= mn
        if not ok:
            bad += 1
        if verbose or not ok:
            print(("OK  " if ok else "СЛАБО ") + t, c["spam"], [s[0] for s in c["signals"]] if not ok else "")
    for t in _GOOD:
        c = _check(t)
        ok = not any(c["found"][k] for k in ("prof", "hate", "adult")) and c["spam"] < 2.5
        if not ok:
            bad += 1
        if verbose or not ok:
            print(("OK  " if ok else "ЛОЖНОЕ ") + t, "" if ok else (c["found"], c["spam"], [s[0] for s in c["signals"]]))
    # проверки отдельных фишек
    extra = [
        ("хиджра: 2026-03-01 — Рамадан", season(1772323200) == "Рамадан"),
        ("хиджра: 2026-10-29 — обычный сезон", season(1793232000) == ""),
        ("диалект: левант", dialect_of(collapse(t) for t in _TOK.findall(ar_fold("شو كيفك هلق بدي روح"))) [0] == "L"),
        ("диалект: египет", dialect_of(collapse(t) for t in _TOK.findall(ar_fold("ازيك ايه ده عايز كده"))) [0] == "E"),
        ("щит не глушит жёсткую брань", bool(_check("قال تعالى كس امك")["found"]["prof"])),
        ("щит выключен, если в тексте ссылка/номер", bool(analyze("قال تعالى سكس 0501234567").found.adult)),
        ("числа прописью → контакт", bool(analyze("رقمي صفر خمسة صفر واحد اثنين ثلاثة اربعة خمسة ستة").phones)),
    ]
    for name, ok in extra:
        if not ok:
            bad += 1
        if verbose or not ok:
            print(("OK  " if ok else "ПРОВАЛ ") + name)
    total = len(_BAD) + len(_BAD_SPAM) + len(_GOOD) + len(extra)
    print("самопроверка: %d из %d пройдено%s" % (total - bad, total, "" if bad else " — всё хорошо"))
    return 1 if bad else 0


def cli(argv: list) -> int:
    if argv and argv[0] == "--selftest":
        return selftest("-v" in argv)
    if not argv:
        print(__doc__ or "python guard_ar.py \"текст\" | --selftest [-v]")
        return 0
    text = " ".join(argv)
    c = _check(text)
    print("нормализовано:", ar_fold(text))
    print("находки:", c["found"])
    print("диалект:", DIALECT_RU.get(c["dialect"], "—"), "· сезон:", c["season"] or "обычный")
    print("спам-оценка (арабская часть): %.2f" % c["spam"])
    for n, w, why in c["signals"]:
        print("   %-18s %5.2f  %s" % (n, w, why))
    return 0


if __name__ == "__main__":
    reload()
    raise SystemExit(cli(sys.argv[1:]))
