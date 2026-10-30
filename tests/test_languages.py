"""Языковые модули guard: es / de / ar / zh подключаются сами и работают вместе.

Запуск:  python -m unittest discover -s tests -t .
aiogram и токен не нужны: если aiogram не установлен, подставляется заглушка (только для импорта guard.py).
"""
import os
import sys
import types
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)


def _stub_aiogram() -> None:
    try:
        import aiogram  # noqa: F401
        return
    except ImportError:
        pass

    def mod(name: str, **attrs):
        m = types.ModuleType(name)
        m.__dict__.update(attrs)
        sys.modules[name] = m
        return m

    class _Any:
        def __init__(self, *a, **k):
            pass

    err = type("TelegramAPIError", (Exception,), {})
    mod("aiogram", BaseMiddleware=_Any, Bot=_Any, Dispatcher=_Any, Router=_Any)
    mod("aiogram.client")
    mod("aiogram.client.default", DefaultBotProperties=_Any)
    mod("aiogram.enums", ParseMode=type("ParseMode", (), {"HTML": "HTML"}))
    mod("aiogram.exceptions", TelegramAPIError=err,
        **{n: type(n, (err,), {}) for n in ("TelegramBadRequest", "TelegramForbiddenError", "TelegramNetworkError",
                                            "TelegramRetryAfter", "TelegramServerError")})
    mod("aiogram.filters", Command=_Any)
    mod("aiogram.types", ChatPermissions=_Any)


_stub_aiogram()
import guard  # noqa: E402

LANGS = ["es", "de", "ar", "zh"]

# (язык, текст, категория, которая должна найтись)
PROFANITY = [
    ("es", "eres un hijo de puta", "prof"),
    ("de", "Du Hurensohn", "prof"),
    ("ar", "يا ابن الكلب", "prof"),
    ("zh", "你妈死了 傻逼", "prof"),
]
# (язык, текст) — оценка спама не ниже порога «наблюдать»
SPAM = [
    ("es", "gana 500 dolares al dia, escribeme al privado"),
    ("de", "Nebenverdienst 500 Euro am Tag, schreib mir privat"),
    ("ar", "اربح 500 دولار يوميا بدون راس مال، راسلني خاص"),
    ("zh", "招聘兼职，日结300-800，手机在家就能做，无需押金，加微信 abc12345"),
]
CLEAN = [
    "hola, ¿cómo estás? computadora Vergara",
    "Guten Morgen, wie geht's? Marsch Barsch Fagott",
    "مرحبا كيف حالك اليوم",
    "今天天气真好，我们一起去公园玩吧",
    "привет всем, как дела",
    "hello everyone",
]


def analyze(text: str):
    return guard.analyze_text(text, (), guard.ChatCfg())


class LanguagesTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.installed = guard.install_languages()

    def test_all_languages_installed(self):
        self.assertEqual(self.installed, LANGS)

    def test_install_is_idempotent(self):
        self.assertEqual(guard.install_languages(), LANGS)

    def test_profanity_caught(self):
        for lang, text, cat in PROFANITY:
            with self.subTest(lang=lang):
                self.assertTrue(analyze(text).found[cat], text)

    def test_spam_scored(self):
        for lang, text in SPAM:
            with self.subTest(lang=lang):
                self.assertGreaterEqual(analyze(text).raw, 4.0, text)

    def test_clean_text_untouched(self):
        for text in CLEAN:
            with self.subTest(text=text):
                a = analyze(text)
                self.assertEqual(a.raw, 0, text)
                self.assertFalse(any(v for v in a.found.values()), text)

    def test_russian_still_works(self):
        self.assertGreaterEqual(analyze("заработок 500$ в день, пиши в личку").raw, 4.0)


class SwitchesTest(unittest.TestCase):
    def test_langs_wanted(self):
        w = guard._langs_wanted
        self.assertEqual(w({}), LANGS)
        self.assertEqual(w({"GUARD_LANGS": "all"}), LANGS)
        self.assertEqual(w({"GUARD_LANGS": "es, de"}), ["es", "de"])
        self.assertEqual(w({"GUARD_LANGS": "zh;ar"}), ["ar", "zh"])
        self.assertEqual(w({"GUARD_LANGS": "off"}), [])
        self.assertEqual(w({"GUARD_LANGS": "0"}), [])


class SelftestsTest(unittest.TestCase):
    """У модулей есть свои встроенные самопроверки — гоняем их тоже."""

    def test_es(self):
        import guard_es
        self.assertEqual(guard_es._selftest(), 0)

    def test_ar(self):
        import guard_ar
        self.assertEqual(guard_ar.selftest(), 0)

    def test_zh(self):
        import guard_zh
        self.assertEqual(guard_zh.selftest(), 0)


if __name__ == "__main__":
    unittest.main()
