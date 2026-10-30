# guard

Telegram-бот-сторож для чатов: антиспам, антимат, защита от рейдов и мошенников. Python + [aiogram 3](https://docs.aiogram.dev/).

> **EN:** a self-hosted Telegram moderation bot (anti-spam, anti-scam, captcha, raid protection, self-learning).
> Built-in Russian and English; Spanish, German, Arabic and Chinese are separate drop-in modules that load automatically.

## Что умеет

- **Фильтры:** мат, оскорбления, ненависть, 18+ и «18+ рядом с детской темой» — с учётом обходов (замены букв, разрядка, маски, «лит»).
- **Спам и скам:** правила с весами и комбинациями («предложение + призыв писать в личку»), фишинг и поддельные ссылки, проверка контактов и реквизитов.
- **Вход в чат:** капча, сверка с базой спамеров CAS, обработка заявок на вход.
- **Волны:** «строгий режим», «полная защита» (`/fullguard`, `/panic`), автопилот, «Следопыт», «кукольный театр» (постановочные диалоги подставных аккаунтов).
- **Самообучение:** карточки «спам / нормально» владельцу, уроки из реакций и команд, память о пойманном спаме.
- **«Дела»:** каждое наказание — запись с уликами; владелец может отменить, автор — подать апелляцию.
- **Команды модерации:** `/warn /mute /ban /purge`, `/remind`, `/repeat`, `/stats`, `/explain` и другие (список — `/help`).
- **Мост с игрой** (по желанию): включается, только если задан `GUARD_SECRET`.

## Быстрый старт

```bash
git clone <ссылка на ваш репозиторий>
cd guard
pip install -r requirements.txt

cp .env.example .env        # впишите GUARD_BOT_TOKEN и GUARD_ADMIN_IDS
python guard.py --check     # проверка настроек без запуска бота
python guard.py             # запуск
```

1. Создайте **отдельного** бота у [@BotFather](https://t.me/BotFather) и вставьте его токен в `GUARD_BOT_TOKEN`.
2. Свой числовой id узнайте командой `/id` в личке с ботом и впишите в `GUARD_ADMIN_IDS` — только эти люди управляют ботом (права админа в самом чате ничего не значат).
3. Добавьте бота в чат и дайте права администратора (удаление сообщений, ограничение и бан участников).

Нужен Python 3.10+. Актуальный шаблон настроек всегда можно получить командой `python guard.py --env-example`.

## Языки

Русский и английский встроены в `guard.py`. Остальные языки — отдельные файлы рядом с `guard.py`; бот подхватывает их сам, ничего править не нужно.

| Язык | Файл | Что ловит |
|---|---|---|
| Испанский | `guard_es.py` | мат (с режимом «друзей» для Латинской Америки), ненависть, 18+, спам и скам, реквизиты (IBAN, CLABE, CBU) |
| Немецкий | `guard_de.py` | составные слова, умляуты, спам и скам (Nebenverdienst, Finanzagent, DHL/Sparkasse-фишинг), проверка IBAN |
| Арабский | `guard_ar.py` | огласовки, татвиль, диалекты, арабизи (латиницей), спам и скам |
| Китайский | `guard_zh.py` | пиньинь-аббревиатуры, омофоны, традиционное письмо, 刷单 / 杀猪盘 / 跑分 и жаргон чёрных рынков |

Настройки в `.env`:

```ini
GUARD_LANGS=all        # all — все найденные; "es,de" — только эти; off — никакие
GUARD_ES=0             # выключить один язык (так же GUARD_DE, GUARD_AR, GUARD_ZH)
```

Удалите файл `guard_xx.py` — язык просто не подключится, бот продолжит работать. Сбой в одном языковом модуле не влияет на остальные. Что подключилось, видно в логе при старте (`языки: es, de, ar, zh`) и в `python guard.py --check`.

Проверить текст вручную, без Telegram:

```bash
python guard_es.py --check "gana 500 dolares al dia, escribeme al privado"
python guard_de.py --explain "Nebenverdienst 500 Euro am Tag, schreib mir privat"
python guard_ar.py "اربح 500 دولار يوميا، راسلني خاص"
python guard_zh.py --zh-check "加V领彩金 日结500"
```

Самопроверка модулей: `python guard_es.py --selftest`, `python guard_ar.py --selftest`, `python guard_zh.py --zh-selftest`.

### Свои слова

Скопируйте `custom_words.example.txt` в `custom_words.txt`. Строки вида `prof: слово`, `hate:`, `adult:`, `allow:` (исключение); `=слово` — только точное совпадение. Работает для всех языков, у арабского есть ещё `custom_words_ar.txt`.

## Расширения

`guard5.py` (5.0) и `guard6.py` (6.0) лежат рядом с `guard.py` и подхватываются сами. `GUARD5=0` / `GUARD6=0` выключают их целиком, остальные переключатели — в `.env.example`.

## Тесты

```bash
python -m unittest discover -s tests -t .
```

Для тестов aiogram и токен не нужны.

## Что не коммитить

`.env` (токен и секреты), `guard_state.json`, `guard_vault.db` — всё это уже в `.gitignore`. Если токен когда-либо попал в репозиторий, перевыпустите его в @BotFather.

## Структура

```
guard.py            ядро бота
guard5.py guard6.py расширения 5.0 и 6.0
guard_es.py guard_de.py guard_ar.py guard_zh.py   языковые модули
tests/              тесты
.env.example        шаблон настроек
```

## Лицензия

Все права защищены. Копировать, изменять и распространять код без разрешения автора нельзя.
