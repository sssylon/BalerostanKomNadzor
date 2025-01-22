# BalKomNadzor Bot

Telegram бот для модерации групп с расширенными возможностями управления контентом.

## Требования

- Python 3.12.8
- pip (последняя версия)

## Установка

1. Клонируйте репозиторий:
```bash
git clone https://github.com/your-username/BalKomNadzor.git
cd BalKomNadzor
```

2. Создайте виртуальное окружение и активируйте его:
```bash
python -m venv venv
# Windows
venv\Scripts\activate
# Linux/macOS
source venv/bin/activate
```

3. Установите зависимости:
```bash
pip install -r requirements.txt
```

4. Создайте файл .env на основе example.env и заполните его своими данными:
```bash
cp example.env .env
```

## Настройка

1. Получите токен бота у @BotFather
2. Заполните .env файл:
   - BOT_TOKEN: токен вашего бота
   - BOT_ID: ID вашего бота
   - MAIN_GROUP: ID основной группы
   - MONITORED_GROUPS: ID групп через запятую
   - ADMIN_IDS: ID администраторов через запятую
   - SPECIAL_SEND_USER: ID пользователя с правом на команду send

## Запуск

```bash
python bot.py
```

## Основные команды

- /tts - Преобразование текста в голосовое сообщение (поддерживает русский, украинский, английский и польский языки)
- /warn - Выдача предупреждения пользователю
- /warns - Проверка количества предупреждений
- /gifmute - Запрет на отправку GIF/стикеров
- /unmute - Снятие ограничений
- /uamode - Включение режима проверки украинского языка
- /bind - Привязка команды к стикеру или GIF
- /binds - Просмотр активных привязок

## Лицензия

MIT 