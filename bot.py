import asyncio
import logging
import sys
import re
import json
import os
import signal
import time
from datetime import datetime, timedelta
from typing import Dict, Optional, List, Set, Tuple, Union

from aiogram import Bot, Dispatcher, types, F
from aiogram.filters import Command
from aiogram.types import InlineKeyboardButton, InlineKeyboardMarkup, FSInputFile
from gtts import gTTS
import tempfile
from lingua import Language, LanguageDetectorBuilder
from dotenv import load_dotenv

# Загружаем переменные окружения
load_dotenv()

# Настройка логирования
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Создаем детектор языка
language_detector = LanguageDetectorBuilder.from_languages(
    Language.RUSSIAN,
    Language.UKRAINIAN,
    Language.ENGLISH,
    Language.POLISH
).with_minimum_relative_distance(0.25).build()

# Флаг для отслеживания состояния бота
is_running = True

# Обработчики сигналов
def signal_handler(signum, frame):
    """Обработчик сигналов для корректного завершения"""
    global is_running
    logger.info("Получен сигнал завершения, останавливаем бота...")
    is_running = False

# Регистрируем обработчики сигналов
signal.signal(signal.SIGINT, signal_handler)
signal.signal(signal.SIGTERM, signal_handler)

# Константы из переменных окружения
TOKEN = os.getenv("BOT_TOKEN")
BOT_ID = int(os.getenv("BOT_ID"))
MAIN_GROUP = int(os.getenv("MAIN_GROUP"))
MONITORED_GROUPS = {int(group_id) for group_id in os.getenv("MONITORED_GROUPS").split(",")}
ADMIN_IDS = {int(admin_id) for admin_id in os.getenv("ADMIN_IDS").split(",")}
SPECIAL_SEND_USER = int(os.getenv("SPECIAL_SEND_USER"))

# Определяем, запущен ли бот на Python Anywhere
is_pythonanywhere = os.getenv("PYTHONANYWHERE", "false").lower() == "true"

# Пути к файлам данных
WARNINGS_FILE = "warnings.json"
MUTE_HISTORY_FILE = "mute_history.json"
FORBIDDEN_CONTENT_FILE = "forbidden_content.json"
BOT_MUTE_FILE = "bot_mute.json"
BINDS_FILE = "binds.json"  # Файл для хранения биндов

# Хранилище активных голосований: vote_id -> (set of voters, message_id, chat_id, end_time)
active_votes: Dict[str, Tuple[Set[int], int, int, datetime]] = {}

# Хранилище для отслеживания флуда: chat_id -> {user_id -> {"messages": [(timestamp, message_id)], "last_long_msg": (timestamp, message_id)}}
flood_history: Dict[int, Dict[int, Dict[str, Union[List[Tuple[float, int]], Optional[Tuple[float, int]]]]]] = {}

# Хранилище сообщений, отправленных через /send
sent_messages: Set[int] = set()

# Хранилище для отслеживания команд: user_id -> [(timestamp, command)]
command_history: Dict[int, List[Tuple[float, str]]] = {}

# Хранилище биндов: content_id -> command
binds: Dict[str, str] = {}

# Глобальные объекты бота и диспетчера
bot: Optional[Bot] = None
dp = Dispatcher()

# Добавляем после других глобальных переменных
last_tts_use: Dict[int, float] = {}  # ID пользователя -> время последнего использования

# Глобальная переменная для хранения запрещенного контента
forbidden_content: Dict[str, Dict] = {}

# Глобальные переменные
bot_start_time: float = 0  # Время запуска бота

# После других глобальных переменных
links_mode_counter: Optional[int] = None  # Счетчик для режима ссылок

# Состояние украинского режима: chat_id -> end_time
ua_mode: Dict[int, datetime] = {}

# Функции для работы с JSON
def load_data() -> tuple[Dict[int, int], Dict[int, int]]:
    warnings = {}
    mute_history = {}
    
    try:
        if os.path.exists(WARNINGS_FILE):
            with open(WARNINGS_FILE, 'r', encoding='utf-8') as f:
                warnings = {int(k): v for k, v in json.load(f).items()}
    except Exception as e:
        logger.error(f"Ошибка при загрузке предупреждений: {e}")

    try:
        if os.path.exists(MUTE_HISTORY_FILE):
            with open(MUTE_HISTORY_FILE, 'r', encoding='utf-8') as f:
                mute_history = {int(k): v for k, v in json.load(f).items()}
    except Exception as e:
        logger.error(f"Ошибка при загрузке истории мутов: {e}")

    return warnings, mute_history

def save_warnings(data: Dict[int, int]):
    try:
        with open(WARNINGS_FILE, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logger.error(f"Ошибка при сохранении предупреждений: {e}")

def save_mute_history(data: Dict[int, int]):
    try:
        with open(MUTE_HISTORY_FILE, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logger.error(f"Ошибка при сохранении истории мутов: {e}")

def load_forbidden_content():
    """Загружает список запрещенного контента"""
    global forbidden_content
    try:
        if os.path.exists(FORBIDDEN_CONTENT_FILE):
            with open(FORBIDDEN_CONTENT_FILE, 'r', encoding='utf-8') as f:
                forbidden_content = json.load(f)
    except Exception as e:
        logger.error(f"Ошибка при загрузке списка запрещенного контента: {e}")

def save_forbidden_content():
    """Сохраняет список запрещенного контента"""
    try:
        with open(FORBIDDEN_CONTENT_FILE, 'w', encoding='utf-8') as f:
            json.dump(forbidden_content, f, indent=2, ensure_ascii=False)
    except Exception as e:
        logger.error(f"Ошибка при сохранении списка запрещенного контента: {e}")

def get_content_id(message: types.Message) -> Optional[str]:
    """Получает уникальный идентификатор контента"""
    if message.animation:
        return f"gif_{message.animation.file_unique_id}"
    elif message.sticker:
        return f"sticker_{message.sticker.file_unique_id}"
    return None

# Загружаем данные при запуске
warnings, mute_history = load_data()
load_forbidden_content()
bot_muted_users: Dict[int, int] = {}

# Загружаем список запрещенного контента при запуске
load_forbidden_content()

# Регистрируем команду TTS первой
@dp.message(Command("tts", ignore_case=True))
async def text_to_speech(message: types.Message):
    """Преобразует текст в голосовое сообщение"""
    global bot
    logger.info(f"Получена команда TTS от пользователя {message.from_user.id}")
    
    # Проверяем кулдаун для обычных пользователей
    if not is_admin(message.from_user.id):
        current_time = time.time()
        last_use = last_tts_use.get(message.from_user.id, 0)
        if current_time - last_use < 60:  # 60 секунд кулдаун
            remaining = int(60 - (current_time - last_use))
            await message.reply(f"Подождите {remaining} секунд перед следующим использованием команды")
            return
        last_tts_use[message.from_user.id] = current_time
    
    # Получаем текст для озвучивания
    text = None
    
    # Если это ответ на сообщение
    if message.reply_to_message:
        if message.reply_to_message.caption:
            text = message.reply_to_message.caption
        elif message.reply_to_message.text:
            text = message.reply_to_message.text
    # Если текст указан после команды
    else:
        args = message.text.split(maxsplit=1)
        if len(args) > 1:
            text = args[1]
    
    # Если текст не найден
    if not text:
        await bot.send_message(
            chat_id=message.chat.id,
            text="Использование:\n/tts [текст] - озвучить указанный текст\nили используйте команду в ответ на сообщение с текстом\n\nПоддерживаемые языки: русский, украинский, английский, польский",
            reply_to_message_id=message.message_id
        )
        return
        
    logger.info(f"Получен текст для озвучивания: {text}")
    
    try:
        # Определяем язык текста с помощью lingua
        try:
            detected_language = language_detector.detect_language_of(text)
            confidence_values = language_detector.compute_language_confidence_values(text)
            confidence = next((conf for lang, conf in confidence_values if lang == detected_language), 0)
            
            logger.info(f"Определен язык текста: {detected_language} с уверенностью {confidence:.2f}")
            
            # Словарь соответствия языков для gTTS
            lang_map = {
                Language.RUSSIAN: 'ru',
                Language.UKRAINIAN: 'uk',
                Language.ENGLISH: 'en',
                Language.POLISH: 'pl'
            }
            
            # Проверяем уверенность определения языка
            if confidence < 0.5 or detected_language is None:
                logger.info("Низкая уверенность в определении языка или язык не определен, используем русский")
                lang = 'ru'
            else:
                lang = lang_map.get(detected_language, 'ru')
                
        except Exception as e:
            logger.error(f"Ошибка при определении языка: {e}")
            logger.info("Используем русский язык по умолчанию")
            lang = 'ru'
            
        logger.info(f"Выбран язык для озвучки: {lang}")
        
        logger.info("Начинаем преобразование текста в речь")
        # Создаем временный файл для сохранения аудио
        with tempfile.NamedTemporaryFile(suffix='.mp3', delete=False) as temp_file:
            # Преобразуем текст в речь
            tts = gTTS(text=text, lang=lang)
            tts.save(temp_file.name)
            logger.info("Аудио файл создан")
            
            # Отправляем голосовое сообщение
            try:
                with open(temp_file.name, 'rb') as audio:
                    await bot.send_voice(
                        chat_id=message.chat.id,
                        voice=FSInputFile(temp_file.name),
                        reply_to_message_id=message.message_id
                    )
            except Exception as e:
                logger.error(f"Ошибка при отправке голосового сообщения: {e}")
                await bot.send_message(
                    chat_id=message.chat.id,
                    text="Не удалось отправить голосовое сообщение",
                    reply_to_message_id=message.message_id
                )
                
        # Удаляем временный файл
        try:
            os.unlink(temp_file.name)
        except Exception as e:
            logger.error(f"Ошибка при удалении временного файла: {e}")
            
    except Exception as e:
        logger.error(f"Ошибка при создании голосового сообщения: {e}")
        await bot.send_message(
            chat_id=message.chat.id,
            text="Не удалось преобразовать текст в речь",
            reply_to_message_id=message.message_id
        )

@dp.message(Command("uamode", ignore_case=True))
async def ua_mode_command(message: types.Message):
    """Включает режим проверки украинского языка"""
    global bot
    
    try:
        logger.info(f"Пользователь {message.from_user.first_name} вызвал /uamode в группе {message.chat.title} ({message.chat.id})")
        
        # Проверяем права администратора
        if not is_admin(message.from_user.id):
            logger.info(f"Отказано в доступе пользователю {message.from_user.id}")
            try:
                await message.delete()
            except Exception as e:
                logger.error(f"Ошибка при удалении команды: {e}")
            return

        # Проверяем, что команда использована в группе
        if message.chat.id not in MONITORED_GROUPS:
            logger.info(f"Попытка использовать команду в нецелевом чате {message.chat.id}")
            await message.reply("Эта команда работает только в отслеживаемых группах.")
            return

        # Получаем время действия режима
        args = message.text.split()
        if len(args) != 2:
            logger.info("Неверный формат команды")
            await message.reply("Использование: /uamode <время>\nПримеры: 30m, 1h, 1d")
            return

        time_str = args[1].lower()
        logger.info(f"Получено значение времени: {time_str}")
        
        # Парсим время
        match = re.match(r'^(\d+)([mhd])$', time_str)
        if not match:
            logger.info(f"Неверный формат времени: {time_str}")
            await message.reply("Неверный формат времени. Примеры: 30m, 1h, 1d")
            return
            
        amount = int(match.group(1))
        unit = match.group(2)
        logger.info(f"Распознано: количество = {amount}, единица = {unit}")
        
        # Конвертируем в минуты
        duration = 0
        if unit == 'm':
            duration = amount
        elif unit == 'h':
            duration = amount * 60
        elif unit == 'd':
            duration = amount * 24 * 60
            
        logger.info(f"Вычислена длительность: {duration} минут")
            
        if duration <= 0:
            logger.info("Получено неположительное значение времени")
            await message.reply("Время должно быть положительным числом.")
            return
            
        # Проверяем максимальное время (7 дней)
        if duration > 7 * 24 * 60:
            logger.info("Превышено максимальное время")
            await message.reply("Максимальное время - 7 дней.")
            return

        # Устанавливаем время окончания режима
        ua_mode[message.chat.id] = datetime.now() + timedelta(minutes=duration)
        logger.info(f"Установлено время окончания режима: {ua_mode[message.chat.id]}")
        
        # Форматируем сообщение о включении режима
        if unit == 'm':
            time_text = f"{amount} хвилин"
        elif unit == 'h':
            time_text = f"{amount} годин"
        else:
            time_text = f"{amount} днів"
        
        logger.info("Отправляем сообщение об активации режима")
        try:
            await message.reply(f"В ЧАТІ ДІЄ РЕЖИМ НАСТУПАЛЬНОЇ УКРАЇНІЗАЦІЇ НА {time_text}! 🇺🇦")
            logger.info(f"Украинский режим активирован в чате {message.chat.id} на {duration} минут")
        except Exception as e:
            logger.error(f"Ошибка при отправке сообщения об активации: {e}")
            
    except Exception as e:
        logger.error(f"Общая ошибка в обработчике uamode: {e}")
        try:
            await message.reply("Произошла ошибка при обработке команды.")
        except:
            pass

def is_admin(user_id: int) -> bool:
    """Проверяет, является ли пользователь администратором"""
    return user_id in ADMIN_IDS

def can_be_restricted(user_id: int) -> bool:
    """Проверяет, можно ли ограничить пользователя"""
    # Нельзя ограничивать админов и самого бота
    return not (is_admin(user_id) or user_id == BOT_ID)

async def issue_warning(chat_id: int, target_user: types.User) -> str:
    """Выдает предупреждение пользователю и возвращает текст сообщения"""
    if not can_be_restricted(target_user.id):
        return "Этого пользователя нельзя предупредить"

    warnings[target_user.id] = warnings.get(target_user.id, 0) + 1
    warn_count = warnings[target_user.id]
    response = f"Выдано предупреждение пользователю {target_user.full_name}. Всего предупреждений: {warn_count}"

    if warn_count >= 3:
        # Вычисляем длительность мута
        last_mute_duration = mute_history.get(target_user.id, 300)  # 5 минут базовый мут
        new_mute_duration = last_mute_duration * 2
        mute_history[target_user.id] = new_mute_duration
        save_mute_history(mute_history)

        # Сразу обнуляем варны
        warnings[target_user.id] = 0
        save_warnings(warnings)

        until_date = datetime.now() + timedelta(seconds=new_mute_duration)
        
        try:
            await bot.restrict_chat_member(
                chat_id=chat_id,
                user_id=target_user.id,
                permissions=types.ChatPermissions(
                    can_send_messages=True,
                    can_send_media_messages=True,
                    can_send_other_messages=False
                ),
                until_date=until_date
            )
            # Изменяем текст сообщения в зависимости от длительности
            if new_mute_duration < 3600:  # меньше часа
                duration_text = f"{new_mute_duration // 60} минут"
            elif new_mute_duration < 86400:  # меньше суток
                duration_text = f"{new_mute_duration // 3600} часов"
            else:  # сутки и больше
                duration_text = f"{new_mute_duration // 86400} дней"
            
            response += f"\nДостигнуто 3 предупреждения. Варны обнулены.\nПользователь ограничен в отправке стикеров и GIF на {duration_text}"
            
        except Exception as e:
            logger.error(f"Ошибка при ограничении пользователя: {e}")
            response += f"\nОшибка при попытке ограничить пользователя: {str(e)}"
    else:
        save_warnings(warnings)

    return response

async def end_vote(vote_id: str, chat_id: int, message_id: int, reason: str):
    """Завершает голосование и обновляет сообщение"""
    if vote_id in active_votes:
        try:
            await bot.edit_message_text(
                chat_id=chat_id,
                message_id=message_id,
                text=f"Голосование завершено\n\n**{reason}**",
                reply_markup=None  # Убираем кнопку после завершения
            )
        except Exception as e:
            logger.error(f"Ошибка при завершении голосования: {e}")
        finally:
            if vote_id in active_votes:
                # Удаляем сообщения, если они есть
                _, _, _, _, messages_to_delete = active_votes[vote_id]
                for msg_id in messages_to_delete:
                    try:
                        await bot.delete_message(chat_id, msg_id)
                        logger.info(f"Удалено сообщение {msg_id} при завершении голосования")
                    except Exception as e:
                        logger.error(f"Ошибка при удалении сообщения {msg_id}: {e}")
                del active_votes[vote_id]

async def check_vote_expiration():
    """Проверяет истекшие голосования"""
    while is_running:  # Используем глобальный флаг для корректного завершения
        try:
            current_time = datetime.now()
            to_remove = []
            
            for vote_id, (voters, message_id, chat_id, end_time, _) in active_votes.items():
                if current_time >= end_time:
                    # Если время истекло, завершаем голосование
                    try:
                        await bot.edit_message_text(
                            chat_id=chat_id,
                            message_id=message_id,
                            text=f"Голосование закончено\n\n**Это голосование уже закончено**",
                            reply_markup=None
                        )
                    except Exception as e:
                        logger.error(f"Ошибка при завершении голосования: {e}")
                    finally:
                        to_remove.append(vote_id)
            
            # Удаляем завершенные голосования
            for vote_id in to_remove:
                if vote_id in active_votes:
                    del active_votes[vote_id]
                
        except Exception as e:
            logger.error(f"Ошибка при проверке истекших голосований: {e}")
            
        await asyncio.sleep(10)  # Проверяем каждые 10 секунд

@dp.message(Command("votewarn"))
async def votewarn_command(message: types.Message):
    if is_bot_muted(message.from_user.id):
        logger.info(f"Пользователь {message.from_user.id} пытается использовать votewarn, но находится в botmute")
        return
        
    # Проверяем, что команда использована в отслеживаемой группе или в ЛС админом
    if message.chat.type != 'private' and message.chat.id not in MONITORED_GROUPS:
        logger.info(f"Попытка использовать votewarn в неотслеживаемой группе {message.chat.id}")
        try:
            await message.delete()
        except Exception as e:
            logger.error(f"Ошибка при удалении команды votewarn: {e}")
        return
    
    # Если это ЛС, проверяем что пользователь админ
    if message.chat.type == 'private' and not is_admin(message.from_user.id):
        logger.info(f"Попытка использовать votewarn в ЛС неадмином {message.from_user.id}")
        return

    if not message.reply_to_message:
        logger.info(f"Пользователь {message.from_user.id} пытается использовать votewarn без ответа на сообщение")
        await message.reply("Эта команда должна быть ответом на сообщение пользователя")
        return

    target_user = message.reply_to_message.from_user
    initiator = message.from_user
    
    logger.info(f"Инициировано голосование за варн:")
    logger.info(f"- Инициатор: {initiator.full_name} (ID: {initiator.id})")
    logger.info(f"- Цель: {target_user.full_name} (ID: {target_user.id})")
    
    if target_user.id == initiator.id:
        logger.info(f"Пользователь {initiator.full_name} пытается голосовать за предупреждение самому себе")
        await message.reply("Вы не можете голосовать за предупреждение самому себе")
        return
        
    if not can_be_restricted(target_user.id):
        logger.info(f"Попытка выдать предупреждение защищенному пользователю {target_user.full_name}")
        await message.reply("Этого пользователя нельзя предупредить")
        return

    content_description = get_content_description(message.reply_to_message)
    logger.info(f"- Тип контента: {content_description}")
    
    vote_id = f"vote_{message.chat.id}_{target_user.id}_{int(datetime.now().timestamp())}"
    
    # Создаем новое голосование с временем окончания через час
    vote_msg = await message.reply(
        f"Пользователь {initiator.full_name} предлагает выдать варн {target_user.full_name}\n"
        f"Содержание сообщения: {content_description}\n"
        f"Голосов: 1/2\n\n"
        f"Нужен ещё один голос",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="Да ✅", callback_data=f"votewarn_{vote_id}")
        ]])
    )
    
    # Сохраняем информацию о голосовании
    active_votes[vote_id] = (
        {initiator.id},  # Добавляем инициатора в список проголосовавших
        vote_msg.message_id,
        message.chat.id,
        datetime.now() + timedelta(hours=1),
        []  # Пустой список сообщений для удаления
    )
    logger.info(f"Создано голосование ID: {vote_id}")
    logger.info(f"- Сообщение ID: {vote_msg.message_id}")
    logger.info(f"- Чат ID: {message.chat.id}")
    logger.info(f"- Время окончания: {datetime.now() + timedelta(hours=1)}")
    logger.info(f"- Голос инициатора уже учтен")

@dp.callback_query(lambda c: c.data.startswith('votewarn_'))
async def handle_votewarn(callback: types.CallbackQuery):
    vote_id = callback.data.split('_', 1)[1]
    logger.info(f"Получен голос в голосовании {vote_id}")
    logger.info(f"- От пользователя: {callback.from_user.full_name} (ID: {callback.from_user.id})")
    
    if vote_id not in active_votes:
        logger.info(f"Попытка проголосовать в завершенном голосовании {vote_id}")
        await callback.answer("Это голосование уже закончено", show_alert=True)
        return
    
    voters, message_id, chat_id, end_time, messages_to_delete = active_votes[vote_id]
    logger.info(f"- Текущее количество голосов: {len(voters)}")
    
    # Проверяем, не истекло ли время
    if datetime.now() >= end_time:
        logger.info(f"Голосование {vote_id} завершено по истечению времени")
        await end_vote(vote_id, chat_id, message_id, "Голосование завершено: время истекло")
        await callback.answer("Это голосование уже закончено", show_alert=True)
        return
    
    # Проверяем, не голосовал ли пользователь уже
    if callback.from_user.id in voters:
        logger.info(f"Повторная попытка голосования от пользователя {callback.from_user.full_name}")
        await callback.answer("Вы уже участвовали в этом голосовании", show_alert=True)
        return
    
    # Добавляем голос
    voters.add(callback.from_user.id)
    logger.info(f"Добавлен голос от пользователя {callback.from_user.full_name}")
    
    # Получаем информацию о целевом пользователе из vote_id
    _, chat_id, target_user_id, _ = vote_id.split('_')
    chat_id, target_user_id = int(chat_id), int(target_user_id)
    
    # Если набралось 2 голоса (включая инициатора)
    if len(voters) >= 2:
        try:
            target_user = await bot.get_chat_member(chat_id, target_user_id)
            warning_result = await issue_warning(chat_id, target_user.user)
            logger.info(f"Выдано предупреждение пользователю {target_user.user.full_name}")
            logger.info(f"- Результат: {warning_result}")
            
            # Удаляем сообщения только после успешного голосования
            for msg_id in messages_to_delete:
                try:
                    await bot.delete_message(chat_id, msg_id)
                    logger.info(f"Удалено сообщение {msg_id} после успешного голосования")
                except Exception as e:
                    logger.error(f"Ошибка при удалении сообщения {msg_id}: {e}")
            
            await end_vote(vote_id, chat_id, message_id, f"Голосование завершено!\n{warning_result}")
            
        except Exception as e:
            logger.error(f"Ошибка при выдаче предупреждения: {e}")
            await callback.answer("Произошла ошибка при выдаче предупреждения", show_alert=True)
    else:
        # Обновляем сообщение с текущим количеством голосов
        try:
            await bot.edit_message_text(
                chat_id=chat_id,
                message_id=message_id,
                text=f"Голосование за варн продолжается\nГолосов: {len(voters)}/2",
                reply_markup=callback.message.reply_markup
            )
        except Exception as e:
            logger.error(f"Ошибка при обновлении сообщения голосования: {e}")
        
        await callback.answer("Ваш голос учтен")

@dp.message(Command("warn", ignore_case=True))
async def warn_command(message: types.Message):
    """Выдает предупреждение пользователю"""
    global bot
    logger.info(f"Получена команда warn от пользователя {message.from_user.id}")
    
    # Проверяем права администратора
    if not is_admin(message.from_user.id):
        logger.info(f"Отказано в доступе пользователю {message.from_user.id}")
        try:
            await message.delete()
        except Exception as e:
            logger.error(f"Ошибка при удалении команды: {e}")
        return
    
    # Проверяем, что команда использована в отслеживаемой группе
    if message.chat.id not in MONITORED_GROUPS:
        logger.info(f"Попытка использовать warn в неотслеживаемой группе {message.chat.id}")
        try:
            await message.delete()
        except Exception as e:
            logger.error(f"Ошибка при удалении команды warn: {e}")
        return
    
    # Проверяем что это ответ на сообщение
    if not message.reply_to_message:
        await message.reply("Эта команда должна быть ответом на сообщение пользователя")
        return
    
    target_user = message.reply_to_message.from_user
    
    # Проверяем, можно ли выдать предупреждение пользователю
    if not can_be_restricted(target_user.id):
        await message.reply("Этого пользователя нельзя предупредить")
        return
    
    # Получаем причину предупреждения
    args = message.text.split(maxsplit=1)
    reason = args[1] if len(args) > 1 else "не указана"
    
    # Выдаем предупреждение
    warnings[target_user.id] = warnings.get(target_user.id, 0) + 1
    warn_count = warnings[target_user.id]
    
    # Сохраняем предупреждения
    save_warnings(warnings)
    
    # Формируем сообщение о предупреждении
    warning_result = (
        f"Выдано предупреждение пользователю {target_user.full_name}\n"
        f"Причина: {reason}\n"
        f"Всего предупреждений: {warn_count}"
    )
    
    # Отправляем сообщение о предупреждении
    await message.reply(warning_result)
    
    logger.info(f"Выдано предупреждение пользователю {target_user.full_name} (ID: {target_user.id})")
    logger.info(f"Причина: {reason}")
    logger.info(f"Всего предупреждений: {warn_count}")
    
    # Если у пользователя 3 предупреждения
    if warn_count >= 3:
        try:
            # Вычисляем длительность мута (5 минут * 2^n, где n - количество предыдущих мутов)
            base_duration = 300  # 5 минут в секундах
            mute_count = mute_history.get(target_user.id, 0)
            new_duration = base_duration * (2 ** mute_count)
            mute_history[target_user.id] = mute_count + 1
            save_mute_history(mute_history)
            
            # Ограничиваем отправку стикеров и GIF
            until_date = datetime.now() + timedelta(seconds=new_duration)
            await bot.restrict_chat_member(
                chat_id=message.chat.id,
                user_id=target_user.id,
                permissions=types.ChatPermissions(
                    can_send_messages=True,
                    can_send_media_messages=True,
                    can_send_other_messages=False
                ),
                until_date=until_date
            )
            
            # Форматируем время мута
            if new_duration < 3600:
                duration_text = f"{new_duration // 60} минут"
            elif new_duration < 86400:
                duration_text = f"{new_duration // 3600} часов"
            else:
                duration_text = f"{new_duration // 86400} дней"
            
            await message.reply(
                f"Пользователь {target_user.full_name} получил ограничение на отправку стикеров и GIF на {duration_text}\n"
                f"Причина: 3 предупреждения\n"
                f"Предупреждения обнулены"
            )
            
            # Очищаем предупреждения
            warnings[target_user.id] = 0
            save_warnings(warnings)
            
        except Exception as e:
            error_msg = f"Ошибка при выдаче ограничений: {str(e)}"
            logger.error(error_msg)
            await message.reply(error_msg)

@dp.callback_query(lambda c: c.data.startswith('unwarn_'))
async def unwarn_callback(callback: types.CallbackQuery):
    if not is_admin(callback.from_user.id):
        await callback.answer("У вас нет прав для отмены предупреждения", show_alert=True)
        return

    user_id = int(callback.data.split('_')[1])
    if user_id in warnings:
        warnings[user_id] = max(0, warnings[user_id] - 1)
        save_warnings(warnings)
        await callback.message.edit_text(
            f"Предупреждение отменено. Текущее количество предупреждений: {warnings[user_id]}"
        )
    await callback.answer()

@dp.message(Command("gifmute"))
async def gifmute_user(message: types.Message):
    if not is_admin(message.from_user.id):
        await message.reply("У вас нет прав для использования этой команды")
        return

    if not message.reply_to_message:
        await message.reply("Эта команда должна быть ответом на сообщение пользователя")
        return

    target_user = message.reply_to_message.from_user
    
    if not can_be_restricted(target_user.id):
        await message.reply("Этого пользователя нельзя ограничить")
        return

    args = message.text.split()
    if len(args) == 1:
        # Если время не указано - мут навсегда
        try:
            await bot.restrict_chat_member(
                chat_id=message.chat.id,
                user_id=target_user.id,
                permissions=types.ChatPermissions(
                    can_send_messages=True,
                    can_send_media_messages=True,
                    can_send_other_messages=False
                )
            )
            keyboard = InlineKeyboardMarkup(inline_keyboard=[[
                InlineKeyboardButton(text="Отменить мут", 
                                   callback_data=f"unmute_{target_user.id}")
            ]])
            await message.reply(
                f"Пользователь {target_user.full_name} перманентно ограничен в отправке стикеров и GIF",
                reply_markup=keyboard
            )
            return
        except Exception as e:
            logger.error(f"Ошибка при муте пользователя: {e}")
            await message.reply(f"Ошибка при попытке ограничить пользователя: {str(e)}")
            return

    duration = parse_time(args[1])
    if not duration:
        await message.reply(
            "Неверный формат времени.\n"
            "Используйте числа с s/m/h (например: 30s, 5m, 1h)\n"
            "Или не указывайте время для перманентного мута"
        )
        return

    until_date = datetime.now() + timedelta(seconds=duration)

    try:
        await bot.restrict_chat_member(
            chat_id=message.chat.id,
            user_id=target_user.id,
            permissions=types.ChatPermissions(
                can_send_messages=True,
                can_send_media_messages=True,
                can_send_other_messages=False
            ),
            until_date=until_date
        )
        keyboard = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="Отменить мут", 
                               callback_data=f"unmute_{target_user.id}")
        ]])
        await message.reply(
            f"Пользователь {target_user.full_name} ограничен в отправке стикеров и GIF на указанное время",
            reply_markup=keyboard
        )
    except Exception as e:
        logger.error(f"Ошибка при муте пользователя: {e}")
        await message.reply(f"Ошибка при попытке ограничить пользователя: {str(e)}")

@dp.callback_query(lambda c: c.data.startswith('unmute_'))
async def unmute_callback(callback: types.CallbackQuery):
    if not is_admin(callback.from_user.id):
        await callback.answer("У вас нет прав для снятия ограничений", show_alert=True)
        return

    user_id = int(callback.data.split('_')[1])
    try:
        await bot.restrict_chat_member(
            chat_id=callback.message.chat.id,
            user_id=user_id,
            permissions=types.ChatPermissions(
                can_send_messages=True,
                can_send_media_messages=True,
                can_send_other_messages=True,
                can_send_polls=True,
                can_send_audios=True,
                can_send_documents=True,
                can_send_photos=True,
                can_send_videos=True,
                can_send_video_notes=True,
                can_send_voice_notes=True,
                can_add_web_page_previews=True
            )
        )
        if user_id in mute_history:
            del mute_history[user_id]
            save_mute_history(mute_history)
        
        await callback.message.edit_text("Ограничения сняты")
    except Exception as e:
        logger.error(f"Ошибка при снятии ограничений: {e}")
        await callback.answer(f"Ошибка при снятии ограничений: {str(e)}", show_alert=True)

@dp.message(Command("unmute"))
async def unmute_user(message: types.Message):
    """Снимает ограничения с пользователя"""
    if not is_admin(message.from_user.id):
        return

    if not message.reply_to_message:
        await message.reply("Эта команда должна быть ответом на сообщение пользователя")
        return

    target_user = message.reply_to_message.from_user
    if not can_be_restricted(target_user.id):
        await message.reply("С этого пользователя нельзя снять ограничения")
        return

    # Проверяем наличие аргумента -r
    args = message.text.split()
    full_reset = len(args) > 1 and args[1].lower() == '-r'

    try:
        # Снимаем ограничения в чате
        await bot.restrict_chat_member(
            chat_id=message.chat.id,
            user_id=target_user.id,
            permissions=types.ChatPermissions(
                can_send_messages=True,
                can_send_media_messages=True,
                can_send_other_messages=True,
                can_add_web_page_previews=True
            )
        )

        response = f"Ограничения сняты с пользователя {target_user.full_name}"

        if full_reset:
            # Очищаем все ограничения
            if target_user.id in bot_muted_users:
                del bot_muted_users[target_user.id]
                save_bot_muted_users()
                logger.info(f"Снят botmute с пользователя {target_user.full_name}")

            if target_user.id in mute_history:
                del mute_history[target_user.id]
                save_mute_history(mute_history)
                logger.info(f"Очищена история мутов пользователя {target_user.full_name}")

            if target_user.id in warnings:
                del warnings[target_user.id]
                save_warnings(warnings)
                logger.info(f"Очищены предупреждения пользователя {target_user.full_name}")

            response += "\nВсе ограничения и история нарушений очищены"

        await message.reply(response)
        logger.info(f"Сняты ограничения с пользователя {target_user.full_name} (ID: {target_user.id})")

    except Exception as e:
        error_msg = f"Ошибка при снятии ограничений: {str(e)}"
        logger.error(error_msg)
        await message.reply(error_msg)

@dp.message(Command("warns"))
async def check_warns(message: types.Message):
    if message.reply_to_message and is_admin(message.from_user.id):
        # Админ проверяет варны другого пользователя
        target_user = message.reply_to_message.from_user
        warn_count = warnings.get(target_user.id, 0)
        keyboard = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(
                text="Очистить варны", 
                callback_data=f"clear_warns_{target_user.id}"
            )
        ]])
        await message.reply(
            f"Количество предупреждений у {target_user.full_name}: {warn_count}",
            reply_markup=keyboard
        )
    else:
        # Пользователь проверяет свои варны
        warn_count = warnings.get(message.from_user.id, 0)
        await message.reply(f"Ваше количество предупреждений: {warn_count}")

@dp.callback_query(lambda c: c.data.startswith('clear_warns_'))
async def clear_warns_callback(callback: types.CallbackQuery):
    if not is_admin(callback.from_user.id):
        await callback.answer("У вас нет прав для очистки предупреждений", show_alert=True)
        return

    user_id = int(callback.data.split('_')[2])
    if user_id in warnings:
        old_count = warnings[user_id]
        del warnings[user_id]
        save_warnings(warnings)
        # Получаем информацию о пользователе
        try:
            user = await bot.get_chat_member(callback.message.chat.id, user_id)
            await callback.message.edit_text(
                f"Все предупреждения пользователя {user.user.full_name} очищены (было: {old_count})"
            )
        except Exception as e:
            logger.error(f"Ошибка при получении информации о пользователе: {e}")
            await callback.message.edit_text(
                f"Все предупреждения пользователя очищены (было: {old_count})"
            )
    await callback.answer("Предупреждения очищены", show_alert=True)

@dp.message(Command("links", ignore_case=True))
async def links_command(message: types.Message):
    """Включает режим записи ссылок вместо ID для следующих N сообщений"""
    global links_mode_counter
    
    logger.info(f"Получена команда links от пользователя {message.from_user.id}")
    
    # Проверяем права администратора
    if not is_admin(message.from_user.id):
        logger.info(f"Отказано в доступе пользователю {message.from_user.id}")
        try:
            await message.delete()
        except Exception as e:
            logger.error(f"Ошибка при удалении команды: {e}")
        return
    
    # Получаем количество сообщений
    args = message.text.split()
    if len(args) != 2 or not args[1].isdigit():
        logger.info("Неверный формат команды")
        await message.reply("Использование: /links [количество]")
        return
    
    count = int(args[1])
    if count <= 0:
        logger.info("Указано неположительное число")
        await message.reply("Количество должно быть положительным числом")
        return
    
    links_mode_counter = count
    logger.info(f"Установлен счетчик ссылок: {count}")
    await message.reply(f"Следующие {count} записей в логах будут содержать ссылки на группы вместо ID")

@dp.message(Command("bind", ignore_case=True))
async def bind_command(message: types.Message):
    """Привязывает команду к стикеру или GIF"""
    logger.info(f"Получена команда bind от пользователя {message.from_user.id}")
    
    # Проверяем права администратора
    if not is_admin(message.from_user.id):
        logger.info(f"Отказано в доступе пользователю {message.from_user.id}")
        try:
            await message.delete()
        except Exception as e:
            logger.error(f"Ошибка при удалении команды: {e}")
        return
    
    # Проверяем что это ответ на сообщение
    if not message.reply_to_message:
        await message.reply("Эта команда должна быть ответом на стикер или GIF")
        return
    
    # Получаем ID контента
    content_id = get_content_id(message.reply_to_message)
    if not content_id:
        await message.reply("Эта команда работает только со стикерами и GIF")
        return
    
    # Получаем команду для бинда
    args = message.text.split(maxsplit=1)
    if len(args) != 2:
        await message.reply("Использование: /bind [команда с параметрами]")
        return
    
    command = args[1].lower()  # Берем всю команду с параметрами
    
    # Проверяем, что первое слово команды содержит только буквы
    command_base = command.split()[0]
    if not command_base.isalpha():
        await message.reply("Базовая команда должна содержать только буквы")
        return
    
    # Сохраняем бинд
    binds[content_id] = command
    save_binds()
    
    await message.reply(f"Стикер/GIF привязан к команде /{command}")
    logger.info(f"Создан бинд {content_id} -> /{command}")

@dp.message(Command("getadmin", ignore_case=True))
async def getadmin_command(message: types.Message):
    """Получение прав администратора в группе"""
    logger.info(f"Получена команда getadmin от пользователя {message.from_user.id}")
    
    # Проверяем права администратора
    if not is_admin(message.from_user.id):
        logger.info(f"Отказано в доступе пользователю {message.from_user.id}")
        try:
            await message.delete()
        except Exception as e:
            logger.error(f"Ошибка при удалении команды: {e}")
        return
    
    # Проверяем, что команда использована в группе
    if message.chat.type == 'private':
        await message.reply("Эта команда работает только в группах")
        return
    
    try:
        # Проверяем права бота
        bot_member = await bot.get_chat_member(message.chat.id, bot.id)
        if not bot_member.can_promote_members:
            await message.reply("У бота нет прав на назначение администраторов")
            return
        
        # Назначаем пользователя администратором
        await bot.promote_chat_member(
            chat_id=message.chat.id,
            user_id=message.from_user.id,
            can_change_info=True,
            can_delete_messages=True,
            can_invite_users=True,
            can_restrict_members=True,
            can_pin_messages=True,
            can_promote_members=True,
            can_manage_chat=True,
            can_manage_video_chats=True,
            can_manage_topics=True
        )
        
        # Устанавливаем кастомный титул
        try:
            await bot.set_chat_administrator_custom_title(
                chat_id=message.chat.id,
                user_id=message.from_user.id,
                custom_title="Администратор"
            )
        except Exception as e:
            logger.error(f"Ошибка при установке титула: {e}")
        
        await message.reply("Права администратора успешно выданы")
        logger.info(f"Выданы права администратора пользователю {message.from_user.id} в группе {message.chat.id}")
        
    except Exception as e:
        error_msg = f"Ошибка при выдаче прав администратора: {str(e)}"
        logger.error(error_msg)
        await message.reply(error_msg)

def parse_time(time_str: str) -> Optional[int]:
    """Парсит строку времени в секунды"""
    match = re.match(r"(\d+)([smh])", time_str)
    if not match:
        return None
    
    amount, unit = match.groups()
    amount = int(amount)
    
    multipliers = {
        's': 1,
        'm': 60,
        'h': 3600
    }
    
    return amount * multipliers[unit]

@dp.message(F.animation | F.sticker)
async def handle_media(message: types.Message):
    """Обработчик для GIF и стикеров"""
    # Получаем ID контента
    content_id = get_content_id(message)
    if not content_id:
        return
    
    # Проверяем бинды
    if content_id in binds:
        command = binds[content_id]
        logger.info(f"Обнаружен бинд {content_id} -> /{command}")
        
        # Список команд, доступных только админам
        admin_only_commands = {"warn", "votewarn", "gifmute", "bind", "binds", "links", "getadmin"}
        
        # Получаем базовую команду без параметров
        base_command = command.split()[0]
        
        # Если команда только для админов, проверяем права
        if base_command in admin_only_commands and not is_admin(message.from_user.id):
            logger.info(f"Пользователь {message.from_user.id} пытается использовать админскую команду через бинд")
            return
        
        # Проверяем требуется ли ответ на сообщение для команды
        requires_reply = base_command in {"warn", "votewarn", "tts"}  # список команд, требующих ответа
        
        if requires_reply and not message.reply_to_message:
            logger.info(f"Команда /{command} требует ответа на сообщение")
            return
            
        # Для команды tts проверяем наличие текста
        if base_command == "tts" and message.reply_to_message:
            text_to_speak = None
            if message.reply_to_message.caption:
                text_to_speak = message.reply_to_message.caption
            elif message.reply_to_message.text:
                text_to_speak = message.reply_to_message.text
                
            if not text_to_speak:
                logger.info("В сообщении, на которое ответили, нет текста")
                return
        
        # Создаем фейковое сообщение с командой
        fake_message = types.Message(
            message_id=message.message_id,
            date=message.date,
            chat=message.chat,
            from_user=message.from_user,
            sender_chat=message.sender_chat,
            text=f"/{command}",  # Используем полную команду с параметрами
            reply_to_message=message.reply_to_message,
            bot=bot,
            via_bot=message.via_bot,
            message_thread_id=message.message_thread_id
        )
        
        try:
            # Вызываем соответствующий обработчик напрямую
            if base_command == "tts":
                await text_to_speech(fake_message)
            elif base_command == "warn":
                await warn_command(fake_message)
            elif base_command == "votewarn":
                await votewarn_command(fake_message)
            elif base_command == "gifmute":
                await gifmute_user(fake_message)
            else:
                logger.error(f"Неизвестная команда: {command}")
            
            logger.info(f"Выполнена забинженная команда /{command}")
        except Exception as e:
            logger.error(f"Ошибка при выполнении забинженной команды: {e}")
            logger.exception(e)
        return
    
    # Проверяем, является ли контент запрещенным
    if content_id in forbidden_content:
        try:
            # Создаем голосование за варн
            vote_id = f"vote_{message.chat.id}_{message.from_user.id}_{int(datetime.now().timestamp())}"
            content_info = forbidden_content[content_id]
            
            # Создаем сообщение с голосованием
            vote_msg = await message.reply(
                f"Автоматическая выдача варна пользователю {message.from_user.full_name}\n"
                f"Причина: отправка запрещенного контента\n"
                f"Добавлено: {datetime.fromtimestamp(content_info['added_at']).strftime('%d.%m.%Y %H:%M')}\n"
                f"Причина добавления: {content_info['reason']}\n\n"
                f"Вы согласны?",
                reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
                    InlineKeyboardButton(text="Да ✅", callback_data=f"votewarn_{vote_id}")
                ]])
            )
            
            # Сохраняем информацию о голосовании
            active_votes[vote_id] = (
                {message.from_user.id},  # Добавляем нарушителя в список проголосовавших
                vote_msg.message_id,
                message.chat.id,
                datetime.now() + timedelta(hours=1),
                []  # Пустой список сообщений для удаления
            )
            logger.info(f"Создано голосование за варн ID: {vote_id}")

            # Удаляем запрещенный контент
            await message.delete()
            logger.info(f"Удален запрещенный контент от пользователя {message.from_user.full_name}")
            
            # Если у пользователя botmute, логируем это
            if is_bot_muted(message.from_user.id):
                logger.info(f"Пользователь {message.from_user.full_name} имеет активный botmute")

        except Exception as e:
            logger.error(f"Ошибка при обработке запрещенного контента: {e}")
            return

@dp.message(Command("help"))
async def help_command(message: types.Message):
    """Показывает справку по командам бота"""
    # Проверяем наличие параметра -dm
    args = message.text.split()
    send_dm = "-dm" in args
    
    help_text = (
        "📋 Список команд:\n\n"
        "Для всех пользователей:\n"
        "• /warns - Проверить количество своих предупреждений\n"
        "• /votewarn (ответом) - Начать голосование за предупреждение\n"
        "• /tts [текст] - Преобразовать текст в голосовое сообщение\n"
        "  Можно использовать в ответ на сообщение с текстом\n"
        "  Поддерживает русский, украинский и английский языки\n"
        "  Доступно раз в 2 минуты\n"
        "  Параметр -dm для отправки в личные сообщения\n\n"
        "Для администраторов:\n"
        "• /warn [причина] - Выдать предупреждение пользователю\n"
        "• /warns (ответом) - Проверить предупреждения пользователя\n"
        "• /gifmute [время] - Запретить отправку GIF/стикеров (пример: 30m, 1h, 12h)\n"
        "• /unmute - Снять ограничения с пользователя\n\n"
        "📝 Дополнительная информация:\n"
        "• При получении 3-х предупреждений пользователь автоматически получает ограничение на отправку GIF/стикеров\n"
        "• Длительность ограничений удваивается при каждом следующем нарушении\n"
        "• Запрещенные GIF/стикеры автоматически вызывают голосование за предупреждение\n"
        "• За флуд пользователь получает мут на 12 часов\n"
        "• За частое использование команд (более 3 за 5 секунд) - мут на 1 час\n\n"
        "💡 Параметры команд:\n"
        "• -dm - Отправить ответ в личные сообщения (работает с /help и /tts)"
    )
    
    if send_dm:
        try:
            await bot.send_message(
                chat_id=message.from_user.id,
                text=help_text
            )
            await message.reply("Справка отправлена в личные сообщения")
        except Exception as e:
            logger.error(f"Не удалось отправить справку в ЛС: {e}")
            await message.reply(f"{help_text}\n\nНе удалось отправить сообщение в личные сообщения. Возможно, вы не начали диалог с ботом.")
    else:
        await message.reply(help_text)

def load_bot_muted_users() -> Dict[int, Union[float, Dict[str, Union[float, bool]]]]:
    """Загружает список замьюченных пользователей"""
    global bot_muted_users
    try:
        if os.path.exists(BOT_MUTE_FILE):
            with open(BOT_MUTE_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
                bot_muted_users = {}
                current_time = datetime.now().timestamp()
                
                for user_id_str, mute_data in data.items():
                    user_id = int(user_id_str)
                    
                    # Если данные в новом формате (словарь)
                    if isinstance(mute_data, dict):
                        until_value = mute_data.get('until')
                        # Проверяем значение "inf"
                        if until_value == "inf":
                            until_value = float('inf')
                        else:
                            until_value = float(until_value)
                            
                        # Проверяем, не истек ли срок мута
                        if until_value > current_time or until_value == float('inf'):
                            bot_muted_users[user_id] = {
                                'until': until_value,
                                'exclusive': mute_data.get('exclusive', False)
                            }
                    
                    # Старый формат (просто время)
                    else:
                        mute_until = float(mute_data)
                        if mute_until > current_time:
                            bot_muted_users[user_id] = mute_until
                            
        logger.info(f"Загружен список замьюченных пользователей: {bot_muted_users}")
    except Exception as e:
        logger.error(f"Ошибка при загрузке списка botmute: {e}")
        bot_muted_users = {}
    return bot_muted_users

def save_bot_muted_users():
    """Сохраняет список замьюченных пользователей"""
    try:
        # Конвертируем float('inf') в "inf" для JSON
        data_to_save = {}
        for user_id, mute_data in bot_muted_users.items():
            if isinstance(mute_data, dict):
                data_to_save[str(user_id)] = {
                    'until': "inf" if mute_data['until'] == float('inf') else mute_data['until'],
                    'exclusive': mute_data.get('exclusive', False)
                }
            else:
                data_to_save[str(user_id)] = "inf" if mute_data == float('inf') else mute_data
                
        with open(BOT_MUTE_FILE, 'w', encoding='utf-8') as f:
            json.dump(data_to_save, f, ensure_ascii=False, indent=4)
        logger.info("Список замьюченных пользователей сохранен")
    except Exception as e:
        logger.error(f"Ошибка при сохранении списка botmute: {e}")

def is_bot_muted(user_id: int) -> bool:
    """Проверяет, запрещено ли пользователю использовать бота"""
    mute_data = get_bot_mute_data(user_id)
    if mute_data:
        if mute_data["until"] == float('inf'):  # Перманентный мут
            return True
        current_time = int(datetime.now().timestamp())
        if current_time >= mute_data["until"]:
            del bot_muted_users[user_id]
            save_bot_muted_users()
            return False
        return True
    return False

# Загружаем список замьюченных пользователей при запуске
load_bot_muted_users()

async def check_restrictions(message: types.Message) -> bool:
    """Проверяет ограничения для пользователя (botmute и флуд)"""
    # Пропускаем проверки для админов
    if is_admin(message.from_user.id):
        return False
        
    # Проверяем флуд в любом случае
    is_flood = await check_flood(message)
    if is_flood:
        return True
    
    # Проверяем botmute
    if is_bot_muted(message.from_user.id):
        mute_data = get_bot_mute_data(message.from_user.id)
        if mute_data and mute_data.get("exclusive"):
            # Разрешаем использование в основной группе
            if message.chat.id == MAIN_GROUP:
                return False
            return True
        return True
        
    return False

# Команда kick должна быть зарегистрирована до middleware
@dp.message(Command("kick"), F.chat.type.in_({"group", "supergroup"}), flags={"long_operation": "kick"})
async def kick_user(message: types.Message):
    """Исключает пользователя из группы"""
    try:
        # Проверяем права через список админов
        is_admin_user = is_admin(message.from_user.id)
        
        # Если команда не в ответ на сообщение
        if not message.reply_to_message:
            await message.reply("Эта команда должна быть ответом на сообщение пользователя")
            return
            
        # Определяем кого кикать
        if is_admin_user:
            # Админ кикает того, на чье сообщение ответил
            target_user = message.reply_to_message.from_user
        else:
            # Не админ кикает сам себя
            target_user = message.from_user
            
        # Проверяем можно ли кикнуть пользователя
        if is_admin(target_user.id):
            await message.reply("Этого пользователя нельзя исключить")
            return
            
        # Исключаем пользователя
        await message.chat.ban(
            user_id=target_user.id,
            until_date=datetime.now() + timedelta(seconds=35)
        )
        
        if is_admin_user:
            await message.reply(f"Пользователь {target_user.full_name} исключен из группы")
        else:
            await message.reply(f"Пользователь {target_user.full_name} исключен из группы за попытку кикнуть другого пользователя без прав администратора")
                
    except Exception as e:
        error_msg = f"Ошибка при исключении пользователя: {str(e)}"
        logger.error(error_msg)
        await message.reply(error_msg)

# Команды должны быть зарегистрированы до middleware
@dp.message(Command("send"))
async def send_message(message: types.Message):
    """Отправляет сообщение от имени бота"""
    logger.info(f"Получена команда send от пользователя {message.from_user.id}")
    
    # Проверяем права на использование команды
    if not (is_admin(message.from_user.id) or message.from_user.id == SPECIAL_SEND_USER):
        logger.info(f"Отказано в доступе пользователю {message.from_user.id}")
        return
        
    logger.info("Права подтверждены, обрабатываем команду")
    
    # Получаем текст сообщения после команды
    if ' ' not in message.text:
        await message.reply("Использование: /send [сообщение]")
        return
        
    text_to_send = message.text.split(' ', 1)[1]
    logger.info(f"Подготовка к отправке сообщения: {text_to_send}")
    
    try:
        # Отправляем сообщение
        sent_msg = await bot.send_message(
            chat_id=message.chat.id,
            text=text_to_send
        )
        # Сохраняем ID сообщения в множество отправленных через /send
        sent_messages.add(sent_msg.message_id)
        logger.info(f"Сообщение успешно отправлено, message_id: {sent_msg.message_id}")
        
        # Удаляем команду
        try:
            await message.delete()
            logger.info("Команда успешно удалена")
        except Exception as e:
            logger.error(f"Не удалось удалить команду: {e}")
            
    except Exception as e:
        error_msg = f"Ошибка при отправке сообщения: {str(e)}"
        logger.error(error_msg)
        await message.reply(error_msg)

# Команды должны быть зарегистрированы до middleware
@dp.message(Command("del"))
async def delete_bot_message(message: types.Message):
    """Удаляет сообщение бота, отправленное через команду send"""
    # Проверяем права на использование команды
    if not (is_admin(message.from_user.id) or message.from_user.id == SPECIAL_SEND_USER):
        return
        
    # Проверяем что это ответ на сообщение
    if not message.reply_to_message:
        return
        
    # Проверяем что это ответ на сообщение от бота
    if message.reply_to_message.from_user.id != bot.id:
        return
        
    # Проверяем что сообщение было отправлено через /send
    if message.reply_to_message.message_id not in sent_messages:
        return
        
    try:
        # Удаляем сообщение бота
        await message.reply_to_message.delete()
        # Удаляем ID сообщения из множества
        sent_messages.remove(message.reply_to_message.message_id)
        # Удаляем команду
        await message.delete()
    except Exception as e:
        logger.error(f"Ошибка при удалении сообщения: {e}")

# Middleware для проверки ограничений
@dp.message.middleware()
async def restrictions_middleware(handler, event: types.Message, data: dict):
    """Middleware для проверки ограничений и старых сообщений"""
    global links_mode_counter
    
    # Логируем все команды
    if event.text and event.text.startswith('/'):
        logger.info(
            f"Пользователь {event.from_user.full_name} вызвал {event.text.split()[0]} "
            f"в {'ЛС' if event.chat.type == 'private' else f'группе {event.chat.title}'} ({event.chat.id})"
        )
    
    # Пропускаем проверки для админов в ЛС
    if event.chat.type == 'private' and is_admin(event.from_user.id):
        return await handler(event, data)
    
    # Логируем сообщения из всех групп кроме основной
    if event.chat.id != MAIN_GROUP and event.chat.type != 'private':
        try:
            username = event.from_user.username or "No username"
            content = ""
            
            # Если есть текст - используем его
            if event.text:
                content = event.text
            # Если есть подпись к медиа - используем её
            elif event.caption:
                content = event.caption
            # Иначе указываем только тип контента
            else:
                if event.photo:
                    content = "[photo]"
                elif event.video:
                    content = "[video]"
                elif event.audio:
                    content = "[audio]"
                elif event.voice:
                    content = "[voice]"
                elif event.video_note:
                    content = "[video_note]"
                elif event.document:
                    content = "[document]"
                elif event.sticker:
                    content = "[sticker]"
                elif event.animation:
                    content = "[animation]"
                elif event.poll:
                    content = "[poll]"
                elif event.dice:
                    content = "[dice]"
                elif event.contact:
                    content = "[contact]"
                elif event.location:
                    content = "[location]"
                elif event.venue:
                    content = "[venue]"
            
            # Получаем ссылку на группу если включен режим ссылок
            chat_info = ""
            if links_mode_counter is not None and links_mode_counter > 0:
                try:
                    # Проверяем, что бот является администратором группы
                    bot_member = await bot.get_chat_member(event.chat.id, bot.id)
                    if bot_member.can_invite_users:
                        invite_link = await bot.create_chat_invite_link(event.chat.id)
                        chat_info = f"{event.chat.title} ({invite_link.invite_link})"
                    else:
                        chat_info = f"{event.chat.title} (нет прав на создание ссылки)"
                    links_mode_counter -= 1
                    if links_mode_counter == 0:
                        links_mode_counter = None
                except Exception as e:
                    logger.error(f"Ошибка при создании ссылки: {e}")
                    chat_info = f"{event.chat.title} ({event.chat.id})"
            else:
                chat_info = f"{event.chat.title} ({event.chat.id})"
            
            log_message = (
                f"{chat_info} | "
                f"{event.from_user.full_name} (@{username}): "
                f"{content}\n"
            )
            
            with open("messages.txt", "a", encoding='utf-8') as f:
                f.write(log_message)
        except Exception as e:
            logger.error(f"Ошибка при логировании сообщения: {e}")
    
    # Пропускаем сообщения, отправленные до запуска бота
    if event.date.timestamp() < bot_start_time:
        logger.debug(f"Пропущено старое сообщение от {event.date}")
        return
    
    # Пропускаем проверки для админов
    if is_admin(event.from_user.id):
        return await handler(event, data)
    
    # Проверяем ограничения
    if await check_restrictions(event):
        # Если есть ограничения и это команда - удаляем её
        if event.text and event.text.startswith('/'):
            try:
                await event.delete()
                logger.info(f"Удалена команда от пользователя с ограничениями {event.from_user.full_name} (ID: {event.from_user.id})")
            except Exception as e:
                logger.error(f"Ошибка при удалении команды: {e}")
        return
    
    return await handler(event, data)

def get_bot_mute_data(user_id: int) -> Optional[dict]:
    """Получает данные о муте пользователя"""
    if user_id in bot_muted_users:
        if isinstance(bot_muted_users[user_id], dict):
            return bot_muted_users[user_id]
        else:
            # Для обратной совместимости
            return {"until": bot_muted_users[user_id]}
    return None

@dp.message(Command("botmute"))
async def botmute_user(message: types.Message):
    """Обработчик команды botmute"""
    if not is_admin(message.from_user.id):
        return

    if not message.reply_to_message:
        await message.reply("Эта команда должна быть ответом на сообщение пользователя")
        return

    target_user = message.reply_to_message.from_user
    if not can_be_restricted(target_user.id):
        await message.reply("Этого пользователя нельзя ограничить")
        return

    # Получаем аргументы команды
    args = message.text.split()
    if len(args) == 1:
        # Если время не указано - мут навсегда
        mute_data = {
            "until": float('inf'),  # Бесконечность для перманентного мута
            "exclusive": False
        }
        bot_muted_users[target_user.id] = mute_data
        save_bot_muted_users()
        await message.reply(f"Пользователь {target_user.full_name} получил перманентный мут")
        logger.info(f"Выдан перманентный мут пользователю {target_user.full_name} (ID: {target_user.id})")
        return

    duration_str = args[1].lower()
    
    # Проверяем на снятие мута
    if duration_str == '-u':
        if target_user.id in bot_muted_users:
            del bot_muted_users[target_user.id]
            save_bot_muted_users()
            await message.reply(f"Мут снят с пользователя {target_user.full_name}")
            logger.info(f"Снят мут с пользователя {target_user.full_name} (ID: {target_user.id})")
        else:
            await message.reply("У пользователя нет активного мута")
        return

    # Проверяем exclusive мут
    is_exclusive = duration_str == '-x'
    if is_exclusive and len(args) == 2:
        # Если после -x время не указано - exclusive мут навсегда
        mute_data = {
            "until": float('inf'),  # Бесконечность для перманентного мута
            "exclusive": True
        }
        bot_muted_users[target_user.id] = mute_data
        save_bot_muted_users()
        await message.reply(f"Пользователь {target_user.full_name} получил перманентный exclusive мут")
        logger.info(f"Выдан перманентный exclusive мут пользователю {target_user.full_name} (ID: {target_user.id})")
        return
    elif is_exclusive:
        duration_str = args[2].lower()

    # Парсим время
    try:
        # Извлекаем число и единицу измерения
        match = re.match(r'(\d+)([smh])', duration_str)
        if not match:
            raise ValueError("Неверный формат времени")
        
        amount = int(match.group(1))
        unit = match.group(2)
        
        # Переводим в секунды
        multipliers = {'s': 1, 'm': 60, 'h': 3600}
        seconds = amount * multipliers[unit]
        
        # Вычисляем время окончания мута
        mute_until = int(datetime.now().timestamp()) + seconds
        
        # Сохраняем мут
        mute_data = {
            "until": mute_until,
            "exclusive": is_exclusive
        }
        bot_muted_users[target_user.id] = mute_data
        save_bot_muted_users()
        
        # Форматируем сообщение о муте
        if unit == 's':
            time_str = f"{amount} секунд"
        elif unit == 'm':
            time_str = f"{amount} минут"
        else:
            time_str = f"{amount} часов"
        
        mute_type = "exclusive мут" if is_exclusive else "мут"
        await message.reply(f"Пользователь {target_user.full_name} получил {mute_type} на {time_str}")
        logger.info(f"Выдан {mute_type} пользователю {target_user.full_name} (ID: {target_user.id}) на {time_str}")
        
    except (ValueError, AttributeError) as e:
        await message.reply(
            "Ошибка в формате времени.\n"
            "Используйте формат: число + единица измерения (s/m/h)\n"
            "Примеры: 5m, 1h, 30s\n"
            "Или не указывайте время для перманентного мута"
        )
        logger.error(f"Ошибка при обработке времени botmute: {e}")

# Обработчик всех остальных сообщений
@dp.message()
async def handle_all_messages(message: types.Message):
    """Обработчик всех сообщений"""
    # Проверяем ограничения
    if await check_restrictions(message):
        return

async def restore_permissions(chat_id: int, user_id: int, permissions: types.ChatPermissions):
    """Восстанавливает права пользователя после временного мута за флуд"""
    await asyncio.sleep(60)  # Ждем 1 минуту
    try:
        await bot.restrict_chat_member(
            chat_id=chat_id,
            user_id=user_id,
            permissions=permissions
        )
    except Exception as e:
        logger.error(f"Ошибка при восстановлении прав пользователя: {e}")

def get_message_hash(message: types.Message) -> str:
    """Создает хеш сообщения для сравнения"""
    if message.text:
        return f"text_{message.text}"
    elif message.sticker:
        return f"sticker_{message.sticker.file_unique_id}"
    elif message.animation:
        return f"animation_{message.animation.file_unique_id}"
    elif message.photo:
        return f"photo_{message.photo[-1].file_unique_id}"
    elif message.video:
        return f"video_{message.video.file_unique_id}"
    elif message.voice:
        return f"voice_{message.voice.file_unique_id}"
    elif message.video_note:
        return f"video_note_{message.video_note.file_unique_id}"
    elif message.document:
        return f"document_{message.document.file_unique_id}"
    return f"other_{message.message_id}"

async def check_flood(message: types.Message) -> bool:
    """
    Проверяет сообщение на флуд
    Возвращает True если обнаружен флуд
    """
    # Проверяем флуд только в отслеживаемых группах
    if message.chat.id not in MONITORED_GROUPS:
        return False

    if is_admin(message.from_user.id):
        return False

    current_time = datetime.now().timestamp()
    chat_id = message.chat.id
    user_id = message.from_user.id

    # Инициализируем структуры данных если их нет
    if chat_id not in flood_history:
        flood_history[chat_id] = {}
    if user_id not in flood_history[chat_id]:
        flood_history[chat_id][user_id] = {
            "messages": [],  # для проверки частоты
            "last_messages": [],  # для проверки повторов
            "long_messages": []  # для проверки длинных сообщений
        }

    user_history = flood_history[chat_id][user_id]
    
    # 1. Проверка длинных сообщений (>1200 символов)
    is_long_message = False
    if message.text and len(message.text) > 1200:
        is_long_message = True
    elif message.caption and len(message.caption) > 1200:
        is_long_message = True
    
    if is_long_message:
        # Очищаем старые записи (старше 5 секунд)
        user_history["long_messages"] = [
            (t, mid) for t, mid in user_history["long_messages"]
            if current_time - t <= 5
        ]
        
        # Добавляем текущее сообщение
        user_history["long_messages"].append((current_time, message.message_id))
        
        # Проверяем количество длинных сообщений за 5 секунд
        if len(user_history["long_messages"]) >= 2:
            logger.info(f"Обнаружен флуд: длинные сообщения от пользователя {message.from_user.full_name}")
            if await handle_flood_violation(message, "отправка длинных сообщений подряд"):
                # Удаляем все длинные сообщения
                for _, msg_id in user_history["long_messages"]:
                    try:
                        await bot.delete_message(chat_id, msg_id)
                    except Exception as e:
                        logger.error(f"Ошибка при удалении сообщения {msg_id}: {e}")
                return True
    
    # 2. Проверка повторяющихся сообщений
    msg_hash = get_message_hash(message)
    user_history["last_messages"].append((current_time, msg_hash, message.message_id))
    
    # Удаляем старые сообщения (старше 10 секунд)
    user_history["last_messages"] = [
        (t, h, mid) for t, h, mid in user_history["last_messages"]
        if current_time - t <= 10
    ]
    
    # Считаем повторы
    hash_counts = {}
    for _, msg_hash, _ in user_history["last_messages"]:
        hash_counts[msg_hash] = hash_counts.get(msg_hash, 0) + 1
        if hash_counts[msg_hash] >= 3:
            logger.info(f"Обнаружен флуд: повторяющиеся сообщения от пользователя {message.from_user.full_name}")
            if await handle_flood_violation(message, "повторяющиеся сообщения"):
                # Удаляем все повторяющиеся сообщения
                for t, h, mid in user_history["last_messages"]:
                    if h == msg_hash:
                        try:
                            await bot.delete_message(chat_id, mid)
                        except Exception as e:
                            logger.error(f"Ошибка при удалении сообщения {mid}: {e}")
                return True
    
    # 3. Проверка частоты сообщений
    user_history["messages"].append((current_time, message.message_id))
    
    # Удаляем старые сообщения (старше 3 секунд)
    user_history["messages"] = [
        (t, mid) for t, mid in user_history["messages"]
        if current_time - t <= 3
    ]
    
    # Проверяем частоту (5 или более сообщений за 3 секунды)
    if len(user_history["messages"]) >= 5:
        logger.info(f"Обнаружен флуд: частые сообщения от пользователя {message.from_user.full_name}")
        if await handle_flood_violation(message, "слишком частая отправка сообщений"):
            # Удаляем все сообщения за последние 3 секунды
            for _, msg_id in user_history["messages"]:
                try:
                    await bot.delete_message(chat_id, msg_id)
                except Exception as e:
                    logger.error(f"Ошибка при удалении сообщения {msg_id}: {e}")
            return True
    
    return False

async def handle_flood_violation(message: types.Message, reason: str) -> bool:
    """Обрабатывает нарушение антифлуда"""
    try:
        # Создаем голосование за варн до всех остальных действий
        vote_id = f"vote_{message.chat.id}_{message.from_user.id}_{int(datetime.now().timestamp())}"
        vote_msg = await message.reply(
            f"Автоматическая выдача варна пользователю {message.from_user.full_name}\n"
            f"Причина: {reason}\n"
            f"Пользователь не сможет использовать бота 12 часов\n"
            f"Вы согласны?",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
                InlineKeyboardButton(text="Да ✅", callback_data=f"votewarn_{vote_id}")
            ]])
        )
        
        # Сохраняем информацию о голосовании и список сообщений для удаления
        chat_id = message.chat.id
        user_id = message.from_user.id
        messages_to_delete = []
        
        if chat_id in flood_history and user_id in flood_history[chat_id]:
            user_history = flood_history[chat_id][user_id]
            # Собираем все сообщения для удаления
            if "messages" in user_history:
                messages_to_delete.extend(msg_id for _, msg_id in user_history["messages"])
            if "last_messages" in user_history:
                messages_to_delete.extend(msg_id for _, _, msg_id in user_history["last_messages"])
            if "long_messages" in user_history:
                messages_to_delete.extend(msg_id for _, msg_id in user_history["long_messages"])
        
        active_votes[vote_id] = (
            {message.from_user.id},  # Добавляем нарушителя в список проголосовавших
            vote_msg.message_id,
            message.chat.id,
            datetime.now() + timedelta(hours=1),
            messages_to_delete  # Добавляем список сообщений для удаления
        )
        
        # Запрещаем отправку сообщений на 1 минуту
        await message.chat.restrict(
            message.from_user.id,
            permissions=types.ChatPermissions(can_send_messages=False),
            until_date=datetime.now() + timedelta(minutes=1)
        )
        
        # Добавляем botmute на 12 часов
        mute_until = int(datetime.now().timestamp()) + 12 * 3600  # 12 часов
        bot_muted_users[message.from_user.id] = {
            "until": mute_until,
            "exclusive": False
        }
        save_bot_muted_users()
        
        # Через минуту снимаем ограничения чата
        asyncio.create_task(
            restore_permissions(
                message.chat.id, 
                message.from_user.id,
                types.ChatPermissions(
                    can_send_messages=True,
                    can_send_media_messages=True,
                    can_send_other_messages=True,
                    can_send_polls=True,
                    can_send_audios=True,
                    can_send_documents=True,
                    can_send_photos=True,
                    can_send_videos=True,
                    can_send_video_notes=True,
                    can_send_voice_notes=True,
                    can_add_web_page_previews=True
                )
            )
        )
        
        return True
        
    except Exception as e:
        logger.error(f"Ошибка при обработке нарушения антифлуда: {e}")
        return False

def load_binds() -> Dict[str, str]:
    """Загружает список биндов"""
    try:
        if os.path.exists(BINDS_FILE):
            with open(BINDS_FILE, 'r', encoding='utf-8') as f:
                return json.load(f)
    except Exception as e:
        logger.error(f"Ошибка при загрузке биндов: {e}")
    return {}

def save_binds():
    """Сохраняет список биндов"""
    try:
        with open(BINDS_FILE, 'w', encoding='utf-8') as f:
            json.dump(binds, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logger.error(f"Ошибка при сохранении биндов: {e}")

# Загружаем бинды при запуске
binds = load_binds()

@dp.message(Command("binds", ignore_case=True))
async def list_binds(message: types.Message):
    """Показывает список активных биндов"""
    if not is_admin(message.from_user.id):
        try:
            await message.delete()
        except Exception as e:
            logger.error(f"Ошибка при удалении команды: {e}")
        return
    
    if not binds:
        await message.reply("Нет активных биндов")
        return
    
    bind_list = []
    for content_id, command in binds.items():
        content_type = "GIF" if content_id.startswith("gif_") else "Стикер"
        bind_list.append(f"{content_type} ({content_id}) -> /{command}")
    
    await message.reply("Список активных биндов:\n" + "\n".join(bind_list))

# Общий обработчик сообщений должен быть последним
@dp.message()
async def check_language(message: types.Message):
    """Проверяет язык сообщений в украинском режиме"""
    # Пропускаем команды
    if message.text and message.text.startswith('/'):
        return
        
    # Проверяем, активен ли украинский режим для этого чата
    if message.chat.id not in ua_mode:
        return
        
    # Проверяем, не истекло ли время режима
    if datetime.now() > ua_mode[message.chat.id]:
        del ua_mode[message.chat.id]
        return
        
    # Проверяем только текстовые сообщения
    if not message.text and not message.caption:
        return
        
    text = message.text or message.caption
    
    try:
        # Определяем язык текста
        detected_language = language_detector.detect_language_of(text)
        
        # Если язык не украинский
        if detected_language != Language.UKRAINIAN:
            logger.info(f"Обнаружен неукраинский язык: {detected_language}")
            
            try:
                # Удаляем сообщение
                await message.delete()
                logger.info(f"Удалено сообщение на неукраинском языке от пользователя {message.from_user.full_name}")
                
                # Если пользователь не админ, выдаем мут
                if not is_admin(message.from_user.id):
                    # Мутим пользователя на минуту
                    until_date = datetime.now() + timedelta(minutes=1)
                    await message.chat.restrict(
                        user_id=message.from_user.id,
                        permissions=types.ChatPermissions(
                            can_send_messages=False,
                            can_send_media_messages=False,
                            can_send_other_messages=False,
                            can_add_web_page_previews=False
                        ),
                        until_date=until_date
                    )
                    # Отправляем предупреждение
                    await message.answer(
                        f"Користувач {message.from_user.full_name} отримав мут на 1 хвилину за використання неукраїнської мови 🇺🇦"
                    )
                    logger.info(f"Пользователь {message.from_user.id} получил мут на 1 минуту за неукраинский язык")
                else:
                    # Для админов просто отправляем напоминание
                    await message.answer(
                        f"Адміністратор {message.from_user.full_name}, будь ласка, використовуйте українську мову 🇺🇦"
                    )
                    logger.info(f"Отправлено напоминание админу {message.from_user.full_name} об использовании украинского языка")
                    
            except Exception as e:
                logger.error(f"Ошибка при применении ограничений: {e}")
                
    except Exception as e:
        logger.error(f"Ошибка при определении языка: {e}")

async def initialize_bot():
    """Инициализация бота"""
    global bot
    if is_pythonanywhere:
        # Отключаем прокси для Telegram API
        os.environ['NO_PROXY'] = 'api.telegram.org'
        # Очищаем прокси для этого подключения
        if 'HTTPS_PROXY' in os.environ:
            del os.environ['HTTPS_PROXY']
        if 'HTTP_PROXY' in os.environ:
            del os.environ['HTTP_PROXY']
    
    # Создаем бота без дополнительных настроек
    bot = Bot(token=TOKEN)
    return bot

def check_env_vars():
    """Проверяет наличие и корректность всех необходимых переменных окружения"""
    required_vars = {
        'BOT_TOKEN': str,
        'BOT_ID': int,
        'MAIN_GROUP': int,
        'MONITORED_GROUPS': str,  # Список групп через запятую
        'ADMIN_IDS': str,  # Список админов через запятую
        'SPECIAL_SEND_USER': int
    }
    
    missing_vars = []
    invalid_vars = []
    
    for var_name, var_type in required_vars.items():
        value = os.getenv(var_name)
        if value is None:
            missing_vars.append(var_name)
            continue
            
        try:
            if var_type == int:
                int(value)
            elif var_name in ['MONITORED_GROUPS', 'ADMIN_IDS']:
                # Проверяем, что все ID в списке являются числами
                for id_str in value.split(','):
                    int(id_str.strip())
        except ValueError:
            invalid_vars.append(var_name)
    
    if missing_vars or invalid_vars:
        error_msg = []
        if missing_vars:
            error_msg.append(f"Отсутствуют переменные окружения: {', '.join(missing_vars)}")
        if invalid_vars:
            error_msg.append(f"Некорректный формат переменных: {', '.join(invalid_vars)}")
        raise ValueError('\n'.join(error_msg))
    
    logger.info("Все переменные окружения корректно настроены")
    logger.info(f"Основная группа: {os.getenv('MAIN_GROUP')}")
    logger.info(f"Отслеживаемые группы: {os.getenv('MONITORED_GROUPS')}")
    logger.info(f"Количество администраторов: {len(os.getenv('ADMIN_IDS').split(','))}")

async def main():
    """Основная функция запуска бота"""
    global bot, bot_start_time, is_running
    
    # Проверяем переменные окружения
    try:
        check_env_vars()
    except ValueError as e:
        logger.error(f"Ошибка в конфигурации:\n{e}")
        return

    # Устанавливаем время запуска
    bot_start_time = datetime.now().timestamp()
    logger.info(f"Бот запущен: {datetime.fromtimestamp(bot_start_time)}")
    
    # Инициализируем бота
    bot = await initialize_bot()
    
    # Запускаем проверку истекших голосований
    asyncio.create_task(check_vote_expiration())
    
    try:
        await dp.start_polling(bot)
    except Exception as e:
        logger.error(f"Ошибка при запуске бота: {e}")
    finally:
        await bot.session.close()

if __name__ == "__main__":
    try:
        sys.exit(asyncio.run(main()))
    except Exception as e:
        logger.error(f"Ошибка при запуске бота: {e}")
        sys.exit(1) 