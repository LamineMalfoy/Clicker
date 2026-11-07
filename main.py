import vk_api
from vk_api.bot_longpoll import VkBotLongPoll, VkBotEventType
from vk_api.keyboard import VkKeyboard, VkKeyboardColor
from vk_api.utils import get_random_id
from vk_api.upload import VkUpload
import sqlite3
import json
import random
import time
import threading
import math
import re
import html
import requests
import os
import secrets
import socket
from PIL import Image, ImageDraw, ImageFont
from datetime import datetime, timedelta, timezone

# --- ЗАГРУЗКА КОНФИГУРАЦИИ ---
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(BASE_DIR, 'config.json')
DB_PATH = os.path.join(BASE_DIR, 'users.bd')

with open(CONFIG_PATH, 'r', encoding='utf-8') as f:
    config = json.load(f)

try:
    _prava_fp = os.path.join(os.path.dirname(os.path.abspath(__file__)), "prava.json")
    with open(_prava_fp, "r", encoding="utf-8") as _prf:
        PRAVA_DATA = json.load(_prf)
except Exception:
    PRAVA_DATA = {}

TOKEN = config['token']
USER_TOKEN = config.get('user_token', '')
COMMUNITY_CHECK_TOKEN = (config.get('community_check_token') or '').strip() or (USER_TOKEN or '').strip()
try:
    COMMUNITY_STATS_ADMIN_ID = int(config.get('community_stats_admin_id', 0))
except (TypeError, ValueError):
    COMMUNITY_STATS_ADMIN_ID = 0
GROUP_ID = config['group_id']
VERIFICATION_GROUP_SCREEN = (config.get('verification_group_screen') or '').strip()
VERIFICATION_GROUP_URL = (config.get('verification_group_url') or '').strip() or (
    f'https://vk.com/{VERIFICATION_GROUP_SCREEN}' if VERIFICATION_GROUP_SCREEN else ''
)
_cfg_v = config.get("verification_cooperation_enabled")
if _cfg_v is None:
    VERIFICATION_COOPERATION_ENABLED = True
elif isinstance(_cfg_v, bool):
    VERIFICATION_COOPERATION_ENABLED = _cfg_v
else:
    _cfg_vs = str(_cfg_v).strip().lower()
    VERIFICATION_COOPERATION_ENABLED = _cfg_vs not in ("0", "false", "no", "off", "выкл")
_cfg_nm = config.get("neural_moderation_enabled")
if _cfg_nm is None:
    NEURAL_MODERATION_ENABLED = True
elif isinstance(_cfg_nm, bool):
    NEURAL_MODERATION_ENABLED = _cfg_nm
else:
    _cfg_nms = str(_cfg_nm).strip().lower()
    NEURAL_MODERATION_ENABLED = _cfg_nms not in ("0", "false", "no", "off", "выкл")
try:
    ADMIN_ID = int(config['admin_id'])
except (TypeError, ValueError):
    ADMIN_ID = 0
try:
    GROUP_OWNER_ID = int(config.get('group_owner_id', ADMIN_ID))
except (TypeError, ValueError):
    GROUP_OWNER_ID = int(ADMIN_ID)
_raw_wnids = config.get("withdrawal_notify_user_ids") or []
WITHDRAWAL_NOTIFY_USER_IDS = []
if isinstance(_raw_wnids, list):
    for _w in _raw_wnids:
        try:
            WITHDRAWAL_NOTIFY_USER_IDS.append(int(_w))
        except (TypeError, ValueError):
            pass
WITHDRAWAL_NOTIFY_USER_IDS = tuple(sorted({x for x in WITHDRAWAL_NOTIFY_USER_IDS if x > 0}))
# Google Gemini (AI Studio / Google AI): https://ai.google.dev/api
GEMINI_API_KEY = (config.get('gemini_api_key') or config.get('genapi_api_key') or '').strip()
GEMINI_MODEL = (config.get('gemini_model') or config.get('genapi_model_slug') or 'gemini-2.0-flash').strip()
GEMINI_LAST_ERROR = ""
_menu_keyboard_user_id = None
TECH_WORKS_ENABLED = False
GROUP_SUB_CHECK_INTERVAL_SEC = 120.0
_quiz_hours_cfg = config.get('official_event_hours_msk', [15])
try:
    if isinstance(_quiz_hours_cfg, str):
        _quiz_hours_cfg = [x.strip() for x in _quiz_hours_cfg.split(',') if x.strip()]
    _quiz_hours_parsed = tuple(
        sorted({int(h) for h in _quiz_hours_cfg if 0 <= int(h) <= 23})
    )
    if not _quiz_hours_parsed:
        _quiz_hours_parsed = (15,)
except Exception:
    _quiz_hours_parsed = (15,)


def _cfg_bool(val, default):
    if val is None:
        return default
    if isinstance(val, bool):
        return val
    s = str(val).strip().lower()
    if s in ("1", "true", "yes", "on", "вкл"):
        return True
    if s in ("0", "false", "no", "off", "выкл"):
        return False
    return default


def _cfg_int(val, default):
    try:
        return int(val)
    except Exception:
        return int(default)


def _cfg_float(val, default):
    try:
        return float(val)
    except Exception:
        return float(default)


# Дефолты из config.json; переопределение владельцем — в bot_economy (!настройки / !ui+ / !ui-).
CONFIG_UI_SHOW_WORK = _cfg_bool(config.get("ui_show_work"), False)
CONFIG_UI_SHOW_CASINO_HELP = _cfg_bool(config.get("ui_show_casino_help"), False)
CONFIG_UI_SHOW_FULL_STAFF_HELP = _cfg_bool(config.get("ui_show_full_staff_in_help"), False)
# Обратная совместимость имён
UI_SHOW_WORK = CONFIG_UI_SHOW_WORK
UI_SHOW_CASINO_HELP = CONFIG_UI_SHOW_CASINO_HELP
UI_SHOW_FULL_STAFF_HELP = CONFIG_UI_SHOW_FULL_STAFF_HELP

if not GEMINI_API_KEY:
    _tggpt_cfg = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'TGGPT', 'config_local.py')
    if os.path.isfile(_tggpt_cfg):
        try:
            with open(_tggpt_cfg, 'r', encoding='utf-8') as _f:
                _txt = _f.read()
                for _pat in (
                    r'GEMINI_API_KEY\s*=\s*["\']([^"\']+)["\']',
                    r'GENAPI_API_KEY\s*=\s*["\']([^"\']+)["\']',
                ):
                    _m = re.search(_pat, _txt)
                    if _m:
                        GEMINI_API_KEY = _m.group(1).strip()
                        break
        except Exception:
            pass

CLICK_BOOST_PRICE = _cfg_int(config.get("click_boost_price"), 2_000_000_000_000)
CLICK_BOOST_BONUS = _cfg_int(config.get("click_boost_bonus"), 12_000_000_000)
CLICK_BOOST_DAYS = _cfg_int(config.get("click_boost_days"), 7)
SUB_FEED_DISCOUNT_PERCENT = _cfg_int(config.get("sub_feed_discount_percent"), 5)
REPOST_DAILY_REWARD = _cfg_int(config.get("repost_daily_reward"), 150_000_000_000)
REPOST_MAX_DAYS = _cfg_int(config.get("repost_max_days"), 3)
REPOST_CHECK_INTERVAL_SEC = _cfg_int(config.get("repost_check_interval_sec"), 600)
REPOST_WARN_BLOCK_HOURS = _cfg_int(config.get("repost_warn_block_hours"), 24)
# Дефолты экономики (переопределяются таблицей bot_economy, см. !экономика).
# Выше порога богатства клик ниже — но не ниже разумного минимума относительно корма.
WEALTH_7MM_CLICK_THRESHOLD = _cfg_int(config.get("wealth_7mm_click_threshold"), 7 * 1_000_000_000_000)
CLICK_BASE_DEFAULT = _cfg_int(config.get("click_base_default"), 24_000_000_000)
CLICK_BASE_FROM_7MM = _cfg_int(config.get("click_base_from_7mm"), 24_000_000_000)
FEED_PRICE_PER_PERCENT_DEFAULT = _cfg_int(config.get("feed_price_per_percent_default"), 18_000_000_000)  # дороже за 1% сытости
# Кнопка «Покормить за все деньги»: фиксированная цена 1.5мм (не списание всего баланса).
FEED_ALL_FIXED_COST = _cfg_int(config.get("feed_all_fixed_cost"), 1_500_000_000_000)
TAX_COOLDOWN_SEC_DEFAULT = _cfg_int(config.get("tax_cooldown_sec_default"), 12 * 3600)
TAX_COOLDOWN_SEC_FAST = _cfg_int(config.get("tax_cooldown_sec_fast"), 6 * 3600)
STEAL_FAST_PRICE_PER_DAY = _cfg_int(config.get("steal_fast_price_per_day"), 2_000_000_000_000)
STEAL_FAST_COOLDOWN_SEC = _cfg_int(config.get("steal_fast_cooldown_sec"), 2 * 3600)
STEAL_SHIELD_PRICE = _cfg_int(config.get("steal_shield_price"), 5_000_000_000_000)
STEAL_SHIELD_DURATION_SEC = _cfg_int(config.get("steal_shield_duration_sec"), 6 * 3600)
# Базовая добыча банка (мк): случайно от HEIST_MIN_MK до min(потолок, HEIST_MK_BASE + рабы * шаг).
HEIST_MIN_MK = _cfg_int(config.get("heist_min_mk"), 5)
HEIST_MAX_MK_CAP = _cfg_int(config.get("heist_max_mk_cap"), 100)
HEIST_MK_BASE = _cfg_int(config.get("heist_mk_base"), 5)
HEIST_MK_PER_REF = _cfg_int(config.get("heist_mk_per_ref"), 5)
HEIST_COOLDOWN_SEC = _cfg_int(config.get("heist_cooldown_sec"), 24 * 3600)
HEIST_JAIL_SEC = _cfg_int(config.get("heist_jail_sec"), 6 * 3600)
HEIST_FAIL_FINE_PERCENT = _cfg_int(config.get("heist_fail_fine_percent"), 20)
HEIST_FAIL_CHANCE = _cfg_float(config.get("heist_fail_chance"), 0.35)
KLAD_ENABLED = _cfg_bool(config.get("klad_enabled"), False)
KLAD_COOLDOWN_SEC = _cfg_int(config.get("klad_cooldown_sec"), 3600)
KLAD_MIN_MK = _cfg_int(config.get("klad_min_mk"), 200)
KLAD_MAX_MK = _cfg_int(config.get("klad_max_mk"), 300)
KLAD_APP_URL = (config.get("klad_app_url") or "").strip()
KLAD_IMAGE_PATH = (config.get("klad_image_path") or "").strip()
EVENT_IMAGE_PATH = (config.get("event_image_path") or "/home/container/event.png").strip()
REGISTER_CHAT_WRITE_URL = (config.get("register_chat_write_url") or "https://vk.ru/write-237333137?ref=1073822275").strip()
MULTICHAT_REG_HINT_COOLDOWN_SEC = _cfg_int(config.get("multichat_reg_hint_cooldown_sec"), 300)
# VK messages.send: attachment вида sticker{sticker_id}
STICKER_NEW_USER_ID = _cfg_int(config.get("sticker_new_user_id"), 1822)
STICKER_REVIEW_THANKS_ID = _cfg_int(config.get("sticker_review_thanks_id"), 1718)
MAX_REWARDED_COMMENTS_PER_POST = _cfg_int(config.get("max_rewarded_comments_per_post"), 5)
# Беседа 2000000003: кнопки Профиль / Клад / Топы; полная игра и вывод — в ЛС.
RESTRICTED_CHAT_PEER_ID = _cfg_int(config.get("restricted_chat_peer_id"), 2000000003)
ADMIN_CHAT_PEER_ID = _cfg_int(config.get("admin_chat_peer_id"), 2000000004)
QUIZ_CHAT_PEER_ID = _cfg_int(config.get("quiz_chat_peer_id"), 2000000003)
QUIZ_START_HOURS_MSK = _quiz_hours_parsed
QUIZ_PRESTART_MINUTES = _cfg_int(config.get("quiz_prestart_minutes"), 3)
QUIZ_NUMBER_MIN = _cfg_int(config.get("quiz_number_min"), 1)
QUIZ_NUMBER_MAX = _cfg_int(config.get("quiz_number_max"), 100)
QUIZ_REWARD = _cfg_int(config.get("quiz_reward"), 2_500_000_000_000)  # 2.5мм
QUIZ_EVENT_DURATION_SEC = _cfg_int(config.get("quiz_event_duration_sec"), 2 * 3600)


def _quiz_hours_label_msk():
    """Текст расписания викторины: «15:00» или «12:00 и 18:00»."""
    hrs = QUIZ_START_HOURS_MSK
    if not hrs:
        return "—"
    return " и ".join(f"{int(h):02d}:00" for h in hrs)


DEPOSIT_DAILY_RATE = _cfg_float(config.get("deposit_daily_rate"), 0.005)  # 0.5% в день
PERSONAL_EVENT_START_MSK = datetime(2026, 4, 9, 9, 0, 0)
PERSONAL_EVENT_END_MSK = datetime(2026, 4, 15, 9, 0, 0)
PERSONAL_EVENT_PLAY_90_MIN_SEC = 90 * 60
PERSONAL_EVENT_PLAY_120_MIN_SEC = 120 * 60
PERSONAL_EVENT_DONATE_REQ = 2_000_000_000_000
PERSONAL_EVENT_REWARD_DAY3 = 1_000_000_000_000
PERSONAL_EVENT_REWARD_DAY4 = 3_000_000_000_000
PERSONAL_EVENT_REWARD_DAY5 = 5_000_000_000_000
PERSONAL_EVENT_REWARD_DAY6 = 1_000_000_000_000
# Базовая выручка за клик ×1.5 (целочисленно: числитель/знаменатель).
CLICK_INCOME_MULT_NUM = 3
CLICK_INCOME_MULT_DEN = 2
# После всех бонусов к выплате за клик: ÷1.2 (целочисленно 5/6).
CLICK_INCOME_SCALE_DOWN_NUM = 5
CLICK_INCOME_SCALE_DOWN_DEN = 6
# Единственный разрешённый URL профиля для сверки (никаких других хостов).
# Локальные JSON-дампы внешнего профиля для команды !набор: {id}.json (без сетевой интеграции).
NABOR_PROFILE_JSON_DIR = "/home/container/jsons"
PERSONAL_EVENT_MAX_ACTIVITY_DELTA_SEC = 120
STEAL_COOLDOWN_SEC = 3 * 3600
AUTOCLICK_BAN_SEC = 20 * 60
AUTOCLICK_PATTERN_LEN = 6
AUTOCLICK_INTERVAL_SPREAD_SEC = 0.02
# Сообщений до показа капчи (галочка): случайно от 1 до N. Раньше в цикле было до ~40 — чаще капча при меньшем N.
CAPTCHA_MESSAGES_UNTIL_MAX = 18
CHAT_SPAM_WINDOW_SEC = 60
CHAT_SPAM_REPEAT_LIMIT = 5
SPAM_MUTE_SEC = 30 * 60
OFFICIAL_CHAT_WARN_BAN_THRESHOLD = 5
MODERATION_WARN_BAN_THRESHOLD = 3
MSG_DELETED_NOTICE_DELETE_SEC = 3
SPAM_MUTE_BOT_NOTICE_DELETE_SEC = 8
REACTION_DELETE_ADMIN_ID = 682039325
OFFICIAL_ADMIN_IDS = [ADMIN_ID, 682039325]
OFFICIAL_ADMIN_IDS_SET = {int(x) for x in OFFICIAL_ADMIN_IDS}
MIN_REGISTERED_FOR_KLAD_CHAT = _cfg_int(config.get("min_registered_for_klad_chat"), 20)
PET_UPGRADE_BASE_COST = _cfg_int(config.get("pet_upgrade_base_cost"), 500_000_000_000)
MAX_PET_LEVEL = _cfg_int(config.get("max_pet_level"), 25)
PROJECT_ROLE_LABELS = {
    "owner": "👑 ВЛАДЕЛЕЦ ПРОЕКТА",
    "deputy_owner": "🛡 ЗАМ ВЛАДЕЛЕЦ ПРОЕКТА",
    "moderator": "🧩 МОДЕРАТОР ПРОЕКТА",
    "sponsor": "💎 СПОНСОР",
}
ALLOWED_PROJECT_ROLES = frozenset({"owner", "deputy_owner", "moderator", "sponsor"})
USER_NAME_CACHE = {}
USER_NAME_CACHE_TTL_SEC = 300
GPT_LAST_ANSWER = {}
# Беседа: последняя !проверка — cmid команды и ответа бота (чистим после кика).
PROVERKA_PENDING_CMIDS = {}
SPAM_CLEANUP_INTERVAL_SEC = 30
_last_spam_cleanup_at = 0.0
ANTIBOT_TIMING_STATE = {}
ANTIBOT_CAPTCHA_TRACK = {}
# user_id цели → кто выдал принудительную капчу (!капча / антибот), для лога в админ-чат при сдаче/провале
ADMIN_FORCED_CAPTCHA_ISSUER = {}
LAST_SUPPORT_CLEANUP_TS = 0.0
OFFICIAL_NORM_CHAT_PEER_ID = ADMIN_CHAT_PEER_ID
OFFICIAL_NORM_ROLE_RULES = {
    "moderator": {"hours": 1.5, "answers": 1},
}
PROMOTION_REQUIREMENTS = {}
OFFICIAL_QUESTION_WORDS = (
    "как",
    "почему",
    "зачем",
    "где",
    "когда",
    "что",
    "кто",
    "можно",
    "нужно",
    "помогите",
    "подскажите",
    "не работает",
    "не могу",
)
OFFICIAL_INSULT_MUTE_SEC = 30 * 60
# Только персональные оскорбления (п.2.1). Мат без адреса к людям не ведёт к автомуту — см. промпт Gemini ниже.
OFFICIAL_INSULT_WORDS = (
    "тупой",
    "тупая",
    "дебил",
    "идиот",
    "даун",
    "придурок",
    "чмо",
    "ублюд",
    "мразь",
    "гандон",
)
LAST_OFFICIAL_NORM_DAY_CHECK = ""
LAST_OFFICIAL_NORM_REVIEW_SENT_DAY = ""
OFFICIAL_NORM_REVIEW_ADMIN_ID = 743621163
OFFICIAL_NORM_REVIEW_HOUR_MSK = 21
OZON_WORK_CD_SEC = 30
OZON_WORK_WRONG_CD_SEC = 5 * 60
OZON_WORK_REWARD_MIN_MK = 50
OZON_WORK_REWARD_MAX_MK = 100

# --- ПАПКИ ДЛЯ ДАННЫХ ---
STATS_DIR = os.path.expanduser("~/storage/shared/VK/clicker/stats")
os.makedirs(STATS_DIR, exist_ok=True)

# --- ЗАЩИТА ОТ ДУБЛЯ ПРОЦЕССА ---
_single_instance_socket = None
try:
    _single_instance_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    _single_instance_socket.bind(("127.0.0.1", 47000 + (int(GROUP_ID) % 1000)))
except Exception:
    print("Экземпляр бота уже запущен. Завершаю этот процесс, чтобы не было дублей ответов и рассинхрона БД.")
    raise SystemExit(0)

# --- АВТОРИЗАЦИЯ VK ---
vk_session = vk_api.VkApi(token=TOKEN)
vk = vk_session.get_api()
longpoll = None
_LONGPOLL_NET_FAIL_STREAK = 0  # подряд сетевые сбои long poll (для паузы между попытками)
vk_upload = VkUpload(vk_session)

vk_user = None
vk_user_session = None
if USER_TOKEN:
    try:
        vk_user_session = vk_api.VkApi(token=USER_TOKEN)
        vk_user = vk_user_session.get_api()
    except Exception as e:
        print(f"Ошибка токена пользователя: {e}")

vk_community = None
if COMMUNITY_CHECK_TOKEN:
    try:
        if vk_user and COMMUNITY_CHECK_TOKEN == (USER_TOKEN or '').strip():
            vk_community = vk_user
        else:
            vk_community = vk_api.VkApi(token=COMMUNITY_CHECK_TOKEN).get_api()
    except Exception as e:
        print(f"Ошибка токена проверки подписки (community_check_token / user_token): {e}")

# --- БАЗА ДАННЫХ ---
db = sqlite3.connect(DB_PATH, check_same_thread=False, timeout=15)
cursor = db.cursor()
try:
    cursor.execute("PRAGMA journal_mode=WAL")
    cursor.execute("PRAGMA synchronous=NORMAL")
    cursor.execute("PRAGMA temp_store=MEMORY")
    cursor.execute("PRAGMA cache_size=-32000")
except Exception:
    pass

cursor.execute('''
    CREATE TABLE IF NOT EXISTS users (
        user_id INTEGER PRIMARY KEY,
        balance INTEGER DEFAULT 1000000000,
        energy INTEGER DEFAULT 50,
        fed INTEGER DEFAULT 80,
        is_registered INTEGER DEFAULT 0,
        is_banned INTEGER DEFAULT 0,
        captcha_answer INTEGER DEFAULT NULL,
        last_clicks TEXT DEFAULT '[]',
        last_click_timestamp REAL DEFAULT 0,
        review_state INTEGER DEFAULT 0,
        temp_review_text TEXT DEFAULT '',
        ban_until REAL DEFAULT 0,
        msg_until_captcha INTEGER DEFAULT 10,
        bot_username TEXT DEFAULT '',
        bot_photo_url TEXT DEFAULT '',
        bot_photo_attach TEXT DEFAULT '',
        referrer_id INTEGER DEFAULT NULL,
        pending_referrer INTEGER DEFAULT NULL,
        total_earned_from_refs INTEGER DEFAULT 0,
        total_earned_from_heists INTEGER DEFAULT 0,
        total_wealth_bonus INTEGER DEFAULT 0,
        heist_last_at REAL DEFAULT 0,
        heist_jail_until REAL DEFAULT 0,
        pet_id INTEGER DEFAULT 0,
        pet_name TEXT DEFAULT '',
        last_steal_at REAL DEFAULT 0,
        klad_loot_count INTEGER DEFAULT 0,
        click_boost_until REAL DEFAULT 0,
        last_tax_collect REAL DEFAULT 0,
        tax_fast_until REAL DEFAULT 0,
        chat_msg_count INTEGER DEFAULT 0,
        last_multichat_reg_hint_at REAL DEFAULT 0
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS withdrawals (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER,
        amount INTEGER,
        comment_id INTEGER,
        status TEXT DEFAULT 'Ожидает отправки',
        rating TEXT DEFAULT '',
        review_text TEXT DEFAULT ''
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS liked_posts (
        user_id INTEGER,
        post_id INTEGER
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS stats_history (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        timestamp REAL,
        users_count INTEGER
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS support_questions (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        question_text TEXT NOT NULL,
        status TEXT DEFAULT 'new',
        created_at REAL NOT NULL,
        taken_by INTEGER DEFAULT 0,
        taken_at REAL DEFAULT 0,
        answer_text TEXT DEFAULT '',
        answered_at REAL DEFAULT 0
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS moderator_actions (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        moderator_id INTEGER NOT NULL,
        action_type TEXT NOT NULL,
        amount INTEGER DEFAULT 0,
        created_at REAL NOT NULL
    )
''')

# Обновление таблиц
try: cursor.execute("ALTER TABLE users ADD COLUMN last_click_timestamp REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN review_state INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN temp_review_text TEXT DEFAULT ''")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN ban_until REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN msg_until_captcha INTEGER DEFAULT 10")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN bot_username TEXT DEFAULT ''")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN bot_photo_url TEXT DEFAULT ''")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN bot_photo_attach TEXT DEFAULT ''")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN referrer_id INTEGER DEFAULT NULL")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN pending_referrer INTEGER DEFAULT NULL")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN total_earned_from_refs INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN total_earned_from_heists INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN total_wealth_bonus INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN heist_last_at REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN heist_jail_until REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN pet_id INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN pet_name TEXT DEFAULT ''")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN last_steal_at REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN klad_loot_count INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN click_boost_until REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN last_tax_collect REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN tax_fast_until REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN chat_msg_count INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN last_multichat_reg_hint_at REAL DEFAULT 0")
except: pass
cursor.execute('''
    CREATE TABLE IF NOT EXISTS wall_comment_rewards (
        user_id INTEGER NOT NULL,
        post_id INTEGER NOT NULL,
        comment_id INTEGER NOT NULL,
        amount INTEGER NOT NULL,
        created REAL NOT NULL,
        PRIMARY KEY (user_id, post_id, comment_id)
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS promocodes (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        code TEXT NOT NULL UNIQUE,
        amount INTEGER NOT NULL,
        max_activations INTEGER NOT NULL,
        used_count INTEGER NOT NULL DEFAULT 0,
        created_by INTEGER,
        created_at REAL NOT NULL
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS promo_claims (
        promo_id INTEGER NOT NULL,
        user_id INTEGER NOT NULL,
        claimed_at REAL NOT NULL,
        PRIMARY KEY (promo_id, user_id)
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS user_transactions (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        tx_type TEXT NOT NULL,
        amount INTEGER NOT NULL,
        note TEXT NOT NULL DEFAULT '',
        created_at REAL NOT NULL
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS klad_cooldowns (
        peer_id INTEGER PRIMARY KEY,
        last_at REAL NOT NULL
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS klad_loot_events (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        peer_id INTEGER NOT NULL,
        reward INTEGER NOT NULL,
        created REAL NOT NULL
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS bot_economy (
        key TEXT PRIMARY KEY,
        value INTEGER NOT NULL
    )
''')
try:
    cursor.execute("SELECT value FROM bot_economy WHERE key = '_feed_migrated_x11'")
    if not cursor.fetchone():
        cursor.execute("SELECT value FROM bot_economy WHERE key = ?", ("feed_portion",))
        row = cursor.fetchone()
        if row:
            v = max(1, (int(row[0] or 0) * 11) // 10)
            cursor.execute(
                "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
                ("feed_portion", v),
            )
        cursor.execute(
            "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
            ("_feed_migrated_x11", 1),
        )
        db.commit()
except Exception:
    pass
cursor.execute('''
    CREATE TABLE IF NOT EXISTS user_bans (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        issued_by INTEGER NOT NULL DEFAULT 0,
        reason TEXT NOT NULL,
        created_at REAL NOT NULL,
        until_ts REAL NOT NULL DEFAULT 0,
        source_chat INTEGER NOT NULL DEFAULT 0
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS chat_spam_log (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        peer_id INTEGER NOT NULL,
        msg_norm TEXT NOT NULL,
        created_at REAL NOT NULL
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS user_moderation_warns (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        issued_by INTEGER NOT NULL DEFAULT 0,
        message_snippet TEXT NOT NULL DEFAULT '',
        peer_id INTEGER NOT NULL DEFAULT 0,
        source_kind TEXT NOT NULL DEFAULT 'sms',
        created_at REAL NOT NULL
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS repost_campaigns (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        repost_owner_id INTEGER NOT NULL,
        repost_post_id INTEGER NOT NULL,
        source_owner_id INTEGER NOT NULL,
        source_post_id INTEGER NOT NULL,
        started_at REAL NOT NULL,
        days_granted INTEGER NOT NULL DEFAULT 1,
        days_verified INTEGER NOT NULL DEFAULT 0,
        active INTEGER NOT NULL DEFAULT 1
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS repost_reward_locks (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        campaign_id INTEGER NOT NULL,
        user_id INTEGER NOT NULL,
        day_no INTEGER NOT NULL,
        amount INTEGER NOT NULL,
        unlock_at REAL NOT NULL,
        deducted INTEGER NOT NULL DEFAULT 0,
        UNIQUE(campaign_id, day_no)
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS repost_user_claims (
        user_id INTEGER NOT NULL,
        source_owner_id INTEGER NOT NULL,
        source_post_id INTEGER NOT NULL,
        claimed_at REAL NOT NULL,
        PRIMARY KEY (user_id, source_owner_id, source_post_id)
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS repost_reward_blocks (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        blocked_until REAL NOT NULL,
        reason TEXT NOT NULL DEFAULT '',
        created_by INTEGER NOT NULL DEFAULT 0,
        fine_amount INTEGER NOT NULL DEFAULT 0,
        created_at REAL NOT NULL
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS repost_warnings (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        issued_by INTEGER NOT NULL DEFAULT 0,
        reason TEXT NOT NULL DEFAULT '',
        created_at REAL NOT NULL
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS pascha_egg_invites (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        owner_id INTEGER NOT NULL,
        target_id INTEGER NOT NULL,
        token TEXT NOT NULL UNIQUE,
        status TEXT NOT NULL DEFAULT 'pending',
        created_at REAL NOT NULL
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS contests (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        created_at REAL NOT NULL,
        results_end_ts REAL,
        results_end_label TEXT,
        body_preview TEXT,
        prize INTEGER DEFAULT 0,
        winners INTEGER DEFAULT 1,
        status TEXT DEFAULT 'active',
        final_post_text TEXT DEFAULT ''
    )
''')
cursor.execute('''
    CREATE TABLE IF NOT EXISTS contest_participants (
        contest_id INTEGER NOT NULL,
        user_id INTEGER NOT NULL,
        joined_at REAL NOT NULL,
        PRIMARY KEY (contest_id, user_id)
    )
''')
cursor.execute("CREATE INDEX IF NOT EXISTS idx_contests_status ON contests(status)")
cursor.execute("CREATE INDEX IF NOT EXISTS idx_contest_participants_contest ON contest_participants(contest_id)")
cursor.execute("CREATE INDEX IF NOT EXISTS idx_umw_user_id ON user_moderation_warns(user_id)")
cursor.execute("CREATE INDEX IF NOT EXISTS idx_users_balance ON users(balance DESC)")
cursor.execute("CREATE INDEX IF NOT EXISTS idx_users_chat_msg_count ON users(chat_msg_count DESC)")
cursor.execute("CREATE INDEX IF NOT EXISTS idx_users_referrer_id ON users(referrer_id)")
cursor.execute("CREATE INDEX IF NOT EXISTS idx_klad_loot_user_id ON klad_loot_events(user_id)")
cursor.execute("CREATE INDEX IF NOT EXISTS idx_user_transactions_user_id_id ON user_transactions(user_id, id DESC)")
# Только типы, что показываются в банке — ускоряет ORDER BY id DESC LIMIT без скана «лишних» строк.
try:
    cursor.execute(
        """
        CREATE INDEX IF NOT EXISTS idx_user_transactions_bank_view
        ON user_transactions(user_id, id DESC)
        WHERE tx_type IN ('promo','transfer_in','transfer_out')
        """
    )
except Exception:
    pass
cursor.execute("CREATE INDEX IF NOT EXISTS idx_repost_campaigns_active_user ON repost_campaigns(active, user_id)")
cursor.execute("CREATE INDEX IF NOT EXISTS idx_repost_locks_user_unlock ON repost_reward_locks(user_id, unlock_at)")
cursor.execute("CREATE INDEX IF NOT EXISTS idx_repost_blocks_user_until ON repost_reward_blocks(user_id, blocked_until)")
cursor.execute("CREATE INDEX IF NOT EXISTS idx_repost_warnings_user_id ON repost_warnings(user_id)")
try: cursor.execute("ALTER TABLE withdrawals ADD COLUMN rating TEXT DEFAULT ''")
except: pass
try: cursor.execute("ALTER TABLE withdrawals ADD COLUMN review_text TEXT DEFAULT ''")
except: pass
try: cursor.execute("ALTER TABLE withdrawals ADD COLUMN admin_dm_peer INTEGER DEFAULT NULL")
except: pass
try: cursor.execute("ALTER TABLE withdrawals ADD COLUMN admin_dm_cmid INTEGER DEFAULT NULL")
except: pass
try: cursor.execute("ALTER TABLE withdrawals ADD COLUMN admin_chat_peer INTEGER DEFAULT NULL")
except: pass
try: cursor.execute("ALTER TABLE withdrawals ADD COLUMN admin_chat_cmid INTEGER DEFAULT NULL")
except: pass
try: cursor.execute("ALTER TABLE withdrawals ADD COLUMN admin_cmd_peer INTEGER DEFAULT NULL")
except: pass
try: cursor.execute("ALTER TABLE withdrawals ADD COLUMN admin_cmd_cmid INTEGER DEFAULT NULL")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN pascha_egg_done INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN pascha_full_withdraw INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN group_sub_last INTEGER DEFAULT -1")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN group_sub_ever INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN group_sub_checked_at REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN spam_mute_until REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN official_warns INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN project_role TEXT DEFAULT ''")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN staff_balance INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN forced_captcha_answer INTEGER DEFAULT NULL")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN forced_captcha_prompt TEXT DEFAULT ''")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN forced_captcha_attempts INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN captcha_token TEXT DEFAULT ''")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN captcha_message_id INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN steal_fast_until REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN steal_shield_until REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN moderation_warn_count INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN chat_banned INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN chat_ban_until REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN bank_balance INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN last_deposit_interest_day TEXT DEFAULT ''")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN event_day1_claimed INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN event_day2_claimed INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN event_day3_claimed INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN event_day4_claimed INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN event_day5_claimed INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN event_day6_claimed INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN event_play_seconds INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN event_last_activity_ts REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN event_success_rob_count INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN event_notified_mask INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN donated_total INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN donation_wait_custom INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN registered_at REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN donation_pending_amount INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN op_contest_draft TEXT DEFAULT ''")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN staff_reprimands INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN staff_reprimands_from_owner INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN staff_reprimands_from_other INTEGER DEFAULT 0")
except: pass
try:
    cursor.execute(
        "UPDATE users SET staff_reprimands_from_owner = COALESCE(staff_reprimands, 0) "
        "WHERE COALESCE(staff_reprimands_from_owner, 0) = 0 AND COALESCE(staff_reprimands, 0) > 0"
    )
    db.commit()
except Exception:
    pass
try:
    cursor.execute(
        "UPDATE users SET staff_reprimands = 0, staff_reprimands_from_owner = 0, staff_reprimands_from_other = 0 "
        "WHERE TRIM(COALESCE(project_role, '')) = '' "
        "AND (COALESCE(staff_reprimands, 0) != 0 OR COALESCE(staff_reprimands_from_owner, 0) != 0 "
        "OR COALESCE(staff_reprimands_from_other, 0) != 0)"
    )
    db.commit()
except Exception:
    pass
try: cursor.execute("ALTER TABLE users ADD COLUMN last_deputy_promo_at REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN ask_question_wait INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN mod_reply_question_id INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN moderator_public_id INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN role_assigned_at REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN ask_question_wait_started_at REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN promo_click_bonus_percent INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN is_twin INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN casino_last_at REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN promo_click_bonus_until REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE promocodes ADD COLUMN reward_kind TEXT DEFAULT 'money'")
except: pass
try: cursor.execute("ALTER TABLE promocodes ADD COLUMN boost_percent INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE promocodes ADD COLUMN boost_duration_sec INTEGER DEFAULT 604800")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN shop_click_boost_expire_notified INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN shop_steal_fast_expire_notified INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN shop_steal_shield_expire_notified INTEGER DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN ozon_work_cooldown_until REAL DEFAULT 0")
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN ozon_work_target INTEGER DEFAULT 0")
except: pass

cursor.execute(
    """
    CREATE TABLE IF NOT EXISTS admin_op_ui_messages (
        user_id INTEGER NOT NULL,
        peer_id INTEGER NOT NULL,
        conversation_message_id INTEGER NOT NULL,
        created_at REAL,
        PRIMARY KEY (user_id, peer_id, conversation_message_id)
    )
    """
)
cursor.execute(
    """
    CREATE TABLE IF NOT EXISTS official_chat_messages (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        peer_id INTEGER NOT NULL,
        user_id INTEGER NOT NULL,
        text TEXT NOT NULL DEFAULT '',
        created_at REAL NOT NULL,
        is_staff INTEGER NOT NULL DEFAULT 0
    )
    """
)
cursor.execute(
    """
    CREATE TABLE IF NOT EXISTS official_chat_questions (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        peer_id INTEGER NOT NULL,
        asker_id INTEGER NOT NULL,
        question_text TEXT NOT NULL,
        question_cmid INTEGER NOT NULL DEFAULT 0,
        status TEXT NOT NULL DEFAULT 'new',
        created_at REAL NOT NULL,
        answered_by INTEGER NOT NULL DEFAULT 0,
        answered_at REAL NOT NULL DEFAULT 0,
        answer_text TEXT NOT NULL DEFAULT ''
    )
    """
)
cursor.execute(
    """
    CREATE TABLE IF NOT EXISTS official_chat_daily (
        user_id INTEGER NOT NULL,
        day_key TEXT NOT NULL,
        first_at REAL NOT NULL DEFAULT 0,
        last_at REAL NOT NULL DEFAULT 0,
        msg_count INTEGER NOT NULL DEFAULT 0,
        answers_count INTEGER NOT NULL DEFAULT 0,
        report_done INTEGER NOT NULL DEFAULT 0,
        reprimand_issued INTEGER NOT NULL DEFAULT 0,
        updated_at REAL NOT NULL DEFAULT 0,
        PRIMARY KEY (user_id, day_key)
    )
    """
)
cursor.execute("CREATE INDEX IF NOT EXISTS idx_official_chat_questions_peer_status ON official_chat_questions(peer_id, status, created_at DESC)")
cursor.execute("CREATE INDEX IF NOT EXISTS idx_official_chat_daily_day ON official_chat_daily(day_key)")
try: cursor.execute("ALTER TABLE users ADD COLUMN staff_rules_ack INTEGER DEFAULT 0")
except: pass

db.commit()


# --- ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ ---
def format_balance(val):
    return f"{val:,}".replace(',', '.')

def format_short(val):
    if val >= 1_000_000_000_000:
        return f"{val / 1_000_000_000_000:g}мм"
    elif val >= 1_000_000_000:
        return f"{val / 1_000_000_000:g}мк"
    return format_balance(val)

def format_click(val):
    if val >= 1_000_000_000_000:
        return f"{val / 1_000_000_000_000:.1f}мм"
    elif val >= 1_000_000_000:
        return f"{int(val / 1_000_000_000)}мк"
    return format_balance(val)


def format_mk_mm_pair(val):
    """Мк целым (если без дроби), мм ровно 3 знака — как в уведомлениях админу: 5481 мк, 5.481 мм."""
    mk = val / 1_000_000_000
    mm = val / 1_000_000_000_000
    mk_r = round(mk)
    if abs(mk - mk_r) < 1e-6:
        mk_s = str(int(mk_r))
    else:
        mk_s = f"{mk:.6f}".rstrip('0').rstrip('.')
    mm_s = f"{mm:.3f}"
    return f"{mk_s} мк, {mm_s} мм"


def format_mm_tenths(val):
    """Только мм, округление до десятых (для выводов)."""
    return f"{(float(val) / 1_000_000_000_000):.1f} мм"


def format_withdraw_mm_plain(val):
    """Только мм без мк: простые цифры (для текста заявки пользователю)."""
    mm_s = f"{(int(val) / 1_000_000_000_000):.12f}".rstrip('0').rstrip('.')
    if not mm_s:
        mm_s = "0"
    return f"{mm_s} мм"


def format_withdraw_mm_rounded(val):
    """Только мм, округление (для админа и обсуждения)."""
    return format_mm_tenths(val)


def format_withdraw_sum_caption(val):
    """Совместимость старых вызовов: по умолчанию отдаём мм без мк."""
    return format_withdraw_mm_plain(val)


def format_time_left_sec(seconds):
    if seconds <= 0:
        return "сейчас"
    sec = int(seconds)
    h, r = divmod(sec, 3600)
    m, s = divmod(r, 60)
    parts = []
    if h:
        parts.append(f"{h} ч")
    if m:
        parts.append(f"{m} мин")
    if not parts and s:
        parts.append(f"{s} сек")
    if not parts:
        parts.append("меньше минуты")
    return " ".join(parts)


def parse_amount(val_str):
    val_str = val_str.lower().replace(',', '.').replace(' ', '')
    if val_str.endswith('мм'):
        return int(float(val_str[:-2]) * 1_000_000_000_000)
    elif val_str.endswith('мк'):
        return int(float(val_str[:-2]) * 1_000_000_000)
    return int(float(val_str))


ECON_KEY_CLICK_LOW = "click_low"
ECON_KEY_CLICK_HIGH = "click_high"
ECON_KEY_FEED = "feed_portion"
ECON_KEY_FEED_ALL = "feed_all_cost"
ECON_KEY_WEALTH = "wealth_threshold"
ECON_KEY_CLICK_BOOST_PRICE = "click_boost_price"
ECON_KEY_CLICK_BOOST_BONUS = "click_boost_bonus"
ECON_KEY_CLICK_BOOST_DAYS = "click_boost_days"
KAZNA_ECON_KEY = "kazna_balance"
DEPOSITS_DISABLED_KEY = "deposits_disabled"
CASINO_ENABLED_KEY = "casino_enabled"


def _get_kazna_balance():
    """Сумма валюты в казне (пожертвования минус выводы через -казна)."""
    try:
        cursor.execute("SELECT value FROM bot_economy WHERE key = ?", (KAZNA_ECON_KEY,))
        row = cursor.fetchone()
        if row is not None:
            return max(0, int(row[0] or 0))
        cursor.execute("SELECT COALESCE(SUM(donated_total), 0) FROM users")
        seed = int((cursor.fetchone() or [0])[0] or 0)
        cursor.execute(
            "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
            (KAZNA_ECON_KEY, int(seed)),
        )
        db.commit()
        return int(seed)
    except Exception:
        return 0


def _add_kazna(amount):
    amt = int(amount or 0)
    if amt <= 0:
        return
    cur = _get_kazna_balance()
    cursor.execute(
        "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
        (KAZNA_ECON_KEY, int(cur + amt)),
    )
    db.commit()


def _take_kazna(amount):
    amt = int(amount or 0)
    if amt <= 0:
        return False
    cur = _get_kazna_balance()
    if cur < amt:
        return False
    cursor.execute(
        "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
        (KAZNA_ECON_KEY, int(cur - amt)),
    )
    db.commit()
    return True


def _deposits_disabled():
    """Депозиты в боте отключены навсегда (раздел «Банк» снят)."""
    return True


def _disable_deposits_refund_everyone():
    """Отключить депозиты и вернуть все bank_balance на balance. Возвращает (число счетов, сумма возврата)."""
    cursor.execute(
        "SELECT COUNT(*), COALESCE(SUM(bank_balance), 0) FROM users WHERE COALESCE(bank_balance, 0) > 0"
    )
    row = cursor.fetchone() or (0, 0)
    n_acc = int(row[0] or 0)
    total_ref = int(row[1] or 0)
    cursor.execute(
        "UPDATE users SET balance = COALESCE(balance, 0) + COALESCE(bank_balance, 0), "
        "bank_balance = 0, last_deposit_interest_day = '' "
        "WHERE COALESCE(bank_balance, 0) > 0"
    )
    cursor.execute(
        "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
        (DEPOSITS_DISABLED_KEY, 1),
    )
    db.commit()
    return n_acc, total_ref


def _economy_get(key, default):
    try:
        cursor.execute("SELECT value FROM bot_economy WHERE key = ?", (key,))
        row = cursor.fetchone()
        if row is not None:
            return max(1, int(row[0]))
    except Exception:
        pass
    return max(1, int(default))


def _economy_values_normalized():
    low_raw = _economy_get(ECON_KEY_CLICK_LOW, CLICK_BASE_DEFAULT)
    high_raw = _economy_get(ECON_KEY_CLICK_HIGH, CLICK_BASE_FROM_7MM)
    feed_raw = _economy_get(ECON_KEY_FEED, FEED_PRICE_PER_PERCENT_DEFAULT)
    wealth_raw = _economy_get(ECON_KEY_WEALTH, WEALTH_7MM_CLICK_THRESHOLD)

    # Защита от «минусовой» экономики:
    # 1 клик = 1 энергия, а 1 энергия примерно стоит 2% сытости (см. реген в фоне).
    # Балансируем под целевой чистый плюс на цикле корм -> клики.
    max_feed_safe = max(1, (min(low_raw, high_raw) * 4) // 10)
    feed = min(feed_raw, max_feed_safe)
    min_click_safe = max(1, (feed * 25) // 10)  # >= 2.5 * feed
    low = max(low_raw, min_click_safe)
    high = max(high_raw, min_click_safe)
    return low, high, feed, max(1, int(wealth_raw))


def get_economy_click_low():
    low, _, _, _ = _economy_values_normalized()
    return low


def get_economy_click_high():
    _, high, _, _ = _economy_values_normalized()
    return high


def get_economy_feed_portion():
    _, _, feed, _ = _economy_values_normalized()
    return feed


def get_economy_feed_all_cost():
    """Фиксированная цена кнопки «Покормить за все деньги» (не зависит от % сытости)."""
    return _economy_get(ECON_KEY_FEED_ALL, FEED_ALL_FIXED_COST)


def get_effective_feed_portion(boost_active=False):
    base_feed = int(get_economy_feed_portion())
    if not boost_active:
        return base_feed
    discount = max(0, min(95, int(SUB_FEED_DISCOUNT_PERCENT)))
    return max(1, (base_feed * (100 - discount)) // 100)


def get_economy_wealth_threshold():
    _, _, _, wealth = _economy_values_normalized()
    return wealth


def get_economy_click_boost_price():
    return _economy_get(ECON_KEY_CLICK_BOOST_PRICE, CLICK_BOOST_PRICE)


def get_economy_click_boost_bonus():
    return _economy_get(ECON_KEY_CLICK_BOOST_BONUS, CLICK_BOOST_BONUS)


def get_economy_click_boost_days():
    return max(1, min(365, int(_economy_get(ECON_KEY_CLICK_BOOST_DAYS, CLICK_BOOST_DAYS))))


def economy_admin_summary_text():
    wth = get_economy_wealth_threshold()
    low = get_economy_click_low()
    high = get_economy_click_high()
    low_eff = (low * CLICK_INCOME_MULT_NUM) // CLICK_INCOME_MULT_DEN
    high_eff = (high * CLICK_INCOME_MULT_NUM) // CLICK_INCOME_MULT_DEN
    low_eff = (low_eff * CLICK_INCOME_SCALE_DOWN_NUM) // CLICK_INCOME_SCALE_DOWN_DEN
    high_eff = (high_eff * CLICK_INCOME_SCALE_DOWN_NUM) // CLICK_INCOME_SCALE_DOWN_DEN
    feed = get_economy_feed_portion()
    feed_all = get_economy_feed_all_cost()
    b_price = get_economy_click_boost_price()
    b_bonus = get_economy_click_boost_bonus()
    b_days = get_economy_click_boost_days()
    return (
        "⚙ Экономика бота\n\n"
        f"Текущие параметры:\n"
        f"- Клик при балансе < {format_mk_mm_pair(wth)}: +{format_click(low_eff)}$ (база {format_click(low)}$ ×{CLICK_INCOME_MULT_NUM}/{CLICK_INCOME_MULT_DEN} ×{CLICK_INCOME_SCALE_DOWN_NUM}/{CLICK_INCOME_SCALE_DOWN_DEN})\n"
        f"- Клик при балансе ≥ порога: +{format_click(high_eff)}$ (база {format_click(high)}$ ×{CLICK_INCOME_MULT_NUM}/{CLICK_INCOME_MULT_DEN} ×{CLICK_INCOME_SCALE_DOWN_NUM}/{CLICK_INCOME_SCALE_DOWN_DEN})\n"
        f"- Корм: {format_click(feed)}$ за 1% сытости\n"
        f"- «За все деньги» (одна кнопка): {format_click(feed_all)}$\n"
        f"- Порог «богатого» клика: {format_mk_mm_pair(wth)}\n"
        f"- Усилитель клика в магазине: +{format_click(b_bonus)}$ к клику, цена {format_click(b_price)}$, срок {b_days} дн.\n\n"
        "Изменить (суммы как в !выдать — 35мк, 1.5мм):\n"
        "- !экономика показать\n"
        "- !экономика клик_низкий 35мк\n"
        "- !экономика клик_высокий 20мк\n"
        "- !экономика корм 18мк\n"
        "- !экономика корм_все 1.5мм — фикс. цена кнопки «за все деньги»\n"
        "- !экономика порог 7мм\n"
        "- !экономика буст_цена 2мм — цена усилителя клика\n"
        "- !экономика буст_бонус 12мк — бонус к клику от усилителя\n"
        "- !экономика буст_дни 7 — длительность усилителя (1–365 дней)\n\n"
        "Коротко:\n"
        "- !эко кн 35мк\n"
        "- !эко кв 20мк\n"
        "- !эко к 18мк\n"
        "- !эко квсе 1.5мм\n"
        "- !эко п 7мм\n"
        "- !эко бц 2мм  !эко бб 12мк  !эко бд 7"
    )

def get_id_by_domain(domain):
    raw = (domain or "").strip()
    mention_match = re.search(r'\[([^\|]+)\|', raw)
    if mention_match:
        raw = mention_match.group(1)

    s = raw.strip().replace('@', '')
    s = re.sub(r'^https?://', '', s, flags=re.IGNORECASE)
    s = re.sub(r'^(?:m\.)?vk\.(?:com|ru)/', '', s, flags=re.IGNORECASE)
    s = s.strip()
    # Берем только screen name / id без хвостов URL.
    s = re.split(r'[/?#]', s, maxsplit=1)[0].strip()

    if s.startswith('id') and s[2:].isdigit():
        return int(s[2:])
    if s.isdigit():
        return int(s)
    try:
        res = vk.utils.resolveScreenName(screen_name=s)
        if res and res.get('type') == 'user':
            return res.get('object_id')
    except Exception:
        pass
    return None


def admin_create_promocode(created_by, code_raw, amount_str, max_activations):
    code = (code_raw or '').strip().upper()
    if len(code) < 2 or len(code) > 32:
        return None, "Код промо: от 2 до 32 символов."
    if not re.match(r'^[A-Z0-9_]+$', code):
        return None, "Код: только латиница (A–Z), цифры и символ _."
    cursor.execute("SELECT 1 FROM promocodes WHERE code = ?", (code,))
    if cursor.fetchone():
        return None, "Промокод с таким кодом уже существует."
    if max_activations < 1:
        return None, "Число активаций должно быть ≥ 1."
    try:
        amount_game = parse_amount((amount_str or '').strip())
    except (TypeError, ValueError, OverflowError):
        return None, "Некорректная сумма. Пример: 200мк или 1.5мк"
    if amount_game <= 0:
        return None, "Сумма награды должна быть больше нуля."
    now = time.time()
    cursor.execute(
        "INSERT INTO promocodes (code, amount, max_activations, used_count, created_by, created_at, reward_kind, boost_percent, boost_duration_sec) "
        "VALUES (?, ?, ?, 0, ?, ?, 'money', 0, 604800)",
        (code, amount_game, max_activations, created_by, now),
    )
    db.commit()
    return code, None


def admin_create_promocode_click_boost(created_by, code_raw, percent, max_activations, duration_days):
    """Промокод: +percent% к выручке за клик на duration_days дней (награда не деньгами). Только схема БД."""
    code = (code_raw or "").strip().upper()
    if len(code) < 2 or len(code) > 32:
        return None, "Код промо: от 2 до 32 символов."
    if not re.match(r"^[A-Z0-9_]+$", code):
        return None, "Код: только латиница (A–Z), цифры и символ _."
    try:
        pct = int(percent)
    except (TypeError, ValueError):
        return None, "Некорректный процент."
    if pct < 1 or pct > 100:
        return None, "Процент: от 1 до 100."
    if max_activations < 1:
        return None, "Число активаций должно быть ≥ 1."
    try:
        ddays = int(duration_days)
    except (TypeError, ValueError):
        ddays = 7
    ddays = max(1, min(365, ddays))
    dur_sec = ddays * 86400
    cursor.execute("SELECT 1 FROM promocodes WHERE code = ?", (code,))
    if cursor.fetchone():
        return None, "Промокод с таким кодом уже существует."
    now = time.time()
    cursor.execute(
        "INSERT INTO promocodes (code, amount, max_activations, used_count, created_by, created_at, reward_kind, boost_percent, boost_duration_sec) "
        "VALUES (?, 0, ?, 0, ?, ?, 'click_boost', ?, ?)",
        (code, max_activations, created_by, now, pct, dur_sec),
    )
    db.commit()
    return code, None


def admin_delete_promocode(code_raw):
    """Удалить промокод и связанные активации. Код нормализуется как при создании."""
    code = (code_raw or "").strip().upper()
    if len(code) < 2 or len(code) > 32:
        return False, "Код промо: от 2 до 32 символов."
    if not re.match(r"^[A-Z0-9_]+$", code):
        return False, "Код: только латиница (A–Z), цифры и символ _."
    cursor.execute("SELECT id FROM promocodes WHERE code = ?", (code,))
    row = cursor.fetchone()
    if not row:
        return False, "Промокод с таким кодом не найден."
    pid = int(row[0])
    cursor.execute("DELETE FROM promo_claims WHERE promo_id = ?", (pid,))
    cursor.execute("DELETE FROM promocodes WHERE id = ?", (pid,))
    db.commit()
    return True, None


def promolist_admin_text():
    try:
        cursor.execute(
            "SELECT code, amount, max_activations, used_count, "
            "COALESCE(reward_kind, 'money'), COALESCE(boost_percent, 0), COALESCE(boost_duration_sec, 604800), "
            "(max_activations - used_count) AS remaining "
            "FROM promocodes "
            "WHERE used_count < max_activations "
            "ORDER BY remaining ASC, id DESC LIMIT 25"
        )
        rows = cursor.fetchall()
        if not rows:
            return "🎟 Промокоды\n\nАктивных промокодов сейчас нет."
        lines = ["🎟 Список активных промокодов\n"]
        for code, amt, mx, us, rk, bp, bd, remaining in rows:
            if (rk or "money") == "click_boost":
                days = max(1, int(bd or 604800) // 86400)
                lines.append(
                    f"\n- {code} — +{int(bp)}% к клику, {days} дн. ({us}/{mx} акт., осталось: {remaining})"
                )
            else:
                lines.append(
                    f"\n- {code} — +{format_short(amt)}$ ({us}/{mx} акт., осталось: {remaining})"
                )
        return "".join(lines)[:3900]
    except Exception:
        return "Не удалось загрузить список промокодов."


def redeem_promocode(user_id, code_raw):
    code = (code_raw or "").strip().upper()
    if len(code) < 2:
        return False, "Укажите код: промо КОД"
    try:
        with db:
            cursor.execute(
                "SELECT id, amount, max_activations, used_count, COALESCE(reward_kind, 'money'), "
                "COALESCE(boost_percent, 0), COALESCE(boost_duration_sec, 604800) FROM promocodes WHERE code = ?",
                (code,),
            )
            row = cursor.fetchone()
            if not row:
                raise ValueError("not_found")
            pid, amount, mx, used = row[0], row[1], row[2], row[3]
            reward_kind = row[4] or "money"
            boost_pct = int(row[5] or 0)
            boost_dur = int(row[6] or 604800)
            if used >= mx:
                raise ValueError("exhausted")
            cursor.execute("SELECT 1 FROM promo_claims WHERE promo_id = ? AND user_id = ?", (pid, user_id))
            if cursor.fetchone():
                raise ValueError("claimed")
            cursor.execute(
                "UPDATE promocodes SET used_count = used_count + 1 WHERE id = ? AND used_count < max_activations",
                (pid,),
            )
            if cursor.rowcount != 1:
                raise ValueError("race")
            _, _ = get_user(user_id)
            now_ts = time.time()
            if reward_kind == "click_boost" and boost_pct > 0:
                until_ts = now_ts + float(max(60, boost_dur))
                cursor.execute(
                    "UPDATE users SET promo_click_bonus_percent = ?, promo_click_bonus_until = ? WHERE user_id = ?",
                    (int(boost_pct), float(until_ts), int(user_id)),
                )
                cursor.execute(
                    "INSERT INTO promo_claims (promo_id, user_id, claimed_at) VALUES (?, ?, ?)",
                    (pid, user_id, now_ts),
                )
                _log_user_transaction(cursor, user_id, "promo_boost", int(boost_pct), f"Промокод {code} +{boost_pct}% к клику")
            else:
                cursor.execute("UPDATE users SET balance = balance + ? WHERE user_id = ?", (amount, user_id))
                cursor.execute(
                    "INSERT INTO promo_claims (promo_id, user_id, claimed_at) VALUES (?, ?, ?)",
                    (pid, user_id, now_ts),
                )
                _log_user_transaction(cursor, user_id, "promo", int(amount), f"Промокод {code}")
        u, _ = get_user(user_id)
        code_show = (code_raw or "").strip().upper()
        if reward_kind == "click_boost" and boost_pct > 0:
            days_show = max(1, int(boost_dur) // 86400)
            return True, (
                "🎉 Промокод успешно активирован!\n\n"
                f"🔑 Код: {code_show}\n"
                f"⚡ Бонус к выручке за клик: +{int(boost_pct)}% на {days_show} дн.\n"
                f"💰 Баланс: {format_click(u[1])}$"
            )
        return True, (
            "🎉 Промокод успешно активирован!\n\n"
            f"🔑 Код: {code_show}\n"
            f"💸 Начислено: +{format_click(amount)}$\n"
            f"💰 Ваш баланс: {format_click(u[1])}$"
        )
    except ValueError as e:
        m = str(e)
        if m == "not_found":
            return (
                False,
                "❌ Промокод недействителен.\n\n"
                "Промокоды в официальной беседе сообщества выкладываются почти каждый день.",
            )
        if m == "exhausted":
            return (
                False,
                "❌ Промокод недействителен.\n\n"
                "Промокоды в официальной беседе сообщества выкладываются почти каждый день.",
            )
        if m == "claimed":
            return False, "Вы уже активировали этот промокод."
        return False, "Промокод только что исчерпали. Попробуйте другой."
    except Exception:
        return False, "Ошибка активации. Попробуйте позже."


def build_board_msg(user_id, username, amount, status, rating="", review_text=""):
    if status == "Успешно выполнена":
        status_str = "🟢 Успешно выполнена"
    elif status == "Отклонено":
        status_str = "🔴 Отклонено"
    elif status == "Отменено":
        status_str = "⚪ Отменено"
    else:
        status_str = "🟡 Ожидает отправки"
        
    msg = (
        f"Пользователь @id{user_id} ({username})\n"
        f"Сумма: {format_withdraw_mm_rounded(amount)}\n"
        f"Статус: {status_str}"
    )
    if review_text and rating:
        msg += f"\n{rating} Отзыв: {review_text}"
    return msg

def get_user(user_id):
    """Кортеж пользователя и флаг: True если только что создана новая строка (первая активность в боте)."""
    cursor.execute(
        "SELECT user_id, balance, energy, fed, is_registered, is_banned, captcha_answer, last_clicks, last_click_timestamp, "
        "review_state, temp_review_text, ban_until, msg_until_captcha, click_boost_until, last_tax_collect, tax_fast_until, "
        "COALESCE(promo_click_bonus_percent, 0), COALESCE(promo_click_bonus_until, 0), "
        "COALESCE(registered_at, 0), COALESCE(is_twin, 0) "
        "FROM users WHERE user_id = ?",
        (user_id,),
    )
    user = cursor.fetchone()
    if user:
        return user, False
    # Параллельно process_message и process_wall_reply (thread) могли вставить строку — INSERT OR IGNORE + повторный SELECT.
    tc0 = db.total_changes
    cursor.execute(
        "INSERT OR IGNORE INTO users (user_id, msg_until_captcha) VALUES (?, ?)",
        (user_id, random.randint(1, CAPTCHA_MESSAGES_UNTIL_MAX)),
    )
    db.commit()
    is_new = db.total_changes > tc0
    cursor.execute(
        "SELECT user_id, balance, energy, fed, is_registered, is_banned, captcha_answer, last_clicks, last_click_timestamp, "
        "review_state, temp_review_text, ban_until, msg_until_captcha, click_boost_until, last_tax_collect, tax_fast_until, "
        "COALESCE(promo_click_bonus_percent, 0), COALESCE(promo_click_bonus_until, 0), "
        "COALESCE(registered_at, 0), COALESCE(is_twin, 0) "
        "FROM users WHERE user_id = ?",
        (user_id,),
    )
    user = cursor.fetchone()
    if not user:
        raise RuntimeError(f"get_user: нет записи после INSERT OR IGNORE, user_id={user_id}")
    return user, is_new

def update_user(user_id, field, value):
    cursor.execute(f"UPDATE users SET {field} = ? WHERE user_id = ?", (value, user_id))
    db.commit()


def update_user_fields(user_id, **fields):
    """Обновить несколько полей пользователя одним UPDATE + одним COMMIT."""
    if not fields:
        return
    cols = []
    values = []
    for k, v in fields.items():
        cols.append(f"{k} = ?")
        values.append(v)
    values.append(user_id)
    cursor.execute(f"UPDATE users SET {', '.join(cols)} WHERE user_id = ?", tuple(values))
    db.commit()


def _owner_clear_game_cooldowns(target_id):
    """Сброс игровых таймеров ограбления/кражи/налогов/спам-мута/капчи/ускорителей и активного блока репост-штрафа."""
    tid = int(target_id)
    now = float(time.time())
    try:
        cursor.execute("INSERT OR IGNORE INTO users (user_id) VALUES (?)", (tid,))
        update_user_fields(
            tid,
            heist_last_at=0.0,
            heist_jail_until=0.0,
            last_steal_at=0.0,
            last_tax_collect=0.0,
            steal_fast_until=0.0,
            steal_shield_until=0.0,
            click_boost_until=0.0,
            tax_fast_until=0.0,
            spam_mute_until=0.0,
            promo_click_bonus_percent=0,
            promo_click_bonus_until=0.0,
            forced_captcha_answer=None,
            forced_captcha_prompt="",
            forced_captcha_attempts=0,
        )
        cursor.execute(
            "DELETE FROM repost_reward_blocks WHERE user_id = ? AND blocked_until > ?",
            (tid, now),
        )
        db.commit()
        return True
    except Exception as e:
        print(f"[_owner_clear_game_cooldowns] {e}")
        try:
            db.rollback()
        except Exception:
            pass
        return False


def _log_user_transaction(local_cursor, user_id, tx_type, amount, note):
    local_cursor.execute(
        "INSERT INTO user_transactions (user_id, tx_type, amount, note, created_at) VALUES (?, ?, ?, ?, ?)",
        (int(user_id), str(tx_type), int(amount), str(note or ""), time.time()),
    )


def _transfer_target_allowed(sender_id, target_id):
    allow_any_transfer_target = int(sender_id) == 743621163
    # Весь админ-состав может переводить любым пользователям.
    if _is_admin_user(sender_id):
        return True
    return allow_any_transfer_target or _is_owner(target_id) or _is_deputy_owner(target_id) or _is_official_admin_id(target_id)


def _perform_transfer(sender_id, target_id, amount):
    if int(target_id) == int(sender_id):
        return False, "Нельзя переводить самому себе."
    if int(amount) <= 0:
        return False, "Сумма должна быть больше нуля."
    if not _transfer_target_allowed(sender_id, target_id):
        return False, "Перевод доступен только на счета админ-состава."

    cursor.execute(
        "SELECT COALESCE(balance, 0), COALESCE(staff_balance, 0) FROM users WHERE user_id = ?",
        (int(sender_id),),
    )
    row_from = cursor.fetchone() or (0, 0)
    sender_balance = int(row_from[0] or 0)
    sender_staff = int(row_from[1] or 0)
    total_sender = sender_balance + sender_staff
    if total_sender < int(amount):
        return False, (
            f"Недостаточно средств.\nНужно: {format_click(amount)}$\n"
            f"У вас: {format_click(total_sender)}$ (наличные {format_click(sender_balance)}$, служебные {format_click(sender_staff)}$)"
        )

    _, _ = get_user(int(target_id))
    cursor.execute("SELECT COALESCE(balance, 0) FROM users WHERE user_id = ?", (int(target_id),))
    row_to = cursor.fetchone() or (0,)
    target_balance = int(row_to[0] or 0)

    # Сначала списываем служебные (выданные администрацией), затем обычные наличные.
    need = int(amount)
    take_staff = min(need, sender_staff)
    need -= take_staff
    take_balance = min(need, sender_balance)
    new_sender_balance = int(sender_balance - take_balance)
    new_sender_staff = int(sender_staff - take_staff)
    new_target_balance = int(target_balance + int(amount))
    cursor.execute(
        "UPDATE users SET balance = ?, staff_balance = ? WHERE user_id = ?",
        (new_sender_balance, new_sender_staff, int(sender_id)),
    )
    cursor.execute("UPDATE users SET balance = ? WHERE user_id = ?", (new_target_balance, int(target_id)))
    # Явно фиксируем изменения перед формированием топов в отдельных запросах/соединениях.
    cursor.execute("UPDATE users SET balance = balance WHERE user_id IN (?, ?)", (int(sender_id), int(target_id)))
    _log_user_transaction(cursor, sender_id, "transfer_out", -int(amount), f"Перевод @id{target_id}")
    _log_user_transaction(cursor, target_id, "transfer_in", int(amount), f"Перевод от @id{sender_id}")
    db.commit()
    _log_moderator_action(sender_id, "transfer_out", int(amount))
    target_mention = get_user_mention_with_name(target_id)
    sender_left_total = new_sender_balance + new_sender_staff
    return (
        True,
        "✅ Перевод выполнен\n\n"
        f"Получатель: {target_mention}\n"
        f"Сумма: {format_click(amount)}$\n"
        f"Остаток всего: {format_click(sender_left_total)}$ (наличные {format_click(new_sender_balance)}$, служебные {format_click(new_sender_staff)}$)",
    )


_BANK_HISTORY_TX_TYPES = ("promo", "transfer_in", "transfer_out")
_BANK_HISTORY_NOTE_MAX = 100


def _bank_transactions_text(user_id, limit=8):
    uid = int(user_id)
    lim = max(1, min(int(limit), 24))
    ph = ",".join("?" * len(_BANK_HISTORY_TX_TYPES))
    cursor.execute(
        f"SELECT tx_type, amount, note FROM user_transactions "
        f"WHERE user_id = ? AND tx_type IN ({ph}) "
        f"ORDER BY id DESC LIMIT ?",
        (uid, *_BANK_HISTORY_TX_TYPES, lim),
    )
    rows = cursor.fetchall()
    if not rows:
        return "Нет операций."
    lines = []
    for tx_type, amount, note in rows:
        amt = abs(int(amount or 0))
        note_s = (note or "")[:_BANK_HISTORY_NOTE_MAX]
        if tx_type == "promo":
            lines.append(f"+ Промокод: +{format_click(amt)}$")
        elif tx_type == "transfer_in":
            lines.append(f"+ Перевод: +{format_click(amt)}$ ({note_s})")
        elif tx_type == "transfer_out":
            lines.append(f"- Перевод: {format_click(amt)}$ ({note_s})")
    return "\n".join(lines)


def _nabor_json_register_date_to_dmy(raw):
    """Из '2024-07-13 23:43:30' → '13.07.2024'."""
    s = (raw or "").strip()
    if not s or s.lower() == "неизвестно":
        return None
    m = re.match(r"^(\d{4})-(\d{2})-(\d{2})", s)
    if not m:
        return None
    y, mo, d = m.group(1), m.group(2), m.group(3)
    return f"{d}.{mo}.{y}"


def _nabor_json_roles_string(profile):
    """Роли из JSON-дампа: модерация, creator, dev, президент — без вампира и премиума."""
    if not profile:
        return "неизвестно"
    parts = []
    try:
        ml = int(profile.get("moderator_level") or 0)
    except (TypeError, ValueError):
        ml = 0
    mod_labels = {
        1: "Модератор-стажёр",
        2: "Мл. модератор",
        3: "Модератор",
        4: "Ст. модератор",
        5: "Администратор",
        6: "Ст. администратор",
    }
    if ml in mod_labels:
        parts.append(mod_labels[ml])
    if profile.get("creator"):
        parts.append("Creator")
    if profile.get("admin_dev"):
        parts.append("Разработчик")
    if profile.get("president"):
        parts.append("Президент")
    if not parts:
        return "нет"
    return ", ".join(parts)


def _nabor_chat_msg_count_text(chat_msg_count):
    """Количество сообщений в чатах бота (как в топе: format_balance + смс), без места."""
    try:
        cnt = int(chat_msg_count or 0)
    except (TypeError, ValueError):
        return "неизвестно"
    return f"{format_balance(cnt)} смс"


def _load_nabor_profile_json_file(vk_user_id):
    """
    Читает NABOR_PROFILE_JSON_DIR/{id}.json.
    Возвращает (dict|None, status): status 'ok' | 'missing' | 'bad_json'.
    """
    uid = int(vk_user_id)
    path = os.path.join(NABOR_PROFILE_JSON_DIR, f"{uid}.json")
    if not os.path.isfile(path):
        return None, "missing"
    try:
        with open(path, "r", encoding="utf-8") as f:
            raw = json.load(f)
        if not isinstance(raw, dict):
            return None, "bad_json"
        return raw, "ok"
    except (OSError, json.JSONDecodeError, UnicodeDecodeError):
        return None, "bad_json"


def _load_nabor_profile_from_json(vk_user_id):
    """Профиль из локального файла {NABOR_PROFILE_JSON_DIR}/{id}.json."""
    uid = int(vk_user_id)
    data, st = _load_nabor_profile_json_file(uid)
    if st == "missing":
        return None, None
    if st == "bad_json" or data is None:
        return None, "Не удалось прочитать JSON (файл повреждён или не объект)."
    try:
        if int(data.get("id") or 0) not in (0, uid):
            return data, f"⚠️ В JSON id={data.get('id')}, ожидался {uid}."
    except (TypeError, ValueError):
        pass
    return data, None


def _nabor_candidate_report_text(target_user_id, profile, profile_warn):
    """Текст карточки кандидата для команды !набор."""
    tid = int(target_user_id)
    display_name = get_user_name(tid)
    link_line = f"[id{tid}|{display_name}]"

    if profile is None:
        site_date = "неизвестно"
        roles_s = "неизвестно"
    else:
        rd_raw = profile.get("register_date")
        site_date = _nabor_json_register_date_to_dmy(rd_raw) if isinstance(rd_raw, str) else None
        if not site_date and rd_raw:
            site_date = str(rd_raw).strip()
        if not site_date:
            site_date = "не указана"
        roles_s = _nabor_json_roles_string(profile)

    lines = [
        link_line,
        "",
        f"Дата регистрации (по JSON): {site_date}",
        f"Роли (по JSON): {roles_s}",
        "",
    ]

    try:
        cursor.execute(
            "SELECT COALESCE(is_registered, 0), COALESCE(registered_at, 0), COALESCE(chat_msg_count, 0) "
            "FROM users WHERE user_id = ?",
            (tid,),
        )
        row = cursor.fetchone()
    except Exception:
        row = None

    if not row:
        clicker_reg = "неизвестно"
        msg_line = _nabor_chat_msg_count_text(0)
    else:
        reg_ok = int(row[0] or 0) == 1
        reg_ts = float(row[1] or 0)
        msg_n = int(row[2] or 0)
        if reg_ok and reg_ts > 0:
            clicker_reg = datetime.fromtimestamp(reg_ts, tz=timezone.utc).strftime("%d.%m.%Y")
        elif reg_ok:
            clicker_reg = "да (дата не сохранена)"
        else:
            clicker_reg = "нет"
        msg_line = _nabor_chat_msg_count_text(msg_n)

    lines.append(f"Дата регистрации в кликере: {clicker_reg}")
    lines.append(f"Сообщений: {msg_line}")

    if profile_warn:
        lines.extend(["", str(profile_warn)])
    return "\n".join(lines)[:3900]


def _issue_forced_captcha(target_id, source_peer, issued_by=0, reason_text="Антибот-проверка"):
    _, _ = get_user(int(target_id))
    a = random.randint(10, 99)
    b = random.randint(10, 99)
    prompt = f"🧩 Проверка на автоматизацию.\nРешите пример: {a} + {b} = ?\nУ вас 3 попытки."
    update_user_fields(int(target_id), forced_captcha_answer=a + b, forced_captcha_prompt=prompt, forced_captcha_attempts=0)
    try:
        if int(issued_by) > 0:
            ADMIN_FORCED_CAPTCHA_ISSUER[int(target_id)] = int(issued_by)
    except Exception:
        pass
    send_msg(int(target_id), prompt, None)
    send_admin_chat_log(f"[КАПЧА] {reason_text}\nКому: {get_user_mention_with_name(target_id)}\nИнициатор: {get_user_mention_with_name(issued_by) if int(issued_by) > 0 else 'бот'}")
    if int(source_peer) > 0:
        send_msg(int(source_peer), f"Капча отправлена пользователю {get_user_mention_with_name(target_id)}.", kb_for_peer(int(source_peer)))


def _check_antibot_timing(user_id, reply_peer, text, payload_cmd):
    # Подозрительные интервалы команд — только в ЛС с ботом, не в беседах
    if _is_multichat_peer(reply_peer):
        return
    if not _is_private_bot_dialog(reply_peer, user_id):
        return
    if _is_admin_user(user_id):
        return
    has_command = bool(payload_cmd) or bool(_normalize_chat_command(text))
    if not has_command:
        return
    now = time.time()
    st = ANTIBOT_TIMING_STATE.get(int(user_id), {"last_ts": 0.0, "last_dt": 0.0, "rep": 0, "last_alert_ts": 0.0})
    last_ts = float(st.get("last_ts") or 0.0)
    dt = now - last_ts if last_ts > 0 else 0.0
    if last_ts > 0 and 0.35 <= dt <= 6.0:
        prev_dt = float(st.get("last_dt") or 0.0)
        if prev_dt > 0 and abs(dt - prev_dt) <= 0.12:
            st["rep"] = int(st.get("rep") or 0) + 1
        else:
            st["rep"] = 1
        st["last_dt"] = dt
    else:
        st["rep"] = 0
    st["last_ts"] = now
    ANTIBOT_TIMING_STATE[int(user_id)] = st
    if int(st.get("rep") or 0) >= 4 and (now - float(st.get("last_alert_ts") or 0.0)) >= 90:
        mention = get_user_mention_with_name(user_id)
        try:
            mid_ab = send_msg(
                int(ADMIN_CHAT_PEER_ID),
                f"[АНТИБОТ] Пользователь {mention} подозрительно часто выполняет команды.",
                get_antibot_captcha_kb(int(user_id)),
            )
            cmid_ab = _vk_conversation_message_id(int(mid_ab or 0)) or int(mid_ab or 0)
            ANTIBOT_CAPTCHA_TRACK[int(user_id)] = {
                "peer_id": int(ADMIN_CHAT_PEER_ID),
                "cmid": int(cmid_ab),
            }
        except Exception:
            pass
        st["last_alert_ts"] = now
        ANTIBOT_TIMING_STATE[int(user_id)] = st


def klad_chat_last_ts(peer_id):
    try:
        cursor.execute("SELECT last_at FROM klad_cooldowns WHERE peer_id = ?", (int(peer_id),))
        row = cursor.fetchone()
        return float(row[0]) if row else 0.0
    except sqlite3.OperationalError:
        cursor.execute(
            "CREATE TABLE IF NOT EXISTS klad_cooldowns (peer_id INTEGER PRIMARY KEY, last_at REAL NOT NULL)"
        )
        db.commit()
        return 0.0


def klad_chat_set_last_ts(peer_id, ts):
    try:
        cursor.execute(
            "INSERT OR REPLACE INTO klad_cooldowns (peer_id, last_at) VALUES (?, ?)",
            (int(peer_id), float(ts)),
        )
        db.commit()
    except sqlite3.OperationalError:
        cursor.execute(
            "CREATE TABLE IF NOT EXISTS klad_cooldowns (peer_id INTEGER PRIMARY KEY, last_at REAL NOT NULL)"
        )
        db.commit()
        cursor.execute(
            "INSERT OR REPLACE INTO klad_cooldowns (peer_id, last_at) VALUES (?, ?)",
            (int(peer_id), float(ts)),
        )
        db.commit()


def count_registered_players_in_chat(peer_id):
    try:
        members = vk.messages.getConversationMembers(peer_id=int(peer_id))
        profiles = members.get('profiles') or []
        ids = [int(p.get('id')) for p in profiles if int(p.get('id') or 0) > 0]
        if not ids:
            return 0
        ph = ",".join(["?"] * len(ids))
        cursor.execute(
            f"SELECT COUNT(*) FROM users WHERE is_registered = 1 AND user_id IN ({ph})",
            tuple(ids),
        )
        return int(cursor.fetchone()[0] or 0)
    except Exception:
        return 0


def _multichat_member_user_ids(peer_id):
    """Положительные member_id участников беседы (без сообществ)."""
    try:
        raw = vk.messages.getConversationMembers(peer_id=int(peer_id))
        out = []
        for it in raw.get("items") or []:
            mid = it.get("member_id")
            if mid is None:
                continue
            try:
                v = int(mid)
            except (TypeError, ValueError):
                continue
            if v > 0:
                out.append(v)
        return out
    except Exception:
        return []


def _vk_user_is_chat_admin(peer_id, user_id):
    """Администратор/создатель беседы VK (мультичат)."""
    if not _is_multichat_peer(peer_id):
        return False
    try:
        uid = int(user_id)
        raw = vk.messages.getConversationMembers(peer_id=int(peer_id))
        for it in raw.get("items") or []:
            mid = it.get("member_id")
            if mid is None:
                continue
            try:
                if int(mid) != uid:
                    continue
            except (TypeError, ValueError):
                continue
            if it.get("is_admin") or it.get("is_owner"):
                return True
    except Exception:
        pass
    return False


def _can_run_chat_proverka(user_id, peer_id):
    if _is_owner(user_id) or _is_deputy_owner(user_id):
        return True
    return _vk_user_is_chat_admin(peer_id, user_id)


def _user_is_registered_in_clicker(user_id):
    """Завершённая регистрация в боте-кликере (users.is_registered = 1), не только строка в таблице."""
    try:
        cursor.execute(
            "SELECT COALESCE(is_registered, 0) FROM users WHERE user_id = ?",
            (int(user_id),),
        )
        row = cursor.fetchone()
        return bool(row) and int(row[0] or 0) == 1
    except Exception:
        return False


def _proverka_chat_members(peer_id):
    """Считает зарегистрированных в кликере участников беседы. «В кликере» = users.is_registered в БД бота."""
    ids = _multichat_member_user_ids(peer_id)
    n_players = 0
    n_bots = 0
    unregistered_ids = []
    for uid in ids:
        cursor.execute("SELECT COALESCE(is_registered, 0) FROM users WHERE user_id = ?", (int(uid),))
        row = cursor.fetchone()
        reg = int(row[0]) if row else 0
        if reg == 1:
            n_players += 1
        else:
            n_bots += 1
            unregistered_ids.append(int(uid))
    lines = [
        "🔍 Проверка участников беседы",
        "",
        f"👥 Пользователей в беседе: {len(ids)}",
        f"👤 В боте: {n_players}",
        f"🤖 Не в кликере: {n_bots}",
        "",
    ]
    text = "\n".join(lines)[:3900]
    kb = VkKeyboard(inline=True)
    kb.add_callback_button(
        "Кикнуть незарегистрированных",
        color=VkKeyboardColor.NEGATIVE,
        payload={"cmd": "kick_proverka_unregistered", "peer_id": int(peer_id)},
    )
    return text, kb


def _kick_unregistered_from_chat(peer_id, actor_id):
    """Исключает из беседы участников без регистрации в кликере (как при !проверка)."""
    if not _can_run_chat_proverka(actor_id, peer_id):
        return 0, "Недостаточно прав."
    if not _user_is_registered_in_clicker(actor_id):
        return 0, "Сначала зарегистрируйтесь в боте-кликере."
    ids = _multichat_member_user_ids(peer_id)
    kicked = 0
    for uid in ids:
        if int(uid) == int(actor_id):
            continue
        if int(uid) == int(ADMIN_ID):
            continue
        if _is_owner(uid) or _is_deputy_owner(uid):
            continue
        cursor.execute("SELECT COALESCE(is_registered, 0) FROM users WHERE user_id = ?", (int(uid),))
        row = cursor.fetchone()
        reg = int(row[0]) if row else 0
        if reg == 1:
            continue
        if _remove_user_from_chat_if_possible(peer_id, uid, force_kick=True):
            kicked += 1
    return kicked, None


def _proverka_register_pending_ui(peer_id, cmd_cmid, bot_send_message_id):
    """Запомнить сообщение с !проверка и ответ бота для удаления после завершения (кик)."""
    try:
        p = int(peer_id)
        c = int(cmd_cmid or 0)
        b_cmid = _vk_conversation_message_id(int(bot_send_message_id or 0)) if bot_send_message_id else 0
        if c <= 0 and b_cmid <= 0:
            return
        PROVERKA_PENDING_CMIDS[p] = {"cmd": c, "bot": b_cmid}
    except Exception:
        pass


def _proverka_delete_messages_after_kick(peer_id, event_obj):
    """Удалить команду !проверка, карточку с кнопкой и сообщение колбэка (если есть)."""
    try:
        p = int(peer_id)
    except (TypeError, ValueError):
        return
    dedup = []
    seen = set()
    pending = PROVERKA_PENDING_CMIDS.pop(p, None)
    if pending:
        for key in ("cmd", "bot"):
            v = int(pending.get(key) or 0)
            if v > 0 and v not in seen:
                seen.add(v)
                dedup.append(v)
    if isinstance(event_obj, dict):
        ev = int(event_obj.get("conversation_message_id") or 0)
        if ev > 0 and ev not in seen:
            seen.add(ev)
            dedup.append(ev)
    if not dedup:
        return
    try:
        vk.messages.delete(peer_id=p, cmids=",".join(str(x) for x in dedup), delete_for_all=1)
    except Exception as e:
        print(f"[_proverka_delete_messages_after_kick] {e}")


def _run_even1_event_compensation(owner_user_id, reply_peer):
    """
    Доначислить деньги за персональный ивент (дни 3–6), если условия выполнены по БД,
    а денежная награда ещё не отмечена (event_day3..6_claimed = 0). Идемпотентно: повторный
    вызов ничего не начислит тем, кому уже проставлены флаги.
    """
    start_ts = float(_personal_event_start_ts_utc())
    end_ts = float(_personal_event_end_ts_utc())
    cursor.execute("SELECT user_id FROM users WHERE is_registered = 1")
    all_uids = [int(r[0]) for r in cursor.fetchall()]

    total_paid_all = 0
    users_helped = 0
    sample_lines = []

    for uid in all_uids:
        try:
            cursor.execute(
                "SELECT COALESCE(event_success_rob_count, 0), COALESCE(event_notified_mask, 0), "
                "COALESCE(event_day1_claimed, 0), COALESCE(event_day2_claimed, 0), "
                "COALESCE(event_day3_claimed, 0), COALESCE(event_day4_claimed, 0), "
                "COALESCE(event_day5_claimed, 0), COALESCE(event_day6_claimed, 0) "
                "FROM users WHERE user_id = ?",
                (int(uid),),
            )
            row = cursor.fetchone()
            if not row:
                continue
            rob_cnt = int(row[0] or 0)
            notified_mask = int(row[1] or 0)
            claimed = [int(row[i] or 0) for i in range(2, 8)]
            cursor.execute(
                "SELECT COUNT(*) FROM users "
                "WHERE referrer_id = ? AND is_registered = 1 "
                "AND COALESCE(registered_at, 0) >= ? AND COALESCE(registered_at, 0) <= ?",
                (int(uid), start_ts, end_ts),
            )
            invite_cnt = int((cursor.fetchone() or [0])[0] or 0)

            add_money = 0
            updates = []
            if rob_cnt >= 1 and not claimed[2]:
                claimed[2] = 1
                updates.append("event_day3_claimed = 1")
                notified_mask |= 1 << (3 - 1)
                add_money += PERSONAL_EVENT_REWARD_DAY3
            if invite_cnt >= 2 and not claimed[3]:
                claimed[3] = 1
                updates.append("event_day4_claimed = 1")
                notified_mask |= 1 << (4 - 1)
                add_money += PERSONAL_EVENT_REWARD_DAY4
            if invite_cnt >= 3 and not claimed[4]:
                claimed[4] = 1
                updates.append("event_day5_claimed = 1")
                notified_mask |= 1 << (5 - 1)
                add_money += PERSONAL_EVENT_REWARD_DAY5
            if rob_cnt >= 2 and not claimed[5]:
                claimed[5] = 1
                updates.append("event_day6_claimed = 1")
                notified_mask |= 1 << (6 - 1)
                add_money += PERSONAL_EVENT_REWARD_DAY6

            if add_money <= 0 or not updates:
                continue

            set_parts = ["event_notified_mask = ?"]
            params = [int(notified_mask)]
            set_parts.extend(updates)
            set_parts.append("balance = COALESCE(balance, 0) + ?")
            params.append(int(add_money))
            params.append(int(uid))
            cursor.execute(
                "UPDATE users SET " + ", ".join(set_parts) + " WHERE user_id = ?",
                tuple(params),
            )
            db.commit()
            total_paid_all += add_money
            users_helped += 1
            if len(sample_lines) < 15:
                sample_lines.append(f"@id{uid} ({get_user_name(uid)}): +{format_click(add_money)}$")
        except Exception:
            continue

    msg = (
        "✅ /even1 — доначисление денежных наград ивента (дни 3–6)\n\n"
        "Учтены только игроки, у которых по базе выполнены условия этапа, "
        "но не стояли отметки о получении денег (из‑за сбоя начисления).\n\n"
        f"Игроков с доначислением: {users_helped}\n"
        f"Всего начислено: {format_click(total_paid_all)}$"
    )
    if users_helped == 0:
        msg += "\n\nНикому не требовалось доначисление (все флаги уже стоят или условия не выполнены)."
    elif sample_lines:
        msg += "\n\nПримеры (до 15):\n" + "\n".join(sample_lines)
    send_msg(reply_peer, msg[:3900], kb_for_peer(reply_peer))
    send_admin_chat_log(
        f"[EVEN1] Доначисление 3–6 дн. ивента: {format_click(total_paid_all)}$, игроков: {users_helped}. "
        f"Инициатор: {get_user_mention_with_name(owner_user_id)}"
    )


def _run_owner_mass_collect_to_kazna(owner_user_id, reply_peer, amount_per_user):
    """Списать с каждого зарегистрированного до amount_per_user (не больше баланса), суммировать в казну."""
    amt = int(amount_per_user)
    if amt <= 0:
        send_msg(reply_peer, "Сумма должна быть больше нуля.", kb_for_peer(reply_peer))
        return
    cursor.execute("SELECT user_id, COALESCE(balance, 0) FROM users WHERE is_registered = 1")
    rows = cursor.fetchall()
    total_to_kazna = 0
    players_touched = 0
    players_skipped_zero = 0
    for uid, bal in rows:
        try:
            b = int(bal or 0)
            take = min(amt, b)
            if take <= 0:
                players_skipped_zero += 1
                continue
            new_b = b - take
            cursor.execute("UPDATE users SET balance = ? WHERE user_id = ?", (int(new_b), int(uid)))
            total_to_kazna += take
            players_touched += 1
        except Exception:
            continue
    db.commit()
    if total_to_kazna > 0:
        _add_kazna(int(total_to_kazna))
    kazna_after = _get_kazna_balance()
    send_msg(
        reply_peer,
        "✅ Сбор завершён\n\n"
        f"Запрос с игрока: до {format_click(amt)}$\n"
        f"Списано у игроков (с ненулевым балансом): {players_touched}\n"
        f"Без списания (баланс 0): {players_skipped_zero}\n"
        f"Всего собрано в казну: {format_click(total_to_kazna)}$\n"
        f"Казна сообщества сейчас: {format_click(kazna_after)}$",
        kb_for_peer(reply_peer),
    )
    send_admin_chat_log(
        f"[СБОР] !сбор {format_click(amt)}$ с игрока → казна +{format_click(total_to_kazna)}$ "
        f"({players_touched} чел.). Инициатор: {get_user_mention_with_name(owner_user_id)}"
    )


def _pet_name_by_level(level):
    names = {
        1: "Щенок",
        2: "Пёсик",
        3: "Гончая",
        4: "Волк",
        5: "Титан-пёс",
        6: "Лис",
        7: "Рысь",
        8: "Пума",
        9: "Пантера",
        10: "Лев",
        11: "Тигр",
        12: "Ягуар",
        13: "Медведь",
        14: "Гризли",
        15: "Полярный медведь",
        16: "Буйвол",
        17: "Носорог",
        18: "Гиппопотам",
        19: "Крокодил",
        20: "Анаконда",
        21: "Орёл",
        22: "Сокол",
        23: "Снежный барс",
        24: "Кабан",
        25: "Мамонт",
    }
    return names.get(int(level), f"Питомец #{int(level)}")


def get_local_pet_info(user_id):
    cursor.execute("SELECT COALESCE(pet_id, 0), COALESCE(pet_name, '') FROM users WHERE user_id = ?", (int(user_id),))
    row = cursor.fetchone()
    lvl = int((row[0] if row else 0) or 0)
    name = (row[1] if row else '') or ''
    if lvl <= 0:
        lvl = 1
    if not name:
        name = _pet_name_by_level(lvl)
    if not row or int(row[0] or 0) <= 0 or not (row[1] or '').strip():
        cursor.execute("UPDATE users SET pet_id = ?, pet_name = ? WHERE user_id = ?", (lvl, name, int(user_id)))
        db.commit()
    return lvl, name, lvl


def pet_upgrade_cost(level):
    lvl = max(1, int(level))
    return PET_UPGRADE_BASE_COST * lvl


def is_pet_max_level(level):
    return int(level) >= int(MAX_PET_LEVEL)


def sticker_attachment(sticker_id):
    return f"sticker{int(sticker_id)}"


def send_msg(peer_id, text, keyboard=None, attachment=None, disable_mentions=False):
    post = {'peer_id': int(peer_id), 'message': text, 'random_id': get_random_id()}
    if keyboard is not None:
        post['keyboard'] = keyboard if isinstance(keyboard, str) else keyboard.get_keyboard()
    if attachment:
        post['attachment'] = attachment
    if disable_mentions:
        post['disable_mentions'] = 1
    try:
        return int(vk.messages.send(**post) or 0)
    except Exception:
        return 0


def _admin_op_ui_stack_delete_all(user_id, peer_id):
    """Удалить из чата ранее отправленные сообщения админ-панели /op и конструктора конкурса."""
    try:
        cursor.execute(
            "SELECT conversation_message_id FROM admin_op_ui_messages WHERE user_id = ? AND peer_id = ?",
            (int(user_id), int(peer_id)),
        )
        for (cmid,) in cursor.fetchall():
            try:
                vk.messages.delete(peer_id=int(peer_id), cmids=str(int(cmid)), delete_for_all=1)
            except Exception:
                pass
        cursor.execute(
            "DELETE FROM admin_op_ui_messages WHERE user_id = ? AND peer_id = ?",
            (int(user_id), int(peer_id)),
        )
        db.commit()
    except sqlite3.OperationalError:
        pass


def _admin_op_ui_stack_record(user_id, peer_id, message_id_from_send):
    if not message_id_from_send:
        return
    cmid = _vk_conversation_message_id(int(message_id_from_send))
    if not cmid:
        return
    try:
        cursor.execute(
            "INSERT OR IGNORE INTO admin_op_ui_messages (user_id, peer_id, conversation_message_id, created_at) "
            "VALUES (?, ?, ?, ?)",
            (int(user_id), int(peer_id), int(cmid), time.time()),
        )
        db.commit()
    except Exception:
        pass


def _admin_op_ui_stack_ensure_cmid(user_id, peer_id, conversation_message_id):
    """Запомнить cmid панели без message_id (после messages.edit)."""
    if not conversation_message_id:
        return
    try:
        cursor.execute(
            "INSERT OR IGNORE INTO admin_op_ui_messages (user_id, peer_id, conversation_message_id, created_at) "
            "VALUES (?, ?, ?, ?)",
            (int(user_id), int(peer_id), int(conversation_message_id), time.time()),
        )
        db.commit()
    except Exception:
        pass


def send_msg_admin_op_panel(user_id, peer_id, text, keyboard=None, attachment=None, disable_mentions=False, edit_cmid=0):
    """Панель /op или мастера конкурса. При inline-callback — правка того же сообщения (клавиатура не пропадает)."""
    ec = int(edit_cmid or 0)
    if ec > 0 and keyboard is not None:
        try:
            kbd = keyboard if isinstance(keyboard, str) else keyboard.get_keyboard()
            ed = {'peer_id': int(peer_id), 'conversation_message_id': ec, 'message': text, 'keyboard': kbd}
            if attachment:
                ed['attachment'] = attachment
            if disable_mentions:
                ed['disable_mentions'] = 1
            vk.messages.edit(**ed)
            _admin_op_ui_stack_ensure_cmid(user_id, peer_id, ec)
            return ec
        except Exception:
            pass
    _admin_op_ui_stack_delete_all(user_id, peer_id)
    mid = send_msg(peer_id, text, keyboard, attachment, disable_mentions)
    _admin_op_ui_stack_record(user_id, peer_id, mid)
    return mid


def _vk_conversation_message_id(message_id):
    """conversation_message_id для messages.edit / delete в беседах и ЛС."""
    try:
        if not message_id:
            return None
        data = vk.messages.getById(message_ids=int(message_id))
        items = data.get('items') if isinstance(data, dict) else data
        if not items:
            return None
        item0 = items[0]
        if not isinstance(item0, dict):
            return None
        cmid = item0.get('conversation_message_id')
        if cmid is None:
            return None
        return int(cmid)
    except Exception:
        return None


def _withdraw_store_dm_notify(withdraw_id, peer_id, message_id):
    cmid = _vk_conversation_message_id(message_id)
    if not cmid:
        return
    try:
        cursor.execute(
            "UPDATE withdrawals SET admin_dm_peer = ?, admin_dm_cmid = ? WHERE id = ?",
            (int(peer_id), int(cmid), int(withdraw_id)),
        )
        db.commit()
    except Exception:
        pass


def _withdraw_store_chat_blast(withdraw_id, peer_id, message_id):
    cmid = _vk_conversation_message_id(message_id)
    if not cmid:
        return
    try:
        cursor.execute(
            "UPDATE withdrawals SET admin_chat_peer = ?, admin_chat_cmid = ? WHERE id = ?",
            (int(peer_id), int(cmid), int(withdraw_id)),
        )
        db.commit()
    except Exception:
        pass


def _withdraw_store_dm_cmd(withdraw_id, peer_id, message_id):
    """Строка «перевод {amount} @id…» для скрипта — храним cmid, удаляем после «Я перевёл»."""
    cmid = _vk_conversation_message_id(message_id)
    if not cmid:
        return
    try:
        cursor.execute(
            "UPDATE withdrawals SET admin_cmd_peer = ?, admin_cmd_cmid = ? WHERE id = ?",
            (int(peer_id), int(cmid), int(withdraw_id)),
        )
        db.commit()
    except Exception:
        pass


def _withdraw_delete_dm_cmd_line(withdraw_id):
    try:
        cursor.execute(
            "SELECT admin_cmd_peer, admin_cmd_cmid FROM withdrawals WHERE id = ?",
            (int(withdraw_id),),
        )
        row = cursor.fetchone()
        if not row or row[1] is None:
            return
        peer, cmid = int(row[0] or 0), int(row[1] or 0)
        if peer <= 0 or cmid <= 0:
            return
        vk.messages.delete(peer_id=peer, cmids=str(cmid), delete_for_all=1)
    except Exception:
        pass


def _withdraw_clear_notify_columns(withdraw_id):
    try:
        cursor.execute(
            "UPDATE withdrawals SET admin_dm_peer = NULL, admin_dm_cmid = NULL, admin_chat_peer = NULL, admin_chat_cmid = NULL, admin_cmd_peer = NULL, admin_cmd_cmid = NULL WHERE id = ?",
            (int(withdraw_id),),
        )
        db.commit()
    except Exception:
        pass


def _withdraw_delete_chat_blast_row(withdraw_id):
    try:
        cursor.execute(
            "SELECT admin_chat_peer, admin_chat_cmid FROM withdrawals WHERE id = ?",
            (int(withdraw_id),),
        )
        row = cursor.fetchone()
        if not row or row[1] is None:
            return
        peer, cmid = int(row[0] or 0), int(row[1] or 0)
        if peer <= 0 or cmid <= 0:
            return
        vk.messages.delete(peer_id=peer, cmids=str(cmid), delete_for_all=1)
    except Exception:
        pass


def _withdraw_edit_dm_status(withdraw_id, text_line):
    """Редактирует ЛС-сообщение с кнопками (!выводы) в итоговый текст, убирает клавиатуру."""
    try:
        cursor.execute(
            "SELECT admin_dm_peer, admin_dm_cmid FROM withdrawals WHERE id = ?",
            (int(withdraw_id),),
        )
        row = cursor.fetchone()
        if not row or row[0] is None or row[1] is None:
            return False
        peer, cmid = int(row[0]), int(row[1])
        vk.messages.edit(
            peer_id=peer,
            conversation_message_id=cmid,
            message=text_line,
            keyboard='{"inline":true,"buttons":[]}',
        )
        return True
    except Exception as e:
        print(f"[withdraw_edit_dm] {e}")
        return False


def send_admin_chat_log(text):
    try:
        send_msg(ADMIN_CHAT_PEER_ID, str(text), None)
    except Exception:
        pass


def send_msg_with_template(peer_id, text, template_obj, keyboard=None, attachment=None):
    """Отправка сообщения с template (например, carousel)."""
    post = {'peer_id': int(peer_id), 'message': text, 'random_id': get_random_id()}
    if keyboard is not None:
        post['keyboard'] = keyboard if isinstance(keyboard, str) else keyboard.get_keyboard()
    if attachment:
        post['attachment'] = attachment
    if template_obj is not None:
        post['template'] = json.dumps(template_obj, ensure_ascii=False)
    try:
        vk.messages.send(**post)
        return True
    except Exception:
        return False


def send_msg_and_delete_later(peer_id, text, keyboard=None, attachment=None, delete_after_sec=None):
    """Отправить сообщение и удалить его у всех через delete_after_sec (краткий статус модерации)."""
    if delete_after_sec is None:
        delete_after_sec = MSG_DELETED_NOTICE_DELETE_SEC
    post = {'peer_id': int(peer_id), 'message': text, 'random_id': get_random_id()}
    if keyboard is not None:
        post['keyboard'] = keyboard if isinstance(keyboard, str) else keyboard.get_keyboard()
    if attachment:
        post['attachment'] = attachment
    try:
        mid = vk.messages.send(**post)
        if not mid:
            return

        def _do_del():
            try:
                res = vk.messages.getById(message_ids=int(mid))
                items = res.get('items') if isinstance(res, dict) else res
                if not items:
                    return
                item0 = items[0]
                if isinstance(item0, dict):
                    cmid = item0.get('conversation_message_id')
                else:
                    cmid = None
                if cmid:
                    vk.messages.delete(peer_id=int(peer_id), cmids=str(int(cmid)), delete_for_all=1)
            except Exception:
                pass

        t = threading.Timer(float(delete_after_sec), _do_del)
        t.daemon = True
        t.start()
    except Exception:
        pass


def _klad_openlink_keyboard_str():
    """open_link без payload — в vk_api у open_link уходит payload: null, из‑за этого messages.send может падать."""
    if not KLAD_ENABLED or not KLAD_APP_URL:
        return None
    return json.dumps(
        {
            "inline": True,
            "buttons": [
                [{"action": {"type": "open_link", "link": KLAD_APP_URL, "label": "пригласить в беседу"}}]
            ]
        },
        ensure_ascii=False,
    )


def _register_from_chat_keyboard_str():
    """Инлайн «Зарегистрироваться» → диалог с ботом (без payload: null)."""
    return json.dumps(
        {
            "inline": True,
            "buttons": [
                [{"action": {"type": "open_link", "link": REGISTER_CHAT_WRITE_URL, "label": "Зарегистрироваться"}}]
            ]
        },
        ensure_ascii=False,
    )


def _is_multichat_peer(peer_id):
    """Мультичат VK: peer_id = 2_000_000_000 + local_chat_id."""
    try:
        return int(peer_id) >= 2000000000
    except (TypeError, ValueError):
        return False


def _is_private_bot_dialog(peer_id, user_id):
    """Личные сообщения с сообществом (не беседа): peer_id совпадает с пользователем."""
    try:
        if _is_multichat_peer(peer_id):
            return False
        return int(peer_id) == int(user_id) and int(user_id) > 0
    except (TypeError, ValueError):
        return False


def _remove_user_from_chat_if_possible(peer_id, user_id, force_kick=False):
    """Исключить пользователя из беседы VK, если это мультичат.
    force_kick=True — команда «кик» владельца/зама: стажёров тоже можно исключить."""
    try:
        pid = int(peer_id)
        uid = int(user_id)
    except (TypeError, ValueError):
        return False
    if pid < 2000000000 or uid <= 0:
        return False
    if not force_kick:
        # Модераторов не исключаем из беседы даже при бане.
        if _get_project_role_key(uid) == "moderator":
            return False
    try:
        vk.messages.removeChatUser(chat_id=pid - 2000000000, user_id=uid)
        return True
    except Exception:
        return False


def _add_user_to_chat_if_possible(peer_id, user_id):
    """Попытаться вернуть пользователя в беседу VK (если у токена есть права)."""
    try:
        pid = int(peer_id)
        uid = int(user_id)
    except (TypeError, ValueError):
        return False
    if pid < 2000000000 or uid <= 0:
        return False
    chat_id = pid - 2000000000
    last_err = None
    for sess in _vk_api_sessions_for_chat_moderation():
        try:
            sess.method("messages.addChatUser", {"chat_id": int(chat_id), "user_id": int(uid), "v": "5.199"})
            return True
        except Exception as e:
            last_err = e
    try:
        print(f"[add_chat_user] peer={pid} user={uid}: {last_err!r}")
    except Exception:
        pass
    return False


def _vk_api_sessions_for_chat_moderation():
    """Сначала user token (часто админ беседы), затем токен группы."""
    out = []
    if vk_user is not None and vk_user_session is not None:
        out.append(vk_user_session)
    out.append(vk_session)
    return out


def _owner_invite_group_subscribers_to_chat(peer_id, max_users=2000):
    """Массово добавить в беседу подписчиков группы (только для владельца)."""
    try:
        pid = int(peer_id)
    except (TypeError, ValueError):
        return {"ok": False, "reason": "bad_peer"}
    if not _is_multichat_peer(pid):
        return {"ok": False, "reason": "not_chat"}
    if vk_user is None:
        return {"ok": False, "reason": "no_user_token"}

    chat_members = set(_multichat_member_user_ids(pid))
    added = 0
    already = 0
    failed = 0
    checked = 0
    offset = 0
    step = 1000
    limit_total = int(max(1, min(int(max_users or 2000), 100000)))

    while checked < limit_total:
        chunk_size = min(step, limit_total - checked)
        try:
            resp = vk_user.groups.getMembers(group_id=GROUP_ID, offset=offset, count=chunk_size)
        except Exception as e:
            return {
                "ok": False,
                "reason": "vk_error",
                "error": str(e),
                "added": added,
                "already": already,
                "failed": failed,
                "checked": checked,
            }
        ids = resp.get("items") or []
        if not ids:
            break
        for uid in ids:
            try:
                target_uid = int(uid)
            except (TypeError, ValueError):
                continue
            checked += 1
            if target_uid in chat_members:
                already += 1
                continue
            if _add_user_to_chat_if_possible(pid, target_uid):
                added += 1
                chat_members.add(target_uid)
            else:
                failed += 1
            time.sleep(0.12)
            if checked >= limit_total:
                break
        offset += len(ids)
        if len(ids) < chunk_size:
            break

    return {
        "ok": True,
        "added": added,
        "already": already,
        "failed": failed,
        "checked": checked,
        "limited": checked >= limit_total,
        "max_users": limit_total,
    }


def _vk_chat_moderation_restrict_write(peer_id, member_id, duration_sec, restrict=True):
    """
    Запрет/снятие права писать в мультичате через модерацию VK (не только логика бота).
    Требуются права администратора беседы у токена.
    """
    try:
        p = int(peer_id)
        m = int(member_id)
    except (TypeError, ValueError):
        return False
    if not _is_multichat_peer(p) or m <= 0:
        return False
    dur = int(max(60, min(int(duration_sec or 0), 365 * 86400)))
    last_err = None
    for sess in _vk_api_sessions_for_chat_moderation():
        # Вариант 1: action ro/rw + for (актуальные версии API)
        try:
            if restrict:
                sess.method(
                    "messages.changeConversationMemberRestrictions",
                    {"peer_id": p, "member_ids": m, "action": "ro", "for": dur, "v": "5.199"},
                )
            else:
                sess.method(
                    "messages.changeConversationMemberRestrictions",
                    {"peer_id": p, "member_ids": m, "action": "rw", "v": "5.199"},
                )
            return True
        except Exception as e1:
            last_err = e1
        # Вариант 2: restrictions JSON
        try:
            rj = json.dumps({"send_messages": True}) if restrict else json.dumps({"send_messages": False})
            sess.method(
                "messages.changeConversationMemberRestrictions",
                {"peer_id": p, "member_ids": m, "restrictions": rj, "v": "5.199"},
            )
            return True
        except Exception as e2:
            last_err = e2
        # Вариант 3: member_id (единственное число)
        try:
            if restrict:
                sess.method(
                    "messages.changeConversationMemberRestrictions",
                    {"peer_id": p, "member_id": m, "action": "ro", "for": dur, "v": "5.199"},
                )
            else:
                sess.method(
                    "messages.changeConversationMemberRestrictions",
                    {"peer_id": p, "member_id": m, "action": "rw", "v": "5.199"},
                )
            return True
        except Exception as e3:
            last_err = e3
    try:
        print(f"[vk_chat_moderation_restrict_write] peer={p} member={m} restrict={restrict}: {last_err!r}")
    except Exception:
        pass
    return False


def send_klad_reward_message(peer_id, reward_amount, balance_after):
    """Сообщение о кладе: фото plaz.png, инлайн-кнопка со ссылкой (без смешения с text-кнопками)."""
    if not KLAD_ENABLED:
        return False
    text = (
        f"🏴‍☠️ Вы нашли клад! +{format_click(reward_amount)}$\n"
        f"Баланс: {format_click(balance_after)}$"
    )
    kbd = _klad_openlink_keyboard_str()
    attachment = None
    if os.path.isfile(KLAD_IMAGE_PATH):
        try:
            photo_info = vk_upload.photo_messages(photos=KLAD_IMAGE_PATH)[0]
            attachment = f"photo{photo_info['owner_id']}_{photo_info['id']}"
        except Exception:
            pass
    rid = int(peer_id)
    text_fallback = text + f"\n\nпригласить в беседу\n{KLAD_APP_URL}"
    last_e = None
    for use_att, use_kb in ((True, True), (False, True), (False, False)):
        try:
            post = {"peer_id": rid, "message": text, "random_id": get_random_id()}
            if use_kb:
                post["keyboard"] = kbd
            if use_att and attachment:
                post["attachment"] = attachment
            if not use_kb:
                post["message"] = text_fallback
            vk.messages.send(**post)
            return
        except Exception as e:
            last_e = e
            continue
    if last_e is not None:
        print(f"[klad] messages.send failed after retries: {last_e!r}")


def _lp_int(val):
    """Long Poll часто отдаёт числа строками — без int() сравнение с -GROUP_ID ломается."""
    if val is None:
        return None
    try:
        return int(val)
    except (TypeError, ValueError):
        return None


def wall_reply_to_comment(post_id, reply_to_comment_id, text):
    if not text or post_id is None or reply_to_comment_id is None:
        return
    msg = text.strip()[:4096]
    if not msg:
        return
    try:
        vk.wall.createComment(
            owner_id=-int(GROUP_ID),
            post_id=int(post_id),
            message=msg,
            reply_to_comment=int(reply_to_comment_id),
            from_group=1,
        )
    except Exception as e:
        err_s = str(e or "")
        # У некоторых сообществ/токенов нет права отвечать в комментарии от имени группы.
        # В этом кейсе просто пропускаем авто-ответ в стене, чтобы не заспамливать лог.
        if ("[15]" in err_s) or ("Access denied" in err_s and "community" in err_s.lower()):
            return
        print(f"[wall_comment] wall.createComment post={post_id} reply_to={reply_to_comment_id}: {e}")


def notify_wall_comment_dm_and_reply(user_id, post_id, comment_id, text, keyboard=None):
    if TECH_WORKS_ENABLED:
        # В режиме техработ начисления сохраняем, но текстовые ответы отключены.
        return
    kb = keyboard or get_main_kb()
    dm_allowed = True
    try:
        perm = vk.messages.isMessagesFromGroupAllowed(group_id=int(GROUP_ID), user_id=int(user_id))
        dm_allowed = bool((perm or {}).get("is_allowed"))
    except Exception as e:
        # Если проверка прав недоступна, сохраняем старое поведение и пробуем отправить ЛС.
        print(f"[wall_comment] isMessagesFromGroupAllowed user_id={user_id}: {e}")
    if dm_allowed:
        try:
            vk.messages.send(
                peer_id=int(user_id),
                message=text,
                random_id=get_random_id(),
                keyboard=kb.get_keyboard(),
            )
        except Exception as e:
            print(f"[wall_comment] ЛС user_id={user_id}: {e}")
    else:
        print(f"[wall_comment] ЛС пропущено (нет разрешения) user_id={user_id}")
    wall_reply_to_comment(post_id, comment_id, text)

def get_user_name(user_id):
    try:
        now = time.time()
        uid = int(user_id)
        c = USER_NAME_CACHE.get(uid)
        if c and (now - c[1]) <= USER_NAME_CACHE_TTL_SEC:
            return c[0]
        u = vk.users.get(user_ids=uid)[0]
        nm = f"{u.get('first_name', 'Пользователь')} {u.get('last_name', '')}".strip()
        USER_NAME_CACHE[uid] = (nm, now)
        return nm
    except:
        return "Пользователь"


def get_user_names_bulk(user_ids):
    ids = []
    seen = set()
    for uid in user_ids or []:
        try:
            x = int(uid)
        except Exception:
            continue
        if x > 0 and x not in seen:
            seen.add(x)
            ids.append(x)
    if not ids:
        return {}
    try:
        rows = vk.users.get(user_ids=",".join(str(x) for x in ids[:1000]))
        out = {}
        now = time.time()
        for r in rows:
            uid = int(r.get("id") or 0)
            if uid > 0:
                nm = f"{r.get('first_name', 'Пользователь')} {r.get('last_name', '')}".strip()
                out[uid] = nm
                USER_NAME_CACHE[uid] = (nm, now)
        for uid in ids:
            out.setdefault(uid, f"id{uid}")
        return out
    except Exception:
        return {uid: f"id{uid}" for uid in ids}

def check_parent_registration(user_id):
    # Интеграция с внешним профилем отключена.
    return True

def _gemini_extract_text(data):
    """Текст ответа из JSON ответа generateContent."""
    if not isinstance(data, dict):
        return None
    err = data.get("error")
    if isinstance(err, dict) and err.get("message"):
        print(f"[gemini] {err.get('message')}")
    cands = data.get("candidates")
    if not isinstance(cands, list) or not cands:
        return None
    parts = (cands[0].get("content") or {}).get("parts") or []
    texts = [p.get("text", "") for p in parts if isinstance(p, dict) and p.get("text")]
    if not texts:
        return None
    return "\n".join(texts).strip()


def _gemini_generate(system_prompt, user_prompt, *, max_output_tokens=900, temperature=0.2, timeout=90):
    """Один запрос к Google Gemini (REST generateContent)."""
    global GEMINI_LAST_ERROR
    GEMINI_LAST_ERROR = ""
    if not GEMINI_API_KEY:
        GEMINI_LAST_ERROR = "missing_api_key"
        return None
    raw_model = (GEMINI_MODEL or "").removeprefix("models/").strip()
    model = raw_model.lower()
    # Миграция со slug-формата GenAPI (gemini-2-5-...) на формат Google (gemini-2.5-...).
    if re.fullmatch(r"gemini-\d+-\d+-.+", model):
        model = re.sub(r"^gemini-(\d+)-(\d+)-", r"gemini-\1.\2-", model)
    if model in {"gemini-2.5-flash-lite", "gemini-2-5-flash-lite"}:
        model = "gemini-2.5-flash"
    if not model:
        model = "gemini-2.0-flash"
    model_candidates = []
    for m in (model, "gemini-2.5-flash", "gemini-2.0-flash"):
        if m not in model_candidates:
            model_candidates.append(m)
    body = {
        "systemInstruction": {"parts": [{"text": str(system_prompt)}]},
        "contents": [{"role": "user", "parts": [{"text": str(user_prompt)}]}],
        "generationConfig": {
            "temperature": float(temperature),
            "maxOutputTokens": int(max_output_tokens),
        },
    }
    for m in model_candidates:
        url = (
            "https://generativelanguage.googleapis.com/v1beta/models/"
            f"{m}:generateContent?key={GEMINI_API_KEY}"
        )
        for attempt in range(2):
            try:
                r = requests.post(url, json=body, headers={"Content-Type": "application/json"}, timeout=timeout)
                if r.status_code == 200:
                    GEMINI_LAST_ERROR = ""
                    return _gemini_extract_text(r.json())
                details = (r.text or "")[:1200]
                low = details.lower()
                if r.status_code in (429, 503):
                    if "limit: 0" in low or "quota exceeded" in low:
                        GEMINI_LAST_ERROR = "quota_exceeded"
                    elif "high demand" in low or "unavailable" in low:
                        GEMINI_LAST_ERROR = "high_demand"
                    else:
                        GEMINI_LAST_ERROR = f"http_{r.status_code}"
                else:
                    GEMINI_LAST_ERROR = f"http_{r.status_code}"
                print(f"[gemini] HTTP {r.status_code} ({m}): {details[:600]}")
                # Перегрузка/лимит: короткий ретрай и затем fallback на следующую модель.
                if r.status_code in (429, 503):
                    # Явный лимит free tier (limit: 0) обычно не лечится повтором.
                    if "limit: 0" in low:
                        break
                    if attempt == 0:
                        time.sleep(1.3)
                        continue
                    break
                # Невалидная/недоступная модель: сразу fallback на следующую.
                if r.status_code in (400, 404):
                    break
                return None
            except Exception as e:
                GEMINI_LAST_ERROR = "request_exception"
                print(f"[gemini] {e}")
                return None
    return None


def genapi_comment_moderate(comment_text):
    """
    Gemini: оценка креативности/осмысленности комментария.
    Возвращает: (True, None) — ок; (False, hint) — отклонено; (None, None) — ошибка API.
    """
    if not GEMINI_API_KEY:
        return None, None
    system = (
        "Ты оцениваешь комментарий к посту ВКонтакте только по креативности и осмысленности. "
        "Спам, мусор из символов, пустые повторы и бессмыслицу отклоняй. "
        "Ответь ТОЛЬКО JSON без markdown и пояснений: "
        "{\"ok\": true} или {\"ok\": false, \"hint\": \"...\"}. "
        "Если ok=false, hint — короткая причина (до 120 символов)."
    )
    content = _gemini_generate(system, (comment_text or "")[:2000], max_output_tokens=256, temperature=0.2, timeout=60)
    if not content:
        return None, None
    raw = content.strip()
    if raw.startswith("```"):
        raw = re.sub(r"^```\w*\s*", "", raw)
        raw = re.sub(r"\s*```$", "", raw)
    start, end = raw.find("{"), raw.rfind("}")
    if start < 0 or end <= start:
        return None, None
    try:
        jo = json.loads(raw[start : end + 1])
    except Exception:
        return None, None
    if jo.get("ok") is True:
        return True, None
    hint = (jo.get("hint") or "").strip()
    if len(hint) > 200:
        hint = hint[:197] + "..."
    return False, hint or "Комментарий не прошёл проверку."


def _local_faq_answer(text):
    """Локальный FAQ-ответ, когда Gemini временно недоступен."""
    t = (text or "").lower()
    if not t:
        return None
    if ("как" in t and "зарабат" in t) or ("валют" in t and "как" in t):
        return (
            "Можно просто кликать, можно участвовать в ивентах в данной беседе, "
            "а можно лайкать и комментировать посты + промики в чате и в сообществе."
        )
    if ("почему" in t and "вывод" in t) or ("не могу вывести" in t) or ("вывести деньги" in t):
        return "Вывод средств осуществляется только с 5 мм (5000 мк)."
    if ("где" in t and "питом" in t and "куп" in t) or ("купить питомца" in t):
        return (
            "По умолчанию вам выдается питомец щенок, "
            "вы можете прокачивать его за игровую валюту."
        )
    if ("энерг" in t and ("законч" in t or "нет" in t)) or ("как восстановить энергию" in t):
        return (
            "Чтобы ее восполнить, нужно покормить питомца, "
            "и тогда со временем, согласно показателям в профиле (питомец), "
            "энергия будет восстанавливаться."
        )
    if "мут" in t or "варн" in t or "бан" in t:
        return "За что мут/варн/бан: https://vk.ru/topic-237333137_57395396"
    return None


def genapi_admin_answer(question_text, requester_id=None, requester_name=None, unrestricted=False):
    """Ответ нейросети (Google Gemini) для админ-команды /гпт."""
    if not GEMINI_API_KEY:
        return None
    q = (question_text or "").strip()
    if not q:
        return None
    try:
        rid = int(requester_id) if requester_id is not None else 0
    except Exception:
        rid = 0
    rname = (requester_name or "").strip()
    if not rname and rid > 0:
        rname = get_user_name(rid)
    if not rname:
        rname = "Неизвестный пользователь"

    base_system = (
        "Ты главный AI-помощник администратора ВК-бота экономической игры «Нищий кликер». "
        "Технологический контекст проекта: Python, vk_api, SQLite; это бот ВКонтакте, не Telegram. "
        "Игровой контекст: "
        "1) ядро прогресса — клики за энергию питомца; "
        "2) питомец связан с сытостью, восстановлением энергии, кормлением и улучшениями; "
        "3) экономика включает баланс, переводы между игроками, пожертвования; "
        "4) есть PvP/рисковые механики (ограбления, натравить питомца), события с прогрессом и наградами; "
        "5) есть реферальная система, промокоды, магазин апгрейдов; "
        "6) есть заявки на вывод и админ-обработка; "
        "7) есть роли (владелец, заместитель, модерация), а также мут/варн/бан и антиспам/антибот. "
        f"Текущий пользователь диалога: {rname} (id: {rid if rid > 0 else 'unknown'}). "
        "Твоя цель: давать максимально практичные ответы для управления и развития этого конкретного бота. "
        "Приоритет полезности: точность -> применимость -> краткость. "
        "Правила ответа: "
        "а) отвечай только на русском; "
        "б) сначала дай прямой ответ в 1-3 предложениях; "
        "в) затем при необходимости дай пошаговый план внедрения; "
        "г) если есть выбор, предложи один лучший вариант и коротко обоснуй; "
        "д) не выдумывай команды, таблицы БД, функции и факты; если данных не хватает — явно скажи, чего именно не хватает; "
        "е) не уходи в общую теорию, опирайся на реалии этого бота и ВК; "
        "ж) если вопрос двусмысленный, задай один уточняющий вопрос и одновременно предложи наиболее вероятный рабочий вариант. "
        "Официальный FAQ сообщества (если вопрос игрока совпадает или близок — опирайся на эти формулировки, не переписывай смысл): "
        "1) Как зарабатывать валюту? — можно просто кликать; можно участвовать в ивентах в данной беседе; "
        "можно лайкать и комментировать посты; плюс промики в чате и в сообществе. "
        "2) Почему я не могу вывести деньги? — вывод средств осуществляется только с 5 мм (5000 мк). "
        "3) Где купить питомца? — по умолчанию вам выдаётся питомец щенок; вы можете прокачивать его за игровую валюту. "
        "4) Что делать, если закончилась энергия? — чтобы её восполнить, нужно покормить питомца; "
        "тогда со временем, согласно показателям в профиле (питомец), энергия будет восстанавливаться. "
        "5) За что мут/варн/бан? — правила и основания: https://vk.ru/topic-237333137_57395396 "
        "Формат по умолчанию: "
        "«Ответ», затем «Шаги», затем при необходимости «Риски/проверка». "
        "Без markdown-кода и без длинных вступлений."
    )
    if unrestricted:
        system = (
            base_system
            + "Режим полного доступа (admin_id из config.json): ограничения по тематике отключены — "
            + "ты выступаешь и как личный помощник по любым задачам автора запроса, и как помощник для ответов игрокам "
            + "(подбор формулировок, разбор ситуаций, идеи по модерации и поддержке). "
            + "Стиль тот же: конкретно, применимо, без воды; не выдумывай факты о коде/БД без данных."
        )
    else:
        system = (
            base_system
            + "Обычный режим: фокус только на вопросах по этому боту, его коду, механикам, модерации и экономике. "
            + "Если запрос вне контекста проекта — мягко верни диалог к задачам бота и предложи релевантную помощь."
        )
    content = _gemini_generate(system, q[:3500], max_output_tokens=900, temperature=0.2, timeout=90)
    if not content:
        faq_hit = _local_faq_answer(q)
        if faq_hit:
            return faq_hit
        if GEMINI_LAST_ERROR == "quota_exceeded":
            return (
                "Сейчас не могу ответить: у Gemini исчерпана квота API (429). "
                "Проверьте billing/лимиты в Google AI Studio и попробуйте позже."
            )
        if GEMINI_LAST_ERROR == "high_demand":
            return "Gemini сейчас перегружен. Попробуйте повторить запрос через 10-30 секунд."
        return None
    return content.strip()[:3500]


def _format_ai_answer_for_vk(text):
    """Приводит HTML/Markdown-ответ к читабельному plain-text для VK."""
    s = (text or "").strip()
    if not s:
        return ""
    try:
        s = html.unescape(s)
    except Exception:
        pass

    # HTML -> plain text
    s = re.sub(r'(?i)<br\s*/?>', '\n', s)
    s = re.sub(r'(?is)</p\s*>', '\n', s)
    s = re.sub(r'(?is)<p[^>]*>', '', s)
    s = re.sub(r'(?is)</li\s*>', '\n', s)
    s = re.sub(r'(?is)<li[^>]*>', '• ', s)
    s = re.sub(r'(?is)<[^>]+>', '', s)

    # Markdown cleanup
    s = re.sub(r'```(?:\w+)?\s*', '', s)
    s = s.replace('```', '')
    s = re.sub(r'^\s{0,3}#{1,6}\s*', '', s, flags=re.MULTILINE)
    s = re.sub(r'\*\*(.*?)\*\*', r'\1', s)
    s = re.sub(r'__(.*?)__', r'\1', s)
    s = re.sub(r'(?<!\*)\*(?!\*)(.*?)\*(?<!\*)', r'\1', s)
    s = re.sub(r'_(.*?)_', r'\1', s)
    s = re.sub(r'`([^`]+)`', r'\1', s)
    s = re.sub(r'!\[([^\]]*)\]\([^)]+\)', r'\1', s)
    s = re.sub(r'\[([^\]]+)\]\(([^)]+)\)', r'\1 (\2)', s)
    s = re.sub(r'^\s*[-*]\s+', '• ', s, flags=re.MULTILINE)

    # Нормализация пустых строк
    s = re.sub(r'\n{3,}', '\n\n', s).strip()
    return s[:3500]


def get_gpt_answer_kb():
    kb = VkKeyboard(inline=True)
    kb.add_callback_button('Сократить', color=VkKeyboardColor.SECONDARY, payload={'cmd': 'gpt_shorten'})
    return kb


def is_comment_only_digits(text):
    t = re.sub(r'\s+', '', text or '')
    return bool(t) and bool(re.fullmatch(r'[0-9]+', t))


def local_comment_spam_issue(text):
    """
    Локальная проверка: спам символами, повторы, почти нет букв/цифр.
    Возвращает короткое нейтральное сообщение для пользователя или None если пропускаем к Gemini.
    """
    t = (text or '').strip()
    if not t:
        return 'Пустой комментарий не учитывается.'
    nw = ''.join(t.split())
    if len(nw) < 10:
        return 'Комментарий должен содержать минимум 10 символов.'
    return None


def get_bot_stats_lines():
    lines = []
    try:
        local_db = sqlite3.connect(DB_PATH, timeout=15)
        lc = local_db.cursor()
        lc.execute("SELECT COUNT(*) FROM users")
        lines.append(f"Всего пользователей: {lc.fetchone()[0] or 0}")
        lc.execute(
            "SELECT COUNT(DISTINCT user_id) FROM withdrawals WHERE status = 'Ожидает отправки'"
        )
        lines.append(f"Пользователей, ожидающих вывод: {lc.fetchone()[0] or 0}")
        lc.execute("SELECT COUNT(*) FROM withdrawals")
        lines.append(f"Всего подали на вывод (заявок): {lc.fetchone()[0] or 0}")
        lc.execute(
            "SELECT COUNT(*) FROM withdrawals WHERE TRIM(COALESCE(review_text, '')) != ''"
        )
        lines.append(f"Количество отзывов: {lc.fetchone()[0] or 0}")
        local_db.close()
    except Exception:
        lines.append("(статистика временно недоступна)")
    return lines


ADMIN_OP_PAYLOAD_CMDS = frozenset(
    {
        'admin_op_stats',
        'admin_op_banlist',
        'admin_op_withdraw',
        'admin_op_cmds',
        'admin_op_promos',
        'admin_promolist',
        'admin_op_roles',
        'admin_op_menu',
        'admin_op_economy',
    }
)


def _admin_op_stats_text():
    try:
        local_db = sqlite3.connect(DB_PATH, timeout=15)
        lc = local_db.cursor()
        lc.execute("SELECT COUNT(*) FROM users")
        total = lc.fetchone()[0] or 0
        lc.execute("SELECT COUNT(*) FROM users WHERE is_registered = 1")
        reg = lc.fetchone()[0] or 0
        lc.execute("SELECT COUNT(*) FROM users WHERE is_registered = 0")
        unreg = lc.fetchone()[0] or 0
        now = time.time()
        lc.execute(
            "SELECT COUNT(*) FROM users WHERE is_banned = 1 OR (ban_until IS NOT NULL AND ban_until > ?)",
            (now,),
        )
        banned_bot = lc.fetchone()[0] or 0
        lc.execute(
            "SELECT COUNT(*) FROM users WHERE COALESCE(chat_banned, 0) = 1 OR (COALESCE(chat_ban_until, 0) > ?)",
            (now,),
        )
        banned_chat = lc.fetchone()[0] or 0
        lc.execute("SELECT COALESCE(SUM(COALESCE(balance, 0)), 0) FROM users")
        cash_all = int(lc.fetchone()[0] or 0)
        local_db.close()
        return (
            "📊 Статистика пользователей\n\n"
            f"Всего записей в базе: {total}\n"
            f"Зарегистрировано: {reg}\n"
            f"Не завершили регистрацию: {unreg}\n"
            f"Бан в боте (ЛС / глобально): {banned_bot}\n"
            f"Блокировка в беседах: {banned_chat}\n"
            f"Сумма наличных у всех: {format_balance(cash_all)} монет ({format_short(cash_all)})"
        )
    except Exception:
        return "Не удалось загрузить статистику."


def _admin_op_banlist_text():
    """Бан в боте и отдельно блокировки только в беседах."""
    try:
        now = time.time()
        local_db = sqlite3.connect(DB_PATH, timeout=15)
        lc = local_db.cursor()
        lc.execute(
            "SELECT user_id, COALESCE(is_banned, 0), COALESCE(ban_until, 0) FROM users "
            "WHERE COALESCE(is_banned, 0) = 1 OR (ban_until IS NOT NULL AND ban_until > ?) "
            "ORDER BY COALESCE(is_banned, 0) DESC, COALESCE(ban_until, 0) DESC",
            (now,),
        )
        rows_bot = lc.fetchall() or []
        lc.execute(
            "SELECT user_id, COALESCE(chat_banned, 0), COALESCE(chat_ban_until, 0) FROM users "
            "WHERE COALESCE(chat_banned, 0) = 1 OR (COALESCE(chat_ban_until, 0) > ?) "
            "ORDER BY COALESCE(chat_banned, 0) DESC, COALESCE(chat_ban_until, 0) DESC",
            (now,),
        )
        rows_chat = lc.fetchall() or []
        local_db.close()
        lines = ["📛 Банлист\n"]
        if not rows_bot and not rows_chat:
            return "📛 Банлист\n\nСейчас никого нет в бане."
        if rows_bot:
            lines.append(f"\n🤖 В боте (глобально): {len(rows_bot)}\n")
            uids = [int(r[0]) for r in rows_bot]
            names = get_user_names_bulk(uids)
            for uid, is_b, bu in rows_bot[:40]:
                uid = int(uid)
                nm = names.get(uid, f"id{uid}")
                if int(is_b or 0) == 1:
                    kind = "навсегда"
                else:
                    bu_ts = float(bu or 0)
                    left = bu_ts - now
                    dt_s = datetime.fromtimestamp(bu_ts, timezone.utc).strftime("%d.%m.%Y %H:%M")
                    kind = f"до {dt_s} UTC (~{format_time_left_sec(left)})"
                lines.append(f"• @id{uid} ({nm}) — {kind}\n")
            if len(rows_bot) > 40:
                lines.append(f"… ещё {len(rows_bot) - 40}.\n")
        if rows_chat:
            lines.append(f"\n💬 Только беседы: {len(rows_chat)}\n")
            uids_c = [int(r[0]) for r in rows_chat]
            names_c = get_user_names_bulk(uids_c)
            for uid, is_b, bu in rows_chat[:40]:
                uid = int(uid)
                nm = names_c.get(uid, f"id{uid}")
                if int(is_b or 0) == 1:
                    kind = "навсегда (чаты)"
                else:
                    bu_ts = float(bu or 0)
                    left = bu_ts - now
                    dt_s = datetime.fromtimestamp(bu_ts, timezone.utc).strftime("%d.%m.%Y %H:%M")
                    kind = f"в чатах до {dt_s} UTC (~{format_time_left_sec(left)})"
                lines.append(f"• @id{uid} ({nm}) — {kind}\n")
            if len(rows_chat) > 40:
                lines.append(f"… ещё {len(rows_chat) - 40}.\n")
        return "".join(lines)[:3900]
    except Exception:
        return "Не удалось загрузить банлист."


def _admin_op_withdraw_text():
    try:
        local_db = sqlite3.connect(DB_PATH, timeout=15)
        lc = local_db.cursor()
        lc.execute(
            "SELECT COUNT(*), COUNT(DISTINCT user_id), COALESCE(SUM(amount), 0) FROM withdrawals WHERE status = 'Ожидает отправки'"
        )
        row = lc.fetchone()
        n, nu, sm = row[0] or 0, row[1] or 0, row[2] or 0
        lc.execute(
            "SELECT user_id, amount FROM withdrawals WHERE status = 'Ожидает отправки' ORDER BY id DESC LIMIT 12"
        )
        rows = lc.fetchall()
        local_db.close()
        lines = [
            "📤 Заявки на вывод (ожидают)\n\n",
            f"Заявок: {n}\n",
            f"Уникальных пользователей: {nu}\n",
            f"Сумма к выплате: {format_withdraw_mm_rounded(sm)}\n",
        ]
        if rows:
            lines.append("\nПоследние заявки:\n")
            for uid, amt in rows:
                lines.append(f"- @id{uid} — {format_withdraw_mm_rounded(amt)}\n")
        return ''.join(lines)[:3900]
    except Exception:
        return "Не удалось загрузить заявки."


def _top_crown_prefix(lc, uid, now_ts=None):
    now_ts = now_ts if now_ts is not None else time.time()
    lc.execute(
        "SELECT click_boost_until, tax_fast_until FROM users WHERE user_id = ?",
        (uid,),
    )
    r = lc.fetchone()
    if r and ((r[0] or 0) > now_ts or (r[1] or 0) > now_ts):
        return "👑 "
    return ""


def _top_role_prefix(uid):
    try:
        role_key = _get_project_role_key(int(uid))
    except Exception:
        return ""
    if role_key == "owner":
        return "👑 "
    if role_key == "deputy_owner":
        return "🛡 "
    if role_key == "moderator":
        return "👺 "
    if role_key == "sponsor":
        return "💎 "
    return ""


def _top_user_plain(uid, name):
    """Игрок в топе: ссылка [id|имя фамилия] (имя из VK API — first_name + last_name)."""
    uid = int(uid)
    nm = (name or "").strip() or "Пользователь"
    nm = nm.replace("|", "·").replace("]", "›").replace("[", "‹")
    return f"[id{uid}|{nm}]"


def _admin_op_top_refs_text(viewer_user_id=None):
    try:
        local_db = sqlite3.connect(DB_PATH, timeout=15)
        lc = local_db.cursor()
        now_ts = time.time()
        lc.execute(
            "SELECT u.user_id, COUNT(*) AS c, COALESCE(u.click_boost_until, 0), COALESCE(u.tax_fast_until, 0) "
            "FROM users src "
            "JOIN users u ON u.user_id = src.referrer_id "
            "WHERE src.referrer_id IS NOT NULL "
            "GROUP BY u.user_id "
            "ORDER BY c DESC "
            "LIMIT 10"
        )
        rows = lc.fetchall()
        if not rows:
            local_db.close()
            return "🏆 Топ рефералов\n\nПока нет приглашённых."
        lines = ["🏆 Топ по рефералам\n\n👑 — есть активная подписка из магазина\n\n"]
        names = get_user_names_bulk([r[0] for r in rows])
        for i, (rid, c, click_boost_until, tax_fast_until) in enumerate(rows, 1):
            crown = "👑 " if ((click_boost_until or 0) > now_ts or (tax_fast_until or 0) > now_ts) else ""
            role_prefix = _top_role_prefix(rid)
            name = names.get(int(rid), f"id{rid}")
            lines.append(f"{i}. {role_prefix}{crown}{_top_user_plain(rid, name)} — {c}\n")
        if viewer_user_id is not None:
            lc.execute(
                "SELECT COUNT(*) FROM ("
                "SELECT referrer_id, COUNT(*) AS c FROM users WHERE referrer_id IS NOT NULL GROUP BY referrer_id"
                ") t "
                "WHERE t.c > (SELECT COUNT(*) FROM users WHERE referrer_id = ?)",
                (int(viewer_user_id),),
            )
            viewer_rank = int(lc.fetchone()[0] or 0) + 1
            lc.execute("SELECT COUNT(*) FROM users WHERE referrer_id = ?", (int(viewer_user_id),))
            viewer_cnt = int(lc.fetchone()[0] or 0)
            lines.append(f"\n—\nВаше место: {viewer_rank} (рефералов: {viewer_cnt})")
        local_db.close()
        return ''.join(lines)[:3900]
    except Exception:
        return "Не удалось построить топ рефералов."


def _admin_op_top_bal_text(viewer_user_id=None):
    try:
        local_db = sqlite3.connect(DB_PATH, timeout=15)
        lc = local_db.cursor()
        now_ts = time.time()
        lc.execute(
            "SELECT user_id, COALESCE(balance, 0), COALESCE(staff_balance, 0), "
            "COALESCE(click_boost_until, 0), COALESCE(tax_fast_until, 0) "
            "FROM users ORDER BY (COALESCE(balance, 0) + COALESCE(staff_balance, 0)) DESC LIMIT 10"
        )
        rows = lc.fetchall()
        if not rows:
            local_db.close()
            return "💵 Топ балансов\n\nПусто."
        lines = ["💵 Топ балансов\n\n👑 — есть активная подписка из магазина\n\n"]
        names = get_user_names_bulk([r[0] for r in rows])
        for i, (uid, bal, staff_b, click_boost_until, tax_fast_until) in enumerate(rows, 1):
            crown = "👑 " if ((click_boost_until or 0) > now_ts or (tax_fast_until or 0) > now_ts) else ""
            role_prefix = _top_role_prefix(uid)
            name = names.get(int(uid), f"id{uid}")
            total_bal = int(bal or 0) + int(staff_b or 0)
            lines.append(f"{i}. {role_prefix}{crown}{_top_user_plain(uid, name)} — {format_click(total_bal)}$\n")
        if viewer_user_id is not None:
            lc.execute(
                "SELECT COALESCE(balance, 0), COALESCE(staff_balance, 0) FROM users WHERE user_id = ?",
                (int(viewer_user_id),),
            )
            viewer_row = lc.fetchone() or (0, 0)
            viewer_bal = int(viewer_row[0] or 0)
            viewer_staff = int(viewer_row[1] or 0)
            viewer_total = viewer_bal + viewer_staff
            lc.execute(
                "SELECT COUNT(*) FROM users WHERE (COALESCE(balance, 0) + COALESCE(staff_balance, 0)) > ?",
                (viewer_total,),
            )
            viewer_rank = int(lc.fetchone()[0] or 0) + 1
            lines.append(f"\n—\nВаше место: {viewer_rank}")
        local_db.close()
        return ''.join(lines)[:3900]
    except Exception:
        return "Не удалось построить топ балансов."


def _admin_op_top_donations_text(viewer_user_id=None):
    """Топ по сумме пожертвований (donated_total)."""
    try:
        local_db = sqlite3.connect(DB_PATH, timeout=15)
        lc = local_db.cursor()
        now_ts = time.time()
        lc.execute(
            "SELECT user_id, COALESCE(donated_total, 0), COALESCE(click_boost_until, 0), COALESCE(tax_fast_until, 0) "
            "FROM users WHERE COALESCE(donated_total, 0) > 0 "
            "ORDER BY COALESCE(donated_total, 0) DESC LIMIT 10"
        )
        rows = lc.fetchall()
        if not rows:
            local_db.close()
            return "💖 Топ пожертвований\n\nПока никто не жертвовал."
        lines = ["💖 Топ пожертвований\n\n👑 — есть активная подписка из магазина\n\n"]
        names = get_user_names_bulk([r[0] for r in rows])
        for i, (uid, donated, click_boost_until, tax_fast_until) in enumerate(rows, 1):
            crown = "👑 " if ((click_boost_until or 0) > now_ts or (tax_fast_until or 0) > now_ts) else ""
            role_prefix = _top_role_prefix(uid)
            name = names.get(int(uid), f"id{uid}")
            lines.append(f"{i}. {role_prefix}{crown}{_top_user_plain(uid, name)} — {format_click(int(donated or 0))}$\n")
        if viewer_user_id is not None:
            lc.execute("SELECT COALESCE(donated_total, 0) FROM users WHERE user_id = ?", (int(viewer_user_id),))
            viewer_don = int((lc.fetchone() or [0])[0] or 0)
            lc.execute(
                "SELECT COUNT(*) FROM users WHERE COALESCE(donated_total, 0) > ?",
                (viewer_don,),
            )
            viewer_rank = int(lc.fetchone()[0] or 0) + 1
            lines.append(f"\n—\nВаше место: {viewer_rank} (пожертвовано: {format_click(viewer_don)}$)")
        local_db.close()
        return "".join(lines)[:3900]
    except Exception:
        return "Не удалось построить топ пожертвований."


def _admin_op_top_withdrawals_text(viewer_user_id=None):
    """Топ по сумме успешно выведенной валюты (заявки со статусом «Успешно выполнена»)."""
    _w_ok = "Успешно выполнена"
    try:
        local_db = sqlite3.connect(DB_PATH, timeout=15)
        lc = local_db.cursor()
        now_ts = time.time()
        # Сначала только withdrawals: не теряем строки, если user_id нет в users (редкий сбой данных).
        lc.execute(
            "SELECT t.user_id, t.total, "
            "COALESCE(u.click_boost_until, 0), COALESCE(u.tax_fast_until, 0) "
            "FROM ("
            "  SELECT user_id, SUM(COALESCE(amount, 0)) AS total "
            "  FROM withdrawals "
            "  WHERE TRIM(COALESCE(status, '')) = ? "
            "  GROUP BY user_id "
            "  HAVING SUM(COALESCE(amount, 0)) > 0 "
            "  ORDER BY total DESC "
            "  LIMIT 10"
            ") AS t "
            "LEFT JOIN users u ON u.user_id = t.user_id",
            (_w_ok,),
        )
        rows = lc.fetchall()
        if not rows:
            local_db.close()
            return "💸 Топ выводов\n\nПока нет успешно выполненных выводов."
        lines = ["💸 Топ выводов (по сумме выплат)\n\n👑 — активна подписка из магазина\n\n"]
        names = get_user_names_bulk([r[0] for r in rows])
        for i, (uid, total_w, click_boost_until, tax_fast_until) in enumerate(rows, 1):
            crown = "👑 " if ((click_boost_until or 0) > now_ts or (tax_fast_until or 0) > now_ts) else ""
            role_prefix = _top_role_prefix(uid)
            name = names.get(int(uid), f"id{uid}")
            lines.append(f"{i}. {role_prefix}{crown}{_top_user_plain(uid, name)} — {format_click(int(total_w or 0))}$\n")
        if viewer_user_id is not None:
            lc.execute(
                "SELECT COALESCE(SUM(COALESCE(amount, 0)), 0) FROM withdrawals "
                "WHERE user_id = ? AND TRIM(COALESCE(status, '')) = ?",
                (int(viewer_user_id), _w_ok),
            )
            viewer_sum = int((lc.fetchone() or [0])[0] or 0)
            lc.execute(
                "SELECT COUNT(*) FROM ("
                "SELECT user_id FROM withdrawals WHERE TRIM(COALESCE(status, '')) = ? "
                "GROUP BY user_id HAVING SUM(COALESCE(amount, 0)) > ?"
                ") x",
                (_w_ok, viewer_sum),
            )
            viewer_rank = int(lc.fetchone()[0] or 0) + 1
            lines.append(f"\n—\nВаше место: {viewer_rank} (выведено: {format_click(viewer_sum)}$)")
        local_db.close()
        return "".join(lines)[:3900]
    except Exception:
        return "Не удалось построить топ выводов."


def _admin_op_top_spam_text(viewer_user_id=None):
    """Топ по числу сообщений в беседах с ботом (условные «спамеры»)."""
    try:
        local_db = sqlite3.connect(DB_PATH, timeout=15)
        lc = local_db.cursor()
        now_ts = time.time()
        lc.execute(
            "SELECT user_id, COALESCE(chat_msg_count, 0) AS c, COALESCE(click_boost_until, 0), COALESCE(tax_fast_until, 0) "
            "FROM users WHERE COALESCE(chat_msg_count, 0) > 0 "
            "ORDER BY c DESC LIMIT 10"
        )
        rows = lc.fetchall()
        if not rows:
            local_db.close()
            return "📨 Топ по сообщениям в чатах\n\nПока нет данных (пишите в беседах с ботом)."
        lines = ["📨 Топ по сообщениям в чатах (спамеры)\n\n👑 — активна подписка из магазина\n\n"]
        names = get_user_names_bulk([r[0] for r in rows])
        for i, (uid, cnt, click_boost_until, tax_fast_until) in enumerate(rows, 1):
            crown = "👑 " if ((click_boost_until or 0) > now_ts or (tax_fast_until or 0) > now_ts) else ""
            role_prefix = _top_role_prefix(uid)
            name = names.get(int(uid), f"id{uid}")
            lines.append(f"{i}. {role_prefix}{crown}{_top_user_plain(uid, name)} — {format_balance(cnt)} смс\n")
        if viewer_user_id is not None:
            lc.execute("SELECT COALESCE(chat_msg_count, 0) FROM users WHERE user_id = ?", (int(viewer_user_id),))
            viewer_cnt = int((lc.fetchone() or [0])[0] or 0)
            lc.execute("SELECT COUNT(*) FROM users WHERE COALESCE(chat_msg_count, 0) > ?", (viewer_cnt,))
            viewer_rank = int(lc.fetchone()[0] or 0) + 1
            lines.append(f"\n—\nВаше место: {viewer_rank} (сообщений: {format_balance(viewer_cnt)})")
        local_db.close()
        return "".join(lines)[:3900]
    except Exception:
        return "Не удалось построить топ по сообщениям."


def _admin_op_top_klad_text(viewer_user_id=None):
    """Топ по количеству найденных кладов (сумма по всем беседам)."""
    try:
        local_db = sqlite3.connect(DB_PATH, timeout=15)
        lc = local_db.cursor()
        now_ts = time.time()
        lc.execute(
            "SELECT k.user_id, COUNT(*) AS c, COALESCE(u.click_boost_until, 0), COALESCE(u.tax_fast_until, 0) "
            "FROM klad_loot_events k "
            "LEFT JOIN users u ON u.user_id = k.user_id "
            "GROUP BY k.user_id HAVING c > 0 ORDER BY c DESC LIMIT 10"
        )
        rows = lc.fetchall()
        if not rows:
            local_db.close()
            return "🏴‍☠️ Топ по кладу\n\nПока нет данных."
        lines = ["🏴‍☠️ Топ по кладу\n\n👑 — активна подписка из магазина\n\n"]
        names = get_user_names_bulk([r[0] for r in rows])
        for i, (uid, cnt, click_boost_until, tax_fast_until) in enumerate(rows, 1):
            crown = "👑 " if ((click_boost_until or 0) > now_ts or (tax_fast_until or 0) > now_ts) else ""
            role_prefix = _top_role_prefix(uid)
            name = names.get(int(uid), f"id{uid}")
            lines.append(f"{i}. {role_prefix}{crown}{_top_user_plain(uid, name)} — {format_balance(cnt)}\n")
        if viewer_user_id is not None:
            lc.execute("SELECT COUNT(*) FROM klad_loot_events WHERE user_id = ?", (int(viewer_user_id),))
            viewer_cnt = int(lc.fetchone()[0] or 0)
            lc.execute(
                "SELECT COUNT(*) FROM ("
                "SELECT user_id, COUNT(*) AS c FROM klad_loot_events GROUP BY user_id"
                ") t WHERE t.c > ?",
                (viewer_cnt,),
            )
            viewer_rank = int(lc.fetchone()[0] or 0) + 1
            lines.append(f"\n—\nВаше место: {viewer_rank} (кладов: {format_balance(viewer_cnt)})")
        local_db.close()
        return "".join(lines)[:3900]
    except Exception:
        return "Не удалось построить топ по кладу."


def _has_top3_anywhere(user_id):
    """True, если пользователь в топ-3 хотя бы в одном активном топе."""
    try:
        uid = int(user_id)

        # Топ по рефералам (учитываем только пользователей с >=1 рефералом).
        cursor.execute("SELECT COUNT(*) FROM users WHERE referrer_id = ?", (uid,))
        refs_cnt = int(cursor.fetchone()[0] or 0)
        if refs_cnt > 0:
            cursor.execute(
                "SELECT COUNT(*) FROM ("
                "SELECT referrer_id, COUNT(*) AS c FROM users "
                "WHERE referrer_id IS NOT NULL GROUP BY referrer_id"
                ") t WHERE t.c > ?",
                (refs_cnt,),
            )
            if int(cursor.fetchone()[0] or 0) + 1 <= 3:
                return True

        # Топ по балансу (наличные + служебные, без «банка»).
        cursor.execute(
            "SELECT COALESCE(balance, 0) + COALESCE(staff_balance, 0) FROM users WHERE user_id = ?",
            (uid,),
        )
        total_bal = int((cursor.fetchone() or [0])[0] or 0)
        cursor.execute(
            "SELECT COUNT(*) FROM users WHERE (COALESCE(balance, 0) + COALESCE(staff_balance, 0)) > ?",
            (total_bal,),
        )
        if int(cursor.fetchone()[0] or 0) + 1 <= 3:
            return True

        # Топ по сообщениям в чатах.
        cursor.execute("SELECT COALESCE(chat_msg_count, 0) FROM users WHERE user_id = ?", (uid,))
        chat_cnt = int((cursor.fetchone() or [0])[0] or 0)
        if chat_cnt > 0:
            cursor.execute("SELECT COUNT(*) FROM users WHERE COALESCE(chat_msg_count, 0) > ?", (chat_cnt,))
            if int(cursor.fetchone()[0] or 0) + 1 <= 3:
                return True

        # Топ по заработку с ограблений.
        cursor.execute("SELECT COALESCE(total_earned_from_heists, 0) FROM users WHERE user_id = ?", (uid,))
        heist_sum = int((cursor.fetchone() or [0])[0] or 0)
        if heist_sum > 0:
            cursor.execute("SELECT COUNT(*) FROM users WHERE COALESCE(total_earned_from_heists, 0) > ?", (heist_sum,))
            if int(cursor.fetchone()[0] or 0) + 1 <= 3:
                return True
    except Exception:
        return False
    return False


def _admin_op_cmds_text():
    return (
        "📜 Админ-команды\n\n"
        "Интерфейс и очередь выводов: команды владельца !настройки, !ui+/-, !опвывод (см. ответ на !настройки); "
        "дефолты в config.json.\n\n"
        "Базовые:\n"
        "- /op\n"
        "- /promolist\n"
        "- //baninfo [юзер]\n"
        "- /гпт [запрос]\n\n"
        "Управление и экономика:\n"
        "- !экономика / !эко — в т.ч. клик (кн/кв), корм (к), «за все» (квсе), порог, буст клика (бц/бб/бд); в /op → «Экономика»\n"
        "- !выводы\n"
        "- !vivod [лимит]\n"
        "- !рассылка [текст]\n"
        "- !деп-\n"
        "- /even1 — доначисление денег ивента (дни 3–6), если условия есть, а награда не пришла\n"
        "- !сбор [сумма] — с балансов всех игроков в казну (например !сбор 10мм)\n"
        "- !выдать [юзер] [сумма]\n"
        "- !снять [юзер] [сумма]\n"
        "- !твинк [юзер] — метка «твинк» (без вывода); !-твинк [юзер] — снять\n"
        "- !-модерденьги — обнулить служебный баланс у всех пользователей\n"
        "- !кд [юзер] — сброс игровых кулдаунов (или ответом на сообщение: !кд)\n"
        "- !должность [юзер] [должность]\n"
        "- !повысить [юзер]\n\n"
        "Модерация:\n"
        "- бан [юзер] [время] — в беседе: блок только в чатах; в ЛС бота: бан в игре (глобально)\n"
        "- разбан [юзер] — снимает оба вида бана\n"
        "- !капча [юзер]\n\n"
        "Промокоды:\n"
        "- !создатьпромо [код] [сумма] [активации]\n"
        "- !создатьбуст [название] [+%] [время] [м|ч]\n"
        "- !удалитьпромо [код]\n"
        "- /promolist\n\n"
        "«Юзер» — упоминание или ссылка на профиль ВК. Суммы: $, мк, мм.\n\n"
        "Должности для !должность:\n"
        "- модератор\n"
        "- спонсор\n"
        "- зам владелец\n"
        "- снять"
    )


def _op_perm_line(has_right: bool, text_line: str) -> str:
    """Строка права в конструкторе ролей /op: 🟢 есть / 🔴 нет."""
    return f"{'🟢' if has_right else '🔴'} {text_line}"


_OP_ROLE_CATALOG_KEYS = frozenset(
    {
        "owner",
        "deputy_owner",
        "moderator",
        "sponsor",
    }
)


def _op_roles_catalog_intro_text():
    return (
        "🎭 Конструктор ролей\n\n"
        "Справочник по правам для должностей из !должность и владельца.\n"
        "🟢 — право есть у роли, 🔴 — нет.\n"
        "Выберите роль кнопкой ниже.\n\n"
        "Подсказка для !должность: модератор, спонсор, зам владелец; «снять» — убрать роль."
    )


def _op_roles_card_text(rk: str):
    """Текст карточки «права по роли» для /op → 🎭 Роли (🟢 / 🔴)."""
    rk = (rk or "").strip()
    if rk not in _OP_ROLE_CATALOG_KEYS:
        return "Неизвестная роль. Откройте список кнопкой «◀ К списку ролей»."
    label = PROJECT_ROLE_LABELS.get(rk, rk)
    L = _op_perm_line

    if rk == "owner":
        return "\n".join(
            [
                label,
                "",
                L(True, "/op, /promolist, //baninfo, бан, разбан, кик, !капча, !создатьпромо, /гпт, !выводы"),
                L(True, "!удалитьпромо, !рассылка, !экономика / !эко, !деп-, !выдать, !снять, !сбор, !должность, !кд"),
                L(True, "/even1, /repost33, /выговор (репосты), +/− выговор по составу, мут/размут по правилам владельца"),
            ]
        )
    if rk == "deputy_owner":
        return "\n".join(
            [
                label,
                "",
                L(True, "/op, конструктор конкурса, /promolist, //baninfo, !выводы"),
                L(True, "бан до 30 мин, разбан, !капча, !создатьпромо"),
                L(True, "беседа: кик"),
                L(True, "+выговор / −выговор по выговорам состава (не владельца)"),
                L(True, "!должность: модератор, спонсор, снять"),
                L(False, "!рассылка, !экономика, !выдать, полный !должность — только владелец"),
                L(False, "мут/размут/−варн по составу в беседе — только владелец"),
            ]
        )
    if rk == "moderator":
        return "\n".join(
            [
                label,
                "",
                L(True, "/promolist, «промокоды»"),
                L(True, "беседа: мут, −мут, размут, −варн"),
                L(True, "админ-беседа: /инфо [юзер]"),
                L(True, "+выговор / −выговор только по выговорам состава (не владельца)"),
                L(False, "/op, бан игры, !капча, !создатьпромо — нет"),
            ]
        )
    if rk == "sponsor":
        return "\n".join(
            [
                label,
                "",
                L(False, "модераторские команды в беседе"),
                L(True, "служебный баланс при начислениях !выдать от владельца (по правилам бота)"),
            ]
        )
    return f"{label}\n\n(описание не задано.)"


def get_op_roles_constructor_kb():
    """Кнопки выбора роли для конструктора (callback — иначе VK не присылает payload)."""
    kb = VkKeyboard(inline=True)
    kb.add_callback_button("👑 Владелец", color=VkKeyboardColor.POSITIVE, payload={"cmd": "admin_op_roles", "rk": "owner"})
    kb.add_callback_button("🛡 Зам", color=VkKeyboardColor.POSITIVE, payload={"cmd": "admin_op_roles", "rk": "deputy_owner"})
    kb.add_line()
    kb.add_callback_button("🧩 Модер", color=VkKeyboardColor.POSITIVE, payload={"cmd": "admin_op_roles", "rk": "moderator"})
    kb.add_callback_button("💎 Спонсор", color=VkKeyboardColor.SECONDARY, payload={"cmd": "admin_op_roles", "rk": "sponsor"})
    kb.add_line()
    kb.add_callback_button("◀ Панель /op", color=VkKeyboardColor.PRIMARY, payload={"cmd": "admin_op_menu"})
    return kb


def get_op_roles_detail_kb():
    kb = VkKeyboard(inline=True)
    kb.add_callback_button("◀ К списку ролей", color=VkKeyboardColor.SECONDARY, payload={"cmd": "admin_op_roles"})
    kb.add_callback_button("◀ Панель /op", color=VkKeyboardColor.PRIMARY, payload={"cmd": "admin_op_menu"})
    return kb


def _admin_op_promos_text():
    return (
        "🎟 Промокоды\n\n"
        "!создатьпромо [код] [сумма] [активации]\n"
        "!удалитьпромо [код] — удалить промокод (только владелец)\n"
        "Пример: !создатьпромо SUMMER 200мк 100\n"
        "/promolist — активные промокоды (сначала где меньше активаций)\n"
        "Для игрока: промо КОД\n\n"
        + promolist_admin_text()
    )[:3900]


def get_op_panel_kb(user_id=None):
    kb = VkKeyboard(inline=True)
    kb.add_callback_button('📊 Статистика', color=VkKeyboardColor.PRIMARY, payload={'cmd': 'admin_op_stats'})
    kb.add_callback_button('📛 Банлист', color=VkKeyboardColor.SECONDARY, payload={'cmd': 'admin_op_banlist'})
    kb.add_line()
    kb.add_callback_button('📤 На вывод', color=VkKeyboardColor.SECONDARY, payload={'cmd': 'admin_op_withdraw'})
    kb.add_callback_button('🎟 Промокоды', color=VkKeyboardColor.SECONDARY, payload={'cmd': 'admin_op_promos'})
    kb.add_line()
    kb.add_callback_button('📜 Админ-команды', color=VkKeyboardColor.SECONDARY, payload={'cmd': 'admin_op_cmds'})
    if user_id is not None and _is_owner(user_id):
        kb.add_line()
        kb.add_callback_button('⚙️ Экономика', color=VkKeyboardColor.SECONDARY, payload={'cmd': 'admin_op_economy'})
        kb.add_callback_button('📨 Рассылка (!рассылка)', color=VkKeyboardColor.SECONDARY, payload={'cmd': 'admin_op_cmds'})
    elif user_id is not None and _is_deputy_owner(user_id):
        kb.add_line()
        kb.add_callback_button('📨 Команды зама', color=VkKeyboardColor.SECONDARY, payload={'cmd': 'admin_op_cmds'})
    if user_id is not None and (_is_owner(user_id) or _is_deputy_owner(user_id)):
        kb.add_line()
        kb.add_callback_button('🎁 Конкурс', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'admin_op_contest'})
    return kb


def _op_contest_draft_load(user_id):
    try:
        cursor.execute("SELECT COALESCE(op_contest_draft, '') FROM users WHERE user_id = ?", (int(user_id),))
        raw = (cursor.fetchone() or [""])[0] or ""
        if not str(raw).strip():
            return None
        return json.loads(raw)
    except Exception:
        return None


def _op_contest_draft_save(user_id, data):
    update_user(int(user_id), "op_contest_draft", json.dumps(data, ensure_ascii=False))


def _op_contest_draft_clear(user_id):
    update_user(int(user_id), "op_contest_draft", "")


def get_op_contest_cancel_kb():
    kb = VkKeyboard(inline=True)
    kb.add_callback_button("Отмена", color=VkKeyboardColor.NEGATIVE, payload={"cmd": "contest_cb", "a": "x"})
    return kb


def get_op_contest_dashboard_kb():
    kb = VkKeyboard(inline=True)
    kb.add_callback_button("🔄 Обновить", color=VkKeyboardColor.PRIMARY, payload={"cmd": "contest_owner", "a": "rf"})
    kb.add_line()
    kb.add_callback_button("✅ Завершить", color=VkKeyboardColor.SECONDARY, payload={"cmd": "contest_owner", "a": "end"})
    kb.add_callback_button("🆕 Новый конкурс", color=VkKeyboardColor.POSITIVE, payload={"cmd": "contest_owner", "a": "new"})
    return kb


def _op_contest_step_intro(step, total, title, body_text):
    """Единообразный заголовок шагов конструктора."""
    bar = "──────────────"
    body = (body_text or "").strip()
    return f"🎁 Конструктор конкурса  ·  шаг {step}/{total}\n{bar}\n\n{title}\n\n{body}"[:3900]


def _op_contest_conditions_summary(d):
    lines = []
    lines.append(f"🔔 Подписка на сообщество — {'включено' if d.get('sub', True) else 'выключено'}")
    don_on = bool(d.get("don_on", False))
    don_n = max(1, int(d.get("don_n", 1)))
    lines.append(
        f"💸 Пожертвования в боте — {'минимум ' + str(don_n) + ' мм суммой' if don_on else 'выключено'}"
    )
    ref_on = bool(d.get("ref_on", False))
    ref_n = max(1, int(d.get("ref_n", 1)))
    lines.append(f"👥 Рефералы — {'минимум ' + str(ref_n) if ref_on else 'выключено'}")
    rlab = (d.get("results_end_label") or "").strip()
    lines.append(f"📅 Итоги — {rlab if rlab else 'не указано'}")
    return "\n".join(lines)


def _parse_contest_results_datetime(raw):
    """Парсит дату/время итогов в МСК. Формат: ДД.ММ.ГГГГ ЧЧ:ММ. Возвращает (label, unix_ts) или (None, None)."""
    s = (raw or "").strip()
    m = re.match(
        r"^(\d{1,2})\.(\d{1,2})\.(\d{4})\s+(\d{1,2}):(\d{2})\s*(?:мск)?\s*$",
        s,
        re.IGNORECASE,
    )
    if not m:
        return None, None
    try:
        day, month, year = int(m.group(1)), int(m.group(2)), int(m.group(3))
        hour, minute = int(m.group(4)), int(m.group(5))
        dt_msk = datetime(year, month, day, hour, minute, 0)
    except ValueError:
        return None, None
    msk_tz = timezone(timedelta(hours=3))
    dt_aware = dt_msk.replace(tzinfo=msk_tz)
    ts = float(dt_aware.timestamp())
    label = f"{day:02d}.{month:02d}.{year} {hour:02d}:{minute:02d} МСК"
    return label, ts


def get_op_contest_conditions_kb(d):
    """Инлайн-клавиатура шага «условия». ВК: не более 10 кнопок на одной клавиатуре."""
    kb = VkKeyboard(inline=True)
    sub_on = bool(d.get("sub", True))
    don_on = bool(d.get("don_on", False))
    ref_on = bool(d.get("ref_on", False))
    don_n = max(1, int(d.get("don_n", 1)))
    ref_n = max(1, int(d.get("ref_n", 1)))

    kb.add_callback_button(
        f"{'✓' if sub_on else '○'} Подписка",
        color=VkKeyboardColor.POSITIVE if sub_on else VkKeyboardColor.SECONDARY,
        payload={"cmd": "contest_cb", "a": "ts"},
    )
    kb.add_callback_button(
        f"{'✓' if don_on else '○'} Пожертв.",
        color=VkKeyboardColor.POSITIVE if don_on else VkKeyboardColor.SECONDARY,
        payload={"cmd": "contest_cb", "a": "td"},
    )
    kb.add_callback_button(
        f"{'✓' if ref_on else '○'} Рефералы",
        color=VkKeyboardColor.POSITIVE if ref_on else VkKeyboardColor.SECONDARY,
        payload={"cmd": "contest_cb", "a": "tr"},
    )
    kb.add_line()
    if don_on and ref_on:
        # Одна строка порогов — иначе с тремя рядами переваливаем лимит 10 кнопок на клавиатуру
        kb.add_callback_button("−", color=VkKeyboardColor.SECONDARY, payload={"cmd": "contest_cb", "a": "dm"})
        kb.add_callback_button("+", color=VkKeyboardColor.SECONDARY, payload={"cmd": "contest_cb", "a": "dp"})
        kb.add_callback_button("−", color=VkKeyboardColor.SECONDARY, payload={"cmd": "contest_cb", "a": "rm"})
        kb.add_callback_button("+", color=VkKeyboardColor.SECONDARY, payload={"cmd": "contest_cb", "a": "rp"})
        kb.add_line()
    elif don_on:
        kb.add_callback_button("−", color=VkKeyboardColor.SECONDARY, payload={"cmd": "contest_cb", "a": "dm"})
        kb.add_callback_button(
            f"мм:{don_n}",
            color=VkKeyboardColor.PRIMARY,
            payload={"cmd": "contest_cb", "a": "nd"},
        )
        kb.add_callback_button("+", color=VkKeyboardColor.SECONDARY, payload={"cmd": "contest_cb", "a": "dp"})
        kb.add_line()
    elif ref_on:
        kb.add_callback_button("−", color=VkKeyboardColor.SECONDARY, payload={"cmd": "contest_cb", "a": "rm"})
        kb.add_callback_button(
            f"реф:{ref_n}",
            color=VkKeyboardColor.PRIMARY,
            payload={"cmd": "contest_cb", "a": "nr"},
        )
        kb.add_callback_button("+", color=VkKeyboardColor.SECONDARY, payload={"cmd": "contest_cb", "a": "rp"})
        kb.add_line()
    kb.add_callback_button("✨ Дальше", color=VkKeyboardColor.POSITIVE, payload={"cmd": "contest_cb", "a": "pr"})
    kb.add_line()
    kb.add_callback_button("✖ Отмена", color=VkKeyboardColor.NEGATIVE, payload={"cmd": "contest_cb", "a": "x"})
    return kb


def get_op_contest_date_invite_kb():
    """Отдельное сообщение: только переход к вводу даты (не считается в лимит 10 кнопок основного меню)."""
    kb = VkKeyboard(inline=True)
    kb.add_callback_button("📅 Указать дату итогов", color=VkKeyboardColor.SECONDARY, payload={"cmd": "contest_cb", "a": "dt"})
    return kb


def get_op_contest_results_dt_kb():
    kb = VkKeyboard(inline=True)
    kb.add_callback_button("◀ К условиям", color=VkKeyboardColor.SECONDARY, payload={"cmd": "contest_cb", "a": "bk"})
    kb.add_callback_button("✖ Отмена", color=VkKeyboardColor.NEGATIVE, payload={"cmd": "contest_cb", "a": "x"})
    return kb


def get_op_contest_preview_kb():
    kb = VkKeyboard(inline=True)
    kb.add_callback_button("✅ Опубликовать", color=VkKeyboardColor.POSITIVE, payload={"cmd": "contest_cb", "a": "pf"})
    kb.add_line()
    kb.add_callback_button("◀ К условиям", color=VkKeyboardColor.SECONDARY, payload={"cmd": "contest_cb", "a": "bc"})
    kb.add_callback_button("✖ Отмена", color=VkKeyboardColor.NEGATIVE, payload={"cmd": "contest_cb", "a": "x"})
    return kb


def _op_contest_polish_with_gemini(full_text):
    """Улучшает готовый текст поста через Gemini; при ошибке — None."""
    system = (
        "Ты редактор постов для сообщества ВКонтакте. "
        "Улучши текст ниже: добавь уместные эмодзи, сделай аккуратную структуру "
        "(короткие абзацы, тире «—», пустые строки между блоками, без маркированных списков), "
        "чтобы пост выглядел живым и читаемым, как будто его оформил человек вручную, а не шаблон. "
        "Запрещён символ маркера списка «•» (U+2022) и строки, начинающиеся с него; не подставляй вместо него похожие буллеты. "
        "Пожертвования (донаты) в условиях конкурса считаются в мм — это игровая валюта; не переводи мм в «штуки» и не меняй единицы. "
        "Не используй канцелярит, не упоминай нейросети, ИИ и автоматическую генерацию. "
        "Сохрани все числа, суммы в $ и обозначениях мк/мм, даты, количество победителей, требования и условия — "
        "не выдумывай нового и не меняй смысл. "
        "Не добавляй хэштеги, если их не было в исходнике. "
        "Верни только готовый текст поста, без пояснений до или после."
    )
    return _gemini_generate(
        system,
        (full_text or "")[:6000],
        max_output_tokens=2048,
        temperature=0.38,
        timeout=120,
    )


def _op_contest_send_date_invite_message(user_id, reply_peer, d):
    """Второе сообщение только с кнопкой даты — не смешиваем с основной клавиатурой (лимит ВК 10 кнопок)."""
    d2 = _op_contest_draft_load(user_id)
    if not d2 or d2.get("step") != "conditions" or d2.get("date_card_sent"):
        return
    msg = (
        "📅 Дата итогов конкурса\n\n"
        "Нажмите кнопку ниже — бот попросит дату и время одной строкой. "
        "Можно указать позже, перед «✨ Дальше»."
    )
    mid = send_msg(int(reply_peer), msg[:3900], get_op_contest_date_invite_kb())
    _admin_op_ui_stack_record(user_id, reply_peer, mid)
    d2["date_card_sent"] = True
    _op_contest_draft_save(user_id, d2)
    d["date_card_sent"] = True


def _op_contest_prompt_conditions(user_id, reply_peer, d, edit_cmid=0):
    body = d.get("body") or ""
    winners = max(1, int(d.get("winners", 1)))
    prize = int(d.get("prize", 0))
    preview = body if len(body) <= 700 else (body[:700] + "…")
    recap = (
        "📎 Черновик текста\n"
        f"{preview}\n\n"
        f"🏆 Победителей: {winners}\n"
        f"💰 Приз: {format_click(prize)}$ ({format_mm_tenths(prize)})\n"
        f"──────────────\n"
        f"Сейчас выбрано:\n{_op_contest_conditions_summary(d)}"
    )
    hint = (
        "\n\n"
        "Первый ряд — что требовать; при вкл. пожертв./рефералов строка порогов: − / + "
        "(при двух условиях в одном ряду — слева мм, справа рефералы; числа в сводке выше).\n"
        "Нужно ≥1 условие (если всё выкл — снова подписка). Дату итогов — отдельным сообщением под этим · ✨ оформление и пост."
    )
    txt = _op_contest_step_intro(4, 6, "⚙️ Условия для участников", recap + hint)
    kb = get_op_contest_conditions_kb(d)
    _ec = int(edit_cmid or 0)
    if _ec > 0:
        try:
            vk.messages.edit(
                peer_id=int(reply_peer),
                conversation_message_id=_ec,
                message=txt[:3900],
                keyboard=kb.get_keyboard(),
            )
            _op_contest_send_date_invite_message(user_id, reply_peer, d)
            return
        except Exception as _e:
            print(f"[contest conditions edit] {_e}")
    send_msg_admin_op_panel(user_id, reply_peer, txt[:3900], kb)
    _op_contest_send_date_invite_message(user_id, reply_peer, d)


def _op_contest_build_final_text(d):
    body = (d.get("body") or "").strip()
    winners = max(1, int(d.get("winners", 1)))
    prize = int(d.get("prize", 0))
    sub = bool(d.get("sub", True))
    don_on = bool(d.get("don_on", False))
    ref_on = bool(d.get("ref_on", False))
    don_n = max(1, int(d.get("don_n", 1)))
    ref_n = max(1, int(d.get("ref_n", 1)))
    lines = [
        "🎁 РОЗЫГРЫШ",
        "",
        body,
        "",
        f"💰 Сумма розыгрыша: {format_click(prize)}$ ({format_mm_tenths(prize)})",
        f"🏆 Победителей: {winners}",
        "",
        "📋 Условия участия:",
    ]
    if sub:
        lines.append("— Быть подписанным на сообщество на момент подведения итогов.")
    if don_on:
        lines.append(
            f"— Набрать в боте не менее {don_n} мм пожертвований командой «пожертвование» (сумма в мм, не число нажатий)."
        )
    if ref_on:
        lines.append(f"— Пригласить по реферальной ссылке не менее {ref_n} новых игроков (с завершённой регистрацией).")
    rlab = (d.get("results_end_label") or "").strip()
    if rlab:
        lines.append("")
        lines.append(f"⏰ Подведение итогов: {rlab}.")
    lines.append("")
    lines.append("—")
    lines.append("Текст собран конструктором конкурсов (/op → 🎁 Конкурс).")
    return "\n".join(lines).strip()[:3900]


def _get_active_contest_row():
    try:
        cursor.execute(
            "SELECT id, created_at, results_end_ts, results_end_label, body_preview, prize, winners, final_post_text "
            "FROM contests WHERE status = 'active' ORDER BY id DESC LIMIT 1"
        )
        return cursor.fetchone()
    except Exception:
        return None


def _count_contest_participants(contest_id):
    try:
        cursor.execute(
            "SELECT COUNT(*) FROM contest_participants WHERE contest_id = ?",
            (int(contest_id),),
        )
        return int((cursor.fetchone() or [0])[0] or 0)
    except Exception:
        return 0


def _end_all_active_contests():
    try:
        cursor.execute("UPDATE contests SET status = 'ended' WHERE status = 'active'")
        db.commit()
    except Exception:
        pass


def _publish_contest_from_draft(d, final_text):
    _end_all_active_contests()
    now = time.time()
    body_prev = ((d.get("body") or "").strip())[:500]
    rts = d.get("results_end_ts")
    rlab = (d.get("results_end_label") or "").strip() or None
    prize = int(d.get("prize", 0))
    winners = max(1, int(d.get("winners", 1)))
    ft = (final_text or "")[:12000]
    cursor.execute(
        "INSERT INTO contests (created_at, results_end_ts, results_end_label, body_preview, prize, winners, status, final_post_text) "
        "VALUES (?, ?, ?, ?, ?, ?, 'active', ?)",
        (now, rts, rlab, body_prev, prize, winners, ft),
    )
    db.commit()
    return int(cursor.lastrowid or 0)


def _format_contest_owner_dashboard_text(row):
    cid = int(row[0])
    n = _count_contest_participants(cid)
    rlab = (row[3] or "").strip() if len(row) > 3 else ""
    rts = row[2] if len(row) > 2 else None
    if not rlab and rts:
        try:
            msk = timezone(timedelta(hours=3))
            rlab = datetime.fromtimestamp(float(rts), tz=msk).strftime("%d.%m.%Y %H:%M МСК")
        except Exception:
            rlab = ""
    return (
        "🎁 Активный конкурс\n\n"
        f"👥 Участников: {n}\n"
        f"⏰ Дата итогов: {rlab if rlab else 'не указано'}\n\n"
        f"ID: {cid}"
    )[:3900]


def _public_contest_menu_text(row):
    """Краткое описание активного конкурса для игроков (главное меню / кнопка «Конкурс»)."""
    cid = int(row[0])
    n = _count_contest_participants(cid)
    rlab = (row[3] or "").strip() if len(row) > 3 else ""
    rts = row[2] if len(row) > 2 else None
    if not rlab and rts:
        try:
            msk = timezone(timedelta(hours=3))
            rlab = datetime.fromtimestamp(float(rts), tz=msk).strftime("%d.%m.%Y %H:%M МСК")
        except Exception:
            rlab = ""
    prev = (row[4] or "").strip() if len(row) > 4 else ""
    if not prev and len(row) > 7:
        prev = ((row[7] or "").strip())[:600]
    if len(prev) > 600:
        prev = prev[:600] + "…"
    lines = ["🎁 Сейчас проходит розыгрыш", ""]
    if prev:
        lines.append(prev)
        lines.append("")
    lines.append(f"⏰ Дата итогов: {rlab if rlab else 'уточняется'}")
    lines.append(f"👥 Уже в участниках: {n}")
    lines.append("")
    lines.append("Чтобы записаться, отправьте: участие")
    return "\n".join(lines)[:3900]


def _register_contest_participation(user_id):
    row = _get_active_contest_row()
    if not row:
        return False, "no_contest"
    cid = int(row[0])
    try:
        cursor.execute(
            "SELECT 1 FROM contest_participants WHERE contest_id = ? AND user_id = ?",
            (cid, int(user_id)),
        )
        if cursor.fetchone():
            return True, "already"
        cursor.execute(
            "INSERT INTO contest_participants (contest_id, user_id, joined_at) VALUES (?, ?, ?)",
            (cid, int(user_id), float(time.time())),
        )
        db.commit()
        return True, "new"
    except Exception:
        return False, "error"


def _op_contest_process_owner(user_id, reply_peer, text, payload_cmd, payload_data, contest_edit_cmid=0):
    """Обработка мастера конструктора конкурсов для владельца/зама. True — сообщение обработано.
    contest_edit_cmid — для callback: правка того же сообщения (клавиатура не «пропадает»)."""
    if not (_is_owner(user_id) or _is_deputy_owner(user_id)):
        return False

    ce = int(contest_edit_cmid or 0)
    draft_snap = _op_contest_draft_load(user_id)
    if not _is_private_bot_dialog(reply_peer, user_id):
        # Инлайн-кнопки конкурса (contest_cb / contest_owner / admin_op_contest) должны
        # доходить до обработчиков ниже — иначе «Отмена» не чистит op_contest_draft, и бот
        # бесконечно глотает сообщения владельца в этом peer без ответа.
        if payload_cmd in ("admin_op_contest", "contest_cb", "contest_owner"):
            pass
        elif bool((draft_snap or {}).get("step")):
            # Не глотаем текст без ответа: обычные команды должны работать (конструктор — из ЛС)
            return False
        else:
            return False

    if payload_cmd == "contest_owner":
        oa = (payload_data or {}).get("a")
        if oa == "rf":
            row = _get_active_contest_row()
            if row:
                send_msg_admin_op_panel(user_id, reply_peer, _format_contest_owner_dashboard_text(row), get_op_contest_dashboard_kb())
            else:
                send_msg_admin_op_panel(user_id, reply_peer, "Сейчас нет активного опубликованного конкурса.", get_op_panel_kb(user_id))
            return True
        if oa == "end":
            _end_all_active_contests()
            send_msg_admin_op_panel(user_id, reply_peer, "✅ Конкурс завершён. Можно создать новый: /op → 🎁 Конкурс.", get_op_panel_kb(user_id))
            return True
        if oa == "new":
            _end_all_active_contests()
            _op_contest_draft_clear(user_id)
            _op_contest_draft_save(user_id, {"step": "text"})
            send_msg_admin_op_panel(
                user_id, reply_peer,
                _op_contest_step_intro(
                    1,
                    6,
                    "✏️ Текст объявления",
                    "Опишите розыгрыш одним сообщением: о чём пост, сроки, как участвовать.\n\n"
                    "«отмена» — выйти из конструктора.",
                ),
                get_op_contest_cancel_kb(),
            )
            return True
        return True

    if payload_cmd == "contest_cb":
        act = (payload_data or {}).get("a")
        d = _op_contest_draft_load(user_id)
        if act == "x":
            _op_contest_draft_clear(user_id)
            send_msg_admin_op_panel(user_id, reply_peer, "Конструктор конкурса отменён.", get_op_panel_kb(user_id))
            return True
        if not d:
            send_msg_admin_op_panel(
                user_id, reply_peer,
                "Сессия конструктора неактивна. Откройте /op → 🎁 Конкурс.",
                get_op_panel_kb(user_id),
            )
            return True
        if d.get("step") == "preview_ai":
            if act == "bc":
                d.pop("polished_text", None)
                d.pop("base_final", None)
                d["step"] = "conditions"
                _op_contest_draft_save(user_id, d)
                _op_contest_prompt_conditions(user_id, reply_peer, d, edit_cmid=ce)
                return True
            if act == "pf":
                if not (d.get("sub") or d.get("don_on") or d.get("ref_on")):
                    d["sub"] = True
                pub_text = (d.get("polished_text") or "").strip() or _op_contest_build_final_text(d)
                pub_text = pub_text[:12000]
                _publish_contest_from_draft(d, pub_text)
                _op_contest_draft_clear(user_id)
                send_msg_admin_op_panel(user_id, reply_peer, pub_text[:3900], get_op_panel_kb(user_id))
                return True
            send_msg_admin_op_panel(
                user_id, reply_peer,
                "На этом шаге доступны кнопки: «Опубликовать», «К условиям» или «Отмена».",
                get_op_contest_preview_kb(),
            )
            return True
        if d.get("step") == "results_dt":
            if act == "bk":
                d["step"] = "conditions"
                _op_contest_draft_save(user_id, d)
                _op_contest_prompt_conditions(user_id, reply_peer, d, edit_cmid=ce)
                return True
            send_msg(
                reply_peer,
                "Сейчас введите дату и время итогов текстом или нажмите «К условиям».",
                get_op_contest_results_dt_kb(),
            )
            return True
        if d.get("step") != "conditions":
            send_msg_admin_op_panel(
                user_id, reply_peer,
                "Сессия конструктора не на шаге условий. Откройте /op → 🎁 Конкурс или нажмите «Отмена».",
                get_op_panel_kb(user_id),
            )
            return True
        if act == "dt":
            d["step"] = "results_dt"
            _op_contest_draft_save(user_id, d)
            # Не send_msg_admin_op_panel — иначе сотрётся сообщение с условиями (стек /op UI).
            send_msg(
                reply_peer,
                _op_contest_step_intro(
                    5,
                    6,
                    "📅 Дата и время итогов",
                    "Одной строкой, по московскому времени (МСК):\n"
                    "ДД.ММ.ГГГГ ЧЧ:ММ\n"
                    "Пример: 15.04.2026 21:00 (установка по мск врмени)\n\n"
                    "«отмена» — вернуться к условиям без сохранения даты.",
                )[:3900],
                get_op_contest_results_dt_kb(),
            )
            return True
        if act in ("pr", "f"):
            if not (d.get("sub") or d.get("don_on") or d.get("ref_on")):
                d["sub"] = True
            final = _op_contest_build_final_text(d)
            send_msg_admin_op_panel(
                user_id, reply_peer,
                "⏳ Оформляю текст… Это может занять до минуты.",
            )
            polished = _op_contest_polish_with_gemini(final)
            note = ""
            if not (polished or "").strip():
                polished = final
                if GEMINI_LAST_ERROR == "missing_api_key":
                    note = "\n\n⚠️ Ключ Gemini не задан в config — показан исходный черновик без автооформления."
                elif GEMINI_LAST_ERROR in ("quota_exceeded", "high_demand"):
                    note = "\n\n⚠️ Нейросеть временно недоступна (лимит или перегрузка) — показан исходный текст."
                else:
                    note = "\n\n⚠️ Не удалось оформить текст автоматически — показан исходный черновик."
            else:
                polished = polished.strip()
            d["base_final"] = final[:12000]
            d["polished_text"] = polished[:12000]
            d["step"] = "preview_ai"
            _op_contest_draft_save(user_id, d)
            body = (d["polished_text"] or "")[:3600] + note
            send_msg_admin_op_panel(
                user_id, reply_peer,
                _op_contest_step_intro(6, 6, "👀 Предпросмотр перед публикацией", body)[:3900],
                get_op_contest_preview_kb(),
            )
            return True
        if act in ("n", "nd", "nr"):
            _op_contest_prompt_conditions(user_id, reply_peer, d, edit_cmid=ce)
            return True
        if act == "ts":
            d["sub"] = not bool(d.get("sub", True))
        elif act == "td":
            d["don_on"] = not bool(d.get("don_on", False))
        elif act == "tr":
            d["ref_on"] = not bool(d.get("ref_on", False))
        elif act == "dm":
            if d.get("don_on"):
                d["don_n"] = max(1, int(d.get("don_n", 1)) - 1)
        elif act == "dp":
            if d.get("don_on"):
                d["don_n"] = min(500, int(d.get("don_n", 1)) + 1)
        elif act == "rm":
            if d.get("ref_on"):
                d["ref_n"] = max(1, int(d.get("ref_n", 1)) - 1)
        elif act == "rp":
            if d.get("ref_on"):
                d["ref_n"] = min(100000, int(d.get("ref_n", 1)) + 1)
        elif act in ("pf", "bc"):
            send_msg_admin_op_panel(
                user_id, reply_peer,
                "Сначала нажмите «✨ Дальше» — откроется предпросмотр и кнопка публикации.",
                get_op_contest_conditions_kb(d),
            )
            return True
        else:
            print(f"[contest_cb] неизвестное действие step=conditions a={act!r}")
        if not (d.get("sub") or d.get("don_on") or d.get("ref_on")):
            d["sub"] = True
        _op_contest_draft_save(user_id, d)
        _op_contest_prompt_conditions(user_id, reply_peer, d, edit_cmid=ce)
        return True

    if payload_cmd == "admin_op_contest":
        active_row = _get_active_contest_row()
        if active_row:
            send_msg_admin_op_panel(user_id, reply_peer, _format_contest_owner_dashboard_text(active_row), get_op_contest_dashboard_kb())
            return True
        _op_contest_draft_save(user_id, {"step": "text"})
        send_msg_admin_op_panel(
            user_id,
            reply_peer,
            _op_contest_step_intro(
                1,
                6,
                "✏️ Текст объявления",
                "Опишите розыгрыш одним сообщением: о чём пост, сроки, как участвовать.\n\n"
                "«отмена» — выйти из конструктора.",
            ),
            get_op_contest_cancel_kb(),
        )
        return True

    d = draft_snap or _op_contest_draft_load(user_id)
    if not d:
        return False

    step = d.get("step")
    raw_text = (text or "").strip()
    low = raw_text.lower()

    if step == "results_dt" and low == "отмена":
        d["step"] = "conditions"
        d.pop("results_end_label", None)
        d.pop("results_end_ts", None)
        _op_contest_draft_save(user_id, d)
        _op_contest_prompt_conditions(user_id, reply_peer, d)
        return True

    if low == "отмена":
        _op_contest_draft_clear(user_id)
        send_msg_admin_op_panel(user_id, reply_peer, "Конструктор конкурса отменён.", get_op_panel_kb(user_id))
        return True

    if step in ("text", "winners", "prize") and (raw_text.startswith("/") or raw_text.startswith("!")):
        return False

    if step == "text":
        if not raw_text:
            return False
        if payload_cmd:
            return False
        d["body"] = raw_text
        d["step"] = "winners"
        _op_contest_draft_save(user_id, d)
        send_msg_admin_op_panel(
            user_id,
            reply_peer,
            _op_contest_step_intro(
                2,
                6,
                "👥 Число победителей",
                "Отправьте одно целое число от 1 до 9999.\nПример: 3",
            ),
            get_op_contest_cancel_kb(),
        )
        return True

    if step == "winners":
        if not raw_text:
            return False
        if payload_cmd:
            return False
        try:
            w = int(raw_text.split()[0].strip())
        except Exception:
            send_msg_admin_op_panel(
                user_id, reply_peer,
                _op_contest_step_intro(
                    2,
                    6,
                    "👥 Число победителей",
                    "Нужно одно целое число, например: 3",
                ),
                get_op_contest_cancel_kb(),
            )
            return True
        if w < 1 or w > 9999:
            send_msg_admin_op_panel(
                user_id, reply_peer,
                _op_contest_step_intro(
                    2,
                    6,
                    "👥 Число победителей",
                    "Допустимо от 1 до 9999.",
                ),
                get_op_contest_cancel_kb(),
            )
            return True
        d["winners"] = w
        d["step"] = "prize"
        _op_contest_draft_save(user_id, d)
        send_msg_admin_op_panel(
                user_id, reply_peer,
            _op_contest_step_intro(
                3,
                6,
                "💰 Сумма розыгрыша",
                "Укажите общий призовой фонд в привычном формате:\n"
                "500мк, 1.5мм",
            ),
            get_op_contest_cancel_kb(),
        )
        return True

    if step == "prize":
        if not raw_text:
            return False
        if payload_cmd:
            return False
        try:
            prize = int(parse_amount(raw_text))
        except Exception:
            send_msg_admin_op_panel(
                user_id, reply_peer,
                _op_contest_step_intro(
                    3,
                    6,
                    "💰 Сумма розыгрыша",
                    "Не получилось разобрать сумму. Примеры: 5мм, 500мк, 1000000000",
                ),
                get_op_contest_cancel_kb(),
            )
            return True
        if prize <= 0:
            send_msg_admin_op_panel(
                user_id, reply_peer,
                _op_contest_step_intro(
                    3,
                    6,
                    "💰 Сумма розыгрыша",
                    "Сумма должна быть больше нуля.",
                ),
                get_op_contest_cancel_kb(),
            )
            return True
        d["prize"] = prize
        d["step"] = "conditions"
        d["sub"] = True
        d["don_on"] = False
        d["don_n"] = 1
        d["ref_on"] = False
        d["ref_n"] = 1
        _op_contest_draft_save(user_id, d)
        _op_contest_prompt_conditions(user_id, reply_peer, d)
        return True

    if step == "results_dt":
        if not raw_text:
            return False
        if payload_cmd:
            return False
        lab, ts = _parse_contest_results_datetime(raw_text)
        if not lab:
            send_msg(
                reply_peer,
                _op_contest_step_intro(
                    5,
                    6,
                    "📅 Дата и время итогов",
                    "Формат не распознан. Нужна одна строка:\n"
                    "ДД.ММ.ГГГГ ЧЧ:ММ\n"
                    "Пример: 15.04.2026 21:00",
                )[:3900],
                get_op_contest_results_dt_kb(),
            )
            return True
        d["results_end_label"] = lab
        d["results_end_ts"] = ts
        d["step"] = "conditions"
        _op_contest_draft_save(user_id, d)
        _op_contest_prompt_conditions(user_id, reply_peer, d)
        return True

    if step == "preview_ai":
        if raw_text and not payload_cmd:
            send_msg_admin_op_panel(
                user_id, reply_peer,
                "На этом шаге решайте кнопками: «Опубликовать», «К условиям» или «Отмена».",
                get_op_contest_preview_kb(),
            )
        return True

    if step == "conditions":
        if raw_text and not payload_cmd:
            send_msg_admin_op_panel(
                user_id, reply_peer,
                "Этот шаг настраивается кнопками: условия, отдельное сообщение с датой итогов, затем «✨ Дальше» (оформление и предпросмотр).",
                get_op_contest_conditions_kb(d),
            )
        return True

    return False


def get_piska_rank(tops):
    if not tops: tops = 100
    if tops > 500: return 'Рядовой писечник'
    if tops > 200: return 'Неопытный писечник'
    if tops > 100: return 'Опытный писечник'
    if tops > 50: return 'Ветеран писечников'
    if tops > 20: return 'Легендарный писечник'
    if tops > 10: return 'Писечник-перфекционист'
    if tops > 5: return 'Эксклюзивный писечник'
    if tops > 1: return 'Непревзойденный писечник'
    if tops == 1: return 'Король писечников'
    return 'Рядовой писечник'

# --- Профили без внешних JSON ---
def fetch_and_save_json(user_id):
    return None


def get_profile_data(user_id):
    return None


def get_fresh_profile_data(user_id):
    return None


def get_pet_info_from_data(data):
    """(pet_id, pet_name, pet_power). pet_power=0 — питомца нет."""
    if not isinstance(data, dict):
        return 1, "Щенок", 1
    try:
        pet_id = int(data.get('pet_id') or 0)
    except Exception:
        pet_id = 0
    pet_name = (data.get('pet_name') or '').strip()
    if pet_id <= 0 or not pet_name or pet_name.lower() == 'нет питомца':
        return 1, "Щенок", 1
    return pet_id, pet_name, pet_id

def get_roles_from_data(data):
    if not data: return []
    roles = []
    if data.get('admin_dev'): roles.append("👨‍💻 РАЗРАБОТЧИК ПРОЕКТА")
    if data.get('creator'): roles.append("🎨 СОЗДАТЕЛЬ НИЩЕГО")
    if data.get('president'): roles.append("🔞 Президент")
    
    mod_level = data.get('moderator_level', 0)
    if mod_level == 6: roles.append("👹 Ст. Администратор")
    elif mod_level == 5: roles.append("👹 Администратор")
    elif mod_level == 4: roles.append("👺 Ст. Модератор")
    elif mod_level == 3: roles.append("👺 Модератор")
    elif mod_level == 2: roles.append("👺 Мл. Модератор")
    elif mod_level == 1: roles.append("👺 Модератор-стажёр")
    
    now = time.time()
    if data.get('premium_until', 0) > now: roles.append("💎 Premium")
    if data.get('vampire_until', 0) > now: roles.append("🧛‍♂️ Вампир")
    return roles


# --- ГЕНЕРАЦИЯ ГРАФИКА СТАТИСТИКИ (PILLOW) ---
STATS_ATTACHMENT = ""
EVENT_ATTACHMENT = ""
quiz_lock = threading.Lock()
quiz_state = {
    "active": False,
    "number": None,
    "slot_key": None,
    "started_at": 0.0,
    "ends_at": 0.0,
    "guesses_count": 0,
    "guessed_numbers": set(),
}
quiz_pre_announced = set()
quiz_started_slots = set()
QUIZ_LAST_WINNER = {
    "user_id": 0,
    "name": "",
    "finished_at": 0.0,
    "attempts": 0,
}


def _valid_photo_attachment(att):
    if not isinstance(att, str):
        return False
    return bool(re.fullmatch(r'photo-?\d+_\d+(?:_[A-Za-z0-9_]+)?', att.strip()))


def get_event_attachment():
    global EVENT_ATTACHMENT
    if _valid_photo_attachment(EVENT_ATTACHMENT):
        return EVENT_ATTACHMENT
    if not vk_upload or not os.path.isfile(EVENT_IMAGE_PATH):
        return None
    try:
        uploaded = vk_upload.photo_messages(photos=EVENT_IMAGE_PATH)
        if uploaded and isinstance(uploaded[0], dict):
            p = uploaded[0]
            oid = p.get('owner_id')
            pid = p.get('id')
            ak = p.get('access_key')
            if oid is not None and pid is not None:
                cand = f"photo{int(oid)}_{int(pid)}"
                if ak:
                    cand += f"_{ak}"
                if _valid_photo_attachment(cand):
                    EVENT_ATTACHMENT = cand
                    return EVENT_ATTACHMENT
    except Exception:
        pass
    return None


def _event_claimed_status_map(user_id):
    try:
        cursor.execute(
            "SELECT COALESCE(event_day1_claimed, 0), COALESCE(event_day2_claimed, 0), "
            "COALESCE(event_day3_claimed, 0), COALESCE(event_day4_claimed, 0), "
            "COALESCE(event_day5_claimed, 0), COALESCE(event_day6_claimed, 0) "
            "FROM users WHERE user_id = ?",
            (int(user_id),),
        )
        row = cursor.fetchone() or (0, 0, 0, 0, 0, 0)
        return {i + 1: bool(int(row[i] or 0)) for i in range(6)}
    except Exception:
        return {1: False, 2: False, 3: False, 4: False, 5: False, 6: False}


def _is_personal_event_active_now():
    now_msk = _msk_now()
    return PERSONAL_EVENT_START_MSK <= now_msk <= PERSONAL_EVENT_END_MSK


def _personal_event_start_ts_utc():
    msk_tz = timezone(timedelta(hours=3))
    return PERSONAL_EVENT_START_MSK.replace(tzinfo=msk_tz).timestamp()


def _personal_event_end_ts_utc():
    msk_tz = timezone(timedelta(hours=3))
    return PERSONAL_EVENT_END_MSK.replace(tzinfo=msk_tz).timestamp()


def _update_personal_event_playtime(user_id):
    if not _is_personal_event_active_now():
        return
    now_ts = time.time()
    try:
        cursor.execute(
            "SELECT COALESCE(event_last_activity_ts, 0), COALESCE(event_play_seconds, 0) "
            "FROM users WHERE user_id = ?",
            (int(user_id),),
        )
        row = cursor.fetchone() or (0, 0)
        prev_ts = float(row[0] or 0)
        cur_play = int(row[1] or 0)
        add_sec = 0
        if prev_ts > 0:
            add_sec = int(max(0, min(PERSONAL_EVENT_MAX_ACTIVITY_DELTA_SEC, now_ts - prev_ts)))
        cursor.execute(
            "UPDATE users SET event_last_activity_ts = ?, event_play_seconds = ? WHERE user_id = ?",
            (float(now_ts), int(cur_play + add_sec), int(user_id)),
        )
        db.commit()
    except Exception:
        pass


def _event_click_bonus_percent(user_id):
    if not _is_personal_event_active_now():
        return 0
    c = _event_claimed_status_map(user_id)
    bonus = 0
    if c.get(1):
        bonus += 10
    if c.get(2):
        bonus += 8
    return bonus


def _check_personal_event_progress_and_rewards(user_id):
    if not _is_personal_event_active_now():
        return []
    messages = []
    try:
        cursor.execute(
            "SELECT COALESCE(event_success_rob_count, 0), "
            "COALESCE(event_notified_mask, 0), "
            "COALESCE(event_day1_claimed, 0), COALESCE(event_day2_claimed, 0), "
            "COALESCE(event_day3_claimed, 0), COALESCE(event_day4_claimed, 0), "
            "COALESCE(event_day5_claimed, 0), COALESCE(event_day6_claimed, 0), "
            "COALESCE(donated_total, 0) "
            "FROM users WHERE user_id = ?",
            (int(user_id),),
        )
        row = cursor.fetchone() or (0,) * 9
        rob_cnt = int(row[0] or 0)
        notified_mask = int(row[1] or 0)
        claimed = [int(row[2] or 0), int(row[3] or 0), int(row[4] or 0), int(row[5] or 0), int(row[6] or 0), int(row[7] or 0)]
        donated_total = int(row[8] or 0)
        cursor.execute(
            "SELECT COUNT(*) FROM users "
            "WHERE referrer_id = ? AND is_registered = 1 "
            "AND COALESCE(registered_at, 0) >= ? AND COALESCE(registered_at, 0) <= ?",
            (int(user_id), float(_personal_event_start_ts_utc()), float(_personal_event_end_ts_utc())),
        )
        invite_cnt = int((cursor.fetchone() or [0])[0] or 0)

        milestones = [
            (1, donated_total >= PERSONAL_EVENT_DONATE_REQ, "✅ Условие ивента выполнено: пожертвовано 2мм."),
            (2, invite_cnt >= 1, "✅ Условие ивента выполнено: приглашён 1 человек."),
            (3, rob_cnt >= 1, "✅ Условие ивента выполнено: 1 удачное ограбление игрока."),
            (4, invite_cnt >= 2, "✅ Условие ивента выполнено: приглашены 2 человека."),
            (5, invite_cnt >= 3, "✅ Условие ивента выполнено: приглашены 3 человека."),
            (6, rob_cnt >= 2, "✅ Условие ивента выполнено: 2 удачных ограбления игрока."),
        ]
        for bit, ok, msg in milestones:
            if ok and not (notified_mask & (1 << (bit - 1))):
                notified_mask |= (1 << (bit - 1))
                messages.append(msg)

        updates = []
        add_money = 0
        if donated_total >= PERSONAL_EVENT_DONATE_REQ and not claimed[0]:
            claimed[0] = 1
            updates.append("event_day1_claimed = 1")
            messages.append("🎁 Награда 1д получена: +10% к клику до конца ивента.")
        if invite_cnt >= 1 and not claimed[1]:
            claimed[1] = 1
            updates.append("event_day2_claimed = 1")
            messages.append("🎁 Награда 2д получена: +8% к клику до конца ивента.")
        if rob_cnt >= 1 and not claimed[2]:
            claimed[2] = 1
            updates.append("event_day3_claimed = 1")
            add_money += PERSONAL_EVENT_REWARD_DAY3
            messages.append(f"🎁 Награда 3д получена: +{format_click(PERSONAL_EVENT_REWARD_DAY3)}$.")
        if invite_cnt >= 2 and not claimed[3]:
            claimed[3] = 1
            updates.append("event_day4_claimed = 1")
            add_money += PERSONAL_EVENT_REWARD_DAY4
            messages.append(f"🎁 Награда 4д получена: +{format_click(PERSONAL_EVENT_REWARD_DAY4)}$.")
        if invite_cnt >= 3 and not claimed[4]:
            claimed[4] = 1
            updates.append("event_day5_claimed = 1")
            add_money += PERSONAL_EVENT_REWARD_DAY5
            messages.append(f"🎁 Награда 5д получена: +{format_click(PERSONAL_EVENT_REWARD_DAY5)}$.")
        if rob_cnt >= 2 and not claimed[5]:
            claimed[5] = 1
            updates.append("event_day6_claimed = 1")
            add_money += PERSONAL_EVENT_REWARD_DAY6
            messages.append(f"🎁 Награда 6д получена: +{format_click(PERSONAL_EVENT_REWARD_DAY6)}$.")

        set_parts = ["event_notified_mask = ?"]
        params = [int(notified_mask)]
        set_parts.extend(updates)
        if add_money > 0:
            set_parts.append("balance = COALESCE(balance, 0) + ?")
            params.append(int(add_money))
            messages.append(f"💰 Итого начислено: {format_click(add_money)}$.")
        if set_parts:
            params.append(int(user_id))
            cursor.execute(
                "UPDATE users SET " + ", ".join(set_parts) + " WHERE user_id = ?",
                tuple(params),
            )
            db.commit()
    except Exception:
        return []
    return messages

def generate_stats_image():
    global STATS_ATTACHMENT
    try:
        local_db = sqlite3.connect(DB_PATH, timeout=15)
        local_cursor = local_db.cursor()
        
        local_cursor.execute("SELECT COUNT(*) FROM users WHERE is_registered = 1")
        total_users = local_cursor.fetchone()[0] or 0

        # Сохраняем текущее количество юзеров в историю
        current_t = time.time()
        local_cursor.execute("INSERT INTO stats_history (timestamp, users_count) VALUES (?, ?)", (current_t, total_users))
        local_db.commit()

        # Достаем последние 24 записи для графика
        local_cursor.execute("SELECT timestamp, users_count FROM stats_history ORDER BY timestamp DESC LIMIT 24")
        history = local_cursor.fetchall()
        
        # Если бот только запустился, делаем фейковую историю для красоты графика
        if len(history) < 24:
            fake_u = total_users
            history = []
            for i in range(24):
                t = current_t - i * 3600
                history.append((t, max(0, fake_u)))
                fake_u -= random.randint(0, 3)

        history.reverse() # Сортируем от старых к новым
        x_labels = [(datetime.fromtimestamp(h[0], timezone.utc) + timedelta(hours=3)).strftime('%H') for h in history]
        y_values = [h[1] for h in history]

        # Создаем изображение
        width, height = 800, 600
        img = Image.new('RGB', (width, height), color=(0, 0, 0))
        draw = ImageDraw.Draw(img)
        
        font = ImageFont.load_default()
        font_title = ImageFont.load_default()
        try:
            # Пытаемся подгрузить системные шрифты (на Pterodactyl часто есть dejavu)
            font_path = "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"
            if os.path.exists(font_path):
                font = ImageFont.truetype(font_path, 20)
                font_title = ImageFont.truetype(font_path, 30)
            else:
                font = ImageFont.truetype("arial.ttf", 20)
                font_title = ImageFont.truetype("arial.ttf", 30)
        except:
            pass

        # Заголовок графика
        title = "Рост пользователей в Нищий Заработок"
        t_bbox = draw.textbbox((0,0), title, font=font_title)
        draw.text(((width - (t_bbox[2]-t_bbox[0]))/2, 30), title, fill=(255, 255, 255), font=font_title)

        # Рисуем рамку графика (оси)
        pad_l, pad_r, pad_t, pad_b = 100, 50, 100, 120
        gw, gh = width - pad_l - pad_r, height - pad_t - pad_b
        draw.rectangle([pad_l, pad_t, width - pad_r, height - pad_b], outline=(255, 255, 255), width=2)

        # Вычисляем Y-шкалу
        min_y, max_y = min(y_values), max(y_values)
        if max_y == min_y: max_y += 5; min_y = max(0, min_y - 5)
        diff = max_y - min_y
        max_y += diff * 0.1; min_y = max(0, min_y - diff * 0.1)
        diff = max_y - min_y

        # Тики Y (сбоку)
        for i in range(7):
            val = min_y + (diff / 6) * i
            y_p = height - pad_b - (val - min_y) / diff * gh
            label = str(int(val))
            l_b = draw.textbbox((0,0), label, font=font)
            draw.text((pad_l - (l_b[2]-l_b[0]) - 10, y_p - (l_b[3]-l_b[1])/2), label, fill=(255, 255, 255), font=font)
            draw.line([(pad_l, y_p), (pad_l+5, y_p)], fill=(255, 255, 255), width=2)

        # Тики X (снизу) и построение точек графика
        step_x = gw / max(1, len(x_labels) - 1)
        points = []
        for i, (xl, yv) in enumerate(zip(x_labels, y_values)):
            x_p = pad_l + i * step_x
            y_p = height - pad_b - (yv - min_y) / diff * gh
            points.append((x_p, y_p))
            
            # Подпись времени (Х)
            xl_b = draw.textbbox((0,0), xl, font=font)
            draw.text((x_p - (xl_b[2]-xl_b[0])/2, height - pad_b + 15), xl, fill=(255, 255, 255), font=font)
            draw.line([(x_p, height - pad_b), (x_p, height - pad_b - 5)], fill=(255, 255, 255), width=2)

        # Подпись оси X
        x_title = "Время в часах (МСК)"
        xt_b = draw.textbbox((0,0), x_title, font=font)
        draw.text((pad_l + (gw - (xt_b[2]-xt_b[0]))/2, height - pad_b + 50), x_title, fill=(255, 255, 255), font=font)

        # Подпись оси Y (Пользователи)
        txt_img = Image.new('RGBA', (200, 40), (0,0,0,0))
        ImageDraw.Draw(txt_img).text((0, 0), "Пользователи", fill=(255, 255, 255), font=font)
        txt_img = txt_img.rotate(90, expand=1)
        img.paste(txt_img, (10, int(pad_t + (gh - txt_img.height)/2)), txt_img)

        # Рисуем саму желтую линию и точки
        if len(points) > 1:
            draw.line(points, fill=(255, 215, 0), width=3)
        for p in points:
            draw.ellipse([p[0]-4, p[1]-4, p[0]+4, p[1]+4], fill=(255, 215, 0))

        img_path = os.path.join(STATS_DIR, 'stats.jpg')
        img.save(img_path)

        if vk_upload:
            try:
                uploaded = vk_upload.photo_messages(photos=img_path)
                if uploaded and isinstance(uploaded[0], dict):
                    p = uploaded[0]
                    oid = p.get('owner_id')
                    pid = p.get('id')
                    ak = p.get('access_key')
                    if oid is not None and pid is not None:
                        cand = f"photo{int(oid)}_{int(pid)}"
                        if ak:
                            cand += f"_{ak}"
                        if _valid_photo_attachment(cand):
                            STATS_ATTACHMENT = cand
            except Exception:
                pass

        local_db.close()
    except Exception as e:
        print(f"Ошибка генерации статистики: {e}")

# Первичная генерация
generate_stats_image()

def stats_sync_loop():
    while True:
        time.sleep(3600) # Обновление картинки раз в час
        generate_stats_image()

threading.Thread(target=stats_sync_loop, daemon=True).start()


def _msk_now():
    return datetime.utcnow() + timedelta(hours=3)


def _msk_day_key():
    return _msk_now().strftime("%Y-%m-%d")


def _format_unix_msk(unix_ts):
    """Дата/время по московскому времени (UTC+3, без перехода на летнее время)."""
    msk = timezone(timedelta(hours=3))
    return datetime.fromtimestamp(float(unix_ts), tz=msk).strftime("%d.%m.%Y %H:%M МСК")


def _repost_locked_amount(user_id, now_ts=None):
    now_ts = float(now_ts or time.time())
    try:
        cursor.execute(
            "SELECT COALESCE(SUM(amount), 0) FROM repost_reward_locks "
            "WHERE user_id = ? AND deducted = 0 AND unlock_at > ?",
            (int(user_id), float(now_ts)),
        )
        return int((cursor.fetchone() or [0])[0] or 0)
    except Exception:
        return 0


def _is_repost_source_already_claimed(user_id, source_owner_id, source_post_id):
    try:
        cursor.execute(
            "SELECT 1 FROM repost_user_claims WHERE user_id = ? AND source_owner_id = ? AND source_post_id = ?",
            (int(user_id), int(source_owner_id), int(source_post_id)),
        )
        return cursor.fetchone() is not None
    except Exception:
        return False


def _mark_repost_source_claimed(user_id, source_owner_id, source_post_id, now_ts=None):
    try:
        cursor.execute(
            "INSERT OR IGNORE INTO repost_user_claims (user_id, source_owner_id, source_post_id, claimed_at) VALUES (?, ?, ?, ?)",
            (int(user_id), int(source_owner_id), int(source_post_id), float(now_ts or time.time())),
        )
        return True
    except Exception:
        return False


def _get_repost_block_until(user_id, now_ts=None):
    now_ts = float(now_ts or time.time())
    try:
        cursor.execute(
            "SELECT COALESCE(MAX(blocked_until), 0) FROM repost_reward_blocks WHERE user_id = ? AND blocked_until > ?",
            (int(user_id), float(now_ts)),
        )
        return float((cursor.fetchone() or [0])[0] or 0)
    except Exception:
        return 0.0


def _set_repost_block(user_id, issued_by=0, fine_amount=0, reason="", *, hours=None, days=None):
    """Блок выплат за репосты до blocked_until. По умолчанию — сутки, если не заданы hours/days."""
    now_ts = float(time.time())
    if hours is not None:
        delta = max(1, int(hours)) * 3600
    elif days is not None:
        delta = max(1, int(days)) * 86400
    else:
        delta = 24 * 3600
    blocked_until = now_ts + delta
    try:
        cursor.execute(
            "INSERT INTO repost_reward_blocks (user_id, blocked_until, reason, created_by, fine_amount, created_at) VALUES (?, ?, ?, ?, ?, ?)",
            (int(user_id), float(blocked_until), str(reason or ""), int(issued_by or 0), int(fine_amount or 0), now_ts),
        )
        return float(blocked_until)
    except Exception:
        return 0.0


def _repost_warnings_report_text(limit=20):
    """Журнал выговоров по репостам для владельца (/repost33)."""
    try:
        lim = max(1, min(50, int(limit)))
        cursor.execute(
            "SELECT user_id, issued_by, reason, created_at FROM repost_warnings ORDER BY id DESC LIMIT ?",
            (lim,),
        )
        rows = cursor.fetchall() or []
    except Exception:
        return "📋 Не удалось загрузить журнал выговоров."
    if not rows:
        return "📋 Журнал выговоров за репост пуст — записей пока нет."
    lines = [f"📋 Последние выговоры (до {len(rows)} записей):\n"]
    for r in rows:
        uid = int(r[0] or 0)
        cby = int(r[1] or 0)
        reason = str(r[2] or "").strip() or "без причины"
        cat = float(r[3] or 0)
        when = datetime.fromtimestamp(cat, timezone.utc).strftime("%d.%m.%Y %H:%M UTC") if cat > 0 else "—"
        issuer = f"@id{cby}" if cby > 0 else "бот"
        lines.append(
            f"• @id{uid} ({get_user_name(uid)})\n"
            f"  причина: {reason} | когда: {when} | кто выдал: {issuer}"
        )
    return "\n\n".join(lines)


def _issue_repost_warning(user_id, issued_by, reason):
    now_ts = float(time.time())
    try:
        cursor.execute(
            "INSERT INTO repost_warnings (user_id, issued_by, reason, created_at) VALUES (?, ?, ?, ?)",
            (int(user_id), int(issued_by or 0), str(reason or "").strip(), now_ts),
        )
        cursor.execute("SELECT COUNT(*) FROM repost_warnings WHERE user_id = ?", (int(user_id),))
        total_warns = int((cursor.fetchone() or [0])[0] or 0)
        blocked_until = 0.0
        # На каждом 3-м выговоре автоматически блокируем репост-выплаты на сутки.
        if total_warns > 0 and total_warns % 3 == 0:
            blocked_until = _set_repost_block(
                int(user_id),
                issued_by=int(issued_by or 0),
                fine_amount=0,
                reason=f"auto block by warnings ({total_warns})",
                hours=REPOST_WARN_BLOCK_HOURS,
            )
        db.commit()
        return total_warns, float(blocked_until or 0)
    except Exception:
        return 0, 0.0


def _calc_repost_bug_overreward(user_id):
    """Считает сумму бага: все начисления по дубликатам одного и того же исходного поста."""
    try:
        cursor.execute(
            "SELECT id, source_owner_id, source_post_id, started_at "
            "FROM repost_campaigns WHERE user_id = ? "
            "ORDER BY COALESCE(started_at, 0) ASC, id ASC",
            (int(user_id),),
        )
        rows = cursor.fetchall() or []
    except Exception:
        return 0, [], 0
    seen_sources = set()
    duplicate_campaign_ids = []
    duplicate_source_count = 0
    for row in rows:
        campaign_id = int(row[0] or 0)
        src_key = (int(row[1] or 0), int(row[2] or 0))
        if src_key in seen_sources:
            duplicate_campaign_ids.append(campaign_id)
        else:
            seen_sources.add(src_key)
    if not duplicate_campaign_ids:
        return 0, [], 0
    duplicate_source_count = len(duplicate_campaign_ids)
    total_bug_amount = 0
    for campaign_id in duplicate_campaign_ids:
        cursor.execute(
            "SELECT COALESCE(SUM(CASE WHEN deducted = 0 THEN amount ELSE 0 END), 0) "
            "FROM repost_reward_locks WHERE campaign_id = ?",
            (campaign_id,),
        )
        total_bug_amount += int((cursor.fetchone() or [0])[0] or 0)
    return int(total_bug_amount), duplicate_campaign_ids, int(duplicate_source_count)


def _repost_exists_on_page(repost_owner_id, repost_post_id, source_owner_id, source_post_id):
    try:
        raw = vk.wall.getById(posts=f"wall{int(repost_owner_id)}_{int(repost_post_id)}")
        if isinstance(raw, dict):
            rows = raw.get("items") or []
        elif isinstance(raw, list):
            rows = raw
        else:
            rows = []
        if not rows:
            return False
        post = rows[0]
        copy_history = post.get("copy_history") if isinstance(post, dict) else None
        if not isinstance(copy_history, list) or not copy_history:
            return False
        src = copy_history[0] if isinstance(copy_history[0], dict) else {}
        src_owner = int(src.get("owner_id") or 0)
        src_post = int(src.get("id") or 0)
        return src_owner == int(source_owner_id) and src_post == int(source_post_id)
    except Exception:
        return False


def _is_source_post_fresh_24h(source_owner_id, source_post_id):
    """True, если исходному посту не больше 24 часов с публикации."""
    try:
        raw = vk.wall.getById(posts=f"wall{int(source_owner_id)}_{int(source_post_id)}")
        if isinstance(raw, dict):
            rows = raw.get("items") or []
        elif isinstance(raw, list):
            rows = raw
        else:
            rows = []
        if not rows:
            return True
        post = rows[0] if isinstance(rows[0], dict) else {}
        post_date = int(post.get("date") or 0)
        if post_date <= 0:
            return True
        return (time.time() - float(post_date)) <= 24 * 3600
    except Exception:
        # Если API временно не отдал дату поста, не считаем запись "старой".
        return True


def _start_repost_campaign(user_id, repost_owner_id, repost_post_id, source_owner_id, source_post_id):
    now_ts = time.time()
    unlock_at = now_ts + 86400
    try:
        if _get_repost_block_until(user_id, now_ts=now_ts) > float(now_ts):
            return False, "blocked"
        if _is_repost_source_already_claimed(user_id, source_owner_id, source_post_id):
            return False, "duplicate_source"
        cursor.execute("UPDATE repost_campaigns SET active = 0 WHERE user_id = ? AND active = 1", (int(user_id),))
        cursor.execute(
            "INSERT INTO repost_campaigns "
            "(user_id, repost_owner_id, repost_post_id, source_owner_id, source_post_id, started_at, days_granted, days_verified, active) "
            "VALUES (?, ?, ?, ?, ?, ?, 1, 0, 1)",
            (int(user_id), int(repost_owner_id), int(repost_post_id), int(source_owner_id), int(source_post_id), float(now_ts)),
        )
        campaign_id = int(cursor.lastrowid or 0)
        if campaign_id <= 0:
            db.commit()
            return False, "insert_failed"
        cursor.execute("UPDATE users SET balance = balance + ? WHERE user_id = ?", (int(REPOST_DAILY_REWARD), int(user_id)))
        cursor.execute(
            "INSERT OR REPLACE INTO repost_reward_locks (campaign_id, user_id, day_no, amount, unlock_at, deducted) VALUES (?, ?, ?, ?, ?, 0)",
            (campaign_id, int(user_id), 1, int(REPOST_DAILY_REWARD), float(unlock_at)),
        )
        _mark_repost_source_claimed(user_id, source_owner_id, source_post_id, now_ts=now_ts)
        db.commit()
        return True, "ok"
    except Exception:
        return False, "error"


def _repost_daily_checker_loop():
    while True:
        time.sleep(REPOST_CHECK_INTERVAL_SEC)
        try:
            now_ts = time.time()
            has_changes = False
            cursor.execute(
                "SELECT id, user_id, repost_owner_id, repost_post_id, source_owner_id, source_post_id, started_at, "
                "COALESCE(days_granted, 1), COALESCE(days_verified, 0) "
                "FROM repost_campaigns WHERE active = 1"
            )
            campaigns = cursor.fetchall() or []
            for row in campaigns:
                campaign_id = int(row[0] or 0)
                user_id = int(row[1] or 0)
                repost_owner_id = int(row[2] or 0)
                repost_post_id = int(row[3] or 0)
                source_owner_id = int(row[4] or 0)
                source_post_id = int(row[5] or 0)
                started_at = float(row[6] or 0)
                days_granted = int(row[7] or 1)
                days_verified = int(row[8] or 0)
                exists_now = _repost_exists_on_page(repost_owner_id, repost_post_id, source_owner_id, source_post_id)
                if not exists_now:
                    cursor.execute(
                        "SELECT COALESCE(SUM(CASE WHEN deducted = 0 THEN amount ELSE 0 END), 0), "
                        "COALESCE(MAX(day_no), 0) "
                        "FROM repost_reward_locks WHERE campaign_id = ?",
                        (campaign_id,),
                    )
                    agg_row = cursor.fetchone() or (0, 0)
                    total_deduct = int(agg_row[0] or 0)
                    max_day = int(agg_row[1] or 0)
                    if total_deduct > 0:
                        cursor.execute("SELECT COALESCE(balance, 0) FROM users WHERE user_id = ?", (user_id,))
                        bal_row = cursor.fetchone() or (0,)
                        bal_now = int(bal_row[0] or 0)
                        new_bal = max(0, bal_now - total_deduct)
                        cursor.execute("UPDATE users SET balance = ? WHERE user_id = ?", (new_bal, user_id))
                        cursor.execute("UPDATE repost_reward_locks SET deducted = 1 WHERE campaign_id = ? AND deducted = 0", (campaign_id,))
                        has_changes = True
                        send_msg(
                            user_id,
                            f"🔻 Репост удалён или недоступен. Списано {format_click(total_deduct)}$ "
                            f"(кампания {max(1, max_day)}/{REPOST_MAX_DAYS} завершена).",
                            kb_for_peer(user_id),
                        )
                    cursor.execute("UPDATE repost_campaigns SET active = 0 WHERE id = ?", (campaign_id,))
                    has_changes = True
                    continue
                next_day = days_verified + 1
                if next_day > REPOST_MAX_DAYS:
                    cursor.execute("UPDATE repost_campaigns SET active = 0 WHERE id = ?", (campaign_id,))
                    has_changes = True
                    continue
                day_unlock_at = started_at + (next_day * 86400)
                if now_ts < day_unlock_at:
                    continue
                cursor.execute(
                    "SELECT COALESCE(amount, 0), COALESCE(deducted, 0) FROM repost_reward_locks "
                    "WHERE campaign_id = ? AND day_no = ?",
                    (campaign_id, next_day),
                )
                lock_row = cursor.fetchone()
                if not lock_row:
                    cursor.execute("UPDATE repost_campaigns SET active = 0 WHERE id = ?", (campaign_id,))
                    has_changes = True
                    continue
                cursor.execute(
                    "UPDATE repost_campaigns SET days_verified = ? WHERE id = ?",
                    (next_day, campaign_id),
                )
                has_changes = True
                if next_day >= REPOST_MAX_DAYS:
                    cursor.execute("UPDATE repost_campaigns SET active = 0 WHERE id = ?", (campaign_id,))
                    send_msg(
                        user_id,
                        f"✅ Репост проверен {REPOST_MAX_DAYS}/{REPOST_MAX_DAYS}. Кампания завершена.",
                        kb_for_peer(user_id),
                    )
                    continue
                if days_granted < next_day + 1:
                    new_day = next_day + 1
                    new_unlock_at = started_at + (new_day * 86400)
                    cursor.execute("UPDATE users SET balance = balance + ? WHERE user_id = ?", (int(REPOST_DAILY_REWARD), user_id))
                    cursor.execute(
                        "INSERT OR REPLACE INTO repost_reward_locks (campaign_id, user_id, day_no, amount, unlock_at, deducted) VALUES (?, ?, ?, ?, ?, 0)",
                        (campaign_id, user_id, new_day, int(REPOST_DAILY_REWARD), float(new_unlock_at)),
                    )
                    cursor.execute(
                        "UPDATE repost_campaigns SET days_granted = ? WHERE id = ?",
                        (new_day, campaign_id),
                    )
                    send_msg(
                        user_id,
                        f"📌 День {next_day}/{REPOST_MAX_DAYS} подтверждён. Начислено {format_click(REPOST_DAILY_REWARD)}$ за день {new_day}, "
                        f"сумма заблокирована до конца суток кампании.",
                        kb_for_peer(user_id),
                    )
                    has_changes = True
            if has_changes:
                db.commit()
        except Exception:
            pass


def apply_daily_deposit_interest(user_id):
    """Начисляет 0.5% на вклад не чаще 1 раза в сутки (по МСК)."""
    if _deposits_disabled():
        return
    day_key = _msk_day_key()
    try:
        cursor.execute(
            "SELECT COALESCE(bank_balance, 0), COALESCE(last_deposit_interest_day, '') FROM users WHERE user_id = ?",
            (int(user_id),),
        )
        row = cursor.fetchone()
        if not row:
            return
        bank_balance = int(row[0] or 0)
        last_day = str(row[1] or "")
        if bank_balance <= 0 or last_day == day_key:
            return
        gain = int(bank_balance * DEPOSIT_DAILY_RATE)
        if gain > 0:
            cursor.execute(
                "UPDATE users SET bank_balance = bank_balance + ?, last_deposit_interest_day = ? WHERE user_id = ?",
                (int(gain), day_key, int(user_id)),
            )
        else:
            cursor.execute(
                "UPDATE users SET last_deposit_interest_day = ? WHERE user_id = ?",
                (day_key, int(user_id)),
            )
        db.commit()
    except Exception:
        pass


def _event_status_text_for_user(user_id):
    now_ts = time.time()
    with quiz_lock:
        active = bool(quiz_state.get("active"))
        guesses_count = int(quiz_state.get("guesses_count") or 0)
        ends_at = float(quiz_state.get("ends_at") or 0)
        secret_number = quiz_state.get("number")
        slot_key = quiz_state.get("slot_key")
    if active and ends_at > now_ts:
        left_sec = int(max(1, ends_at - now_ts))
        msg = (
            "🎯 Викторина сейчас активна!\n"
            f"Розыгрыш на: {format_click(QUIZ_REWARD)}$\n"
            f"Диапазон: {QUIZ_NUMBER_MIN}–{QUIZ_NUMBER_MAX}\n"
            f"Уникальных названных чисел: {format_balance(guesses_count)}\n"
            f"До конца: {format_time_left_sec(left_sec)}"
        )
    else:
        msg = (
            "🎯 Викторина в официальном чате проходит ежедневно в "
            f"{_quiz_hours_label_msk()} по МСК.\n"
            f"Диапазон чисел: {QUIZ_NUMBER_MIN}–{QUIZ_NUMBER_MAX}.\n"
            f"Приз: {format_click(QUIZ_REWARD)}$.\n"
            f"Длительность ивента: {format_time_left_sec(QUIZ_EVENT_DURATION_SEC)}."
        )
        # Если недавно был победитель, покажем его в статусе (например в течение 5 минут).
        try:
            last_uid = int(QUIZ_LAST_WINNER.get("user_id") or 0)
            last_name = str(QUIZ_LAST_WINNER.get("name") or "").strip()
            last_finished = float(QUIZ_LAST_WINNER.get("finished_at") or 0.0)
            last_attempts = int(QUIZ_LAST_WINNER.get("attempts") or 0)
        except Exception:
            last_uid, last_name, last_finished, last_attempts = 0, "", 0.0, 0
        if last_uid > 0 and last_finished > 0 and (now_ts - last_finished) <= 300:
            tail = (
                "\n\n🏆 Последний победитель:\n"
                f"- {get_user_mention_with_name(last_uid)}\n"
                f"- Угадал число и получил {format_click(QUIZ_REWARD)}$\n"
                f"- Уникальных названных чисел в раунде: {format_balance(last_attempts)}"
            )
            msg += tail
    if _is_owner(user_id):
        owner_tail = (
            "\n\n🔐 Режим владельца\n"
            f"active={active}\n"
            f"slot={slot_key or '-'}\n"
            f"secret={secret_number if secret_number is not None else '-'}\n"
            f"ends_at={int(ends_at) if ends_at else 0}\n"
            f"guesses={guesses_count}"
        )
        msg += owner_tail
    return msg


def _quiz_slot_key(dt_obj, hour):
    return f"{dt_obj.strftime('%Y-%m-%d')}:{int(hour):02d}"


def _time_to_next_quiz_text():
    now_msk = _msk_now()
    starts = []
    for day_shift in (0, 1):
        d = now_msk + timedelta(days=day_shift)
        for hour in QUIZ_START_HOURS_MSK:
            starts.append(datetime(d.year, d.month, d.day, int(hour), 0, 0))
    starts = [dt for dt in starts if dt > now_msk]
    if not starts:
        return "0ч 0мин"
    next_dt = min(starts)
    delta_sec = int((next_dt - now_msk).total_seconds())
    h = max(0, delta_sec // 3600)
    m = max(0, (delta_sec % 3600) // 60)
    return f"{h}ч {m}мин"


def _time_to_personal_event_start_text():
    now_msk = _msk_now()
    if now_msk >= PERSONAL_EVENT_START_MSK:
        return "0ч 0мин"
    delta_sec = int((PERSONAL_EVENT_START_MSK - now_msk).total_seconds())
    h = max(0, delta_sec // 3600)
    m = max(0, (delta_sec % 3600) // 60)
    return f"{h}ч {m}мин"


def _quiz_scheduler_loop():
    global quiz_pre_announced, quiz_started_slots
    while True:
        try:
            now_msk = _msk_now()
            timeout_guesses = None
            with quiz_lock:
                if quiz_state.get("active") and float(quiz_state.get("ends_at") or 0) > 0 and time.time() >= float(quiz_state.get("ends_at") or 0):
                    timeout_guesses = int(quiz_state.get("guesses_count") or 0)
                    quiz_state["active"] = False
                    quiz_state["number"] = None
                    quiz_state["slot_key"] = None
                    quiz_state["started_at"] = 0.0
                    quiz_state["ends_at"] = 0.0
                    quiz_state["guesses_count"] = 0
                    quiz_state["guessed_numbers"] = set()
            if timeout_guesses is not None:
                send_msg(
                    QUIZ_CHAT_PEER_ID,
                    "⏳ Ивент завершён по времени (2 часа).\n"
                    f"Уникальных названных чисел: {format_balance(timeout_guesses)}.\n"
                    "Победителя в этом раунде нет.",
                    kb_for_peer(QUIZ_CHAT_PEER_ID),
                )

            today_prefix = now_msk.strftime("%Y-%m-%d")
            # Не раздуваем память множествами старых ключей.
            quiz_pre_announced = {k for k in quiz_pre_announced if k.startswith(today_prefix)}
            quiz_started_slots = {k for k in quiz_started_slots if k.startswith(today_prefix)}

            for hour in QUIZ_START_HOURS_MSK:
                start_dt = datetime(now_msk.year, now_msk.month, now_msk.day, int(hour), 0, 0)
                pre_dt = start_dt - timedelta(minutes=QUIZ_PRESTART_MINUTES)
                key = _quiz_slot_key(now_msk, hour)
                if pre_dt <= now_msk < start_dt and key not in quiz_pre_announced:
                    quiz_pre_announced.add(key)
                    send_msg(
                        QUIZ_CHAT_PEER_ID,
                        "@all Через 3 минуты начнётся викторина: "
                        f"я загадаю число от {QUIZ_NUMBER_MIN} до {QUIZ_NUMBER_MAX}. Приз — {format_click(QUIZ_REWARD)}$.",
                        kb_for_peer(QUIZ_CHAT_PEER_ID),
                    )
                if start_dt <= now_msk < (start_dt + timedelta(minutes=1)) and key not in quiz_started_slots:
                    quiz_started_slots.add(key)
                    with quiz_lock:
                        quiz_state["active"] = True
                        quiz_state["number"] = random.randint(QUIZ_NUMBER_MIN, QUIZ_NUMBER_MAX)
                        quiz_state["slot_key"] = key
                        quiz_state["started_at"] = time.time()
                        quiz_state["ends_at"] = time.time() + QUIZ_EVENT_DURATION_SEC
                        quiz_state["guesses_count"] = 0
                        quiz_state["guessed_numbers"] = set()
                    send_msg(
                        QUIZ_CHAT_PEER_ID,
                        f"@all Я загадал число от {QUIZ_NUMBER_MIN} до {QUIZ_NUMBER_MAX}, "
                        f"кто отгадает — получит {format_click(QUIZ_REWARD)}$.\n"
                        "Пишите число в чат. Время ивента: 2 часа.",
                        kb_for_peer(QUIZ_CHAT_PEER_ID),
                    )
        except Exception:
            pass
        time.sleep(20)


def try_resolve_quiz_guess(user_id, reply_peer, text, is_registered):
    if int(reply_peer) != QUIZ_CHAT_PEER_ID or not is_registered:
        return False
    s = _strip_club_prefix_raw(text).strip()
    if not re.fullmatch(r"\d{1,3}", s):
        return False
    guess = int(s)
    if guess < QUIZ_NUMBER_MIN or guess > QUIZ_NUMBER_MAX:
        return False
    attempts_used = None
    with quiz_lock:
        if not quiz_state.get("active"):
            return False
        ends_at = float(quiz_state.get("ends_at") or 0)
        if ends_at > 0 and time.time() >= ends_at:
            quiz_state["active"] = False
            quiz_state["number"] = None
            quiz_state["slot_key"] = None
            quiz_state["started_at"] = 0.0
            quiz_state["ends_at"] = 0.0
            quiz_state["guesses_count"] = 0
            quiz_state["guessed_numbers"] = set()
            return False
        guessed_numbers = quiz_state.setdefault("guessed_numbers", set())
        if guess in guessed_numbers:
            return False
        guessed_numbers.add(guess)
        quiz_state["guesses_count"] = len(guessed_numbers)
        if guess != int(quiz_state.get("number") or -1):
            return False
        attempts_used = int(quiz_state.get("guesses_count") or 0)
        quiz_state["active"] = False
        quiz_state["number"] = None
        quiz_state["slot_key"] = None
        quiz_state["started_at"] = 0.0
        quiz_state["ends_at"] = 0.0
        quiz_state["guesses_count"] = 0
        quiz_state["guessed_numbers"] = set()

    urow, _ = get_user(user_id)
    new_bal = int(urow[1]) + QUIZ_REWARD
    update_user(user_id, 'balance', new_bal)
    winner_name = get_user_name(user_id)
    # Запомним победителя для статуса ивента в ближайшие 5 минут.
    try:
        QUIZ_LAST_WINNER["user_id"] = int(user_id)
        QUIZ_LAST_WINNER["name"] = str(winner_name or "")
        QUIZ_LAST_WINNER["finished_at"] = float(time.time())
        QUIZ_LAST_WINNER["attempts"] = int(attempts_used or 0)
    except Exception:
        pass
    send_msg(
        reply_peer,
        f"🎉 @id{user_id}({winner_name}) угадал число и получил {format_click(QUIZ_REWARD)}$!\n"
        f"Уникальных названных чисел в раунде: {format_balance(int(attempts_used or 0))}\n"
        f"Новый баланс: {format_click(new_bal)}$",
        kb_for_peer(reply_peer),
    )
    return True


# --- ФОНОВЫЕ ПРОЦЕССЫ ПАРСИНГА ---
def json_sync_loop():
    while True:
        time.sleep(300)

def energy_regen_loop():
    while True:
        try:
            time.sleep(6)
            local_db = sqlite3.connect(DB_PATH, timeout=15)
            local_cursor = local_db.cursor()
            local_cursor.execute("SELECT user_id, energy, fed FROM users WHERE fed >= 2 AND energy < 50")
            users_to_update = local_cursor.fetchall()
            for uid, energy, fed in users_to_update:
                new_energy = min(50, energy + 1)
                new_fed = max(0, fed - 2)
                local_cursor.execute("UPDATE users SET energy = ?, fed = ? WHERE user_id = ?", (new_energy, new_fed, uid))
            local_db.commit()
            local_db.close()
        except Exception:
            pass

def shop_upgrade_expiry_notify_loop():
    """Уведомления в ЛС, когда закончилось одно из улучшений магазина (раз в ~90 с)."""
    while True:
        try:
            time.sleep(90)
            now = time.time()
            local_db = sqlite3.connect(DB_PATH, timeout=15)
            lc = local_db.cursor()
            lc.execute(
                "SELECT user_id, COALESCE(click_boost_until,0), COALESCE(steal_fast_until,0), COALESCE(steal_shield_until,0), "
                "COALESCE(shop_click_boost_expire_notified,0), COALESCE(shop_steal_fast_expire_notified,0), COALESCE(shop_steal_shield_expire_notified,0) "
                "FROM users WHERE "
                "(COALESCE(click_boost_until,0) > 0 AND COALESCE(click_boost_until,0) < ?) OR "
                "(COALESCE(steal_fast_until,0) > 0 AND COALESCE(steal_fast_until,0) < ?) OR "
                "(COALESCE(steal_shield_until,0) > 0 AND COALESCE(steal_shield_until,0) < ?)",
                (now, now, now),
            )
            for row in lc.fetchall():
                uid = int(row[0])
                cb, sf, sh = float(row[1] or 0), float(row[2] or 0), float(row[3] or 0)
                nb, ns, nh = int(row[4] or 0), int(row[5] or 0), int(row[6] or 0)
                if cb > 0 and cb < now and nb == 0:
                    try:
                        send_msg(
                            uid,
                            "⏳ Усилитель клика закончился. При необходимости снова купите его в магазине.",
                            kb_for_peer(uid),
                        )
                    except Exception:
                        pass
                    lc.execute(
                        "UPDATE users SET shop_click_boost_expire_notified = 1 WHERE user_id = ?",
                        (uid,),
                    )
                if sf > 0 and sf < now and ns == 0:
                    try:
                        send_msg(
                            uid,
                            "⏳ Ускорение атаки питомцем закончилось. Его можно снова купить в магазине.",
                            kb_for_peer(uid),
                        )
                    except Exception:
                        pass
                    lc.execute(
                        "UPDATE users SET shop_steal_fast_expire_notified = 1 WHERE user_id = ?",
                        (uid,),
                    )
                if sh > 0 and sh < now and nh == 0:
                    try:
                        send_msg(
                            uid,
                            "⏳ Щит от атак питомцем закончился. Его можно снова купить в магазине.",
                            kb_for_peer(uid),
                        )
                    except Exception:
                        pass
                    lc.execute(
                        "UPDATE users SET shop_steal_shield_expire_notified = 1 WHERE user_id = ?",
                        (uid,),
                    )
            local_db.commit()
            local_db.close()
        except Exception:
            pass


threading.Thread(target=energy_regen_loop, daemon=True).start()
threading.Thread(target=shop_upgrade_expiry_notify_loop, daemon=True).start()
threading.Thread(target=_quiz_scheduler_loop, daemon=True).start()
threading.Thread(target=_repost_daily_checker_loop, daemon=True).start()


# --- КЛАВИАТУРЫ ---
def get_parent_check_kb():
    kb = VkKeyboard(inline=True)
    kb.add_openlink_button('Зарегистрироваться', link='https://vk.ru/write-221392393?ref=682039325')
    kb.add_line()
    kb.add_button('Проверить', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'check_parent'})
    return kb

def get_register_kb():
    kb = VkKeyboard(inline=True)
    kb.add_button('Согласен', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'agree'})
    return kb

def get_subscribe_kb(user_id=None, include_sponsor_link=False):
    """Клавиатура подписки. Ссылка на сообщество проверки — только при include_sponsor_link (например вывод)."""
    kb = VkKeyboard(inline=True)
    kb.add_openlink_button('Подписаться на группу', link=f'https://vk.com/club{GROUP_ID}')
    show_verif = False
    if include_sponsor_link and VERIFICATION_COOPERATION_ENABLED and VERIFICATION_GROUP_SCREEN and VERIFICATION_GROUP_URL:
        if user_id is None:
            show_verif = True
        else:
            vm = _vk_check_verification_group_member(int(user_id))
            show_verif = vm is not True
    if show_verif:
        kb.add_line()
        kb.add_openlink_button('Сообщество для проверки', link=VERIFICATION_GROUP_URL)
    kb.add_line()
    _sub_pl = {'cmd': 'check_sub'}
    if include_sponsor_link:
        _sub_pl['w'] = 1
    kb.add_button('Я подписался', color=VkKeyboardColor.POSITIVE, payload=_sub_pl)
    return kb


def _vk_parse_groups_is_member_response(resp):
    """
    Разбор ответа groups.isMember: скаляр 0/1 или extended [{\"member\": 0|1, \"user_id\": ...}, ...].
    Нельзя делать bool(r[0]) для dict — непустой объект всегда True даже при member=0.
    """
    if resp is None:
        return False
    if isinstance(resp, bool):
        return resp
    if isinstance(resp, int):
        return int(resp) == 1
    if isinstance(resp, dict):
        mv = resp.get("member")
        if mv is not None:
            try:
                return int(mv) == 1
            except (TypeError, ValueError):
                pass
        return False
    if isinstance(resp, list):
        if not resp:
            return False
        el = resp[0]
        if isinstance(el, dict):
            try:
                return int(el.get("member", 0) or 0) == 1
            except (TypeError, ValueError):
                return False
        try:
            return int(el) == 1
        except (TypeError, ValueError):
            return bool(el)
    try:
        return int(resp) == 1
    except (TypeError, ValueError):
        return False


def _vk_groups_is_member_bool(api, group_id, user_id):
    """Один вызов groups.isMember → bool. Предпочитаем user_id (скалярный ответ)."""
    uid = int(user_id)
    r = api.groups.isMember(group_id=group_id, user_id=uid)
    return _vk_parse_groups_is_member_response(r)


def _vk_iter_apis_for_membership_checks():
    """Порядок: отдельный community_check, user, токен группы (своя группа и чужая — по возможности)."""
    seen = set()
    for api in (vk_community, vk_user, vk):
        if api is None:
            continue
        oid = id(api)
        if oid in seen:
            continue
        seen.add(oid)
        yield api


def _vk_check_verification_group_member(target_uid):
    """Проверка вступления в дополнительное сообщество (screen name). None — API недоступен."""
    if not VERIFICATION_GROUP_SCREEN:
        return True
    uid = int(target_uid)
    last_err = None
    for api in _vk_iter_apis_for_membership_checks():
        try:
            return _vk_groups_is_member_bool(api, VERIFICATION_GROUP_SCREEN, uid)
        except Exception as e:
            last_err = e
            continue
    try:
        print(f"[verif_group_member] uid={uid}: {last_err!r}")
    except Exception:
        pass
    return None


def _vk_bot_group_subscription_ok(target_uid):
    """Только основная группа бота (сообщество для проверки не учитывается)."""
    uid = int(target_uid)
    m = _vk_check_group_member(uid)
    if m is None:
        try:
            r = vk.groups.isMember(group_id=GROUP_ID, user_id=uid)
            m = _vk_parse_groups_is_member_response(r)
        except Exception:
            m = False
    else:
        m = bool(m)
    return bool(m)


def _vk_subscription_fully_ok(target_uid):
    """Состоит в основной группе бота и (если задано) в сообществе проверки."""
    uid = int(target_uid)
    if not _vk_bot_group_subscription_ok(uid):
        return False
    if not VERIFICATION_GROUP_SCREEN or not VERIFICATION_COOPERATION_ENABLED:
        return True
    v = _vk_check_verification_group_member(uid)
    if v is None:
        try:
            r = vk.groups.isMember(group_id=VERIFICATION_GROUP_SCREEN, user_id=uid)
            v = _vk_parse_groups_is_member_response(r)
        except Exception:
            v = False
    return bool(v)


def _vk_check_group_member(target_uid):
    """Проверка вступления в группу бота. None — все токены не смогли ответить."""
    uid = int(target_uid)
    last_err = None
    for api in _vk_iter_apis_for_membership_checks():
        try:
            return _vk_groups_is_member_bool(api, GROUP_ID, uid)
        except Exception as e:
            last_err = e
            continue
    try:
        print(f"[group_member] uid={uid}: {last_err!r}")
    except Exception:
        pass
    return None


def _sync_user_group_subscription(user_id, force=False, notify_admin_on_sub=False):
    """Кеш подписки в users. Уведомление COMMUNITY_STATS_ADMIN_ID — только если notify_admin_on_sub
    (сейчас: подписка в контексте вывода, кнопка «Я подписался» с пометкой вывода)."""
    uid = int(user_id)
    now = time.time()
    cursor.execute(
        "SELECT COALESCE(group_sub_last, -1), COALESCE(group_sub_ever, 0), COALESCE(group_sub_checked_at, 0) FROM users WHERE user_id = ?",
        (uid,),
    )
    row = cursor.fetchone()
    last = int(row[0]) if row else -1
    ever = int(row[1]) if row else 0
    checked_at = float(row[2] if row else 0)
    if not force and checked_at > 0 and (now - checked_at) < GROUP_SUB_CHECK_INTERVAL_SEC:
        return last == 1, None
    is_m = _vk_bot_group_subscription_ok(uid)
    new_last = 1 if is_m else 0
    new_ever = 1 if (ever == 1 or is_m) else 0
    event = None
    if last in (-1, 0) and is_m:
        event = "sub"
    elif last == 1 and not is_m:
        event = "unsub"
    try:
        cursor.execute(
            "UPDATE users SET group_sub_last = ?, group_sub_ever = ?, group_sub_checked_at = ? WHERE user_id = ?",
            (new_last, new_ever, now, uid),
        )
        db.commit()
    except Exception:
        pass
    if (
        event == "sub"
        and notify_admin_on_sub
        and COMMUNITY_STATS_ADMIN_ID
        and int(uid) != int(COMMUNITY_STATS_ADMIN_ID)
    ):
        try:
            send_msg(
                int(COMMUNITY_STATS_ADMIN_ID),
                "🔔 Подписка (контекст вывода), игрок в группе:\n"
                f"{get_user_mention_with_name(uid)}\n"
                f"id{uid}",
                None,
                disable_mentions=True,
            )
        except Exception:
            try:
                send_msg(
                    int(COMMUNITY_STATS_ADMIN_ID),
                    f"🔔 Подписка (вывод): id{uid}",
                    None,
                )
            except Exception:
                pass
    return is_m, event


def _community_subscription_stats_text():
    try:
        cursor.execute(
            """
            SELECT
              COALESCE(SUM(CASE WHEN COALESCE(is_registered,0)=1 AND COALESCE(group_sub_last,-1)=1 THEN 1 ELSE 0 END), 0),
              COALESCE(SUM(CASE WHEN COALESCE(is_registered,0)=1 AND COALESCE(group_sub_ever,0)=1 THEN 1 ELSE 0 END), 0),
              COALESCE(SUM(CASE WHEN COALESCE(is_registered,0)=1 AND COALESCE(group_sub_ever,0)=1 AND COALESCE(group_sub_last,-1)!=1 THEN 1 ELSE 0 END), 0)
            FROM users
            """
        )
        t = cursor.fetchone() or (0, 0, 0)
        cur, ev, un = int(t[0] or 0), int(t[1] or 0), int(t[2] or 0)
    except Exception:
        cur, ev, un = 0, 0, 0
    return (
        "📊 Подписка на сообщество (зарегистрированные в боте)\n\n"
        f"✅ Сейчас подписаны: {cur}\n"
        f"📌 Когда-либо подписывались: {ev}\n"
        f"📤 Отписались (были в группе, сейчас нет): {un}\n\n"
        "Счётчики обновляются при проверках API (раз в несколько минут на игрока или по кнопке «Я подписался»)."
    )[:3900]


_MAIN_KB_CACHE = {}
_MAIN_KB_CONTEST_CACHE = {"is_active": False, "ts": 0.0}
_MAIN_KB_CONTEST_CACHE_TTL_SEC = 20.0


def _main_menu_contest_active_cached():
    now = time.time()
    if (now - float(_MAIN_KB_CONTEST_CACHE.get("ts") or 0.0)) <= _MAIN_KB_CONTEST_CACHE_TTL_SEC:
        return bool(_MAIN_KB_CONTEST_CACHE.get("is_active"))
    is_active = bool(_get_active_contest_row())
    _MAIN_KB_CONTEST_CACHE["is_active"] = is_active
    _MAIN_KB_CONTEST_CACHE["ts"] = now
    return is_active


def get_main_kb():
    try:
        _muid = globals().get("_menu_keyboard_user_id")
        _muid = int(_muid) if _muid is not None else None
    except (TypeError, ValueError):
        _muid = None
    has_sub_stats_btn = bool(
        COMMUNITY_STATS_ADMIN_ID
        and _muid is not None
        and int(_muid) == int(COMMUNITY_STATS_ADMIN_ID)
    )
    has_contest_btn = _main_menu_contest_active_cached()
    show_work = bool(_runtime_ui_show_work())
    cache_key = (int(has_contest_btn), int(has_sub_stats_btn), int(show_work))
    cached = _MAIN_KB_CACHE.get(cache_key)
    if cached is not None:
        return cached

    kb = VkKeyboard(one_time=False)
    kb.add_button('Кликать', color=VkKeyboardColor.POSITIVE)
    kb.add_button('Профиль', color=VkKeyboardColor.SECONDARY)
    kb.add_line()
    kb.add_button('Топ', color=VkKeyboardColor.SECONDARY)
    kb.add_button('Рефка', color=VkKeyboardColor.SECONDARY)
    kb.add_button('Магазин', color=VkKeyboardColor.SECONDARY)
    kb.add_line()
    if show_work:
        kb.add_button('Работа', color=VkKeyboardColor.PRIMARY, payload={'cmd': 'ozon_work_start'})
    kb.add_button('Пожертвования', color=VkKeyboardColor.SECONDARY)
    kb.add_line()
    kb.add_button('О боте', color=VkKeyboardColor.SECONDARY)
    kb.add_button('Помощь', color=VkKeyboardColor.SECONDARY)
    if has_contest_btn:
        kb.add_line()
        kb.add_button('🎁 Конкурс', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'contest_public'})
    if has_sub_stats_btn:
        kb.add_line()
        kb.add_button('📊 Подписки', color=VkKeyboardColor.PRIMARY, payload={'cmd': 'community_sub_stats'})
    _MAIN_KB_CACHE[cache_key] = kb
    return kb


def get_ozon_work_kb():
    kb = VkKeyboard(inline=True)
    kb.add_callback_button("⬅️", color=VkKeyboardColor.PRIMARY, payload={"cmd": "ozon_work_pick", "pos": 1})
    kb.add_callback_button("⬆️", color=VkKeyboardColor.POSITIVE, payload={"cmd": "ozon_work_pick", "pos": 2})
    kb.add_callback_button("➡️", color=VkKeyboardColor.PRIMARY, payload={"cmd": "ozon_work_pick", "pos": 3})
    return kb


def get_event_carousel():
    """Карусель личного ивента по дням (отключена)."""
    return None


def get_top_choice_kb(owner_user_id=None):
    owner_payload = {"owner_id": int(owner_user_id)} if owner_user_id is not None else {}
    o = owner_payload
    kb = VkKeyboard(inline=True)
    kb.add_button('🏆 Рефералы', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'top_refs', **o})
    kb.add_button('💵 Баланс', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'top_balance', **o})
    kb.add_line()
    kb.add_button('📨 Чаты', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'top_spam', **o})
    kb.add_button('💖 Пожертв.', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'top_donations', **o})
    kb.add_line()
    kb.add_button('💸 Выводы', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'top_withdrawals', **o})
    return kb


def get_shop_kb():
    kb = VkKeyboard(inline=True)
    _bd = get_economy_click_boost_days()
    kb.add_button(
        f'Клик +{format_short(get_economy_click_boost_bonus())} ({_bd}д) — {format_short(get_economy_click_boost_price())}$',
        color=VkKeyboardColor.POSITIVE,
        payload={'cmd': 'shop_buy_click_boost'},
    )
    kb.add_line()
    kb.add_button(
        f'Атака 2ч (1д) — {format_short(STEAL_FAST_PRICE_PER_DAY)}$',
        color=VkKeyboardColor.PRIMARY,
        payload={'cmd': 'shop_buy_steal_fast'},
    )
    kb.add_line()
    kb.add_button(
        f'Щит 6ч — {format_short(STEAL_SHIELD_PRICE)}$',
        color=VkKeyboardColor.NEGATIVE,
        payload={'cmd': 'shop_buy_steal_shield'},
    )
    return kb

def get_profile_kb():
    kb = VkKeyboard(inline=True)
    kb.add_button('Вывести', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'withdraw'})
    return kb


def _donation_menu_contest_hint():
    return "\n\n💡 Жертвуя валюту, вы увеличиваете шанс проведения конкурсов в сообществе."


def get_donation_kb():
    """Inline callback-клавиатура: кнопки под сообщением, нижнее меню не подменяется."""
    kb = VkKeyboard(inline=True)
    kb.add_callback_button("Пожертвовать 15%", color=VkKeyboardColor.POSITIVE, payload={"cmd": "donate_pick_15"})
    kb.add_line()
    kb.add_callback_button("Пожертвовать 30%", color=VkKeyboardColor.POSITIVE, payload={"cmd": "donate_pick_30"})
    kb.add_line()
    kb.add_callback_button("Своя сумма", color=VkKeyboardColor.SECONDARY, payload={"cmd": "donate_pick_custom"})
    kb.add_line()
    kb.add_callback_button("Отмена", color=VkKeyboardColor.NEGATIVE, payload={"cmd": "donation_menu_close"})
    return kb


def get_donation_confirm_kb(amount):
    kb = VkKeyboard(inline=True)
    kb.add_callback_button("Подтвердить", color=VkKeyboardColor.POSITIVE, payload={"cmd": "donate_confirm", "amt": int(amount)})
    kb.add_line()
    kb.add_callback_button("Отмена", color=VkKeyboardColor.NEGATIVE, payload={"cmd": "donate_cancel"})
    return kb


def _process_message_from_donation_callback(user_id, peer_id, payload_dict, conversation_message_id=0):
    """Inline callback (MESSAGE_EVENT): пожертвования, пасха «Принять» и т.п. — прокидываем в process_message."""
    class _Ev:
        pass

    ev = _Ev()
    ev.obj = type("_O", (), {})()
    ev.obj.message = {
        "from_id": int(user_id),
        "peer_id": int(peer_id),
        "text": "",
        "payload": json.dumps(payload_dict),
        "conversation_message_id": int(conversation_message_id or 0),
        "_from_callback": True,
    }
    process_message(ev)


def get_transfer_confirm_kb(target_id, amount, owner_user_id=None):
    kb = VkKeyboard(inline=True)
    base = {"uid": int(target_id), "amt": int(amount)}
    if owner_user_id is not None:
        base["owner_id"] = int(owner_user_id)
    kb.add_callback_button("Подтвердить", color=VkKeyboardColor.POSITIVE, payload={"cmd": "transfer_confirm", **base})
    kb.add_line()
    kb.add_callback_button("Отмена", color=VkKeyboardColor.NEGATIVE, payload={"cmd": "transfer_cancel", **base})
    return kb


def get_antibot_captcha_kb(target_id):
    kb = VkKeyboard(inline=True)
    kb.add_callback_button("Отправить капчу (пример)", color=VkKeyboardColor.NEGATIVE, payload={"cmd": "anti_bot_send_captcha", "uid": int(target_id)})
    return kb


def get_user_vk_at_mention(user_id):
    try:
        u = vk.users.get(user_ids=user_id, fields='domain')[0]
        d = (u.get('domain') or '').strip()
        if d and not str(d).lower().startswith('id'):
            return f'@{d}'
    except Exception:
        pass
    return f'@id{user_id}'


def get_user_mention_with_name(user_id):
    uid = int(user_id)
    return f"@id{uid} ({get_user_name(uid)})"


def _casino_win_probability(bet, cash_balance=None):
    """Шанс выигрыша на «нейтральном» броске (без учёта чередования). На 5мм — CASINO_WIN_P_MAX_STAKE."""
    b = max(CASINO_MIN_BET, min(int(bet), CASINO_MAX_BET))
    lo, hi = float(CASINO_MIN_BET), float(CASINO_MAX_BET)
    span = max(1.0, hi - lo)
    t = (float(b) - lo) / span
    p = float(CASINO_WIN_P_MIN_STAKE) + (float(CASINO_WIN_P_MAX_STAKE) - float(CASINO_WIN_P_MIN_STAKE)) * t
    if cash_balance is not None and int(cash_balance) > int(CASINO_RICH_BALANCE_THRESHOLD):
        p = max(float(CASINO_RICH_WIN_P_FLOOR), p * float(CASINO_RICH_WIN_P_MULT))
    return p


def _casino_token_means_all_balance(token):
    """вб / все / всё / all — ставка всеми наличными (не больше лимита казино)."""
    t = (token or '').strip().casefold().replace('ё', 'е')
    return t in ('вб', 'все', 'всё', 'all')


def _casino_help_text():
    return (
        '🎰 Казино\n\n'
        'Напишите в чат или в личку боту:\n'
        'казик [ставка]\n\n'
        'Есть поддержка мк, мм, вб и тп.\n'
        'Между играми пауза 1 минута.\n'
    )


# последний исход слота по юзеру (для 40/60 после выигрыша)
_casino_last_outcome = {}


def _casino_slot_box(r1, r2, r3):
    return (
        '┏━━━━━━━━━━━┓\n'
        f'┃  {r1}  |  {r2}  |  {r3}    ┃\n'
        '┗━━━━━━━━━━━┛'
    )


def _casino_spin_round(user_id, bet, cash_balance=None):
    """Исход раунда: (net_delta, reels, headline). После выигрыша — 40% удачи / 60% неудачи на следующий спин; иначе — шанс p."""
    bet = int(bet)
    uid = int(user_id)
    p = _casino_win_probability(bet, cash_balance)
    prev = _casino_last_outcome.get(uid)
    if prev == 'win':
        want_win = random.random() < float(CASINO_AFTER_WIN_NEXT_WIN_P)
    else:
        want_win = random.random() < p

    mention = get_user_mention_with_name(uid)

    if want_win:
        payout_mult = random.uniform(1.18, 4.2)
        winnings = int(round(bet * payout_mult))
        net = winnings - bet
        # иногда «занос» без трёх одинаковых в ряд — как кривой слот
        if random.random() < 0.42:
            a, b = random.sample(CASINO_SYMBOLS, 2)
            reels = random.choice(((a, a, b), (a, b, a), (b, a, a), (a, b, b), (b, a, b)))
        else:
            sym = random.choice(CASINO_SYMBOLS)
            reels = (sym, sym, sym)
        head = f'{mention}, 🎉 занесло (×{payout_mult:.2f})'
        _casino_last_outcome[uid] = 'win'
        return net, reels, head

    for _ in range(40):
        reels = tuple(random.choice(CASINO_SYMBOLS) for _ in range(3))
        if len(set(reels)) > 1:
            break
    else:
        reels = (CASINO_SYMBOLS[0], CASINO_SYMBOLS[1], CASINO_SYMBOLS[0])
    payout_mult = random.uniform(0.05, 0.95)
    winnings = int(round(bet * payout_mult))
    net = winnings - bet
    loss_pct = int(round((1.0 - payout_mult) * 100))
    head = f'{mention}, 🙄 минус {loss_pct}% к ставке (×{payout_mult:.2f})'
    _casino_last_outcome[uid] = 'loss'
    return net, reels, head


def _casino_is_command(text):
    raw = _strip_club_prefix_raw(text).strip()
    if not raw:
        return False
    return raw.split(None, 1)[0].lower() == 'казик'


def _casino_enabled():
    try:
        cursor.execute("SELECT value FROM bot_economy WHERE key = ?", (CASINO_ENABLED_KEY,))
        row = cursor.fetchone()
        if row is None:
            return True
        return int(row[0] or 0) != 0
    except Exception:
        return True


def _set_casino_enabled(on):
    cursor.execute(
        "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
        (CASINO_ENABLED_KEY, 1 if on else 0),
    )
    db.commit()


# --- Runtime UI (bot_economy), fallback CONFIG_* from config.json ---
RUNTIME_KEY_UI_WORK = "ui_show_work"
RUNTIME_KEY_UI_CASINO = "ui_show_casino_help"
RUNTIME_KEY_UI_STAFF = "ui_show_full_staff_in_help"
WITHDRAWAL_OPERATORS_KEY = "withdrawal_operators"


def _get_runtime_bool(key, config_default):
    try:
        cursor.execute("SELECT value FROM bot_economy WHERE key = ?", (key,))
        row = cursor.fetchone()
        if row is not None:
            return int(row[0] or 0) != 0
    except Exception:
        pass
    return bool(config_default)


def _set_runtime_bool(key, on):
    cursor.execute(
        "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
        (key, 1 if on else 0),
    )
    db.commit()
    try:
        _MAIN_KB_CACHE.clear()
    except Exception:
        pass


def _runtime_ui_show_work():
    return _get_runtime_bool(RUNTIME_KEY_UI_WORK, CONFIG_UI_SHOW_WORK)


def _runtime_ui_show_casino_help():
    return _get_runtime_bool(RUNTIME_KEY_UI_CASINO, CONFIG_UI_SHOW_CASINO_HELP)


def _runtime_ui_show_full_staff_help():
    return _get_runtime_bool(RUNTIME_KEY_UI_STAFF, CONFIG_UI_SHOW_FULL_STAFF_HELP)


def _get_withdrawal_operator_spec():
    """None — не задано, действует prava.json (withdrawals_queue). frozenset — эти id; владелец и замы всегда могут выводы (см. _can_manage_withdrawals_queue)."""
    try:
        cursor.execute("SELECT value FROM bot_economy WHERE key = ?", (WITHDRAWAL_OPERATORS_KEY,))
        row = cursor.fetchone()
        if row is None:
            return None
        raw = (row[0] or "").strip()
        if not raw:
            return frozenset()
        data = json.loads(raw)
        if not isinstance(data, list):
            return None
        return frozenset(int(x) for x in data if int(x) > 0)
    except Exception:
        return None


def _set_withdrawal_operator_ids(id_set):
    ids = sorted({int(x) for x in id_set if int(x) > 0})
    cursor.execute(
        "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
        (WITHDRAWAL_OPERATORS_KEY, json.dumps(ids, ensure_ascii=False)),
    )
    db.commit()


def _clear_withdrawal_operators():
    cursor.execute("DELETE FROM bot_economy WHERE key = ?", (WITHDRAWAL_OPERATORS_KEY,))
    db.commit()


def _owner_settings_summary_text():
    w = "вкл" if _runtime_ui_show_work() else "выкл"
    st = "полный" if _runtime_ui_show_full_staff_help() else "краткий (владелец, замы, спонсоры)"
    spec = _get_withdrawal_operator_spec()
    if spec is None:
        wl = "очередь выводов (!выводы, кнопки): по ролям из prava.json (withdrawals_queue)"
    elif len(spec) == 0:
        wl = "очередь выводов: явный список пуст — обрабатывают владелец и заместители"
    else:
        wl = (
            "очередь выводов: id "
            + ", ".join(str(x) for x in sorted(spec))
            + " (владелец и заместители — всегда)"
        )
    return (
        "⚙️ Настройки бота\n\n"
        f"• Работа (меню и справка): {w}\n"
        f"• Блок «Администрация» в помощи: {st}\n"
        f"• {wl}\n\n"
        "Команды (владелец, ЛС или админ-беседа):\n"
        "!ui+работа  !ui-работа\n"
        "!ui+состав  !ui-состав\n\n"
        "!опвывод список — кто может обрабатывать выводы\n"
        "!опвывод + [юзер]  !опвывод - [юзер]\n"
        "!опвывод сброс — снова prava.json\n\n"
        "Дефолты при первом запуске берутся из config.json; переопределения хранятся в БД."
    )[:3900]


def _strip_club_prefix_raw(text):
    s = (text or '').replace('\ufeff', '').replace('\u200b', '').replace('\xa0', ' ').strip()
    if s.startswith('[') and ']' in s:
        s = s[s.index(']') + 1 :].strip()
    return s


def _normalize_chat_command(text):
    """Текст из беседы: убрать служебные символы и префикс [club…|…] у ответа боту."""
    s = _strip_club_prefix_raw(text).lower()
    if s.startswith("/"):
        s = s[1:].lstrip()
    return s


def _chat_mute_cmd_first_token(text):
    """Первый токен для мут-команды: «+мут» → «мут»."""
    s = _normalize_chat_command(text).lstrip("+").strip()
    if not s:
        return ""
    return s.split(None, 1)[0]


def _chat_first_token(text):
    nk = _normalize_chat_command(text).strip()
    if not nk:
        return ""
    return nk.split(None, 1)[0]


def get_pascha_accept_kb(token):
    kb = VkKeyboard(inline=True)
    kb.add_callback_button(
        "Принять",
        color=VkKeyboardColor.POSITIVE,
        payload={"cmd": "pascha_accept", "t": str(token)},
    )
    return kb


def _handle_pascha_accept(user_id, token, reply_peer):
    """Callback «Принять» в ЛС: битва яйцами 50/50, один раз на игрока."""
    token = (token or "").strip()
    if len(token) < 8:
        send_msg(reply_peer, "Приглашение недействительно или устарело.", kb_for_peer(reply_peer))
        return
    try:
        cursor.execute(
            "SELECT id, owner_id, target_id, status FROM pascha_egg_invites WHERE token = ? LIMIT 1",
            (token,),
        )
        row = cursor.fetchone()
    except Exception:
        row = None
    if not row or str(row[3] or "") != "pending":
        send_msg(reply_peer, "Приглашение уже использовано или недействительно.", kb_for_peer(reply_peer))
        return
    invite_id, owner_oid, target_oid, _st = int(row[0]), int(row[1]), int(row[2]), row[3]
    if int(user_id) != int(target_oid):
        send_msg(reply_peer, "Это приглашение выдано другому юзеру.", kb_for_peer(reply_peer))
        return
    cursor.execute("SELECT COALESCE(pascha_egg_done, 0) FROM users WHERE user_id = ?", (int(target_oid),))
    egg_row = cursor.fetchone()
    if egg_row and int(egg_row[0] or 0) == 1:
        send_msg(reply_peer, "Вы уже участвовали в пасхальной битве яйцами (один раз).", kb_for_peer(reply_peer))
        return
    user_wins = random.random() < 0.5
    cursor.execute(
        "UPDATE pascha_egg_invites SET status = 'done' WHERE id = ?",
        (invite_id,),
    )
    if user_wins:
        cursor.execute(
            "UPDATE users SET pascha_egg_done = 1, pascha_full_withdraw = 1 WHERE user_id = ?",
            (int(target_oid),),
        )
        db.commit()
        send_msg(
            int(target_oid),
            "🥚 Вы выиграли в битве яйцами!\n\n"
            "🎁 Подарок: одна заявка на вывод может включить все ваши наличные (без обычного минимума). "
            "Нажмите «Вывести» в меню бота.",
            kb_for_peer(int(target_oid)),
        )
        send_msg(
            int(owner_oid),
            f"🥚 Пасха: {get_user_mention_with_name(target_oid)} выиграл в битве яйцами.",
            get_main_kb(),
        )
        send_admin_chat_log(
            f"[ПАСХА] Победа игрока {get_user_mention_with_name(target_oid)} над владельцем в битве яйцами. Подарок: полный вывод одной заявкой."
        )
    else:
        cursor.execute("SELECT COALESCE(balance, 0) FROM users WHERE user_id = ?", (int(target_oid),))
        br = cursor.fetchone()
        bal = int((br[0] if br else 0) or 0)
        fine = (bal * 10) // 100
        new_bal = max(0, bal - fine)
        cursor.execute(
            "UPDATE users SET balance = ?, pascha_egg_done = 1 WHERE user_id = ?",
            (int(new_bal), int(target_oid)),
        )
        db.commit()
        send_msg(
            int(target_oid),
            f"🥚 Вы проиграли в битве яйцами.\nС баланса списано 10%: {format_click(fine)}$.\n"
            f"Текущий баланс: {format_click(new_bal)}$.",
            kb_for_peer(int(target_oid)),
        )
        send_msg(
            int(owner_oid),
            f"🥚 Пасха: вы выиграли в битве яйцами у {get_user_mention_with_name(target_oid)}.\n"
            f"У соперника списано 10% ({format_click(fine)}$).",
            get_main_kb(),
        )
        send_admin_chat_log(
            f"[ПАСХА] Победа владельца в битве яйцами над {get_user_mention_with_name(target_oid)}. Списано 10%: {format_click(fine)}$."
        )


def _is_klad_command_text(text):
    """«клад», «/клад», с префиксом клуба и т.п."""
    if not KLAD_ENABLED:
        return False
    s = _normalize_chat_command(text)
    first = s.split(None, 1)[0] if s else ""
    return first == "клад"


def _is_heist_command_text(text):
    s = _normalize_chat_command(text)
    return s in ("ограбление", "ограбить", "грабить")


def _parse_chat_mute_seconds(raw):
    s = (raw or "").strip().lower().replace(" ", "")
    if not s:
        return 30 * 60
    m = re.fullmatch(r'(\d+(?:[.,]\d+)?)([a-zа-я]+)', s)
    if not m:
        raise ValueError("format")
    val = float(m.group(1).replace(",", "."))
    unit = m.group(2)
    if val <= 0:
        raise ValueError("bad")
    if unit in ("m", "min", "мин", "м"):
        return int(val * 60)
    if unit in ("h", "hr", "час", "ч"):
        return int(val * 3600)
    if unit in ("d", "day", "д", "дн"):
        return int(val * 86400)
    raise ValueError("unit")


def _is_promo_activation_text(text):
    """Команда активации промо: «промо КОД» (в т.ч. в беседах, без капчи)."""
    pp = _strip_club_prefix_raw(text).split(None, 1)
    return len(pp) == 2 and pp[0].lower() == 'промо'


def _ai_detect_official_insult(text, context=""):
    s = (_strip_club_prefix_raw(text or "") or "").strip().lower()
    if len(s) < 3:
        return False
    if any(w in s for w in OFFICIAL_INSULT_WORDS):
        return True
    if not NEURAL_MODERATION_ENABLED or not GEMINI_API_KEY:
        return False
    system = (
        "Ты модерационный классификатор. Ответь строго YES или NO. "
        "YES только если есть персональное оскорбление или унижение конкретного участника чата "
        "или представителя администрации (в т.ч. по нику, роли, обращению «ты/вы» к адресату). "
        "NO если в сообщении только ненормативная лексика (мат), междометия или ругань без адреса к человеку "
        "и без унижения личности — мат сам по себе не считается оскорблением по этому правилу."
    )
    prompt = (
        f"Контекст чата:\n{(context or '')[:800]}\n\n"
        f"Сообщение:\n{s[:450]}\n\n"
        "Есть ли адресное оскорбление/унижение участника или администрации (не просто мат)? Ответ: YES или NO."
    )
    out = (_gemini_generate(system, prompt, max_output_tokens=4, temperature=0.0, timeout=12) or "").strip().upper()
    return out.startswith("YES")


def _check_and_apply_official_insult_mute(user_id, peer_id, text, message_cmid=None):
    if int(peer_id) != int(RESTRICTED_CHAT_PEER_ID):
        return False
    if _is_admin_user(user_id):
        return False
    raw = (_strip_club_prefix_raw(text or "") or "").strip()
    if not raw or raw.startswith(("!", "/")):
        return False
    ctx = _official_chat_recent_context(peer_id, limit=5)
    if not _ai_detect_official_insult(raw, ctx):
        return False
    _vk_chat_moderation_restrict_write(int(peer_id), int(user_id), int(OFFICIAL_INSULT_MUTE_SEC), True)
    try:
        cmid = int(message_cmid or 0)
    except Exception:
        cmid = 0
    if cmid > 0:
        try:
            vk.messages.delete(peer_id=int(peer_id), cmids=str(cmid), delete_for_all=1)
        except Exception:
            pass
    send_msg(
        int(peer_id),
        f"⛔ @id{int(user_id)} ({get_user_name(int(user_id))}), мут 30 минут за оскорбления (п.2.1).",
        kb_for_peer(int(peer_id)),
    )
    try:
        send_admin_chat_log(
            f"[МУТ 2.1] {get_user_mention_with_name(int(user_id))}\n"
            f"Наказание: мут 30 минут в официальном чате.\n"
            f"Сообщение: {raw[:300]}"
        )
    except Exception:
        pass
    return True


def _normalize_spam_text(text):
    base = (text or "").lower().strip()
    if not base:
        return ""
    base = re.sub(r'\s+', ' ', base)
    return re.sub(r'[^a-zа-я0-9 ]+', '', base).strip()


def _log_ban_event(user_id, reason, until_ts=0, issued_by=0, source_chat=0):
    try:
        cursor.execute(
            "INSERT INTO user_bans (user_id, issued_by, reason, created_at, until_ts, source_chat) VALUES (?, ?, ?, ?, ?, ?)",
            (int(user_id), int(issued_by or 0), str(reason or "Без причины"), time.time(), float(until_ts or 0), int(source_chat or 0)),
        )
        db.commit()
    except Exception:
        pass


def _log_moderator_action(moderator_id, action_type, amount=0):
    try:
        cursor.execute(
            "INSERT INTO moderator_actions (moderator_id, action_type, amount, created_at) VALUES (?, ?, ?, ?)",
            (int(moderator_id), str(action_type), int(amount or 0), float(time.time())),
        )
        db.commit()
    except Exception:
        pass


def _moderator_stats_for_user(user_id):
    uid = int(user_id)
    kinds = ("ban", "mute", "unmute", "unban", "support_answer", "kick")
    out = {k: 0 for k in kinds}
    try:
        cursor.execute(
            "SELECT action_type, COUNT(*) FROM moderator_actions WHERE moderator_id = ? GROUP BY action_type",
            (uid,),
        )
        for action_type, cnt in cursor.fetchall():
            k = str(action_type or "")
            if k in out:
                out[k] = int(cnt or 0)
        cursor.execute(
            "SELECT COALESCE(SUM(amount), 0) FROM moderator_actions WHERE moderator_id = ? AND action_type = 'transfer_out'",
            (uid,),
            
        )
        out["transfer_sum"] = int((cursor.fetchone() or [0])[0] or 0)
    except Exception:
        out["transfer_sum"] = 0
    return out


def _moderator_support_chat_answers_count(user_id):
    """Количество ответов модератора в чате обращений (support_questions)."""
    try:
        cursor.execute(
            "SELECT COUNT(*) FROM support_questions "
            "WHERE status = 'answered' AND COALESCE(taken_by, 0) = ? "
            "AND TRIM(COALESCE(answer_text, '')) != ''",
            (int(user_id),),
        )
        row = cursor.fetchone()
        return int((row[0] if row else 0) or 0)
    except Exception:
        return 0


def _msk_day_key(ts=None):
    tsv = float(ts or time.time())
    msk = timezone(timedelta(hours=3))
    return datetime.fromtimestamp(tsv, tz=msk).strftime("%Y-%m-%d")


def _day_key_shift(day_key, days_delta):
    try:
        msk = timezone(timedelta(hours=3))
        dt = datetime.strptime(str(day_key), "%Y-%m-%d").replace(tzinfo=msk)
        return (dt + timedelta(days=int(days_delta))).strftime("%Y-%m-%d")
    except Exception:
        return day_key


def _official_norm_for_role(role_key):
    return OFFICIAL_NORM_ROLE_RULES.get(str(role_key or "").strip())


def _heuristic_question_detect(text):
    s = (text or "").strip().lower()
    if len(s) < 4:
        return False
    if "?" in s:
        return True
    return any(w in s for w in OFFICIAL_QUESTION_WORDS)


def _official_chat_recent_context(peer_id, limit=6):
    try:
        cursor.execute(
            "SELECT user_id, text FROM official_chat_messages WHERE peer_id = ? ORDER BY id DESC LIMIT ?",
            (int(peer_id), int(limit)),
        )
        rows = cursor.fetchall() or []
    except Exception:
        rows = []
    if not rows:
        return ""
    rows.reverse()
    return "\n".join(f"id{int(uid)}: {(txt or '')[:220]}" for uid, txt in rows)


def _ai_detect_question_with_context(text, context):
    s = (text or "").strip()
    if len(s) < 6:
        return False
    if not GEMINI_API_KEY or not NEURAL_MODERATION_ENABLED:
        return _heuristic_question_detect(s)
    if not _heuristic_question_detect(s):
        return False
    system = (
        "Ты анализатор чата поддержки. Ответь строго одним словом: YES или NO. "
        "YES только если сообщение игрока реально является вопросом/запросом помощи по боту."
    )
    prompt = (
        f"Контекст беседы:\n{(context or '')[:1000]}\n\n"
        f"Сообщение игрока:\n{s[:450]}\n\n"
        "Это вопрос к модерации/админу? Ответ: YES или NO."
    )
    out = (_gemini_generate(system, prompt, max_output_tokens=4, temperature=0.0, timeout=12) or "").strip().upper()
    return out.startswith("YES")


def _ai_detect_answer_with_context(question_text, answer_text, context):
    a = (answer_text or "").strip()
    if len(a) < 6:
        return False
    if a.startswith(("!", "/")):
        return False
    if not GEMINI_API_KEY or not NEURAL_MODERATION_ENABLED:
        return True
    system = (
        "Ты анализатор модераторского чата. Ответь строго YES или NO. "
        "YES если сообщение модератора является ответом по существу на вопрос игрока."
    )
    prompt = (
        f"Контекст:\n{(context or '')[:900]}\n\n"
        f"Вопрос игрока:\n{(question_text or '')[:350]}\n\n"
        f"Сообщение модератора:\n{a[:450]}\n\n"
        "Это засчитываем как ответ на вопрос? Ответ: YES или NO."
    )
    out = (_gemini_generate(system, prompt, max_output_tokens=4, temperature=0.0, timeout=12) or "").strip().upper()
    return out.startswith("YES")


def _official_chat_touch_daily(user_id, ts, *, add_message=False, add_answer=False):
    uid = int(user_id)
    now_ts = float(ts or time.time())
    day_key = _msk_day_key(now_ts)
    cursor.execute(
        "SELECT first_at, last_at, msg_count, answers_count, report_done, reprimand_issued "
        "FROM official_chat_daily WHERE user_id = ? AND day_key = ?",
        (uid, day_key),
    )
    row = cursor.fetchone()
    if not row:
        first_at = now_ts
        last_at = now_ts
        msg_count = 1 if add_message else 0
        answers_count = 1 if add_answer else 0
        report_done = 0
        reprimand_issued = 0
        cursor.execute(
            "INSERT OR REPLACE INTO official_chat_daily "
            "(user_id, day_key, first_at, last_at, msg_count, answers_count, report_done, reprimand_issued, updated_at) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (uid, day_key, first_at, last_at, msg_count, answers_count, report_done, reprimand_issued, now_ts),
        )
    else:
        first_at, last_at, msg_count, answers_count, report_done, reprimand_issued = row
        if add_message:
            msg_count = int(msg_count or 0) + 1
            first_at = min(float(first_at or now_ts), now_ts)
            last_at = max(float(last_at or now_ts), now_ts)
        if add_answer:
            answers_count = int(answers_count or 0) + 1
        cursor.execute(
            "UPDATE official_chat_daily SET first_at = ?, last_at = ?, msg_count = ?, answers_count = ?, updated_at = ? "
            "WHERE user_id = ? AND day_key = ?",
            (float(first_at or now_ts), float(last_at or now_ts), int(msg_count or 0), int(answers_count or 0), now_ts, uid, day_key),
        )

    role_key = _get_project_role_key(uid)
    rule = _official_norm_for_role(role_key)
    if rule:
        cursor.execute(
            "SELECT first_at, last_at, answers_count FROM official_chat_daily WHERE user_id = ? AND day_key = ?",
            (uid, day_key),
        )
        rr = cursor.fetchone() or (0, 0, 0)
        worked_hours = max(0.0, (float(rr[1] or 0) - float(rr[0] or 0)) / 3600.0)
        done = 1 if worked_hours >= float(rule["hours"]) and int(rr[2] or 0) >= int(rule["answers"]) else 0
        cursor.execute(
            "UPDATE official_chat_daily SET report_done = ? WHERE user_id = ? AND day_key = ?",
            (int(done), uid, day_key),
        )


def _official_total_answers_for_promo(user_id):
    uid = int(user_id)
    try:
        cursor.execute("SELECT COALESCE(SUM(answers_count), 0) FROM official_chat_daily WHERE user_id = ?", (uid,))
        chat_ans = int((cursor.fetchone() or [0])[0] or 0)
    except Exception:
        chat_ans = 0
    try:
        cursor.execute(
            "SELECT COUNT(*) FROM moderator_actions WHERE moderator_id = ? AND action_type = 'support_answer'",
            (uid,),
        )
        support_ans = int((cursor.fetchone() or [0])[0] or 0)
    except Exception:
        support_ans = 0
    return int(chat_ans + support_ans)


def _official_report_days_for_promo(user_id):
    try:
        cursor.execute(
            "SELECT COUNT(*) FROM official_chat_daily WHERE user_id = ? AND report_done = 1",
            (int(user_id),),
        )
        return int((cursor.fetchone() or [0])[0] or 0)
    except Exception:
        return 0


def _official_is_active_for_promo(user_id):
    uid = int(user_id)
    now_day = _msk_day_key()
    min_day = _day_key_shift(now_day, -2)
    try:
        cursor.execute(
            "SELECT COALESCE(SUM(msg_count), 0) FROM official_chat_daily "
            "WHERE user_id = ? AND day_key >= ?",
            (uid, str(min_day)),
        )
        msg_sum = int((cursor.fetchone() or [0])[0] or 0)
    except Exception:
        msg_sum = 0
    return msg_sum >= 5


def _official_promotion_check(target_id, old_role, new_role):
    req = PROMOTION_REQUIREMENTS.get((str(old_role or ""), str(new_role or "")))
    if not req:
        return True, ""
    total_answers = _official_total_answers_for_promo(target_id)
    report_days = _official_report_days_for_promo(target_id)
    is_active = _official_is_active_for_promo(target_id)
    need_rules = int(req.get("need_rules_ack") or 0) == 1
    try:
        cursor.execute("SELECT COALESCE(staff_rules_ack, 0) FROM users WHERE user_id = ?", (int(target_id),))
        rules_ack = int((cursor.fetchone() or [0])[0] or 0)
    except Exception:
        rules_ack = 0

    problems = []
    need_answers = int(req.get("answers") or 0)
    need_days = int(req.get("report_days") or 0)
    if total_answers < need_answers:
        problems.append(f"ответов игрокам: {total_answers}/{need_answers}")
    if report_days < need_days:
        problems.append(f"отчётных дней: {report_days}/{need_days}")
    if not is_active:
        problems.append("недостаточная активность в оф. беседе (нужно минимум 5 сообщений за последние 3 дня)")
    if need_rules and rules_ack != 1:
        problems.append("не подтверждено ознакомление с правилами (!правила ок)")
    if problems:
        return False, "Повышение пока нельзя:\n- " + "\n- ".join(problems)
    return True, ""


def _official_check_previous_day_norms():
    global LAST_OFFICIAL_NORM_DAY_CHECK
    today = _msk_day_key()
    if LAST_OFFICIAL_NORM_DAY_CHECK == today:
        return
    LAST_OFFICIAL_NORM_DAY_CHECK = today
    prev_day = _day_key_shift(today, -1)
    cursor.execute(
        "SELECT user_id, COALESCE(project_role, '') FROM users "
        "WHERE COALESCE(project_role, '') IN ('moderator')"
    )
    role_rows = cursor.fetchall() or []
    for uid, role_key in role_rows:
        uid = int(uid or 0)
        if uid <= 0:
            continue
        rule = _official_norm_for_role(role_key)
        if not rule:
            continue
        cursor.execute(
            "SELECT first_at, last_at, answers_count, report_done, reprimand_issued "
            "FROM official_chat_daily WHERE user_id = ? AND day_key = ?",
            (uid, str(prev_day)),
        )
        row = cursor.fetchone()
        if not row:
            cursor.execute(
                "INSERT OR REPLACE INTO official_chat_daily "
                "(user_id, day_key, first_at, last_at, msg_count, answers_count, report_done, reprimand_issued, updated_at) "
                "VALUES (?, ?, 0, 0, 0, 0, 0, 0, ?)",
                (uid, str(prev_day), float(time.time())),
            )
            row = (0, 0, 0, 0, 0)
        first_at, last_at, answers_count, report_done, reprimand_issued = row
        worked_hours = max(0.0, (float(last_at or 0) - float(first_at or 0)) / 3600.0)
        met = worked_hours >= float(rule["hours"]) and int(answers_count or 0) >= int(rule["answers"])
        if met:
            if int(report_done or 0) != 1:
                cursor.execute(
                    "UPDATE official_chat_daily SET report_done = 1 WHERE user_id = ? AND day_key = ?",
                    (uid, str(prev_day)),
                )
            continue
        cursor.execute(
            "UPDATE official_chat_daily SET report_done = 0 WHERE user_id = ? AND day_key = ?",
            (uid, str(prev_day)),
        )


def _official_norm_rules_text():
    return (
        "📌 Норма администраторов (официальная беседа)\n\n"
        "🧪 Стажёр: 1 час (начало→конец фото) + 1 ответ игроку.\n"
        "🔹 Мл. модератор: 1.5 часа (начало→конец фото) + 1 ответ игроку.\n"
        "🔰 Ст. модератор: 2 часа (начало→конец фото) + 2 ответа игрокам.\n\n"
        "Проверка нормы проводится вручную ответственным админом (кнопки «Норма/Выговор»).\n\n"
        "🎖 Повышение:\n"
        "Стажёр → мл. модератор: 10 ответов, активность, минимум 4 отчётных дня.\n"
        "Мл. модератор → модератор: 20 ответов, активность, минимум 7 отчётных дней, ознакомление с правилами (!правила ок).\n"
        "Модератор → ст. модератор: 35 ответов, активность, минимум 14 отчётных дней."
    )


def _official_chat_ai_track_message(event, user_id, reply_peer, text):
    if int(reply_peer) != int(OFFICIAL_NORM_CHAT_PEER_ID):
        return
    msg_obj = event.obj.message if isinstance(event.obj.message, dict) else {}
    has_attachments = bool((msg_obj.get("attachments") or []) if isinstance(msg_obj, dict) else [])
    raw_text = (_strip_club_prefix_raw(text or "") or "").strip()
    if not raw_text and has_attachments:
        raw_text = "(вложение)"
    if not raw_text:
        return
    now_ts = float(time.time())
    is_staff = 1 if _is_moderation_staff(user_id) else 0
    cursor.execute(
        "INSERT INTO official_chat_messages (peer_id, user_id, text, created_at, is_staff) VALUES (?, ?, ?, ?, ?)",
        (int(reply_peer), int(user_id), raw_text[:1800], now_ts, int(is_staff)),
    )
    if is_staff:
        _official_chat_touch_daily(int(user_id), now_ts, add_message=True, add_answer=False)
    if is_staff:
        rm = msg_obj.get("reply_message") if isinstance(msg_obj, dict) else None
        if isinstance(rm, dict):
            try:
                asker_id = int(rm.get("from_id") or 0)
            except Exception:
                asker_id = 0
            if asker_id > 0 and not _is_moderation_staff(asker_id):
                q_txt = str(rm.get("text") or "").strip()
                q_cmid = int(rm.get("conversation_message_id") or 0)
                qid = 0
                if q_cmid > 0:
                    cursor.execute(
                        "SELECT id FROM official_chat_questions WHERE peer_id = ? AND question_cmid = ? ORDER BY id DESC LIMIT 1",
                        (int(reply_peer), int(q_cmid)),
                    )
                    qrow = cursor.fetchone()
                    qid = int((qrow[0] if qrow else 0) or 0)
                if qid <= 0 and _heuristic_question_detect(q_txt):
                    cursor.execute(
                        "INSERT INTO official_chat_questions (peer_id, asker_id, question_text, question_cmid, status, created_at) "
                        "VALUES (?, ?, ?, ?, 'new', ?)",
                        (int(reply_peer), int(asker_id), (q_txt or "(вопрос без текста)")[:1800], int(q_cmid), now_ts),
                    )
                    qid = int(cursor.lastrowid or 0)
                q_text_for_ai = q_txt
                if qid > 0:
                    cursor.execute("SELECT question_text FROM official_chat_questions WHERE id = ?", (int(qid),))
                    q_text_for_ai = str((cursor.fetchone() or [""])[0] or "")
                ctx = _official_chat_recent_context(reply_peer, limit=6)
                if _ai_detect_answer_with_context(q_text_for_ai, raw_text, ctx):
                    if qid > 0:
                        cursor.execute(
                            "UPDATE official_chat_questions SET status = 'answered', answered_by = ?, answered_at = ?, answer_text = ? WHERE id = ?",
                            (int(user_id), now_ts, raw_text[:1800], int(qid)),
                        )
                    _official_chat_touch_daily(int(user_id), now_ts, add_message=False, add_answer=True)
        try:
            db.commit()
        except Exception:
            pass
        return
    ctx = _official_chat_recent_context(reply_peer, limit=6)
    if _ai_detect_question_with_context(raw_text, ctx):
        q_cmid = int(msg_obj.get("conversation_message_id") or 0) if isinstance(msg_obj, dict) else 0
        cursor.execute(
            "INSERT INTO official_chat_questions (peer_id, asker_id, question_text, question_cmid, status, created_at) "
            "VALUES (?, ?, ?, ?, 'new', ?)",
            (int(reply_peer), int(user_id), raw_text[:1800], int(q_cmid), now_ts),
        )
    try:
        db.commit()
    except Exception:
        pass


def _official_ts_to_msk_hhmm(unix_ts):
    try:
        if float(unix_ts or 0) <= 0:
            return "—"
        msk = timezone(timedelta(hours=3))
        return datetime.fromtimestamp(float(unix_ts), tz=msk).strftime("%H:%M")
    except Exception:
        return "—"


def _official_avg_hours_last_days(user_id, days=7):
    try:
        now_day = _msk_day_key()
        min_day = _day_key_shift(now_day, -(max(1, int(days)) - 1))
        cursor.execute(
            "SELECT first_at, last_at FROM official_chat_daily WHERE user_id = ? AND day_key >= ?",
            (int(user_id), str(min_day)),
        )
        rows = cursor.fetchall() or []
    except Exception:
        rows = []
    spans = []
    for first_at, last_at in rows:
        first_v = float(first_at or 0)
        last_v = float(last_at or 0)
        if first_v > 0 and last_v >= first_v:
            spans.append((last_v - first_v) / 3600.0)
    if not spans:
        return 0.0
    return float(sum(spans) / len(spans))


def get_official_norm_review_kb(target_id, day_key):
    kb = VkKeyboard(inline=True)
    kb.add_callback_button(
        "✅ Норма",
        color=VkKeyboardColor.POSITIVE,
        payload={"cmd": "official_norm_review", "a": "ok", "uid": int(target_id), "d": str(day_key)},
    )
    kb.add_callback_button(
        "📛 Выговор",
        color=VkKeyboardColor.NEGATIVE,
        payload={"cmd": "official_norm_review", "a": "repr", "uid": int(target_id), "d": str(day_key)},
    )
    return kb


def _official_send_manual_norm_review():
    day_key = _msk_day_key()
    cursor.execute(
        "SELECT user_id, COALESCE(project_role, '') FROM users "
        "WHERE COALESCE(project_role, '') IN ('moderator')"
    )
    role_rows = cursor.fetchall() or []
    for uid, role_key in role_rows:
        uid = int(uid or 0)
        if uid <= 0:
            continue
        rule = _official_norm_for_role(role_key)
        if not rule:
            continue
        cursor.execute(
            "SELECT first_at, last_at, msg_count, answers_count, report_done, reprimand_issued "
            "FROM official_chat_daily WHERE user_id = ? AND day_key = ?",
            (uid, str(day_key)),
        )
        row = cursor.fetchone()
        if not row:
            cursor.execute(
                "INSERT OR REPLACE INTO official_chat_daily "
                "(user_id, day_key, first_at, last_at, msg_count, answers_count, report_done, reprimand_issued, updated_at) "
                "VALUES (?, ?, 0, 0, 0, 0, 0, 0, ?)",
                (uid, str(day_key), float(time.time())),
            )
            row = (0, 0, 0, 0, 0, 0)
        first_at, last_at, msg_count, answers_count, _, _ = row
        worked_hours = max(0.0, (float(last_at or 0) - float(first_at or 0)) / 3600.0)
        avg_hours = _official_avg_hours_last_days(uid, days=7)
        online_from = _official_ts_to_msk_hhmm(first_at)
        online_to = _official_ts_to_msk_hhmm(last_at)
        auto_mark = (
            "✅ Авто-оценка: норма выполнена"
            if worked_hours >= float(rule["hours"]) and int(answers_count or 0) >= int(rule["answers"])
            else "❌ Авто-оценка: норма не выполнена"
        )
        txt = (
            f"📋 Проверка нормы ({day_key})\n"
            f"Пользователь: {get_user_mention_with_name(uid)} ({PROJECT_ROLE_LABELS.get(str(role_key), str(role_key))})\n"
            f"Сообщений за день: {int(msg_count or 0)}\n"
            f"Ответы игрокам: {int(answers_count or 0)} / {int(rule['answers'])}\n"
            f"Онлайн сегодня: {online_from} — {online_to} ({worked_hours:.1f} ч)\n"
            f"Средний онлайн (7 дн): {avg_hours:.2f} ч\n"
            f"{auto_mark}\n\n"
            "Выберите решение вручную:"
        )
        send_msg(
            int(OFFICIAL_NORM_REVIEW_ADMIN_ID),
            txt,
            get_official_norm_review_kb(uid, day_key),
        )
    try:
        db.commit()
    except Exception:
        pass


def _official_norm_review_scheduler_loop():
    global LAST_OFFICIAL_NORM_REVIEW_SENT_DAY
    while True:
        try:
            now_msk = _msk_now()
            day_key = now_msk.strftime("%Y-%m-%d")
            if int(now_msk.hour) == int(OFFICIAL_NORM_REVIEW_HOUR_MSK) and LAST_OFFICIAL_NORM_REVIEW_SENT_DAY != day_key:
                _official_send_manual_norm_review()
                LAST_OFFICIAL_NORM_REVIEW_SENT_DAY = day_key
        except Exception:
            pass
        time.sleep(30)


def _unban_user(target_id, issued_by=0, source_chat=0, reason="Разбан администратором"):
    """Снять бан в боте и бан в беседах, записать в историю."""
    try:
        tid = int(target_id)
        _, _ = get_user(tid)
        update_user_fields(tid, is_banned=0, ban_until=0, chat_banned=0, chat_ban_until=0)
        _log_ban_event(
            tid,
            f"Разбан: {str(reason or 'Без причины')}",
            until_ts=0,
            issued_by=issued_by,
            source_chat=source_chat,
        )
        return True
    except Exception:
        return False


def _snippet_from_reply_message(rm):
    """Короткий текст сообщения для истории варнов (до 450 симв.)."""
    if not isinstance(rm, dict):
        return ''
    t = (rm.get('text') or '').strip()
    if t:
        return t[:450]
    atts = rm.get('attachments') or rm.get('attachment')
    if atts:
        return '(сообщение без текста, есть вложения)'
    return '(нет текста)'


def _apply_moderation_warn(target_user_id, issued_by, peer_id, message_snippet, source_kind):
    """Записывает предупреждение модерации; при достижении порога — бан. source_kind: 'sms' | 'warn_cmd'."""
    try:
        tid = int(target_user_id)
        if tid <= 0:
            return None
    except (TypeError, ValueError):
        return None
    if _is_admin_user(tid):
        return {'skipped_admin': True, 'warn_count': None, 'banned': False}
    try:
        iid = int(issued_by or 0)
        pid = int(peer_id or 0)
        snip = (message_snippet or '')[:500]
        sk = source_kind if source_kind in ('sms', 'warn_cmd') else 'sms'
        cursor.execute(
            "INSERT INTO user_moderation_warns (user_id, issued_by, message_snippet, peer_id, source_kind, created_at) VALUES (?, ?, ?, ?, ?, ?)",
            (tid, iid, snip, pid, sk, time.time()),
        )
        cursor.execute("SELECT COALESCE(moderation_warn_count, 0) FROM users WHERE user_id = ?", (tid,))
        prev = int((cursor.fetchone() or [0])[0] or 0)
        newc = prev + 1
        update_user(tid, 'moderation_warn_count', newc)
        snip_line = (snip or '').replace('\n', ' ').strip()
        msg_line = f"\nСообщение: «{snip_line[:220]}»" if snip_line else ""
        send_admin_chat_log(
            f"[ВАРН] {get_user_mention_with_name(tid)} — {newc}/{MODERATION_WARN_BAN_THRESHOLD}\n"
            f"Тип: {_moderation_warn_kind_label(sk)}\n"
            f"Кто: {get_user_mention_with_name(iid) if iid > 0 else 'бот'}"
            f"{msg_line}"
        )
        banned = False
        if newc >= MODERATION_WARN_BAN_THRESHOLD:
            update_user(tid, 'chat_banned', 1)
            update_user(tid, 'moderation_warn_count', 0)
            banned = True
            kind_ru = 'команда -варн'
            _log_ban_event(
                tid,
                f"Бан за {MODERATION_WARN_BAN_THRESHOLD} предупреждения модерации (последнее: {kind_ru}). Сообщение: {snip[:200]}",
                0,
                iid,
                pid,
            )
            _remove_user_from_chat_if_possible(pid, tid)
        db.commit()
        return {'warn_count': newc, 'banned': banned, 'skipped_admin': False}
    except Exception:
        try:
            db.rollback()
        except Exception:
            pass
        return None


def _moderation_warn_kind_label(source_kind):
    return '-варн'


def _baninfo_text_for_target(target_id):
    try:
        tid = int(target_id)
        uname = get_user_name(tid)
        lines = [f"📋 @id{tid} ({uname})", ""]
        cursor.execute(
            "SELECT COALESCE(is_banned, 0), COALESCE(ban_until, 0), COALESCE(chat_banned, 0), COALESCE(chat_ban_until, 0) FROM users WHERE user_id = ?",
            (tid,),
        )
        ur = cursor.fetchone() or (0, 0, 0, 0)
        now_ts = time.time()
        glob_active = int(ur[0] or 0) == 1 or float(ur[1] or 0) > now_ts
        chat_active = int(ur[2] or 0) == 1 or float(ur[3] or 0) > now_ts
        g_line = f"🤖 Бан в боте (глобально): {'да' if glob_active else 'нет'}"
        if float(ur[1] or 0) > now_ts and int(ur[0] or 0) != 1:
            g_line += f" (до {datetime.fromtimestamp(float(ur[1]), timezone.utc).strftime('%d.%m.%Y %H:%M')} UTC)"
        c_line = f"💬 Блокировка в беседах: {'да' if chat_active else 'нет'}"
        if float(ur[3] or 0) > now_ts and int(ur[2] or 0) != 1:
            c_line += f" (до {datetime.fromtimestamp(float(ur[3]), timezone.utc).strftime('%d.%m.%Y %H:%M')} UTC)"
        lines.extend([g_line, c_line, ""])

        cursor.execute(
            "SELECT message_snippet, source_kind, created_at, issued_by, peer_id FROM user_moderation_warns WHERE user_id = ? ORDER BY id DESC LIMIT 15",
            (tid,),
        )
        wrows = cursor.fetchall()
        if wrows:
            lines.append("⚠️ Предупреждения модерации:")
            for idx, (snippet, source_kind, created_at, issued_by, peer_id) in enumerate(wrows, 1):
                created_s = datetime.fromtimestamp(float(created_at or 0), timezone.utc).strftime('%d.%m.%Y %H:%M UTC')
                ib = int(issued_by or 0)
                peer_s = f"чат {int(peer_id)}" if int(peer_id or 0) else "—"
                lbl = _moderation_warn_kind_label(source_kind)
                snip_disp = (snippet or '').replace('\n', ' ')[:220]
                lines.append(f"{idx}. [{lbl}] {created_s} | чат: {peer_s} | от @id{ib}")
                lines.append(f"   Сообщение: «{snip_disp}»")
            lines.append("")

        cursor.execute(
            "SELECT reason, created_at, until_ts, source_chat FROM user_bans WHERE user_id = ? ORDER BY id DESC LIMIT 15",
            (tid,),
        )
        rows = cursor.fetchall()
        if not rows and not wrows:
            lines.append("ℹ️ Нет записей в журнале варнов и истории банов.")
            return "\n".join(lines)[:3900]
        if not rows:
            lines.append("🚫 В таблице истории банов записей нет.")
            return "\n".join(lines)[:3900]
        lines.append(f"🚫 История банов (записей: {len(rows)}):")
        for idx, (reason, created_at, until_ts, source_chat) in enumerate(rows, 1):
            created_s = datetime.fromtimestamp(float(created_at or 0), timezone.utc).strftime('%d.%m.%Y %H:%M UTC')
            until_s = datetime.fromtimestamp(float(until_ts), timezone.utc).strftime('%d.%m.%Y %H:%M UTC') if float(until_ts or 0) > 0 else "без срока"
            src = f"чат {int(source_chat)}" if int(source_chat or 0) else "личные/система"
            lines.append(f"{idx}. {reason} | {created_s} | до: {until_s} | {src}")
        return "\n".join(lines)[:3900]
    except Exception:
        return "Не удалось получить историю банов."


def _check_and_apply_chat_spam(user_id, peer_id, text, message_cmid=None):
    global _last_spam_cleanup_at
    if not _is_multichat_peer(peer_id):
        return False
    msg_norm = _normalize_spam_text(text)
    if not msg_norm:
        return False
    now = time.time()
    cutoff = now - CHAT_SPAM_WINDOW_SEC
    try:
        if (now - _last_spam_cleanup_at) >= SPAM_CLEANUP_INTERVAL_SEC:
            cursor.execute("DELETE FROM chat_spam_log WHERE created_at < ?", (cutoff,))
            _last_spam_cleanup_at = now
        cursor.execute(
            "INSERT INTO chat_spam_log (user_id, peer_id, msg_norm, created_at) VALUES (?, ?, ?, ?)",
            (int(user_id), int(peer_id), msg_norm[:200], now),
        )
        cursor.execute(
            "SELECT COUNT(*) FROM chat_spam_log WHERE user_id = ? AND peer_id = ? AND msg_norm = ? AND created_at >= ?",
            (int(user_id), int(peer_id), msg_norm[:200], cutoff),
        )
        cnt = int(cursor.fetchone()[0] or 0)
        if cnt < CHAT_SPAM_REPEAT_LIMIT:
            db.commit()
            return False
        mute_until = now + SPAM_MUTE_SEC
        update_user(user_id, 'spam_mute_until', mute_until)
        _vk_chat_moderation_restrict_write(int(peer_id), int(user_id), int(SPAM_MUTE_SEC), True)
        try:
            cmid = int(message_cmid or 0)
            if cmid > 0:
                vk.messages.delete(peer_id=int(peer_id), cmids=str(cmid), delete_for_all=1)
        except Exception:
            pass
        _log_ban_event(
            user_id=user_id,
            reason=f"Мут за спам в чате {peer_id} (однотипные сообщения)",
            until_ts=mute_until,
            issued_by=0,
            source_chat=peer_id,
        )
        if int(peer_id) == int(RESTRICTED_CHAT_PEER_ID):
            cursor.execute("SELECT COALESCE(official_warns, 0) FROM users WHERE user_id = ?", (int(user_id),))
            warns = int((cursor.fetchone() or [0])[0] or 0) + 1
            update_user(user_id, 'official_warns', warns)
            send_msg(
                int(peer_id),
                f"⚠️ @id{user_id} ({get_user_name(user_id)}), предупреждение за спам: {warns}/{OFFICIAL_CHAT_WARN_BAN_THRESHOLD}.\nВы получили мут в боте на 30 минут.",
                kb_for_peer(peer_id),
            )
            if warns >= OFFICIAL_CHAT_WARN_BAN_THRESHOLD:
                update_user(user_id, 'chat_banned', 1)
                _log_ban_event(
                    user_id=user_id,
                    reason=f"Бан за 3 предупреждения за спам в официальной беседе {RESTRICTED_CHAT_PEER_ID}",
                    until_ts=0,
                    issued_by=0,
                    source_chat=peer_id,
                )
                _remove_user_from_chat_if_possible(peer_id, user_id)
                send_msg(
                    int(peer_id),
                    f"🚫 Пользователь @id{user_id} ({get_user_name(user_id)}) забанен за 3 предупреждения в официальной беседе.",
                    kb_for_peer(peer_id),
                )
        db.commit()
        return True
    except Exception:
        return False


def _get_help_kb(allow_ask=True):
    kb = VkKeyboard(inline=True)
    kb.add_button('Команды', color=VkKeyboardColor.PRIMARY, payload={'cmd': 'help_commands'})
    kb.add_button('Вопросы', color=VkKeyboardColor.SECONDARY, payload={'cmd': 'help_faq'})
    if allow_ask:
        kb.add_line()
        kb.add_callback_button('Спросить вопрос', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'help_ask_question'})
    return kb


def _project_role_key_from_text(raw):
    t = re.sub(r"\s+", " ", (raw or "").strip().lower().replace("ё", "е"))
    if t in ("владелец", "владелец проекта", "owner"):
        return "owner"
    if t in ("зам владелец", "замвладелец", "зам владельца", "зам владелец проекта", "deputy_owner"):
        return "deputy_owner"
    if t in ("модератор", "модератор проекта", "moderator"):
        return "moderator"
    if t in ("спонсор", "sponsor"):
        return "sponsor"
    if t in ("нет", "снять", "убрать", "none"):
        return ""
    return None


def _get_project_role_key(user_id):
    if int(user_id) == int(ADMIN_ID):
        return "owner"
    cursor.execute("SELECT COALESCE(project_role, '') FROM users WHERE user_id = ?", (int(user_id),))
    row = cursor.fetchone()
    raw = ((row[0] if row else "") or "").strip()
    if not raw:
        return ""
    normalized = _project_role_key_from_text(raw)
    if normalized is not None:
        return normalized
    rk = raw.lower()
    return rk if rk in ALLOWED_PROJECT_ROLES else ""


def _project_role_label_for_user(user_id):
    key = _get_project_role_key(user_id)
    return PROJECT_ROLE_LABELS.get(key, "")


def _project_role_hashtag_from_label(role_label):
    """Хэштеги ролей отключены: возвращаем пустую строку для совместимости."""
    return ""


def _project_role_label_with_hashtag_by_key(role_key):
    lbl = PROJECT_ROLE_LABELS.get(str(role_key or "").strip(), str(role_key or ""))
    tag = _project_role_hashtag_from_label(lbl)
    return f"{lbl} {tag}" if tag else lbl


def _project_role_label_with_hashtag_for_user(user_id):
    lbl = _project_role_label_for_user(user_id) or "Игрок"
    tag = _project_role_hashtag_from_label(lbl)
    return f"{lbl} {tag}" if tag else lbl


def _is_owner(user_id):
    try:
        return int(user_id) == int(ADMIN_ID)
    except Exception:
        return False


def _is_official_admin_id(user_id):
    try:
        return int(user_id) in OFFICIAL_ADMIN_IDS_SET
    except (TypeError, ValueError):
        return False


def _genapi_unrestricted_for(user_id):
    """Полный режим Gemini без тематических ограничений — только для admin_id из config.json."""
    try:
        return int(user_id) == int(ADMIN_ID)
    except (TypeError, ValueError):
        return False


def _is_deputy_owner(user_id):
    return _get_project_role_key(user_id) == "deputy_owner"


def _prava_effective_role_key(user_id):
    try:
        uid = int(user_id)
    except (TypeError, ValueError):
        return ""
    if _is_owner(uid):
        return "owner"
    try:
        if _is_official_admin_id(uid):
            return "official_vk"
    except Exception:
        pass
    return (_get_project_role_key(uid) or "").strip()


def _prava_role_can(user_id, perm_key):
    """Права из prava.json: значение [true/false, «комментарий»] или bool."""
    rk = _prava_effective_role_key(user_id)
    entry = ((PRAVA_DATA or {}).get("roles") or {}).get(rk, {}).get(perm_key)
    if isinstance(entry, list) and len(entry) >= 1:
        return bool(entry[0])
    if isinstance(entry, bool):
        return entry
    if perm_key in ("chat_mute", "chat_unmute"):
        return _is_owner(user_id) or _is_deputy_owner(user_id) or (
            _get_project_role_key(user_id) == "moderator"
        ) or _is_official_admin_id(user_id)
    return False


def _can_use_baninfo(user_id):
    return _is_owner(user_id) or _is_deputy_owner(user_id)


def _can_use_promolist(user_id):
    return _is_admin_user(user_id)


def _can_manage_withdrawals_queue(user_id):
    """Очередь выводов: владелец и заместители; либо явный список id в БД (!опвывод); иначе prava.json (withdrawals_queue)."""
    try:
        uid = int(user_id)
    except (TypeError, ValueError):
        return False
    if _is_owner(uid):
        return True
    if _is_deputy_owner(uid):
        return True
    spec = _get_withdrawal_operator_spec()
    if spec is not None:
        return uid in spec
    return _prava_role_can(uid, "withdrawals_queue")


def _is_admin_command_attempt(text, payload_cmd, user_id):
    if payload_cmd in ADMIN_OP_PAYLOAD_CMDS or payload_cmd in ("admin_op_contest", "contest_cb", "contest_owner"):
        return True
    if payload_cmd in ("admin_pay", "admin_deny", "admin_withdraw_cancel"):
        return _can_manage_withdrawals_queue(user_id)
    s = _strip_club_prefix_raw(text).strip().lower()
    if s == "/op":
        return _is_owner(user_id) or _is_deputy_owner(user_id) or _can_use_promolist(user_id)
    if s == "/promolist":
        return _is_owner(user_id) or _can_use_promolist(user_id)
    if s.startswith("!рассылка"):
        return _is_owner(user_id)
    if s.startswith("!экономика") or s.startswith("!эко"):
        return _is_owner(user_id)
    if s.startswith("/гпт"):
        return _is_owner(user_id) or _is_deputy_owner(user_id)
    if s.startswith("!выводы"):
        return _can_manage_withdrawals_queue(user_id)
    if s.startswith("!vivod"):
        return _can_manage_withdrawals_queue(user_id)
    if s.startswith("!создатьпромо"):
        return _is_owner(user_id) or _is_deputy_owner(user_id)
    if s.startswith("!создатьпромобуст") or s.startswith("!создатьбуст"):
        return _is_owner(user_id)
    if s.startswith("!удалитьпромо"):
        return _is_owner(user_id)
    if s.startswith("!снять"):
        return _is_owner(user_id)
    if s.startswith("!кд"):
        return _is_owner(user_id)
    if s.startswith("!сбор"):
        return _is_owner(user_id)
    if re.match(r"^\s*/even1\s*$", s, re.IGNORECASE):
        return _is_owner(user_id)
    if s.startswith("!выдать"):
        return _is_owner(user_id)
    if re.match(r'^\s*!-?твинк\b', s, re.IGNORECASE):
        return _is_owner(user_id)
    if re.match(r'^\s*!-модерденьги\s*$', s, re.IGNORECASE):
        return _is_owner(user_id)
    if re.match(r'^\s*!настройки\s*$', s, re.IGNORECASE):
        return _is_owner(user_id)
    if re.match(r'^\s*!ui[\+\-]', s, re.IGNORECASE):
        return _is_owner(user_id)
    if re.match(r'^\s*!опвывод', s, re.IGNORECASE):
        return _is_owner(user_id)
    if s.startswith("!должность"):
        return _is_owner(user_id)
    if s.startswith("!капча"):
        return _is_owner(user_id) or _is_deputy_owner(user_id)
    if s.startswith("//baninfo"):
        return _can_use_baninfo(user_id)
    if re.match(r'^\s*!?бан\s', s, re.IGNORECASE):
        return _is_owner(user_id) or _is_deputy_owner(user_id)
    if re.match(r'^\s*!?разбан\s', s, re.IGNORECASE):
        return _is_owner(user_id) or _is_deputy_owner(user_id)
    if re.match(r'^\s*\+выговор\b', s, re.IGNORECASE) or re.match(r'^\s*-выговор\b', s, re.IGNORECASE):
        return _is_owner(user_id) or _can_use_staff_reprimand_non_owner_commands(user_id)
    if re.match(r'^\s*!повысить\b', s, re.IGNORECASE):
        return _is_owner(user_id) or _is_deputy_owner(user_id)
    if s.startswith("!набор"):
        return _can_use_admin_chat_mod_features(user_id)
    if re.match(r"^\s*/?инфо\s+\S", s, re.IGNORECASE):
        return _can_use_admin_chat_mod_features(user_id)
    return False


def _owner_admin_allowed_in_this_peer(reply_peer, _text):
    """Владельческие команды (/op, !сбор, /repost33…) — только ЛС или админ-беседа."""
    try:
        if not _is_multichat_peer(reply_peer):
            return True
        if int(reply_peer) == int(ADMIN_CHAT_PEER_ID):
            return True
    except (TypeError, ValueError):
        return True
    return False


def _admin_flow_requires_private_or_mod_chat(text, payload_cmd, user_id):
    """Дополнительные админ-триггеры к _is_admin_command_attempt (для блокировки в обычных беседах)."""
    if _is_admin_command_attempt(text, payload_cmd, user_id):
        return True
    t = (text or '').strip()
    tl = t.lower()
    try:
        uid = int(user_id)
    except (TypeError, ValueError):
        uid = 0
    if payload_cmd == 'gpt_shorten' and (_is_owner(uid) or _is_deputy_owner(uid)):
        return True
    if re.match(r'^\s*/гпт(?:\s+.+)?$', t, re.IGNORECASE) and (_is_owner(uid) or _is_deputy_owner(uid)):
        return True
    if tl == '/promolist' and _can_use_promolist(uid):
        return True
    if _is_owner(uid) and (tl.startswith('!экономика') or tl.startswith('!эко') or tl.startswith('!удалитьпромо')):
        return True
    if uid == int(ADMIN_ID) and (
        tl.startswith('!выдать')
        or tl.startswith('!рассылка')
        or tl == '!выводы'
        or tl.startswith('!vivod')
        or payload_cmd in ('admin_pay', 'admin_deny', 'admin_withdraw_cancel')
    ):
        return True
    return False


def _abort_public_multichat_admin_spam(reply_peer, text, payload_cmd, user_id):
    """Не обрабатываем админку в обычных беседах (только ЛС или ADMIN_CHAT_PEER_ID)."""
    if not _is_multichat_peer(reply_peer):
        return False
    try:
        if int(reply_peer) == int(ADMIN_CHAT_PEER_ID):
            return False
    except (TypeError, ValueError):
        return False
    return _admin_flow_requires_private_or_mod_chat(text, payload_cmd, user_id)


def _deputy_daily_promo_count(user_id):
    now = time.time()
    day_start = int(now // 86400) * 86400
    day_end = day_start + 86400
    cursor.execute(
        "SELECT COUNT(*) FROM promocodes "
        "WHERE created_by = ? AND created_at >= ? AND created_at < ?",
        (int(user_id), float(day_start), float(day_end)),
    )
    return int(cursor.fetchone()[0] or 0)


STAFF_REPRIMAND_MAX = 10


def _can_use_staff_reprimand_non_owner_commands(user_id):
    """+выговор / −выговор не от владельца: замы и мод. состав (не стажёр). − только по выговорам не от владельца."""
    if _is_owner(user_id):
        return False
    if _is_deputy_owner(user_id):
        return True
    return _prava_role_can(user_id, "strike_staff")


def _get_staff_repr_breakdown(uid):
    """(выговоры от владельца, выговоры от состава, всего)."""
    try:
        cursor.execute(
            "SELECT COALESCE(staff_reprimands_from_owner, 0), COALESCE(staff_reprimands_from_other, 0), COALESCE(staff_reprimands, 0) "
            "FROM users WHERE user_id = ?",
            (int(uid),),
        )
        row = cursor.fetchone()
        if not row:
            return 0, 0, 0
        o = int(row[0] or 0)
        ot = int(row[1] or 0)
        legacy_total = int(row[2] or 0)
        if o == 0 and ot == 0 and legacy_total > 0:
            o = legacy_total
        total = o + ot
        return o, ot, total
    except Exception:
        return 0, 0, 0


def _get_staff_reprimands(uid):
    _, _, total = _get_staff_repr_breakdown(uid)
    return min(STAFF_REPRIMAND_MAX, int(total))


def _set_staff_repr_counts(uid, owner_n, other_n):
    owner_n = max(0, min(STAFF_REPRIMAND_MAX, int(owner_n)))
    other_n = max(0, min(STAFF_REPRIMAND_MAX, int(other_n)))
    while owner_n + other_n > STAFF_REPRIMAND_MAX:
        if other_n > 0:
            other_n -= 1
        else:
            owner_n -= 1
    total = owner_n + other_n
    update_user(int(uid), "staff_reprimands_from_owner", owner_n)
    update_user(int(uid), "staff_reprimands_from_other", other_n)
    update_user(int(uid), "staff_reprimands", total)
    return total


def _set_staff_reprimands(uid, n):
    """Совместимость: задать только общее число (всё считается выданным владельцем)."""
    n = max(0, min(STAFF_REPRIMAND_MAX, int(n)))
    return _set_staff_repr_counts(uid, n, 0)


def _staff_reprimands_team_block_text():
    try:
        cursor.execute(
            "SELECT user_id, COALESCE(staff_reprimands, 0) FROM users WHERE COALESCE(staff_reprimands, 0) > 0 "
            "ORDER BY staff_reprimands DESC, user_id ASC LIMIT 18"
        )
        rows = cursor.fetchall() or []
    except Exception:
        return "\n📛 Выговоры состава: (ошибка загрузки)\n"
    if not rows:
        return "\n📛 Выговоры состава: активных нет.\n"
    lines = ["\n📛 Выговоры состава:\n"]
    names = get_user_names_bulk([int(r[0]) for r in rows])
    for uid, cnt in rows:
        uid = int(uid)
        nm = names.get(uid, f"id{uid}")
        lines.append(f"• @id{uid} ({nm}) — {int(cnt)}/{STAFF_REPRIMAND_MAX}\n")
    return "".join(lines)


def _format_moderator_info_message(user_id, moderator_public_id, include_team_reprimands=False):
    _rl_plain = _project_role_label_for_user(user_id)
    role_label = _project_role_label_with_hashtag_for_user(user_id) if _rl_plain else "Модератор"
    tenure = _role_tenure_text(user_id)
    pub_id_line = f"@id{int(moderator_public_id)}" if int(moderator_public_id) > 0 else "не установлен"
    mstats = _moderator_stats_for_user(user_id)
    rep_n = _get_staff_reprimands(user_id)
    support_answers_chat = _moderator_support_chat_answers_count(user_id)
    extra_team = _staff_reprimands_team_block_text() if include_team_reprimands else ""
    title = "📋 Модераторское меню" if include_team_reprimands else "🪪 Инфо модератора"
    return (
        f"{title}\n\n"
        f"VK ID: @id{int(user_id)}\n"
        f"Публичный ID для ответов: {pub_id_line}\n"
        f"Ранг: {role_label}\n"
        f"На должности: {tenure}\n"
        f"📛 Выговоры: {rep_n}/{STAFF_REPRIMAND_MAX}\n\n"
        "📊 Статистика:\n"
        f"- Банов: {format_balance(mstats.get('ban', 0))}\n"
        f"- Мутов: {format_balance(mstats.get('mute', 0))}\n"
        f"- Размутов: {format_balance(mstats.get('unmute', 0))}\n"
        f"- Разбанов: {format_balance(mstats.get('unban', 0))}\n"
        f"- Киков: {format_balance(mstats.get('kick', 0))}\n"
        f"- Передано валюты: {format_click(mstats.get('transfer_sum', 0))}$\n"
        f"- Обработано обращений: {format_balance(mstats.get('support_answer', 0))}\n"
        f"- Ответов в чате обращений: {format_balance(support_answers_chat)}\n"
        f"{extra_team}\n"
        "В админ-беседе карточка другого модератора: /инфо [юзер]. "
        "Смена своего публичного ID в ответах: !модер айди [число]"
    )[:3900]


def _resolve_reply_or_mention_target(event, text, cmd_prefix):
    """cmd_prefix например '!повысить' или '+выговор' (без пробела в конце)."""
    msg_obj = event.obj.message if isinstance(event.obj.message, dict) else {}
    rm = msg_obj.get("reply_message")
    if rm:
        try:
            fid = int(rm.get("from_id"))
            if fid > 0:
                return fid, None
        except (TypeError, ValueError):
            pass
    raw = _strip_club_prefix_raw(text or "").strip()
    esc = re.escape(cmd_prefix)
    m = re.match(rf"^\s*{esc}\s+(\S+)", raw, re.IGNORECASE)
    if m:
        tid = get_id_by_domain(m.group(1))
        if tid:
            return int(tid), None
    return None, "Укажите юзера (упоминание или ссылку) или ответьте на его сообщение."


def _resolve_strike_command_target_reason(event, text, cmd_prefix):
    """+выговор / -выговор: ответ на сообщение или «cmd [юзер] [причина]». Возвращает (target_id, reason_or_None, err)."""
    msg_obj = event.obj.message if isinstance(event.obj.message, dict) else {}
    rm = msg_obj.get("reply_message")
    raw = _strip_club_prefix_raw(text or "").strip()
    esc = re.escape(cmd_prefix)
    if rm:
        try:
            fid = int(rm.get("from_id"))
            if fid > 0:
                tail = re.sub(rf"^\s*{esc}\s*", "", raw, count=1, flags=re.IGNORECASE).strip()
                return fid, (tail if tail else None), None
        except (TypeError, ValueError):
            pass
    m = re.match(rf"^\s*{esc}\s+(\S+)\s*(.*)$", raw, re.IGNORECASE | re.DOTALL)
    if m:
        tid = get_id_by_domain(m.group(1))
        if tid:
            reason = (m.group(2) or "").strip()
            return int(tid), (reason if reason else None), None
    return (
        None,
        None,
        f"Формат: {cmd_prefix} [юзер] [причина] или ответьте на сообщение и напишите {cmd_prefix} с причиной.",
    )


def _parse_ban_duration_seconds(raw, is_deputy=False):
    s = (raw or "").strip().lower().replace(" ", "")
    if not s:
        raise ValueError("empty")
    m = re.fullmatch(r'(\d+(?:[.,]\d+)?)([a-zа-я]*)', s)
    if not m:
        raise ValueError("bad")
    val = float(m.group(1).replace(",", "."))
    unit = m.group(2)
    if val <= 0:
        raise ValueError("bad")
    if unit in ("",):
        sec = int(val * (60 if is_deputy else 86400))
    elif unit in ("m", "min", "мин", "м"):
        sec = int(val * 60)
    elif unit in ("h", "hr", "час", "ч"):
        sec = int(val * 3600)
    elif unit in ("d", "day", "д", "дн"):
        sec = int(val * 86400)
    else:
        raise ValueError("unit")
    if sec <= 0:
        raise ValueError("bad")
    if is_deputy and sec > 30 * 60:
        raise ValueError("deputy_limit")
    return sec


def _admins_help_text_compact():
    """Краткий вид: владелец, заместители, роль «спонсор» (модерация скрыта)."""
    lines = ["🛡 Администрация (кратко):"]
    lines.append(
        f"@id{int(ADMIN_ID)} ({get_user_name(int(ADMIN_ID))}) — {_project_role_label_with_hashtag_by_key('owner')}"
    )
    lines.append("\n🛡 Заместители владельца:")
    try:
        cursor.execute(
            "SELECT user_id, TRIM(COALESCE(project_role, '')) FROM users "
            "WHERE TRIM(COALESCE(project_role, '')) IN ('deputy_owner')",
        )
        dep_rows = cursor.fetchall() or []
    except Exception:
        dep_rows = []
    dep_rows.sort(key=lambda x: int(x[0]))
    if dep_rows:
        for uid, rk in dep_rows:
            uid = int(uid)
            rk = (rk or "").strip()
            if uid == int(ADMIN_ID):
                continue
            lines.append(f"- @id{uid} ({get_user_name(uid)}) — {_project_role_label_with_hashtag_by_key(rk)}")
    else:
        lines.append("- Пока не назначены.")
    lines.append("\n💎 Спонсоры (роль в !должность):")
    try:
        cursor.execute(
            "SELECT user_id FROM users WHERE TRIM(COALESCE(project_role, '')) = ? ORDER BY user_id",
            ("sponsor",),
        )
        sp_rows = cursor.fetchall()
    except Exception:
        sp_rows = []
    if sp_rows:
        for (uid,) in sp_rows:
            uid = int(uid)
            lines.append(f"- @id{uid} ({get_user_name(uid)}) — {_project_role_label_with_hashtag_by_key('sponsor')}")
    else:
        lines.append("- Пока никого с ролью «спонсор».")
    lines.append("\n—\nПолный список модераторов в этом разделе скрыт.")
    return "\n".join(lines)[:3900]


def _admins_help_text():
    if not _runtime_ui_show_full_staff_help():
        return _admins_help_text_compact()
    lines = ["🛡 Администрация:"]
    seen = set()
    lines.append(
        f"@id{int(ADMIN_ID)} ({get_user_name(int(ADMIN_ID))}) — {_project_role_label_with_hashtag_by_key('owner')}"
    )
    seen.add(int(ADMIN_ID))
    cursor.execute("SELECT user_id, COALESCE(project_role, '') FROM users WHERE TRIM(COALESCE(project_role, '')) != ''")
    rows = cursor.fetchall()
    admin_roles = {"deputy_owner"}
    moderator_roles = {"moderator"}
    honorary_roles = ("sponsor",)
    honorary_lines = []
    order = {
        "deputy_owner": 1,
        "moderator": 2,
        "sponsor": 3,
        "owner": 7,
    }
    rows.sort(key=lambda x: order.get((x[1] or "").strip(), 9))
    mod_lines = []
    for uid, role_key in rows:
        uid = int(uid)
        if uid in seen:
            continue
        role_key = (role_key or "").strip()
        label = PROJECT_ROLE_LABELS.get(role_key)
        if not label:
            continue
        if role_key in admin_roles:
            lines.append(f"- @id{uid} ({get_user_name(uid)}) — {_project_role_label_with_hashtag_by_key(role_key)}")
            seen.add(uid)
        elif role_key in moderator_roles:
            mod_lines.append(f"- @id{uid} ({get_user_name(uid)}) — {_project_role_label_with_hashtag_by_key(role_key)}")
            seen.add(uid)
        elif role_key in honorary_roles:
            honorary_lines.append(
                (
                    honorary_roles.index(role_key),
                    f"- @id{uid} ({get_user_name(uid)}) — {_project_role_label_with_hashtag_by_key(role_key)}",
                )
            )
            seen.add(uid)
    lines.append("\n👮 Модераторский состав:")
    if mod_lines:
        lines.extend(mod_lines)
    else:
        lines.append("- Пока нет назначений.")
    if honorary_lines:
        honorary_lines.sort(key=lambda x: x[0])
        lines.append("\n💎 Поддержка и прочие должности:")
        lines.extend(x[1] for x in honorary_lines)
    return "\n".join(lines)


def _user_commands_help_text():
    prog_extra = []
    if _runtime_ui_show_work():
        prog_extra.append("работа — Ozon: поиск коробок (кнопка «Работа»)")
    prog_mid = ("\n" + "\n".join(prog_extra)) if prog_extra else ""
    return (
        "📚 Это кликер-бот проекта: прогресс и баланс привязаны к вашему аккаунту ВК. "
        "Основной функционал в личке с ботом; отдельно есть бот сообщества для репостов и активности группы.\n"
        "Команды ниже — без префиксов, отправляйте текстом, как написано.\n\n"
        "Основа:\n"
        "кликать\n"
        "профиль\n\n"
        "Деньги:\n"
        "пожертвование\n"
        "транзакции\n\n"
        "Прогресс и активности:\n"
        "рефка\n"
        "магазин\n"
        "топ\n"
        "ограбление\n"
        f"{prog_mid}\n\n"
        "Прочее:\n"
        "промо КОД\n"
        "участие\n"
        "помощь\n"
        "команды\n"
        "о боте\n\n"
        "«Юзер» — упоминание или ссылка на профиль ВК."
    )


def _user_faq_help_text():
    return (
        "❓ Частые вопросы\n\n"
        "1) Как быстрее заработать?\n"
        "- Кликайте регулярно и используйте доступные активности.\n"
        "- Используйте переводы и промокоды.\n"
        "- Активируйте промокоды и развивайте рефку.\n\n"
        "2) Почему не могу кликать?\n"
        "- Нужна энергия. Если энергии 0, подождите реген.\n\n"
        "3) Почему не могу вывести все деньги?\n"
        "- Минимальная сумма вывода: 5мм.\n"
        "- Часть баланса может быть временно заблокирована (например, награда за репост до конца суток).\n\n"
        "4) Как работает репост-доход?\n"
        f"- За репост поста сообщества: {format_click(REPOST_DAILY_REWARD)}$ в день, максимум {REPOST_MAX_DAYS} дня.\n"
        "- Если удалить репост до конца дня, награда за этот день списывается.\n\n"
        "5) Как работают ограбления?\n"
        "- Команда: \"ограбление\".\n"
        "- Есть шанс неудачи со штрафом и тюрьмой, учитывайте риск.\n\n"
        "6) Что дает магазин?\n"
        "- Усиления клика для ускорения прогресса и заработка.\n\n"
        "7) Что вводить в промокод?\n"
        "- Формат: \"промо КОД\" (пример: промо START).\n\n"
        "8) Куда писать, если что-то не работает?\n"
        "- Напишите администратору/владельцу проекта и опишите проблему."
    )


def _moderator_staff_help_lines(title_rank: str):
    """Команды для модераторов/ст. модеров и части официального состава (беседа + promolist)."""
    return [
        f"\n{title_rank}\n",
        "\nВезде:\n"
        "- /promolist\n"
        "- или текстом: промокоды\n\n"
        "В беседе (ответом на сообщение):\n"
        "- мут [время]\n"
        "- -мут или размут\n"
        "- -варн\n\n"
        "В админ-беседе:\n"
        "- /инфо [юзер] — карточка модератора (статистика, выговоры состава)\n\n"
        "+выговор / −выговор — только по выговорам, выданным составом; снять выговор владельца может только владелец.\n\n"
        "Состав модерации и оф. админы варны этими командами не получают.\n",
    ]


def _admin_commands_help_text(user_id):
    role_key = _get_project_role_key(user_id)
    lines = ["🛠 Команды администратора\n"]
    try:
        official_other = _is_official_admin_id(user_id) and not _is_owner(user_id) and role_key not in (
            "deputy_owner",
        )
    except Exception:
        official_other = False
    if _is_owner(user_id):
        lines += [
            "\nРанг: владелец.\n",
            "\nБазовые команды:\n"
            "- /op\n"
            "- /promolist\n"
            "- //baninfo\n"
            "- бан / разбан\n"
            "- кик (беседа, ответом на сообщение)\n"
            "- !капча\n"
            "- !создатьпромо\n"
            "- /гпт\n"
            "- !выводы\n",
            "\nТолько владелец:\n"
            "- !удалитьпромо\n"
            "- !рассылка\n"
            "- !экономика (!эко)\n"
            "- !деп- (отключить депозиты и вернуть все средства с депозита)\n"
            "- !выдать / !снять\n"
            "- !сбор\n"
            "- !должность\n"
            "- !кд — сброс игровых кулдаунов у игрока\n",
            "\nИнтерфейс и кто обрабатывает выводы: !настройки, !ui+/-, !опвывод (дефолты в config.json).\n",
            "\nЗам владельца (кратко):\n"
            "- /op (админ-панель, конкурс)\n"
            "- бан до 30 мин, разбан\n"
            "- !капча\n"
            "- промо, /promolist\n"
            "- в беседе: кик (муты и выговоры по составу от владельца — только у владельца)\n",
            "\nМодератор (в !должность: модератор):\n"
            "- /promolist\n"
            "- в беседе: мут, -варн\n",
        ]
    elif role_key == "deputy_owner":
        rank_line = "\nРанг: зам владельца.\n"
        lines += [
            rank_line,
            "\nКоманды:\n"
            "- /op (админ-панель, конкурс)\n"
            "- /promolist\n"
            "- //baninfo\n"
            "- бан до 30 мин (в беседе только чаты)\n"
            "- разбан\n"
            "- !капча\n"
            "- !создатьпромо\n",
            "\nБеседа (ответом на сообщение):\n"
            "- кик\n"
            "\nМуты, размут, -варн — только у владельца.\n"
            "+выговор / −выговор: можно по выговорам состава; выговор, выданный владельцем, снимает только владелец.\n"
            "Варны не для состава модерации и оф. админов.\n",
        ]
    elif role_key == "moderator" or official_other:
        rk_label = (
            PROJECT_ROLE_LABELS.get(role_key, "Состав модерации")
            if role_key == "moderator"
            else "Официальный администратор"
        )
        lines += _moderator_staff_help_lines(f"Ваш ранг: {rk_label}")
    elif role_key == "sponsor":
        lines += [
            "\nВаш ранг: 💎 СПОНСОР",
            "\n\nОтдельная роль поддержки проекта. Админ-команд нет; служебный баланс — при начислениях !выдать от владельца (по правилам бота).",
        ]
    else:
        lines += ["\nДля вашего ранга админ-команд нет."]
    return "".join(lines)


def _is_admin_user(user_id):
    try:
        uid = int(user_id)
        if uid == int(ADMIN_ID):
            return True
        if _is_official_admin_id(uid):
            return True
        return _get_project_role_key(uid) in (
            "deputy_owner",
            "moderator",
        )
    except Exception:
        return False


def _is_trainee_user(user_id):
    return False


def _is_moderation_staff(user_id):
    try:
        uid = int(user_id)
    except Exception:
        return False
    return _is_admin_user(uid)


def _can_use_admin_chat_mod_features(user_id):
    """Кнопки/команды модер-меню в админ-беседе: состав + владелец (admin_id / group_owner_id)."""
    try:
        uid = int(user_id)
    except (TypeError, ValueError):
        return False
    if _is_moderation_staff(uid):
        return True
    if _is_owner(uid):
        return True
    try:
        if uid == int(GROUP_OWNER_ID):
            return True
    except (TypeError, ValueError):
        pass
    return False


def _receives_staff_grant_balance(user_id):
    """Начисления !выдать на служебный баланс (нельзя вывести, можно переводить)."""
    try:
        uid = int(user_id)
    except Exception:
        return False
    if _is_moderation_staff(uid):
        return True
    k = _get_project_role_key(uid)
    return k == "sponsor"


def _role_tenure_text(user_id):
    try:
        cursor.execute("SELECT COALESCE(role_assigned_at, 0) FROM users WHERE user_id = ?", (int(user_id),))
        row = cursor.fetchone()
        ts = float((row[0] if row else 0) or 0)
    except Exception:
        ts = 0
    if ts <= 0:
        return "неизвестно"
    delta = int(max(0, time.time() - ts))
    days = delta // 86400
    hours = (delta % 86400) // 3600
    if days > 0:
        return f"{days} дн. {hours} ч."
    mins = (delta % 3600) // 60
    return f"{hours} ч. {mins} мин."


def _close_expired_support_questions():
    """Автозакрытие обращений без ответа спустя 3 часа."""
    try:
        cutoff = float(time.time() - 3 * 3600)
        cursor.execute(
            "SELECT id, user_id FROM support_questions "
            "WHERE status IN ('new', 'in_progress') AND created_at <= ?",
            (cutoff,),
        )
        rows = cursor.fetchall() or []
        if not rows:
            return
        for qid, uid in rows:
            cursor.execute(
                "UPDATE support_questions SET status = 'closed_timeout' WHERE id = ? AND status IN ('new', 'in_progress')",
                (int(qid),),
            )
            send_msg(
                int(uid),
                f"⏱ Обращение #{int(qid)} закрыто автоматически: прошло 3 часа без ответа модерации.",
                get_main_kb(),
            )
        db.commit()
    except Exception:
        pass


def get_ask_question_admin_kb(question_id):
    kb = VkKeyboard(inline=True)
    kb.add_callback_button(
        "Ответить",
        color=VkKeyboardColor.PRIMARY,
        payload={"cmd": "mod_answer_question", "qid": int(question_id)},
    )
    return kb


def get_moderator_info_kb(user_id, has_public_id, for_admin_chat=False):
    kb = VkKeyboard(inline=True)
    if not has_public_id:
        kb.add_callback_button(
            "Установить айди",
            color=VkKeyboardColor.POSITIVE,
            payload={"cmd": "mod_set_public_id", "uid": int(user_id)},
        )
    if for_admin_chat:
        if not has_public_id:
            kb.add_line()
        kb.add_callback_button(
            "🔄 Обновить меню",
            color=VkKeyboardColor.SECONDARY,
            payload={"cmd": "mod_menu_refresh", "uid": int(user_id)},
        )
    return kb


def _is_steal_command_text(text):
    return False


PROFILE_CHAT_CMD = 'open_profile'
RESTRICTED_KLAD_CMD = 'klad_button'
RESTRICTED_TOPS_MENU_CMD = 'show_top_menu'
RESTRICTED_EVENT_INFO_CMD = 'restricted_event_info'
CASINO_MENU_CMD = 'casino_menu'
CASINO_MAX_BET = 5_000_000_000_000  # 5мм
CASINO_MIN_BET = 1
CASINO_DEFAULT_BET = 10
# Нейтральный бросок (prev нет): от ~50% на копейках до CASINO_WIN_P_MAX_STAKE на полной 5мм.
# Раньше было max(5%, 0.5−0.45·(ставка/max)) — на 5мм получалось ровно 5%, слишком уныло; шкала теперь по [MIN..MAX].
CASINO_WIN_P_MIN_STAKE = 0.50
CASINO_WIN_P_MAX_STAKE = 0.08
CASINO_COOLDOWN_SEC = 60
# После выигрыша следующий бросок: доля «удачи» (повторный выигрыш), остальное — неудача (60%).
CASINO_AFTER_WIN_NEXT_WIN_P = 0.40
# При наличных > 7мм базовый шанс (нейтральный бросок) дополнительно снижается.
CASINO_RICH_BALANCE_THRESHOLD = 7_000_000_000_000  # 7мм
CASINO_RICH_WIN_P_MULT = 0.62
CASINO_RICH_WIN_P_FLOOR = 0.035
CASINO_SYMBOLS = ('🍕', '🍇', '🍒', '🍋', '⭐', '💎', '🍀')


def _restricted_chat_allowed(message, text, payload_cmd):
    """В беседах разрешены профиль, топы и базовые пользовательские команды."""
    s = _strip_club_prefix_raw(text)
    if re.match(r"^\s*!проверка\b", s, re.IGNORECASE):
        return True
    if re.match(r"^\s*!(?:сбор|снять|выдать)\b", s, re.IGNORECASE):
        return True
    parts = s.split(None, 1)
    if payload_cmd in (
        PROFILE_CHAT_CMD,
        'admin_op_banlist',
        'admin_promolist',
        RESTRICTED_TOPS_MENU_CMD,
        RESTRICTED_EVENT_INFO_CMD,
        'top_refs',
        'top_balance',
        'top_spam',
        'top_donations',
        'top_withdrawals',
        'transfer_confirm',
        'transfer_cancel',
        'help_commands',
        'anti_bot_send_captcha',
    ):
        return True
    _nc = _normalize_chat_command(text)
    _mute_tok = _chat_mute_cmd_first_token(text)
    _unmute_tok = _nc.strip().split(None, 1)[0] if _nc.strip() else ""
    if _mute_tok == "мут" or _unmute_tok in ("-мут", "размут") or _nc in (
        'топ',
        'топ смс',
        'топспам',
        'топ спам',
        'топ пожертвований',
        'топ пожертвование',
        'топ выводов',
        'топ вывод',
        'помощь',
        'help',
        'команды',
        'меню команд',
        '-варн',
        'кик',
    ) or _nc.startswith('кик '):
        return True
    if _is_promo_activation_text(text):
        return True
    if _is_steal_command_text(text):
        return True
    if _is_heist_command_text(text):
        return True
    if s.lower().startswith('перевод '):
        return True
    if s and s.lower() in ('профиль', 'я', 'б', 'баланс'):
        return True
    if len(parts) == 2 and parts[0].lower() in ('проф', 'профиль', 'prof'):
        return True
    return False


def _restricted_profile_subject_uid(message, text, payload_cmd, viewer_id):
    """Чей профиль показать в беседе RESTRICTED_CHAT_PEER_ID. (uid, err_text_or_None)."""
    if payload_cmd == PROFILE_CHAT_CMD:
        return viewer_id, None
    rm = message.get('reply_message') if isinstance(message, dict) else None
    if rm:
        rid = rm.get('from_id')
        try:
            if rid is not None and int(rid) > 0:
                return int(rid), None
        except (TypeError, ValueError):
            pass
    s = _strip_club_prefix_raw(text)
    parts = s.split(None, 1)
    if len(parts) == 2 and parts[0].lower() in ('проф', 'профиль', 'prof'):
        tid = get_id_by_domain(parts[1])
        if not tid:
            return None, 'Не удалось найти юзера.'
        return tid, None
    return viewer_id, None


def _is_profile_request_chat(text, payload_cmd):
    if payload_cmd == PROFILE_CHAT_CMD:
        return True
    s = _strip_club_prefix_raw(text)
    if s and s.lower() in ('профиль', 'я', 'б', 'баланс'):
        return True
    parts = s.split(None, 1)
    return len(parts) == 2 and parts[0].lower() in ('проф', 'профиль', 'prof')


def _vk_reply_to_json(peer_id, conversation_message_id):
    try:
        return json.dumps(
            {'peer_id': int(peer_id), 'conversation_message_id': int(conversation_message_id)}
        )
    except (TypeError, ValueError):
        return None


def send_msg_with_reply_to_cmid(peer_id, text, reply_conversation_message_id, keyboard=None, disable_mentions=False):
    """Отправка в чат с ответом на сообщение (conversation_message_id)."""
    post = {'peer_id': int(peer_id), 'message': text, 'random_id': get_random_id()}
    if keyboard is not None:
        post['keyboard'] = keyboard if isinstance(keyboard, str) else keyboard.get_keyboard()
    if disable_mentions:
        post['disable_mentions'] = 1
    try:
        cmid = int(reply_conversation_message_id)
    except (TypeError, ValueError):
        cmid = 0
    if cmid > 0:
        rj = _vk_reply_to_json(peer_id, cmid)
        if rj:
            post['reply_to'] = rj
    try:
        return int(vk.messages.send(**post) or 0)
    except Exception:
        return 0


def _admin_rp_strip_emphasis(s):
    s = (s or '').strip()
    if len(s) >= 2 and s.startswith('*') and s.endswith('*'):
        s = s[1:-1].strip()
    return s


def _admin_rp_first_verb_past_masc(word):
    """Грубое «инфинитив → прош. м.р.» только для первого слова (для /me в админ-чате)."""
    if not word:
        return word
    w = word
    lw = word.lower()
    special = {
        'идти': 'пошёл',
        'ехать': 'поехал',
        'есть': 'ел',
        'быть': 'был',
        'дать': 'дал',
    }
    if lw in special:
        return special[lw]
    pairs = (
        ('ировать', 'ировал'),
        ('овать', 'овал'),
        ('евать', 'евал'),
        ('ебать', 'ебал'),
        ('ать', 'ал'),
        ('ять', 'ял'),
        ('еть', 'ел'),
        ('нуть', 'нул'),
        ('уть', 'ул'),
        ('ить', 'ил'),
        ('ыть', 'ыл'),
    )
    for suf, repl in pairs:
        if lw.endswith(suf) and len(lw) > len(suf) + 1:
            return w[: -len(suf)] + repl
    return w


def _admin_chat_try_me_rp(event, user_id, reply_peer, text, payload_cmd, message_cmid):
    """RP /me в админ-беседе. True — сообщение обработано (дальше process_message не идём)."""
    try:
        if int(reply_peer) != int(ADMIN_CHAT_PEER_ID):
            return False
    except (TypeError, ValueError):
        return False
    if not _can_use_admin_chat_mod_features(user_id):
        return False
    if payload_cmd:
        return False
    s_me = _strip_club_prefix_raw(text).strip()
    s_me = s_me.replace("\uff0f", "/").replace("\u2215", "/")
    m_me = re.match(r"^/me\s+(.+)$", s_me, re.IGNORECASE | re.DOTALL)
    if not m_me:
        return False
    action_raw = _admin_rp_strip_emphasis(m_me.group(1).strip())
    if not action_raw:
        send_msg(
            reply_peer,
            "Укажите действие: /me текст (ответом на сообщение).\n"
            "Пример: ответить на сообщение и написать «/me трахнуть без смазки».",
            kb_for_peer(reply_peer),
        )
        return True
    msg_obj_me = event.obj.message
    rm_me = msg_obj_me.get("reply_message") if isinstance(msg_obj_me, dict) else None
    if not rm_me:
        send_msg(
            reply_peer,
            "Команда /me: ответьте на сообщение того, к кому относится действие.",
            kb_for_peer(reply_peer),
        )
        return True
    try:
        target_uid = int(rm_me.get("from_id") or 0)
    except (TypeError, ValueError):
        target_uid = 0
    if target_uid <= 0:
        send_msg(reply_peer, "Не удалось определить пользователя из ответа.", kb_for_peer(reply_peer))
        return True
    parts_act = action_raw.split(None, 1)
    first_w = parts_act[0]
    tail = parts_act[1] if len(parts_act) > 1 else ""
    past_phrase = _admin_rp_first_verb_past_masc(first_w)
    if tail:
        past_phrase = f"{past_phrase} {tail}".strip()
    who = get_user_mention_with_name(user_id)
    whom = get_user_mention_with_name(target_uid)
    line = f"🎭 {who} {past_phrase} {whom}"
    try:
        tgt_cmid = int(rm_me.get("conversation_message_id") or 0)
    except (TypeError, ValueError):
        tgt_cmid = 0
    sent = 0
    if tgt_cmid > 0:
        sent = int(send_msg_with_reply_to_cmid(reply_peer, line, tgt_cmid, kb_for_peer(reply_peer)) or 0)
    if not sent:
        send_msg(reply_peer, line, kb_for_peer(reply_peer))
    return True


def send_profile_card(reply_peer, profile_user_id, viewer_user_id=None, reply_to_cmid=None):
    """Мини-профиль без картинок и внешних данных."""
    if viewer_user_id is None:
        viewer_user_id = profile_user_id
    username = get_user_name(profile_user_id)
    profile_mention = f"@id{int(profile_user_id)}"
    _, local_pet_name, _ = get_local_pet_info(profile_user_id)
    role_label = _project_role_label_with_hashtag_for_user(profile_user_id)
    topper_label = "Топер" if _has_top3_anywhere(profile_user_id) else ""
    now_ts = time.time()
    cursor.execute(
        "SELECT COALESCE(balance, 0), COALESCE(staff_balance, 0), "
        "COALESCE(click_boost_until, 0), COALESCE(tax_fast_until, 0), "
        "COALESCE(steal_fast_until, 0), COALESCE(steal_shield_until, 0), COALESCE(registered_at, 0), "
        "COALESCE(is_twin, 0) "
        "FROM users WHERE user_id = ?",
        (int(profile_user_id),),
    )
    prow = cursor.fetchone() or (0, 0, 0, 0, 0, 0, 0, 0)
    reg_bot_ts = float(prow[6] or 0)
    is_twin_profile = int(prow[7] or 0)
    reg_bot_line = (
        f"📅 В боте с: {datetime.fromtimestamp(reg_bot_ts, tz=timezone.utc).strftime('%d.%m.%Y')}\n"
        if reg_bot_ts > 0
        else ""
    )
    game_balance = int(prow[0] or 0)
    staff_balance = int(prow[1] or 0)
    repost_locked = _repost_locked_amount(profile_user_id, now_ts=now_ts)
    purchases = []
    if float(prow[2] or 0) > now_ts:
        purchases.append(f"Клик +{format_short(get_economy_click_boost_bonus())}")
    if float(prow[4] or 0) > now_ts:
        purchases.append("Ускорение атаки")
    if float(prow[5] or 0) > now_ts:
        purchases.append("Щит от атак")
    purchases_text = "\n".join(purchases) if purchases else "Нет активных"
    header = ""
    if _is_multichat_peer(reply_peer) and profile_user_id != viewer_user_id:
        header = "👀 Профиль игрока\n\n"
    msg = (
        header
        + f"👤 {username}\n"
        + f"🆔 ID: {profile_mention}\n"
        + reg_bot_line
        + f"🎖 Роль: {role_label}\n"
        + (f"{topper_label}\n" if topper_label else "")
        + (f"🏷 Метка: твинк — вывод средств недоступен\n" if is_twin_profile else "")
        + f"🐾 Питомец: {local_pet_name}\n\n"
        + "💳 Финансы\n"
        + f"Наличные: {format_click(game_balance)}$\n"
        + (
            f"Служебные (только переводы, без вывода): {format_click(staff_balance)}$\n"
            if staff_balance > 0
            else ""
        )
        + f"Удержано: {format_click(repost_locked)}$\n"
        + f"Итого: {format_click(game_balance + staff_balance)}$\n\n"
        + "🛒 Активные покупки\n"
        + f"{purchases_text}"
    )
    if _is_multichat_peer(reply_peer):
        kb_chat = kb_for_peer(reply_peer)
        post = {
            'peer_id': int(reply_peer),
            'message': msg,
            'random_id': get_random_id(),
            'keyboard': kb_chat.get_keyboard(),
        }
        rj = _vk_reply_to_json(reply_peer, reply_to_cmid) if reply_to_cmid is not None else None
        if rj:
            post['reply_to'] = rj
        try:
            vk.messages.send(**post)
        except Exception:
            try:
                fb = {
                    'peer_id': int(reply_peer),
                    'message': msg,
                    'random_id': get_random_id(),
                    'keyboard': kb_chat.get_keyboard(),
                }
                vk.messages.send(**fb)
            except Exception:
                try:
                    vk.messages.send(
                        peer_id=int(reply_peer),
                        message=msg,
                        random_id=get_random_id(),
                        keyboard=kb_chat.get_keyboard(),
                    )
                except Exception:
                    pass
    else:
        send_msg(reply_peer, msg, profile_kb_for_peer(reply_peer))


def kb_for_peer(peer_id):
    if _is_multichat_peer(peer_id):
        kb = VkKeyboard(one_time=False)
        if int(peer_id) == int(ADMIN_CHAT_PEER_ID):
            kb.add_button('Банлист', color=VkKeyboardColor.SECONDARY, payload={'cmd': 'admin_op_banlist'})
            kb.add_button('Промолист', color=VkKeyboardColor.SECONDARY, payload={'cmd': 'admin_promolist'})
            kb.add_button('Профиль', color=VkKeyboardColor.PRIMARY, payload={'cmd': PROFILE_CHAT_CMD})
            return kb
        if int(peer_id) == int(RESTRICTED_CHAT_PEER_ID):
            kb.add_button('Ивент', color=VkKeyboardColor.SECONDARY, payload={'cmd': RESTRICTED_EVENT_INFO_CMD})
            kb.add_line()
            kb.add_button('Профиль', color=VkKeyboardColor.PRIMARY, payload={'cmd': PROFILE_CHAT_CMD})
            kb.add_button('Топы', color=VkKeyboardColor.SECONDARY, payload={'cmd': RESTRICTED_TOPS_MENU_CMD})
            kb.add_button('Помощь', color=VkKeyboardColor.SECONDARY)
            return kb
        kb.add_button('Профиль', color=VkKeyboardColor.PRIMARY, payload={'cmd': PROFILE_CHAT_CMD})
        kb.add_button('Топы', color=VkKeyboardColor.SECONDARY, payload={'cmd': RESTRICTED_TOPS_MENU_CMD})
        kb.add_button('Помощь', color=VkKeyboardColor.SECONDARY)
        return kb
    return get_main_kb()


def profile_kb_for_peer(peer_id):
    if _is_multichat_peer(peer_id):
        return None
    return get_profile_kb()


def get_pet_kb(balance, fed, pet_power, show_info=True, owner_user_id=None, boost_active=False):
    kb = VkKeyboard(inline=True)
    feed_portion = get_effective_feed_portion(boost_active=boost_active)
    fixed_all = int(get_economy_feed_all_cost())

    if fed >= 100:
        cost_str = "Макс."
    elif balance < fixed_all:
        cost_str = f"нужно {format_click(fixed_all)}$"
    else:
        cost_str = f"{format_click(fixed_all)}$"

    kb.add_button(f'Покормить за все деньги ({cost_str})', color=VkKeyboardColor.NEGATIVE, payload={'cmd': 'feed_all'})
    kb.add_line()
    if is_pet_max_level(pet_power):
        kb.add_button(
            f'Улучшить питомца (макс. {MAX_PET_LEVEL})',
            color=VkKeyboardColor.SECONDARY,
            payload={'cmd': 'pet_upgrade'},
        )
    else:
        kb.add_button(
            f'Улучшить питомца ({format_short(pet_upgrade_cost(pet_power))}$)',
            color=VkKeyboardColor.POSITIVE,
            payload={'cmd': 'pet_upgrade'},
        )
    
    if show_info:
        kb.add_line()
        pet_info_payload = {'cmd': 'pet_info'}
        if owner_user_id is not None:
            pet_info_payload['owner_id'] = int(owner_user_id)
        kb.add_callback_button('Информация', color=VkKeyboardColor.SECONDARY, payload=pet_info_payload)
        
    return kb

def get_captcha_kb(captcha_token):
    kb = VkKeyboard(inline=True)
    buttons = [
        ('✅', VkKeyboardColor.POSITIVE, 1),
        ('❌', VkKeyboardColor.NEGATIVE, 0),
        ('❌', VkKeyboardColor.NEGATIVE, 0),
        ('❌', VkKeyboardColor.NEGATIVE, 0),
    ]
    random.shuffle(buttons)
    for label, color, ok_v in buttons:
        kb.add_button(
            label,
            color=color,
            payload={'cmd': 'captcha_click', 'ok': int(ok_v), 't': str(captcha_token), 'nonce': random.randint(1000, 999999)},
        )
    return kb


def _delete_captcha_message_if_any(user_id):
    try:
        cursor.execute("SELECT COALESCE(captcha_message_id, 0) FROM users WHERE user_id = ?", (int(user_id),))
        row = cursor.fetchone()
        mid = int((row[0] if row else 0) or 0)
        if mid > 0:
            try:
                vk.messages.delete(message_ids=str(mid), delete_for_all=1)
            except Exception:
                pass
        update_user(user_id, 'captcha_message_id', 0)
    except Exception:
        pass


def _user_reset_interactive_sessions_on_start(user_id):
    """Сброс режимов по «начать»/start: обычная и принудительная капча, донат, вопрос, отзыв, черновик конкурса."""
    try:
        _delete_captcha_message_if_any(user_id)
    except Exception:
        pass
    mc = random.randint(1, CAPTCHA_MESSAGES_UNTIL_MAX)
    update_user_fields(
        user_id,
        review_state=0,
        temp_review_text='',
        donation_wait_custom=0,
        donation_pending_amount=0,
        ask_question_wait=0,
        ask_question_wait_started_at=0.0,
        op_contest_draft='',
        captcha_answer=None,
        captcha_token='',
        captcha_message_id=0,
        msg_until_captcha=mc,
        forced_captcha_answer=None,
        forced_captcha_prompt='',
        forced_captcha_attempts=0,
    )
    try:
        ADMIN_FORCED_CAPTCHA_ISSUER.pop(int(user_id), None)
    except Exception:
        pass
    try:
        ANTIBOT_CAPTCHA_TRACK.pop(int(user_id), None)
    except Exception:
        pass
    return mc


def issue_captcha_challenge(user_id, reply_peer, text):
    token = secrets.token_hex(8)
    update_user(user_id, 'captcha_token', token)
    _delete_captcha_message_if_any(user_id)
    msg_id = 0
    try:
        msg_id = int(
            vk.messages.send(
                peer_id=int(reply_peer),
                message=str(text),
                keyboard=get_captcha_kb(token).get_keyboard(),
                random_id=get_random_id(),
            ) or 0
        )
    except Exception:
        send_msg(reply_peer, text, get_captcha_kb(token))
    if msg_id > 0:
        update_user(user_id, 'captcha_message_id', msg_id)

def get_admin_pay_kb(target_id, is_banned=False, withdraw_id=None):
    kb = VkKeyboard(inline=True)
    payload_pay = {'cmd': 'admin_pay', 'uid': int(target_id)}
    payload_cancel = {'cmd': 'admin_withdraw_cancel', 'uid': int(target_id)}
    if withdraw_id is not None:
        payload_pay['wid'] = int(withdraw_id)
        payload_cancel['wid'] = int(withdraw_id)
    kb.add_button('✅ Я перевел', color=VkKeyboardColor.POSITIVE, payload=payload_pay)
    kb.add_button('🛑 Отменить', color=VkKeyboardColor.SECONDARY, payload=payload_cancel)
    if is_banned:
        kb.add_line()
        payload_deny = {'cmd': 'admin_deny', 'uid': int(target_id)}
        if withdraw_id is not None:
            payload_deny['wid'] = int(withdraw_id)
        kb.add_button('❌ Отказать', color=VkKeyboardColor.NEGATIVE, payload=payload_deny)
    return kb


def _send_owner_pending_withdrawals(owner_peer_id):
    try:
        cursor.execute(
            "SELECT w.id, w.user_id, w.amount, COALESCE(u.is_banned, 0), COALESCE(u.ban_until, 0) "
            "FROM withdrawals w "
            "LEFT JOIN users u ON u.user_id = w.user_id "
            "WHERE w.status = 'Ожидает отправки' "
            "ORDER BY w.id ASC"
        )
        rows = cursor.fetchall() or []
    except Exception:
        rows = []
    if not rows:
        send_msg(owner_peer_id, "📭 Активных заявок на вывод нет.", get_main_kb())
        return
    send_msg(owner_peer_id, f"📤 Активные выводы: {len(rows)} шт.", get_main_kb())
    for wid, uid, amount, is_banned, ban_until in rows:
        uid = int(uid or 0)
        if uid <= 0:
            continue
        amount = int(amount or 0)
        is_banned_now = bool(int(is_banned or 0) == 1 or float(ban_until or 0) > time.time())
        warn_banned = "\n⚠️ ПОЛЬЗОВАТЕЛЬ В БАНЕ!" if is_banned_now else ""
        amt_line = format_withdraw_mm_rounded(amount)
        mid_dm = send_msg(
            owner_peer_id,
            f"🔔 Заявка #{int(wid)} на вывод{warn_banned}\n"
            f"Пользователь: @id{uid} ({get_user_name(uid)})\n"
            f"Сумма: {amt_line}",
            None,
        )
        _withdraw_store_dm_notify(int(wid), int(owner_peer_id), mid_dm)
        mid_cmd = send_msg(
            owner_peer_id,
            f"перевод {amount} @id{uid}",
            get_admin_pay_kb(uid, is_banned=is_banned_now, withdraw_id=int(wid)),
        )
        if mid_cmd:
            _withdraw_store_dm_cmd(int(wid), int(owner_peer_id), mid_cmd)


def _owner_restore_withdraw_board_history(limit_rows=200):
    """Восстановить историю выводов в обсуждении и актуализировать comment_id в БД."""
    if vk_user is None:
        return {"ok": False, "reason": "no_user_token"}
    lim = int(max(1, min(int(limit_rows or 200), 2000)))
    cursor.execute(
        "SELECT id, user_id, amount, comment_id, status, COALESCE(rating, ''), COALESCE(review_text, '') "
        "FROM withdrawals ORDER BY id ASC LIMIT ?",
        (lim,),
    )
    rows = cursor.fetchall() or []
    created = 0
    edited = 0
    failed = 0
    for row in rows:
        try:
            wid = int(row[0] or 0)
            uid = int(row[1] or 0)
            amount = int(row[2] or 0)
            old_comment_id = int(row[3] or 0)
            status = str(row[4] or "Ожидает отправки")
            rating = str(row[5] or "")
            review_text = str(row[6] or "")
            body = build_board_msg(uid, get_user_name(uid), amount, status, rating, review_text)

            new_comment_id = 0
            if old_comment_id > 0:
                try:
                    vk_user.board.editComment(
                        group_id=GROUP_ID,
                        topic_id=57395405,
                        comment_id=old_comment_id,
                        message=body,
                    )
                    new_comment_id = old_comment_id
                    edited += 1
                except Exception:
                    new_comment_id = 0
            if new_comment_id <= 0:
                try:
                    new_comment_id = int(
                        vk_user.board.createComment(
                            group_id=GROUP_ID,
                            topic_id=57395405,
                            message=body,
                            from_group=1,
                        )
                        or 0
                    )
                except Exception:
                    new_comment_id = 0
                if new_comment_id > 0:
                    created += 1
            if new_comment_id > 0 and new_comment_id != old_comment_id:
                cursor.execute(
                    "UPDATE withdrawals SET comment_id = ? WHERE id = ?",
                    (int(new_comment_id), int(wid)),
                )
                db.commit()
            if new_comment_id <= 0:
                failed += 1
            time.sleep(0.12)
        except Exception:
            failed += 1
    return {
        "ok": True,
        "processed": len(rows),
        "created": created,
        "edited": edited,
        "failed": failed,
        "limit": lim,
    }


def get_payout_success_kb():
    kb = VkKeyboard(inline=True)
    kb.add_openlink_button('Проверить', link='https://vk.ru/write-221392393?ref=682039325')
    kb.add_line()
    kb.add_button('Написать отзыв', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'write_review'})
    return kb

def get_rating_kb():
    kb = VkKeyboard(inline=True)
    kb.add_button('👍', color=VkKeyboardColor.POSITIVE, payload={'cmd': 'rate_good'})
    kb.add_button('👎', color=VkKeyboardColor.NEGATIVE, payload={'cmd': 'rate_bad'})
    return kb

def get_about_kb():
    kb = VkKeyboard(inline=True)
    kb.add_openlink_button('Выводы', link='https://vk.com/topic-237333137_57395405')
    return kb

def get_ref_kb():
    kb = VkKeyboard(inline=True)
    kb.add_button('Ограбление', color=VkKeyboardColor.NEGATIVE, payload={'cmd': 'heist_run'})
    kb.add_line()
    kb.add_button('Пост для рефки', color=VkKeyboardColor.PRIMARY, payload={'cmd': 'ref_post'})
    return kb


def get_add_to_chat_kb():
    kb = VkKeyboard(inline=True)
    if KLAD_APP_URL:
        kb.add_openlink_button('Добавить', link=KLAD_APP_URL)
    return kb


def get_promo_join_chat_kb():
    kb = VkKeyboard(inline=True)
    kb.add_openlink_button('Вступить', link='https://vk.me/join/zNURw9NhGPPnP3avIM7TQ2CiC2/N7vg_JuA=')
    return kb


def build_ref_post_text(user_id):
    ref_link = f"https://vk.ru/write-{GROUP_ID}?ref={user_id}"
    try:
        cursor.execute("SELECT COUNT(*) FROM users WHERE is_registered = 1")
        users_count = int(cursor.fetchone()[0] or 0)
    except Exception:
        users_count = 0
    try:
        cursor.execute(
            "SELECT COALESCE(SUM(amount), 0) FROM withdrawals WHERE status = 'Успешно выполнена'"
        )
        paid_total = int(cursor.fetchone()[0] or 0)
    except Exception:
        paid_total = 0
    users_count_floor = max(0, int(math.floor(users_count)))
    paid_total_mm_ceil = max(0, int(math.ceil(paid_total / 1_000_000_000_000)))
    return (
        f"{ref_link}\n\n"
        f"Новый бот где можно заработать деньги и выводить всё в бота нищего! "
        f"Бот уже имеет аудиторию свыше {format_balance(users_count_floor)} человек, "
        f"и выводов на сумму свыше {paid_total_mm_ceil} мм. "
        f"Покликай и ты, и получай пассивный доход сидя на диване!"
    )


def process_wall_reply_delete(event):
    """Если удалили комментарий, с которого была награда — снимаем запись и деньги с баланса."""
    try:
        obj = event.object
        raw_po = obj.get('post_owner_id')
        if raw_po is None:
            raw_po = obj.get('owner_id')
        post_owner_id = _lp_int(raw_po)
        if post_owner_id != -int(GROUP_ID):
            return
        post_id = obj.get('post_id')
        comment_id = obj.get('id') if obj.get('id') is not None else obj.get('comment_id')
        if post_id is None or comment_id is None:
            return
        post_id, comment_id = int(post_id), int(comment_id)

        local_db = sqlite3.connect(DB_PATH, check_same_thread=False, timeout=15)
        try:
            lc = local_db.cursor()
            lc.execute(
                "SELECT user_id, amount FROM wall_comment_rewards WHERE post_id = ? AND comment_id = ?",
                (post_id, comment_id),
            )
            row = lc.fetchone()
            if not row:
                return
            uid, amount = int(row[0]), int(row[1])
            lc.execute(
                "DELETE FROM wall_comment_rewards WHERE user_id = ? AND post_id = ? AND comment_id = ?",
                (uid, post_id, comment_id),
            )
            lc.execute(
                "UPDATE users SET balance = MAX(0, balance - ?) WHERE user_id = ?",
                (amount, uid),
            )
            local_db.commit()
            send_msg(
                uid,
                f"Комментарий к посту удалён — награда отменена, с баланса списано {format_click(amount)}$.",
                get_main_kb(),
            )
        finally:
            local_db.close()
    except Exception:
        pass


def process_wall_reply(event):
    """Награда за комментарии под постом группы: до 5 наград на один пост."""
    try:
        obj = event.object
        raw_po = obj.get('post_owner_id')
        if raw_po is None:
            raw_po = obj.get('owner_id')
        post_owner_id = _lp_int(raw_po)
        if post_owner_id != -int(GROUP_ID):
            return

        from_id = _lp_int(obj.get('from_id'))
        if from_id is None or from_id <= 0:
            from_id = _lp_int(obj.get('user_id'))
        if from_id is None or from_id <= 0:
            from_id = _lp_int(obj.get('author_id'))
        if from_id is None or from_id <= 0:
            return

        post_id = _lp_int(obj.get('post_id'))
        comment_id = _lp_int(obj.get('id'))
        if comment_id is None:
            comment_id = _lp_int(obj.get('comment_id'))
        ctext = (obj.get('text') or '').strip()
        if not ctext or post_id is None or comment_id is None:
            return

        from_id = int(from_id)
        post_id = int(post_id)
        comment_id = int(comment_id)

        # Только локальное соединение — глобальный cursor/db из другого потока даёт гонки, ошибки bindings и segfault.
        local_db = sqlite3.connect(DB_PATH, check_same_thread=False, timeout=15)
        try:
            lc = local_db.cursor()
            lc.execute(
                "INSERT OR IGNORE INTO users (user_id, msg_until_captcha) VALUES (?, ?)",
                (from_id, random.randint(1, CAPTCHA_MESSAGES_UNTIL_MAX)),
            )
            local_db.commit()

            lc.execute(
                "SELECT is_registered, is_banned, ban_until FROM users WHERE user_id = ?",
                (from_id,),
            )
            row = lc.fetchone()
            if not row:
                return
            is_registered, is_banned, ban_until = row[0], row[1], row[2] or 0
            if not is_registered:
                notify_wall_comment_dm_and_reply(
                    from_id,
                    post_id,
                    comment_id,
                    "Чтобы получать награды за комментарии, сначала зарегистрируйтесь в боте сообщества (откройте чат с группой и нажмите «Начать»).",
                )
                return
            if is_banned == 1 or ban_until > time.time():
                return

            lc.execute("SELECT COUNT(*) FROM wall_comment_rewards WHERE post_id = ?", (post_id,))
            already = lc.fetchone()[0] or 0
            if already >= MAX_REWARDED_COMMENTS_PER_POST:
                return

            lc.execute(
                "SELECT 1 FROM wall_comment_rewards WHERE user_id = ? AND post_id = ? AND comment_id = ?",
                (from_id, post_id, comment_id),
            )
            if lc.fetchone():
                return

            local_msg = local_comment_spam_issue(ctext)
            if local_msg:
                notify_wall_comment_dm_and_reply(from_id, post_id, comment_id, local_msg)
                return

            amount = 40 * 1_000_000_000
            try:
                lc.execute(
                    "INSERT INTO wall_comment_rewards (user_id, post_id, comment_id, amount, created) VALUES (?, ?, ?, ?, ?)",
                    (from_id, post_id, comment_id, amount, time.time()),
                )
                lc.execute(
                    "UPDATE users SET balance = balance + ? WHERE user_id = ?",
                    (amount, from_id),
                )
                local_db.commit()
            except sqlite3.IntegrityError:
                return
            new_n = already + 1
            ok_text = (
                f"💬 За комментарий начислено {format_click(amount)}$\n"
                f"Наград за этот пост: {new_n}/{MAX_REWARDED_COMMENTS_PER_POST}."
            )
            notify_wall_comment_dm_and_reply(from_id, post_id, comment_id, ok_text)
        finally:
            local_db.close()
    except Exception as e:
        print(f"[wall_comment] process_wall_reply: {e}")


# --- ОБРАБОТКА СООБЩЕНИЙ ---
def process_message(event):
    global LAST_SUPPORT_CLEANUP_TS, _menu_keyboard_user_id, TECH_WORKS_ENABLED
    user_id = event.obj.message['from_id']
    try:
        _menu_keyboard_user_id = int(user_id)
    except (TypeError, ValueError):
        _menu_keyboard_user_id = None
    text = event.obj.message['text']
    _raw_peer = event.obj.message.get('peer_id')
    reply_peer = int(_raw_peer) if _raw_peer is not None else int(user_id)
    message_cmid = int(event.obj.message.get('conversation_message_id') or 0)
    now_ts = time.time()
    if (now_ts - float(LAST_SUPPORT_CLEANUP_TS or 0)) >= 60:
        _close_expired_support_questions()
        LAST_SUPPORT_CLEANUP_TS = now_ts

    _raw_payload = event.obj.message.get('payload')
    payload_str = _raw_payload if isinstance(_raw_payload, str) else ""
    payload_cmd = ""
    payload_uid = None
    payload_wid = None
    payload_data = {}
    if isinstance(_raw_payload, dict):
        payload_data = _raw_payload
        payload_cmd = (payload_data.get('cmd') or '') or ''
        payload_uid = payload_data.get('uid', None)
        payload_wid = payload_data.get('wid', None)
    elif payload_str:
        try:
            payload_data = json.loads(payload_str)
            payload_cmd = (payload_data.get('cmd') or '') or ''
            payload_uid = payload_data.get('uid', None)
            payload_wid = payload_data.get('wid', None)
        except Exception:
            pass
    if _is_multichat_peer(reply_peer) and payload_cmd:
        try:
            payload_owner_id = int(payload_data.get('owner_id') or 0)
        except Exception:
            payload_owner_id = 0
        if payload_owner_id and payload_owner_id != int(user_id):
            return

    _raw_cmd = _normalize_chat_command(text)
    if not payload_cmd and _is_owner(user_id) and _raw_cmd in ("on", "off"):
        TECH_WORKS_ENABLED = (_raw_cmd == "on")
        send_msg(
            reply_peer,
            "🛠 Техработы включены. Текстовые ответы пользователям отключены."
            if TECH_WORKS_ENABLED
            else "✅ Техработы выключены. Бот отвечает в обычном режиме.",
            kb_for_peer(reply_peer),
        )
        return

    if TECH_WORKS_ENABLED and not _is_owner(user_id):
        return

    if _abort_public_multichat_admin_spam(reply_peer, text, payload_cmd, user_id):
        return

    user, is_new_user = get_user(user_id)
    try:
        _official_chat_ai_track_message(event, user_id, reply_peer, text)
    except Exception:
        pass
    (
        _,
        balance,
        energy,
        fed,
        is_registered,
        is_banned_db,
        captcha_answer,
        last_clicks,
        last_click_timestamp,
        review_state,
        temp_review_text,
        ban_until,
        msg_until_captcha,
        click_boost_until,
        last_tax_collect,
        tax_fast_until,
        promo_click_bonus_percent,
        promo_click_bonus_until,
        _registered_at_ts,
        is_twin_db,
    ) = user[:20]
    cursor.execute("SELECT COALESCE(spam_mute_until, 0) FROM users WHERE user_id = ?", (user_id,))
    _sm_row = cursor.fetchone()
    spam_mute_until = float((_sm_row[0] if _sm_row else 0) or 0)
    cursor.execute(
        "SELECT forced_captcha_answer, COALESCE(forced_captcha_prompt, ''), COALESCE(forced_captcha_attempts, 0) "
        "FROM users WHERE user_id = ?",
        (user_id,),
    )
    _fc_row = cursor.fetchone()
    forced_captcha_answer = _fc_row[0] if _fc_row else None
    forced_captcha_prompt = (_fc_row[1] if _fc_row else "") or ""
    forced_captcha_attempts = int((_fc_row[2] if _fc_row else 0) or 0)
    cursor.execute(
        "SELECT COALESCE(steal_fast_until, 0), COALESCE(steal_shield_until, 0) FROM users WHERE user_id = ?",
        (user_id,),
    )
    _steal_row = cursor.fetchone()
    steal_fast_until = float((_steal_row[0] if _steal_row else 0) or 0)
    steal_shield_until = float((_steal_row[1] if _steal_row else 0) or 0)
    cursor.execute("SELECT COALESCE(heist_jail_until, 0) FROM users WHERE user_id = ?", (user_id,))
    _hj_row = cursor.fetchone()
    heist_jail_until = float((_hj_row[0] if _hj_row else 0) or 0)
    cursor.execute(
        "SELECT COALESCE(donation_wait_custom, 0), COALESCE(donation_pending_amount, 0), COALESCE(donated_total, 0) "
        "FROM users WHERE user_id = ?",
        (user_id,),
    )
    _don_row = cursor.fetchone() or (0, 0, 0)
    donation_wait_custom = int(_don_row[0] or 0)
    donation_pending_amount = int(_don_row[1] or 0)
    donated_total = int(_don_row[2] or 0)

    if is_new_user:
        send_msg(reply_peer, "\u2060", None, attachment=sticker_attachment(STICKER_NEW_USER_ID))

    pet_id_me, pet_name_me, pet_power_me = get_local_pet_info(user_id)

    ref_str = event.obj.message.get('ref')
    if not ref_str and payload_str:
        try:
            p_data = json.loads(payload_str)
            if 'ref' in p_data: ref_str = str(p_data['ref'])
        except: pass

    if ref_str and ref_str.isdigit() and not is_registered:
        ref_id = int(ref_str)
        if ref_id != user_id: update_user(user_id, 'pending_referrer', ref_id)

    is_banned = (is_banned_db == 1) or (ban_until > time.time())
    cursor.execute(
        "SELECT COALESCE(chat_banned, 0), COALESCE(chat_ban_until, 0) FROM users WHERE user_id = ?",
        (user_id,),
    )
    _chatban_row = cursor.fetchone() or (0, 0)
    is_chat_ban_active = int(_chatban_row[0] or 0) == 1 or float(_chatban_row[1] or 0) > time.time()
    restricted_peer_blocked = (
        is_banned if not _is_multichat_peer(reply_peer) else (is_banned or is_chat_ban_active)
    )
    is_spam_muted = spam_mute_until > time.time()

    # «начать»/start — сброс режимов ДО принудительной капчи и галочки, иначе сообщение не доходило до сброса
    _cmd_start = _normalize_chat_command(text)
    if _cmd_start in ('начать', 'start') and not payload_cmd:
        mc = _user_reset_interactive_sessions_on_start(user_id)
        captcha_answer = None
        review_state = 0
        donation_wait_custom = 0
        donation_pending_amount = 0
        msg_until_captcha = mc
        forced_captcha_answer = None
        forced_captcha_prompt = ''
        forced_captcha_attempts = 0

    # Принудительная капча (автоматизация): ответ только в ЛС; в беседах не блокируем
    if forced_captcha_answer is not None and user_id != ADMIN_ID and not _is_multichat_peer(reply_peer):
        raw_answer = _strip_club_prefix_raw(text).strip()
        try:
            user_answer = int(raw_answer)
            is_correct = user_answer == int(forced_captcha_answer)
        except Exception:
            is_correct = False
        if is_correct:
            update_user_fields(user_id, forced_captcha_answer=None, forced_captcha_prompt='', forced_captcha_attempts=0)
            send_msg(reply_peer, "✅ Капча пройдена. Доступ к командам восстановлен.", kb_for_peer(reply_peer))
            _cap_issuer = ADMIN_FORCED_CAPTCHA_ISSUER.pop(int(user_id), None)
            if _cap_issuer is not None:
                send_admin_chat_log(
                    f"[КАПЧА] ✅ {get_user_mention_with_name(user_id)} прошёл проверку.\n"
                    f"Инициатор: {get_user_mention_with_name(_cap_issuer)}"
                )
            tr = ANTIBOT_CAPTCHA_TRACK.get(int(user_id))
            if tr and int(tr.get("peer_id") or 0) > 0 and int(tr.get("cmid") or 0) > 0:
                try:
                    vk.messages.edit(
                        peer_id=int(tr["peer_id"]),
                        conversation_message_id=int(tr["cmid"]),
                        message=f"✅ [АНТИБОТ] Пользователь {get_user_mention_with_name(user_id)} прошел капчу.",
                        keyboard='{"inline":true,"buttons":[]}',
                    )
                except Exception:
                    pass
                ANTIBOT_CAPTCHA_TRACK.pop(int(user_id), None)
            return
        forced_captcha_attempts += 1
        update_user(user_id, 'forced_captcha_attempts', forced_captcha_attempts)
        if forced_captcha_attempts >= 3:
            ban_to = time.time() + 30 * 60
            update_user_fields(
                user_id,
                ban_until=ban_to,
                forced_captcha_answer=None,
                forced_captcha_prompt='',
                forced_captcha_attempts=0,
            )
            _log_ban_event(
                user_id=user_id,
                reason="Бан за непрохождение принудительной капчи (подозрение на автоматизацию)",
                until_ts=ban_to,
                issued_by=0,
                source_chat=reply_peer,
            )
            send_msg(
                reply_peer,
                "⛔ Вы не прошли капчу за 3 попытки.\nБан на 30 минут за подозрение на автоматизацию.",
                kb_for_peer(reply_peer),
            )
            _cap_issuer_fail = ADMIN_FORCED_CAPTCHA_ISSUER.pop(int(user_id), None)
            if _cap_issuer_fail is not None:
                send_admin_chat_log(
                    f"[КАПЧА] ⛔ {get_user_mention_with_name(user_id)} не прошёл капчу (3 попытки, бан 30 мин).\n"
                    f"Инициатор проверки: {get_user_mention_with_name(_cap_issuer_fail)}"
                )
            tr = ANTIBOT_CAPTCHA_TRACK.get(int(user_id))
            if tr and int(tr.get("peer_id") or 0) > 0:
                send_msg(
                    int(tr["peer_id"]),
                    f"[АНТИБОТ] Пользователь {get_user_mention_with_name(user_id)} не прошел капчу.",
                    kb_for_peer(int(tr["peer_id"])),
                )
                ANTIBOT_CAPTCHA_TRACK.pop(int(user_id), None)
        else:
            left = 3 - forced_captcha_attempts
            send_msg(
                reply_peer,
                f"❌ Неверный ответ. Осталось попыток: {left}.\n{forced_captcha_prompt}",
                None,
            )
        return

    if _admin_chat_try_me_rp(event, user_id, reply_peer, text, payload_cmd, message_cmid):
        return

    if is_registered and _is_multichat_peer(reply_peer) and user_id != ADMIN_ID and not is_spam_muted:
        if _check_and_apply_official_insult_mute(user_id, reply_peer, text, message_cmid=message_cmid):
            return
        _check_and_apply_chat_spam(user_id, reply_peer, text, message_cmid=message_cmid)
        cursor.execute("SELECT COALESCE(spam_mute_until, 0) FROM users WHERE user_id = ?", (user_id,))
        row_m = cursor.fetchone()
        if row_m:
            spam_mute_until = float(row_m[0] or 0)
            is_spam_muted = spam_mute_until > time.time()

    if restricted_peer_blocked and user_id != ADMIN_ID:
        if _is_multichat_peer(reply_peer) and _restricted_chat_allowed(event.obj.message, text, payload_cmd):
            pass
        elif payload_cmd not in ['withdraw', 'write_review']:
            return
    # Мут в беседе (модератор / антиспам) не блокирует использование бота в ЛС
    if is_spam_muted and user_id != ADMIN_ID and _is_multichat_peer(reply_peer):
        try:
            if int(message_cmid or 0) > 0:
                vk.messages.delete(peer_id=int(reply_peer), cmids=str(int(message_cmid)), delete_for_all=1)
        except Exception:
            pass
        send_msg_and_delete_later(
            reply_peer,
            f"⛔ Вы в муте за спам до {_format_unix_msk(spam_mute_until)}.\nКоманды временно недоступны.",
            kb_for_peer(reply_peer),
            delete_after_sec=SPAM_MUTE_BOT_NOTICE_DELETE_SEC,
        )
        return

    if int(reply_peer) == int(ADMIN_CHAT_PEER_ID) and _can_use_admin_chat_mod_features(user_id):
        if payload_cmd == 'admin_op_banlist':
            send_msg(reply_peer, _admin_op_banlist_text(), kb_for_peer(reply_peer))
            return
        if payload_cmd == 'admin_promolist' and _can_use_promolist(user_id):
            send_msg(reply_peer, promolist_admin_text(), kb_for_peer(reply_peer))
            return

    owner_cmd = _normalize_chat_command(text)
    if owner_cmd == 'id' and not _is_owner(user_id):
        send_msg(reply_peer, "Команда /id доступна только владельцу проекта.", get_main_kb())
        return
    if owner_cmd == 'op' and not (_is_owner(user_id) or _is_deputy_owner(user_id)):
        send_msg(reply_peer, "Команда /op доступна только владельцу или заместителю проекта.", get_main_kb())
        return
    if re.match(r'^\s*!выдать\b', _strip_club_prefix_raw(text), re.IGNORECASE) and not _is_owner(user_id):
        send_msg(
            reply_peer,
            "Команда доступна только владельцу проекта.\n"
            "Формат: !выдать [юзер] [сумма в $, мк или мм]",
            get_main_kb(),
        )
        return
    if re.match(r'^\s*!снять\b', _strip_club_prefix_raw(text), re.IGNORECASE) and not _is_owner(user_id):
        send_msg(
            reply_peer,
            "Команда доступна только владельцу проекта.\n"
            "Формат: !снять [юзер] [сумма в $, мк или мм]",
            get_main_kb(),
        )
        return
    if re.match(r'^\s*!сбор\b', _strip_club_prefix_raw(text), re.IGNORECASE) and not _is_owner(user_id):
        send_msg(
            reply_peer,
            "Команда доступна только владельцу проекта.\n"
            "Формат: !сбор [сумма] (например: !сбор 10мм)",
            get_main_kb(),
        )
        return
    if re.match(r'^\s*!удалитьпромо\b', _strip_club_prefix_raw(text), re.IGNORECASE) and not _is_owner(user_id):
        send_msg(
            reply_peer,
            "Команда доступна только владельцу проекта.\n"
            "Формат: !удалитьпромо [код]",
            get_main_kb(),
        )
        return
    if re.match(r'^\s*!-?твинк\b', _strip_club_prefix_raw(text), re.IGNORECASE) and not _is_owner(user_id):
        send_msg(
            reply_peer,
            "Команда !твинк / !-твинк доступна только владельцу проекта.",
            get_main_kb(),
        )
        return
    if re.match(r'^\s*!-модерденьги\s*$', _strip_club_prefix_raw(text), re.IGNORECASE) and not _is_owner(user_id):
        send_msg(
            reply_peer,
            "Команда !-модерденьги доступна только владельцу проекта.",
            get_main_kb(),
        )
        return
    if (
        (
            re.match(r'^\s*!настройки\s*$', _strip_club_prefix_raw(text), re.IGNORECASE)
            or re.match(r'^\s*!ui[\+\-]', _strip_club_prefix_raw(text), re.IGNORECASE)
            or re.match(r'^\s*!опвывод', _strip_club_prefix_raw(text), re.IGNORECASE)
        )
        and not _is_owner(user_id)
    ):
        send_msg(reply_peer, "Команда доступна только владельцу проекта.", get_main_kb())
        return

    if (_is_owner(user_id) or _is_deputy_owner(user_id)) and _owner_admin_allowed_in_this_peer(reply_peer, text):
        if _op_contest_process_owner(
            user_id, reply_peer, text, payload_cmd, payload_data, contest_edit_cmid=message_cmid
        ):
            return
        if re.match(r"^\s*/even1\s*$", _strip_club_prefix_raw(text), re.IGNORECASE):
            _run_even1_event_compensation(user_id, reply_peer)
            return

        m_repost33 = re.match(r'^\s*/repost33(?:\s+(.+))?$', _strip_club_prefix_raw(text), re.IGNORECASE)
        if m_repost33:
            args_raw = (m_repost33.group(1) or "").strip()
            if not args_raw:
                send_msg(
                    reply_peer,
                    "Формат: /repost33 [юзер]\n"
                    "Команда проверяет по БД дубли репост-кампаний одного и того же поста,\n"
                    "считает сумму, полученную багом, и автоматически списывает ее.",
                    kb_for_peer(reply_peer),
                )
                return

            target_id = get_id_by_domain(args_raw.split()[0])
            if not target_id:
                send_msg(reply_peer, "Не удалось определить юзера. Укажи упоминание или ссылку на профиль.", kb_for_peer(reply_peer))
                return
            target_id = int(target_id)
            cursor.execute(
                "INSERT OR IGNORE INTO users (user_id, msg_until_captcha) VALUES (?, ?)",
                (target_id, random.randint(1, CAPTCHA_MESSAGES_UNTIL_MAX)),
            )
            cursor.execute("SELECT COALESCE(balance, 0) FROM users WHERE user_id = ?", (target_id,))
            bal_row = cursor.fetchone() or (0,)
            bal_before = int(bal_row[0] or 0)

            bug_amount, dup_campaign_ids, dup_count = _calc_repost_bug_overreward(target_id)
            if bug_amount <= 0:
                send_msg(
                    reply_peer,
                    f"✅ Проверка завершена: у @id{target_id} ({get_user_name(target_id)}) не найдено суммы для автоштрафа.",
                    kb_for_peer(reply_peer),
                )
                return

            bal_after = max(0, bal_before - int(bug_amount))
            cursor.execute("UPDATE users SET balance = ? WHERE user_id = ?", (bal_after, target_id))
            for campaign_id in dup_campaign_ids:
                cursor.execute("UPDATE repost_campaigns SET active = 0 WHERE id = ?", (int(campaign_id),))
                cursor.execute(
                    "UPDATE repost_reward_locks SET deducted = 1 WHERE campaign_id = ? AND deducted = 0",
                    (int(campaign_id),),
                )
            total_warns, _ = _issue_repost_warning(target_id, user_id, f"автоштраф /repost33: {format_click(bug_amount)}$")
            db.commit()

            send_admin_chat_log(
                f"[REPOST33-АВТОШТРАФ] {get_user_mention_with_name(target_id)}\n"
                f"Списано по БД: {format_click(bug_amount)}$.\n"
                f"Дубликат-кампаний: {dup_count}.\n"
                f"Баланс: {format_click(bal_before)}$ -> {format_click(bal_after)}$.\n"
                f"Выговоров теперь: {total_warns}.\n"
                f"Инициатор: {get_user_mention_with_name(user_id)}"
            )
            send_msg(
                reply_peer,
                f"✅ /repost33 выполнен для @id{target_id} ({get_user_name(target_id)}).\n"
                f"Автоштраф по БД: {format_click(bug_amount)}$.\n"
                f"Дубликат-кампаний: {dup_count}.\n"
                f"Баланс после списания: {format_click(bal_after)}$.\n"
                f"Выговоров: {total_warns}.",
                kb_for_peer(reply_peer),
            )
            send_msg(
                target_id,
                "⚠️ По результатам проверки базы найден багаюз репостов.\n"
                f"С вашего баланса автоматически списано: {format_click(bug_amount)}$.",
                kb_for_peer(target_id),
            )
            return

        m_repost_warn = re.match(r'^\s*/выговор(?:\s+(.+))?$', _strip_club_prefix_raw(text), re.IGNORECASE)
        if m_repost_warn:
            if not _is_owner(user_id):
                send_msg(
                    reply_peer,
                    "Команда /выговор по репостам доступна только владельцу проекта.",
                    kb_for_peer(reply_peer),
                )
                return
            args_raw = (m_repost_warn.group(1) or "").strip()
            if not args_raw:
                send_msg(
                    reply_peer,
                    "Система выговоров за баги с репостами:\n"
                    "/выговор [юзер] [причина — по желанию]\n"
                    "Пример: /выговор @ник багаюз репостов\n"
                    f"Каждый 3-й выговор: авто-блок репост-выплат на {REPOST_WARN_BLOCK_HOURS} ч.\n\n"
                    "Журнал: /repost33",
                    kb_for_peer(reply_peer),
                )
                return
            parts = re.split(r"\s+", args_raw)
            target_id = get_id_by_domain(parts[0])
            if not target_id:
                send_msg(reply_peer, "Не удалось определить юзера. Укажи упоминание или ссылку на профиль.", kb_for_peer(reply_peer))
                return
            target_id = int(target_id)
            reason_txt = " ".join(parts[1:]).strip() if len(parts) > 1 else "багаюз репостов"
            total_warns, blocked_until = _issue_repost_warning(target_id, user_id, reason_txt)
            if total_warns <= 0:
                send_msg(reply_peer, "Не удалось выдать выговор (ошибка БД).", kb_for_peer(reply_peer))
                return
            admin_summary = (
                f"[РЕПОСТ-ВЫГОВОР] {get_user_mention_with_name(target_id)}\n"
                f"Причина: {reason_txt}\n"
                f"Всего выговоров: {total_warns}\n"
                f"Выдал: {get_user_mention_with_name(user_id)}"
            )
            if blocked_until > time.time():
                admin_summary += (
                    "\n"
                    f"Авто-блок репост-выплат до "
                    f"{datetime.fromtimestamp(blocked_until, timezone.utc).strftime('%d.%m.%Y %H:%M UTC')}."
                )
            send_admin_chat_log(admin_summary)
            send_msg(
                reply_peer,
                f"✅ Выговор выдан @id{target_id} ({get_user_name(target_id)}).\n"
                f"Причина: {reason_txt}\n"
                f"Всего выговоров: {total_warns}.",
                kb_for_peer(reply_peer),
            )
            if blocked_until > time.time():
                send_msg(target_id, f"⚠️ Вы получили выговор за репосты (#{total_warns}).\nВыплаты за репосты отключены на {REPOST_WARN_BLOCK_HOURS} часов.", kb_for_peer(target_id))
            else:
                send_msg(target_id, f"⚠️ Вы получили выговор за репосты (#{total_warns}).\nПричина: {reason_txt}", kb_for_peer(target_id))
            return

        if owner_cmd == 'id':
            send_msg(
                reply_peer,
                f"🆔 Идентификаторы\npeer_id: {int(reply_peer)}\nuser_id: {int(user_id)}",
                kb_for_peer(reply_peer),
            )
            return
        _op_edit_cmid = int(message_cmid or 0) if event.obj.message.get('_from_callback') else 0
        if owner_cmd == 'op':
            send_msg_admin_op_panel(
                user_id,
                reply_peer,
                "🔐 Админ-панель\n\nВыберите раздел:",
                get_op_panel_kb(user_id),
                edit_cmid=_op_edit_cmid,
            )
            return
        if payload_cmd == 'admin_op_menu':
            send_msg_admin_op_panel(
                user_id,
                reply_peer,
                "🔐 Админ-панель\n\nВыберите раздел:",
                get_op_panel_kb(user_id),
                edit_cmid=_op_edit_cmid,
            )
            return
        if payload_cmd == 'admin_op_roles':
            raw_rk = (payload_data or {}).get('rk')
            rk = str(raw_rk).strip() if raw_rk not in (None, '') else ''
            if rk and rk not in _OP_ROLE_CATALOG_KEYS:
                send_msg_admin_op_panel(
                    user_id,
                    reply_peer,
                    "Неизвестная роль. Выберите из списка.",
                    get_op_roles_constructor_kb(),
                    edit_cmid=_op_edit_cmid,
                )
                return
            if not rk:
                send_msg_admin_op_panel(
                    user_id,
                    reply_peer,
                    _op_roles_catalog_intro_text()[:3900],
                    get_op_roles_constructor_kb(),
                    edit_cmid=_op_edit_cmid,
                )
            else:
                send_msg_admin_op_panel(
                    user_id,
                    reply_peer,
                    _op_roles_card_text(rk)[:3900],
                    get_op_roles_detail_kb(),
                    edit_cmid=_op_edit_cmid,
                )
            return
        if payload_cmd in ADMIN_OP_PAYLOAD_CMDS:
            if payload_cmd == 'admin_op_economy':
                if not _is_owner(user_id):
                    op_body = "⚙️ Раздел «Экономика» (цены клика и усилителя) доступен только владельцу. Используйте другие кнопки панели."
                else:
                    op_body = economy_admin_summary_text()
            elif payload_cmd == 'admin_op_stats':
                op_body = _admin_op_stats_text()
            elif payload_cmd == 'admin_op_banlist':
                op_body = _admin_op_banlist_text()
            elif payload_cmd == 'admin_op_withdraw':
                op_body = _admin_op_withdraw_text()
            elif payload_cmd == 'admin_op_promos':
                op_body = _admin_op_promos_text()
            elif payload_cmd == 'admin_promolist':
                op_body = promolist_admin_text()
            elif payload_cmd == 'admin_op_cmds':
                op_body = _admin_op_cmds_text()
            else:
                return
            send_msg_admin_op_panel(user_id, reply_peer, op_body, get_op_panel_kb(user_id), edit_cmid=_op_edit_cmid)
            return

    if _is_multichat_peer(reply_peer):
        try:
            cursor.execute(
                "UPDATE users SET chat_msg_count = COALESCE(chat_msg_count, 0) + 1 WHERE user_id = ?",
                (user_id,),
            )
            db.commit()
        except sqlite3.OperationalError:
            try:
                cursor.execute("ALTER TABLE users ADD COLUMN chat_msg_count INTEGER DEFAULT 0")
                db.commit()
                cursor.execute(
                    "UPDATE users SET chat_msg_count = COALESCE(chat_msg_count, 0) + 1 WHERE user_id = ?",
                    (user_id,),
                )
                db.commit()
            except Exception:
                pass

    if (
        not is_registered
        and _is_multichat_peer(reply_peer)
        and user_id != ADMIN_ID
    ):
        now_hint = time.time()
        reg_msg = (
            "Функции бота доступны только после регистрации.\n"
            "Нажмите «Зарегистрироваться» и пройдите короткую регистрацию в личных сообщениях с ботом."
        )
        kbd_reg = _register_from_chat_keyboard_str()
        if (text or "").strip() or payload_cmd:
            cursor.execute(
                "SELECT COALESCE(last_multichat_reg_hint_at, 0) FROM users WHERE user_id = ?",
                (user_id,),
            )
            row_h = cursor.fetchone()
            last_h = float(row_h[0] or 0) if row_h else 0.0
            if now_hint - last_h >= MULTICHAT_REG_HINT_COOLDOWN_SEC:
                try:
                    cursor.execute(
                        "UPDATE users SET last_multichat_reg_hint_at = ? WHERE user_id = ?",
                        (now_hint, user_id),
                    )
                    db.commit()
                except sqlite3.OperationalError:
                    try:
                        cursor.execute(
                            "ALTER TABLE users ADD COLUMN last_multichat_reg_hint_at REAL DEFAULT 0"
                        )
                        db.commit()
                        cursor.execute(
                            "UPDATE users SET last_multichat_reg_hint_at = ? WHERE user_id = ?",
                            (now_hint, user_id),
                        )
                        db.commit()
                    except Exception:
                        pass
                send_msg(reply_peer, reg_msg, kbd_reg)
        return

    # 1. Регистрация
    admin_chat_bypass = _is_multichat_peer(reply_peer) and int(reply_peer) == int(ADMIN_CHAT_PEER_ID) and _is_admin_user(user_id)
    if not is_registered and not admin_chat_bypass:
        # Автовосстановление регистрации для пользователей, которые уже проходили основной бот
        # и сейчас состоят в группе: не требуем повторно нажимать «Согласен».
        if check_parent_registration(user_id):
            try:
                if _vk_bot_group_subscription_ok(user_id):
                    _reg_ts_auto = time.time()
                    cursor.execute(
                        "UPDATE users SET is_registered = 1, "
                        "registered_at = CASE WHEN COALESCE(registered_at, 0) <= 0 THEN ? ELSE registered_at END "
                        "WHERE user_id = ?",
                        (_reg_ts_auto, int(user_id)),
                    )
                    db.commit()
                    is_registered = 1
                    send_msg(
                        reply_peer,
                        "✅ Регистрация подтверждена автоматически.\n"
                        "Добро пожаловать! Вот твое главное меню.",
                        kb_for_peer(reply_peer),
                    )
                    try:
                        _sync_user_group_subscription(user_id, force=True)
                    except Exception:
                        pass
            except Exception:
                pass
        if payload_cmd in ['agree', 'check_sub']:
            is_member = _vk_bot_group_subscription_ok(user_id)

            if is_member:
                _reg_ts = time.time()
                cursor.execute(
                    "UPDATE users SET is_registered = 1, "
                    "registered_at = CASE WHEN COALESCE(registered_at, 0) <= 0 THEN ? ELSE registered_at END "
                    "WHERE user_id = ?",
                    (_reg_ts, int(user_id)),
                )
                db.commit()
                send_msg(reply_peer, "Добро пожаловать! Вот твое главное меню.\nКраткая инструкция: кликай, зарабатывай и выводи!", kb_for_peer(reply_peer))
                try:
                    _sync_user_group_subscription(user_id, force=True)
                except Exception:
                    pass
                try:
                    send_admin_chat_log(
                        f"[РЕГИСТРАЦИЯ] Новый игрок: {get_user_mention_with_name(user_id)}\n"
                        f"ID: {int(user_id)}"
                    )
                except Exception:
                    pass
                cursor.execute("SELECT pending_referrer FROM users WHERE user_id = ?", (user_id,))
                row = cursor.fetchone()
                if row and row[0]:
                    ref_id = row[0]
                    update_user(user_id, 'referrer_id', ref_id)
                    update_user(user_id, 'pending_referrer', None)
                    new_ref_name = get_user_name(user_id)
                    send_msg(ref_id, f"🎉 У вас новый раб: {new_ref_name}!\nОн успешно подписался и зарегистрировался.", get_main_kb())
            else:
                if VERIFICATION_GROUP_SCREEN:
                    msg = (
                        "Нужно состоять в группе бота."
                        if payload_cmd == 'agree'
                        else "Пока не видим подписку на группу бота. Вступите в сообщество и нажмите «Я подписался» снова."
                    )
                else:
                    msg = "Для использования бота необходимо подписаться на наше сообщество!" if payload_cmd == 'agree' else "Вы всё ещё не подписаны на сообщество! Проверьте подписку."
                send_msg(reply_peer, msg, get_subscribe_kb(user_id))
            return
        if is_registered:
            # Регистрация автоматически восстановлена выше — продолжаем обычную обработку.
            pass
        else:
            if check_parent_registration(user_id):
                send_msg(
                    reply_peer,
                    "В самом начале ознакомьтесь с правилами: https://vk.com/topic-237333137_57395396\n"
                    "После прочтения нажмите «Согласен».\n\n"
                    "⚠️ Этот бот ведётся сообществом независимо; за его работу отвечает администрация проекта.",
                    get_register_kb(),
                )
            else:
                send_msg(reply_peer, "Для использования бота необходимо иметь профиль в основном боте!\nЗарегистрируйтесь по кнопке ниже, а затем нажмите «Проверить».", get_parent_check_kb())
            return

    if try_resolve_quiz_guess(user_id, reply_peer, text, is_registered):
        return
    if is_registered:
        _update_personal_event_playtime(user_id)

    if is_registered and _is_multichat_peer(reply_peer) and user_id != ADMIN_ID:
        # В админ-чате состав и владелец проекта не режем белым списком restricted
        if not (int(reply_peer) == int(ADMIN_CHAT_PEER_ID) and _can_use_admin_chat_mod_features(user_id)):
            if not _restricted_chat_allowed(event.obj.message, text, payload_cmd):
                return
        update_user(user_id, 'captcha_answer', None)
        update_user(user_id, 'msg_until_captcha', random.randint(1, CAPTCHA_MESSAGES_UNTIL_MAX))
        captcha_answer = None

    # 2. Капча
    if captcha_answer is not None and not _is_multichat_peer(reply_peer):
        if not _is_promo_activation_text(text):
            if payload_cmd == 'captcha_click':
                cursor.execute(
                    "SELECT COALESCE(captcha_token, ''), COALESCE(captcha_message_id, 0) FROM users WHERE user_id = ?",
                    (int(user_id),),
                )
                _cr = cursor.fetchone()
                token_saved = (_cr[0] if _cr else "") or ""
                token_got = str(payload_data.get('t') or "")
                ok_got = int(payload_data.get('ok') or 0)
                if token_saved and token_got == token_saved and ok_got == 1:
                    update_user(user_id, 'captcha_answer', None)
                    update_user(user_id, 'msg_until_captcha', random.randint(1, CAPTCHA_MESSAGES_UNTIL_MAX))
                    update_user(user_id, 'captcha_token', '')
                    _delete_captcha_message_if_any(user_id)
                    send_msg(reply_peer, "Верно! Можешь продолжать.", kb_for_peer(reply_peer))
                else:
                    issue_captcha_challenge(user_id, reply_peer, "Неверно! Попробуйте еще раз.\n✅ Нажмите на галочку:")
                return
            if payload_cmd == 'captcha_pass':
                update_user(user_id, 'captcha_answer', None)
                update_user(user_id, 'msg_until_captcha', random.randint(1, CAPTCHA_MESSAGES_UNTIL_MAX)) 
                update_user(user_id, 'captcha_token', '')
                _delete_captcha_message_if_any(user_id)
                send_msg(reply_peer, "Верно! Можешь продолжать.", kb_for_peer(reply_peer))
            elif payload_cmd == 'captcha_fail':
                issue_captcha_challenge(user_id, reply_peer, "Неверно! Попробуйте еще раз.\n✅ Нажмите на галочку:")
            else:
                issue_captcha_challenge(user_id, reply_peer, "Пожалуйста, нажмите на галочку на инлайн-клавиатуре:")
            return

    # 3. Отмена отзыва
    if _normalize_chat_command(text) in [
        'кликать', 'профиль', 'я', 'б', 'баланс', 'о боте', 'меню', 'начать', 'start',
        'рефка', 'магазин', 'пожертвование', 'пожертвовать', 'пожертвования', 'топ', 'ограбление', 'топ смс', 'топ спам', 'топспам',
    ] and review_state != 0:
        update_user(user_id, 'review_state', 0)
        update_user(user_id, 'temp_review_text', '')
        review_state = 0

    # 4. Отзыв
    if payload_cmd == 'write_review':
        update_user(user_id, 'review_state', 1)
        send_msg(reply_peer, "Пожалуйста, напишите краткий отзыв о выплате (до 90 символов):")
        return

    if (
        review_state == 1
        and not payload_cmd
        and not _is_promo_activation_text(text)
    ):
        if len(text) > 90: return send_msg(reply_peer, "Отзыв не должен превышать 90 символов. Попробуйте короче:", kb_for_peer(reply_peer))
        update_user(user_id, 'temp_review_text', text)
        update_user(user_id, 'review_state', 2)
        send_msg(reply_peer, "Выберите категорию:", get_rating_kb())
        return

    if review_state == 2 and payload_cmd in ['rate_good', 'rate_bad']:
        rating = "👍" if payload_cmd == 'rate_good' else "👎"
        cursor.execute("SELECT id, comment_id, status, amount FROM withdrawals WHERE user_id = ? ORDER BY id DESC LIMIT 1", (user_id,))
        w_data = cursor.fetchone()
        if w_data:
            cursor.execute("UPDATE withdrawals SET rating = ?, review_text = ? WHERE id = ?", (rating, temp_review_text, w_data[0]))
            db.commit()
            if vk_user:
                username = get_user_name(user_id)
                new_body = build_board_msg(user_id, username, w_data[3], w_data[2], rating, temp_review_text)
                comment_id = int(w_data[1] or 0)
                if comment_id > 0:
                    try:
                        vk_user.board.editComment(
                            group_id=GROUP_ID,
                            topic_id=57395405,
                            comment_id=comment_id,
                            message=new_body,
                        )
                    except Exception:
                        pass
                else:
                    try:
                        new_comment_id = vk_user.board.createComment(
                            group_id=GROUP_ID,
                            topic_id=57395405,
                            message=new_body,
                            from_group=1,
                        )
                        if isinstance(new_comment_id, dict):
                            new_comment_id = int(new_comment_id.get("comment_id") or 0)
                        else:
                            new_comment_id = int(new_comment_id or 0)
                        if new_comment_id > 0:
                            cursor.execute(
                                "UPDATE withdrawals SET comment_id = ? WHERE id = ?",
                                (new_comment_id, int(w_data[0])),
                            )
                            db.commit()
                    except Exception:
                        pass
        update_user(user_id, 'review_state', 0)
        update_user(user_id, 'temp_review_text', '')
        send_msg(
            reply_peer,
            "Спасибо за ваш отзыв!",
            kb_for_peer(reply_peer),
            attachment=sticker_attachment(STICKER_REVIEW_THANKS_ID),
        )
        return

    # 5. Новая капча (в ограниченном чате только профиль — капчу не показываем; «промо КОД» не считаем)
    if is_registered and user_id != ADMIN_ID and not _is_multichat_peer(reply_peer) and payload_cmd not in ['agree', 'check_sub', 'check_parent', 'heist_run', 'shop_buy_click_boost', 'shop_buy_steal_fast', 'shop_buy_steal_shield', 'top_refs', 'top_balance', 'top_spam', 'top_donations', 'donate_pick_15', 'donate_pick_30', 'donate_pick_custom', 'donate_confirm', 'donate_cancel', 'donation_menu_close', 'pascha_accept', 'ozon_work_start', 'ozon_work_pick', RESTRICTED_TOPS_MENU_CMD, 'top_withdrawals'] and review_state == 0:
        if not _is_promo_activation_text(text) and not (_is_multichat_peer(reply_peer) and _is_steal_command_text(text)):
            if msg_until_captcha is None: msg_until_captcha = random.randint(1, CAPTCHA_MESSAGES_UNTIL_MAX)
            msg_until_captcha -= 1
            if msg_until_captcha <= 0:
                update_user(user_id, 'captcha_answer', 1)
                update_user(user_id, 'msg_until_captcha', random.randint(1, CAPTCHA_MESSAGES_UNTIL_MAX))
                issue_captcha_challenge(user_id, reply_peer, "✅ Нажмите на галочку для проверки:")
                return
            else: update_user(user_id, 'msg_until_captcha', msg_until_captcha)

    # 6. Команды
    cmd_text = _normalize_chat_command(text)
    promo_pair = _strip_club_prefix_raw(text).split(None, 1)
    apply_daily_deposit_interest(user_id)
    if is_registered:
        for _m in _check_personal_event_progress_and_rewards(user_id):
            send_msg(reply_peer, _m, kb_for_peer(reply_peer))
    _check_antibot_timing(user_id, reply_peer, text, payload_cmd)

    # Казино отключено полностью.
    if (
        payload_cmd == CASINO_MENU_CMD
        or _casino_is_command(text)
        or re.match(r'^\s*!\+казик\s*$', _strip_club_prefix_raw(text), re.IGNORECASE)
        or re.match(r'^\s*!-казик\s*$', _strip_club_prefix_raw(text), re.IGNORECASE)
    ):
        send_msg(reply_peer, "🎰 Казино отключено.", kb_for_peer(reply_peer))
        return

    # Система питомцев и команды атаки отключены полностью.
    if (
        cmd_text in ("мой питомец", "натравить", "натравить питомца")
        or _is_steal_command_text(text)
        or payload_cmd in ("feed_all", "pet_upgrade", "pet_info")
    ):
        send_msg(reply_peer, "🐾 Система питомцев отключена.", kb_for_peer(reply_peer))
        return

    if (
        COMMUNITY_STATS_ADMIN_ID
        and int(user_id) == int(COMMUNITY_STATS_ADMIN_ID)
        and payload_cmd == "community_sub_stats"
        and not _is_multichat_peer(reply_peer)
    ):
        send_msg(reply_peer, _community_subscription_stats_text(), kb_for_peer(reply_peer))
        return

    if (
        is_registered
        and not _is_multichat_peer(reply_peer)
        and COMMUNITY_STATS_ADMIN_ID
        and int(user_id) != int(COMMUNITY_STATS_ADMIN_ID)
    ):
        _withdraw_check_sub = (
            payload_cmd == "check_sub"
            and isinstance(payload_data, dict)
            and int(payload_data.get("w") or 0) == 1
        )
        sub_ok, _sub_ev = _sync_user_group_subscription(
            user_id,
            force=(payload_cmd == "check_sub"),
            notify_admin_on_sub=_withdraw_check_sub,
        )
        if payload_cmd == "check_sub":
            if sub_ok:
                send_msg(
                    reply_peer,
                    "✅ Подписка на сообщество подтверждена.",
                    kb_for_peer(reply_peer),
                )
            else:
                send_msg(
                    reply_peer,
                    (
                        "Пока не видим подписку на группу бота. Вступите и нажмите «Я подписался» снова."
                        if VERIFICATION_GROUP_SCREEN and VERIFICATION_COOPERATION_ENABLED
                        else "Пока не видим вас в подписчиках группы. Вступите в сообщество и нажмите «Я подписался» снова."
                    ),
                    get_subscribe_kb(user_id),
                )
            return
        if not sub_ok:
            _sub_allow = cmd_text in (
                "помощь",
                "help",
                "команды",
                "меню команд",
                "вопросы",
                "о боте",
                "начать",
                "меню",
                "start",
            ) or payload_cmd in ("help_commands", "help_faq", "help_ask_question", "pascha_accept")
            if not _sub_allow:
                send_msg(
                    reply_peer,
                    (
                        "Чтобы пользоваться ботом, вступите в группу бота и нажмите «Я подписался»."
                        if VERIFICATION_GROUP_SCREEN and VERIFICATION_COOPERATION_ENABLED
                        else "Чтобы пользоваться ботом, вступите в сообщество и нажмите «Я подписался»."
                    ),
                    get_subscribe_kb(user_id),
                )
                return

    if payload_cmd == "pascha_accept":
        if not is_registered:
            send_msg(reply_peer, "Сначала зарегистрируйтесь в боте сообщества.", kb_for_peer(reply_peer))
            return
        _handle_pascha_accept(user_id, payload_data.get("t"), reply_peer)
        return

    if payload_cmd == 'help_ask_question':
        if _is_multichat_peer(reply_peer):
            send_msg(reply_peer, "Задайте вопрос в ЛС боту.", get_main_kb())
            return
        update_user_fields(user_id, ask_question_wait=1, ask_question_wait_started_at=float(time.time()))
        send_msg(
            reply_peer,
            "💬 Чат для вопросов и ответов модерации:\n"
            "https://vk.me/join/zNURw9NhGPPnP3avIM7TQ2CiC2/N7vg_JuA=\n\n"
            "✍️ Напишите свой вопрос следующим сообщением.\n"
            "Если не отправите вопрос в течение 3 часов, запрос будет отменен.",
            _get_help_kb(),
        )
        return

    try:
        cursor.execute(
            "SELECT COALESCE(ask_question_wait, 0), COALESCE(mod_reply_question_id, 0), COALESCE(moderator_public_id, 0), COALESCE(ask_question_wait_started_at, 0) "
            "FROM users WHERE user_id = ?",
            (int(user_id),),
        )
        _qrow = cursor.fetchone() or (0, 0, 0)
        ask_question_wait = int(_qrow[0] or 0)
        mod_reply_question_id = int(_qrow[1] or 0)
        moderator_public_id = int(_qrow[2] or 0)
        ask_question_wait_started_at = float(_qrow[3] or 0)
    except Exception:
        ask_question_wait = 0
        mod_reply_question_id = 0
        moderator_public_id = 0
        ask_question_wait_started_at = 0.0

    if ask_question_wait == 1 and not payload_cmd and not _is_multichat_peer(reply_peer):
        if ask_question_wait_started_at > 0 and (time.time() - ask_question_wait_started_at) > 3 * 3600:
            update_user_fields(user_id, ask_question_wait=0, ask_question_wait_started_at=0)
            send_msg(reply_peer, "⏱ Ожидание вопроса истекло (3 часа). Нажмите «Спросить вопрос» снова.", _get_help_kb())
            return
        q_text = (_strip_club_prefix_raw(text) or "").strip()
        if not q_text:
            send_msg(reply_peer, "Вопрос пустой. Напишите текст вопроса.", _get_help_kb())
            return
        if len(q_text) > 1800:
            send_msg(reply_peer, "Слишком длинный вопрос. Лимит: 1800 символов.", _get_help_kb())
            return
        cursor.execute(
            "INSERT INTO support_questions (user_id, question_text, status, created_at) VALUES (?, ?, 'new', ?)",
            (int(user_id), q_text, float(time.time())),
        )
        qid = int(cursor.lastrowid or 0)
        db.commit()
        update_user_fields(user_id, ask_question_wait=0, ask_question_wait_started_at=0)
        send_msg(reply_peer, f"✅ Вопрос отправлен в модераторский чат.\nID обращения: #{qid}\nОжидайте ответ.", _get_help_kb())
        if qid > 0:
            send_msg(
                ADMIN_CHAT_PEER_ID,
                f"❓ Новый вопрос #{qid}\n"
                f"От: {get_user_mention_with_name(user_id)}\n\n"
                f"Вопрос:\n{q_text}",
                get_ask_question_admin_kb(qid),
                disable_mentions=True,
            )
        return

    if (
        int(reply_peer) == int(ADMIN_CHAT_PEER_ID)
        and _is_moderation_staff(user_id)
        and mod_reply_question_id > 0
        and not payload_cmd
    ):
        raw_answer = (_strip_club_prefix_raw(text) or "").strip()
        if raw_answer and not raw_answer.startswith(("!", "/")):
            cursor.execute(
                "SELECT user_id, question_text, status, COALESCE(taken_by, 0) "
                "FROM support_questions WHERE id = ?",
                (int(mod_reply_question_id),),
            )
            sq = cursor.fetchone()
            if sq and str(sq[2]) == "in_progress" and int(sq[3] or 0) == int(user_id):
                target_uid = int(sq[0] or 0)
                question_text = str(sq[1] or "")
                _rk_plain = _project_role_label_for_user(user_id)
                rank_label = _project_role_label_with_hashtag_for_user(user_id) if _rk_plain else "Модератор"
                responder_id = moderator_public_id if moderator_public_id > 0 else int(user_id)
                send_msg(
                    target_uid,
                    f"{rank_label} {responder_id} ответил на ваш вопрос: {question_text}\n\n"
                    f"Ответ: {raw_answer}",
                    get_main_kb(),
                )
                cursor.execute(
                    "UPDATE support_questions SET status = 'answered', answer_text = ?, answered_at = ? WHERE id = ?",
                    (raw_answer, float(time.time()), int(mod_reply_question_id)),
                )
                db.commit()
                _log_moderator_action(user_id, "support_answer", 0)
                update_user(user_id, 'mod_reply_question_id', 0)
                try:
                    send_admin_chat_log(
                        f"[ОТВЕТ НА ВОПРОС] #{int(mod_reply_question_id)}\n"
                        f"Модератор: {get_user_mention_with_name(user_id)}\n"
                        f"Игрок: {get_user_mention_with_name(target_uid)}\n"
                        f"Вопрос: {(question_text or '')[:220]}\n"
                        f"Ответ: {(raw_answer or '')[:260]}"
                    )
                except Exception:
                    pass
                send_msg(
                    reply_peer,
                    f"✅ Ответ на вопрос #{int(mod_reply_question_id)} отправлен пользователю.",
                    kb_for_peer(reply_peer),
                )
                return

    if donation_wait_custom == 1 and payload_cmd == "":
        if _is_multichat_peer(reply_peer):
            update_user(user_id, 'donation_wait_custom', 0)
            update_user(user_id, 'donation_pending_amount', 0)
            send_msg(
                reply_peer,
                "Пожертвования и ввод суммы доступны только в личных сообщениях с ботом.",
                kb_for_peer(reply_peer),
            )
            return
        try:
            donate_amt = int(parse_amount(cmd_text))
        except Exception:
            donate_amt = 0
        if donate_amt > 0:
            update_user(user_id, 'donation_pending_amount', int(donate_amt))
            update_user(user_id, 'donation_wait_custom', 0)
            send_msg(
                reply_peer,
                f"Подтвердите пожертвование: {format_click(donate_amt)}$ ?",
                get_donation_confirm_kb(donate_amt),
            )
            return
        # Сумма не распознана — выходим из режима ввода; сообщение обрабатывается как обычная команда
        update_user(user_id, 'donation_wait_custom', 0)
        update_user(user_id, 'donation_pending_amount', 0)

    if payload_cmd == 'donation_menu_close':
        update_user(user_id, 'donation_wait_custom', 0)
        update_user(user_id, 'donation_pending_amount', 0)
        if _is_multichat_peer(reply_peer):
            send_msg(reply_peer, "Меню пожертвований доступно в ЛС с ботом.", kb_for_peer(reply_peer))
            return
        send_msg(reply_peer, "Главное меню:", get_main_kb())
        return

    _text_for_chat_cmd = _strip_club_prefix_raw(text or "").strip()
    if re.match(r"^\s*инфо\s+\S", cmd_text.strip(), re.IGNORECASE):
        try:
            _ainfo_admin_chat_only = int(reply_peer) == int(ADMIN_CHAT_PEER_ID)
        except (TypeError, ValueError):
            _ainfo_admin_chat_only = False
        if not _ainfo_admin_chat_only:
            if _can_use_admin_chat_mod_features(user_id):
                send_msg(
                    reply_peer,
                    "Команда /инфо доступна только в админ-беседе.",
                    kb_for_peer(reply_peer),
                )
            return
    is_role_assign_cmd = bool(re.match(r'^\s*!должность\s', _text_for_chat_cmd, re.IGNORECASE))
    is_force_captcha_cmd = bool(re.match(r'^\s*!?капча\s', _text_for_chat_cmd, re.IGNORECASE))
    is_gpt_cmd = bool(re.match(r'^\s*/гпт(?:\s+.+)?$', _text_for_chat_cmd, re.IGNORECASE))
    is_staff_reprimand_cmd = bool(
        re.match(r'^\s*\+выговор\b', _text_for_chat_cmd, re.IGNORECASE)
        or re.match(r'^\s*-выговор\b', _text_for_chat_cmd, re.IGNORECASE)
    )
    is_promote_cmd = bool(re.match(r'^\s*!повысить\b', _text_for_chat_cmd, re.IGNORECASE))
    try:
        is_admin_info_cmd = (
            int(reply_peer) == int(ADMIN_CHAT_PEER_ID)
            and bool(re.match(r"^\s*инфо\s+\S", cmd_text.strip(), re.IGNORECASE))
            and _can_use_admin_chat_mod_features(user_id)
        )
    except (TypeError, ValueError):
        is_admin_info_cmd = False
    allow_admin_cmd_in_chat = (
        is_role_assign_cmd
        or (is_force_captcha_cmd and int(reply_peer) == int(ADMIN_CHAT_PEER_ID))
        or (is_gpt_cmd and (_is_owner(user_id) or _is_deputy_owner(user_id)))
        or (is_staff_reprimand_cmd and (_is_owner(user_id) or _can_use_staff_reprimand_non_owner_commands(user_id)))
        or (is_promote_cmd and (_is_owner(user_id) or _is_deputy_owner(user_id)))
        or is_admin_info_cmd
    )
    if _is_multichat_peer(reply_peer) and _is_admin_command_attempt(text, payload_cmd, user_id) and not allow_admin_cmd_in_chat:
        send_msg(
            reply_peer,
            "В беседе доступны только обычные команды.\nАдмин-команды отправлены вам в ЛС.",
            kb_for_peer(reply_peer),
        )
        send_msg(
            user_id,
            "🔐 Админ-команды работают только в личных сообщениях с ботом.\nНапишите команду сюда, в ЛС.",
            get_main_kb(),
        )
        return
    if cmd_text in ['меню', 'начать', 'start']: send_msg(reply_peer, "Главное меню:", kb_for_peer(reply_peer))

    elif cmd_text == 'кликать':
        now_click = time.time()
        if heist_jail_until > now_click:
            send_msg(
                reply_peer,
                f"🚔 Пока вы в тюрьме, кликать нельзя.\nДо освобождения: {format_time_left_sec(heist_jail_until - now_click)}.",
                kb_for_peer(reply_peer),
            )
            return
        if now_click - last_click_timestamp < 1.0: return
        try:
            click_intervals = json.loads(last_clicks or "[]")
            if not isinstance(click_intervals, list):
                click_intervals = []
        except Exception:
            click_intervals = []
        if last_click_timestamp > 0:
            click_intervals.append(round(now_click - last_click_timestamp, 2))
        click_intervals = click_intervals[-AUTOCLICK_PATTERN_LEN:]
        cursor.execute(
            "UPDATE users SET last_click_timestamp = ?, last_clicks = ? WHERE user_id = ?",
            (now_click, json.dumps(click_intervals, ensure_ascii=False), user_id),
        )
        db.commit()
        if len(click_intervals) >= AUTOCLICK_PATTERN_LEN:
            spread = max(click_intervals) - min(click_intervals)
            if spread <= AUTOCLICK_INTERVAL_SPREAD_SEC:
                ban_to = now_click + AUTOCLICK_BAN_SEC
                update_user(user_id, 'ban_until', ban_to)
                update_user(user_id, 'last_clicks', '[]')
                _log_ban_event(
                    user_id=user_id,
                    reason="Автобан за подозрительные клики",
                    until_ts=ban_to,
                    issued_by=0,
                    source_chat=reply_peer,
                )
                send_msg(
                    reply_peer,
                    "⛔ Вас забанили на 20 минут за подозрительные клики.",
                    kb_for_peer(reply_peer),
                )
                send_msg(
                    ADMIN_ID,
                    f"🚨 Автобан за подозрительные клики\n"
                    f"Пользователь: @id{user_id} ({get_user_name(user_id)})\n"
                    f"Интервалы: {click_intervals}\n"
                    f"Бан до: {datetime.fromtimestamp(ban_to, timezone.utc).strftime('%d.%m.%Y %H:%M')} UTC",
                    get_main_kb(),
                )
                return
        if energy >= 1:
            wealth_threshold = int(get_economy_wealth_threshold())
            gain = int(get_economy_click_low() if int(balance) < wealth_threshold else get_economy_click_high())
            gain = (gain * CLICK_INCOME_MULT_NUM) // CLICK_INCOME_MULT_DEN
            boost_active = (click_boost_until or 0) > time.time()
            if boost_active:
                gain += int(get_economy_click_boost_bonus())
            event_bonus_percent = _event_click_bonus_percent(user_id)
            if event_bonus_percent > 0:
                gain += (gain * event_bonus_percent) // 100
            _now_promo = time.time()
            _p_pct = int(promo_click_bonus_percent or 0)
            _p_until = float(promo_click_bonus_until or 0)
            if _p_until <= _now_promo and _p_pct > 0:
                update_user_fields(user_id, promo_click_bonus_percent=0, promo_click_bonus_until=0)
                _p_pct = 0
            if _p_until > _now_promo and _p_pct > 0:
                gain += (gain * _p_pct) // 100
            gain = (gain * CLICK_INCOME_SCALE_DOWN_NUM) // CLICK_INCOME_SCALE_DOWN_DEN
            new_balance = balance + gain
            update_user_fields(user_id, balance=new_balance, energy=energy - 1)
            extra = f"\n⚡ Бонус подписки: +{format_short(get_economy_click_boost_bonus())}$" if boost_active else ""
            send_msg(reply_peer, f"Клик! +{format_balance(gain)}${extra}\nТекущий баланс: {format_click(new_balance)}$\nЭнергия: {energy-1}/50", kb_for_peer(reply_peer))
        else:
            send_msg(reply_peer, "Недостаточно энергии! Покорми питомца или подожди.", kb_for_peer(reply_peer))

    elif cmd_text == 'работа' or payload_cmd in ('ozon_work_start', 'ozon_work_pick'):
        if not _runtime_ui_show_work():
            return
        if _is_multichat_peer(reply_peer):
            send_msg(reply_peer, "Работа доступна только в ЛС с ботом.", kb_for_peer(reply_peer))
            return
        try:
            cursor.execute(
                "SELECT COALESCE(ozon_work_cooldown_until, 0), COALESCE(ozon_work_target, 0) FROM users WHERE user_id = ?",
                (int(user_id),),
            )
            ow_row = cursor.fetchone() or (0, 0)
            ozon_cd_until = float(ow_row[0] or 0)
            ozon_target = int(ow_row[1] or 0)
        except Exception:
            ozon_cd_until = 0.0
            ozon_target = 0
        now_oz = time.time()
        if payload_cmd in ("", "ozon_work_start"):
            if ozon_cd_until > now_oz:
                send_msg(
                    reply_peer,
                    f"⏳ Работа на Ozon будет доступна через {format_time_left_sec(ozon_cd_until - now_oz)}.",
                    kb_for_peer(reply_peer),
                )
                return
            target = random.randint(1, 3)
            em = ["📦", "📦", "📦"]
            em[target - 1] = "🎁"
            cursor.execute(
                "UPDATE users SET ozon_work_target = ? WHERE user_id = ?",
                (int(target), int(user_id)),
            )
            db.commit()
            send_msg(
                reply_peer,
                "📦 Работа на Ozon: поиск коробок\n"
                "Энергия для кликов не тратится.\n\n"
                f"{em[0]} {em[1]} {em[2]}\n\n"
                "Найдите коробку с подарком 🎁 и нажмите правильную стрелку.",
                get_ozon_work_kb(),
            )
            return
        if payload_cmd == "ozon_work_pick":
            try:
                picked = int(payload_data.get("pos") or 0)
            except Exception:
                picked = 0
            if ozon_target <= 0:
                send_msg(reply_peer, "Сначала начните работу кнопкой «Работа».", kb_for_peer(reply_peer))
                return
            reward_mk = random.randint(int(OZON_WORK_REWARD_MIN_MK), int(OZON_WORK_REWARD_MAX_MK))
            reward = int(reward_mk * 1_000_000_000)
            if int(picked) == int(ozon_target):
                cd_ok = now_oz + OZON_WORK_CD_SEC
                new_bal = int(balance) + reward
                cursor.execute(
                    "UPDATE users SET balance = ?, ozon_work_target = 0, ozon_work_cooldown_until = ? WHERE user_id = ?",
                    (int(new_bal), float(cd_ok), int(user_id)),
                )
                db.commit()
                send_msg(
                    reply_peer,
                    f"✅ Коробка найдена! Награда: {reward_mk} мк ({format_click(reward)}$)\n"
                    f"Следующая работа через {format_time_left_sec(OZON_WORK_CD_SEC)}.",
                    kb_for_peer(reply_peer),
                )
            else:
                cd_fail = now_oz + OZON_WORK_WRONG_CD_SEC
                cursor.execute(
                    "UPDATE users SET ozon_work_target = 0, ozon_work_cooldown_until = ? WHERE user_id = ?",
                    (float(cd_fail), int(user_id)),
                )
                db.commit()
                send_msg(
                    reply_peer,
                    "📦 Вы потеряли груз. Следующая попытка через 5 минут.",
                    kb_for_peer(reply_peer),
                )
            return

    elif cmd_text == 'мой питомец':
        pet_line = f"🐶 Питомец: {pet_name_me}"
        boost_active = (click_boost_until or 0) > time.time()
        send_msg(reply_peer, f"{pet_line}\n⚡ Энергия: {energy}/50\n🍖 Накормленность: {fed}%", get_pet_kb(balance, fed, pet_power_me, show_info=True, owner_user_id=user_id, boost_active=boost_active))

    elif _is_steal_command_text(text):
        raw_cmd = _strip_club_prefix_raw(text).strip()
        target_id = None
        # В беседе можно просто ответить на сообщение нужного пользователя: "натравить питомца".
        rm = event.obj.message.get('reply_message') if isinstance(event.obj.message, dict) else None
        if _is_multichat_peer(reply_peer) and rm:
            try:
                rid = rm.get('from_id')
                if rid is not None and int(rid) > 0:
                    target_id = int(rid)
            except (TypeError, ValueError):
                target_id = None
        if target_id is None:
            m_target = re.match(
                r'^\s*(?:натравить(?:\s+питомца)?|ограбить\s+игрока|грабить\s+игрока)\s+(.+?)\s*$',
                raw_cmd,
                re.IGNORECASE,
            )
            if not m_target:
                send_msg(
                    reply_peer,
                    "Формат:\n- Натравить питомца (ответом на сообщение в беседе)\n- Натравить питомца [юзер]",
                    kb_for_peer(reply_peer),
                )
                return
            target_id = get_id_by_domain(m_target.group(1))
        cursor.execute("SELECT last_steal_at FROM users WHERE user_id = ?", (user_id,))
        _srow = cursor.fetchone()
        last_steal_at = float(_srow[0] or 0) if _srow else 0.0
        now_steal = time.time()
        steal_cd = STEAL_FAST_COOLDOWN_SEC if (steal_fast_until or 0) > now_steal else STEAL_COOLDOWN_SEC
        if last_steal_at > 0 and (now_steal - last_steal_at) < steal_cd:
            wait = steal_cd - (now_steal - last_steal_at)
            send_msg(
                reply_peer,
                f"⏳ Натравить питомца можно не чаще чем раз в {2 if steal_cd == STEAL_FAST_COOLDOWN_SEC else 3} часа.\nСледующая попытка через {format_time_left_sec(wait)}.",
                kb_for_peer(reply_peer),
            )
            return
        if not target_id:
            send_msg(reply_peer, "Не удалось найти юзера.", kb_for_peer(reply_peer))
            return
        if int(target_id) == int(user_id):
            send_msg(reply_peer, "Нельзя натравить питомца на самого себя.", kb_for_peer(reply_peer))
            return
        if pet_power_me <= 0:
            send_msg(reply_peer, "У вас нет питомца. Для атаки нужен питомец в профиле.", kb_for_peer(reply_peer))
            return

        _, tpet_name, tpet_power = get_local_pet_info(target_id)
        target_row, _ = get_user(target_id)
        target_balance = int(target_row[1])
        cursor.execute("SELECT COALESCE(steal_shield_until, 0) FROM users WHERE user_id = ?", (target_id,))
        _shield_row = cursor.fetchone()
        target_shield_until = float((_shield_row[0] if _shield_row else 0) or 0)
        if target_shield_until > now_steal:
            send_msg(
                reply_peer,
                f"🛡 У цели активен щит от атак питомцем до {datetime.fromtimestamp(target_shield_until, timezone.utc).strftime('%d.%m.%Y %H:%M')} UTC.",
                kb_for_peer(reply_peer),
            )
            return
        if target_balance <= 0:
            send_msg(reply_peer, "У цели нулевой баланс — атаковать бессмысленно.", kb_for_peer(reply_peer))
            return
        if pet_power_me <= tpet_power:
            cursor.execute("SELECT COALESCE(balance, 0) FROM users WHERE user_id = ?", (user_id,))
            _attacker_row = cursor.fetchone()
            attacker_balance_now = int((_attacker_row[0] if _attacker_row else 0) or 0)
            fail_penalty = max(1, attacker_balance_now // 100) if attacker_balance_now > 0 else 0
            if fail_penalty > 0:
                update_user(user_id, 'balance', max(0, attacker_balance_now - fail_penalty))
            send_msg(
                reply_peer,
                "❌ Атака питомцем не удалась\n\n"
                f"Ваш питомец: {pet_name_me} (сила {pet_power_me})\n"
                f"Питомец цели: {tpet_name} (сила {tpet_power})\n\n"
                "Нужен питомец сильнее, чем у цели.\n"
                + (
                    f"Штраф за неудачную попытку: {format_click(fail_penalty)}$ (1% вашего баланса)."
                    if fail_penalty > 0
                    else "Штраф за неудачную попытку: 0$"
                ),
                kb_for_peer(reply_peer),
            )
            return

        steal_amount = max(1, target_balance // 100)
        cursor.execute("SELECT balance FROM users WHERE user_id = ?", (user_id,))
        arow = cursor.fetchone()
        attacker_balance = int(arow[0]) if arow else 0
        cursor.execute(
            "UPDATE users SET balance = ? WHERE user_id = ?",
            (max(0, target_balance - steal_amount), int(target_id)),
        )
        cursor.execute(
            "UPDATE users SET balance = ?, last_steal_at = ? WHERE user_id = ?",
            (attacker_balance + steal_amount, float(now_steal), int(user_id)),
        )
        cursor.execute(
            "UPDATE users SET event_success_rob_count = COALESCE(event_success_rob_count, 0) + 1 WHERE user_id = ?",
            (int(user_id),),
        )
        db.commit()

        attacker_name = get_user_name(user_id)
        send_msg(
            reply_peer,
            "✅ Питомец успешно атаковал цель\n\n"
            f"Ваш питомец: {pet_name_me} (сила {pet_power_me})\n"
            f"Питомец цели: {tpet_name} (сила {tpet_power})\n"
            f"Добыча: {format_click(steal_amount)}$ (1% баланса цели)\n"
            f"Новый баланс: {format_click(attacker_balance + steal_amount)}$",
            kb_for_peer(reply_peer),
        )
        send_msg(
            target_id,
            "⚠ Вас атаковали питомцем\n\n"
            f"[id{user_id}|{attacker_name}] натравил на вас своего питомца и вы потеряли 1% баланса.\n"
            "Советуем приобрести более сильного питомца.\n"
            f"Потеря: {format_click(steal_amount)}$",
            kb_for_peer(target_id),
        )
        for _m in _check_personal_event_progress_and_rewards(user_id):
            send_msg(reply_peer, _m, kb_for_peer(reply_peer))

    elif payload_cmd == 'feed_all':
        boost_active = (click_boost_until or 0) > time.time()
        fixed_cost = int(get_economy_feed_all_cost())
        if fed >= 100: send_msg(reply_peer, "Питомец уже полностью сыт!", get_pet_kb(balance, fed, pet_power_me, show_info=True, owner_user_id=user_id, boost_active=boost_active))
        else:
            fp = get_effective_feed_portion(boost_active=boost_active)
            if fp <= 0:
                fp = 1
            if balance < fixed_cost:
                send_msg(
                    reply_peer,
                    f"Нужно {format_click(fixed_cost)}$ на кошельке (кнопка «за все деньги» — фиксированная цена).",
                    get_pet_kb(balance, fed, pet_power_me, show_info=True, owner_user_id=user_id, boost_active=boost_active),
                )
            else:
                buy = min(100 - fed, fixed_cost // fp)
                if buy <= 0:
                    send_msg(
                        reply_peer,
                        f"При цене {format_click(fp)}$ за 1% суммы {format_click(fixed_cost)}$ не хватает на целый процент сытости.",
                        get_pet_kb(balance, fed, pet_power_me, show_info=True, owner_user_id=user_id, boost_active=boost_active),
                    )
                else:
                    update_user(user_id, 'balance', balance - fixed_cost)
                    update_user(user_id, 'fed', fed + buy)
                    discount_note = f"\n👑 Скидка подписки на корм: -{SUB_FEED_DISCOUNT_PERCENT}%" if boost_active else ""
                    send_msg(
                        reply_peer,
                        f"Ты покормил питомца на +{buy}%!\nПотрачено: {format_click(fixed_cost)}${discount_note}\nТекущая сытость: {fed + buy}%",
                        get_pet_kb(balance - fixed_cost, fed + buy, pet_power_me, show_info=True, owner_user_id=user_id, boost_active=boost_active),
                    )

    elif payload_cmd == 'pet_upgrade':
        if is_pet_max_level(pet_power_me):
            send_msg(
                reply_peer,
                f"Питомец уже достиг максимального уровня ({MAX_PET_LEVEL}).",
                get_pet_kb(balance, fed, pet_power_me, show_info=True, owner_user_id=user_id),
            )
            return
        cost = pet_upgrade_cost(pet_power_me)
        if balance < cost:
            send_msg(
                reply_peer,
                f"Недостаточно денег для улучшения питомца.\nНужно: {format_click(cost)}$\nСейчас: {format_click(balance)}$",
                    get_pet_kb(balance, fed, pet_power_me, show_info=True, owner_user_id=user_id, boost_active=(click_boost_until or 0) > time.time()),
            )
            return
        new_power = pet_power_me + 1
        new_name = _pet_name_by_level(new_power)
        update_user(user_id, 'balance', balance - cost)
        update_user(user_id, 'pet_id', new_power)
        update_user(user_id, 'pet_name', new_name)
        send_msg(
            reply_peer,
            f"🐾 Питомец улучшен!\nНовая форма: {new_name}\nСила: {new_power}\nСписано: {format_click(cost)}$",
            get_pet_kb(balance - cost, fed, new_power, show_info=True, owner_user_id=user_id),
        )

    elif _is_klad_command_text(text) or payload_cmd == RESTRICTED_KLAD_CMD:
        send_msg(reply_peer, "🏴‍☠️ Клады отключены. Используйте команду «ограбление».", kb_for_peer(reply_peer))
        return

    elif _is_heist_command_text(text) or payload_cmd == 'heist_run':
        if _is_multichat_peer(reply_peer):
            send_msg(reply_peer, "Ограбление доступно только в личных сообщениях с ботом.", kb_for_peer(reply_peer))
            return
        now_heist = time.time()
        cursor.execute(
            "SELECT COALESCE(heist_last_at, 0), COALESCE(heist_jail_until, 0) FROM users WHERE user_id = ?",
            (int(user_id),),
        )
        hrow = cursor.fetchone() or (0, 0)
        heist_last_at = float(hrow[0] or 0)
        heist_jail_until = float(hrow[1] or 0)
        if heist_jail_until > now_heist:
            send_msg(
                reply_peer,
                f"🚔 Вы в тюрьме за неудачное ограбление.\nДо освобождения: {format_time_left_sec(heist_jail_until - now_heist)}.",
                kb_for_peer(reply_peer),
            )
            return
        if heist_last_at > 0 and (now_heist - heist_last_at) < HEIST_COOLDOWN_SEC:
            wait = HEIST_COOLDOWN_SEC - (now_heist - heist_last_at)
            send_msg(
                reply_peer,
                f"⏳ Ограбление можно совершать раз в 24 часа.\nСледующая попытка через {format_time_left_sec(wait)}.",
                kb_for_peer(reply_peer),
            )
            return
        cursor.execute("SELECT user_id, balance FROM users WHERE referrer_id = ?", (int(user_id),))
        refs = cursor.fetchall()
        ref_count = len(refs)
        if ref_count <= 0:
            send_msg(reply_peer, "Для ограбления нужны рабы. Пригласите хотя бы 1 человека по реф-ссылке.", get_ref_kb())
            return
        cursor.execute("UPDATE users SET heist_last_at = ? WHERE user_id = ?", (float(now_heist), int(user_id)))
        if random.random() < HEIST_FAIL_CHANCE:
            fine = max(1, (int(balance) * HEIST_FAIL_FINE_PERCENT) // 100)
            new_bal = max(0, int(balance) - fine)
            jail_until = now_heist + HEIST_JAIL_SEC
            cursor.execute(
                "UPDATE users SET balance = ?, heist_jail_until = ? WHERE user_id = ?",
                (int(new_bal), float(jail_until), int(user_id)),
            )
            db.commit()
            send_msg(
                reply_peer,
                f"❌ Ограбление провалилось.\n"
                f"Штраф: -{HEIST_FAIL_FINE_PERCENT}% ({format_click(fine)}$)\n"
                f"🚔 Вы отправлены в тюрьму на 6 часов.\n"
                f"Освобождение через: {format_time_left_sec(HEIST_JAIL_SEC)}\n"
                f"Новый баланс: {format_click(new_bal)}$",
                kb_for_peer(reply_peer),
            )
            return
        min_mk = HEIST_MIN_MK
        max_mk = min(HEIST_MAX_MK_CAP, HEIST_MK_BASE + ref_count * HEIST_MK_PER_REF)
        reward_mk = random.randint(min_mk, max_mk)
        base_reward = reward_mk * 1_000_000_000
        reward = int(base_reward)
        new_bal = int(balance) + int(reward)
        cursor.execute(
            "UPDATE users SET balance = ?, heist_jail_until = 0, "
            "total_earned_from_heists = COALESCE(total_earned_from_heists, 0) + ? "
            "WHERE user_id = ?",
            (int(new_bal), int(reward), int(user_id)),
        )
        db.commit()
        robber_name = get_user_name(user_id)
        send_msg(
            reply_peer,
            f"💣 Вы пошли грабить банк с {ref_count} рабами.\n"
            f"👤 Лидер ограбления: {robber_name}\n"
            f"💰 Добыча банка: {reward_mk}мк ({format_click(base_reward)}$)\n"
            f"💵 Итого за ограбление: {format_click(reward)}$\n"
            f"Новый баланс: {format_click(new_bal)}$",
            kb_for_peer(reply_peer),
        )
        return

    elif payload_cmd == RESTRICTED_TOPS_MENU_CMD and _is_multichat_peer(reply_peer):
        send_msg(reply_peer, "🏆 Какой топ показать? Выберите вариант:", get_top_choice_kb(user_id))
        return

    elif payload_cmd == CASINO_MENU_CMD:
        if not _runtime_ui_show_casino_help():
            return
        if not _casino_enabled():
            send_msg(reply_peer, "🎰 Казино временно выключено владельцем.", kb_for_peer(reply_peer))
            return
        send_msg(reply_peer, _casino_help_text(), kb_for_peer(reply_peer))
        return

    elif _casino_is_command(text):
        if not _runtime_ui_show_casino_help():
            return
        if not _casino_enabled():
            send_msg(reply_peer, "🎰 Казино временно выключено владельцем.", kb_for_peer(reply_peer))
            return
        if not is_registered:
            send_msg(reply_peer, "Сначала зарегистрируйтесь в боте сообщества.", kb_for_peer(reply_peer))
            return
        if is_banned:
            send_msg(reply_peer, "Для вас недоступно.", kb_for_peer(reply_peer))
            return
        cursor.execute("SELECT COALESCE(casino_last_at, 0) FROM users WHERE user_id = ?", (int(user_id),))
        _cas_last = float((cursor.fetchone() or [0])[0] or 0)
        _now_cas = time.time()
        if _cas_last > 0 and (_now_cas - _cas_last) < float(CASINO_COOLDOWN_SEC):
            _left_cd = max(1, int(math.ceil(float(CASINO_COOLDOWN_SEC) - (_now_cas - _cas_last))))
            send_msg(
                reply_peer,
                f"⏳ Казик на перезарядке. Следующая попытка через {format_time_left_sec(_left_cd)}.",
                kb_for_peer(reply_peer),
            )
            return
        raw = _strip_club_prefix_raw(text).strip()
        parts = raw.split(None, 1)
        bet_raw = (parts[1] if len(parts) > 1 else "").strip()
        if not bet_raw:
            bet = CASINO_DEFAULT_BET
        else:
            first_w = bet_raw.split(None, 1)[0]
            if _casino_token_means_all_balance(first_w):
                cursor.execute("SELECT COALESCE(balance, 0) FROM users WHERE user_id = ?", (int(user_id),))
                cash_all = int((cursor.fetchone() or [0])[0] or 0)
                bet = min(max(cash_all, 0), CASINO_MAX_BET)
                if bet < CASINO_MIN_BET:
                    send_msg(
                        reply_peer,
                        f"На «всё» не хватает наличных (нужно ≥ {format_balance(CASINO_MIN_BET)}).",
                        kb_for_peer(reply_peer),
                    )
                    return
            else:
                try:
                    bet = parse_amount(bet_raw)
                except Exception:
                    send_msg(
                        reply_peer,
                        "Не удалось разобрать ставку. Примеры: казик 10, казик 1мк, казик вб, казик всё",
                        kb_for_peer(reply_peer),
                    )
                    return
        bet = int(bet)
        if bet < CASINO_MIN_BET:
            send_msg(
                reply_peer,
                f"Минимальная ставка — {format_balance(CASINO_MIN_BET)} монет.",
                kb_for_peer(reply_peer),
            )
            return
        if bet > CASINO_MAX_BET:
            send_msg(
                reply_peer,
                f"Максимальная ставка — 5мм ({format_click(CASINO_MAX_BET)}).",
                kb_for_peer(reply_peer),
            )
            return
        cursor.execute("SELECT COALESCE(balance, 0) FROM users WHERE user_id = ?", (int(user_id),))
        cur_before = int((cursor.fetchone() or [0])[0] or 0)
        if cur_before < bet:
            send_msg(
                reply_peer,
                f"Недостаточно монет для ставки {format_balance(bet)}. Сейчас: {format_balance(cur_before)}.",
                kb_for_peer(reply_peer),
            )
            return
        net_delta, reels, head = _casino_spin_round(user_id, bet, cur_before)
        cursor.execute(
            "UPDATE users SET balance = balance + ? WHERE user_id = ? AND COALESCE(balance, 0) >= ?",
            (int(net_delta), int(user_id), int(bet)),
        )
        if cursor.rowcount != 1:
            send_msg(
                reply_peer,
                "Не удалось списать ставку (баланс изменился). Попробуйте ещё раз.",
                kb_for_peer(reply_peer),
            )
            return
        db.commit()
        update_user_fields(user_id, casino_last_at=float(time.time()))
        cursor.execute("SELECT COALESCE(balance, 0) FROM users WHERE user_id = ?", (int(user_id),))
        new_bal = int((cursor.fetchone() or [0])[0] or 0)
        r1, r2, r3 = reels
        box = _casino_slot_box(r1, r2, r3)
        if net_delta > 0:
            itog_line = f"🔺 Итог: +{format_balance(net_delta)} монет"
        elif net_delta < 0:
            itog_line = f"🔻 Итог: -{format_balance(abs(net_delta))} монет"
        else:
            itog_line = "➖ Итог: 0 монет"
        msg_out = (
            f"{head}\n\n"
            f"{box}\n\n"
            f"💎 Ставка: {format_balance(bet)} монет\n"
            f"{itog_line}\n\n"
            f"💰 Ваш баланс: {format_balance(new_bal)} монет"
        )
        send_msg(reply_peer, msg_out, kb_for_peer(reply_peer))
        return

    elif payload_cmd in ('top_refs', 'top_balance', 'top_spam', 'top_klad', 'top_donations', 'top_withdrawals'):
        if payload_cmd == 'top_refs':
            send_msg(reply_peer, _admin_op_top_refs_text(user_id), kb_for_peer(reply_peer), disable_mentions=True)
        elif payload_cmd == 'top_balance':
            send_msg(reply_peer, _admin_op_top_bal_text(user_id), kb_for_peer(reply_peer), disable_mentions=True)
        elif payload_cmd == 'top_donations':
            send_msg(reply_peer, _admin_op_top_donations_text(user_id), kb_for_peer(reply_peer), disable_mentions=True)
        elif payload_cmd == 'top_withdrawals':
            send_msg(reply_peer, _admin_op_top_withdrawals_text(user_id), kb_for_peer(reply_peer), disable_mentions=True)
        elif payload_cmd == 'top_klad':
            send_msg(reply_peer, "🏴‍☠️ Топ по кладу отключён.", kb_for_peer(reply_peer))
        else:
            send_msg(reply_peer, _admin_op_top_spam_text(user_id), kb_for_peer(reply_peer), disable_mentions=True)
        return

    elif (_is_multichat_peer(reply_peer) and _is_profile_request_chat(text, payload_cmd)) or (
        not _is_multichat_peer(reply_peer) and (cmd_text in ('профиль', 'я', 'б', 'баланс') or payload_cmd == PROFILE_CHAT_CMD)
    ):
        if _is_multichat_peer(reply_peer):
            profile_uid, err = _restricted_profile_subject_uid(event.obj.message, text, payload_cmd, user_id)
            if err:
                send_msg(reply_peer, err, kb_for_peer(reply_peer))
            else:
                cmid = event.obj.message.get('conversation_message_id')
                send_profile_card(
                    reply_peer,
                    profile_uid,
                    viewer_user_id=user_id,
                    reply_to_cmid=cmid,
                )
        else:
            send_profile_card(reply_peer, user_id)

    elif len(promo_pair) == 2 and promo_pair[0].lower() == 'промо':
        _pkb = (
            kb_for_peer(reply_peer)
            if _is_multichat_peer(reply_peer)
            else get_main_kb()
        )
        if is_banned:
            send_msg(reply_peer, "Вы в бане и не можете активировать промокоды.", _pkb)
        else:
            _, pr_msg = redeem_promocode(user_id, promo_pair[1])
            promo_kb = get_promo_join_chat_kb() if "недействителен" in (pr_msg or "").lower() else _pkb
            send_msg(reply_peer, pr_msg, promo_kb)

    elif cmd_text == 'help':
        if _is_admin_user(user_id) or _is_owner(user_id) or _is_deputy_owner(user_id):
            send_msg(reply_peer, _admin_commands_help_text(user_id), _get_help_kb(allow_ask=not _is_multichat_peer(reply_peer)))
        else:
            send_msg(reply_peer, _user_commands_help_text(), _get_help_kb(allow_ask=not _is_multichat_peer(reply_peer)))

    elif cmd_text == 'помощь':
        send_msg(
            reply_peer,
            _admins_help_text() + "\n\nВыберите раздел ниже: «Команды» или «Вопросы».",
            _get_help_kb(allow_ask=not _is_multichat_peer(reply_peer)),
        )

    elif cmd_text in ('промокоды', 'промолист') and _can_use_promolist(user_id):
        send_msg(reply_peer, promolist_admin_text(), kb_for_peer(reply_peer))

    elif cmd_text in ['команды', 'меню команд']:
        send_msg(reply_peer, _user_commands_help_text(), _get_help_kb(allow_ask=not _is_multichat_peer(reply_peer)))

    elif cmd_text == 'вопросы':
        send_msg(reply_peer, _user_faq_help_text(), _get_help_kb(allow_ask=not _is_multichat_peer(reply_peer)))

    elif cmd_text == 'конкурс' or payload_cmd == 'contest_public':
        row = _get_active_contest_row()
        if not row:
            send_msg(
                reply_peer,
                "Сейчас нет активного розыгрыша. Следите за новостями сообщества.",
                kb_for_peer(reply_peer),
            )
            return
        send_msg(reply_peer, _public_contest_menu_text(row), kb_for_peer(reply_peer))
        return

    elif cmd_text in ("участие", "участвую"):
        if not is_registered:
            send_msg(reply_peer, "Сначала зарегистрируйтесь в боте сообщества.", kb_for_peer(reply_peer))
            return
        _ok, _st = _register_contest_participation(user_id)
        if not _ok:
            if _st == "no_contest":
                send_msg(reply_peer, "Сейчас нет активного розыгрыша от бота.", kb_for_peer(reply_peer))
            else:
                send_msg(reply_peer, "Не удалось записать участие. Попробуйте позже.", kb_for_peer(reply_peer))
            return
        if _st == "already":
            send_msg(reply_peer, "Вы уже участвуете в текущем розыгрыше.", kb_for_peer(reply_peer))
        else:
            send_msg(reply_peer, "✅ Вы записаны в участники текущего розыгрыша.", kb_for_peer(reply_peer))
        return

    elif payload_cmd == 'help_commands':
        send_msg(reply_peer, _user_commands_help_text(), _get_help_kb(allow_ask=not _is_multichat_peer(reply_peer)))

    elif payload_cmd == 'help_faq':
        send_msg(reply_peer, _user_faq_help_text(), _get_help_kb(allow_ask=not _is_multichat_peer(reply_peer)))

    elif cmd_text.startswith('//baninfo') and _can_use_baninfo(user_id):
        parts = _strip_club_prefix_raw(text).split(None, 1)
        if len(parts) < 2:
            send_msg(reply_peer, "Формат: //baninfo [юзер]", get_main_kb())
        else:
            tid = get_id_by_domain(parts[1])
            if not tid:
                send_msg(reply_peer, "Не удалось найти юзера.", get_main_kb())
            else:
                send_msg(reply_peer, _baninfo_text_for_target(tid), get_main_kb())

    elif cmd_text in ['рефка', 'рефералы', 'рабы']:
        cursor.execute("SELECT balance FROM users WHERE referrer_id = ?", (user_id,))
        refs = cursor.fetchall()
        ref_count = len(refs)
        cursor.execute(
            "SELECT COALESCE(total_earned_from_heists, 0) FROM users WHERE user_id = ?",
            (user_id,),
        )
        tr = cursor.fetchone() or (0,)
        total_heists = int(tr[0] or 0)
        ref_link = f"https://vk.ru/write-{GROUP_ID}?ref={user_id}"
        msg = (
            f"🔗 Ваша реферальная система\n\n👥 Количество рабов: {format_balance(ref_count)}\n"
            f"💣 Заработано на ограблениях: {format_click(total_heists)}$\n\n"
            f"Отправляй эту ссылку друзьям. Как только они пройдут регистрацию — станут твоими рабами!\n{ref_link}"
        )
        send_msg(reply_peer, msg, get_ref_kb())

    elif payload_cmd == 'ref_post':
        send_msg(reply_peer, build_ref_post_text(user_id), get_ref_kb())

    elif payload_cmd == 'withdraw':
        min_w = 5_000_000_000_000
        max_w = 20_000_000_000_000
        cursor.execute("SELECT COALESCE(pascha_full_withdraw, 0) FROM users WHERE user_id = ?", (int(user_id),))
        _pfw = cursor.fetchone()
        pascha_fw = int((_pfw[0] if _pfw else 0) or 0)
        if pascha_fw:
            min_w = 1
            max_w = 10**30
        if int(is_twin_db or 0) == 1:
            return send_msg(
                reply_peer,
                "⛔ У аккаунта метка «твинк»: вывод валюты недоступен. Играть и получать деньги можно.",
                kb_for_peer(reply_peer),
            )
        cursor.execute(
            "SELECT id, amount FROM withdrawals WHERE user_id = ? AND status = 'Ожидает отправки' ORDER BY id DESC LIMIT 1",
            (int(user_id),),
        )
        pending_withdraw = cursor.fetchone()
        if pending_withdraw:
            pending_amount = int(pending_withdraw[1] or 0)
            return send_msg(
                reply_peer,
                "У вас уже есть заявка на вывод, которая ожидает одобрения.\n"
                f"Текущая заявка: {format_withdraw_mm_plain(pending_amount)}.\n"
                "Дождитесь обработки перед отправкой следующей.",
                kb_for_peer(reply_peer),
            )
        if VERIFICATION_GROUP_SCREEN and not _vk_subscription_fully_ok(int(user_id)):
            if VERIFICATION_COOPERATION_ENABLED:
                return send_msg(
                    reply_peer,
                    "Для вывода нужно состоять в группе бота и в сообществе для проверки.\n"
                    "Вступите в оба сообщества и нажмите «Я подписался».",
                    get_subscribe_kb(int(user_id), include_sponsor_link=True),
                )
            return send_msg(
                reply_peer,
                "Для вывода нужно состоять в группе бота.\n"
                "Вступите в сообщество и нажмите «Я подписался».",
                get_subscribe_kb(int(user_id), include_sponsor_link=False),
            )
        locked_repost = _repost_locked_amount(user_id)
        available_balance = max(0, int(balance) - int(locked_repost))
        if not pascha_fw and int(available_balance) < int(min_w):
            if locked_repost > 0:
                return send_msg(
                    reply_peer,
                    f"На вывод доступно: {format_withdraw_mm_plain(available_balance)}.\n"
                    f"Заблокировано по репостам до конца суток: {format_withdraw_mm_plain(locked_repost)}.\n"
                    f"Минимальная сумма вывода {format_withdraw_mm_plain(min_w)}.",
                    kb_for_peer(reply_peer),
                )
            return send_msg(
                reply_peer,
                f"Минимальная сумма вывода {format_withdraw_mm_plain(min_w)}.",
                kb_for_peer(reply_peer),
            )
        if pascha_fw and int(available_balance) <= 0:
            update_user(user_id, "pascha_full_withdraw", 0)
            return send_msg(
                reply_peer,
                "Подарок «полный вывод» недоступен: на балансе нет наличных (с учётом блокировок по репостам).",
                kb_for_peer(reply_peer),
            )
        amount = min(int(available_balance), int(max_w))
        new_cash = max(0, int(balance) - amount)
        if pascha_fw:
            update_user_fields(user_id, balance=new_cash, pascha_full_withdraw=0)
        else:
            update_user(user_id, "balance", new_cash)

        username = get_user_name(user_id)
            
        comment_id = 0
        if vk_user:
            try: comment_id = vk_user.board.createComment(group_id=GROUP_ID, topic_id=57395405, message=build_board_msg(user_id, username, amount, "Ожидает отправки"), from_group=1)
            except: pass

        cursor.execute("INSERT INTO withdrawals (user_id, amount, comment_id, status) VALUES (?, ?, ?, ?)", (user_id, amount, comment_id, 'Ожидает отправки'))
        db.commit()
        new_wid = int(cursor.lastrowid or 0)
        warn_banned = "\n⚠️ ПОЛЬЗОВАТЕЛЬ В БАНЕ!" if is_banned else ""
        amt_line_user = format_withdraw_mm_plain(amount)
        amt_line_admin = format_withdraw_mm_rounded(amount)
        _withdraw_tail = (
            f"{warn_banned}\n"
            f"Пользователь: @id{user_id} ({username})\n"
            f"Сумма: {amt_line_admin}"
        )
        withdraw_notify_text = f"🔔 Новая заявка на вывод{_withdraw_tail}"
        mid_blast = send_msg(
            ADMIN_CHAT_PEER_ID,
            f"🔔 НОВАЯ ЗАЯВКА НА ВЫВОД{_withdraw_tail}",
        )
        if new_wid > 0 and mid_blast:
            _withdraw_store_chat_blast(new_wid, int(ADMIN_CHAT_PEER_ID), mid_blast)
        admin_dm_sent = False
        if int(reply_peer) != int(ADMIN_ID):
            send_msg(int(ADMIN_ID), withdraw_notify_text, get_main_kb())
            admin_dm_sent = True
        for _nid in WITHDRAWAL_NOTIFY_USER_IDS:
            if int(_nid) == int(ADMIN_ID) and admin_dm_sent:
                continue
            send_msg(int(_nid), withdraw_notify_text, get_main_kb())
        send_msg(
            reply_peer,
            (
                f"Заявка на вывод отправлена (вы в бане).\nСумма: {amt_line_user}"
                if is_banned
                else (
                    "Заявка на вывод успешно создана! Ожидайте выплаты.\n"
                    f"Сумма: {amt_line_user}"
                    + (
                        f"\n\nℹ️ Лимит за одну заявку: {format_withdraw_mm_plain(max_w)}. "
                        "Остаток можете вывести следующей заявкой."
                        if int(available_balance) > int(max_w)
                        else ""
                    )
                )
            ),
            kb_for_peer(reply_peer),
        )

    elif cmd_text == 'о боте':
        stats_txt = "\n".join(get_bot_stats_lines())
        try:
            cursor.execute(
                "SELECT COALESCE(SUM(amount), 0) FROM withdrawals WHERE status = 'Успешно выполнена'"
            )
            paid_total = int(cursor.fetchone()[0] or 0)
        except Exception:
            paid_total = 0
        stats_att = STATS_ATTACHMENT if _valid_photo_attachment(STATS_ATTACHMENT) else None
        send_msg(
            reply_peer,
            f"📊 О боте\n\n{stats_txt}\n💸 Выведено за всё время: {format_click(paid_total)}$\n\n"
            f"По вопросам: @molokanov.offical",
            get_about_kb(),
            attachment=stats_att,
        )

    elif cmd_text == 'магазин' or payload_cmd in ('shop_buy_click_boost', 'shop_buy_steal_fast', 'shop_buy_steal_shield'):
        now_shop = time.time()

        if payload_cmd == 'shop_buy_click_boost':
            if (click_boost_until or 0) > now_shop:
                left = max(1, int(float(click_boost_until) - now_shop))
                send_msg(
                    reply_peer,
                    "Усилитель клика ещё активен.\n"
                    f"Осталось: {format_time_left_sec(left)}\n\n"
                    "Можно купить другие улучшения (ускорение атаки или щит), если они ещё не активны.",
                    get_shop_kb(),
                )
                return
            _cb_price = int(get_economy_click_boost_price())
            _cb_bonus = int(get_economy_click_boost_bonus())
            _cb_days = int(get_economy_click_boost_days())
            if balance < _cb_price:
                send_msg(
                    reply_peer,
                    "Не хватает денег для покупки усилителя клика.\n"
                    f"Нужно: {format_short(_cb_price)}$\n"
                    f"Сейчас у вас: {format_click(balance)}$",
                    get_shop_kb(),
                )
            else:
                now = time.time()
                new_until = now + _cb_days * 86400
                update_user_fields(
                    user_id,
                    balance=balance - _cb_price,
                    click_boost_until=new_until,
                    shop_click_boost_expire_notified=0,
                )
                send_msg(
                    reply_peer,
                    "✅ Покупка успешна: усилитель клика активирован.\n"
                    f"Срок до: {datetime.fromtimestamp(new_until, timezone.utc).strftime('%d.%m.%Y %H:%M')} UTC\n"
                    f"Бонус: +{format_short(_cb_bonus)}$ за каждый клик\n"
                    f"Длительность: {_cb_days} дн.\n"
                    f"Списано: {format_short(_cb_price)}$",
                    kb_for_peer(reply_peer),
                )
        elif payload_cmd == 'shop_buy_steal_fast':
            if (steal_fast_until or 0) > now_shop:
                left = max(1, int(float(steal_fast_until) - now_shop))
                send_msg(
                    reply_peer,
                    "Ускорение атаки питомцем ещё активно.\n"
                    f"Осталось: {format_time_left_sec(left)}\n\n"
                    "Можно купить другие улучшения (усилитель клика или щит), если они ещё не активны.",
                    get_shop_kb(),
                )
                return
            if balance < STEAL_FAST_PRICE_PER_DAY:
                send_msg(
                    reply_peer,
                    "Не хватает денег для ускорения атаки питомцем.\n"
                    f"Нужно: {format_short(STEAL_FAST_PRICE_PER_DAY)}$\n"
                    f"Сейчас у вас: {format_click(balance)}$",
                    get_shop_kb(),
                )
            else:
                now = time.time()
                new_until = now + 86400
                update_user_fields(
                    user_id,
                    balance=balance - STEAL_FAST_PRICE_PER_DAY,
                    steal_fast_until=new_until,
                    shop_steal_fast_expire_notified=0,
                )
                send_msg(
                    reply_peer,
                    "✅ Покупка успешна: ускорение атаки питомцем активировано.\n"
                    f"Срок до: {datetime.fromtimestamp(new_until, timezone.utc).strftime('%d.%m.%Y %H:%M')} UTC\n"
                    "Теперь натравить питомца можно каждые 2 часа (вместо 3)\n"
                    f"Списано: {format_short(STEAL_FAST_PRICE_PER_DAY)}$",
                    kb_for_peer(reply_peer),
                )
        elif payload_cmd == 'shop_buy_steal_shield':
            if (steal_shield_until or 0) > now_shop:
                left = max(1, int(float(steal_shield_until) - now_shop))
                send_msg(
                    reply_peer,
                    "Щит от атак питомцем ещё активен.\n"
                    f"Осталось: {format_time_left_sec(left)}\n\n"
                    "Можно купить другие улучшения (усилитель клика или ускорение атаки), если они ещё не активны.",
                    get_shop_kb(),
                )
                return
            if balance < STEAL_SHIELD_PRICE:
                send_msg(
                    reply_peer,
                    "Не хватает денег для покупки щита от атак питомцем.\n"
                    f"Нужно: {format_short(STEAL_SHIELD_PRICE)}$\n"
                    f"Сейчас у вас: {format_click(balance)}$",
                    get_shop_kb(),
                )
            else:
                now = time.time()
                new_until = now + STEAL_SHIELD_DURATION_SEC
                update_user_fields(
                    user_id,
                    balance=balance - STEAL_SHIELD_PRICE,
                    steal_shield_until=new_until,
                    shop_steal_shield_expire_notified=0,
                )
                send_msg(
                    reply_peer,
                    "🛡 Покупка успешна: щит от атак питомцем активирован.\n"
                    f"Срок до: {datetime.fromtimestamp(new_until, timezone.utc).strftime('%d.%m.%Y %H:%M')} UTC\n"
                    "На время действия щита вас нельзя атаковать питомцем.\n"
                    f"Списано: {format_short(STEAL_SHIELD_PRICE)}$",
                    kb_for_peer(reply_peer),
                )
        else:
            send_msg(
                reply_peer,
                "🛒 Магазин\n\n"
                f"1) Усилитель клика ({get_economy_click_boost_days()} дн.)\n"
                f"+{format_short(get_economy_click_boost_bonus())} к каждому клику\n"
                f"Цена: {format_short(get_economy_click_boost_price())}$\n\n"
                "2) Ускорение атаки питомцем (1 день)\n"
                "Натравить питомца можно каждые 2 часа вместо 3\n"
                f"Цена: {format_short(STEAL_FAST_PRICE_PER_DAY)}$\n\n"
                "3) Щит от атак питомцем (6 часов)\n"
                "Блокирует атаки питомцем на вас\n"
                f"Цена: {format_short(STEAL_SHIELD_PRICE)}$\n\n"
                "Все три улучшения можно купить и держать активными одновременно. "
                "Повторно купить тот же тип можно после окончания срока — о завершении напишем в ЛС.",
                get_shop_kb(),
            )

    elif cmd_text in ('пожертвование', 'пожертвовать', 'пожертвования') or payload_cmd in ('donate_pick_15', 'donate_pick_30', 'donate_pick_custom', 'donate_confirm', 'donate_cancel'):
        if _is_multichat_peer(reply_peer):
            send_msg(
                reply_peer,
                "💖 Пожертвования доступны только в личных сообщениях с ботом.\n"
                "Откройте диалог с сообществом и напишите «пожертвование» или нажмите кнопку в меню.",
                kb_for_peer(reply_peer),
            )
            return
        cursor.execute("SELECT COALESCE(balance, 0), COALESCE(donated_total, 0) FROM users WHERE user_id = ?", (int(user_id),))
        drow = cursor.fetchone() or (0, 0)
        bal_now = int(drow[0] or 0)
        donated_total_now = int(drow[1] or 0)
        try:
            cursor.execute("SELECT COALESCE(SUM(donated_total), 0) FROM users")
            donated_total_all = int((cursor.fetchone() or [0])[0] or 0)
        except Exception:
            donated_total_all = 0

        if payload_cmd == 'donate_cancel':
            update_user(user_id, 'donation_wait_custom', 0)
            update_user(user_id, 'donation_pending_amount', 0)
            send_msg(reply_peer, "Пожертвование отменено.", get_donation_kb())
            return

        if payload_cmd == 'donate_pick_custom':
            update_user(user_id, 'donation_wait_custom', 1)
            update_user(user_id, 'donation_pending_amount', 0)
            send_msg(
                reply_peer,
                "Введите сумму пожертвования следующим сообщением (например: 500мк или 1мм)."
                + _donation_menu_contest_hint(),
                get_donation_kb(),
            )
            return

        if payload_cmd in ('donate_pick_15', 'donate_pick_30'):
            pct = 15 if payload_cmd == 'donate_pick_15' else 30
            amount = max(1, (bal_now * pct) // 100)
            update_user(user_id, 'donation_pending_amount', int(amount))
            update_user(user_id, 'donation_wait_custom', 0)
            send_msg(
                reply_peer,
                f"Вы уверены, что хотите пожертвовать {pct}%?\nСумма: {format_click(amount)}$"
                + _donation_menu_contest_hint(),
                get_donation_confirm_kb(amount),
            )
            return

        if payload_cmd == 'donate_confirm':
            amount = int(payload_data.get('amt') or donation_pending_amount or 0)
            if amount <= 0:
                send_msg(reply_peer, "Некорректная сумма пожертвования.", get_donation_kb())
                return
            if bal_now < amount:
                send_msg(reply_peer, "Недостаточно средств для пожертвования.", get_donation_kb())
                return
            new_bal = bal_now - amount
            new_total = donated_total_now + amount
            cursor.execute(
                "UPDATE users SET balance = ?, donated_total = ?, donation_pending_amount = 0, donation_wait_custom = 0 WHERE user_id = ?",
                (int(new_bal), int(new_total), int(user_id)),
            )
            db.commit()
            _add_kazna(int(amount))
            amount_mm = f"{(int(amount) / 1_000_000_000_000):.1f}"
            total_mm = f"{(int(new_total) / 1_000_000_000_000):.1f}"
            balance_mm = f"{(int(new_bal) / 1_000_000_000_000):.1f}"
            send_msg(
                reply_peer,
                "💖 Спасибо за пожертвование!\n"
                f"Сумма: {amount_mm}мм$\n"
                f"Всего пожертвовано: {total_mm}мм$\n"
                f"Текущий баланс: {balance_mm}мм$\n\n"
                "💡 Жертвуя валюту, вы увеличиваете шанс проведения конкурсов в сообществе.",
                get_main_kb(),
            )
            if int(amount) >= 2_000_000_000_000:
                auto_unbanned = False
                try:
                    cursor.execute(
                        "SELECT COALESCE(is_banned, 0), COALESCE(ban_until, 0) FROM users WHERE user_id = ?",
                        (int(user_id),),
                    )
                    b_row = cursor.fetchone() or (0, 0)
                    is_banned_now = int(b_row[0] or 0) == 1 or float(b_row[1] or 0) > time.time()
                except Exception:
                    is_banned_now = False
                if is_banned_now:
                    _unban_user(
                        int(user_id),
                        issued_by=ADMIN_ID,
                        source_chat=int(reply_peer),
                        reason="Авторазбан за пожертвование 2мм+",
                    )
                    auto_unbanned = True
                    send_msg(
                        reply_peer,
                        "✅ Бан автоматически снят: вы пожертвовали 2мм или больше.",
                        get_main_kb(),
                    )
                returned_to_chat = _add_user_to_chat_if_possible(int(RESTRICTED_CHAT_PEER_ID), int(user_id))
                if returned_to_chat:
                    send_msg(
                        reply_peer,
                        "✅ Вы автоматически возвращены в официальную беседу.",
                        get_main_kb(),
                    )
                try:
                    status_parts = []
                    status_parts.append("бан снят" if auto_unbanned else "бан уже отсутствовал")
                    status_parts.append("в беседу возвращен" if returned_to_chat else "в беседу вернуть не удалось")
                    send_admin_chat_log(
                        f"[2ММ БОНУС] {get_user_mention_with_name(user_id)}\n"
                        f"Пожертвование: {format_click(amount)}$ (>= 2мм)\n"
                        f"Результат: {', '.join(status_parts)}."
                    )
                except Exception:
                    pass
            for _m in _check_personal_event_progress_and_rewards(user_id):
                send_msg(reply_peer, _m, kb_for_peer(reply_peer))
            return

        send_msg(
            reply_peer,
            "💖 Пожертвования\n\n"
            f"Пожертвовано игроком: {format_click(donated_total_now)}$\n"
            f"Пожертвовано всего: {format_click(donated_total_all)}$\n"
            f"В казне сообщества: {format_click(_get_kazna_balance())}$\n\n"
            "Выберите вариант пожертвования:"
            + _donation_menu_contest_hint(),
            get_donation_kb(),
        )
        return

    elif cmd_text == 'банк':
        send_msg(
            reply_peer,
            "Раздел «Банк» и депозиты отключены. Деньги на руках — в «профиль».\n"
            "Остаток на старом депозите можно вернуть на кошелёк: -депозит все",
            get_main_kb(),
        )
        return

    elif cmd_text == 'транзакции' or payload_cmd == 'bank_transactions':
        tx_history = _bank_transactions_text(user_id)
        send_msg(
            reply_peer,
            "🧾 История транзакций (промокоды/переводы):\n"
            f"{tx_history}",
            get_main_kb(),
        )
        return

    elif cmd_text.startswith('+депозит') or cmd_text.startswith('-депозит'):
        parts = cmd_text.split(None, 1)
        if len(parts) < 2:
            send_msg(reply_peer, "Депозиты отключены. Чтобы снять остаток с депозита: -депозит все", kb_for_peer(reply_peer))
            return
        is_plus = parts[0].startswith('+')
        arg = (parts[1] or "").strip().lower()
        cursor.execute(
            "SELECT COALESCE(balance, 0), COALESCE(bank_balance, 0) FROM users WHERE user_id = ?",
            (int(user_id),),
        )
        cur_row = cursor.fetchone() or (0, 0)
        cur_balance = int(cur_row[0] or 0)
        cur_deposit = int(cur_row[1] or 0)
        try:
            if arg in ("все", "all"):
                amount = cur_balance if is_plus else cur_deposit
            else:
                amount = int(parse_amount(arg))
        except Exception:
            send_msg(reply_peer, "Неверная сумма. Пример: -депозит 10мк", kb_for_peer(reply_peer))
            return
        if amount <= 0:
            send_msg(reply_peer, "Сумма должна быть больше нуля.", kb_for_peer(reply_peer))
            return
        if is_plus:
            send_msg(reply_peer, "Депозиты отключены. Вклады недоступны.", kb_for_peer(reply_peer))
            return
        else:
            if cur_deposit < amount:
                send_msg(reply_peer, "На депозите недостаточно средств.", kb_for_peer(reply_peer))
                return
            new_deposit = cur_deposit - amount
            new_balance = cur_balance + amount
            cursor.execute(
                "UPDATE users SET balance = ?, bank_balance = ? WHERE user_id = ?",
                (int(new_balance), int(new_deposit), int(user_id)),
            )
            db.commit()
            send_msg(
                reply_peer,
                f"✅ С депозита снято: {format_click(amount)}$\n"
                f"💵 Кошелёк: {format_click(new_balance)}$\n"
                f"🏦 Депозит: {format_click(new_deposit)}$",
                kb_for_peer(reply_peer),
            )
        return

    elif cmd_text.startswith('перевод '):
        raw_transfer = _strip_club_prefix_raw(text).strip()
        m_transfer = re.match(r'^перевод\s+(\S+)\s+(.+?)\s*$', raw_transfer, re.IGNORECASE)
        m_transfer_reply = re.match(r'^перевод\s+(.+?)\s*$', raw_transfer, re.IGNORECASE)
        target_id = None
        amount_raw = None
        if m_transfer:
            target_id = get_id_by_domain(m_transfer.group(1))
            amount_raw = m_transfer.group(2)
        elif m_transfer_reply:
            rm_transfer = event.obj.message.get('reply_message') if isinstance(event.obj.message, dict) else None
            if not rm_transfer:
                send_msg(
                    reply_peer,
                    "Формат:\n- перевод [юзер] [сумма]\n- перевод [сумма] (ответом на сообщение юзера)\nПример: перевод 40мк",
                    kb_for_peer(reply_peer),
                )
                return
            try:
                rid = rm_transfer.get('from_id')
                if rid is not None and int(rid) > 0:
                    target_id = int(rid)
            except (TypeError, ValueError):
                target_id = None
            amount_raw = m_transfer_reply.group(1)
        else:
            send_msg(
                reply_peer,
                "Формат:\n- перевод [юзер] [сумма]\n- перевод [сумма] (ответом на сообщение юзера)\nПример: перевод @ник 40мк",
                kb_for_peer(reply_peer),
            )
            return
        if not target_id:
            send_msg(reply_peer, "Юзер не найден.", kb_for_peer(reply_peer))
            return
        if not _transfer_target_allowed(user_id, target_id):
            send_msg(reply_peer, "Переводы доступны только владельцу и заму владельца.", kb_for_peer(reply_peer))
            return
        try:
            amount = int(parse_amount(amount_raw))
        except Exception:
            send_msg(reply_peer, "Неверная сумма. Пример: 40мк или 1.5мм", kb_for_peer(reply_peer))
            return
        if amount <= 0:
            send_msg(reply_peer, "Сумма должна быть больше нуля.", kb_for_peer(reply_peer))
            return

        cursor.execute(
            "SELECT COALESCE(balance, 0), COALESCE(staff_balance, 0) FROM users WHERE user_id = ?",
            (int(user_id),),
        )
        row_from = cursor.fetchone() or (0, 0)
        sender_balance = int(row_from[0] or 0)
        sender_staff = int(row_from[1] or 0)
        sender_total = sender_balance + sender_staff
        if sender_total < amount:
            send_msg(
                reply_peer,
                f"Недостаточно средств.\nНужно: {format_click(amount)}$\n"
                f"У вас: {format_click(sender_total)}$ (наличные {format_click(sender_balance)}$, служебные {format_click(sender_staff)}$)",
                kb_for_peer(reply_peer),
            )
            return

        send_msg(
            reply_peer,
            "💸 Подтверждение перевода\n\n"
            f"Получатель: {get_user_mention_with_name(target_id)}\n"
            f"Сумма: {format_click(amount)}$\n"
            + (
                f"(будет списано в первую очередь со служебного счёта, затем с наличных)\n\n"
                if sender_staff > 0
                else "\n"
            )
            + "Нажмите «Подтвердить» или «Отмена».",
            get_transfer_confirm_kb(target_id, amount, owner_user_id=user_id),
        )
        return

    elif payload_cmd in ('transfer_confirm', 'transfer_cancel'):
        if payload_cmd == 'transfer_cancel':
            send_msg(reply_peer, "❎ Перевод отменён.", kb_for_peer(reply_peer))
            return
        try:
            target_id = int(payload_data.get('uid') or 0)
            amount = int(payload_data.get('amt') or 0)
        except Exception:
            target_id, amount = 0, 0
        if target_id <= 0 or amount <= 0:
            send_msg(reply_peer, "Не удалось выполнить перевод: неверные данные.", kb_for_peer(reply_peer))
            return
        ok_tr, msg_tr = _perform_transfer(user_id, target_id, amount)
        send_msg(reply_peer, msg_tr, kb_for_peer(reply_peer))
        if ok_tr:
            cursor.execute(
                "SELECT COALESCE(balance, 0), COALESCE(staff_balance, 0) FROM users WHERE user_id = ?",
                (int(target_id),),
            )
            _tb = cursor.fetchone() or (0, 0)
            tbal = int(_tb[0] or 0) + int(_tb[1] or 0)
            send_msg(
                int(target_id),
                f"💸 Вам поступил перевод от {get_user_mention_with_name(user_id)}\n"
                f"Сумма: +{format_click(amount)}$\n"
                f"Всего на счетах: {format_click(tbal)}$",
                kb_for_peer(int(target_id)),
            )
        return

    elif cmd_text in ('топ смс', 'топспам', 'топ спам'):
        send_msg(reply_peer, _admin_op_top_spam_text(user_id), kb_for_peer(reply_peer), disable_mentions=True)
        return

    elif cmd_text in ('топ клад', 'клад топ', 'топклада', 'топклад'):
        send_msg(reply_peer, "🏴‍☠️ Топ по кладу отключён.", kb_for_peer(reply_peer))
        return

    elif cmd_text in ('топ пожертвований', 'топ пожертвование'):
        send_msg(reply_peer, _admin_op_top_donations_text(user_id), kb_for_peer(reply_peer), disable_mentions=True)
        return

    elif cmd_text in ('топ выводов', 'топ вывод'):
        send_msg(reply_peer, _admin_op_top_withdrawals_text(user_id), kb_for_peer(reply_peer), disable_mentions=True)
        return

    elif cmd_text == 'топ':
        send_msg(reply_peer, "🏆 Какой топ показать? Выберите вариант:", get_top_choice_kb(user_id))
        return

    elif cmd_text == 'ивент' or payload_cmd in ('event_menu', RESTRICTED_EVENT_INFO_CMD):
        if _is_multichat_peer(reply_peer):
            # В официальной беседе показываем живой статус викторины:
            # при активном ивенте — вопрос, приз, количество уникальных чисел и время до конца;
            # после завершения — расписание и, если недавно был победитель, информацию о нём.
            send_msg(reply_peer, _event_status_text_for_user(user_id), kb_for_peer(reply_peer))
        else:
            # Личный ивент в ЛС завершён, оставляем короткое уведомление.
            send_msg(
                reply_peer,
                "🎉 Личный ивент в боте завершён.\nСледите за новостями сообщества — когда запустим новый, сообщим отдельно.",
                kb_for_peer(reply_peer),
            )
        return

    elif _is_owner(user_id) and re.match(r"^\s*-\s*казна\s+\S", _strip_club_prefix_raw(text), re.IGNORECASE):
        raw_k = _strip_club_prefix_raw(text).strip()
        m_k = re.match(r"^-\s*казна\s+(.+)$", raw_k, re.IGNORECASE)
        if not m_k:
            send_msg(reply_peer, "Формат: -казна [сумма] (например: -казна 10мк или 1.5мм)", get_main_kb())
            return
        try:
            amt = int(parse_amount(m_k.group(1).strip()))
        except Exception:
            send_msg(reply_peer, "Неверная сумма. Пример: -казна 500мк", get_main_kb())
            return
        if amt <= 0:
            send_msg(reply_peer, "Сумма должна быть больше нуля.", get_main_kb())
            return
        k_before = _get_kazna_balance()
        if k_before < amt:
            send_msg(
                reply_peer,
                f"В казне недостаточно средств.\nВ казне: {format_click(k_before)}$\nЗапрошено: {format_click(amt)}$",
                get_main_kb(),
            )
            return
        if not _take_kazna(amt):
            send_msg(reply_peer, "Не удалось списать из казны.", get_main_kb())
            return
        cursor.execute("SELECT COALESCE(balance, 0) FROM users WHERE user_id = ?", (int(ADMIN_ID),))
        ob = int((cursor.fetchone() or [0])[0] or 0)
        new_ob = ob + int(amt)
        cursor.execute("UPDATE users SET balance = ? WHERE user_id = ?", (int(new_ob), int(ADMIN_ID)))
        db.commit()
        k_after = _get_kazna_balance()
        send_msg(
            reply_peer,
            f"✅ Из казны переведено на баланс владельца: {format_click(amt)}$\n"
            f"Баланс владельца: {format_click(new_ob)}$\n"
            f"Остаток в казне: {format_click(k_after)}$",
            get_main_kb(),
        )
        send_admin_chat_log(
            f"[КАЗНА] Списано {format_click(amt)}$ → баланс владельца @id{ADMIN_ID}.\n"
            f"Остаток казны: {format_click(k_after)}$."
        )
        return

    # --- АДМИН ПАНЕЛЬ ---
    elif text.lower().startswith('!рассылка') and user_id == ADMIN_ID:
        msg_text = text[9:].strip()
        if not msg_text: return send_msg(ADMIN_ID, "Укажите текст.", get_main_kb())
            
        attachments = []
        if 'attachments' in event.obj.message:
            for att in event.obj.message['attachments']:
                if att['type'] == 'photo':
                    photo = att['photo']
                    acc_key = f"_{photo['access_key']}" if 'access_key' in photo else ""
                    attachments.append(f"photo{photo['owner_id']}_{photo['id']}{acc_key}")
        attachment_str = ','.join(attachments) if attachments else None
        
        cursor.execute("SELECT user_id FROM users WHERE is_registered = 1")
        users_list = cursor.fetchall()
        count = 0
        send_msg(ADMIN_ID, f"⏳ Начинаю рассылку для {len(users_list)} пользователей...", get_main_kb())
        for (uid,) in users_list:
            try: send_msg(uid, f"📢 Объявление от Администрации:\n\n{msg_text}", get_main_kb(), attachment=attachment_str); count += 1
            except: pass
        send_msg(ADMIN_ID, f"✅ Рассылка успешно отправлена {count} пользователям.", get_main_kb())

    elif payload_cmd == 'admin_pay' and _can_manage_withdrawals_queue(user_id):
        try:
            wid = int(payload_wid) if payload_wid is not None else 0
            if wid > 0:
                cursor.execute(
                    "SELECT id, user_id, comment_id, amount, rating, review_text "
                    "FROM withdrawals WHERE id = ? AND status = 'Ожидает отправки' LIMIT 1",
                    (wid,),
                )
            else:
                cursor.execute(
                    "SELECT id, user_id, comment_id, amount, rating, review_text "
                    "FROM withdrawals WHERE user_id = ? AND status = 'Ожидает отправки' ORDER BY id DESC LIMIT 1",
                    (payload_uid,),
                )
            w_data = cursor.fetchone()
            if w_data:
                target_uid = int(w_data[1] or 0)
                cursor.execute("UPDATE withdrawals SET status = 'Успешно выполнена' WHERE id = ?", (int(w_data[0]),))
                db.commit()
                if vk_user and w_data[2]:
                    try:
                        username = get_user_name(target_uid)
                        vk_user.board.editComment(
                            group_id=GROUP_ID,
                            topic_id=57395405,
                            comment_id=w_data[2],
                            message=build_board_msg(target_uid, username, w_data[3], "Успешно выполнена", w_data[4], w_data[5]),
                        )
                    except: pass
                
                cursor.execute("SELECT is_banned, ban_until FROM users WHERE user_id = ?", (target_uid,))
                t_user_info = cursor.fetchone()
                is_banned = t_user_info and ((t_user_info[0] == 1) or (t_user_info[1] > time.time()))
                amt = int(w_data[3] or 0)
                send_msg(
                    target_uid,
                    f"Ваша заявка на вывод была успешно обработана администратором!\n"
                    f"Сумма: {format_withdraw_mm_plain(amt)}",
                    get_payout_success_kb() if not is_banned else get_main_kb(),
                )
                wid_done = int(w_data[0])
                done_txt = f"✅ Заявка #{wid_done} для @id{target_uid} отмечена как выплаченная."
                _withdraw_delete_chat_blast_row(wid_done)
                _withdraw_delete_dm_cmd_line(wid_done)
                if not _withdraw_edit_dm_status(wid_done, done_txt):
                    send_msg(ADMIN_ID, done_txt, get_main_kb())
                _withdraw_clear_notify_columns(wid_done)
            else:
                send_msg(ADMIN_ID, "Активная заявка на вывод не найдена.", get_main_kb())
        except: pass

    elif payload_cmd == 'admin_withdraw_cancel' and _can_manage_withdrawals_queue(user_id):
        try:
            wid = int(payload_wid) if payload_wid is not None else 0
            if wid > 0:
                cursor.execute(
                    "SELECT id, user_id, comment_id, amount FROM withdrawals WHERE id = ? AND status = 'Ожидает отправки' LIMIT 1",
                    (wid,),
                )
            else:
                cursor.execute(
                    "SELECT id, user_id, comment_id, amount FROM withdrawals WHERE user_id = ? AND status = 'Ожидает отправки' ORDER BY id DESC LIMIT 1",
                    (payload_uid,),
                )
            w_data = cursor.fetchone()
            if w_data:
                wid_row = int(w_data[0])
                target_uid = int(w_data[1] or 0)
                comment_id = w_data[2]
                amt = int(w_data[3] or 0)
                cursor.execute("UPDATE withdrawals SET status = 'Отменено' WHERE id = ?", (wid_row,))
                cursor.execute(
                    "UPDATE users SET balance = COALESCE(balance, 0) + ? WHERE user_id = ?",
                    (amt, target_uid),
                )
                db.commit()
                if vk_user and comment_id:
                    try:
                        username = get_user_name(target_uid)
                        vk_user.board.editComment(
                            group_id=GROUP_ID,
                            topic_id=57395405,
                            comment_id=comment_id,
                            message=build_board_msg(target_uid, username, amt, "Отменено"),
                        )
                    except Exception:
                        pass
                send_msg(
                    target_uid,
                    f"Заявка на вывод отменена администратором. На баланс возвращено: {format_withdraw_mm_plain(amt)}.",
                    get_main_kb(),
                )
                cancel_txt = f"↩️ Заявка #{wid_row} отменена, {format_balance(amt)}$ возвращены @id{target_uid}."
                _withdraw_delete_chat_blast_row(wid_row)
                _withdraw_delete_dm_cmd_line(wid_row)
                if not _withdraw_edit_dm_status(wid_row, cancel_txt):
                    send_msg(ADMIN_ID, cancel_txt, get_main_kb())
                _withdraw_clear_notify_columns(wid_row)
            else:
                send_msg(ADMIN_ID, "Активная заявка на вывод не найдена.", get_main_kb())
        except Exception as e:
            print(f"[admin_withdraw_cancel] {e}")

    elif payload_cmd == 'admin_deny' and _can_manage_withdrawals_queue(user_id):
        try:
            wid = int(payload_wid) if payload_wid is not None else 0
            if wid > 0:
                cursor.execute(
                    "SELECT id, user_id, comment_id FROM withdrawals WHERE id = ? AND status = 'Ожидает отправки' LIMIT 1",
                    (wid,),
                )
            else:
                cursor.execute(
                    "SELECT id, user_id, comment_id FROM withdrawals WHERE user_id = ? AND status = 'Ожидает отправки' ORDER BY id DESC LIMIT 1",
                    (payload_uid,),
                )
            w_data = cursor.fetchone()
            if w_data:
                target_uid = int(w_data[1] or 0)
                cursor.execute("UPDATE withdrawals SET status = 'Отклонено' WHERE id = ?", (int(w_data[0]),))
                db.commit()
                if vk_user and w_data[2]:
                    try:
                        username = get_user_name(target_uid)
                        vk_user.board.editComment(group_id=GROUP_ID, topic_id=57395405, comment_id=w_data[2], message=f"Пользователь @id{target_uid} ({username})\nСтатус: 🔴 Отклонено (Бан)")
                    except: pass
                send_msg(target_uid, "Вы в бане и не можете выводить деньги", get_main_kb())
                wid_d = int(w_data[0])
                deny_txt = f"❌ Заявка #{wid_d} для @id{target_uid} отклонена."
                _withdraw_delete_chat_blast_row(wid_d)
                _withdraw_delete_dm_cmd_line(wid_d)
                if not _withdraw_edit_dm_status(wid_d, deny_txt):
                    send_msg(ADMIN_ID, deny_txt, get_main_kb())
                _withdraw_clear_notify_columns(wid_d)
            else:
                send_msg(ADMIN_ID, "Активная заявка на вывод не найдена.", get_main_kb())
        except: pass

    elif _can_manage_withdrawals_queue(user_id) and (text or '').strip().lower() == '!выводы':
        _send_owner_pending_withdrawals(reply_peer)

    elif _can_manage_withdrawals_queue(user_id) and re.match(r'^\s*!vivod(?:\s+\d+)?\s*$', _strip_club_prefix_raw(text), re.IGNORECASE):
        raw_vvd = _strip_club_prefix_raw(text).strip()
        m_vvd = re.match(r'^\s*!vivod(?:\s+(\d+))?\s*$', raw_vvd, re.IGNORECASE)
        lim_vvd = int(m_vvd.group(1)) if (m_vvd and m_vvd.group(1)) else 200
        send_msg(reply_peer, f"⏳ Восстанавливаю историю выводов в обсуждении (до {lim_vvd} заявок)...", get_main_kb())
        rs = _owner_restore_withdraw_board_history(limit_rows=lim_vvd)
        if not rs.get("ok"):
            if rs.get("reason") == "no_user_token":
                send_msg(reply_peer, "Нужен валидный user_token в config.json для работы с обсуждениями.", get_main_kb())
            else:
                send_msg(reply_peer, "Не удалось восстановить историю выводов.", get_main_kb())
        else:
            send_msg(
                reply_peer,
                "✅ Восстановление истории выводов завершено.\n"
                f"Обработано: {int(rs.get('processed') or 0)}\n"
                f"Создано комментариев: {int(rs.get('created') or 0)}\n"
                f"Обновлено комментариев: {int(rs.get('edited') or 0)}\n"
                f"Ошибок: {int(rs.get('failed') or 0)}",
                get_main_kb(),
            )

    elif (text or '').strip().lower() == '/promolist' and _can_use_promolist(user_id):
        send_msg(reply_peer, promolist_admin_text(), get_main_kb())

    elif (_is_owner(user_id) or _is_deputy_owner(user_id)) and re.match(r'^\s*/гпт(?:\s+.+)?$', (text or '').strip(), re.IGNORECASE):
        m_ai = re.match(r'^\s*/гпт\s+(.+?)\s*$', _strip_club_prefix_raw(text), re.IGNORECASE)
        if not m_ai:
            send_msg(reply_peer, "Формат: /гпт [запрос]", get_main_kb())
        else:
            q_ai = (m_ai.group(1) or "").strip()
            if not q_ai:
                send_msg(reply_peer, "Введите запрос после /гпт.", get_main_kb())
            else:
                think_mid = send_msg(reply_peer, "⏳ Думаю...", None)
                ai_answer = genapi_admin_answer(
                    q_ai,
                    requester_id=user_id,
                    requester_name=get_user_name(user_id),
                    unrestricted=_genapi_unrestricted_for(user_id),
                )
                if ai_answer:
                    GPT_LAST_ANSWER[int(user_id)] = str(ai_answer)
                    send_msg(
                        reply_peer,
                        f"🤖 Ответ:\n{_format_ai_answer_for_vk(ai_answer)}",
                        get_gpt_answer_kb(),
                        disable_mentions=True,
                    )
                else:
                    send_msg(reply_peer, "Не удалось получить ответ. Попробуйте позже.", get_main_kb())
                if think_mid:
                    try:
                        vk.messages.delete(message_ids=str(int(think_mid)), delete_for_all=1)
                    except Exception:
                        pass

    elif payload_cmd == 'gpt_shorten' and (_is_owner(user_id) or _is_deputy_owner(user_id)):
        src = (GPT_LAST_ANSWER.get(int(user_id)) or "").strip()
        if not src:
            send_msg(reply_peer, "Нет последнего ответа для сокращения. Сначала используйте /гпт [запрос].", get_main_kb())
        else:
            think_mid = send_msg(reply_peer, "⏳ Сокращаю...", None)
            short_q = (
                "Сократи ответ до 3-5 коротких пунктов, без воды и без потери смысла. "
                "Только русский язык.\n\nТекст:\n" + src
            )
            short_answer = genapi_admin_answer(
                short_q,
                requester_id=user_id,
                requester_name=get_user_name(user_id),
                unrestricted=_genapi_unrestricted_for(user_id),
            )
            if short_answer:
                GPT_LAST_ANSWER[int(user_id)] = str(short_answer)
                send_msg(
                    reply_peer,
                    f"🤖 Кратко:\n{_format_ai_answer_for_vk(short_answer)}",
                    get_gpt_answer_kb(),
                    disable_mentions=True,
                )
            else:
                send_msg(reply_peer, "Не удалось сократить ответ. Попробуйте позже.", get_main_kb())
            if think_mid:
                try:
                    vk.messages.delete(message_ids=str(int(think_mid)), delete_for_all=1)
                except Exception:
                    pass

    elif _is_moderation_staff(user_id) and re.match(r"^\s*!норма\b", _strip_club_prefix_raw(text), re.IGNORECASE):
        send_msg(reply_peer, _official_norm_rules_text(), kb_for_peer(reply_peer))

    elif _can_use_admin_chat_mod_features(user_id) and (not _is_multichat_peer(reply_peer) or int(reply_peer) == int(ADMIN_CHAT_PEER_ID)) and re.match(r'^\s*!модер\s+айди\s+\d+\s*$', _strip_club_prefix_raw(text), re.IGNORECASE):
        m_mod_id = re.match(r'^\s*!модер\s+айди\s+(\d+)\s*$', _strip_club_prefix_raw(text), re.IGNORECASE)
        new_public_id = int(m_mod_id.group(1)) if m_mod_id else 0
        if new_public_id <= 0:
            send_msg(reply_peer, "Формат: !модер айди [число]", kb_for_peer(reply_peer))
        else:
            update_user(user_id, 'moderator_public_id', int(new_public_id))
            send_msg(
                reply_peer,
                f"✅ Публичный ID для ответов обновлен: @id{int(new_public_id)}",
                kb_for_peer(reply_peer),
            )

    elif _is_moderation_staff(user_id) and re.match(r"^\s*!правила\s+(ок|прочитал|ознакомлен)\s*$", _strip_club_prefix_raw(text), re.IGNORECASE):
        update_user(user_id, "staff_rules_ack", 1)
        db.commit()
        send_msg(
            reply_peer,
            "✅ Ознакомление с правилами отмечено.\nЭто будет учтено при повышении.",
            kb_for_peer(reply_peer),
        )

    elif (
        _can_use_admin_chat_mod_features(user_id)
        and (not _is_multichat_peer(reply_peer) or int(reply_peer) == int(ADMIN_CHAT_PEER_ID))
        and re.match(r"^\s*!набор\s+", _strip_club_prefix_raw(text), re.IGNORECASE)
    ):
        raw_nb = _strip_club_prefix_raw(text).strip()
        m_nb = re.match(r"^\s*!набор\s+(.+)$", raw_nb, re.IGNORECASE)
        arg_nb = (m_nb.group(1) or "").strip() if m_nb else ""
        if not arg_nb:
            send_msg(
                reply_peer,
                "Формат: !набор [юзер]",
                kb_for_peer(reply_peer),
            )
        else:
            tid_nb = get_id_by_domain(arg_nb)
            if not tid_nb:
                send_msg(reply_peer, "Не удалось определить юзера.", kb_for_peer(reply_peer))
            else:
                pdata_nb, pwarn_nb = _load_nabor_profile_from_json(tid_nb)
                send_msg(
                    reply_peer,
                    _nabor_candidate_report_text(tid_nb, pdata_nb, pwarn_nb),
                    kb_for_peer(reply_peer),
                )
        return

    elif (
        _can_use_admin_chat_mod_features(user_id)
        and int(reply_peer) == int(ADMIN_CHAT_PEER_ID)
        and re.match(r"^\s*инфо\s+\S", cmd_text.strip(), re.IGNORECASE)
    ):
        m_ainfo = re.match(r"^\s*инфо\s+(.+)$", cmd_text.strip(), re.IGNORECASE)
        arg_ainfo = (m_ainfo.group(1) or "").strip() if m_ainfo else ""
        first_ainfo = arg_ainfo.split()[0] if arg_ainfo.split() else ""
        tid_ainfo = get_id_by_domain(first_ainfo) if first_ainfo else None
        if not tid_ainfo:
            send_msg(
                reply_peer,
                "Формат: /инфо [юзер] — упоминание или ссылка на профиль ВК.\n"
                "Показывает карточку модератора (статистика, выговоры состава и т.д.).",
                kb_for_peer(reply_peer),
            )
        else:
            tid_ainfo = int(tid_ainfo)
            cursor.execute(
                "SELECT COALESCE(moderator_public_id, 0) FROM users WHERE user_id = ?",
                (tid_ainfo,),
            )
            _mpr_ainfo = cursor.fetchone()
            mod_pub_ainfo = int((_mpr_ainfo[0] if _mpr_ainfo else 0) or 0)
            send_msg(
                reply_peer,
                _format_moderator_info_message(tid_ainfo, mod_pub_ainfo, include_team_reprimands=True),
                get_moderator_info_kb(
                    tid_ainfo,
                    has_public_id=mod_pub_ainfo > 0,
                    for_admin_chat=True,
                ),
            )

    elif _is_owner(user_id) and (
        (text or '').strip().lower().startswith('!экономика')
        or (text or '').strip().lower().startswith('!эко')
    ):
        raw = (text or '').strip()
        low = raw.lower()
        if low in ('!экономика', '!эко', '!экономика показать', '!эко показать'):
            send_msg(reply_peer, economy_admin_summary_text(), get_main_kb())
        else:
            m = re.match(r'^!(?:экономика|эко)\s+(\S+)\s+(.+)$', raw.strip(), re.IGNORECASE)
            if not m:
                send_msg(
                    reply_peer,
                    "Формат: !экономика клик_низкий 35мк\n"
                    "См. полный список: !экономика",
                    get_main_kb(),
                )
            else:
                sub, amt_s = m.group(1).lower(), m.group(2).strip()
                try:
                    v = parse_amount(amt_s)
                    if v < 1:
                        raise ValueError()
                except Exception:
                    send_msg(reply_peer, "Неверная сумма. Пример: !экономика корм 18мк", get_main_kb())
                else:
                    ok_msg = None
                    if sub in ('клик_низкий', 'кликнизкий', 'кн'):
                        cursor.execute(
                            "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
                            (ECON_KEY_CLICK_LOW, v),
                        )
                        db.commit()
                        ok_msg = f"Клик при балансе ниже порога: +{format_click(v)}$"
                    elif sub in ('клик_высокий', 'кликвысокий', 'кв'):
                        cursor.execute(
                            "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
                            (ECON_KEY_CLICK_HIGH, v),
                        )
                        db.commit()
                        ok_msg = f"Клик при балансе от порога и выше: +{format_click(v)}$"
                    elif sub in ('корм', 'к'):
                        cursor.execute(
                            "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
                            (ECON_KEY_FEED, v),
                        )
                        db.commit()
                        ok_msg = f"Корм за 1% сытости: {format_click(v)}$"
                    elif sub in ('корм_все', 'кормвсе', 'квсе'):
                        cursor.execute(
                            "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
                            (ECON_KEY_FEED_ALL, v),
                        )
                        db.commit()
                        ok_msg = f"Кнопка «за все деньги»: фикс. {format_click(v)}$"
                    elif sub in ('порог', 'п'):
                        cursor.execute(
                            "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
                            (ECON_KEY_WEALTH, v),
                        )
                        db.commit()
                        ok_msg = f"Порог «богатого» клика: {format_mk_mm_pair(v)}"
                    elif sub in ('буст_цена', 'бустцена', 'бц'):
                        cursor.execute(
                            "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
                            (ECON_KEY_CLICK_BOOST_PRICE, v),
                        )
                        db.commit()
                        ok_msg = f"Цена усилителя клика в магазине: {format_click(v)}$"
                    elif sub in ('буст_бонус', 'бустбонус', 'бб'):
                        cursor.execute(
                            "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
                            (ECON_KEY_CLICK_BOOST_BONUS, v),
                        )
                        db.commit()
                        ok_msg = f"Бонус усилителя к клику: +{format_click(v)}$"
                    elif sub in ('буст_дни', 'бустдни', 'бд'):
                        try:
                            days_v = int(float(amt_s.strip().replace(',', '.')))
                        except Exception:
                            send_msg(
                                reply_peer,
                                "Укажите целое число дней. Пример: !эко бд 7",
                                get_main_kb(),
                            )
                            ok_msg = "__sent__"
                        else:
                            if days_v < 1 or days_v > 365:
                                send_msg(
                                    reply_peer,
                                    "Число дней от 1 до 365. Пример: !эко бд 7",
                                    get_main_kb(),
                                )
                                ok_msg = "__sent__"
                            else:
                                cursor.execute(
                                    "INSERT OR REPLACE INTO bot_economy (key, value) VALUES (?, ?)",
                                    (ECON_KEY_CLICK_BOOST_DAYS, int(days_v)),
                                )
                                db.commit()
                                ok_msg = f"Срок усилителя клика: {int(days_v)} дн."
                    if ok_msg == "__sent__":
                        pass
                    elif ok_msg:
                        send_msg(reply_peer, ok_msg + "\n\n" + economy_admin_summary_text(), get_main_kb())
                    else:
                        send_msg(
                            reply_peer,
                            "Неизвестная подкоманда. Варианты: клик_низкий/кн, клик_высокий/кв, корм/к, корм_все/квсе, порог/п, буст_цена/бц, буст_бонус/бб, буст_дни/бд",
                            get_main_kb(),
                        )

    elif _is_owner(user_id) and _strip_club_prefix_raw(text).strip().lower() == '!деп-':
        n_acc, total_ref = _disable_deposits_refund_everyone()
        send_msg(
            reply_peer,
            "✅ Депозиты отключены.\n"
            f"Обработано счетов с ненулевым депозитом: {n_acc}.\n"
            f"На кошельки возвращено: {format_click(total_ref)}$.",
            get_main_kb(),
        )

    elif (_is_owner(user_id) or _is_deputy_owner(user_id)) and re.match(r'^!создатьпромо\s', (text or '').strip(), re.IGNORECASE):
        cm = re.match(
            r'^!создатьпромо\s+(\S+)\s+(\S+)\s+(\d+)\s*$',
            (text or '').strip(),
            re.IGNORECASE,
        )
        if not cm:
            send_msg(
                reply_peer,
                "Формат: !создатьпромо [код] [сумма] [активации]\n"
                "Пример: !создатьпромо GIFT2026 200мк 50\n"
                "Сумма: как в !выдать — 200мк, 1.5мм или число в $.",
                get_main_kb(),
            )
        else:
            promo_code, amount_part, act_s = cm.group(1), cm.group(2), cm.group(3)
            if _is_deputy_owner(user_id):
                try:
                    amt_req = parse_amount(amount_part.strip())
                except Exception:
                    amt_req = 0
                deputy_max_single = 500_000_000_000
                promo_cnt_today = _deputy_daily_promo_count(user_id)
                if promo_cnt_today >= 3:
                    send_msg(reply_peer, "Лимит зам владельца: до 3 промокодов в сутки.", get_main_kb())
                    return
                if amt_req <= 0:
                    send_msg(reply_peer, "Неверная сумма промокода.", get_main_kb())
                    return
                if amt_req > deputy_max_single:
                    send_msg(
                        reply_peer,
                        f"Для зам владельца максимум за 1 промокод: {format_click(deputy_max_single)}$ (500мк).",
                        get_main_kb(),
                    )
                    return
            code, err = admin_create_promocode(user_id, promo_code, amount_part, int(act_s))
            if err:
                send_msg(reply_peer, err, get_main_kb())
            else:
                try:
                    amt_g = parse_amount(amount_part.strip())
                except Exception:
                    amt_g = 0
                send_msg(
                    reply_peer,
                    f"Промокод создан.\nКод: `{code}`\nНаграда: +{format_click(amt_g)}$\nАктиваций: {act_s}.",
                    get_main_kb(),
                )

    elif _is_owner(user_id) and re.match(r"^!(?:создатьпромобуст|создатьбуст)\s", _strip_club_prefix_raw(text).strip(), re.IGNORECASE):
        _boost_raw = _strip_club_prefix_raw(text).strip()
        cm_b = re.match(
            r"^!(?:создатьпромобуст|создатьбуст)\s+(\S+)\s+\+?(\d+)%?\s+(\d+)\s*([мч])\s*$",
            _boost_raw,
            re.IGNORECASE,
        )
        if not cm_b:
            cm_b = re.match(
                r"^!(?:создатьпромобуст|создатьбуст)\s+(\S+)\s+\+?(\d+)%?\s+(\d+)([мч])\s*$",
                _boost_raw,
            re.IGNORECASE,
        )
        if not cm_b:
            send_msg(
                reply_peer,
                "Формат: !создатьбуст [название] [+процент] [время] [м|ч]\n"
                "Примеры: !создатьбуст BOOST15 +15 30 м  /  !создатьбуст BOOST20 20 2 ч\n"
                "Буст создаётся с большим лимитом активаций.",
                get_main_kb(),
            )
        else:
            p_code, p_pct_s, t_num_s, t_unit = cm_b.group(1), cm_b.group(2), cm_b.group(3), (cm_b.group(4) or "").lower()
            t_num = int(t_num_s or 0)
            if t_num <= 0:
                send_msg(reply_peer, "Время должно быть больше нуля.", get_main_kb())
                return
            if t_unit == "м":
                duration_sec = t_num * 60
            else:
                duration_sec = t_num * 3600
            duration_days = max(1, math.ceil(duration_sec / 86400))
            max_acts = 1_000_000
            code_b, err_b = admin_create_promocode_click_boost(user_id, p_code, int(p_pct_s), int(max_acts), int(duration_days))
            if err_b:
                send_msg(reply_peer, err_b, get_main_kb())
            else:
                try:
                    cursor.execute(
                        "UPDATE promocodes SET boost_duration_sec = ? WHERE code = ?",
                        (int(duration_sec), code_b),
                    )
                    db.commit()
                except Exception:
                    pass
                send_msg(
                    reply_peer,
                    f"Промокод-буст создан.\nКод: `{code_b}`\n+{p_pct_s}% к выручке за клик.\nВремя: {t_num} {'мин' if t_unit == 'м' else 'ч'}.",
                    get_main_kb(),
                )

    elif _is_owner(user_id) and re.match(r'^\s*!удалитьпромо\b', _strip_club_prefix_raw(text), re.IGNORECASE):
        dm = re.match(
            r'^\s*!удалитьпромо\s+(\S+)\s*$',
            _strip_club_prefix_raw(text),
            re.IGNORECASE,
        )
        if not dm:
            send_msg(
                reply_peer,
                "Формат: !удалитьпромо [код]\n"
                "Пример: !удалитьпромо GIFT2026\n"
                "Код: латиница, цифры и _ (как при создании).",
                get_main_kb(),
            )
        else:
            _ok_del, err_del = admin_delete_promocode(dm.group(1))
            if err_del:
                send_msg(reply_peer, err_del, get_main_kb())
            else:
                send_msg(
                    reply_peer,
                    f"Промокод удалён: `{dm.group(1).strip().upper()}`",
                    get_main_kb(),
                )

    elif re.match(r'^\s*!?бан\s', (text or ''), re.IGNORECASE) and (_is_owner(user_id) or _is_deputy_owner(user_id)):
        try:
            raw_ban = _strip_club_prefix_raw(text)
            lines_ban = raw_ban.splitlines()
            first_line = (lines_ban[0] if lines_ban else "").strip()
            reason = "\n".join(lines_ban[1:]).strip() if len(lines_ban) > 1 else ""
            m_ban = re.match(r'^!?бан\s+(\S+)\s+(\S+)\s*$', first_line, re.IGNORECASE)
            if not m_ban:
                raise ValueError("format")
            target_id = get_id_by_domain(m_ban.group(1))
            if not target_id:
                return send_msg(reply_peer, "Юзер не найден.", get_main_kb())
            sec = _parse_ban_duration_seconds(m_ban.group(2), is_deputy=_is_deputy_owner(user_id))
            _, _ = get_user(target_id)
            reason = reason or ("Бан зам. владельца" if _is_deputy_owner(user_id) else "Бан администратором")
            ban_until_ts = time.time() + sec
            if _is_multichat_peer(reply_peer):
                update_user_fields(target_id, chat_ban_until=ban_until_ts, chat_banned=0)
                ban_scope = "в беседах (в ЛС с ботом игрок не заблокирован)"
            else:
                update_user(target_id, 'ban_until', ban_until_ts)
                ban_scope = "в боте (глобально)"
            _log_ban_event(target_id, reason, ban_until_ts, issued_by=user_id, source_chat=reply_peer)
            kicked = _remove_user_from_chat_if_possible(reply_peer, target_id) if _is_multichat_peer(reply_peer) else False
            send_msg(
                reply_peer,
                f"Юзер @id{target_id} забанен {ban_scope} на {format_time_left_sec(sec)}.\n"
                f"Причина: {reason}\n"
                + (
                    f"{'✅ Исключён из беседы.' if kicked else 'ℹ️ Не удалось исключить из беседы.'}"
                    if _is_multichat_peer(reply_peer)
                    else "ℹ️ Команда из ЛС: действует на всю игру в боте."
                ),
                get_main_kb(),
            )
            _log_moderator_action(user_id, "ban", 0)
            send_admin_chat_log(f"[БАН] {get_user_mention_with_name(target_id)} на {format_time_left_sec(sec)}.\nПричина: {reason}\nКто: {get_user_mention_with_name(user_id)}")
        except:
            hint = (
                "Ошибка. Формат:\nбан [юзер] [время]\nпричина\n\n"
                "Для зама максимум 30 минут. Примеры времени: 30м, 2ч, 1д."
            )
            send_msg(reply_peer, hint, get_main_kb())

    elif re.match(r'^\s*!?разбан\s', (text or ''), re.IGNORECASE) and (_is_owner(user_id) or _is_deputy_owner(user_id)):
        try:
            raw_unban = _strip_club_prefix_raw(text)
            lines_unban = raw_unban.splitlines()
            first_line = (lines_unban[0] if lines_unban else "").strip()
            reason_unban = "\n".join(lines_unban[1:]).strip() if len(lines_unban) > 1 else ""
            m_unban = re.match(r'^!?разбан\s+(\S+)\s*$', first_line, re.IGNORECASE)
            if not m_unban:
                raise ValueError("format")
            target_id = get_id_by_domain(m_unban.group(1))
            if not target_id:
                return send_msg(reply_peer, "Юзер не найден.", get_main_kb())
            reason_unban = reason_unban or ("Разбан зам. владельца" if _is_deputy_owner(user_id) else "Разбан администратором")
            ok_unban = _unban_user(target_id, issued_by=user_id, source_chat=reply_peer, reason=reason_unban)
            if not ok_unban:
                return send_msg(reply_peer, "Не удалось снять бан.", get_main_kb())
            send_msg(
                reply_peer,
                f"Юзер @id{target_id} разбанен.\nПричина: {reason_unban}",
                get_main_kb(),
            )
            send_admin_chat_log(f"[РАЗБАН] {get_user_mention_with_name(target_id)}\nПричина: {reason_unban}\nКто: {get_user_mention_with_name(user_id)}")
            _log_moderator_action(user_id, "unban", 0)
            try:
                send_msg(
                    int(target_id),
                    f"✅ Вас разбанили.\nПричина: {reason_unban}",
                    get_main_kb(),
                )
            except Exception:
                pass
        except Exception:
            send_msg(
                reply_peer,
                "Ошибка. Формат:\nразбан [юзер]\nпричина (необязательно)",
                get_main_kb(),
            )

    elif re.match(r'^\s*!?капча\s', (text or ''), re.IGNORECASE) and (_is_owner(user_id) or _is_deputy_owner(user_id)):
        try:
            parts = _strip_club_prefix_raw(text).split(None, 1)
            if len(parts) < 2:
                return send_msg(reply_peer, "Формат: !капча [юзер]", get_main_kb())
            target_id = get_id_by_domain(parts[1])
            if not target_id:
                return send_msg(reply_peer, "Юзер не найден.", get_main_kb())
            _issue_forced_captcha(target_id, reply_peer, issued_by=user_id, reason_text="Команда !капча")
        except Exception:
            send_msg(reply_peer, "Не удалось отправить капчу.", get_main_kb())

    elif re.match(r"^\s*!кд\b", _strip_club_prefix_raw(text), re.IGNORECASE) and _is_owner(user_id):
        raw_cd = _strip_club_prefix_raw(text).strip()
        target_cd = None
        m_cd_arg = re.match(r"^!кд\s+(.+)$", raw_cd, re.IGNORECASE)
        if m_cd_arg:
            target_cd = get_id_by_domain(m_cd_arg.group(1).strip().split()[0])
        else:
            msg_obj_cd = event.obj.message if isinstance(event.obj.message, dict) else {}
            rm_cd = msg_obj_cd.get("reply_message") if isinstance(msg_obj_cd, dict) else None
            if rm_cd:
                try:
                    tf = rm_cd.get("from_id")
                    target_cd = int(tf) if tf is not None else None
                except (TypeError, ValueError):
                    target_cd = None
        if not target_cd:
            send_msg(
                reply_peer,
                "Формат: !кд [юзер]\n"
                "Или ответьте на сообщение человека и напишите !кд.\n"
                "Сбрасываются кулдауны ограбления, кражи, налогов, спам-мута, принудительной капчи, ускорителей воровства и блок репост-штрафа.",
                get_main_kb(),
            )
        else:
            target_cd = int(target_cd)
            _, _ = get_user(target_cd)
            if _owner_clear_game_cooldowns(target_cd):
                send_msg(
                    reply_peer,
                    f"✅ Кулдауны сброшены для @id{target_cd} ({get_user_name(target_cd)}).",
                    get_main_kb(),
                )
                send_admin_chat_log(
                    f"[!КД] {get_user_mention_with_name(target_cd)}\nКто: {get_user_mention_with_name(user_id)}"
                )
            else:
                send_msg(reply_peer, "Не удалось сбросить кулдауны (ошибка БД).", get_main_kb())

    elif re.match(r'^\s*!-?твинк\b', _strip_club_prefix_raw(text), re.IGNORECASE) and _is_owner(user_id):
        raw_tw = _strip_club_prefix_raw(text).strip()
        m_tw = re.match(r'^!(-?)твинк\s+(.+)$', raw_tw, re.IGNORECASE)
        if not m_tw:
            return send_msg(
                reply_peer,
                "Формат:\n"
                "!твинк [username или ссылка] — метка «твинк» (игра можно, вывод нельзя)\n"
                "!-твинк [username] — снять метку",
                get_main_kb(),
            )
        remove_tw = bool(m_tw.group(1))
        target_tw = get_id_by_domain(m_tw.group(2).strip().split()[0])
        if not target_tw:
            return send_msg(reply_peer, "Пользователь не найден.", get_main_kb())
        target_tw = int(target_tw)
        if int(target_tw) == int(user_id):
            return send_msg(reply_peer, "Нельзя применить к себе.", get_main_kb())
        _, _ = get_user(target_tw)
        update_user_fields(target_tw, is_twin=(0 if remove_tw else 1))
        if remove_tw:
            send_msg(
                reply_peer,
                f"✅ Метка «твинк» снята: @id{target_tw} ({get_user_name(target_tw)}).",
                get_main_kb(),
            )
            try:
                send_msg(
                    target_tw,
                    "✅ Метка «твинк» снята. Вывод снова доступен при соблюдении условий бота.",
                    kb_for_peer(target_tw),
                )
            except Exception:
                pass
        else:
            send_msg(
                reply_peer,
                f"✅ @id{target_tw} ({get_user_name(target_tw)}) — метка «твинк» (вывод отключён).",
                get_main_kb(),
            )
            try:
                send_msg(
                    target_tw,
                    "⚠️ На аккаунт установлена метка «твинк».\n"
                    "Копить и тратить валюту можно; вывести — нельзя.",
                    kb_for_peer(target_tw),
                )
            except Exception:
                pass
        try:
            send_admin_chat_log(
                f"[ТВИНК] {'снята' if remove_tw else 'выдана'} метка\n"
                f"Цель: {get_user_mention_with_name(target_tw)}\n"
                f"Кто: {get_user_mention_with_name(user_id)}"
            )
        except Exception:
            pass

    elif re.match(r'^\s*!-модерденьги\s*$', _strip_club_prefix_raw(text), re.IGNORECASE) and _is_owner(user_id):
        try:
            cursor.execute("SELECT COALESCE(SUM(COALESCE(staff_balance, 0)), 0) FROM users")
            total_staff = int((cursor.fetchone() or [0])[0] or 0)
            cursor.execute("UPDATE users SET staff_balance = 0 WHERE COALESCE(staff_balance, 0) != 0")
            n_rows = int(cursor.rowcount or 0)
            db.commit()
        except Exception:
            send_msg(reply_peer, "Не удалось обнулить служебные балансы (ошибка БД).", get_main_kb())
        else:
            send_msg(
                reply_peer,
                f"💼 Служебный баланс обнулён у {n_rows} чел. Списано всего: {format_click(total_staff)}$.",
                get_main_kb(),
            )
            try:
                send_admin_chat_log(
                    f"[МОДЕРДЕНЬГИ] Обнуление служебного баланса у {n_rows} чел., сумма {format_click(total_staff)}$\n"
                    f"Кто: {get_user_mention_with_name(user_id)}"
                )
            except Exception:
                pass

    elif (
        _is_owner(user_id)
        and _owner_admin_allowed_in_this_peer(reply_peer, text)
        and (
            re.match(r'^\s*!настройки\s*$', _strip_club_prefix_raw(text).strip(), re.IGNORECASE)
            or re.match(r'^\s*!ui[\+\-]', _strip_club_prefix_raw(text).strip(), re.IGNORECASE)
            or re.match(r'^\s*!опвывод', _strip_club_prefix_raw(text).strip(), re.IGNORECASE)
        )
    ):
        raw_o = _strip_club_prefix_raw(text).strip()
        if re.match(r'^!настройки\s*$', raw_o, re.IGNORECASE):
            send_msg(reply_peer, _owner_settings_summary_text(), get_main_kb())
        else:
            mui = re.match(r'^!ui([+\-])(\S+)', raw_o, re.IGNORECASE)
            if mui:
                op, tag = mui.group(1), mui.group(2).lower()
                keymap = {
                    'работа': RUNTIME_KEY_UI_WORK,
                    'состав': RUNTIME_KEY_UI_STAFF,
                }
                if tag not in keymap:
                    send_msg(
                        reply_peer,
                        "Неизвестный ключ. Используйте: работа, состав.\nПример: !ui+работа",
                        get_main_kb(),
                    )
                else:
                    on = op == '+'
                    _set_runtime_bool(keymap[tag], on)
                    lab = {'работа': 'Работа', 'состав': 'Полный состав в помощи'}[tag]
                    send_msg(reply_peer, f"✅ {lab}: {'вкл' if on else 'выкл'}", get_main_kb())
                    try:
                        send_admin_chat_log(
                            f"[НАСТРОЙКИ] {lab} {'вкл' if on else 'выкл'}\nКто: {get_user_mention_with_name(user_id)}"
                        )
                    except Exception:
                        pass
            elif raw_o.lower().startswith('!опвывод'):
                rest = raw_o[len('!опвывод') :].strip()
                if not rest or rest.lower() == 'список':
                    send_msg(reply_peer, _owner_settings_summary_text(), get_main_kb())
                else:
                    parts = rest.split(None, 1)
                    cmd0 = parts[0].lower()
                    if cmd0 == 'сброс':
                        _clear_withdrawal_operators()
                        send_msg(
                            reply_peer,
                            "✅ Список операторов выводов сброшен. Снова действует prava.json (withdrawals_queue).",
                            get_main_kb(),
                        )
                    elif cmd0 in ('+', '-') and len(parts) > 1:
                        tid = get_id_by_domain(parts[1].strip())
                        if not tid:
                            send_msg(reply_peer, "Не удалось определить пользователя.", get_main_kb())
                        else:
                            tid = int(tid)
                            spec = _get_withdrawal_operator_spec()
                            cur = set(spec) if spec is not None else set()
                            if cmd0 == '+':
                                cur.add(tid)
                            else:
                                cur.discard(tid)
                            _set_withdrawal_operator_ids(cur)
                            if not cur:
                                send_msg(
                                    reply_peer,
                                    "✅ Список пуст. Обрабатывать выводы может только владелец (пока не добавите id снова).",
                                    get_main_kb(),
                                )
                            else:
                                send_msg(
                                    reply_peer,
                                    "✅ Операторы выводов: "
                                    + ", ".join(f"@id{x}" for x in sorted(cur))
                                    + "\n(владелец всегда может)",
                                    get_main_kb(),
                                )
                            try:
                                send_admin_chat_log(
                                    f"[ОПВЫВОД] {'+' if cmd0 == '+' else '-'}{tid}\nКто: {get_user_mention_with_name(user_id)}"
                                )
                            except Exception:
                                pass
                    else:
                        send_msg(
                            reply_peer,
                            "Формат:\n"
                            "!опвывод список\n"
                            "!опвывод + [юзер]\n"
                            "!опвывод - [юзер]\n"
                            "!опвывод сброс",
                            get_main_kb(),
                        )
            else:
                send_msg(reply_peer, "Команда не распознана.", get_main_kb())
        return

    elif text.lower().startswith('!выдать') and user_id == ADMIN_ID:
        try:
            parts = text.split()
            target_id = get_id_by_domain(parts[1])
            if not target_id: return send_msg(ADMIN_ID, "Юзер не найден.", get_main_kb())
            amount = parse_amount("".join(parts[2:]))
            _, _ = get_user(target_id)
            cursor.execute("SELECT COALESCE(balance, 0), COALESCE(staff_balance, 0) FROM users WHERE user_id = ?", (target_id,))
            t_user = cursor.fetchone()
            if t_user:
                cur_bal = int(t_user[0] or 0)
                cur_staff = int(t_user[1] or 0)
                if _receives_staff_grant_balance(target_id):
                    new_staff = cur_staff + amount
                    update_user_fields(target_id, staff_balance=new_staff)
                    total_vis = cur_bal + new_staff
                    send_msg(
                        ADMIN_ID,
                        f"Юзеру @id{target_id} выдано на служебный счёт {format_click(amount)}$ "
                        f"(без вывода, только переводы). Служебный: {format_click(new_staff)}$, всего с наличными: {format_click(total_vis)}$",
                        get_main_kb(),
                    )
                    send_msg(
                        target_id,
                        f"🎁 Вам начислили бонус от администрации на служебный счёт (не для вывода, можно переводить).\n"
                        f"Сумма: +{format_click(amount)}$\n"
                        f"Служебный баланс: {format_click(new_staff)}$",
                        get_main_kb(),
                    )
                else:
                    new_bal = cur_bal + amount
                    update_user(target_id, 'balance', new_bal)
                    send_msg(ADMIN_ID, f"Юзеру @id{target_id} выдано {format_click(amount)}$. Новый баланс: {format_click(new_bal)}$", get_main_kb())
                    send_msg(
                        target_id,
                        f"🎁 Вам начислили бонус от администрации!\n"
                        f"Сумма: +{format_click(amount)}$\n"
                        f"Новый баланс: {format_click(new_bal)}$",
                        get_main_kb(),
                    )
        except: send_msg(ADMIN_ID, "Ошибка. Используй: !выдать [юзер] [сумма в $, мк или мм]", get_main_kb())

    elif re.match(r'^\s*!снять\s', _strip_club_prefix_raw(text), re.IGNORECASE) and _is_owner(user_id):
        raw_sn = _strip_club_prefix_raw(text).strip()
        m_sn = re.match(r'^!снять\s+(\S+)\s+(.+)$', raw_sn, re.IGNORECASE)
        if not m_sn:
            send_msg(
                reply_peer,
                "Формат: !снять [юзер] [сумма]\n"
                "Сумма как в !выдать — например: 200мк, 1.5мм.",
                get_main_kb(),
            )
        else:
            try:
                target_take = get_id_by_domain(m_sn.group(1))
                if not target_take:
                    send_msg(reply_peer, "Юзер не найден.", get_main_kb())
                else:
                    target_take = int(target_take)
                    amt_take = int(parse_amount(m_sn.group(2).strip()))
                    if amt_take <= 0:
                        send_msg(reply_peer, "Сумма должна быть больше нуля.", get_main_kb())
                    else:
                        _, _ = get_user(target_take)
                        cursor.execute(
                            "SELECT COALESCE(balance, 0), COALESCE(staff_balance, 0) FROM users WHERE user_id = ?",
                            (target_take,),
                        )
                        row_take = cursor.fetchone()
                        bal_take_before = int((row_take[0] if row_take else 0) or 0)
                        staff_take_before = int((row_take[1] if row_take else 0) or 0)
                        total_take_before = bal_take_before + staff_take_before
                        if total_take_before <= 0:
                            send_msg(
                                reply_peer,
                                f"У {get_user_mention_with_name(target_take)} нулевой баланс.",
                                get_main_kb(),
                            )
                        else:
                            deducted = min(amt_take, total_take_before)
                            from_bal = min(deducted, bal_take_before)
                            from_staff = deducted - from_bal
                            bal_take_after = bal_take_before - from_bal
                            staff_take_after = staff_take_before - from_staff
                            cursor.execute(
                                "UPDATE users SET balance = ?, staff_balance = ? WHERE user_id = ?",
                                (int(bal_take_after), int(staff_take_after), int(target_take)),
                            )
                            _log_user_transaction(
                                cursor,
                                target_take,
                                "owner_take",
                                -int(deducted),
                                f"!снять владельцем @id{user_id}",
                            )
                            db.commit()
                            send_msg(
                                reply_peer,
                                f"✅ Списано у @id{target_take} ({get_user_name(target_take)}): {format_click(deducted)}$\n"
                                f"Было: наличные {format_click(bal_take_before)}$ + служебные {format_click(staff_take_before)}$\n"
                                f"Стало: наличные {format_click(bal_take_after)}$ + служебные {format_click(staff_take_after)}$"
                                + (
                                    f"\n(запрошено {format_click(amt_take)}$, снято меньше — недостаточно средств)"
                                    if deducted < amt_take
                                    else ""
                                ),
                                get_main_kb(),
                            )
                            send_admin_chat_log(
                                f"[СНЯТЬ] {get_user_mention_with_name(target_take)}\n"
                                f"Списано: {format_click(deducted)}$ "
                                f"(наличные {format_click(bal_take_before)}$ → {format_click(bal_take_after)}$, "
                                f"служебные {format_click(staff_take_before)}$ → {format_click(staff_take_after)}$)\n"
                                f"Кто: {get_user_mention_with_name(user_id)}"
                            )
                            try:
                                send_msg(
                                    int(target_take),
                                    f"⚠️ С ваших счетов списано {format_click(deducted)}$.\n"
                                    f"Наличные: {format_click(bal_take_after)}$, служебные: {format_click(staff_take_after)}$",
                                    kb_for_peer(int(target_take)),
                                )
                            except Exception:
                                pass
            except Exception:
                send_msg(
                    reply_peer,
                    "Ошибка. Формат: !снять [юзер] [сумма в $, мк или мм]",
                    get_main_kb(),
                )

    elif re.match(r'^\s*!сбор\s', _strip_club_prefix_raw(text), re.IGNORECASE) and _is_owner(user_id):
        raw_sb = _strip_club_prefix_raw(text).strip()
        m_sb = re.match(r'^!сбор\s+(.+)$', raw_sb, re.IGNORECASE)
        if not m_sb:
            send_msg(
                reply_peer,
                "Формат: !сбор [сумма]\n"
                "Пример: !сбор 10мм\n\n"
                "С баланса каждого зарегистрированного игрока списывается не больше этой суммы "
                "(если на балансе меньше — списывается весь баланс). Всё зачисляется в казну сообщества.",
                get_main_kb(),
            )
        else:
            try:
                amt_collect = int(parse_amount(m_sb.group(1).strip()))
            except Exception:
                send_msg(reply_peer, "Неверная сумма. Пример: !сбор 10мм или !сбор 500мк", get_main_kb())
            else:
                _run_owner_mass_collect_to_kazna(user_id, reply_peer, amt_collect)

    elif (_is_owner(user_id) or _is_deputy_owner(user_id)) and re.match(r'^!должность\s', (text or '').strip(), re.IGNORECASE):
        parts = _strip_club_prefix_raw(text).split(None, 2)
        if len(parts) < 3:
            send_msg(
                reply_peer,
                "Формат: !должность [юзер] [должность]\n"
                "Пример: !должность @ник модератор\n\n"
                "Должности:\n"
                "модератор, спонсор, зам владелец; снять — убрать роль.",
                get_main_kb(),
            )
        else:
            target_id = get_id_by_domain(parts[1])
            if not target_id:
                send_msg(reply_peer, "Юзер не найден.", get_main_kb())
            elif int(target_id) == int(ADMIN_ID):
                send_msg(reply_peer, "Владелец проекта назначается из config и не изменяется командой.", get_main_kb())
            else:
                role_key = _project_role_key_from_text(parts[2])
                if role_key is None:
                    send_msg(reply_peer, "Неизвестная должность.", get_main_kb())
                else:
                    if _is_deputy_owner(user_id) and not _is_owner(user_id):
                        allowed_for_deputy = {"moderator", "sponsor", ""}
                        if role_key not in allowed_for_deputy:
                            send_msg(
                                reply_peer,
                                "Зам может назначать или снимать: модератор, спонсор. "
                                "Остальные должности — только у владельца.",
                                get_main_kb(),
                            )
                            return
                    update_user(target_id, 'project_role', role_key)
                    update_user(target_id, 'role_assigned_at', float(time.time()) if role_key else 0)
                    if role_key:
                        send_msg(
                            reply_peer,
                            f"Юзеру @id{target_id} назначена должность: {_project_role_label_with_hashtag_by_key(role_key)}.",
                            get_main_kb(),
                        )
                        send_msg(
                            target_id,
                            f"🎖 Вам назначили должность: {_project_role_label_with_hashtag_by_key(role_key)}.",
                            get_main_kb(),
                        )
                        send_admin_chat_log(
                            f"[ДОЛЖНОСТЬ] {get_user_mention_with_name(target_id)} -> {_project_role_label_with_hashtag_by_key(role_key)}\n"
                            f"Кто назначил: {get_user_mention_with_name(user_id)}"
                        )
                    else:
                        _set_staff_repr_counts(int(target_id), 0, 0)
                        send_msg(
                            reply_peer,
                            f"Должность у @id{target_id} снята. Модераторские выговоры обнулены.",
                            get_main_kb(),
                        )
                        send_msg(target_id, "ℹ️ Ваша должность в проекте была снята.", get_main_kb())
                        send_admin_chat_log(f"[ДОЛЖНОСТЬ] Снята у {get_user_mention_with_name(target_id)}\nКто снял: {get_user_mention_with_name(user_id)}")

    elif _is_owner(user_id) and re.match(r"^\s*\+выговор\b", (text or "").strip(), re.IGNORECASE):
        target_id, strike_reason, err = _resolve_strike_command_target_reason(event, text, "+выговор")
        if err or not target_id:
            send_msg(reply_peer, err or "Не удалось определить юзера.", get_main_kb())
        elif int(target_id) == int(ADMIN_ID):
            send_msg(reply_peer, "Владельцу проекта выговоры не выдаются.", get_main_kb())
        else:
            _, _ = get_user(target_id)
            o, ot, total = _get_staff_repr_breakdown(target_id)
            if total >= STAFF_REPRIMAND_MAX:
                send_msg(
                    reply_peer,
                    f"У @id{target_id} уже максимум выговоров ({STAFF_REPRIMAND_MAX}).",
                    get_main_kb(),
                )
            else:
                new_n = _set_staff_repr_counts(target_id, o + 1, ot)
                rs = f"\nПричина: {strike_reason}" if strike_reason else ""
                send_msg(
                    reply_peer,
                    f"📛 Выговор выдан @id{target_id} ({get_user_name(target_id)}).\nСейчас: {new_n}/{STAFF_REPRIMAND_MAX}.{rs}",
                    get_main_kb(),
                )
                log_r = f"\nПричина: {strike_reason}" if strike_reason else ""
                send_admin_chat_log(
                    f"[ВЫГОВОР +] {get_user_mention_with_name(target_id)} — {new_n}/{STAFF_REPRIMAND_MAX} (от владельца)\n"
                    f"Кто: {get_user_mention_with_name(user_id)}{log_r}"
                )
                try:
                    dm_r = f"\nПричина: {strike_reason}" if strike_reason else ""
                    send_msg(
                        int(target_id),
                        f"📛 Вам выдан выговор по линии модерации (владелец). Всего: {new_n}/{STAFF_REPRIMAND_MAX}.{dm_r}",
                        kb_for_peer(int(target_id)),
                    )
                except Exception:
                    pass

    elif _can_use_staff_reprimand_non_owner_commands(user_id) and re.match(
        r"^\s*\+выговор\b", (text or "").strip(), re.IGNORECASE
    ):
        target_id, strike_reason, err = _resolve_strike_command_target_reason(event, text, "+выговор")
        if err or not target_id:
            send_msg(reply_peer, err or "Не удалось определить юзера.", get_main_kb())
        elif int(target_id) == int(ADMIN_ID):
            send_msg(reply_peer, "Владельцу проекта выговоры не выдаются.", get_main_kb())
        else:
            _, _ = get_user(target_id)
            o, ot, total = _get_staff_repr_breakdown(target_id)
            if total >= STAFF_REPRIMAND_MAX:
                send_msg(
                    reply_peer,
                    f"У @id{target_id} уже максимум выговоров ({STAFF_REPRIMAND_MAX}).",
                    get_main_kb(),
                )
            else:
                new_n = _set_staff_repr_counts(target_id, o, ot + 1)
                rs = f"\nПричина: {strike_reason}" if strike_reason else ""
                send_msg(
                    reply_peer,
                    f"📛 Выговор выдан @id{target_id} ({get_user_name(target_id)}).\nСейчас: {new_n}/{STAFF_REPRIMAND_MAX}.{rs}",
                    get_main_kb(),
                )
                log_r = f"\nПричина: {strike_reason}" if strike_reason else ""
                send_admin_chat_log(
                    f"[ВЫГОВОР +] {get_user_mention_with_name(target_id)} — {new_n}/{STAFF_REPRIMAND_MAX} (от состава)\n"
                    f"Кто: {get_user_mention_with_name(user_id)}{log_r}"
                )
                try:
                    dm_r = f"\nПричина: {strike_reason}" if strike_reason else ""
                    send_msg(
                        int(target_id),
                        f"📛 Вам выдан выговор по линии модерации (состав). Всего: {new_n}/{STAFF_REPRIMAND_MAX}.{dm_r}",
                        kb_for_peer(int(target_id)),
                    )
                except Exception:
                    pass

    elif _is_owner(user_id) and re.match(r"^\s*-выговор\b", (text or "").strip(), re.IGNORECASE):
        target_id, strike_reason, err = _resolve_strike_command_target_reason(event, text, "-выговор")
        if err or not target_id:
            send_msg(reply_peer, err or "Не удалось определить юзера.", get_main_kb())
        elif int(target_id) == int(ADMIN_ID):
            send_msg(reply_peer, "У владельца нет учёта выговоров.", get_main_kb())
        else:
            _, _ = get_user(target_id)
            o, ot, total = _get_staff_repr_breakdown(target_id)
            if total <= 0:
                send_msg(reply_peer, f"У @id{target_id} нет выговоров для снятия.", get_main_kb())
            else:
                if ot > 0:
                    new_n = _set_staff_repr_counts(target_id, o, ot - 1)
                else:
                    new_n = _set_staff_repr_counts(target_id, o - 1, ot)
                rs = f"\nКомментарий: {strike_reason}" if strike_reason else ""
                send_msg(
                    reply_peer,
                    f"📛 Снят один выговор у @id{target_id} ({get_user_name(target_id)}).\nСейчас: {new_n}/{STAFF_REPRIMAND_MAX}.{rs}",
                    get_main_kb(),
                )
                log_r = f"\nКомментарий: {strike_reason}" if strike_reason else ""
                send_admin_chat_log(
                    f"[ВЫГОВОР −] {get_user_mention_with_name(target_id)} — {new_n}/{STAFF_REPRIMAND_MAX}\n"
                    f"Кто: {get_user_mention_with_name(user_id)}{log_r}"
                )
                try:
                    dm_r = f"\nКомментарий: {strike_reason}" if strike_reason else ""
                    send_msg(
                        int(target_id),
                        f"ℹ️ С вас снят один выговор по линии модерации. Сейчас: {new_n}/{STAFF_REPRIMAND_MAX}.{dm_r}",
                        kb_for_peer(int(target_id)),
                    )
                except Exception:
                    pass

    elif _can_use_staff_reprimand_non_owner_commands(user_id) and re.match(
        r"^\s*-выговор\b", (text or "").strip(), re.IGNORECASE
    ):
        target_id, strike_reason, err = _resolve_strike_command_target_reason(event, text, "-выговор")
        if err or not target_id:
            send_msg(reply_peer, err or "Не удалось определить юзера.", get_main_kb())
        elif int(target_id) == int(ADMIN_ID):
            send_msg(reply_peer, "У владельца нет учёта выговоров.", get_main_kb())
        else:
            _, _ = get_user(target_id)
            o, ot, total = _get_staff_repr_breakdown(target_id)
            if total <= 0:
                send_msg(reply_peer, f"У @id{target_id} нет выговоров для снятия.", get_main_kb())
            elif ot <= 0:
                send_msg(
                    reply_peer,
                    "Выговор, выданный владельцем проекта, может снять только владелец.",
                    get_main_kb(),
                )
            else:
                new_n = _set_staff_repr_counts(target_id, o, ot - 1)
                rs = f"\nКомментарий: {strike_reason}" if strike_reason else ""
                send_msg(
                    reply_peer,
                    f"📛 Снят один выговор у @id{target_id} ({get_user_name(target_id)}).\nСейчас: {new_n}/{STAFF_REPRIMAND_MAX}.{rs}",
                    get_main_kb(),
                )
                log_r = f"\nКомментарий: {strike_reason}" if strike_reason else ""
                send_admin_chat_log(
                    f"[ВЫГОВОР −] {get_user_mention_with_name(target_id)} — {new_n}/{STAFF_REPRIMAND_MAX} (только состав)\n"
                    f"Кто: {get_user_mention_with_name(user_id)}{log_r}"
                )
                try:
                    dm_r = f"\nКомментарий: {strike_reason}" if strike_reason else ""
                    send_msg(
                        int(target_id),
                        f"ℹ️ С вас снят один выговор по линии модерации. Сейчас: {new_n}/{STAFF_REPRIMAND_MAX}.{dm_r}",
                        kb_for_peer(int(target_id)),
                    )
                except Exception:
                    pass

    elif (_is_owner(user_id) or _is_deputy_owner(user_id)) and re.match(r"^\s*!повысить\b", (text or "").strip(), re.IGNORECASE):
        send_msg(
            reply_peer,
            "Команда !повысить отключена. Используйте !должность (только роли: зам владельца, модератор, спонсор).",
            get_main_kb(),
        )

    elif (
        _is_multichat_peer(reply_peer)
        and _chat_mute_cmd_first_token(text) == 'мут'
        and _prava_role_can(user_id, "chat_mute")
    ):
        msg_obj_m = event.obj.message if isinstance(event.obj.message, dict) else {}
        rm_m = msg_obj_m.get('reply_message') if isinstance(msg_obj_m, dict) else None
        if not rm_m:
            send_msg(reply_peer, "Ответьте на сообщение юзера и напишите: мут или +мут и время (например 30м, 1ч).", kb_for_peer(reply_peer))
        else:
            try:
                raw_from_m = rm_m.get('from_id')
                target_author_m = int(raw_from_m) if raw_from_m is not None else 0
            except (TypeError, ValueError):
                target_author_m = 0
            if target_author_m <= 0:
                send_msg(reply_peer, "Нельзя выдать мут этому сообщению.", kb_for_peer(reply_peer))
            elif _is_admin_user(target_author_m):
                send_msg(reply_peer, "Админ-состав нельзя мутить этой командой.", kb_for_peer(reply_peer))
            else:
                raw_mute = _normalize_chat_command(text).lstrip("+").strip()
                parts_m = raw_mute.split(None, 1)
                dur_raw = parts_m[1] if len(parts_m) > 1 else ""
                try:
                    mute_sec = _parse_chat_mute_seconds(dur_raw)
                except Exception:
                    send_msg(reply_peer, "Неверный формат времени. Пример: мут 30м, +мут 2ч", kb_for_peer(reply_peer))
                    mute_sec = 0
                if mute_sec > 0:
                    mute_until = time.time() + int(mute_sec)
                    update_user(target_author_m, 'spam_mute_until', mute_until)
                    _vk_chat_moderation_restrict_write(int(reply_peer), target_author_m, int(mute_sec), True)
                    snippet_m = _snippet_from_reply_message(rm_m)
                    snippet_line_m = (snippet_m or '').replace('\n', ' ').strip()
                    reason_line_m = f"\nСообщение: «{snippet_line_m[:220]}»" if snippet_line_m else ""
                    send_msg(
                        reply_peer,
                        f"⛔ {get_user_mention_with_name(target_author_m)} выдан мут на {format_time_left_sec(mute_sec)}.",
                        kb_for_peer(reply_peer),
                    )
                    send_admin_chat_log(
                        f"[МУТ] {get_user_mention_with_name(target_author_m)} на {format_time_left_sec(mute_sec)}\n"
                        f"Кто: {get_user_mention_with_name(user_id)}"
                        f"{reason_line_m}"
                    )
                    _log_moderator_action(user_id, "mute", 0)

    elif (
        _is_multichat_peer(reply_peer)
        and _chat_first_token(text) in ('-мут', 'размут')
        and _prava_role_can(user_id, "chat_unmute")
    ):
        msg_obj_um = event.obj.message if isinstance(event.obj.message, dict) else {}
        rm_um = msg_obj_um.get('reply_message') if isinstance(msg_obj_um, dict) else None
        if not rm_um:
            send_msg(reply_peer, "Ответьте на сообщение юзера и напишите -мут или размут.", kb_for_peer(reply_peer))
        else:
            try:
                raw_from_um = rm_um.get('from_id')
                target_author_um = int(raw_from_um) if raw_from_um is not None else 0
            except (TypeError, ValueError):
                target_author_um = 0
            if target_author_um <= 0:
                send_msg(reply_peer, "Нельзя снять мут этому сообщению.", kb_for_peer(reply_peer))
            else:
                update_user(target_author_um, 'spam_mute_until', 0)
                _vk_chat_moderation_restrict_write(int(reply_peer), target_author_um, 0, False)
                send_msg(
                    reply_peer,
                    f"✅ Мут снят у {get_user_mention_with_name(target_author_um)}.",
                    kb_for_peer(reply_peer),
                )
                send_admin_chat_log(
                    f"[РАЗМУТ] {get_user_mention_with_name(target_author_um)}\n"
                    f"Кто: {get_user_mention_with_name(user_id)}"
                )
                _log_moderator_action(user_id, "unmute", 0)

    elif (
        _is_multichat_peer(reply_peer)
        and (_is_owner(user_id) or _is_deputy_owner(user_id))
        and _chat_first_token(text) == 'кик'
    ):
        norm_k = _normalize_chat_command(text)
        msg_obj_k = event.obj.message if isinstance(event.obj.message, dict) else {}
        rm_k = msg_obj_k.get('reply_message') if isinstance(msg_obj_k, dict) else None
        if not rm_k:
            send_msg(
                reply_peer,
                "Ответьте на сообщение юзера и напишите: кик\n(причину можно дописать в той же строке или с новой строки)",
                kb_for_peer(reply_peer),
            )
        else:
            try:
                raw_from_k = rm_k.get('from_id')
                target_k = int(raw_from_k) if raw_from_k is not None else 0
            except (TypeError, ValueError):
                target_k = 0
            reason_k = norm_k[3:].strip() if norm_k.startswith('кик') else ""
            reason_k = reason_k.strip() or "Исключение из беседы"
            snippet_k = _snippet_from_reply_message(rm_k)
            snippet_line_k = (snippet_k or '').replace('\n', ' ').strip()
            ctx_k = f"\nСообщение: «{snippet_line_k[:220]}»" if snippet_line_k else ""
            if target_k <= 0:
                send_msg(reply_peer, "Нельзя исключить по этому сообщению (не юзер).", kb_for_peer(reply_peer))
            elif target_k == int(user_id):
                send_msg(reply_peer, "Нельзя исключить самого себя.", kb_for_peer(reply_peer))
            elif _is_deputy_owner(user_id) and (_is_owner(target_k) or _is_deputy_owner(target_k)):
                send_msg(
                    reply_peer,
                    "Заместитель не может исключить владельца проекта или другого заместителя.",
                    kb_for_peer(reply_peer),
                )
            elif _is_owner(target_k):
                send_msg(reply_peer, "Владельца проекта нельзя исключить этой командой.", kb_for_peer(reply_peer))
            else:
                kicked_ok = _remove_user_from_chat_if_possible(reply_peer, target_k, force_kick=True)
                cmid_del = int(rm_k.get('conversation_message_id') or 0)
                if cmid_del > 0:
                    try:
                        vk.messages.delete(peer_id=int(reply_peer), cmids=str(cmid_del), delete_for_all=1)
                    except Exception:
                        pass
                send_msg(
                    reply_peer,
                    f"{'✅ Юзер исключён из беседы.' if kicked_ok else '⚠️ Не удалось исключить из беседы (права бота или лимит API).'}\n"
                    f"{get_user_mention_with_name(target_k)}\nПричина: {reason_k}",
                    kb_for_peer(reply_peer),
                )
                send_admin_chat_log(
                    f"[КИК] {get_user_mention_with_name(target_k)}\nПричина: {reason_k}\n"
                    f"Кто: {get_user_mention_with_name(user_id)}{ctx_k}"
                )
                _log_moderator_action(user_id, "kick", 0)
                try:
                    send_msg(
                        int(target_k),
                        f"⛔ Вас исключили из беседы.\nПричина: {reason_k}",
                        kb_for_peer(int(target_k)),
                    )
                except Exception:
                    pass

    elif (
        _is_multichat_peer(reply_peer)
        and re.match(r"^\s*!проверка\b", _strip_club_prefix_raw(text), re.IGNORECASE)
        and _can_run_chat_proverka(user_id, reply_peer)
    ):
        if not _user_is_registered_in_clicker(user_id):
            send_msg(
                reply_peer,
                "Команда !проверка доступна только тем, кто зарегистрирован в кликере: "
                "откройте личные сообщения с ботом и завершите регистрацию («Начать» / подписка / согласие).",
                kb_for_peer(reply_peer),
            )
        else:
            try:
                msg_pv = event.obj.message if isinstance(event.obj.message, dict) else {}
                cmd_cmid_pv = int(msg_pv.get("conversation_message_id") or 0)
                text_out, kb_out = _proverka_chat_members(reply_peer)
                mid_bot = send_msg(reply_peer, text_out, kb_out.get_keyboard())
                _proverka_register_pending_ui(reply_peer, cmd_cmid_pv, mid_bot)
            except Exception:
                send_msg(
                    reply_peer,
                    "Не удалось выполнить проверку (API беседы или БД). Проверьте права бота в чате.",
                    kb_for_peer(reply_peer),
                )

    elif _is_multichat_peer(reply_peer) and _strip_club_prefix_raw(text).lower() == '-варн' and _is_admin_user(user_id):
        msg_obj_w = event.obj.message if isinstance(event.obj.message, dict) else {}
        rm_w = msg_obj_w.get('reply_message') if isinstance(msg_obj_w, dict) else None
        if not rm_w:
            send_msg(reply_peer, "Ответьте на сообщение юзера и напишите -варн.", kb_for_peer(reply_peer))
        else:
            try:
                raw_from_w = rm_w.get('from_id')
                try:
                    target_author_w = int(raw_from_w) if raw_from_w is not None else 0
                except (TypeError, ValueError):
                    target_author_w = 0
                snippet_w = _snippet_from_reply_message(rm_w)
                warn_w = _apply_moderation_warn(target_author_w, user_id, reply_peer, snippet_w, 'warn_cmd') if target_author_w > 0 else None
                if warn_w and warn_w.get('skipped_admin'):
                    send_msg(reply_peer, "Юзер в составе модерации — предупреждение не выдаётся.", kb_for_peer(reply_peer))
                elif warn_w and warn_w.get('warn_count') is not None:
                    wc_w = warn_w['warn_count']
                    parts_w = [
                        f"⚠️ @id{target_author_w} ({get_user_name(target_author_w)}): предупреждение {wc_w}/{MODERATION_WARN_BAN_THRESHOLD}."
                    ]
                    snip_line = (snippet_w or '').replace('\n', ' ')
                    if snip_line:
                        parts_w.append(f"Сообщение: «{snip_line[:220]}»")
                    if warn_w.get('banned'):
                        parts_w.append(f"🚫 @id{target_author_w} забанен за {MODERATION_WARN_BAN_THRESHOLD} предупреждения.")
                    send_msg(reply_peer, "\n".join(parts_w), kb_for_peer(reply_peer))
                elif target_author_w <= 0:
                    send_msg(reply_peer, "Нельзя выдать предупреждение за сообщение не от юзера.", kb_for_peer(reply_peer))
                else:
                    send_msg(reply_peer, "Не удалось выдать предупреждение.", kb_for_peer(reply_peer))
            except Exception:
                send_msg(reply_peer, "Ошибка команды -варн.", kb_for_peer(reply_peer))

    elif _is_multichat_peer(reply_peer) and _strip_club_prefix_raw(text).lower() == '-смс' and _is_admin_user(user_id):
        send_msg(reply_peer, "Команда -смс отключена.", kb_for_peer(reply_peer))


# --- ГЛАВНЫЙ ЦИКЛ ---
def _ensure_longpoll_ready():
    """Создать longpoll при старте/обрыве. False — если сейчас недоступно."""
    global longpoll
    if longpoll is not None:
        return True
    try:
        longpoll = VkBotLongPoll(vk_session, GROUP_ID)
        print("[longpoll] connected")
        return True
    except Exception as e:
        print("[longpoll] connect failed:", e)
        return False


threading.Thread(target=_official_norm_review_scheduler_loop, daemon=True).start()
print("Бот запущен...")
try:
    send_msg(RESTRICTED_CHAT_PEER_ID, "🟢 Бот включился.", kb_for_peer(RESTRICTED_CHAT_PEER_ID))
except Exception:
    pass
while True:
    if not _ensure_longpoll_ready():
        time.sleep(2)
        continue
    try:
        for event in longpoll.listen():
            try:
                _LONGPOLL_NET_FAIL_STREAK = 0
                ev_type = getattr(event.type, 'value', str(event.type))
                if event.type == VkBotEventType.MESSAGE_NEW:
                    process_message(event)
                elif event.type == VkBotEventType.MESSAGE_EVENT:
                    user_id = event.obj.get('user_id')
                    peer_id = event.obj.get('peer_id')
                    event_id = event.obj.get('event_id')
                    try: vk.messages.sendMessageEventAnswer(event_id=event_id, user_id=user_id, peer_id=peer_id)
                    except: pass
                    _mpl_ev = event.obj.get('payload')
                    if isinstance(_mpl_ev, str):
                        try:
                            payload_ev = json.loads(_mpl_ev)
                        except Exception:
                            payload_ev = {}
                    elif isinstance(_mpl_ev, dict):
                        payload_ev = _mpl_ev
                    else:
                        payload_ev = {}
                    cmd_ev = payload_ev.get('cmd')

                    # Режим техработ: для обычных пользователей команды/кнопки недоступны.
                    # Наградные события (лайки/комментарии) обрабатываются в других ветках цикла.
                    if TECH_WORKS_ENABLED and not _is_owner(user_id):
                        continue

                    if cmd_ev == 'official_norm_review':
                        try:
                            actor_id = int(user_id or 0)
                            target_id = int(payload_ev.get('uid') or 0)
                            day_key = str(payload_ev.get('d') or '').strip()
                            action = str(payload_ev.get('a') or '').strip().lower()
                            if actor_id not in (int(OFFICIAL_NORM_REVIEW_ADMIN_ID), int(ADMIN_ID)) and not _is_deputy_owner(actor_id):
                                try:
                                    vk.messages.sendMessageEventAnswer(
                                        event_id=event_id,
                                        user_id=user_id,
                                        peer_id=peer_id,
                                        event_data=json.dumps({"type": "show_snackbar", "text": "Недостаточно прав"}),
                                    )
                                except Exception:
                                    pass
                                continue
                            if target_id <= 0 or not re.fullmatch(r"\d{4}-\d{2}-\d{2}", day_key):
                                continue
                            cursor.execute(
                                "SELECT COALESCE(project_role, '') FROM users WHERE user_id = ?",
                                (int(target_id),),
                            )
                            role_key = str((cursor.fetchone() or [""])[0] or "")
                            rule = _official_norm_for_role(role_key)
                            if not rule:
                                continue
                            cursor.execute(
                                "SELECT first_at, last_at, msg_count, answers_count, report_done, reprimand_issued "
                                "FROM official_chat_daily WHERE user_id = ? AND day_key = ?",
                                (int(target_id), str(day_key)),
                            )
                            row = cursor.fetchone()
                            if not row:
                                cursor.execute(
                                    "INSERT OR REPLACE INTO official_chat_daily "
                                    "(user_id, day_key, first_at, last_at, msg_count, answers_count, report_done, reprimand_issued, updated_at) "
                                    "VALUES (?, ?, 0, 0, 0, 0, 0, 0, ?)",
                                    (int(target_id), str(day_key), float(time.time())),
                                )
                                row = (0, 0, 0, 0, 0, 0)
                            first_at, last_at, msg_count, answers_count, report_done, reprimand_issued = row
                            worked_hours = max(0.0, (float(last_at or 0) - float(first_at or 0)) / 3600.0)
                            if action == 'ok':
                                cursor.execute(
                                    "UPDATE official_chat_daily SET report_done = 1 WHERE user_id = ? AND day_key = ?",
                                    (int(target_id), str(day_key)),
                                )
                                db.commit()
                                decision_txt = "✅ Норма подтверждена человеком"
                            elif action == 'repr':
                                if int(reprimand_issued or 0) != 1:
                                    o, ot, _ = _get_staff_repr_breakdown(target_id)
                                    _set_staff_repr_counts(target_id, o, int(ot) + 1)
                                cursor.execute(
                                    "UPDATE official_chat_daily SET report_done = 0, reprimand_issued = 1 WHERE user_id = ? AND day_key = ?",
                                    (int(target_id), str(day_key)),
                                )
                                db.commit()
                                decision_txt = "📛 Выговор выдан человеком"
                            else:
                                continue
                            try:
                                send_admin_chat_log(
                                    f"[НОРМА РУЧНАЯ] {get_user_mention_with_name(target_id)} ({PROJECT_ROLE_LABELS.get(str(role_key), str(role_key))})\n"
                                    f"Дата: {day_key}\n"
                                    f"Сообщений: {int(msg_count or 0)}\n"
                                    f"Ответы игрокам: {int(answers_count or 0)} / {int(rule['answers'])}\n"
                                    f"Онлайн: {_official_ts_to_msk_hhmm(first_at)} — {_official_ts_to_msk_hhmm(last_at)} ({worked_hours:.1f} ч)\n"
                                    f"Решение: {decision_txt}\n"
                                    f"Кто проверил: {get_user_mention_with_name(actor_id)}"
                                )
                            except Exception:
                                pass
                            try:
                                _cmid_norm = int(event.obj.get('conversation_message_id') or 0)
                                if _cmid_norm > 0:
                                    vk.messages.delete(
                                        peer_id=int(peer_id),
                                        cmids=str(_cmid_norm),
                                        delete_for_all=1,
                                    )
                            except Exception:
                                pass
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Решение сохранено"}),
                                )
                            except Exception:
                                pass
                        except Exception as _onr:
                            print(f"[official_norm_review callback] {_onr}")
                        continue

                    if cmd_ev in (
                        'donate_pick_15',
                        'donate_pick_30',
                        'donate_pick_custom',
                        'donate_confirm',
                        'donate_cancel',
                        'donation_menu_close',
                        'ozon_work_start',
                        'ozon_work_pick',
                        'pascha_accept',
                    ):
                        try:
                            uid_d = int(user_id)
                            pid_d = int(peer_id) if peer_id is not None else uid_d
                            cmid_d = int(event.obj.get('conversation_message_id') or 0)
                            pl_d = dict(payload_ev) if isinstance(payload_ev, dict) else {}
                            _process_message_from_donation_callback(uid_d, pid_d, pl_d, cmid_d)
                        except Exception as _de:
                            print(f"[inline callback {cmd_ev}] {_de}")
                        continue

                    # Inline-кнопки топов/меню: иногда приходят как MESSAGE_EVENT (callback), а не как сообщение.
                    if cmd_ev in (
                        'top_refs',
                        'top_balance',
                        'top_spam',
                        'top_donations',
                        'top_withdrawals',
                        'top_klad',
                        RESTRICTED_TOPS_MENU_CMD,
                        CASINO_MENU_CMD,
                        PROFILE_CHAT_CMD,
                    ):
                        try:
                            uid_ev = int(user_id)
                            rp_ev = int(peer_id) if peer_id is not None else uid_ev
                            cmid_ev = int(event.obj.get('conversation_message_id') or 0)
                            pl_d = dict(payload_ev) if isinstance(payload_ev, dict) else {}
                            _menu_keyboard_user_id = uid_ev
                            _process_message_from_donation_callback(uid_ev, rp_ev, pl_d, cmid_ev)
                        except Exception as _tcb:
                            print(f"[inline топ/kb] {_tcb}")
                        continue

                    if isinstance(cmd_ev, str) and cmd_ev.startswith("admin_op"):
                        try:
                            uid_ev = int(user_id)
                            rp_ev = int(peer_id) if peer_id is not None else uid_ev
                            cmid_ev = int(event.obj.get("conversation_message_id") or 0)
                            pl_d = dict(payload_ev) if isinstance(payload_ev, dict) else {}
                            _process_message_from_donation_callback(uid_ev, rp_ev, pl_d, cmid_ev)
                        except Exception as _aop:
                            print(f"[admin_op callback] {_aop}")
                        continue

                    if cmd_ev in ('contest_cb', 'contest_owner'):
                        try:
                            uid_ev = int(user_id)
                            rp_ev = int(peer_id) if peer_id is not None else uid_ev
                        except (TypeError, ValueError):
                            continue
                        _menu_keyboard_user_id = uid_ev
                        try:
                            _cmid_ct = int(event.obj.get("conversation_message_id") or 0)
                            _op_contest_process_owner(
                                uid_ev, rp_ev, "", str(cmd_ev), payload_ev, contest_edit_cmid=_cmid_ct
                            )
                        except Exception as _ce:
                            print(f"[contest keyboard event] {_ce}")
                        continue

                    if cmd_ev == 'anti_bot_send_captcha':
                        if not (_is_owner(user_id) or _is_deputy_owner(user_id)):
                            continue
                        try:
                            target_id = int(payload_ev.get('uid') or 0)
                        except Exception:
                            target_id = 0
                        if target_id > 0:
                            _issue_forced_captcha(target_id, int(peer_id), issued_by=user_id, reason_text="Кнопка антибота")
                            try:
                                vk.messages.edit(
                                    peer_id=int(peer_id),
                                    conversation_message_id=event.obj.get('conversation_message_id'),
                                    message=f"[АНТИБОТ] Капча отправлена пользователю {get_user_mention_with_name(target_id)}.",
                                    keyboard='{"inline":true,"buttons":[]}',
                                )
                            except Exception:
                                pass
                        continue

                    if cmd_ev in ('kick_proverka_unregistered', 'kick_badbotik_unregistered'):
                        try:
                            tpeer = int(payload_ev.get('peer_id') or 0)
                        except Exception:
                            tpeer = 0
                        if tpeer <= 0 or not _is_multichat_peer(tpeer):
                            continue
                        if not _can_run_chat_proverka(user_id, tpeer):
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Недостаточно прав"}),
                                )
                            except Exception:
                                pass
                            continue
                        if not _user_is_registered_in_clicker(user_id):
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps(
                                        {"type": "show_snackbar", "text": "Сначала зарегистрируйтесь в кликере"}
                                    ),
                                )
                            except Exception:
                                pass
                            continue
                        kicked, err = _kick_unregistered_from_chat(tpeer, user_id)
                        snack = (err or f"Исключено: {kicked}")[:200]
                        try:
                            vk.messages.sendMessageEventAnswer(
                                event_id=event_id,
                                user_id=user_id,
                                peer_id=peer_id,
                                event_data=json.dumps({"type": "show_snackbar", "text": snack}),
                            )
                        except Exception:
                            pass
                        if err is None and int(peer_id) == int(tpeer):
                            _proverka_delete_messages_after_kick(tpeer, event.obj)
                            send_admin_chat_log(
                                f"[!проверка кик] peer={tpeer}, исключено={kicked}, кто={get_user_mention_with_name(user_id)}"
                            )
                        continue

                    if cmd_ev == 'mod_set_public_id':
                        if not _can_use_admin_chat_mod_features(user_id):
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Недостаточно прав"}),
                                )
                            except Exception:
                                pass
                            continue
                        try:
                            target_mod = int(payload_ev.get("uid") or user_id)
                        except (TypeError, ValueError):
                            target_mod = int(user_id)
                        if target_mod <= 0:
                            continue
                        update_user(target_mod, 'moderator_public_id', int(target_mod))
                        try:
                            vk.messages.sendMessageEventAnswer(
                                event_id=event_id,
                                user_id=user_id,
                                peer_id=peer_id,
                                event_data=json.dumps({"type": "show_snackbar", "text": "ID сохранен"}),
                            )
                        except Exception:
                            pass
                        continue

                    if cmd_ev == 'mod_menu_refresh':
                        if not _can_use_admin_chat_mod_features(user_id) or int(peer_id) != int(ADMIN_CHAT_PEER_ID):
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Недостаточно прав"}),
                                )
                            except Exception:
                                pass
                            continue
                        try:
                            uid_ev = int(payload_ev.get("uid") or user_id)
                        except (TypeError, ValueError):
                            try:
                                uid_ev = int(user_id)
                            except (TypeError, ValueError):
                                continue
                        cursor.execute(
                            "SELECT COALESCE(moderator_public_id, 0) FROM users WHERE user_id = ?",
                            (uid_ev,),
                        )
                        _mpr = cursor.fetchone()
                        mod_pub = int((_mpr[0] if _mpr else 0) or 0)
                        _mod_info_body = _format_moderator_info_message(
                            uid_ev, mod_pub, include_team_reprimands=True
                        )
                        _mod_info_kb = get_moderator_info_kb(
                            uid_ev,
                            has_public_id=mod_pub > 0,
                            for_admin_chat=True,
                        )
                        try:
                            _cmid_rf = int(event.obj.get("conversation_message_id") or 0)
                        except (TypeError, ValueError):
                            _cmid_rf = 0
                        if _cmid_rf > 0:
                            try:
                                vk.messages.edit(
                                    peer_id=int(peer_id),
                                    conversation_message_id=_cmid_rf,
                                    message=_mod_info_body,
                                    keyboard=_mod_info_kb.get_keyboard(),
                                )
                            except Exception:
                                send_msg(
                                    int(peer_id),
                                    _mod_info_body,
                                    _mod_info_kb,
                                )
                        else:
                            send_msg(int(peer_id), _mod_info_body, _mod_info_kb)
                        continue

                    if cmd_ev == 'mod_answer_question':
                        if not _is_moderation_staff(user_id) or int(peer_id) != int(ADMIN_CHAT_PEER_ID):
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Недостаточно прав"}),
                                )
                            except Exception:
                                pass
                            continue
                        try:
                            qid = int(payload_ev.get('qid') or 0)
                        except Exception:
                            qid = 0
                        if qid <= 0:
                            continue
                        cursor.execute(
                            "SELECT status, COALESCE(taken_by, 0) FROM support_questions WHERE id = ?",
                            (int(qid),),
                        )
                        qrow = cursor.fetchone()
                        if not qrow:
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Вопрос не найден"}),
                                )
                            except Exception:
                                pass
                            continue
                        status = str(qrow[0] or "")
                        taken_by = int(qrow[1] or 0)
                        if status == "answered":
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Уже отвечено"}),
                                )
                            except Exception:
                                pass
                            continue
                        if status == "in_progress" and taken_by != int(user_id):
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Уже взят другим модератором"}),
                                )
                            except Exception:
                                pass
                            continue
                        cursor.execute(
                            "UPDATE support_questions SET status = 'in_progress', taken_by = ?, taken_at = ? WHERE id = ?",
                            (int(user_id), float(time.time()), int(qid)),
                        )
                        db.commit()
                        update_user(user_id, 'mod_reply_question_id', int(qid))
                        cmid_ev = event.obj.get('conversation_message_id')
                        try:
                            vk.messages.edit(
                                peer_id=int(peer_id),
                                conversation_message_id=cmid_ev,
                                keyboard='{"inline":true,"buttons":[]}',
                            )
                        except Exception:
                            pass
                        send_msg(
                            int(peer_id),
                            f"📝 Модератор {get_user_mention_with_name(user_id)} взял вопрос #{int(qid)}.\n"
                            "Напишите ответ следующим сообщением в этот чат.",
                            kb_for_peer(int(peer_id)),
                        )
                        try:
                            vk.messages.sendMessageEventAnswer(
                                event_id=event_id,
                                user_id=user_id,
                                peer_id=peer_id,
                                event_data=json.dumps({"type": "show_snackbar", "text": "Режим ответа включен"}),
                            )
                        except Exception:
                            pass
                        continue

                    if cmd_ev == 'gpt_shorten':
                        if not (_is_owner(user_id) or _is_deputy_owner(user_id)):
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Недостаточно прав"}),
                                )
                            except Exception:
                                pass
                            continue
                        src = (GPT_LAST_ANSWER.get(int(user_id)) or "").strip()
                        if not src:
                            send_msg(int(peer_id), "Нет последнего ответа для сокращения. Сначала используйте /гпт {запрос}.", get_main_kb())
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Сначала вызовите /гпт"}),
                                )
                            except Exception:
                                pass
                            continue
                        think_mid = send_msg(int(peer_id), "⏳ Сокращаю...", None)
                        short_q = (
                            "Сократи ответ до 3-5 коротких пунктов, без воды и без потери смысла. "
                            "Только русский язык.\n\nТекст:\n" + src
                        )
                        short_answer = genapi_admin_answer(
                            short_q,
                            requester_id=user_id,
                            requester_name=get_user_name(user_id),
                            unrestricted=_genapi_unrestricted_for(user_id),
                        )
                        if short_answer:
                            GPT_LAST_ANSWER[int(user_id)] = str(short_answer)
                            send_msg(
                                int(peer_id),
                                f"🤖 Кратко:\n{_format_ai_answer_for_vk(short_answer)}",
                                get_gpt_answer_kb(),
                                disable_mentions=True,
                            )
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Готово"}),
                                )
                            except Exception:
                                pass
                        else:
                            send_msg(int(peer_id), "Не удалось сократить ответ. Попробуйте позже.", get_main_kb())
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Ошибка сокращения"}),
                                )
                            except Exception:
                                pass
                        if think_mid:
                            try:
                                vk.messages.delete(message_ids=str(int(think_mid)), delete_for_all=1)
                            except Exception:
                                pass
                        continue

                    if cmd_ev in ('transfer_confirm', 'transfer_cancel'):
                        try:
                            owner_id = int(payload_ev.get('owner_id') or 0)
                        except Exception:
                            owner_id = 0
                        cmid_ev = event.obj.get('conversation_message_id')
                        if owner_id and int(owner_id) != int(user_id):
                            try:
                                vk.messages.sendMessageEventAnswer(
                                    event_id=event_id,
                                    user_id=user_id,
                                    peer_id=peer_id,
                                    event_data=json.dumps({"type": "show_snackbar", "text": "Эта кнопка не для вас"}),
                                )
                            except Exception:
                                pass
                            continue
                        if cmd_ev == 'transfer_cancel':
                            try:
                                vk.messages.edit(
                                    peer_id=int(peer_id),
                                    conversation_message_id=cmid_ev,
                                    message="❎ Перевод отменён.",
                                    keyboard='{"inline":true,"buttons":[]}',
                                )
                            except Exception:
                                pass
                            continue
                        try:
                            target_id = int(payload_ev.get('uid') or 0)
                            amount = int(payload_ev.get('amt') or 0)
                        except Exception:
                            target_id, amount = 0, 0
                        ok_tr, msg_tr = _perform_transfer(user_id, target_id, amount)
                        try:
                            vk.messages.edit(
                                peer_id=int(peer_id),
                                conversation_message_id=cmid_ev,
                                message=msg_tr,
                                keyboard='{"inline":true,"buttons":[]}',
                            )
                        except Exception:
                            pass
                        if ok_tr:
                            cursor.execute(
                                "SELECT COALESCE(balance, 0), COALESCE(staff_balance, 0) FROM users WHERE user_id = ?",
                                (int(target_id),),
                            )
                            _tb2 = cursor.fetchone() or (0, 0)
                            tbal = int(_tb2[0] or 0) + int(_tb2[1] or 0)
                            send_msg(
                                int(target_id),
                                f"💸 Вам поступил перевод от {get_user_mention_with_name(user_id)}\n"
                                f"Сумма: +{format_click(amount)}$\n"
                                f"Всего на счетах: {format_click(tbal)}$",
                                kb_for_peer(int(target_id)),
                            )
                        continue

                    if cmd_ev == 'pet_info':
                        user, _ = get_user(user_id)
                        energy, fed = user[2], user[3]
                        _, pet_name_ev, pet_power_ev = get_local_pet_info(user_id)
                        pet_line_ev = f"🐶 Питомец: {pet_name_ev}"
                        if not (user[5] == 1 or user[11] > time.time()):
                            try: vk.messages.edit(peer_id=peer_id, conversation_message_id=event.obj.get('conversation_message_id'), message=f"{pet_line_ev}\n⚡ Энергия: {energy}/50\n🍖 Накормленность: {fed}%\n\n(1 энергия = 1 клик. Каждые 2% сытости раз в ~6 сек дают 1 энергию, пока сытость ≥2%).\n\nУлучшение питомца доступно в меню «Мой питомец».", keyboard=get_pet_kb(user[1], fed, pet_power_ev, show_info=False, owner_user_id=user_id).get_keyboard())
                            except: pass
                elif event.type == VkBotEventType.WALL_REPLY_NEW:
                    threading.Thread(target=process_wall_reply, args=(event,), daemon=True).start()
                elif event.type == VkBotEventType.WALL_REPLY_DELETE:
                    threading.Thread(target=process_wall_reply_delete, args=(event,), daemon=True).start()
                elif event.type == VkBotEventType.WALL_POST_NEW:
                    attachment = f"wall-{GROUP_ID}_{event.obj['id']}"
                    dm_post_text = "Вышел новый пост!, за лайк и коментарий можно получить деньги!"
                    try:
                        vk.messages.send(
                            peer_id=RESTRICTED_CHAT_PEER_ID,
                            message="@all вышел новый пост",
                            attachment=attachment,
                            random_id=get_random_id(),
                            keyboard=kb_for_peer(RESTRICTED_CHAT_PEER_ID).get_keyboard(),
                        )
                    except Exception:
                        pass
                    cursor.execute("SELECT user_id FROM users WHERE is_registered = 1 AND is_banned = 0 AND ban_until < ?", (time.time(),))
                    for (uid,) in cursor.fetchall():
                        try:
                            vk.messages.send(
                                peer_id=int(uid),
                                message=dm_post_text,
                                attachment=attachment,
                                random_id=get_random_id(),
                                keyboard=get_main_kb().get_keyboard(),
                            )
                        except Exception:
                            pass
                elif event.type == VkBotEventType.WALL_REPOST:
                    try:
                        obj = event.obj if isinstance(event.obj, dict) else {}
                        repost_owner_id = int(obj.get("owner_id") or obj.get("from_id") or 0)
                        repost_post_id = int(obj.get("id") or obj.get("post_id") or 0)
                        src_owner = 0
                        src_post = 0
                        src_post_date = 0
                        ch = obj.get("copy_history")
                        if isinstance(ch, list) and ch:
                            ch0 = ch[0] if isinstance(ch[0], dict) else {}
                            src_owner = int(ch0.get("owner_id") or 0)
                            src_post = int(ch0.get("id") or 0)
                            src_post_date = int(ch0.get("date") or 0)
                        if src_owner == 0:
                            src_owner = int(obj.get("copy_owner_id") or 0)
                        if src_post == 0:
                            src_post = int(obj.get("copy_post_id") or 0)
                        if repost_owner_id > 0 and repost_post_id > 0 and src_owner == -int(GROUP_ID) and src_post > 0:
                            cursor.execute("SELECT COALESCE(is_registered, 0), COALESCE(is_banned, 0), COALESCE(ban_until, 0) FROM users WHERE user_id = ?", (repost_owner_id,))
                            urow = cursor.fetchone()
                            if urow and int(urow[0] or 0) == 1 and not (int(urow[1] or 0) == 1 or float(urow[2] or 0) > time.time()):
                                block_until = _get_repost_block_until(repost_owner_id)
                                if block_until > time.time():
                                    send_msg(
                                        repost_owner_id,
                                        f"⛔ Репост не засчитан: выплаты за репосты временно отключены до "
                                        f"{datetime.fromtimestamp(block_until, timezone.utc).strftime('%d.%m.%Y %H:%M')} UTC.",
                                        kb_for_peer(repost_owner_id),
                                    )
                                    continue
                                if src_post_date > 0:
                                    is_fresh = (time.time() - float(src_post_date)) <= 24 * 3600
                                else:
                                    is_fresh = _is_source_post_fresh_24h(src_owner, src_post)
                                if not is_fresh:
                                    send_msg(
                                        repost_owner_id,
                                        "⚠️ Репост не засчитан: запись опубликована более 24 часов назад.",
                                        kb_for_peer(repost_owner_id),
                                    )
                                    continue
                                started, repost_reason = _start_repost_campaign(repost_owner_id, repost_owner_id, repost_post_id, src_owner, src_post)
                                if started:
                                    send_msg(
                                        repost_owner_id,
                                        f"🔁 Репост засчитан!\n"
                                        f"Начислено: +{format_click(REPOST_DAILY_REWARD)}$ (день 1/{REPOST_MAX_DAYS}).\n"
                                        f"Сумма заблокирована до конца текущих суток кампании.\n"
                                        f"Если репост удалить, сумма за незавершённый день будет списана.",
                                        kb_for_peer(repost_owner_id),
                                    )
                                elif repost_reason == "duplicate_source":
                                    send_msg(
                                        repost_owner_id,
                                        "⚠️ Этот пост уже был засчитан вам ранее. Один и тот же пост нельзя монетизировать повторно.",
                                        kb_for_peer(repost_owner_id),
                                    )
                                elif repost_reason == "blocked":
                                    send_msg(
                                        repost_owner_id,
                                        "⛔ Репост не засчитан: выплаты за репосты временно отключены.",
                                        kb_for_peer(repost_owner_id),
                                    )
                    except Exception:
                        pass
                elif ev_type in ('message_reaction_event', 'message_reaction_add', 'message_reaction_new'):
                    robj = event.obj if isinstance(event.obj, dict) else {}
                    nested = []
                    for k in ('object', 'message', 'reaction'):
                        v = robj.get(k)
                        if isinstance(v, dict):
                            nested.append(v)
                    if isinstance(getattr(event, 'object', None), dict):
                        nested.append(event.object)

                    def _pick_int(keys):
                        for src in [robj] + nested:
                            for kk in keys:
                                vv = src.get(kk)
                                try:
                                    iv = int(vv)
                                    if iv != 0:
                                        return iv
                                except Exception:
                                    pass
                        return 0

                    actor_id = _pick_int(('actor_id', 'user_id', 'from_id', 'member_id'))
                    if actor_id == int(REACTION_DELETE_ADMIN_ID):
                        peer_id = _pick_int(('peer_id',))
                        cmid = _pick_int(('conversation_message_id', 'cmid', 'conversation_message_ids'))
                        if peer_id > 0 and cmid > 0:
                            try:
                                vk.messages.delete(peer_id=peer_id, cmids=str(cmid), delete_for_all=1)
                            except Exception:
                                pass
                elif ev_type == 'like_add' and event.obj.get('object_type') == 'post':
                    liker_id, post_id = event.obj.get('liker_id'), event.obj.get('object_id')
                    cursor.execute("SELECT is_registered, balance FROM users WHERE user_id = ?", (liker_id,))
                    u_data = cursor.fetchone()
                    if u_data and u_data[0] == 1:
                        cursor.execute("SELECT * FROM liked_posts WHERE user_id = ? AND post_id = ?", (liker_id, post_id))
                        if not cursor.fetchone():
                            update_user(liker_id, 'balance', u_data[1] + 90_000_000_000)
                            cursor.execute("INSERT INTO liked_posts (user_id, post_id) VALUES (?, ?)", (liker_id, post_id))
                            db.commit()
                            if not TECH_WORKS_ENABLED:
                                send_msg(liker_id, f"❤ Спасибо за лайк! Тебе начислено 90.000.000.000$\nТекущий баланс: {format_click(u_data[1] + 90_000_000_000)}$", get_main_kb())
                elif ev_type == 'like_remove' and event.obj.get('object_type') == 'post':
                    liker_id, post_id = event.obj.get('liker_id'), event.obj.get('object_id')
                    cursor.execute("SELECT * FROM liked_posts WHERE user_id = ? AND post_id = ?", (liker_id, post_id))
                    if cursor.fetchone():
                        cursor.execute("SELECT balance FROM users WHERE user_id = ?", (liker_id,))
                        u_data = cursor.fetchone()
                        if u_data:
                            update_user(liker_id, 'balance', max(0, u_data[0] - 90_000_000_000))
                            cursor.execute("DELETE FROM liked_posts WHERE user_id = ? AND post_id = ?", (liker_id, post_id))
                            db.commit()
                            if not TECH_WORKS_ENABLED:
                                send_msg(liker_id, f"💔 Вы убрали лайк! С вашего баланса списано 90.000.000.000$\nТекущий баланс: {format_click(max(0, u_data[0] - 90_000_000_000))}$", get_main_kb())
            except Exception as _lp_err:
                import traceback
                print("[longpoll handler]", _lp_err)
                print(traceback.format_exc())
    except KeyboardInterrupt:
        try:
            send_msg(RESTRICTED_CHAT_PEER_ID, "🔴 Бот выключается.", kb_for_peer(RESTRICTED_CHAT_PEER_ID))
        except Exception:
            pass
        break
    except requests.exceptions.ReadTimeout as _lp_timeout:
        print("[longpoll timeout]", _lp_timeout)
        longpoll = None
        time.sleep(1)
    except (requests.exceptions.ConnectionError, requests.exceptions.ConnectTimeout) as _lp_net_err:
        # Типичный случай: socket.gaierror / NameResolutionError — контейнер не резолвит lp.vk.com или нет сети.
        _LONGPOLL_NET_FAIL_STREAK = min(_LONGPOLL_NET_FAIL_STREAK + 1, 12)
        wait = min(120, max(5, 3 * (2 ** min(_LONGPOLL_NET_FAIL_STREAK - 1, 6))))
        print(
            "[longpoll] сеть/DNS: long poll недоступен (lp.vk.com). "
            f"Повтор через {wait}s (серия сбоев: {_LONGPOLL_NET_FAIL_STREAK}). "
            "Проверьте DNS, firewall и доступ в интернет.\n"
            f"    {_lp_net_err!r}"
        )
        longpoll = None
        time.sleep(wait)
    except Exception as _main_lp_err:
        import traceback
        print("[longpoll main loop]", _main_lp_err)
        print(traceback.format_exc())
        # При обрывах longpoll/ключа пытаемся пересоздать слушатель, чтобы бот сам восстановился.
        longpoll = None
        time.sleep(2)