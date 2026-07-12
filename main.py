"""
Traqd Casino — Telegram casino bot.
Neon Postgres persistence (wallets, active games, deposits/withdrawals) +
in-memory write-through cache for speed.
"""

import requests
import json
import time
import os
import random
import secrets
import hashlib
import html
import threading
import math
from roulette_stickers import get_sticker_for_number, get_colour

try:
    import db as db
    _DB_MODULE_AVAILABLE = True
except ImportError:
    _DB_MODULE_AVAILABLE = False

SESSION = requests.Session()

BOT_TOKEN = os.environ.get("BOT_TOKEN", "PASTE_YOUR_BOT_TOKEN_HERE")
API = f"https://api.telegram.org/bot{BOT_TOKEN}"

# Comma-separated Telegram user IDs allowed to run admin-only commands
# (e.g. /broadcast). Set this on Railway: ADMIN_IDS=123456789,987654321
ADMIN_IDS = set()
for _id in os.environ.get("ADMIN_IDS", "").split(","):
    _id = _id.strip()
    if _id.isdigit():
        ADMIN_IDS.add(int(_id))


def is_admin(user_id):
    return user_id in ADMIN_IDS


DATABASE_URL = os.environ.get("DATABASE_URL", "")
DB_ENABLED = False  # flipped to True in main() once db.init()/migrate() succeed

BOT_USERNAME = None


def fetch_bot_username():
    global BOT_USERNAME
    try:
        result = api_call("getMe")
        if result.get("ok"):
            BOT_USERNAME = result["result"]["username"]
    except Exception as e:
        print(f"Could not fetch bot username: {e}")
    return BOT_USERNAME

STARTING_BALANCE = 0.00
MIN_BET = 0.10
MAX_BET = 5000.00

MIN_DEPOSIT = 3.00
MIN_WITHDRAW = 10.00
MIN_TIP = 0.50
FIRST_DEPOSIT_BONUS_PCT = 1.30     # 130% match on the very first deposit
BONUS_WAGER_MULTIPLIER = 50        # bonus funds need 50x wagered before withdrawal
DEPOSIT_WAGER_MULTIPLIER = 1       # every deposit needs 1x wagered before ANY withdrawal

balances = {}
pending_bets = {}
active_mines_games = {}
active_towers_games = {}
active_keno_games = {}

# Per-user preferred display currency (balance is always tracked internally
# in USD - this only affects how it's *shown*, converted at a cached live
# rate). Defaults to "usd" for anyone who hasn't picked one.
user_display_currency = {}
CURRENCY_LOCK = threading.Lock()
known_usernames = {}  # lowercased @username (no @) -> user_id, for /tip lookups
all_known_user_ids = set()  # every user_id who's ever messaged the bot, for /broadcast
KNOWN_USERS_LOCK = threading.Lock()
test_fund_grants = {}  # user_id -> {"token", "original_wager_required", "total_test_amount"}
                        # so a stale expiry timer never wipes a newer /testfund grant
                        # and any pre-existing real bonus wager state can be restored
MAX_TESTFUND = 100.00
TESTFUND_LIFETIME_SECONDS = 3 * 3600  # 3 hours
SUPPORTED_CURRENCIES = {
    "usd": {"label": "USD", "emoji": "💵", "decimals": 2, "icon_id": "5409048419211682843"},
    "inr": {"label": "INR", "emoji": "🇮🇳", "decimals": 2, "icon_id": "5296467211735539812"},
    "ltc": {"label": "LTC", "emoji": "⚪", "decimals": 6, "icon_id": "5080170678729049007"},
}
_rate_cache = {"usd_inr": None, "usd_ltc": None, "fetched_at": 0}
_RATE_CACHE_TTL = 300  # seconds
active_crash_games = {}   # token -> game dict
user_active_crash = {}    # user_id -> token (one live crash round per user)
client_seeds = {}         # user_id -> client seed string (provably fair)
nonces = {}               # user_id -> int, increments every bet
fair_verifications = {}   # short token -> (game, params, server_seed, client_seed, nonce)
BALANCE_LOCK = threading.Lock()
MINES_LOCK = threading.Lock()
TOWERS_LOCK = threading.Lock()
KENO_LOCK = threading.Lock()
CRASH_LOCK = threading.Lock()
CLIENT_SEED_LOCK = threading.Lock()
FAIR_LOCK = threading.Lock()

# ---------------------------------------------------------------------------
# WALLET — real (withdrawable) balance vs. bonus (wager-locked) balance.
#
# Every user has:
#   real_balance      - deposits + winnings from real-balance bets.
#                       Withdrawable once the DEPOSIT wager requirement
#                       (below) is cleared.
#   bonus_balance     - money credited from promotions (currently just the
#                       130% first-deposit match). Can be played with like
#                       normal balance, but can't be withdrawn until enough
#                       has been wagered.
#   wager_required    - how much total betting volume is still needed
#                       before the CURRENT bonus_balance unlocks (130%
#                       bonus -> 50x this amount).
#   wager_progress    - how much has been wagered toward that requirement
#                       so far.
#   deposit_wager_required - how much total betting volume is still needed
#                       before the deposited (real) funds unlock for
#                       withdrawal. Every deposit adds 1x its USD amount
#                       here - a standard anti-abuse measure so deposits
#                       can't be immediately cashed back out unplayed.
#   deposit_wager_progress - how much has been wagered toward that
#                       requirement so far.
#   has_deposited     - whether the user has ever completed a deposit
#                       (gates the first-deposit bonus to a true first time).
#
# Bets are funded bonus-first, real-second (so bonus money actually gets
# used down instead of sitting untouched while real balance drains) - see
# spend_for_bet(). Winnings from a bet are credited back into whichever
# pool funded it, proportionally, so the split stays consistent. Every bet,
# regardless of which pool funded it, counts toward BOTH wager
# requirements at once (the bonus one and the deposit one) - that's
# standard practice and keeps this simple rather than needing two
# separately-tracked betting streams.
# ---------------------------------------------------------------------------

wallets = {}   # user_id -> {"real", "bonus", "wager_required", "wager_progress", "deposit_wager_required", "deposit_wager_progress", "has_deposited"}
WALLET_LOCK = threading.Lock()


def _ensure_wallet(user_id):
    if user_id not in wallets:
        loaded = db.load_wallet(user_id) if DB_ENABLED else None
        if loaded:
            # .setdefault(...) keeps this forward-compatible with wallet
            # rows saved before the deposit-wager fields existed.
            loaded.setdefault("deposit_wager_required", 0.0)
            loaded.setdefault("deposit_wager_progress", 0.0)
            wallets[user_id] = loaded
        else:
            wallets[user_id] = {
                "real": 0.0,
                "bonus": 0.0,
                "wager_required": 0.0,
                "wager_progress": 0.0,
                "deposit_wager_required": 0.0,
                "deposit_wager_progress": 0.0,
                "has_deposited": False,
            }
    return wallets[user_id]


def _persist_wallet(user_id):
    """Best-effort write-through to Postgres. Failures are logged but never
    block gameplay - the in-memory value (which the player already saw)
    stays authoritative for this process's lifetime either way. A DB outage
    degrades to "acts like the old in-memory-only build" rather than
    crashing bets."""
    if not DB_ENABLED:
        return
    try:
        db.save_wallet(user_id, wallets[user_id])
    except Exception as e:
        print(f"⚠️ Failed to persist wallet for user {user_id}: {e}")


def get_balance(user_id):
    """Total spendable balance (real + bonus combined) - used everywhere
    games already check 'can I afford this bet'."""
    with WALLET_LOCK:
        w = _ensure_wallet(user_id)
        return round(w["real"] + w["bonus"], 2)


def get_wallet_breakdown(user_id):
    with WALLET_LOCK:
        w = _ensure_wallet(user_id)
        return dict(w)


def _fetch_exchange_rates():
    """Refresh the USD->INR and USD->LTC cached rates. Best-effort - on any
    failure the stale cached values (or None on first-ever failure) are
    left in place, so a network hiccup degrades to 'last known rate'
    rather than breaking the /balance display."""
    try:
        resp = requests.get("https://api.exchangerate-api.com/v4/latest/USD", timeout=8)
        data = resp.json()
        rate = data.get("rates", {}).get("INR")
        if rate:
            _rate_cache["usd_inr"] = float(rate)
    except Exception as e:
        print(f"⚠️ Could not refresh USD/INR rate: {e}")

    try:
        resp = requests.get(
            "https://api.coingecko.com/api/v3/simple/price?ids=litecoin&vs_currencies=usd",
            timeout=8,
        )
        data = resp.json()
        ltc_usd_price = data.get("litecoin", {}).get("usd")
        if ltc_usd_price:
            _rate_cache["usd_ltc"] = 1 / float(ltc_usd_price)  # how many LTC per 1 USD
    except Exception as e:
        print(f"⚠️ Could not refresh USD/LTC rate: {e}")

    _rate_cache["fetched_at"] = time.time()


def _get_rates():
    if time.time() - _rate_cache["fetched_at"] > _RATE_CACHE_TTL:
        _fetch_exchange_rates()
    return _rate_cache


def get_user_currency(user_id):
    with CURRENCY_LOCK:
        return user_display_currency.get(user_id, "usd")


def set_user_currency(user_id, currency):
    with CURRENCY_LOCK:
        user_display_currency[user_id] = currency
    if DB_ENABLED:
        try:
            db.save_user_currency(user_id, currency)
        except Exception as e:
            print(f"⚠️ Could not persist currency pref for {user_id}: {e}")


def fmt_balance(user_id, usd_amount=None):
    """Format a USD balance in the user's preferred display currency.
    Pass usd_amount explicitly to convert an arbitrary figure (e.g. a bet
    result); omit it to format the user's current wallet balance."""
    if usd_amount is None:
        usd_amount = get_balance(user_id)

    currency = get_user_currency(user_id)
    meta = SUPPORTED_CURRENCIES[currency]

    if currency == "usd":
        value = usd_amount
    elif currency == "inr":
        rates = _get_rates()
        rate = rates["usd_inr"]
        if not rate:
            # Rate unavailable (never fetched successfully) - fall back to
            # USD rather than showing a wrong/zero number.
            return f"${usd_amount:.2f} (INR rate unavailable)"
        value = usd_amount * rate
    elif currency == "ltc":
        rates = _get_rates()
        rate = rates["usd_ltc"]
        if not rate:
            return f"${usd_amount:.2f} (LTC rate unavailable)"
        value = usd_amount * rate
    else:
        value = usd_amount

    return f'<tg-emoji emoji-id="{meta["icon_id"]}">{meta["emoji"]}</tg-emoji> {value:.{meta["decimals"]}f} {meta["label"]}'


def fmt_money(user_id, usd_amount):
    """Lighter-weight sibling of fmt_balance for use inline inside game
    result text (bet amounts, payouts, profit, balances) - just the number
    in the user's chosen currency, no emoji/label clutter since these show
    up many times per message. Falls back to USD if the live rate isn't
    available, rather than showing a stale/wrong number."""
    currency = get_user_currency(user_id)
    if currency == "usd":
        return f"${usd_amount:.2f}"

    rates = _get_rates()
    rate = rates.get("usd_inr") if currency == "inr" else rates.get("usd_ltc")
    if not rate:
        return f"${usd_amount:.2f}"

    value = usd_amount * rate
    if currency == "inr":
        return f"₹{value:,.2f}"
    return f"{value:.6f} LTC"


def resolve_bet_amount(user_id, raw_text):
    """Parses a bet amount the user typed, interpreting it in whichever
    currency they've picked with /currency (default USD) and converting to
    USD - the currency ALL wallet/betting logic runs in internally. This is
    what makes /currency actually change what you PLAY with, not just how
    the balance is displayed - a user on INR typing '100' means ₹100, not
    $100. Returns (usd_amount, error) where error is None on success, or
    one of "invalid_number" / "rate_unavailable"."""
    try:
        raw_value = float(raw_text)
    except (ValueError, TypeError):
        return None, "invalid_number"
    if raw_value <= 0:
        return None, "invalid_number"

    currency = get_user_currency(user_id)
    if currency == "usd":
        return round(raw_value, 2), None

    rates = _get_rates()
    rate = rates.get("usd_inr") if currency == "inr" else rates.get("usd_ltc")
    if not rate:
        return None, "rate_unavailable"

    return round(raw_value / rate, 2), None


def spend_for_bet(user_id, amount):
    """Deducts a bet, taking from bonus balance first, then real. Returns
    (bonus_portion, real_portion) so the caller can credit winnings back
    proportionally. Also advances wager progress by the full bet amount
    regardless of which pool funded it - wagering requirements count ALL
    play, not just bonus-funded play, which is the standard/fair approach."""
    with WALLET_LOCK:
        w = _ensure_wallet(user_id)
        total = w["real"] + w["bonus"]
        if amount > total + 1e-9:
            return None  # insufficient balance, caller should have already checked

        bonus_used = min(w["bonus"], amount)
        real_used = amount - bonus_used
        w["bonus"] = round(w["bonus"] - bonus_used, 2)
        w["real"] = round(w["real"] - real_used, 2)

        if w["wager_required"] > 0:
            w["wager_progress"] = round(w["wager_progress"] + amount, 2)
            if w["wager_progress"] >= w["wager_required"]:
                w["wager_required"] = 0.0
                w["wager_progress"] = 0.0

        if w["deposit_wager_required"] > 0:
            w["deposit_wager_progress"] = round(w["deposit_wager_progress"] + amount, 2)
            if w["deposit_wager_progress"] >= w["deposit_wager_required"]:
                w["deposit_wager_required"] = 0.0
                w["deposit_wager_progress"] = 0.0

        _persist_wallet(user_id)
        return (bonus_used, real_used)


def credit_winnings(user_id, payout, bonus_portion, real_portion, bet_amount):
    """Credits a payout back proportionally to how the bet was funded, so
    a bet split 60% bonus / 40% real pays out 60% into bonus_balance and
    40% into real_balance. If the bet was funded entirely from one pool
    (the overwhelmingly common case), the whole payout goes there."""
    with WALLET_LOCK:
        w = _ensure_wallet(user_id)
        if bet_amount <= 0:
            w["real"] = round(w["real"] + payout, 2)
        else:
            bonus_share = bonus_portion / bet_amount
            real_share = real_portion / bet_amount
            w["bonus"] = round(w["bonus"] + payout * bonus_share, 2)
            w["real"] = round(w["real"] + payout * real_share, 2)
        _persist_wallet(user_id)


_last_bet_split = {}  # user_id -> (bonus_used, real_used, bet_amount) from their last
                       # adjust_balance(-amount) call, consumed by the very next
                       # adjust_balance(+payout) call so winnings get credited back
                       # proportionally to whichever pool funded the bet - critical for
                       # bonus/test money to actually stay non-withdrawable (see below).


def adjust_balance(user_id, delta):
    """Legacy-compatible helper: every existing game calls adjust_balance()
    directly for both the bet deduction (-amount) and the payout (+payout)
    as two separate calls, rather than using spend_for_bet/credit_winnings.
    Negative deltas draw bonus-first same as spend_for_bet. Positive deltas
    used to always land in real_balance regardless of how the bet was
    funded - that was a real bug: it meant winnings from a bonus-funded (or
    /testfund-funded) bet became immediately withdrawable, completely
    bypassing the wagering requirement. Fixed by remembering the bonus/real
    split from the matching bet (via _last_bet_split) and crediting the
    payout back in that same proportion, same as credit_winnings() does."""
    with WALLET_LOCK:
        w = _ensure_wallet(user_id)
        if delta < 0:
            amount = -delta
            bonus_used = min(w["bonus"], amount)
            real_used = amount - bonus_used
            w["bonus"] = round(w["bonus"] - bonus_used, 2)
            w["real"] = round(w["real"] - real_used, 2)
            _last_bet_split[user_id] = (bonus_used, real_used, amount)
            if w["wager_required"] > 0:
                w["wager_progress"] = round(w["wager_progress"] + amount, 2)
                if w["wager_progress"] >= w["wager_required"]:
                    w["wager_required"] = 0.0
                    w["wager_progress"] = 0.0
            if w["deposit_wager_required"] > 0:
                w["deposit_wager_progress"] = round(w["deposit_wager_progress"] + amount, 2)
                if w["deposit_wager_progress"] >= w["deposit_wager_required"]:
                    w["deposit_wager_required"] = 0.0
                    w["deposit_wager_progress"] = 0.0
        else:
            payout = delta
            split = _last_bet_split.pop(user_id, None)
            if split and split[2] > 0:
                bonus_used, real_used, bet_amount = split
                bonus_share = bonus_used / bet_amount
                real_share = real_used / bet_amount
                w["bonus"] = round(w["bonus"] + payout * bonus_share, 2)
                w["real"] = round(w["real"] + payout * real_share, 2)
            else:
                # No matching bet found (e.g. an admin credit, /testfund
                # itself, or a refund) - land it in real, the safe default
                # for money that didn't come from a tracked wager.
                w["real"] = round(w["real"] + payout, 2)
        _persist_wallet(user_id)
        return round(w["real"] + w["bonus"], 2)


def get_withdrawable_balance(user_id):
    """Bonus balance becomes withdrawable (folds into real) once its own
    wager requirement is cleared - adjust_balance/spend_for_bet already
    handle that by zeroing wager_required when it's met.

    On top of that, the WHOLE real balance (deposits + winnings) is gated
    behind deposit_wager_required: every deposit needs to be wagered 1x
    before any of it - or anything won while playing it - can be cashed
    out. This is the standard "wager the deposit once" anti-abuse rule and
    applies even if there's no bonus involved."""
    with WALLET_LOCK:
        w = _ensure_wallet(user_id)
        if w["wager_required"] <= 0 and w["bonus"] > 0:
            # Bonus requirement cleared but bonus hasn't been folded in yet - fold it now.
            w["real"] = round(w["real"] + w["bonus"], 2)
            w["bonus"] = 0.0
            _persist_wallet(user_id)
        if w["deposit_wager_required"] > 0:
            return 0.0
        return w["real"]


def process_tip(sender_id, recipient_id, amount):
    """Moves `amount` from sender's REAL balance (never bonus - bonus can't
    be tipped) into recipient's real balance. If the sender's own deposit
    hasn't been fully wagered yet (deposit_wager_required > 0), that
    "unwagered" status carries over to the recipient for this amount - they
    now need to wager it 1x before it (or anything won with it) can be
    withdrawn, same as if they'd deposited it themselves. If the sender's
    funds were already fully wagered/clean, the tip arrives clean with no
    new requirement for the recipient. Returns (ok, reason)."""
    with WALLET_LOCK:
        sw = _ensure_wallet(sender_id)
        if amount > sw["real"] + 1e-9:
            return False, "insufficient_real"

        sw["real"] = round(sw["real"] - amount, 2)
        sender_unwagered = sw["deposit_wager_required"] > 0
        _persist_wallet(sender_id)

        rw = _ensure_wallet(recipient_id)
        rw["real"] = round(rw["real"] + amount, 2)
        if sender_unwagered:
            rw["deposit_wager_required"] = round(rw["deposit_wager_required"] + amount, 2)
        _persist_wallet(recipient_id)

        return True, "unwagered" if sender_unwagered else "clean"

# Public HTTPS base URL the bot is reachable at, used to build the Crash
# Mini App link (Telegram requires an https:// URL for web_app buttons).
# On Railway this is usually your generated domain, e.g.
# https://your-service.up.railway.app - set it as the APP_URL env var.
APP_URL = os.environ.get("APP_URL", "").rstrip("/")
if not APP_URL:
    railway_domain = os.environ.get("RAILWAY_PUBLIC_DOMAIN", "")
    if railway_domain:
        APP_URL = f"https://{railway_domain}"


def api_call(method, **params):
    # Telegram rate-limits per chat; a burst of replies landing at the same
    # instant (e.g. several delayed Coinflip results resolving together)
    # can get a 429 back. Previously that response was just returned as-is
    # and every caller ignored it, so the message silently never sent.
    # Retry a few times, honoring Telegram's own requested wait time.
    for attempt in range(4):
        resp = SESSION.post(f"{API}/{method}", data=params, timeout=15)
        data = resp.json()
        if data.get("ok") or data.get("error_code") != 429:
            return data
        wait = data.get("parameters", {}).get("retry_after", 1) + 0.2
        time.sleep(wait)
    return data


def mention(user_id, name):
    safe_name = html.escape(str(name))
    return f'<a href="tg://user?id={user_id}">{safe_name}</a>'


CUSTOM_EMOJIS = {
    "fire":    {"id": "5424972470023104089", "fallback": "🔥"},
    "money":   {"id": "5409048419211682843", "fallback": "💰"},
    "dice":    {"id": "", "fallback": "🎲"},
    "trophy":  {"id": "5224257782013769471", "fallback": "🏆"},
    "diamond": {"id": "", "fallback": "💎"},
    "chip":    {"id": "5765076709556623066", "fallback": "🪙"},
}

# Shared premium warning emoji, used everywhere a ⚠️ shows up in a bot message.
WARN_EMOJI = '<tg-emoji emoji-id="5447644880824181073">⚠️</tg-emoji>'

# Premium emojis used in Chicken Road message text (not button labels/alerts -
# Telegram doesn't render tg-emoji tags there, only in HTML message bodies).
CHICKEN_EMOJI = '<tg-emoji emoji-id="6334536360224884639">🐔</tg-emoji>'
DICE_EMOJI = "🎲"
CHICKEN_HIT_EMOJI = '<tg-emoji emoji-id="5276032951342088188">💥</tg-emoji>'

# Premium emojis used in Keno message text.
KENO_EMOJI = '<tg-emoji emoji-id="5332576234448628743">🎱</tg-emoji>'
KENO_NOLUCK_EMOJI = '<tg-emoji emoji-id="5456530180317134480">😬</tg-emoji>'

# Premium emojis used in Crash game messages.
CRASH_ROCKET_EMOJI = '<tg-emoji emoji-id="6017043379748082509">🚀</tg-emoji>'
CRASH_BOOM_EMOJI = '<tg-emoji emoji-id="5276032951342088188">💥</tg-emoji>'
CRASH_EXPIRED_EMOJI = '<tg-emoji emoji-id="5280725048494142112">⌛</tg-emoji>'

# Premium emojis used in Mines game messages.
MINES_BOMBSELECT_EMOJI = '<tg-emoji emoji-id="5249496324105062810">💣</tg-emoji>'
MINES_FRESH_BOARD_EMOJI = '<tg-emoji emoji-id="5199607933909888987">💣</tg-emoji>'
MINES_BOOM_LOSS_EMOJI = '<tg-emoji emoji-id="5276032951342088188">💥</tg-emoji>'
PAYOUT_EMOJI = '<tg-emoji emoji-id="5346123450358444391">💰</tg-emoji>'

# Premium emojis used in Towers game messages.
TOWERS_HEADER_EMOJI = '<tg-emoji emoji-id="5269554925183982228">🗼</tg-emoji>'
TOWERS_SNAKE_LOSS_EMOJI = '<tg-emoji emoji-id="5384389684820471923">🐍</tg-emoji>'
TOWERS_LOST_MONEY_EMOJI = '<tg-emoji emoji-id="5809816842713174497">💰</tg-emoji>'

# Premium emojis used in Blackjack game messages.
BJ_HEADER_EMOJI = '<tg-emoji emoji-id="5285420684699260907">🃏</tg-emoji>'
BJ_EXPIRED_EMOJI = '<tg-emoji emoji-id="5240241223632954241">⌛</tg-emoji>'
BJ_WIN_EMOJI = '<tg-emoji emoji-id="5258073279305889554">✅</tg-emoji>'
BJ_LOSE_EMOJI = '<tg-emoji emoji-id="5215572533507529497">❌</tg-emoji>'
BJ_PUSH_EMOJI = '<tg-emoji emoji-id="5371010084304342436">➖</tg-emoji>'


def cemoji(key):
    e = CUSTOM_EMOJIS.get(key)
    if not e:
        return ""
    if not e["id"]:
        return e["fallback"]
    return f'<tg-emoji emoji-id="{e["id"]}">{e["fallback"]}</tg-emoji>'


def check_for_custom_emoji_ids(message):
    entities = message.get("entities", []) or message.get("caption_entities", [])
    custom = [e for e in entities if e.get("type") == "custom_emoji"]
    if not custom:
        return False
    chat_id = message["chat"]["id"]
    lines = ["🔍 <b>Custom emoji id(s) found:</b>"]
    for e in custom:
        lines.append(f'<code>{e["custom_emoji_id"]}</code>')
    send_message(chat_id, "\n".join(lines))
    return True


def send_message(chat_id, text, reply_markup=None, parse_mode="HTML"):
    params = {"chat_id": chat_id, "text": text, "parse_mode": parse_mode}
    if reply_markup:
        import json
        params["reply_markup"] = json.dumps(reply_markup)
    return api_call("sendMessage", **params)


# ---------------------------------------------------------------------------
# WINS FEED — every game, every win, posted into one public channel.
#
# Set WINS_CHANNEL_ID to the channel's id (e.g. -1001234567890) once the
# bot has been added to that channel as admin with "Post Messages"
# permission. Leave it unset and this silently does nothing - no game is
# ever blocked or slowed down waiting on this.
# ---------------------------------------------------------------------------
WINS_CHANNEL_ID = os.environ.get("WINS_CHANNEL_ID", "").strip()

# Minimum payout (profit, not stake back) worth posting - keeps the feed
# from being spammed with $0.10 dice wins. Override with WINS_MIN_PROFIT.
WINS_MIN_PROFIT = float(os.environ.get("WINS_MIN_PROFIT", "0") or 0)

# One custom emoji for every win, regardless of game - keeps the feed
# looking like a single clean ticker instead of a wall of random icons.
WIN_FEED_EMOJI = '<tg-emoji emoji-id="5258073279305889554">✅</tg-emoji>'


def broadcast_win(user_id, username, game, bet_amount, payout_amount, detail=""):
    """Posts a win to the public wins-feed channel. Fire-and-forget: any
    failure here (channel not set, bot not admin there, network hiccup)
    is swallowed so it can never break the game flow that triggered it.

    profit = payout_amount - bet_amount is what gets checked against
    WINS_MIN_PROFIT and shown as the headline number - a $10 bet that pays
    back $10.50 reads a lot better as "+$0.50" than as "won $10.50"."""
    if not WINS_CHANNEL_ID:
        return
    try:
        profit = round(payout_amount - bet_amount, 2)
        if profit < WINS_MIN_PROFIT:
            return
        multiplier_txt = ""
        if bet_amount > 0:
            multiplier_txt = f" · {payout_amount / bet_amount:.2f}x"
        text = (
            f"{WIN_FEED_EMOJI} {mention(user_id, username)} just won <b>${profit:.2f}</b> "
            f"on <b>{game}</b>{multiplier_txt}"
        )
        if detail:
            text += f"\n{detail}"
        send_message(WINS_CHANNEL_ID, text)
    except Exception as e:
        print(f"broadcast_win failed (game={game}, user_id={user_id}): {e}")


def edit_message(chat_id, message_id, text, reply_markup=None, parse_mode="HTML"):
    params = {"chat_id": chat_id, "message_id": message_id, "text": text, "parse_mode": parse_mode}
    if reply_markup:
        import json
        params["reply_markup"] = json.dumps(reply_markup)
    return api_call("editMessageText", **params)


def send_sticker(chat_id, file_id):
    return api_call("sendSticker", chat_id=chat_id, sticker=file_id)


def send_photo(chat_id, photo_path_or_file_id, caption=None, reply_markup=None, parse_mode="HTML"):
    params = {"chat_id": chat_id}
    if caption:
        params["caption"] = caption
        params["parse_mode"] = parse_mode
    if reply_markup:
        import json
        params["reply_markup"] = json.dumps(reply_markup)

    if photo_path_or_file_id.startswith("/") or photo_path_or_file_id.startswith("./"):
        with open(photo_path_or_file_id, "rb") as f:
            files = {"photo": f}
            resp = SESSION.post(f"{API}/sendPhoto", data=params, files=files, timeout=30)
            result = resp.json()
            if result.get("ok"):
                global ROULETTE_TABLE_FILE_ID
                ROULETTE_TABLE_FILE_ID = result["result"]["photo"][-1]["file_id"]
            return result
    else:
        params["photo"] = photo_path_or_file_id
        return api_call("sendPhoto", **params)


def edit_message_caption(chat_id, message_id, caption, reply_markup=None, parse_mode="HTML"):
    params = {"chat_id": chat_id, "message_id": message_id, "caption": caption, "parse_mode": parse_mode}
    if reply_markup:
        import json
        params["reply_markup"] = json.dumps(reply_markup)
    return api_call("editMessageCaption", **params)


def answer_callback(callback_id, text=None, show_alert=False):
    params = {"callback_query_id": callback_id}
    if text:
        params["text"] = text
    if show_alert:
        params["show_alert"] = True
    return api_call("answerCallbackQuery", **params)


ROULETTE_TABLE_FILE_ID = None
ROULETTE_TABLE_PATH = os.path.join(os.path.dirname(__file__), "roulette_table.png")


# ---------------------------------------------------------------------------
# PAYMENTS — NowPayments (crypto deposits + withdrawals)
#
#   /deposit   -> pick a coin -> NowPayments invoice -> IPN webhook credits
#                 the wallet the moment the network confirms it. First-ever
#                 deposit also triggers a 130% bonus (50x wagering to unlock).
#                 Every deposit (first or not) also needs 1x wagering before
#                 any of the real balance becomes withdrawable.
#   /withdraw  -> pick a coin, enter address + amount -> NowPayments payout
#                 API sends the crypto. Only the withdrawable (real, or
#                 bonus with a cleared wager requirement) balance can be
#                 sent out - see get_withdrawable_balance().
#
# This mirrors the exact NowPayments integration pattern already proven
# working on the CasiX web app (deposit/create + webhook signature
# verification via HMAC-SHA512 of the sorted JSON body), adapted to a
# Telegram-bot-only flow with inline keyboards instead of a web form.
# ---------------------------------------------------------------------------

NOWPAYMENTS_API_KEY = os.environ.get("NOWPAYMENTS_API_KEY", "")
NOWPAYMENTS_IPN_SECRET = os.environ.get("NOWPAYMENTS_IPN_SECRET", "")
NOWPAYMENTS_BASE = "https://api.nowpayments.io/v1"

# Payouts (unlike deposit invoices) are NOT authorized by x-api-key alone -
# NowPayments requires a short-lived JWT (from /v1/auth, valid ~5 minutes)
# AND a 2FA code on every payout batch. These three additionally cover
# that:
#   NOWPAYMENTS_EMAIL / NOWPAYMENTS_PASSWORD - the dashboard login used
#       only to mint JWTs for payout calls (never sent anywhere else).
#   NOWPAYMENTS_2FA_SECRET - the base32 secret NowPayments shows once when
#       you enable "Use an app" under Dashboard > Account Settings > Two
#       step authentication for payouts. pyotp uses this to generate the
#       same 6-digit code an authenticator app would, so payouts verify
#       themselves with no human in the loop.
NOWPAYMENTS_EMAIL = os.environ.get("NOWPAYMENTS_EMAIL", "")
NOWPAYMENTS_PASSWORD = os.environ.get("NOWPAYMENTS_PASSWORD", "")
NOWPAYMENTS_2FA_SECRET = os.environ.get("NOWPAYMENTS_2FA_SECRET", "")

# code shown to the player -> exact NowPayments pay_currency code
DEPOSIT_COINS = {
    "usdttrc20": {"label": "USDT (TRC-20)", "emoji": "🟢", "icon_id": "5080152738650653521"},
    "usdtbsc":   {"label": "USDT (BEP-20)", "emoji": "🟡", "icon_id": "5080264137217409933"},
    "btc":       {"label": "Bitcoin",       "emoji": "🟠", "icon_id": "5080441454942225477"},
    "eth":       {"label": "Ethereum",      "emoji": "🔷", "icon_id": "5080063484935275722"},
    "ltc":       {"label": "Litecoin",      "emoji": "⚪", "icon_id": "5080170678729049007"},
    "trx":       {"label": "TRON",          "emoji": "🔴", "icon_id": "5080152738650653521"},
}

pending_deposits = {}      # nowpayments payment_id -> {"user_id", "usd_amount", "coin"}
deposit_log = []           # simple in-memory audit trail of credited deposits
withdraw_requests = {}     # withdraw_id -> {"user_id", "usd_amount", "coin", "address", "status"}
PAYMENTS_LOCK = threading.Lock()

# Short-lived state while a user is walking through /deposit or /withdraw
# (choosing a coin, then typing an amount / address as a plain message).
pending_deposit_flow = {}   # user_id -> {"coin": ...}
pending_withdraw_flow = {}  # user_id -> {"coin": ..., "step": "amount"/"address", "amount": ...}
FLOW_LOCK = threading.Lock()


def _set_deposit_flow(user_id, state):
    with FLOW_LOCK:
        pending_deposit_flow[user_id] = state
    if DB_ENABLED:
        try:
            db.save_payment_flow(user_id, "deposit", state)
        except Exception as e:
            print(f"⚠️ Could not persist deposit flow for {user_id}: {e}")


def _set_withdraw_flow(user_id, state):
    with FLOW_LOCK:
        pending_withdraw_flow[user_id] = state
    if DB_ENABLED:
        try:
            db.save_payment_flow(user_id, "withdraw", state)
        except Exception as e:
            print(f"⚠️ Could not persist withdraw flow for {user_id}: {e}")


def _clear_deposit_flow(user_id):
    with FLOW_LOCK:
        pending_deposit_flow.pop(user_id, None)
    if DB_ENABLED:
        try:
            db.clear_payment_flow(user_id)
        except Exception as e:
            print(f"⚠️ Could not clear persisted flow for {user_id}: {e}")


def _clear_withdraw_flow(user_id):
    with FLOW_LOCK:
        pending_withdraw_flow.pop(user_id, None)
    if DB_ENABLED:
        try:
            db.clear_payment_flow(user_id)
        except Exception as e:
            print(f"⚠️ Could not clear persisted flow for {user_id}: {e}")


# Cached JWT for payout calls - {"token": str, "expires_at": epoch_seconds}.
# Refreshed proactively a bit before NowPayments' 5-minute expiry so a
# payout never fires mid-request with a stale token.
_now_jwt_cache = {"token": None, "expires_at": 0}
NOW_JWT_LOCK = threading.Lock()
NOW_JWT_TTL_SECONDS = 280  # NowPayments issues 300s tokens; refresh at 280s to be safe


def _now_api(method, path, payload=None):
    headers = {"x-api-key": NOWPAYMENTS_API_KEY, "Content-Type": "application/json"}
    url = f"{NOWPAYMENTS_BASE}{path}"
    try:
        if method == "GET":
            r = SESSION.get(url, headers=headers, timeout=15)
        else:
            r = SESSION.post(url, headers=headers, json=payload, timeout=15)
        return r.status_code, r.json()
    except Exception as e:
        return 0, {"error": str(e)}


def _now_get_jwt():
    """Returns a valid JWT for payout/verify calls, fetching a fresh one
    via /v1/auth if the cached one is missing or close to expiry. This is
    the piece that makes payouts callable with zero manual steps - without
    it, /v1/payout rejects with 401 no matter how correct x-api-key is."""
    with NOW_JWT_LOCK:
        if _now_jwt_cache["token"] and time.time() < _now_jwt_cache["expires_at"]:
            return _now_jwt_cache["token"]

        if not NOWPAYMENTS_EMAIL or not NOWPAYMENTS_PASSWORD:
            return None

        try:
            r = SESSION.post(
                f"{NOWPAYMENTS_BASE}/auth",
                json={"email": NOWPAYMENTS_EMAIL, "password": NOWPAYMENTS_PASSWORD},
                timeout=15,
            )
            data = r.json()
        except Exception as e:
            print(f"NowPayments auth request failed: {e}")
            return None

        token = data.get("token")
        if not token:
            print(f"NowPayments auth failed: {data}")
            return None

        _now_jwt_cache["token"] = token
        _now_jwt_cache["expires_at"] = time.time() + NOW_JWT_TTL_SECONDS
        return token


def _now_payout_api(method, path, payload=None):
    """Like _now_api, but for the payout/verify endpoints that require a
    Bearer JWT on top of x-api-key. Returns (status_code, json_body) same
    as _now_api - callers check status/body the same way."""
    token = _now_get_jwt()
    if not token:
        return 0, {"error": "no_jwt", "detail": "NOWPAYMENTS_EMAIL/NOWPAYMENTS_PASSWORD not set or auth failed"}

    headers = {
        "x-api-key": NOWPAYMENTS_API_KEY,
        "Authorization": f"Bearer {token}",
        "Content-Type": "application/json",
    }
    url = f"{NOWPAYMENTS_BASE}{path}"
    try:
        if method == "GET":
            r = SESSION.get(url, headers=headers, timeout=15)
        else:
            r = SESSION.post(url, headers=headers, json=payload, timeout=15)
        return r.status_code, r.json()
    except Exception as e:
        return 0, {"error": str(e)}


def _now_generate_2fa_code():
    """Generates the current 6-digit TOTP code for payout verification,
    the same way an authenticator app would - using the secret NowPayments
    showed once when 2FA-via-app was enabled for payouts. Returns None if
    NOWPAYMENTS_2FA_SECRET isn't configured."""
    if not NOWPAYMENTS_2FA_SECRET:
        return None
    import pyotp
    return pyotp.TOTP(NOWPAYMENTS_2FA_SECRET).now()


def balance_action_keyboard():
    """Shown under /balance - one tap straight into the deposit or
    withdraw flow. Uses Bot API 9.4's button style + icon_custom_emoji_id
    fields: Deposit is blue (style=primary) with the deposit premium
    emoji, Withdraw is green (style=success) with the withdraw premium
    emoji. icon_custom_emoji_id only renders if the bot owner has active
    Telegram Premium (or a Fragment-purchased username) - it's silently
    ignored otherwise, so this degrades gracefully either way."""
    return {
        "inline_keyboard": [
            [
                {
                    "text": "Deposit",
                    "callback_data": "bal_action:deposit",
                    "style": "primary",
                    "icon_custom_emoji_id": "5264895611517300926",
                },
                {
                    "text": "Withdraw",
                    "callback_data": "bal_action:withdraw",
                    "style": "success",
                    "icon_custom_emoji_id": "5472250091332993630",
                },
            ]
        ]
    }


def deposit_coin_keyboard():
    rows = []
    row = []
    for code, meta in DEPOSIT_COINS.items():
        row.append({
            "text": meta["label"],
            "callback_data": f"dep_coin:{code}",
            "icon_custom_emoji_id": meta["icon_id"],
        })
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    return {"inline_keyboard": rows}


def withdraw_coin_keyboard():
    rows = []
    row = []
    for code, meta in DEPOSIT_COINS.items():
        row.append({
            "text": meta["label"],
            "callback_data": f"wd_coin:{code}",
            "icon_custom_emoji_id": meta["icon_id"],
        })
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    return {"inline_keyboard": rows}


# ---------------------------------------------------------------------------
# DEPOSIT / WITHDRAW GROUP INVITES
# ---------------------------------------------------------------------------
# Same single-use, owner-locked deep-link pattern as Crash/Blackjack/Chicken
# Road/Dice's group invites (see handle_crash_command's comment for why this
# exists at all) - except these two hand out a plain url button rather than
# a web_app button, since deposit/withdraw are pure conversational DM flows
# with no Mini App page behind them.

active_deposit_invites = {}    # invite_token -> {owner_id, owner_name, used}
DEPOSIT_INVITE_LOCK = threading.Lock()
DEPOSIT_INVITE_TIMEOUT = 300

active_withdraw_invites = {}   # invite_token -> {owner_id, owner_name, used}
WITHDRAW_INVITE_LOCK = threading.Lock()
WITHDRAW_INVITE_TIMEOUT = 300


def deposit_invite_expiry(invite_token):
    time.sleep(DEPOSIT_INVITE_TIMEOUT)
    with DEPOSIT_INVITE_LOCK:
        active_deposit_invites.pop(invite_token, None)


def withdraw_invite_expiry(invite_token):
    time.sleep(WITHDRAW_INVITE_TIMEOUT)
    with WITHDRAW_INVITE_LOCK:
        active_withdraw_invites.pop(invite_token, None)


def handle_deposit_command(chat_id, user_id, username, args, chat_type="private"):
    if not NOWPAYMENTS_API_KEY:
        send_message(chat_id, f"{WARN_EMOJI} Deposits aren't configured yet - the bot owner needs to set NOWPAYMENTS_API_KEY.")
        return

    if chat_type != "private":
        # Deposit/withdraw only ever run in DM - the amount and address
        # steps are plain typed replies, and typing a wallet amount into a
        # group chat is exactly what we don't want. Same single-use,
        # owner-locked deep-link pattern as Crash/Dice/Blackjack/Chicken
        # Road's group invites - but a PLAIN url button, not a web_app
        # button, since there's no Mini App here at all, just a redirect
        # into DM where the existing conversational flow takes over.
        if not BOT_USERNAME:
            send_message(chat_id, f"{WARN_EMOJI} Bot isn't fully started yet - try again in a few seconds.")
            return
        invite_token = secrets.token_urlsafe(8)
        with DEPOSIT_INVITE_LOCK:
            active_deposit_invites[invite_token] = {
                "owner_id": user_id, "owner_name": username, "used": False,
            }
        threading.Thread(target=deposit_invite_expiry, args=(invite_token,), daemon=True).start()
        deep_link = f"https://t.me/{BOT_USERNAME}?start=depi_{invite_token}"
        send_message(
            chat_id,
            f"💳 <b>Deposit</b> — {mention(user_id, username)}\n\n"
            f"Deposits only run in DM. This button is one-time use, only for {mention(user_id, username)}:",
            reply_markup={"inline_keyboard": [[{"text": "Deposit in DM", "url": deep_link}]]}
        )
        return

    _clear_deposit_flow(user_id)
    send_message(
        chat_id,
        f"💳 <b>Deposit</b> — {mention(user_id, username)}\n\n"
        f"Minimum deposit: <b>${MIN_DEPOSIT:.2f}</b>\n\n"
        f"Choose a coin to deposit with:",
        reply_markup=deposit_coin_keyboard()
    )


def handle_withdraw_command(chat_id, user_id, username, args, chat_type="private"):
    if not NOWPAYMENTS_API_KEY:
        send_message(chat_id, f"{WARN_EMOJI} Withdrawals aren't configured yet - the bot owner needs to set NOWPAYMENTS_API_KEY.")
        return

    if chat_type != "private":
        # Same group->DM redirect as handle_deposit_command above - plain
        # url button into DM, no Mini App, no balance/amount details ever
        # shown in the group.
        if not BOT_USERNAME:
            send_message(chat_id, f"{WARN_EMOJI} Bot isn't fully started yet - try again in a few seconds.")
            return
        invite_token = secrets.token_urlsafe(8)
        with WITHDRAW_INVITE_LOCK:
            active_withdraw_invites[invite_token] = {
                "owner_id": user_id, "owner_name": username, "used": False,
            }
        threading.Thread(target=withdraw_invite_expiry, args=(invite_token,), daemon=True).start()
        deep_link = f"https://t.me/{BOT_USERNAME}?start=wdi_{invite_token}"
        send_message(
            chat_id,
            f"💸 <b>Withdraw</b> — {mention(user_id, username)}\n\n"
            f"Withdrawals only run in DM. This button is one-time use, only for {mention(user_id, username)}:",
            reply_markup={"inline_keyboard": [[{"text": "Withdraw in DM", "url": deep_link}]]}
        )
        return

    withdrawable = get_withdrawable_balance(user_id)
    w = get_wallet_breakdown(user_id)

    if withdrawable < MIN_WITHDRAW:
        extra = ""
        if w["deposit_wager_required"] > 0:
            remaining_deposit = round(w["deposit_wager_required"] - w["deposit_wager_progress"], 2)
            extra += (
                f"\n\nYou still have a deposit wagering requirement (1×): "
                f"<b>${remaining_deposit:.2f}</b> more wagered needed before "
                f"any of your balance can be withdrawn."
            )
        if w["wager_required"] > 0:
            remaining = round(w["wager_required"] - w["wager_progress"], 2)
            extra += (
                f"\n\nYou still have a bonus wagering requirement: "
                f"<b>${remaining:.2f}</b> more wagered needed to unlock "
                f"<b>${w['bonus']:.2f}</b> in bonus funds."
            )
        send_message(
            chat_id,
            f"{WARN_EMOJI} Minimum withdrawal is <b>${MIN_WITHDRAW:.2f}</b>.\n"
            f"Your withdrawable balance: <b>${withdrawable:.2f}</b>{extra}"
        )
        return

    _clear_withdraw_flow(user_id)

    send_message(
        chat_id,
        f"💸 <b>Withdraw</b> — {mention(user_id, username)}\n\n"
        f"Withdrawable balance: <b>${withdrawable:.2f}</b>\n"
        f"Minimum withdrawal: <b>${MIN_WITHDRAW:.2f}</b>\n\n"
        f"Choose a coin to withdraw to:",
        reply_markup=withdraw_coin_keyboard()
    )


def start_deposit_amount_prompt(chat_id, user_id, username, coin):
    _set_deposit_flow(user_id, {"coin": coin})
    meta = DEPOSIT_COINS[coin]
    send_message(
        chat_id,
        f'<tg-emoji emoji-id="{meta["icon_id"]}">{meta["emoji"]}</tg-emoji> <b>{meta["label"]} Deposit</b>\n\n'
        f"Reply with the USD amount you want to deposit (min ${MIN_DEPOSIT:.2f}).\n"
        f"Example: <code>25</code>"
    )


def start_withdraw_amount_prompt(chat_id, user_id, username, coin):
    withdrawable = get_withdrawable_balance(user_id)
    _set_withdraw_flow(user_id, {"coin": coin, "step": "amount"})
    meta = DEPOSIT_COINS[coin]
    send_message(
        chat_id,
        f'<tg-emoji emoji-id="{meta["icon_id"]}">{meta["emoji"]}</tg-emoji> <b>{meta["label"]} Withdrawal</b>\n\n'
        f"Withdrawable balance: <b>${withdrawable:.2f}</b>\n\n"
        f"Reply with the USD amount you want to withdraw (min ${MIN_WITHDRAW:.2f}).\n"
        f"Example: <code>20</code>"
    )


def _apply_first_deposit_bonus(user_id, usd_amount):
    """Called once, only on a user's very first successfully credited
    deposit. Adds 130% of the deposit as bonus balance, locked behind a
    50x wagering requirement on that bonus amount specifically (separate
    from the 1x deposit-wager requirement applied to every deposit by
    _apply_deposit_wager_requirement)."""
    with WALLET_LOCK:
        w = _ensure_wallet(user_id)
        if w["has_deposited"]:
            return 0.0
        w["has_deposited"] = True
        bonus_amount = round(usd_amount * FIRST_DEPOSIT_BONUS_PCT, 2)
        w["bonus"] = round(w["bonus"] + bonus_amount, 2)
        w["wager_required"] = round(w["wager_required"] + bonus_amount * BONUS_WAGER_MULTIPLIER, 2)
        return bonus_amount


def _apply_deposit_wager_requirement(user_id, usd_amount):
    """Called on EVERY credited deposit (not just the first). Adds 1x the
    deposited USD amount to deposit_wager_required - the whole real
    balance (deposits + any winnings) stays locked from withdrawal until
    that volume has been wagered. Returns the new total requirement so
    callers can show it to the player."""
    with WALLET_LOCK:
        w = _ensure_wallet(user_id)
        w["deposit_wager_required"] = round(
            w["deposit_wager_required"] + usd_amount * DEPOSIT_WAGER_MULTIPLIER, 2
        )
        _persist_wallet(user_id)
        return w["deposit_wager_required"]


def process_deposit_amount(chat_id, user_id, username, text):
    with FLOW_LOCK:
        flow = pending_deposit_flow.get(user_id)
    if not flow:
        return False

    if not APP_URL:
        # Without a reachable APP_URL, NowPayments has nowhere to send the
        # IPN webhook that actually credits the balance - the crypto would
        # arrive but the player's wallet would never update. Refuse up
        # front rather than take money that can't be automatically credited.
        send_message(
            chat_id,
            f"{WARN_EMOJI} Deposits are temporarily unavailable (server URL not configured). "
            "Please try again shortly or contact support."
        )
        _clear_deposit_flow(user_id)
        return True

    try:
        usd_amount = float(text.strip())
    except ValueError:
        send_message(chat_id, f"{WARN_EMOJI} Please reply with a plain number, e.g. <code>25</code>")
        return True

    if usd_amount < MIN_DEPOSIT:
        send_message(chat_id, f"{WARN_EMOJI} Minimum deposit is ${MIN_DEPOSIT:.2f}")
        return True
    if usd_amount > 50000:
        send_message(chat_id, f"{WARN_EMOJI} Maximum deposit is $50,000. Contact support for larger amounts.")
        return True

    coin = flow["coin"]
    meta = DEPOSIT_COINS[coin]

    order_id = f"tc_{user_id}_{int(time.time())}"
    status, resp = _now_api("POST", "/payment", {
        "price_amount": usd_amount,
        "price_currency": "usd",
        "pay_currency": coin,
        "order_id": order_id,
        "order_description": f"Traqd Casino deposit - user {user_id}",
        "ipn_callback_url": f"{APP_URL}/api/nowpayments/ipn" if APP_URL else None,
    })

    if status not in (200, 201) or "payment_id" not in resp:
        send_message(chat_id, f"{WARN_EMOJI} Couldn't create the deposit invoice right now. Please try again shortly.")
        print(f"NowPayments create-payment failed: status={status} resp={resp}")
        _clear_deposit_flow(user_id)
        return True

    payment_id = str(resp["payment_id"])
    pay_address = resp.get("pay_address", "?")
    pay_amount = resp.get("pay_amount", "?")

    with PAYMENTS_LOCK:
        pending_deposits[payment_id] = {
            "user_id": user_id,
            "chat_id": chat_id,
            "username": username,
            "usd_amount": usd_amount,
            "coin": coin,
            "created_at": time.time(),
        }

    _clear_deposit_flow(user_id)

    send_message(
        chat_id,
        f'<tg-emoji emoji-id="{meta["icon_id"]}">{meta["emoji"]}</tg-emoji> <b>Send exactly this to complete your deposit:</b>\n\n'
        f"Amount: <code>{pay_amount}</code> {coin.upper()}\n"
        f"Address:\n<code>{pay_address}</code>\n\n"
        f"Your balance updates automatically once the network confirms it - "
        f"usually within a few minutes. No need to do anything else here."
    )
    return True


def process_withdraw_amount(chat_id, user_id, username, text):
    with FLOW_LOCK:
        flow = pending_withdraw_flow.get(user_id)
    if not flow or flow.get("step") != "amount":
        return False

    try:
        usd_amount = float(text.strip())
    except ValueError:
        send_message(chat_id, f"{WARN_EMOJI} Please reply with a plain number, e.g. <code>20</code>")
        return True

    withdrawable = get_withdrawable_balance(user_id)
    if usd_amount < MIN_WITHDRAW:
        send_message(chat_id, f"{WARN_EMOJI} Minimum withdrawal is ${MIN_WITHDRAW:.2f}")
        return True
    if usd_amount > withdrawable:
        send_message(chat_id, f"{WARN_EMOJI} You only have ${withdrawable:.2f} withdrawable right now.")
        return True

    _set_withdraw_flow(user_id, {"coin": flow["coin"], "step": "address", "amount": usd_amount})

    meta = DEPOSIT_COINS[flow["coin"]]
    send_message(
        chat_id,
        f'<tg-emoji emoji-id="{meta["icon_id"]}">{meta["emoji"]}</tg-emoji> Now reply with your <b>{meta["label"]}</b> wallet address to receive ${usd_amount:.2f}.'
    )
    return True


def _now_create_and_verify_payout(address, coin, usd_amount):
    """Full automated payout flow: create the payout batch (JWT-authed),
    then immediately verify it with a self-generated TOTP code (same
    mechanism as an authenticator app) so no human ever has to click
    anything. Returns (ok, stage, detail):
        stage == "success"       -> ok=True, payout created and verified
        stage == "create_failed" -> ok=False, NOTHING was created on
                                     NowPayments' side - safe to refund
        stage == "verify_failed" -> ok=False, the payout batch WAS
                                     created but couldn't self-verify
                                     (missing/wrong TOTP secret, or a rare
                                     code-timing miss) - do NOT refund,
                                     since the batch still exists on
                                     NowPayments and may complete once
                                     someone verifies it manually in the
                                     dashboard within the 1-hour window.
    """
    status, resp = _now_payout_api("POST", "/payout", {
        "ipn_callback_url": f"{APP_URL}/api/nowpayments/payout-ipn" if APP_URL else None,
        "withdrawals": [{
            "address": address,
            "currency": coin,
            "amount": usd_amount,
        }]
    })
    if status not in (200, 201):
        return False, "create_failed", {"status": status, "resp": resp}

    # NowPayments' response shape has varied across API versions - accept
    # either a top-level batch id or one nested in the withdrawals array.
    withdrawals = resp.get("withdrawals") or []
    batch_id = (
        resp.get("batch_withdrawal_id")
        or resp.get("id")
        or (withdrawals[0].get("batch_withdrawal_id") if withdrawals else None)
        or (withdrawals[0].get("id") if withdrawals else None)
    )
    if not batch_id:
        return False, "create_failed", {"status": status, "resp": resp, "detail": "no batch id in response"}

    # Try to self-verify with a TOTP code. A code is valid for a 30s
    # window - if we land right on the boundary, one retry with the next
    # window covers it rather than failing the whole payout over timing.
    for attempt in range(2):
        code = _now_generate_2fa_code()
        if not code:
            return False, "verify_failed", {
                "batch_id": batch_id, "create_resp": resp,
                "detail": "NOWPAYMENTS_2FA_SECRET not configured - payout created but unverified",
            }
        v_status, v_resp = _now_payout_api("POST", f"/payout/{batch_id}/verify", {"verification_code": code})
        if v_status in (200, 201):
            return True, "success", {"batch_id": batch_id, "create_resp": resp, "verify_resp": v_resp}
        if attempt == 0:
            time.sleep(2)  # give a boundary-case code a moment to roll over

    return False, "verify_failed", {"batch_id": batch_id, "create_resp": resp, "verify_status": v_status, "verify_resp": v_resp}


def process_withdraw_address(chat_id, user_id, username, text):
    with FLOW_LOCK:
        flow = pending_withdraw_flow.get(user_id)
    if not flow or flow.get("step") != "address":
        return False

    address = text.strip()
    if len(address) < 10 or len(address) > 128 or " " in address:
        send_message(chat_id, f"{WARN_EMOJI} That doesn't look like a valid wallet address. Please try again.")
        return True

    coin = flow["coin"]
    usd_amount = flow["amount"]
    meta = DEPOSIT_COINS[coin]

    withdrawable = get_withdrawable_balance(user_id)
    if usd_amount > withdrawable:
        send_message(chat_id, f"{WARN_EMOJI} Your withdrawable balance changed and is now only ${withdrawable:.2f}. Start over with /withdraw.")
        _clear_withdraw_flow(user_id)
        return True

    # Deduct immediately so the same funds can't be withdrawn twice while
    # the payout request is in flight.
    adjust_balance(user_id, -usd_amount)

    withdraw_id = secrets.token_hex(6)
    with PAYMENTS_LOCK:
        withdraw_requests[withdraw_id] = {
            "user_id": user_id,
            "chat_id": chat_id,
            "username": username,
            "usd_amount": usd_amount,
            "coin": coin,
            "address": address,
            "status": "pending",
            "created_at": time.time(),
        }

    _clear_withdraw_flow(user_id)

    ok, stage, detail = _now_create_and_verify_payout(address, coin, usd_amount)

    if not ok and stage == "create_failed":
        # Nothing was created on NowPayments' side - safe to refund in full.
        adjust_balance(user_id, usd_amount)
        with PAYMENTS_LOCK:
            withdraw_requests[withdraw_id]["status"] = "failed"
        send_message(
            chat_id,
            f"{WARN_EMOJI} Couldn't process the withdrawal right now - your ${usd_amount:.2f} has been refunded to your balance. Please try again shortly."
        )
        print(f"NowPayments payout creation failed for withdraw_id={withdraw_id}: {detail}")
        return True

    if not ok and stage == "verify_failed":
        # The payout batch DOES exist on NowPayments (funds are already
        # earmarked there) - refunding here would risk a double-payout if
        # it later gets verified manually, so we don't touch the balance.
        # NowPayments auto-rejects unverified batches after an hour if
        # nobody validates them, at which point they'd need to be refunded
        # by hand after confirming via GET /v1/payout/:id that it never went out.
        with PAYMENTS_LOCK:
            withdraw_requests[withdraw_id]["status"] = "awaiting_manual_2fa"
            withdraw_requests[withdraw_id]["batch_id"] = detail.get("batch_id")
        send_message(
            chat_id,
            f'<tg-emoji emoji-id="{meta["icon_id"]}">{meta["emoji"]}</tg-emoji> <b>Withdrawal received!</b>\n\n'
            f"Amount: <b>${usd_amount:.2f}</b>\n"
            f"Coin: {meta['label']}\n\n"
            f"It's queued and pending confirmation - this can take a little longer than usual. "
            f"You'll be notified the moment it's sent."
        )
        print(f"⚠️ Payout needs manual 2FA verification - withdraw_id={withdraw_id} batch_id={detail.get('batch_id')} detail={detail}")
        return True

    with PAYMENTS_LOCK:
        withdraw_requests[withdraw_id]["status"] = "processing"
        withdraw_requests[withdraw_id]["batch_id"] = detail.get("batch_id")

    new_balance = get_balance(user_id)
    send_message(
        chat_id,
        f'<tg-emoji emoji-id="{meta["icon_id"]}">{meta["emoji"]}</tg-emoji> <b>Withdrawal submitted!</b>\n\n'
        f"Amount: <b>${usd_amount:.2f}</b>\n"
        f"Coin: {meta['label']}\n"
        f"Address: <code>{address}</code>\n\n"
        f"It's on its way - crypto payouts typically arrive within a few minutes.\n"
        f"New balance: <b>${new_balance:.2f}</b>"
    )
    return True


def try_handle_payment_flow_message(chat_id, user_id, username, text):
    """Called from handle_message for any plain (non-command) text - lets
    a user reply with a bare number/address while walking through
    /deposit or /withdraw. Returns True if it consumed the message."""
    if process_deposit_amount(chat_id, user_id, username, text):
        return True
    if process_withdraw_amount(chat_id, user_id, username, text):
        return True
    if process_withdraw_address(chat_id, user_id, username, text):
        return True
    return False


def handle_deposit_callback(callback_id, chat_id, user_id, username, coin):
    if coin not in DEPOSIT_COINS:
        answer_callback(callback_id, "Unknown coin.")
        return
    answer_callback(callback_id)
    start_deposit_amount_prompt(chat_id, user_id, username, coin)


def handle_withdraw_coin_callback(callback_id, chat_id, user_id, username, coin):
    if coin not in DEPOSIT_COINS:
        answer_callback(callback_id, "Unknown coin.")
        return
    answer_callback(callback_id)
    start_withdraw_amount_prompt(chat_id, user_id, username, coin)


# ---------------------------------------------------------------------------
# NowPayments IPN webhook — this bot doesn't run a normal web framework,
# so the webhook is wired into the same lightweight HTTP server crash_web.py
# already runs (via the same handle_get/handle_post(handler, path, ...)
# delegation contract used for the Mini Apps). See nowpayments_web.py.
# ---------------------------------------------------------------------------

def verify_nowpayments_signature(raw_body_dict, signature_header):
    if not NOWPAYMENTS_IPN_SECRET:
        return False
    import json as _json
    import hmac as _hmac
    sorted_body = _json.dumps(raw_body_dict, sort_keys=True, separators=(",", ":"))
    mac = _hmac.new(NOWPAYMENTS_IPN_SECRET.encode(), sorted_body.encode(), hashlib.sha512)
    expected = mac.hexdigest()
    return _hmac.compare_digest(expected, signature_header or "")


def handle_deposit_ipn(payload):
    """Called by nowpayments_web.py once the signature is verified. Credits
    the wallet, applies the 1x deposit-wager requirement to every deposit,
    and, if this is the user's first-ever deposit, also applies the 130%
    bonus (with its own 50x wager requirement)."""
    payment_id = str(payload.get("payment_id", ""))
    payment_status = payload.get("payment_status", "")

    with PAYMENTS_LOCK:
        pending = pending_deposits.get(payment_id)

    if not pending:
        return  # unknown/duplicate payment_id - ignore

    if payment_status not in ("finished", "confirmed"):
        return  # still waiting on more confirmations

    user_id = pending["user_id"]
    chat_id = pending["chat_id"]
    username = pending["username"]
    usd_amount = pending["usd_amount"]

    with PAYMENTS_LOCK:
        if payment_id not in pending_deposits:
            return  # already processed by a concurrent callback
        del pending_deposits[payment_id]
        deposit_log.append({
            "user_id": user_id, "usd_amount": usd_amount,
            "payment_id": payment_id, "at": time.time(),
        })

    adjust_balance(user_id, usd_amount)
    deposit_wager_total = _apply_deposit_wager_requirement(user_id, usd_amount)
    bonus_amount = _apply_first_deposit_bonus(user_id, usd_amount)

    new_balance = get_balance(user_id)
    msg = (
        f"{cemoji('money')} <b>Deposit confirmed!</b>\n\n"
        f"Amount: <b>${usd_amount:.2f}</b>\n"
    )
    if bonus_amount > 0:
        w = get_wallet_breakdown(user_id)
        msg += (
            f"🎁 First deposit bonus: <b>+${bonus_amount:.2f}</b> (130% match)\n"
            f"   Wager <b>${w['wager_required']:.2f}</b> total to unlock the bonus for withdrawal.\n"
        )
    msg += (
        f"   Wager <b>${deposit_wager_total:.2f}</b> total (1× your deposit) "
        f"before any of this balance can be withdrawn.\n"
    )
    msg += f"\nNew balance: <b>${new_balance:.2f}</b>"
    send_message(chat_id, msg)


def handle_payout_ipn(payload):
    """Optional: NowPayments can also notify on payout status changes.
    Currently just logged - the player already got a confirmation message
    when the payout was submitted."""
    print(f"Payout IPN: {payload}")


def get_client_seed(user_id):
    """Returns the user's current client seed, generating a random one the
    first time they're seen (checking the DB before generating fresh, so a
    restart doesn't silently reset everyone's provably-fair seed)."""
    with CLIENT_SEED_LOCK:
        if user_id not in client_seeds:
            loaded = db.load_fairness(user_id) if DB_ENABLED else None
            if loaded:
                client_seeds[user_id] = loaded["client_seed"]
                nonces[user_id] = loaded["nonce"]
            else:
                client_seeds[user_id] = secrets.token_hex(8)
                nonces[user_id] = 0
                if DB_ENABLED:
                    try:
                        db.save_fairness(user_id, client_seeds[user_id], 0)
                    except Exception as e:
                        print(f"⚠️ Failed to persist fairness for user {user_id}: {e}")
        return client_seeds[user_id]


def set_client_seed(user_id, seed):
    """Sets a custom client seed for the user and resets their nonce."""
    with CLIENT_SEED_LOCK:
        client_seeds[user_id] = seed
        nonces[user_id] = 0
        if DB_ENABLED:
            try:
                db.save_fairness(user_id, seed, 0)
            except Exception as e:
                print(f"⚠️ Failed to persist fairness for user {user_id}: {e}")


def get_nonce(user_id):
    with CLIENT_SEED_LOCK:
        return nonces.get(user_id, 0)


def next_nonce(user_id):
    """Call once per bet - bumps and returns the nonce for this user, so the
    same client seed never produces the same result twice."""
    with CLIENT_SEED_LOCK:
        if user_id not in client_seeds:
            loaded = db.load_fairness(user_id) if DB_ENABLED else None
            if loaded:
                client_seeds[user_id] = loaded["client_seed"]
                nonces[user_id] = loaded["nonce"]
            else:
                client_seeds[user_id] = secrets.token_hex(8)
                nonces[user_id] = 0
        nonces[user_id] = nonces.get(user_id, 0) + 1
        if DB_ENABLED:
            try:
                db.save_fairness(user_id, client_seeds[user_id], nonces[user_id])
            except Exception as e:
                print(f"⚠️ Failed to persist fairness for user {user_id}: {e}")
        return nonces[user_id]


def roll_new_client_seed(user_id):
    """Generates and stores a fresh random client seed for /newseed."""
    new_seed = secrets.token_hex(8)
    set_client_seed(user_id, new_seed)
    return new_seed


def store_fair_verification(game, server_seed, client_seed, nonce, params=""):
    """
    Stashes everything needed to verify a round behind a short random token,
    instead of cramming server_seed/client_seed/nonce into the deep-link
    payload itself. Telegram's /start payload only allows [A-Za-z0-9_-] and
    caps out at 64 characters - a 32-char server seed plus a 16+ char client
    seed alone blows past that, which is why the button used to do nothing.
    """
    token = secrets.token_urlsafe(8)
    with FAIR_LOCK:
        fair_verifications[token] = (game, params, server_seed, client_seed, nonce)
    return token


def generate_roulette_result(client_seed, nonce):
    server_seed = secrets.token_hex(16)
    combined = f"{server_seed}:{client_seed}:{nonce}"
    h = hashlib.sha256(combined.encode()).hexdigest()
    num = int(h[:8], 16) % 37
    return num, server_seed


def fair_button_keyboard(game, server_seed, client_seed, nonce, params=""):
    """
    game: short code identifying which game this seed belongs to -
          'r' (roulette), 'l' (limbo), 'm' (mines), 't' (towers), 'k' (keno),
          'c' (crash)
    params: any extra info needed to recompute the exact result (e.g. the
            bomb_count for mines, or the difficulty for towers). Empty
            string if the game needs none (roulette/limbo/crash).
    client_seed / nonce: the exact values used for THIS bet - stored under
            the token below so verification later doesn't depend on the
            user's current (possibly since-changed) client seed.
    """
    token = store_fair_verification(game, server_seed, client_seed, nonce, params)
    if BOT_USERNAME:
        return {
            "inline_keyboard": [
                [{"text": "Provably Fair", "icon_custom_emoji_id": "5330194932781050507", "url": f"https://t.me/{BOT_USERNAME}?start=fair_{token}"}]
            ]
        }
    return {
        "inline_keyboard": [
            [{"text": "Provably Fair", "icon_custom_emoji_id": "5330194932781050507", "callback_data": f"fair:{token}"}]
        ]
    }


def fair_verification_text(game, params, server_seed, client_seed, nonce):
    """
    Recomputes and formats the actual result for a given seed/game/params,
    so a normal user can see with their own eyes that it matches what
    happened in the game - not just a seed and a hash they can't use.
    """
    combined = f"{server_seed}:{client_seed}:{nonce}"
    result_hash = hashlib.sha256(combined.encode()).hexdigest()
    header = (
        f"🔒 <b>Provably Fair Verification</b>\n\n"
        f"Server Seed: <code>{server_seed}</code>\n"
        f"Client Seed: <code>{client_seed}</code>\n"
        f"Nonce: <code>{nonce}</code>\n\n"
        f"Result hash = SHA256(server_seed:client_seed:nonce). You can "
        f"compute that yourself and confirm it matches the hash below - "
        f"the server seed was generated before your bet, and your client "
        f"seed/nonce are yours, so the result couldn't have been changed "
        f"afterward.\n\n"
        f"Hash: <code>{result_hash}</code>\n\n"
    )

    if game == "r":
        num = int(result_hash[:8], 16) % 37
        colour = get_colour(num)
        colour_label = {"red": "🔴 Red", "black": "⚫ Black", "green": "🟢 Green"}[colour]
        body = (
            f"<b>Roulette</b>\n"
            f"Formula: first 8 hex chars of the hash, as a number, mod 37\n"
            f"Result: <b>{num}</b> ({colour_label})"
        )

    elif game == "l":
        r = int(result_hash[:13], 16) / float(1 << 52)
        raw_multiplier = ((1 - LIMBO_HOUSE_EDGE) / (1 - r)) ** (1 / LIMBO_TAIL_EXP)
        result_multiplier = max(1.00, math.floor(raw_multiplier * 100) / 100)
        body = (
            f"<b>Limbo</b>\n"
            f"Formula: first 13 hex chars of the hash -> uniform 0-1 value, "
            f"then ((1 - house edge) / (1 - value)) ^ (1 / tail exponent)\n"
            f"Result: <b>{result_multiplier:.2f}x</b>"
        )

    elif game == "m":
        bomb_count = int(params)
        rng = random.Random(result_hash)
        positions = list(range(MINES_TOTAL_TILES))
        rng.shuffle(positions)
        mine_positions = sorted(p + 1 for p in positions[:bomb_count])
        tiles_str = ", ".join(str(p) for p in mine_positions)
        body = (
            f"<b>Mines</b> ({bomb_count} mines)\n"
            f"Formula: the hash seeds a shuffle of tiles 1-25; the first "
            f"{bomb_count} shuffled tiles are the mines\n"
            f"Mines were on tiles: <b>{tiles_str}</b>"
        )

    elif game == "t":
        difficulty = params
        tiles_per_row = TOWERS_DIFFICULTY.get(difficulty, {}).get("tiles", 3)
        lines = []
        for row in range(1, TOWERS_ROWS + 1):
            snake_idx = towers_snake_index(server_seed, client_seed, nonce, row, tiles_per_row)
            lines.append(f"Row {row}: snake on tile {snake_idx + 1}")
        body = (
            f"<b>Towers</b> ({TOWERS_DIFFICULTY.get(difficulty, {}).get('label', difficulty)}, "
            f"{tiles_per_row} tiles/row)\n"
            f"Formula: each row's snake tile = sha256(server:client:nonce:row) mod tiles-per-row\n"
            + "\n".join(lines)
        )

    elif game == "k":
        try:
            picks_str, risk = params.split("-", 1)
            picks = int(picks_str)
        except Exception:
            picks, risk = 0, params
        rng = random.Random(result_hash)
        numbers = list(range(1, KENO_BOARD_SIZE + 1))
        rng.shuffle(numbers)
        drawn_numbers = sorted(numbers[:KENO_DRAWN_COUNT])
        drawn_str = ", ".join(str(n) for n in drawn_numbers)
        risk_label = KENO_RISK_CONFIG.get(risk, {}).get("label", risk)
        body = (
            f"<b>Keno</b> ({risk_label} risk, {picks} picks)\n"
            f"Formula: the hash seeds a shuffle of numbers 1-40; the first "
            f"10 shuffled numbers are drawn\n"
            f"Drawn numbers: <b>{drawn_str}</b>\n"
            f"(Compare against the numbers you picked to confirm your hit count.)"
        )

    elif game == "c":
        r = int(result_hash[:13], 16) / float(1 << 52)
        raw_multiplier = (1 - CRASH_HOUSE_EDGE) / (1 - r)
        crash_point = max(1.00, math.floor(raw_multiplier * 100) / 100)
        body = (
            f"<b>Crash</b>\n"
            f"Formula: first 13 hex chars of the hash -> uniform 0-1 value, "
            f"then (1 - house edge) / (1 - value)\n"
            f"Crash point: <b>{crash_point:.2f}x</b>"
        )

    elif game == "bj":
        rng = random.Random(result_hash)
        deck = [(r, s) for _ in range(BLACKJACK_DECKS) for r in RANKS for s in SUITS]
        rng.shuffle(deck)
        preview = ", ".join(f"{r}{s}" for r, s in deck[:8])
        body = (
            f"<b>Blackjack</b>\n"
            f"Formula: the hash seeds a shuffle of a {BLACKJACK_DECKS}-deck shoe "
            f"({BLACKJACK_DECKS * 52} cards); cards are dealt off the front in order\n"
            f"First 8 cards of the shoe: <b>{preview}</b>\n"
            f"(These match the cards you were dealt, in the order they came out.)"
        )

    elif game == "cf":
        r = int(result_hash[:13], 16) / float(1 << 52)
        result = "heads" if r < 0.5 else "tails"
        body = (
            f"<b>Coinflip</b>\n"
            f"Formula: first 13 hex chars of the hash -> uniform 0-1 value; "
            f"below 0.5 is heads, at or above is tails\n"
            f"Result: <b>{result}</b>"
        )

    elif game == "d":
        direction, target_str = params.split("|")
        target = float(target_str)
        r = int(result_hash[:13], 16) / float(1 << 52)
        roll = math.floor(r * 10000) / 100
        win = roll < target if direction == "under" else roll > target
        body = (
            f"<b>Dice</b>\n"
            f"Formula: first 13 hex chars of the hash -> uniform 0-1 value, "
            f"scaled to a roll between 0.00 and 99.99\n"
            f"Roll: <b>{roll:.2f}</b> (needed {direction} <b>{target:.2f}</b>)\n"
            f"Result: <b>{'Win' if win else 'Loss'}</b>"
        )

    else:
        body = "Couldn't identify the game for this seed - but the seed and hash above are still valid."

    return header + body


def roulette_main_keyboard(amount, user_id):
    return {
        "inline_keyboard": [
            [{"text": "🔢 Bet On Number", "callback_data": f"rl_type:pick_number:{amount}:{user_id}"}],
            [
                {"text": "1 to 12 · 1.93x", "callback_data": f"rl_type:dozen1:{amount}:{user_id}"},
                {"text": "13 to 24 · 1.93x", "callback_data": f"rl_type:dozen2:{amount}:{user_id}"},
                {"text": "25 to 36 · 1.93x", "callback_data": f"rl_type:dozen3:{amount}:{user_id}"},
            ],
            [
                {"text": "1 to 18 \xb7 1.93x", "callback_data": f"rl_type:low:{amount}:{user_id}"},
                {"text": "19 to 36 \xb7 1.93x", "callback_data": f"rl_type:high:{amount}:{user_id}"},
            ],
            [
                {"text": "Even \xb7 1.93x", "callback_data": f"rl_type:even:{amount}:{user_id}"},
                {"text": "Odd \xb7 1.93x", "callback_data": f"rl_type:odd:{amount}:{user_id}"},
            ],
            [
                {"text": "🔴 Red · 1.93x", "callback_data": f"rl_type:red:{amount}:{user_id}", "style": "danger"},
                {"text": "⚫ Black · 1.93x", "callback_data": f"rl_type:black:{amount}:{user_id}", "style": "primary"},
            ],
            [
                {"text": "🟢 Green · 14x", "callback_data": f"rl_type:green:{amount}:{user_id}", "style": "success"},
            ],
        ]
    }


BET_PAYOUTS = {
    "red": 1.93, "black": 1.93, "green": 14.0,
    "even": 1.93, "odd": 1.93,
    "low": 1.93, "high": 1.93,
    "dozen1": 1.93, "dozen2": 1.93, "dozen3": 1.93,
    "number": 35.0,
}

BET_LABELS = {
    "red": "🔴 Red", "black": "⚫ Black", "green": "🟢 Green",
    "even": "Even", "odd": "Odd",
    "low": "1 to 18", "high": "19 to 36",
    "dozen1": "1st 12 (1-12)", "dozen2": "2nd 12 (13-24)", "dozen3": "3rd 12 (25-36)",
}


def check_win(bet_type, bet_value, result_number, result_colour):
    if bet_type == "red":
        return result_colour == "red"
    if bet_type == "black":
        return result_colour == "black"
    if bet_type == "green":
        return result_colour == "green"
    if bet_type == "even":
        return result_number != 0 and result_number % 2 == 0
    if bet_type == "odd":
        return result_number != 0 and result_number % 2 == 1
    if bet_type == "low":
        return 1 <= result_number <= 18
    if bet_type == "high":
        return 19 <= result_number <= 36
    if bet_type == "dozen1":
        return 1 <= result_number <= 12
    if bet_type == "dozen2":
        return 13 <= result_number <= 24
    if bet_type == "dozen3":
        return 25 <= result_number <= 36
    if bet_type == "number":
        return int(bet_value) == result_number
    return False


def roulette_number_grid_keyboard(amount, user_id):
    rows = []
    row = []
    for n in range(37):
        emoji = "🟢" if n == 0 else ("🔴" if get_colour(n) == "red" else "⚫")
        row.append({"text": f"{emoji}{n}", "callback_data": f"rl_num:{n}:{amount}:{user_id}"})
        if len(row) == 6:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    rows.append([{"text": "⬅️ Back", "callback_data": f"rl_back:{amount}:{user_id}"}])
    return {"inline_keyboard": rows}


def confirm_keyboard(bet_type, bet_value, amount, user_id):
    return {
        "inline_keyboard": [
            [{"text": "✅ CONFIRM BET", "callback_data": f"rl_confirm:{bet_type}:{bet_value}:{amount}:{user_id}", "style": "success"}],
            [{"text": "❌ Cancel", "callback_data": f"rl_cancel:{user_id}", "style": "danger"}],
        ]
    }


ROULETTE_WARN_EMOJI = WARN_EMOJI
ROULETTE_HEADER_EMOJI = '<tg-emoji emoji-id="5924675271914426175">🎰</tg-emoji>'


def handle_roulette_command(chat_id, user_id, username, args):
    if not args:
        send_message(chat_id, f"{ROULETTE_WARN_EMOJI} Usage: <code>/roulette &lt;amount&gt;</code>\nExample: <code>/roulette 10</code>")
        return

    amount, _amt_err = resolve_bet_amount(user_id, args[0])
    if _amt_err == "invalid_number":
        send_message(chat_id, f"{ROULETTE_WARN_EMOJI} Invalid amount. Example: <code>/roulette 10</code>")
        return
    if _amt_err == "rate_unavailable":
        send_message(chat_id, f"{ROULETTE_WARN_EMOJI} Currency rate temporarily unavailable - try again shortly, or run /currency to switch to USD.")
        return

    if amount < MIN_BET:
        send_message(chat_id, f"{ROULETTE_WARN_EMOJI} Minimum bet is {fmt_money(user_id, MIN_BET)}")
        return
    if amount > MAX_BET:
        send_message(chat_id, f"{ROULETTE_WARN_EMOJI} Maximum bet is {fmt_money(user_id, MAX_BET)}")
        return

    balance = get_balance(user_id)
    if amount > balance:
        send_message(chat_id, f"{ROULETTE_WARN_EMOJI} Insufficient balance. Your balance: {fmt_money(user_id, balance)}")
        return

    caption = (
        f"{ROULETTE_HEADER_EMOJI} <b>Roulette</b> — 🎡 {mention(user_id, username)}\n\n"
        f"Bet: <b>{fmt_money(user_id, amount)}</b>\n"
        f"Balance: <b>{fmt_money(user_id, balance)}</b>\n\n"
        f"Place your bet:"
    )

    photo_source = ROULETTE_TABLE_FILE_ID if ROULETTE_TABLE_FILE_ID else ROULETTE_TABLE_PATH
    send_photo(
        chat_id, photo_source,
        caption=caption,
        reply_markup=roulette_main_keyboard(amount, user_id)
    )


def handle_callback(callback_query):
    callback_id = callback_query["id"]
    data = callback_query["data"]
    chat_id = callback_query["message"]["chat"]["id"]
    message_id = callback_query["message"]["message_id"]
    clicking_user_id = callback_query["from"]["id"]
    username = callback_query["from"].get("first_name", "Player")

    parts = data.split(":")
    action = parts[0]

    if action == "curr":
        chosen = parts[1] if len(parts) > 1 else "usd"
        if chosen not in SUPPORTED_CURRENCIES:
            answer_callback(callback_id, "Unknown currency.", show_alert=True)
            return
        set_user_currency(clicking_user_id, chosen)
        meta = SUPPORTED_CURRENCIES[chosen]
        answer_callback(callback_id, f"Display currency set to {meta['label']}")
        current = chosen
        buttons = [[{
            "text": m['label'] + (" ✅" if code == current else ""),
            "callback_data": f"curr:{code}",
            "icon_custom_emoji_id": m["icon_id"],
        } for code, m in SUPPORTED_CURRENCIES.items()]]
        edit_message(
            chat_id, message_id,
            f"💱 <b>Display Currency</b>\n\n"
            f"Your balance is always tracked in USD internally - this just changes "
            f"how it's <i>shown</i> to you, converted at the current rate.\n\n"
            f"Current: <b>{meta['label']}</b>",
            reply_markup={"inline_keyboard": buttons}
        )
        return

    if action == "fair":
        token = parts[1] if len(parts) > 1 else ""
        entry = fair_verifications.get(token)
        if not entry:
            answer_callback(callback_id, text="Verification data not found (bot may have restarted).", show_alert=True)
            return
        game, params, server_seed, client_seed, nonce = entry
        combined = f"{server_seed}:{client_seed}:{nonce}"
        result_hash = hashlib.sha256(combined.encode()).hexdigest()
        # Alert popups are capped at ~200 chars by Telegram, so keep this
        # short - the full breakdown with the actual computed result lives
        # in the deep-link version sent via /start (used whenever the bot's
        # username is available, which is the normal case).
        answer_callback(
            callback_id,
            text=f"Server: {server_seed}\nClient: {client_seed}\nNonce: {nonce}\nHash: {result_hash}\nOpen the bot in DM for full verification.",
            show_alert=True
        )
        return

    if action == "mn_noop" or action == "tw_noop" or action == "kn_noop":
        answer_callback(callback_id)
        return

    if action == "mn_bombs":
        bomb_count = int(parts[1])
        amount = float(parts[2])
        owner_id = int(parts[3])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet! Start your own with /mines")
            return

        if owner_id in active_mines_games:
            answer_callback(callback_id, f"{WARN_EMOJI} You already have an active Mines game!")
            return

        balance = get_balance(owner_id)
        if amount > balance:
            answer_callback(callback_id, "Insufficient balance!")
            edit_message(chat_id, message_id, f"{WARN_EMOJI} Insufficient balance. Your balance: {fmt_money(owner_id, balance)}")
            return

        answer_callback(callback_id)

        adjust_balance(owner_id, -amount)

        client_seed = get_client_seed(owner_id)
        nonce = next_nonce(owner_id)
        mine_positions, server_seed = generate_mines_layout(bomb_count, client_seed, nonce)

        with MINES_LOCK:
            active_mines_games[owner_id] = {
                "amount": amount,
                "bomb_count": bomb_count,
                "mine_positions": mine_positions,
                "revealed": set(),
                "server_seed": server_seed,
                "client_seed": client_seed,
                "nonce": nonce,
                "chat_id": chat_id,
                "message_id": message_id,
            }

        edit_message(
            chat_id, message_id,
            f"{MINES_FRESH_BOARD_EMOJI} <b>Mines</b> — {mention(owner_id, username)}\n\n"
            f"Bet: <b>{fmt_money(owner_id, amount)}</b> · Mines: <b>{bomb_count}</b>\n"
            f"Multiplier: <b>1.00x</b>\n\n"
            f"Pick a tile:",
            reply_markup=mines_grid_keyboard(owner_id, set(), bomb_count, 1.00)
        )
        return

    if action == "mn_pick":
        idx = int(parts[1])
        owner_id = int(parts[2])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet! Start your own with /mines")
            return

        game = active_mines_games.get(owner_id)
        if not game:
            answer_callback(callback_id, f"{WARN_EMOJI} No active Mines game. Start one with /mines")
            return

        if idx in game["revealed"]:
            answer_callback(callback_id, "Already revealed!")
            return

        amount = game["amount"]
        bomb_count = game["bomb_count"]
        mine_positions = game["mine_positions"]
        server_seed = game["server_seed"]
        client_seed = game["client_seed"]
        nonce = game["nonce"]

        if idx in mine_positions:
            answer_callback(callback_id, "💥 BOOM!")
            with MINES_LOCK:
                active_mines_games.pop(owner_id, None)

            new_balance = get_balance(owner_id)
            revealed_count = len(game["revealed"])
            edit_message(
                chat_id, message_id,
                f"{MINES_BOOM_LOSS_EMOJI} <b>BOOM! You hit a mine!</b>\n\n"
                f"Bet: <b>{fmt_money(owner_id, amount)}</b> · Mines: <b>{bomb_count}</b>\n"
                f"Safe tiles found: <b>{revealed_count}</b>\n\n"
                f"{cemoji('money')} You lost <b>{fmt_money(owner_id, amount)}</b>\n"
                f"{cemoji('money')} Balance: <b>{fmt_money(owner_id, new_balance)}</b>",
                reply_markup=mines_grid_keyboard(
                    owner_id, game["revealed"], bomb_count, 0,
                    mine_positions=mine_positions, hit_index=idx,
                    game_over=True, server_seed=server_seed,
                    client_seed=client_seed, nonce=nonce
                )
            )
            return

        game["revealed"].add(idx)
        revealed_count = len(game["revealed"])
        multiplier = mines_multiplier(revealed_count, bomb_count)
        safe_tiles_total = MINES_TOTAL_TILES - bomb_count

        answer_callback(callback_id, "💎 Safe!")

        if revealed_count == safe_tiles_total:
            payout = amount * multiplier
            profit = payout - amount
            adjust_balance(owner_id, payout)
            broadcast_win(owner_id, username, "Mines", amount, payout, detail=f"Cleared the board · {bomb_count} mines")
            with MINES_LOCK:
                active_mines_games.pop(owner_id, None)
            new_balance = get_balance(owner_id)
            edit_message(
                chat_id, message_id,
                f"{cemoji('trophy')} <b>Board cleared!</b>\n\n"
                f"Bet: <b>{fmt_money(owner_id, amount)}</b> · Mines: <b>{bomb_count}</b>\n"
                f"Safe tiles found: <b>{revealed_count}</b> (all of them!)\n"
                f"You found every safe tile — cashed out automatically.\n\n"
                f"{PAYOUT_EMOJI} Payout: <b>{fmt_money(owner_id, payout)}</b> ({multiplier:g}x)\n"
                f"{cemoji('fire')} Profit: <b>+{fmt_money(owner_id, profit)}</b>\n"
                f"{cemoji('money')} Balance: <b>{fmt_money(owner_id, new_balance)}</b>",
                reply_markup=mines_grid_keyboard(
                    owner_id, game["revealed"], bomb_count, multiplier,
                    mine_positions=mine_positions, game_over=True, server_seed=server_seed,
                    client_seed=client_seed, nonce=nonce
                )
            )
            return

        edit_message(
            chat_id, message_id,
            f"{MINES_BOMBSELECT_EMOJI} <b>Mines</b> — {mention(owner_id, username)}\n\n"
            f"Bet: <b>{fmt_money(owner_id, amount)}</b> · Mines: <b>{bomb_count}</b>\n"
            f"Multiplier: <b>{multiplier:g}x</b>\n\n"
            f"Pick a tile or cash out:",
            reply_markup=mines_grid_keyboard(owner_id, game["revealed"], bomb_count, multiplier)
        )
        return

    if action == "mn_cashout":
        owner_id = int(parts[1])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet!")
            return

        game = active_mines_games.get(owner_id)
        if not game:
            answer_callback(callback_id, f"{WARN_EMOJI} No active Mines game.")
            return

        if not game["revealed"]:
            answer_callback(callback_id, "Reveal at least one tile first!")
            return

        amount = game["amount"]
        bomb_count = game["bomb_count"]
        mine_positions = game["mine_positions"]
        server_seed = game["server_seed"]
        client_seed = game["client_seed"]
        nonce = game["nonce"]
        revealed_count = len(game["revealed"])
        multiplier = mines_multiplier(revealed_count, bomb_count)
        payout = amount * multiplier
        profit = payout - amount

        adjust_balance(owner_id, payout)
        broadcast_win(owner_id, username, "Mines", amount, payout, detail=f"Cashed out · {bomb_count} mines, {revealed_count} tiles")
        with MINES_LOCK:
            active_mines_games.pop(owner_id, None)

        new_balance = get_balance(owner_id)
        answer_callback(callback_id, f"Cashed out {multiplier:g}x!")

        edit_message(
            chat_id, message_id,
            f"{cemoji('trophy')} <b>Cashed out!</b>\n\n"
            f"Bet: <b>{fmt_money(owner_id, amount)}</b> · Mines: <b>{bomb_count}</b>\n"
            f"Safe tiles found: <b>{revealed_count}</b>\n\n"
            f"{PAYOUT_EMOJI} Payout: <b>{fmt_money(owner_id, payout)}</b> ({multiplier:g}x)\n"
            f"{cemoji('fire')} Profit: <b>+{fmt_money(owner_id, profit)}</b>\n"
            f"{cemoji('money')} Balance: <b>{fmt_money(owner_id, new_balance)}</b>",
            reply_markup=mines_grid_keyboard(
                owner_id, game["revealed"], bomb_count, multiplier,
                mine_positions=mine_positions, game_over=True, server_seed=server_seed,
                client_seed=client_seed, nonce=nonce
            )
        )
        return

    if action == "tw_diff":
        difficulty = parts[1]
        amount = float(parts[2])
        owner_id = int(parts[3])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet! Start your own with /towers")
            return

        if owner_id in active_towers_games:
            answer_callback(callback_id, f"{WARN_EMOJI} You already have an active Towers game!")
            return

        balance = get_balance(owner_id)
        if amount > balance:
            answer_callback(callback_id, "Insufficient balance!")
            edit_message(chat_id, message_id, f"{WARN_EMOJI} Insufficient balance. Your balance: {fmt_money(owner_id, balance)}")
            return

        config = TOWERS_DIFFICULTY[difficulty]
        tiles_per_row = config["tiles"]
        label = config["label"]

        answer_callback(callback_id)

        # Deduct bet immediately
        adjust_balance(owner_id, -amount)

        server_seed = secrets.token_hex(16)
        client_seed = get_client_seed(owner_id)
        nonce = next_nonce(owner_id)

        with TOWERS_LOCK:
            active_towers_games[owner_id] = {
                "amount": amount,
                "difficulty": difficulty,
                "label": label,
                "tiles_per_row": tiles_per_row,
                "current_row": 1,
                "picks": {},
                "server_seed": server_seed,
                "client_seed": client_seed,
                "nonce": nonce,
                "chat_id": chat_id,
                "message_id": message_id,
                "hit_row": None,
                "hit_index": None,
            }

        game = active_towers_games[owner_id]
        edit_message(
            chat_id, message_id,
            f"{TOWERS_HEADER_EMOJI} <b>Towers</b> — {mention(owner_id, username)}\n\n"
            f"Bet: <b>{fmt_money(owner_id, amount)}</b> · Difficulty: <b>{label}</b>\n"
            f"Row: <b>1 / {TOWERS_ROWS}</b> · Multiplier: <b>1.00x</b>\n\n"
            f"Pick a tile:",
            reply_markup=towers_grid_keyboard(owner_id, game)
        )
        return

    if action == "tw_pick":
        tile_idx = int(parts[1])
        owner_id = int(parts[2])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet! Start your own with /towers")
            return

        game = active_towers_games.get(owner_id)
        if not game:
            answer_callback(callback_id, f"{WARN_EMOJI} No active Towers game. Start one with /towers")
            return

        current_row = game["current_row"]
        tiles_per_row = game["tiles_per_row"]
        amount = game["amount"]
        label = game["label"]
        server_seed = game["server_seed"]
        client_seed = game["client_seed"]
        nonce = game["nonce"]
        snake_idx = towers_snake_index(server_seed, client_seed, nonce, current_row, tiles_per_row)

        if tile_idx == snake_idx:
            # Hit the snake - game over, bet already deducted at start
            answer_callback(callback_id, "🐍 Snake!")
            game["hit_row"] = current_row
            game["hit_index"] = tile_idx
            with TOWERS_LOCK:
                active_towers_games.pop(owner_id, None)

            new_balance = get_balance(owner_id)
            rows_cleared = current_row - 1
            edit_message(
                chat_id, message_id,
                f"{TOWERS_SNAKE_LOSS_EMOJI} <b>You hit a snake!</b>\n\n"
                f"Bet: <b>{fmt_money(owner_id, amount)}</b> · Difficulty: <b>{label}</b>\n"
                f"Rows climbed: <b>{rows_cleared} / {TOWERS_ROWS}</b>\n\n"
                f"{TOWERS_LOST_MONEY_EMOJI} You lost <b>{fmt_money(owner_id, amount)}</b>\n"
                f"{cemoji('money')} Balance: <b>{fmt_money(owner_id, new_balance)}</b>",
                reply_markup=towers_grid_keyboard(owner_id, game, game_over=True)
            )
            return

        # Egg - safe pick
        game["picks"][current_row] = tile_idx
        rows_cleared = current_row
        multiplier = towers_multiplier(rows_cleared, tiles_per_row)

        answer_callback(callback_id, "🥚 Safe!")

        if rows_cleared == TOWERS_ROWS:
            # Climbed the whole tower - auto cash out at max multiplier
            payout = amount * multiplier
            profit = payout - amount
            adjust_balance(owner_id, payout)
            broadcast_win(owner_id, username, "Towers", amount, payout, detail=f"Conquered the tower · {label}")
            game["current_row"] = current_row + 1
            with TOWERS_LOCK:
                active_towers_games.pop(owner_id, None)
            new_balance = get_balance(owner_id)
            edit_message(
                chat_id, message_id,
                f"{cemoji('trophy')} <b>Tower conquered!</b>\n\n"
                f"Bet: <b>{fmt_money(owner_id, amount)}</b> · Difficulty: <b>{label}</b>\n"
                f"Rows climbed: <b>{rows_cleared} / {TOWERS_ROWS}</b> (all of them!)\n\n"
                f"{PAYOUT_EMOJI} Payout: <b>{fmt_money(owner_id, payout)}</b> ({multiplier:g}x)\n"
                f"{cemoji('fire')} Profit: <b>+{fmt_money(owner_id, profit)}</b>\n"
                f"{cemoji('money')} Balance: <b>{fmt_money(owner_id, new_balance)}</b>",
                reply_markup=towers_grid_keyboard(owner_id, game, game_over=True)
            )
            return

        game["current_row"] = current_row + 1
        edit_message(
            chat_id, message_id,
            f"{TOWERS_HEADER_EMOJI} <b>Towers</b> — {mention(owner_id, username)}\n\n"
            f"Bet: <b>{fmt_money(owner_id, amount)}</b> · Difficulty: <b>{label}</b>\n"
            f"Row: <b>{game['current_row']} / {TOWERS_ROWS}</b> · Multiplier: <b>{multiplier:g}x</b>\n\n"
            f"Pick a tile or cash out:",
            reply_markup=towers_grid_keyboard(owner_id, game)
        )
        return

    if action == "tw_cashout":
        owner_id = int(parts[1])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet!")
            return

        game = active_towers_games.get(owner_id)
        if not game:
            answer_callback(callback_id, f"{WARN_EMOJI} No active Towers game.")
            return

        rows_cleared = game["current_row"] - 1
        if rows_cleared <= 0:
            answer_callback(callback_id, "Clear at least one row first!")
            return

        amount = game["amount"]
        label = game["label"]
        tiles_per_row = game["tiles_per_row"]
        multiplier = towers_multiplier(rows_cleared, tiles_per_row)
        payout = amount * multiplier
        profit = payout - amount

        adjust_balance(owner_id, payout)
        broadcast_win(owner_id, username, "Towers", amount, payout, detail=f"Cashed out · {label}, row {rows_cleared}")
        with TOWERS_LOCK:
            active_towers_games.pop(owner_id, None)

        new_balance = get_balance(owner_id)
        answer_callback(callback_id, f"Cashed out {multiplier:g}x!")

        edit_message(
            chat_id, message_id,
            f"{cemoji('trophy')} <b>Cashed out!</b>\n\n"
            f"Bet: <b>{fmt_money(owner_id, amount)}</b> · Difficulty: <b>{label}</b>\n"
            f"Rows climbed: <b>{rows_cleared} / {TOWERS_ROWS}</b>\n\n"
            f"{PAYOUT_EMOJI} Payout: <b>{fmt_money(owner_id, payout)}</b> ({multiplier:g}x)\n"
            f"{cemoji('fire')} Profit: <b>+{fmt_money(owner_id, profit)}</b>\n"
            f"{cemoji('money')} Balance: <b>{fmt_money(owner_id, new_balance)}</b>",
            reply_markup=towers_grid_keyboard(owner_id, game, game_over=True)
        )
        return

    if action == "kn_risk":
        risk = parts[1]
        owner_id = int(parts[2])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet! Start your own with /keno")
            return

        game = active_keno_games.get(owner_id)
        if not game:
            answer_callback(callback_id, f"{WARN_EMOJI} No active Keno game. Start one with /keno")
            return

        game["risk"] = risk
        risk_label = KENO_RISK_CONFIG[risk]["label"]
        answer_callback(callback_id)

        edit_message(
            chat_id, message_id,
            f"{KENO_EMOJI} <b>Keno</b> — {mention(owner_id, username)}\n\n"
            f"Bet: <b>{fmt_money(owner_id, game['amount'])}</b> · Risk: <b>{risk_label}</b>\n\n"
            f"Pick 1-10 numbers (1-40), then Confirm:",
            reply_markup=keno_select_keyboard(owner_id, game["selected"])
        )
        return

    if action == "kn_toggle":
        num = int(parts[1])
        owner_id = int(parts[2])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet! Start your own with /keno")
            return

        game = active_keno_games.get(owner_id)
        if not game:
            answer_callback(callback_id, f"{WARN_EMOJI} No active Keno game. Start one with /keno")
            return

        selected = game["selected"]
        if num in selected:
            selected.discard(num)
            answer_callback(callback_id)
        else:
            if len(selected) >= KENO_MAX_PICKS:
                answer_callback(callback_id, f"{WARN_EMOJI} Max {KENO_MAX_PICKS} picks!")
                return
            selected.add(num)
            answer_callback(callback_id)

        risk_label = KENO_RISK_CONFIG[game["risk"]]["label"]
        edit_message(
            chat_id, message_id,
            f"{KENO_EMOJI} <b>Keno</b> — {mention(owner_id, username)}\n\n"
            f"Bet: <b>{fmt_money(owner_id, game['amount'])}</b> · Risk: <b>{risk_label}</b>\n\n"
            f"Pick 1-10 numbers (1-40), then Confirm:",
            reply_markup=keno_select_keyboard(owner_id, selected)
        )
        return

    if action == "kn_clear":
        owner_id = int(parts[1])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet!")
            return

        game = active_keno_games.get(owner_id)
        if not game:
            answer_callback(callback_id, f"{WARN_EMOJI} No active Keno game.")
            return

        game["selected"].clear()
        answer_callback(callback_id, "Cleared")

        risk_label = KENO_RISK_CONFIG[game["risk"]]["label"]
        edit_message(
            chat_id, message_id,
            f"{KENO_EMOJI} <b>Keno</b> — {mention(owner_id, username)}\n\n"
            f"Bet: <b>{fmt_money(owner_id, game['amount'])}</b> · Risk: <b>{risk_label}</b>\n\n"
            f"Pick 1-10 numbers (1-40), then Confirm:",
            reply_markup=keno_select_keyboard(owner_id, game["selected"])
        )
        return

    if action == "kn_confirm":
        owner_id = int(parts[1])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet!")
            return

        game = active_keno_games.get(owner_id)
        if not game:
            answer_callback(callback_id, f"{WARN_EMOJI} No active Keno game.")
            return

        selected = game["selected"]
        if len(selected) < KENO_MIN_PICKS:
            answer_callback(callback_id, "Pick at least 1 number!")
            return

        amount = game["amount"]
        risk = game["risk"]
        picks = len(selected)

        balance = get_balance(owner_id)
        if amount > balance:
            answer_callback(callback_id, "Insufficient balance!")
            edit_message(chat_id, message_id, f"{WARN_EMOJI} Insufficient balance. Your balance: {fmt_money(owner_id, balance)}")
            with KENO_LOCK:
                active_keno_games.pop(owner_id, None)
            return

        answer_callback(callback_id, "🎱 Drawing...")

        # Deduct bet immediately
        adjust_balance(owner_id, -amount)

        server_seed = secrets.token_hex(16)
        client_seed = get_client_seed(owner_id)
        nonce = next_nonce(owner_id)
        drawn_numbers = generate_keno_draw(server_seed, client_seed, nonce)
        hits = len(selected & set(drawn_numbers))
        paytable = keno_paytable(picks, risk)
        multiplier = paytable.get(hits, 0.0)
        payout = amount * multiplier
        profit = payout - amount

        if payout > 0:
            adjust_balance(owner_id, payout)
            if profit > 0:
                broadcast_win(owner_id, username, "Keno", amount, payout, detail=f"{hits}/{picks} hits · {risk.capitalize()} risk")

        with KENO_LOCK:
            active_keno_games.pop(owner_id, None)

        new_balance = get_balance(owner_id)
        risk_label = KENO_RISK_CONFIG[risk]["label"]

        if profit > 0:
            header = f"{cemoji('trophy')} <b>You won!</b>"
        elif payout > 0:
            header = f"{cemoji('money')} <b>Small return</b>"
        else:
            header = f"{KENO_NOLUCK_EMOJI} <b>No luck this time</b>"

        result_text = (
            f"{KENO_EMOJI} <b>Keno</b> — {header}\n"
            f"{mention(owner_id, username)}\n\n"
            f"Bet: <b>{fmt_money(owner_id, amount)}</b> · Risk: <b>{risk_label}</b> · Picks: <b>{picks}</b>\n"
            f"Hits: <b>{hits} / {picks}</b>\n\n"
            f"{cemoji('money')} Payout: <b>{fmt_money(owner_id, payout)}</b> ({multiplier:g}x)\n"
        )
        if profit >= 0:
            result_text += f"{cemoji('fire')} Profit: <b>+{fmt_money(owner_id, profit)}</b>\n"
        else:
            result_text += f"{cemoji('money')} Loss: <b>{fmt_money(owner_id, abs(profit))}</b>\n"
        result_text += f"{cemoji('money')} Balance: <b>{fmt_money(owner_id, new_balance)}</b>"

        edit_message(
            chat_id, message_id, result_text,
            reply_markup=keno_result_keyboard(owner_id, selected, drawn_numbers, server_seed, client_seed, nonce, picks, risk)
        )
        return

    if action == "rl_cancel":
        owner_id = int(parts[1])
        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet!")
            return
        answer_callback(callback_id, "Bet cancelled")
        edit_message_caption(chat_id, message_id, f'<tg-emoji emoji-id="6298671811345254603">❌</tg-emoji> {mention(owner_id, username)} cancelled their bet. No balance was deducted.')
        return

    if action == "rl_type":
        bet_type = parts[1]
        amount = float(parts[2])
        owner_id = int(parts[3])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet! Start your own with /roulette")
            return

        if bet_type == "pick_number":
            answer_callback(callback_id)
            edit_message_caption(
                chat_id, message_id,
                f"{ROULETTE_HEADER_EMOJI} <b>Roulette</b> — 🎡 {mention(owner_id, username)}\n\n"
                f"Bet: <b>{fmt_money(owner_id, amount)}</b>\n\n"
                f"🔢 Pick a number (0-36):",
                reply_markup=roulette_number_grid_keyboard(amount, owner_id)
            )
            return

        payout_mult = BET_PAYOUTS[bet_type]
        label = BET_LABELS[bet_type]
        answer_callback(callback_id)
        edit_message_caption(
            chat_id, message_id,
            f"{ROULETTE_HEADER_EMOJI} <b>Roulette</b> — 🎡 {mention(owner_id, username)}\n\n"
            f"Bet: <b>{label}</b>\n"
            f"Amount: <b>{fmt_money(owner_id, amount)}</b>\n"
            f"Payout if win: <b>{fmt_money(owner_id, amount * payout_mult)}</b> ({payout_mult:g}x)\n\n"
            f"Confirm your bet?",
            reply_markup=confirm_keyboard(bet_type, bet_type, amount, owner_id)
        )
        return

    if action == "rl_num":
        number = parts[1]
        amount = float(parts[2])
        owner_id = int(parts[3])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet! Start your own with /roulette")
            return

        payout_mult = BET_PAYOUTS["number"]
        num_colour_emoji = "🟢" if int(number) == 0 else ("🔴" if get_colour(int(number)) == "red" else "⚫")
        answer_callback(callback_id)
        edit_message_caption(
            chat_id, message_id,
            f"{ROULETTE_HEADER_EMOJI} <b>Roulette</b> — 🎡 {mention(owner_id, username)}\n\n"
            f"Bet: <b>{num_colour_emoji} Number {number}</b>\n"
            f"Amount: <b>{fmt_money(owner_id, amount)}</b>\n"
            f"Payout if win: <b>{fmt_money(owner_id, amount * payout_mult)}</b> ({payout_mult:g}x)\n\n"
            f"Confirm your bet?",
            reply_markup=confirm_keyboard("number", number, amount, owner_id)
        )
        return

    if action == "rl_back":
        amount = float(parts[1])
        owner_id = int(parts[2])
        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet!")
            return
        balance = get_balance(owner_id)
        answer_callback(callback_id)
        edit_message_caption(
            chat_id, message_id,
            f"{ROULETTE_HEADER_EMOJI} <b>Roulette</b> — 🎡 {mention(owner_id, username)}\n\n"
            f"Bet: <b>{fmt_money(owner_id, amount)}</b>\n"
            f"Balance: <b>{fmt_money(owner_id, balance)}</b>\n\n"
            f"Place your bet:",
            reply_markup=roulette_main_keyboard(amount, owner_id)
        )
        return

    if action == "rl_confirm":
        bet_type = parts[1]
        bet_value = parts[2]
        amount = float(parts[3])
        owner_id = int(parts[4])

        if clicking_user_id != owner_id:
            answer_callback(callback_id, "🚫 This isn't your bet! Start your own with /roulette")
            return

        balance = get_balance(owner_id)
        if amount > balance:
            answer_callback(callback_id, "Insufficient balance!")
            edit_message_caption(chat_id, message_id, f"{ROULETTE_WARN_EMOJI} Insufficient balance. Your balance: {fmt_money(owner_id, balance)}")
            return

        answer_callback(callback_id, "🎲 Spinning...")

        adjust_balance(owner_id, -amount)

        client_seed = get_client_seed(owner_id)
        nonce = next_nonce(owner_id)
        result_number, server_seed = generate_roulette_result(client_seed, nonce)
        result_colour = get_colour(result_number)

        edit_message_caption(
            chat_id, message_id,
            f"{ROULETTE_HEADER_EMOJI} <b>Roulette</b> — 🎡 {mention(owner_id, username)}\n\n"
            f"🎡 Spinning the wheel..."
        )

        sticker_id = get_sticker_for_number(result_number)
        send_sticker(chat_id, sticker_id)

        time.sleep(3)

        win = check_win(bet_type, bet_value, result_number, result_colour)
        payout_mult = BET_PAYOUTS[bet_type]
        payout = amount * payout_mult if win else 0.0

        if win:
            adjust_balance(owner_id, payout)

        new_balance = get_balance(owner_id)
        colour_emoji = {"red": "🔴", "black": "⚫", "green": "🟢"}[result_colour]
        bet_display = f"Number {bet_value}" if bet_type == "number" else BET_LABELS.get(bet_type, bet_type)

        if win:
            broadcast_win(owner_id, username, "Roulette", amount, payout, detail=f"{bet_display} · landed on {result_number}")

        roulette_win_emoji = '<tg-emoji emoji-id="5413566144986503832">🏆</tg-emoji>'
        roulette_wins_emoji = '<tg-emoji emoji-id="6300733352697661457">🔥</tg-emoji>'
        roulette_balance_emoji = '<tg-emoji emoji-id="5409048419211682843">💰</tg-emoji>'

        if win:
            result_text = (
                f"{roulette_win_emoji} It landed on <b>{result_number}</b> {colour_emoji} — "
                f"{mention(owner_id, username)} wins {roulette_wins_emoji}\n"
                f"Your {bet_display} bet paid <b>{fmt_money(owner_id, payout)}</b>\n"
                f"{roulette_balance_emoji} Balance: <b>{fmt_money(owner_id, new_balance)}</b>"
            )
        else:
            result_text = (
                f"It landed on <b>{result_number}</b> {colour_emoji} — "
                f"{mention(owner_id, username)}, no luck this time\n"
                f"Your {bet_display} bet lost <b>{fmt_money(owner_id, amount)}</b>\n"
                f"{roulette_balance_emoji} Balance: <b>{fmt_money(owner_id, new_balance)}</b>"
            )

        send_message(chat_id, result_text, reply_markup=fair_button_keyboard("r", server_seed, client_seed, nonce))
        return

    if action == "dep_coin":
        coin = parts[1]
        handle_deposit_callback(callback_id, chat_id, clicking_user_id, username, coin)
        return

    if action == "wd_coin":
        coin = parts[1]
        handle_withdraw_coin_callback(callback_id, chat_id, clicking_user_id, username, coin)
        return

    if action == "bal_action":
        sub_action = parts[1]
        answer_callback(callback_id)
        bal_chat_type = callback_query["message"]["chat"].get("type", "private")
        if sub_action == "deposit":
            handle_deposit_command(chat_id, clicking_user_id, username, [], bal_chat_type)
        elif sub_action == "withdraw":
            handle_withdraw_command(chat_id, clicking_user_id, username, [], bal_chat_type)
        return


LIMBO_HOUSE_EDGE = 0.05
# Tail steepness. At 1.0 this is the classic Limbo/Crash curve where
# P(mult >= m) = (1-edge)/m - e.g. 10x+ hits ~9.5% of rounds. Raising this
# above 1.0 keeps that same formula shape for small multipliers but makes
# big ones disproportionately rarer (10x+ drops to ~5% at 1.3, ~3% at 1.5),
# instead of just scaling every payout down equally like the house edge does.
LIMBO_TAIL_EXP = 1.3
LIMBO_MIN_TARGET = 1.01
LIMBO_MAX_TARGET = 1000000.00


def generate_limbo_result(client_seed, nonce):
    server_seed = secrets.token_hex(16)
    combined = f"{server_seed}:{client_seed}:{nonce}"
    h = hashlib.sha256(combined.encode()).hexdigest()
    r = int(h[:13], 16) / float(1 << 52)
    raw_multiplier = ((1 - LIMBO_HOUSE_EDGE) / (1 - r)) ** (1 / LIMBO_TAIL_EXP)
    result_multiplier = math.floor(raw_multiplier * 100) / 100
    result_multiplier = max(1.00, result_multiplier)
    return result_multiplier, server_seed


def handle_limbo_command(chat_id, user_id, username, args):
    if len(args) < 2:
        send_message(
            chat_id,
            f'{WARN_EMOJI} Usage: <code>/limbo &lt;amount&gt; &lt;target&gt;</code>\n'
            "Example: <code>/limbo 10 5.00</code>"
        )
        return

    try:
        target = float(args[1])
    except ValueError:
        send_message(chat_id, f"{WARN_EMOJI} Invalid amount or target. Example: <code>/limbo 10 5.00</code>")
        return

    amount, _amt_err = resolve_bet_amount(user_id, args[0])
    if _amt_err == "invalid_number":
        send_message(chat_id, f"{WARN_EMOJI} Invalid amount or target. Example: <code>/limbo 10 5.00</code>")
        return
    if _amt_err == "rate_unavailable":
        send_message(chat_id, f"{WARN_EMOJI} Currency rate temporarily unavailable - try again shortly, or run /currency to switch to USD.")
        return

    if amount < MIN_BET:
        send_message(chat_id, f"{WARN_EMOJI} Minimum bet is {fmt_money(user_id, MIN_BET)}")
        return
    if amount > MAX_BET:
        send_message(chat_id, f"{WARN_EMOJI} Maximum bet is {fmt_money(user_id, MAX_BET)}")
        return
    if target < LIMBO_MIN_TARGET:
        send_message(chat_id, f"{WARN_EMOJI} Minimum target is {LIMBO_MIN_TARGET:.2f}x")
        return
    if target > LIMBO_MAX_TARGET:
        send_message(chat_id, f"{WARN_EMOJI} Maximum target is {LIMBO_MAX_TARGET:,.2f}x")
        return

    balance = get_balance(user_id)
    if amount > balance:
        send_message(chat_id, f'{WARN_EMOJI} Insufficient balance. Your balance: {fmt_money(user_id, balance)}')
        return

    adjust_balance(user_id, -amount)

    client_seed = get_client_seed(user_id)
    nonce = next_nonce(user_id)
    result_multiplier, server_seed = generate_limbo_result(client_seed, nonce)
    win = result_multiplier >= target
    potential_payout = amount * target
    payout = potential_payout if win else 0.0

    if win:
        adjust_balance(user_id, payout)
        broadcast_win(user_id, username, "Limbo", amount, payout, detail=f"Target {target:g}x · Rolled {result_multiplier:.2f}x")

    new_balance = get_balance(user_id)

    if win:
        result_text = (
            f'<tg-emoji emoji-id="5244837092042750681">🎯</tg-emoji> <b>Limbo</b> \u2014 {mention(user_id, username)}\n\n'
            f"{fmt_money(user_id, amount)} \u2192 {fmt_money(user_id, potential_payout)} ({target:g}x)\n"
            f'Rolled: <b>{result_multiplier:.2f}x</b> <tg-emoji emoji-id="5206607081334906820">✅</tg-emoji>\n\n'
            f'<tg-emoji emoji-id="6082586710988820084">🏆</tg-emoji> You won <b>{fmt_money(user_id, payout)}</b>!\n'
            f'<tg-emoji emoji-id="5224257782013769471">💰</tg-emoji> Balance: <b>{fmt_money(user_id, new_balance)}</b>'
        )
    else:
        result_text = (
            f'<tg-emoji emoji-id="5244837092042750681">🎯</tg-emoji> <b>Limbo</b> \u2014 {mention(user_id, username)}\n\n'
            f"{fmt_money(user_id, amount)} \u2192 {fmt_money(user_id, potential_payout)} ({target:g}x)\n"
            f'Rolled: <b>{result_multiplier:.2f}x</b> <tg-emoji emoji-id="5210952531676504517">❌</tg-emoji>\n\n'
            f"No luck this time. Lost <b>{fmt_money(user_id, amount)}</b>\n"
            f'<tg-emoji emoji-id="5224257782013769471">💰</tg-emoji> Balance: <b>{fmt_money(user_id, new_balance)}</b>'
        )

    send_message(chat_id, result_text, reply_markup=fair_button_keyboard("l", server_seed, client_seed, nonce))


# ---------------------------------------------------------------------------
# COINFLIP
# ---------------------------------------------------------------------------
# The simplest game in the file: a straight 50/50 heads-or-tails, resolved
# instantly in one command, same provably-fair convention as everything
# else (sha256(server_seed:client_seed:nonce) -> uniform 0-1 value). No
# persistent game state, no lock needed - there's nothing to race.

COINFLIP_PAYOUT = 1.88  # fixed payout on a correct guess

COINFLIP_STICKERS = {
    "heads": "CAACAgUAAxkBAAEFKD9qThaNuTXbRcmG0GpO3P2WkRBwzQACEyMAAlJ5cVarSiKuKFTG5jwE",
    "tails": "CAACAgUAAxkBAAEFKDtqThY2M8f72u9NtLDGOjMi0W9dJgACIx4AAgfHcFZokloxvGbBtDwE",
}


COINFLIP_LOCK = threading.Lock()
user_active_coinflip = set()  # user_ids currently mid-flip (bet placed, sticker/result not sent yet)


def generate_coinflip_result(client_seed, nonce):
    server_seed = secrets.token_hex(16)
    combined = f"{server_seed}:{client_seed}:{nonce}"
    h = hashlib.sha256(combined.encode()).hexdigest()
    r = int(h[:13], 16) / float(1 << 52)
    result = "heads" if r < 0.5 else "tails"
    return result, server_seed


def handle_coinflip_command(chat_id, user_id, username, args):
    if len(args) < 2:
        send_message(
            chat_id,
            f'{WARN_EMOJI} Usage: <code>/coinflip &lt;amount&gt; &lt;heads|tails&gt;</code>\n'
            "Example: <code>/coinflip 10 heads</code>"
        )
        return

    amount, _amt_err = resolve_bet_amount(user_id, args[0])
    if _amt_err == "invalid_number":
        send_message(chat_id, f"{WARN_EMOJI} Invalid amount. Example: <code>/coinflip 10 heads</code>")
        return
    if _amt_err == "rate_unavailable":
        send_message(chat_id, f"{WARN_EMOJI} Currency rate temporarily unavailable - try again shortly, or run /currency to switch to USD.")
        return

    guess = args[1].lower()
    if guess in ("h", "head"):
        guess = "heads"
    elif guess in ("t", "tail"):
        guess = "tails"
    if guess not in ("heads", "tails"):
        send_message(chat_id, f"{WARN_EMOJI} Pick <code>heads</code> or <code>tails</code>. Example: <code>/coinflip 10 heads</code>")
        return

    if amount < MIN_BET:
        send_message(chat_id, f"{WARN_EMOJI} Minimum bet is {fmt_money(user_id, MIN_BET)}")
        return
    if amount > MAX_BET:
        send_message(chat_id, f"{WARN_EMOJI} Maximum bet is {fmt_money(user_id, MAX_BET)}")
        return

    with COINFLIP_LOCK:
        if user_id in user_active_coinflip:
            send_message(chat_id, f"{WARN_EMOJI} Your last flip is still in the air! Wait for the result before flipping again.")
            return
        balance = get_balance(user_id)
        if amount > balance:
            send_message(chat_id, f'{WARN_EMOJI} Insufficient balance. Your balance: {fmt_money(user_id, balance)}')
            return
        # Deducting and marking this user "busy" inside the same lock as the
        # balance check above is the actual fix here - spamming /coinflip
        # several times in under a second used to let every one of those
        # calls read the same starting balance before any of them had
        # deducted anything, so checks that should have failed all passed.
        adjust_balance(user_id, -amount)
        user_active_coinflip.add(user_id)

    try:
        client_seed = get_client_seed(user_id)
        nonce = next_nonce(user_id)
        result, server_seed = generate_coinflip_result(client_seed, nonce)
        win = result == guess
        potential_payout = round(amount * COINFLIP_PAYOUT, 2)
        payout = potential_payout if win else 0.0

        if win:
            adjust_balance(user_id, payout)
            broadcast_win(user_id, username, "Coinflip", amount, payout, detail=f"Called {guess}, landed {result}")

        new_balance = get_balance(user_id)

        send_sticker(chat_id, COINFLIP_STICKERS[result])
        time.sleep(3)  # let the sticker play out before the result lands

        if win:
            result_text = (
                f"{cemoji('chip')} <b>Coinflip</b> — {mention(user_id, username)}\n\n"
                f"You called <b>{guess}</b>, landed <b>{result}</b>\n"
                f"{fmt_money(user_id, amount)} \u2192 {fmt_money(user_id, potential_payout)} ({COINFLIP_PAYOUT:g}x)\n\n"
                f"{cemoji('trophy')} You won <b>{fmt_money(user_id, payout)}</b>!\n"
                f"{cemoji('money')} Balance: <b>{fmt_money(user_id, new_balance)}</b>"
            )
        else:
            result_text = (
                f"{cemoji('chip')} <b>Coinflip</b> — {mention(user_id, username)}\n\n"
                f"You called <b>{guess}</b>, landed <b>{result}</b>\n"
                f"No luck this time. Lost <b>{fmt_money(user_id, amount)}</b>\n"
                f"{cemoji('money')} Balance: <b>{fmt_money(user_id, new_balance)}</b>"
            )

        send_message(chat_id, result_text, reply_markup=fair_button_keyboard("cf", server_seed, client_seed, nonce))
    finally:
        with COINFLIP_LOCK:
            user_active_coinflip.discard(user_id)


MINES_HOUSE_EDGE = 0.01
MINES_TOTAL_TILES = 25
MINES_GRID_SIZE = 5
MINES_BOMB_OPTIONS = [1, 3, 5, 10, 15, 24]


def mines_multiplier(revealed_count, bomb_count, house_edge=MINES_HOUSE_EDGE, total=MINES_TOTAL_TILES):
    if revealed_count <= 0:
        return 1.0
    prob = 1.0
    for i in range(revealed_count):
        prob *= (total - bomb_count - i) / (total - i)
    if prob <= 0:
        return 0.0
    return math.floor(((1 - house_edge) / prob) * 100) / 100


def generate_mines_layout(bomb_count, client_seed, nonce):
    server_seed = secrets.token_hex(16)
    combined = f"{server_seed}:{client_seed}:{nonce}"
    h = hashlib.sha256(combined.encode()).hexdigest()
    rng = random.Random(h)
    positions = list(range(MINES_TOTAL_TILES))
    rng.shuffle(positions)
    mine_positions = set(positions[:bomb_count])
    return mine_positions, server_seed


def mines_bomb_count_keyboard(amount, user_id):
    rows = []
    row = []
    for count in MINES_BOMB_OPTIONS:
        row.append({"text": f"{count}", "callback_data": f"mn_bombs:{count}:{amount}:{user_id}", "style": "primary", "icon_custom_emoji_id": "5249496324105062810"})
        if len(row) == 3:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    return {"inline_keyboard": rows}


def mines_grid_keyboard(user_id, revealed, bomb_count, current_multiplier,
                         mine_positions=None, hit_index=None, game_over=False,
                         server_seed=None, client_seed=None, nonce=None):
    rows = []
    for r in range(MINES_GRID_SIZE):
        row = []
        for c in range(MINES_GRID_SIZE):
            idx = r * MINES_GRID_SIZE + c
            if game_over:
                if mine_positions is not None and idx in mine_positions:
                    if idx == hit_index:
                        row.append({"text": " ", "callback_data": "mn_noop", "style": "danger", "icon_custom_emoji_id": "5197371802136892976"})
                    else:
                        row.append({"text": " ", "callback_data": "mn_noop", "style": "danger", "icon_custom_emoji_id": "5197371802136892976"})
                elif idx in revealed:
                    row.append({"text": " ", "callback_data": "mn_noop", "style": "success", "icon_custom_emoji_id": "5427168083074628963"})
                else:
                    row.append({"text": " ", "callback_data": "mn_noop", "icon_custom_emoji_id": "5803420768826038185"})
            else:
                if idx in revealed:
                    row.append({"text": " ", "callback_data": "mn_noop", "style": "success", "icon_custom_emoji_id": "5427168083074628963"})
                else:
                    row.append({"text": " ", "callback_data": f"mn_pick:{idx}:{user_id}", "icon_custom_emoji_id": "5803420768826038185"})
        rows.append(row)

    if not game_over and revealed:
        rows.append([{
            "text": f"Cashout ({current_multiplier:g}x)",
            "callback_data": f"mn_cashout:{user_id}",
            "style": "success",
            "icon_custom_emoji_id": "5346123450358444391"
        }])

    if game_over and server_seed:
        rows.append(fair_button_keyboard("m", server_seed, client_seed, nonce, str(bomb_count))["inline_keyboard"][0])

    return {"inline_keyboard": rows}


def handle_mines_command(chat_id, user_id, username, args):
    if not args:
        send_message(chat_id, f"{WARN_EMOJI} Usage: <code>/mines &lt;amount&gt;</code>\nExample: <code>/mines 10</code>")
        return

    amount, _amt_err = resolve_bet_amount(user_id, args[0])
    if _amt_err == "invalid_number":
        send_message(chat_id, f"{WARN_EMOJI} Invalid amount. Example: <code>/mines 10</code>")
        return
    if _amt_err == "rate_unavailable":
        send_message(chat_id, f"{WARN_EMOJI} Currency rate temporarily unavailable - try again shortly, or run /currency to switch to USD.")
        return

    if amount < MIN_BET:
        send_message(chat_id, f"{WARN_EMOJI} Minimum bet is {fmt_money(user_id, MIN_BET)}")
        return
    if amount > MAX_BET:
        send_message(chat_id, f"{WARN_EMOJI} Maximum bet is {fmt_money(user_id, MAX_BET)}")
        return

    balance = get_balance(user_id)
    if amount > balance:
        send_message(chat_id, f"{WARN_EMOJI} Insufficient balance. Your balance: {fmt_money(user_id, balance)}")
        return

    if user_id in active_mines_games:
        send_message(chat_id, f"{WARN_EMOJI} You already have an active Mines game! Pick a tile or cash out first.")
        return

    send_message(
        chat_id,
        f"{MINES_BOMBSELECT_EMOJI} <b>Mines</b> — {mention(user_id, username)}\n\n"
        f"Bet: <b>{fmt_money(user_id, amount)}</b>\n\n"
        f"How many mines do you want on the board?",
        reply_markup=mines_bomb_count_keyboard(amount, user_id)
    )


# ---------------------------------------------------------------------------
# TOWERS GAME LOGIC
# ---------------------------------------------------------------------------
# Classic "Towers": a vertical stack of rows. Each row has N tiles, exactly
# ONE of which is a snake (the rest are eggs). Player climbs row by row,
# picking one tile per row. Egg -> advance + multiplier goes up. Snake ->
# game over, bet lost. Cashout locks in the current multiplier any time
# after clearing the first row. Difficulty only changes tiles-per-row
# (fewer tiles = higher risk per row = higher multiplier growth).

TOWERS_HOUSE_EDGE = 0.01   # same 1% house edge convention as Mines/Limbo
TOWERS_ROWS = 9            # number of rows to climb, same for every difficulty

TOWERS_DIFFICULTY = {
    "normal": {"tiles": 3, "label": "Normal"},
    "hard":   {"tiles": 2, "label": "Hard"},
}


def towers_multiplier(rows_cleared, tiles_per_row, house_edge=TOWERS_HOUSE_EDGE):
    """
    Fair multiplier for having safely climbed `rows_cleared` rows, where each
    row has exactly 1 snake among `tiles_per_row` tiles (so egg-chance per
    row is (tiles_per_row - 1) / tiles_per_row).
    """
    if rows_cleared <= 0:
        return 1.0
    prob_per_row = (tiles_per_row - 1) / tiles_per_row
    total_prob = prob_per_row ** rows_cleared
    if total_prob <= 0:
        return 0.0
    return math.floor(((1 - house_edge) / total_prob) * 100) / 100


def towers_snake_index(server_seed, client_seed, nonce, row, tiles_per_row):
    """
    Provably-fair-style: deterministic snake position for a given row, derived
    from the server seed + client seed + nonce + row number. Same seed/hash
    convention used elsewhere in this file (roulette/limbo/mines/crash).
    """
    h = hashlib.sha256(f"{server_seed}:{client_seed}:{nonce}:{row}".encode()).hexdigest()
    return int(h[:8], 16) % tiles_per_row


def towers_difficulty_keyboard(amount, user_id):
    return {
        "inline_keyboard": [
            [
                {"text": "🟡 Normal", "callback_data": f"tw_diff:normal:{amount}:{user_id}", "style": "primary"},
                {"text": "🔴 Hard", "callback_data": f"tw_diff:hard:{amount}:{user_id}", "style": "danger"},
            ]
        ]
    }


def towers_grid_keyboard(user_id, game, game_over=False):
    """
    Renders the tower with the topmost (highest reward) row at the top of the
    message and row 1 at the bottom, just above the cashout button - so it
    visually reads like climbing upward.
    """
    tiles_per_row = game["tiles_per_row"]
    current_row = game["current_row"]
    picks = game["picks"]
    server_seed = game["server_seed"]
    client_seed = game["client_seed"]
    nonce = game["nonce"]
    hit_row = game.get("hit_row")
    hit_index = game.get("hit_index")

    rows = []
    for r in range(TOWERS_ROWS, 0, -1):
        row_buttons = []
        if r in picks:
            # Already cleared row - show the picked tile as an egg
            picked = picks.get(r)
            for t in range(tiles_per_row):
                if t == picked:
                    row_buttons.append({"text": " ", "callback_data": "tw_noop", "style": "success", "icon_custom_emoji_id": "5199607933909888987"})
                else:
                    row_buttons.append({"text": "▪️", "callback_data": "tw_noop"})
        elif game_over and r >= current_row:
            # Game ended on or above this row - reveal the snake, rest are eggs
            snake_idx = towers_snake_index(server_seed, client_seed, nonce, r, tiles_per_row)
            for t in range(tiles_per_row):
                if r == hit_row and t == hit_index:
                    row_buttons.append({"text": " ", "callback_data": "tw_noop", "style": "danger", "icon_custom_emoji_id": "5384389684820471923"})
                elif t == snake_idx:
                    row_buttons.append({"text": " ", "callback_data": "tw_noop", "style": "danger", "icon_custom_emoji_id": "5384389684820471923"})
                else:
                    row_buttons.append({"text": " ", "callback_data": "tw_noop", "style": "success", "icon_custom_emoji_id": "5199607933909888987"})
        elif r == current_row and not game_over:
            for t in range(tiles_per_row):
                row_buttons.append({"text": "❔", "callback_data": f"tw_pick:{t}:{user_id}"})
        else:
            for t in range(tiles_per_row):
                row_buttons.append({"text": "❔", "callback_data": "tw_noop"})
        rows.append(row_buttons)

    if not game_over and current_row > 1:
        rows.append([{
            "text": f"Cashout ({towers_multiplier(current_row - 1, tiles_per_row):g}x)",
            "callback_data": f"tw_cashout:{user_id}",
            "style": "primary",
            "icon_custom_emoji_id": "5809816842713174497"
        }])

    if game_over and server_seed:
        rows.append(fair_button_keyboard("t", server_seed, client_seed, nonce, game["difficulty"])["inline_keyboard"][0])

    return {"inline_keyboard": rows}


def handle_towers_command(chat_id, user_id, username, args):
    if not args:
        send_message(chat_id, f"{WARN_EMOJI} Usage: <code>/towers &lt;amount&gt;</code>\nExample: <code>/towers 10</code>")
        return

    amount, _amt_err = resolve_bet_amount(user_id, args[0])
    if _amt_err == "invalid_number":
        send_message(chat_id, f"{WARN_EMOJI} Invalid amount. Example: <code>/towers 10</code>")
        return
    if _amt_err == "rate_unavailable":
        send_message(chat_id, f"{WARN_EMOJI} Currency rate temporarily unavailable - try again shortly, or run /currency to switch to USD.")
        return

    if amount < MIN_BET:
        send_message(chat_id, f"{WARN_EMOJI} Minimum bet is {fmt_money(user_id, MIN_BET)}")
        return
    if amount > MAX_BET:
        send_message(chat_id, f"{WARN_EMOJI} Maximum bet is {fmt_money(user_id, MAX_BET)}")
        return

    balance = get_balance(user_id)
    if amount > balance:
        send_message(chat_id, f"{WARN_EMOJI} Insufficient balance. Your balance: {fmt_money(user_id, balance)}")
        return

    if user_id in active_towers_games:
        send_message(chat_id, f"{WARN_EMOJI} You already have an active Towers game! Pick a tile or cash out first.")
        return

    send_message(
        chat_id,
        f"{TOWERS_HEADER_EMOJI} <b>Towers</b> — {mention(user_id, username)}\n\n"
        f"Bet: <b>{fmt_money(user_id, amount)}</b>\n\n"
        f"Pick a difficulty:",
        reply_markup=towers_difficulty_keyboard(amount, user_id)
    )


# ---------------------------------------------------------------------------
# KENO GAME LOGIC
# ---------------------------------------------------------------------------
# Player picks 1-10 numbers out of a 40-number board, then 10 numbers are
# drawn. Payout depends on how many of the player's picks were drawn, scaled
# by risk level (Low/Medium/High). Multipliers are derived from the exact
# hypergeometric probability of each hit-count, then normalized so every
# picks-count/risk combination has the same house edge (same technique as
# the fair-multiplier math used for Mines/Towers above).

KENO_HOUSE_EDGE = 0.01
KENO_BOARD_SIZE = 40
KENO_DRAWN_COUNT = 10
KENO_MIN_PICKS = 1
KENO_MAX_PICKS = 10

KENO_RISK_CONFIG = {
    "low":    {"label": "Low",    "threshold_frac": 0.2, "exponent": 1.3},
    "medium": {"label": "Medium", "threshold_frac": 0.4, "exponent": 1.8},
    "high":   {"label": "High",   "threshold_frac": 0.6, "exponent": 2.6},
}


def keno_hit_probability(picks, hits, board=KENO_BOARD_SIZE, drawn=KENO_DRAWN_COUNT):
    """Exact hypergeometric probability of matching exactly `hits` out of
    `picks` chosen numbers, given `drawn` numbers are drawn from `board`."""
    if hits < 0 or hits > picks or hits > drawn or (picks - hits) > (board - drawn):
        return 0.0
    return (
        math.comb(picks, hits) * math.comb(board - picks, drawn - hits)
        / math.comb(board, drawn)
    )


def keno_paytable(picks, risk, house_edge=KENO_HOUSE_EDGE):
    """
    Builds a hits -> multiplier table for a given picks count and risk
    level. A raw reward curve is shaped by the risk config (higher risk =
    only high hit-counts pay, but pay much more), then the whole table is
    scaled so the expected payout across all outcomes equals
    (1 - house_edge) * bet - keeping the house edge identical no matter
    what the player picks or which risk level they choose.
    """
    config = KENO_RISK_CONFIG[risk]
    threshold = max(1, math.ceil(picks * config["threshold_frac"]))
    exponent = config["exponent"]

    raw = {}
    for h in range(picks + 1):
        raw[h] = 0.0 if h < threshold else float((h - threshold + 1) ** exponent)

    ev_raw = sum(keno_hit_probability(picks, h) * raw[h] for h in range(picks + 1))
    if ev_raw <= 0:
        return {h: 0.0 for h in range(picks + 1)}

    scale = (1 - house_edge) / ev_raw
    table = {}
    for h in range(picks + 1):
        table[h] = math.floor(raw[h] * scale * 100) / 100 if raw[h] > 0 else 0.0
    return table


def generate_keno_draw(server_seed, client_seed, nonce):
    """Provably-fair-style: hash seeds a shuffle of numbers 1-40, first 10
    shuffled numbers are the drawn numbers. Same shuffle convention as the
    Mines mine-layout generation elsewhere in this file."""
    combined = f"{server_seed}:{client_seed}:{nonce}"
    h = hashlib.sha256(combined.encode()).hexdigest()
    rng = random.Random(h)
    numbers = list(range(1, KENO_BOARD_SIZE + 1))
    rng.shuffle(numbers)
    return sorted(numbers[:KENO_DRAWN_COUNT])


def keno_select_keyboard(user_id, selected):
    rows = []
    row = []
    for n in range(1, KENO_BOARD_SIZE + 1):
        if n in selected:
            row.append({"text": f"{n}", "callback_data": f"kn_toggle:{n}:{user_id}", "style": "primary", "icon_custom_emoji_id": "5258073279305889554"})
        else:
            row.append({"text": str(n), "callback_data": f"kn_toggle:{n}:{user_id}"})
        if len(row) == 8:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    rows.append([
        {"text": "🗑 Clear", "callback_data": f"kn_clear:{user_id}", "style": "danger"},
        {"text": f"✅ Confirm ({len(selected)})", "callback_data": f"kn_confirm:{user_id}", "style": "success"},
    ])
    return {"inline_keyboard": rows}


def keno_risk_keyboard(user_id):
    return {
        "inline_keyboard": [[
            {"text": "🟢 Low", "callback_data": f"kn_risk:low:{user_id}", "style": "success"},
            {"text": "🟡 Medium", "callback_data": f"kn_risk:medium:{user_id}"},
            {"text": "🔴 High", "callback_data": f"kn_risk:high:{user_id}", "style": "danger"},
        ]]
    }


def keno_result_keyboard(user_id, selected, drawn_numbers, server_seed, client_seed, nonce, picks, risk):
    drawn_set = set(drawn_numbers)
    rows = []
    row = []
    for n in range(1, KENO_BOARD_SIZE + 1):
        picked = n in selected
        was_drawn = n in drawn_set
        if picked and was_drawn:
            row.append({"text": f"{n}", "callback_data": "kn_noop", "style": "success", "icon_custom_emoji_id": "5199607933909888987"})
        elif picked and not was_drawn:
            row.append({"text": f"{n}", "callback_data": "kn_noop", "style": "danger", "icon_custom_emoji_id": "5215572533507529497"})
        elif was_drawn and not picked:
            row.append({"text": f"⭐{n}", "callback_data": "kn_noop", "style": "primary"})
        else:
            row.append({"text": str(n), "callback_data": "kn_noop"})
        if len(row) == 8:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    rows.append(fair_button_keyboard("k", server_seed, client_seed, nonce, f"{picks}-{risk}")["inline_keyboard"][0])
    return {"inline_keyboard": rows}


def handle_keno_command(chat_id, user_id, username, args):
    if not args:
        send_message(chat_id, f"{WARN_EMOJI} Usage: <code>/keno &lt;amount&gt;</code>\nExample: <code>/keno 10</code>")
        return

    amount, _amt_err = resolve_bet_amount(user_id, args[0])
    if _amt_err == "invalid_number":
        send_message(chat_id, f"{WARN_EMOJI} Invalid amount. Example: <code>/keno 10</code>")
        return
    if _amt_err == "rate_unavailable":
        send_message(chat_id, f"{WARN_EMOJI} Currency rate temporarily unavailable - try again shortly, or run /currency to switch to USD.")
        return

    if amount < MIN_BET:
        send_message(chat_id, f"{WARN_EMOJI} Minimum bet is {fmt_money(user_id, MIN_BET)}")
        return
    if amount > MAX_BET:
        send_message(chat_id, f"{WARN_EMOJI} Maximum bet is {fmt_money(user_id, MAX_BET)}")
        return

    balance = get_balance(user_id)
    if amount > balance:
        send_message(chat_id, f"{WARN_EMOJI} Insufficient balance. Your balance: {fmt_money(user_id, balance)}")
        return

    if user_id in active_keno_games:
        send_message(chat_id, f"{WARN_EMOJI} You already have an active Keno game! Finish picking numbers first.")
        return

    with KENO_LOCK:
        active_keno_games[user_id] = {"amount": amount, "selected": set(), "risk": None}

    send_message(
        chat_id,
        f"{KENO_EMOJI} <b>Keno</b> — {mention(user_id, username)}\n\n"
        f"Bet: <b>{fmt_money(user_id, amount)}</b>\n\n"
        f"Choose a risk level:",
        reply_markup=keno_risk_keyboard(user_id)
    )


CRASH_HOUSE_EDGE = 0.01
# Multiplier doubles roughly every CRASH_DOUBLE_SECONDS - tune this to make
# the rocket climb faster/slower.
CRASH_DOUBLE_SECONDS = 5.0
CRASH_GROWTH_RATE = math.log(2) / CRASH_DOUBLE_SECONDS


def crash_multiplier_at(elapsed_seconds):
    if elapsed_seconds <= 0:
        return 1.00
    m = math.exp(CRASH_GROWTH_RATE * elapsed_seconds)
    return math.floor(m * 100) / 100


def crash_time_for_point(crash_point):
    if crash_point <= 1.00:
        return 0.0
    return math.log(crash_point) / CRASH_GROWTH_RATE


def generate_crash_point(client_seed, nonce):
    server_seed = secrets.token_hex(16)
    combined = f"{server_seed}:{client_seed}:{nonce}"
    h = hashlib.sha256(combined.encode()).hexdigest()
    r = int(h[:13], 16) / float(1 << 52)
    raw_multiplier = (1 - CRASH_HOUSE_EDGE) / (1 - r)
    result = math.floor(raw_multiplier * 100) / 100
    return max(1.00, result), server_seed


def crash_finalize(token):
    """Flips an expired round from 'active' to 'crashed' exactly once and
    sends the loss message. Safe to call from the poll/cashout endpoints
    and from the background watchdog thread - the lock guarantees only the
    caller that actually performs the flip sends the notification."""
    should_notify = False
    game = None
    with CRASH_LOCK:
        game = active_crash_games.get(token)
        if not game or game["status"] != "active":
            return
        elapsed = time.time() - game["start_time"]
        if elapsed < crash_time_for_point(game["crash_point"]):
            return
        game["status"] = "crashed"
        should_notify = True
        with BALANCE_LOCK:
            pass  # balance already debited at bet time, nothing to do here
        user_active_crash.pop(game["user_id"], None)

    if should_notify:
        send_message(
            game["chat_id"],
            f"{CRASH_BOOM_EMOJI} <b>Crash</b> — {mention(game['user_id'], game['username'])}\n\n"
            f"The rocket blew up at <b>{game['crash_point']:.2f}x</b>!\n"
            f"You didn't cash out in time. Lost <b>{fmt_money(game['user_id'], game['amount'])}</b>\n"
            f"{cemoji('money')} Balance: <b>{fmt_money(game['user_id'], get_balance(game['user_id']))}</b>",
            reply_markup=fair_button_keyboard("c", game["server_seed"], game["client_seed"], game["nonce"])
        )


def crash_watchdog(token, delay_seconds):
    time.sleep(max(delay_seconds, 0) + 0.15)
    crash_finalize(token)


CRASH_PENDING_TIMEOUT = 300  # seconds a launch pad stays open before it expires unused


def crash_pending_expiry(token):
    time.sleep(CRASH_PENDING_TIMEOUT)
    with CRASH_LOCK:
        game = active_crash_games.get(token)
        if not game or game["status"] != "pending":
            return
        active_crash_games.pop(token, None)
        user_active_crash.pop(game["user_id"], None)
        chat_id, user_id, username = game["chat_id"], game["user_id"], game["username"]

    send_message(
        chat_id,
        f"{CRASH_EXPIRED_EMOJI} {mention(user_id, username)}, your Crash launch pad expired unused. "
        f"Nothing was charged - start a new one with /crash."
    )


def crash_start(token):
    """Called by the web page's Start button. This is the moment the bet is
    actually placed - balance is checked and deducted here, not when /crash
    was typed, and the timer only begins now."""
    with CRASH_LOCK:
        game = active_crash_games.get(token)
        if not game:
            return {"ok": False, "error": "not_found"}
        if game["status"] != "pending":
            return {"ok": False, "error": "already_started"}

        balance = get_balance(game["user_id"])
        if game["amount"] > balance:
            return {"ok": False, "error": "insufficient_balance", "balance": balance}

        adjust_balance(game["user_id"], -game["amount"])
        game["start_time"] = time.time()
        game["status"] = "active"
        crash_point = game["crash_point"]
        start_time = game["start_time"]

    threading.Thread(
        target=crash_watchdog,
        args=(token, crash_time_for_point(crash_point)),
        daemon=True
    ).start()
    return {"ok": True, "start_ms": int(start_time * 1000)}


def crash_get_state(token):
    """Returns a JSON-able dict describing the live state of a round. Used
    by the Mini App's poll loop."""
    crash_finalize(token)
    with CRASH_LOCK:
        game = active_crash_games.get(token)
        if not game:
            return None
        if game["status"] == "pending":
            return {"status": "pending", "amount": game["amount"]}
        if game["status"] == "active":
            elapsed = time.time() - game["start_time"]
            current = min(crash_multiplier_at(elapsed), game["crash_point"])
            return {"status": "active", "multiplier": current, "amount": game["amount"]}
        if game["status"] == "crashed":
            return {"status": "crashed", "crash_point": game["crash_point"], "amount": game["amount"]}
        if game["status"] == "cashed_out":
            return {
                "status": "cashed_out",
                "multiplier": game["cashout_multiplier"],
                "payout": round(game["amount"] * game["cashout_multiplier"], 2),
                "amount": game["amount"],
            }
    return None


def crash_attempt_cashout(token):
    """Attempts to cash a round out at whatever multiplier the server clock
    says it's currently at. Server time is the only source of truth - the
    client's animation is just a visual approximation of this."""
    crash_finalize(token)
    with CRASH_LOCK:
        game = active_crash_games.get(token)
        if not game:
            return {"ok": False, "error": "not_found"}
        if game["status"] != "active":
            if game["status"] == "crashed":
                return {"ok": False, "error": "crashed", "crash_point": game["crash_point"]}
            if game["status"] == "pending":
                return {"ok": False, "error": "not_started"}
            return {"ok": False, "error": "already_ended"}

        elapsed = time.time() - game["start_time"]
        current = min(crash_multiplier_at(elapsed), game["crash_point"])
        payout = round(game["amount"] * current, 2)
        game["status"] = "cashed_out"
        game["cashout_multiplier"] = current
        user_active_crash.pop(game["user_id"], None)
        user_id, chat_id, username, amount = game["user_id"], game["chat_id"], game["username"], game["amount"]

    adjust_balance(user_id, payout)
    broadcast_win(user_id, username, "Crash", amount, payout, detail=f"Cashed out at {current:.2f}x")
    send_message(
        chat_id,
        f"{CRASH_ROCKET_EMOJI} <b>Crash</b> — {mention(user_id, username)}\n\n"
        f"Cashed out at <b>{current:.2f}x</b>!\n"
        f"{fmt_money(user_id, amount)} \u2192 {fmt_money(user_id, payout)}\n\n"
        f"{cemoji('trophy')} You won <b>{fmt_money(user_id, payout - amount)}</b>!\n"
        f"{cemoji('money')} Balance: <b>{fmt_money(user_id, get_balance(user_id))}</b>",
        reply_markup=fair_button_keyboard("c", game["server_seed"], game["client_seed"], game["nonce"])
    )
    return {"ok": True, "multiplier": current, "payout": payout}


def crash_mini_app_keyboard(token):
    url = f"{APP_URL}/crash/{token}"
    return {"inline_keyboard": [[{"text": "Launch Rocket", "icon_custom_emoji_id": "6017043379748082509", "web_app": {"url": url}}]]}


# ---------------------------------------------------------------------------
# CRASH GROUP INVITES
# ---------------------------------------------------------------------------
# Telegram only allows web_app buttons in private chats, so /crash in a
# group hands out a plain URL button that deep-links into a DM instead.
# A URL button can't be restricted to one clicker the way a callback_data
# button can (Telegram lets anyone in the chat tap it) - so the invite
# itself has to carry that restriction: it's tied to the user who ran the
# command, and it can only ever be consumed once, by them.

active_crash_invites = {}       # invite_token -> {owner_id, owner_name, amount, used}
CRASH_INVITE_LOCK = threading.Lock()
CRASH_INVITE_TIMEOUT = 300      # seconds an unused invite link stays valid


def crash_invite_expiry(invite_token):
    time.sleep(CRASH_INVITE_TIMEOUT)
    with CRASH_INVITE_LOCK:
        active_crash_invites.pop(invite_token, None)


def handle_crash_command(chat_id, user_id, username, args, chat_type="private"):
    if not args:
        send_message(chat_id, f"{WARN_EMOJI} Usage: <code>/crash &lt;amount&gt;</code>\nExample: <code>/crash 10</code>")
        return

    amount, _amt_err = resolve_bet_amount(user_id, args[0])
    if _amt_err == "invalid_number":
        send_message(chat_id, f"{WARN_EMOJI} Invalid amount. Example: <code>/crash 10</code>")
        return
    if _amt_err == "rate_unavailable":
        send_message(chat_id, f"{WARN_EMOJI} Currency rate temporarily unavailable - try again shortly, or run /currency to switch to USD.")
        return

    if amount < MIN_BET:
        send_message(chat_id, f"{WARN_EMOJI} Minimum bet is ${MIN_BET:.2f}")
        return
    if amount > MAX_BET:
        send_message(chat_id, f"{WARN_EMOJI} Maximum bet is ${MAX_BET:.2f}")
        return

    balance = get_balance(user_id)
    if amount > balance:
        send_message(chat_id, f"{WARN_EMOJI} Insufficient balance. Your balance: ${balance:.2f}")
        return

    if not APP_URL:
        send_message(
            chat_id,
            f"{WARN_EMOJI} Crash's Mini App isn't configured yet. The bot owner needs to "
            "set the <code>APP_URL</code> environment variable to this "
            "service's public HTTPS URL (e.g. your Railway domain)."
        )
        return

    if user_id in user_active_crash:
        send_message(chat_id, f"{WARN_EMOJI} You already have an active Crash round! Finish it in the app first.")
        return

    if chat_type != "private":
        # Telegram only allows web_app buttons in private chats, so groups
        # get a deep-link that opens a DM with the bot. The link is single-
        # use and locked to whoever typed the command - see the crash_ (cri_)
        # handling in handle_message()'s /start branch.
        if not BOT_USERNAME:
            send_message(chat_id, f"{WARN_EMOJI} Bot isn't fully started yet - try again in a few seconds.")
            return

        invite_token = secrets.token_urlsafe(8)
        with CRASH_INVITE_LOCK:
            active_crash_invites[invite_token] = {
                "owner_id": user_id,
                "owner_name": username,
                "amount": amount,
                "used": False,
            }
        threading.Thread(
            target=crash_invite_expiry,
            args=(invite_token,),
            daemon=True
        ).start()

        deep_link = f"https://t.me/{BOT_USERNAME}?start=cri_{invite_token}"
        send_message(
            chat_id,
            f"{CRASH_ROCKET_EMOJI} <b>Crash</b> — {mention(user_id, username)}\n\n"
            f"Bet: <b>${amount:.2f}</b>\n\n"
            f"Crash only runs in DM (Telegram doesn't allow the Mini App in groups). "
            f"This button is one-time use, only for {mention(user_id, username)}:",
            reply_markup={"inline_keyboard": [[{"text": "Play Crash in DM", "icon_custom_emoji_id": "6017043379748082509", "url": deep_link}]]}
        )
        return

    with CRASH_LOCK:
        if user_id in user_active_crash:
            send_message(chat_id, f"{WARN_EMOJI} You already have an active Crash round! Finish it in the app first.")
            return

        # NOTE: balance is intentionally NOT touched here. crash_start()
        # (fired by the mini app's Start button) is the single place that
        # checks and deducts the bet - see its docstring. Deducting here too
        # double-charged the player: if they bet their whole balance, this
        # line took it immediately, and crash_start's own balance check then
        # failed because the balance was already gone, rejecting the round
        # as "insufficient balance" with the bet never refunded.
        client_seed = get_client_seed(user_id)
        nonce = next_nonce(user_id)
        crash_point, server_seed = generate_crash_point(client_seed, nonce)
        token = secrets.token_urlsafe(12)

        active_crash_games[token] = {
            "token": token,
            "user_id": user_id,
            "chat_id": chat_id,
            "username": username,
            "amount": amount,
            "crash_point": crash_point,
            "server_seed": server_seed,
            "client_seed": client_seed,
            "nonce": nonce,
            "start_time": None,
            "status": "pending",   # becomes "active" only once /start is hit on the web page
            "cashout_multiplier": None,
        }
        user_active_crash[user_id] = token

    threading.Thread(
        target=crash_pending_expiry,
        args=(token,),
        daemon=True
    ).start()

    send_message(
        chat_id,
        f"{CRASH_ROCKET_EMOJI} <b>Crash</b> — {mention(user_id, username)}\n\n"
        f"Bet: <b>${amount:.2f}</b>\n"
        f"Balance: <b>${get_balance(user_id):.2f}</b>\n\n"
        f"Open the launch pad below, then press <b>Start</b> when you're ready "
        f"(that's when your bet is placed and the rocket takes off):",
        reply_markup=crash_mini_app_keyboard(token)
    )


# ---------------------------------------------------------------------------
# BLACKJACK
# ---------------------------------------------------------------------------
# Same architecture as Crash: this module only holds game state + rules.
# blackjack_web.py is the thin HTTP wrapper the Mini App page talks to.
# One round can have up to two hands (after a single split) - everything
# below is written in terms of a list of hands so the split case falls out
# naturally instead of being a bolt-on special case.

BLACKJACK_DECKS = 6
RANKS = ['2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K', 'A']
SUITS = ['S', 'H', 'D', 'C']

active_blackjack_games = {}   # token -> game dict
user_active_blackjack = {}    # user_id -> token (one live blackjack round per user)
BLACKJACK_LOCK = threading.Lock()


def bj_card_value(rank):
    if rank in ('J', 'Q', 'K'):
        return 10
    if rank == 'A':
        return 11
    return int(rank)


def bj_hand_value(cards):
    total = sum(bj_card_value(r) for r, s in cards)
    aces = sum(1 for r, s in cards if r == 'A')
    while total > 21 and aces:
        total -= 10
        aces -= 1
    return total


def bj_is_natural(cards):
    return len(cards) == 2 and bj_hand_value(cards) == 21


def bj_build_shoe(server_seed, client_seed, nonce):
    """Deterministic shoe shuffle - identical inputs always produce the
    identical shoe order, which is what makes /fair verification possible."""
    combined = f"{server_seed}:{client_seed}:{nonce}"
    result_hash = hashlib.sha256(combined.encode()).hexdigest()
    rng = random.Random(result_hash)
    deck = [(r, s) for _ in range(BLACKJACK_DECKS) for r in RANKS for s in SUITS]
    rng.shuffle(deck)
    return deck


def bj_deal_card(game):
    return game["shoe"].pop(0)


def bj_new_hand(bet, cards, natural=False, split_ace=False):
    return {
        "cards": cards,
        "bet": bet,
        "status": "active",   # active | stand | bust
        "doubled": False,
        "natural": natural,
        "split_ace": split_ace,
        "result": None,       # win | lose | push (set once the round finishes)
        "payout": None,
    }


def bj_can_hit(hand):
    return hand["status"] == "active" and not hand["split_ace"]


def bj_can_double(game, hand):
    if hand["status"] != "active" or len(hand["cards"]) != 2 or hand["split_ace"]:
        return False
    return get_balance(game["user_id"]) >= hand["bet"]


def bj_can_split(game, hand):
    if hand["status"] != "active" or len(hand["cards"]) != 2:
        return False
    if len(game["hands"]) != 1:
        return False  # only one split per round, no re-splitting
    (r1, _), (r2, _) = hand["cards"]
    if bj_card_value(r1) != bj_card_value(r2):
        return False
    return get_balance(game["user_id"]) >= hand["bet"]


def bj_active_hand(game):
    idx = game["active_hand_index"]
    if idx is None or idx >= len(game["hands"]):
        return None
    return game["hands"][idx]


def bj_advance_or_finish(game):
    """Call after a hand stops being playable (stand/bust/double/split-ace).
    Moves to the next hand if one exists, otherwise resolves the dealer and
    every hand's payout. Must be called while holding BLACKJACK_LOCK.
    Returns a payout summary dict if the round just finished, else None."""
    hands = game["hands"]
    idx = game["active_hand_index"]
    for i in range(idx + 1, len(hands)):
        if hands[i]["status"] == "active":
            game["active_hand_index"] = i
            return None

    # every hand is done - reveal the dealer and settle up
    game["dealer_hole_revealed"] = True
    any_live = any(h["status"] != "bust" for h in hands)
    if any_live:
        while bj_hand_value(game["dealer_cards"]) < 17:
            game["dealer_cards"].append(bj_deal_card(game))
    dealer_total = bj_hand_value(game["dealer_cards"])
    dealer_bust = dealer_total > 21
    dealer_natural = bj_is_natural(game["dealer_cards"])

    total_payout = 0.0
    for h in hands:
        bet = h["bet"]
        if h["status"] == "bust":
            h["result"], h["payout"] = "lose", 0.0
        elif h["natural"]:
            if dealer_natural:
                h["result"], h["payout"] = "push", bet
            else:
                h["result"], h["payout"] = "win", round(bet * 2.5, 2)
        elif dealer_natural:
            h["result"], h["payout"] = "lose", 0.0
        else:
            my_total = bj_hand_value(h["cards"])
            if dealer_bust or my_total > dealer_total:
                h["result"], h["payout"] = "win", round(bet * 2, 2)
            elif my_total == dealer_total:
                h["result"], h["payout"] = "push", bet
            else:
                h["result"], h["payout"] = "lose", 0.0
        total_payout += h["payout"]

    game["status"] = "done"
    game["active_hand_index"] = None
    return {
        "total_payout": round(total_payout, 2),
        "total_bet": round(sum(h["bet"] for h in hands), 2),
    }


def blackjack_start(token, requested_amount=None):
    """Called by the Mini App's Deal button - bet is checked/deducted here,
    same convention as crash_start. requested_amount lets the player adjust
    the bet from the idle panel's quick-amount buttons before dealing."""
    with BLACKJACK_LOCK:
        game = active_blackjack_games.get(token)
        if not game:
            return {"ok": False, "error": "not_found"}
        if game["status"] != "pending":
            return {"ok": False, "error": "already_started"}

        amount = game["amount"]
        if requested_amount is not None:
            try:
                requested_amount = round(float(requested_amount), 2)
            except (TypeError, ValueError):
                requested_amount = None
            if requested_amount is not None and requested_amount > 0:
                if requested_amount < MIN_BET:
                    return {"ok": False, "error": "min_bet"}
                if requested_amount > MAX_BET:
                    return {"ok": False, "error": "max_bet"}
                amount = requested_amount

        balance = get_balance(game["user_id"])
        if amount > balance:
            return {"ok": False, "error": "insufficient_balance"}

        game["amount"] = amount
        adjust_balance(game["user_id"], -amount)
        game["shoe"] = bj_build_shoe(game["server_seed"], game["client_seed"], game["nonce"])

        p_cards = [bj_deal_card(game), bj_deal_card(game)]
        d_cards = [bj_deal_card(game), bj_deal_card(game)]
        hand = bj_new_hand(game["amount"], p_cards, natural=bj_is_natural(p_cards))
        game["hands"] = [hand]
        game["dealer_cards"] = d_cards
        game["dealer_hole_revealed"] = False
        game["active_hand_index"] = 0
        game["status"] = "active"

        summary = None
        if hand["natural"] or bj_is_natural(d_cards):
            summary = bj_advance_or_finish(game)

        user_id, chat_id, username = game["user_id"], game["chat_id"], game["username"]

    if summary:
        _bj_settle(game, user_id, chat_id, username, summary)
    return {"ok": True}


def blackjack_play_again(token):
    """Called by the Mini App's Play Again button once a round is 'done'.
    Resets the table back to 'pending' in place (fresh seed/nonce for
    fairness) so the player can Deal again without leaving the page or
    losing their spot. Nothing is charged here - that happens on the next
    /start, exactly like any other pending table."""
    with BLACKJACK_LOCK:
        game = active_blackjack_games.get(token)
        if not game:
            return {"ok": False, "error": "not_found"}
        if game["status"] != "done":
            return {"ok": False, "error": "not_done"}

        game["server_seed"] = secrets.token_hex(16)
        game["client_seed"] = get_client_seed(game["user_id"])
        game["nonce"] = next_nonce(game["user_id"])
        game["shoe"] = []
        game["hands"] = []
        game["dealer_cards"] = []
        game["dealer_hole_revealed"] = False
        game["active_hand_index"] = None
        game["status"] = "pending"
        user_active_blackjack[game["user_id"]] = token

    threading.Thread(target=blackjack_pending_expiry, args=(token,), daemon=True).start()
    return {"ok": True}


def blackjack_hit(token):
    with BLACKJACK_LOCK:
        game = active_blackjack_games.get(token)
        if not game or game["status"] != "active":
            return {"ok": False, "error": "not_active"}
        hand = bj_active_hand(game)
        if not hand or not bj_can_hit(hand):
            return {"ok": False, "error": "cannot_hit"}

        hand["cards"].append(bj_deal_card(game))
        total = bj_hand_value(hand["cards"])
        summary = None
        if total >= 21:
            hand["status"] = "bust" if total > 21 else "stand"
            summary = bj_advance_or_finish(game)

        user_id, chat_id, username = game["user_id"], game["chat_id"], game["username"]

    if summary:
        _bj_settle(game, user_id, chat_id, username, summary)
    return {"ok": True}


def blackjack_stand(token):
    with BLACKJACK_LOCK:
        game = active_blackjack_games.get(token)
        if not game or game["status"] != "active":
            return {"ok": False, "error": "not_active"}
        hand = bj_active_hand(game)
        if not hand or hand["status"] != "active":
            return {"ok": False, "error": "cannot_stand"}

        hand["status"] = "stand"
        summary = bj_advance_or_finish(game)
        user_id, chat_id, username = game["user_id"], game["chat_id"], game["username"]

    if summary:
        _bj_settle(game, user_id, chat_id, username, summary)
    return {"ok": True}


def blackjack_double(token):
    with BLACKJACK_LOCK:
        game = active_blackjack_games.get(token)
        if not game or game["status"] != "active":
            return {"ok": False, "error": "not_active"}
        hand = bj_active_hand(game)
        if not hand or not bj_can_double(game, hand):
            return {"ok": False, "error": "cannot_double"}

        adjust_balance(game["user_id"], -hand["bet"])
        hand["bet"] *= 2
        hand["doubled"] = True
        hand["cards"].append(bj_deal_card(game))
        total = bj_hand_value(hand["cards"])
        hand["status"] = "bust" if total > 21 else "stand"
        summary = bj_advance_or_finish(game)
        user_id, chat_id, username = game["user_id"], game["chat_id"], game["username"]

    if summary:
        _bj_settle(game, user_id, chat_id, username, summary)
    return {"ok": True}


def blackjack_split(token):
    with BLACKJACK_LOCK:
        game = active_blackjack_games.get(token)
        if not game or game["status"] != "active":
            return {"ok": False, "error": "not_active"}
        hand = bj_active_hand(game)
        if not hand or not bj_can_split(game, hand):
            return {"ok": False, "error": "cannot_split"}

        adjust_balance(game["user_id"], -hand["bet"])
        (c1, c2) = hand["cards"]
        is_ace_split = bj_card_value(c1[0]) == 11

        hand_a = bj_new_hand(hand["bet"], [c1, bj_deal_card(game)], split_ace=is_ace_split)
        hand_b = bj_new_hand(hand["bet"], [c2, bj_deal_card(game)], split_ace=is_ace_split)
        if is_ace_split:
            hand_a["status"] = "stand"
            hand_b["status"] = "stand"

        idx = game["active_hand_index"]
        game["hands"][idx:idx + 1] = [hand_a, hand_b]

        summary = bj_advance_or_finish(game) if is_ace_split else None
        user_id, chat_id, username = game["user_id"], game["chat_id"], game["username"]

    if summary:
        _bj_settle(game, user_id, chat_id, username, summary)
    return {"ok": True}


def _bj_settle(game, user_id, chat_id, username, summary):
    """Pays out and sends the result message once a round is fully done.
    Called outside BLACKJACK_LOCK, mirroring crash's pattern of not holding
    a game lock during network I/O."""
    if summary["total_payout"] > 0:
        adjust_balance(user_id, summary["total_payout"])
    user_active_blackjack.pop(user_id, None)

    profit = round(summary["total_payout"] - summary["total_bet"], 2)
    lines = [f"{BJ_HEADER_EMOJI} <b>Blackjack</b> — {mention(user_id, username)}", ""]
    dealer_total = bj_hand_value(game["dealer_cards"])
    dealer_str = ", ".join(f"{r}{s}" for r, s in game["dealer_cards"])
    lines.append(f"Dealer: {dealer_str} (<b>{dealer_total}</b>)")
    for i, h in enumerate(game["hands"], 1):
        hand_str = ", ".join(f"{r}{s}" for r, s in h["cards"])
        label = {"win": f"{BJ_WIN_EMOJI} Win", "lose": f"{BJ_LOSE_EMOJI} Lose", "push": f"{BJ_PUSH_EMOJI} Push"}[h["result"]]
        tag = f" Hand {i}:" if len(game["hands"]) > 1 else ""
        lines.append(f"{tag} {hand_str} (<b>{bj_hand_value(h['cards'])}</b>) — {label} ${h['payout']:.2f}")
    lines.append("")
    if profit > 0:
        lines.append(f"{cemoji('money')} You won <b>${profit:.2f}</b>! Balance: <b>${get_balance(user_id):.2f}</b>")
        broadcast_win(user_id, username, "Blackjack", summary["total_bet"], summary["total_payout"])
    elif profit < 0:
        lines.append(f"{cemoji('money')} You lost <b>${-profit:.2f}</b>. Balance: <b>${get_balance(user_id):.2f}</b>")
    else:
        lines.append(f"{cemoji('money')} Pushed - balance unchanged: <b>${get_balance(user_id):.2f}</b>")

    send_message(
        chat_id,
        "\n".join(lines),
        reply_markup=fair_button_keyboard("bj", game["server_seed"], game["client_seed"], game["nonce"])
    )


def bj_serialize_state(game):
    """The single state shape every blackjack API endpoint returns - the
    front-end just renders whatever comes back, all legality checks (can
    this hand hit/double/split right now) are decided here, not in JS."""
    hands_out = []
    for i, h in enumerate(game.get("hands", [])):
        hands_out.append({
            "cards": [{"rank": r, "suit": s} for r, s in h["cards"]],
            "total": bj_hand_value(h["cards"]),
            "bet": h["bet"],
            "status": h["status"],
            "result": h["result"],
            "payout": h["payout"],
            "is_active": game.get("status") == "active" and game.get("active_hand_index") == i,
            "can_hit": game.get("status") == "active" and game.get("active_hand_index") == i and bj_can_hit(h),
            "can_double": game.get("status") == "active" and game.get("active_hand_index") == i and bj_can_double(game, h),
            "can_split": game.get("status") == "active" and game.get("active_hand_index") == i and bj_can_split(game, h),
        })

    dealer_cards = game.get("dealer_cards", [])
    hole_revealed = game.get("dealer_hole_revealed", False)
    if dealer_cards and not hole_revealed:
        dealer_out = [{"rank": dealer_cards[0][0], "suit": dealer_cards[0][1]}, {"rank": None, "suit": None}]
        dealer_total = None
    else:
        dealer_out = [{"rank": r, "suit": s} for r, s in dealer_cards]
        dealer_total = bj_hand_value(dealer_cards) if dealer_cards else None

    return {
        "status": game["status"],
        "amount": game["amount"],
        "balance": get_balance(game["user_id"]),
        "dealer": {"cards": dealer_out, "total": dealer_total, "hole_hidden": bool(dealer_cards) and not hole_revealed},
        "hands": hands_out,
        "active_hand_index": game.get("active_hand_index"),
    }


def blackjack_get_state(token):
    with BLACKJACK_LOCK:
        game = active_blackjack_games.get(token)
        if not game:
            return None
        if game["status"] == "pending":
            return {"status": "pending", "amount": game["amount"], "balance": get_balance(game["user_id"])}
        return bj_serialize_state(game)


def blackjack_mini_app_keyboard(token):
    url = f"{APP_URL}/blackjack/{token}"
    return {"inline_keyboard": [[{"text": "Sit at Table", "icon_custom_emoji_id": "5285420684699260907", "web_app": {"url": url}}]]}


active_blackjack_invites = {}
BLACKJACK_INVITE_LOCK = threading.Lock()
BLACKJACK_INVITE_TIMEOUT = 300
BLACKJACK_PENDING_TIMEOUT = 300


def blackjack_invite_expiry(invite_token):
    time.sleep(BLACKJACK_INVITE_TIMEOUT)
    with BLACKJACK_INVITE_LOCK:
        active_blackjack_invites.pop(invite_token, None)


def blackjack_pending_expiry(token):
    time.sleep(BLACKJACK_PENDING_TIMEOUT)
    with BLACKJACK_LOCK:
        game = active_blackjack_games.get(token)
        if not game or game["status"] != "pending":
            return
        active_blackjack_games.pop(token, None)
        user_active_blackjack.pop(game["user_id"], None)
        chat_id, user_id, username = game["chat_id"], game["user_id"], game["username"]

    send_message(
        chat_id,
        f"{BJ_EXPIRED_EMOJI} {mention(user_id, username)}, your Blackjack table expired unused. "
        f"Nothing was charged - start a new one with /blackjack."
    )


def handle_blackjack_command(chat_id, user_id, username, args, chat_type="private"):
    if not args:
        send_message(chat_id, f"{WARN_EMOJI} Usage: <code>/blackjack &lt;amount&gt;</code>\nExample: <code>/blackjack 10</code>")
        return
    amount, _amt_err = resolve_bet_amount(user_id, args[0])
    if _amt_err == "invalid_number":
        send_message(chat_id, f"{WARN_EMOJI} Invalid amount. Example: <code>/blackjack 10</code>")
        return
    if _amt_err == "rate_unavailable":
        send_message(chat_id, f"{WARN_EMOJI} Currency rate temporarily unavailable - try again shortly, or run /currency to switch to USD.")
        return
    if amount < MIN_BET:
        send_message(chat_id, f"{WARN_EMOJI} Minimum bet is ${MIN_BET:.2f}")
        return
    if amount > MAX_BET:
        send_message(chat_id, f"{WARN_EMOJI} Maximum bet is ${MAX_BET:.2f}")
        return
    balance = get_balance(user_id)
    if amount > balance:
        send_message(chat_id, f"{WARN_EMOJI} Insufficient balance. Your balance: ${balance:.2f}")
        return
    if not APP_URL:
        send_message(
            chat_id,
            f"{WARN_EMOJI} Blackjack's Mini App isn't configured yet. The bot owner needs to "
            "set the <code>APP_URL</code> environment variable to this service's public HTTPS URL."
        )
        return
    if user_id in user_active_blackjack:
        send_message(chat_id, f"{WARN_EMOJI} You already have an active Blackjack table! Finish it in the app first.")
        return

    if chat_type != "private":
        if not BOT_USERNAME:
            send_message(chat_id, f"{WARN_EMOJI} Bot isn't fully started yet - try again in a few seconds.")
            return
        invite_token = secrets.token_urlsafe(8)
        with BLACKJACK_INVITE_LOCK:
            active_blackjack_invites[invite_token] = {
                "owner_id": user_id, "owner_name": username, "amount": amount, "used": False,
            }
        threading.Thread(target=blackjack_invite_expiry, args=(invite_token,), daemon=True).start()
        deep_link = f"https://t.me/{BOT_USERNAME}?start=bji_{invite_token}"
        send_message(
            chat_id,
            f"{BJ_HEADER_EMOJI} <b>Blackjack</b> — {mention(user_id, username)}\n\n"
            f"Bet: <b>${amount:.2f}</b>\n\n"
            f"Blackjack only runs in DM. This button is one-time use, only for {mention(user_id, username)}:",
            reply_markup={"inline_keyboard": [[{"text": "Play Blackjack in DM", "icon_custom_emoji_id": "5285420684699260907", "url": deep_link}]]}
        )
        return

    with BLACKJACK_LOCK:
        if user_id in user_active_blackjack:
            send_message(chat_id, f"{WARN_EMOJI} You already have an active Blackjack table! Finish it in the app first.")
            return
        client_seed = get_client_seed(user_id)
        nonce = next_nonce(user_id)
        server_seed = secrets.token_hex(16)
        token = secrets.token_urlsafe(12)
        active_blackjack_games[token] = {
            "token": token, "user_id": user_id, "chat_id": chat_id, "username": username,
            "amount": amount, "server_seed": server_seed, "client_seed": client_seed, "nonce": nonce,
            "shoe": [], "hands": [], "dealer_cards": [], "dealer_hole_revealed": False,
            "active_hand_index": None, "status": "pending",
        }
        user_active_blackjack[user_id] = token

    threading.Thread(target=blackjack_pending_expiry, args=(token,), daemon=True).start()

    send_message(
        chat_id,
        f"{BJ_HEADER_EMOJI} <b>Blackjack</b> — {mention(user_id, username)}\n\n"
        f"Bet: <b>${amount:.2f}</b>\n"
        f"Balance: <b>${get_balance(user_id):.2f}</b>\n\n"
        f"Open the table below, then press <b>Deal</b> when you're ready:",
        reply_markup=blackjack_mini_app_keyboard(token)
    )


def handle_message(message):
    chat_id = message["chat"]["id"]
    user_id = message["from"]["id"]
    text = message.get("text", "").strip()

    uname = message["from"].get("username")
    if uname:
        key = uname.lower()
        if known_usernames.get(key) != user_id:
            known_usernames[key] = user_id
            if DB_ENABLED:
                try:
                    db.save_username(user_id, key)
                except Exception as e:
                    print(f"⚠️ Could not persist username for {user_id}: {e}")

    if user_id not in all_known_user_ids:
        with KNOWN_USERS_LOCK:
            all_known_user_ids.add(user_id)
        if DB_ENABLED:
            try:
                db.touch_user(user_id)
            except Exception as e:
                print(f"⚠️ Could not record user {user_id}: {e}")

    if check_for_custom_emoji_ids(message):
        return

    if not text.startswith("/"):
        # Not a command - might be a reply to a /deposit or /withdraw prompt
        # (a bare amount, or a wallet address). Let that flow claim it;
        # otherwise there's nothing else this bot does with free text.
        # IMPORTANT: deposit/withdraw are DM-only flows (see handle_deposit_command)
        # - pending_deposit_flow/pending_withdraw_flow are keyed by user_id only,
        # with no chat_id check, so without this guard a user typing a plain
        # number in ANY group they're in (e.g. "10" as unrelated chat) gets
        # misread as their deposit amount and the invoice - amount + pay
        # address - gets posted into that group instead of their DM.
        chat_type = message["chat"].get("type", "private")
        if text and chat_type == "private":
            username = message["from"].get("first_name", "Player")
            try_handle_payment_flow_message(chat_id, user_id, username, text)
        return

    parts = text.split()
    command = parts[0].split("@")[0]
    args = parts[1:]

    # Short-form aliases - map to the canonical command so the rest of the
    # dispatch logic below needs zero changes.
    COMMAND_ALIASES = {
        "/roul": "/roulette",
        "/tw": "/towers",
        "/bal": "/balance",
        "/bj": "/blackjack",
        "/cr": "/chickenroad",
        "/cf": "/coinflip",
        "/dep": "/deposit",
        "/wd": "/withdraw",
    }
    command = COMMAND_ALIASES.get(command, command)

    if command == "/start":
        get_balance(user_id)
        name = message["from"].get("first_name", "Player")

        if args and args[0].startswith("fair_"):
            token = args[0][len("fair_"):]
            entry = fair_verifications.get(token)
            if entry:
                game, params, server_seed, client_seed, nonce = entry
                send_message(chat_id, fair_verification_text(game, params, server_seed, client_seed, nonce))
            else:
                send_message(chat_id, f"{WARN_EMOJI} This verification link is invalid or has expired (bot restart clears them).")
            return

        if args and args[0].startswith("cri_"):
            # Deep-linked in from a group's "Play Crash in DM" button. This
            # invite is single-use and locked to the user who typed /crash -
            # everyone else gets turned away here, and a second click by the
            # rightful owner (after their round finished) gets turned away
            # too, since `used` is only ever flipped True once.
            invite_token = args[0][len("cri_"):]
            with CRASH_INVITE_LOCK:
                invite = active_crash_invites.get(invite_token)
                if invite is None:
                    send_message(
                        chat_id,
                        f"{WARN_EMOJI} This launch link has expired or was already used. "
                        "Go back to the group and run /crash again."
                    )
                    return
                if invite["owner_id"] != user_id:
                    send_message(
                        chat_id,
                        f"🚫 This isn't your bet! Only {mention(invite['owner_id'], invite['owner_name'])} "
                        f"can use this link. Start your own with /crash &lt;amount&gt;."
                    )
                    return
                if invite["used"]:
                    send_message(
                        chat_id,
                        f"{WARN_EMOJI} This launch link was already used for its one round. "
                        "Go back to the group and run /crash again for a new one."
                    )
                    return
                invite["used"] = True
                amount = invite["amount"]

            handle_crash_command(chat_id, user_id, name, [str(amount)], "private")
            return

        if args and args[0].startswith("bji_"):
            # Same deep-link pattern as cri_ above, for Blackjack's group invite.
            invite_token = args[0][len("bji_"):]
            with BLACKJACK_INVITE_LOCK:
                invite = active_blackjack_invites.get(invite_token)
                if invite is None:
                    send_message(
                        chat_id,
                        f"{WARN_EMOJI} This table link has expired or was already used. "
                        "Go back to the group and run /blackjack again."
                    )
                    return
                if invite["owner_id"] != user_id:
                    send_message(
                        chat_id,
                        f"🚫 This isn't your bet! Only {mention(invite['owner_id'], invite['owner_name'])} "
                        f"can use this link. Start your own with /blackjack &lt;amount&gt;."
                    )
                    return
                if invite["used"]:
                    send_message(
                        chat_id,
                        f"{WARN_EMOJI} This table link was already used for its one round. "
                        "Go back to the group and run /blackjack again for a new one."
                    )
                    return
                invite["used"] = True
                amount = invite["amount"]

            handle_blackjack_command(chat_id, user_id, name, [str(amount)], "private")
            return

        if args and args[0].startswith("chi_"):
            # Same deep-link pattern as cri_/bji_ above, for Chicken Road's group invite.
            invite_token = args[0][len("chi_"):]
            with CHICKEN_INVITE_LOCK:
                invite = active_chicken_invites.get(invite_token)
                if invite is None:
                    send_message(
                        chat_id,
                        f"{WARN_EMOJI} This link has expired or was already used. "
                        "Go back to the group and run /chickenroad again."
                    )
                    return
                if invite["owner_id"] != user_id:
                    send_message(
                        chat_id,
                        f"🚫 This isn't your bet! Only {mention(invite['owner_id'], invite['owner_name'])} "
                        f"can use this link. Start your own with /chickenroad &lt;amount&gt;."
                    )
                    return
                if invite["used"]:
                    send_message(
                        chat_id,
                        f"{WARN_EMOJI} This link was already used for its one game. "
                        "Go back to the group and run /chickenroad again for a new one."
                    )
                    return
                invite["used"] = True
                amount = invite["amount"]

            handle_chicken_command(chat_id, user_id, name, [str(amount)], "private")
            return

        if args and args[0].startswith("dri_"):
            # Same deep-link pattern as cri_/bji_/chi_ above, for Dice's group invite.
            invite_token = args[0][len("dri_"):]
            with DICE_INVITE_LOCK:
                invite = active_dice_invites.get(invite_token)
                if invite is None:
                    send_message(
                        chat_id,
                        f"{WARN_EMOJI} This link has expired or was already used. "
                        "Go back to the group and run /dice again."
                    )
                    return
                if invite["owner_id"] != user_id:
                    send_message(
                        chat_id,
                        f"🚫 This isn't your bet! Only {mention(invite['owner_id'], invite['owner_name'])} "
                        f"can use this link. Start your own with /dice &lt;amount&gt;."
                    )
                    return
                if invite["used"]:
                    send_message(
                        chat_id,
                        f"{WARN_EMOJI} This link was already used for its one round. "
                        "Go back to the group and run /dice again for a new one."
                    )
                    return
                invite["used"] = True
                amount = invite["amount"]

            handle_dice_command(chat_id, user_id, name, [str(amount)], "private")
            return

        if args and args[0].startswith("depi_"):
            # Same deep-link pattern as cri_/bji_/chi_/dri_ above, for the
            # Deposit group invite - no amount to carry through, just hands
            # control to the normal DM deposit flow once ownership checks pass.
            invite_token = args[0][len("depi_"):]
            with DEPOSIT_INVITE_LOCK:
                invite = active_deposit_invites.get(invite_token)
                if invite is None:
                    send_message(
                        chat_id,
                        f"{WARN_EMOJI} This link has expired or was already used. "
                        "Go back to the group and run /deposit again."
                    )
                    return
                if invite["owner_id"] != user_id:
                    send_message(
                        chat_id,
                        f"🚫 This isn't your link! Only {mention(invite['owner_id'], invite['owner_name'])} "
                        f"can use this. Start your own with /deposit."
                    )
                    return
                if invite["used"]:
                    send_message(
                        chat_id,
                        f"{WARN_EMOJI} This link was already used. "
                        "Go back to the group and run /deposit again for a new one."
                    )
                    return
                invite["used"] = True

            handle_deposit_command(chat_id, user_id, name, [], "private")
            return

        if args and args[0].startswith("wdi_"):
            # Same deep-link pattern as depi_ above, for the Withdraw group invite.
            invite_token = args[0][len("wdi_"):]
            with WITHDRAW_INVITE_LOCK:
                invite = active_withdraw_invites.get(invite_token)
                if invite is None:
                    send_message(
                        chat_id,
                        f"{WARN_EMOJI} This link has expired or was already used. "
                        "Go back to the group and run /withdraw again."
                    )
                    return
                if invite["owner_id"] != user_id:
                    send_message(
                        chat_id,
                        f"🚫 This isn't your link! Only {mention(invite['owner_id'], invite['owner_name'])} "
                        f"can use this. Start your own with /withdraw."
                    )
                    return
                if invite["used"]:
                    send_message(
                        chat_id,
                        f"{WARN_EMOJI} This link was already used. "
                        "Go back to the group and run /withdraw again for a new one."
                    )
                    return
                invite["used"] = True

            handle_withdraw_command(chat_id, user_id, name, [], "private")
            return

        send_message(
            chat_id,
            f'<tg-emoji emoji-id="6105006251295377689">🎉</tg-emoji> Welcome {mention(user_id, name)} to <b>Traqd Casino</b>! {cemoji("fire")}\n\n'
            f"10 provably-fair games, instant crypto deposits, and a "
            f"<b>130% first-deposit bonus</b> waiting for you.\n\n"
            f"💳 <b>/deposit</b> — fund your account (min ${MIN_DEPOSIT:.2f})\n"
            f"📖 <b>/help</b> — every game, every command, how to play\n\n"
            f"Ready when you are. 🎰"
        )
        return

    if command == "/help":
        send_message(
            chat_id,
            f'<tg-emoji emoji-id="5361775397811795920">📖</tg-emoji> <b>Traqd Casino — Help</b>\n\n'
            f'<b><tg-emoji emoji-id="5215420556089776398">💰</tg-emoji> Wallet</b>\n'
            f"/balance — check your balance\n"
            f"/deposit — deposit crypto (min ${MIN_DEPOSIT:.2f})\n"
            f"/withdraw — withdraw crypto (min ${MIN_WITHDRAW:.2f})\n\n"
            f"Your <b>first deposit</b> gets a <b>130% bonus</b> automatically. "
            f"Bonus funds play just like normal balance, but need to be "
            f"wagered <b>{BONUS_WAGER_MULTIPLIER}×</b> before they're withdrawable. "
            f"Every deposit (bonus or not) also needs to be wagered "
            f"<b>{DEPOSIT_WAGER_MULTIPLIER}×</b> before any of your balance "
            f"can be withdrawn.\n\n"
            f'<b><tg-emoji emoji-id="5361766739157730216">🎮</tg-emoji> Games</b>\n'
            f"/roulette &lt;amount&gt; — bet red/black/green, odds/evens, "
            f"dozens, or a single number\n"
            f"/blackjack &lt;amount&gt; — classic 21 vs the dealer, hit/stand/"
            f"double/split\n"
            f"/crash &lt;amount&gt; — cash out before the multiplier crashes\n"
            f"/mines &lt;amount&gt; — reveal safe tiles, avoid the bombs, "
            f"cash out any time\n"
            f"/towers &lt;amount&gt; — climb the tower one level at a time\n"
            f"/keno &lt;amount&gt; — pick numbers, match the draw\n"
            f"/dice &lt;amount&gt; — roll under/over your target\n"
            f"/coinflip &lt;amount&gt; &lt;heads|tails&gt; — 50/50, straight up\n"
            f"/limbo &lt;amount&gt; &lt;target&gt; — pick a multiplier, beat it "
            f"or lose\n"
            f"/chickenroad &lt;amount&gt; — cross the road, each step raises "
            f"the multiplier\n\n"
            f"Most games open as an in-chat Mini App — tap the button the "
            f"bot sends after you run the command. Every result is provably "
            f'fair; look for the <tg-emoji emoji-id="5443000797111528222">🔍</tg-emoji> <b>Verify</b> button under each result '
            f"to check it yourself.\n\n"
            f'<b><tg-emoji emoji-id="5296533616224906961">👥</tg-emoji> Groups</b>\n'
            f"Every command above works in group chats too — each player's "
            f"bet is independent. Mini App games (Crash, Blackjack, Dice, "
            f"Chicken Road) send you a one-time link into DM since Telegram "
            f"only allows Mini Apps in private chats.\n\n"
            f"Questions? Just start again with /start."
        )
        return

    if command == "/balance":
        bal = get_balance(user_id)
        name = message["from"].get("first_name", "Player")
        send_message(
            chat_id,
            f'<tg-emoji emoji-id="5264895611517300926">💰</tg-emoji> '
            f'<tg-emoji emoji-id="5472250091332993630">💸</tg-emoji> '
            f"{mention(user_id, name)} balance: <b>${bal:.2f}</b> ({fmt_balance(user_id, bal)})",
            reply_markup=balance_action_keyboard()
        )
        return

    if command == "/currency":
        current = get_user_currency(user_id)
        buttons = [[{
            "text": meta['label'] + (" ✅" if code == current else ""),
            "callback_data": f"curr:{code}",
            "icon_custom_emoji_id": meta["icon_id"],
        } for code, meta in SUPPORTED_CURRENCIES.items()]]
        send_message(
            chat_id,
            f"💱 <b>Display Currency</b>\n\n"
            f"Your balance is always tracked in USD internally - this just changes "
            f"how it's <i>shown</i> to you, converted at the current rate.\n\n"
            f"Current: <b>{SUPPORTED_CURRENCIES[current]['label']}</b>",
            reply_markup={"inline_keyboard": buttons}
        )
        return

    if command == "/tip":
        # Deliberately NOT listed in /help or the Telegram command menu.
        if not args:
            send_message(chat_id, f"{WARN_EMOJI} Usage: reply to their message with <code>/tip 1</code>, or <code>/tip 1 @username</code>.")
            return
        try:
            amount = round(float(args[0]), 2)
        except ValueError:
            send_message(chat_id, f"{WARN_EMOJI} Please give a plain number, e.g. <code>/tip 1</code>")
            return
        if amount < MIN_TIP:
            send_message(chat_id, f"{WARN_EMOJI} Minimum tip is ${MIN_TIP:.2f}")
            return

        recipient_id = None
        recipient_name = None
        reply_msg = message.get("reply_to_message")
        if reply_msg and reply_msg.get("from") and not reply_msg["from"].get("is_bot"):
            recipient_id = reply_msg["from"]["id"]
            recipient_name = reply_msg["from"].get("first_name", "Player")
        elif len(args) > 1 and args[1].startswith("@"):
            uname = args[1][1:].lower()
            recipient_id = known_usernames.get(uname)
            recipient_name = args[1]
            if not recipient_id:
                send_message(chat_id, f"{WARN_EMOJI} Can't find @{args[1][1:]} - they need to have messaged in here at least once.")
                return
        else:
            send_message(chat_id, f"{WARN_EMOJI} Reply to their message with <code>/tip {amount}</code>, or use <code>/tip {amount} @username</code>.")
            return

        if recipient_id == user_id:
            send_message(chat_id, f"{WARN_EMOJI} You can't tip yourself.")
            return

        ok, reason = process_tip(user_id, recipient_id, amount)
        if not ok:
            send_message(chat_id, f"{WARN_EMOJI} Not enough non-bonus balance to tip that much - bonus funds can't be tipped.")
            return

        name = message["from"].get("first_name", "Player")
        note = " (they'll need to wager it 1x before withdrawing it)" if reason == "unwagered" else ""
        send_message(
            chat_id,
            f"🎁 {mention(user_id, name)} tipped {mention(recipient_id, recipient_name)} <b>${amount:.2f}</b>!{note}"
        )
        return

    if command == "/broadcast":
        # Admin-only, deliberately NOT listed in /help or the command menu.
        if not is_admin(user_id):
            return
        parts0 = text.split(None, 1)
        if len(parts0) < 2 or not parts0[1].strip():
            send_message(chat_id, f"{WARN_EMOJI} Usage: <code>/broadcast Your message here</code>\nHTML formatting (&lt;b&gt;, &lt;i&gt;, etc.) is supported.")
            return
        broadcast_text = parts0[1].strip()
        recipients = list(all_known_user_ids)
        send_message(chat_id, f"📣 Broadcasting to {len(recipients)} user(s)...")

        def _run_broadcast():
            sent, failed = 0, 0
            for uid in recipients:
                try:
                    send_message(uid, broadcast_text)
                    sent += 1
                except Exception as e:
                    failed += 1
                    print(f"⚠️ Broadcast failed for {uid}: {e}")
                time.sleep(0.05)  # ~20 msg/sec, safely under Telegram's global rate limit
            send_message(chat_id, f"✅ Broadcast complete. Sent: {sent}, Failed: {failed}.")

        threading.Thread(target=_run_broadcast, daemon=True).start()
        return

    if command == "/testfund":
        # Admin-only, deliberately NOT listed in /help or the command menu.
        # Grants play-money for testing games - it's added to the bonus
        # pool with an unclearable wager requirement so it (and any
        # winnings from it) can NEVER be converted to withdrawable real
        # balance, and it's wiped after 3 hours regardless of whether it
        # was played or not.
        #
        # IMPORTANT: if this account also has a real, legitimate bonus
        # active (e.g. from an actual test deposit) with its own
        # wager_required, we must not clobber that. So the ORIGINAL
        # wager_required is captured once (on the first grant) and
        # restored exactly at expiry - wager_progress is left completely
        # untouched throughout, so any real wagering the account does
        # during the test period still counts normally toward the real
        # requirement. At expiry we only remove the cumulative amount
        # actually granted (floored at 0, in case it was lost playing),
        # never the account's other bonus funds.
        if not is_admin(user_id):
            return
        if not args:
            send_message(chat_id, f"{WARN_EMOJI} Usage: <code>/testfund 50</code> (max ${MAX_TESTFUND:.2f})")
            return
        try:
            fund_amount = round(float(args[0]), 2)
        except ValueError:
            send_message(chat_id, f"{WARN_EMOJI} Please give a plain number, e.g. <code>/testfund 50</code>")
            return
        if fund_amount <= 0 or fund_amount > MAX_TESTFUND:
            send_message(chat_id, f"{WARN_EMOJI} Amount must be between $0.01 and ${MAX_TESTFUND:.2f}")
            return

        grant_token = time.time()
        with WALLET_LOCK:
            w = _ensure_wallet(user_id)
            existing = test_fund_grants.get(user_id)
            if existing:
                # Extending an already-active grant: keep the ORIGINAL
                # pre-testfund wager_required we captured the first time,
                # and accumulate the total amount to claw back at expiry.
                original_wager_required = existing["original_wager_required"]
                total_test_amount = round(existing["total_test_amount"] + fund_amount, 2)
            else:
                original_wager_required = w["wager_required"]
                total_test_amount = fund_amount

            w["bonus"] = round(w["bonus"] + fund_amount, 2)
            w["wager_required"] = 10 ** 9  # effectively unclearable while a grant is active
            _persist_wallet(user_id)

        test_fund_grants[user_id] = {
            "token": grant_token,
            "original_wager_required": original_wager_required,
            "total_test_amount": total_test_amount,
        }

        def _expire_testfund(uid, token):
            time.sleep(TESTFUND_LIFETIME_SECONDS)
            grant = test_fund_grants.get(uid)
            if not grant or grant["token"] != token:
                return  # a newer /testfund grant superseded this one - its own timer handles it
            with WALLET_LOCK:
                w2 = _ensure_wallet(uid)
                w2["bonus"] = max(0.0, round(w2["bonus"] - grant["total_test_amount"], 2))
                w2["wager_required"] = grant["original_wager_required"]
                _persist_wallet(uid)
            test_fund_grants.pop(uid, None)
            try:
                send_message(uid, f"{WARN_EMOJI} Your test funds have expired and been removed.")
            except Exception:
                pass

        threading.Thread(target=_expire_testfund, args=(user_id, grant_token), daemon=True).start()

        send_message(
            chat_id,
            f"🧪 Added <b>${fund_amount:.2f}</b> test funds.\n"
            f"This money (and anything won with it) <b>cannot be withdrawn</b> "
            f"and will be wiped in <b>3 hours</b>. Any real bonus you already "
            f"had is untouched and will be restored to its normal state then."
        )
        return

    if command == "/seed":
        current_seed = get_client_seed(user_id)
        current_nonce = get_nonce(user_id)
        if not args:
            send_message(
                chat_id,
                f"🔑 <b>Your Client Seed</b>\n\n"
                f"Seed: <code>{current_seed}</code>\n"
                f"Nonce: <code>{current_nonce}</code>\n\n"
                f"This is mixed into the server seed for every bet you place, "
                f"so you can prove results weren't rigged against you.\n"
                f"Set your own with <code>/seed &lt;text&gt;</code> (letters/numbers only, max 32 chars), "
                f"or get a fresh random one with /newseed."
            )
            return

        new_seed = args[0]
        if not new_seed.isalnum():
            send_message(chat_id, f"{WARN_EMOJI} Client seed can only contain letters and numbers.")
            return
        if len(new_seed) > 32:
            send_message(chat_id, f"{WARN_EMOJI} Client seed must be 32 characters or fewer.")
            return

        set_client_seed(user_id, new_seed)
        send_message(
            chat_id,
            f"✅ Client seed updated!\n\n"
            f"Seed: <code>{new_seed}</code>\n"
            f"Nonce reset to <code>0</code>."
        )
        return

    if command == "/newseed":
        new_seed = roll_new_client_seed(user_id)
        send_message(
            chat_id,
            f"🎲 New client seed generated!\n\n"
            f"Seed: <code>{new_seed}</code>\n"
            f"Nonce reset to <code>0</code>."
        )
        return

    if command == "/roulette":
        username = message["from"].get("first_name", "Player")
        handle_roulette_command(chat_id, user_id, username, args)
        return

    if command == "/limbo":
        username = message["from"].get("first_name", "Player")
        handle_limbo_command(chat_id, user_id, username, args)
        return

    if command == "/coinflip":
        username = message["from"].get("first_name", "Player")
        handle_coinflip_command(chat_id, user_id, username, args)
        return

    if command == "/mines":
        username = message["from"].get("first_name", "Player")
        handle_mines_command(chat_id, user_id, username, args)
        return

    if command == "/towers":
        username = message["from"].get("first_name", "Player")
        handle_towers_command(chat_id, user_id, username, args)
        return

    if command == "/keno":
        username = message["from"].get("first_name", "Player")
        handle_keno_command(chat_id, user_id, username, args)
        return

    if command == "/crash":
        username = message["from"].get("first_name", "Player")
        chat_type = message["chat"].get("type", "private")
        handle_crash_command(chat_id, user_id, username, args, chat_type)
        return

    if command == "/blackjack":
        username = message["from"].get("first_name", "Player")
        chat_type = message["chat"].get("type", "private")
        handle_blackjack_command(chat_id, user_id, username, args, chat_type)
        return

    if command == "/chickenroad":
        username = message["from"].get("first_name", "Player")
        chat_type = message["chat"].get("type", "private")
        handle_chicken_command(chat_id, user_id, username, args, chat_type)
        return

    if command == "/dice":
        username = message["from"].get("first_name", "Player")
        chat_type = message["chat"].get("type", "private")
        handle_dice_command(chat_id, user_id, username, args, chat_type)
        return

    if command == "/deposit":
        username = message["from"].get("first_name", "Player")
        chat_type = message["chat"].get("type", "private")
        handle_deposit_command(chat_id, user_id, username, args, chat_type)
        return

    if command == "/withdraw":
        username = message["from"].get("first_name", "Player")
        chat_type = message["chat"].get("type", "private")
        handle_withdraw_command(chat_id, user_id, username, args, chat_type)
        return

    # Reached only if the message started with "/" but matched none of the
    # commands above - e.g. someone typed a bare "/", a typo like "/rulette",
    # or a command that doesn't exist. Previously this fell through to the
    # end of the function silently, so the bot looked completely dead.
    send_message(
        chat_id,
        f"{WARN_EMOJI} Unknown command <code>{command}</code>. Send /help to see everything I can do."
    )
    return


# ---------------------------------------------------------------------------
# CHICKEN ROAD
# ---------------------------------------------------------------------------
# Same architecture as Crash/Blackjack: this module only holds game state +
# rules, chickenroad_web.py is the thin HTTP wrapper the Mini App page talks
# to. The chicken crosses a fixed CHICKEN_LANES-lane road one lane at a time;
# each lane independently has a fixed chance of a car being in it, set by
# difficulty. Multiplier uses the exact same "fair odds" construction as
# Towers: given a constant per-step survival probability, the multiplier for
# having survived N steps is (1 - house_edge) / survival_probability^N,
# floored to cents. Crossing every lane forces an automatic cashout at the
# final multiplier - clearing the whole board is a real, intended outcome,
# not just a bonus.

CHICKEN_HOUSE_EDGE = 0.01
CHICKEN_LANES = 12   # fixed across every difficulty - only the per-lane risk changes

CHICKEN_DIFFICULTY = {
    # safe_prob   = the REAL per-lane survival chance (what actually decides hit/safe)
    # payout_prob = the probability the multiplier formula assumes - only
    #               differs from safe_prob where we deliberately want the
    #               multiplier curve to move independently of the real odds.
    "easy":      {"label": "Easy",      "safe_prob": 0.73, "payout_prob": 0.80},
    "medium":    {"label": "Medium",    "safe_prob": 0.63, "payout_prob": 0.63},
    "hard":      {"label": "Hard",      "safe_prob": 0.52, "payout_prob": 0.52},
    "daredevil": {"label": "Daredevil", "safe_prob": 0.26, "payout_prob": 0.33},
}
CHICKEN_DEFAULT_DIFFICULTY = "easy"

active_chicken_games = {}   # token -> game dict
user_active_chicken = {}    # user_id -> token (one live Chicken Road game per user)
CHICKEN_LOCK = threading.Lock()


def chicken_multiplier(lanes_cleared, safe_prob, house_edge=CHICKEN_HOUSE_EDGE):
    """Fair multiplier for having safely crossed `lanes_cleared` lanes in a
    row, each with independent survival chance `safe_prob`. Same construction
    as towers_multiplier."""
    if lanes_cleared <= 0:
        return 1.0
    total_prob = safe_prob ** lanes_cleared
    if total_prob <= 0:
        return 0.0
    return math.floor(((1 - house_edge) / total_prob) * 100) / 100


def chicken_lane_is_hit(server_seed, client_seed, nonce, lane_index, safe_prob):
    """Deterministic provably-fair outcome for one specific lane - same
    seed/hash convention used everywhere else in this file (roulette/limbo/
    mines/towers/crash)."""
    h = hashlib.sha256(f"{server_seed}:{client_seed}:{nonce}:{lane_index}".encode()).hexdigest()
    r = int(h[:13], 16) / float(1 << 52)
    return r >= safe_prob


def chicken_start(token, requested_amount=None, requested_difficulty=None):
    """Called by the Mini App's Go button - bet, difficulty, and balance
    deduction are all locked in here, not when /chickenroad was typed (same
    convention as crash_start/blackjack_start, and for the same reason: this
    is the only place that should ever touch the player's balance for this
    round)."""
    with CHICKEN_LOCK:
        game = active_chicken_games.get(token)
        if not game:
            return {"ok": False, "error": "not_found"}
        if game["status"] != "pending":
            return {"ok": False, "error": "already_started"}

        amount = game["amount"]
        if requested_amount is not None:
            try:
                requested_amount = round(float(requested_amount), 2)
            except (TypeError, ValueError):
                requested_amount = None
            if requested_amount is not None and requested_amount > 0:
                if requested_amount < MIN_BET:
                    return {"ok": False, "error": "min_bet"}
                if requested_amount > MAX_BET:
                    return {"ok": False, "error": "max_bet"}
                amount = requested_amount

        difficulty = game["difficulty"]
        if requested_difficulty in CHICKEN_DIFFICULTY:
            difficulty = requested_difficulty

        balance = get_balance(game["user_id"])
        if amount > balance:
            return {"ok": False, "error": "insufficient_balance"}

        adjust_balance(game["user_id"], -amount)
        game["amount"] = amount
        game["difficulty"] = difficulty
        game["lane_index"] = 0
        game["current_multiplier"] = 1.0
        game["status"] = "active"
    return {"ok": True}


def chicken_step(token):
    """Advances one lane. This is the only place a lane's outcome is ever
    decided - each call checks exactly one new lane, deterministically, from
    the round's own seed/nonce, so replaying the same round always produces
    the same sequence of safe/hit lanes."""
    hit = False
    full_clear = False
    with CHICKEN_LOCK:
        game = active_chicken_games.get(token)
        if not game:
            return {"ok": False, "error": "not_found"}
        if game["status"] != "active":
            return {"ok": False, "error": "not_active"}

        safe_prob = CHICKEN_DIFFICULTY[game["difficulty"]]["safe_prob"]
        payout_prob = CHICKEN_DIFFICULTY[game["difficulty"]]["payout_prob"]
        lane = game["lane_index"]
        hit = chicken_lane_is_hit(game["server_seed"], game["client_seed"], game["nonce"], lane, safe_prob)

        if hit:
            game["status"] = "crashed"
            game["hit_lane"] = lane
            user_active_chicken.pop(game["user_id"], None)
        else:
            game["lane_index"] += 1
            game["current_multiplier"] = chicken_multiplier(game["lane_index"], payout_prob)
            full_clear = game["lane_index"] >= CHICKEN_LANES
            if full_clear:
                game["status"] = "cashed_out"
                game["cashout_multiplier"] = game["current_multiplier"]
                user_active_chicken.pop(game["user_id"], None)

        user_id, chat_id, username, amount = game["user_id"], game["chat_id"], game["username"], game["amount"]
        server_seed, client_seed, nonce = game["server_seed"], game["client_seed"], game["nonce"]
        multiplier = game["current_multiplier"]

    if hit:
        send_message(
            chat_id,
            f"{CHICKEN_HIT_EMOJI} <b>Chicken Road</b> — {mention(user_id, username)}\n\n"
            f"Hit by a car crossing lane <b>{lane + 1}</b>! Lost <b>${amount:.2f}</b>\n"
            f"{cemoji('money')} Balance: <b>${get_balance(user_id):.2f}</b>",
            reply_markup=fair_button_keyboard("cr", server_seed, client_seed, nonce)
        )
        return {"ok": True, "hit": True, "lane": lane}

    if full_clear:
        payout = round(amount * multiplier, 2)
        adjust_balance(user_id, payout)
        broadcast_win(user_id, username, "Chicken Road", amount, payout, detail=f"Crossed all {CHICKEN_LANES} lanes")
        send_message(
            chat_id,
            f"{CHICKEN_EMOJI} <b>Chicken Road</b> — {mention(user_id, username)}\n\n"
            f"Crossed all {CHICKEN_LANES} lanes!\n"
            f"${amount:.2f} \u2192 ${payout:.2f}\n\n"
            f"{cemoji('trophy')} You won <b>${payout - amount:.2f}</b>!\n"
            f"{cemoji('money')} Balance: <b>${get_balance(user_id):.2f}</b>",
            reply_markup=fair_button_keyboard("cr", server_seed, client_seed, nonce)
        )

    return {"ok": True, "hit": False, "full_clear": full_clear, "multiplier": multiplier}


def chicken_cashout(token):
    """Cashes out at whatever multiplier the player has already locked in by
    safely crossing lanes so far. Only ever reads state that chicken_step
    already committed - there's no server-side clock here to race against,
    unlike Crash."""
    with CHICKEN_LOCK:
        game = active_chicken_games.get(token)
        if not game:
            return {"ok": False, "error": "not_found"}
        if game["status"] != "active":
            if game["status"] == "crashed":
                return {"ok": False, "error": "crashed", "hit_lane": game.get("hit_lane")}
            if game["status"] == "pending":
                return {"ok": False, "error": "not_started"}
            return {"ok": False, "error": "already_ended"}
        if game["lane_index"] <= 0:
            # Same rule across every difficulty - at least one lane has to be
            # crossed before there's anything to lock in.
            return {"ok": False, "error": "no_steps_taken"}

        lane_index = game["lane_index"]
        multiplier = game["current_multiplier"]
        payout = round(game["amount"] * multiplier, 2)
        game["status"] = "cashed_out"
        game["cashout_multiplier"] = multiplier
        user_active_chicken.pop(game["user_id"], None)
        user_id, chat_id, username, amount = game["user_id"], game["chat_id"], game["username"], game["amount"]
        server_seed, client_seed, nonce = game["server_seed"], game["client_seed"], game["nonce"]

    adjust_balance(user_id, payout)
    broadcast_win(user_id, username, "Chicken Road", amount, payout, detail=f"Cashed out after {lane_index} lane{'s' if lane_index != 1 else ''} at {multiplier:.2f}x")
    send_message(
        chat_id,
        f"{CHICKEN_EMOJI} <b>Chicken Road</b> — {mention(user_id, username)}\n\n"
        f"Cashed out after <b>{lane_index}</b> lane{'s' if lane_index != 1 else ''} at <b>{multiplier:.2f}x</b>!\n"
        f"${amount:.2f} \u2192 ${payout:.2f}\n\n"
        f"{cemoji('trophy')} You won <b>${payout - amount:.2f}</b>!\n"
        f"{cemoji('money')} Balance: <b>${get_balance(user_id):.2f}</b>",
        reply_markup=fair_button_keyboard("cr", server_seed, client_seed, nonce)
    )
    return {"ok": True, "multiplier": multiplier, "payout": payout}


def chicken_play_again(token):
    """Resets an already-finished table back to 'pending' in place, fresh
    seed/nonce, so the player can hit Go again without leaving the page.
    Nothing is charged here - same convention as blackjack_play_again."""
    with CHICKEN_LOCK:
        game = active_chicken_games.get(token)
        if not game:
            return {"ok": False, "error": "not_found"}
        if game["status"] not in ("crashed", "cashed_out"):
            return {"ok": False, "error": "not_done"}

        game["server_seed"] = secrets.token_hex(16)
        game["client_seed"] = get_client_seed(game["user_id"])
        game["nonce"] = next_nonce(game["user_id"])
        game["lane_index"] = 0
        game["current_multiplier"] = 1.0
        game["hit_lane"] = None
        game["cashout_multiplier"] = None
        game["status"] = "pending"
        user_active_chicken[game["user_id"]] = token

    threading.Thread(target=chicken_pending_expiry, args=(token,), daemon=True).start()
    return {"ok": True}


def chicken_get_state(token):
    """Single state shape every Chicken Road API endpoint returns - the
    front-end just renders whatever comes back."""
    with CHICKEN_LOCK:
        game = active_chicken_games.get(token)
        if not game:
            return None

        if game["status"] == "pending":
            return {
                "status": "pending",
                "amount": game["amount"],
                "difficulty": game["difficulty"],
                "lanes": CHICKEN_LANES,
                "balance": get_balance(game["user_id"]),
            }

        payout_prob = CHICKEN_DIFFICULTY[game["difficulty"]]["payout_prob"]

        if game["status"] == "active":
            return {
                "status": "active",
                "amount": game["amount"],
                "difficulty": game["difficulty"],
                "lane_index": game["lane_index"],
                "multiplier": game["current_multiplier"],
                "next_multiplier": chicken_multiplier(game["lane_index"] + 1, payout_prob),
                "lanes": CHICKEN_LANES,
                "balance": get_balance(game["user_id"]),
            }
        if game["status"] == "crashed":
            return {
                "status": "crashed",
                "hit_lane": game.get("hit_lane"),
                "amount": game["amount"],
                "difficulty": game["difficulty"],
                "lanes": CHICKEN_LANES,
                "balance": get_balance(game["user_id"]),
            }
        if game["status"] == "cashed_out":
            return {
                "status": "cashed_out",
                "multiplier": game["cashout_multiplier"],
                "payout": round(game["amount"] * game["cashout_multiplier"], 2),
                "amount": game["amount"],
                "lane_index": game["lane_index"],
                "difficulty": game["difficulty"],
                "lanes": CHICKEN_LANES,
                "balance": get_balance(game["user_id"]),
            }
    return None


def chicken_mini_app_keyboard(token):
    url = f"{APP_URL}/chickenroad/{token}"
    return {"inline_keyboard": [[{"text": "Cross the Road", "icon_custom_emoji_id": "6334536360224884639", "web_app": {"url": url}}]]}


CHICKEN_PENDING_TIMEOUT = 300  # seconds a game stays open unstarted before it expires


def chicken_pending_expiry(token):
    time.sleep(CHICKEN_PENDING_TIMEOUT)
    with CHICKEN_LOCK:
        game = active_chicken_games.get(token)
        if not game or game["status"] != "pending":
            return
        active_chicken_games.pop(token, None)
        user_active_chicken.pop(game["user_id"], None)
        chat_id, user_id, username = game["chat_id"], game["user_id"], game["username"]

    send_message(
        chat_id,
        f"⌛ {mention(user_id, username)}, your Chicken Road game expired unused. "
        f"Nothing was charged - start a new one with /chickenroad."
    )


# ---------------------------------------------------------------------------
# CHICKEN ROAD GROUP INVITES
# ---------------------------------------------------------------------------
# Same single-use, owner-locked deep-link pattern as Crash/Blackjack's group
# invites - see handle_crash_command's comment for why this exists at all.

active_chicken_invites = {}
CHICKEN_INVITE_LOCK = threading.Lock()
CHICKEN_INVITE_TIMEOUT = 300


def chicken_invite_expiry(invite_token):
    time.sleep(CHICKEN_INVITE_TIMEOUT)
    with CHICKEN_INVITE_LOCK:
        active_chicken_invites.pop(invite_token, None)


def handle_chicken_command(chat_id, user_id, username, args, chat_type="private"):
    if not args:
        send_message(chat_id, f"{WARN_EMOJI} Usage: <code>/chickenroad &lt;amount&gt;</code>\nExample: <code>/chickenroad 10</code>")
        return
    amount, _amt_err = resolve_bet_amount(user_id, args[0])
    if _amt_err == "invalid_number":
        send_message(chat_id, f"{WARN_EMOJI} Invalid amount. Example: <code>/chickenroad 10</code>")
        return
    if _amt_err == "rate_unavailable":
        send_message(chat_id, f"{WARN_EMOJI} Currency rate temporarily unavailable - try again shortly, or run /currency to switch to USD.")
        return
    if amount < MIN_BET:
        send_message(chat_id, f"{WARN_EMOJI} Minimum bet is ${MIN_BET:.2f}")
        return
    if amount > MAX_BET:
        send_message(chat_id, f"{WARN_EMOJI} Maximum bet is ${MAX_BET:.2f}")
        return
    balance = get_balance(user_id)
    if amount > balance:
        send_message(chat_id, f"{WARN_EMOJI} Insufficient balance. Your balance: ${balance:.2f}")
        return
    if not APP_URL:
        send_message(
            chat_id,
            f"{WARN_EMOJI} Chicken Road's Mini App isn't configured yet. The bot owner needs to "
            "set the <code>APP_URL</code> environment variable to this service's public HTTPS URL."
        )
        return
    if user_id in user_active_chicken:
        send_message(chat_id, f"{WARN_EMOJI} You already have an active Chicken Road game! Finish it in the app first.")
        return

    if chat_type != "private":
        if not BOT_USERNAME:
            send_message(chat_id, f"{WARN_EMOJI} Bot isn't fully started yet - try again in a few seconds.")
            return
        invite_token = secrets.token_urlsafe(8)
        with CHICKEN_INVITE_LOCK:
            active_chicken_invites[invite_token] = {
                "owner_id": user_id, "owner_name": username, "amount": amount, "used": False,
            }
        threading.Thread(target=chicken_invite_expiry, args=(invite_token,), daemon=True).start()
        deep_link = f"https://t.me/{BOT_USERNAME}?start=chi_{invite_token}"
        send_message(
            chat_id,
            f"{CHICKEN_EMOJI} <b>Chicken Road</b> — {mention(user_id, username)}\n\n"
            f"Bet: <b>${amount:.2f}</b>\n\n"
            f"Chicken Road only runs in DM. This button is one-time use, only for {mention(user_id, username)}:",
            reply_markup={"inline_keyboard": [[{"text": "Play in DM", "icon_custom_emoji_id": "6334536360224884639", "url": deep_link}]]}
        )
        return

    with CHICKEN_LOCK:
        if user_id in user_active_chicken:
            send_message(chat_id, f"{WARN_EMOJI} You already have an active Chicken Road game! Finish it in the app first.")
            return
        client_seed = get_client_seed(user_id)
        nonce = next_nonce(user_id)
        server_seed = secrets.token_hex(16)
        token = secrets.token_urlsafe(12)
        active_chicken_games[token] = {
            "token": token, "user_id": user_id, "chat_id": chat_id, "username": username,
            "amount": amount, "difficulty": CHICKEN_DEFAULT_DIFFICULTY,
            "server_seed": server_seed, "client_seed": client_seed, "nonce": nonce,
            "lane_index": 0, "current_multiplier": 1.0, "hit_lane": None, "cashout_multiplier": None,
            "status": "pending",
        }
        user_active_chicken[user_id] = token

    threading.Thread(target=chicken_pending_expiry, args=(token,), daemon=True).start()

    send_message(
        chat_id,
        f"{CHICKEN_EMOJI} <b>Chicken Road</b> — {mention(user_id, username)}\n\n"
        f"Bet: <b>${amount:.2f}</b>\n"
        f"Balance: <b>${get_balance(user_id):.2f}</b>\n\n"
        f"Open the road below, pick a difficulty, then press <b>Go</b> "
        f"(that's when your bet is placed):",
        reply_markup=chicken_mini_app_keyboard(token)
    )


# ---------------------------------------------------------------------------
# DICE
# ---------------------------------------------------------------------------
# Same architecture as Crash/Chicken Road: this module only holds game state +
# rules, dice_web.py is the thin HTTP wrapper the Mini App page talks to.
#
# Unlike Crash/Chicken Road there's no ongoing round to watch - the player
# picks Roll Under or Roll Over and a target (2.00-98.00) on a slider, the
# Mini App shows the live fair multiplier for whatever target is currently
# selected, and one tap rolls it. The server_seed/client_seed/nonce (and
# therefore the roll itself) are locked in the moment /dice is typed, before
# the player even opens the app or picks a target - target/direction only
# change how that already-fixed roll is interpreted and paid out, they can
# never change what the roll itself turns out to be.

DICE_HOUSE_EDGE = 0.01
DICE_MIN_TARGET = 2.00
DICE_MAX_TARGET = 98.00
DICE_DEFAULT_TARGET = 50.00
DICE_DEFAULT_DIRECTION = "under"

active_dice_games = {}   # token -> game dict
user_active_dice = {}    # user_id -> token (one live Dice round per user)
DICE_LOCK = threading.Lock()


def dice_multiplier(win_chance_pct, house_edge=DICE_HOUSE_EDGE):
    """Fair multiplier for a win chance given as a percentage (0-100) - same
    fair-odds construction as every other game in this file."""
    if win_chance_pct <= 0:
        return 0.0
    return math.floor(((1 - house_edge) / (win_chance_pct / 100)) * 100) / 100


def dice_roll_value(server_seed, client_seed, nonce):
    """Provably-fair roll in [0.00, 99.99] - same seed/hash convention used
    everywhere else in this file (roulette/limbo/mines/towers/keno/crash/
    chicken road)."""
    h = hashlib.sha256(f"{server_seed}:{client_seed}:{nonce}".encode()).hexdigest()
    r = int(h[:13], 16) / float(1 << 52)
    return math.floor(r * 10000) / 100


def _dice_clean_direction(requested_direction):
    return requested_direction if requested_direction in ("under", "over") else DICE_DEFAULT_DIRECTION


def _dice_clean_target(requested_target):
    try:
        target = round(float(requested_target), 2)
    except (TypeError, ValueError):
        return DICE_DEFAULT_TARGET
    return min(max(target, DICE_MIN_TARGET), DICE_MAX_TARGET)


def dice_roll(token, requested_amount=None, requested_direction=None, requested_target=None):
    """Called by the Mini App's Roll button. Bet, direction, and target are
    all locked in here (not when /dice was typed) - same convention as
    crash_start/chicken_start, and for the same reason: this is the only
    place that should ever touch the player's balance for this round. The
    roll itself was already fixed the moment /dice was typed though - this
    just decides how to score/pay out that already-fixed number."""
    with DICE_LOCK:
        game = active_dice_games.get(token)
        if not game:
            return {"ok": False, "error": "not_found"}
        if game["status"] != "pending":
            return {"ok": False, "error": "already_started"}

        amount = game["amount"]
        if requested_amount is not None:
            try:
                requested_amount = round(float(requested_amount), 2)
            except (TypeError, ValueError):
                requested_amount = None
            if requested_amount is not None and requested_amount > 0:
                if requested_amount < MIN_BET:
                    return {"ok": False, "error": "min_bet"}
                if requested_amount > MAX_BET:
                    return {"ok": False, "error": "max_bet"}
                amount = requested_amount

        direction = _dice_clean_direction(requested_direction)
        target = _dice_clean_target(requested_target)

        balance = get_balance(game["user_id"])
        if amount > balance:
            return {"ok": False, "error": "insufficient_balance"}

        win_chance = target if direction == "under" else (100 - target)
        multiplier = dice_multiplier(win_chance)

        adjust_balance(game["user_id"], -amount)
        roll = dice_roll_value(game["server_seed"], game["client_seed"], game["nonce"])
        win = (roll < target) if direction == "under" else (roll > target)
        payout = round(amount * multiplier, 2) if win else 0.0
        if win:
            adjust_balance(game["user_id"], payout)
            broadcast_win(game["user_id"], game["username"], "Dice", amount, payout, detail=f"Rolled {roll:.2f}, needed {'under' if direction == 'under' else 'over'} {target:.2f}")

        game.update({
            "amount": amount, "direction": direction, "target": target,
            "multiplier": multiplier, "roll": roll, "win": win, "payout": payout,
            "status": "done",
        })
        user_active_dice.pop(game["user_id"], None)
        user_id, chat_id, username = game["user_id"], game["chat_id"], game["username"]
        server_seed, client_seed, nonce = game["server_seed"], game["client_seed"], game["nonce"]

    verb = "under" if direction == "under" else "over"
    if win:
        send_message(
            chat_id,
            f"{DICE_EMOJI} <b>Dice</b> — {mention(user_id, username)}\n\n"
            f"Rolled <b>{roll:.2f}</b> (needed {verb} <b>{target:.2f}</b>)\n"
            f"${amount:.2f} \u2192 ${payout:.2f}\n\n"
            f"{cemoji('trophy')} You won <b>${payout - amount:.2f}</b>!\n"
            f"{cemoji('money')} Balance: <b>${get_balance(user_id):.2f}</b>",
            reply_markup=fair_button_keyboard("d", server_seed, client_seed, nonce, f"{direction}|{target}")
        )
    else:
        send_message(
            chat_id,
            f"{DICE_EMOJI} <b>Dice</b> — {mention(user_id, username)}\n\n"
            f"Rolled <b>{roll:.2f}</b> (needed {verb} <b>{target:.2f}</b>)\n\n"
            f"{cemoji('money')} You lost <b>${amount:.2f}</b>\n"
            f"{cemoji('money')} Balance: <b>${get_balance(user_id):.2f}</b>",
            reply_markup=fair_button_keyboard("d", server_seed, client_seed, nonce, f"{direction}|{target}")
        )

    return {
        "ok": True, "roll": roll, "win": win, "payout": payout, "amount": amount,
        "multiplier": multiplier, "direction": direction, "target": target,
        "balance": get_balance(user_id),
    }


def dice_again(token, requested_amount=None):
    """Resets a finished round back to 'pending' for another roll, with a
    fresh server seed + nonce (same idea as chicken_play_again) - so players
    don't need to leave the Mini App or re-run /dice for round two."""
    with DICE_LOCK:
        game = active_dice_games.get(token)
        if not game:
            return {"ok": False, "error": "not_found"}
        if game["status"] != "done":
            return {"ok": False, "error": "not_done"}

        amount = game["amount"]
        if requested_amount is not None:
            try:
                requested_amount = round(float(requested_amount), 2)
            except (TypeError, ValueError):
                requested_amount = None
            if requested_amount is not None and requested_amount > 0:
                if requested_amount < MIN_BET:
                    return {"ok": False, "error": "min_bet"}
                if requested_amount > MAX_BET:
                    return {"ok": False, "error": "max_bet"}
                amount = requested_amount

        user_id = game["user_id"]
        client_seed = get_client_seed(user_id)
        nonce = next_nonce(user_id)
        game.update({
            "amount": amount, "server_seed": secrets.token_hex(16),
            "client_seed": client_seed, "nonce": nonce,
            "direction": None, "target": None, "multiplier": None,
            "roll": None, "win": None, "payout": None,
            "status": "pending",
        })
        user_active_dice[user_id] = token
    return {"ok": True}


def dice_get_state(token):
    """Returns a JSON-able dict describing the current state of a round.
    Used on Mini App page load/reload."""
    with DICE_LOCK:
        game = active_dice_games.get(token)
        if not game:
            return None
        balance = get_balance(game["user_id"])
        if game["status"] == "pending":
            return {
                "status": "pending", "amount": game["amount"], "balance": balance,
                "min_target": DICE_MIN_TARGET, "max_target": DICE_MAX_TARGET,
                "house_edge": DICE_HOUSE_EDGE,
            }
        return {
            "status": "done", "amount": game["amount"], "balance": balance,
            "direction": game["direction"], "target": game["target"],
            "multiplier": game["multiplier"], "roll": game["roll"],
            "win": game["win"], "payout": game["payout"],
            "min_target": DICE_MIN_TARGET, "max_target": DICE_MAX_TARGET,
            "house_edge": DICE_HOUSE_EDGE,
        }


def dice_mini_app_keyboard(token):
    url = f"{APP_URL}/dice/{token}"
    return {"inline_keyboard": [[{"text": "Roll the Dice", "web_app": {"url": url}}]]}


DICE_PENDING_TIMEOUT = 300  # seconds a game stays open unstarted before it expires


def dice_pending_expiry(token):
    time.sleep(DICE_PENDING_TIMEOUT)
    with DICE_LOCK:
        game = active_dice_games.get(token)
        if not game or game["status"] != "pending":
            return
        active_dice_games.pop(token, None)
        user_active_dice.pop(game["user_id"], None)
        chat_id, user_id, username = game["chat_id"], game["user_id"], game["username"]

    send_message(
        chat_id,
        f"⌛ {mention(user_id, username)}, your Dice game expired unused. "
        f"Nothing was charged - start a new one with /dice."
    )


# ---------------------------------------------------------------------------
# DICE GROUP INVITES
# ---------------------------------------------------------------------------
# Same single-use, owner-locked deep-link pattern as Crash/Blackjack/Chicken
# Road's group invites - see handle_crash_command's comment for why this
# exists at all.

active_dice_invites = {}
DICE_INVITE_LOCK = threading.Lock()
DICE_INVITE_TIMEOUT = 300


def dice_invite_expiry(invite_token):
    time.sleep(DICE_INVITE_TIMEOUT)
    with DICE_INVITE_LOCK:
        active_dice_invites.pop(invite_token, None)


def handle_dice_command(chat_id, user_id, username, args, chat_type="private"):
    if not args:
        send_message(chat_id, f"{WARN_EMOJI} Usage: <code>/dice &lt;amount&gt;</code>\nExample: <code>/dice 10</code>")
        return
    amount, _amt_err = resolve_bet_amount(user_id, args[0])
    if _amt_err == "invalid_number":
        send_message(chat_id, f"{WARN_EMOJI} Invalid amount. Example: <code>/dice 10</code>")
        return
    if _amt_err == "rate_unavailable":
        send_message(chat_id, f"{WARN_EMOJI} Currency rate temporarily unavailable - try again shortly, or run /currency to switch to USD.")
        return
    if amount < MIN_BET:
        send_message(chat_id, f"{WARN_EMOJI} Minimum bet is ${MIN_BET:.2f}")
        return
    if amount > MAX_BET:
        send_message(chat_id, f"{WARN_EMOJI} Maximum bet is ${MAX_BET:.2f}")
        return
    balance = get_balance(user_id)
    if amount > balance:
        send_message(chat_id, f"{WARN_EMOJI} Insufficient balance. Your balance: ${balance:.2f}")
        return
    if not APP_URL:
        send_message(
            chat_id,
            f"{WARN_EMOJI} Dice's Mini App isn't configured yet. The bot owner needs to "
            "set the <code>APP_URL</code> environment variable to this service's public HTTPS URL."
        )
        return
    if user_id in user_active_dice:
        send_message(chat_id, f"{WARN_EMOJI} You already have an active Dice round! Finish it in the app first.")
        return

    if chat_type != "private":
        if not BOT_USERNAME:
            send_message(chat_id, f"{WARN_EMOJI} Bot isn't fully started yet - try again in a few seconds.")
            return
        invite_token = secrets.token_urlsafe(8)
        with DICE_INVITE_LOCK:
            active_dice_invites[invite_token] = {
                "owner_id": user_id, "owner_name": username, "amount": amount, "used": False,
            }
        threading.Thread(target=dice_invite_expiry, args=(invite_token,), daemon=True).start()
        deep_link = f"https://t.me/{BOT_USERNAME}?start=dri_{invite_token}"
        send_message(
            chat_id,
            f"{DICE_EMOJI} <b>Dice</b> — {mention(user_id, username)}\n\n"
            f"Bet: <b>${amount:.2f}</b>\n\n"
            f"Dice only runs in DM. This button is one-time use, only for {mention(user_id, username)}:",
            reply_markup={"inline_keyboard": [[{"text": "Play in DM", "url": deep_link}]]}
        )
        return

    with DICE_LOCK:
        if user_id in user_active_dice:
            send_message(chat_id, f"{WARN_EMOJI} You already have an active Dice round! Finish it in the app first.")
            return
        client_seed = get_client_seed(user_id)
        nonce = next_nonce(user_id)
        server_seed = secrets.token_hex(16)
        token = secrets.token_urlsafe(12)
        active_dice_games[token] = {
            "token": token, "user_id": user_id, "chat_id": chat_id, "username": username,
            "amount": amount, "server_seed": server_seed, "client_seed": client_seed, "nonce": nonce,
            "direction": None, "target": None, "multiplier": None, "roll": None, "win": None, "payout": None,
            "status": "pending",
        }
        user_active_dice[user_id] = token

    threading.Thread(target=dice_pending_expiry, args=(token,), daemon=True).start()

    send_message(
        chat_id,
        f"{DICE_EMOJI} <b>Dice</b> — {mention(user_id, username)}\n\n"
        f"Bet: <b>${amount:.2f}</b>\n"
        f"Balance: <b>${get_balance(user_id):.2f}</b>\n\n"
        f"Open the app below, pick Roll Under or Roll Over and your target, then press <b>Roll</b> "
        f"(that's when your bet is placed):",
        reply_markup=dice_mini_app_keyboard(token)
    )


# ---------------------------------------------------------------------------
# DB SYNC — every active-game dict in this file (Mines/Towers/Keno are
# keyed by user_id; Crash/Blackjack/Dice/ChickenRoad are keyed by a token,
# with a companion user_id->token pointer dict) gets periodically snapshotted
# into Postgres's game_sessions table. This is a background sweep rather
# than a save-on-every-mutation approach, so adding persistence didn't
# require touching every single betting/hit/reveal code path across seven
# different games - the tradeoff is a restart can lose up to ~4 seconds of
# the most recent action in whatever game was mid-round at that instant.
# ---------------------------------------------------------------------------

# (game_type, dict_ref, keyed_by_token: bool, pointer_dict_ref_or_None)
_SYNCED_GAME_STORES = None  # populated lazily so this runs after every
                             # active_*_games dict above has been declared


def _synced_game_stores():
    global _SYNCED_GAME_STORES
    if _SYNCED_GAME_STORES is None:
        _SYNCED_GAME_STORES = [
            ("mines",   active_mines_games,   False, None),
            ("towers",  active_towers_games,  False, None),
            ("keno",    active_keno_games,    False, None),
            ("crash",   active_crash_games,   True,  user_active_crash),
            ("blackjack", active_blackjack_games, True, user_active_blackjack),
            ("chickenroad", active_chicken_games, True, user_active_chicken),
            ("dice",    active_dice_games,    True,  user_active_dice),
        ]
    return _SYNCED_GAME_STORES


def restore_state_from_db():
    """Called once at startup - repopulates every in-memory cache (wallets,
    fairness seeds, active games) from Postgres, so a restart resumes
    exactly where the last run left off instead of wiping everyone's
    balance and mid-round games back to zero."""
    try:
        loaded_wallets = db.load_all_wallets()
        wallets.update(loaded_wallets)
        print(f"💾 Restored {len(loaded_wallets)} wallet(s) from DB.")
    except Exception as e:
        print(f"⚠️ Failed to restore wallets: {e}")

    try:
        seeds, loaded_nonces = db.load_all_fairness()
        client_seeds.update(seeds)
        nonces.update(loaded_nonces)
        print(f"💾 Restored {len(seeds)} fairness seed(s) from DB.")
    except Exception as e:
        print(f"⚠️ Failed to restore fairness seeds: {e}")

    try:
        flows = db.load_all_payment_flows()
        for uid, flow_type, state in flows:
            if flow_type == "deposit":
                pending_deposit_flow[uid] = state
            elif flow_type == "withdraw":
                pending_withdraw_flow[uid] = state
        print(f"💾 Restored {len(flows)} in-progress deposit/withdraw flow(s) from DB.")
    except Exception as e:
        print(f"⚠️ Failed to restore payment flows: {e}")

    try:
        currencies, usernames = db.load_all_user_prefs()
        user_display_currency.update(currencies)
        known_usernames.update(usernames)
        print(f"💾 Restored {len(currencies)} currency pref(s) and {len(usernames)} username(s) from DB.")
    except Exception as e:
        print(f"⚠️ Failed to restore user prefs: {e}")

    try:
        all_ids = db.load_all_user_ids()
        all_known_user_ids.update(all_ids)
        print(f"💾 Restored {len(all_ids)} known user(s) for /broadcast.")
    except Exception as e:
        print(f"⚠️ Failed to restore known users: {e}")

    try:
        deposits_loaded = db.load_all_pending_deposits()
        pending_deposits.update(deposits_loaded)
        print(f"💾 Restored {len(deposits_loaded)} pending deposit(s) from DB.")
    except Exception as e:
        print(f"⚠️ Failed to restore pending deposits: {e}")

    for game_type, store_dict, keyed_by_token, pointer_dict in _synced_game_stores():
        try:
            games = db.load_all_games(game_type)
            if keyed_by_token:
                # Token keys are strings both in memory and from the DB - no conversion needed.
                store_dict.update(games)
                if pointer_dict is not None:
                    pointers = db.load_all_active_pointers(game_type)
                    pointer_dict.update(pointers)  # user_id column is already BIGINT -> Python int
            else:
                # These dicts are keyed by integer user_id in memory, but
                # JSON round-tripping always turns dict keys into strings -
                # convert back or every lookup like active_mines_games[user_id]
                # would silently miss and "lose" the player's in-progress game.
                store_dict.update({int(k): v for k, v in games.items()})
            if games:
                print(f"💾 Restored {len(games)} active {game_type} game(s) from DB.")
        except Exception as e:
            print(f"⚠️ Failed to restore {game_type} games: {e}")


def periodic_db_sync_loop():
    """Runs forever in a background thread once DB_ENABLED. Every ~4
    seconds: snapshot every active game into Postgres, and clean up rows
    for games that have since been removed from memory (cashed out,
    finished and cleared, expired, etc) so the table doesn't grow
    unbounded."""
    while True:
        time.sleep(4)
        if not DB_ENABLED:
            continue
        for game_type, store_dict, keyed_by_token, pointer_dict in _synced_game_stores():
            try:
                # Snapshot every currently-active game.
                snapshot = dict(store_dict)
                for key, state in snapshot.items():
                    token = key if keyed_by_token else str(key)
                    user_id = state.get("user_id", key if not keyed_by_token else None)
                    if user_id is None:
                        continue
                    db.save_game(game_type, token, user_id, state)

                # Clean up any DB rows for games no longer in memory (they
                # finished/cashed-out/expired since the last sync).
                db_tokens = set(db.load_all_games(game_type).keys())
                memory_tokens = {str(k) for k in snapshot.keys()}
                stale = db_tokens - memory_tokens
                for token in stale:
                    db.delete_game(game_type, token)

                # Keep the user->token pointer table in sync too.
                if keyed_by_token and pointer_dict is not None:
                    pointer_snapshot = dict(pointer_dict)
                    for user_id, token in pointer_snapshot.items():
                        db.set_active_pointer(game_type, user_id, token)
                    db_pointers = db.load_all_active_pointers(game_type)
                    for user_id in set(db_pointers.keys()) - set(pointer_snapshot.keys()):
                        db.clear_active_pointer(game_type, user_id)
            except Exception as e:
                print(f"⚠️ DB sync error for {game_type}: {e}")


def main():
    global DB_ENABLED

    if not BOT_TOKEN or BOT_TOKEN == "PASTE_YOUR_BOT_TOKEN_HERE":
        print("⚠️  BOT_TOKEN not set. Add it as an environment variable.")
        while True:
            time.sleep(60)

    print("🎰 Traqd Casino running...")

    try:
        commands = [
            {"command": "start", "description": "Welcome & quick intro"},
            {"command": "deposit", "description": "Fund your account (crypto)"},
            {"command": "withdraw", "description": "Withdraw your balance"},
            {"command": "balance", "description": "Check your balance"},
            {"command": "currency", "description": "Set display currency (USD/INR/LTC)"},
            {"command": "blackjack", "description": "Play Blackjack"},
            {"command": "dice", "description": "Play Dice"},
            {"command": "crash", "description": "Play Crash"},
            {"command": "chickenroad", "description": "Play Chicken Road"},
            {"command": "roulette", "description": "Play Roulette"},
            {"command": "coinflip", "description": "Play Coinflip"},
            {"command": "towers", "description": "Play Towers"},
            {"command": "mines", "description": "Play Mines"},
            {"command": "keno", "description": "Play Keno"},
            {"command": "limbo", "description": "Play Limbo"},
            {"command": "seed", "description": "View your provably-fair seed"},
            {"command": "newseed", "description": "Rotate your provably-fair seed"},
            {"command": "help", "description": "Every game & command"},
        ]
        result = api_call("setMyCommands", commands=json.dumps(commands))
        if result.get("ok"):
            print("✅ Bot command menu registered with Telegram.")
        else:
            print(f"⚠️  setMyCommands returned: {result}")
    except Exception as e:
        print(f"⚠️  Could not register command menu: {e}")

    if NOWPAYMENTS_API_KEY:
        missing = [
            name for name, val in [
                ("NOWPAYMENTS_EMAIL", NOWPAYMENTS_EMAIL),
                ("NOWPAYMENTS_PASSWORD", NOWPAYMENTS_PASSWORD),
                ("NOWPAYMENTS_2FA_SECRET", NOWPAYMENTS_2FA_SECRET),
            ] if not val
        ]
        if missing:
            print(
                f"⚠️  Withdrawals are only PARTIALLY automated - missing {', '.join(missing)}. "
                "Payouts will be created but stuck awaiting manual 2FA verification in the "
                "NowPayments dashboard until these are set."
            )
        else:
            print("💸 Withdrawals are fully automated (JWT + self-verified 2FA configured).")

    # ------------------------------------------------------------------
    # DATABASE — connect + create schema + restore state from the last run.
    # If this fails for any reason (Neon down, DATABASE_URL missing,
    # psycopg2 not installed), the bot still starts and runs exactly like
    # the old in-memory-only build - it just won't survive a restart.
    # ------------------------------------------------------------------
    if _DB_MODULE_AVAILABLE and DATABASE_URL:
        try:
            db.init(DATABASE_URL)
            db.migrate()
            DB_ENABLED = True
            print("💾 Connected to Postgres - state will persist across restarts.")
            restore_state_from_db()
        except Exception as e:
            DB_ENABLED = False
            print(f"⚠️ Database unavailable ({e}) - running in-memory only, state will NOT survive a restart.")
    else:
        print("⚠️ DATABASE_URL not set (or psycopg2 missing) - running in-memory only.")

    # Deferred import: by the time main() runs, every name crash_web.py
    # needs (crash_get_state, active_crash_games, CRASH_GROWTH_RATE, ...)
    # is already defined at module level, avoiding a circular-import issue.
    import crash_web
    import blackjack_web
    import dice_web
    import chickenroad_web
    import nowpayments_web

    this_module = __import__("sys").modules[__name__]
    crash_web.init(this_module)
    blackjack_web.init(this_module)
    dice_web.init(this_module)
    chickenroad_web.init(this_module)
    nowpayments_web.init(this_module)

    # Blackjack/Dice/ChickenRoad/NowPayments-IPN don't run their own
    # servers - they piggyback on crash_web's single HTTP server via
    # do_GET/do_POST delegation, since Railway only exposes one PORT per
    # service.
    crash_web.init_extra_modules([blackjack_web, dice_web, chickenroad_web, nowpayments_web])
    crash_web.start_in_background()

    if DB_ENABLED:
        threading.Thread(target=periodic_db_sync_loop, daemon=True, name="db-sync").start()
        print("💾 Background DB sync started (every 4s).")

    if APP_URL:
        print(f"🚀 Crash Mini App serving at {APP_URL}/crash/<token>")
        print(f"🃏 Blackjack Mini App serving at {APP_URL}/blackjack/<token>")
        print(f"🎲 Dice Mini App serving at {APP_URL}/dice/<token>")
        print(f"🐔 Chicken Road Mini App serving at {APP_URL}/chickenroad/<token>")
    else:
        print("⚠️  APP_URL not set - Mini Apps will tell players it's not configured yet.")

    fetch_bot_username()
    offset = None
    while True:
        try:
            params = {"timeout": 30}
            if offset:
                params["offset"] = offset
            resp = SESSION.get(f"{API}/getUpdates", params=params, timeout=35)
            data = resp.json()

            if not data.get("ok"):
                print(f"Error polling: {data}")
                time.sleep(2)
                continue

            for update in data.get("result", []):
                offset = update["update_id"] + 1

                def process(update=update):
                    try:
                        if "message" in update:
                            handle_message(update["message"])
                        elif "callback_query" in update:
                            handle_callback(update["callback_query"])
                    except Exception as e:
                        print(f"Error handling update: {e}")

                threading.Thread(target=process, daemon=True).start()

        except requests.exceptions.RequestException as e:
            print(f"Network error: {e}, retrying...")
            time.sleep(3)
        except KeyboardInterrupt:
            print("\n🛑 Stopped.")
            break
        except Exception as e:
            print(f"Unexpected error: {e}")
            time.sleep(2)


if __name__ == "__main__":
    main()
