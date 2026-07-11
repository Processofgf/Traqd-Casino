"""
db.py — Neon Postgres persistence layer for Traqd Casino.

Design: rather than a bespoke table per game (mines_games, towers_games,
crash_games, ...), every game's state dict is stored as JSONB in ONE
`game_sessions` table, keyed by (game_type, token). This matches how the
bot already models games in memory (plain Python dicts), so persistence
becomes "save this dict" / "load this dict" instead of a full ORM rewrite
of every game module. Wallets, deposits, and withdrawals get real typed
columns since those are financial records worth stricter shape.

Connection: a small threadsafe connection pool (psycopg2's
ThreadedConnectionPool), since every Telegram update is handled in its own
thread (see main.py's polling loop) and games can run concurrent DB calls.
"""

import json
import threading
from contextlib import contextmanager


class _GameStateEncoder(json.JSONEncoder):
    """Game state dicts sometimes contain Python `set` objects (e.g. Mines'
    revealed tiles, Keno's selected numbers) which json.dumps can't handle
    natively. Sets get tagged so the loader can convert them back on read,
    instead of silently flattening them into a plain list that would be
    ambiguous with an actually-a-list field."""
    def default(self, obj):
        if isinstance(obj, set):
            return {"__set__": list(obj)}
        return super().default(obj)


def _restore_sets(obj):
    """Recursively reverses _GameStateEncoder's set-tagging after a
    json.load, so callers get back the exact same shape they saved
    (sets as sets, not lists)."""
    if isinstance(obj, dict):
        if set(obj.keys()) == {"__set__"}:
            return set(obj["__set__"])
        return {k: _restore_sets(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_restore_sets(v) for v in obj]
    return obj


try:
    import psycopg2
    import psycopg2.extras
    from psycopg2.pool import ThreadedConnectionPool
    _PSYCOPG_AVAILABLE = True
except ImportError:
    _PSYCOPG_AVAILABLE = False

_pool = None
_DB_LOCK = threading.Lock()


def init(database_url, minconn=1, maxconn=10):
    global _pool
    if not _PSYCOPG_AVAILABLE:
        raise RuntimeError("psycopg2 is not installed - add psycopg2-binary to requirements.txt")
    if not database_url:
        raise RuntimeError("DATABASE_URL is empty")
    dsn = database_url
    if "sslmode=" not in dsn:
        sep = "&" if "?" in dsn else "?"
        dsn = f"{dsn}{sep}sslmode=require"
    _pool = ThreadedConnectionPool(minconn, maxconn, dsn)


def is_enabled():
    return _pool is not None


@contextmanager
def _conn():
    if _pool is None:
        raise RuntimeError("db.init() was never called")
    conn = _pool.getconn()
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        _pool.putconn(conn)


@contextmanager
def _cursor():
    with _conn() as conn:
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        try:
            yield cur
        finally:
            cur.close()


SCHEMA = """
CREATE TABLE IF NOT EXISTS wallets (
    user_id                 BIGINT PRIMARY KEY,
    real_balance            NUMERIC(18,2) NOT NULL DEFAULT 0,
    bonus_balance           NUMERIC(18,2) NOT NULL DEFAULT 0,
    wager_required          NUMERIC(18,2) NOT NULL DEFAULT 0,
    wager_progress          NUMERIC(18,2) NOT NULL DEFAULT 0,
    deposit_wager_required  NUMERIC(18,2) NOT NULL DEFAULT 0,
    deposit_wager_progress  NUMERIC(18,2) NOT NULL DEFAULT 0,
    has_deposited           BOOLEAN NOT NULL DEFAULT FALSE,
    updated_at              TIMESTAMPTZ NOT NULL DEFAULT now()
);

-- Forward-compatible with databases created before the deposit-wager
-- columns existed - CREATE TABLE IF NOT EXISTS above won't add columns to
-- an already-existing table, so add them explicitly here too.
ALTER TABLE wallets ADD COLUMN IF NOT EXISTS deposit_wager_required NUMERIC(18,2) NOT NULL DEFAULT 0;
ALTER TABLE wallets ADD COLUMN IF NOT EXISTS deposit_wager_progress NUMERIC(18,2) NOT NULL DEFAULT 0;

CREATE TABLE IF NOT EXISTS fairness (
    user_id      BIGINT PRIMARY KEY,
    client_seed  TEXT NOT NULL,
    nonce        INTEGER NOT NULL DEFAULT 0,
    updated_at   TIMESTAMPTZ NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS game_sessions (
    game_type   TEXT NOT NULL,
    token       TEXT NOT NULL,
    user_id     BIGINT NOT NULL,
    state       JSONB NOT NULL,
    created_at  TIMESTAMPTZ NOT NULL DEFAULT now(),
    updated_at  TIMESTAMPTZ NOT NULL DEFAULT now(),
    PRIMARY KEY (game_type, token)
);
CREATE INDEX IF NOT EXISTS idx_game_sessions_user ON game_sessions(user_id, game_type);

CREATE TABLE IF NOT EXISTS active_game_pointers (
    game_type  TEXT NOT NULL,
    user_id    BIGINT NOT NULL,
    token      TEXT NOT NULL,
    PRIMARY KEY (game_type, user_id)
);

CREATE TABLE IF NOT EXISTS deposits (
    payment_id  TEXT PRIMARY KEY,
    user_id     BIGINT NOT NULL,
    chat_id     BIGINT NOT NULL,
    username    TEXT,
    usd_amount  NUMERIC(18,2) NOT NULL,
    coin        TEXT NOT NULL,
    status      TEXT NOT NULL DEFAULT 'pending',
    created_at  TIMESTAMPTZ NOT NULL DEFAULT now(),
    credited_at TIMESTAMPTZ
);

CREATE TABLE IF NOT EXISTS withdrawals (
    withdraw_id TEXT PRIMARY KEY,
    user_id     BIGINT NOT NULL,
    chat_id     BIGINT NOT NULL,
    username    TEXT,
    usd_amount  NUMERIC(18,2) NOT NULL,
    coin        TEXT NOT NULL,
    address     TEXT NOT NULL,
    status      TEXT NOT NULL DEFAULT 'pending',
    created_at  TIMESTAMPTZ NOT NULL DEFAULT now(),
    updated_at  TIMESTAMPTZ NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS payment_flow_state (
    user_id    BIGINT PRIMARY KEY,
    flow_type  TEXT NOT NULL,
    state      JSONB NOT NULL,
    updated_at TIMESTAMPTZ NOT NULL DEFAULT now()
);

CREATE TABLE IF NOT EXISTS user_prefs (
    user_id           BIGINT PRIMARY KEY,
    username          TEXT,
    display_currency  TEXT NOT NULL DEFAULT 'usd',
    updated_at        TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE INDEX IF NOT EXISTS idx_user_prefs_username ON user_prefs(username);
"""


def migrate():
    with _cursor() as cur:
        cur.execute(SCHEMA)


def load_wallet(user_id):
    with _cursor() as cur:
        cur.execute("SELECT * FROM wallets WHERE user_id = %s", (user_id,))
        row = cur.fetchone()
        if not row:
            return None
        return {
            "real": float(row["real_balance"]),
            "bonus": float(row["bonus_balance"]),
            "wager_required": float(row["wager_required"]),
            "wager_progress": float(row["wager_progress"]),
            "deposit_wager_required": float(row.get("deposit_wager_required") or 0),
            "deposit_wager_progress": float(row.get("deposit_wager_progress") or 0),
            "has_deposited": row["has_deposited"],
        }


def save_wallet(user_id, wallet):
    with _cursor() as cur:
        cur.execute("""
            INSERT INTO wallets (
                user_id, real_balance, bonus_balance, wager_required, wager_progress,
                deposit_wager_required, deposit_wager_progress, has_deposited, updated_at
            )
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, now())
            ON CONFLICT (user_id) DO UPDATE SET
                real_balance = EXCLUDED.real_balance,
                bonus_balance = EXCLUDED.bonus_balance,
                wager_required = EXCLUDED.wager_required,
                wager_progress = EXCLUDED.wager_progress,
                deposit_wager_required = EXCLUDED.deposit_wager_required,
                deposit_wager_progress = EXCLUDED.deposit_wager_progress,
                has_deposited = EXCLUDED.has_deposited,
                updated_at = now()
        """, (
            user_id, wallet["real"], wallet["bonus"],
            wallet["wager_required"], wallet["wager_progress"],
            wallet.get("deposit_wager_required", 0.0), wallet.get("deposit_wager_progress", 0.0),
            wallet["has_deposited"],
        ))


def load_all_wallets():
    with _cursor() as cur:
        cur.execute("SELECT * FROM wallets")
        rows = cur.fetchall()
        return {
            row["user_id"]: {
                "real": float(row["real_balance"]),
                "bonus": float(row["bonus_balance"]),
                "wager_required": float(row["wager_required"]),
                "wager_progress": float(row["wager_progress"]),
                "deposit_wager_required": float(row.get("deposit_wager_required") or 0),
                "deposit_wager_progress": float(row.get("deposit_wager_progress") or 0),
                "has_deposited": row["has_deposited"],
            }
            for row in rows
        }


def load_fairness(user_id):
    with _cursor() as cur:
        cur.execute("SELECT client_seed, nonce FROM fairness WHERE user_id = %s", (user_id,))
        row = cur.fetchone()
        if not row:
            return None
        return {"client_seed": row["client_seed"], "nonce": row["nonce"]}


def save_fairness(user_id, client_seed, nonce):
    with _cursor() as cur:
        cur.execute("""
            INSERT INTO fairness (user_id, client_seed, nonce, updated_at)
            VALUES (%s, %s, %s, now())
            ON CONFLICT (user_id) DO UPDATE SET
                client_seed = EXCLUDED.client_seed,
                nonce = EXCLUDED.nonce,
                updated_at = now()
        """, (user_id, client_seed, nonce))


def load_all_fairness():
    with _cursor() as cur:
        cur.execute("SELECT user_id, client_seed, nonce FROM fairness")
        rows = cur.fetchall()
        seeds = {row["user_id"]: row["client_seed"] for row in rows}
        nonces = {row["user_id"]: row["nonce"] for row in rows}
        return seeds, nonces


def save_game(game_type, token, user_id, state_dict):
    with _cursor() as cur:
        cur.execute("""
            INSERT INTO game_sessions (game_type, token, user_id, state, updated_at)
            VALUES (%s, %s, %s, %s, now())
            ON CONFLICT (game_type, token) DO UPDATE SET
                state = EXCLUDED.state,
                updated_at = now()
        """, (game_type, token, user_id, json.dumps(state_dict, cls=_GameStateEncoder)))


def load_game(game_type, token):
    with _cursor() as cur:
        cur.execute(
            "SELECT state FROM game_sessions WHERE game_type = %s AND token = %s",
            (game_type, token)
        )
        row = cur.fetchone()
        return _restore_sets(row["state"]) if row else None


def delete_game(game_type, token):
    with _cursor() as cur:
        cur.execute(
            "DELETE FROM game_sessions WHERE game_type = %s AND token = %s",
            (game_type, token)
        )


def load_all_games(game_type):
    with _cursor() as cur:
        cur.execute("SELECT token, state FROM game_sessions WHERE game_type = %s", (game_type,))
        return {row["token"]: _restore_sets(row["state"]) for row in cur.fetchall()}


def set_active_pointer(game_type, user_id, token):
    with _cursor() as cur:
        cur.execute("""
            INSERT INTO active_game_pointers (game_type, user_id, token)
            VALUES (%s, %s, %s)
            ON CONFLICT (game_type, user_id) DO UPDATE SET token = EXCLUDED.token
        """, (game_type, user_id, token))


def clear_active_pointer(game_type, user_id):
    with _cursor() as cur:
        cur.execute(
            "DELETE FROM active_game_pointers WHERE game_type = %s AND user_id = %s",
            (game_type, user_id)
        )


def load_all_active_pointers(game_type):
    with _cursor() as cur:
        cur.execute(
            "SELECT user_id, token FROM active_game_pointers WHERE game_type = %s",
            (game_type,)
        )
        return {row["user_id"]: row["token"] for row in cur.fetchall()}


def save_pending_deposit(payment_id, user_id, chat_id, username, usd_amount, coin):
    with _cursor() as cur:
        cur.execute("""
            INSERT INTO deposits (payment_id, user_id, chat_id, username, usd_amount, coin, status)
            VALUES (%s, %s, %s, %s, %s, %s, 'pending')
            ON CONFLICT (payment_id) DO NOTHING
        """, (payment_id, user_id, chat_id, username, usd_amount, coin))


def load_pending_deposit(payment_id):
    with _cursor() as cur:
        cur.execute("SELECT * FROM deposits WHERE payment_id = %s AND status = 'pending'", (payment_id,))
        row = cur.fetchone()
        if not row:
            return None
        return {
            "user_id": row["user_id"], "chat_id": row["chat_id"],
            "username": row["username"], "usd_amount": float(row["usd_amount"]),
            "coin": row["coin"],
        }


def mark_deposit_credited(payment_id):
    with _cursor() as cur:
        cur.execute("""
            UPDATE deposits SET status = 'credited', credited_at = now()
            WHERE payment_id = %s AND status = 'pending'
            RETURNING payment_id
        """, (payment_id,))
        return cur.fetchone() is not None


def load_all_pending_deposits():
    with _cursor() as cur:
        cur.execute("SELECT * FROM deposits WHERE status = 'pending'")
        rows = cur.fetchall()
        return {
            row["payment_id"]: {
                "user_id": row["user_id"], "chat_id": row["chat_id"],
                "username": row["username"], "usd_amount": float(row["usd_amount"]),
                "coin": row["coin"], "created_at": row["created_at"].timestamp(),
            }
            for row in rows
        }


def save_withdrawal(withdraw_id, user_id, chat_id, username, usd_amount, coin, address, status="pending"):
    with _cursor() as cur:
        cur.execute("""
            INSERT INTO withdrawals (withdraw_id, user_id, chat_id, username, usd_amount, coin, address, status)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
        """, (withdraw_id, user_id, chat_id, username, usd_amount, coin, address, status))


def update_withdrawal_status(withdraw_id, status):
    with _cursor() as cur:
        cur.execute(
            "UPDATE withdrawals SET status = %s, updated_at = now() WHERE withdraw_id = %s",
            (status, withdraw_id)
        )


def save_payment_flow(user_id, flow_type, state_dict):
    with _cursor() as cur:
        cur.execute("""
            INSERT INTO payment_flow_state (user_id, flow_type, state, updated_at)
            VALUES (%s, %s, %s, now())
            ON CONFLICT (user_id) DO UPDATE SET
                flow_type = EXCLUDED.flow_type,
                state = EXCLUDED.state,
                updated_at = now()
        """, (user_id, flow_type, json.dumps(state_dict)))


def load_payment_flow(user_id, flow_type):
    with _cursor() as cur:
        cur.execute(
            "SELECT state FROM payment_flow_state WHERE user_id = %s AND flow_type = %s",
            (user_id, flow_type)
        )
        row = cur.fetchone()
        return row["state"] if row else None


def load_all_payment_flows():
    """Returns [(user_id, flow_type, state_dict), ...] for every
    in-progress /deposit or /withdraw flow, so main() can repopulate
    pending_deposit_flow / pending_withdraw_flow after a restart instead
    of silently dropping users mid-flow."""
    with _cursor() as cur:
        cur.execute("SELECT user_id, flow_type, state FROM payment_flow_state")
        return [(row["user_id"], row["flow_type"], row["state"]) for row in cur.fetchall()]


def clear_payment_flow(user_id):
    with _cursor() as cur:
        cur.execute("DELETE FROM payment_flow_state WHERE user_id = %s", (user_id,))


def touch_user(user_id):
    """Ensures a user_prefs row exists for this user_id even if they have
    no @username and haven't touched currency prefs - so /broadcast can
    reach everyone who's ever messaged the bot, not just depositors."""
    with _cursor() as cur:
        cur.execute("""
            INSERT INTO user_prefs (user_id, updated_at)
            VALUES (%s, now())
            ON CONFLICT (user_id) DO NOTHING
        """, (user_id,))


def save_user_currency(user_id, currency):
    with _cursor() as cur:
        cur.execute("""
            INSERT INTO user_prefs (user_id, display_currency, updated_at)
            VALUES (%s, %s, now())
            ON CONFLICT (user_id) DO UPDATE SET
                display_currency = EXCLUDED.display_currency,
                updated_at = now()
        """, (user_id, currency))


def save_username(user_id, username):
    with _cursor() as cur:
        cur.execute("""
            INSERT INTO user_prefs (user_id, username, updated_at)
            VALUES (%s, %s, now())
            ON CONFLICT (user_id) DO UPDATE SET
                username = EXCLUDED.username,
                updated_at = now()
        """, (user_id, username))


def load_all_user_prefs():
    """Returns (currencies, usernames) where currencies is
    {user_id: 'usd'/'inr'/'ltc'} and usernames is
    {lowercased_username: user_id}, both rebuilt from the DB on startup."""
    with _cursor() as cur:
        cur.execute("SELECT user_id, username, display_currency FROM user_prefs")
        rows = cur.fetchall()
        currencies = {row["user_id"]: row["display_currency"] for row in rows if row["display_currency"]}
        usernames = {row["username"].lower(): row["user_id"] for row in rows if row["username"]}
        return currencies, usernames


def load_all_user_ids():
    """All known user_ids across wallets + prefs, for /broadcast."""
    with _cursor() as cur:
        cur.execute("""
            SELECT user_id FROM wallets
            UNION
            SELECT user_id FROM user_prefs
        """)
        return [row["user_id"] for row in cur.fetchall()]
