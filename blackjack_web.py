"""
blackjack_web.py - route layer for the Blackjack Mini App.

Unlike crash_web.py this module does NOT run its own HTTP server - Railway
(and most simple hosts) only expose one public port, so both Mini Apps have
to share the single ThreadingHTTPServer crash_web.py already starts. This
module just plugs a second set of routes into that same server: crash_web's
Handler calls handle_get()/handle_post() below for anything it doesn't
recognise itself, and returns whatever HTTP response those produce.

No game logic lives here either - it all goes through the functions already
defined in main.py (blackjack_start, blackjack_hit, blackjack_stand,
blackjack_double, blackjack_split, blackjack_get_state, active_blackjack_games,
get_balance, BLACKJACK_LOCK). This module is just the HTTP wrapper.

    GET  /blackjack/<token>            -> the app page
    GET  /api/blackjack/info?token=    -> balance / status / full hand state
    POST /api/blackjack/start          -> {token}            deals the round
    POST /api/blackjack/hit            -> {token}            hit the active hand
    POST /api/blackjack/stand          -> {token}            stand the active hand
    POST /api/blackjack/double         -> {token}            double the active hand
    POST /api/blackjack/split          -> {token}            split the active hand
"""

import os

_main = None
_html_cache = None
HTML_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "blackjack.html")


def init(main_module):
    global _main
    _main = main_module


def _load_html():
    global _html_cache
    if _html_cache is None:
        with open(HTML_PATH, "r", encoding="utf-8") as f:
            _html_cache = f.read()
    return _html_cache


def _get_game(token):
    with _main.BLACKJACK_LOCK:
        return _main.active_blackjack_games.get(token)


def handle_get(handler, path, parsed):
    """Returns True if this module handled the request (handler._json/_html
    was already called), False to let the caller fall through to its own
    404 handling."""
    from urllib.parse import parse_qs

    if path.startswith("/blackjack/"):
        token = path[len("/blackjack/"):].strip("/")
        if not _get_game(token):
            handler._html(404, "<h1>Table not found or expired</h1>"
                                "<p>Go back to the chat and run /blackjack again.</p>")
            return True
        handler._html(200, _load_html())
        return True

    if path == "/api/blackjack/info":
        qs = parse_qs(parsed.query)
        token = (qs.get("token") or [""])[0]
        game = _get_game(token)
        if not game:
            handler._json(404, {"detail": "Table not found or expired"})
            return True
        state = _main.blackjack_get_state(token)
        if state is None:
            handler._json(404, {"detail": "Table not found or expired"})
            return True
        handler._json(200, state)
        return True

    return False


def handle_post(handler, path, body):
    token = body.get("token", "")

    if path == "/api/blackjack/start":
        game = _get_game(token)
        if not game:
            handler._json(404, {"detail": "Table not found or expired"})
            return True
        result = _main.blackjack_start(token, body.get("amount"))
        return _finish_post(handler, token, result)

    actions = {
        "/api/blackjack/hit": _main.blackjack_hit,
        "/api/blackjack/stand": _main.blackjack_stand,
        "/api/blackjack/double": _main.blackjack_double,
        "/api/blackjack/split": _main.blackjack_split,
        "/api/blackjack/again": _main.blackjack_play_again,
    }
    fn = actions.get(path)
    if fn is None:
        return False

    game = _get_game(token)
    if not game:
        handler._json(404, {"detail": "Table not found or expired"})
        return True

    result = fn(token)
    return _finish_post(handler, token, result)


def _finish_post(handler, token, result):
    if not result.get("ok"):
        msg = {
            "not_found": "Table not found or expired.",
            "already_started": "This hand already started.",
            "insufficient_balance": "Insufficient balance.",
            "min_bet": "That bet is below the table minimum.",
            "max_bet": "That bet is above the table maximum.",
            "not_active": "There's no active hand right now.",
            "cannot_hit": "Can't hit right now.",
            "cannot_stand": "Can't stand right now.",
            "cannot_double": "Can't double down right now.",
            "cannot_split": "Can't split right now.",
            "not_done": "This round isn't finished yet.",
        }.get(result.get("error"), "Couldn't complete that action.")
        handler._json(400, {"detail": msg})
        return True

    state = _main.blackjack_get_state(token)
    handler._json(200, state if state is not None else {"detail": "Table not found or expired"})
    return True
