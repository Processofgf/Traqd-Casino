"""
dice_web.py - route layer for the Dice Mini App.

Same pattern as blackjack_web.py/chickenroad_web.py: this rides on the single
shared server crash_web.py already starts (most hosts, Railway included, only
expose one public port). No game logic lives here - it all goes through
main.py (dice_roll, dice_again, dice_get_state, active_dice_games,
get_balance, DICE_LOCK). This module is just the HTTP wrapper around that
state.

    GET  /dice/<token>       -> the app page
    GET  /api/dice/info?token=      -> balance / status / full state
    POST /api/dice/roll             -> {token, amount?, direction, target}  locks in bet + rolls
    POST /api/dice/again            -> {token, amount?}                     reset to pending for another round
"""

import os

_main = None
_html_cache = None
HTML_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "dice.html")


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
    with _main.DICE_LOCK:
        return _main.active_dice_games.get(token)


def handle_get(handler, path, parsed):
    """Returns True if this module handled the request, False to let the
    caller fall through to its own 404 handling."""
    from urllib.parse import parse_qs

    if path.startswith("/dice/"):
        token = path[len("/dice/"):].strip("/")
        if not _get_game(token):
            handler._html(404, "<h1>Table not found or expired</h1>"
                                "<p>Go back to the chat and run /dice again.</p>")
            return True
        handler._html(200, _load_html())
        return True

    if path == "/api/dice/info":
        qs = parse_qs(parsed.query)
        token = (qs.get("token") or [""])[0]
        state = _main.dice_get_state(token)
        if state is None:
            handler._json(404, {"detail": "Table not found or expired"})
            return True
        handler._json(200, state)
        return True

    return False


def handle_post(handler, path, body):
    token = body.get("token", "")

    if path == "/api/dice/roll":
        game = _get_game(token)
        if not game:
            handler._json(404, {"detail": "Table not found or expired"})
            return True
        result = _main.dice_roll(
            token, body.get("amount"), body.get("direction"), body.get("target")
        )
        return _finish_post(handler, token, result)

    if path == "/api/dice/again":
        game = _get_game(token)
        if not game:
            handler._json(404, {"detail": "Table not found or expired"})
            return True
        result = _main.dice_again(token, body.get("amount"))
        return _finish_post(handler, token, result)

    return False


def _finish_post(handler, token, result):
    if not result.get("ok"):
        msg = {
            "not_found": "Table not found or expired.",
            "already_started": "This round already finished - hit Play Again.",
            "insufficient_balance": "Insufficient balance.",
            "min_bet": "That bet is below the minimum.",
            "max_bet": "That bet is above the maximum.",
            "not_done": "This round isn't finished yet.",
        }.get(result.get("error"), "Couldn't complete that action.")
        handler._json(400, {"detail": msg})
        return True

    state = _main.dice_get_state(token)
    handler._json(200, state if state is not None else {"detail": "Table not found or expired"})
    return True
