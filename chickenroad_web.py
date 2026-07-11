"""
chickenroad_web.py - route layer for the Chicken Road Mini App.

Same pattern as blackjack_web.py: this rides on the single shared server
crash_web.py already starts (most hosts, Railway included, only expose one
public port). No game logic lives here - it all goes through main.py
(chicken_start, chicken_step, chicken_cashout, chicken_play_again,
chicken_get_state, active_chicken_games, get_balance, CHICKEN_LOCK). This
module is just the HTTP wrapper around that state.

    GET  /chickenroad/<token>            -> the app page
    GET  /api/chickenroad/info?token=    -> balance / status / full state
    POST /api/chickenroad/start          -> {token, amount?, difficulty?}  locks in bet + difficulty
    POST /api/chickenroad/step           -> {token}                       advance one lane
    POST /api/chickenroad/cashout        -> {token}                       cash out now
    POST /api/chickenroad/again          -> {token}                       reset to pending for another round
"""

import os

_main = None
_html_cache = None
HTML_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "chicken_road.html")


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
    with _main.CHICKEN_LOCK:
        return _main.active_chicken_games.get(token)


def handle_get(handler, path, parsed):
    """Returns True if this module handled the request, False to let the
    caller fall through to its own 404 handling."""
    from urllib.parse import parse_qs

    if path.startswith("/chickenroad/"):
        token = path[len("/chickenroad/"):].strip("/")
        if not _get_game(token):
            handler._html(404, "<h1>Road not found or expired</h1>"
                                "<p>Go back to the chat and run /chickenroad again.</p>")
            return True
        handler._html(200, _load_html())
        return True

    if path == "/api/chickenroad/info":
        qs = parse_qs(parsed.query)
        token = (qs.get("token") or [""])[0]
        state = _main.chicken_get_state(token)
        if state is None:
            handler._json(404, {"detail": "Road not found or expired"})
            return True
        handler._json(200, state)
        return True

    return False


def handle_post(handler, path, body):
    token = body.get("token", "")

    if path == "/api/chickenroad/start":
        game = _get_game(token)
        if not game:
            handler._json(404, {"detail": "Road not found or expired"})
            return True
        result = _main.chicken_start(token, body.get("amount"), body.get("difficulty"))
        return _finish_post(handler, token, result)

    actions = {
        "/api/chickenroad/step": _main.chicken_step,
        "/api/chickenroad/cashout": _main.chicken_cashout,
        "/api/chickenroad/again": _main.chicken_play_again,
    }
    fn = actions.get(path)
    if fn is None:
        return False

    game = _get_game(token)
    if not game:
        handler._json(404, {"detail": "Road not found or expired"})
        return True

    result = fn(token)
    return _finish_post(handler, token, result)


def _finish_post(handler, token, result):
    if not result.get("ok"):
        err = result.get("error")
        if err == "crashed":
            # Only reachable from a cashout attempt racing a step that
            # already crashed the round - chicken_step itself never returns
            # ok:False for a hit, since the step action still completed
            # successfully (the outcome was just a car). See main.py.
            handler._json(200, {"result": "crashed", "hit_lane": result.get("hit_lane")})
            return True
        msg = {
            "not_found": "Road not found or expired.",
            "already_started": "This game already started.",
            "insufficient_balance": "Insufficient balance.",
            "min_bet": "That bet is below the minimum.",
            "max_bet": "That bet is above the maximum.",
            "not_active": "There's no active game right now.",
            "not_started": "Game hasn't started yet.",
            "already_ended": "Game already ended.",
            "not_done": "This round isn't finished yet.",
            "no_steps_taken": "Take at least one step before cashing out.",
        }.get(err, "Couldn't complete that action.")
        handler._json(400, {"detail": msg})
        return True

    state = _main.chicken_get_state(token)
    handler._json(200, state if state is not None else {"detail": "Road not found or expired"})
    return True
