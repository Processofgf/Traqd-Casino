"""
crash_web.py — serves the Crash Mini App.

Replaces the old crash_web implementation with something that just serves
the real index.html (the one designed for this app) plus the small JSON
API that page calls:

    GET  /crash/<token>            -> the app page
    GET  /api/crash/info?token=    -> balance / locked amount / current status
                                       (used once, on page load, and to resume
                                       a round if the page is reopened)
    POST /api/crash/start          -> {token}          starts the round
    GET  /api/crash/state?token=   -> {crashed, crash_point?}   (polled)
    POST /api/crash/cashout        -> {token}          cashes out

No game logic lives here - everything goes through the functions/dicts
already defined in main.py (crash_start, crash_attempt_cashout,
crash_get_state, active_crash_games, get_balance, CRASH_LOCK). This module
is just the HTTP wrapper around that state.
"""

import os
import json
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

_main = None  # set by init(), holds a reference to the main.py module
_html_cache = None
HTML_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "index.html")

# Blackjack, Dice, and Chicken Road each ship their own thin web wrapper
# with the same handle_get(handler, path, parsed) / handle_post(handler,
# path, body) -> bool contract as this file. Instead of running four
# separate HTTP servers on four ports, they all piggyback on THIS single
# server - do_GET/do_POST below try each registered module in turn before
# falling through to a 404. main.py registers them at startup via
# init_extra_modules().
_extra_modules = []


def init_extra_modules(modules):
    global _extra_modules
    _extra_modules = modules


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
    with _main.CRASH_LOCK:
        return _main.active_crash_games.get(token)


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):
        pass  # keep stdout clean; main.py already logs bot activity

    def _json(self, status, payload):
        body = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _html(self, status, text):
        body = text.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _read_json_body(self):
        length = int(self.headers.get("Content-Length", 0) or 0)
        raw = self.rfile.read(length) if length else b""
        try:
            return json.loads(raw.decode("utf-8")) if raw else {}
        except Exception:
            return {}

    # ------------------------------------------------------------------
    def do_GET(self):
        parsed = urlparse(self.path)
        path = parsed.path

        if path.startswith("/crash/"):
            token = path[len("/crash/"):].strip("/")
            if not _get_game(token):
                self._html(404, "<h1>Launch pad not found or expired</h1>"
                                 "<p>Go back to the chat and run /crash again.</p>")
                return
            self._html(200, _load_html())
            return

        if path == "/api/crash/info":
            qs = parse_qs(parsed.query)
            token = (qs.get("token") or [""])[0]
            game = _get_game(token)
            if not game:
                self._json(404, {"detail": "Launch pad not found or expired"})
                return

            balance = _main.get_balance(game["user_id"])
            state = _main.crash_get_state(token) or {}
            status = state.get("status", game["status"])

            resp = {"balance": balance, "amount": game["amount"], "status": status}
            if status == "active":
                with _main.CRASH_LOCK:
                    g = _main.active_crash_games.get(token)
                    start_time = g["start_time"] if g else None
                import time as _time
                resp["elapsed_ms"] = int((_time.time() - start_time) * 1000) if start_time else 0
            elif status == "crashed":
                resp["crash_point"] = state.get("crash_point", game.get("crash_point"))
            elif status == "cashed_out":
                resp["multiplier"] = state.get("multiplier")
            self._json(200, resp)
            return

        if path == "/api/crash/state":
            import time as _time
            qs = parse_qs(parsed.query)
            token = (qs.get("token") or [""])[0]

            # Long-poll: hold the connection open and re-check frequently
            # instead of making the client wait for its next fixed-interval
            # request. This is what keeps the crash moment "live" - without
            # it, the client only finds out a round crashed on its next
            # scheduled poll, by which point its local animation has kept
            # climbing past the real crash point for however long that gap
            # was.
            deadline = _time.time() + 4.0
            while True:
                game = _get_game(token)
                if not game:
                    self._json(404, {"detail": "Round not found"})
                    return
                state = _main.crash_get_state(token)
                if not state:
                    self._json(404, {"detail": "Round not found"})
                    return
                if state["status"] == "crashed":
                    self._json(200, {"crashed": True, "crash_point": state["crash_point"]})
                    return
                if state["status"] != "active":
                    self._json(200, {"crashed": False})
                    return
                if _time.time() >= deadline:
                    self._json(200, {"crashed": False})
                    return
                _time.sleep(0.06)

        for mod in _extra_modules:
            if mod.handle_get(self, path, parsed):
                return

        self._json(404, {"detail": "not_found"})

    # ------------------------------------------------------------------
    def do_POST(self):
        parsed = urlparse(self.path)
        path = parsed.path
        body = self._read_json_body()
        token = body.get("token", "")

        if path == "/api/crash/start":
            game = _get_game(token)
            if not game:
                self._json(404, {"detail": "Launch pad not found or expired"})
                return
            result = _main.crash_start(token)
            if not result.get("ok"):
                msg = {
                    "already_started": "This round already started.",
                    "insufficient_balance": "Insufficient balance.",
                    "not_found": "Launch pad not found or expired.",
                }.get(result.get("error"), "Could not start round.")
                self._json(400, {"detail": msg})
                return
            self._json(200, {"balance": _main.get_balance(game["user_id"])})
            return

        if path == "/api/crash/cashout":
            game = _get_game(token)
            if not game:
                self._json(404, {"detail": "Round not found"})
                return
            result = _main.crash_attempt_cashout(token)
            if not result.get("ok"):
                err = result.get("error")
                if err == "crashed":
                    self._json(200, {
                        "result": "crashed",
                        "crash_point": result["crash_point"],
                        "balance": _main.get_balance(game["user_id"]),
                    })
                    return
                msg = {
                    "not_started": "Round hasn't started yet.",
                    "already_ended": "Round already ended.",
                    "not_found": "Round not found.",
                }.get(err, "Could not cash out.")
                self._json(400, {"detail": msg})
                return

            amount = game["amount"]
            payout = result["payout"]
            self._json(200, {
                "result": "cashed_out",
                "multiplier": result["multiplier"],
                "profit": round(payout - amount, 2),
                "balance": _main.get_balance(game["user_id"]),
            })
            return

        for mod in _extra_modules:
            if mod.handle_post(self, path, body):
                return

        self._json(404, {"detail": "not_found"})


def start_in_background():
    port = int(os.environ.get("PORT", "8080"))
    server = ThreadingHTTPServer(("0.0.0.0", port), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True, name="crash-web")
    thread.start()
    return server
