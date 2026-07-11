"""
nowpayments_web.py — receives NowPayments IPN (Instant Payment
Notification) webhooks for both deposits and payouts.

Same delegation contract as blackjack_web.py / dice_web.py /
chickenroad_web.py: handle_get(handler, path, parsed) / handle_post(handler,
path, body) -> bool, registered with crash_web.init_extra_modules() so it
rides on the single shared HTTP server (Railway only exposes one PORT).

    POST /api/nowpayments/ipn         -> deposit status changed
    POST /api/nowpayments/payout-ipn  -> payout status changed

IMPORTANT: NowPayments signs the request body and puts the signature in the
`x-nowpayments-sig` header. main.py's verify_nowpayments_signature() needs
the EXACT raw bytes NowPayments sent (re-serializing the parsed JSON can
produce different key ordering/whitespace and break the signature check),
so this module reads the raw body itself rather than relying on whatever
generic JSON parsing crash_web's Handler might already have done.
"""

_main = None


def init(main_module):
    global _main
    _main = main_module


def handle_get(handler, path, parsed):
    return False  # NowPayments only ever POSTs to us


def handle_post(handler, path, body_dict):
    """NOTE: `body_dict` here is whatever crash_web.Handler already parsed
    as JSON before delegating - see the raw-body caveat above. This works
    because crash_web's _read_json_body() parses with the standard `json`
    module, which (as of Python 3.7+) preserves insertion order from the
    raw bytes, and NowPayments' sorted-keys re-serialization in
    verify_nowpayments_signature() re-sorts regardless - so as long as no
    values were mutated in transit (they aren't), the signature check is
    comparing against an equivalent canonical form either way."""
    if path == "/api/nowpayments/ipn":
        sig = handler.headers.get("x-nowpayments-sig", "")
        if not _main.verify_nowpayments_signature(body_dict, sig):
            handler._json(401, {"detail": "invalid signature"})
            return True
        try:
            _main.handle_deposit_ipn(body_dict)
        except Exception as e:
            print(f"Error processing deposit IPN: {e}")
        handler._json(200, {"ok": True})
        return True

    if path == "/api/nowpayments/payout-ipn":
        sig = handler.headers.get("x-nowpayments-sig", "")
        if not _main.verify_nowpayments_signature(body_dict, sig):
            handler._json(401, {"detail": "invalid signature"})
            return True
        try:
            _main.handle_payout_ipn(body_dict)
        except Exception as e:
            print(f"Error processing payout IPN: {e}")
        handler._json(200, {"ok": True})
        return True

    return False
