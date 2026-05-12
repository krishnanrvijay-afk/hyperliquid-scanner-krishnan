import html as _html
import math
import os
import json
import re as _re
import threading
import time
import requests as _requests
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from zoneinfo import ZoneInfo

BUILD_TIME = datetime.now(tz=ZoneInfo("America/New_York")).strftime("%Y-%m-%d %H:%M")
from http.server import BaseHTTPRequestHandler, HTTPServer

from scanner import (
    DEFAULT_SYMBOLS, scan_symbol, fetch_ticker,
    calc_trade_params_long, calc_trade_params_short,
)
from hyperliquid_api import place_order_from_alert, monitor_position

ACCOUNT_MODE          = "SMALL"      # "SMALL" | "MEDIUM" | "LARGE" — change this one line
API_TRADING_ENABLED   = os.environ.get("API_TRADING_ENABLED", "False").strip().lower() == "true"
CONSECUTIVE_LOSSES    = 0            # incremented on SL hit; reset on TP win; auto-pauses at 5
_daily_trades: list   = []           # list of trade dicts for current calendar day (EST)
_TRADE_STATE_FILE     = "trade_state.json"
PORT              = int(os.environ.get("PORT", 8000))
PRICE_INTERVAL    = int(os.environ.get("PRICE_INTERVAL", 1))
SCAN_INTERVAL     = int(os.environ.get("SCAN_INTERVAL", 20))
ALERT_THRESHOLD   = int(os.environ.get("ALERT_THRESHOLD", 8))
TRADE_MARGIN      = (700  if ACCOUNT_MODE == "SMALL"
                else 1000 if ACCOUNT_MODE == "MEDIUM"
                else 2500)          # base margin per mode — dashboard display only
TRADE_LEV_FIXED   = (5   if ACCOUNT_MODE == "SMALL"
                else 10  if ACCOUNT_MODE == "MEDIUM"
                else 25)            # leverage per mode — dashboard display only
MIN_TP_DOLLARS    = (15  if ACCOUNT_MODE == "SMALL"
                else 25  if ACCOUNT_MODE == "MEDIUM"
                else 75)            # Minimum TP $ — scales with mode notional
BTC_MIN_SCORE     = 9               # BTC requires higher score confidence
BTC_MIN_TP        = (25.0 if ACCOUNT_MODE == "SMALL"
                else 40.0 if ACCOUNT_MODE == "MEDIUM"
                else 125.0)         # BTC minimum TP $ per mode
TAKER_FEE_RATE    = 0.00035         # Hyperliquid taker fee per side
ROUND_TRIP_FEE    = 0.0007          # Round-trip (entry + exit)
DAILY_LOSS_LIMIT  = (500  if ACCOUNT_MODE == "SMALL"
                else 750  if ACCOUNT_MODE == "MEDIUM"
                else 1500)          # daily loss cap before alerts pause
BULLISH_TRENDS    = ["Strong Bull", "Bullish"]
BEARISH_TRENDS    = ["Strong Bear", "Bearish"]
COUNTER_TREND_MIN_SCORE = 9  # Neutral/Choppy (counter-trend) setups require this minimum score
NEUTRAL_TRENDS    = ["Neutral", "Choppy"]
TELEGRAM_TOKEN    = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID  = os.environ.get("TELEGRAM_CHAT_ID", "")
SYMBOLS = os.environ.get("SCAN_SYMBOLS", "").split(",") if os.environ.get("SCAN_SYMBOLS") else DEFAULT_SYMBOLS
SYMBOLS = [s.strip().upper() for s in SYMBOLS if s.strip()]

_TREND_BADGE = {
    "Strong Bull": ("🟢🟢", "#0d2e1a", "#3fb950"),
    "Bullish":     ("🟢",   "#112b1a", "#56d364"),
    "Neutral":     ("⚪",   "#1c1c1c", "#8b949e"),
    "Choppy":      ("🟡",   "#2b2200", "#d29922"),
    "Bearish":     ("🔴",   "#2d1010", "#f0786b"),
    "Strong Bear": ("🔴🔴", "#3d0000", "#ff6b6b"),
}
_TREND_EMOJI = {
    "Strong Bull": "🟢🟢", "Bullish": "🟢", "Neutral": "⚪",
    "Choppy": "🟡", "Bearish": "🔴", "Strong Bear": "🔴🔴",
}

EST = ZoneInfo("America/New_York")

def now_est(fmt="%Y-%m-%d %H:%M:%S EST"):
    return datetime.now(tz=EST).strftime(fmt)

def now_est_short():
    return datetime.now(tz=EST).strftime("%H:%M:%S EST")


def get_session_bonus():
    h = datetime.now(tz=EST).hour
    if 8 <= h < 12:
        return 1.0, "🌍🌎 EU/US Overlap"
    elif 12 <= h < 17:
        return 0.5, "🌎 US Session"
    elif 3 <= h < 8:
        return 0.5, "🌍 EU Session"
    else:
        return 0.0, "🌏 Asia/Off-hours"


def is_active_session() -> bool:
    """True during EU/US trading hours (3AM–5PM EST). False during Asia (5PM–3AM)."""
    h = datetime.now(tz=EST).hour
    return 3 <= h < 17

STALE_PCT     = float(os.environ.get("STALE_PCT", 0.003))      # 0.3% — base entry zone half-width
SL_BUFFER_PCT = float(os.environ.get("SL_BUFFER_PCT", 0.5))    # Cap stale zone at 50% of SL distance


def calc_stale_zone(entry: float, sl: float, direction: str):
    """
    Return (stale_low, stale_high) — the valid entry zone for a trigger order.

    The side facing the SL is capped to SL_BUFFER_PCT of SL distance, so that
    even a worst-case fill at the edge of the valid zone leaves at least
    (1 - SL_BUFFER_PCT) of the risk budget remaining. The side facing the TP
    keeps the base STALE_PCT width.

    Without this cap, a tight-SL setup could produce a stale zone that
    overlaps or exceeds the SL, allowing fills with zero room to be right.
    """
    base_width      = entry * STALE_PCT
    sl_distance     = abs(sl - entry)
    sl_capped_width = sl_distance * SL_BUFFER_PCT

    if direction == "LONG":
        # SL is below entry — cap the LOW side (toward SL).
        # HIGH side (toward TP) stays at base width.
        low_width = min(base_width, sl_capped_width)
        return round(entry - low_width, 8), round(entry + base_width, 8)
    else:  # SHORT
        # SL is above entry — cap the HIGH side (toward SL).
        # LOW side (toward TP) stays at base width.
        high_width = min(base_width, sl_capped_width)
        return round(entry - base_width, 8), round(entry + high_width, 8)


def get_tier(score: int, mode: str = None):
    """Return (margin_usdt, leverage, tier_label) based on score and account mode."""
    if mode is None:
        mode = ACCOUNT_MODE
    if mode == "LARGE":
        if score >= 12: return 7500, 25, "💎 Perfect"
        elif score >= 11: return 5000, 25, "⭐⭐⭐ Prime"
        elif score >= 9:  return 3500, 25, "⭐⭐ Premium"
        else:             return 2500, 25, "⭐ Quality"
    elif mode == "MEDIUM":
        if score >= 12: return 2500, 10, "💎 Perfect"
        elif score >= 11: return 2000, 10, "⭐⭐⭐ Prime"
        elif score >= 9:  return 1500, 10, "⭐⭐ Premium"
        else:             return 1000, 10, "⭐ Quality"
    else:  # SMALL
        if score >= 12: return 3500, 5, "💎 Perfect"
        elif score >= 11: return 2100, 5, "⭐⭐⭐ Prime"
        elif score >= 9:  return 1400, 5, "⭐⭐ Premium"
        else:             return  700, 5, "⭐ Quality"


# ── Telegram helpers ───────────────────────────────────────────────────────────

_PRICE_DECIMALS = {
    "BTC":  1,
    "ETH":  2, "BNB_USDT":  2, "SOL_USDT":  2,
    "ZEC":  2, "AAVE_USDT": 2,
    "DOGE": 5, "XRP_USDT":  4, "SUI_USDT":  4,
    "LINK": 3,
}

def _fmt_price(symbol, price):
    dp = _PRICE_DECIMALS.get(symbol, 4)
    return f"{price:.{dp}f}"

def _fmt_lev(lev):
    return max(1, math.floor(lev))

# Detects raw HTML error pages (e.g. exchange 403 "Access Denied" bodies)
_HTML_PAGE_RE = _re.compile(r'<html[\s>]|<!doctype\s+html', _re.IGNORECASE)
_HTML_TITLE_RE = _re.compile(r'<title[^>]*>([^<]{1,80})</title>', _re.IGNORECASE)

def _sanitize_err(text: str) -> str:
    """Replace raw HTML error bodies with a short plain-text summary."""
    if _HTML_PAGE_RE.search(text):
        m = _HTML_TITLE_RE.search(text)
        label = m.group(1).strip() if m else "HTML error response"
        return f"[{label} — HTML body stripped]"
    return text


def _tg_post(text):
    text = "🟣 Hyperliquid\n" + text
    # Last-resort guard: if raw HTML is still in the message, drop parse_mode
    # so Telegram receives it as plain text rather than rejecting it with 400.
    if _HTML_PAGE_RE.search(text):
        print("  [telegram] WARNING: raw HTML detected — sending as plain text")
        payload = {"chat_id": TELEGRAM_CHAT_ID, "text": text}
    else:
        payload = {"chat_id": TELEGRAM_CHAT_ID, "text": text, "parse_mode": "HTML"}
    r = _requests.post(
        f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
        json=payload,
        timeout=5,
    )
    print(f"  [telegram] HTTP {r.status_code}: {r.text[:200]}")
    r.raise_for_status()
    return r


def calc_liq_price(entry: float, leverage: float, side: str) -> float:
    """Return liquidation price — always a numeric value, never None or N/A."""
    try:
        lev = float(leverage)
        if lev <= 0:
            lev = 0.01
        if side == "LONG":
            liq = entry * (1 - 1 / lev)
            if liq <= 0:
                liq = entry * (1 - lev)   # sub-1x: practical floor
        else:
            liq = entry * (1 + 1 / lev)
        return round(liq, 2)
    except Exception:
        return round(entry * 0.9, 2)      # fallback: 10% below entry


# ── Telegram notifications ─────────────────────────────────────────────────────

def send_telegram(alert):
    if not TELEGRAM_TOKEN:
        print("  [telegram] SKIPPED — TELEGRAM_BOT_TOKEN not set")
        return
    if not TELEGRAM_CHAT_ID:
        print("  [telegram] SKIPPED — TELEGRAM_CHAT_ID not set")
        return

    d          = alert["direction"]
    sym        = alert["symbol"]
    entry      = alert["entry"]
    sl         = alert["sl"]
    tp1        = alert["tp1"]
    tp2        = alert["tp2"]
    trend      = alert.get("trend", "—")
    score      = alert["score"]
    bonus      = alert.get("session_bonus", 0.0)
    sess_label = alert.get("session_label", "—")
    max_lev    = alert.get("max_lev", 1)
    alignment  = alert.get("alignment", "")
    j5         = alert.get("j5")
    bid_pct    = alert.get("bid_pct")
    ask_pct    = alert.get("ask_pct")
    if alert.get("stale_low") is not None and alert.get("stale_high") is not None:
        stale_low  = alert["stale_low"]
        stale_high = alert["stale_high"]
    else:
        stale_low, stale_high = calc_stale_zone(entry, sl, d)

    # Tier-based position sizing
    tiered_margin, tiered_lev, tier_label = get_tier(score)
    pos_size  = tiered_margin * tiered_lev
    fee_cost  = pos_size * ROUND_TRIP_FEE

    # Price percentages
    tp1_pct = abs(tp1 - entry) / entry if entry > 0 else 0
    tp2_pct = abs(tp2 - entry) / entry if entry > 0 else 0
    sl_pct  = abs(sl  - entry) / entry if entry > 0 else 0

    # Fee-adjusted P&L
    tp1_gross = pos_size * tp1_pct
    tp1_net   = tp1_gross - fee_cost
    tp2_gross = pos_size * tp2_pct
    tp2_net   = tp2_gross - fee_cost
    sl_gross  = pos_size * sl_pct
    sl_net    = sl_gross + fee_cost
    rr_net    = round(tp1_net / sl_net, 1) if sl_net > 0 else 0

    # Tiered liq price and true breakeven
    if d == "LONG":
        liq            = round(entry * (1 - 1 / max(tiered_lev, 0.01)), 2)
        true_breakeven = entry * (1 + ROUND_TRIP_FEE)
    else:
        liq            = round(entry * (1 + 1 / max(tiered_lev, 0.01)), 2)
        true_breakeven = entry * (1 - ROUND_TRIP_FEE)

    trend_emoji  = _TREND_EMOJI.get(trend, "❓")
    counter_warn = "⚠️ Counter-trend setup\n" if "Counter-trend" in alignment else ""
    sub1x_warn   = "⚠️ Small move — verify before entering\n" if max_lev < 1 else ""

    # Session display e.g. "🌎 US +0.5"
    parts = sess_label.split()
    sess_display = f"{parts[0]} {parts[1]} +{bonus:.1f}" if len(parts) >= 2 else sess_label

    def fp(p): return _fmt_price(sym, p)

    adx     = alert.get("adx")
    j5_str  = f"{j5:.1f}"      if j5      is not None else "—"
    adx_str = f"{adx:.1f}"     if adx     is not None else "—"
    bid_str = f"{bid_pct:.1f}" if bid_pct is not None else "—"
    ask_str = f"{ask_pct:.1f}" if ask_pct is not None else "—"

    text = (
        f"{tier_label} {d} — {sym}\n"
        f"\n"
        f"Score: {score}/{'13' if d == 'LONG' else '12'}\n"
        f"Trend: {trend_emoji} {trend}\n"
        f"5m KDJ J: {j5_str}\n"
        f"📊 ADX: {adx_str} — {'Trending' if adx is not None and adx > 25 else 'Ranging'}\n"
        f"Depth: B{bid_str}% / S{ask_str}%\n"
        f"Session: {sess_display}\n"
        f"\n"
        f"━━━ TRIGGER ORDER SETUP ━━━\n"
        f"Order Type:  Trigger → Limit\n"
        f"Direction:   Open {d.capitalize()}\n"
        f"Trigger:     <code>{fp(entry)}</code>\n"
        f"Limit:       <code>{fp(entry)}</code>\n"
        f"Cost:        {tiered_margin:.0f} USDT\n"
        f"Leverage:    {tiered_lev:.0f}x (Isolated)\n"
        f"TP:          <code>{fp(tp1)}</code>\n"
        f"SL:          <code>{fp(sl)}</code>\n"
        f"\n"
        f"⏰ Valid entry zone: <code>{fp(stale_low)}</code> — <code>{fp(stale_high)}</code>\n"
        f"Cancel trigger if price exits this range\n"
        f"\n"
        f"{'⚠️ ASIA SESSION — Review at EU open (3AM EST)' + chr(10) + 'Consider waiting for active session confirmation' + chr(10) + 'before setting trigger order' if 'Asia' in sess_label else '⚡ After fill: move SL to ' + '<code>' + fp(true_breakeven) + '</code>'}\n"
        f"\n"
        f"━━━ RISK SUMMARY ━━━\n"
        f"Est. Profit: ${tp1_gross:.2f} gross / ${tp1_net:.2f} net\n"
        f"Backup TP:   ${tp2_gross:.2f} gross / ${tp2_net:.2f} net — <code>{fp(tp2)}</code>\n"
        f"Max Loss:    ${sl_gross:.2f} gross / ${sl_net:.2f} net\n"
        f"Fees:        ${fee_cost:.2f} round trip (0.12%)\n"
        f"R:R (net):   1:{rr_net}\n"
        f"Liq Price:   ~<code>{fp(liq)}</code>\n"
        f"\n"
        f"{counter_warn}"
        f"{sub1x_warn}"
        f"⏱ {now_est_short()}"
    )

    # Append order execution result if present (set by _fire_trade before calling us)
    order_result = alert.get("order_result", "")
    if order_result:
        text += f"\n\n━━━ ORDER EXECUTION ━━━\n{_html.escape(order_result)}"

    print(f"  [telegram] building message: {d} {sym} score={score}")
    _msg_len = len(text)
    if _msg_len > 4000:
        print(f"  [telegram] WARNING: message is {_msg_len} chars — truncating to 4000")
        text = text[:3950] + "\n…[truncated — message too long]"
    else:
        print(f"  [telegram] message length: {_msg_len} chars — OK")
    try:
        _tg_post(text)
        print(f"  [telegram] sent {d} {sym} tier={tier_label} margin={tiered_margin} lev={tiered_lev}x")
    except Exception as e:
        _tg_resp = getattr(getattr(e, "response", None), "text", "") or ""
        print(f"  [telegram] SEND FAILED — {type(e).__name__}: {e}")
        if _tg_resp:
            print(f"  [telegram] API response body: {_tg_resp[:500]}")
        else:
            print(f"  [telegram] (no API response body — likely a network/timeout error)")


# ── Trade state persistence ───────────────────────────────────────────────────

_LOSS_LOCK = threading.Lock()

def _load_trade_state() -> None:
    """Load persisted trade state (consecutive losses, flag, daily trades) from disk."""
    global CONSECUTIVE_LOSSES, API_TRADING_ENABLED, _daily_trades
    try:
        with open(_TRADE_STATE_FILE) as f:
            state = json.load(f)
        CONSECUTIVE_LOSSES  = int(state.get("consecutive_losses", 0))
        # Only restore a saved False if the auto-pause threshold was actually hit.
        # This prevents a stale file from overriding a deliberate code-level True.
        saved_enabled = bool(state.get("api_trading_enabled", True))
        if not saved_enabled and CONSECUTIVE_LOSSES >= 5:
            API_TRADING_ENABLED = False   # auto-pause persists across restarts
        # else: keep whatever the code default says (True or False)
        _daily_trades       = list(state.get("daily_trades", []))
        print(f"[trade_state] loaded: consecutive_losses={CONSECUTIVE_LOSSES} "
              f"api_trading_enabled={API_TRADING_ENABLED} "
              f"daily_trades={len(_daily_trades)}")
    except FileNotFoundError:
        pass  # first run — no state file yet
    except Exception as e:
        print(f"[trade_state] load error: {e}")

def _save_trade_state(reset_daily: bool = False) -> None:
    """Persist trade state to disk. Pass reset_daily=True to clear today's trade list."""
    global _daily_trades
    if reset_daily:
        _daily_trades = []
    try:
        with open(_TRADE_STATE_FILE, "w") as f:
            json.dump({
                "consecutive_losses": CONSECUTIVE_LOSSES,
                "api_trading_enabled": API_TRADING_ENABLED,
                "daily_trades": _daily_trades,
            }, f, indent=2)
    except Exception as e:
        print(f"[trade_state] save error: {e}")

def record_trade_result(outcome: str, trade_info: dict | None = None) -> None:
    """
    Called by monitor_position when a trade fully closes.
      outcome="loss" — position closed before TP1 (SL hit).
      outcome="win"  — TP1 reached; trade closed via trail or exchange TP.
      trade_info     — dict with symbol/direction/entry/exit/pnl/fees/win/timestamp.
    Thread-safe. Persists to trade_state.json.
    Auto-pauses API trading after 5 consecutive losses.
    """
    global CONSECUTIVE_LOSSES, API_TRADING_ENABLED, _daily_trades
    with _LOSS_LOCK:
        if trade_info:
            _daily_trades.append(trade_info)
            print(f"[trade_state] trade logged: {trade_info.get('symbol')} "
                  f"{trade_info.get('direction')} pnl={trade_info.get('pnl')}")
        if outcome == "loss":
            CONSECUTIVE_LOSSES += 1
            print(f"[trade_state] LOSS recorded — consecutive={CONSECUTIVE_LOSSES}")
            _save_trade_state()
            if CONSECUTIVE_LOSSES >= 5:
                API_TRADING_ENABLED = False
                _save_trade_state()
                msg = (
                    "🛑 5 consecutive losses detected. "
                    "API trading paused automatically. "
                    "Review setups before re-enabling."
                )
                print(f"[trade_state] AUTO-PAUSE: {msg}")
                try:
                    _tg_post(msg)
                except Exception:
                    pass
        elif outcome == "win":
            if CONSECUTIVE_LOSSES:
                print(f"[trade_state] WIN — resetting consecutive_losses "
                      f"from {CONSECUTIVE_LOSSES} to 0")
            CONSECUTIVE_LOSSES = 0
            _save_trade_state()

_load_trade_state()   # restore counter + flag + daily trades from previous run

# ── Daily P&L summary ─────────────────────────────────────────────────────────

def _send_daily_summary() -> None:
    """Build and send the daily P&L Telegram summary, then reset daily trade list."""
    from datetime import timedelta
    with _LOSS_LOCK:
        trades   = list(_daily_trades)
    date_str = (datetime.now(tz=EST) - timedelta(seconds=30)).strftime("%Y-%m-%d")

    if not trades:
        msg = f"📊 DAILY SUMMARY — {date_str} — No trades today"
    else:
        wins      = [t for t in trades if t.get("win")]
        losses_t  = [t for t in trades if not t.get("win")]
        total     = len(trades)
        gross_pnl = sum(t.get("pnl", 0) for t in trades)
        win_rate  = len(wins) / total * 100
        worst     = min(trades, key=lambda t: t.get("pnl", 0))
        sign      = "+" if gross_pnl >= 0 else ""
        msg = (
            f"📊 DAILY SUMMARY — {date_str}\n"
            f"Trades: {total}  |  Wins: {len(wins)}  Losses: {len(losses_t)}\n"
            f"Win Rate: {win_rate:.0f}%\n"
            f"Gross P&L: {sign}{gross_pnl:.2f} USDT\n"
            f"Worst Trade: {worst['symbol']} {worst['direction']} "
            f"${worst.get('pnl', 0):.2f} USDT"
        )

    print(f"[daily_summary] sending: {msg.splitlines()[0]}")
    try:
        _tg_post(msg)
    except Exception as e:
        print(f"[daily_summary] tg error: {e}")

    with _LOSS_LOCK:
        _save_trade_state(reset_daily=True)


def _midnight_summary_loop() -> None:
    """Background daemon: sleeps until midnight EST, fires summary, repeats."""
    from datetime import timedelta
    while True:
        now           = datetime.now(tz=EST)
        next_midnight = (now + timedelta(days=1)).replace(
            hour=0, minute=0, second=0, microsecond=0)
        sleep_secs    = (next_midnight - now).total_seconds()
        print(f"[daily_summary] next summary in {sleep_secs/3600:.1f}h "
              f"({next_midnight.strftime('%Y-%m-%d 00:00 EST')})")
        time.sleep(sleep_secs)
        try:
            _send_daily_summary()
        except Exception as e:
            print(f"[daily_summary] loop error: {e}")


# ── Trade execution + notification ────────────────────────────────────────────

def _fire_trade(alert: dict, cancel_event: threading.Event) -> None:
    """
    Background thread: optionally places an order, then sends the Telegram alert.

    Flow (SMALL account mode only):
      1. Attempt order via place_order_from_alert (dry_run when API_TRADING_ENABLED=False).
      2. Attach result string to alert["order_result"] so send_telegram appends it.
      3. On order error: set a failure note, send the alert anyway, then send a
         separate error Telegram so the trader knows to enter manually.
      4. If a real order was placed successfully, start monitor_position thread.
      5. Always start the 30-min send_reminder thread.
    """
    _ft_sym = alert.get("symbol", "?")
    _ft_dir = alert.get("direction", "?")
    print(f"  [_fire_trade] started: {_ft_dir} {_ft_sym}")
    try:
        _fire_trade_inner(alert, cancel_event)
    except Exception as _ft_exc:
        print(f"  [_fire_trade] UNHANDLED EXCEPTION for {_ft_dir} {_ft_sym}: "
              f"{type(_ft_exc).__name__}: {_ft_exc}")
        import traceback
        traceback.print_exc()


def _fire_trade_inner(alert: dict, cancel_event: threading.Event) -> None:
    direction = alert["direction"]
    symbol    = alert["symbol"]
    entry     = alert["entry"]
    sl        = alert["sl"]
    tp1       = alert["tp1"]
    tp2       = alert["tp2"]
    margin    = alert["tiered_margin"]
    leverage  = int(alert["tiered_lev"])

    order_placed = False   # True only when a REAL (non-dry) order was accepted

    if ACCOUNT_MODE == "SMALL":
        dry = not API_TRADING_ENABLED
        try:
            result = place_order_from_alert(
                symbol      = symbol,
                direction   = direction,
                entry_price = entry,
                sl_price    = sl,
                tp1_price   = tp1,
                tp2_price   = tp2,
                margin_usdt = margin,
                leverage    = leverage,
                dry_run     = dry,
            )
            vol = result.get("params", {}).get("vol") if dry else result.get("vol", "?")
            if dry:
                alert["order_result"] = (
                    f"🟡 DRY RUN — no real order placed\n"
                    f"Vol: {vol} contracts  "
                    f"Margin: ${margin:.0f}  Lev: {leverage}x\n"
                    f"Set API_TRADING_ENABLED=True to go live"
                )
            else:
                # Check for exchange-level order rejection (success=False in response)
                if not result.get("success", False):
                    hl_code  = result.get("code", "?")
                    hl_msg   = _sanitize_err(result.get("message", str(result))[:200])
                    err_str  = f"code={hl_code}: {hl_msg}"
                    alert["order_result"] = f"❌ Order rejected by exchange — enter manually\n{err_str}"
                    print(f"  [trade] order rejected ({direction} {symbol}): {err_str}")
                    send_telegram(alert)
                    threading.Thread(target=send_reminder, args=(alert, cancel_event), daemon=True).start()
                    try:
                        _tg_post(
                            f"⚠️ <b>Order Rejected — {direction} {symbol}</b>\n"
                            f"<code>{_html.escape(err_str)}</code>\n"
                            f"Manual entry required."
                        )
                    except Exception:
                        pass
                    return
                data      = result.get("data") or result
                order_id  = data.get("orderId", "?")
                state     = data.get("state", data.get("status", "submitted"))
                alert["order_result"] = (
                    f"✅ ORDER PLACED\n"
                    f"Order ID: <code>{order_id}</code>\n"
                    f"Status: {state}  Vol: {vol} contracts\n"
                    f"Margin: ${margin:.0f}  Lev: {leverage}x"
                )
                order_placed = True
                print(f"  [trade] order placed: {direction} {symbol} id={order_id} state={state}")
        except Exception as e:
            # Network error, JSON parse failure, or unexpected exception
            err = _sanitize_err(str(e)[:300])
            alert["order_result"] = f"❌ Order failed (exception) — enter manually\n{err}"
            print(f"  [trade] order exception ({direction} {symbol}): {err}")
            # Send normal alert first, then follow-up error message
            send_telegram(alert)
            threading.Thread(target=send_reminder, args=(alert, cancel_event), daemon=True).start()
            try:
                _tg_post(
                    f"⚠️ <b>Order Exception — {direction} {symbol}</b>\n"
                    f"<code>{_html.escape(err)}</code>\n"
                    f"Manual entry required."
                )
            except Exception:
                pass
            return

    # Send enriched Telegram (order_result appended if set)
    print(f"  [telegram] _fire_trade: calling send_telegram for {direction} {symbol}")
    send_telegram(alert)
    threading.Thread(target=send_reminder, args=(alert, cancel_event), daemon=True).start()

    # Start position monitor only for real (live) orders
    if order_placed:
        monitor_position(
            symbol      = symbol,
            direction   = direction,
            entry_price = entry,
            tp1_price   = tp1,
            sl_price    = sl,
            margin_usdt = margin,
            leverage    = leverage,
            on_close    = record_trade_result,
        )


# ── 30-minute follow-up reminders ──────────────────────────────────────────────

_pending_reminders:     dict  = {}    # symbol -> threading.Event (cancel flag)
_last_alert_time:       dict  = {}    # key: "SYMBOL_SIDE", value: datetime of last alert sent
pending_alerts:         dict  = {}    # key: "SYMBOL_SIDE", value: datetime first qualifying scan seen
daily_loss_total:       float = 0.0   # LARGE mode: running daily loss (USDT)
daily_loss_reset_date         = None  # date of last daily reset
_daily_limit_notified:  bool  = False # True once limit-hit Telegram has been sent today

def _cooldown_remaining(key: str) -> float:
    """Return remaining cooldown seconds for the given key, or 0.0 if not in cooldown."""
    last = _last_alert_time.get(key)
    if last is None:
        return 0.0
    return max(0.0, 900.0 - (datetime.now() - last).total_seconds())
_pending_lock = threading.Lock()

def send_reminder(alert, cancel_event):
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        return
    # Only active sessions (EU, US, Overlap) get a reminder
    if alert.get("session_bonus", 0) == 0:
        return

    sym   = alert["symbol"]
    d     = alert["direction"]
    entry = alert["entry"]
    orig_time = alert["time"]

    # Sleep 30 minutes in 10-second chunks, cancellable
    deadline = time.time() + 1800
    while time.time() < deadline:
        if cancel_event.is_set():
            return
        time.sleep(min(10, deadline - time.time()))
    if cancel_event.is_set():
        return

    # Fetch live price
    try:
        ticker = fetch_ticker(sym)
        current_price = float(ticker.get("lastPrice", entry))
    except Exception:
        current_price = entry

    def fp(p): return _fmt_price(sym, p)

    if alert.get("stale_low") is not None and alert.get("stale_high") is not None:
        stale_low  = alert["stale_low"]
        stale_high = alert["stale_high"]
    else:
        _sl = alert.get("sl", entry)
        stale_low, stale_high = calc_stale_zone(entry, _sl, d)

    if current_price < stale_low:
        if d == "LONG":
            status1 = "🚫 STALE — Setup failed"
            status2 = f"Price dropped below {fp(stale_low)}\nCancel trigger order"
        else:
            status1 = "🚫 STALE — Entry missed"
            status2 = f"Price dropped below {fp(stale_low)} before fill\nCancel trigger order — do not chase"
    elif current_price > stale_high:
        if d == "LONG":
            status1 = "🚫 STALE — Entry missed"
            status2 = f"Price ripped above {fp(stale_high)} before fill\nCancel trigger order — do not chase"
        else:
            status1 = "🚫 STALE — Setup failed"
            status2 = f"Price ripped above {fp(stale_high)}\nCancel trigger order"
    else:
        status1 = "✅ ACTIVE — Price within entry zone"
        status2 = f"{fp(stale_low)} ← {fp(current_price)} → {fp(stale_high)}"

    text = (
        f"⏰ <b>REMINDER — {sym} {d}</b>\n"
        f"Alert sent 30 min ago at {orig_time}\n"
        f"\n"
        f"{status1}\n"
        f"{status2}\n"
        f"\n"
        f"⏱ {now_est_short()}"
    )
    try:
        _tg_post(text)
        print(f"  [telegram] reminder sent {d} {sym}")
    except Exception as e:
        print(f"  [telegram] reminder error: {e}")


_lock        = threading.Lock()
_price_pause = threading.Event()   # set() while full scan runs; price loop skips fetches during this window
_price_ex    = ThreadPoolExecutor(max_workers=len(SYMBOLS), thread_name_prefix="price-fetch")
# Persistent executor — reused every cycle to avoid creating/destroying 8 threads per second
_state = {
    "last_price_update": None,
    "last_scan": None,
    "next_scan_epoch": None,
    "scan_cycle": 0,
    "symbols": {s: {
        "price": None, "change_pct": None,
        "long_score": None, "short_score": None, "max_lev": None, "trend": None, "tp_dollar": None, "error": None,
        "stale": False, "j5": None, "bid_pct": None, "ask_pct": None, "adx": None,
        "long_suppressed": False, "short_suppressed": False, "session_bonus": 0.0,
        "long_block": None, "short_block": None,
        "long_checklist": [], "short_checklist": [], "extra": None,
        "long_trade": None, "short_trade": None,
        "last_alert": None,
    } for s in SYMBOLS},
    "alerts": deque(maxlen=3),
    "balance_usdt": None,
}

# Updated atomically at the start of every scan cycle.
# The watchdog thread uses this to detect a stale/dead scan loop.
_last_scan_dt = datetime.now(tz=EST)


# ── Fast price loop (every PRICE_INTERVAL seconds) ───────────────────────────

def _fetch_price(symbol):
    ticker = fetch_ticker(symbol)
    return symbol, float(ticker.get("lastPrice", 0)), float(ticker.get("riseFallRate", 0)) * 100


def run_price_loop():
    # Uses the module-level _price_ex persistent executor — no per-cycle create/destroy cost.
    while True:
        if not _price_pause.is_set():          # skip price fetches while the full scan is running
            futures = {_price_ex.submit(_fetch_price, s): s for s in SYMBOLS}
            try:
                for fut in as_completed(futures, timeout=10):  # 10s wall-clock ceiling
                    try:
                        sym, price, change_pct = fut.result()
                        with _lock:
                            _state["symbols"][sym]["price"]      = price
                            _state["symbols"][sym]["change_pct"] = change_pct
                    except Exception as e:
                        print(f"  [price] {futures[fut]}: {e}")
            except TimeoutError:
                print("  [price] fetch timed out (10s) — skipping this cycle")
                for _f in futures:
                    _f.cancel()     # release any queued (not running) futures
            with _lock:
                _state["last_price_update"] = now_est_short()
        time.sleep(PRICE_INTERVAL)


# ── Full scan loop (every SCAN_INTERVAL seconds) ──────────────────────────────

def run_scanner():
    global _last_alert_time, pending_alerts, daily_loss_total, daily_loss_reset_date, _daily_limit_notified, _last_scan_dt
    while True:
        _last_scan_dt = datetime.now(tz=EST)   # heartbeat for watchdog
        cycle_time = now_est()
        with _lock:
            _state["last_scan"] = cycle_time
            _state["scan_cycle"] += 1

        # ── Daily loss reset at midnight EST ──────────────────────────────
        today = datetime.now(tz=EST).date()
        if daily_loss_reset_date != today:
            daily_loss_total      = 0.0
            daily_loss_reset_date = today
            _daily_limit_notified = False

        cycle_bonus, _cycle_sess = get_session_bonus()

        # ── Fetch all symbols in parallel, hard-bounded to 50s ────────────
        # Sequential fetches took up to 5 calls × 10s × 7 symbols = 350s/cycle.
        # Parallel reduces that to the worst single-symbol time (~25s)
        # and the 50s ceiling kills any hangers.
        #
        # IMPORTANT: _price_pause.set() and _price_pause.clear() MUST both be
        # inside the same try/finally so the event can never be left stuck SET
        # if ThreadPoolExecutor() raises (e.g. thread exhaustion from abandoned
        # workers accumulating over many stalled cycles).
        _scan_results: dict = {}
        _ex = None
        try:
            _ex = ThreadPoolExecutor(max_workers=len(SYMBOLS))
            _price_pause.set()                 # stop price polling while scan fetches run
            _futs = {}
            for _i, _sym in enumerate(SYMBOLS):
                _futs[_ex.submit(scan_symbol, _sym)] = _sym
                if _i < len(SYMBOLS) - 1:
                    time.sleep(0.5)            # 0.5s stagger — gentle pacing, no burst
            try:
                for _fut in as_completed(_futs, timeout=45):  # 3s stagger + retry back-off headroom
                    _sym = _futs[_fut]
                    try:
                        _scan_results[_sym] = _fut.result()
                    except Exception as _fe:
                        print(f"  {_sym}: fetch failed — {_fe}")
                        with _lock:
                            _state["symbols"][_sym]["error"] = str(_fe)
                            _state["symbols"][_sym]["stale"] = True
            except TimeoutError:
                print("SCAN: parallel fetch timed out (45s) — processing partial results")
        finally:
            if _ex is not None:
                _ex.shutdown(wait=False, cancel_futures=True)
            _price_pause.clear()               # always resume price polling

        for symbol in SYMBOLS:
            _scan_result = _scan_results.get(symbol)
            if _scan_result is None:
                continue
            try:
                price, change_pct, ls, ss, ld, sd, c5m, trend, j15, extra = _scan_result
                # Compute trade params once — reused for both state update and alert logic
                e_l, sl_l, tp1_l, tp2_l, lev_l, slp_l = calc_trade_params_long(price, c5m, symbol=symbol)
                e_s, sl_s, tp1_s, tp2_s, lev_s, slp_s = calc_trade_params_short(price, c5m, symbol=symbol)
                cur_lev   = max(lev_l, lev_s)
                # TP $ using direction-specific tier so dashboard matches what the alert would use
                _tp1_pct_l      = abs(tp1_l - e_l) / e_l if e_l > 0 else 0
                _tp1_pct_s      = abs(tp1_s - e_s) / e_s if e_s > 0 else 0
                _tm_l, _tlv_l, _ = get_tier(ls)
                _tm_s, _tlv_s, _ = get_tier(ss)
                tp_dollar_long  = _tm_l * _tlv_l * _tp1_pct_l
                tp_dollar_short = _tm_s * _tlv_s * _tp1_pct_s
                tp_dollar = tp_dollar_long if ls >= ss else tp_dollar_short
                _raw_liq_l = e_l * (1 - 1 / lev_l + 0.005) if lev_l > 0 else 0
                liq_l      = _raw_liq_l if _raw_liq_l > 0 else None  # None = unliquidatable (lev < ~1×)
                _raw_liq_s = e_s * (1 + 1 / lev_s - 0.005) if lev_s > 0 else 0
                liq_s      = _raw_liq_s if _raw_liq_s > e_s else None  # sanity: liq must be above entry for short
                with _lock:
                    long_sup  = ls >= ALERT_THRESHOLD and trend in BEARISH_TRENDS
                    short_sup = ss >= ALERT_THRESHOLD and trend in BULLISH_TRENDS
                    _state["symbols"][symbol].update({
                        "price": price, "change_pct": change_pct,
                        "long_score": ls, "short_score": ss, "max_lev": cur_lev,
                        "trend": trend, "tp_dollar": tp_dollar, "error": None, "stale": False,
                        "j5": (extra.get("ind5m") or {}).get("j") if extra else None,
                        "bid_pct": extra.get("bid_pct") if extra else None,
                        "ask_pct": extra.get("ask_pct") if extra else None,
                        "adx": extra.get("adx") if extra else None,
                        "long_suppressed": long_sup, "short_suppressed": short_sup,
                        "session_bonus": cycle_bonus,
                        "long_checklist": ld, "short_checklist": sd, "extra": extra,
                        "long_trade": {
                            "entry": e_l, "sl": sl_l, "tp1": tp1_l, "tp2": tp2_l,
                            "lev": lev_l, "sl_pct": slp_l, "liq": liq_l,
                        },
                        "short_trade": {
                            "entry": e_s, "sl": sl_s, "tp1": tp1_s, "tp2": tp2_s,
                            "lev": lev_s, "sl_pct": slp_s, "liq": liq_s,
                        },
                    })
                # ── LONG alert check ──────────────────────────────────────
                long_block_reason = None
                _lpk = f"{symbol}_LONG"
                _score_thr = BTC_MIN_SCORE if symbol == 'BTC' else ALERT_THRESHOLD
                _tp_thr    = BTC_MIN_TP    if symbol == 'BTC' else MIN_TP_DOLLARS
                if ls >= _score_thr - 1:
                    entry, sl, tp1, tp2, lev, slp = e_l, sl_l, tp1_l, tp2_l, lev_l, slp_l
                    _alert_margin, _alert_lev, _alert_tier = get_tier(ls)
                    tp1_gain = _alert_margin * _alert_lev * _tp1_pct_l
                    rr = abs(tp1 - entry) / abs(sl - entry) if sl != entry else 0
                    bonus, sess_label = get_session_bonus()
                    eff = ls + bonus
                    trend_str   = (trend or "").strip()
                    trend_lower = trend_str.lower()
                    is_long_misaligned = trend_lower in [t.lower() for t in BEARISH_TRENDS]
                    j5      = (extra.get("ind5m") or {}).get("j") if extra else None
                    bid_pct = extra.get("bid_pct") if extra else None
                    ask_pct = extra.get("ask_pct") if extra else None
                    adx_1h  = extra.get("adx") if extra else None
                    bad_j   = j5 is not None and j5 < -50
                    c1 = eff >= _score_thr
                    c2 = j5 is not None and not bad_j and -50 <= j5 < 15
                    c3 = not is_long_misaligned
                    c4 = bid_pct is not None and bid_pct >= 70
                    c5 = tp1_gain >= _tp_thr
                    # C6: Choppy+ADX>25 → standard threshold; Choppy+ADX<=25 or Neutral → 9
                    _ctr_score_thr_l = (
                        _score_thr            if trend_str == "Choppy" and adx_1h is not None and adx_1h > 25
                        else COUNTER_TREND_MIN_SCORE if trend_str in NEUTRAL_TRENDS
                        else _score_thr
                    )
                    c7_ctr = eff >= _ctr_score_thr_l
                    j5_s  = f"{j5:.1f}"      if j5      is not None else "N/A"
                    bp_s  = f"{bid_pct:.1f}" if bid_pct is not None else "N/A"
                    if bid_pct is not None:
                        print(f"{symbol} depth: {bid_pct:.1f}% required 70% PASS={bid_pct >= 70}")
                    print(f"[{symbol}] LONG check (min score={_score_thr} min TP=${_tp_thr}):")
                    print(f"  C1 score: eff={eff:.1f} >= {_score_thr} → {'✅' if c1 else '❌'}")
                    print(f"  C2 KDJ:   J5={j5_s} < 15 → {'✅' if c2 else '❌'}")
                    print(f"  C3 trend: {trend_str} → {'✅' if c3 else '❌ suppressed'}")
                    print(f"  C4 depth: bid={bp_s}% >= 70 → {'✅' if c4 else '❌'}")
                    print(f"  C5 TP:    ${tp1_gain:.2f} >= ${_tp_thr:.0f} → {'✅' if c5 else '❌'}")
                    print(f"  C6 ctr:   trend={trend_str} eff={eff:.1f} >= {_ctr_score_thr_l} → {'✅' if c7_ctr else '❌'}")
                    if bad_j:
                        pending_alerts.pop(_lpk, None)
                    elif is_long_misaligned:
                        pending_alerts.pop(_lpk, None)
                        long_block_reason = "Trend misaligned 🚫"
                        print(f"  RESULT: BLOCKED - C3 trend (LONG in {trend_str})")
                    elif not c1:
                        pending_alerts.pop(_lpk, None)
                        long_block_reason = f"Score {eff:.1f} < {_score_thr}"
                        print(f"  RESULT: BLOCKED - C1 score")
                    elif not c2:
                        pending_alerts.pop(_lpk, None)
                        long_block_reason = f"KDJ J={j5_s} not < 15"
                        print(f"  RESULT: BLOCKED - C2 KDJ")
                    elif not c4:
                        pending_alerts.pop(_lpk, None)
                        long_block_reason = f"Depth bid={bp_s}% < 70"
                        print(f"  RESULT: BLOCKED - C4 depth")
                    elif not c5:
                        pending_alerts.pop(_lpk, None)
                        long_block_reason = f"TP ${tp1_gain:.2f} < ${_tp_thr:.0f}"
                        print(f"  RESULT: BLOCKED - C5 TP ${tp1_gain:.2f} < ${_tp_thr:.0f}")
                    elif not c7_ctr:
                        pending_alerts.pop(_lpk, None)
                        long_block_reason = f"Counter-trend: score {eff:.1f} < {_ctr_score_thr_l}"
                        print(f"  RESULT: BLOCKED - C7 counter-trend score {eff:.1f} < {_ctr_score_thr_l}")
                    else:
                        print(f"  RESULT: all checks pass")
                        _cd_key = _lpk
                        _now_dt = datetime.now()
                        # ── Cooldown ──────────────────────────────────────
                        _last = _last_alert_time.get(_cd_key)
                        if _last is not None and (_now_dt - _last).total_seconds() < 900:
                            _elapsed = (_now_dt - _last).total_seconds()
                            _rm = int((900 - _elapsed) / 60)
                            _rs = int((900 - _elapsed) % 60)
                            long_block_reason = f"Cooldown {_rm}m"
                            print(f"  COOLDOWN: {_cd_key} {_rm}m{_rs:02d}s remaining")
                            pending_alerts.pop(_lpk, None)
                            with _lock:
                                _state["symbols"][symbol]["long_block"] = long_block_reason
                            continue
                        # ── Consecutive confirmation ───────────────────────
                        if _lpk not in pending_alerts:
                            pending_alerts[_lpk] = _now_dt
                            long_block_reason = "Pending ⏱"
                            print(f"  PENDING: {_lpk} — awaiting 2nd consecutive qualifying scan")
                            with _lock:
                                _state["symbols"][symbol]["long_block"] = long_block_reason
                            continue
                        # Second consecutive qualifying scan — fire alert
                        pending_alerts.pop(_lpk, None)
                        print(f"  CONFIRMED: {_lpk} — firing alert")
                        # ── Daily loss limit (MEDIUM / LARGE mode) ────────
                        if ACCOUNT_MODE in ("MEDIUM", "LARGE") and daily_loss_total >= DAILY_LOSS_LIMIT:
                            long_block_reason = "Daily loss limit 🛑"
                            if not _daily_limit_notified:
                                threading.Thread(target=_tg_post, args=(
                                    f"🛑 Daily loss limit ${DAILY_LOSS_LIMIT:.0f} reached. Alerts paused until midnight EST.",
                                ), daemon=True).start()
                                _daily_limit_notified = True
                            print(f"  DAILY LOSS LIMIT: suppressing LONG {symbol}")
                            with _lock:
                                _state["symbols"][symbol]["long_block"] = long_block_reason
                            continue
                        alignment = "✅ Trend confirmed" if trend_lower in [t.lower() for t in BULLISH_TRENDS] else "⚠️ Counter-trend (neutral)"
                        alert = {
                            "time": cycle_time, "symbol": symbol, "direction": "LONG",
                            "score": ls, "price": price, "entry": entry, "sl": sl,
                            "tp1": tp1, "tp2": tp2, "max_lev": lev, "sl_pct": slp,
                            "liq_price": calc_liq_price(entry, _alert_lev, "LONG"),
                            "trend": trend, "rr_ratio": rr, "tp_dollar_gain": tp1_gain,
                            "alignment": alignment, "session_label": sess_label,
                            "session_bonus": bonus, "effective_score": eff,
                            "j15": j15, "checklist": ld,
                            "j5": j5, "bid_pct": bid_pct, "ask_pct": ask_pct,
                            "adx": extra.get("adx"),
                            **dict(zip(("stale_low", "stale_high"), calc_stale_zone(entry, sl, "LONG"))),
                            "tiered_margin": _alert_margin, "tiered_lev": _alert_lev,
                            "tier_label": _alert_tier,
                        }
                        with _lock:
                            _state["alerts"].appendleft(alert)
                            _state["symbols"][symbol]["last_alert"] = alert
                            if symbol in _pending_reminders:
                                _pending_reminders[symbol].set()
                            cancel_event = threading.Event()
                            _pending_reminders[symbol] = cancel_event
                        _last_alert_time[_cd_key] = _now_dt
                        print(f"  ALERT SENT: {_cd_key} at {_now_dt}")
                        print(f"[LONG ALERT] {symbol} score={ls}/13 eff={eff:.1f} rr={rr:.2f} tp=${tp1_gain:.2f}")
                        threading.Thread(target=_fire_trade, args=(alert, cancel_event), daemon=True).start()
                else:
                    pending_alerts.pop(_lpk, None)

                # ── SHORT alert check ─────────────────────────────────────
                short_block_reason = None
                _spk = f"{symbol}_SHORT"
                _score_thr = BTC_MIN_SCORE if symbol == 'BTC' else ALERT_THRESHOLD
                _tp_thr    = BTC_MIN_TP    if symbol == 'BTC' else MIN_TP_DOLLARS
                if ss >= _score_thr - 1:
                    entry, sl, tp1, tp2, lev, slp = e_s, sl_s, tp1_s, tp2_s, lev_s, slp_s
                    _alert_margin, _alert_lev, _alert_tier = get_tier(ss)
                    tp1_gain = _alert_margin * _alert_lev * _tp1_pct_s
                    rr = abs(tp1 - entry) / abs(sl - entry) if sl != entry else 0
                    bonus, sess_label = get_session_bonus()
                    eff = ss + bonus
                    trend_str   = (trend or "").strip()
                    trend_lower = trend_str.lower()
                    is_short_misaligned = trend_lower in [t.lower() for t in BULLISH_TRENDS]
                    j5      = (extra.get("ind5m") or {}).get("j") if extra else None
                    bid_pct = extra.get("bid_pct") if extra else None
                    ask_pct = extra.get("ask_pct") if extra else None
                    adx_1h  = extra.get("adx") if extra else None
                    bad_j   = j5 is not None and j5 < -50
                    c1 = eff >= _score_thr
                    c2 = j5 is not None and not bad_j and j5 > 85
                    c3 = not is_short_misaligned
                    c4 = ask_pct is not None and ask_pct >= 70
                    c5 = tp1_gain >= _tp_thr
                    # C6: Choppy+ADX>25 → standard threshold; Choppy+ADX<=25 or Neutral → 9
                    _ctr_score_thr_s = (
                        _score_thr            if trend_str == "Choppy" and adx_1h is not None and adx_1h > 25
                        else COUNTER_TREND_MIN_SCORE if trend_str in NEUTRAL_TRENDS
                        else _score_thr
                    )
                    c7_ctr = eff >= _ctr_score_thr_s
                    j5_s  = f"{j5:.1f}"      if j5      is not None else "N/A"
                    ap_s  = f"{ask_pct:.1f}" if ask_pct is not None else "N/A"
                    if ask_pct is not None:
                        print(f"{symbol} depth: {ask_pct:.1f}% required 70% PASS={ask_pct >= 70}")
                    print(f"[{symbol}] SHORT check (min score={_score_thr} min TP=${_tp_thr}):")
                    print(f"  C1 score: eff={eff:.1f} >= {_score_thr} → {'✅' if c1 else '❌'}")
                    print(f"  C2 KDJ:   J5={j5_s} > 85 → {'✅' if c2 else '❌'}")
                    print(f"  C3 trend: {trend_str} → {'✅' if c3 else '❌ suppressed'}")
                    print(f"  C4 depth: ask={ap_s}% >= 70 → {'✅' if c4 else '❌'}")
                    print(f"  C5 TP:    ${tp1_gain:.2f} >= ${_tp_thr:.0f} → {'✅' if c5 else '❌'}")
                    print(f"  C6 ctr:   trend={trend_str} eff={eff:.1f} >= {_ctr_score_thr_s} → {'✅' if c7_ctr else '❌'}")
                    if bad_j:
                        pending_alerts.pop(_spk, None)
                    elif is_short_misaligned:
                        pending_alerts.pop(_spk, None)
                        short_block_reason = "Trend misaligned 🚫"
                        print(f"  RESULT: BLOCKED - C3 trend (SHORT in {trend_str})")
                    elif not c1:
                        pending_alerts.pop(_spk, None)
                        short_block_reason = f"Score {eff:.1f} < {_score_thr}"
                        print(f"  RESULT: BLOCKED - C1 score")
                    elif not c2:
                        pending_alerts.pop(_spk, None)
                        short_block_reason = f"KDJ J={j5_s} not > 85"
                        print(f"  RESULT: BLOCKED - C2 KDJ")
                    elif not c4:
                        pending_alerts.pop(_spk, None)
                        short_block_reason = f"Depth ask={ap_s}% < 70"
                        print(f"  RESULT: BLOCKED - C4 depth")
                    elif not c5:
                        pending_alerts.pop(_spk, None)
                        short_block_reason = f"TP ${tp1_gain:.2f} < ${_tp_thr:.0f}"
                        print(f"  RESULT: BLOCKED - C5 TP ${tp1_gain:.2f} < ${_tp_thr:.0f}")
                    elif not c7_ctr:
                        pending_alerts.pop(_spk, None)
                        short_block_reason = f"Counter-trend: score {eff:.1f} < {_ctr_score_thr_s}"
                        print(f"  RESULT: BLOCKED - C7 counter-trend score {eff:.1f} < {_ctr_score_thr_s}")
                    else:
                        print(f"  RESULT: all checks pass")
                        _cd_key = _spk
                        _now_dt = datetime.now()
                        # ── Cooldown ──────────────────────────────────────
                        _last = _last_alert_time.get(_cd_key)
                        if _last is not None and (_now_dt - _last).total_seconds() < 900:
                            _elapsed = (_now_dt - _last).total_seconds()
                            _rm = int((900 - _elapsed) / 60)
                            _rs = int((900 - _elapsed) % 60)
                            short_block_reason = f"Cooldown {_rm}m"
                            print(f"  COOLDOWN: {_cd_key} {_rm}m{_rs:02d}s remaining")
                            pending_alerts.pop(_spk, None)
                            with _lock:
                                _state["symbols"][symbol]["short_block"] = short_block_reason
                            continue
                        # ── Consecutive confirmation ───────────────────────
                        if _spk not in pending_alerts:
                            pending_alerts[_spk] = _now_dt
                            short_block_reason = "Pending ⏱"
                            print(f"  PENDING: {_spk} — awaiting 2nd consecutive qualifying scan")
                            with _lock:
                                _state["symbols"][symbol]["short_block"] = short_block_reason
                            continue
                        # Second consecutive qualifying scan — fire alert
                        pending_alerts.pop(_spk, None)
                        print(f"  CONFIRMED: {_spk} — firing alert")
                        # ── Daily loss limit (MEDIUM / LARGE mode) ────────
                        if ACCOUNT_MODE in ("MEDIUM", "LARGE") and daily_loss_total >= DAILY_LOSS_LIMIT:
                            short_block_reason = "Daily loss limit 🛑"
                            if not _daily_limit_notified:
                                threading.Thread(target=_tg_post, args=(
                                    f"🛑 Daily loss limit ${DAILY_LOSS_LIMIT:.0f} reached. Alerts paused until midnight EST.",
                                ), daemon=True).start()
                                _daily_limit_notified = True
                            print(f"  DAILY LOSS LIMIT: suppressing SHORT {symbol}")
                            with _lock:
                                _state["symbols"][symbol]["short_block"] = short_block_reason
                            continue
                        alignment = "✅ Trend confirmed" if trend_lower in [t.lower() for t in BEARISH_TRENDS] else "⚠️ Counter-trend (neutral)"
                        alert = {
                            "time": cycle_time, "symbol": symbol, "direction": "SHORT",
                            "score": ss, "price": price, "entry": entry, "sl": sl,
                            "tp1": tp1, "tp2": tp2, "max_lev": lev, "sl_pct": slp,
                            "liq_price": calc_liq_price(entry, _alert_lev, "SHORT"),
                            "trend": trend, "rr_ratio": rr, "tp_dollar_gain": tp1_gain,
                            "alignment": alignment, "session_label": sess_label,
                            "session_bonus": bonus, "effective_score": eff,
                            "j15": j15, "checklist": sd,
                            "j5": j5, "bid_pct": bid_pct, "ask_pct": ask_pct,
                            "adx": extra.get("adx"),
                            **dict(zip(("stale_low", "stale_high"), calc_stale_zone(entry, sl, "SHORT"))),
                            "tiered_margin": _alert_margin, "tiered_lev": _alert_lev,
                            "tier_label": _alert_tier,
                        }
                        with _lock:
                            _state["alerts"].appendleft(alert)
                            _state["symbols"][symbol]["last_alert"] = alert
                            if symbol in _pending_reminders:
                                _pending_reminders[symbol].set()
                            cancel_event = threading.Event()
                            _pending_reminders[symbol] = cancel_event
                        _last_alert_time[_cd_key] = _now_dt
                        print(f"  ALERT SENT: {_cd_key} at {_now_dt}")
                        print(f"[SHORT ALERT] {symbol} score={ss}/12 eff={eff:.1f} rr={rr:.2f} tp=${tp1_gain:.2f}")
                        threading.Thread(target=_fire_trade, args=(alert, cancel_event), daemon=True).start()
                else:
                    pending_alerts.pop(_spk, None)

                if ls < ALERT_THRESHOLD - 1 and ss < ALERT_THRESHOLD - 1:
                    print(f"  {symbol:<12} ${price:<12.6g} {change_pct:+.2f}%  L:{ls}/12  S:{ss}/11")

                # Store block reasons for dashboard display
                with _lock:
                    _state["symbols"][symbol]["long_block"]  = long_block_reason
                    _state["symbols"][symbol]["short_block"] = short_block_reason
            except Exception as e:
                print(f"  {symbol}: ERROR — {e}")
                with _lock:
                    _state["symbols"][symbol]["error"] = str(e)
                    _state["symbols"][symbol]["stale"] = True
            pass   # parallel fetch replaced sequential gap

        next_epoch = time.time() + SCAN_INTERVAL
        with _lock:
            _state["next_scan_epoch"] = next_epoch
        if pending_alerts:
            print(f"Pending:   { {k: 'awaiting confirm' for k in pending_alerts} }")
        if _last_alert_time:
            _now_cd = datetime.now()
            print(f"Cooldowns: { {k: f'{int(900 - (_now_cd-v).total_seconds())}s left' for k,v in _last_alert_time.items() if (_now_cd-v).total_seconds() < 900} }")
        _last_scan_dt = datetime.now(tz=EST)              # reset heartbeat after scan so sleep doesn't look stale
        with _lock:
            _state["last_scan"] = now_est()               # update to COMPLETED timestamp (not just cycle-start)
        print(f"  Next full scan in {SCAN_INTERVAL}s\n")
        time.sleep(SCAN_INTERVAL)


# ── Balance polling loop (every 60s) ──────────────────────────────────────────

def _balance_loop():
    """Fetch Hyperliquid account balance every 60 seconds and store in _state."""
    from hyperliquid_api import get_balance
    while True:
        try:
            bal = get_balance()
            with _lock:
                _state["balance_usdt"] = bal if bal and bal > 0 else None
        except Exception as e:
            print(f"  [balance] fetch error: {e}")
        time.sleep(60)


# ── JSON state endpoint ────────────────────────────────────────────────────────

def get_state_json():
    with _lock:
        alerts = list(_state["alerts"])
        syms   = {k: dict(v) for k, v in _state["symbols"].items()}
        # Compute per-symbol cooldown remainders and pending state
        for sym, d in syms.items():
            d["long_cooldown_secs"]  = _cooldown_remaining(f"{sym}_LONG")
            d["short_cooldown_secs"] = _cooldown_remaining(f"{sym}_SHORT")
            d["long_pending"]  = f"{sym}_LONG"  in pending_alerts
            d["short_pending"] = f"{sym}_SHORT" in pending_alerts
        _age = (datetime.now(tz=EST) - _last_scan_dt).total_seconds()
        return json.dumps({
            "scan_cycle":        _state["scan_cycle"],
            "last_scan":         _state["last_scan"],
            "last_price_update": _state["last_price_update"],
            "next_scan_epoch":   _state["next_scan_epoch"],
            "loop_healthy":      _age < 90,   # 90s: 48.5s max fetch + 20s sleep + 21.5s buffer
            "loop_age_secs":     round(_age, 1),
            "balance_usdt":      _state.get("balance_usdt"),
            "symbols":           syms,
            "alerts": [{
                "time": a["time"], "symbol": a["symbol"], "direction": a["direction"],
                "score": a["score"], "price": a["price"], "entry": a["entry"],
                "sl": a["sl"], "tp1": a["tp1"], "tp2": a["tp2"],
                "max_lev": a["max_lev"], "sl_pct": a["sl_pct"],
                "liq_price": a.get("liq_price"), "trend": a.get("trend"),
                "rr_ratio": a.get("rr_ratio"), "tp_dollar_gain": a.get("tp_dollar_gain"),
                "alignment": a.get("alignment"), "session_label": a.get("session_label"),
                "session_bonus": a.get("session_bonus"), "effective_score": a.get("effective_score"),
                "j15": a.get("j15"),
                "checklist": a["checklist"],
                "stale_low": a.get("stale_low"), "stale_high": a.get("stale_high"),
            } for a in alerts],
        })


# ── Detail page JSON endpoint ──────────────────────────────────────────────────

def get_detail_json(symbol):
    with _lock:
        d = dict(_state["symbols"].get(symbol, {}))
        next_scan_epoch = _state.get("next_scan_epoch")
    if not d:
        return json.dumps({"error": "Symbol not found"})
    return json.dumps({
        "symbol":           symbol,
        "price":            d.get("price"),
        "change_pct":       d.get("change_pct"),
        "trend":            d.get("trend"),
        "long_score":       d.get("long_score"),
        "short_score":      d.get("short_score"),
        "max_lev":          d.get("max_lev"),
        "tp_dollar":        d.get("tp_dollar"),
        "session_bonus":    d.get("session_bonus", 0),
        "long_block":       d.get("long_block"),
        "short_block":      d.get("short_block"),
        "long_suppressed":  d.get("long_suppressed", False),
        "short_suppressed": d.get("short_suppressed", False),
        "long_checklist":   d.get("long_checklist", []),
        "short_checklist":  d.get("short_checklist", []),
        "extra":            d.get("extra"),
        "long_trade":       d.get("long_trade"),
        "short_trade":      d.get("short_trade"),
        "last_alert":       d.get("last_alert"),
        "adx":              d.get("adx"),
        "next_scan_epoch":  next_scan_epoch,
    })


def build_detail_html(symbol):
    initial_json = get_detail_json(symbol)
    return f"""<!DOCTYPE html>
<html lang="en">
<head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{symbol} — Hyperliquid Scanner v{BUILD_TIME}</title>
<style>
  :root{{--bg:#0d1117;--surface:#161b22;--border:#30363d;--green:#3fb950;--red:#f85149;--text:#e6edf3;--dim:#8b949e;--font:ui-monospace,SFMono-Regular,monospace}}
  *{{box-sizing:border-box;margin:0;padding:0}}
  body{{background:var(--bg);color:var(--text);font-family:var(--font);font-size:13px;min-height:100vh}}
  header{{background:var(--surface);border-bottom:1px solid var(--border);padding:.6rem 1.25rem;display:flex;align-items:center;gap:.65rem;flex-wrap:wrap}}
  .back-link{{color:var(--dim);text-decoration:none;font-size:.8rem;padding:.2rem .5rem;border:1px solid var(--border);border-radius:6px;transition:color .15s}}
  .back-link:hover{{color:var(--text)}}
  header h1{{font-size:1rem;letter-spacing:.05em}}
  .status-dot{{width:8px;height:8px;border-radius:50%;background:var(--green);display:inline-block;margin-right:.4rem;animation:pulse 2s infinite}}
  .green{{color:var(--green)}} .red{{color:var(--red)}} .dim{{color:var(--dim)}}
  .change{{font-size:.85rem;font-weight:bold}}
  .countdown{{color:var(--dim);font-size:.75rem;margin-left:auto}}
  .sess{{border-radius:12px;padding:.2rem .55rem;font-size:.75rem;display:inline-flex;align-items:center;gap:.3rem;border:1px solid;transition:all .3s}}
  .sess-open{{background:#0d2e1a;border-color:#3fb950;color:#3fb950}}
  .sess-prime{{background:#0a3d20;border-color:#56d364;color:#56d364;font-weight:bold;box-shadow:0 0 8px #3fb95044}}
  .sess-closed{{background:#161b22;border-color:#30363d;color:#8b949e}}
  .row-banner{{background:#0d1117;border-bottom:2px solid var(--border);padding:.65rem 1.25rem;display:flex;align-items:flex-start;gap:2rem;flex-wrap:wrap}}
  .rb-cell{{display:flex;flex-direction:column;gap:.15rem}}
  .rb-label{{color:var(--dim);font-size:.68rem;text-transform:uppercase;letter-spacing:.07em}}
  .rb-price{{font-size:1rem;font-weight:bold}}
  .rb-val{{font-size:.85rem;font-weight:bold}}
  .block-reason{{font-size:.68rem;color:var(--dim);margin-top:.1rem}}
  .sess-badge{{background:#0a3d20;border:1px solid #56d364;color:#56d364;border-radius:10px;padding:.15rem .45rem;font-size:.72rem;display:inline-block}}
  .container{{max-width:1200px;margin:0 auto;padding:1rem}}
  .detail-grid{{display:grid;grid-template-columns:minmax(0,2fr) minmax(0,1fr);gap:1rem;align-items:start}}
  @media(max-width:820px){{.detail-grid{{grid-template-columns:1fr}}}}
  .card{{background:var(--surface);border:1px solid var(--border);border-radius:8px;margin-bottom:.75rem;overflow:hidden}}
  .card-title{{padding:.5rem .85rem;font-size:.72rem;font-weight:bold;letter-spacing:.09em;text-transform:uppercase;color:var(--dim);border-bottom:1px solid var(--border)}}
  .card-body{{padding:.7rem .85rem}}
  .dir-section{{margin-bottom:1rem}}
  .dir-section:last-child{{margin-bottom:0}}
  .dir-header{{display:flex;align-items:baseline;gap:.5rem;margin-bottom:.55rem;padding:.35rem .6rem;border-radius:6px}}
  .dir-header.long{{background:#0d2e1a;border:1px solid #3fb950;border-left:3px solid #3fb950}}
  .dir-header.short{{background:#2d1010;border:1px solid #f85149;border-left:3px solid #f85149}}
  .dir-score{{font-size:.9rem;font-weight:bold}}
  .dir-tally{{font-size:.75rem;color:var(--dim)}}
  .dir-block{{font-size:.72rem;color:var(--dim);margin-left:auto;white-space:nowrap}}
  .checklist-grid{{display:grid;grid-template-columns:1fr 1fr;gap:.15rem .75rem}}
  .cl-pass{{color:var(--green);font-size:.75rem}} .cl-fail{{color:var(--dim);font-size:.75rem}} .cl-neutral{{color:#8b949e;font-size:.75rem}}
  .ma-section{{margin-bottom:.65rem}}
  .ma-section:last-child{{margin-bottom:0}}
  .ma-tf-label{{font-size:.68rem;color:var(--dim);text-transform:uppercase;letter-spacing:.07em;margin-bottom:.25rem;padding-bottom:.2rem;border-bottom:1px solid var(--border)}}
  .ma-row{{display:flex;align-items:center;padding:.2rem 0;font-size:.78rem;gap:.3rem}}
  .ma-name{{color:var(--dim);width:4rem;flex-shrink:0}}
  .ma-val{{font-weight:bold;flex:1;text-align:right}}
  .ma-arrow{{font-size:.7rem;width:1rem;text-align:center}}
  .ma-above{{color:var(--green)}} .ma-below{{color:var(--red)}}
  .ma-structure{{font-size:.7rem;margin-top:.3rem;padding:.2rem .4rem;border-radius:4px}}
  .ms-bull{{background:#0d2e1a;color:#3fb950}} .ms-bear{{background:#2d1010;color:#f85149}} .ms-mix{{background:#2b2200;color:#d29922}}
  .kdj-row{{display:flex;align-items:center;padding:.25rem 0;font-size:.78rem;border-bottom:1px solid #21262d}}
  .kdj-row:last-child{{border-bottom:none}}
  .kdj-tf{{color:var(--dim);width:2.5rem;flex-shrink:0}}
  .kdj-vals{{flex:1;text-align:right}}
  .trade-section{{margin-bottom:.75rem;padding-bottom:.75rem;border-bottom:1px solid var(--border)}}
  .trade-section:last-child{{margin-bottom:0;padding-bottom:0;border-bottom:none}}
  .trade-dir-header{{font-size:.75rem;font-weight:bold;padding:.3rem .5rem;border-radius:4px;margin-bottom:.4rem}}
  .tdh-long{{background:#0d2e1a;color:#3fb950}} .tdh-short{{background:#2d1010;color:#f85149}}
  .trade-row{{display:flex;justify-content:space-between;align-items:center;padding:.2rem 0;font-size:.78rem;border-bottom:1px solid #1c2128}}
  .trade-row:last-child{{border-bottom:none}}
  .tl{{color:var(--dim)}} .tv{{font-weight:bold}}
  .mkt-row{{display:flex;justify-content:space-between;align-items:center;padding:.22rem 0;font-size:.78rem;border-bottom:1px solid #1c2128}}
  .mkt-row:last-child{{border-bottom:none}}
  .mkt-label{{color:var(--dim)}}
  .depth-bar{{width:64px;height:5px;background:#30363d;border-radius:3px;overflow:hidden;display:inline-block;vertical-align:middle;margin-left:.4rem}}
  .depth-fill{{height:100%;border-radius:3px}}
  @keyframes pulse{{0%,100%{{opacity:1}}50%{{opacity:.4}}}}
  @keyframes flash{{0%{{background:#1f6feb44}}100%{{background:transparent}}}}
  .flash{{animation:flash .4s ease-out}}
  .tf-card{{background:#1c2333;border:1px solid #2a3548;border-radius:8px;overflow:hidden;margin-top:.75rem;font-family:ui-monospace,SFMono-Regular,monospace}}
  .tf-header{{display:flex;justify-content:space-between;align-items:center;padding:10px 14px;border-bottom:1px solid #2a3548;background:#212840}}
  .tf-header-title{{font-size:10px;font-weight:600;letter-spacing:.14em;text-transform:uppercase;color:#5a7aaa}}
  .tf-header-symbol{{font-size:10px;color:#3a4a60;letter-spacing:.06em}}
  .tf-col-row{{display:grid;grid-template-columns:48px 1fr 1fr 1fr;padding:7px 14px 6px;border-bottom:1px solid #232e42;background:#1a2030}}
  .tf-col-lbl{{font-size:9px;font-weight:600;letter-spacing:.12em;text-transform:uppercase;color:#3a4e6a;text-align:center}}
  .tf-col-lbl:first-child{{color:transparent;text-align:left}}
  .tf-j-row{{display:grid;grid-template-columns:48px 1fr 1fr 1fr;gap:5px;padding:8px 10px 8px 14px;align-items:center;border-bottom:1px solid #232e42}}
  .tf-row-lbl{{font-size:9px;font-weight:600;letter-spacing:.12em;text-transform:uppercase;color:#4a6080}}
  .tf-j-cell{{display:flex;flex-direction:column;align-items:center;justify-content:center;padding:8px 4px 7px;border-radius:4px;border:1px solid transparent}}
  .tf-j-val{{font-size:15px;font-weight:600;line-height:1}}
  .tf-j-sub{{font-size:8px;margin-top:3px;opacity:.5}}
  .tf-j-badge{{font-size:7px;font-weight:700;letter-spacing:.08em;padding:1px 5px;border-radius:2px;margin-bottom:3px;line-height:1.5}}
  .j-oversold{{background:#0d2a1a;border-color:#1a5030;color:#22c55e}}
  .j-overbought{{background:#2a0d0d;border-color:#501a1a;color:#ef4444}}
  .j-neutral{{background:#1e2a3a;border-color:#2a3a50;color:#4a6a8a}}
  .badge-hot{{background:#22c55e;color:#000}} .badge-ob{{background:#ef4444;color:#fff}}
  .tf-depth-row{{display:grid;grid-template-columns:48px 1fr;align-items:center;padding:0 10px 0 14px}}
  .tf-depth-row+.tf-depth-row{{border-top:1px solid #232e42}}
  .tf-depth-banner{{display:flex;align-items:center;justify-content:space-between;padding:8px 12px;border-radius:4px;margin:7px 0;border:1px solid transparent}}
  .tf-depth-side{{font-size:9px;font-weight:600;letter-spacing:.1em;text-transform:uppercase;opacity:.75}}
  .tf-depth-pct{{font-size:15px;font-weight:600}}
  .tf-depth-tag{{font-size:8px;font-weight:500;letter-spacing:.1em;text-transform:uppercase;opacity:.55}}
  .bid-bull{{background:#0d2a1a;border-color:#1a5030;color:#22c55e}}
  .bid-bear{{background:#2a0d0d;border-color:#501a1a;color:#ef4444}}
  .bid-mixed{{background:#1e2a3a;border-color:#2a3a50;color:#4a6a8a}}
  .ask-bear{{background:#2a0d0d;border-color:#501a1a;color:#ef4444}}
  .ask-bull{{background:#0d2a1a;border-color:#1a5030;color:#22c55e}}
  .ask-mixed{{background:#1e2a3a;border-color:#2a3a50;color:#4a6a8a}}
  .alert-card-long{{background:#0a1f12;border:1px solid #3fb950;border-left:4px solid #3fb950;border-radius:8px;margin-bottom:.75rem;overflow:hidden}}
  .alert-card-short{{background:#1f0a0a;border:1px solid #f85149;border-left:4px solid #f85149;border-radius:8px;margin-bottom:.75rem;overflow:hidden}}
  .alert-card-hdr{{padding:.5rem .85rem;font-size:.78rem;font-weight:bold;display:flex;align-items:center;gap:.6rem;flex-wrap:wrap}}
  .alert-card-hdr-long{{background:#0d2e1a;color:#3fb950}}
  .alert-card-hdr-short{{background:#2d1010;color:#f85149}}
  .alert-ts{{color:var(--dim);font-size:.7rem;margin-left:auto;font-weight:normal}}
  .alert-setup-grid{{display:grid;grid-template-columns:1fr 1fr;gap:.15rem .75rem;padding:.65rem .85rem}}
  .asg-row{{display:flex;justify-content:space-between;align-items:center;font-size:.78rem;padding:.18rem 0;border-bottom:1px solid #1c2128}}
  .asg-row:last-child{{border-bottom:none}}
  .asg-label{{color:var(--dim)}} .asg-val{{font-weight:bold}}
  .alert-cl-wrap{{padding:0 .85rem .65rem}}
  .alert-cl-grid{{display:grid;grid-template-columns:1fr 1fr;gap:.1rem .6rem;margin-top:.3rem}}
</style>
</head>
<body>
<header>
  <a class="back-link" href="/">&#8592; Dashboard</a>
  <h1><span class="status-dot"></span>{symbol}</h1>
  <span id="d-price" class="rb-price">—</span>
  <span id="d-change" class="change dim"></span>
  <span id="d-trend"></span>
  <span class="badge" style="color:#8b949e">&#128197; Deployed: {BUILD_TIME}</span>
  <span class="sess" id="sess-euus">🌍🌎 EU/US 8a–12p</span>
  <span class="sess" id="sess-us">🌎 US 12p–5p</span>
  <span class="sess" id="sess-eu">🌍 EU 3a–8a</span>
  <span class="sess" id="sess-asia">🌏 Asia 5p–3a</span>
  <span class="countdown" id="countdown"></span>
</header>
<div class="row-banner" id="row-banner">
  <span class="dim" style="font-size:.8rem">Loading…</span>
</div>
<div class="container">
  <div id="last-alert-wrap"></div>
  <div class="detail-grid">
    <div>
      <div class="card">
        <div class="card-title">Analysis</div>
        <div class="card-body" id="analysis-body"><span class="dim">Waiting for first scan…</span></div>
      </div>
      <div class="tf-card" id="tf-signals"><span class="dim" style="font-size:.78rem">Waiting for first scan…</span></div>
    </div>
    <div>
      <div class="card">
        <div class="card-title">Moving Averages</div>
        <div class="card-body" id="ma-body"><span class="dim">Waiting…</span></div>
      </div>
      <div class="card">
        <div class="card-title">KDJ Oscillator</div>
        <div class="card-body" id="kdj-body"><span class="dim">Waiting…</span></div>
      </div>
      <div class="card">
        <div class="card-title">Trade Setup</div>
        <div class="card-body" id="trade-body"><span class="dim">Waiting…</span></div>
      </div>
      <div class="card">
        <div class="card-title">Depth Analysis</div>
        <div class="card-body" id="market-body"><span class="dim">Waiting…</span></div>
      </div>
    </div>
  </div>
</div>
<script>
const SYMBOL   = "{symbol}";
const SCAN_IV  = {SCAN_INTERVAL};
const PRICE_IV = {PRICE_INTERVAL};
const MARGIN   = {TRADE_MARGIN:.0f};
const MIN_TP   = {MIN_TP_DOLLARS:.0f};
let DATA = {initial_json};
let nextEpoch = Date.now() / 1000 + SCAN_IV;
const TS = {{
  'Strong Bull': ['🟢🟢','#0d2e1a','#3fb950'],
  'Bullish':     ['🟢',  '#112b1a','#56d364'],
  'Neutral':     ['⚪',  '#1c1c1c','#8b949e'],
  'Choppy':      ['🟡',  '#2b2200','#d29922'],
  'Bearish':     ['🔴',  '#2d1010','#f0786b'],
  'Strong Bear': ['🔴🔴','#3d0000','#ff6b6b'],
}};
function fp(v) {{
  if (v == null) return '—';
  return parseFloat(parseFloat(v).toPrecision(6)).toString();
}}
function fm(v, d) {{ return v == null ? '—' : parseFloat(v).toFixed(d); }}
function fPct(v) {{
  if (v == null) return '';
  const c = parseFloat(v);
  return (c >= 0 ? '+' : '') + c.toFixed(2) + '%';
}}
function tBadge(t, sm) {{
  if (!t) return '—';
  const s = TS[t] || TS['Choppy'];
  const pad = sm ? '.1rem .35rem' : '.2rem .55rem';
  const sz  = sm ? '.72rem' : '.82rem';
  return '<span style="background:' + s[1] + ';color:' + s[2] + ';padding:' + pad + ';border-radius:10px;font-size:' + sz + ';white-space:nowrap">' + s[0] + ' ' + t + '</span>';
}}
function renderBanner(d) {{
  const pe = document.getElementById('d-price');
  if (d.price != null) {{
    const np = '$' + fp(d.price);
    if (pe.textContent !== np) {{ pe.textContent = np; pe.classList.remove('flash'); void pe.offsetWidth; pe.classList.add('flash'); }}
  }}
  const ce = document.getElementById('d-change');
  if (d.change_pct != null) {{ ce.textContent = fPct(d.change_pct); ce.className = 'change ' + (parseFloat(d.change_pct) >= 0 ? 'green' : 'red'); }}
  const te = document.getElementById('d-trend');
  if (d.trend) te.innerHTML = tBadge(d.trend, false);
  const bonus = d.session_bonus || 0;
  const ls = d.long_score, ss = d.short_score;
  const lEff = (ls != null && bonus > 0) ? ' (' + (ls + bonus).toFixed(1) + ')' : '';
  const sEff = (ss != null && bonus > 0) ? ' (' + (ss + bonus).toFixed(1) + ')' : '';
  const lBlk = d.long_block  ? '<div class="block-reason">' + d.long_block  + '</div>' : '';
  const sBlk = d.short_block ? '<div class="block-reason">' + d.short_block + '</div>' : '';
  const tpCls = (d.tp_dollar != null && d.tp_dollar >= MIN_TP) ? 'green' : 'red';
  const sessBadge = bonus > 0 ? '<div class="rb-cell"><span class="rb-label">Session</span><span class="sess-badge">+' + bonus.toFixed(1) + ' bonus</span></div>' : '';
  document.getElementById('row-banner').innerHTML =
    '<div class="rb-cell"><span class="rb-label">Price</span><span class="rb-price">' + (d.price != null ? '$' + fp(d.price) : '—') + '</span>' +
      (d.change_pct != null ? '<span class="change ' + (parseFloat(d.change_pct) >= 0 ? 'green' : 'red') + '">' + fPct(d.change_pct) + '</span>' : '') + '</div>' +
    '<div class="rb-cell"><span class="rb-label">Trend</span>' + tBadge(d.trend, true) + '</div>' +
    '<div class="rb-cell"><span class="rb-label">TP $</span><span class="rb-val ' + tpCls + '">' + (d.tp_dollar != null ? '$' + fm(d.tp_dollar, 2) : '—') + '</span></div>' +
    '<div class="rb-cell"><span class="rb-label">Long Score</span><span class="rb-val green">' + (ls != null ? ls + '/12' + lEff + (d.long_suppressed ? ' 🚫' : '') : '—') + '</span>' + lBlk + '</div>' +
    '<div class="rb-cell"><span class="rb-label">Short Score</span><span class="rb-val red">'  + (ss != null ? ss + '/11' + sEff + (d.short_suppressed ? ' 🚫' : '') : '—') + '</span>' + sBlk + '</div>' +
    (d.adx != null ? '<div class="rb-cell"><span class="rb-label">ADX</span><span class="rb-val ' + (d.adx > 25 ? 'green' : 'dim') + '">' + d.adx.toFixed(1) + (d.adx > 25 ? ' ▲' : ' —') + '</span></div>' : '') +
    sessBadge +
    (function() {{
      const a = d.last_alert;
      if (!a || a.stale_low == null || a.stale_high == null || d.price == null) return '';
      const cur = parseFloat(d.price), sl = a.stale_low, sh = a.stale_high;
      if (cur < sl) {{
        const tag = a.direction === 'LONG' ? 'STALE DOWN' : 'STALE UP';
        return '<div class="rb-cell" style="flex-basis:100%"><span style="color:var(--red);font-size:.75rem">🚫 ' + tag + ' — ' + a.symbol + ' ' + a.direction + ' — Price below ' + fp(sl) + '</span></div>';
      }} else if (cur > sh) {{
        const tag = a.direction === 'LONG' ? 'STALE UP' : 'STALE DOWN';
        return '<div class="rb-cell" style="flex-basis:100%"><span style="color:var(--red);font-size:.75rem">🚫 ' + tag + ' — ' + a.symbol + ' ' + a.direction + ' — Price above ' + fp(sh) + '</span></div>';
      }} else {{
        return '<div class="rb-cell" style="flex-basis:100%"><span style="color:var(--green);font-size:.75rem">✅ ACTIVE — ' + a.symbol + ' ' + a.direction + ' — ' + fp(sl) + ' ← ' + fp(cur) + ' → ' + fp(sh) + '</span></div>';
      }}
    }})();
}}
function renderAnalysis(d) {{
  function section(dir, score, cl, blk, sup, bonus) {{
    const dc = dir === 'LONG' ? 'long' : 'short';
    const sc = dir === 'LONG' ? 'green' : 'red';
    const eff = (score != null && bonus > 0) ? ' — eff: ' + (score + bonus).toFixed(1) : '';
    const passed = (cl || []).filter(c => c.startsWith('[+]')).length;
    const supBadge = sup ? ' 🚫' : '';
    const blkBadge = blk ? '<span class="dir-block">' + blk + '</span>' : '';
    const items = (cl || []).map(c => '<div class="' + (c.startsWith('[+]') ? 'cl-pass' : c.startsWith('[~]') ? 'cl-neutral' : 'cl-fail') + '">' + c + '</div>').join('');
    return '<div class="dir-section">' +
      '<div class="dir-header ' + dc + '">' +
        '<span class="dir-score ' + sc + '">' + dir + '</span>' +
        '<span class="dir-tally">' + (score != null ? score + '/' + (dir === 'LONG' ? 12 : 11) + eff : '—') + supBadge + '</span>' +
        '<span class="dir-tally dim">(' + passed + '/' + (dir === 'LONG' ? 12 : 11) + ' passed)</span>' +
        blkBadge +
      '</div>' +
      '<div class="checklist-grid">' + (items || '<span class="dim" style="font-size:.78rem;grid-column:1/-1">Waiting for first scan…</span>') + '</div>' +
    '</div>';
  }}
  const b = d.session_bonus || 0;
  document.getElementById('analysis-body').innerHTML =
    section('LONG',  d.long_score,  d.long_checklist,  d.long_block,  d.long_suppressed,  b) +
    section('SHORT', d.short_score, d.short_checklist, d.short_block, d.short_suppressed, b);
}}
function maArrow(price, val) {{
  if (price == null || val == null) return '<span class="dim">—</span>';
  if (price > val) return '<span class="ma-above">▲</span>';
  if (price < val) return '<span class="ma-below">▼</span>';
  return '<span class="dim">≈</span>';
}}
function renderMAs(d) {{
  const p = d.price;
  const ex = d.extra;
  if (!ex) {{ document.getElementById('ma-body').innerHTML = '<span class="dim">No data yet</span>'; return; }}
  const i5 = ex.ind5m || {{}};
  const i1 = ex.ind1h || {{}};
  const m5 = i5.ma5, m10 = i5.ma10, m30 = i5.ma30, e20 = i5.ema20;
  let s5 = '', c5 = '';
  if (m5 && m10 && m30) {{
    if (m5 > m10 && m10 > m30)      {{ s5 = '↑ Bullish stack (MA5>MA10>MA30)'; c5 = 'ms-bull'; }}
    else if (m5 < m10 && m10 < m30) {{ s5 = '↓ Bearish stack (MA5<MA10<MA30)'; c5 = 'ms-bear'; }}
    else                             {{ s5 = '↔ Mixed / Choppy'; c5 = 'ms-mix'; }}
  }}
  const h10 = i1.ma10, h30 = i1.ma30, h60 = i1.ma60;
  let s1 = '', c1 = '';
  if (h10 && h30 && h60) {{
    if (h10 > h30 && h30 > h60)      {{ s1 = '↑ Bullish (MA10>MA30>MA60)'; c1 = 'ms-bull'; }}
    else if (h10 < h30 && h30 < h60) {{ s1 = '↓ Bearish (MA10<MA30<MA60)'; c1 = 'ms-bear'; }}
    else                              {{ s1 = '↔ Mixed'; c1 = 'ms-mix'; }}
  }}
  function row(name, val) {{
    const vc = (p && val) ? (p > val ? 'ma-above' : 'ma-below') : 'dim';
    return '<div class="ma-row"><span class="ma-name">' + name + '</span><span class="ma-val ' + vc + '">' + (val != null ? fp(val) : '—') + '</span><span class="ma-arrow">' + maArrow(p, val) + '</span></div>';
  }}
  let h = '<div class="ma-section"><div class="ma-tf-label">5m Timeframe</div>';
  h += row('MA5', m5) + row('MA10', m10) + row('MA30', m30) + row('MA60', i5.ma60) + row('EMA20', e20);
  if (s5) h += '<div class="ma-structure ' + c5 + '">' + s5 + '</div>';
  h += '</div><div class="ma-section"><div class="ma-tf-label">1h Timeframe</div>';
  h += row('MA10', h10) + row('MA30', h30) + row('MA60', h60) + row('EMA20', i1.ema20);
  if (s1) h += '<div class="ma-structure ' + c1 + '">' + s1 + '</div>';
  h += '</div>';
  document.getElementById('ma-body').innerHTML = h;
}}
function renderKDJ(d) {{
  const ex = d.extra;
  if (!ex) {{ document.getElementById('kdj-body').innerHTML = '<span class="dim">No data yet</span>'; return; }}
  const i5 = ex.ind5m || {{}};
  const i1 = ex.ind1h || {{}};
  function row(tf, k, dv, j) {{
    const jv = j != null ? parseFloat(j) : null;
    let jcl = 'dim';
    if (jv != null) {{
      if      (tf === '5m')  {{ jcl = jv < 15 ? 'green' : jv > 85 ? 'red' : ''; }}
      else if (tf === '15m') {{ jcl = jv < 30 ? 'green' : jv > 70 ? 'red' : ''; }}
      else if (tf === '1h')  {{ jcl = jv < 50 ? 'green' : jv > 50 ? 'red' : ''; }}
    }}
    const js = jv != null ? '<strong class="' + jcl + '">' + fm(jv, 1) + '</strong>' : '—';
    return '<div class="kdj-row"><span class="kdj-tf">' + tf + '</span><span class="kdj-vals">K=' + fm(k, 1) + '&nbsp; D=' + fm(dv, 1) + '&nbsp; J=' + js + '</span></div>';
  }}
  document.getElementById('kdj-body').innerHTML =
    row('5m',  i5.k, i5.d, i5.j) +
    row('15m', ex.k15, ex.d15, ex.j15) +
    row('1h',  i1.k, i1.d, i1.j);
}}
function renderTrade(d) {{
  function section(dir, t) {{
    const hcl = dir === 'LONG' ? 'tdh-long' : 'tdh-short';
    if (!t) return '<div class="trade-section"><div class="trade-dir-header ' + hcl + '">' + dir + '</div><span class="dim" style="font-size:.78rem">No data yet</span></div>';
    const est = t.entry > 0 ? MARGIN * Math.abs(t.tp1 - t.entry) / t.entry : 0;
    const rr  = (t.entry && t.sl && t.tp1) ? Math.abs(t.tp1 - t.entry) / Math.abs(t.sl - t.entry) : 0;
    return '<div class="trade-section">' +
      '<div class="trade-dir-header ' + hcl + '">' + dir + ' &mdash; Max ' + fm(t.lev, 1) + 'x</div>' +
      '<div class="trade-row"><span class="tl">Entry</span><span class="tv">' + fp(t.entry) + '</span></div>' +
      '<div class="trade-row"><span class="tl">Stop Loss</span><span class="tv red">' + fp(t.sl) + ' <span class="dim">(' + fm(t.sl_pct, 2) + '% risk)</span></span></div>' +
      '<div class="trade-row"><span class="tl">TP1 (1.5R)</span><span class="tv green">' + fp(t.tp1) + '</span></div>' +
      '<div class="trade-row"><span class="tl">TP2 (2.0R)</span><span class="tv green">' + fp(t.tp2) + '</span></div>' +
      '<div class="trade-row"><span class="tl">Liq Price</span><span class="tv ' + (t.liq != null && t.liq > 0 ? 'red' : 'dim') + '">' + (t.liq != null && t.liq > 0 ? fp(t.liq) : 'N/A') + '</span></div>' +
      '<div class="trade-row"><span class="tl">Est. Profit</span><span class="tv green">$' + fm(est, 2) + ' <span class="dim">(at $' + MARGIN + ' margin)</span></span></div>' +
      '<div class="trade-row"><span class="tl">R:R</span><span class="tv">1:' + fm(rr, 2) + '</span></div>' +
    '</div>';
  }}
  document.getElementById('trade-body').innerHTML = section('LONG', d.long_trade) + section('SHORT', d.short_trade);
}}
function renderMarket(d) {{
  const ex = d.extra || {{}};
  if (!ex.bids_top) {{
    document.getElementById('market-body').innerHTML = '<span class="dim">No data yet</span>';
    return;
  }}
  const bp = ex.bid_pct, ap = ex.ask_pct;

  // ── Bid/Ask ratio bar ──
  let ratioBar = '';
  if (bp != null) {{
    ratioBar =
      '<div style="display:flex;height:16px;border-radius:4px;overflow:hidden;margin-bottom:.5rem;gap:1px;font-size:.68rem;font-weight:bold">' +
        '<div style="background:#3fb950;width:' + bp + '%;display:flex;align-items:center;padding:0 .35rem;color:#0d1117;overflow:hidden;white-space:nowrap">' + bp.toFixed(1) + '% BID</div>' +
        '<div style="background:#f85149;flex:1;display:flex;align-items:center;justify-content:flex-end;padding:0 .35rem;color:#fff;white-space:nowrap">ASK ' + (ap != null ? ap.toFixed(1) + '%' : '') + '</div>' +
      '</div>';
  }}

  // ── Spread ──
  let spreadHtml = '';
  if (ex.best_bid && ex.best_ask) {{
    spreadHtml =
      '<div style="display:flex;justify-content:space-between;font-size:.72rem;margin-bottom:.45rem;padding:.22rem .4rem;background:#21262d;border-radius:4px">' +
        '<span class="green">Bid ' + fp(ex.best_bid) + '</span>' +
        '<span class="dim">Spread $' + fp(ex.spread) + ' (' + fm(ex.spread_pct, 4) + '%)</span>' +
        '<span class="red">Ask ' + fp(ex.best_ask) + '</span>' +
      '</div>';
  }}

  // ── Order book ──
  const allSizes = [...(ex.bids_top || []).map(l => l[1]), ...(ex.asks_top || []).map(l => l[1])];
  const maxSize = allSizes.length > 0 ? Math.max(...allSizes) : 1;

  function bookRow(price, size, side) {{
    const pct = Math.min(100, size / maxSize * 100).toFixed(1);
    const bg  = side === 'bid' ? 'rgba(63,185,80,.2)' : 'rgba(248,81,73,.2)';
    const pCol = side === 'bid' ? '#3fb950' : '#f85149';
    const bSide = side === 'bid' ? 'left' : 'right';
    return '<div style="position:relative;padding:.18rem .45rem;font-size:.75rem;border-bottom:1px solid #1c2128">' +
      '<div style="position:absolute;top:0;' + bSide + ':0;height:100%;width:' + pct + '%;background:' + bg + '"></div>' +
      '<span style="position:relative;color:' + pCol + '">' + fp(price) + '</span>' +
      '<span style="position:relative;float:right;color:var(--dim)">' + parseFloat(size).toFixed(3) + '</span>' +
    '</div>';
  }}

  const asks5 = (ex.asks_top || []).slice(0, 5).reverse();
  const bids5 = (ex.bids_top || []).slice(0, 5);

  let bookHtml = '<div style="border:1px solid var(--border);border-radius:6px;overflow:hidden;margin-bottom:.5rem">';
  bookHtml += '<div style="font-size:.65rem;color:var(--dim);padding:.15rem .45rem;background:#21262d;text-transform:uppercase;letter-spacing:.07em;border-bottom:1px solid var(--border)">Order book — top 5 levels</div>';
  asks5.forEach(function(l) {{ bookHtml += bookRow(l[0], l[1], 'ask'); }});
  bookHtml += '<div style="padding:.18rem .45rem;background:#21262d;font-size:.72rem;text-align:center;color:var(--dim);border-top:1px solid var(--border);border-bottom:1px solid var(--border)">' +
    (ex.spread != null ? 'Spread &nbsp;$' + fp(ex.spread) : '—') + '</div>';
  bids5.forEach(function(l) {{ bookHtml += bookRow(l[0], l[1], 'bid'); }});
  bookHtml += '</div>';

  // ── Walls ──
  let wallsHtml = '';
  if (ex.bid_wall) {{
    const w = ex.bid_wall;
    wallsHtml +=
      '<div style="font-size:.72rem;padding:.2rem 0;border-bottom:1px solid #1c2128">' +
        '<span class="dim">🟢 Bid Wall</span>' +
        '<span style="float:right"><span class="green">' + fp(w.price) + '</span>' +
        '<span class="dim"> &nbsp;' + w.size.toFixed(3) + ' · ' + w.ratio + '× avg · −' + fm(w.dist_pct, 2) + '% from price</span></span>' +
      '</div>';
  }}
  if (ex.ask_wall) {{
    const w = ex.ask_wall;
    wallsHtml +=
      '<div style="font-size:.72rem;padding:.2rem 0;border-bottom:1px solid #1c2128">' +
        '<span class="dim">🔴 Ask Wall</span>' +
        '<span style="float:right"><span class="red">' + fp(w.price) + '</span>' +
        '<span class="dim"> &nbsp;' + w.size.toFixed(3) + ' · ' + w.ratio + '× avg · +' + fm(w.dist_pct, 2) + '% from price</span></span>' +
      '</div>';
  }}
  if (!ex.bid_wall && !ex.ask_wall) {{
    wallsHtml = '<div style="font-size:.72rem;color:var(--dim);padding:.2rem 0;border-bottom:1px solid #1c2128">No significant walls detected (&lt;3× avg)</div>';
  }}

  // ── Cumulative depth table ──
  const cumHtml =
    '<div style="display:grid;grid-template-columns:2.5rem 1fr 1fr;gap:.12rem .4rem;font-size:.72rem;padding:.3rem 0 .2rem;border-bottom:1px solid #1c2128;margin-top:.2rem">' +
      '<span class="dim" style="font-size:.65rem">Band</span>' +
      '<span class="green" style="text-align:right;font-size:.65rem">Bid vol</span>' +
      '<span class="red" style="text-align:right;font-size:.65rem">Ask vol</span>' +
      '<span class="dim">0.5%</span>' +
        '<span class="green" style="text-align:right">' + (ex.bid_vol_05p != null ? ex.bid_vol_05p.toFixed(3) : '—') + '</span>' +
        '<span class="red"  style="text-align:right">' + (ex.ask_vol_05p != null ? ex.ask_vol_05p.toFixed(3) : '—') + '</span>' +
      '<span class="dim">1.0%</span>' +
        '<span class="green" style="text-align:right">' + (ex.bid_vol_1p != null ? ex.bid_vol_1p.toFixed(3) : '—') + '</span>' +
        '<span class="red"  style="text-align:right">' + (ex.ask_vol_1p != null ? ex.ask_vol_1p.toFixed(3) : '—') + '</span>' +
    '</div>';

  // ── Funding & market ──
  const fr = ex.funding_rate;
  const frCls = fr != null ? (Math.abs(fr) <= 0.01 ? 'green' : fr > 0.01 ? 'red' : 'dim') : 'dim';
  const lc = ex.last_candle_5m;
  const lcHtml = lc ?
    '<div style="font-size:.72rem;padding:.2rem 0;border-bottom:1px solid #1c2128"><span class="dim">Last 5m candle</span>' +
    '<span style="float:right;color:' + (lc.close > lc.open ? 'var(--green)' : 'var(--red)') + '">' +
    (lc.close > lc.open ? '▲ Green' : '▼ Red') + ' &nbsp;vol=' + parseFloat(lc.vol).toFixed(0) + '</span></div>' : '';

  const mktHtml =
    '<div style="font-size:.72rem;padding:.2rem 0;border-bottom:1px solid #1c2128"><span class="dim">Funding Rate</span>' +
      '<span class="' + frCls + '" style="float:right">' + (fr != null ? (fr >= 0 ? '+' : '') + fr.toFixed(4) + '%' : '—') + '</span></div>' +
    '<div style="font-size:.72rem;padding:.2rem 0;border-bottom:1px solid #1c2128"><span class="dim">24h High / Low</span>' +
      '<span style="float:right">' + (ex.high_price ? '$' + fp(ex.high_price) : '—') + ' / ' + (ex.low_price ? '$' + fp(ex.low_price) : '—') + '</span></div>' +
    '<div style="font-size:.72rem;padding:.2rem 0"><span class="dim">24h Volume</span>' +
      '<span class="dim" style="float:right">' + (ex.volume_24 ? parseFloat(ex.volume_24).toFixed(0) : '—') + '</span></div>' +
    lcHtml;

  document.getElementById('market-body').innerHTML =
    ratioBar + spreadHtml + bookHtml + wallsHtml + cumHtml +
    '<div style="border-top:1px solid var(--border);padding-top:.4rem;margin-top:.35rem">' + mktHtml + '</div>';
}}
function renderLastAlert(d) {{
  const wrap = document.getElementById('last-alert-wrap');
  if (!wrap) return;
  const a = d.last_alert;
  if (!a) {{ wrap.innerHTML = ''; return; }}
  const isLong = a.direction === 'LONG';
  const cc = isLong ? 'long' : 'short';
  const valCls = isLong ? 'green' : 'red';
  const slCls = 'red';
  const bonus = a.session_bonus || 0;
  const eff = a.effective_score || a.score;
  const ts = TS[a.trend] || TS['Choppy'];
  const trendBadgeHtml = a.trend ? '<span style="background:' + ts[1] + ';color:' + ts[2] + ';padding:.1rem .3rem;border-radius:8px;font-size:.72rem">' + ts[0] + ' ' + a.trend + '</span>' : '';
  const sessBit = bonus > 0 ? '<span class="sess-badge" style="font-size:.7rem">+' + bonus.toFixed(1) + ' ' + (a.session_label || '') + '</span>' : '';
  const est = a.tp_dollar_gain || 0;
  const rr  = a.rr_ratio || 0;
  const sl_dist = a.entry > 0 ? (a.sl - a.entry) : 0;
  const tp1_dist = a.entry > 0 ? (a.tp1 - a.entry) : 0;
  const tp2_dist = a.entry > 0 ? (a.tp2 - a.entry) : 0;
  function fDist(v) {{ return (v >= 0 ? '+' : '') + parseFloat(v).toPrecision(4); }}
  const passed = (a.checklist || []).filter(c => c.startsWith('[+]')).length;
  const clItems = (a.checklist || []).map(c => '<div class="' + (c.startsWith('[+]') ? 'cl-pass' : c.startsWith('[~]') ? 'cl-neutral' : 'cl-fail') + '">' + c + '</div>').join('');
  wrap.innerHTML =
    '<div class="alert-card-' + cc + '">' +
      '<div class="alert-card-hdr alert-card-hdr-' + cc + '">' +
        '<span>🔔 ' + a.direction + ' ALERT</span>' +
        '<span class="dim" style="font-weight:normal;font-size:.75rem">Score: ' + a.score + '/' + (a.direction === 'LONG' ? 12 : 11) + ' (eff ' + fm(eff, 1) + ')</span>' +
        trendBadgeHtml +
        (a.alignment ? '<span class="dim" style="font-size:.7rem;font-weight:normal">' + a.alignment + '</span>' : '') +
        sessBit +
        '<span class="alert-ts">' + (a.time || '') + '</span>' +
      '</div>' +
      '<div style="display:grid;grid-template-columns:1fr 1fr;gap:0 1px;background:var(--border)">' +
        '<div style="background:var(--surface);padding:.6rem .85rem">' +
          '<div style="font-size:.68rem;color:var(--dim);text-transform:uppercase;letter-spacing:.07em;margin-bottom:.3rem">Entry &amp; Exits</div>' +
          '<div class="asg-row"><span class="asg-label">Entry</span><span class="asg-val">' + fp(a.entry) + '</span></div>' +
          '<div class="asg-row"><span class="asg-label">Stop Loss</span><span class="asg-val ' + slCls + '">' + fp(a.sl) + ' <span class="dim">(' + fDist(sl_dist) + ')</span></span></div>' +
          '<div class="asg-row"><span class="asg-label">TP1 (1.5R)</span><span class="asg-val green">' + fp(a.tp1) + ' <span class="dim">(' + fDist(tp1_dist) + ')</span></span></div>' +
          '<div class="asg-row"><span class="asg-label">TP2 (2.0R)</span><span class="asg-val green">' + fp(a.tp2) + ' <span class="dim">(' + fDist(tp2_dist) + ')</span></span></div>' +
        '</div>' +
        '<div style="background:var(--surface);padding:.6rem .85rem">' +
          '<div style="font-size:.68rem;color:var(--dim);text-transform:uppercase;letter-spacing:.07em;margin-bottom:.3rem">Risk &amp; Sizing</div>' +
          '<div class="asg-row"><span class="asg-label">Max Leverage</span><span class="asg-val">' + fm(a.max_lev, 1) + 'x (Isolated)</span></div>' +
          '<div class="asg-row"><span class="asg-label">Cost</span><span class="asg-val">$' + MARGIN + ' USDT</span></div>' +
          '<div class="asg-row"><span class="asg-label">Liq Price</span><span class="asg-val ' + (a.liq_price != null && a.liq_price > 0 ? 'red' : 'dim') + '">' + (a.liq_price != null && a.liq_price > 0 ? fp(a.liq_price) : 'N/A') + '</span></div>' +
          '<div class="asg-row"><span class="asg-label">Est. Profit</span><span class="asg-val green">$' + fm(est, 2) + '</span></div>' +
          '<div class="asg-row"><span class="asg-label">R:R</span><span class="asg-val">1:' + fm(rr, 2) + '</span></div>' +
        '</div>' +
      '</div>' +
      '<div class="alert-cl-wrap">' +
        '<details><summary class="dim" style="cursor:pointer;font-size:.72rem;padding:.3rem 0">Checklist (' + passed + '/' + (a.direction === 'LONG' ? 12 : 11) + ' passed)</summary>' +
          '<div class="alert-cl-grid">' + clItems + '</div>' +
        '</details>' +
      '</div>' +
    '</div>';
}}
function jClass(j, tf) {{
  if (tf === '5m')  return j < 15 ? 'j-oversold' : j > 85 ? 'j-overbought' : 'j-neutral';
  if (tf === '15m') return j < 30 ? 'j-oversold' : j > 70 ? 'j-overbought' : 'j-neutral';
  if (tf === '1h')  return j < 50 ? 'j-oversold' : j > 50 ? 'j-overbought' : 'j-neutral';
  return 'j-neutral';
}}
function jBadge(j) {{
  if (j < 10) return '<span class="tf-j-badge badge-hot">HOT</span>';
  if (j > 92) return '<span class="tf-j-badge badge-ob">OB</span>';
  return '';
}}
function bidClass(b) {{ return b >= 60 ? 'bid-bull' : b <= 40 ? 'bid-bear' : 'bid-mixed'; }}
function askClass(a) {{ return a >= 60 ? 'ask-bear' : a <= 40 ? 'ask-bull' : 'ask-mixed'; }}
function bidArrow(b) {{ return b >= 60 ? '↑' : b <= 40 ? '↓' : '→'; }}
function askArrow(a) {{ return a >= 60 ? '↓' : a <= 40 ? '↑' : '→'; }}
function bidTag(b) {{ return b >= 70 ? 'Dominant' : b >= 60 ? 'Leading' : b <= 40 ? 'Weak' : 'Mixed'; }}
function askTag(a) {{ return a >= 70 ? 'Dominant' : a >= 60 ? 'Leading' : a <= 40 ? 'Weak' : 'Mixed'; }}
function buildTFCard(sym, d) {{
  const el = document.getElementById('tf-signals');
  if (!el) return;
  const ex = d.extra;
  if (!ex) return;
  const i5  = ex.ind5m || {{}};
  const i1  = ex.ind1h || {{}};
  const j5  = i5.j, j15 = ex.j15, j1h = i1.j;
  const bid = ex.bid_pct, ask = ex.ask_pct;
  const disp = sym + '/USDT';
  let h =
    '<div class="tf-header">' +
      '<span class="tf-header-title">Timeframe Signals</span>' +
      '<span class="tf-header-symbol">' + disp + '</span>' +
    '</div>' +
    '<div class="tf-col-row">' +
      '<div class="tf-col-lbl">x</div>' +
      '<div class="tf-col-lbl">5m</div>' +
      '<div class="tf-col-lbl">15m</div>' +
      '<div class="tf-col-lbl">1h</div>' +
    '</div>' +
    '<div class="tf-j-row">' +
      '<div class="tf-row-lbl">J</div>';
  [['5m', j5], ['15m', j15], ['1h', j1h]].forEach(function(p) {{
    const tf = p[0], j = p[1];
    if (j == null) {{
      h += '<div class="tf-j-cell j-neutral"><span class="tf-j-val" style="color:#4a6a8a">—</span><span class="tf-j-sub">KDJ-J</span></div>';
    }} else {{
      h += '<div class="tf-j-cell ' + jClass(j, tf) + '">' + jBadge(j) +
        '<span class="tf-j-val">' + parseFloat(j).toFixed(1) + '</span>' +
        '<span class="tf-j-sub">KDJ-J</span></div>';
    }}
  }});
  h += '</div>';
  if (bid != null) {{
    h += '<div class="tf-depth-row"><div class="tf-row-lbl">B%</div>' +
      '<div class="tf-depth-banner ' + bidClass(bid) + '">' +
        '<span class="tf-depth-side">' + bidArrow(bid) + ' Bid</span>' +
        '<span class="tf-depth-pct">' + parseFloat(bid).toFixed(1) + '%</span>' +
        '<span class="tf-depth-tag">' + bidTag(bid) + '</span>' +
      '</div></div>';
  }} else {{
    h += '<div class="tf-depth-row"><div class="tf-row-lbl">B%</div>' +
      '<div class="tf-depth-banner bid-mixed"><span class="tf-depth-pct" style="color:#4a6a8a">—</span></div></div>';
  }}
  if (ask != null) {{
    h += '<div class="tf-depth-row"><div class="tf-row-lbl">S%</div>' +
      '<div class="tf-depth-banner ' + askClass(ask) + '">' +
        '<span class="tf-depth-side">' + askArrow(ask) + ' Ask</span>' +
        '<span class="tf-depth-pct">' + parseFloat(ask).toFixed(1) + '%</span>' +
        '<span class="tf-depth-tag">' + askTag(ask) + '</span>' +
      '</div></div>';
  }} else {{
    h += '<div class="tf-depth-row"><div class="tf-row-lbl">S%</div>' +
      '<div class="tf-depth-banner ask-mixed"><span class="tf-depth-pct" style="color:#4a6a8a">—</span></div></div>';
  }}
  el.innerHTML = h;
}}
function render(d) {{
  renderLastAlert(d);
  renderBanner(d);
  renderAnalysis(d);
  renderMAs(d);
  renderKDJ(d);
  renderTrade(d);
  renderMarket(d);
  buildTFCard(SYMBOL, d);
}}
function tick() {{
  const r = nextEpoch * 1000 - Date.now();
  const el = document.getElementById('countdown');
  if (el) el.textContent = r <= 0 ? 'Scanning…' : 'Scan in ' + Math.ceil(r / 1000) + 's';
}}
async function poll() {{
  try {{
    const r = await fetch('/api/detail/' + SYMBOL);
    const nd = await r.json();
    if (!nd.error) {{
      DATA = nd;
      if (nd.next_scan_epoch) nextEpoch = nd.next_scan_epoch;
    }}
    render(DATA);
  }} catch(e) {{
    console.error('detail poll error:', e);
    const el = document.getElementById('countdown');
    if (el) el.textContent = 'Poll error — ' + e.message;
  }}
}}
function updateSessions() {{
  const now = new Date();
  const h  = parseInt(new Intl.DateTimeFormat('en-US', {{hour:'numeric',hour12:false,timeZone:'America/New_York'}}).format(now));
  const mn = parseInt(new Intl.DateTimeFormat('en-US', {{minute:'2-digit',timeZone:'America/New_York'}}).format(now));
  const t = h * 60 + mn;
  [
    {{id:'sess-euus', label:'🌍🌎 EU/US 8a-12p', start:480,  end:720,  bonus:1.0, prime:true}},
    {{id:'sess-us',   label:'🌎 US 12p-5p',       start:720,  end:1020, bonus:0.5, prime:false}},
    {{id:'sess-eu',   label:'🌍 EU 3a-8a',         start:180,  end:480,  bonus:0.5, prime:false}},
    {{id:'sess-asia', label:'🌏 Asia 5p-3a',       start:1020, end:180,  bonus:0.0, prime:false}},
  ].forEach(s => {{
    const el = document.getElementById(s.id);
    if (!el) return;
    const active = s.start < s.end ? (t >= s.start && t < s.end) : (t >= s.start || t < s.end);
    el.className = 'sess ' + (active ? (s.prime ? 'sess-prime' : 'sess-open') : 'sess-closed');
    el.textContent = active ? s.label + ' +' + s.bonus.toFixed(1) : s.label;
  }});
}}
render(DATA);
updateSessions();
setInterval(updateSessions, 30000);
setInterval(poll, PRICE_IV * 1000);
setInterval(tick, 250);
tick();
poll();
</script>
</body>
</html>"""


# ── HTML shell ─────────────────────────────────────────────────────────────────

def build_log_html() -> str:
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Trade Log — Hyperliquid Scanner</title>
<style>
  :root{{--bg:#0d1117;--surface:#161b22;--border:#30363d;--green:#3fb950;--red:#f85149;--text:#e6edf3;--dim:#8b949e;--font:ui-monospace,SFMono-Regular,monospace}}
  *{{box-sizing:border-box;margin:0;padding:0}}
  body{{background:var(--bg);color:var(--text);font-family:var(--font);font-size:13px;min-height:100vh}}
  header{{background:var(--surface);border-bottom:1px solid var(--border);padding:.75rem 1.25rem;display:flex;align-items:center;gap:.7rem;flex-wrap:wrap}}
  header h1{{font-size:1rem;letter-spacing:.05em}}
  .back-link{{color:var(--dim);text-decoration:none;font-size:.8rem;padding:.2rem .6rem;border:1px solid var(--border);border-radius:6px;transition:color .15s}}
  .back-link:hover{{color:var(--text)}}
  .meta{{color:var(--dim);font-size:.75rem;margin-left:auto;display:flex;align-items:center;gap:.6rem}}
  .btn{{background:#21262d;border:1px solid var(--border);border-radius:6px;padding:.25rem .7rem;font-size:.75rem;font-family:var(--font);color:var(--text);cursor:pointer;transition:background .15s}}
  .btn:hover{{background:#30363d}} .btn:active{{opacity:.7}} .btn:disabled{{opacity:.4;cursor:default}}
  .btn-danger{{border-color:#6e2a2a;color:#f85149}}
  .btn-danger:hover{{background:#2d1a1a}}
  .container{{max-width:1100px;margin:0 auto;padding:1rem}}
  .card{{background:var(--surface);border:1px solid var(--border);border-radius:8px;margin-bottom:1rem;overflow:hidden}}
  .card-title{{padding:.5rem .85rem;font-size:.72rem;font-weight:bold;letter-spacing:.09em;text-transform:uppercase;color:var(--dim);border-bottom:1px solid var(--border)}}
  .card-body{{padding:.75rem .85rem}}
  .summary-grid{{display:grid;grid-template-columns:repeat(auto-fill,minmax(180px,1fr));gap:.6rem}}
  .stat{{display:flex;flex-direction:column;gap:.2rem}}
  .stat-label{{font-size:.7rem;color:var(--dim);text-transform:uppercase;letter-spacing:.07em}}
  .stat-val{{font-size:1.15rem;font-weight:bold}}
  table{{width:100%;border-collapse:collapse}}
  th,td{{padding:.5rem .75rem;text-align:left;border-bottom:1px solid var(--border);white-space:nowrap}}
  th{{color:var(--dim);font-weight:normal;font-size:.72rem;text-transform:uppercase;letter-spacing:.06em;position:sticky;top:0;background:var(--surface);z-index:1}}
  tr:last-child td{{border-bottom:none}}
  tr:hover td{{background:#1c2128}}
  .green{{color:var(--green)}} .red{{color:var(--red)}} .dim{{color:var(--dim)}}
  .badge-win{{background:#0d2e1a;color:#3fb950;border:1px solid #3fb950;border-radius:10px;padding:.15rem .55rem;font-size:.72rem}}
  .badge-loss{{background:#2d1010;color:#f85149;border:1px solid #f85149;border-radius:10px;padding:.15rem .55rem;font-size:.72rem}}
  .badge-long{{color:#3fb950;font-weight:bold}}
  .badge-short{{color:#f85149;font-weight:bold}}
  .empty{{text-align:center;color:var(--dim);padding:2.5rem;font-size:.9rem}}
  #status{{font-size:.75rem;color:var(--dim)}}
</style>
</head>
<body>
<header>
  <a href="/" class="back-link">&#8592; Dashboard</a>
  <h1>&#128202; Trade Log</h1>
  <div class="meta">
    <span id="status">Loading…</span>
    <button class="btn" onclick="loadTrades()">&#8635; Refresh</button>
    <button class="btn btn-danger" onclick="clearLog(this)">&#x1F5D1; Clear Log</button>
  </div>
</header>
<div class="container">
  <div class="card" id="summary-card" style="display:none">
    <div class="card-title">Summary</div>
    <div class="card-body">
      <div class="summary-grid">
        <div class="stat"><span class="stat-label">Total Trades</span><span class="stat-val" id="s-total">—</span></div>
        <div class="stat"><span class="stat-label">Wins / Losses</span><span class="stat-val" id="s-wl">—</span></div>
        <div class="stat"><span class="stat-label">Win Rate</span><span class="stat-val" id="s-winrate">—</span></div>
        <div class="stat"><span class="stat-label">Total Net P&amp;L</span><span class="stat-val" id="s-pnl">—</span></div>
        <div class="stat"><span class="stat-label">Total Fees</span><span class="stat-val" id="s-fees">—</span></div>
      </div>
    </div>
  </div>
  <div class="card">
    <div class="card-title">All Trades</div>
    <div id="table-wrap">
      <table>
        <thead><tr>
          <th>Time</th><th>Symbol</th><th>Direction</th>
          <th>Entry</th><th>Exit</th><th>P&amp;L</th><th>Result</th><th>Fees</th>
        </tr></thead>
        <tbody id="log-tbody"><tr><td colspan="8" class="empty">Loading…</td></tr></tbody>
      </table>
    </div>
  </div>
</div>
<script>
function fmt(n, dec=4) {{
  if (n == null) return '—';
  const v = parseFloat(n);
  if (isNaN(v)) return '—';
  return v.toPrecision ? parseFloat(v.toPrecision(dec)).toString() : v.toFixed(dec);
}}
function fmtPnl(n) {{
  if (n == null) return '—';
  const v = parseFloat(n);
  const s = v >= 0 ? '+' : '';
  return `${{s}}${{v.toFixed(2)}}`;
}}
function fmtTime(ts) {{
  if (!ts) return '—';
  try {{
    const d = new Date(ts);
    return d.toLocaleString('en-US', {{month:'2-digit',day:'2-digit',hour:'2-digit',minute:'2-digit',hour12:false}});
  }} catch(e) {{ return ts; }}
}}
async function loadTrades() {{
  document.getElementById('status').textContent = 'Loading…';
  try {{
    const r = await fetch('/api/trades');
    const trades = await r.json();
    document.getElementById('status').textContent = `${{trades.length}} trade${{trades.length===1?'':'s'}}`;
    renderSummary(trades);
    renderTable(trades);
  }} catch(e) {{
    document.getElementById('status').textContent = 'Error loading trades';
  }}
}}
function renderSummary(trades) {{
  const card = document.getElementById('summary-card');
  if (!trades.length) {{ card.style.display='none'; return; }}
  card.style.display='';
  const wins    = trades.filter(t => t.win);
  const pnl     = trades.reduce((s,t) => s + (t.pnl||0), 0);
  const fees    = trades.reduce((s,t) => s + (t.fees||0), 0);
  const rate    = trades.length ? (wins.length/trades.length*100).toFixed(0) : 0;
  const pnlSign = pnl >= 0 ? '+' : '';
  document.getElementById('s-total').textContent   = trades.length;
  document.getElementById('s-wl').innerHTML        = `<span class="green">${{wins.length}}W</span> / <span class="red">${{trades.length-wins.length}}L</span>`;
  document.getElementById('s-winrate').textContent = rate + '%';
  document.getElementById('s-pnl').innerHTML       = `<span class="${{pnl>=0?'green':'red'}}">${{pnlSign}}$${{pnl.toFixed(2)}}</span>`;
  document.getElementById('s-fees').textContent    = `$${{fees.toFixed(2)}}`;
}}
function renderTable(trades) {{
  const tbody = document.getElementById('log-tbody');
  if (!trades.length) {{
    tbody.innerHTML = '<tr><td colspan="8" class="empty">No trades recorded yet</td></tr>';
    return;
  }}
  tbody.innerHTML = [...trades].reverse().map(t => {{
    const pnl     = parseFloat(t.pnl||0);
    const pnlHtml = `<span class="${{pnl>=0?'green':'red'}}">${{fmtPnl(t.pnl)}}</span>`;
    const dirHtml = t.direction==='LONG'
      ? '<span class="badge-long">▲ LONG</span>'
      : '<span class="badge-short">▼ SHORT</span>';
    const res     = t.win
      ? '<span class="badge-win">Win</span>'
      : '<span class="badge-loss">Loss</span>';
    const sym     = (t.symbol||'');
    return `<tr>
      <td class="dim">${{fmtTime(t.timestamp)}}</td>
      <td><strong>${{sym}}</strong></td>
      <td>${{dirHtml}}</td>
      <td>${{fmt(t.entry)}}</td>
      <td>${{fmt(t.exit)}}</td>
      <td>${{pnlHtml}}</td>
      <td>${{res}}</td>
      <td class="dim">$${{(t.fees||0).toFixed(2)}}</td>
    </tr>`;
  }}).join('');
}}
async function clearLog(btn) {{
  if (!confirm('Clear all trade history? This cannot be undone.')) return;
  btn.disabled = true;
  btn.textContent = 'Clearing…';
  try {{
    await fetch('/api/clear-trades', {{method:'POST'}});
    await loadTrades();
  }} catch(e) {{
    alert('Error clearing log');
  }}
  btn.disabled = false;
  btn.innerHTML = '&#x1F5D1; Clear Log';
}}
loadTrades();
</script>
</body>
</html>"""


def build_html():
    # Static shell — zero scan data embedded.
    # All live data is fetched from /api/status by the JS poll loop.
    rows = ""
    for sym in SYMBOLS:
        rows += (
            f'<tr id="row-{sym}">'
            f'<td><a href="/detail/{sym}" class="sym-link">{sym}</a><div id="zone-{sym}" style="font-size:.65rem;color:var(--dim);margin-top:.18rem"></div></td>'
            f'<td id="tr-{sym}" class="dim">—</td>'
            f'<td class="price-cell dim" data-sym="{sym}">—</td>'
            f'<td id="tp-{sym}" class="dim">—</td>'
            f'<td id="ls-{sym}" class="dim">—</td>'
            f'<td id="j5-{sym}" class="dim">—</td>'
            f'<td id="adx-{sym}" class="dim">—</td>'
            f'<td id="bp-{sym}" class="dim">—</td>'
            f'<td id="ap-{sym}" class="dim">—</td>'
            f'<td id="ss-{sym}" class="dim">—</td>'
            f'</tr>'
        )
    _mode_color = ('#3fb950' if ACCOUNT_MODE == 'SMALL'
              else '#f0a500' if ACCOUNT_MODE == 'MEDIUM'
              else '#d29922')
    _mode_label = ('📱 Small ($700/5x)'   if ACCOUNT_MODE == 'SMALL'
              else f'📈 Medium ($1000/10x) · Loss: ${daily_loss_total:.0f}/${DAILY_LOSS_LIMIT:.0f}' if ACCOUNT_MODE == 'MEDIUM'
              else f'🏦 Large ($2500/25x) · Loss: ${daily_loss_total:.0f}/${DAILY_LOSS_LIMIT:.0f}')

    return f"""<!DOCTYPE html>
<!-- generated: {datetime.now(tz=EST).isoformat()} mode: {ACCOUNT_MODE} -->
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="Cache-Control" content="no-cache, no-store, must-revalidate">
<meta http-equiv="Pragma" content="no-cache">
<meta http-equiv="Expires" content="0">
<title>Hyperliquid Futures Scanner v{BUILD_TIME}</title>
<style>
  :root{{--bg:#0d1117;--surface:#161b22;--border:#30363d;--green:#3fb950;--red:#f85149;--text:#e6edf3;--dim:#8b949e;--font:ui-monospace,SFMono-Regular,monospace}}
  *{{box-sizing:border-box;margin:0;padding:0}}
  body{{background:var(--bg);color:var(--text);font-family:var(--font);font-size:13px;min-height:100vh}}
  header{{background:var(--surface);border-bottom:1px solid var(--border);padding:.75rem 1.25rem;display:flex;align-items:center;gap:.6rem;flex-wrap:wrap}}
  header h1{{font-size:1rem;letter-spacing:.05em}}
  .badge{{background:#21262d;border:1px solid var(--border);border-radius:12px;padding:.2rem .6rem;font-size:.75rem}}
  .badge-price{{border-color:#1f6feb;color:#58a6ff}}
  .meta{{color:var(--dim);font-size:.75rem;margin-left:auto;display:flex;align-items:center;gap:.6rem;flex-wrap:wrap}}
  .btn{{background:#21262d;border:1px solid var(--border);border-radius:6px;padding:.25rem .7rem;font-size:.75rem;font-family:var(--font);color:var(--text);cursor:pointer;display:inline-flex;align-items:center;gap:.35rem;transition:background .15s}}
  .btn:hover{{background:#30363d}} .btn:active{{opacity:.7}} .btn:disabled{{opacity:.4;cursor:default}}
  .btn-danger{{border-color:#6e2a2a;color:#f85149}}
  .btn-danger:hover{{background:#2d1a1a}}
  .countdown{{color:var(--dim);font-size:.75rem}}
  .container{{max-width:1100px;margin:0 auto;padding:1rem}}
  h2{{font-size:.85rem;letter-spacing:.08em;text-transform:uppercase;color:var(--dim);margin:.5rem 0 .5rem}}
  .alert-bar{{display:flex;align-items:center;justify-content:space-between;margin-bottom:.5rem}}
  table{{width:100%;border-collapse:collapse;margin-bottom:1.5rem}}
  th,td{{padding:.5rem .75rem;text-align:left;border-bottom:1px solid var(--border)}}
  th{{color:var(--dim);font-weight:normal;font-size:.75rem;text-transform:uppercase;letter-spacing:.06em}}
  tr:last-child td{{border-bottom:none}}
  .green{{color:var(--green)}} .red{{color:var(--red)}} .dim{{color:var(--dim)}}
  .green-border{{border-left:3px solid var(--green)}} .red-border{{border-left:3px solid var(--red)}}
  .alert{{background:var(--surface);border:1px solid var(--border);border-radius:6px;margin-bottom:.75rem;overflow:hidden}}
  .alert-header{{padding:.5rem .75rem;font-weight:bold;font-size:.85rem}}
  .alert-body{{padding:.75rem}}
  .trade-grid{{display:grid;grid-template-columns:repeat(auto-fill,minmax(160px,1fr));gap:.4rem .75rem;margin-bottom:.75rem}}
  .label{{color:var(--dim);margin-right:.3rem}}
  details summary{{cursor:pointer;user-select:none;font-size:.78rem}}
  .checklist{{margin-top:.5rem;display:grid;grid-template-columns:1fr 1fr;gap:.15rem .5rem}}
  .cl-pass{{color:var(--green);font-size:.75rem}} .cl-fail{{color:var(--dim);font-size:.75rem}} .cl-neutral{{color:#8b949e;font-size:.75rem}}
  .status-dot{{width:8px;height:8px;border-radius:50%;background:var(--green);display:inline-block;margin-right:.4rem;animation:pulse 2s infinite}}
  .flash{{animation:flash .4s ease-out}}
  @keyframes pulse{{0%,100%{{opacity:1}}50%{{opacity:.4}}}}
  @keyframes flash{{0%{{background:#1f6feb44}}100%{{background:transparent}}}}
  @keyframes spin{{to{{transform:rotate(360deg)}}}}
  .spinning{{animation:spin .6s linear infinite;display:inline-block}}
  .sess{{border-radius:12px;padding:.2rem .55rem;font-size:.75rem;display:inline-flex;align-items:center;gap:.3rem;border:1px solid;transition:all .3s}}
  .sess-open{{background:#0d2e1a;border-color:#3fb950;color:#3fb950}}
  .sess-prime{{background:#0a3d20;border-color:#56d364;color:#56d364;font-weight:bold;box-shadow:0 0 8px #3fb95044}}
  .sess-closed{{background:#161b22;border-color:#30363d;color:#8b949e}}
  .sym-link{{color:var(--text);text-decoration:none;font-weight:bold;border-bottom:1px solid transparent;transition:border-color .15s,color .15s}}
  .sym-link:hover{{color:var(--green);border-color:var(--green)}}
</style>
</head>
<body>
<header>
  <h1><span class="status-dot"></span>Hyperliquid Futures Scanner</h1>
  <span class="badge badge-price">Price every {PRICE_INTERVAL}s</span>
  <span class="badge">Scan every {SCAN_INTERVAL}s</span>
  <span class="badge">Score &ge; 8 | J &lt; 15 | Depth &ge; 70%</span>
  <span class="badge" style="color:{_mode_color}">{_mode_label}</span>
  <span class="badge" id="balance-pill" style="color:#c9d1d9">Balance: <span id="balance-val">…</span></span><button id="balance-eye" onclick="toggleBalance()" style="background:none;border:none;cursor:pointer;padding:0 0 0 4px;font-size:.8rem;color:#8b949e;vertical-align:middle" title="Show/hide balance">👁</button>
  <a href="/log" style="text-decoration:none"><span class="badge" style="color:#58a6ff;border-color:#1f6feb">&#128202; Trade Log</span></a>
  <span class="badge" style="color:#8b949e">&#128197; Deployed: {BUILD_TIME}</span>
  <span class="sess" id="sess-euus">🌍🌎 EU/US 8a–12p</span>
  <span class="sess" id="sess-us">🌎 US 12p–5p</span>
  <span class="sess" id="sess-eu">🌍 EU 3a–8a</span>
  <span class="sess" id="sess-asia">🌏 Asia 5p–3a</span>
  <div class="meta">
    <span id="last-price">Prices: loading…</span>
    <span id="last-scan">Last scan: —</span>
    <button class="btn" onclick="doRefresh(this)">
      <span id="refresh-icon">&#8635;</span> Refresh
    </button>
    <span class="countdown" id="countdown">Scan in {SCAN_INTERVAL}s</span>
  </div>
</header>
<div class="container">
  <h2>Current Status</h2>
  <table>
    <thead><tr><th>Symbol</th><th>Trend</th><th>Price</th><th>TP $</th><th>Long Score</th><th>5m J</th><th>ADX</th><th>B%</th><th>S%</th><th>Short Score</th></tr></thead>
    <tbody id="symbol-tbody">{rows}</tbody>
  </table>
  <p style="font-size:.72rem;color:var(--dim);margin:.4rem 0 .75rem .25rem">Icons: ⏳ cooldown &nbsp;⏱ pending confirm &nbsp;🌙 Asia session &nbsp;🚫 misaligned</p>
  <div class="alert-bar">
    <h2 id="alert-heading" style="margin:0">Alerts</h2>
    <button class="btn btn-danger" onclick="clearAlerts(this)">&#x1F5D1; Clear Alerts</button>
  </div>
  <div id="alert-container"><p class="dim" style="padding:1rem">Loading…</p></div>
</div>
<script>
const PRICE_IV  = {PRICE_INTERVAL};
const SCAN_IV   = {SCAN_INTERVAL};
let nextScanEpoch = 0;
let lastCycle     = -1;
let refreshing    = false;
const TREND_STYLES = {{
  'Strong Bull': ['🟢🟢', '#0d2e1a', '#3fb950'],
  'Bullish':     ['🟢',   '#112b1a', '#56d364'],
  'Neutral':     ['⚪',   '#1c1c1c', '#8b949e'],
  'Choppy':      ['🟡',   '#2b2200', '#d29922'],
  'Bearish':     ['🔴',   '#2d1010', '#f0786b'],
  'Strong Bear': ['🔴🔴', '#3d0000', '#ff6b6b'],
}};

function updateRow(sym, d) {{
  const priceEl = document.querySelector('.price-cell[data-sym="' + sym + '"]');
  const lsEl    = document.getElementById('ls-' + sym);
  const ssEl    = document.getElementById('ss-' + sym);
  if (!priceEl) return;
  if (d.price != null) {{
    const newP = '$' + parseFloat(parseFloat(d.price).toPrecision(6)) + (d.stale ? ' ⚠️' : '');
    if (priceEl.textContent !== newP) {{
      priceEl.textContent = newP;
      if (!d.stale) {{
        priceEl.classList.remove('flash');
        void priceEl.offsetWidth;
        priceEl.classList.add('flash');
      }}
    }}
  }} else if (d.stale) {{
    priceEl.textContent = '⚠️ stale';
  }}
  const _estH  = parseInt(new Intl.DateTimeFormat('en-US',{{hour:'numeric',hour12:false,timeZone:'America/New_York'}}).format(new Date()));
  const _isAsia = _estH < 3 || _estH >= 17;
  if (lsEl && d.long_score != null) {{
    const lb = d.session_bonus > 0 ? ' (' + (d.long_score + d.session_bonus).toFixed(1) + ')' : '';
    const lc = (d.long_score >= {ALERT_THRESHOLD} && d.long_cooldown_secs > 0) ? ' ⏳' + Math.ceil(d.long_cooldown_secs / 60) + 'm' :
               (d.long_score >= {ALERT_THRESHOLD} && d.long_pending)            ? ' ⏱' :
               (d.long_score >= {ALERT_THRESHOLD} && _isAsia)                   ? ' 🌙' : '';
    lsEl.innerHTML = d.long_score + '/11' + lb + lc + (d.long_suppressed ? ' <span title="LONG suppressed \u2014 trend is ' + (d.trend||'') + '">🚫</span>' : '');
  }}
  const zoneEl = document.getElementById('zone-' + sym);
  if (zoneEl && d.last_alert && d.price != null) {{
    const a = d.last_alert;
    const sl = a.stale_low, sh = a.stale_high;
    const cur = parseFloat(d.price);
    const pf = v => parseFloat(parseFloat(v).toPrecision(6));
    if (sl != null && sh != null) {{
      if (cur < sl) {{
        const tag = a.direction === 'LONG' ? 'STALE DOWN' : 'STALE UP';
        zoneEl.innerHTML = '<span style="color:var(--red)">🚫 ' + tag + ' — ' + a.symbol + ' ' + a.direction + ' — Price below ' + pf(sl) + '</span>';
      }} else if (cur > sh) {{
        const tag = a.direction === 'LONG' ? 'STALE UP' : 'STALE DOWN';
        zoneEl.innerHTML = '<span style="color:var(--red)">🚫 ' + tag + ' — ' + a.symbol + ' ' + a.direction + ' — Price above ' + pf(sh) + '</span>';
      }} else {{
        zoneEl.innerHTML = '<span style="color:var(--green)">✅ ACTIVE — ' + a.symbol + ' ' + a.direction + ' — ' + pf(sl) + ' ← ' + pf(cur) + ' → ' + pf(sh) + '</span>';
      }}
    }}
  }} else if (zoneEl) {{
    zoneEl.innerHTML = '';
  }}
  if (ssEl && d.short_score != null) {{
    const sb = d.session_bonus > 0 ? ' (' + (d.short_score + d.session_bonus).toFixed(1) + ')' : '';
    const sc = (d.short_score >= {ALERT_THRESHOLD} && d.short_cooldown_secs > 0) ? ' ⏳' + Math.ceil(d.short_cooldown_secs / 60) + 'm' :
               (d.short_score >= {ALERT_THRESHOLD} && d.short_pending)            ? ' ⏱' :
               (d.short_score >= {ALERT_THRESHOLD} && _isAsia)                    ? ' 🌙' : '';
    ssEl.innerHTML = d.short_score + '/11' + sb + sc + (d.short_suppressed ? ' <span title="SHORT suppressed \u2014 trend is ' + (d.trend||'') + '">🚫</span>' : '');
  }}
  const j5El = document.getElementById('j5-' + sym);
  if (j5El && d.j5 != null) {{
    const v = d.j5;
    j5El.textContent = v.toFixed(1);
    j5El.className = v < 15 ? 'green' : v > 85 ? 'red' : 'dim';
  }}
  const adxEl = document.getElementById('adx-' + sym);
  if (adxEl) {{
    if (d.adx != null) {{
      adxEl.textContent = d.adx.toFixed(1);
      adxEl.className = d.adx > 25 ? 'green' : 'dim';
    }}
  }}
  const bpEl = document.getElementById('bp-' + sym);
  if (bpEl && d.bid_pct != null) {{
    bpEl.textContent = Math.round(d.bid_pct) + '%';
    bpEl.className = d.bid_pct >= 70 ? 'green' : 'red';
  }}
  const apEl = document.getElementById('ap-' + sym);
  if (apEl && d.ask_pct != null) {{
    apEl.textContent = Math.round(d.ask_pct) + '%';
    apEl.className = d.ask_pct >= 70 ? 'green' : 'red';
  }}
  const tpEl = document.getElementById('tp-' + sym);
  if (tpEl && d.tp_dollar != null) {{
    tpEl.textContent = '$' + d.tp_dollar.toFixed(2);
    tpEl.className = d.tp_dollar >= {MIN_TP_DOLLARS} ? 'green' : 'red';
  }}
  const trEl = document.getElementById('tr-' + sym);
  if (trEl && d.trend) {{
    const s = TREND_STYLES[d.trend] || TREND_STYLES['Choppy'];
    trEl.innerHTML = '<span style="background:' + s[1] + ';color:' + s[2] + ';padding:.15rem .45rem;border-radius:10px;font-size:.75rem;white-space:nowrap">' + s[0] + ' ' + d.trend + '</span>';
  }}
}}

function renderAlerts(alerts) {{
  const container = document.getElementById('alert-container');
  const heading   = document.getElementById('alert-heading');
  heading.textContent = 'Alerts (' + alerts.length + ' recent)';
  if (!alerts.length) {{
    container.innerHTML = '<p class="dim" style="padding:1rem">No alerts yet — scanner is running\u2026</p>';
    return;
  }}
  container.innerHTML = alerts.map(a => {{
    const dc     = a.direction === 'LONG' ? 'green' : 'red';
    const passed = (a.checklist || []).filter(c => c.startsWith('[+]')).length;
    const cl     = (a.checklist || []).map(c =>
      '<div class="' + (c.startsWith('[+]') ? 'cl-pass' : c.startsWith('[~]') ? 'cl-neutral' : 'cl-fail') + '">' + c + '</div>'
    ).join('');
    const p = v => parseFloat(parseFloat(v).toPrecision(6));
    return '<div class="alert ' + dc + '-border">' +
      '<div class="alert-header ' + dc + '">' +
        a.direction + ' &mdash; ' + a.symbol +
        '&nbsp; Score: ' + a.score + '/' + (a.direction === 'LONG' ? 12 : 11) +
        (a.alignment ? '&nbsp; <span class="dim">' + a.alignment + '</span>' : '') +
        (a.session_label ? '&nbsp; <span class="dim">' + a.session_label + ' (+' + (a.session_bonus || 0).toFixed(1) + ')</span>' : '') +
        (a.trend && TREND_STYLES[a.trend] ? '&nbsp;<span style="background:' + TREND_STYLES[a.trend][1] + ';color:' + TREND_STYLES[a.trend][2] + ';padding:.1rem .4rem;border-radius:8px;font-size:.8rem">' + TREND_STYLES[a.trend][0] + ' ' + a.trend + '</span>' : '') +
        '&nbsp; <span style="color:var(--' + dc + ')">Max ' + a.max_lev.toFixed(1) + 'x</span>' +
        '&nbsp; <span class="dim">' + a.time + '</span>' +
      '</div>' +
      '<div class="alert-body">' +
        '<div class="trade-grid">' +
          '<div><span class="label">Price</span> $' + p(a.price) + '</div>' +
          '<div><span class="label">Entry</span> ' + p(a.entry) + '</div>' +
          '<div><span class="label">SL</span> ' + p(a.sl) + ' <span class="dim">(' + (a.sl - a.entry >= 0 ? '+' : '') + parseFloat((a.sl - a.entry).toPrecision(4)) + ') (' + a.sl_pct.toFixed(2) + '% risk)</span></div>' +
          '<div><span class="label">TP1</span> ' + p(a.tp1) + ' <span class="dim">(' + (a.tp1 - a.entry >= 0 ? '+' : '') + parseFloat((a.tp1 - a.entry).toPrecision(4)) + ') (1.5R)</span></div>' +
          '<div><span class="label">TP2</span> ' + p(a.tp2) + ' <span class="dim">(' + (a.tp2 - a.entry >= 0 ? '+' : '') + parseFloat((a.tp2 - a.entry).toPrecision(4)) + ') (2.0R)</span></div>' +
          '<div><span class="label">Liq Price</span> <strong class="' + (a.liq_price != null && a.liq_price > 0 ? 'red' : 'dim') + '">' + (a.liq_price != null && a.liq_price > 0 ? parseFloat(a.liq_price.toPrecision(6)) : 'N/A') + '</strong></div>' +
          '<div><span class="label">Max Lev</span> <strong>' + a.max_lev.toFixed(1) + 'x</strong></div>' +
          (a.tp_dollar_gain != null ? '<div><span class="label">Est. Profit</span> <strong class="green">$' + (a.tp_dollar_gain || 0).toFixed(2) + '</strong> <span class="dim">(5x / $700)</span></div>' : '') +
          (a.rr_ratio != null ? '<div><span class="label">R:R</span> 1:' + (a.rr_ratio || 0).toFixed(1) + '</div>' : '') +
          (a.alignment ? '<div><span class="label">Alignment</span> ' + a.alignment + '</div>' : '') +
          (a.session_label ? '<div><span class="label">Session</span> ' + a.session_label + ' <span class="dim">(+' + (a.session_bonus || 0).toFixed(1) + ' bonus · eff: ' + (a.effective_score || a.score).toFixed(1) + '/' + (a.direction === 'LONG' ? 12 : 11) + ')</span></div>' : '') +
          (a.j15 != null ? '<div><span class="label">15m J</span> ' + a.j15.toFixed(1) + '</div>' : '') +
        '</div>' +
        '<details><summary class="dim">Checklist (' + passed + '/' + (a.direction === 'LONG' ? 12 : 11) + ' passed)</summary>' +
          '<div class="checklist">' + cl + '</div>' +
        '</details>' +
      '</div></div>';
  }}).join('');
}}

async function poll() {{
  try {{
    const res  = await fetch('/api/v2/status');
    const data = await res.json();
    for (const [sym, d] of Object.entries(data.symbols)) updateRow(sym, d);
    if (data.last_price_update)
      document.getElementById('last-price').textContent = 'Prices: ' + data.last_price_update;
    if (data.scan_cycle > lastCycle) {{
      lastCycle = data.scan_cycle;
      document.getElementById('last-scan').textContent = 'Last scan: ' + (data.last_scan || '—');
      renderAlerts(data.alerts);
    }}
    if (data.next_scan_epoch) nextScanEpoch = data.next_scan_epoch * 1000;
    if (data.balance_usdt !== undefined) {{ _balanceVal = data.balance_usdt; _renderBalance(); }}
  }} catch(e) {{}}
}}

async function clearAlerts(btn) {{
  btn.disabled = true;
  try {{
    await fetch('/api/clear-alerts', {{method: 'POST'}});
    renderAlerts([]);
  }} catch(e) {{}}
  btn.disabled = false;
}}

function tick() {{
  const remaining = nextScanEpoch - Date.now();
  const el = document.getElementById('countdown');
  el.textContent = remaining <= 0 ? 'Scanning…' : 'Scan in ' + Math.ceil(remaining / 1000) + 's';
}}

let _balanceVal = null;
let _balanceVisible = localStorage.getItem('balanceVisible') !== 'false';
function _renderBalance() {{
  const el  = document.getElementById('balance-val');
  const eye = document.getElementById('balance-eye');
  if (!el) return;
  if (_balanceVal === null || _balanceVal === undefined) {{
    el.textContent = '–';
  }} else if (_balanceVisible) {{
    el.textContent = '$' + Number(_balanceVal).toLocaleString('en-US', {{minimumFractionDigits:2, maximumFractionDigits:2}}) + ' USDT';
  }} else {{
    el.textContent = '••••••';
  }}
  if (eye) eye.textContent = _balanceVisible ? '👁' : '🙈';
}}
function toggleBalance() {{
  _balanceVisible = !_balanceVisible;
  localStorage.setItem('balanceVisible', _balanceVisible);
  _renderBalance();
}}
_renderBalance();

function doRefresh(btn) {{
  if (refreshing) return;
  refreshing = true;
  document.getElementById('refresh-icon').classList.add('spinning');
  btn.disabled = true;
  location.reload();
}}

function updateSessions() {{
  const now = new Date();
  const h = parseInt(new Intl.DateTimeFormat('en-US',{{hour:'numeric',hour12:false,timeZone:'America/New_York'}}).format(now));
  const mn = parseInt(new Intl.DateTimeFormat('en-US',{{minute:'2-digit',timeZone:'America/New_York'}}).format(now));
  const t = h * 60 + mn;
  const sessions = [
    {{id:'sess-euus', label:'🌍🌎 EU/US 8a-12p', start:8*60,  end:12*60, bonus:1.0, prime:true}},
    {{id:'sess-us',   label:'🌎 US 12p-5p',       start:12*60, end:17*60, bonus:0.5, prime:false}},
    {{id:'sess-eu',   label:'🌍 EU 3a-8a',         start:3*60,  end:8*60,  bonus:0.5, prime:false}},
    {{id:'sess-asia', label:'🌏 Asia 5p-3a',       start:17*60, end:3*60,  bonus:0.0, prime:false}},
  ];
  sessions.forEach(s => {{
    const el = document.getElementById(s.id);
    if (!el) return;
    const active = s.start < s.end ? (t >= s.start && t < s.end) : (t >= s.start || t < s.end);
    if (active) {{
      el.className = 'sess ' + (s.prime ? 'sess-prime' : 'sess-open');
      el.textContent = s.label + ' +' + s.bonus.toFixed(1);
    }} else {{
      el.className = 'sess sess-closed';
      el.textContent = s.label;
    }}
  }});
}}
updateSessions();
setInterval(updateSessions, 30000);
setInterval(poll, PRICE_IV * 1000);
setInterval(tick, 250);
tick(); poll();
</script>
</body>
</html>"""


def _render_alerts(alerts):
    if not alerts:
        return '<p class="dim" style="padding:1rem">No alerts yet — scanner is running&hellip;</p>'
    out = ""
    for a in alerts:
        dir_cls = "green" if a["direction"] == "LONG" else "red"
        passed  = sum(1 for c in a["checklist"] if c.startswith("[+]"))
        cl_html = "".join(
            f'<div class="{"cl-pass" if c.startswith("[+]") else "cl-neutral" if c.startswith("[~]") else "cl-fail"}">{c}</div>'
            for c in a["checklist"]
        )
        out += f"""
        <div class="alert {dir_cls}-border">
          <div class="alert-header {dir_cls}">
            {a["direction"]} &mdash; {a["symbol"]} &nbsp; Score: {a["score"]}/{"12" if a["direction"] == "LONG" else "11"}
            {f'&nbsp; <span class="dim">{a["alignment"]}</span>' if a.get("alignment") else ""}
            {f'&nbsp; <span class="dim">{a.get("session_label", "")} (+{a.get("session_bonus", 0):.1f})</span>' if a.get("session_label") else ""}
            &nbsp; {(lambda t: f'<span style="background:{_TREND_BADGE[t][1]};color:{_TREND_BADGE[t][2]};padding:.1rem .4rem;border-radius:8px;font-size:.8rem">{_TREND_BADGE[t][0]}</span>' if t in _TREND_BADGE else '')(a.get("trend") or "Choppy")}
            &nbsp; <span style="color:var(--{dir_cls})">Max {a["max_lev"]:.1f}x</span>
            &nbsp; <span class="dim">{a["time"]}</span>
          </div>
          <div class="alert-body">
            <div class="trade-grid">
              <div><span class="label">Price</span> ${a["price"]:.6g}</div>
              <div><span class="label">Entry</span> {a["entry"]:.6g}</div>
              <div><span class="label">SL</span> {a["sl"]:.6g} <span class="dim">({a["sl"] - a["entry"]:+.4g}) ({a["sl_pct"]:.2f}% risk)</span></div>
              <div><span class="label">TP1</span> {a["tp1"]:.6g} <span class="dim">({a["tp1"] - a["entry"]:+.4g}) (1.5R)</span></div>
              <div><span class="label">TP2</span> {a["tp2"]:.6g} <span class="dim">({a["tp2"] - a["entry"]:+.4g}) (2.0R)</span></div>
              <div><span class="label">Liq Price</span> <strong class="{'red' if a.get('liq_price') and a['liq_price'] > 0 else 'dim'}">{f'{a["liq_price"]:.6g}' if a.get('liq_price') and a['liq_price'] > 0 else 'N/A'}</strong></div>
              <div><span class="label">Max Lev</span> <strong>{a["max_lev"]:.1f}x</strong></div>
              <div><span class="label">Est. Profit</span> <strong class="green">${a.get("tp_dollar_gain", 0):.2f}</strong> <span class="dim">({a.get("tiered_lev", TRADE_LEV_FIXED):.0f}x / ${a.get("tiered_margin", TRADE_MARGIN):.0f})</span></div>
              <div><span class="label">R:R</span> 1:{a.get("rr_ratio", 0):.1f}</div>
              {f'<div><span class="label">Alignment</span> {a["alignment"]}</div>' if a.get("alignment") else ""}
              {f'<div><span class="label">Session</span> {a.get("session_label")} <span class="dim">(+{a.get("session_bonus", 0):.1f} bonus · eff. {a.get("effective_score", a["score"]):.1f}/{"12" if a["direction"] == "LONG" else "11"})</span></div>' if a.get("session_label") else ""}
              {f'<div><span class="label">15m J</span> {a["j15"]:.1f}</div>' if a.get("j15") is not None else ""}
            </div>
            <details><summary class="dim">Checklist ({passed}/{"12" if a["direction"] == "LONG" else "11"} passed)</summary>
              <div class="checklist">{cl_html}</div>
            </details>
          </div>
        </div>"""
    return out


class Handler(BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        pass

    def do_GET(self):
        path = self.path.split("?")[0]
        if path in ("/health", "/healthz"):
            body = json.dumps({
                "status": "ok",
                "time": datetime.now().isoformat(),
                "mode": ACCOUNT_MODE,
                "version": "2026-05-05",
            }).encode()
            self._respond(200, "application/json", body)
        elif path == "/api/v2/status":
            body = get_state_json().encode()
            self._respond(200, "application/json", body, cache=False)
        elif path == "/api/v2/threads":
            import threading as _thr
            thread_list = sorted(
                [{"name": t.name, "daemon": t.daemon, "alive": t.is_alive(), "ident": t.ident}
                 for t in _thr.enumerate()],
                key=lambda x: x["name"],
            )
            body = json.dumps({
                "total": len(thread_list),
                "threads": thread_list,
            }, indent=2).encode()
            self._respond(200, "application/json", body, cache=False)
        elif path == "/api/v2/myip":
            try:
                ip = _requests.get("https://api4.ipify.org", timeout=5).text.strip()
            except Exception as e:
                ip = f"unavailable: {e}"
            body = json.dumps({"outbound_ip": ip}).encode()
            self._respond(200, "application/json", body, cache=False)
        elif path == "/api/my-ip":
            try:
                ip = _requests.get("https://ifconfig.me", timeout=5).text.strip()
            except Exception as e:
                ip = f"unavailable: {e}"
            self._respond(200, "text/plain; charset=utf-8", ip.encode(), cache=False)
        elif path == "/api/test-hyperliquid":
            from hyperliquid_api import get_balance, get_open_positions
            balance   = get_balance()
            positions = get_open_positions()
            body = json.dumps({
                "available_balance_usdt": balance,
                "open_positions":         positions,
                "position_count":         len(positions),
            }, indent=2).encode()
            self._respond(200, "application/json", body, cache=False)
        elif path in ("/api/state", "/api/status"):
            self.send_response(301)
            self.send_header("Location", "/api/v2/status")
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
        elif path == "/test-alert":
            tok_ok  = bool(TELEGRAM_TOKEN)
            chat_ok = bool(TELEGRAM_CHAT_ID)
            if not tok_ok or not chat_ok:
                err = "TELEGRAM_BOT_TOKEN missing" if not tok_ok else "TELEGRAM_CHAT_ID missing"
                body = json.dumps({"error": err, "fix": "Set secrets in Replit Secrets panel"}, indent=2).encode()
                self._respond(200, "application/json", body, cache=False)
                return
            with _lock:
                zec = _state["symbols"].get("ZEC", {})
            lt    = zec.get("long_trade") or {}
            price = zec.get("price") or 410.0
            entry = lt.get("entry", price)
            sl    = lt.get("sl",    entry * (1 - 0.005))
            tp1   = lt.get("tp1",   entry * (1 + 0.0075))
            tp2   = lt.get("tp2",   entry * (1 + 0.010))
            lev   = lt.get("lev",   5.0)
            slp   = lt.get("sl_pct", 0.5)
            bonus, sess_label = get_session_bonus()
            _test_score = 9
            tiered_margin, tiered_lev, tier_label = get_tier(_test_score)
            pos_size  = tiered_margin * tiered_lev
            fee_cost  = pos_size * ROUND_TRIP_FEE
            tp1_pct   = abs(tp1 - entry) / entry if entry > 0 else 0
            sl_pct_v  = abs(sl  - entry) / entry if entry > 0 else 0
            tp1_gross = pos_size * tp1_pct
            tp1_net   = tp1_gross - fee_cost
            sl_gross  = pos_size * sl_pct_v
            sl_net    = sl_gross + fee_cost
            rr_net    = round(tp1_net / sl_net, 1) if sl_net > 0 else 0
            true_be   = entry * (1 + ROUND_TRIP_FEE)
            test_alert = {
                "time": now_est_short(), "symbol": "ZEC", "direction": "LONG",
                "score": _test_score, "price": price, "entry": entry, "sl": sl,
                "tp1": tp1, "tp2": tp2, "max_lev": lev, "sl_pct": slp,
                "liq_price": round(entry * (1 - 1 / max(tiered_lev, 0.01)), 2),
                "trend": zec.get("trend", "Bullish"),
                "rr_ratio": rr_net, "tp_dollar_gain": tp1_gross,
                "alignment": "✅ Trend confirmed", "session_label": sess_label,
                "session_bonus": bonus, "effective_score": float(_test_score) + bonus,
                "j15": None, "checklist": ["[+] TEST ALERT — diagnostics only"],
                "j5": 12.5, "bid_pct": 72.3, "ask_pct": 27.7,
                **dict(zip(("stale_low", "stale_high"), calc_stale_zone(entry, sl, "LONG"))),
            }
            try:
                send_telegram(test_alert)
                result = {
                    "status": "sent", "score": _test_score, "tier": tier_label,
                    "mode": ACCOUNT_MODE, "margin": tiered_margin, "leverage": tiered_lev,
                    "entry": round(entry, 4),
                    "tp1_gross": round(tp1_gross, 2), "tp1_net": round(tp1_net, 2),
                    "fee_cost": round(fee_cost, 2), "true_breakeven": round(true_be, 4),
                    "rr_net": rr_net,
                }
            except Exception as e:
                result = {"status": "error", "error": str(e)}
            body = json.dumps(result, indent=2).encode()
            self._respond(200, "application/json", body, cache=False)
        elif path == "/api/test-alert-gates":
            # ── Diagnostic gate test — live data, relaxed thresholds, no alerts ──
            RELAXED_SCORE   = 6
            RELAXED_J_LONG  = 50    # real: < 15
            RELAXED_J_SHORT = 50    # real: > 85
            RELAXED_DEPTH   = 50.0  # real: >= 70%

            _t0 = time.time()
            bonus, sess_label = get_session_bonus()

            # ── Parallel scan (live market data) ─────────────────────────────
            _scan_results, _scan_errors = {}, {}
            with ThreadPoolExecutor(max_workers=len(SYMBOLS)) as _ex:
                _futs = {_ex.submit(scan_symbol, s): s for s in SYMBOLS}
                for _fut in as_completed(_futs, timeout=45):
                    _sym = _futs[_fut]
                    try:
                        _scan_results[_sym] = _fut.result()
                    except Exception as _e:
                        _scan_errors[_sym] = str(_e)

            def _eval_dir(sym, score, eff, is_misaligned, j5_val, j_thr,
                          depth_val, tp_gain, ctr_thr, long_side):
                """Evaluate all gates for one direction; return structured dict."""
                _score_thr = BTC_MIN_SCORE if sym == 'BTC' else ALERT_THRESHOLD
                _tp_thr    = BTC_MIN_TP    if sym == 'BTC' else MIN_TP_DOLLARS

                bad_j = j5_val is not None and j5_val < -50

                # Real gate booleans
                c1 = eff >= _score_thr
                c2 = (j5_val is not None and not bad_j and
                      (j5_val < j_thr if long_side else j5_val > j_thr))
                c3 = not is_misaligned
                c4 = depth_val is not None and depth_val >= 70.0
                c5 = tp_gain is not None and tp_gain >= _tp_thr
                c6 = eff >= ctr_thr

                # Relaxed gate booleans (for "would fire" marker)
                r_c1 = eff >= RELAXED_SCORE
                r_c2 = (j5_val is not None and
                        (j5_val < RELAXED_J_LONG if long_side else j5_val > RELAXED_J_SHORT))
                r_c4 = depth_val is not None and depth_val >= RELAXED_DEPTH
                relaxed_fires = (r_c1 and r_c2 and c3 and r_c4 and
                                 (tp_gain is None or c5) and c6 and not bad_j)
                all_pass = c1 and c2 and c3 and c4 and c5 and c6 and not bad_j

                def _gap_j(v, thr, long):
                    """Gap to J threshold — positive means passing."""
                    if v is None: return None
                    return round(thr - v, 1) if long else round(v - thr, 1)

                gates = {
                    "C1_score": {
                        "pass": c1,
                        "value": round(eff, 1),
                        "threshold": _score_thr,
                        "gap": round(eff - _score_thr, 1),
                        "note": "effective score (raw + session bonus)",
                    },
                    "C2_j5": {
                        "pass": c2,
                        "value": round(j5_val, 1) if j5_val is not None else None,
                        "threshold": f"< {j_thr}" if long_side else f"> {j_thr}",
                        "gap_to_threshold": _gap_j(j5_val, j_thr, long_side),
                        "note": "positive gap = currently passing",
                    },
                    "C3_trend": {
                        "pass": c3,
                        "trend": trend_str,
                        "misaligned": is_misaligned,
                        "note": ("LONG blocked by bearish trend" if not c3 and long_side
                                 else "SHORT blocked by bullish trend" if not c3
                                 else "ok"),
                    },
                    "C4_depth": {
                        "pass": c4,
                        "value": round(depth_val, 1) if depth_val is not None else None,
                        "threshold": 70.0,
                        "gap": round(depth_val - 70.0, 1) if depth_val is not None else None,
                        "note": "bid% for LONG, ask% for SHORT",
                    },
                    "C5_tp": {
                        "pass": c5,
                        "value": round(tp_gain, 2) if tp_gain is not None else None,
                        "threshold": _tp_thr,
                        "gap": round(tp_gain - _tp_thr, 2) if tp_gain is not None else None,
                        "note": "estimated TP1 dollar gain at tiered position size",
                    },
                    "C6_counter_trend": {
                        "pass": c6,
                        "value": round(eff, 1),
                        "threshold": ctr_thr,
                        "gap": round(eff - ctr_thr, 1),
                        "note": ("neutral/choppy (ADX<=25) — needs score >= 9" if ctr_thr == COUNTER_TREND_MIN_SCORE
                                 else "trending or choppy+ADX>25 — uses standard score threshold"),
                    },
                }
                if bad_j:
                    gates["BAD_J_PRECHECK"] = {
                        "pass": False,
                        "value": round(j5_val, 1),
                        "note": "J5 < -50 indicates stale/error data — flushes pending",
                    }

                blocking = []
                if bad_j:
                    blocking.append(f"BAD_J: J5={j5_val:.1f} < -50 (data error)")
                if not c3:
                    blocking.append(f"C3_trend: {trend_str} misaligned for {'LONG' if long_side else 'SHORT'}")
                if not c1:
                    blocking.append(f"C1_score: eff={eff:.1f} needs {_score_thr} (gap {eff-_score_thr:+.1f})")
                if not c2:
                    if j5_val is None:
                        blocking.append("C2_j5: no data")
                    elif long_side:
                        blocking.append(f"C2_j5: J={j5_val:.1f} needs < {j_thr} (gap {j5_val-j_thr:+.1f})")
                    else:
                        blocking.append(f"C2_j5: J={j5_val:.1f} needs > {j_thr} (gap {j5_val-j_thr:+.1f})")
                if not c4:
                    dv = f"{depth_val:.1f}" if depth_val is not None else "N/A"
                    gv = f"{depth_val-70.0:+.1f}" if depth_val is not None else "N/A"
                    blocking.append(f"C4_depth: {dv}% needs >= 70% (gap {gv})")
                if not c5:
                    tv = f"${tp_gain:.2f}" if tp_gain is not None else "N/A"
                    blocking.append(f"C5_tp: {tv} needs >= ${_tp_thr:.0f} (gap {tp_gain-_tp_thr:+.2f if tp_gain is not None else 'N/A'})")
                if not c6:
                    blocking.append(f"C6_ctr: eff={eff:.1f} needs >= {ctr_thr} for {trend_str} trend")

                return {
                    "raw_score": score,
                    "eff_score": round(eff, 1),
                    "all_real_pass": all_pass,
                    "relaxed_would_fire": relaxed_fires,
                    "blocking_gates": blocking,
                    "gates": gates,
                }

            _out = {}
            _would_fire_relaxed, _all_real_pass = [], []

            for sym in SYMBOLS:
                if sym in _scan_errors:
                    _out[sym] = {"error": _scan_errors[sym]}
                    continue

                price, chg, ls, ss, ld, sd, c5m, trend, j15, extra = _scan_results[sym]
                trend_str   = (trend or "").strip()
                j5_val      = (extra.get("ind5m") or {}).get("j") if extra else None
                bid_pct     = extra.get("bid_pct") if extra else None
                ask_pct     = extra.get("ask_pct") if extra else None
                adx_val     = extra.get("adx") if extra else None
                eff_l       = ls + bonus
                eff_s       = ss + bonus
                is_long_mis  = trend_str in BEARISH_TRENDS
                is_short_mis = trend_str in BULLISH_TRENDS
                _score_thr  = BTC_MIN_SCORE if sym == 'BTC' else ALERT_THRESHOLD
                # C6: Choppy+ADX>25 → standard threshold; Choppy+ADX<=25 or Neutral → 9
                _ctr_l = (
                    _score_thr            if trend_str == "Choppy" and adx_val is not None and adx_val > 25
                    else COUNTER_TREND_MIN_SCORE if trend_str in NEUTRAL_TRENDS
                    else _score_thr
                )
                _ctr_s = _ctr_l  # symmetric — ADX applies equally to both directions

                try:
                    e_l, sl_l, tp1_l = calc_trade_params_long(price, c5m, symbol=sym)[:3]
                    _tm_l, _tlv_l, _ = get_tier(ls)
                    tp1_gain_l = _tm_l * _tlv_l * (abs(tp1_l - e_l) / e_l) if e_l > 0 else None
                except Exception:
                    tp1_gain_l = None

                try:
                    e_s, sl_s, tp1_s = calc_trade_params_short(price, c5m, symbol=sym)[:3]
                    _tm_s, _tlv_s, _ = get_tier(ss)
                    tp1_gain_s = _tm_s * _tlv_s * (abs(tp1_s - e_s) / e_s) if e_s > 0 else None
                except Exception:
                    tp1_gain_s = None

                long_r  = _eval_dir(sym, ls, eff_l, is_long_mis,  j5_val, 15, bid_pct, tp1_gain_l, _ctr_l, True)
                short_r = _eval_dir(sym, ss, eff_s, is_short_mis, j5_val, 85, ask_pct, tp1_gain_s, _ctr_s, False)

                if long_r["relaxed_would_fire"]:  _would_fire_relaxed.append(f"{sym} LONG")
                if short_r["relaxed_would_fire"]:  _would_fire_relaxed.append(f"{sym} SHORT")
                if long_r["all_real_pass"]:         _all_real_pass.append(f"{sym} LONG")
                if short_r["all_real_pass"]:         _all_real_pass.append(f"{sym} SHORT")

                _out[sym] = {
                    "price":         price,
                    "change_pct_24h": round(chg, 2),
                    "trend":          trend_str,
                    "j5":             round(j5_val, 1) if j5_val is not None else None,
                    "j15":            round(j15, 1) if j15 is not None else None,
                    "bid_pct":        round(bid_pct, 1) if bid_pct is not None else None,
                    "ask_pct":        round(ask_pct, 1) if ask_pct is not None else None,
                    "adx_1h":         round(adx_val, 1) if adx_val is not None else None,
                    "session_bonus":  round(bonus, 1),
                    "long":           long_r,
                    "short":          short_r,
                }

            _diag = {
                "generated_at":   now_est_short(),
                "elapsed_s":      round(time.time() - _t0, 2),
                "account_mode":   ACCOUNT_MODE,
                "session":        sess_label,
                "session_bonus":  round(bonus, 1),
                "real_thresholds": {
                    "score":                    ALERT_THRESHOLD,
                    "btc_score":                BTC_MIN_SCORE,
                    "j_long_must_be_below":     15,
                    "j_short_must_be_above":    85,
                    "depth_pct":                70,
                    "min_tp_dollars":           MIN_TP_DOLLARS,
                    "btc_min_tp":               BTC_MIN_TP,
                    "counter_trend_min_score":  COUNTER_TREND_MIN_SCORE,
                    "cooldown_secs":            900,
                    "confirmation_scans":       2,
                },
                "relaxed_thresholds": {
                    "score":                RELAXED_SCORE,
                    "j_long_must_be_below": RELAXED_J_LONG,
                    "j_short_must_be_above":RELAXED_J_SHORT,
                    "depth_pct":            RELAXED_DEPTH,
                    "note": "relaxed = diagnostic only; tp/trend/ctr gates unchanged",
                },
                "summary": {
                    "would_fire_relaxed":  _would_fire_relaxed,
                    "all_real_gates_pass": _all_real_pass,
                    "scan_errors":         _scan_errors,
                    "symbols_scanned":     len(_scan_results),
                },
                "symbols": _out,
            }
            body = json.dumps(_diag, indent=2, default=str).encode()
            self._respond(200, "application/json", body, cache=False)
        elif path in ("/", ""):
            body = build_html().encode()
            self._respond(200, "text/html; charset=utf-8", body, cache=False)
        elif path == "/log":
            body = build_log_html().encode()
            self._respond(200, "text/html; charset=utf-8", body, cache=False)
        elif path == "/api/trades":
            with _LOSS_LOCK:
                trades = list(_daily_trades)
            body = json.dumps(trades).encode()
            self._respond(200, "application/json", body, cache=False)
        elif path.startswith("/detail/"):
            sym = path[len("/detail/"):].upper()
            if sym in SYMBOLS:
                body = build_detail_html(sym).encode()
                self._respond(200, "text/html; charset=utf-8", body, cache=False)
            else:
                self.send_response(302)
                self.send_header("Location", "/")
                self.end_headers()
        elif path.startswith("/api/detail/"):
            sym = path[len("/api/detail/"):].upper()
            if sym in SYMBOLS:
                body = get_detail_json(sym).encode()
                self._respond(200, "application/json", body, cache=False)
            else:
                body = json.dumps({"error": "Symbol not found"}).encode()
                self._respond(404, "application/json", body, cache=False)
        else:
            self.send_response(404)
            self.end_headers()

    def do_POST(self):
        global daily_loss_total, _daily_limit_notified
        path = self.path.split("?")[0]
        if path == "/api/clear-alerts":
            with _lock:
                _state["alerts"].clear()
            body = json.dumps({"ok": True}).encode()
            self._respond(200, "application/json", body, cache=False)
        elif path == "/api/reset-daily-loss":
            daily_loss_total      = 0.0
            _daily_limit_notified = False
            msg = f"✅ Daily loss counter reset manually at {now_est_short()} EST"
            threading.Thread(target=_tg_post, args=(msg,), daemon=True).start()
            body = json.dumps({"ok": True, "daily_loss_total": 0}).encode()
            self._respond(200, "application/json", body, cache=False)
        elif path == "/api/clear-trades":
            global _daily_trades
            with _LOSS_LOCK:
                _save_trade_state(reset_daily=True)
            body = json.dumps({"ok": True, "cleared": True}).encode()
            self._respond(200, "application/json", body, cache=False)
        elif path == "/api/reset-losses":
            global CONSECUTIVE_LOSSES, API_TRADING_ENABLED
            with _LOSS_LOCK:
                CONSECUTIVE_LOSSES  = 0
                API_TRADING_ENABLED = True
                _save_trade_state()
            msg = (f"✅ Consecutive loss counter reset to 0. "
                   f"API trading re-enabled. {now_est_short()}")
            threading.Thread(target=_tg_post, args=(msg,), daemon=True).start()
            body = json.dumps({"ok": True, "consecutive_losses": 0,
                               "api_trading_enabled": True}).encode()
            self._respond(200, "application/json", body, cache=False)
        else:
            self.send_response(404)
            self.end_headers()

    def _respond(self, code, content_type, body, cache=True):
        self.send_response(code)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        if not cache:
            self.send_header("Cache-Control", "no-store, no-cache, must-revalidate")
            self.send_header("Pragma", "no-cache")
            self.send_header("Expires", "0")
        self.end_headers()
        self.wfile.write(body)


def _scanner_envelope():
    """Outer restart guard — catches any exception that escapes run_scanner's while loop."""
    import traceback as _tb
    while True:
        try:
            run_scanner()
        except Exception as _err:
            print(f"SCANNER FATAL ({type(_err).__name__}): {_err} — restarting in 5s")
            _tb.print_exc()
        time.sleep(5)


_watchdog_last_spawn: float = 0.0   # epoch of last recovery spawn — prevents pile-up

def _watchdog():
    """Independent staleness monitor — if no scan heartbeat for > 120 s, spawn a new runner.
    Threshold: 3.5s stagger + 45s fetch timeout + 20s sleep + 51.5s buffer = 120s.
    Dedup guard: will not spawn more than once per 120s to prevent cascading threads."""
    global _watchdog_last_spawn
    while True:
        time.sleep(30)
        age = (datetime.now(tz=EST) - _last_scan_dt).total_seconds()
        if age > 120:
            now_epoch = time.time()
            if now_epoch - _watchdog_last_spawn > 120:
                _watchdog_last_spawn = now_epoch
                print(f"WATCHDOG: scan stale ({age:.0f}s since last heartbeat) — spawning recovery thread")
                threading.Thread(target=_scanner_envelope, daemon=True).start()
            else:
                secs = int(120 - (now_epoch - _watchdog_last_spawn))
                print(f"WATCHDOG: scan stale ({age:.0f}s) — recovery already spawned, waiting {secs}s")


def main():
    print(f"Hyperliquid Futures Scanner — web mode")
    print(f"Symbols  : {', '.join(SYMBOLS)}")
    print(f"Prices   : every {PRICE_INTERVAL}s   (times in EST)")
    print(f"Full scan: every {SCAN_INTERVAL}s   Threshold: {ALERT_THRESHOLD}/11   Min TP: ${MIN_TP_DOLLARS:.0f}")
    _tok_display  = (TELEGRAM_TOKEN[:10] + "…" + TELEGRAM_TOKEN[-4:]) if len(TELEGRAM_TOKEN) > 14 else ('SET' if TELEGRAM_TOKEN else '*** NOT SET ***')
    _chat_display = TELEGRAM_CHAT_ID if TELEGRAM_CHAT_ID else '*** NOT SET ***'
    print(f"Telegram : TOKEN={_tok_display}  CHAT_ID={_chat_display}")
    try:
        _outbound_ip = _requests.get("https://api4.ipify.org", timeout=5).text.strip()
    except Exception:
        _outbound_ip = "unavailable"
    print(f"Outbound IP: {_outbound_ip}")
    print(f"Serving  : http://0.0.0.0:{PORT}/\n")

    threading.Thread(target=run_price_loop,         daemon=True).start()
    threading.Thread(target=_scanner_envelope,      daemon=True).start()
    threading.Thread(target=_watchdog,              daemon=True).start()
    threading.Thread(target=_midnight_summary_loop, daemon=True).start()
    threading.Thread(target=_balance_loop,          daemon=True).start()

    server = HTTPServer(("0.0.0.0", PORT), Handler)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")


if __name__ == "__main__":
    main()
