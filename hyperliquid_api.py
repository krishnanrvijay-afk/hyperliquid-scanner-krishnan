"""
hyperliquid_api.py — Hyperliquid Futures trading module

Mirrors the public interface of mexc_api.py so that scanner_server.py
requires only the import swap (mexc_api → hyperliquid_api).

Auth   : reads HL_PRIVATE_KEY from environment (hex private key, 0x-prefixed).
Network: MAINNET https://api.hyperliquid.xyz — no testnet fallback.
SDK    : hyperliquid-python-sdk, eth-account
"""

import os
import time
import threading
import requests

HL_BASE_URL  = "https://api.hyperliquid.xyz"
HL_INFO_URL  = f"{HL_BASE_URL}/info"
HL_PRIVATE_KEY = os.environ.get("HL_PRIVATE_KEY", "")

# ── Lazy SDK initialisation ───────────────────────────────────────────────────
# SDK clients are created on first use so the module can be imported
# even when HL_PRIVATE_KEY is not set (read-only / dry-run mode).

_exchange   = None
_info_client = None
_address    = None
_init_lock  = threading.Lock()


def _get_clients():
    """Return (Exchange, Info, wallet_address) — initialised once per process."""
    global _exchange, _info_client, _address
    if _exchange is not None:
        return _exchange, _info_client, _address
    with _init_lock:
        if _exchange is not None:
            return _exchange, _info_client, _address
        from hyperliquid.exchange import Exchange
        from hyperliquid.info import Info
        from eth_account import Account
        if not HL_PRIVATE_KEY:
            raise RuntimeError(
                "HL_PRIVATE_KEY environment variable is not set. "
                "Set it to your Hyperliquid wallet private key (0x-prefixed hex)."
            )
        acct = Account.from_key(HL_PRIVATE_KEY)
        _address     = acct.address
        _info_client = Info(base_url=HL_BASE_URL, skip_ws=True)
        _exchange    = Exchange(wallet=acct, base_url=HL_BASE_URL)
        print(f"[hl] SDK initialised — wallet: {_address[:6]}…{_address[-4:]}")
        return _exchange, _info_client, _address


# ── Public price feed (no auth) ───────────────────────────────────────────────

def _get_price(symbol: str) -> float | None:
    """Return latest mark price for symbol from Hyperliquid Info API."""
    try:
        r = requests.post(HL_INFO_URL, json={"type": "metaAndAssetCtxs"}, timeout=5)
        data = r.json()
        universe = data[0]["universe"]
        ctxs     = data[1]
        idx = next((i for i, a in enumerate(universe) if a["name"] == symbol), None)
        if idx is not None:
            return float(ctxs[idx].get("markPx", 0) or 0)
    except Exception as exc:
        print(f"  [hl] _get_price({symbol}) error: {exc}")
    return None


# ── Account ───────────────────────────────────────────────────────────────────

def get_balance() -> float:
    """Return withdrawable USDT balance."""
    try:
        _, info, address = _get_clients()
        state = info.user_state(address)
        return float(state.get("withdrawable", 0) or 0)
    except Exception as exc:
        print(f"  [hl] get_balance error: {exc}")
        return 0.0


def get_open_positions(symbol: str = None) -> list:
    """Return list of open positions, optionally filtered by coin name."""
    try:
        _, info, address = _get_clients()
        state = info.user_state(address)
        positions = []
        for ap in state.get("assetPositions", []):
            pos = ap.get("position", {})
            szi = float(pos.get("szi", 0) or 0)
            if szi == 0:
                continue
            coin = pos.get("coin", "")
            if symbol and coin != symbol:
                continue
            lev_info = pos.get("leverage", {}) or {}
            leverage = int(lev_info.get("value", 1)) if isinstance(lev_info, dict) else 1
            positions.append({
                "symbol":        coin,
                "holdSide":      "LONG" if szi > 0 else "SHORT",
                "holdVol":       abs(szi),
                "entryPx":       float(pos.get("entryPx",        0) or 0),
                "unrealised":    float(pos.get("unrealizedPnl",  0) or 0),
                "liquidationPx": (float(pos.get("liquidationPx", 0))
                                  if pos.get("liquidationPx") else None),
                "marginUsed":    float(pos.get("marginUsed",     0) or 0),
                "leverage":      leverage,
            })
        return positions
    except Exception as exc:
        print(f"  [hl] get_open_positions error: {exc}")
        return []


def get_position(symbol: str) -> dict | None:
    """Return single open position for symbol or None."""
    positions = get_open_positions(symbol)
    return positions[0] if positions else None


# ── Order helpers ─────────────────────────────────────────────────────────────

def calc_vol(margin_usdt: float, price: float, leverage: int) -> float:
    """Contract size for a given margin, price and leverage.
    Hyperliquid sizes are in coin units: sz = (margin * leverage) / price.
    """
    if price <= 0:
        return 0.0
    return round(margin_usdt * leverage / price, 6)


# ── Alert-driven order placement ─────────────────────────────────────────────

def place_order_from_alert(
    symbol: str,
    direction: str,       # "LONG" or "SHORT"
    entry_price: float,
    sl_price: float,
    tp1_price: float,
    tp2_price: float,
    margin_usdt: float,
    leverage: int,
    dry_run: bool = False,
) -> dict:
    """
    Place a Hyperliquid futures order from a scanner alert.

    Calculates coin size from margin_usdt, entry_price and leverage.
    Sets leverage to isolated mode before placing.
    SL is set as a reduce-only trigger order after entry is placed.
    tp1_price is included in the return value for reference.
    tp2_price is registered as a TP limit order (reduce-only).
    dry_run=True prints params without hitting the API.
    """
    is_buy   = direction == "LONG"
    pos_size = margin_usdt * leverage
    sz       = calc_vol(margin_usdt, entry_price, leverage)

    order_params = {
        "symbol":      symbol,
        "direction":   direction,
        "is_buy":      is_buy,
        "entry_price": entry_price,
        "sl_price":    sl_price,
        "tp1_price":   tp1_price,
        "tp2_price":   tp2_price,
        "margin_usdt": margin_usdt,
        "leverage":    leverage,
        "sz":          sz,
    }

    if dry_run:
        risk_usdt = abs(entry_price - sl_price)  / entry_price * pos_size
        tp1_usdt  = abs(tp1_price   - entry_price) / entry_price * pos_size
        tp2_usdt  = abs(tp2_price   - entry_price) / entry_price * pos_size
        print("=" * 55)
        print(f"  DRY RUN — {direction} {symbol}")
        print("=" * 55)
        print(f"  Entry     : {entry_price}")
        print(f"  SL        : {sl_price}  (risk ≈ ${risk_usdt:.2f})")
        print(f"  TP1       : {tp1_price}  (≈ +${tp1_usdt:.2f})  [manual]")
        print(f"  TP2       : {tp2_price}  (≈ +${tp2_usdt:.2f})  [exchange TP]")
        print(f"  Margin    : ${margin_usdt:.2f}  Lev: {leverage}x")
        print(f"  Position  : ${pos_size:.2f}  Size: {sz} {symbol}")
        print("=" * 55)
        return {"dry_run": True, "params": order_params}

    try:
        exchange, _, _ = _get_clients()

        # Set isolated leverage
        exchange.update_leverage(leverage, symbol, is_cross=False)

        # Entry limit order
        entry_result = exchange.order(
            name=symbol,
            is_buy=is_buy,
            sz=sz,
            limit_px=entry_price,
            order_type={"limit": {"tif": "Gtc"}},
            reduce_only=False,
        )

        # Stop-loss trigger order (reduce-only)
        sl_result = exchange.order(
            name=symbol,
            is_buy=not is_buy,
            sz=sz,
            limit_px=sl_price,
            order_type={"trigger": {"isMarket": True, "triggerPx": sl_price, "tpsl": "sl"}},
            reduce_only=True,
        )

        # TP2 limit order (reduce-only)
        tp_result = exchange.order(
            name=symbol,
            is_buy=not is_buy,
            sz=sz,
            limit_px=tp2_price,
            order_type={"limit": {"tif": "Gtc"}},
            reduce_only=True,
        )

        return {
            "success":      True,
            "entry_result": entry_result,
            "sl_result":    sl_result,
            "tp_result":    tp_result,
            "params":       order_params,
        }

    except Exception as exc:
        print(f"  [hl] place_order_from_alert error: {exc}")
        return {"success": False, "message": str(exc), "params": order_params}


# ── Position management ───────────────────────────────────────────────────────

def close_partial(symbol: str, pct: float, price: float = None) -> dict:
    """Close a percentage (0.0–1.0) of open position at market."""
    try:
        exchange, _, _ = _get_clients()
        pos = get_position(symbol)
        if not pos:
            return {"success": False, "message": "No open position found"}
        close_sz = round(float(pos["holdVol"]) * pct, 6)
        result = exchange.market_close(symbol, sz=close_sz)
        return {"success": True, "result": result, "sz_closed": close_sz}
    except Exception as exc:
        print(f"  [hl] close_partial error: {exc}")
        return {"success": False, "message": str(exc)}


def update_sl(symbol: str, sl_price: float) -> dict:
    """Update stop loss — replaces existing SL with a new reduce-only trigger order."""
    try:
        exchange, _, _ = _get_clients()
        pos = get_position(symbol)
        if not pos:
            return {"success": False, "message": "No open position found"}
        is_long = pos["holdSide"] == "LONG"
        sz      = float(pos["holdVol"])
        result  = exchange.order(
            name=symbol,
            is_buy=not is_long,
            sz=sz,
            limit_px=sl_price,
            order_type={"trigger": {"isMarket": True, "triggerPx": sl_price, "tpsl": "sl"}},
            reduce_only=True,
        )
        return {"success": True, "result": result}
    except Exception as exc:
        print(f"  [hl] update_sl error: {exc}")
        return {"success": False, "message": str(exc)}


# ── Position monitor ──────────────────────────────────────────────────────────

_TRAIL_PCT: dict[str, float] = {
    "BTC":  0.003,
    "ETH":  0.002,
    "SOL":  0.003,
    "LINK": 0.003,
    "ZEC":  0.005,
    "DOGE": 0.005,
    "SUI":  0.005,
    "XRP":  0.005,
}
_FEE_BUFFER      = 0.0007   # 0.07% round-trip (0.035% × 2) for breakeven SL
TRAILING_ENABLED = os.environ.get("TRAILING_ENABLED", "True").strip().lower() == "true"


def monitor_position(
    symbol: str,
    direction: str,       # "LONG" or "SHORT"
    entry_price: float,
    tp1_price: float,
    sl_price: float,
    margin_usdt: float,
    leverage: int = 5,
    poll_interval: int = 5,
    on_close: "callable | None" = None,
) -> threading.Thread:
    """
    Monitor a Hyperliquid position in a background thread.

    Mirrors the mexc_api.monitor_position interface exactly.

    Lifecycle:
      1. Poll mark price every poll_interval seconds via Hyperliquid Info API.
      2. At midpoint (entry → TP1): move SL to breakeven (entry ± fee buffer).
      3. Early trail (when TRAILING_ENABLED):
           After ≥ 2 min AND unrealised PNL ≥ 50% of TP1 dollar target —
           activate trailing stop BEFORE TP1.
           If price reverses from peak by trail %, close 100% at market.
           If TP1 hit while early trail active: close 70%, trail remaining 30%.
      4. At TP1: close 70%, activate post-TP1 trailing stop on remaining 30%.
      5. Post-TP1 trail reversal by trail % closes remaining 30% at market.
      6. on_close(outcome, trade_info) called when trade resolves.

    Trail % by symbol: BTC/SOL/LINK 0.3%, ETH 0.2%, ZEC/DOGE/SUI/XRP 0.5%.

    Returns the daemon thread (already started).
    """
    trail_pct = _TRAIL_PCT.get(symbol, 0.003)
    pos_size  = margin_usdt * leverage
    midpoint  = (entry_price + tp1_price) / 2.0
    be_sl     = (entry_price * (1 + _FEE_BUFFER) if direction == "LONG"
                 else entry_price * (1 - _FEE_BUFFER))
    tp1_dollar           = abs(tp1_price - entry_price) / entry_price * pos_size
    activation_threshold = tp1_dollar * 0.5

    def _run() -> None:
        nonlocal sl_price
        be_moved: bool            = False
        tp1_hit: bool             = False
        early_trail_active: bool  = False
        early_trail_peak: float | None = None
        trail_peak: float | None  = None
        open_time: float          = time.time()

        tag = f"{symbol} {direction}"
        print(
            f"[MONITOR] {tag} started | entry={entry_price} "
            f"mid={midpoint:.6g} tp1={tp1_price} "
            f"tp1_dollar=${tp1_dollar:.2f} trail_threshold=${activation_threshold:.2f} "
            f"trail={trail_pct*100:.1f}% TRAILING_ENABLED={TRAILING_ENABLED}"
        )

        def _mk_trade(exit_price: float, reason: str) -> dict:
            raw_pnl = ((exit_price - entry_price) / entry_price * pos_size
                       if direction == "LONG"
                       else (entry_price - exit_price) / entry_price * pos_size)
            fee = pos_size * _FEE_BUFFER
            return {
                "symbol":    symbol, "direction": direction,
                "entry":     entry_price, "exit": exit_price,
                "pnl":       round(raw_pnl - fee, 2), "reason": reason,
            }

        while True:
            try:
                price = _get_price(symbol)
                if price is None:
                    time.sleep(poll_interval)
                    continue

                elapsed = time.time() - open_time
                pnl_usd = ((price - entry_price) / entry_price * pos_size
                           if direction == "LONG"
                           else (entry_price - price) / entry_price * pos_size)

                # ── SL hit ──────────────────────────────────────────────────
                sl_hit = ((direction == "LONG"  and price <= sl_price) or
                          (direction == "SHORT" and price >= sl_price))
                if sl_hit:
                    print(f"[MONITOR] {tag} SL hit at {price:.6g}")
                    if on_close:
                        on_close("loss", _mk_trade(price, "sl"))
                    return

                # ── Midpoint → breakeven SL ──────────────────────────────────
                if not be_moved:
                    mid_hit = ((direction == "LONG"  and price >= midpoint) or
                               (direction == "SHORT" and price <= midpoint))
                    if mid_hit:
                        be_moved = True
                        sl_price = be_sl
                        update_sl(symbol, be_sl)
                        print(f"[MONITOR] {tag} midpoint hit — SL → BE {be_sl:.6g}")

                # ── Early trail (before TP1) ─────────────────────────────────
                if TRAILING_ENABLED and not tp1_hit and elapsed >= 120 and pnl_usd >= activation_threshold:
                    if not early_trail_active:
                        early_trail_active = True
                        early_trail_peak   = price
                        print(f"[MONITOR] {tag} early trail activated at {price:.6g}")
                    else:
                        if direction == "LONG":
                            early_trail_peak = max(early_trail_peak, price)
                            if price <= early_trail_peak * (1 - trail_pct):
                                print(f"[MONITOR] {tag} early trail triggered — closing at {price:.6g}")
                                close_partial(symbol, 1.0)
                                outcome = "win" if pnl_usd > 0 else "loss"
                                if on_close:
                                    on_close(outcome, _mk_trade(price, "early_trail"))
                                return
                        else:
                            early_trail_peak = min(early_trail_peak, price)
                            if price >= early_trail_peak * (1 + trail_pct):
                                print(f"[MONITOR] {tag} early trail triggered — closing at {price:.6g}")
                                close_partial(symbol, 1.0)
                                outcome = "win" if pnl_usd > 0 else "loss"
                                if on_close:
                                    on_close(outcome, _mk_trade(price, "early_trail"))
                                return

                # ── TP1 ──────────────────────────────────────────────────────
                if not tp1_hit:
                    tp1_reached = ((direction == "LONG"  and price >= tp1_price) or
                                   (direction == "SHORT" and price <= tp1_price))
                    if tp1_reached:
                        tp1_hit    = True
                        trail_peak = price
                        close_partial(symbol, 0.7)
                        print(f"[MONITOR] {tag} TP1 hit at {price:.6g} — closed 70%, trailing 30%")

                # ── Post-TP1 trail ───────────────────────────────────────────
                if tp1_hit and trail_peak is not None:
                    if direction == "LONG":
                        trail_peak = max(trail_peak, price)
                        if price <= trail_peak * (1 - trail_pct):
                            print(f"[MONITOR] {tag} trail stop — closing remaining at {price:.6g}")
                            close_partial(symbol, 1.0)
                            if on_close:
                                on_close("win", _mk_trade(price, "trail_tp2"))
                            return
                    else:
                        trail_peak = min(trail_peak, price)
                        if price >= trail_peak * (1 + trail_pct):
                            print(f"[MONITOR] {tag} trail stop — closing remaining at {price:.6g}")
                            close_partial(symbol, 1.0)
                            if on_close:
                                on_close("win", _mk_trade(price, "trail_tp2"))
                            return

                time.sleep(poll_interval)

            except Exception as exc:
                print(f"[MONITOR] {tag} error: {exc}")
                time.sleep(poll_interval)

    t = threading.Thread(target=_run, daemon=True, name=f"monitor-{symbol}-{direction}")
    t.start()
    return t


# ── Module self-test ──────────────────────────────────────────────────────────

if __name__ == "__main__":
    print("Hyperliquid API Module — connection test")
    print(f"HL_PRIVATE_KEY: {'configured' if HL_PRIVATE_KEY else 'MISSING'}")
    print()

    balance   = get_balance()
    print(f"Available balance : ${balance:.2f} USDT")

    positions = get_open_positions()
    if positions:
        print(f"Open positions    : {len(positions)}")
        for p in positions:
            print(f"  {p['symbol']} {p['holdSide']} sz={p['holdVol']} pnl={p['unrealised']:.2f}")
    else:
        print("Open positions    : none")

    print()
    place_order_from_alert(
        symbol="ETH", direction="LONG",
        entry_price=2500.0, sl_price=2450.0,
        tp1_price=2570.0,   tp2_price=2620.0,
        margin_usdt=700.0,  leverage=5, dry_run=True,
    )
    place_order_from_alert(
        symbol="SOL", direction="SHORT",
        entry_price=150.0,  sl_price=153.0,
        tp1_price=146.0,    tp2_price=143.0,
        margin_usdt=700.0,  leverage=5, dry_run=True,
    )
