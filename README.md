# Hyperliquid Futures Scanner

A real-time Hyperliquid perpetuals market scanner built from the MEXC scanner codebase, adapted to use Hyperliquid's MAINNET endpoints exclusively.

## What it does

Scans 8 Hyperliquid perpetual markets every 20 seconds, scores LONG and SHORT setups across 13 technical criteria, and fires Telegram alerts when high-confidence setups align. Includes a live dashboard, ADX-aware counter-trend gating, tiered position sizing, and a trailing stop monitor.

**Scanned pairs:** ZEC, SOL, BTC, ETH, XRP, DOGE, LINK, SUI

## Architecture

| File | Role |
|---|---|
| `scanner.py` | Technical indicators, scoring engine, Hyperliquid Info API data fetching |
| `scanner_server.py` | HTTP dashboard server, alert engine, gate evaluation, Telegram notifications |
| `hyperliquid_api.py` | Trading module — order placement, position monitoring, SL/TP management via Hyperliquid SDK |

## Data endpoints (MAINNET only)

All market data comes from `https://api.hyperliquid.xyz/info`:

| Data | Endpoint type |
|---|---|
| Candles (5m / 15m / 1h) | `candleSnapshot` POST |
| Price, funding, 24h change | `metaAndAssetCtxs` POST |
| Order book depth | `l2Book` POST |

No testnet fallback is implemented. The scanner connects to Hyperliquid MAINNET at all times.

## Environment variables

| Variable | Required | Description |
|---|---|---|
| `HL_PRIVATE_KEY` | Yes (live trading) | Hyperliquid wallet private key (0x-prefixed hex) |
| `TELEGRAM_BOT_TOKEN` | Recommended | Telegram bot token for alerts |
| `TELEGRAM_CHAT_ID` | Recommended | Telegram chat/channel ID |
| `PORT` | Auto | HTTP server port (default 8000) |
| `SCAN_INTERVAL` | No | Scan cycle interval in seconds (default 20) |
| `ALERT_THRESHOLD` | No | Minimum score to alert (default 8) |
| `ACCOUNT_MODE` | No | `SMALL` / `MEDIUM` / `LARGE` — sets position sizing (default SMALL) |
| `API_TRADING_ENABLED` | No | Set `True` to enable live order placement (default False / dry-run) |

## Fee rates

- Taker fee: **0.035%** per side (Hyperliquid standard)
- Round-trip: **0.07%** (used for breakeven SL calculation)

## Scoring

Scores are computed independently for LONG (max 13) and SHORT (max 12) using:
- MA structure (5m + 1h), EMA20, price position vs MA60
- KDJ oscillator (5m, 15m, 1h)
- Order book depth and wall detection
- Volume surge and trend confirmation
- ADX (Wilder-smoothed, 14-period on 1H candles)
- Funding rate neutrality

## Alert gates (all must pass)

| Gate | LONG | SHORT |
|---|---|---|
| C1 Score | eff ≥ 8 (BTC: 9) | eff ≥ 8 (BTC: 9) |
| C2 KDJ J5 | J < 15 | J > 85 |
| C3 Trend | not bearish | not bullish |
| C4 Depth | bid% ≥ 70% | ask% ≥ 70% |
| C5 TP $ | ≥ $15 SMALL / $25 MEDIUM / $75 LARGE | same |
| C6 Counter-trend | Choppy+ADX>25: score ≥ 8; Choppy+ADX≤25 or Neutral: score ≥ 9 | same |

## Origin

Ported from the MEXC scanner (`mexc-scanner-krishnan`). The scoring engine, dashboard, and alert logic are identical. Only the market data fetching (scanner.py) and trading execution (hyperliquid_api.py vs mexc_api.py) differ.
