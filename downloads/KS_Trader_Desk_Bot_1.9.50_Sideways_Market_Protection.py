#!/usr/bin/env python3
"""KS Trader Desk -> Exness Trading API (demo-only, Indie parity; Entry 1=50% midpoint, Entry 2=20% retracement only).
Signal checks run once per newly completed M1 candle. Each signal group has a
50% midpoint leg and, where broker volume/risk limits permit, a directional
20% leg. Both share the master SL/TP and are independently reconciled/tracked.
Daily risk capital is captured from the current Exness balance at the first bot run of each IST day and then frozen for that day.

Strategy ported from the user's supplied Indie v5 indicator for its 1-minute
chart configuration. Entry 3+ add-on markers/orders are removed. No market-order fallback; max two pending legs.
Indie-aligned trailing: master trailing is gated by active 50% Entry 1; M1 three-close confirmation.
"""
from __future__ import annotations

import base64
import hashlib
import json
import logging
import math
import os
import re
import sqlite3
import sys
import time
import uuid
import threading
from dataclasses import dataclass, replace
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from pathlib import Path
from typing import Any
from urllib.parse import urlencode, urlparse

import pandas as pd
import requests
try:
    import websocket  # websocket-client; required for live quote validation
except ImportError:
    websocket = None
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives.serialization import load_pem_private_key
from dotenv import load_dotenv
from decimal import Decimal
APP_VERSION = "1.9.50-sideways-market-protection"  # Indie Entry 1/2 only + pre-entry checklist
UTC = timezone.utc
IST = ZoneInfo("Asia/Kolkata")
_RECENT_EXNESS_DEALS_CACHE: dict[str, Any] = {}
# Last preflight-block signature per group/leg; avoids repeated identical warnings/events.
_PREFLIGHT_BLOCK_SIGNATURES: dict[tuple[str, str], str] = {}



def env_bool(name: str, default: bool = False) -> bool:
    raw = os.getenv(name)
    if raw is None:
        return default
    return raw.strip().lower() in {"1", "true", "yes", "y", "on"}


def b64url(raw: bytes) -> str:
    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def utc_iso(dt: datetime) -> str:
    return dt.astimezone(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def dec(value: Any) -> Decimal:
    return Decimal(str(value))


def executable_sl_hit(side: str, bid: Any, ask: Any, sl: Any) -> bool:
    """Check stop using the broker's executable close side.

    BUY positions close at Bid; SELL positions close at Ask. The Indie chart
    signal/setup logic remains Bid-OHLC based, but live broker-side SELL SL
    protection must use Ask to avoid waiting for Bid High to reach the stop.
    """
    normalized = str(side).strip().lower()
    stop = dec(sl)
    bid_price, ask_price = dec(bid), dec(ask)
    if normalized == "buy":
        return bid_price <= stop
    if normalized == "sell":
        return ask_price >= stop
    return False


class QuietConsoleFilter(logging.Filter):
    """Hide routine status/file-path chatter in CMD; retain it in the log file."""
    SUPPRESSED_PREFIXES = (
        "Python daily group P/L report refreshed:",
        "Entry method:",
        "Saved Exness instrument conditions and account API limits",
        "Daily closed P/L:",
        "EXNESS DAILY ACCOUNT P/L |",
        "XAUUSD trading settings loaded:",
        "XAUUSD trading settings loaded",
        # Routine signal diagnostics are kept in ks_trader_bot.log, not CMD.
        "INDIE SIGNAL CANDLE |",
        "INDIE PARITY CALC |",
        "ADAPTIVE ORDER TYPE |",
        "GROUP CREATED |",
        "SIGNAL GROUP RESULT |",
        "EXNESS OPERATION REJECTION DETAIL |",
        # Repeated quote/preflight failures remain in ks_trader_bot.log;
        # CMD is reserved for concise trade lifecycle updates.
        "ORDER PREFLIGHT BLOCKED",
        "ORDER WAITING |",
        # Setup polling/wait diagnostics are internal-only. Keep them in the
        # technical log file, never in the user's CMD window.
        "Waiting for more completed 1-minute and 3-minute market data.",
        "Waiting for enough completed market candles before checking for a signal.",
        "No M1 candles are currently available",
        "No M3 candles are currently available",
        "M1/M3 setup check",
        "LIVE MARKET CHECK",
        "Checking live market",
        "Exness did not provide the optional order_types list.",
        "GROUP ",  # detailed per-leg status/accepted-operation chatter
    )

    def filter(self, record: logging.LogRecord) -> bool:
        message = record.getMessage()
        # Keep the concise, meaningful rejection summary; suppress only verbose
        # per-leg routine messages and the full rejection JSON payload.
        if message.startswith("GROUP ") and "definitively rejected" in message:
            return True
        return not any(message.startswith(prefix) for prefix in self.SUPPRESSED_PREFIXES)


def log_table(title: str, rows: list[tuple[str, Any]]) -> None:
    """Write compact aligned rows to the console and detailed log."""
    key_width = max([len(str(key)) for key, _ in rows] + [8])
    value_width = max([len(str(value)) for _, value in rows] + [10])
    border = "+" + "-" * (key_width + 2) + "+" + "-" * (value_width + 2) + "+"
    table_lines = [title, border,
                   f"| {'SETTING':<{key_width}} | {'VALUE':<{value_width}} |",
                   border]
    table_lines.extend(f"| {str(key):<{key_width}} | {str(value):<{value_width}} |" for key, value in rows)
    table_lines.append(border)
    logging.info("%s", "\n".join(table_lines))


def configure_logging(log_level: str) -> None:
    """Keep CMD concise; preserve all technical details in ks_trader_bot.log."""
    root = logging.getLogger()
    root.handlers.clear()
    root.setLevel(logging.DEBUG)

    console = logging.StreamHandler(sys.stdout)
    configured_level = getattr(logging, log_level, logging.INFO)
    console.setLevel(max(logging.INFO, configured_level))
    console.addFilter(QuietConsoleFilter())
    console.setFormatter(logging.Formatter("%(asctime)s | %(message)s", datefmt="%H:%M:%S"))

    details = logging.FileHandler("ks_trader_bot.log", encoding="utf-8")
    details.setLevel(logging.DEBUG)
    details.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))

    root.addHandler(console)
    root.addHandler(details)


class APIHTTPError(RuntimeError):
    def __init__(self, status_code: int, payload: Any):
        self.status_code = status_code
        self.payload = payload
        super().__init__(f"Exness API HTTP {status_code}: {payload}")


class RateLimitCooldownError(RuntimeError):
    """Raised locally while Exness rate-limit cooldown is active; no HTTP call is made."""
    def __init__(self, remaining: float):
        self.remaining = max(0.0, float(remaining))
        super().__init__(f"Exness API cooldown active for {self.remaining:.1f}s; request held locally.")


def api_retry_after_seconds(payload: Any, default: int = 60) -> int:
    """Return a bounded wait based on Exness retry_after, when supplied."""
    if isinstance(payload, dict):
        raw = payload.get("retry_after")
        if isinstance(raw, str) and raw.strip():
            try:
                target = datetime.fromisoformat(raw.strip().replace("Z", "+00:00"))
                if target.tzinfo is None:
                    target = target.replace(tzinfo=UTC)
                return max(1, min(300, math.ceil((target - datetime.now(UTC)).total_seconds())))
            except (TypeError, ValueError):
                pass
    return max(1, min(300, int(default)))


class UncertainPostError(RuntimeError):
    """POST outcome is unknown; the caller must reconcile and must not retry."""


@dataclass
class Config:
    api_key: str
    secret_key: str
    account_id: str
    gateway_url: str
    instrument: str
    account_mode: str
    trading_enabled: bool
    account_capital: float
    risk_percent: float
    risk_buffer_percent: float
    contract_size: float
    risk_reward: str
    poll_seconds: int
    db_path: str
    log_level: str
    candles_count: int

    @classmethod
    def from_env(cls) -> "Config":
        load_dotenv()
        cfg = cls(
            api_key=os.getenv("EXN_API_KEY", "").strip(),
            secret_key=os.getenv("EXN_SECRET_KEY", "").strip(),
            account_id=os.getenv("EXN_ACCOUNT_ID", "").strip(),
            gateway_url=os.getenv("EXN_GATEWAY_URL", "").strip().rstrip("/"),
            instrument=os.getenv("EXN_INSTRUMENT", "XAUUSD").strip(),
            account_mode=os.getenv("EXN_ACCOUNT_MODE", "demo").strip().lower(),
            trading_enabled=env_bool("TRADING_ENABLED", False),
            account_capital=float(os.getenv("ACCOUNT_CAPITAL", "1000.0")),
            risk_percent=float(os.getenv("RISK_PERCENT", "5.0")),
            risk_buffer_percent=float(os.getenv("RISK_BUFFER_PERCENT", "2.0")),
            contract_size=float(os.getenv("CONTRACT_SIZE", "100.0")),
            risk_reward=os.getenv("RISK_REWARD", "AUTO").strip(),
            # This interval is for broker REST reconciliation only; live setup
            # evaluation is tick-woken and candle-boundary driven.
            poll_seconds=max(15, int(os.getenv("POLL_SECONDS", "15"))),
            db_path=os.getenv("STATE_DB", "ks_trader_state.sqlite3"),
            log_level=os.getenv("LOG_LEVEL", "INFO").upper(),
            candles_count=int(os.getenv("CANDLES_COUNT", "600")),
        )
        missing = [k for k, v in {
            "EXN_API_KEY": cfg.api_key,
            "EXN_SECRET_KEY": cfg.secret_key,
            "EXN_ACCOUNT_ID": cfg.account_id,
            "EXN_GATEWAY_URL": cfg.gateway_url,
        }.items() if not v]
        if missing:
            raise ValueError("Missing required .env values: " + ", ".join(missing))
        if not re.fullmatch(r"\d{1,20}", cfg.account_id):
            raise ValueError("EXN_ACCOUNT_ID must be the numeric Exness trading account ID.")
        if cfg.account_mode != "demo":
            raise ValueError("This build is demo-only. Set EXN_ACCOUNT_MODE=demo.")
        if cfg.risk_reward not in {"AUTO", "1:1", "1:1.5", "1:2", "1:3", "1:4"}:
            raise ValueError("RISK_REWARD must be AUTO or one of 1:1, 1:1.5, 1:2, 1:3, 1:4.")
        if not (5.0 <= cfg.risk_percent <= 5.0):
            raise ValueError("RISK_PERCENT is the normal risk target and must be 5.0.")
        if not (0.0 <= cfg.risk_buffer_percent <= 2.0):
            raise ValueError("RISK_BUFFER_PERCENT must be between 0.0 and 2.0.")
        if cfg.risk_percent + cfg.risk_buffer_percent > 7.0:
            raise ValueError("Normal risk plus buffer cannot exceed the 7.0% maximum.")
        if not all(math.isfinite(x) for x in (cfg.account_capital, cfg.risk_percent, cfg.risk_buffer_percent, cfg.contract_size)):
            raise ValueError("ACCOUNT_CAPITAL, RISK_PERCENT, RISK_BUFFER_PERCENT and CONTRACT_SIZE must be finite numbers.")
        if cfg.account_capital < 1 or cfg.contract_size < 1:
            raise ValueError("ACCOUNT_CAPITAL and CONTRACT_SIZE must be positive.")
        if not (15 <= cfg.poll_seconds <= 180):
            raise ValueError("POLL_SECONDS must be between 15 and 180 seconds for broker account/order reconciliation.")
        if not (300 <= cfg.candles_count <= 1500):
            raise ValueError("CANDLES_COUNT must be between 300 and 1500.")
        if len(cfg.secret_key) == 128 and re.fullmatch(r"[0-9a-fA-F]{128}", cfg.secret_key):
            pass
        elif "BEGIN PRIVATE KEY" in cfg.secret_key:
            pass
        else:
            raise ValueError("EXN_SECRET_KEY must be the 128-character hex Ed25519 private key or PKCS#8 PEM.")
        return cfg


class ExnessAPI:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.session = requests.Session()
        self.session.headers.update({"User-Agent": f"KS-Trader-Desk/{APP_VERSION}", "Accept": "application/json"})
        self.private_key = self._load_private_key(cfg.secret_key)
        self.access_point: str | None = None
        # Shared REST cooldown: every API path observes the same broker lockout.
        # WebSocket tick ingestion continues independently during this window.
        self._rate_limit_until = 0.0
        self._rate_limit_lock = threading.Lock()
        self._rate_limit_was_active = False

    def set_rate_limit_cooldown(self, seconds: int | float) -> float:
        bounded = max(1.0, min(300.0, float(seconds)))
        with self._rate_limit_lock:
            self._rate_limit_until = max(self._rate_limit_until, time.monotonic() + bounded)
            self._rate_limit_was_active = True
            return max(0.0, self._rate_limit_until - time.monotonic())

    def rate_limit_remaining(self) -> float:
        with self._rate_limit_lock:
            remaining = self._rate_limit_until - time.monotonic()
            if remaining <= 0:
                self._rate_limit_until = 0.0
                return 0.0
            return remaining

    @staticmethod
    def _load_private_key(raw: str) -> Ed25519PrivateKey:
        if "BEGIN PRIVATE KEY" in raw:
            key = load_pem_private_key(raw.encode(), password=None)
            if not isinstance(key, Ed25519PrivateKey):
                raise ValueError("The PEM key is not Ed25519.")
            return key
        key_bytes = bytes.fromhex(raw)
        if len(key_bytes) != 64:
            raise ValueError("Exness-generated Ed25519 key must decode to 64 bytes.")
        # Exness-generated 128-hex format = 32-byte seed + 32-byte public key.
        return Ed25519PrivateKey.from_private_bytes(key_bytes[:32])

    def _headers(self, method: str, path_query: str, body: bytes = b"", idem: str = "") -> dict[str, str]:
        timestamp = int(time.time() * 1000)
        body_hash = b64url(hashlib.sha256(body).digest())
        payload = {
            "api_key": self.cfg.api_key,
            "idempotency_key": idem,
            "timestamp": timestamp,
            "sign_version": 1,
            "method": method.upper(),
            "path": path_query,
            "body_hash": body_hash,
        }
        # Exness signs the compact JSON bytes, then base64url-encodes those same bytes.
        payload_bytes = json.dumps(payload, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        signature = self.private_key.sign(payload_bytes)
        return {
            "EXN-API-KEY": self.cfg.api_key,
            "EXN-IDEMPOTENCY-KEY": idem,
            "EXN-TIMESTAMP": str(timestamp),
            "EXN-SIGN-VERSION": "1",
            "EXN-DATA": b64url(payload_bytes),
            "EXN-SIGN": b64url(signature),
        }

    def request(self, method: str, path_query: str, body_obj: dict | None = None, *, gateway: bool = False, idem: str | None = None) -> dict:
        method = method.upper()
        cooldown_remaining = self.rate_limit_remaining()
        if cooldown_remaining > 0:
            # Do not send any REST request while the broker's 429 cooldown is active.
            raise RateLimitCooldownError(cooldown_remaining)
        body = b"" if body_obj is None else json.dumps(body_obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        # GET requests are safe to retry. Mutating requests are deliberately
        # sent once only: a timeout may occur after the broker accepted the order.
        idempotency = (idem or "") if method == "GET" else (idem or uuid.uuid4().hex)
        base = self.cfg.gateway_url if gateway else (self.access_point or "")
        if not base:
            raise RuntimeError("Exness account Access Point has not been resolved.")

        max_attempts = 4 if method == "GET" else 1
        last_error: Exception | None = None
        access_point_refreshed = False
        for attempt in range(max_attempts):
            headers = self._headers(method, path_query, body, idempotency)
            if body_obj is not None:
                headers["Content-Type"] = "application/json"
            try:
                response = self.session.request(
                    method, base + path_query,
                    data=body if body_obj is not None else None,
                    headers=headers, timeout=(5, 45), allow_redirects=False,
                )
            except requests.RequestException as exc:
                last_error = exc
                if method != "GET":
                    raise UncertainPostError(
                        "Mutating request transport failed; broker acceptance is unknown. "
                        "Do not retry blindly. Reconcile the account snapshot first."
                    ) from exc
                if attempt + 1 >= max_attempts:
                    raise
                delay = min(2 ** attempt, 8)
                logging.warning("Connection to Exness was interrupted. Retrying in %d second(s) (%d of %d).", delay, attempt + 1, max_attempts)
                logging.debug("GET transport error details: %r", exc)
                time.sleep(delay)
                continue

            try:
                data = response.json() if response.content else {}
            except ValueError:
                data = {"raw": response.text[:1000]}

            if response.ok:
                return data

            # A transient 401 was seen after a dropped connection in the log.
            # Refresh the account Access Point once for GETs only; never loop
            # or retry an order-submission POST.
            if method == "GET" and not gateway and response.status_code == 401 and not access_point_refreshed and attempt + 1 < max_attempts:
                logging.warning("Exness rejected a market-data read with HTTP 401. Refreshing the Access Point once before retrying.")
                logging.debug("HTTP 401 response details: %r", data)
                access_point_refreshed = True
                base = self.discover_access_point()
                continue

            # Exness AUTH_RATE_LIMIT includes an absolute retry_after timestamp.
            # REQUEST_RATE_LIMIT (code 3015) explicitly says not to retry
            # immediately, so let the caller pause rather than hammering API.
            retryable_get = method == "GET" and response.status_code in {429, 500, 502, 503, 504}
            rate_code = str(data.get("error_message", "")).upper() if isinstance(data, dict) else ""
            if response.status_code == 429:
                # Apply a process-wide cooldown for GET and mutating requests alike.
                # Honour Exness retry_after first; Retry-After header is fallback.
                delay = api_retry_after_seconds(data)
                header_retry = response.headers.get("Retry-After")
                if header_retry:
                    try:
                        delay = max(delay, min(300, int(float(header_retry))))
                    except (TypeError, ValueError):
                        pass
                self.set_rate_limit_cooldown(delay)
                raise APIHTTPError(response.status_code, data)
            if retryable_get and attempt + 1 < max_attempts:
                if response.status_code == 429 and rate_code == "REQUEST_RATE_LIMIT":
                    raise APIHTTPError(response.status_code, data)
                if response.status_code == 429 and rate_code == "AUTH_RATE_LIMIT":
                    delay = api_retry_after_seconds(data)
                else:
                    delay = min(2 ** attempt, 8)
                logging.warning("Exness is temporarily unavailable (HTTP %d). Retrying in %d second(s).", response.status_code, delay)
                logging.debug("Retryable GET response details: %r", data)
                time.sleep(delay)
                continue
            if method != "GET" and response.status_code >= 500:
                raise UncertainPostError(
                    f"Mutating request returned HTTP {response.status_code}; acceptance may be unknown. "
                    "Do not retry blindly. Reconcile the account snapshot."
                )
            raise APIHTTPError(response.status_code, data)

        if last_error:
            raise last_error
        raise RuntimeError("Exness request failed without a response.")

    def discover_access_point(self) -> str:
        path = f"/v1/trading/access-point?{urlencode({'account_id': self.cfg.account_id})}"
        result = self.request("GET", path, gateway=True)
        host = result.get("access_point")
        if not isinstance(host, str) or not host:
            raise RuntimeError(f"Access-point discovery response missing access_point: {result}")
        if not host.startswith("https://"):
            host = "https://" + host.lstrip("/")
        parsed = urlparse(host)
        if parsed.scheme != "https" or not parsed.netloc:
            raise RuntimeError("Exness returned an invalid Access Point host.")
        self.access_point = host.rstrip("/")
        logging.info("Connected to Exness trading server.")
        return self.access_point

    def get(self, path_query: str) -> dict:
        return self.request("GET", path_query)

    def post(self, path: str, body: dict, idem: str | None = None) -> dict:
        return self.request("POST", path, body, idem=idem or uuid.uuid4().hex)

    def snapshot(self) -> dict:
        return self.get(f"/v1/trading/accounts/{self.cfg.account_id}/snapshot")

    def orders_history(self, start_time: str, instrument: str) -> dict:
        """Fetch the first page of historical orders from the lock start time onward."""
        params = {
            "from": start_time,
            "to": utc_iso(datetime.now(UTC)),
            "limit": 200,
            "instrument": instrument,
        }
        path = f"/v1/history/accounts/{self.cfg.account_id}/orders?{urlencode(params)}"
        return self.get(path)

    def orders_history_all_since(self, start: datetime, end: datetime, instrument: str) -> list[dict]:
        """Fetch every historical order since start, following Exness cursors."""
        params = {
            "from": utc_iso(start),
            "to": utc_iso(end),
            "limit": 200,
            "instrument": instrument,
        }
        path = f"/v1/history/accounts/{self.cfg.account_id}/orders?{urlencode(params)}"
        all_items: list[dict] = []
        seen_cursors: set[str] = set()
        for _ in range(100):
            page = self.get(path)
            items = page.get("items", []) or []
            if not isinstance(items, list):
                raise RuntimeError("Exness orders history returned an invalid items collection.")
            all_items.extend(row for row in items if isinstance(row, dict))
            cursor = page.get("next_cursor")
            if not cursor:
                if page.get("has_more"):
                    raise RuntimeError("Exness indicates more order-history pages but did not provide next_cursor.")
                return all_items
            cursor = str(cursor)
            if cursor in seen_cursors:
                raise RuntimeError("Exness orders-history pagination repeated a cursor; refusing incomplete trade-lock reconciliation.")
            seen_cursors.add(cursor)
            path = f"/v1/history/accounts/{self.cfg.account_id}/orders?{urlencode({'cursor': cursor, 'limit': 200})}"
        raise RuntimeError("Exness orders history exceeded 100 pages; refusing incomplete trade-lock reconciliation.")

    def deals_history(self, start_time: str, instrument: str) -> dict:
        """Fetch deal history to link a filled order to its position."""
        params = {
            "from": start_time,
            "to": utc_iso(datetime.now(UTC)),
            "limit": 200,
            "instrument": instrument,
        }
        path = f"/v1/history/accounts/{self.cfg.account_id}/deals?{urlencode(params)}"
        return self.get(path)

    def deals_history_all_since(self, start: datetime, end: datetime) -> list[dict]:
        """Fetch every account deal since start, following the opaque cursor."""
        params = {"from": utc_iso(start), "to": utc_iso(end), "limit": 200}
        path = f"/v1/history/accounts/{self.cfg.account_id}/deals?{urlencode(params)}"
        all_items: list[dict] = []
        seen_cursors: set[str] = set()
        for _ in range(100):
            page = self.get(path)
            items = page.get("items", []) or []
            if not isinstance(items, list):
                raise RuntimeError("Exness deals history returned an invalid items collection.")
            all_items.extend(row for row in items if isinstance(row, dict))
            cursor = page.get("next_cursor")
            if not cursor:
                if page.get("has_more"):
                    raise RuntimeError("Exness indicates more deal-history pages but did not provide next_cursor.")
                return all_items
            cursor = str(cursor)
            if cursor in seen_cursors:
                raise RuntimeError("Exness deals-history pagination repeated a cursor; refusing an incomplete balance calculation.")
            seen_cursors.add(cursor)
            path = f"/v1/history/accounts/{self.cfg.account_id}/deals?{urlencode({'cursor': cursor, 'limit': 200})}"
        raise RuntimeError("Exness deals history exceeded 100 pages; refusing an incomplete daily balance calculation.")

    def instrument_conditions(self) -> dict:
        return self.get(f"/v1/configuration/accounts/{self.cfg.account_id}/instruments/{self.cfg.instrument}/conditions")

    def api_limits(self) -> dict:
        """Read account-specific REST/WebSocket limits; never hardcode broker quotas."""
        return self.get(f"/v1/configuration/accounts/{self.cfg.account_id}/limits")

    def candles(self, timeframe: str, count: int) -> pd.DataFrame:
        # Request a recent UTC time window. Exness candles are returned ascending.
        mins = count * {"M1": 1, "M3": 3, "M5": 5}.get(timeframe, 1)
        start = datetime.now(UTC) - timedelta(minutes=mins + 5)
        end = datetime.now(UTC)
        params = {
            "instrument": self.cfg.instrument,
            "timeframe": timeframe,
            "price_type": "both",
            "from": utc_iso(start),
            "to": utc_iso(end),
        }
        path = f"/v1/market-data/accounts/{self.cfg.account_id}/candles?{urlencode(params)}"
        data = self.get(path)
        rows = data.get("candles", [])
        if not rows:
            logging.debug("No %s candles are currently available for %s; waiting internally for the next live update.", timeframe, self.cfg.instrument)
            return pd.DataFrame()
        # The Trading API's both-price response nests OHLC under bid/ask. Keep
        # bid OHLC in the legacy columns (signal parity) and retain ask OHLC for
        # correct SELL-position exit-side analysis. Fall back to flat bid rows
        # for older response variants.
        normalized = []
        for row in rows:
            item = dict(row)
            bid = row.get("bid") if isinstance(row.get("bid"), dict) else None
            ask = row.get("ask") if isinstance(row.get("ask"), dict) else None
            if bid:
                for col in ("open", "high", "low", "close"):
                    item[col] = bid.get(col)
            if ask:
                for col in ("open", "high", "low", "close"):
                    item[f"ask_{col}"] = ask.get(col)
            normalized.append(item)
        frame = pd.DataFrame(normalized)
        frame["time"] = pd.to_datetime(frame["time"], utc=True)
        for col in ["open", "high", "low", "close", "volume", "ask_open", "ask_high", "ask_low", "ask_close"]:
            if col in frame.columns:
                frame[col] = pd.to_numeric(frame[col], errors="coerce")
        frame = frame.dropna(subset=["time", "open", "high", "low", "close", "volume"])
        frame = frame.sort_values("time").drop_duplicates("time").reset_index(drop=True)
        now = pd.Timestamp.now(tz="UTC")
        duration = pd.Timedelta(minutes=1 if timeframe == "M1" else 3)
        # Never evaluate a still-forming candle.
        frame = frame[frame["time"] + duration <= now].reset_index(drop=True)
        return frame

    def place_entry_pending(self, signal: dict, volume_text: str, idem: str, order_type: str) -> dict:
        order_type = str(order_type or "").strip().lower()
        if order_type not in {"limit", "stop"}:
            raise ValueError(f"Unsupported pending order type {order_type!r}; market orders are never used.")
        body = {
            "instrument": self.cfg.instrument,
            "side": signal["side"],
            "type": order_type,
            "volume": volume_text,
            "price": signal["entry_text"],
            "stop_loss_price": signal["sl_text"],
            "take_profit_price": signal["tp_text"],
            "comment": str(signal.get("comment", "KS Trader Desk Entry 1")),
        }
        return self.post(f"/v1/trading/accounts/{self.cfg.account_id}/orders", body, idem=idem)

    def cancel_pending_order(self, order_id: str, idem: str) -> dict:
        """Request cancellation of a pending order; Exness finalizes asynchronously."""
        path = f"/v1/trading/accounts/{self.cfg.account_id}/orders/{order_id}"
        return self.request("DELETE", path, idem=idem)

    def modify_pending_order(self, order_id: str, price_text: str | None = None,
                             idem: str = "", take_profit_text: str | None = None) -> dict:
        """Modify the price and/or TP of a still-pending Exness order."""
        body = {}
        if price_text not in (None, ""):
            body["price"] = str(price_text)
        if take_profit_text not in (None, ""):
            body["take_profit_price"] = str(take_profit_text)
        if not body:
            raise ValueError("Pending-order PATCH requires a price or take-profit value.")
        path = f"/v1/trading/accounts/{self.cfg.account_id}/orders/{order_id}"
        return self.request("PATCH", path, body, idem=idem)

    def modify_active_order(self, order_id: str, stop_loss_text: str | None,
                            idem: str, take_profit_text: str | None = None) -> dict:
        """Modify SL and/or TP on the active SLTP order linked to a position."""
        body = {}
        if stop_loss_text not in (None, ""):
            body["stop_loss_price"] = str(stop_loss_text)
        if take_profit_text not in (None, ""):
            body["take_profit_price"] = str(take_profit_text)
        if not body:
            raise ValueError("Active SLTP PATCH requires a stop-loss or take-profit value.")
        path = f"/v1/trading/accounts/{self.cfg.account_id}/orders/{order_id}"
        return self.request("PATCH", path, body, idem=idem)

    def close_position(self, position_id: str, idem: str) -> dict:
        """Request a full close of one open Exness position."""
        if not position_id:
            raise ValueError("A broker position ID is required for a close request.")
        path = f"/v1/trading/accounts/{self.cfg.account_id}/positions/{position_id}"
        return self.request("DELETE", path, idem=idem)

    def operation_status(self, operation_id: str) -> dict:
        return self.get(f"/v1/trading/accounts/{self.cfg.account_id}/operations/{operation_id}")




class LiveTickMonitor:
    """Collect raw Exness ticks and expose a fresh Bid/Ask quote for preflight checks."""
    def __init__(self, api: ExnessAPI, instrument: str, stale_after: int = 10):
        self.api = api
        self.instrument = instrument
        self.stale_after = stale_after
        self._lock = threading.Lock()
        self._latest: dict | None = None
        # Wake the strategy loop immediately when a fresh live quote arrives.
        self._tick_event = threading.Event()
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None
        self._app = None
        self.diagnostic_path = Path("exness_tick_diagnostics.json")
        # Diagnostics are best-effort only: a locked JSON file must never
        # interrupt live quote ingestion or the trading safety checks.
        self._diagnostic_lock = threading.Lock()
        self._last_diagnostic_write = 0.0
        self._diagnostic_warning_logged = False

    @staticmethod
    def _find_quote(obj: Any) -> dict | None:
        if isinstance(obj, dict):
            lower = {str(k).lower(): v for k, v in obj.items()}
            bid, ask = lower.get("bid"), lower.get("ask")
            if bid is not None and ask is not None:
                try:
                    b, a = dec(bid), dec(ask)
                    if b > 0 and a > 0 and b <= a:
                        return {"bid": str(b), "ask": str(a), "raw_object": obj}
                except Exception:
                    pass
            for value in obj.values():
                found = LiveTickMonitor._find_quote(value)
                if found:
                    return found
        elif isinstance(obj, list):
            for value in obj:
                found = LiveTickMonitor._find_quote(value)
                if found:
                    return found
        return None

    def _save_diagnostic(self, payload: Any, quote: dict | None) -> None:
        """Best-effort, throttled diagnostic write; never raise into WebSocket callback.

        Windows can deny os.replace when the destination is open in an editor,
        scanner, sync client, or another bot process. Use a unique temp filename,
        serialize writes within this monitor, and treat diagnostics as optional.
        """
        now = time.monotonic()
        if now - self._last_diagnostic_write < 1.0:
            return
        if not self._diagnostic_lock.acquire(blocking=False):
            return
        tmp = None
        try:
            now = time.monotonic()
            if now - self._last_diagnostic_write < 1.0:
                return
            record = {
                "received_at_utc": utc_iso(datetime.now(UTC)),
                "instrument_configured": self.instrument,
                "parsed_quote": quote,
                "raw_message": payload,
            }
            tmp = self.diagnostic_path.with_name(
                f"{self.diagnostic_path.stem}.{os.getpid()}.{threading.get_ident()}.{uuid.uuid4().hex[:8]}.tmp"
            )
            tmp.write_text(json.dumps(record, indent=2, default=str), encoding="utf-8")
            last_error = None
            for attempt in range(3):
                try:
                    os.replace(str(tmp), str(self.diagnostic_path))
                    last_error = None
                    break
                except PermissionError as exc:
                    last_error = exc
                    if attempt < 2:
                        time.sleep(0.05 * (attempt + 1))
            if last_error is not None:
                raise last_error
            self._last_diagnostic_write = time.monotonic()
            self._diagnostic_warning_logged = False
        except OSError as exc:
            # Do not let a diagnostics-file permission/locking problem stop ticks.
            if not self._diagnostic_warning_logged:
                logging.warning(
                    "Tick diagnostics file is locked/unavailable (%s); continuing live tick processing. "
                    "Close the JSON file in other apps and ensure only one bot instance writes it.", exc
                )
                self._diagnostic_warning_logged = True
        except Exception as exc:
            if not self._diagnostic_warning_logged:
                logging.warning("Could not save optional tick diagnostics (%s); live tick processing continues.", exc)
                self._diagnostic_warning_logged = True
        finally:
            if tmp is not None:
                try:
                    tmp.unlink(missing_ok=True)
                except OSError:
                    pass
            self._diagnostic_lock.release()

    def start(self) -> None:
        if websocket is None:
            logging.warning(
                "LIVE TICK VALIDATION UNAVAILABLE: install websocket-client using "
                "`python -m pip install websocket-client`. New order submission will fail closed."
            )
            return
        if not self.api.access_point:
            raise RuntimeError("Cannot start Exness ticks stream before Access Point discovery.")
        path = f"/v1/server-events/accounts/{self.api.cfg.account_id}/ws/ticks"
        signed_headers = self.api._headers("GET", path, b"", "")
        header_lines = [f"{key}: {value}" for key, value in signed_headers.items()]
        ws_url = self.api.access_point.replace("https://", "wss://", 1) + path

        def on_open(app):
            app.send(json.dumps({
                "id": f"ks-ticks-{uuid.uuid4().hex[:12]}",
                "subscribe": {"event": "ticks", "instruments": [self.instrument]},
            }, separators=(",", ":")))
            logging.info("Subscribed to Exness live ticks for %s.", self.instrument)

        def on_message(app, message):
            try:
                payload = json.loads(message)
            except Exception:
                payload = {"raw_text": str(message)[:10000]}
            quote = self._find_quote(payload)
            # Publish the live quote FIRST. Optional disk diagnostics must never
            # prevent the trading loop from seeing a valid Bid/Ask tick.
            if quote:
                with self._lock:
                    self._latest = {
                        "bid": quote["bid"], "ask": quote["ask"],
                        "received_monotonic": time.monotonic(),
                        "received_at_utc": utc_iso(datetime.now(UTC)),
                        "raw_message": payload,
                    }
                    self._tick_event.set()
                logging.debug("Exness tick captured: %s Bid=%s Ask=%s", self.instrument, quote["bid"], quote["ask"])
            else:
                logging.debug("Raw Exness tick captured; Bid/Ask not recognized yet. See %s.", self.diagnostic_path)
            self._save_diagnostic(payload, quote)

        def on_error(app, error):
            logging.warning("Exness ticks WebSocket error: %s", error)

        def on_close(app, status_code, message):
            logging.warning("Exness ticks WebSocket closed (%s): %s", status_code, message)

        def runner():
            while not self._stop.is_set():
                self._app = websocket.WebSocketApp(
                    ws_url, header=header_lines,
                    on_open=on_open, on_message=on_message,
                    on_error=on_error, on_close=on_close,
                )
                try:
                    self._app.run_forever(ping_interval=20, ping_timeout=10)
                except Exception:
                    logging.debug("Ticks WebSocket reconnect details:", exc_info=True)
                if not self._stop.is_set():
                    self._stop.wait(3)

        self._thread = threading.Thread(target=runner, name="exness-live-ticks", daemon=True)
        self._thread.start()

    def wait_for_tick(self, timeout: float | None = None) -> bool:
        """Block until a live quote arrives; return False on timeout."""
        with self._lock:
            if self._tick_event.is_set():
                self._tick_event.clear()
                return True
        self._tick_event.wait(timeout)
        with self._lock:
            signaled = self._tick_event.is_set()
            if signaled:
                self._tick_event.clear()
            return signaled

    def latest(self) -> dict | None:
        with self._lock:
            tick = dict(self._latest) if self._latest else None
        if not tick:
            return None
        age = time.monotonic() - float(tick["received_monotonic"])
        if age > self.stale_after:
            return None
        tick["age_seconds"] = round(age, 3)
        return tick

    def stop(self) -> None:
        self._stop.set()
        if self._app:
            try:
                self._app.close()
            except Exception:
                pass


def select_adaptive_pending_order_type(side: str, entry_text: str, tick: dict) -> str | None:
    """Choose STOP/LIMIT from the saved entry price and the live executable quote.

    Return None while the entry lies inside the spread (or exactly on a quote);
    in that case the caller must wait for a fresh quote rather than changing the
    saved strategy price or submitting an invalid pending order.
    """
    side = str(side).lower()
    bid, ask, entry = dec(tick["bid"]), dec(tick["ask"]), dec(entry_text)
    if side == "buy":
        if entry > ask:
            return "stop"
        if entry < bid:
            return "limit"
        return None
    if side == "sell":
        if entry < bid:
            return "stop"
        if entry > ask:
            return "limit"
        return None
    raise ValueError(f"Unsupported trade side: {side}.")


def validate_pending_price_against_quote(side: str, order_type: str, entry_text: str, tick: dict) -> None:
    """Validate pending entry placement against the current executable quote side."""
    side, order_type = str(side).lower(), str(order_type).lower()
    bid, ask, entry = dec(tick["bid"]), dec(tick["ask"]), dec(entry_text)
    if side == "buy" and order_type == "stop" and not entry > ask:
        raise ValueError(f"BUY STOP entry {entry} must be above current Ask {ask}.")
    if side == "sell" and order_type == "stop" and not entry < bid:
        raise ValueError(f"SELL STOP entry {entry} must be below current Bid {bid}.")
    if side == "buy" and order_type == "limit" and not entry < ask:
        raise ValueError(f"BUY LIMIT entry {entry} must be below current Ask {ask}.")
    if side == "sell" and order_type == "limit" and not entry > bid:
        raise ValueError(f"SELL LIMIT entry {entry} must be above current Bid {bid}.")
    if side not in {"buy", "sell"} or order_type not in {"limit", "stop"}:
        raise ValueError(f"Unsupported pending order combination: {side}/{order_type}.")


class StateStore:
    def __init__(self, path: str):
        self.conn = sqlite3.connect(path)
        self.conn.execute("""CREATE TABLE IF NOT EXISTS state (
            key TEXT PRIMARY KEY, value TEXT NOT NULL
        )""")
        # Append-only diagnostic history: rejected leg details survive when
        # the current trade_group state is replaced by a later signal.
        self.conn.execute("""CREATE TABLE IF NOT EXISTS group_leg_events (
            event_id INTEGER PRIMARY KEY AUTOINCREMENT,
            group_id TEXT NOT NULL,
            leg_name TEXT NOT NULL,
            event_type TEXT NOT NULL,
            created_at TEXT NOT NULL,
            payload_json TEXT NOT NULL
        )""")
        self.conn.commit()

    def append_group_leg_event(self, group_id: str, leg_name: str,
                               event_type: str, payload: dict) -> None:
        self.conn.execute(
            "INSERT INTO group_leg_events(group_id,leg_name,event_type,created_at,payload_json) "
            "VALUES(?,?,?,?,?)",
            (str(group_id), str(leg_name), str(event_type),
             utc_iso(datetime.now(UTC)),
             json.dumps(payload, separators=(",", ":"), default=str)),
        )
        self.conn.commit()

    def get(self, key: str, default: str = "") -> str:
        row = self.conn.execute("SELECT value FROM state WHERE key=?", (key,)).fetchone()
        return row[0] if row else default

    def set(self, key: str, value: Any) -> None:
        self.conn.execute("INSERT INTO state(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value", (key, str(value)))
        self.conn.commit()

    def get_json(self, key: str, default: Any = None) -> Any:
        raw = self.get(key, "")
        if not raw:
            return default
        return json.loads(raw)

    def set_json(self, key: str, value: Any) -> None:
        self.set(key, json.dumps(value, separators=(",", ":"), default=str))


def _deal_balance_impact(item: dict) -> Decimal:
    """Return the signed balance impact of one Exness deal.

    Exness exposes realized P/L or balance movement in profit.amount and
    the separately signed commission in commission. Adding both preserves
    the broker's debit/credit signs. Opening deals normally contribute only
    commission; their unrealized P/L does not change balance.
    """
    deal = item.get("deal", item)
    deal_type = str(deal.get("type", "")).lower()
    profit = deal.get("profit")
    if isinstance(profit, dict) and profit.get("amount") is not None:
        impact = dec(profit["amount"])
    elif deal_type == "open":
        impact = Decimal("0")
    else:
        raise RuntimeError(
            f"Exness deal {deal.get('deal_id', 'unknown')} type={deal_type!r} "
            "has no profit.amount; cannot reconstruct the midnight balance safely."
        )
    if deal.get("commission") not in (None, ""):
        impact += dec(deal["commission"])
    if deal.get("swap") not in (None, ""):
        impact += dec(deal["swap"])
    return impact


def get_daily_opening_balance(store: StateStore, api: ExnessAPI, snapshot: dict) -> tuple[Decimal, str]:
    """Reconstruct and freeze the actual 00:00 IST balance for the current day.

    Current Exness balance minus every signed account-deal movement since
    midnight gives the opening balance. It is cached per IST date. If the
    history is incomplete or ambiguous, trading fails closed rather than
    silently using a later balance.
    """
    now_ist = datetime.now(IST)
    day_key = now_ist.date().isoformat()
    cached = store.get_json("daily_opening_balance", {}) or {}
    if cached.get("date_ist") == day_key and cached.get("opening_balance") is not None:
        return dec(cached["opening_balance"]), day_key

    account_state = snapshot.get("account_state") or {}
    raw_balance = account_state.get("balance")
    if raw_balance in (None, ""):
        raise RuntimeError("Exness snapshot has no account_state.balance; daily risk capital cannot be established.")
    current_balance = dec(raw_balance)

    midnight_ist = datetime.combine(now_ist.date(), datetime.min.time(), tzinfo=IST)
    midnight_utc = midnight_ist.astimezone(UTC)
    now_utc = datetime.now(UTC)
    items = api.deals_history_all_since(midnight_utc, now_utc)
    _RECENT_EXNESS_DEALS_CACHE.update({
        "day_key": day_key,
        "fetched_monotonic": time.monotonic(),
        "items": items,
    })

    net_change = Decimal("0")
    seen_deal_ids: set[str] = set()
    for item in items:
        deal = item.get("deal", item)
        event_time = item.get("event_time") or deal.get("create_time")
        if not event_time:
            raise RuntimeError("An Exness deal-history record has no event_time/create_time; cannot reconstruct 00:00 IST balance.")
        parsed_time = pd.Timestamp(event_time)
        if parsed_time.tzinfo is None:
            raise RuntimeError("An Exness deal-history timestamp has no timezone; cannot reconstruct 00:00 IST balance.")
        if parsed_time.to_pydatetime().astimezone(UTC) < midnight_utc:
            continue

        deal_id = str(deal.get("deal_id") or "")
        if deal_id and deal_id in seen_deal_ids:
            continue
        if deal_id:
            seen_deal_ids.add(deal_id)
        net_change += _deal_balance_impact(item)

    opening_balance = current_balance - net_change
    if not opening_balance.is_finite() or opening_balance <= 0:
        raise RuntimeError(f"Reconstructed 00:00 IST opening balance is invalid: {opening_balance}.")
    record = {
        "date_ist": day_key,
        "midnight_ist": midnight_ist.isoformat(),
        "computed_at": utc_iso(now_utc),
        "opening_balance": str(opening_balance),
        "current_balance_at_calculation": str(current_balance),
        "net_deals_balance_change": str(net_change),
        "deal_count": len(seen_deal_ids) if seen_deal_ids else len(items),
        "history_complete": True,
        "source": "Exness current snapshot balance minus all signed account deals since 00:00 IST",
    }
    store.set_json("daily_opening_balance", record)

    risk_percent = dec(os.getenv("RISK_PERCENT", "5.0"))
    risk_buffer_percent = dec(os.getenv("RISK_BUFFER_PERCENT", "2.0"))
    total_risk_percent = min(Decimal("7.0"), risk_percent + risk_buffer_percent)
    risk_budget = opening_balance * total_risk_percent / Decimal("100")
    logging.info(
        "Today's starting balance is $%.2f. Risk target %.2f%% + buffer %.2f%% = %.2f%% maximum ($%.2f).",
        float(opening_balance), float(risk_percent), float(risk_buffer_percent),
        float(total_risk_percent), float(risk_budget),
    )
    return opening_balance, day_key



def get_daily_risk_state(store: StateStore, opening_balance: Decimal, day_key: str) -> dict:
    """Load/create the IST day's persistent closed-P/L risk mode."""
    state = store.get_json("daily_risk_state", {}) or {}
    if state.get("date_ist") != day_key:
        state = {
            "date_ist": day_key,
            "opening_balance": str(opening_balance),
            "realized_closed_pnl": "0",
            "reduced_mode": False,
            "processed_position_ids": [],
            "updated_at": utc_iso(datetime.now(UTC)),
        }
        store.set_json("daily_risk_state", state)
        logging.info(
            "Daily capital protection initialized: opening balance $%.2f; 30%% loss threshold $%.2f; NORMAL risk 5%% + 2%%.",
            float(opening_balance), float(opening_balance * Decimal("0.30")),
        )
        return state
    state.setdefault("realized_closed_pnl", "0")
    state.setdefault("reduced_mode", False)
    state.setdefault("processed_position_ids", [])
    return state


def record_daily_closed_trade(
    store: StateStore,
    opening_balance: Decimal,
    day_key: str,
    position_id: str,
    realized_pnl: Decimal,
    exit_reason: str,
) -> dict:
    """Apply one broker-confirmed SL/TP close once; supports repeated mode changes.

    Match the Indie capital-protection rule: only filled active trades closed by
    SL/TP (including a trailing stop reported as SL) affect this daily ledger.
    Manual/external exits and unfilled pending-order outcomes are excluded.
    """
    if str(exit_reason or "").upper() not in {"SL", "TP"}:
        return get_daily_risk_state(store, opening_balance, day_key)
    state = get_daily_risk_state(store, opening_balance, day_key)
    pid = str(position_id or "")
    if not pid:
        raise RuntimeError("Cannot update daily risk without a confirmed position ID.")
    processed = set(str(x) for x in state.get("processed_position_ids", []))
    if pid in processed:
        return state

    new_pnl = dec(state.get("realized_closed_pnl", "0")) + realized_pnl
    threshold = dec(state["opening_balance"]) * Decimal("0.30")
    was_reduced = bool(state.get("reduced_mode", False))
    if new_pnl <= -threshold:
        reduced = True
    elif new_pnl >= Decimal("0"):
        reduced = False
    else:
        reduced = was_reduced

    processed.add(pid)
    state.update({
        "realized_closed_pnl": str(new_pnl),
        "reduced_mode": reduced,
        "processed_position_ids": sorted(processed),
        "updated_at": utc_iso(datetime.now(UTC)),
        "last_closed_position_id": pid,
        "last_exit_reason": exit_reason,
        "last_trade_realized_pnl": str(realized_pnl),
    })
    store.set_json("daily_risk_state", state)

    if reduced and not was_reduced:
        logging.warning(
            "CAPITAL PROTECTION ACTIVATED: Daily closed P/L $%.2f reached the 30%% loss threshold (-$%.2f). New trades use 3%% + 1%% risk.",
            float(new_pnl), float(threshold),
        )
    elif was_reduced and not reduced:
        logging.info(
            "CAPITAL PROTECTION CLEARED: Daily closed P/L recovered to $%.2f. New trades return to 5%% + 2%% risk.",
            float(new_pnl),
        )
    else:
        logging.info(
            "Daily closed P/L: $%.2f | Risk mode: %s",
            float(new_pnl), "REDUCED 3% + 1%" if reduced else "NORMAL 5% + 2%",
        )
    return state


def daily_risk_parameters(cfg: Config, opening_balance: Decimal, state: dict) -> tuple[float, float, Decimal]:
    """Return current target, buffer and cash budget for the next new entry."""
    if bool(state.get("reduced_mode", False)):
        target, buffer = 3.0, 1.0
    else:
        target, buffer = cfg.risk_percent, cfg.risk_buffer_percent
    total = min(Decimal("7.0"), dec(target) + dec(buffer))
    return target, buffer, opening_balance * total / Decimal("100")


def reconcile_daily_account_pnl_from_exness(
    store: StateStore, api: ExnessAPI, opening_balance: Decimal, day_key: str, snapshot: dict
) -> dict:
    """Rebuild today's account-wide realized trading P/L from Exness deal history.

    Exness is authoritative; bot group records are not used for this ledger.
    All account instruments and externally/manual closed positions are included.
    Capital protection uses net broker-confirmed closed P/L, not estimated
    inactive orders. Account floating P/L is shown separately from realized P/L.
    """
    day = datetime.fromisoformat(day_key).date()
    midnight_ist = datetime.combine(day, datetime.min.time(), tzinfo=IST)
    midnight_utc = midnight_ist.astimezone(UTC)
    request_started_utc = datetime.now(UTC)
    cached_history = _RECENT_EXNESS_DEALS_CACHE
    if (
        cached_history.get("day_key") == day_key
        and time.monotonic() - float(cached_history.get("fetched_monotonic", 0)) <= 90
    ):
        raw_items = cached_history.get("items", [])
    else:
        raw_items = api.deals_history_all_since(midnight_utc, request_started_utc)
        _RECENT_EXNESS_DEALS_CACHE.update({
            "day_key": day_key,
            "fetched_monotonic": time.monotonic(),
            "items": raw_items,
        })
    # Use current time as the upper bound so a just-recorded deal isn't
    # discarded as a few milliseconds "in the future".
    now_utc = datetime.now(UTC)

    # Preserve one copy of each deal; Exness pages may overlap at cursor edges.
    unique: dict[str, tuple[dict, datetime]] = {}
    anonymous: list[tuple[dict, datetime]] = []
    for item in raw_items:
        deal = item.get("deal", item) if isinstance(item, dict) else {}
        if not isinstance(deal, dict):
            continue
        event_time = item.get("event_time") or deal.get("create_time")
        parsed = _history_time(event_time)
        if parsed is None:
            raise RuntimeError("Exness daily deal history contains a missing/invalid timestamp; daily P/L and risk mode cannot be safely reconciled.")
        if parsed < midnight_utc or parsed > now_utc:
            continue
        deal_id = str(deal.get("deal_id") or deal.get("id") or "")
        row = (deal, parsed)
        if deal_id:
            unique.setdefault(deal_id, row)
        else:
            anonymous.append(row)
    rows = list(unique.values()) + anonymous

    # Only broker deal types that actually close/partially close a position
    # contribute to realized trading P/L. Deposits, credits and pending-order
    # estimates are excluded. Include same-day open/commission/swap deals for
    # those positions so the realized result is net of costs.
    close_types = {"close", "close_by", "closeby", "closed", "partial_close"}
    closed_position_ids: set[str] = set()
    for deal, _ in rows:
        if str(deal.get("type", "")).strip().lower() in close_types:
            pid = str(deal.get("position_id") or "")
            if pid:
                closed_position_ids.add(pid)

    realized = Decimal("0")
    position_totals: dict[str, Decimal] = {}
    unlinked_close_total = Decimal("0")
    for deal, _ in rows:
        pid = str(deal.get("position_id") or "")
        if pid and pid in closed_position_ids:
            position_totals[pid] = position_totals.get(pid, Decimal("0")) + _deal_money_amount(deal.get("profit")) + _deal_money_amount(deal.get("commission")) + _deal_money_amount(deal.get("swap"))
        elif not pid and str(deal.get("type", "")).strip().lower() in close_types:
            unlinked_close_total += _deal_money_amount(deal.get("profit")) + _deal_money_amount(deal.get("commission")) + _deal_money_amount(deal.get("swap"))
    realized = sum(position_totals.values(), Decimal("0")) + unlinked_close_total

    account_state = snapshot.get("account_state") or {}
    balance_raw = account_state.get("balance")
    equity_raw = account_state.get("equity")
    floating = None
    if balance_raw not in (None, "") and equity_raw not in (None, ""):
        # Account money values may be scalar strings or {amount: ...} objects.
        floating = _deal_money_amount(equity_raw) - _deal_money_amount(balance_raw)
    total_account_pnl = realized + floating if floating is not None else None

    state = get_daily_risk_state(store, opening_balance, day_key)
    threshold = dec(state.get("opening_balance", opening_balance)) * Decimal("0.30")
    was_reduced = bool(state.get("reduced_mode", False))
    if realized <= -threshold:
        reduced = True
    elif realized >= Decimal("0"):
        # Capital protection is restored only when actual net closed trading
        # P/L has recovered to the daily opening balance (>= zero).
        reduced = False
    else:
        reduced = was_reduced

    account_pnl_state = {
        "date_ist": day_key,
        "source": "Exness account deals history API + account snapshot",
        "realized_closed_pnl": str(realized),
        "floating_pnl": str(floating) if floating is not None else None,
        "total_pnl_including_floating": str(total_account_pnl) if total_account_pnl is not None else None,
        "closed_position_count": len(closed_position_ids) + (1 if unlinked_close_total else 0),
        "account_balance": str(_deal_money_amount(balance_raw)) if balance_raw not in (None, "") else None,
        "deal_count": len(rows),
        "updated_at": utc_iso(now_utc),
    }
    state.update({
        "realized_closed_pnl": str(realized),
        "reduced_mode": reduced,
        "broker_realized_closed_pnl": str(realized),
        "broker_reconciled_at": utc_iso(now_utc),
        "account_pnl": account_pnl_state,
        "updated_at": utc_iso(now_utc),
    })
    store.set_json("daily_risk_state", state)

    # Keep the persistent daily report current from broker data, even when no
    # bot-managed group closes today or trades are closed manually in Exness.
    daily_report = store.get_json("daily_group_report", {}) or {}
    if daily_report.get("date_ist") != day_key:
        daily_report = _empty_daily_group_report(day_key)
    daily_report["exness_account_pnl"] = account_pnl_state
    store.set_json("daily_group_report", daily_report)
    archive = store.get_json("daily_group_reports", {}) or {}
    archive[day_key] = daily_report
    store.set_json("daily_group_reports", archive)
    _write_group_daily_report_file(daily_report)

    if reduced and not was_reduced:
        logging.warning(
            "EXNESS CAPITAL PROTECTION ACTIVATED: Broker-confirmed daily closed P/L $%.2f reached the 30%% loss threshold (-$%.2f). New trades use 3%% + 1%% risk.",
            float(realized), float(threshold),
        )
    elif was_reduced and not reduced:
        logging.info(
            "EXNESS CAPITAL PROTECTION CLEARED: Broker-confirmed daily closed P/L recovered to $%.2f. New trades return to 5%% + 2%% risk.",
            float(realized),
        )
    logging.debug(
        "EXNESS DAILY ACCOUNT P/L | Realized closed: $%+.2f | Floating: %s | Total: %s | Risk mode: %s | closed positions: %d",
        float(realized),
        f"${float(floating):+.2f}" if floating is not None else "unavailable",
        f"${float(total_account_pnl):+.2f}" if total_account_pnl is not None else "realized only",
        "REDUCED 3%+1%" if reduced else "NORMAL 5%+2%",
        len(closed_position_ids),
    )
    return state


# ---------- Indicator calculations ----------
def _indie_rma(series: pd.Series, length: int) -> pd.Series:
    """Reproduce Indie Rma: SMA seed, then Wilder recursive smoothing."""
    values = series.astype(float).to_numpy()
    out = [float("nan")] * len(values)
    previous = float("nan")
    for i, value in enumerate(values):
        if pd.isna(value):
            previous = float("nan")
            out[i] = float("nan")
            continue
        if pd.isna(previous):
            start = i - length + 1
            if start >= 0:
                window = values[start:i + 1]
                if not pd.isna(window).any():
                    previous = float(window.mean())
        else:
            previous = (float(value) + (length - 1) * previous) / length
        out[i] = previous
    return pd.Series(out, index=series.index, dtype=float)


def ema(series: pd.Series, length: int) -> pd.Series:
    """Reproduce Indie Ema: first valid value is an SMA, then EMA recursion."""
    values = series.astype(float).to_numpy()
    out = [float("nan")] * len(values)
    previous = float("nan")
    alpha = 2.0 / (length + 1.0)
    for i, value in enumerate(values):
        if pd.isna(value):
            previous = float("nan")
            out[i] = float("nan")
            continue
        if pd.isna(previous):
            start = i - length + 1
            if start >= 0:
                window = values[start:i + 1]
                if not pd.isna(window).any():
                    previous = float(window.mean())
        else:
            previous = alpha * float(value) + (1.0 - alpha) * previous
        out[i] = previous
    return pd.Series(out, index=series.index, dtype=float)


def rsi_wilder(close: pd.Series, length: int = 14) -> pd.Series:
    """Reproduce Indie Rsi: RMA(gains/losses), including its SMA seed."""
    delta = close.astype(float).diff()
    gain = delta.clip(lower=0.0)
    loss = (-delta).clip(lower=0.0)
    avg_gain = _indie_rma(gain, length)
    avg_loss = _indie_rma(loss, length)
    denominator = avg_gain + avg_loss
    # Indie Rsi uses divide(avg_gain, avg_gain + avg_loss, 1.0).
    ratio = avg_gain.div(denominator.where(denominator != 0.0))
    ratio = ratio.where(denominator != 0.0, 1.0)
    return 100.0 * ratio


def truth(x: Any) -> bool:
    return bool(x) if pd.notna(x) else False


def price_string(value: float, digits: int) -> str:
    """Round an order price to the broker's advertised point precision.

    Keep the unrounded Indie strategy value in signal logs for parity checks,
    but submit only a broker-valid price increment (e.g. 3 decimals for XAUUSD
    when point_digits=3). ROUND_HALF_UP avoids Python's banker's rounding.
    """
    quantum = Decimal("1").scaleb(-digits)
    rounded = dec(value).quantize(quantum, rounding=ROUND_HALF_UP)
    return format(rounded, f".{digits}f")


def volume_string(lot: float, conditions: dict) -> str:
    """Round volume DOWN to the broker step so actual risk never exceeds budget."""
    requested = dec(str(lot))
    vmin = dec(conditions.get("volume_min", "0"))
    vmax = dec(conditions.get("volume_max", "0"))
    step = dec(conditions.get("volume_step", "0"))
    if step <= 0 or vmin <= 0 or vmax < vmin:
        raise ValueError(f"Invalid broker volume specification: min={vmin}, max={vmax}, step={step}.")
    if requested < vmin:
        raise ValueError(f"Calculated lot {requested} is below broker minimum {vmin}; refusing to increase risk.")
    steps = ((requested - vmin) / step).to_integral_value(rounding="ROUND_FLOOR")
    actual = vmin + steps * step
    if actual < vmin or actual > vmax:
        raise ValueError(f"Rounded lot {actual} is outside broker volume range {vmin}..{vmax}.")
    return format(actual, "f")


def _floor_volume_step(value: Decimal, vmin: Decimal, step: Decimal) -> Decimal:
    if step <= 0 or vmin <= 0:
        raise ValueError("Broker minimum volume and step must be positive.")
    if value < vmin:
        return Decimal("0")
    return vmin + ((value - vmin) / step).to_integral_value(rounding="ROUND_FLOOR") * step


def split_entry_volumes(total_lot: Any, conditions: dict) -> tuple[str, str]:
    """Allocate lots like Indie: 60/40 at >=0.03, 50/50 at 0.02, 100/0 at 0.01.

    Indie rounds each leg to 0.01 lot and assigns the remainder to Entry 2.
    Respect the broker's volume step/minimum; if the exact split is not
    executable, safely retain the full lot on Entry 1 instead of increasing risk.
    """
    total = dec(volume_string(float(dec(total_lot)), conditions))
    vmin = dec(conditions.get("volume_min", "0"))
    step = dec(conditions.get("volume_step", "0"))
    max_volume = dec(conditions.get("volume_max", "0"))
    if total < vmin or step <= 0:
        raise ValueError("Total volume is below broker minimum or broker volume_step is invalid.")
    primary, secondary = total, Decimal("0")
    if total >= Decimal("0.03"):
        primary = (total * Decimal("0.60")).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        secondary = total - primary
    elif total >= Decimal("0.02"):
        primary = (total * Decimal("0.50")).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        secondary = total - primary
    # Exact Indie split only if both legs can be represented by broker volume step.
    if secondary > 0 and (primary < vmin or secondary < vmin or primary % step != 0 or secondary % step != 0):
        primary, secondary = total, Decimal("0")
    if primary > max_volume or secondary > max_volume:
        raise ValueError("Split entry volume exceeds broker volume_max.")
    return format(primary, "f"), (format(secondary, "f") if secondary > 0 else "")


def _entry_level_touched(side: str, candle_high: float, candle_low: float, entry: float) -> bool:
    """Return whether the completed candle crossed a pending entry price."""
    return candle_low <= entry if side == "buy" else candle_high >= entry


def _setup_retrace_percent(side: str, candle_high: float, candle_low: float,
                           setup_high: float, setup_low: float) -> float:
    """Retracement from the setup candle extreme toward its midpoint."""
    candle_range = setup_high - setup_low
    if candle_range <= 0:
        return 0.0
    if side == "buy":
        return max(0.0, min(100.0, (setup_high - candle_low) / candle_range * 100.0))
    return max(0.0, min(100.0, (candle_high - setup_low) / candle_range * 100.0))


def classify_signal_group(entry_triggered: bool, retrace_percent: float = 0.0) -> str:
    """Classify by broker-confirmed fill only; candle touch alone is not a fill."""
    return "ACTIVE" if entry_triggered else "INACTIVE"


def _auto_structure_rr_multiplier(history: pd.DataFrame, index: int, side: str,
                                  entry: float, risk: float, signal_range: float) -> float | None:
    """Select the highest RR tier fitting the prior ten candles' opposing structure."""
    if risk <= 0.0 or index < 10:
        return None
    prior = history.iloc[index - 10:index]
    if len(prior) < 10:
        return None
    buffer = max(float(signal_range) * 0.15, float(risk) * 0.03)
    room = (float(prior["high"].max()) - float(entry) - buffer) if side == "buy" else (float(entry) - float(prior["low"].min()) - buffer)
    available_rr = room / float(risk)
    for tier in (4.0, 3.0, 2.0, 1.5, 1.0):
        if available_rr + 1e-9 >= tier:
            return tier
    return None


def _validate_exness_indie_master_calculation(
    side: str, candle: Any, history: pd.DataFrame, index: int, cfg: Config,
    risk_budget_cash: float, rr_multiplier: float, entry: float, stop: float,
    target: float, secondary_entry: float, total_lot: float,
) -> None:
    """Fail closed if Python's primary/secondary prices or lot differ from Indie.

    Master source: Exness_Indie backup(2010level)(2).txt. Indie uses the
    completed chart candle (Bid chart data): Entry 1 = candle midpoint; the
    shared SL = highest/lowest of signal candle + previous 7 candles, padded
    by max(25% signal range, 0.005% of entry); TP = RR multiple; Entry 2 =
    BUY high - 20% range / SELL low + 20% range. Lot is floored to 0.01.
    Broker volume-step constraints are applied later by the execution adapter
    and may safely disable the secondary leg, never increase total risk.
    """
    tol = max(1e-8, abs(float(entry)) * 1e-10)
    candle_range = float(candle.high) - float(candle.low)
    if candle_range <= 0.0:
        raise ValueError("Indie master parity: signal candle range must be positive.")
    expected_entry = (float(candle.high) + float(candle.low)) / 2.0
    buffer = max(candle_range * 0.25, abs(expected_entry) * 0.00005)
    if side == "buy":
        recent_extreme = float(history.iloc[index-7:index+1]["low"].min())
        expected_stop = min(recent_extreme, expected_entry - buffer)
        risk = expected_entry - expected_stop
        expected_secondary = float(candle.high) - candle_range * 0.20
        expected_target = expected_entry + risk * rr_multiplier
    elif side == "sell":
        recent_extreme = float(history.iloc[index-7:index+1]["high"].max())
        expected_stop = max(recent_extreme, expected_entry + buffer)
        risk = expected_stop - expected_entry
        expected_secondary = float(candle.low) + candle_range * 0.20
        expected_target = expected_entry - risk * rr_multiplier
    else:
        raise ValueError(f"Indie master parity: invalid side {side!r}.")
    if risk <= 0.0:
        raise ValueError("Indie master parity: computed risk must be positive.")
    expected_lot = int((risk_budget_cash / (risk * cfg.contract_size)) * 100.0) / 100.0
    checks = (
        ("Entry 1 midpoint", entry, expected_entry),
        ("shared SL", stop, expected_stop),
        ("shared TP", target, expected_target),
        ("Entry 2 20%", secondary_entry, expected_secondary),
        ("risk-sized lot", total_lot, expected_lot),
    )
    for label, actual, expected in checks:
        if abs(float(actual) - float(expected)) > tol:
            raise RuntimeError(
                f"Indie master parity mismatch for {label}: bot={actual:.10f}, "
                f"Indie={expected:.10f}. Signal blocked; no broker order submitted."
            )


def compute_signal(m1: pd.DataFrame, m3: pd.DataFrame, cfg: Config, pending: dict, risk_target_percent: float | None = None, risk_buffer_percent: float | None = None, active_group: dict | None = None) -> tuple[dict | None, dict]:
    """Replicate the supplied Indie indicator's M1 setup and entry rules.

    Indie is the source of truth for EMA/RSI seeds, HTF indexing, candle
    patterns, volume/SR, OB/FVG/H&S, breakout-pullback state, midpoint/20%
    entries, SL/TP and risk sizing. Broker validation/execution remains an
    adapter and must not alter the saved strategy price levels.
    """
    if len(m1) < 210 or len(m3) < 55:
        logging.debug("Waiting for more completed 1-minute and 3-minute market data.")
        return None, pending

    d = m1.copy().reset_index(drop=True)
    for n in (9, 20, 50, 200):
        d[f"ema{n}"] = ema(d["close"], n)
    d["rsi"] = rsi_wilder(d["close"], 14)

    # Indie calc_on(ConfirmHtfEma, 3m) reads EMA20/50[1]. At each M1 bar,
    # select the latest 3m candle that was already closed before that M1 bar opened.
    m3x = m3.copy().reset_index(drop=True)
    m3x["ema20"] = ema(m3x["close"], 20)
    m3x["ema50"] = ema(m3x["close"], 50)
    m1_open = d.iloc[-1]["time"]
    completed_htf = m3x[m3x["time"] + pd.Timedelta(minutes=3) <= m1_open]
    if completed_htf.empty:
        return None, pending
    htf = completed_htf.iloc[-1]

    i = len(d) - 1
    c = d.iloc[i]
    # Latest uploaded Indie source expires breakout pullback setups after 10 bars.
    indie_breakout_expiry_bars = 10
    p1, p2, p3 = d.iloc[i-1], d.iloc[i-2], d.iloc[i-3]
    ema9, ema20, ema50, ema200 = c.ema9, c.ema20, c.ema50, c.ema200
    rsi_now, rsi_prev = c.rsi, p1.rsi
    if pd.isna([ema9, ema20, ema50, ema200, rsi_now, rsi_prev, htf.ema20, htf.ema50]).any():
        return None, pending

    htf_buy = htf.ema20 > htf.ema50
    htf_sell = htf.ema20 < htf.ema50
    bullish_trend = ema20 > ema50 and ema50 > ema200
    bearish_trend = ema20 < ema50 and ema50 < ema200
    buy_momentum = rsi_now > 45
    sell_momentum = rsi_now < 55

    candle_range = c.high - c.low
    candidate_entry_price = (c.high + c.low) / 2.0
    # Secondary 20% level follows the user's directional convention:
    # BUY: measure down from candle HIGH; SELL: measure up from candle LOW.
    buy_secondary_20 = c.high - (candle_range * 0.20)
    sell_secondary_20 = c.low + (candle_range * 0.20)
    candle_body = abs(c.close - c.open)
    lower_wick = min(c.open, c.close) - c.low
    upper_wick = c.high - max(c.open, c.close)

    bullish_close_momentum = candle_range > 0 and c.close > c.open and (c.close - c.low) / candle_range >= .75
    bearish_close_momentum = candle_range > 0 and c.close < c.open and (c.high - c.close) / candle_range >= .75
    bullish_engulfing = p1.close < p1.open and c.close > c.open and c.open <= p1.close and c.close >= p1.open
    bearish_engulfing = p1.close > p1.open and c.close < c.open and c.open >= p1.close and c.close <= p1.open
    bullish_rejection = candle_body > 0 and lower_wick >= candle_body * 1.2 and bullish_close_momentum
    bearish_rejection = candle_body > 0 and upper_wick >= candle_body * 1.2 and bearish_close_momentum
    bullish_hammer = candle_range > 0 and lower_wick >= candle_body * 2 and upper_wick <= candle_body * .8 and c.close > c.open and (c.close-c.low)/candle_range >= .60
    bearish_shooting_star = candle_range > 0 and upper_wick >= candle_body * 2 and lower_wick <= candle_body * .8 and c.close < c.open and (c.high-c.close)/candle_range >= .60
    previous_range = p1.high - p1.low
    previous_body = abs(p1.close-p1.open)
    morning_star = p2.close < p2.open and previous_range > 0 and previous_body <= previous_range*.35 and c.close > c.open and c.close > (p2.open+p2.close)/2
    evening_star = p2.close > p2.open and previous_range > 0 and previous_body <= previous_range*.35 and c.close < c.open and c.close < (p2.open+p2.close)/2
    bullish_break_previous = c.close > p1.high and c.close > c.open
    bearish_break_previous = c.close < p1.low and c.close < c.open
    bullish_strong_body = candle_range > 0 and candle_body/candle_range >= .60 and c.close > c.open and (c.close-c.low)/candle_range >= .70
    bearish_strong_body = candle_range > 0 and candle_body/candle_range >= .60 and c.close < c.open and (c.high-c.close)/candle_range >= .70

    # On the user's 1m chart, the indicator's 3m-chart-only candle/volume filter
    # and 3m-only volume impulse are inactive; MTF candle confirmations default True.
    bullish_mtf_candle_confirm = True
    bearish_mtf_candle_confirm = True
    bullish_price_action = (bullish_engulfing or bullish_rejection or bullish_hammer or morning_star or bullish_close_momentum or bullish_strong_body or bullish_break_previous) and bullish_mtf_candle_confirm
    bearish_price_action = (bearish_engulfing or bearish_rejection or bearish_shooting_star or evening_star or bearish_close_momentum or bearish_strong_body or bearish_break_previous) and bearish_mtf_candle_confirm

    avg_volume = d.iloc[i-10:i]["volume"].mean()
    volume_confirm = avg_volume > 0 and c.volume > avg_volume * 1.2
    buy_volume_confirm = volume_confirm
    sell_volume_confirm = volume_confirm

    support = d.iloc[i-10:i]["low"].min()
    resistance = d.iloc[i-10:i]["high"].max()
    sr_range = resistance - support
    support_zone = sr_range > 0 and c.low <= support + sr_range*.15 and c.close > support
    resistance_zone = sr_range > 0 and c.high >= resistance - sr_range*.15 and c.close < resistance

    bullish_breakout_volume_setup = c.close > resistance and c.close > c.open and volume_confirm and (bullish_strong_body or bullish_close_momentum)
    bearish_breakout_volume_setup = c.close < support and c.close < c.open and volume_confirm and (bearish_strong_body or bearish_close_momentum)

    buy_pullback = c.low <= ema20 and c.close > ema9 and c.close > c.open
    sell_pullback = c.high >= ema20 and c.close < ema9 and c.close < c.open
    buy_rejection_setup = support_zone and buy_volume_confirm and (bullish_engulfing or bullish_rejection)
    sell_rejection_setup = resistance_zone and sell_volume_confirm and (bearish_engulfing or bearish_rejection)

    bullish_ob_low = bullish_ob_high = None
    for j in range(1, 6):
        q = d.iloc[i-j]
        if q.close < q.open:
            bullish_ob_low, bullish_ob_high = q.low, q.high
            break
    bullish_ob_touch = bullish_ob_low is not None and c.low <= bullish_ob_high and c.high >= bullish_ob_low and c.close > bullish_ob_low and c.close > c.open and bullish_mtf_candle_confirm

    bearish_ob_low = bearish_ob_high = None
    for j in range(1, 6):
        q = d.iloc[i-j]
        if q.close > q.open:
            bearish_ob_low, bearish_ob_high = q.low, q.high
            break
    bearish_ob_touch = bearish_ob_low is not None and c.low <= bearish_ob_high and c.high >= bearish_ob_low and c.close < bearish_ob_high and c.close < c.open and bearish_mtf_candle_confirm

    bullish_fvg_valid = p1.low > p3.high
    bullish_fvg_low, bullish_fvg_high = p3.high, p1.low
    bullish_fvg_touch = bullish_fvg_valid and c.low <= bullish_fvg_high and c.high >= bullish_fvg_low and c.close > bullish_fvg_low and c.close > c.open
    bearish_fvg_valid = p1.high < p3.low
    bearish_fvg_low, bearish_fvg_high = p1.high, p3.low
    bearish_fvg_touch = bearish_fvg_valid and c.high >= bearish_fvg_low and c.low <= bearish_fvg_high and c.close < bearish_fvg_high and c.close < c.open

    hs_left, hs_head, hs_right = d.iloc[i-8].high, d.iloc[i-5].high, d.iloc[i-2].high
    hs_neckline = (d.iloc[i-7].low + d.iloc[i-3].low)/2
    hs_shoulders_similar = sr_range > 0 and abs(hs_left-hs_right) <= sr_range*.15
    head_shoulders_sell = hs_shoulders_similar and hs_head > hs_left and hs_head > hs_right and c.close < hs_neckline and c.close < c.open
    ihs_left, ihs_head, ihs_right = d.iloc[i-8].low, d.iloc[i-5].low, d.iloc[i-2].low
    ihs_neckline = (d.iloc[i-7].high + d.iloc[i-3].high)/2
    ihs_shoulders_similar = sr_range > 0 and abs(ihs_left-ihs_right) <= sr_range*.15
    inverse_head_shoulders_buy = ihs_shoulders_similar and ihs_head < ihs_left and ihs_head < ihs_right and c.close > ihs_neckline and c.close > c.open

    buy_existing_setup = buy_pullback and (bullish_ob_touch or bullish_fvg_touch or support_zone)
    sell_existing_setup = sell_pullback and (bearish_ob_touch or bearish_fvg_touch or resistance_zone)
    # 3m-chart-only volume impulse setup is false on a 1m chart.
    bullish_volume_impulse_setup = False
    bearish_volume_impulse_setup = False
    buy_condition = (htf_buy and bullish_trend and buy_momentum and bullish_price_action and (buy_existing_setup or buy_rejection_setup or bullish_ob_touch or bullish_fvg_touch or inverse_head_shoulders_buy)) or bullish_volume_impulse_setup
    sell_condition = (htf_sell and bearish_trend and sell_momentum and bearish_price_action and (sell_existing_setup or sell_rejection_setup or bearish_ob_touch or bearish_fvg_touch or head_shoulders_sell)) or bearish_volume_impulse_setup

    # Add-on Entry 3+ marker logic is intentionally removed.
    # Strategy entries are only Entry 1 (50%) and Entry 2 (20%).

    # Match the latest uploaded Indie breakout-pullback state:
    # arm from a breakout+volume candle; expire after 10 completed bars;
    # invalidate if close crosses back through the setup extreme.
    # The latest Indie source does NOT use the separate 4-bar early-setup
    # rule or the 0.5 ATR late-entry rejection filter.
    bar_time = c.time
    pending = dict(pending)
    active_group = active_group or {}
    has_active_group = bool(active_group.get("active"))

    if not has_active_group:
        if bullish_breakout_volume_setup:
            pending = {
                "side": "buy",
                "time": bar_time.isoformat(),
                "average": float(candidate_entry_price),
                "low": float(c.low),
                "high": float(c.high),
            }
            logging.info(
                "INDIE BREAKOUT PULLBACK SETUP ARMED | BUY | bar=%s | midpoint=%.3f | expiry=10 bars",
                bar_time, float(candidate_entry_price),
            )
        elif bearish_breakout_volume_setup:
            pending = {
                "side": "sell",
                "time": bar_time.isoformat(),
                "average": float(candidate_entry_price),
                "low": float(c.low),
                "high": float(c.high),
            }
            logging.info(
                "INDIE BREAKOUT PULLBACK SETUP ARMED | SELL | bar=%s | midpoint=%.3f | expiry=10 bars",
                bar_time, float(candidate_entry_price),
            )

    def _pending_age_bars(saved: dict) -> int:
        try:
            setup_time = pd.Timestamp(saved["time"])
            if setup_time.tzinfo is None:
                setup_time = setup_time.tz_localize("UTC")
            else:
                setup_time = setup_time.tz_convert("UTC")
            times = pd.to_datetime(d["time"], utc=True)
            return int(((times > setup_time) & (times <= bar_time)).sum())
        except Exception:
            return 999

    if pending.get("side") == "buy" and bar_time > pd.Timestamp(pending["time"]):
        buy_pending_age = _pending_age_bars(pending)
        if buy_pending_age > 10 or c.close < float(pending["low"]):
            logging.info(
                "INDIE BUY BREAKOUT SETUP EXPIRED/INVALIDATED | age=%d bars",
                buy_pending_age,
            )
            pending = {}
    elif pending.get("side") == "sell" and bar_time > pd.Timestamp(pending["time"]):
        sell_pending_age = _pending_age_bars(pending)
        if sell_pending_age > 10 or c.close > float(pending["high"]):
            logging.info(
                "INDIE SELL BREAKOUT SETUP EXPIRED/INVALIDATED | age=%d bars",
                sell_pending_age,
            )
            pending = {}

    buy_breakout_pullback_ready = False
    sell_breakout_pullback_ready = False
    buy_breakout_ideal_entry = None
    sell_breakout_ideal_entry = None

    if pending.get("side") == "buy" and bar_time > pd.Timestamp(pending["time"]):
        pullback_confirm = c.close > c.open and (
            bullish_rejection or bullish_engulfing or bullish_hammer or bullish_close_momentum
        )
        if pullback_confirm:
            buy_average_touched = c.low <= float(pending["average"]) and c.close > float(pending["average"])
            buy_bottom_touched = c.low <= float(pending["low"]) and c.close > float(pending["low"])
            buy_breakout_pullback_ready = buy_average_touched or (not buy_average_touched and buy_bottom_touched)
            if buy_breakout_pullback_ready:
                buy_breakout_ideal_entry = float(pending["average"]) if buy_average_touched else float(pending["low"])

    if pending.get("side") == "sell" and bar_time > pd.Timestamp(pending["time"]):
        pullback_confirm = c.close < c.open and (
            bearish_rejection or bearish_engulfing or bearish_shooting_star or bearish_close_momentum
        )
        if pullback_confirm:
            sell_average_touched = c.high >= float(pending["average"]) and c.close < float(pending["average"])
            sell_top_touched = c.high >= float(pending["high"]) and c.close < float(pending["high"])
            sell_breakout_pullback_ready = sell_average_touched or (not sell_average_touched and sell_top_touched)
            if sell_breakout_pullback_ready:
                sell_breakout_ideal_entry = float(pending["average"]) if sell_average_touched else float(pending["high"])

    # Indie allows a direct signal on the breakout candle itself. A pending
    # breakout setup must not suppress an otherwise valid primary signal.
    buy_entry_ready = buy_condition or buy_breakout_pullback_ready
    sell_entry_ready = sell_condition or sell_breakout_pullback_ready

    # Refresh a pending, unfilled group only from a newer confirmed Indie setup.
    active_group = active_group or {}
    pending_group_only = (
        bool(active_group.get("active"))
        and not bool(active_group.get("active_triggered"))
        and not bool(active_group.get("group_exit_event"))
    )
    if bool(active_group.get("active")) and not pending_group_only:
        pending = {}
        group_side = str(active_group.get("side", "")).lower()
        group_legs = active_group.get("legs", []) or []
        filled_leg = next(
            (leg for leg in group_legs
             if str(leg.get("status", "")).lower() == "filled"
             and leg.get("position_id")),
            None,
        )
        events = []
        if filled_leg and bool(active_group.get("active_triggered")):
            # Only the two original strategy legs are retained: 50% and 20%.
            # No chart-only Entry 3/4/5 add-on marker is generated.
            # Indie early-exit warning is advisory only; it does not close
            # the chart-side simulated trade.
            if not bool(active_group.get("indie_early_exit_warned", False)):
                if group_side == "buy":
                    failure_score = 0
                    if c.close < ema20 and ema20 < ema50:
                        failure_score += 1
                    if htf_sell:
                        failure_score += 1
                    if rsi_now < 45 and rsi_now < rsi_prev:
                        failure_score += 1
                    if bearish_price_action:
                        failure_score += 1
                else:
                    failure_score = 0
                    if c.close > ema20 and ema20 > ema50:
                        failure_score += 1
                    if htf_buy:
                        failure_score += 1
                    if rsi_now > 55 and rsi_now > rsi_prev:
                        failure_score += 1
                    if bullish_price_action:
                        failure_score += 1
                if failure_score >= 3:
                    events.append({
                        "type": "OPPOSITE_SIGNAL_EXIT",
                        "side": group_side,
                        "opposite_side": "sell" if group_side == "buy" else "buy",
                        "failure_score": int(failure_score),
                        "bar_time": c.time.isoformat(),
                        "exit_reference_price": float(c.close),
                    })

        if events:
            return {"kind": "INDIE_EVENT", "events": events}, pending
        return None, pending

    side = None
    if sell_entry_ready and not buy_entry_ready:
        side = "sell"
    elif buy_entry_ready and not sell_entry_ready:
        side = "buy"
    if pending_group_only and side is not None and side != str(active_group.get("side", "")).lower():
        return {"kind": "INDIE_EVENT", "events": [{
            "type": "PENDING_SETUP_INVALIDATED",
            "side": str(active_group.get("side", "")).lower(),
            "opposite_side": side,
            "bar_time": c.time.isoformat(),
            "exit_reference_price": float(c.close),
        }]}, pending
    breakout_pullback_signal = bool(
        (side == "buy" and buy_breakout_pullback_ready)
        or (side == "sell" and sell_breakout_pullback_ready)
    )
    if breakout_pullback_signal:
        breakout_setup_high = float(pending.get("high", c.high))
        breakout_setup_low = float(pending.get("low", c.low))
    else:
        breakout_setup_high = float(c.high)
        breakout_setup_low = float(c.low)
    if side is not None:
        # Indie clears pending BUY and SELL breakout states on any primary entry.
        pending = {}


    if side is None:
        # Indie-parity diagnostics: expose each gate without changing strategy.
        logging.debug(
            "INDIE PARITY | M1 trend BUY=%s SELL=%s | M3 EMA BUY=%s SELL=%s | "
            "RSI BUY=%s SELL=%s | price action BUY=%s SELL=%s | "
            "setup BUY=%s SELL=%s | breakout pullback BUY=%s SELL=%s",
            bullish_trend, bearish_trend, htf_buy, htf_sell,
            buy_momentum, sell_momentum, bullish_price_action, bearish_price_action,
            (buy_existing_setup or buy_rejection_setup or bullish_ob_touch or bullish_fvg_touch or inverse_head_shoulders_buy),
            (sell_existing_setup or sell_rejection_setup or bearish_ob_touch or bearish_fvg_touch or head_shoulders_sell),
            buy_breakout_pullback_ready, sell_breakout_pullback_ready,
        )
        logging.debug(
            "INDIE PARITY VALUES | close=%.5f EMA20=%.5f EMA50=%.5f EMA200=%.5f "
            "RSI=%.2f M3 EMA20=%.5f M3 EMA50=%.5f",
            float(c.close), float(ema20), float(ema50), float(ema200),
            float(rsi_now), float(htf.ema20), float(htf.ema50),
        )
        return None, pending

    # Exact Indie Entry 1: every setup, including breakout-pullback setups,
    # uses the confirmation candle midpoint. Breakout pullback changes the
    # signal reason/qualification only; it does not override the entry price.
    entry = float(candidate_entry_price)
    logging.info(
        "INDIE SIGNAL CANDLE | side=%s | bar_utc=%s | O=%.5f H=%.5f L=%.5f C=%.5f | "
        "direct=%s breakout_pullback=%s | entry_basis=%s",
        side.upper(), c.time.isoformat(), float(c.open), float(c.high),
        float(c.low), float(c.close),
        bool(buy_condition if side == "buy" else sell_condition),
        breakout_pullback_signal,
        "confirmation candle midpoint (Indie Entry 1)",
    )
    if candle_range <= 0:
        logging.info("SIGNAL SKIPPED: completed confirmation candle has zero range.")
        return None, pending
    stop_buffer = max(candle_range * .25, abs(entry) * .00005)
    if side == "buy":
        recent_low = d.iloc[i-7:i+1]["low"].min()
        stop = min(recent_low, entry - stop_buffer)
        risk = entry - stop
    else:
        recent_high = d.iloc[i-7:i+1]["high"].max()
        stop = max(recent_high, entry + stop_buffer)
        risk = stop - entry
    active_target = cfg.risk_percent if risk_target_percent is None else risk_target_percent
    active_buffer = cfg.risk_buffer_percent if risk_buffer_percent is None else risk_buffer_percent
    total_risk_percent = min(7.0, active_target + active_buffer)
    risk_budget_cash = cfg.account_capital * total_risk_percent / 100.0
    if cfg.risk_reward == "AUTO":
        rr = _auto_structure_rr_multiplier(d, i, side, entry, risk, candle_range)
        if rr is None:
            logging.info("SIGNAL SKIPPED: AUTO TP has less than 1R available before the prior 10-candle opposing structure.")
            return None, pending
    else:
        rr = {"1:1": 1.0, "1:1.5": 1.5, "1:2": 2.0, "1:3": 3.0, "1:4": 4.0}[cfg.risk_reward]
    target = entry + risk * rr if side == "buy" else entry - risk * rr

    # Match Indie Entry 2 exactly: confirmation candle HIGH - 20% of its
    # range for BUY; confirmation candle LOW + 20% of its range for SELL.
    if candle_range <= 0:
        logging.info("SIGNAL SKIPPED: confirmation candle has zero range for Entry 2.")
        return None, pending
    secondary_entry_20 = (
        float(c.high) - candle_range * 0.20
        if side == "buy"
        else float(c.low) + candle_range * 0.20
    )
    midpoint_sl_percent = (risk / abs(entry) * 100.0) if entry else float("inf")
    if midpoint_sl_percent > 7.0:
        logging.info("SIGNAL SKIPPED: midpoint shared-SL distance %.4f%% exceeds the 7%% cap.", midpoint_sl_percent)
        return None, pending
    midpoint_risk_per_lot = risk * cfg.contract_size
    secondary_risk_distance = abs(secondary_entry_20 - stop)
    secondary_sl_percent = (secondary_risk_distance / abs(secondary_entry_20) * 100.0) if secondary_entry_20 else float("inf")
    secondary_allowed = secondary_sl_percent <= 9.0
    secondary_risk_per_lot = secondary_risk_distance * cfg.contract_size
    # Indie calculates total lot from the 50% midpoint's stop distance.
    # The secondary leg is only included if its own SL distance passes 9%.
    sizing_risk_per_lot = midpoint_risk_per_lot
    lot = 0.0
    if sizing_risk_per_lot > 0 and risk_budget_cash > 0:
        raw_lot = risk_budget_cash / sizing_risk_per_lot
        lot = int(raw_lot * 100.0) / 100.0
    if not (risk > 0 and risk <= 15.0 and lot >= .01):
        logging.info("SIGNAL SKIPPED: The stop distance or calculated lot size does not meet the configured risk rules.")
        return None, pending

    risk_cash = lot * sizing_risk_per_lot
    logging.info(
        "INDIE PARITY CALC | side=%s | midpoint=%.5f | SL=%.5f | TP=%.5f | "
        "midpoint risk=%.5f | secondary 20%%=%.5f | secondary SL distance=%.4f%% | "
        "risk budget=$%.2f | total lot=%.2f | conservative planned risk=$%.2f | RR=%s",
        side.upper(), entry, stop, target, risk, secondary_entry_20,
        secondary_sl_percent, risk_budget_cash, lot, risk_cash, cfg.risk_reward,
    )
    if not secondary_allowed:
        logging.warning(
            "20%% SECONDARY LEG SKIPPED: its shared master SL is %.4f%% from its entry, above the 9%% cap. "
            "The 50%% midpoint leg remains available.", secondary_sl_percent,
        )
    # Validate the complete price/risk calculation against the Indie master
    # before this signal can reach the Exness order-submission layer.
    _validate_exness_indie_master_calculation(
        side, c, d, i, cfg, risk_budget_cash, rr, entry, stop, target,
        float(secondary_entry_20), float(lot),
    )
    signal = {
        "strategy_master": "Exness Indie",
        "signal_price_basis": "Bid chart OHLC (Indie chart source)",
        "execution_quote_basis": "BUY pending/entry Ask; SELL pending/entry Bid; BUY exits Bid; SELL exits Ask",
        "bar_time": bar_time.isoformat(), "side": side,
        "entry": entry, "secondary_entry_20": float(secondary_entry_20),
        "setup_high": float(c.high), "setup_low": float(c.low),
        
        "sl": stop, "tp": target, "lot": lot,
        "risk_cash": risk_cash, "risk_budget_cash": risk_budget_cash,
        "risk_per_one_lot": sizing_risk_per_lot,
        "midpoint_risk_per_lot": midpoint_risk_per_lot,
        "secondary_risk_per_lot": secondary_risk_per_lot,
        "midpoint_sl_percent": midpoint_sl_percent,
        "secondary_sl_percent": secondary_sl_percent,
        "secondary_allowed": secondary_allowed,
        "secondary_skip_reason": None if secondary_allowed else "SKIPPED_STOP_DISTANCE_CAP",
        "reason": ("Indie breakout-pullback qualified; Entry 1 remains confirmation midpoint" if (buy_breakout_pullback_ready or sell_breakout_pullback_ready) else "Indie direct signal"),
    }
    if pending_group_only and side == str(active_group.get("side", "")).lower():
        signal["kind"] = "PENDING_REPRICE"
        signal["reprice_bar_time"] = c.time.isoformat()
    return signal, pending


def validate_signal_price_levels(signal: dict, conditions: dict) -> None:
    """Reject malformed LIMIT price geometry before sending any broker POST.

    Exness remains authoritative for live minimum-distance rules. If the
    instrument-conditions response exposes a documented stop-distance field,
    enforce it; otherwise do not invent a distance or silently alter prices.
    """
    side = str(signal.get("side", "")).strip().lower()
    if side not in {"buy", "sell"}:
        raise ValueError(f"Invalid order side for LIMIT entry: {side!r}")
    legs = signal.get("entry_legs") or [{
        "entry_text": signal.get("entry_text"),
        "sl_text": signal.get("sl_text"),
        "tp_text": signal.get("tp_text"),
    }]
    # Exness condition payloads may expose one of these distance fields. Only
    # use a positive, explicit broker-provided value; no guessed fallback.
    min_distance = None
    for key in ("minimum_stop_distance", "min_stop_distance", "stop_level", "minimum_distance"):
        raw = conditions.get(key)
        if raw not in (None, "", 0, "0"):
            try:
                candidate = dec(raw)
                if candidate > 0:
                    min_distance = candidate
                    break
            except Exception:
                continue
    for index, leg in enumerate(legs, start=1):
        try:
            entry = dec(leg.get("entry_text", leg.get("entry")))
            sl = dec(leg.get("sl_text", leg.get("sl")))
            tp = dec(leg.get("tp_text", leg.get("tp")))
        except Exception as exc:
            raise ValueError(f"LIMIT leg {index} has a missing or invalid entry/SL/TP price: {exc}")
        if min(entry, sl, tp) <= 0:
            raise ValueError(f"LIMIT leg {index} prices must all be positive.")
        if side == "buy" and not (sl < entry < tp):
            raise ValueError(f"BUY LIMIT leg {index} requires SL < entry < TP; got SL={sl}, entry={entry}, TP={tp}.")
        if side == "sell" and not (tp < entry < sl):
            raise ValueError(f"SELL LIMIT leg {index} requires TP < entry < SL; got TP={tp}, entry={entry}, SL={sl}.")
        if min_distance is not None:
            if abs(entry - sl) < min_distance or abs(tp - entry) < min_distance:
                raise ValueError(
                    f"LIMIT leg {index} violates Exness minimum stop distance {min_distance}; "
                    f"entry={entry}, SL={sl}, TP={tp}. Signal skipped without changing prices."
                )


def check_broker_compatibility(signal: dict, conditions: dict) -> dict:
    digits = int(conditions.get("point_digits", -1))
    if digits < 0:
        raise ValueError("Broker did not provide point_digits; refusing to submit an order.")
    if conditions.get("trade_mode") != "enabled":
        raise ValueError(f"Instrument trade_mode is not enabled: {conditions.get('trade_mode')}")
    side = str(signal.get("side", "")).strip().lower()
    if side not in {"buy", "sell"}:
        raise ValueError(f"Invalid signal side: {side!r}")
    raw_allowed = conditions.get("order_types")
    if isinstance(raw_allowed, (list, tuple, set)):
        allowed = [str(item).strip().lower() for item in raw_allowed if str(item).strip()]
    elif raw_allowed:
        allowed = [str(raw_allowed).strip().lower()]
    else:
        allowed = []
    if allowed and "limit" not in allowed:
        raise ValueError(f"Broker explicitly excludes the required 50% midpoint LIMIT order: {allowed}")
    if not allowed:
        logging.warning(
            "Exness did not provide the optional order_types list. The bot will use the strategy-matched "
            "pending types (50%% midpoint=LIMIT, 20%% retracement=LIMIT); it will never use a market order."
        )
    if signal.get("secondary_allowed") and allowed and "limit" not in allowed:
        logging.warning(
            "20%% SECONDARY LEG SKIPPED: Exness explicitly does not list LIMIT orders for this instrument. "
            "The midpoint LIMIT leg will use the full calculated volume."
        )
        signal["secondary_allowed"] = False
        signal["secondary_skip_reason"] = "SKIPPED_BROKER_LIMIT_UNAVAILABLE"

    # At the broker minimum total lot (0.01), submit only the 50%
    # midpoint entry. The 20% level is not eligible and must not be
    # treated as an active trade or submitted as a second leg.
    if dec(signal.get("lot", 0)) <= Decimal("0.01"):
        signal["secondary_allowed"] = False
        signal["secondary_skip_reason"] = "SKIPPED_MINIMUM_TOTAL_VOLUME_MIDPOINT_ONLY"
    if signal.get("secondary_allowed"):
        primary_volume, secondary_volume = split_entry_volumes(signal["lot"], conditions)
        if not secondary_volume:
            # Preserve the user's requested fallback: at the broker minimum
            # total volume, submit the 50% midpoint only. Do not increase lot.
            signal["secondary_skip_reason"] = "SKIPPED_INSUFFICIENT_VOLUME"
    else:
        # When the 20% leg is disallowed by its 9% stop-distance cap or broker
        # compatibility, allocate the complete already-risk-sized volume to
        # the midpoint. Never increase the calculated total volume.
        primary_volume = volume_string(float(dec(signal["lot"])), conditions)
        secondary_volume = ""
        signal.setdefault("secondary_skip_reason", "SKIPPED_SECONDARY_NOT_ALLOWED")
    # Aggregate risk must use EACH leg's distance to the shared master SL.
    # Sizing only from Entry 1 underestimates risk whenever Entry 2 is farther from the SL.
    risk_budget_cash = dec(signal.get("risk_budget_cash", "0"))
    midpoint_risk_per_lot = dec(
        signal.get("midpoint_risk_per_lot") or signal.get("risk_per_one_lot") or "0"
    )
    secondary_risk_per_lot = dec(signal.get("secondary_risk_per_lot") or "0")
    actual_group_risk_cash = (
        dec(primary_volume) * midpoint_risk_per_lot
        + (dec(secondary_volume) * secondary_risk_per_lot if secondary_volume else Decimal("0"))
    )

    if actual_group_risk_cash > risk_budget_cash + Decimal("0.01"):
        volume_step = dec(conditions.get("volume_step", "0"))
        volume_min = dec(conditions.get("volume_min", "0"))
        base_total = dec(signal.get("lot", "0"))
        if volume_step <= 0 or volume_min <= 0 or base_total <= 0:
            raise ValueError("Aggregate risk guard cannot run: invalid broker volume step/minimum or total lot.")

        selected_split = None
        if secondary_volume and actual_group_risk_cash > 0:
            safe_total = base_total * risk_budget_cash / actual_group_risk_cash
            candidate_total = (safe_total // volume_step) * volume_step
            attempts = 0
            while candidate_total >= volume_min and attempts < 1000:
                try:
                    candidate_primary, candidate_secondary = split_entry_volumes(candidate_total, conditions)
                except ValueError:
                    candidate_total -= volume_step
                    attempts += 1
                    continue
                candidate_risk = (
                    dec(candidate_primary) * midpoint_risk_per_lot
                    + (dec(candidate_secondary) * secondary_risk_per_lot if candidate_secondary else Decimal("0"))
                )
                if candidate_secondary and candidate_risk <= risk_budget_cash + Decimal("0.01"):
                    selected_split = (candidate_primary, candidate_secondary, candidate_risk)
                    break
                candidate_total -= volume_step
                attempts += 1

        if selected_split is not None:
            primary_volume, secondary_volume, actual_group_risk_cash = selected_split
            logging.warning(
                "AGGREGATE RISK GUARD | two legs resized | Entry 1=%s | Entry 2=%s | actual risk=$%.2f / budget=$%.2f",
                primary_volume, secondary_volume, float(actual_group_risk_cash), float(risk_budget_cash),
            )
        else:
            # If two legs cannot fit safely after broker-step rounding, retain Entry 1 only.
            # Never add volume; reduce Entry 1 only if its broker lot-step rounds above budget.
            primary_candidate = (base_total // volume_step) * volume_step
            attempts = 0
            while (
                primary_candidate >= volume_min
                and primary_candidate * midpoint_risk_per_lot > risk_budget_cash + Decimal("0.01")
                and attempts < 1000
            ):
                primary_candidate -= volume_step
                attempts += 1
            if primary_candidate < volume_min:
                raise ValueError("Aggregate risk guard: broker minimum volume exceeds the configured risk budget.")
            primary_volume = volume_string(float(primary_candidate), conditions)
            secondary_volume = ""
            actual_group_risk_cash = dec(primary_volume) * midpoint_risk_per_lot
            signal["secondary_allowed"] = False
            signal["secondary_skip_reason"] = "SKIPPED_AGGREGATE_RISK_BUDGET"
            logging.warning(
                "AGGREGATE RISK GUARD | Entry 2 disabled | Entry 1=%s | actual risk=$%.2f / budget=$%.2f",
                primary_volume, float(actual_group_risk_cash), float(risk_budget_cash),
            )

    if actual_group_risk_cash > risk_budget_cash + Decimal("0.01"):
        raise ValueError(
            "Aggregate risk guard failed closed: actual per-leg risk exceeds the configured risk budget."
        )

    actual_total = dec(primary_volume) + (dec(secondary_volume) if secondary_volume else Decimal("0"))
    signal["entry_text"] = price_string(signal["entry"], digits)
    signal["secondary_entry_20_text"] = price_string(signal["secondary_entry_20"], digits)
    signal["sl_text"] = price_string(signal["sl"], digits)
    signal["tp_text"] = price_string(signal["tp"], digits)
    signal["volume_text"] = primary_volume
    signal["secondary_volume_text"] = secondary_volume
    if secondary_volume:
        signal["secondary_skip_reason"] = None
    elif not signal.get("secondary_skip_reason"):
        signal["secondary_skip_reason"] = "SKIPPED_INSUFFICIENT_VOLUME"
    signal["lot"] = float(actual_total)
    signal["risk_cash"] = float(actual_group_risk_cash)

    legs = [{
        "leg": "MIDPOINT_50", "order_type": "limit", "entry": float(signal["entry"]),
        "entry_text": signal["entry_text"], "volume_text": primary_volume,
        "volume": float(dec(primary_volume)), "comment": "KS Trader Desk Entry 1 - 50% Midpoint",
        "sl_text": signal["sl_text"], "tp_text": signal["tp_text"],
        "status": "prepared", "idempotency_key": None,
        "order_id": None, "position_id": None,
        "estimated_unfilled_pnl": None,
    }]
    if secondary_volume and signal.get("secondary_allowed"):
        legs.append({
            "leg": "SECONDARY_20", "order_type": "limit", "entry": float(signal["secondary_entry_20"]),
            "entry_text": signal["secondary_entry_20_text"], "volume_text": secondary_volume,
            "volume": float(dec(secondary_volume)), "comment": "KS Trader Desk Entry 2 - 20% Level",
            "sl_text": signal["sl_text"], "tp_text": signal["tp_text"],
            "status": "prepared", "idempotency_key": None,
            "order_id": None, "position_id": None,
            "estimated_unfilled_pnl": None,
        })
    if len(legs) > 1:
        midpoint = dec(legs[0]["entry_text"])
        secondary = dec(legs[1]["entry_text"])
        if side == "sell" and not secondary < midpoint:
            raise ValueError(
                f"SELL 20% Indie retracement level must be below the 50% midpoint; "
                f"secondary={secondary}, midpoint={midpoint}. Signal skipped safely."
            )
        if side == "buy" and not secondary > midpoint:
            raise ValueError(
                f"BUY 20% Indie retracement level must be above the 50% midpoint; "
                f"secondary={secondary}, midpoint={midpoint}. Signal skipped safely."
            )
    signal["entry_legs"] = legs
    signal["total_volume_text"] = format(actual_total, "f")
    validate_signal_price_levels(signal, conditions)
    return signal


def validate_pre_entry_checklist(signal: dict) -> list[str]:
    """Final fail-closed checklist before a signal can reach broker submission.

    This validates the already-computed Indie master signal; it does not add a
    new strategy or alter the 50%/20% price levels.
    """
    checks: list[str] = []
    side = str(signal.get("side", "")).strip().lower()
    if side not in {"buy", "sell"}:
        raise ValueError("Pre-entry check 1/8 failed: signal side must be BUY or SELL.")
    checks.append("1/8 direction is unambiguous")

    if str(signal.get("strategy_master", "")).strip() != "Exness Indie":
        raise ValueError("Pre-entry check 2/8 failed: signal is not tagged as Exness Indie master.")
    checks.append("2/8 Exness Indie is the strategy master")

    try:
        bar_time = pd.Timestamp(signal.get("bar_time"))
        if bar_time.tzinfo is None:
            bar_time = bar_time.tz_localize("UTC")
        else:
            bar_time = bar_time.tz_convert("UTC")
        age_seconds = (datetime.now(UTC) - bar_time.to_pydatetime()).total_seconds()
    except Exception as exc:
        raise ValueError(f"Pre-entry check 3/8 failed: invalid signal-candle timestamp ({exc}).") from exc
    # Candle timestamp is the M1 candle open time; allow the candle duration and
    # normal processing latency, but reject a setup delayed by a long outage.
    if age_seconds < -5 or age_seconds > 180:
        raise ValueError(
            f"Pre-entry check 3/8 failed: completed M1 setup is stale/future "
            f"(age={age_seconds:.1f}s; maximum=180s)."
        )
    checks.append(f"3/8 completed M1 signal is fresh ({age_seconds:.0f}s)")

    try:
        high = float(signal["setup_high"])
        low = float(signal["setup_low"])
        entry50 = float(signal["entry"])
        entry20 = float(signal["secondary_entry_20"])
        sl = float(signal["sl"])
        tp = float(signal["tp"])
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError(f"Pre-entry check 4/8 failed: required master price is missing ({exc}).") from exc
    if not all(math.isfinite(v) and v > 0 for v in (high, low, entry50, entry20, sl, tp)) or high <= low:
        raise ValueError("Pre-entry check 4/8 failed: price levels are non-finite or candle range is invalid.")
    tol = max(1e-8, abs(entry50) * 1e-10)
    expected50 = (high + low) / 2.0
    candle_range = high - low
    expected20 = high - candle_range * 0.20 if side == "buy" else low + candle_range * 0.20
    if abs(entry50 - expected50) > tol:
        raise ValueError(f"Pre-entry check 4/8 failed: Entry 1 is not the exact 50% midpoint ({entry50} vs {expected50}).")
    if abs(entry20 - expected20) > tol:
        raise ValueError(f"Pre-entry check 4/8 failed: Entry 2 is not the exact Indie 20% level ({entry20} vs {expected20}).")
    checks.append("4/8 Entry 1=50% midpoint and Entry 2=Indie 20% retracement")

    if side == "buy":
        if not sl < entry50 < tp:
            raise ValueError("Pre-entry check 5/8 failed: BUY master SL/TP geometry is invalid.")
        if not entry20 > entry50:
            raise ValueError("Pre-entry check 5/8 failed: BUY 20% level must be above the midpoint.")
    else:
        if not tp < entry50 < sl:
            raise ValueError("Pre-entry check 5/8 failed: SELL master SL/TP geometry is invalid.")
        if not entry20 < entry50:
            raise ValueError("Pre-entry check 5/8 failed: SELL 20% level must be below the midpoint.")
    checks.append("5/8 shared master SL/TP geometry is valid")

    legs = signal.get("entry_legs") or []
    allowed_names = {"MIDPOINT_50", "SECONDARY_20"}
    if not 1 <= len(legs) <= 2:
        raise ValueError(f"Pre-entry check 6/8 failed: expected only 1 or 2 entry legs, got {len(legs)}.")
    names = [str(leg.get("leg", "")).upper() for leg in legs]
    if any(name not in allowed_names for name in names) or len(set(names)) != len(names) or "MIDPOINT_50" not in names:
        raise ValueError(f"Pre-entry check 6/8 failed: only Entry 1 (50%) and optional Entry 2 (20%) are permitted; got {names}.")
    for leg in legs:
        if str(leg.get("sl_text")) != str(signal.get("sl_text")) or str(leg.get("tp_text")) != str(signal.get("tp_text")):
            raise ValueError("Pre-entry check 6/8 failed: legs do not share the master SL and TP.")
        if str(leg.get("order_type", "")).lower() not in {"limit", "stop"}:
            raise ValueError("Pre-entry check 6/8 failed: unsupported pending order type.")
    checks.append("6/8 only Entry 1/Entry 2 legs; shared SL/TP; pending orders only")

    try:
        total_volume = sum(float(dec(leg.get("volume_text", "0"))) for leg in legs)
        risk_cash = float(signal.get("risk_cash", 0.0))
        risk_budget = float(signal.get("risk_budget_cash", 0.0))
        midpoint_risk_per_lot = dec(
            signal.get("midpoint_risk_per_lot") or signal.get("risk_per_one_lot") or "0"
        )
        secondary_risk_per_lot = dec(signal.get("secondary_risk_per_lot") or "0")
        expected_group_risk = Decimal("0")
        for leg in legs:
            leg_name = str(leg.get("leg", "")).upper()
            leg_volume = dec(leg.get("volume_text", "0"))
            if leg_name == "MIDPOINT_50":
                expected_group_risk += leg_volume * midpoint_risk_per_lot
            elif leg_name == "SECONDARY_20":
                expected_group_risk += leg_volume * secondary_risk_per_lot
            else:
                raise ValueError("Unsupported entry leg in risk check: " + repr(leg_name))
    except Exception as exc:
        raise ValueError(f"Pre-entry check 7/8 failed: volume/risk data invalid ({exc}).") from exc
    if total_volume <= 0 or not math.isfinite(total_volume) or risk_cash <= 0 or risk_budget <= 0:
        raise ValueError("Pre-entry check 7/8 failed: total volume or risk budget is invalid.")
    if abs(float(expected_group_risk) - risk_cash) > 0.02:
        raise ValueError(
            "Pre-entry check 7/8 failed: declared risk does not equal the actual per-leg risk ($" +
            format(float(expected_group_risk), ".2f") + ")."
        )
    if float(expected_group_risk) > risk_budget + max(0.01, risk_budget * 1e-6):
        raise ValueError(
            "Pre-entry check 7/8 failed: actual combined leg risk $" +
            format(float(expected_group_risk), ".2f") + " exceeds budget $" + format(risk_budget, ".2f") + "."
        )
    checks.append(f"7/8 lot and planned risk within budget (${risk_cash:.2f}/${risk_budget:.2f})")

    if str(signal.get("execution_quote_basis", "")).strip() != "BUY pending/entry Ask; SELL pending/entry Bid; BUY exits Bid; SELL exits Ask":
        raise ValueError("Pre-entry check 8/8 failed: broker execution-side mapping is not explicit.")
    checks.append("8/8 executable Bid/Ask side mapping confirmed; no market-order fallback")
    logging.info("PRE-ENTRY CHECKLIST PASS | %s | %s", side.upper(), " | ".join(checks))
    return checks



# ---------- Adaptive hybrid trailing manager ----------
TRAILING_TIMEFRAME = "M1"
TRAILING_CONFIRMATION_CANDLES = 3
TRAILING_ATR_PERIOD = 14
TRAILING_EMA_FAST = 9
TRAILING_EMA_SLOW = 21
TRAILING_ADX_PERIOD = 14
TRAILING_STRONG_ADX = 25.0
TRAILING_STRONG_ATR_MULTIPLIER = 1.5
TRAILING_WEAK_ATR_MULTIPLIER = 1.0
TRAILING_ACTIVATION_R = 1.0
TRAILING_STRUCTURE_R = 1.4
TRAILING_BE_TP_PROGRESS = 0.0  # Indie has no separate 70% TP-progress trigger
TRAILING_LOCK30_TP_PROGRESS = 0.85
TRAILING_LOCK60_TP_PROGRESS = 0.95


def _trailing_indicators(frame: pd.DataFrame) -> dict:
    """Calculate Wilder ATR/ADX and EMA values from completed candles only."""
    high = frame["high"].astype(float)
    low = frame["low"].astype(float)
    close = frame["close"].astype(float)
    prev_close = close.shift(1)
    tr = pd.concat([(high - low), (high - prev_close).abs(), (low - prev_close).abs()], axis=1).max(axis=1)
    atr = _indie_rma(tr, TRAILING_ATR_PERIOD)

    up = high.diff()
    down = -low.diff()
    plus_dm = pd.Series(0.0, index=frame.index)
    minus_dm = pd.Series(0.0, index=frame.index)
    plus_dm[(up > down) & (up > 0)] = up[(up > down) & (up > 0)]
    minus_dm[(down > up) & (down > 0)] = down[(down > up) & (down > 0)]
    safe_atr = atr.replace(0, float("nan"))
    plus_di = 100.0 * _indie_rma(plus_dm, TRAILING_ADX_PERIOD) / safe_atr
    minus_di = 100.0 * _indie_rma(minus_dm, TRAILING_ADX_PERIOD) / safe_atr
    denom = (plus_di + minus_di).replace(0, float("nan"))
    dx = 100.0 * (plus_di - minus_di).abs() / denom
    adx = _indie_rma(dx, TRAILING_ADX_PERIOD)
    ema_fast = ema(close, TRAILING_EMA_FAST)
    ema_slow = ema(close, TRAILING_EMA_SLOW)
    return {
        "atr": float(atr.iloc[-1]),
        "adx": float(adx.iloc[-1]),
        "plus_di": float(plus_di.iloc[-1]),
        "minus_di": float(minus_di.iloc[-1]),
        "ema_fast": float(ema_fast.iloc[-1]),
        "ema_slow": float(ema_slow.iloc[-1]),
    }


def _confirmed_swing(frame: pd.DataFrame, side: str, lookback: int = 80) -> tuple[float | None, int | None]:
    """Return latest 2-left/2-right confirmed pivot; never uses a live candle."""
    start = max(2, len(frame) - lookback)
    end = len(frame) - 2  # two completed right-side candles are required
    found = []
    for i in range(start, end):
        if side == "buy":
            value = float(frame.iloc[i]["low"])
            left = frame.iloc[i-2:i]["low"].astype(float)
            right = frame.iloc[i+1:i+3]["low"].astype(float)
            if value < float(left.min()) and value <= float(right.min()):
                found.append((value, i))
        else:
            value = float(frame.iloc[i]["high"])
            left = frame.iloc[i-2:i]["high"].astype(float)
            right = frame.iloc[i+1:i+3]["high"].astype(float)
            if value > float(left.max()) and value >= float(right.max()):
                found.append((value, i))
    return found[-1] if found else (None, None)


def _find_position_sltp_order(snapshot: dict, instrument: str, position_id: str) -> dict | None:
    matches = [
        row for row in (snapshot.get("orders", []) or [])
        if str(row.get("instrument", "")).upper() == instrument.upper()
        and str(row.get("order_type", "")).lower() == "sltp"
        and str(row.get("position_id", "")) == str(position_id)
        and str(row.get("state", "")).lower() in {"placed", "pending_new", "pending", "accepted"}
    ]
    return matches[0] if len(matches) == 1 else None


def _trailing_price_text(value: float, digits: int, side: str) -> str:
    """Round a stop conservatively: down for BUY, up for SELL."""
    quantum = Decimal("1").scaleb(-digits)
    raw = dec(value)
    rounding = "ROUND_FLOOR" if side == "buy" else "ROUND_CEILING"
    rounded = raw.quantize(quantum, rounding=rounding)
    return format(rounded, f".{digits}f")



def _commit_pending_reprice(group: dict, leg: dict, target_text: str, signal: dict) -> None:
    leg["entry_text"] = str(target_text)
    leg["entry"] = float(dec(target_text))
    leg["reprice_pending"] = None
    if str(leg.get("leg", "")).upper() == "MIDPOINT_50":
        group["midpoint_entry"] = str(target_text)
    elif str(leg.get("leg", "")).upper() == "SECONDARY_20":
        group["secondary_entry_20"] = str(target_text)
    group["bar_time"] = signal.get("reprice_bar_time") or signal.get("bar_time") or group.get("bar_time")
    group["signal_high"] = signal.get("setup_high", group.get("signal_high"))
    group["signal_low"] = signal.get("setup_low", group.get("signal_low"))


def reprice_pending_group_from_signal(store: StateStore, api: ExnessAPI, snapshot: dict,
                                      signal: dict, conditions: dict, tick: dict | None) -> int:
    """Reprice eligible unfilled entries from a newer valid same-side Indie setup."""
    group = store.get_json("trade_group", {}) or {}
    if not group.get("active") or group.get("active_triggered") or group.get("group_exit_event"):
        return 0
    side = str(group.get("side", "")).lower()
    if str(signal.get("side", "")).lower() != side:
        return 0
    digits = int(conditions.get("point_digits", -1))
    if digits < 0:
        return 0
    prices = {
        "MIDPOINT_50": price_string(signal.get("entry"), digits),
        "SECONDARY_20": price_string(signal.get("secondary_entry_20"), digits),
    }
    mid, second = dec(prices["MIDPOINT_50"]), dec(prices["SECONDARY_20"])
    if (side == "buy" and second <= mid) or (side == "sell" and second >= mid):
        logging.warning("PENDING REPRICE BLOCKED | new Indie 50%%/20%% level geometry is invalid.")
        return 0
    changed = 0
    for leg in group.get("legs", []) or []:
        name = str(leg.get("leg", "")).upper()
        status = str(leg.get("status", "")).lower()
        if name not in prices or status not in {"prepared", "pending", "acknowledged", "awaiting_visibility"}:
            continue
        if leg.get("position_id") or leg.get("reprice_pending"):
            continue
        target = prices[name]
        new_entry, old_entry = dec(target), dec(leg.get("entry_text"))
        sl, tp = dec(group.get("sl_text")), dec(group.get("tp_text"))
        old_risk, new_risk = abs(old_entry-sl), abs(new_entry-sl)
        geometry = (sl < new_entry < tp) if side == "buy" else (tp < new_entry < sl)
        if not geometry or old_risk <= 0 or new_risk > old_risk + Decimal("0.00000001"):
            continue
        if _history_decimal_equal(old_entry, new_entry):
            continue
        if status == "prepared" and not leg.get("order_id"):
            _commit_pending_reprice(group, leg, target, signal)
            changed += 1
            continue
        order_id = str(leg.get("order_id") or "")
        if not order_id or not tick or float(tick.get("age_seconds", 999999)) > 10:
            continue
        order_type = str(leg.get("order_type") or "limit").lower()
        try:
            validate_pending_price_against_quote(side, order_type, target, tick)
        except (ValueError, InvalidOperation):
            continue
        bar_key = re.sub(r"[^0-9]", "", str(signal.get("reprice_bar_time") or signal.get("bar_time") or ""))
        idem = "KS-REPRICE-" + re.sub(r"[^A-Za-z0-9_-]", "", str(group.get("group_id", ""))) + "-" + name + "-" + bar_key
        try:
            ack = api.modify_pending_order(order_id, price_text=target, idem=idem)
        except Exception as exc:
            logging.error("PENDING REPRICE FAILED | order=%s target=%s | %s", order_id, target, str(exc)[:160])
            continue
        leg["reprice_pending"] = {
            "target": target, "operation_id": str(ack.get("operation_id") or "") or None,
            "idempotency_key": idem, "requested_at": utc_iso(datetime.now(UTC)),
            "signal_high": signal.get("setup_high"), "signal_low": signal.get("setup_low"),
            "bar_time": signal.get("reprice_bar_time") or signal.get("bar_time"),
        }
        store.set_json("trade_group", group)
        try:
            fresh = api.snapshot()
            broker = next((o for o in (fresh.get("orders", []) or []) if str(o.get("order_id", "")) == order_id), None)
            if broker and _history_decimal_equal(broker.get("price"), target):
                _commit_pending_reprice(group, leg, target, signal)
                changed += 1
        except Exception:
            pass
    if changed:
        group["last_reprice_bar"] = signal.get("reprice_bar_time") or signal.get("bar_time")
        store.set_json("trade_group", group)
        _sync_group_trade_lock(store, group)
        logging.info("PENDING ENTRY REPRICE CONFIRMED | group=%s | legs=%d", group.get("group_id"), changed)
    else:
        store.set_json("trade_group", group)
    return changed


def reconcile_group_opposite_signal_exit(store: StateStore, api: ExnessAPI,
                                         snapshot: dict, instrument: str) -> bool:
    """Close filled legs and cancel all unfilled siblings on an opposite signal."""
    group = store.get_json("trade_group", {}) or {}
    event = group.get("group_exit_event") or {}
    if not group.get("active") or str(event.get("reason", "")).upper() != "OPPOSITE_SIGNAL":
        return False
    positions = {
        str(p.get("position_id") or p.get("id") or ""): p
        for p in (snapshot.get("positions", []) or [])
        if str(p.get("instrument", p.get("symbol", ""))).upper() == str(instrument).upper()
        and str(p.get("state", "open")).lower() in {"open", "opened"}
    }
    operations = group.get("opposite_close_ops", {}) or {}
    for leg in group.get("legs", []) or []:
        pid = str(leg.get("position_id") or "")
        status = str(leg.get("status", "")).lower()
        if not pid:
            if status in {"prepared", "waiting_for_midpoint_confirmation"} and not leg.get("order_id"):
                leg["status"] = "skipped"
            elif status in {"pending", "acknowledged", "awaiting_visibility", "cancel_requested", "cancel_rejected", "awaiting_order_id_for_cancel"}:
                try:
                    _group_leg_cancel(store, api, group, leg, "OPPOSITE_SIGNAL", float(event.get("exit_reference_price") or event.get("price") or 0.0))
                    leg["estimated_unfilled_pnl"] = None
                except Exception as exc:
                    leg["cancel_error"] = str(exc)
                    logging.error("OPPOSITE EXIT | sibling cancel unresolved: %s", str(exc)[:160])
            continue
        if pid not in positions:
            leg["status"] = "closed"
            leg["closed_at"] = leg.get("closed_at") or utc_iso(datetime.now(UTC))
            continue
        op = operations.get(pid, {}) or {}
        requested = _history_time(op.get("requested_at")) if op else None
        if op.get("operation_id"):
            try:
                status_doc = api.operation_status(str(op["operation_id"]))
                op_state = str(status_doc.get("status", "")).lower()
            except Exception:
                op_state = "processing"
            if op_state in {"confirmed", "completed", "succeeded", "success"}:
                fresh = api.snapshot()
                active_ids = {str(p.get("position_id") or p.get("id") or "") for p in (fresh.get("positions", []) or [])}
                if pid not in active_ids:
                    leg["status"] = "closed"
                    leg["closed_at"] = utc_iso(datetime.now(UTC))
                else:
                    # The operation completed but the position is still in
                    # Exness' active snapshot. Clear this operation ID so a
                    # fresh close can be retried after the cooldown if needed.
                    op["status"] = "awaiting_position_snapshot"
                    op["operation_id"] = None
                    operations[pid] = op
                continue
            if op_state not in {"rejected", "failed"}:
                continue
            op["status"] = "rejected"
            operations[pid] = op
        if op.get("status") in {"requested", "uncertain", "awaiting_position_snapshot"} and requested and (datetime.now(UTC)-requested).total_seconds() < 15:
            continue
        idem = str(op.get("idempotency_key") or ("KS-OPPOSITE-CLOSE-" + re.sub(r"[^A-Za-z0-9_-]", "", pid)))
        retry = int(op.get("retry_count", 0)) + (1 if op.get("status") == "rejected" else 0)
        if retry:
            idem += "-R" + str(retry)
        try:
            ack = api.close_position(pid, idem=idem)
            operations[pid] = {
                "status":"requested", "operation_id":str(ack.get("operation_id") or "") or None,
                "idempotency_key":idem, "requested_at":utc_iso(datetime.now(UTC)), "retry_count":retry,
            }
            logging.warning("OPPOSITE SIGNAL CLOSE REQUESTED | %s position=%s", instrument, pid)
        except Exception as exc:
            operations[pid] = {
                "status":"uncertain", "operation_id":None, "idempotency_key":idem,
                "requested_at":utc_iso(datetime.now(UTC)), "retry_count":retry, "error":str(exc)[:200],
            }
            logging.error("OPPOSITE SIGNAL CLOSE UNCERTAIN | position=%s | %s", pid, str(exc)[:160])
    group["opposite_close_ops"] = operations
    group["state"] = "opposite_signal_exit_pending"
    store.set_json("trade_group", group)
    _sync_group_trade_lock(store, group)
    return True


def _dynamic_tp_structure_candidate(frame: pd.DataFrame, side: str, entry: float,
                                    current_tp: float, point: float) -> tuple[float | None, dict]:
    """Return a farther TP only after strong momentum approaches current TP."""
    if len(frame) < 40:
        return None, {"reason": "waiting for 40 completed M1 candles"}
    metrics = _trailing_indicators(frame)
    atr, adx = metrics.get("atr", float("nan")), metrics.get("adx", float("nan"))
    strong = (
        math.isfinite(adx) and adx >= 25.0 and math.isfinite(atr) and atr > 0
        and ((metrics["plus_di"] > metrics["minus_di"] and metrics["ema_fast"] > metrics["ema_slow"]) if side == "buy"
             else (metrics["minus_di"] > metrics["plus_di"] and metrics["ema_fast"] < metrics["ema_slow"]))
    )
    if not strong:
        return None, {"reason": "strong momentum confirmation absent", **metrics}
    close = float(frame.iloc[-1]["close"])
    distance = abs(current_tp-entry)
    progress = ((close-entry)/distance) if side == "buy" and distance > 0 else ((entry-close)/distance) if distance > 0 else 0.0
    if progress < .80:
        return None, {"reason":"price has not reached 80% of TP distance", "progress":progress, **metrics}
    prior = frame.iloc[-21:-1]
    if len(prior) < 20:
        return None, {"reason":"20-candle structure unavailable", **metrics}
    if side == "buy":
        structure = float(prior["high"].max())
        candidate = structure - atr*.10
        valid = candidate > current_tp + point and candidate > close + atr*.25
    else:
        structure = float(prior["low"].min())
        candidate = structure + atr*.10
        valid = candidate < current_tp - point and candidate < close - atr*.25
    if not valid:
        return None, {"reason":"no farther valid structure target", "progress":progress, "structure":structure, **metrics}
    return candidate, {"reason":"strong momentum and next structure confirmed", "progress":progress, "structure":structure, **metrics}


def _dynamic_target_price_text(value: float, digits: int, side: str) -> str:
    quantum = Decimal("1").scaleb(-digits)
    raw = dec(value)
    rounding = "ROUND_CEILING" if side == "buy" else "ROUND_FLOOR"
    return format(raw.quantize(quantum, rounding=rounding), f".{digits}f")


def run_dynamic_take_profit(store: StateStore, api: ExnessAPI, snapshot: dict,
                            m1: pd.DataFrame, conditions: dict, instrument: str) -> None:
    """Extend the shared TP only with confirmed momentum/structure and verify all broker amendments."""
    group = store.get_json("trade_group", {}) or {}
    if not group.get("active") or not group.get("active_triggered") or m1 is None or m1.empty:
        return
    master = next((x for x in (group.get("legs", []) or []) if str(x.get("leg", "")).upper() == "MIDPOINT_50"), None)
    if not master:
        return
    state = group.get("dynamic_tp_update") or {}
    if state:
        fresh = api.snapshot()
        all_ok = bool(state.get("requests"))
        for req in state.get("requests", []) or []:
            if req.get("confirmed"):
                continue
            if req.get("kind") == "position":
                linked = _find_position_sltp_order(fresh, instrument, str(req.get("position_id") or ""))
                current_value = (linked or {}).get("take_profit_price")
            else:
                order = next((o for o in (fresh.get("orders", []) or []) if str(o.get("order_id", "")) == str(req.get("order_id", ""))), None)
                current_value = (order or {}).get("take_profit_price")
            req["confirmed"] = _history_decimal_equal(current_value, state.get("target_text"))
            if req["confirmed"]:
                req["status"] = "confirmed"
                continue

            op_state = "confirmed"
            if req.get("operation_id"):
                try:
                    doc = api.operation_status(str(req["operation_id"]))
                    op_state = str(doc.get("status", "")).lower()
                except Exception:
                    op_state = "processing"
            if op_state not in {"confirmed", "completed", "succeeded", "success", "rejected", "failed"}:
                all_ok = False
                continue

            # Acknowledgement alone is not success. If the broker has not
            # reflected the target after the cooldown, retry with a fresh
            # idempotency key; never resend while the prior operation is pending.
            requested_at = _history_time(req.get("requested_at"))
            age = (datetime.now(UTC) - requested_at).total_seconds() if requested_at else 999999
            retry_count = int(req.get("retry_count", 0))
            if age >= 15 and retry_count < 3:
                retry_count += 1
                suffix = "-R" + str(retry_count)
                base_idem = str(req.get("idempotency_key") or (
                    "KS-DYNAMIC-TP-" + re.sub(
                        r"[^A-Za-z0-9_-]", "",
                        str(group.get("group_id", "")) + "-" + str(state.get("bar_time", "")) + "-" +
                        str(req.get("position_id") or req.get("order_id"))
                    )
                ))
                idem = base_idem + suffix
                try:
                    if req.get("kind") == "position":
                        ack = api.modify_active_order(str(req["order_id"]), None, idem, take_profit_text=str(state["target_text"]))
                    else:
                        ack = api.modify_pending_order(str(req["order_id"]), idem=idem, take_profit_text=str(state["target_text"]))
                    req["operation_id"] = str(ack.get("operation_id") or "") or None
                    req["idempotency_key"] = base_idem
                    req["requested_at"] = utc_iso(datetime.now(UTC))
                    req["retry_count"] = retry_count
                    req["status"] = "retry_requested"
                except Exception as exc:
                    req["requested_at"] = utc_iso(datetime.now(UTC))
                    req["retry_count"] = retry_count
                    req["status"] = "retry_uncertain"
                    req["error"] = str(exc)[:180]
                    logging.error("DYNAMIC TP RETRY UNCERTAIN | %s | %s", req.get("order_id"), str(exc)[:150])
            all_ok = False
        if all_ok:
            group["tp_text"] = str(state["target_text"])
            for leg in group.get("legs", []) or []:
                leg["tp_text"] = group["tp_text"]
            group["last_dynamic_tp_bar"] = state.get("bar_time")
            group["dynamic_tp_update"] = None
            logging.info("DYNAMIC TP CONFIRMED | group=%s | TP=%s", group.get("group_id"), group["tp_text"])
        else:
            group["dynamic_tp_update"] = state
        store.set_json("trade_group", group)
        _sync_group_trade_lock(store, group)
        return
    bar_time = m1.iloc[-1]["time"].isoformat()
    if group.get("last_dynamic_tp_bar") == bar_time:
        return
    side = str(group.get("side", "")).lower()
    try:
        entry, tp, sl = float(dec(master.get("entry"))), float(dec(group.get("tp_text"))), float(dec(group.get("sl_text")))
        if not ((sl < entry < tp) if side == "buy" else (tp < entry < sl)):
            return
        digits = int(conditions.get("point_digits", -1))
        if digits < 0:
            return
        point = 10.0 ** (-digits)
        candidate, detail = _dynamic_tp_structure_candidate(m1, side, entry, tp, point)
        if candidate is None:
            group["last_dynamic_tp_bar"] = bar_time
            group["last_dynamic_tp_reason"] = detail.get("reason")
            store.set_json("trade_group", group)
            return
        target_text = _dynamic_target_price_text(candidate, digits, side)
        target = float(dec(target_text))
        if (side == "buy" and target <= tp + point) or (side == "sell" and target >= tp - point):
            return
        positions = {str(p.get("position_id") or ""):p for p in (snapshot.get("positions",[]) or []) if str(p.get("instrument",p.get("symbol",""))).upper()==instrument.upper()}
        orders = {str(o.get("order_id") or ""):o for o in (snapshot.get("orders",[]) or []) if str(o.get("instrument",o.get("symbol",""))).upper()==instrument.upper()}
        requests=[]
        for leg in group.get("legs",[]) or []:
            pid, oid = str(leg.get("position_id") or ""), str(leg.get("order_id") or "")
            if pid and pid in positions:
                sltp = _find_position_sltp_order(snapshot, instrument, pid)
                if sltp and sltp.get("order_id"):
                    requests.append({"kind":"position","position_id":pid,"order_id":str(sltp["order_id"])})
            elif oid and oid in orders and str(leg.get("status","")).lower() in {"pending","acknowledged","awaiting_visibility"}:
                requests.append({"kind":"pending","order_id":oid})
        if not requests:
            group["last_dynamic_tp_bar"]=bar_time
            store.set_json("trade_group",group)
            return
        state={"target_text":target_text,"bar_time":bar_time,"detail":detail,"requests":requests}
        group["dynamic_tp_update"]=state
        store.set_json("trade_group",group)
        for req in requests:
            idem="KS-DYNAMIC-TP-"+re.sub(r"[^A-Za-z0-9_-]","",str(group.get("group_id",""))+"-"+bar_time)+"-"+re.sub(r"[^A-Za-z0-9_-]","",str(req.get("position_id") or req.get("order_id")))
            try:
                if req["kind"]=="position":
                    ack=api.modify_active_order(req["order_id"],None,idem,take_profit_text=target_text)
                else:
                    ack=api.modify_pending_order(req["order_id"],idem=idem,take_profit_text=target_text)
                req["operation_id"]=str(ack.get("operation_id") or "") or None
                req["idempotency_key"]=idem
                req["retry_count"]=int(req.get("retry_count",0))
                req["requested_at"]=utc_iso(datetime.now(UTC))
                req["status"]="requested"
            except Exception as exc:
                req["status"]="rejected"
                req["idempotency_key"]=idem
                req["requested_at"]=utc_iso(datetime.now(UTC))
                req["retry_count"]=int(req.get("retry_count",0))
                req["error"]=str(exc)[:200]
                logging.error("DYNAMIC TP PATCH FAILED | order=%s | %s",req.get("order_id"),str(exc)[:140])
        store.set_json("trade_group",group)
        fresh=api.snapshot()
        for req in requests:
            if req.get("operation_id"):
                try:
                    result=api.operation_status(str(req["operation_id"]))
                    if str(result.get("status","")).lower() not in {"confirmed","completed","succeeded","success"}:
                        continue
                except Exception:
                    continue
            if req["kind"]=="position":
                sltp=_find_position_sltp_order(fresh,instrument,req["position_id"])
                val=(sltp or {}).get("take_profit_price")
            else:
                order=next((o for o in (fresh.get("orders",[]) or []) if str(o.get("order_id",""))==req["order_id"]),None)
                val=(order or {}).get("take_profit_price")
            req["confirmed"]=_history_decimal_equal(val,target_text)
        if requests and all(x.get("confirmed") for x in requests):
            group["tp_text"]=target_text
            for leg in group.get("legs",[]) or []:
                leg["tp_text"]=target_text
            group["last_dynamic_tp_bar"]=bar_time
            group["dynamic_tp_update"]=None
            logging.info("DYNAMIC TP EXTENDED | group=%s | TP=%s",group.get("group_id"),target_text)
        store.set_json("trade_group",group)
        _sync_group_trade_lock(store,group)
    except Exception as exc:
        logging.error("DYNAMIC TP MANAGER PAUSED | group=%s | %s",group.get("group_id"),str(exc)[:180])


def _trailing_candidate(frame: pd.DataFrame, side: str, entry: float, initial_sl: float,                        current_sl: float, tp: float, point: float,
                        position_open_time: str | None = None,
                        trailing_state: dict | None = None) -> tuple[float | None, dict]:
    """Mirror the supplied Indie indicator's M1 adaptive trailing state machine.

    Trigger levels use the best favourable high/low since entry. A proposed
    level is then confirmed by three consecutive completed candle closes that
    remain beyond that level. The caller persists trailing_state between bars.
    """
    state = trailing_state if trailing_state is not None else {}
    cols = ("open", "high", "low", "close")
    if not all(col in frame.columns for col in cols):
        return None, {"reason": "required M1 OHLC data unavailable"}
    work = frame.copy().reset_index(drop=True)
    for col in cols:
        work[col] = pd.to_numeric(work[col], errors="coerce")
    work = work.dropna(subset=list(cols)).reset_index(drop=True)
    if "time" not in work.columns or not position_open_time:
        return None, {"reason": "position creation time unavailable; cannot identify post-entry candles"}
    try:
        opened_at = pd.to_datetime(position_open_time, utc=True)
        work["time"] = pd.to_datetime(work["time"], utc=True)
    except Exception:
        return None, {"reason": "invalid position creation timestamp"}
    # Indie starts adaptive trailing only on a candle after the entry/fill
    # candle (bar_index > last_entry_bar). Exness create_time can be inside
    # that candle, so exclude the entire fill minute.
    fill_bar_open = opened_at.floor("min")
    post_open = work[work["time"] > fill_bar_open]
    if post_open.empty:
        return None, {"reason": "waiting for first completed M1 candle after the fill candle", "post_entry_candles": 0}

    initial_risk = abs(entry - initial_sl)
    target_distance = abs(tp - entry)
    if initial_risk <= 0 or target_distance <= 0:
        return None, {"reason": "invalid original risk or TP distance"}

    # Indie tracks the best excursion, not the minimum of the last three closes.
    if side == "buy":
        extreme = float(post_open["high"].max())
        old_extreme = state.get("favorable_extreme")
        if old_extreme not in (None, ""):
            extreme = max(extreme, float(old_extreme))
        state["favorable_extreme"] = str(extreme)
        favourable_move = extreme - entry
    else:
        extreme = float(post_open["low"].min())
        old_extreme = state.get("favorable_extreme")
        if old_extreme not in (None, ""):
            extreme = min(extreme, float(old_extreme))
        state["favorable_extreme"] = str(extreme)
        favourable_move = entry - extreme

    r_progress = favourable_move / initial_risk
    tp_progress = favourable_move / target_distance
    close = float(work.iloc[-1]["close"])
    proposed_sl = current_sl

    # Exact Indie thresholds: +1R break-even (buffer defaults to zero).
    if r_progress >= 1.0:
        proposed_sl = max(proposed_sl, entry) if side == "buy" else min(proposed_sl, entry)

    # Profit locks are percentages of the original TP distance.
    if tp_progress >= 0.95:
        locked = 0.60 * initial_risk
        proposed_sl = max(proposed_sl, entry + locked) if side == "buy" else min(proposed_sl, entry - locked)
    elif tp_progress >= 0.85:
        locked = 0.30 * initial_risk
        proposed_sl = max(proposed_sl, entry + locked) if side == "buy" else min(proposed_sl, entry - locked)

    metrics = _trailing_indicators(work)
    atr = metrics.get("atr", float("nan"))
    adx = metrics.get("adx", float("nan"))
    structure_details = {"atr": atr, "adx": adx, **metrics}

    # Match Indie: structure/reaction trailing starts at +1.4R and uses the
    # five-candle pivot centred two completed candles ago.
    if r_progress >= 1.4 and math.isfinite(atr) and atr > 0:
        strong = (
            math.isfinite(adx) and adx >= 25.0
            and ((metrics["plus_di"] > metrics["minus_di"] and metrics["ema_fast"] > metrics["ema_slow"]) if side == "buy"
                 else (metrics["minus_di"] > metrics["plus_di"] and metrics["ema_fast"] < metrics["ema_slow"]))
        )
        atr_buffer = atr * (1.5 if strong else 1.0)
        if len(work) >= 5:
            w = work.iloc[-5:].reset_index(drop=True)
            if side == "buy":
                pivot = float(w.iloc[2]["low"])
                confirmed_pivot = (pivot < float(w.iloc[1]["low"]) and pivot < float(w.iloc[3]["low"])
                                   and pivot <= float(w.iloc[0]["low"]) and pivot <= float(w.iloc[4]["low"]))
                if confirmed_pivot:
                    swing_candidate = pivot - atr_buffer
                    if swing_candidate > proposed_sl and swing_candidate < close:
                        proposed_sl = max(proposed_sl, swing_candidate)
                bearish_three = (float(w.iloc[4]["close"]) < float(w.iloc[3]["close"]) < float(w.iloc[2]["close"])
                                 and float(w.iloc[4]["close"]) < metrics["ema_fast"])
                if bearish_three:
                    reaction_candidate = float(w["low"].tail(3).min()) - atr
                    if reaction_candidate > proposed_sl and reaction_candidate < close:
                        proposed_sl = max(proposed_sl, reaction_candidate)
            else:
                pivot = float(w.iloc[2]["high"])
                confirmed_pivot = (pivot > float(w.iloc[1]["high"]) and pivot > float(w.iloc[3]["high"])
                                   and pivot >= float(w.iloc[0]["high"]) and pivot >= float(w.iloc[4]["high"]))
                if confirmed_pivot:
                    swing_candidate = pivot + atr_buffer
                    if swing_candidate < proposed_sl and swing_candidate > close:
                        proposed_sl = min(proposed_sl, swing_candidate)
                bullish_three = (float(w.iloc[4]["close"]) > float(w.iloc[3]["close"]) > float(w.iloc[2]["close"])
                                 and float(w.iloc[4]["close"]) > metrics["ema_fast"])
                if bullish_three:
                    reaction_candidate = float(w["high"].tail(3).max()) + atr
                    if reaction_candidate < proposed_sl and reaction_candidate > close:
                        proposed_sl = min(proposed_sl, reaction_candidate)

    # Candidate validity and confirmation mirror the Indie series logic.
    candidate_valid = (proposed_sl > current_sl and proposed_sl < close) if side == "buy" else (proposed_sl < current_sl and proposed_sl > close)
    candidate_raw = state.get("trail_candidate")
    candidate = float(candidate_raw) if candidate_raw not in (None, "") else None
    confirm_count = int(state.get("trail_confirm_count", 0) or 0)
    if candidate_valid:
        if candidate is None or (proposed_sl > candidate if side == "buy" else proposed_sl < candidate):
            candidate = proposed_sl
            confirm_count = 0

    if candidate is not None:
        still_safe = close > candidate if side == "buy" else close < candidate
        if still_safe:
            confirm_count += 1
        else:
            candidate = None
            confirm_count = 0

    state["trail_candidate"] = str(candidate) if candidate is not None else ""
    state["trail_confirm_count"] = confirm_count
    info = {**structure_details, "r": r_progress, "tp_progress": tp_progress,
            "favorable_extreme": extreme, "candidate": candidate,
            "confirmation_count": confirm_count}
    if candidate is not None and confirm_count >= 3 and (candidate > current_sl if side == "buy" else candidate < current_sl):
        state["trail_candidate"] = ""
        state["trail_confirm_count"] = 0
        stage = "lock_60_percent" if tp_progress >= .95 else "lock_30_percent" if tp_progress >= .85 else "break_even" if r_progress >= 1.0 else "structure_trailing"
        info.update({"reason": "Indie candidate confirmed", "stages": [stage]})
        return candidate, info

    reason = "waiting for three consecutive safe completed M1 closes" if candidate is not None else "no valid more-protective Indie trailing candidate"
    info["reason"] = reason
    return None, info


def _trail_state_key(position_id: str, group_id: str | None = None) -> str:
    # One confirmation counter/extreme/candidate for the entire 50% master group.
    # Legacy trades without a group ID retain their position-scoped state.
    return ("adaptive_trailing_group_state:" + str(group_id)) if group_id else ("adaptive_trailing_state:" + str(position_id))


def _trail_pending_key(position_id: str) -> str:
    return "trailing_pending_operation:" + str(position_id)


def _confirm_trailing_operation(store: StateStore, api: ExnessAPI, snapshot: dict, pending: dict) -> bool:
    """Resolve one position's pending SL modification without cross-leg state."""
    target = str(pending.get("candidate_sl", ""))
    order_id = str(pending.get("order_id", ""))
    position_id = str(pending.get("position_id", ""))
    operation_id = str(pending.get("operation_id") or "")
    state_key = _trail_state_key(position_id, pending.get("group_id"))
    pending_key = _trail_pending_key(position_id)
    trailing = store.get_json(state_key, {}) or {}
    if operation_id:
        status_doc = api.operation_status(operation_id)
        state = str(status_doc.get("status", "")).lower()
        if state in {"rejected", "failed"}:
            logging.error("Exness rejected the protective SL update for position %s; its previous SL remains active.", position_id)
            rejected = trailing.get("rejected_sl_by_position", {}) or {}
            rejected[position_id] = target
            trailing["rejected_sl_by_position"] = rejected
            store.set_json(state_key, trailing)
            store.set_json(pending_key, {})
            return True
        if state not in {"confirmed", "completed", "succeeded", "success"}:
            logging.info("Position %s SL update is still processing; no duplicate PATCH will be sent.", position_id)
            return False
    orders = snapshot.get("orders", []) or []
    matched = [o for o in orders if str(o.get("order_id", "")) == order_id and str(o.get("position_id", "")) == position_id]
    if len(matched) == 1 and _history_decimal_equal(matched[0].get("stop_loss_price"), target):
        trailing.update({"position_id": position_id, "current_sl": target,
                         "last_confirmed_at": utc_iso(datetime.now(UTC)),
                         "last_confirmed_bar": pending.get("bar_time"),
                         "last_stage": pending.get("stage")})
        store.set_json(state_key, trailing)
        store.set_json(pending_key, {})
        logging.info("STOP LOSS UPDATED: position %s now has confirmed SL %s.", position_id, target)
        return True
    logging.info("Exness is processing the SL update for position %s; waiting for snapshot confirmation.", position_id)
    return False


def _run_adaptive_trailing_for_position(store: StateStore, api: ExnessAPI, snapshot: dict,
                                       position: dict, m1: pd.DataFrame, conditions: dict,
                                       instrument: str, group: dict) -> None:
    position_id = str(position.get("position_id", ""))
    side = str(position.get("direction", "")).lower()
    if side not in {"buy", "sell"} or not position_id:
        logging.error("STOP MANAGER PAUSED: Exness did not provide a clear ID/direction for one group position.")
        return
    leg = next((x for x in group.get("legs", []) if str(x.get("position_id", "")) == position_id), None)
    if not leg:
        logging.warning("Stop management skipped: position %s is not mapped to this bot's saved signal group.", position_id)
        return
    sltp = _find_position_sltp_order(snapshot, instrument, position_id)
    if not sltp or not sltp.get("order_id") or sltp.get("stop_loss_price") in (None, ""):
        logging.error("STOP MANAGER PAUSED: Exness did not show one clear active SLTP order for position %s.", position_id)
        return
    group_id = str(group.get("group_id") or "")
    state_key = _trail_state_key(position_id, group_id or None)
    pending_key = _trail_pending_key(position_id)
    pending_op = store.get_json(pending_key, {}) or {}
    if pending_op:
        _confirm_trailing_operation(store, api, snapshot, pending_op)
        if store.get_json(pending_key, {}) or {}:
            return
    trailing = store.get_json(state_key, {}) or {}
    if not trailing:
        trailing = {"group_id": group_id or None, "initialized_at": utc_iso(datetime.now(UTC))}
        store.set_json(state_key, trailing)

    current_sl = float(dec(sltp["stop_loss_price"]))
    # The 50% midpoint leg is the master reference for the entire signal group.
    # Both the 50% and optional 20% positions therefore calculate the same
    # protective level from the planned 50% entry, not from each leg's fill.
    master_leg = next(
        (item for item in group.get("legs", []) if str(item.get("leg", "")).upper() == "MIDPOINT_50"),
        None,
    )
    if not master_leg or master_leg.get("entry") in (None, ""):
        logging.error("STOP MANAGER PAUSED: the signal group has no valid 50%% master entry.")
        return
    master_entry = float(dec(master_leg["entry"]))
    master_position_id = str(master_leg.get("position_id") or "")
    master_position = next(
        (item for item in (snapshot.get("positions", []) or [])
         if str(item.get("position_id", "")) == master_position_id
         and str(item.get("state", "")).lower() in {"open", "opened"}),
        None,
    )
    master_position_open_time = (master_position or {}).get("create_time")
    if not master_position_open_time:
        logging.error("STOP MANAGER PAUSED: the primary midpoint fill time is unavailable; cannot reproduce Indie trailing start bar.")
        return
    current_tp_raw = group.get("tp_text") or sltp.get("take_profit_price") or trailing.get("initial_tp") or leg.get("tp_text")
    if current_tp_raw in (None, ""):
        logging.error("STOP MANAGER PAUSED: TP is unavailable for position %s.", position_id)
        return
    tp = float(dec(current_tp_raw))
    # Use the planned 50% midpoint as the shared R/trailing reference even
    # when only the 20% leg has filled so far.
    entry = master_entry
    initial_sl_raw = trailing.get("initial_sl") or group.get("sl_text") or leg.get("sl_text") or sltp.get("stop_loss_price")
    initial_sl = float(dec(initial_sl_raw))
    if not ((initial_sl < entry < tp) if side == "buy" else (tp < entry < initial_sl)):
        logging.error("STOP MANAGER PAUSED: Position %s has invalid entry/SL/TP geometry.", position_id)
        return
    trailing.setdefault("initial_sl", str(initial_sl))
    trailing.setdefault("initial_tp", str(tp))
    trailing.setdefault("entry", str(entry))
    bar_time = m1.iloc[-1]["time"].isoformat()
    # Evaluate the master trailing state once per completed M1 candle. Every
    # filled leg then consumes the same confirmed candidate on that candle.
    already_evaluated = trailing.get("last_evaluated_bar") == bar_time
    if already_evaluated:
        shared_candidate = trailing.get("confirmed_candidate_sl")
        if trailing.get("confirmed_candidate_bar") != bar_time or shared_candidate in (None, ""):
            return
        candidate = float(dec(shared_candidate))
        info = {"reason": "shared 50% master candidate already confirmed for this M1 candle",
                "stages": trailing.get("confirmed_candidate_stages", ["shared_master_trailing"])}
    else:
        trailing["last_evaluated_bar"] = bar_time
    digits = int(conditions.get("point_digits", -1))
    if digits < 0:
        logging.error("STOP MANAGER PAUSED: Exness price precision is unavailable.")
        return
    point = 10.0 ** (-digits)
    if not already_evaluated:
        # SELL positions are marked/closed against ASK. Use the ASK OHLC series
        # for all SELL trailing calculations; pause safely if it is absent.
        # Original Indie trailing uses its chart OHLC (Bid) for both sides.
        # Keep the same candle frame for BUY and SELL so trailing stages,
        # favorable excursion, swing levels, and close confirmation align.
        trailing_frame = m1
        # The favorable excursion and three-close confirmation are shared by
        # the signal group, not restarted or incremented once per position.
        candidate, info = _trailing_candidate(
            trailing_frame, side, entry, initial_sl, current_sl, tp, point,
            position_open_time=master_position_open_time, trailing_state=trailing,
        )
        if candidate is not None:
            trailing["confirmed_candidate_sl"] = str(candidate)
            trailing["confirmed_candidate_bar"] = bar_time
            trailing["confirmed_candidate_stages"] = info.get("stages", ["shared_master_trailing"])
    store.set_json(state_key, trailing)
    if candidate is None:
        logging.debug("Position %s: shared master protective SL unchanged (%s).", position_id, info.get("reason"))
        return
    candidate_text = _trailing_price_text(candidate, digits, side)
    rejected_for_position = (trailing.get("rejected_sl_by_position", {}) or {}).get(position_id, "")
    if str(rejected_for_position) == candidate_text:
        return
    candidate_rounded = float(candidate_text)
    if (side == "buy" and candidate_rounded <= current_sl) or (side == "sell" and candidate_rounded >= current_sl):
        return
    idem = "KST-TRAIL-" + uuid.uuid4().hex
    pending = {
        "status": "prepared", "position_id": position_id, "order_id": str(sltp["order_id"]),
        "candidate_sl": candidate_text, "previous_sl": str(sltp.get("stop_loss_price")),
        "operation_id": None, "idempotency_key": idem, "bar_time": bar_time,
        "stage": ",".join(info.get("stages", [])), "group_id": group_id or None,
        "created_at": utc_iso(datetime.now(UTC)),
    }
    store.set_json(pending_key, pending)
    try:
        ack = api.modify_active_order(str(sltp["order_id"]), candidate_text, idem)
    except APIHTTPError as exc:
        rejected = trailing.get("rejected_sl_by_position", {}) or {}
        rejected[position_id] = candidate_text
        trailing["rejected_sl_by_position"] = rejected
        store.set_json(state_key, trailing)
        store.set_json(pending_key, {})
        logging.error("Exness declined the SL update for position %s (HTTP %s).", position_id, exc.status_code)
        return
    except (UncertainPostError, Exception) as exc:
        pending["status"] = "uncertain"
        pending["error"] = str(exc)
        store.set_json(pending_key, pending)
        logging.error("Position %s SL update outcome uncertain; no duplicate PATCH will be sent.", position_id)
        logging.debug("Position SL update detail:", exc_info=True)
        return
    operation_id = ack.get("operation_id")
    pending.update({"status": "acknowledged", "operation_id": str(operation_id) if operation_id else None, "ack": ack})
    store.set_json(pending_key, pending)
    logging.info("POSITION %s SL UPDATE: %s -> %s; waiting for Exness confirmation.", position_id, current_sl, candidate_text)
    if not operation_id:
        return
    deadline = time.time() + 15
    while time.time() < deadline:
        try:
            status_doc = api.operation_status(str(operation_id))
        except Exception:
            return
        op_state = str(status_doc.get("status", "")).lower()
        if op_state in {"rejected", "failed"}:
            rejected = trailing.get("rejected_sl_by_position", {}) or {}
            rejected[position_id] = candidate_text
            trailing["rejected_sl_by_position"] = rejected
            store.set_json(state_key, trailing)
            store.set_json(pending_key, {})
            return
        if op_state in {"confirmed", "completed", "succeeded", "success"}:
            fresh = api.snapshot()
            _confirm_trailing_operation(store, api, fresh, pending)
            return
        time.sleep(1)


def run_adaptive_trailing(store: StateStore, api: ExnessAPI, snapshot: dict, m1: pd.DataFrame,
                          conditions: dict, instrument: str) -> None:
    """Apply one 50%-midpoint-referenced trailing model to every filled group leg.

    Each broker position receives its own Exness SL modification request, but
    the risk distance, R progress, TP progress, and candidate level are all
    calculated from the group's 50% master entry. The optional 20% leg never
    creates a separate trailing reference.
    """
    positions = [p for p in (snapshot.get("positions", []) or [])
                 if str(p.get("instrument", "")).upper() == instrument.upper()
                 and str(p.get("state", "")).lower() in {"open", "opened"}]
    if not positions:
        return
    group = store.get_json("trade_group", {}) or {}
    if group.get("active"):
        # Indie gates the master trailing manager on Entry 1 (the 50% midpoint)
        # being active. A secondary-only 20% fill must not start trailing.
        primary_leg = next((leg for leg in group.get("legs", [])
                           if str(leg.get("leg", "")).upper() == "MIDPOINT_50"), None)
        primary_position_id = str((primary_leg or {}).get("position_id") or "")
        primary_is_open = bool(primary_position_id) and any(
            str(p.get("position_id", "")) == primary_position_id for p in positions
        )
        if not primary_is_open:
            logging.debug("INDIE TRAILING GATE: Entry 1 midpoint position is not open; secondary-only leg will not activate master trailing.")
            return
        mapped = {str(leg.get("position_id")) for leg in group.get("legs", []) if leg.get("position_id")}
        for position in positions:
            if str(position.get("position_id", "")) in mapped:
                _run_adaptive_trailing_for_position(store, api, snapshot, position, m1, conditions, instrument, group)
        unmanaged = [str(p.get("position_id", "")) for p in positions if str(p.get("position_id", "")) not in mapped]
        if unmanaged:
            logging.warning("STOP MANAGER: Ignoring positions not mapped to this signal group: %s", ", ".join(unmanaged))
        return
    # Legacy single-position lock remains supported for existing pre-upgrade trades.
    lock = store.get_json("trade_lock", {}) or {}
    legacy_id = str(lock.get("position_id") or "")
    matching = [p for p in positions if legacy_id and str(p.get("position_id", "")) == legacy_id]
    if len(matching) == 1:
        legacy_group = {"legs": [{"position_id": legacy_id, "entry_text": lock.get("entry"),
                                 "sl_text": lock.get("sl"), "tp_text": lock.get("tp"),
                                 "volume_text": lock.get("volume"), "leg": "LEGACY"}]}
        _run_adaptive_trailing_for_position(store, api, snapshot, matching[0], m1, conditions, instrument, legacy_group)


def instrument_activity(snapshot: dict, instrument: str) -> tuple[list, list]:
    """Return matching active orders and open positions from an account snapshot."""
    orders = snapshot.get("orders", []) or []
    positions = snapshot.get("positions", []) or []
    active_orders = [
        o for o in orders
        if str(o.get("instrument", "")).upper() == instrument.upper()
        and str(o.get("state", "")).lower() in {"placed", "pending_new", "pending", "accepted"}
    ]
    open_positions = [
        p for p in positions
        if str(p.get("instrument", "")).upper() == instrument.upper()
        and str(p.get("state", "")).lower() in {"open", "opened"}
    ]
    return active_orders, open_positions


def _history_orders(history: dict) -> list[dict]:
    rows = history.get("items", []) or []
    return [row.get("order", row) for row in rows if isinstance(row, dict)]


def _history_deals(history: dict) -> list[dict]:
    rows = history.get("items", []) or []
    return [row.get("deal", row) for row in rows if isinstance(row, dict)]


def _deal_money_amount(value: Any) -> Decimal:
    """Read a broker monetary field represented as a scalar or {amount: ...}."""
    if isinstance(value, dict):
        value = value.get("amount")
    if value in (None, ""):
        return Decimal("0")
    try:
        return dec(value)
    except Exception:
        return Decimal("0")


def _position_realized_pnl(deals: list[dict], position_id: str) -> Decimal:
    """Net all available broker deal money fields for one completed position."""
    total = Decimal("0")
    for deal in deals:
        if str(deal.get("position_id", "")) != str(position_id):
            continue
        total += _deal_money_amount(deal.get("profit"))
        total += _deal_money_amount(deal.get("commission"))
        total += _deal_money_amount(deal.get("swap"))
    return total


def _history_time(value: Any) -> datetime | None:
    """Parse an Exness ISO timestamp into UTC, returning None if unavailable."""
    if not value:
        return None
    try:
        parsed = datetime.fromisoformat(str(value).replace("Z", "+00:00"))
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=UTC)
        return parsed.astimezone(UTC)
    except (TypeError, ValueError):
        return None


def _history_decimal_equal(actual: Any, expected: Any) -> bool:
    """Compare broker decimal strings without binary-float rounding."""
    if actual in (None, "") or expected in (None, ""):
        return False
    try:
        return abs(Decimal(str(actual)) - Decimal(str(expected))) <= Decimal("0.0000001")
    except (InvalidOperation, TypeError, ValueError):
        return False


def _match_submission_order(
    rows: list[dict], lock: dict, instrument: str
) -> dict | None:
    """Find the opening LIMIT order for a lock whose IDs were never captured.

    The match uses the persisted signal's side, entry, SL, TP and volume, plus
    the submission timestamp. It deliberately requires every price/volume
    field so an unrelated XAUUSD order cannot be adopted accidentally.
    """
    expected = {
        "price": lock.get("entry"),
        "stop_loss_price": lock.get("sl"),
        "take_profit_price": lock.get("tp"),
        "volume": lock.get("volume"),
    }
    if any(value in (None, "") for value in expected.values()):
        return None

    expected_side = str(lock.get("side") or "").lower()
    lock_time = _history_time(lock.get("created_at"))
    matches: list[tuple[float, dict]] = []
    for row in rows:
        if str(row.get("instrument", "")).upper() != instrument.upper():
            continue
        if str(row.get("order_type", "")).lower() != "limit":
            continue
        if expected_side and str(row.get("direction", "")).lower() != expected_side:
            continue
        if not all(_history_decimal_equal(row.get(key), value) for key, value in expected.items()):
            continue

        row_time = _history_time(row.get("create_time"))
        if lock_time and row_time:
            delta = abs((row_time - lock_time).total_seconds())
            if delta > 600:
                continue
        else:
            # Without timestamps, a strict five-field match is still required.
            delta = 999999.0
        matches.append((delta, row))

    if not matches:
        return None
    matches.sort(key=lambda item: item[0])
    # If timestamps are unavailable and multiple identical orders exist, do
    # not guess which one belongs to this submission.
    if len(matches) > 1 and matches[0][0] == matches[1][0]:
        return None
    return matches[0][1]


def _sync_group_trade_lock(store: StateStore, group: dict) -> None:
    """Keep the legacy lock key as a restart-safe mirror for dashboards/tools."""
    legs = group.get("legs", []) or []
    first = legs[0] if legs else {}
    lock = {
        "active": bool(group.get("active", True)),
        "state": str(group.get("state", "group_active")),
        "group_id": group.get("group_id"),
        "created_at": group.get("created_at"),
        "instrument": group.get("instrument"),
        "side": group.get("side"),
        "entry": first.get("entry_text"),
        "sl": group.get("sl_text"),
        "tp": group.get("tp_text"),
        "volume": group.get("total_volume_text"),
        "order_id": first.get("order_id"),
        "position_id": first.get("position_id"),
        "idempotency_key": first.get("idempotency_key"),
        "legs": [{k: leg.get(k) for k in ("leg", "status", "order_id", "position_id", "entry_text", "volume_text")} for leg in legs],
    }
    store.set_json("trade_lock", lock)


def create_group_submission_record(store: StateStore, signal: dict) -> str:
    """Persist the complete group and both leg intentions before any POST."""
    old = store.get_json("trade_group", {}) or {}
    if old.get("active"):
        raise RuntimeError("An earlier signal group is still active; refusing a new group.")
    if len(signal.get("entry_legs", [])) not in {1, 2} or any(str(x.get("leg", "")).upper() not in {"MIDPOINT_50", "SECONDARY_20"} for x in signal.get("entry_legs", [])):
        raise ValueError("Only Entry 1 (50% midpoint) and optional Entry 2 (20% retracement) are allowed; Entry 3+ are removed.")
    group_id = "KSG-" + uuid.uuid4().hex
    now = utc_iso(datetime.now(UTC))
    legs = []
    for leg in signal["entry_legs"]:
        item = dict(leg)
        item["idempotency_key"] = "KS1-" + uuid.uuid4().hex
        # Indie tracks midpoint and 20% retracement as independent pending legs.
        item["status"] = "prepared"
        item["created_at"] = now
        item["cancel_operation_id"] = None
        item["cancel_requested_at"] = None
        item["actual_pnl"] = None
        item["estimated_unfilled_pnl"] = None
        item["exit_reason"] = None
        legs.append(item)
    group = {
        "group_id": group_id,
        "active": True,
        "state": "submission_prepared",
        "instrument": signal.get("instrument"),
        "side": signal.get("side"),
        "bar_time": signal.get("bar_time"),
        "created_at": now,
        "signal_high": signal.get("setup_high"),
        "signal_low": signal.get("setup_low"),
        "midpoint_entry": signal.get("entry_text"),
        "secondary_entry_20": signal.get("secondary_entry_20_text"),
        "sl_text": signal.get("sl_text"),
        "tp_text": signal.get("tp_text"),
        "total_volume_text": signal.get("total_volume_text"),
        "secondary_20_decision": {
            "status": "PREPARED" if signal.get("secondary_volume_text") else str(signal.get("secondary_skip_reason") or "SKIPPED_INSUFFICIENT_VOLUME"),
            "reason": signal.get("secondary_skip_reason"),
            "entry_text": signal.get("secondary_entry_20_text"),
            "volume_text": signal.get("secondary_volume_text") or None,
        },
        "risk_cash": signal.get("risk_cash"),
        "risk_budget_cash": signal.get("risk_budget_cash"),
        "active_triggered": False,
        "indie_early_exit_warned": False,
        "indie_addon_state_initialized": False,
        "max_retrace_percent": 0.0,
        "estimated_unfilled_pnl": 0.0,
        "history_checked_at": None,
        "result_recorded": False,
        "legs": legs,
    }
    store.set_json("trade_group", group)
    _sync_group_trade_lock(store, group)
    store.set_json("submission_state", {
        "status": "prepared", "group_id": group_id, "created_at": now,
        "instrument": group["instrument"], "side": group["side"],
        "entry": group["midpoint_entry"], "sl": group["sl_text"],
        "tp": group["tp_text"], "volume": group["total_volume_text"],
    })
    return group_id


def _snapshot_leg_match(leg: dict, group: dict, orders: list[dict], positions: list[dict]) -> tuple[dict | None, dict | None]:
    """Match a persisted group leg to Exness snapshot rows using schema aliases.

    Exness snapshot payloads may expose order direction/type as side/type while
    older normalized rows use direction/order_type. Prefer exact ID, then an
    exact full-field match, then a unique instrument+side+entry+volume match.
    The final fallback is deliberately unique-only to avoid cancelling an
    unrelated order.
    """
    order_id = str(leg.get("order_id") or "")
    position_id = str(leg.get("position_id") or "")
    matched_order = next((o for o in orders if order_id and str(o.get("order_id", o.get("id", ""))) == order_id), None)
    if matched_order is None and position_id:
        matched_order = next((o for o in orders if str(o.get("position_id", "")) == position_id), None)

    def val(row: dict, *keys: str) -> Any:
        for key in keys:
            value = row.get(key)
            if value not in (None, ""):
                return value
        return None

    if matched_order is None:
        base = [o for o in orders
                if str(val(o, "instrument", "symbol") or "").upper() == str(group.get("instrument", "")).upper()
                and str(val(o, "direction", "side") or "").lower() == str(group.get("side", "")).lower()
                and _history_decimal_equal(val(o, "price", "entry_price", "open_price"), leg.get("entry_text"))]
        exact = [o for o in base
                 if _history_decimal_equal(val(o, "volume", "quantity"), leg.get("volume_text"))
                 and (val(o, "stop_loss_price", "stop_loss") is None or _history_decimal_equal(val(o, "stop_loss_price", "stop_loss"), leg.get("sl_text")))
                 and (val(o, "take_profit_price", "take_profit") is None or _history_decimal_equal(val(o, "take_profit_price", "take_profit"), leg.get("tp_text")))]
        candidates = exact if exact else [o for o in base if _history_decimal_equal(val(o, "volume", "quantity"), leg.get("volume_text"))]
        if len(candidates) == 1:
            matched_order = candidates[0]

    matched_position = next((p for p in positions if position_id and str(p.get("position_id", p.get("id", ""))) == position_id), None)
    if matched_position is None and matched_order and matched_order.get("position_id"):
        matched_position = next((p for p in positions if str(p.get("position_id", "")) == str(matched_order.get("position_id"))), None)
    if matched_position is None and not position_id:
        candidates = [p for p in positions
                      if str(p.get("instrument", p.get("symbol", ""))).upper() == str(group.get("instrument", "")).upper()
                      and str(p.get("direction", p.get("side", ""))).lower() == str(group.get("side", "")).lower()
                      and _history_decimal_equal(p.get("open_price", p.get("price")), leg.get("entry_text"))
                      and _history_decimal_equal(p.get("volume", p.get("quantity")), leg.get("volume_text"))]
        if len(candidates) == 1:
            matched_position = candidates[0]
    return matched_order, matched_position

def _group_leg_cancel(store: StateStore, api: ExnessAPI, group: dict, leg: dict,
                      reason: str, exit_price: float) -> bool:
    """Cancel an unfilled leg once; persist estimated P/L for group classification."""
    order_id = str(leg.get("order_id") or "")
    # A definitively rejected DELETE is safe to retry only after a fresh
    # snapshot proves the order is still pending. Uncertain DELETE outcomes
    # are never blindly repeated.
    if str(leg.get("status", "")).lower() == "cancel_rejected":
        last_attempt = _history_time(leg.get("cancel_last_attempt_at"))
        if last_attempt is not None and (datetime.now(UTC) - last_attempt).total_seconds() < 15:
            return False
        fresh = api.snapshot()
        fresh_orders, fresh_positions = instrument_activity(fresh, str(group.get("instrument")))
        fresh_order, fresh_position = _snapshot_leg_match(leg, group, fresh_orders, fresh_positions)
        if fresh_position:
            leg["position_id"] = str(fresh_position.get("position_id") or leg.get("position_id") or "")
            leg["status"] = "filled"
            leg["estimated_unfilled_pnl"] = None
            group["active_triggered"] = True
            return False
        if not fresh_order:
            leg["status"] = "cancelled_unfilled"
            leg["cancelled_at"] = utc_iso(datetime.now(UTC))
            logging.warning("PENDING ORDER CANCELLED | %s %s order %s is no longer active at Exness.", group.get("instrument"), leg.get("leg"), order_id)
            return True
        leg["status"] = "pending"
        leg["cancel_operation_id"] = None
        leg["cancel_error"] = None
        logging.warning("GROUP %s | retrying a definitively rejected cancellation for %s after confirming the order is still pending.", group.get("group_id"), leg.get("leg"))
    if not order_id:
        leg["status"] = "awaiting_order_id_for_cancel"
        return False
    if leg.get("status") == "cancel_requested":
        op_id = str(leg.get("cancel_operation_id") or "")
        if not op_id:
            # Some DELETE acknowledgements/uncertain responses may not expose
            # an operation ID. Reconcile snapshots only; never issue a second
            # DELETE for the same leg.
            fresh = api.snapshot()
            fresh_orders, fresh_positions = instrument_activity(fresh, str(group.get("instrument")))
            fresh_order, fresh_position = _snapshot_leg_match(leg, group, fresh_orders, fresh_positions)
            if fresh_position:
                leg["position_id"] = str(fresh_position.get("position_id") or leg.get("position_id") or "")
                leg["status"] = "filled"
                leg["estimated_unfilled_pnl"] = None
                group["active_triggered"] = True
                return False
            if not fresh_order:
                leg["status"] = "cancelled_unfilled"
                leg["cancelled_at"] = utc_iso(datetime.now(UTC))
                return True
            last_attempt = _history_time(leg.get("cancel_last_attempt_at"))
            same_idem = str(leg.get("cancel_idempotency_key") or "")
            if same_idem and last_attempt is not None and (datetime.now(UTC) - last_attempt).total_seconds() >= 15:
                # Reuse the original idempotency key: if the first DELETE was
                # accepted but its response was lost, Exness returns the same
                # operation rather than executing a second cancellation.
                leg["cancel_last_attempt_at"] = utc_iso(datetime.now(UTC))
                ack = api.cancel_pending_order(order_id, idem=same_idem)
                leg["cancel_operation_id"] = str(ack.get("operation_id") or "") or None
                return False
            return False
        status_doc = api.operation_status(op_id)
        state = str(status_doc.get("status", "")).lower()
        if state in {"rejected", "failed"}:
            leg["status"] = "cancel_rejected"
            leg["cancel_last_attempt_at"] = utc_iso(datetime.now(UTC))
            leg["cancel_error"] = status_doc
            logging.error("PENDING ORDER CANCEL FAILED | Exness rejected cancellation for %s %s; checking order state and retrying safely.", group.get("instrument"), leg.get("leg"))
            logging.error("GROUP %s | Exness rejected cancellation for %s; a snapshot-verified retry will be attempted after cooldown.", group.get("group_id"), leg.get("leg"))            return False
        if state not in {"confirmed", "completed", "succeeded", "success"}:
            return False
        # Broker operation status confirms the cancellation. Avoid an extra
        # snapshot for every leg: this burst caused HTTP 429 and blocked the
        # sibling DELETE. If Exness rejects/does not confirm the operation,
        # normal reconciliation still checks fill state before any retry.
        leg["status"] = "cancelled_unfilled"
        leg["cancelled_at"] = utc_iso(datetime.now(UTC))
        leg["cancel_confirmed_by_operation"] = True
        logging.warning(
            "PENDING ORDER CANCELLED | Exness confirmed %s cancellation for %s order %s; redundant post-cancel snapshot skipped.",
            leg.get("exit_reason", "SL/TP"), leg.get("leg"), order_id,
        )
        return True

    sign = 1.0 if str(group.get("side")).lower() == "buy" else -1.0
    leg["estimated_unfilled_pnl"] = (
        (float(exit_price) - float(dec(leg["entry_text"])))
        * sign * float(dec(api.cfg.contract_size)) * float(dec(leg["volume_text"]))
    )
    if str(reason).upper() not in {"SL", "TP"}:
        leg["estimated_unfilled_pnl"] = None
    leg["exit_reason"] = reason
    leg["cancel_requested_at"] = utc_iso(datetime.now(UTC))
    leg["cancel_last_attempt_at"] = leg["cancel_requested_at"]
    leg["cancel_attempt_count"] = int(leg.get("cancel_attempt_count", 0)) + 1
    leg["status"] = "cancel_requested"
    idem = str(leg.get("cancel_idempotency_key") or ("KS-GROUP-CANCEL-" + uuid.uuid4().hex))
    leg["cancel_idempotency_key"] = idem
    logging.warning("PENDING ORDER CANCEL | sending %s cancellation for %s order %s.", reason, leg.get("leg"), order_id)
    try:
        ack = api.cancel_pending_order(order_id, idem=idem)
    except UncertainPostError as exc:
        leg["cancel_error"] = str(exc)
        logging.error("PENDING ORDER CANCEL WAITING | %s %s: Exness response was uncertain; the same request will be reconciled.", group.get("instrument"), leg.get("leg"))
        logging.error("GROUP %s | %s cancellation outcome uncertain. The same idempotency key will be reconciled; no new key will be generated.", group.get("group_id"), leg.get("leg"))
        return False
    operation_id = ack.get("operation_id")
    leg["cancel_operation_id"] = str(operation_id) if operation_id else None
    if not operation_id:
        # Avoid an immediate duplicate REST call after DELETE. The next normal
        # account reconciliation will check state and reuse the same idempotency
        # key if the order is still pending.
        logging.warning(
            "PENDING ORDER CANCEL | Exness accepted cancellation for %s order %s without an operation ID; awaiting scheduled reconciliation.",
            leg.get("leg"), order_id,
        )
        return False
    status_doc = api.operation_status(str(operation_id))
    state = str(status_doc.get("status", "")).lower()
    if state in {"rejected", "failed"}:
        leg["status"] = "cancel_rejected"
        leg["cancel_last_attempt_at"] = utc_iso(datetime.now(UTC))
        leg["cancel_error"] = status_doc
        logging.error("PENDING ORDER CANCEL FAILED | Exness rejected cancellation for %s %s; checking order state and retrying safely.", group.get("instrument"), leg.get("leg"))
        logging.error("GROUP %s | Exness rejected cancellation for %s; retry will use a new idempotency key only after a fresh snapshot and cooldown.", group.get("group_id"), leg.get("leg"))
        return False
    if state in {"confirmed", "completed", "succeeded", "success"}:
        # The cancellation operation is broker-confirmed; avoid another
        # per-leg account snapshot which can trip Exness request limits.
        leg["status"] = "cancelled_unfilled"
        leg["cancelled_at"] = utc_iso(datetime.now(UTC))
        leg["cancel_confirmed_by_operation"] = True
        logging.warning(
            "PENDING ORDER CANCELLED | Exness confirmed %s cancellation for %s order %s; redundant post-cancel snapshot skipped.",
            reason, leg.get("leg"), order_id,
        )
        return True
    return False


def _write_group_daily_report_file(report: dict) -> None:
    """Refresh one persistent daily group P/L block and favorable buckets."""
    path = Path(os.getenv("GROUP_DAILY_REPORT_PATH", "KS_Trader_Desk_Python_Daily_PL_Report.txt"))
    path.parent.mkdir(parents=True, exist_ok=True)
    day_label = datetime.fromisoformat(report["date_ist"]).strftime("%d-%b-%Y")
    sep = "=" * 54
    lines = [
        sep,
        "KS TRADER DESK - PYTHON DAILY GROUP P/L",
        f"Date : {day_label}",
        f"Active signal groups : {int(report['active_groups'])}",
        f"Inactive signal groups : {int(report['inactive_groups'])}",
        f"Total signal groups : {int(report['active_groups']) + int(report['inactive_groups'])}",
        f"Active orders : {int(report.get('active_orders', 0))}",
        f"Inactive orders : {int(report.get('inactive_orders', 0))}",
        f"Missed entries (TP/SL before fill) : {int(report.get('missed_entry_groups', 0))}",
        f"Active Trade P/L : ${float(report['active_pnl']):.2f}",
        f"Inactive Trade P/L (estimated) : ${float(report['inactive_pnl']):.2f}",
        f"Bot Group Net P/L (not account total) : ${float(report['net_pnl']):.2f}",
    ]
    exness_pnl = report.get("exness_account_pnl") or {}
    if exness_pnl.get("date_ist") == report.get("date_ist"):
        realized = dec(exness_pnl.get("realized_closed_pnl", "0"))
        floating_raw = exness_pnl.get("floating_pnl")
        total_raw = exness_pnl.get("total_pnl_including_floating")
        lines += [
            "EXNESS ACTUAL ACCOUNT P/L (BROKER API)",
            f"Realized closed trading P/L : ${float(realized):+.2f}",
            f"Current floating P/L : ${float(dec(floating_raw)):+.2f}" if floating_raw not in (None, "") else "Current floating P/L : unavailable",
            f"Realized + floating P/L : ${float(dec(total_raw)):+.2f}" if total_raw not in (None, "") else "Realized + floating P/L : realized only",
            f"Closed position count : {int(exness_pnl.get('closed_position_count', 0))}",
        ]
    lines += [
        sep,
        "ACTIVE GROUP MAX FAVOURABLE MOVEMENT | BUY | SELL",
    ]
    for i in range(10):
        lines.append(f"{(i + 1) * 10}% | {int(report['active_mfe']['buy'][i])} | {int(report['active_mfe']['sell'][i])}")
    lines += [sep, "INACTIVE GROUP MAX FAVOURABLE MOVEMENT | BUY | SELL"]
    for i in range(10):
        lines.append(f"{(i + 1) * 10}% | {int(report['inactive_mfe']['buy'][i])} | {int(report['inactive_mfe']['sell'][i])}")
    lines.append(sep)
    block = "\n".join(lines)
    old_text = path.read_text(encoding="utf-8") if path.exists() else ""
    blocks = [b.strip() for b in old_text.split(sep) if b.strip()]
    kept = []
    for old in blocks:
        if f"Date : {day_label}" not in old:
            kept.append(old)
    kept.append(block)
    path.write_text(("\n" + sep + "\n").join(kept) + "\n", encoding="utf-8")
    logging.debug("Python daily group P/L report refreshed: %s", path.resolve())



def allocate_group_pnl(active_triggered: bool, actual_filled_pnl: Any,
                       estimated_unfilled_pnl: Any) -> tuple[float, float]:
    """Return filled-position P/L and unfilled-order estimates independently.

    A mixed signal group can contain both a filled leg and an unfilled sibling;
    the sibling's estimated result must not disappear merely because another
    leg filled.
    """
    actual = float(dec(actual_filled_pnl or 0))
    estimated = float(dec(estimated_unfilled_pnl or 0))
    return actual, estimated


def _empty_daily_group_report(day: str) -> dict:
    return {
        "date_ist": day, "active_groups": 0, "inactive_groups": 0,
        "active_orders": 0, "inactive_orders": 0,
        "missed_entry_groups": 0,
        "active_pnl": 0.0, "inactive_pnl": 0.0, "net_pnl": 0.0,
        "active_mfe": {"buy": [0] * 10, "sell": [0] * 10},
        "inactive_mfe": {"buy": [0] * 10, "sell": [0] * 10},
    }


def _save_daily_group_report(store: StateStore, report: dict) -> None:
    current = store.get_json("daily_group_report", {}) or {}
    if current.get("date_ist") == report.get("date_ist") and current.get("exness_account_pnl"):
        report["exness_account_pnl"] = current["exness_account_pnl"]
    archive = store.get_json("daily_group_reports", {}) or {}
    archive[str(report["date_ist"])] = report
    store.set_json("daily_group_reports", archive)
    if report["date_ist"] == datetime.now(IST).date().isoformat():
        store.set_json("daily_group_report", report)
    _write_group_daily_report_file(report)


def _group_daily_report(store: StateStore, group: dict) -> None:
    """Persist group counts on signal day and each leg's P/L on its outcome day."""
    if group.get("result_recorded"):
        return
    created = _history_time(group.get("created_at")) or datetime.now(UTC)
    group_day = created.astimezone(IST).date().isoformat()
    legs = group.get("legs", []) or []
    has_reportable_outcome = any(
        str(leg.get("status", "")).lower() in {"closed", "cancelled_unfilled"}
        or leg.get("actual_pnl") not in (None, "")
        or leg.get("estimated_unfilled_pnl") not in (None, "")
        for leg in legs
    )
    if not has_reportable_outcome:
        group["result_recorded"] = True
        group["classification"] = "NOT_TRADED"
        return

    archive = store.get_json("daily_group_reports", {}) or {}
    group_report = archive.get(group_day) or _empty_daily_group_report(group_day)
    is_active = classify_signal_group(bool(group.get("active_triggered")), float(group.get("max_retrace_percent", 0.0) or 0.0)) == "ACTIVE"
    group_exit = group.get("group_exit_event") or {}
    missed_reason = str(group_exit.get("reason", "")).upper()
    if not group.get("active_triggered") and missed_reason in {"TP", "SL"}:
        group["missed_entry_reason"] = f"MASTER_{missed_reason}_REACHED_BEFORE_FILL"
        group_report["missed_entry_groups"] = int(group_report.get("missed_entry_groups", 0)) + 1
        logging.warning(
            "MISSED ENTRY | group=%s side=%s reason=MASTER_%s_REACHED_BEFORE_FILL | no pending entry filled; pending orders expired and no late market entry will be placed.",
            group.get("group_id"), str(group.get("side", "")).upper(), missed_reason,
        )
    if is_active:
        group_report["active_groups"] = int(group_report.get("active_groups", 0)) + 1
    else:
        group_report["inactive_groups"] = int(group_report.get("inactive_groups", 0)) + 1
    bucket_value = float(group.get("max_retrace_percent", 0.0) or 0.0)
    bucket = max(1, min(10, int(bucket_value / 10.0) + (1 if bucket_value % 10 else 0)))
    side = str(group.get("side", "buy")).lower()
    mfe_key = "active_mfe" if is_active else "inactive_mfe"
    if side not in {"buy", "sell"}:
        side = "buy"
    if 0.0 < bucket_value <= 100.0:
        group_report[mfe_key][side][bucket - 1] += 1
    _save_daily_group_report(store, group_report)
    archive[group_day] = group_report

    total_actual = 0.0
    total_estimated = 0.0
    for leg in legs:
        status = str(leg.get("status", "")).lower()
        actual = float(dec(leg.get("actual_pnl", 0) or 0))
        estimated_raw = leg.get("estimated_unfilled_pnl")
        estimated = float(dec(estimated_raw or 0)) if estimated_raw not in (None, "") else 0.0
        total_actual += actual
        total_estimated += estimated
        if status not in {"closed", "cancelled_unfilled"} and leg.get("actual_pnl") in (None, "") and estimated_raw in (None, ""):
            continue
        event_time = _history_time(leg.get("closed_at") or leg.get("cancelled_at") or leg.get("cancel_requested_at")) or created
        outcome_day = event_time.astimezone(IST).date().isoformat()
        report = archive.get(outcome_day) or _empty_daily_group_report(outcome_day)
        if status in {"filled", "closed"} or leg.get("actual_pnl") not in (None, ""):
            report["active_orders"] = int(report.get("active_orders", 0)) + 1
            report["active_pnl"] = round(float(report.get("active_pnl", 0.0)) + actual, 2)
        elif status == "cancelled_unfilled" and estimated_raw not in (None, ""):
            report["inactive_orders"] = int(report.get("inactive_orders", 0)) + 1
            report["inactive_pnl"] = round(float(report.get("inactive_pnl", 0.0)) + estimated, 2)
        report["net_pnl"] = round(float(report.get("active_pnl", 0.0)) + float(report.get("inactive_pnl", 0.0)), 2)
        archive[outcome_day] = report
        _save_daily_group_report(store, report)

    group["result_recorded"] = True
    group["classification"] = "ACTIVE" if is_active else "INACTIVE"
    group["actual_filled_pnl"] = round(total_actual, 2)
    group["estimated_unfilled_pnl"] = round(total_estimated, 2)
    logging.info("SIGNAL GROUP RESULT | %s | class=%s | actual filled P/L=$%.2f | unfilled estimate=$%.2f",
                 group.get("group_id"), group["classification"], total_actual, total_estimated)


def _pending_initial_sl_from_tick(group: dict, tick: dict | None) -> float | None:
    """Detect the ORIGINAL master SL before either entry leg has filled.

    This is deliberately independent of candle completion and broker order
    visibility: a fresh executable quote crossing the setup's saved initial
    SL invalidates every still-pending leg in that signal group.
    Match the original Indie: both BUY and SELL setup invalidation use Bid.
    """
    if not tick or not group or not group.get("active"):
        return None
    if bool(group.get("active_triggered")):
        return None
    legs = group.get("legs", []) or []
    if any(
        str(leg.get("status", "")).lower() in {"filled", "closed"}
        or bool(leg.get("position_id"))
        for leg in legs
    ):
        return None
    pending_statuses = {
        "pending", "acknowledged", "awaiting_visibility",
        "awaiting_order_id_for_cancel", "cancel_requested", "cancel_rejected",
    }
    if not any(
        str(leg.get("status", "")).lower() in pending_statuses
        and not leg.get("position_id")
        for leg in legs
    ):
        return None
    try:
        if float(tick.get("age_seconds", 999999)) > 10:
            return None
        bid, ask = dec(tick["bid"]), dec(tick["ask"])
        # sl_text is the original signal group's initial/master SL. Never use
        # a trailing/current position SL for this pre-fill invalidation.
        initial_sl = dec(group["sl_text"])
    except (KeyError, TypeError, ValueError, InvalidOperation):
        return None
    side = str(group.get("side", "")).lower()
    if side == "buy" and bid <= initial_sl:
        return float(initial_sl)
    if side == "sell" and bid >= initial_sl:
        return float(initial_sl)
    return None


def _pending_order_original_sl_crossed(order: dict, tick: dict | None) -> bool:
    """Return True when a bot-managed, still-pending order has crossed its own original SL.

    This also covers orders left at Exness from an earlier bot run when the
    persisted trade_group is missing or belongs to an older version.
    """
    if not order or not tick:
        return False
    comment = str(order.get("comment") or "").lower()
    if "ks trader desk" not in comment:
        return False
    if str(order.get("state", "")).lower() not in {"placed", "pending_new", "pending", "accepted"}:
        return False
    try:
        if float(tick.get("age_seconds", 999999)) > 10:
            return False
        original_sl = dec(order.get("stop_loss_price"))
        bid, ask = dec(tick["bid"]), dec(tick["ask"])
    except (KeyError, TypeError, ValueError, InvalidOperation):
        return False
    side = str(order.get("direction") or "").lower()
    # Still-pending orders have not become positions: retain Indie Bid-based
    # master-SL invalidation, rather than applying the position's Ask stop side.
    if side == "buy":
        return bid <= original_sl
    if side == "sell":
        return bid >= original_sl
    return False


def cancel_bot_pending_orders_past_original_sl(store: StateStore, api: ExnessAPI, snapshot: dict,
                                               instrument: str, tick: dict | None) -> int:
    """Cancel orphaned bot pending orders; active groups use their own reconciler."""
    active_orders, _ = instrument_activity(snapshot, instrument)
    group = store.get_json("trade_group", {}) or {}
    group_order_ids = {str(leg.get("order_id") or "") for leg in (group.get("legs", []) or [])}
    crossed = [order for order in active_orders
               if str(order.get("order_id") or "") not in group_order_ids
               and _pending_order_original_sl_crossed(order, tick)]
    cancelled_requests = 0
    for order in crossed:
        order_id = str(order.get("order_id") or "")
        if not order_id:
            continue
        # Recheck against a fresh broker snapshot immediately before DELETE so
        # a just-filled order is never treated as an unfilled pending order.
        fresh_snapshot = api.snapshot()
        fresh_orders, fresh_positions = instrument_activity(fresh_snapshot, instrument)
        still_pending = next((item for item in fresh_orders
                              if str(item.get("order_id") or "") == order_id), None)
        linked_position_id = str(order.get("position_id") or "")
        already_filled = bool(linked_position_id and any(
            str(position.get("position_id") or "") == linked_position_id
            for position in fresh_positions
        ))
        if not still_pending or already_filled:
            continue
        idem = "KS-ORIGINAL-SL-CANCEL-" + re.sub(r"[^A-Za-z0-9_-]", "", order_id)
        try:
            ack = api.cancel_pending_order(order_id, idem=idem)
            cancelled_requests += 1
            logging.warning(
                "ORIGINAL SL HIT | cancelling unfilled bot pending order %s (%s): BID=%s ASK=%s SL=%s; operation=%s",
                order_id, still_pending.get("direction"), tick.get("bid"), tick.get("ask"),
                still_pending.get("stop_loss_price"), ack.get("operation_id") or "awaiting confirmation",
            )
        except UncertainPostError:
            # The deterministic idempotency key makes subsequent checks safe;
            # the order remains visible and will be reconciled on the next pass.
            logging.error("ORIGINAL SL HIT | cancellation outcome uncertain for pending order %s; will reconcile with Exness.", order_id)
        except Exception as exc:
            logging.error("ORIGINAL SL HIT | could not cancel pending order %s: %s", order_id, str(exc)[:220])
    return cancelled_requests


def _active_group_exit_from_tick(group: dict, tick: dict | None) -> tuple[str, float] | None:
    """Detect shared SL/TP on a filled leg using live executable quotes.

    When one leg has filled, a still-unfilled sibling must be cancelled as soon
    as the filled position reaches the shared master SL/TP. This check runs on
    live BID/ASK ticks (not only completed candle data).
    """
    if not tick or not group or not group.get("active") or not group.get("active_triggered"):
        return None
    pending_statuses = {
        "pending", "acknowledged", "awaiting_visibility",
        "awaiting_order_id_for_cancel", "cancel_requested", "cancel_rejected",
    }
    if not any(
        str(leg.get("status", "")).lower() in pending_statuses
        and not str(leg.get("position_id") or "")
        for leg in (group.get("legs", []) or [])
    ):
        return None
    try:
        if float(tick.get("age_seconds", 999999)) > 10:
            return None
        bid, ask = dec(tick["bid"]), dec(tick["ask"])
        sl, tp = dec(group["sl_text"]), dec(group["tp_text"])
    except (KeyError, TypeError, ValueError, InvalidOperation):
        return None
    side = str(group.get("side", "")).lower()
    # Live active-position exits use broker executable sides: BUY closes at
    # Bid; SELL closes at Ask. Strategy/signal candles remain Indie Bid based.
    if side == "buy":
        if executable_sl_hit(side, bid, ask, sl):
            return ("SL", float(sl))
        if bid >= tp:
            return ("TP", float(tp))
    elif side == "sell":
        if executable_sl_hit(side, bid, ask, sl):
            return ("SL", float(sl))
        if ask <= tp:
            return ("TP", float(tp))
    return None


def _pending_group_exit_from_tick(group: dict, tick: dict | None) -> tuple[str, float] | None:
    """Return master SL/TP exit when a fresh executable quote has passed it.

    Use Indie Bid-based invalidation before fill; after a leg is filled,
    use executable Bid for BUY and Ask for SELL. This deliberately does not
    depend on a completed M1 candle, a saved
    last-bar timestamp, or snapshot visibility.
    """
    if not tick or not group or not group.get("active"):
        return None
    pending_statuses = {
        "pending", "acknowledged", "awaiting_visibility",
        "cancel_requested", "cancel_rejected",
        "awaiting_order_id_for_cancel",
    }
    has_unfilled_pending = any(
        str(leg.get("status", "")).lower() in pending_statuses
        and not str(leg.get("position_id") or "")
        for leg in (group.get("legs", []) or [])
    )
    if not has_unfilled_pending:
        return None
    try:
        age = float(tick.get("age_seconds", 999999))
        if age > 10:
            return None
        bid = float(dec(tick["bid"]))
        ask = float(dec(tick["ask"]))
        sl = float(dec(group["sl_text"]))
        tp = float(dec(group["tp_text"]))
    except (KeyError, TypeError, ValueError, InvalidOperation):
        return None
    side = str(group.get("side", "")).lower()
    if side == "sell":
        # Before any fill, preserve Indie Bid-based master-level invalidation.
        # Once a leg has filled, use the broker's SELL close side (Ask).
        sell_exit_price = ask if group.get("active_triggered") else bid
        sell_sl_crossed = sell_exit_price >= sl
        if sell_sl_crossed:
            return ("SL", sl)
        if sell_exit_price <= tp:
            return ("TP", tp)
    elif side == "buy":
        # BUY positions close by selling at BID.
        if executable_sl_hit(side, bid, ask, sl):
            return ("SL", sl)
        if bid >= tp:
            return ("TP", tp)
    return None


def refresh_trade_group_lock(store: StateStore, api: ExnessAPI, snapshot: dict,
                             instrument: str, m1: pd.DataFrame | None = None,
                             tick: dict | None = None) -> bool:
    """Reconcile both legs under one signal group and classify P/L once."""
    group = store.get_json("trade_group", {}) or {}
    if not group.get("active"):
        return False
    orders, positions = instrument_activity(snapshot, instrument)
    side = str(group.get("side", "")).lower()
    candle_high = candle_low = None  # Indie-compatible Bid candles for all software logic
    position_high = position_low = None  # Indie uses the same Bid OHLC for exits
    if m1 is not None and not m1.empty:
        last = m1.iloc[-1]
        candle_high, candle_low = float(last["high"]), float(last["low"])
        position_high, position_low = candle_high, candle_low
        # Signal retracement, pending entries, and exit checks use Bid OHLC,
        # matching the original Indie convention.
        retrace = _setup_retrace_percent(side, candle_high, candle_low,
                                         float(group["signal_high"]), float(group["signal_low"]))
        group["max_retrace_percent"] = max(float(group.get("max_retrace_percent", 0.0)), retrace)

    # A signal group is one trade: once ANY filled leg reaches the shared
    # master TP/SL, cancel every still-pending sibling leg. The previous
    # per-leg-only check missed this case when the 20% leg filled but the
    # 50% sibling remained pending (or vice versa).
    if any(
        str(leg.get("position_id") or "") and any(
            str(pos.get("position_id", "")) == str(leg.get("position_id"))
            for pos in positions
        )
        for leg in group.get("legs", [])
    ):
        group["active_triggered"] = True

    group_exit = group.get("group_exit_event") or {}

    # Invalidate a still-unfilled setup if a completed M1 close breaks its
    # originating candle boundary. This is not reported as a TP/SL loss.
    if not group_exit and not group.get("active_triggered") and m1 is not None and not m1.empty:
        close_now = float(m1.iloc[-1]["close"])
        setup_high_raw, setup_low_raw = group.get("signal_high"), group.get("signal_low")
        invalid = False
        if setup_high_raw not in (None, "") and setup_low_raw not in (None, ""):
            setup_high, setup_low = float(dec(setup_high_raw)), float(dec(setup_low_raw))
            invalid = (side == "buy" and close_now < setup_low) or (side == "sell" and close_now > setup_high)
        if invalid:
            group_exit = {"reason":"SETUP_INVALIDATED","price":close_now,
                          "detected_at":utc_iso(datetime.now(UTC)),
                          "source":"completed_M1_close_beyond_setup_boundary"}
            group["group_exit_event"] = group_exit
            logging.warning("PENDING SETUP INVALIDATED | group=%s | close=%s",group.get("group_id"),close_now)

    # Pending/unfilled group expiry: any still-unfilled pending leg must be
    # cancelled when the shared master SL or TP is crossed, regardless of
    # whether that order appears in the latest broker snapshot. Snapshot
    # matching can temporarily fail during API delays/reconnects; requiring a
    # visible match here was the reason an order could remain open.
    pending_statuses_for_expiry = {
        "pending", "cancel_requested", "cancel_rejected",
        "awaiting_order_id_for_cancel", "awaiting_visibility", "acknowledged",
    }
    # Rebuild each leg's pending/filled state from the fresh Exness snapshot
    # before deciding whether expiry applies. A visible broker order takes
    # precedence over a stale local status left by a restart/older bot build.
    for pending_leg in group.get("legs", []):
        matched_order, matched_position = _snapshot_leg_match(
            pending_leg, group, orders, positions
        )
        if matched_position is not None:
            pending_leg["position_id"] = str(matched_position.get("position_id") or pending_leg.get("position_id") or "")
            pending_leg["status"] = "filled"
            group["active_triggered"] = True
        elif matched_order is not None:
            pending_leg["order_id"] = str(matched_order.get("order_id") or pending_leg.get("order_id") or "")
            pending_leg["position_id"] = None
            if str(pending_leg.get("status", "")).lower() not in {"cancel_requested", "cancel_rejected"}:
                pending_leg["status"] = "pending"

    has_unfilled_pending_leg = any(
        str(pending_leg.get("status", "")).lower() in pending_statuses_for_expiry
        and not str(pending_leg.get("position_id") or "")
        for pending_leg in group.get("legs", [])
    )

    # PRE-FILL MASTER SL INVALIDATION: if neither the 20% nor 50% leg has
    # filled and price reaches the original setup SL, cancel every remaining
    # pending order immediately. This is separate from the active-position
    # exit manager and never substitutes a trailing SL.
    if not group_exit and has_unfilled_pending_leg and not group.get("active_triggered"):
        initial_sl_crossed = _pending_initial_sl_from_tick(group, tick)
        if initial_sl_crossed is not None:
            group_exit = {
                "reason": "SL",
                "price": initial_sl_crossed,
                "detected_at": utc_iso(datetime.now(UTC)),
                "source": "live_quote_original_master_sl_before_any_fill",
                "bid": tick.get("bid"), "ask": tick.get("ask"),
                "tick_age_seconds": tick.get("age_seconds"),
            }
            group["group_exit_event"] = group_exit
            logging.warning(
                "PENDING ORDER SAFETY | ORIGINAL MASTER SL %s crossed at %s before any leg filled; cancelling ALL unfilled group orders.",
                group.get("side", "").upper(), initial_sl_crossed,
            )

    if not group_exit and has_unfilled_pending_leg:
        pending_exit = _pending_group_exit_from_tick(group, tick)
        if pending_exit:
            pending_exit_reason, pending_exit_price = pending_exit
            group_exit = {
                "reason": pending_exit_reason,
                "price": pending_exit_price,
                "detected_at": utc_iso(datetime.now(UTC)),
                "source": "live_exness_quote_pending_expiry",
                "bid": tick.get("bid"), "ask": tick.get("ask"),
                "tick_age_seconds": tick.get("age_seconds"),
            }
            group["group_exit_event"] = group_exit
            logging.warning(
                "PENDING ORDER SAFETY | %s master %s passed at %s; cancelling unfilled pending order(s).",
                group.get("instrument"), pending_exit_reason, pending_exit_price,
            )

        # Candle history is a fallback for an SL/TP crossing that happened
        # while the WebSocket was disconnected or before the bot restarted.
        if not group_exit and candle_high is not None and candle_low is not None:
            shared_sl = float(dec(group.get("sl_text")))
            shared_tp = float(dec(group.get("tp_text")))
            pending_exit_reason = None
            pending_exit_price = None
            expiry_candles = m1
            group_created = _history_time(group.get("created_at"))
            if expiry_candles is not None and not expiry_candles.empty and "time" in expiry_candles.columns:
                candle_times = pd.to_datetime(expiry_candles["time"], utc=True, errors="coerce")
                if group_created is not None:
                    # Include the minute containing order creation, because Exness
                    # candle timestamps are candle-open timestamps.
                    group_minute = pd.Timestamp(group_created).floor("min")
                    expiry_candles = expiry_candles.loc[candle_times >= group_minute]
                else:
                    expiry_candles = expiry_candles.iloc[-1:]

            if expiry_candles is not None and not expiry_candles.empty:
                # Before any fill, pending setup invalidation follows Indie chart
                # OHLC (Bid). Once a leg is filled, an unfilled sibling must be
                # cancelled using the executable close side for the active trade:
                # BUY exits use Bid; SELL exits use Ask.
                use_ask_for_sell_exit = side == "sell" and bool(group.get("active_triggered"))
                ask_columns_available = all(
                    col in expiry_candles.columns and expiry_candles[col].notna().any()
                    for col in ("ask_high", "ask_low")
                )
                if use_ask_for_sell_exit and not ask_columns_available:
                    logging.warning(
                        "SELL active-group candle fallback: Ask OHLC unavailable; "
                        "using Indie Bid OHLC approximation. Fresh live Ask tick checks remain enabled."
                    )
                for _, expiry_candle in expiry_candles.iterrows():
                    if use_ask_for_sell_exit and pd.notna(expiry_candle.get("ask_high")) and pd.notna(expiry_candle.get("ask_low")):
                        candle_hi = float(expiry_candle["ask_high"])
                        candle_lo = float(expiry_candle["ask_low"])
                    else:
                        candle_hi = float(expiry_candle["high"])
                        candle_lo = float(expiry_candle["low"])
                    if side == "sell":
                        sl_crossed = candle_hi >= shared_sl
                        tp_crossed = candle_lo <= shared_tp
                    else:
                        sl_crossed = candle_lo <= shared_sl
                        tp_crossed = candle_hi >= shared_tp
                    # Ambiguous same-candle SL/TP: conservatively classify SL.
                    if sl_crossed:
                        pending_exit_reason, pending_exit_price = "SL", shared_sl
                        break
                    if tp_crossed:
                        pending_exit_reason, pending_exit_price = "TP", shared_tp
                        break

            if pending_exit_reason:
                group_exit = {
                    "reason": pending_exit_reason,
                    "price": pending_exit_price,
                    "detected_at": utc_iso(datetime.now(UTC)),
                    "source": "pending_group_m1_price_cross",
                }
                group["group_exit_event"] = group_exit
                logging.warning(
                    "PENDING ORDER SAFETY | %s master %s crossed in M1 history at %s; cancelling unfilled pending order(s).",
                    group.get("instrument"), pending_exit_reason, pending_exit_price,
                )

    # For an active group, check the live executable quote before waiting for
    # candle data. If one leg filled and the shared master SL/TP is reached,
    # the group_exit event below cancels every still-unfilled sibling order.
    if not group_exit and group.get("active_triggered"):
        active_tick_exit = _active_group_exit_from_tick(group, tick)
        if active_tick_exit:
            active_exit_reason, active_exit_price = active_tick_exit
            group_exit = {
                "reason": active_exit_reason,
                "price": active_exit_price,
                "detected_at": utc_iso(datetime.now(UTC)),
                "source": "live_exness_quote_active_group_sibling_cancel",
                "bid": tick.get("bid"), "ask": tick.get("ask"),
                "tick_age_seconds": tick.get("age_seconds"),
            }
            group["group_exit_event"] = group_exit
            logging.warning(
                "ACTIVE GROUP SAFETY | one leg is filled and live %s reached shared master %s=%s; cancelling every unfilled sibling order.",
                group.get("side", "").upper(), active_exit_reason, active_exit_price,
            )

    # Candle-based fallback remains for periods without a fresh live quote.
    if not group_exit and group.get("active_triggered") and position_high is not None:
        shared_sl = float(dec(group.get("sl_text")))
        shared_tp = float(dec(group.get("tp_text")))
        # Broker-side candle fallback: BUY exit uses Bid OHLC; SELL exit uses
        # Ask OHLC where Exness supplied both-price candles. If Ask candles are
        # unavailable, fall back to Bid candles but record that approximation.
        if side == "sell" and m1 is not None and not m1.empty and all(
            col in m1.columns and pd.notna(m1.iloc[-1].get(col))
            for col in ("ask_high", "ask_low")
        ):
            exit_high = float(m1.iloc[-1]["ask_high"])
            exit_low = float(m1.iloc[-1]["ask_low"])
        else:
            exit_high, exit_low = position_high, position_low
            if side == "sell":
                logging.warning("SELL exit candle fallback: Ask OHLC unavailable; using Bid OHLC approximation. Live Ask tick checks remain enabled.")
        if exit_low <= shared_sl <= exit_high:
            group_exit = {"reason": "SL", "price": shared_sl, "detected_at": utc_iso(datetime.now(UTC)), "source": "active_position_exit_ask_ohlc" if side == "sell" else "active_position_exit_bid_ohlc"}
        elif exit_low <= shared_tp <= exit_high:
            group_exit = {"reason": "TP", "price": shared_tp, "detected_at": utc_iso(datetime.now(UTC)), "source": "active_position_exit_ask_ohlc" if side == "sell" else "active_position_exit_bid_ohlc"}
        if group_exit:
            group["group_exit_event"] = group_exit
            logging.warning(
                "GROUP %s | ACTIVE LEG REACHED %s at %s. Cancelling any unfilled sibling LIMIT order(s).",
                group.get("group_id"), group_exit["reason"], group_exit["price"],
            )
        # Signal-group ACTIVE classification requires a broker-confirmed fill;
        # a candle retracement alone is not treated as an executed order.
        if classify_signal_group(bool(group.get("active_triggered")), group["max_retrace_percent"]) == "ACTIVE":
            group["active_triggered"] = True
            group["activation_reason"] = "entry_trigger_or_20pct_retrace"

    unresolved = False
    for leg in group.get("legs", []):
        status = str(leg.get("status", "")).lower()
        if status in {"closed", "cancelled_unfilled", "rejected", "skipped"}:
            continue
        found_order, found_position = _snapshot_leg_match(leg, group, orders, positions)
        if found_order:
            leg["order_id"] = str(found_order.get("order_id") or leg.get("order_id") or "")
            if found_order.get("position_id"):
                leg["position_id"] = str(found_order["position_id"])
            pending_reprice = leg.get("reprice_pending") or {}
            if pending_reprice:
                if _history_decimal_equal(found_order.get("price"), pending_reprice.get("target")):
                    _commit_pending_reprice(group, leg, str(pending_reprice["target"]), {
                        "reprice_bar_time": pending_reprice.get("bar_time"),
                        "setup_high": pending_reprice.get("signal_high"),
                        "setup_low": pending_reprice.get("signal_low"),
                    })
                else:
                    requested_at = _history_time(pending_reprice.get("requested_at"))
                    if requested_at and (datetime.now(UTC)-requested_at).total_seconds() > 15:
                        leg["reprice_pending"] = None
                        logging.warning("PENDING REPRICE NOT CONFIRMED | group=%s leg=%s | allowing a later fresh attempt.",group.get("group_id"),leg.get("leg"))
            if status not in {"cancel_requested", "cancel_rejected"}:
                leg["status"] = "pending"
        if found_position:
            leg["position_id"] = str(found_position.get("position_id") or leg.get("position_id") or "")
            leg["status"] = "filled"
            leg["estimated_unfilled_pnl"] = None
            leg["entry_touched"] = True
            group["active_triggered"] = True

        # Candle touches are tracked for pending-order reconciliation only.
        # A candle touch alone is not a broker-confirmed fill.
        current_leg_status = str(leg.get("status", status)).lower()
        if candle_high is not None and current_leg_status not in {"rejected", "skipped", "waiting_for_midpoint_confirmation", "prepared", "submission_in_flight", "uncertain", "awaiting_visibility"}:
            if leg.get("order_id") and _entry_level_touched(side, candle_high, candle_low, float(dec(leg["entry_text"]))):
                # Candle touch is not proof of execution. Keep it for pending
                # cancellation logic; only a broker position/open deal activates P/L.
                leg["entry_touched"] = True

        # Group-level exit has priority over the individual leg's entry-touch
        # test. A filled 20% leg reaching shared TP/SL invalidates the still
        # pending 50% leg even if the sibling's own entry was never touched.
        current_leg_status = str(leg.get("status", status)).lower()
        if group_exit and not leg.get("position_id"):
            if current_leg_status in {"prepared", "waiting_for_midpoint_confirmation"} and not leg.get("order_id"):
                # No broker order was submitted for this leg, so safely prevent
                # any later submission after the group's TP/SL event.
                leg["status"] = "skipped"
                continue
            if current_leg_status in {"submission_in_flight", "uncertain", "acknowledged", "awaiting_visibility"} and not leg.get("order_id"):
                # POST may have been accepted even if its order ID is not known.
                # Wait for snapshot/history to identify it; never send another POST.
                leg["status"] = "awaiting_order_id_for_cancel"
                continue
            if current_leg_status in {
                "pending", "acknowledged", "awaiting_visibility",
                "cancel_requested", "awaiting_order_id_for_cancel", "cancel_rejected"
            }:
                try:
                    _group_leg_cancel(
                        store, api, group, leg,
                        str(group_exit["reason"]), float(group_exit["price"])
                    )
                except Exception as exc:
                    leg["cancel_error"] = repr(exc)
                    logging.error(
                        "PENDING ORDER CANCEL ERROR | %s %s: %s; order remains locked for retry.",
                        group.get("instrument"), leg.get("leg"), str(exc)[:220]
                    )
                    logging.error(
                        "GROUP %s | sibling cancellation failed for %s; keeping group locked.",
                        group.get("group_id"), leg.get("leg")
                    )
                    logging.debug("Group sibling cancellation detail:", exc_info=True)
                continue

        # If the order remains pending and SL/TP is hit while its entry price
        # was not touched in this same completed candle, cancel that leg.
        if found_order and m1 is not None and not m1.empty and candle_high is not None:
            entry = float(dec(leg["entry_text"]))
            # Original Indie checks pending entry and SL/TP expiry on Bid OHLC.
            entry_touched = _entry_level_touched(side, candle_high, candle_low, entry)
            entry_not_touched = not entry_touched and not bool(leg.get("entry_touched"))
            sl = float(dec(leg["sl_text"]))
            tp = float(dec(leg["tp_text"]))
            exit_reason = None
            exit_price = None
            expiry_high, expiry_low = candle_high, candle_low
            if entry_not_touched:
                if expiry_low <= sl <= expiry_high:
                    exit_reason, exit_price = "SL", sl
                elif expiry_low <= tp <= expiry_high:
                    exit_reason, exit_price = "TP", tp
            try:
                if str(leg.get("status", "")).lower() == "cancel_requested":
                    _group_leg_cancel(store, api, group, leg, str(leg.get("exit_reason", "SL")), float(leg.get("cancel_exit_price", sl)))
                elif exit_reason:
                    leg["cancel_exit_price"] = exit_price
                    _group_leg_cancel(store, api, group, leg, exit_reason, exit_price)
            except Exception as exc:
                leg["cancel_error"] = repr(exc)
                logging.error("GROUP %s | cancel/reconcile failed for %s; keeping group locked.", group.get("group_id"), leg.get("leg"))
                logging.debug("Group cancellation detail:", exc_info=True)

    # Resolve legs no longer visible in the snapshot through broker history.
    needs_history = any(
        str(leg.get("status", "")).lower() in {"submission_in_flight", "uncertain", "acknowledged", "awaiting_visibility", "pending"}
        for leg in group.get("legs", [])
    ) or any(str(leg.get("status", "")).lower() == "filled" for leg in group.get("legs", []) if not any(str(p.get("position_id", "")) == str(leg.get("position_id", "")) for p in positions))
    last_hist = _history_time(group.get("history_checked_at"))
    if needs_history and (last_hist is None or (datetime.now(UTC) - last_hist).total_seconds() >= 10):
        start_dt = _history_time(group.get("created_at")) or (datetime.now(UTC) - timedelta(days=2))
        try:
            hist_orders = _history_orders({"items": api.orders_history_all_since(start_dt, datetime.now(UTC), instrument)})
            hist_deals = _history_deals({"items": api.deals_history_all_since(start_dt, datetime.now(UTC))})
            group["history_checked_at"] = utc_iso(datetime.now(UTC))
            for leg in group.get("legs", []):
                leg_status = str(leg.get("status", "")).lower()
                oid = str(leg.get("order_id") or "")
                if leg_status in {"closed", "cancelled_unfilled", "rejected", "skipped"}:
                    continue
                source = next((o for o in hist_orders if oid and str(o.get("order_id", "")) == oid), None)
                if source is None:
                    # Match only on all leg-specific broker values; never guess
                    # between identical submissions.
                    candidates = [o for o in hist_orders
                                  if str(o.get("instrument", "")).upper() == instrument.upper()
                                  and str(o.get("order_type", "")).lower() == str(leg.get("order_type") or ("limit" if leg.get("leg") in {"MIDPOINT_50", "SECONDARY_20"} else "limit")).lower()
                                  and str(o.get("direction", "")).lower() == side
                                  and _history_decimal_equal(o.get("price"), leg.get("entry_text"))
                                  and _history_decimal_equal(o.get("volume"), leg.get("volume_text"))
                                  and _history_decimal_equal(o.get("stop_loss_price"), leg.get("sl_text"))
                                  and _history_decimal_equal(o.get("take_profit_price"), leg.get("tp_text"))]
                    if len(candidates) == 1:
                        source = candidates[0]
                if source is None:
                    continue
                if source.get("order_id"):
                    leg["order_id"] = str(source["order_id"])
                if source.get("position_id"):
                    leg["position_id"] = str(source["position_id"])
                source_state = str(source.get("state", "")).lower()
                if source_state in {"cancelled", "canceled", "rejected", "expired"}:
                    leg["status"] = "cancelled_unfilled" if source_state != "rejected" else "rejected"
                    continue
                if source_state in {"filled", "executed", "closed"} or leg.get("position_id"):
                    pid = str(leg.get("position_id") or "")
                    opening = next((d for d in hist_deals if pid and str(d.get("position_id", "")) == pid and str(d.get("type", "")).lower() == "open"), None)
                    if opening is None and source.get("order_id"):
                        opening = next((d for d in hist_deals if str(d.get("order_id", "")) == str(source.get("order_id")) and str(d.get("type", "")).lower() == "open"), None)
                        if opening and opening.get("position_id"):
                            pid = str(opening["position_id"])
                            leg["position_id"] = pid
                    if opening:
                        group["active_triggered"] = True
                        close_deals = [d for d in hist_deals if str(d.get("position_id", "")) == pid and str(d.get("type", "")).lower() == "close"]
                        still_open = any(str(p.get("position_id", "")) == pid for p in positions)
                        if close_deals and not still_open:
                            # Reconcile the whole position, not just its final
                            # close deal: opening/closing commissions and swap
                            # can be recorded on separate broker deals.
                            realized = _position_realized_pnl(hist_deals, pid)
                            leg["actual_pnl"] = str(realized)
                            leg["status"] = "closed"
                            close_deal = close_deals[-1]
                            close_time = _history_time(close_deal.get("create_time"))
                            if close_time is not None:
                                leg["closed_at"] = utc_iso(close_time)
                            close_order_id = str(close_deal.get("order_id") or "")
                            exit_order = next((o for o in hist_orders
                                               if str(o.get("position_id", "")) == pid
                                               and str(o.get("order_id", "")) == close_order_id
                                               and str(o.get("order_type", "")).lower() == "sltp"), None)
                            reason = str((exit_order or {}).get("reason", "")).lower()
                            close_price = close_deal.get("price")
                            if reason not in {"sl", "tp"} and exit_order:
                                if _history_decimal_equal(close_price, exit_order.get("take_profit_price")):
                                    reason = "tp"
                                elif _history_decimal_equal(close_price, exit_order.get("stop_loss_price")):
                                    reason = "sl"
                            leg["exit_reason"] = reason.upper() if reason else "MANUAL_OR_EXTERNAL"
                            if reason in {"sl", "tp"} and not group.get("group_exit_event"):
                                group["group_exit_event"] = {
                                    "reason": reason.upper(),
                                    # Use the configured shared trigger level, not the
                                    # slipped close-deal fill price, for sibling estimates.
                                    "price": float(dec(group.get("sl_text" if reason == "sl" else "tp_text"))),
                                    "detected_at": utc_iso(datetime.now(UTC)),
                                    "source": "broker_history_confirmed",
                                    "position_id": pid,
                                }
                                logging.warning(
                                    "GROUP %s | broker history confirmed %s close for position %s; pending sibling cancellation queued.",
                                    group.get("group_id"), reason.upper(), pid,
                                )
                            if close_time is not None:
                                opening_balance = store.get_json("daily_opening_balance", {}) or {}
                                close_day = close_time.astimezone(IST).date().isoformat()
                                if opening_balance.get("date_ist") == close_day and opening_balance.get("opening_balance") is not None:
                                    record_daily_closed_trade(
                                        store, dec(opening_balance["opening_balance"]),
                                        close_day, pid, realized,
                                        reason.upper() if reason in {"sl", "tp"} else "MANUAL_OR_EXTERNAL",
                                    )
                        else:
                            leg["status"] = "filled"
        except Exception:
            logging.warning("GROUP %s | broker-history reconciliation is temporarily unavailable; keeping the group locked.", group.get("group_id"))
            logging.debug("Group history reconciliation detail:", exc_info=True)

    # IMPORTANT: broker-history reconciliation above can discover a filled
    # leg's SL/TP close AFTER the first cancellation pass earlier in this
    # function. Process that newly-created group_exit_event immediately in
    # this same refresh; do not wait for another tick/candle cycle.
    confirmed_group_exit = group.get("group_exit_event") or {}
    if confirmed_group_exit and str(confirmed_group_exit.get("reason", "")).upper() in {"SL", "TP"}:
        exit_reason = str(confirmed_group_exit["reason"]).upper()
        exit_price = float(confirmed_group_exit.get("price") or dec(group.get("sl_text" if exit_reason == "SL" else "tp_text")))
        # Refresh broker state at the point of cancellation. Local leg status can
        # be stale (for example, CLOSED/SKIPPED from an earlier reconciliation)
        # while the actual order is still visible at Exness. Broker snapshot wins.
        try:
            exit_snapshot = api.snapshot()
            exit_orders, exit_positions = instrument_activity(exit_snapshot, instrument)
        except Exception:
            exit_orders, exit_positions = orders, positions
            logging.exception("GROUP %s | could not refresh Exness snapshot before sibling cancellation; using last snapshot.", group.get("group_id"))
        for sibling in group.get("legs", []):
            try:
                matched_order, matched_position = _snapshot_leg_match(
                    sibling, group, exit_orders, exit_positions
                )
                if matched_position is not None:
                    sibling["position_id"] = str(matched_position.get("position_id") or sibling.get("position_id") or "")
                    sibling["status"] = "filled"
                    sibling["estimated_unfilled_pnl"] = None
                    continue
                if matched_order is not None:
                    # The broker proves this leg is still an unfilled pending order.
                    sibling["order_id"] = str(matched_order.get("order_id") or sibling.get("order_id") or "")
                    sibling["position_id"] = None
                    sibling["status"] = "pending"
                else:
                    # Never cancel by guessed ID. If the broker snapshot has no
                    # matching order, let normal reconciliation resolve its state.
                    continue
                _group_leg_cancel(store, api, group, sibling, exit_reason, exit_price)
            except Exception as exc:
                sibling["cancel_error"] = repr(exc)
                logging.error(
                    "GROUP EXIT SIBLING CANCEL ERROR | group=%s leg=%s reason=%s: %s; retry remains armed.",
                    group.get("group_id"), sibling.get("leg"), exit_reason, str(exc)[:220]
                )
                logging.debug("Immediate post-history sibling cancellation detail:", exc_info=True)

    # If the midpoint leg ended before Exness visibly accepted it, the group is
    # invalidated; do not create a late secondary order after its master setup ended.
    legs_now = group.get("legs", []) or []
    if legs_now and str(legs_now[0].get("status", "")).lower() in {"cancelled_unfilled", "rejected", "skipped"}:
        for later in legs_now[1:]:
            if str(later.get("status", "")).lower() == "waiting_for_midpoint_confirmation":
                later["status"] = "skipped"

    # Keep any visible position mapped to the right leg and group-active state.
    if any(str(leg.get("status", "")).lower() in {"filled", "closed"} for leg in group.get("legs", [])):
        group["active_triggered"] = True

    terminal = {"closed", "cancelled_unfilled", "rejected", "skipped"}
    all_terminal = all(str(leg.get("status", "")).lower() in terminal for leg in group.get("legs", []))
    live_group_activity = any(
        (leg.get("order_id") and any(str(o.get("order_id", "")) == str(leg.get("order_id")) for o in orders))
        or (leg.get("position_id") and any(str(p.get("position_id", "")) == str(leg.get("position_id")) for p in positions))
        for leg in group.get("legs", [])
    )
    if all_terminal and not live_group_activity:
        _group_daily_report(store, group)
        group["active"] = False
        group["state"] = "completed"
        group["completed_at"] = utc_iso(datetime.now(UTC))
        store.set_json("trade_group", group)
        _sync_group_trade_lock(store, group)
        lock = store.get_json("trade_lock", {}) or {}
        lock.update({"active": False, "state": "group_completed", "completed_at": group["completed_at"]})
        store.set_json("trade_lock", lock)
        return False

    group["state"] = "active_group" if group.get("active_triggered") else "pending_group"
    store.set_json("trade_group", group)
    _sync_group_trade_lock(store, group)
    unresolved = any(str(leg.get("status", "")).lower() in {"prepared", "submission_in_flight", "uncertain", "acknowledged", "awaiting_visibility", "cancel_requested", "cancel_rejected", "awaiting_order_id_for_cancel"} for leg in group.get("legs", []))
    return bool(group.get("active", True) or unresolved)


def _submit_group_leg(store: StateStore, api: ExnessAPI, leg_index: int, tick_monitor: LiveTickMonitor | None = None) -> bool:
    """Submit one Indie pending leg once, independent of its sibling's fill."""
    group = store.get_json("trade_group", {}) or {}
    legs = group.get("legs", []) or []
    if not group.get("active") or leg_index >= len(legs):
        return False
    leg = legs[leg_index]
    if str(leg.get("status", "")).lower() != "prepared":
        return False
    # Fail closed without a fresh quote; never guess or modify strategy prices.
    tick = tick_monitor.latest() if tick_monitor is not None else None
    if not tick:
        logging.warning(
            "ORDER PREFLIGHT BLOCKED: no fresh %s Bid/Ask tick (max age 10s). "
            "No order POST sent; inspect exness_tick_diagnostics.json.",
            group.get("instrument"),
        )
        return False
    # Entry 2 is a retracement-touch level in Indie, so it must remain a LIMIT
    # order. Do not use a STOP trigger (which executes on continuation).
    is_secondary_retracement = (
        leg_index == 1 and str(leg.get("leg", "")).upper() == "SECONDARY_20"
    )
    try:
        if is_secondary_retracement:
            order_type = "limit"
            validate_pending_price_against_quote(
                str(group.get("side")), order_type, str(leg.get("entry_text")), tick
            )
        else:
            order_type = select_adaptive_pending_order_type(
                str(group.get("side")), str(leg.get("entry_text")), tick
            )
        if order_type is None:
            diagnostic = {
                "group_id": group.get("group_id"), "instrument": group.get("instrument"),
                "leg": leg.get("leg"), "side": group.get("side"),                "entry": leg.get("entry_text"), "bid": tick.get("bid"),
                "ask": tick.get("ask"), "tick_age_seconds": tick.get("age_seconds"),
                "reason": "Original entry is inside the live Bid/Ask spread; waiting for a fresh quote.",
                "checked_at_utc": utc_iso(datetime.now(UTC)),
            }
            store.append_group_leg_event(
                str(group.get("group_id") or "unknown"), str(leg.get("leg") or "unknown"),
                "waiting_entry_inside_spread", diagnostic,
            )
            logging.info(
                "ORDER WAITING | %s %s original entry=%s is inside spread Bid=%s Ask=%s; retrying unchanged.",
                group.get("group_id"), leg.get("leg"), leg.get("entry_text"), tick.get("bid"), tick.get("ask")
            )
            return False
        if not is_secondary_retracement:
            validate_pending_price_against_quote(
                str(group.get("side")), order_type, str(leg.get("entry_text")), tick
            )
    except ValueError as quote_error:
        diagnostic = {
            "group_id": group.get("group_id"), "instrument": group.get("instrument"),
            "leg": leg.get("leg"), "side": group.get("side"), "order_type": order_type,
            "entry": leg.get("entry_text"), "stop_loss": leg.get("sl_text"),
            "take_profit": leg.get("tp_text"), "volume": leg.get("volume_text"),
            "bid": tick.get("bid"), "ask": tick.get("ask"),
            "tick_age_seconds": tick.get("age_seconds"), "reason": str(quote_error),
            "checked_at_utc": utc_iso(datetime.now(UTC)),
        }
        # Bid/Ask and tick age change on every quote, but the reason an order
        # is invalid usually remains identical. Record/log only when the block
        # reason changes; still run this safety check on every retry.
        block_key = (
            str(group.get("group_id") or "unknown"),
            str(leg.get("leg") or "unknown"),
        )
        block_signature = "|".join((str(group.get("side") or ""), str(order_type or ""),
                                   str(leg.get("entry_text") or ""), str(quote_error)))
        if _PREFLIGHT_BLOCK_SIGNATURES.get(block_key) != block_signature:
            _PREFLIGHT_BLOCK_SIGNATURES[block_key] = block_signature
            store.append_group_leg_event(
                str(group.get("group_id") or "unknown"), str(leg.get("leg") or "unknown"),
                "local_price_preflight_block", diagnostic,
            )
            logging.warning("ORDER PREFLIGHT BLOCKED | %s", json.dumps(diagnostic, default=str))
        return False

    # A successful preflight resets the dedupe state so a later new block can
    # be reported once again for this same order leg.
    _PREFLIGHT_BLOCK_SIGNATURES.pop(
        (str(group.get("group_id") or "unknown"), str(leg.get("leg") or "unknown")), None
    )
    leg["order_type"] = order_type
    logging.info(
        "ADAPTIVE ORDER TYPE | group=%s leg=%s side=%s entry=%s selected=%s | Bid=%s Ask=%s",
        group.get("group_id"), leg.get("leg"), group.get("side"), leg.get("entry_text"),
        order_type.upper(), tick.get("bid"), tick.get("ask")
    )
    leg["preflight_quote"] = {
        "bid": tick["bid"], "ask": tick["ask"],
        "age_seconds": tick.get("age_seconds"),
        "checked_at_utc": utc_iso(datetime.now(UTC)),
    }
    leg["status"] = "submission_in_flight"
    group["state"] = f"submitting_{leg.get('leg', '').lower()}"
    store.set_json("trade_group", group)
    _sync_group_trade_lock(store, group)
    request_signal = {
        "side": group.get("side"), "entry_text": leg.get("entry_text"),
        "sl_text": leg.get("sl_text"), "tp_text": leg.get("tp_text"),
        "comment": leg.get("comment"),
    }
    try:
        ack = api.place_entry_pending(request_signal, str(leg.get("volume_text")), str(leg.get("idempotency_key")), order_type)
    except APIHTTPError as exc:
        leg["status"] = "rejected"
        leg["error"] = {"http_status": exc.status_code, "payload": exc.payload}
        leg["rejection_record"] = {
            "group_id": group.get("group_id"),
            "leg": leg.get("leg"),
            "operation_id": leg.get("operation_id"),
            "http_status": exc.status_code,
            "response_payload": exc.payload,
            "entry": leg.get("entry_text"),
            "volume": leg.get("volume_text"),
            "order_type": order_type, "preflight_quote": leg.get("preflight_quote"),
            "sl": leg.get("sl_text"), "tp": leg.get("tp_text"),
        }
        group["state"] = "partial_group" if leg_index > 0 else "submission_rejected"
        if leg_index == 0:
            for later in legs[1:]:
                later["status"] = "skipped"
            group["active"] = False
        store.set_json("trade_group", group)
        _sync_group_trade_lock(store, group)
        if leg_index == 0:
            store.set_json("submission_state", {
                "status": "rejected_confirmed", "group_id": group.get("group_id"),
                "http_status": exc.status_code, "error": str(exc),
                "confirmed_at": utc_iso(datetime.now(UTC)),
            })
            lock = store.get_json("trade_lock", {}) or {}
            lock.update({"active": False, "state": "rejection_confirmed_no_order"})
            store.set_json("trade_lock", lock)
        rejection_record = {
            "group_id": group.get("group_id"),
            "instrument": group.get("instrument"),
            "side": group.get("side"),
            "leg": leg.get("leg"),
            "entry": leg.get("entry_text"),
            "volume": leg.get("volume_text"),
            "operation_id": leg.get("operation_id"),
            "http_status": exc.status_code,
            "response_payload": exc.payload,
            "idempotency_key": leg.get("idempotency_key"),
            "order_type": order_type, "preflight_quote": leg.get("preflight_quote"),
            "sl": leg.get("sl_text"), "tp": leg.get("tp_text"),
        }
        store.append_group_leg_event(
            str(group.get("group_id") or "unknown"), str(leg.get("leg") or "unknown"),
            "http_rejected", rejection_record,
        )
        logging.error(
            "GROUP %s | %s order rejected by Exness (HTTP %s).",
            group.get("group_id"), leg.get("leg"), exc.status_code,
        )
        logging.error("EXNESS REJECTION DETAIL | %s", json.dumps(rejection_record, default=str))
        return False
    except UncertainPostError as exc:
        leg["status"] = "uncertain"
        leg["error"] = str(exc)
        group["state"] = "submission_uncertain"
        store.set_json("trade_group", group)
        _sync_group_trade_lock(store, group)
        store.set_json("submission_state", {"status": "uncertain", "group_id": group.get("group_id"), "error": str(exc)})
        logging.error("GROUP %s | %s submission uncertain. No retry and no later leg will be submitted.", group.get("group_id"), leg.get("leg"))
        return False
    except Exception as exc:
        leg["status"] = "uncertain"
        leg["error"] = repr(exc)
        group["state"] = "submission_uncertain"
        store.set_json("trade_group", group)
        _sync_group_trade_lock(store, group)
        store.set_json("submission_state", {"status": "uncertain", "group_id": group.get("group_id"), "error": repr(exc)})
        logging.error("GROUP %s | %s submission outcome unknown. No retry and no later leg will be submitted.", group.get("group_id"), leg.get("leg"))
        logging.debug("Group leg POST error:", exc_info=True)
        return False

    leg["ack"] = ack
    leg["operation_id"] = str(ack.get("operation_id") or "")
    ack_order = ack.get("order") if isinstance(ack.get("order"), dict) else {}
    ack_order_id = ack.get("order_id") or ack_order.get("order_id")
    if ack_order_id:
        leg["order_id"] = str(ack_order_id)
    leg["status"] = "acknowledged"
    group["state"] = "awaiting_order_visibility"
    store.set_json("trade_group", group)
    _sync_group_trade_lock(store, group)
    if leg_index == 0:
        store.set_json("submission_state", {"status": "acknowledged", "group_id": group.get("group_id"), "operation_id": leg["operation_id"]})
    op_id = leg["operation_id"]
    if op_id:
        deadline = time.time() + 20
        while time.time() < deadline:
            try:
                status_doc = api.operation_status(op_id)
            except Exception:
                logging.warning("GROUP %s | Could not confirm %s operation yet; awaiting snapshot reconciliation.", group.get("group_id"), leg.get("leg"))
                break
            op_state = str(status_doc.get("status", "")).lower()
            if op_state in {"rejected", "failed"}:
                leg["status"] = "rejected"
                leg["operation_status"] = status_doc
                group["state"] = "partial_group" if leg_index > 0 else "submission_rejected"
                if leg_index == 0:
                    for later in legs[1:]:
                        later["status"] = "skipped"
                    group["active"] = False
                store.set_json("trade_group", group)
                _sync_group_trade_lock(store, group)
                if leg_index == 0:
                    store.set_json("submission_state", {
                        "status": "rejected_confirmed", "group_id": group.get("group_id"),
                        "operation_id": op_id, "operation_status": status_doc,
                        "confirmed_at": utc_iso(datetime.now(UTC)),
                    })
                    lock = store.get_json("trade_lock", {}) or {}
                    lock.update({"active": False, "state": "rejection_confirmed_no_order"})
                    store.set_json("trade_lock", lock)
                rejection_record = {
                    "group_id": group.get("group_id"),
                    "instrument": group.get("instrument"),
                    "side": group.get("side"),
                    "leg": leg.get("leg"),
                    "entry": leg.get("entry_text"),
                    "volume": leg.get("volume_text"),
                    "operation_id": op_id,
                    "http_status": None,
                    "response_payload": status_doc,
                    "idempotency_key": leg.get("idempotency_key"),
                }
                leg["rejection_record"] = rejection_record
                store.set_json("trade_group", group)
                store.append_group_leg_event(
                    str(group.get("group_id") or "unknown"), str(leg.get("leg") or "unknown"),
                    "operation_rejected", rejection_record,
                )
                logging.error(
                    "GROUP %s | Exness definitively rejected %s order operation; no retry will be made for this signal.",
                    group.get("group_id"), leg.get("leg"),
                )
                logging.error("EXNESS OPERATION REJECTION DETAIL | %s", json.dumps(rejection_record, default=str))
                return False
            if op_state in {"confirmed", "completed", "succeeded", "success"}:
                leg["operation_status"] = status_doc
                break
            time.sleep(1)

    snap = api.snapshot()
    live_orders, live_positions = instrument_activity(snap, str(group.get("instrument")))
    matched_order, matched_position = _snapshot_leg_match(leg, group, live_orders, live_positions)
    if matched_order:
        leg["order_id"] = str(matched_order.get("order_id") or "")
        if matched_order.get("position_id"):
            leg["position_id"] = str(matched_order["position_id"])
        leg["status"] = "pending"
    elif matched_position:
        leg["position_id"] = str(matched_position.get("position_id") or "")
        leg["status"] = "filled"
        group["active_triggered"] = True
    else:
        leg["status"] = "awaiting_visibility"
        group["state"] = "awaiting_order_visibility"
        logging.warning("GROUP %s | %s was acknowledged but is not yet visible in Exness snapshot. The next leg will not be sent until it is visible.", group.get("group_id"), leg.get("leg"))
    store.set_json("trade_group", group)
    _sync_group_trade_lock(store, group)
    if leg_index == 0 and leg.get("status") in {"pending", "filled"}:
        store.set_json("submission_state", {"status": "reconciled_present", "group_id": group.get("group_id"), "order_id": leg.get("order_id"), "position_id": leg.get("position_id")})
    logging.info("GROUP %s | %s status=%s | entry=%s | volume=%s", group.get("group_id"), leg.get("leg"), leg.get("status"), leg.get("entry_text"), leg.get("volume_text"))
    return leg.get("status") in {"pending", "filled"}


def advance_group_submission(store: StateStore, api: ExnessAPI, tick_monitor: LiveTickMonitor | None = None) -> None:
    """Submit all Indie pending legs independently, once each, with reconciliation.

    Indie keeps midpoint and 20% retracement pending simultaneously. The Python
    adapter submits sequential API calls but does not require midpoint
    visibility or fill before submitting the secondary leg. Each leg has its
    own persisted idempotency key and reconciliation state.
    """
    group = store.get_json("trade_group", {}) or {}
    legs = group.get("legs", []) or []
    if not group.get("active") or not legs:
        return
    if group.get("group_exit_event"):
        logging.info(
            "GROUP %s | shared %s reached; no new pending leg will be submitted.",
            group.get("group_id"), group["group_exit_event"].get("reason")
        )
        return

    # Upgrade groups persisted by older versions that held Entry 2 until
    # midpoint visibility. Indie has no such strategy dependency.
    changed = False
    for leg in legs:
        if str(leg.get("status", "")).lower() == "waiting_for_midpoint_confirmation":
            leg["status"] = "prepared"
            changed = True
    if changed:
        group["state"] = "submission_prepared"
        store.set_json("trade_group", group)
        _sync_group_trade_lock(store, group)

    for leg_index, leg in enumerate(legs):
        if str(leg.get("status", "")).lower() == "prepared":
            _submit_group_leg(store, api, leg_index, tick_monitor)
            group = store.get_json("trade_group", {}) or {}
            legs = group.get("legs", []) or []
            if not group.get("active") or group.get("group_exit_event"):
                return


def _reconcile_legacy_pending_cancel(store: StateStore, api: ExnessAPI, lock: dict,
                                     instrument: str, order_id: str) -> bool:
    """Reconcile/retry a pending-order cancellation in the legacy trade_lock path.

    Returns True while the order/operation still needs management, False only
    after Exness snapshots confirm that the pending order is no longer active.
    """
    order_id = str(order_id or lock.get("order_id") or "")
    if not order_id:
        logging.error("PENDING ORDER CANCEL BLOCKED | Exness did not provide an order ID; keeping the safety lock.")
        return True

    now = datetime.now(UTC)
    last_attempt = _history_time(lock.get("cancel_last_attempt_at") or lock.get("cancel_requested_at"))
    seconds_since_attempt = (now - last_attempt).total_seconds() if last_attempt else 999999
    operation_id = str(lock.get("cancel_operation_id") or "")
    operation_state = ""

    if operation_id:
        try:
            status_doc = api.operation_status(operation_id)
            operation_state = str(status_doc.get("status", "")).lower()
        except Exception:
            logging.debug("Pending cancellation operation status temporarily unavailable.", exc_info=True)
            return True

        if operation_state in {"confirmed", "completed", "succeeded", "success"}:
            fresh = api.snapshot()
            fresh_orders, fresh_positions = instrument_activity(fresh, instrument)
            if any(str(row.get("order_id", "")) == order_id for row in fresh_orders):
                logging.warning("PENDING ORDER CANCEL | Exness confirmed the request; order %s is still visible, checking again.", order_id)
                return True
            lock.update({
                "active": False,
                "state": f"cancelled_unfilled_{str(lock.get('cancel_exit_reason') or 'SLTP').lower()}_reached",
                "resolved_at": utc_iso(datetime.now(UTC)),
                "cancel_confirmed_at": utc_iso(datetime.now(UTC)),
            })
            store.set_json("trade_lock", lock)
            logging.info("PENDING ORDER CANCELLED | Exness snapshot confirms order %s is no longer pending.", order_id)
            return False

        if operation_state not in {"rejected", "failed"}:
            return True

        lock["state"] = "pending_order_cancel_rejected"
        lock["cancel_last_attempt_at"] = utc_iso(now)
        lock["cancel_error"] = status_doc
        store.set_json("trade_lock", lock)
        if seconds_since_attempt < 15:
            logging.error("PENDING ORDER CANCEL FAILED | Exness rejected cancellation for order %s; retrying after safety cooldown.", order_id)
            return True

    # Snapshot before any retry: it may already have filled or been cancelled.
    fresh = api.snapshot()
    fresh_orders, fresh_positions = instrument_activity(fresh, instrument)
    still_pending = any(str(row.get("order_id", "")) == order_id for row in fresh_orders)
    linked_position_id = str(lock.get("position_id") or "")
    became_position = any(
        (linked_position_id and str(row.get("position_id", "")) == linked_position_id)
        or str(row.get("order_id", "")) == order_id
        for row in fresh_positions
    )
    if became_position:
        lock["state"] = "position_open"
        lock["position_id"] = next((str(row.get("position_id")) for row in fresh_positions
                                    if (linked_position_id and str(row.get("position_id", "")) == linked_position_id)
                                    or str(row.get("order_id", "")) == order_id), lock.get("position_id"))
        store.set_json("trade_lock", lock)
        logging.warning("PENDING ORDER SAFETY | Order %s filled before cancellation; switching to open-position management.", order_id)
        return True
    if not still_pending:
        lock.update({
            "active": False,
            "state": f"cancelled_unfilled_{str(lock.get('cancel_exit_reason') or 'SLTP').lower()}_reached",
            "resolved_at": utc_iso(datetime.now(UTC)),
        })
        store.set_json("trade_lock", lock)
        logging.info("PENDING ORDER CANCELLED | Exness snapshot confirms order %s is no longer active.", order_id)
        return False

    if seconds_since_attempt < 15:
        return True

    # Reuse the original idempotency key for uncertain requests. After a
    # definitive broker rejection, issue a new key only after fresh snapshot
    # verification and the cooldown above.
    if operation_state in {"rejected", "failed"}:
        idem = "KS-CANCEL-" + uuid.uuid4().hex
    else:
        idem = str(lock.get("cancel_idempotency_key") or ("KS-CANCEL-" + uuid.uuid4().hex))
    lock["cancel_idempotency_key"] = idem
    lock["cancel_requested_at"] = utc_iso(datetime.now(UTC))
    lock["cancel_last_attempt_at"] = lock["cancel_requested_at"]
    lock["cancel_attempt_count"] = int(lock.get("cancel_attempt_count", 0)) + 1
    lock["state"] = "pending_exit_cancel_requested"
    lock.pop("cancel_operation_id", None)
    store.set_json("trade_lock", lock)
    try:
        ack = api.cancel_pending_order(order_id, idem=idem)
    except UncertainPostError:
        logging.error("PENDING ORDER CANCEL WAITING | Exness response is uncertain for order %s; will reconcile the same request.", order_id)
        return True
    new_operation_id = ack.get("operation_id")
    lock["cancel_operation_id"] = str(new_operation_id) if new_operation_id else None
    store.set_json("trade_lock", lock)
    logging.warning("PENDING ORDER CANCEL RETRY | Resubmitted cancellation for order %s; awaiting Exness confirmation.", order_id)
    return True

def refresh_trade_lock(store: StateStore, api: ExnessAPI, snapshot: dict, instrument: str,
                       m1: pd.DataFrame | None = None, tick: dict | None = None) -> bool:
    """Hold one signal-group lock until every linked leg is reconciled."""
    group = store.get_json("trade_group", {}) or {}
    if group.get("active"):
        return refresh_trade_group_lock(store, api, snapshot, instrument, m1, tick)
    lock = store.get_json("trade_lock", {}) or {}
    if not lock.get("active"):
        return False

    old_state = str(lock.get("state", "")).lower()
    if old_state == "rejected_signal_hold":
        active_orders, open_positions = instrument_activity(snapshot, instrument)
        group_record = store.get_json("trade_group", {}) or {}
        legs = group_record.get("legs", []) or []
        confirmed_rejection = any(
            str(leg.get("status", "")).lower() == "rejected"
            and str((leg.get("operation_status") or {}).get("status", "")).lower() in {"rejected", "failed"}
            for leg in legs
        )
        if confirmed_rejection and not active_orders and not open_positions:
            # The operation endpoint has already returned a final rejection;
            # the fresh account snapshot confirms no live order/position exists.
            # It is now safe to release this stale rejection hold.
            submission = store.get_json("submission_state", {}) or {}
            submission.update({
                "status": "rejected_confirmed", "confirmed_at": utc_iso(datetime.now(UTC)),
                "recovery_reason": "final_Exness_operation_rejection_and_empty_account_snapshot",
            })
            store.set_json("submission_state", submission)
            lock.update({"active": False, "state": "rejection_confirmed_no_order", "released_at": utc_iso(datetime.now(UTC))})
            store.set_json("trade_lock", lock)
            logging.warning("CONFIRMED REJECTION RECONCILED: Exness operation is rejected and no XAUUSD order/position exists. The stale entry hold is cleared; the rejected signal will not be retried.")
            return False
        logging.critical("NEW ENTRIES PAUSED: rejection is not yet safely reconciled (live activity=%d orders/%d positions; confirmed rejection=%s).", len(active_orders), len(open_positions), confirmed_rejection)
        return True

    active_orders, open_positions = instrument_activity(snapshot, instrument)
    locked_order_id = str(lock.get("order_id") or "")
    locked_position_id = str(lock.get("position_id") or "")

    matching_orders = [
        order for order in active_orders
        if str(order.get("order_type", "")).lower() != "sltp"
        and (
            (locked_order_id and str(order.get("order_id", "")) == locked_order_id)
            or (locked_position_id and str(order.get("position_id", "")) == locked_position_id)
            or (not locked_order_id and not locked_position_id)
        )
    ]
    if not matching_orders and not locked_position_id:
        # During upgrades, an older trade_lock can retain an order ID that no
        # longer matches the persisted signal-group leg. Recover only by an
        # exact broker order ID recorded on that same KS signal group.
        saved_group = store.get_json("trade_group", {}) or {}
        saved_group_order_ids = {
            str(leg.get("order_id")) for leg in (saved_group.get("legs", []) or [])
            if leg.get("order_id")
        }
        if saved_group_order_ids:
            matching_orders = [
                order for order in active_orders
                if str(order.get("order_type", "")).lower() != "sltp"
                and str(order.get("order_id", "")) in saved_group_order_ids
            ]

    if matching_orders:
        found = matching_orders[0]
        if found.get("order_id"):
            lock["order_id"] = str(found["order_id"])
        if found.get("position_id"):
            lock["position_id"] = str(found["position_id"])

        # If price reaches the pending order's TP before its entry is touched,
        # the setup has already played out without an open position. Cancel it.
        # Never treat a pending order's TP as a position close.
        cancel_state = str(lock.get("state", "")).lower()
        if cancel_state in {"pending_exit_cancel_requested", "pending_order_cancel_rejected"}:
            return _reconcile_legacy_pending_cancel(
                store, api, lock, instrument, str(found.get("order_id") or lock.get("order_id") or "")
            )

        side = str(found.get("direction") or lock.get("side") or "").lower()
        entry_raw = found.get("price") or lock.get("entry")
        tp_raw = found.get("take_profit_price") or lock.get("tp")
        sl_raw = found.get("stop_loss_price") or lock.get("sl")
        unfilled_exit_reason = None
        touched_level = None

        # A pending LIMIT order is invalidated when its attached SL or TP level
        # is reached while the candle's full range remains on the pre-entry side.
        # This proves the entry price was not touched during this completed M1 bar.
        if m1 is not None and not m1.empty and side in {"buy", "sell"} and entry_raw not in (None, ""):
            last = m1.iloc[-1]
            entry_price = float(dec(entry_raw))
            candle_high = float(last["high"])
            candle_low = float(last["low"])
            entry_not_touched = (
                candle_high < entry_price if side == "sell"
                else candle_low > entry_price
            )
            if entry_not_touched:
                for reason, raw_level in (("SL", sl_raw), ("TP", tp_raw)):
                    if raw_level not in (None, ""):
                        level = float(dec(raw_level))
                        if candle_low <= level <= candle_high:
                            unfilled_exit_reason = reason
                            touched_level = raw_level
                            break

        if unfilled_exit_reason:
            order_id = str(found.get("order_id") or "")
            if not order_id:
                raise RuntimeError("Pending order reached its SL/TP before entry but Exness did not provide order_id; refusing to guess which order to cancel.")
            cancel_idem = "KS-CANCEL-" + uuid.uuid4().hex
            lock["state"] = "pending_exit_cancel_requested"
            lock["cancel_reason"] = f"{unfilled_exit_reason.lower()}_reached_before_entry"
            lock["cancel_requested_at"] = utc_iso(datetime.now(UTC))
            store.set_json("trade_lock", lock)
            logging.warning(
                "INVALID PENDING SETUP: %s LIMIT order %s reached %s (%s) before entry (%s). Requesting cancellation; this is NOT recorded as a trade win/loss.",
                side.upper(), order_id, unfilled_exit_reason, touched_level, entry_raw,
            )
            try:
                ack = api.cancel_pending_order(order_id, idem=cancel_idem)
            except UncertainPostError:
                logging.error(
                    "PENDING ORDER CANCEL STATUS UNCERTAIN for order %s. The bot will not retry blindly; it will reconcile the Exness snapshot before any new entry.",
                    order_id,
                )
                return True
            operation_id = ack.get("operation_id")
            if operation_id:
                lock["cancel_operation_id"] = str(operation_id)
                store.set_json("trade_lock", lock)
                deadline = time.time() + 20
                while time.time() < deadline:
                    status_doc = api.operation_status(str(operation_id))
                    op_state = str(status_doc.get("status", "")).lower()
                    if op_state in {"confirmed", "completed", "succeeded", "success"}:
                        fresh = api.snapshot()
                        fresh_orders, fresh_positions = instrument_activity(fresh, instrument)
                        still_pending = any(str(o.get("order_id", "")) == order_id for o in fresh_orders)
                        if still_pending:
                            logging.warning("Exness confirmed the cancellation operation but the pending order is still visible. Keeping the trade lock until the next snapshot reconciliation.")
                            return True
                        lock.update({
                            "active": False,
                            "state": f"cancelled_unfilled_{unfilled_exit_reason.lower()}_reached",
                            "resolved_at": utc_iso(datetime.now(UTC)),
                        })
                        store.set_json("trade_lock", lock)
                        logging.info(
                            "PENDING ORDER CANCELLED: %s was reached before entry. No position was opened, no P/L is booked, and the bot can look for a fresh setup.",
                            unfilled_exit_reason,
                        )
                        return False
                    if op_state in {"rejected", "failed"}:
                        lock["state"] = "pending_order_cancel_rejected"
                        lock["cancel_last_attempt_at"] = utc_iso(datetime.now(UTC))
                        lock["cancel_error"] = status_doc
                        store.set_json("trade_lock", lock)
                        logging.error("Exness rejected cancellation of pending order %s. The order remains locked for manual review; no replacement order will be submitted.", order_id)
                        return True
                    time.sleep(1)
            logging.warning("Exness accepted the cancellation request but has not confirmed the final result. Keeping the trade lock and reconciling the pending order on the next cycle.")
            return True

        lock["state"] = "pending_order"
        store.set_json("trade_lock", lock)
        if old_state != "pending_order":
            logging.debug("Your %s LIMIT order remains pending at entry; internal live-price monitoring continues. No second order will be placed.", instrument)
        return True

    matching_positions = [
        position for position in open_positions
        if (locked_position_id and str(position.get("position_id", "")) == locked_position_id)
        or not locked_position_id
    ]
    if matching_positions:
        position = matching_positions[0]
        if position.get("position_id"):
            lock["position_id"] = str(position["position_id"])
        lock["state"] = "position_open"
        store.set_json("trade_lock", lock)
        # The human-readable trade dashboard reports the live position state.
        return True

    # No matching live activity: reconcile every available page of broker history.
    history_start = lock.get("created_at") or utc_iso(datetime.now(UTC) - timedelta(days=2))
    history_start_dt = _history_time(history_start) or (datetime.now(UTC) - timedelta(days=2))
    history_end_dt = datetime.now(UTC)
    order_items = api.orders_history_all_since(history_start_dt, history_end_dt, instrument)
    historical_orders = _history_orders({"items": order_items})
    deal_items = api.deals_history_all_since(history_start_dt, history_end_dt)
    historical_deals = _history_deals({"items": deal_items})

    # Identify the original Entry 1 LIMIT order, not a later closing MARKET order.
    source_order = None
    if locked_order_id:
        source_order = next(
            (row for row in historical_orders
             if str(row.get("order_id", "")) == locked_order_id
             and str(row.get("order_type", "")).lower() == "limit"),
            None,
        )
    if source_order is None and locked_position_id:
        expected_side = str(lock.get("side") or "").lower()
        source_order = next(
            (row for row in historical_orders
             if str(row.get("position_id", "")) == locked_position_id
             and str(row.get("order_type", "")).lower() == "limit"
             and (not expected_side or str(row.get("direction", "")).lower() == expected_side)),
            None,
        )

    # Critical recovery path: a very fast trade can open and close between
    # snapshots, leaving the persisted lock's order_id/position_id as None.
    if source_order is None and not locked_order_id and not locked_position_id:
        # Older lock records did not persist volume. Recover missing match fields
        # from the paired submission_state record written before the order POST.
        submission_record = store.get_json("submission_state", {}) or {}
        match_lock = dict(lock)
        for field in ("instrument", "side", "entry", "sl", "tp", "volume", "created_at"):
            if match_lock.get(field) in (None, "") and submission_record.get(field) not in (None, ""):
                match_lock[field] = submission_record[field]
        source_order = _match_submission_order(historical_orders, match_lock, instrument)
        if source_order:
            logging.info("The bot matched the previous entry with Exness history and is checking how that trade ended.")

    if source_order:
        historical_order_id = str(source_order.get("order_id") or "")
        historical_position_id = str(source_order.get("position_id") or "")
        if historical_order_id:
            lock["order_id"] = historical_order_id
            locked_order_id = historical_order_id
        if historical_position_id:
            lock["position_id"] = historical_position_id
            locked_position_id = historical_position_id

    # Find the opening deal by recovered position ID (order ID as fallback).
    opening_deal = None
    if locked_position_id:
        opening_deal = next(
            (deal for deal in historical_deals
             if str(deal.get("position_id", "")) == locked_position_id
             and str(deal.get("type", "")).lower() == "open"),
            None,
        )
    if opening_deal is None and locked_order_id:
        opening_deal = next(
            (deal for deal in historical_deals
             if str(deal.get("order_id", "")) == locked_order_id
             and str(deal.get("type", "")).lower() == "open"),
            None,
        )

    if opening_deal:
        deal_position_id = str(opening_deal.get("position_id") or "")
        if deal_position_id:
            locked_position_id = deal_position_id
            lock["position_id"] = deal_position_id
        deal_order_id = str(opening_deal.get("order_id") or "")
        if deal_order_id:
            lock["opening_order_id"] = deal_order_id
        lock["state"] = "awaiting_sl_tp_confirmation"

    source_state = str((source_order or {}).get("state", "")).lower()
    if source_order and source_state in {"cancelled", "canceled", "rejected"} and not opening_deal:
        lock.update({
            "active": False,
            "state": f"{source_state}_unfilled",
            "resolved_at": source_order.get("update_time") or source_order.get("create_time") or utc_iso(datetime.now(UTC)),
        })
        store.set_json("trade_lock", lock)
        logging.info("PENDING ENTRY ENDED: Exness marked the order as %s before it opened a position. The bot can watch for the next valid signal.", source_state.upper())
        return False

    # First retain the original strict TP/SL rule: require both a filled
    # linked SLTP order and its matching closing deal.
    exit_order = None
    exit_reason = None
    market_close_metadata: dict[str, Any] = {}
    if locked_position_id:
        for candidate in historical_orders:
            if (
                str(candidate.get("position_id", "")) != locked_position_id
                or str(candidate.get("order_type", "")).lower() != "sltp"
                or str(candidate.get("state", "")).lower() != "filled"
            ):
                continue
            candidate_order_id = str(candidate.get("order_id", ""))
            closing_deal = next(
                (deal for deal in historical_deals
                 if str(deal.get("position_id", "")) == locked_position_id
                 and str(deal.get("order_id", "")) == candidate_order_id
                 and str(deal.get("type", "")).lower() == "close"),
                None,
            )
            if not closing_deal:
                continue

            reported_reason = str(candidate.get("reason", "")).lower()
            if reported_reason in {"sl", "tp"}:
                exit_order, exit_reason = candidate, reported_reason.upper()
                break

            close_price = closing_deal.get("price")
            tp_price = candidate.get("take_profit_price") or (source_order or {}).get("take_profit_price")
            sl_price = candidate.get("stop_loss_price") or (source_order or {}).get("stop_loss_price")
            if _history_decimal_equal(close_price, tp_price):
                exit_order, exit_reason = candidate, "TP"
                break
            if _history_decimal_equal(close_price, sl_price):
                exit_order, exit_reason = candidate, "SL"
                break

    # Separate recovery path for a position closed by a filled non-SLTP order
    # (for example, a manual/external MARKET close). A close deal alone is not
    # enough: IDs, direction, filled order state, and full position volume must
    # all reconcile before the lock can be released.
    if not exit_order and locked_position_id and opening_deal:
        position_open_deals = [
            deal for deal in historical_deals
            if str(deal.get("position_id", "")) == locked_position_id
            and str(deal.get("type", "")).lower() == "open"
        ]
        opening_volume = Decimal("0")
        opening_deal_ids: set[str] = set()
        opening_directions: set[str] = set()
        for deal in position_open_deals:
            deal_id = str(deal.get("deal_id") or "")
            if deal_id and deal_id in opening_deal_ids:
                continue
            if deal_id:
                opening_deal_ids.add(deal_id)
            try:
                volume = dec(deal.get("volume"))
            except (InvalidOperation, TypeError, ValueError):
                continue
            if volume <= 0:
                continue
            opening_volume += volume
            direction = str(deal.get("direction") or "").lower()
            if direction in {"buy", "sell"}:
                opening_directions.add(direction)

        if not opening_directions:
            fallback_direction = str(lock.get("side") or "").lower()
            if fallback_direction in {"buy", "sell"}:
                opening_directions.add(fallback_direction)

        expected_close_directions = {
            "sell" if direction == "buy" else "buy"
            for direction in opening_directions
        }
        confirmed_closes: list[tuple[datetime, dict, dict]] = []
        closing_deal_ids: set[str] = set()
        closing_volume = Decimal("0")

        for deal in historical_deals:
            if (
                str(deal.get("position_id", "")) != locked_position_id
                or str(deal.get("type", "")).lower() != "close"
            ):
                continue
            deal_id = str(deal.get("deal_id") or "")
            if not deal_id or deal_id in closing_deal_ids:
                continue

            closing_order_id = str(deal.get("order_id") or "")
            if not closing_order_id:
                continue
            closing_order = next(
                (row for row in historical_orders
                 if str(row.get("position_id", "")) == locked_position_id
                 and str(row.get("order_id", "")) == closing_order_id
                 and str(row.get("state", "")).lower() == "filled"
                 and str(row.get("order_type", "")).lower() != "sltp"),
                None,
            )
            if not closing_order:
                continue

            close_direction = str(deal.get("direction") or closing_order.get("direction") or "").lower()
            if expected_close_directions and close_direction not in expected_close_directions:
                continue

            try:
                volume = dec(deal.get("volume"))
            except (InvalidOperation, TypeError, ValueError):
                continue
            if volume <= 0:
                continue

            closing_deal_ids.add(deal_id)
            closing_volume += volume
            close_time = _history_time(deal.get("create_time")) or _history_time(closing_order.get("update_time")) or datetime.min.replace(tzinfo=UTC)
            confirmed_closes.append((close_time, deal, closing_order))

        volume_tolerance = Decimal("0.0000001")
        if opening_volume > 0 and closing_volume + volume_tolerance >= opening_volume and confirmed_closes:
            confirmed_closes.sort(key=lambda item: item[0])
            latest_close_time, latest_close_deal, latest_close_order = confirmed_closes[-1]
            exit_order = latest_close_order
            exit_reason = (
                "MANUAL"
                if str(latest_close_order.get("order_type", "")).lower() == "market"
                else "EXTERNAL"
            )

            # Retain an audit trail. This is deliberately not labeled SL or TP.
            market_close_metadata = {
                "close_order_id": str(latest_close_order.get("order_id") or ""),
                "closing_deal_ids": sorted(closing_deal_ids),
                "opening_volume": str(opening_volume),
                "closing_volume": str(closing_volume),
                "close_price": latest_close_deal.get("price"),
                "closed_at": latest_close_deal.get("create_time") or latest_close_order.get("update_time") or utc_iso(datetime.now(UTC)),
            }
            profit_values: list[Decimal] = []
            all_close_profits_present = True
            for _, close_deal, _ in confirmed_closes:
                profit = close_deal.get("profit")
                if isinstance(profit, dict) and profit.get("amount") not in (None, ""):
                    try:
                        deal_net = dec(profit["amount"])
                        if close_deal.get("commission") not in (None, ""):
                            deal_net += dec(close_deal["commission"])
                        profit_values.append(deal_net)
                    except (InvalidOperation, TypeError, ValueError):
                        all_close_profits_present = False
                        break
                else:
                    all_close_profits_present = False
                    break
            if all_close_profits_present and len(profit_values) == len(confirmed_closes):
                market_close_metadata["realized_profit"] = str(sum(profit_values, Decimal("0")))

    if exit_order and exit_reason:
        if exit_reason in {"SL", "TP"}:
            close_order_id = str(exit_order.get("order_id") or "")
            close_deal = next(
                (deal for deal in historical_deals
                 if str(deal.get("position_id", "")) == locked_position_id
                 and str(deal.get("type", "")).lower() == "close"
                 and str(deal.get("order_id", "")) == close_order_id),
                None,
            )
            if close_deal is None:
                raise RuntimeError("Exness confirmed an SL/TP exit but its matching close deal is missing; retry reconciliation before new entries.")
            profit = close_deal.get("profit")
            if not isinstance(profit, dict) or profit.get("amount") in (None, ""):
                raise RuntimeError("Confirmed SL/TP close deal has no profit.amount; refusing to change daily risk mode.")
            # Use the same whole-position net P/L calculation as signal-group
            # history reconciliation to keep daily risk totals consistent.
            closed_pnl = _position_realized_pnl(historical_deals, locked_position_id)
            close_time = _history_time(close_deal.get("create_time")) or _history_time(exit_order.get("update_time"))
            if close_time is None:
                raise RuntimeError("Confirmed SL/TP close deal has no valid timestamp; refusing to assign it to an IST day.")
            close_day = close_time.astimezone(IST).date().isoformat()
            opening = store.get_json("daily_opening_balance", {}) or {}
            if opening.get("date_ist") == close_day and opening.get("opening_balance") is not None:
                record_daily_closed_trade(
                    store, dec(opening["opening_balance"]), close_day,
                    locked_position_id, closed_pnl, exit_reason,
                )
        elif exit_reason in {"MANUAL", "EXTERNAL"} and market_close_metadata.get("realized_profit") not in (None, ""):
            close_time = _history_time(market_close_metadata.get("closed_at"))
            if close_time is not None:
                close_day = close_time.astimezone(IST).date().isoformat()
                opening = store.get_json("daily_opening_balance", {}) or {}
                if opening.get("date_ist") == close_day and opening.get("opening_balance") is not None:
                    record_daily_closed_trade(
                        store, dec(opening["opening_balance"]), close_day,
                        locked_position_id, dec(market_close_metadata["realized_profit"]), exit_reason,
                    )
            else:
                logging.warning("Confirmed manual/external close has no valid close timestamp; daily risk recovery was not updated yet.")
        lock.update({
            "active": False,
            "state": f"closed_by_{exit_reason.lower()}",
            "closed_by": exit_reason,
            "closed_at": market_close_metadata.get("closed_at") or exit_order.get("update_time") or utc_iso(datetime.now(UTC)),
            "order_id": locked_order_id or lock.get("order_id"),
            "position_id": locked_position_id or lock.get("position_id"),
        })
        if market_close_metadata:
            lock.update(market_close_metadata)
        store.set_json("trade_lock", lock)
        if market_close_metadata:
            realized = market_close_metadata.get("realized_profit")
            pnl_text = f" | Realized P/L: ${float(dec(realized)):.2f}" if realized not in (None, "") else ""
            close_kind = "MANUAL EXIT" if exit_reason == "MANUAL" else "EXTERNAL EXIT"
            logging.info(
                "TRADE CLOSED: %s | Position %s | Fully closed volume %s / %s%s. New signals can be considered.",
                close_kind, locked_position_id,
                market_close_metadata.get("closing_volume"), market_close_metadata.get("opening_volume"), pnl_text,
            )
        else:
            close_label = "TAKE PROFIT" if exit_reason == "TP" else "STOP LOSS"
            logging.info("TRADE CLOSED: Exness confirms %s was hit for position %s. The bot can watch for the next valid setup.", close_label, locked_position_id)

        if exit_reason in {"MANUAL", "EXTERNAL"}:
            logging.info(
                "MANUAL / EXTERNAL EXIT CONFIRMED: Position %s is fully closed. The trade lock is released; the bot can evaluate the next valid entry. This exit is excluded from the SL/TP-only daily risk protection ledger.",
                locked_position_id,
            )
        return False

    lock["state"] = "awaiting_sl_tp_confirmation"
    store.set_json("trade_lock", lock)
    if old_state != "awaiting_sl_tp_confirmation":
        logging.warning(
            "The previous trade is not fully reconciled yet (order %s, position %s). "
            "The bot is checking Exness history; new entries remain paused for safety.",
            lock.get("order_id"), lock.get("position_id"),
        )
    return True


def _display_price(value: Any, digits: int = 3) -> str:
    if value in (None, ""):
        return "N/A"
    try:
        return f"{float(dec(value)):.{max(0, min(digits, 8))}f}"
    except Exception:
        return str(value)


_LAST_DASHBOARD_SIGNATURE: Any = None


def _dashboard_table_text(title: str, lines: list[str]) -> str:
    """Convert dashboard detail lines into a clean two-column text table."""
    rows: list[tuple[str, str]] = []
    for raw in lines:
        line = str(raw).strip()
        if not line or set(line) <= {"=", "-", " "}:
            continue
        if ":" in line:
            key, value = line.split(":", 1)
            key = key.strip()
            value = value.strip()
            if key and value:
                rows.append((key, value))
                continue
        rows.append(("Details", line))
    if not rows:
        rows = [("Status", "No additional details")]
    key_width = max([len(k) for k, _ in rows] + [8])
    value_width = min(100, max([len(v) for _, v in rows] + [10]))
    border = "+" + "-" * (key_width + 2) + "+" + "-" * (value_width + 2) + "+"
    result = [title, border,
              f"| {'FIELD':<{key_width}} | {'VALUE':<{value_width}} |",
              border]
    for key, value in rows:
        # Keep terminal table columns stable; long values are wrapped as continuation rows.
        chunks = [value[i:i + value_width] for i in range(0, max(1, len(value)), value_width)]
        result.append(f"| {key:<{key_width}} | {chunks[0]:<{value_width}} |")
        for chunk in chunks[1:]:
            result.append(f"| {'':<{key_width}} | {chunk:<{value_width}} |")
    result.append(border)
    return "\n".join(result)


def _group_status_table_text(title: str, rows: list[tuple[str, str, str, str, str, str, str]]) -> str:
    """Render a de-duplicated group/order status as a fixed column table."""
    headers = ("ITEM", "ENTRY", "LOT", "RISK / SL", "PROFIT / TP", "STATUS", "ACTIVE")
    normalized = [tuple(str(cell if cell not in (None, "") else "—") for cell in row) for row in rows]
    # Fixed practical widths keep the seven-column table within a typical CMD window.
    limits = (20, 13, 7, 13, 13, 34, 6)
    widths = [min(limits[i], max(len(headers[i]), *(len(row[i]) for row in normalized))) for i in range(len(headers))]
    border = "+" + "+".join("-" * (w + 2) for w in widths) + "+"
    def render(row: tuple[str, ...]) -> str:
        cells = [cell if len(cell) <= widths[i] else cell[:widths[i]-1] + "…" for i, cell in enumerate(row)]
        return "| " + " | ".join(f"{cells[i]:<{widths[i]}}" for i in range(len(widths))) + " |"
    out = [title, border, render(headers), border]
    out.extend(render(row) for row in normalized)
    out.append(border)
    return "\n".join(out)


def display_trade_dashboard(store: StateStore, snapshot: dict, m1: pd.DataFrame,
                            instrument: str, account_mode: str, contract_size: float,
                            daily_opening_balance: float, risk_percent: float,
                            risk_buffer_percent: float, conditions: dict,
                            trailing_enabled: bool, daily_risk_state: dict | None = None) -> None:
    """Print a concise, human-readable CMD dashboard from broker-confirmed data."""
    global _LAST_DASHBOARD_SIGNATURE
    orders, positions = instrument_activity(snapshot, instrument)
    group_for_signature = store.get_json("trade_group", {}) or {}
    risk_for_signature = daily_risk_state or {}
    if group_for_signature.get("active"):
        legs_signature = tuple(
            (str(leg.get("leg")), str(leg.get("status")),
             str(leg.get("order_id") or ""), str(leg.get("position_id") or ""))
            for leg in (group_for_signature.get("legs", []) or [])
        )
        trail_signature = store.get_json(
            "adaptive_trailing_group_state:" + str(group_for_signature.get("group_id") or ""),
            {},
        ) or {}
        signature = (
            "group", str(group_for_signature.get("group_id")),
            str(group_for_signature.get("state")),
            bool(group_for_signature.get("active_triggered")),
            legs_signature, str(trail_signature.get("current_sl") or ""),
            bool(risk_for_signature.get("reduced_mode")),
        )
    elif positions:
        signature = (
            "position",            tuple((str(pos.get("position_id")), str(pos.get("stop_loss_price") or ""))
                  for pos in positions),
            bool(risk_for_signature.get("reduced_mode")),
        )
    elif orders:
        signature = (
            "orders", tuple((str(o.get("order_id")), str(o.get("status") or ""),
                            str(o.get("order_type") or "")) for o in orders),
            bool(risk_for_signature.get("reduced_mode")),
        )
    else:
        signature = ("idle", bool(risk_for_signature.get("reduced_mode")))
    if signature == _LAST_DASHBOARD_SIGNATURE:
        return

    digits = int(conditions.get("point_digits", 3) or 3)
    now_ist = datetime.now(IST).strftime("%d-%b-%Y %I:%M:%S %p IST")
    group = store.get_json("trade_group", {}) or {}
    if group.get("active"):
        daily_report = store.get_json("daily_group_report", {}) or {}
        trail = store.get_json(
            "adaptive_trailing_group_state:" + str(group.get("group_id") or ""),
            {},
        ) or {}
        legs = group.get("legs", []) or []
        rows: list[tuple[str, str, str, str, str, str, str]] = []
        group_id = str(group.get("group_id") or "—")
        master_sl = str(group.get("sl_text") or "—")
        master_tp = str(group.get("tp_text") or "—")
        master_leg = next(
            (leg for leg in legs if str(leg.get("leg", "")).upper() == "MIDPOINT_50"),
            None,
        )
        master_position_id = str((master_leg or {}).get("position_id") or "")
        master_position = next(
            (
                position for position in positions
                if master_position_id
                and str(position.get("position_id", "")) == master_position_id
            ),
            None,
        )
        if master_position is None:
            # The shared Indie trailing model starts only after the 50% master fills.
            # Do not display a previous group's global/legacy trailing value here.
            master_trail = "WAITING FOR 50% ENTRY"
            trail_stage = "Waiting for Entry 1 fill"
        else:
            master_sltp = _find_position_sltp_order(snapshot, instrument, master_position_id) or {}
            master_trail = str(
                trail.get("current_sl")
                or master_sltp.get("stop_loss_price")
                or master_sl
            )
            trail_stage = trail.get("last_stage") or "Initial SL"
        total_lot = Decimal("0")
        max_risk = Decimal("0")
        max_profit = Decimal("0")
        per_leg_rows = []
        api_messages = []
        for leg in legs:
            try:
                volume = dec(leg.get("volume_text") or leg.get("volume") or "0")
            except Exception:
                volume = Decimal("0")
            total_lot += volume
            entry = leg.get("entry_text") or leg.get("entry") or "—"
            sl = leg.get("sl_text") or group.get("sl_text") or "—"
            tp = leg.get("tp_text") or group.get("tp_text") or "—"
            try:
                max_risk += abs(dec(entry) - dec(sl)) * volume * Decimal(str(contract_size))
                max_profit += abs(dec(tp) - dec(entry)) * volume * Decimal(str(contract_size))
            except Exception:
                pass
            pid = str(leg.get("position_id") or "")
            pos = next((p for p in positions if pid and str(p.get("position_id", "")) == pid), None)
            ord_row = next((o for o in orders if str(leg.get("order_id") or "") and str(o.get("order_id", "")) == str(leg.get("order_id"))), None)
            leg_status = str(leg.get("status", "unknown")).replace("_", " ").upper()
            active = "YES" if pos else "NO"
            if pos:
                leg_status = "OPEN POSITION"
                sltp = _find_position_sltp_order(snapshot, instrument, pid) or {}
                sl = sltp.get("stop_loss_price") or sl
                tp = sltp.get("take_profit_price") or tp
            elif ord_row:
                leg_status = "PENDING ORDER"
            elif leg.get("status"):
                leg_status = str(leg.get("status")).replace("_", " ").upper()
            item = "50% MIDPOINT" if leg.get("leg") == "MIDPOINT_50" else "20% SECONDARY"
            per_leg_rows.append((item, str(entry), f"{float(volume):.2f}", str(sl), str(tp), leg_status, active))
            rejection = leg.get("rejection_record") or {}
            response = rejection.get("response_payload") or {}
            err = response.get("error_message") or response.get("description") or rejection.get("error_message")
            err_code = response.get("error_code") or rejection.get("error_code")
            if str(err_code) == "5005":
                short_error = "API 5005: PRICE LEVELS INVALID"
            elif err_code and err:
                short_error = f"API {err_code}: {str(err).split('.')[0]}"
            else:
                short_error = str(err or "")
            if short_error:
                api_messages.append(f"{item}: {short_error}")
        # Summary row and each leg appear once; shared SL/TP are shown on the group row
        # and per-leg values only when broker-confirmed values differ.
        rows.append(("GROUP", "—", f"{float(total_lot):.2f}", master_sl, master_tp,
                     str(group.get("state", "ACTIVE")).replace("_", " ").upper(),
                     "YES" if group.get("active_triggered") else "NO"))
        for legrow in per_leg_rows:
            item, entry, lot, sl, tp, status, active = legrow
            # Avoid repeating shared SL/TP in both group and leg rows unless live values differ.
            sl_display = "Trail SL" if sl == master_trail else ("Master SL" if sl == master_sl else sl)
            tp_display = "Master TP" if tp == master_tp else tp
            rows.append((item, entry, lot, sl_display, tp_display, status, active))
        rows.append(("MAX RISK", "—", "—", f"${float(max_risk):.2f}", "—", "PLANNED GROSS", "—"))
        rows.append(("MAX PROFIT", "—", "—", "—", f"${float(max_profit):.2f}", "TARGET GROSS", "—"))
        # Current signal-group P/L: confirmed realized P/L plus live position
        # floating P/L, and the stored estimate for legs that never filled.
        active_pnl = float(dec(group.get("actual_filled_pnl", "0") or "0"))
        group_estimate_raw = group.get("estimated_unfilled_pnl")
        leg_estimate_total = 0.0
        for leg in legs:
            try:
                leg_estimate_total += float(dec(leg.get("estimated_unfilled_pnl", "0") or "0"))
            except Exception:
                pass
        inactive_pnl = float(dec(group_estimate_raw or "0")) if group_estimate_raw not in (None, "") and float(dec(group_estimate_raw or "0")) != 0 else leg_estimate_total

        group_open_position_ids = set()
        position_profit_available = False
        for leg in legs:
            pid = str(leg.get("position_id") or "")
            pos = next((p for p in positions if pid and str(p.get("position_id", "")) == pid), None)
            if pos:
                group_open_position_ids.add(pid)
                profit = pos.get("profit")
                if isinstance(profit, dict):
                    profit = profit.get("amount")
                if profit not in (None, ""):
                    try:
                        active_pnl += float(dec(profit))
                        position_profit_available = True
                    except Exception:
                        pass

        account_pnl = (daily_risk_state or {}).get("account_pnl", {}) or {}
        all_open_account_positions = [
            position for position in (snapshot.get("positions", []) or [])
            if str(position.get("state", "open")).lower() in {"open", "opened"}
        ]
        floating_attributed = position_profit_available
        if (
            group_open_position_ids
            and not floating_attributed
            and len(all_open_account_positions) == 1
            and str(all_open_account_positions[0].get("position_id") or "") in group_open_position_ids
            and account_pnl.get("date_ist") == datetime.now(IST).date().isoformat()
            and account_pnl.get("floating_pnl") not in (None, "")
        ):
            active_pnl += float(dec(account_pnl.get("floating_pnl")))
            floating_attributed = True
        floating_note = (
            " | floating not attributable"
            if group_open_position_ids and not floating_attributed else ""
        )
        net_pnl = active_pnl + inactive_pnl
        rows.append(("ACTIVE GROUP P/L", "—", "—", "—", "—", f"${active_pnl:+.2f}" + floating_note, "—"))
        rows.append(("INACTIVE EST. P/L", "—", "—", "—", "—", f"${inactive_pnl:+.2f}", "—"))
        rows.append(("OVERALL GROUP P/L", "—", "—", "—", "—", f"${net_pnl:+.2f}" + floating_note, "—"))
        account_pnl = (daily_risk_state or {}).get("account_pnl", {}) or {}
        if account_pnl.get("date_ist") == datetime.now(IST).date().isoformat():
            realized = dec(account_pnl.get("realized_closed_pnl", "0"))
            floating_raw = account_pnl.get("floating_pnl")
            total_raw = account_pnl.get("total_pnl_including_floating")
            rows.append(("DAILY REALIZED P/L", "—", "—", "—", "—", f"${float(realized):+.2f}", "—"))
            if floating_raw not in (None, ""):
                rows.append(("DAILY FLOATING P/L", "—", "—", "—", "—", f"${float(dec(floating_raw)):+.2f}", "—"))
            if total_raw not in (None, ""):
                rows.append(("DAILY TOTAL P/L", "—", "—", "—", "—", f"${float(dec(total_raw)):+.2f}", "—"))
        rows.append(("MASTER TRAILING SL", "—", "—", str(master_trail), "—", f"{'ON' if trailing_enabled else 'OFF'} | {trail_stage}", "—"))
        secondary_decision = group.get("secondary_20_decision") or {}
        if secondary_decision and str(secondary_decision.get("status", "")).startswith("SKIPPED"):
            rows.append(("20% ORDER", str(secondary_decision.get("entry_text") or "—"), str(secondary_decision.get("volume_text") or "—"), master_sl, master_tp, str(secondary_decision.get("status")), "NO"))
        trigger_errors = []
        for key in ("trigger_error", "error", "error_message", "preflight_error"):
            value = group.get(key)
            if value:
                trigger_errors.append(str(value))
        for leg in legs:
            for key in ("trigger_error", "error", "error_message", "preflight_error"):
                value = leg.get(key)
                if value:
                    trigger_errors.append(str(value))
        trigger_text = "; ".join(dict.fromkeys(trigger_errors)) if trigger_errors else "No trigger error recorded"
        rows.append(("TRIGGER / ERRORS", "—", "—", "—", "—", trigger_text, "—"))
        issue_text = "; ".join(api_messages) if api_messages else "No API rejection recorded"
        rows.append(("API WARNING", "—", "—", "—", "—", issue_text, "—"))
        title = f"KS TRADER DESK | {instrument} | {account_mode.upper()} | {now_ist} | {group_id}"
        print(_group_status_table_text(title, rows), flush=True)
        _LAST_DASHBOARD_SIGNATURE = signature
        return
    # Initialize dashboard rows before adding position/order/idle details.
    lines: list[str] = []
    if positions:
        position = positions[0]
        pid = str(position.get("position_id", "N/A"))
        side = str(position.get("direction", "unknown")).upper()
        entry_raw = position.get("open_price")
        volume_raw = position.get("volume")
        lock = store.get_json("trade_lock", {}) or {}
        trail = store.get_json("adaptive_trailing_state", {}) or {}
        sltp = _find_position_sltp_order(snapshot, instrument, pid) or {}
        entry = float(dec(entry_raw)) if entry_raw not in (None, "") else None
        volume = float(dec(volume_raw if volume_raw not in (None, "") else lock.get("volume"))) if (volume_raw not in (None, "") or lock.get("volume") not in (None, "")) else None
        tp_raw = sltp.get("take_profit_price") or lock.get("tp") or trail.get("initial_tp")
        sl_broker = sltp.get("stop_loss_price")
        # Prefer the latest SL confirmed and persisted after Exness snapshot confirmation.
        sl_current = trail.get("current_sl") or sl_broker
        sl_initial = trail.get("initial_sl") or lock.get("sl")
        # Match Indie chart valuation: use Bid close for both directions.
        current = None
        if not m1.empty:
            last = m1.iloc[-1]
            raw = last.get("close", None)
            if raw is not None and not pd.isna(raw):
                current = float(raw)
        tp = float(dec(tp_raw)) if tp_raw not in (None, "") else None
        initial_sl = float(dec(sl_initial)) if sl_initial not in (None, "") else None
        cur_sl = float(dec(sl_current)) if sl_current not in (None, "") else None
        risk_distance = abs(entry - initial_sl) if entry is not None and initial_sl is not None else None
        favourable = ((current-entry) if side == "BUY" else (entry-current)) if current is not None and entry is not None and side in {"BUY", "SELL"} else None
        r_multiple = favourable / risk_distance if favourable is not None and risk_distance and risk_distance > 0 else None
        tp_distance = abs(tp-entry) if tp is not None and entry is not None else None
        tp_progress = favourable / tp_distance * 100 if favourable is not None and tp_distance and tp_distance > 0 else None
        est_pl = favourable * contract_size * volume if favourable is not None and volume is not None else None
        risk_cash = risk_distance * contract_size * volume if risk_distance is not None and volume is not None else None
        trailing_pending = store.get_json("trailing_pending_operation", {}) or {}
        stage = trail.get("last_stage") or (" / ".join(trail.get("stages", [])) if trail.get("stages") else "Monitoring structure")
        lines += ["", f"TRADE IN PROGRESS : {side} POSITION", f"Position ID  : {pid}",
                  f"Lot / Volume : {volume:.2f}" if volume is not None else "Lot / Volume : N/A",
                  f"Entry Price  : {_display_price(entry, digits)}",
                  f"Market Price  : {_display_price(current, digits)}  (latest completed candle)",
                  f"Take Profit  : {_display_price(tp, digits)}",
                  f"Current Stop  : {_display_price(cur_sl, digits)}  (confirmed by Exness)",
                  f"Initial Stop  : {_display_price(initial_sl, digits)}" if initial_sl is not None else "Initial Stop  : Not available",
                  f"Initial Risk : {risk_distance:.{digits}f} price units" if risk_distance is not None else "Initial Risk : N/A",
                  f"Planned Risk  : ~${risk_cash:.2f}" if risk_cash is not None else "Planned Risk  : Not available",
                  f"Open P/L      : ~${est_pl:.2f} gross estimate" if est_pl is not None else "Open P/L      : Not available",
                  f"Open R       : {r_multiple:+.2f}R" if r_multiple is not None else "Open R       : N/A",
                  f"TP Progress  : {tp_progress:.1f}%" if tp_progress is not None else "TP Progress  : N/A",
                  f"Stop Manager  : {'ON' if trailing_enabled else 'OFF'} | Stage: {stage}"]
        if trailing_pending:
            lines.append(f"Stop Update   : Waiting for Exness to confirm {_display_price(trailing_pending.get('candidate_sl'), digits)}")
        else:
            lines.append("Stop Update   : No change pending")
        if est_pl is not None:
            lines.append("P/L note     : Gross estimate; excludes commission, swap and broker adjustments")
    elif orders:
        order = orders[0]
        lines += ["", f"WAITING FOR ENTRY : {str(order.get('direction', '')).upper()} LIMIT ORDER",
                  f"Order ID     : {order.get('order_id', 'N/A')}",
                  f"Direction    : {str(order.get('direction', 'N/A')).upper()}",
                  f"Entry Price  : {_display_price(order.get('price'), digits)}",
                  f"Stop Loss    : {_display_price(order.get('stop_loss_price'), digits)}",
                  f"Take Profit  : {_display_price(order.get('take_profit_price'), digits)}",
                  f"Volume       : {order.get('volume', 'N/A')}",
                  "Next Step     : Waiting for market price to reach the entry level",
                  "Safety        : No second XAUUSD entry will be placed while this order is active"]
    else:
        lines += ["", "TRADE STATUS : NO ACTIVE XAUUSD TRADE", "Watching completed 1-minute candles for the next valid setup."]
    risk_state = daily_risk_state or {}
    reduced_mode = bool(risk_state.get("reduced_mode", False))
    active_target = 3.0 if reduced_mode else risk_percent
    active_buffer = 1.0 if reduced_mode else risk_buffer_percent
    total_risk_percent = min(7.0, active_target + active_buffer)
    daily_budget = daily_opening_balance * Decimal(str(total_risk_percent)) / Decimal("100")
    daily_closed_pnl = dec(risk_state.get("realized_closed_pnl", "0"))
    mode_label = "REDUCED" if reduced_mode else "NORMAL"
    lines += ["", f"Daily Opening Balance: ${daily_opening_balance:.2f}",
              f"Daily Closed P/L      : ${float(daily_closed_pnl):+.2f}",
              f"Risk Mode             : {mode_label} ({active_target:.2f}% + {active_buffer:.2f}% = {total_risk_percent:.2f}%)",
              f"Risk Budget           : ${daily_budget:.2f}", 
              f"New Entries          : {'ON (DEMO LIMIT only)' if (os.getenv('TRADING_ENABLED', 'false').strip().lower() in {'1','true','yes','y','on'} and not (store.get_json('trade_lock', {}) or {}).get('active') and str((store.get_json('submission_state', {}) or {}).get('status', '')).lower() not in {'prepared', 'uncertain', 'acknowledged'}) else 'PAUSED/OFF'}",
              "=" * 68, ""]
    print(_dashboard_table_text(f"KS TRADER DESK | {instrument} | {account_mode.upper()} | {now_ist}", lines), flush=True)
    _LAST_DASHBOARD_SIGNATURE = signature


def pending_submission_blocks(store: StateStore, api: ExnessAPI, snapshot: dict, instrument: str) -> bool:
    """Automatically reconcile a persisted uncertain submission; never require manual DB edits.

    A completed persisted signal group is authoritative only when Exness currently
    shows no live order/position for this instrument. Otherwise query the original
    operation and run the existing broker-history trade-lock reconciler on a
    cooldown. Mutating order POSTs are never repeated here.
    """
    record = store.get_json("submission_state", {}) or {}
    status = str(record.get("status", "")).lower()
    if status not in {"prepared", "uncertain", "acknowledged"}:
        return False

    orders, positions = instrument_activity(snapshot, instrument)
    if orders or positions:
        record["status"] = "reconciled_present"
        record["reconciled_at"] = utc_iso(datetime.now(UTC))
        store.set_json("submission_state", record)
        logging.warning(
            "AUTOMATIC ORDER RECOVERY | Exness currently shows %d pending order(s) and %d open position(s). The bot adopted the broker state and will manage/wait; no duplicate entry will be sent.",
            len(orders), len(positions),
        )
        return False

    # A prior group reconciler may already have fully resolved the trade, while
    # submission_state remained stale/uncertain. Repair that stale flag at startup.
    group = store.get_json("trade_group", {}) or {}
    same_group = bool(record.get("group_id") and record.get("group_id") == group.get("group_id"))
    group_state = str(group.get("state", "")).lower()
    if same_group and not bool(group.get("active", True)) and group_state in {
        "completed", "group_completed", "closed", "resolved_terminal",
        "cancelled_unfilled", "rejected_confirmed_no_order",
    }:
        now = utc_iso(datetime.now(UTC))
        record.update({
            "status": "resolved_terminal",
            "resolved_at": now,
            "resolution": "persisted_group_terminal_and_no_live_broker_activity",
        })
        store.set_json("submission_state", record)
        lock = store.get_json("trade_lock", {}) or {}
        lock.update({"active": False, "state": "group_completed", "resolved_at": now})
        store.set_json("trade_lock", lock)
        logging.info("AUTOMATIC ORDER RECOVERY | Stale submission lock cleared: saved trade group is terminal and Exness confirms no live order/position.")
        return False

    # Poll Exness' original operation status. Terminal rejection is safe to clear
    # only after the fresh snapshot above confirms no live broker activity.
    operation_id = str(record.get("operation_id") or "")
    if not operation_id and same_group:
        for leg in (group.get("legs", []) or []):
            op = str(leg.get("operation_id") or "")
            if op and str(leg.get("status", "")).lower() in {
                "uncertain", "acknowledged", "submission_in_flight", "awaiting_visibility",
            }:
                operation_id = op
                break
    if operation_id:
        try:
            operation = api.operation_status(operation_id)
            operation_state = str(operation.get("status", "")).lower()
            if operation_state in {"rejected", "failed"}:
                now = utc_iso(datetime.now(UTC))
                record.update({
                    "status": "resolved_rejected",
                    "resolved_at": now,
                    "resolution": "exness_operation_terminal_rejection_and_no_live_broker_activity",
                    "operation_status": operation_state,
                })
                store.set_json("submission_state", record)
                lock = store.get_json("trade_lock", {}) or {}
                lock.update({"active": False, "state": "rejection_confirmed_no_order", "resolved_at": now})
                store.set_json("trade_lock", lock)
                logging.warning("AUTOMATIC ORDER RECOVERY | Exness confirmed the previous submission was %s and no live order/position exists. The stale entry hold is cleared.", operation_state)
                return False
        except Exception:
            logging.debug("Automatic submission operation-status check is temporarily unavailable; will retry.", exc_info=True)

    # Use the existing strict history reconciler to determine whether the order
    # filled and closed, was cancelled, or is still unresolved. Rate-limit this
    # history walk so the 24/7 loop does not hammer Exness on every poll.
    last_check = _history_time(record.get("last_auto_reconcile_at"))
    now_dt = datetime.now(UTC)
    if last_check is None or (now_dt - last_check).total_seconds() >= 60:
        record["last_auto_reconcile_at"] = utc_iso(now_dt)
        store.set_json("submission_state", record)
        lock = store.get_json("trade_lock", {}) or {}
        recovery_group = store.get_json("trade_group", {}) or {}
        # A crash/older build may leave an uncertain submission record but no
        # active trade_lock. Reconstruct a minimal history-matching lock from the
        # persisted signal/group so reconciliation still runs automatically.
        # This does not submit, cancel, or modify any broker order.
        if not lock.get("active") and status in {"prepared", "uncertain", "acknowledged"}:
            first_leg = next(iter(recovery_group.get("legs", []) or []), {})
            lock = {
                "active": True,
                "state": "automatic_submission_recovery",
                "group_id": record.get("group_id") or recovery_group.get("group_id"),
                "instrument": record.get("instrument") or recovery_group.get("instrument") or instrument,
                "side": record.get("side") or recovery_group.get("side"),
                "entry": record.get("entry") or recovery_group.get("midpoint_entry") or first_leg.get("entry_text"),
                "sl": record.get("sl") or recovery_group.get("sl_text") or first_leg.get("sl_text"),
                "tp": record.get("tp") or recovery_group.get("tp_text") or first_leg.get("tp_text"),
                "volume": record.get("volume") or first_leg.get("volume_text") or recovery_group.get("total_volume_text"),
                "order_id": record.get("order_id") or first_leg.get("order_id"),
                "position_id": record.get("position_id") or first_leg.get("position_id"),
                "created_at": record.get("created_at") or recovery_group.get("created_at") or utc_iso(now_dt - timedelta(days=2)),
                "operation_id": record.get("operation_id") or first_leg.get("operation_id"),
            }
            store.set_json("trade_lock", lock)
            logging.info("AUTOMATIC ORDER RECOVERY | Rebuilt missing local trade lock from saved submission/group metadata; reconciling broker history.")
        history_reconcile_attempted = bool(lock.get("active") or recovery_group.get("active"))
        if history_reconcile_attempted:
            try:
                refresh_trade_lock(store, api, snapshot, instrument, None, None)
            except Exception:
                logging.warning("AUTOMATIC ORDER RECOVERY | Exness history is not complete yet; keeping the safety lock and retrying automatically.")
                logging.debug("Automatic order-history reconciliation details:", exc_info=True)

        # Re-read state because refresh_trade_lock may have resolved it.
        refreshed_record = store.get_json("submission_state", {}) or {}
        refreshed_status = str(refreshed_record.get("status", "")).lower()
        refreshed_lock = store.get_json("trade_lock", {}) or {}
        refreshed_group = store.get_json("trade_group", {}) or {}
        terminal_group = (
            same_group
            and not bool(refreshed_group.get("active", True))
            and str(refreshed_group.get("state", "")).lower() in {
                "completed", "group_completed", "closed", "resolved_terminal",
                "cancelled_unfilled", "rejected_confirmed_no_order",
            }
        )
        history_resolved_lock = history_reconcile_attempted and not refreshed_lock.get("active")
        if terminal_group or history_resolved_lock or (not refreshed_lock.get("active") and refreshed_status not in {"prepared", "uncertain", "acknowledged"}):
            if refreshed_status in {"prepared", "uncertain", "acknowledged"}:
                refreshed_record.update({
                    "status": "resolved_terminal",
                    "resolved_at": utc_iso(datetime.now(UTC)),
                    "resolution": "automatic_broker_history_reconciliation_no_live_activity",
                })
                store.set_json("submission_state", refreshed_record)
            logging.info("AUTOMATIC ORDER RECOVERY | Previous order state reconciled. New entries may resume when the next valid signal appears.")
            return False

    logging.warning(
        "AUTOMATIC ORDER RECOVERY | Previous submission is still being checked by Exness. New entries remain blocked for safety; the bot will keep monitoring and retry reconciliation automatically.")
    return True


def create_submission_record(store: StateStore, signal: dict) -> str:
    """Persist intent and idempotency key before the single mutating POST."""
    existing = store.get_json("submission_state", {}) or {}
    if str(existing.get("status", "")).lower() in {"prepared", "uncertain", "acknowledged"}:
        raise RuntimeError("An earlier order submission is unresolved; refusing another POST.")
    idem = "KS1-" + uuid.uuid4().hex
    record = {
        "status": "prepared",
        "idempotency_key": idem,
        "created_at": utc_iso(datetime.now(UTC)),
        "instrument": signal.get("instrument"),
        "side": signal.get("side"),
        "bar_time": signal.get("bar_time"),
        "entry": signal.get("entry_text"),
        "sl": signal.get("sl_text"),
        "tp": signal.get("tp_text"),
        "volume": signal.get("volume_text"),
        "risk_cash": signal.get("risk_cash"),
    }
    store.set_json("submission_state", record)
    store.set_json("trade_lock", {
        "active": True,
        "state": "submission_pending",
        "created_at": record["created_at"],
        "instrument": record.get("instrument"),
        "side": record.get("side"),
        "entry": record.get("entry"),
        "sl": record.get("sl"),
        "tp": record.get("tp"),
        "volume": record.get("volume"),
        "order_id": None,
        "position_id": None,
        "idempotency_key": idem,
    })
    return idem


def update_submission(store: StateStore, status: str, **fields: Any) -> None:
    record = store.get_json("submission_state", {}) or {}
    record.update(fields)
    record["status"] = status
    record["updated_at"] = utc_iso(datetime.now(UTC))
    store.set_json("submission_state", record)




# ---------------- SIDEWAYS MARKET PROTECTION ----------------
def _sideways_completed_candles(frame: pd.DataFrame, minutes: int = 5) -> pd.DataFrame:
    """Use closed candles only; discard a still-forming M5 candle."""
    if frame is None or frame.empty or "time" not in frame.columns:
        return pd.DataFrame()
    data = frame.copy()
    data["time"] = pd.to_datetime(data["time"], utc=True, errors="coerce")
    data = data.dropna(subset=["time"]).sort_values("time")
    cutoff = pd.Timestamp.now(tz="UTC") - pd.Timedelta(minutes=minutes)
    data = data[data["time"] <= cutoff].copy()
    for col in ("high", "low", "close"):
        if col not in data.columns:
            return pd.DataFrame()
        data[col] = pd.to_numeric(data[col], errors="coerce")
    return data.dropna(subset=["high", "low", "close"]).reset_index(drop=True)


def _sideways_indicator_reading(frame: pd.DataFrame) -> dict | None:
    """ADX(14), ATR(14) vs ATR(50), Bollinger width(20,2) vs 50-bar mean."""
    data = _sideways_completed_candles(frame, 5)
    if len(data) < 80:
        return None
    high, low, close = data["high"], data["low"], data["close"]
    prev_close = close.shift(1)
    tr = pd.concat([high-low, (high-prev_close).abs(), (low-prev_close).abs()], axis=1).max(axis=1)
    up, down = high.diff(), -low.diff()
    plus_dm = up.where((up > down) & (up > 0), 0.0)
    minus_dm = down.where((down > up) & (down > 0), 0.0)
    atr14 = tr.rolling(14, min_periods=14).mean()
    atr50 = atr14.rolling(50, min_periods=50).mean()
    plus_di = 100.0 * plus_dm.rolling(14, min_periods=14).mean() / atr14.replace(0, float("nan"))
    minus_di = 100.0 * minus_dm.rolling(14, min_periods=14).mean() / atr14.replace(0, float("nan"))
    dx = 100.0 * (plus_di-minus_di).abs() / (plus_di+minus_di).replace(0, float("nan"))
    adx = dx.rolling(14, min_periods=14).mean()
    mid = close.rolling(20, min_periods=20).mean()
    width = (4.0 * close.rolling(20, min_periods=20).std(ddof=0)) / mid.abs().replace(0, float("nan"))
    width_avg = width.rolling(50, min_periods=50).mean()
    vals = [adx.iloc[-1], atr14.iloc[-1], atr50.iloc[-1], width.iloc[-1], width_avg.iloc[-1]]
    if any(pd.isna(v) or not math.isfinite(float(v)) for v in vals):
        return None
    av, at, at50, bw, bw50 = map(float, vals)
    votes = int(av < 18.0) + int(at50 > 0 and at < 0.70*at50) + int(bw50 > 0 and bw < 0.80*bw50)
    return {"adx":av,"atr":at,"atr50":at50,"bb_width":bw,"bb_width50":bw50,
            "votes":votes,"bar_time":data.iloc[-1]["time"].isoformat()}


def update_sideways_market_state(store: StateStore, m5: pd.DataFrame) -> dict:
    """Block after 2 consecutive sideways M5 bars; resume after 3 healthy bars."""
    state = store.get_json("sideways_market_state", {}) or {}
    state.setdefault("blocked", False)
    state.setdefault("sideways_streak", 0)
    state.setdefault("healthy_streak", 0)
    reading = _sideways_indicator_reading(m5)
    if reading is None or reading["bar_time"] == state.get("last_evaluated_m5"):
        return state
    state["last_evaluated_m5"] = reading["bar_time"]
    state["last_reading"] = reading
    if reading["votes"] >= 2:
        state["sideways_streak"] = int(state.get("sideways_streak",0))+1
        state["healthy_streak"] = 0
        if state["sideways_streak"] >= 2 and not state["blocked"]:
            state["blocked"] = True
            logging.warning("SIDEWAYS MARKET PROTECTION | BLOCK NEW ENTRIES | ADX %.1f | ATR ratio %.2f | BB width ratio %.2f", reading["adx"], reading["atr"]/reading["atr50"] if reading["atr50"] else 0, reading["bb_width"]/reading["bb_width50"] if reading["bb_width50"] else 0)
    else:
        state["healthy_streak"] = int(state.get("healthy_streak",0))+1
        state["sideways_streak"] = 0
        if state["healthy_streak"] >= 3 and state["blocked"]:
            state["blocked"] = False
            logging.info("SIDEWAYS MARKET PROTECTION | TREND RECOVERED | 3 consecutive healthy M5 readings.")
    store.set_json("sideways_market_state", state)
    return state


def cancel_unfilled_group_for_sideways(store: StateStore, api: ExnessAPI, instrument: str, exit_price: float) -> None:
    """Cancel pending unfilled legs in the current bot group; do not touch positions."""
    group = store.get_json("trade_group", {}) or {}
    if not group or not group.get("active") or str(group.get("instrument","")).upper() != str(instrument).upper():
        return
    changed = False
    for leg in group.get("legs", []) or []:
        if str(leg.get("status","")).lower() not in {"pending","cancel_rejected","cancel_requested"}:
            continue
        if leg.get("position_id") or not leg.get("order_id"):
            continue
        try:
            leg["sideways_cancel_reason"] = "SIDEWAYS_MARKET_PROTECTION"
            _group_leg_cancel(store, api, group, leg, "SIDEWAYS", float(exit_price))
            changed = True
        except Exception as exc:
            logging.error("SIDEWAYS MARKET PROTECTION | pending cancellation failed for %s: %s", leg.get("leg"), exc)
    if changed:
        store.set_json("trade_group", group)
        logging.warning("SIDEWAYS MARKET PROTECTION | requested cancellation of unfilled legs in group %s; open positions untouched.", group.get("group_id"))


def main() -> int:
    cfg = Config.from_env()
    trailing_enabled = env_bool("ADAPTIVE_TRAILING_ENABLED", cfg.trading_enabled)
    configure_logging(cfg.log_level)
    logging.info("=" * 68)
    logging.info("KS TRADER DESK is starting (version %s).", APP_VERSION)
    logging.info("Account: %s | Market: %s", cfg.account_mode.upper(), cfg.instrument)
    logging.info(
        "Normal risk: %.2f%% + %.2f%% buffer = %.2f%% maximum | Reduced after 30%% daily closed loss: 3%% + 1%% | Reward ratio: %s | Stop manager: %s",
        cfg.risk_percent, cfg.risk_buffer_percent,
        min(7.0, cfg.risk_percent + cfg.risk_buffer_percent),
        cfg.risk_reward, "ON" if trailing_enabled else "OFF",
    )
    if cfg.trading_enabled:
        logging.info("New DEMO entries are ENABLED. The bot will only trade when a valid signal appears.")
    else:
        logging.info("New entries are OFF. The bot will monitor signals without placing orders.")
    logging.info("=" * 68)

    store = StateStore(cfg.db_path)
    api = ExnessAPI(cfg)
    api.discover_access_point()
    conditions = api.instrument_conditions()
    # Instrument conditions are required for broker-valid prices/volume.
    # API limits are informational only, so do not request them on startup.
    Path("exness_instrument_conditions.json").write_text(
        json.dumps(conditions, indent=2, default=str), encoding="utf-8"
    )
    tick_monitor = LiveTickMonitor(api, cfg.instrument)
    tick_monitor.start()
    log_table("BROKER SETTINGS", [
        ("Entry method", "50% midpoint + 20% retracement LIMIT"),
        ("Market fallback", "Disabled"),
        ("Instrument", cfg.instrument),
        ("Price decimals", conditions.get("point_digits", "n/a")),
        ("Minimum lot", conditions.get("volume_min", "n/a")),
        ("Lot step", conditions.get("volume_step", "n/a")),
    ])
    if conditions.get("instrument") and str(conditions["instrument"]).upper() != cfg.instrument.upper():
        raise RuntimeError(f"API returned conditions for {conditions['instrument']}, not {cfg.instrument}.")

    pending = {}
    try:
        pending = store.get_json("breakout_pending", {}) or {}
    except Exception:
        logging.error("Saved breakout setup could not be restored. A fresh setup will be used.")
        logging.debug("Breakout restore details:", exc_info=True)
        pending = {}

    snap = api.snapshot()
    orders, positions = instrument_activity(snap, cfg.instrument)
    logging.info("Account check: %d pending order(s) and %d open position(s) found for %s.", len(orders), len(positions), cfg.instrument)
    daily_opening_balance, daily_balance_date = get_daily_opening_balance(store, api, snap)
    daily_risk_state = get_daily_risk_state(store, daily_opening_balance, daily_balance_date)
    daily_risk_state = reconcile_daily_account_pnl_from_exness(
        store, api, daily_opening_balance, daily_balance_date, snap
    )
    active_target, active_buffer, active_budget = daily_risk_parameters(cfg, daily_opening_balance, daily_risk_state)
    logging.info(
        "Today's opening balance (%s IST): $%.2f | %s risk %.2f%% + buffer %.2f%% = maximum $%.2f (%.2f%%).",
        daily_balance_date, float(daily_opening_balance),
        "REDUCED" if daily_risk_state.get("reduced_mode") else "NORMAL",
        active_target, active_buffer, float(active_budget), active_target + active_buffer,
    )
    unresolved = pending_submission_blocks(store, api, snap, cfg.instrument)
    existing_lock = store.get_json("trade_lock", {}) or {}
    previous_submission = store.get_json("submission_state", {}) or {}
    if str(previous_submission.get("status", "")).lower() == "rejected":
        if not existing_lock.get("active"):
            existing_lock.update({
                "active": True,
                "state": "rejected_signal_hold",
                "http_status": previous_submission.get("http_status"),
                "created_at": previous_submission.get("created_at") or utc_iso(datetime.now(UTC)),
            })
            store.set_json("trade_lock", existing_lock)
        logging.warning("A previous entry was rejected by Exness. New entries remain paused until that rejection is reviewed.")
    if not existing_lock.get("active") and (orders or positions):
        # Adopt existing activity after an upgrade/restart rather than risking
        # a second entry while a pre-existing trade is still running.
        adopted = orders[0] if orders else None
        adopted_position = positions[0] if positions else None
        created = (adopted or adopted_position or {}).get("create_time") or utc_iso(datetime.now(UTC))
        store.set_json("trade_lock", {
            "active": True, "state": "adopted_existing_activity", "created_at": created,
            "instrument": cfg.instrument,
            "order_id": (adopted or {}).get("order_id"),
            "position_id": (adopted_position or {}).get("position_id"),
            "side": (adopted or adopted_position or {}).get("direction"),
            "entry": str((adopted or {}).get("price", "")),
        })
        logging.warning("An existing XAUUSD order or position was found. The bot will manage/wait for it and will not place another entry.")
    last_bar = store.get("last_processed_m1", "")
    # Strategy evaluation is tick-woken at candle boundaries. REST snapshots
    # remain rate-limited to the configured broker reconciliation cadence.
    last_secondary_full_check = time.monotonic()
    last_broker_reconcile = 0.0
    last_market_minute = None
    candle_retry_at = 0.0
    candle_retry_deadline = 0.0
    candle_retry_delay = 0.5
    cached_m1 = pd.DataFrame()
    cached_m3 = pd.DataFrame()
    cached_m5 = pd.DataFrame()
    sideways_protection_enabled = env_bool("SIDEWAYS_MARKET_PROTECTION", True)
    logging.info("SIDEWAYS MARKET PROTECTION | %s | ADX<18, ATR<70%% of ATR50, BB width<80%% of 50-bar mean; 2/3 conditions.", "ON" if sideways_protection_enabled else "OFF")

    while True:
        try:
            # Rate-limit recovery is NON-BLOCKING: keep receiving live ticks and
            # persist pending-order expiry events while REST is cooling down.
            # No REST calls are attempted until Exness' cooldown expires.
            cooldown_remaining = api.rate_limit_remaining()
            if cooldown_remaining > 0:
                if tick_monitor is not None:
                    tick_monitor.wait_for_tick(timeout=min(0.25, cooldown_remaining))
                safety_tick = tick_monitor.latest() if tick_monitor is not None else None
                safety_group = store.get_json("trade_group", {}) or {}
                if safety_group.get("active") and not safety_group.get("group_exit_event"):
                    safety_exit = _pending_initial_sl_from_tick(safety_group, safety_tick)
                    safety_source = "rate_limit_live_quote_initial_sl"
                    if safety_exit is None:
                        safety_exit = _pending_group_exit_from_tick(safety_group, safety_tick)
                        safety_source = "rate_limit_live_quote_pending_group_exit"
                    if safety_exit is not None:
                        if isinstance(safety_exit, tuple):
                            safety_reason, safety_price = safety_exit
                        else:
                            safety_reason, safety_price = "SL", safety_exit
                        safety_group["group_exit_event"] = {
                            "reason": safety_reason,
                            "price": safety_price,
                            "detected_at": utc_iso(datetime.now(UTC)),
                            "source": safety_source,
                            "bid": (safety_tick or {}).get("bid"),
                            "ask": (safety_tick or {}).get("ask"),
                            "tick_age_seconds": (safety_tick or {}).get("age_seconds"),
                            "deferred_until_api_available": True,
                        }
                        store.set_json("trade_group", safety_group)
                        logging.warning(
                            "RATE-LIMIT SAFETY EVENT | %s at %s detected from live quote and saved; "
                            "pending sibling cancellation will resume automatically after API cooldown.",
                            safety_reason, safety_price,
                        )
                continue

            # Live ticks wake this loop immediately. A short silent fallback
            # only handles minute edges/reconnect gaps when no tick is arriving;
            # it is not a 15-second setup polling interval.
            if tick_monitor is not None:
                tick_monitor.wait_for_tick(timeout=0.25)
            wall_now = datetime.now(UTC)
            market_minute = wall_now.replace(second=0, microsecond=0)
            now_mono = time.monotonic()
            candle_due = (
                last_market_minute is None
                or market_minute > last_market_minute
                or (
                    candle_retry_at > 0
                    and now_mono >= candle_retry_at
                    and now_mono <= candle_retry_deadline
                    and market_minute == last_market_minute
                )
            )
            broker_due = time.monotonic() - last_broker_reconcile >= cfg.poll_seconds
            retry_group = store.get_json("trade_group", {}) or {}
            retry_legs = retry_group.get("legs", []) or []
            prepared_group_leg = (
                bool(retry_group.get("active"))
                and any(str(leg.get("status", "")).lower() in {"prepared", "waiting_for_midpoint_confirmation"}
                        for leg in retry_legs)
                and not retry_group.get("group_exit_event")
            )
            pending_order_sl_watch = bool(
                tick_monitor is not None
                and any(_pending_order_original_sl_crossed(order, tick_monitor.latest())
                        for order in (orders or []))
            )
            # Keep watching every active group that still has an unfilled
            # broker leg. This includes (a) a lone 50% order when the 20% leg
            # was skipped, (b) a pending sibling after another leg filled,
            # and (c) a group whose exit event is already recorded but whose
            # cancellation is still awaiting broker confirmation.
            pending_group_watch = (
                bool(retry_group.get("active"))
                and any(
                    str(leg.get("status", "")).lower() in {
                        "prepared", "waiting_for_midpoint_confirmation", "pending", "acknowledged", "awaiting_visibility",
                        "awaiting_order_id_for_cancel", "cancel_requested", "cancel_rejected",
                    } and not str(leg.get("position_id") or "")
                    for leg in retry_legs
                )
            )
            if prepared_group_leg or pending_group_watch or pending_order_sl_watch:
                now_monotonic = time.monotonic()
                if now_monotonic - last_secondary_full_check < cfg.poll_seconds:
                    # Do not hit REST candle/snapshot endpoints in this fast
                    # retry path. Only inspect the already-streamed fresh quote.
                    tick = tick_monitor.latest() if tick_monitor is not None else None
                    if tick and (
                        bool(retry_group.get("group_exit_event"))
                        or _pending_initial_sl_from_tick(retry_group, tick) is not None
                        or _pending_group_exit_from_tick(retry_group, tick) is not None
                        or any(_pending_order_original_sl_crossed(order, tick) for order in (orders or []))
                    ):
                        fast_snapshot = api.snapshot()
                        cancel_bot_pending_orders_past_original_sl(store, api, fast_snapshot, cfg.instrument, tick)
                        refresh_trade_lock(store, api, fast_snapshot, cfg.instrument, None, tick)
                        time.sleep(0.25)
                        continue
                    if prepared_group_leg and tick:
                        try:
                            candidate_type = select_adaptive_pending_order_type(
                                str(retry_group.get("side")),
                                str(retry_legs[1].get("entry_text")),
                                tick,
                            )
                        except (ValueError, InvalidOperation):
                            candidate_type = None
                        if candidate_type is not None:
                            advance_group_submission(store, api, tick_monitor)
                    if not candle_due and not broker_due:
                        time.sleep(0.25)
                        continue
                last_secondary_full_check = now_monotonic

            if not candle_due and not broker_due:
                # All continuous quote checks above are internal; no CMD status
                # line and no REST candle/snapshot request on every tick.
                continue

            if candle_due:
                if last_market_minute is None or market_minute > last_market_minute:
                    candle_retry_deadline = now_mono + 3.0
                    candle_retry_delay = 0.5
                m1 = api.candles("M1", max(300, min(cfg.candles_count, 300)))
                last_market_minute = market_minute
                if not m1.empty:
                    cached_m1 = m1
                    candidate_bar = m1.iloc[-1]["time"].isoformat()
                    if not last_bar or candidate_bar != last_bar:
                        candle_retry_at = 0.0
                        candle_retry_deadline = 0.0
                        candle_retry_delay = 0.5
                    else:
                        candle_retry_at = time.monotonic() + candle_retry_delay
                        candle_retry_delay = min(1.0, candle_retry_delay * 1.5)
                else:
                    m1 = cached_m1
                    candle_retry_at = time.monotonic() + candle_retry_delay
                    candle_retry_delay = min(1.0, candle_retry_delay * 1.5)
            else:
                m1 = cached_m1

            # Always reconcile existing orders before any same-bar/indicator
            # early-continue. Pending-order safety is independent of new signals.
            # The live quote catches a level already passed at startup, even if
            # no new completed M1 candle has formed since last_processed_m1.
            management_tick = tick_monitor.latest() if tick_monitor is not None else None
            if broker_due:
                snap = api.snapshot()
                last_broker_reconcile = time.monotonic()
            active_orders, open_positions = instrument_activity(snap, cfg.instrument)
            orders = active_orders  # refresh the fast-path pending-order watch from Exness
            cancel_bot_pending_orders_past_original_sl(store, api, snap, cfg.instrument, management_tick)
            trade_locked = refresh_trade_lock(
                store, api, snap, cfg.instrument,
                m1 if (m1 is not None and not m1.empty) else None,
                management_tick,
            )
            if trade_locked:
                exit_group = store.get_json("trade_group", {}) or {}
                if str((exit_group.get("group_exit_event") or {}).get("reason", "")).upper() == "OPPOSITE_SIGNAL":
                    reconcile_group_opposite_signal_exit(store, api, snap, cfg.instrument)
                    snap = api.snapshot()
                    active_orders, open_positions = instrument_activity(snap, cfg.instrument)
                    trade_locked = refresh_trade_lock(store, api, snap, cfg.instrument,
                        m1 if (m1 is not None and not m1.empty) else None, management_tick)
                advance_group_submission(store, api, tick_monitor)
                active_group = store.get_json("trade_group", {}) or {}
                if active_group.get("active"):
                    snap = api.snapshot()
                    active_orders, open_positions = instrument_activity(snap, cfg.instrument)

            if m1.empty:
                # No closed candle yet; retry silently on the next tick/short
                # fallback wake instead of sleeping for a full polling period.
                continue

            if candle_due:
                m3 = api.candles("M3", max(100, min(cfg.candles_count, 300)))
                if not m3.empty:
                    cached_m3 = m3
            else:
                m3 = cached_m3
            if m3.empty:
                continue
            if candle_due:
                m5 = api.candles("M5", max(100, min(cfg.candles_count, 300)))
                if not m5.empty:
                    cached_m5 = m5
            else:
                m5 = cached_m5
            if len(m1) < 210 or len(m3) < 55:
                logging.debug("Waiting for enough completed market candles before checking for a signal.")
                continue
            bar_ts = m1.iloc[-1]["time"].isoformat()
            confirmed_setup = store.get_json("confirmed_setup", {}) or {}
            if bar_ts == last_bar and not confirmed_setup:
                # A waiting 20% leg is retried from fresh WebSocket ticks in
                # the fast path above; avoid adding another full poll delay.
                current_group = store.get_json("trade_group", {}) or {}
                current_legs = current_group.get("legs", []) or []
                waiting_secondary = (
                    bool(current_group.get("active"))
                    and len(current_legs) > 1
                    and str(current_legs[1].get("status", "")).lower() == "prepared"
                )
                # The tick event / minute-edge fallback drives the next pass.
                continue

            daily_opening_balance, daily_balance_date = get_daily_opening_balance(store, api, snap)
            # Re-fetch full deal history only when account balance changes or
            # every 5 minutes as a safety refresh. Snapshot equity supplies
            # floating P/L each minute without another history request.
            daily_risk_state = get_daily_risk_state(store, daily_opening_balance, daily_balance_date)
            cached_account_pnl = daily_risk_state.get("account_pnl") or {}
            account_state_now = snap.get("account_state") or {}
            balance_now = account_state_now.get("balance")
            cached_balance = cached_account_pnl.get("account_balance")
            balance_changed = (
                balance_now not in (None, "")
                and cached_balance not in (None, "")
                and dec(balance_now) != dec(cached_balance)
            )
            last_reconciled_raw = daily_risk_state.get("broker_reconciled_at")
            try:
                last_reconciled_dt = datetime.fromisoformat(str(last_reconciled_raw).replace("Z", "+00:00"))
                reconcile_due = (datetime.now(UTC) - last_reconciled_dt.astimezone(UTC)).total_seconds() >= 300
            except Exception:
                reconcile_due = True
            if (
                cached_account_pnl.get("date_ist") != daily_balance_date
                or balance_changed
                or reconcile_due
            ):
                # A balance change signals a possible new close; bypass any
                # startup history cache so capital protection sees fresh deals.
                if balance_changed:
                    _RECENT_EXNESS_DEALS_CACHE.clear()
                daily_risk_state = reconcile_daily_account_pnl_from_exness(
                    store, api, daily_opening_balance, daily_balance_date, snap
                )
            else:
                equity_now = account_state_now.get("equity")
                if balance_now not in (None, "") and equity_now not in (None, ""):
                    floating_now = _deal_money_amount(equity_now) - _deal_money_amount(balance_now)
                    cached_account_pnl["floating_pnl"] = str(floating_now)
                    cached_account_pnl["total_pnl_including_floating"] = str(
                        dec(cached_account_pnl.get("realized_closed_pnl", "0")) + floating_now
                    )
                    cached_account_pnl["updated_at"] = utc_iso(datetime.now(UTC))
                    daily_risk_state["account_pnl"] = cached_account_pnl
                    store.set_json("daily_risk_state", daily_risk_state)
            unresolved = pending_submission_blocks(store, api, snap, cfg.instrument)
            # Run once per newly completed M1 candle. Pending orders are ignored;
            # only an actually open position with its linked active SLTP order is managed.
            if trade_locked and open_positions:
                # Position management remains active even when new entries are disabled.
                run_dynamic_take_profit(store, api, snap, m1, conditions, cfg.instrument)
                snap = api.snapshot()
            if trade_locked and open_positions and trailing_enabled:
                run_adaptive_trailing(store, api, snap, m1, conditions, cfg.instrument)
            if trade_locked or active_orders or open_positions:
                display_trade_dashboard(
                    store, snap, m1, cfg.instrument, cfg.account_mode, cfg.contract_size,
                    daily_opening_balance, cfg.risk_percent, cfg.risk_buffer_percent,
                    conditions, trailing_enabled, daily_risk_state,
                )
            # Signal monitoring is independent from trade management. The bot
            # evaluates every newly completed M1 candle even while an earlier
            # order/position is active. The broker-side submission guard below
            # still prevents overlapping groups.
            if trade_locked or unresolved or active_orders or open_positions:
                logging.debug(
                    "Signal monitoring active | %d pending order(s), %d open position(s); overlapping submissions blocked.",
                    len(active_orders), len(open_positions),
                )

            daily_opening_balance, daily_balance_date = get_daily_opening_balance(store, api, snap)
            # Account P/L and capital-protection mode were reconciled from Exness
            # immediately above. Reuse that state here; avoid duplicate REST history calls.
            daily_risk_state = get_daily_risk_state(store, daily_opening_balance, daily_balance_date)
            active_target, active_buffer, active_budget = daily_risk_parameters(cfg, daily_opening_balance, daily_risk_state)
            risk_cfg = replace(cfg, account_capital=float(daily_opening_balance))
            active_group_for_signal = store.get_json("trade_group", {}) or {}
            # Once the 50% primary leg is broker-confirmed filled, initialize
            # the Indie add-on marker clock from the current completed M1 bar.
            if (
                active_group_for_signal.get("active")
                and active_group_for_signal.get("active_triggered")
                and not active_group_for_signal.get("indie_addon_state_initialized")
            ):
                primary_leg_for_addon = next(
                    (leg for leg in (active_group_for_signal.get("legs", []) or [])
                     if str(leg.get("leg", "")).upper() == "MIDPOINT_50"
                     and str(leg.get("status", "")).lower() == "filled"
                     and leg.get("position_id")),
                    None,
                )
                if primary_leg_for_addon:
                    active_group_for_signal["indie_entry_count"] = 1
                    active_group_for_signal["indie_last_entry_price"] = primary_leg_for_addon.get(
                        "entry", active_group_for_signal.get("midpoint_entry")
                    )
                    primary_position_id = str(primary_leg_for_addon.get("position_id") or "")
                    primary_position = next(
                        (pos for pos in (snap.get("positions", []) or [])
                         if str(pos.get("position_id", "")) == primary_position_id),
                        None,
                    )
                    primary_fill_time = (
                        primary_leg_for_addon.get("position_create_time")
                        or primary_leg_for_addon.get("filled_at")
                        or (primary_position or {}).get("create_time")
                    )
                    if primary_fill_time:
                        active_group_for_signal["indie_last_entry_bar_time"] = pd.to_datetime(
                            primary_fill_time, utc=True
                        ).floor("min").isoformat()
                    else:
                        active_group_for_signal["indie_last_entry_bar_time"] = pd.Timestamp(
                            m1.iloc[-1]["time"]
                        ).isoformat()
                    active_group_for_signal["indie_addon_state_initialized"] = True
                    store.set_json("trade_group", active_group_for_signal)

            # A confirmation candle's setup is durable unless sideways protection blocks new entries.
            sideways_blocked = False
            if sideways_protection_enabled:
                sideways_state = update_sideways_market_state(store, m5)
                sideways_blocked = bool(sideways_state.get("blocked"))
            confirmed_setup = store.get_json("confirmed_setup", {}) or {}
            if sideways_blocked:
                signal = None
                if confirmed_setup:
                    store.set_json("confirmed_setup", {})
                store.set("last_processed_m1", bar_ts)
                last_bar = bar_ts
                cancel_unfilled_group_for_sideways(store, api, cfg.instrument, float(m1.iloc[-1]["close"]))
            elif confirmed_setup:
                # A confirmed setup takes priority over every later signal.
                signal = confirmed_setup
            elif unresolved:
                # Exness is still reconciling the already-confirmed submission.
                # Do not discover a replacement entry during this recovery
                # window; let the existing persisted trade_group recover first.
                signal = None
                store.set("last_processed_m1", bar_ts)
                last_bar = bar_ts
            else:
                signal, pending = compute_signal(
                    m1, m3, risk_cfg, pending, active_target, active_buffer,
                    active_group=active_group_for_signal,
                )
                if signal and signal.get("kind") != "INDIE_EVENT":
                    signal["instrument"] = cfg.instrument
                    signal["confirmation_bar_time"] = bar_ts
                    # Persist the confirmed setup first so a failure while saving
                    # auxiliary strategy state cannot lose this entry.
                    store.set_json("confirmed_setup", signal)
                store.set_json("breakout_pending", pending)
                # Consume this closed bar after saving the confirmed setup.
                store.set("last_processed_m1", bar_ts)
                last_bar = bar_ts

            if signal and signal.get("kind") == "PENDING_REPRICE":
                reprice_pending_group_from_signal(store, api, snap, signal, conditions,
                    tick_monitor.latest() if tick_monitor is not None else None)
                signal = None

            if signal and signal.get("kind") == "INDIE_EVENT":
                event_group = store.get_json("trade_group", {}) or {}
                for event in signal.get("events", []):
                    event_type = event.get("type")
                    if event_type == "OPPOSITE_SIGNAL_EXIT":
                        event_group["indie_early_exit_warned"] = True
                        event_group["group_exit_event"] = {
                            "reason":"OPPOSITE_SIGNAL",
                            "price":float(event.get("exit_reference_price") or 0.0),
                            "exit_reference_price":float(event.get("exit_reference_price") or 0.0),
                            "detected_at":utc_iso(datetime.now(UTC)),
                            "source":"confirmed_opposite_signal_failure_score_3_of_4",
                            "failure_score":int(event.get("failure_score",0)),
                        }
                        store.set_json("trade_group",event_group)
                        reconcile_group_opposite_signal_exit(store,api,snap,cfg.instrument)
                        snap=api.snapshot()
                        refresh_trade_lock(store,api,snap,cfg.instrument,m1,tick_monitor.latest() if tick_monitor is not None else None)
                    elif event_type == "PENDING_SETUP_INVALIDATED":
                        event_group["group_exit_event"] = {
                            "reason":"SETUP_INVALIDATED",
                            "price":float(event.get("exit_reference_price") or 0.0),
                            "detected_at":utc_iso(datetime.now(UTC)),
                            "source":"opposite_confirmed_setup_before_fill",
                        }
                        store.set_json("trade_group",event_group)
                        refresh_trade_lock(store,api,api.snapshot(),cfg.instrument,m1,tick_monitor.latest() if tick_monitor is not None else None)
                if event_group:
                    store.set_json("trade_group",event_group)
                store.set_json("confirmed_setup", {})
                signal = None

            if signal:
                try:
                    signal = check_broker_compatibility(signal, conditions)
                    validate_pre_entry_checklist(signal)
                except ValueError as validation_error:
                    logging.warning("SIGNAL SKIPPED BEFORE ORDER SUBMISSION: %s", validation_error)
                    store.set_json("confirmed_setup", {})
                    signal = None
            if signal:
                signal["instrument"] = cfg.instrument
                signal_rows = [
                    ("Direction", str(signal["side"]).upper()),
                    ("Instrument", cfg.instrument),
                    ("50% midpoint LIMIT", f"{signal['entry_text']} | volume {signal['volume_text']}"),
                    ("20% retracement LIMIT", f"{signal['secondary_entry_20_text']} | volume {signal.get('secondary_volume_text')}" if signal.get("secondary_volume_text") else "Not submitted (volume split / stop-distance rule)"),
                    ("Master SL / TP", f"{signal['sl_text']} / {signal['tp_text']}"),
                    ("Total volume", signal["total_volume_text"]),
                    ("Planned risk / budget", f"${signal['risk_cash']:.2f} / ${signal['risk_budget_cash']:.2f}"),
                    ("Signal candle", signal["bar_time"]),
                ]
                log_table(f"NEW {str(signal['side']).upper()} SIGNAL | {cfg.instrument}", signal_rows)
                if cfg.trading_enabled:
                    snap2 = api.snapshot()
                    orders2, positions2 = instrument_activity(snap2, cfg.instrument)
                    current_group = store.get_json("trade_group", {}) or {}
                    current_lock = store.get_json("trade_lock", {}) or {}
                    if trade_locked or unresolved or current_group.get("active") or current_lock.get("active") or orders2 or positions2:
                        logging.warning("A signal group/order/position is already active or unresolved. This new signal is monitored but not submitted.")
                        store.set_json("confirmed_setup", {})
                    else:
                        create_group_submission_record(store, signal)
                        # The exact setup is now represented by the durable
                        # trade_group/submission_state records; recovery resumes
                        # that group and must not rediscover a replacement.
                        store.set_json("confirmed_setup", {})
                        last_secondary_full_check = time.monotonic()
                        logging.info("GROUP CREATED | Indie midpoint and 20%% retracement legs are independent pending entries; each is submitted/reconciled separately.")
                        _submit_group_leg(store, api, 0, tick_monitor)
                        advance_group_submission(store, api, tick_monitor)
                else:
                    logging.info("SIGNAL ONLY: no order was placed because automatic entries are turned OFF.")
                    store.set_json("confirmed_setup", {})

            # Return directly to the tick-woken loop; no fixed setup polling delay.
        except KeyboardInterrupt:
            logging.info("KS Trader Desk stopped safely.")
            return 0
        except RateLimitCooldownError:
            # Expected local guard: no network request was sent. Return to the
            # tick loop so quote-based safety continues during cooldown.
            continue
        except Exception as exc:
            logging.error("TEMPORARY ISSUE: The bot could not complete this market check.")
            logging.debug("Main loop error details:", exc_info=True)
            # Retry the candle boundary after a recoverable failure. last_bar
            # prevents replaying a signal that was already consumed before an
            # order submission/reconciliation error. Do not wait for next M1.
            last_market_minute = None

            # Do not rediscover the Access Point on authentication/rate-limit
            # responses: that adds more gateway traffic and can extend a lockout.
            if isinstance(exc, APIHTTPError) and exc.status_code in {401, 429}:
                if exc.status_code == 429:
                    delay = max(
                        api_retry_after_seconds(exc.payload),
                        int(math.ceil(api.rate_limit_remaining())),
                    )
                    logging.warning(
                        "Exness rate limit reached. REST requests are locally paused for up to %d second(s); "
                        "live ticks and saved pending-order safety checks continue. Automatic retry is enabled.",
                        delay,
                    )
                    # Do not sleep the trading loop. Its cooldown branch keeps
                    # processing ticks and records pending-order expiry events.
                    continue
                else:
                    delay = 60
                    logging.error("Exness still rejected the read after one Access Point refresh. Check that the API key is active and has account access. Retrying in 60 seconds.")
                time.sleep(max(cfg.poll_seconds, delay))
                continue

            # GET recovery is safe and retried inside request(); no order POST is repeated.
            try:
                api.discover_access_point()
                snap = api.snapshot()
                orders, positions = instrument_activity(snap, cfg.instrument)
                logging.info("Connection restored. Exness shows %d pending order(s) and %d open position(s).", len(orders), len(positions))
                pending_submission_blocks(store, api, snap, cfg.instrument)
            except Exception:
                logging.error("Could not reconnect to Exness yet. The bot will pause briefly and try again.")
                logging.debug("Exness reconnection details:", exc_info=True)
            # Short internal retry for transient non-rate-limit errors.
            # 401/429 above retain their required longer cooldown.
            time.sleep(1.0)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        logging.basicConfig(level=logging.ERROR)
        logging.error("The bot could not start. Please check ks_trader_bot.log for technical details.")
        logging.debug("Startup error details:", exc_info=True)
        raise SystemExit(1)