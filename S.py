#!/usr/bin/env python3
"""
Discord Username Checker V11 — Residential Proxies Edition
- Loads from proxies.txt (no scraping)
- Skips validation (residential = always alive)
- High concurrency (safe with residential)
- Bandwidth tracking (stops at limit)
- No proxy kill on 429/403 (cooldown only)
"""
import os
import sys
import time
import json
import math
import random
import string
import hashlib
import asyncio
import itertools
import ipaddress
import re
import tempfile
import threading
import signal
from collections import defaultdict, deque, OrderedDict
from dataclasses import dataclass, field
from typing import Optional, List, Tuple, Dict, Set
from urllib.parse import quote

import aiohttp

SOCKS_OK = False
try:
    from aiohttp_socks import ProxyConnector
    SOCKS_OK = True
except ImportError:
    pass

RICH = False
try:
    from rich.console import Console
    from rich.panel import Panel
    from rich.prompt import Prompt, IntPrompt
    from rich.table import Table
    RICH = True
    console = Console()
except ImportError:
    pass


# ==================== ENDPOINTS ====================
API_TOKENLESS = "https://discord.com/api/v9/unique-username/username-attempt-unauthed"
API_IPIFY     = "https://api.ipify.org?format=json"


# ==================== CONFIG ====================
USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.1 Safari/605.1.15",
    "Mozilla/5.0 (X11; Linux x86_64; rv:133.0) Gecko/20100101 Firefox/133.0",
]

VERIFY_TLS = True

# ---- Residential-optimized concurrency ----
CHECK_WORKERS       = 40        # 40 concurrent requests is safe
ACQUIRE_MAX_WAIT    = 6.0       # short wait

# HTTP pool
TCP_LIMIT           = 500
TCP_LIMIT_PER_HOST  = 50
DNS_CACHE_TTL       = 300
KEEPALIVE_TIMEOUT   = 45

# SOCKS pool
MAX_SOCKS_SESSIONS  = 300
SOCKS_PER_CONNECTOR = 20
SOCKS_PER_HOST      = 10

# Timeouts
TIMEOUT_CONNECT     = 10
TIMEOUT_TOTAL       = 18

# Rate safety (residential IPs tolerate more)
PROXY_MAX_PER_MIN   = 30        # 30 req/min per IP
PROXY_MIN_GAP       = 0.3
PROXY_COOLDOWN_S    = 20
PROXY_FAIL_LIMIT    = 8         # much higher — residential rarely dies

# Files
PROXY_FILE    = "proxies.txt"
RESULTS_FILE  = "results.jsonl"
HITS_FILE     = "available.txt"
BANDWIDTH_FILE = "bandwidth.json"
SESSION_FILE  = "session.json"

STATS_INTERVAL = 5

# Bandwidth management
BANDWIDTH_LIMIT_GB = 100.0
BANDWIDTH_WARN_GB  = 5.0        # warn when remaining < this
AVG_REQUEST_KB     = 3.5        # estimated size per request
STOP_AT_REMAINING_GB = 0.5      # stop with this much buffer left


# ==================== LOGGER ====================
_log_lk = threading.Lock()


def log(msg, style=""):
    with _log_lk:
        if RICH:
            console.print(msg, style=style, highlight=False)
        else:
            print(msg, flush=True)


def plog(tag, ident, idx, extra=""):
    colors = {"Avb": "bold green", "Usd": "bold cyan", "Err": "bold red"}
    with _log_lk:
        if RICH:
            console.print(
                f"[{colors.get(tag, 'white')}][ {tag} ][/] "
                f"[dim][ Api ][/] | [white]{ident}[/] | "
                f"[dim]#{idx:05d}[/] {extra}",
                highlight=False,
            )
        else:
            print(f"[ {tag} ] [ Api ] | {ident} | #{idx:05d} {extra}", flush=True)


# ==================== STATE ====================
class State:
    def __init__(self):
        self.reset()

    def reset(self):
        self.stop = threading.Event()
        self.counters = defaultdict(int)
        self.counters_lock = threading.Lock()
        self.hits: List[str] = []
        self.hits_lock = threading.Lock()
        self.bytes_used = 0
        self.bytes_lock = threading.Lock()

    def inc(self, key, n=1):
        with self.counters_lock:
            self.counters[key] += n

    def hit(self, username):
        with self.hits_lock:
            self.hits.append(username)

    def add_bytes(self, n):
        with self.bytes_lock:
            self.bytes_used += n

    def snapshot_counters(self):
        with self.counters_lock:
            return dict(self.counters)

    def snapshot_hits(self):
        with self.hits_lock:
            return list(self.hits)

    def snapshot_bytes(self):
        with self.bytes_lock:
            return self.bytes_used


STATE = State()


# ==================== PROXY MODEL ====================
@dataclass(frozen=True)
class ProxyKey:
    protocol: str
    host: str
    port: int
    user: Optional[str] = None
    password: Optional[str] = None


@dataclass
class Proxy:
    key: ProxyKey
    status: str = "alive"
    fails: int = 0
    ok: int = 0
    busy_until: float = 0.0
    cooldown_until: float = 0.0
    last_used: float = 0.0
    request_times: deque = field(default_factory=deque)
    bytes_used: int = 0
    requests: int = 0

    @property
    def url(self):
        if self.key.user is not None:
            u = quote(self.key.user, safe="")
            pw = quote(self.key.password or "", safe="")
            return f"{self.key.protocol}://{u}:{pw}@{self.key.host}:{self.key.port}"
        return f"{self.key.protocol}://{self.key.host}:{self.key.port}"

    @property
    def safe_url(self):
        return f"{self.key.protocol}://{self.key.host}:{self.key.port}"


# ==================== PARSER ====================
_SCHEME_RE = re.compile(r"^([a-zA-Z][a-zA-Z0-9+.\-]*)://")


def _validate_host(h: str) -> bool:
    h = h.strip()
    if not h or len(h) > 253:
        return False
    try:
        ipaddress.IPv4Address(h)
        return True
    except ValueError:
        pass
    try:
        ipaddress.IPv6Address(h)
        return True
    except ValueError:
        pass
    return bool(re.match(
        r"^[a-zA-Z0-9]([a-zA-Z0-9\-]{0,61}[a-zA-Z0-9])?"
        r"(\.[a-zA-Z0-9]([a-zA-Z0-9\-]{0,61}[a-zA-Z0-9])?)*$", h))


def _validate_port(p) -> Optional[int]:
    try:
        v = int(p)
    except (TypeError, ValueError):
        return None
    return v if 0 < v < 65536 else None


def parse_proxy_line(line: str, proto_hint: str = "http") -> Optional[ProxyKey]:
    """
    Supports residential formats:
        user:pass@host:port
        host:port:user:pass
        http://user:pass@host:port
        socks5://user:pass@host:port
    """
    line = line.strip()
    if not line or line.startswith("#"):
        return None

    proto = proto_hint
    creds = None
    hostport = ""

    m = _SCHEME_RE.match(line)
    if m:
        proto = m.group(1).lower()
        rest = line[m.end():]
        if "@" in rest:
            creds, hostport = rest.split("@", 1)
        else:
            hostport = rest
    elif "@" in line:
        creds, hostport = line.split("@", 1)
    else:
        # host:port:user:pass format
        parts = line.split(":")
        if len(parts) == 4:
            hostport = f"{parts[0]}:{parts[1]}"
            creds = f"{parts[2]}:{parts[3]}"
        else:
            hostport = line

    if hostport.startswith("["):
        end = hostport.find("]")
        if end < 0:
            return None
        host = hostport[1:end]
        rest = hostport[end + 1:]
        if not rest.startswith(":"):
            return None
        port_s = rest[1:]
    else:
        if hostport.count(":") != 1:
            return None
        host, port_s = hostport.rsplit(":", 1)

    if not _validate_host(host):
        return None
    port = _validate_port(port_s)
    if port is None:
        return None

    user = password = None
    if creds:
        if ":" in creds:
            user, password = creds.split(":", 1)
        else:
            user = creds

    if proto in ("socks5", "socks5h"):
        proto = "socks5"
    elif proto in ("socks4", "socks4a"):
        proto = "socks4"
    elif proto in ("http", "https"):
        proto = "http"
    else:
        proto = proto_hint
    if proto not in ("http", "socks4", "socks5"):
        proto = "http"
    if proto in ("socks4", "socks5") and not SOCKS_OK:
        return None

    return ProxyKey(protocol=proto, host=host, port=port,
                    user=user, password=password)


# ==================== PROXY POOL ====================
class ProxyPool:
    def __init__(self, proxies):
        self._lock = asyncio.Lock()
        # Round-robin order — shuffle once for even distribution
        self.items = list(proxies)
        random.shuffle(self.items)
        self.idx = -1

    def size(self):
        return len(self.items)

    def alive_count(self):
        return sum(1 for p in self.items if p.status == "alive")

    def _ready(self, p, now):
        if p.status != "alive":
            return False
        if p.busy_until > now or p.cooldown_until > now:
            return False
        cutoff = now - 60
        while p.request_times and p.request_times[0] < cutoff:
            p.request_times.popleft()
        if len(p.request_times) >= PROXY_MAX_PER_MIN:
            return False
        if PROXY_MIN_GAP > 0 and (now - p.last_used) < PROXY_MIN_GAP:
            return False
        return True

    async def acquire(self, max_wait: float = ACQUIRE_MAX_WAIT):
        if not self.items:
            return None

        deadline = time.time() + max_wait
        while True:
            async with self._lock:
                now = time.time()
                alive = 0
                n = len(self.items)
                for _ in range(n):
                    self.idx = (self.idx + 1) % n
                    p = self.items[self.idx]
                    if p.status == "cooldown" and p.cooldown_until <= now:
                        p.status = "alive"
                        p.fails = 0
                    if p.status == "alive":
                        alive += 1
                    if self._ready(p, now):
                        p.busy_until = now + TIMEOUT_TOTAL
                        p.last_used = now
                        p.request_times.append(now)
                        return p

                if alive == 0:
                    return None

            if time.time() >= deadline:
                return None
            await asyncio.sleep(0.15)

    async def release(self, p):
        if p is None:
            return
        async with self._lock:
            p.busy_until = 0.0

    async def report_success(self, p, bytes_used=0):
        if p is None:
            return
        async with self._lock:
            p.ok += 1
            p.fails = 0
            p.requests += 1
            p.bytes_used += bytes_used

    async def report_cooldown(self, p, seconds):
        """Residential: cooldown, NEVER kill."""
        if p is None:
            return
        async with self._lock:
            p.status = "cooldown"
            p.cooldown_until = time.time() + seconds

    async def report_fail(self, p):
        """Residential proxies should rarely be killed."""
        if p is None:
            return
        async with self._lock:
            p.fails += 1
            if p.fails >= PROXY_FAIL_LIMIT:
                p.status = "cooldown"
                p.cooldown_until = time.time() + 120
                p.fails = 0

    def stats(self):
        now = time.time()
        return {
            "total": len(self.items),
            "alive": sum(1 for p in self.items if p.status == "alive"),
            "cooldown": sum(1 for p in self.items
                            if p.status == "cooldown"
                            and p.cooldown_until > now),
            "dead": 0,
        }


# ==================== SESSION MANAGER ====================
class SessionManager:
    def __init__(self):
        self._http = None
        self._socks = OrderedDict()  # url -> [session, refcount]
        self._lock = asyncio.Lock()
        self._closed = False

    async def _http_session(self):
        if self._closed:
            raise RuntimeError("SessionManager closed")
        if self._http is None or self._http.closed:
            connector = aiohttp.TCPConnector(
                limit=TCP_LIMIT,
                limit_per_host=TCP_LIMIT_PER_HOST,
                ttl_dns_cache=DNS_CACHE_TTL,
                keepalive_timeout=KEEPALIVE_TIMEOUT,
                enable_cleanup_closed=True,
                ssl=VERIFY_TLS,
            )
            self._http = aiohttp.ClientSession(
                connector=connector,
                timeout=aiohttp.ClientTimeout(
                    total=TIMEOUT_TOTAL, connect=TIMEOUT_CONNECT),
            )
        return self._http

    async def _socks_acquire(self, url):
        if not SOCKS_OK:
            raise RuntimeError("aiohttp-socks not installed")
        if self._closed:
            raise RuntimeError("SessionManager closed")
        async with self._lock:
            if url in self._socks:
                entry = self._socks[url]
                entry[1] += 1
                self._socks.move_to_end(url)
                return entry[0]

            if len(self._socks) >= MAX_SOCKS_SESSIONS:
                idle = [k for k, e in self._socks.items() if e[1] == 0]
                if not idle:
                    raise RuntimeError("SOCKS pool full")
                _, [old, _] = self._socks.pop(idle[0])
                asyncio.create_task(self._safe_close(old))

            connector = ProxyConnector.from_url(
                url, ssl=VERIFY_TLS, rdns=True,
                limit=SOCKS_PER_CONNECTOR, limit_per_host=SOCKS_PER_HOST,
            )
            sess = aiohttp.ClientSession(
                connector=connector,
                timeout=aiohttp.ClientTimeout(
                    total=TIMEOUT_TOTAL, connect=TIMEOUT_CONNECT),
            )
            self._socks[url] = [sess, 1]
            return sess

    async def _socks_release(self, url):
        async with self._lock:
            if url in self._socks:
                entry = self._socks[url]
                if entry[1] > 0:
                    entry[1] -= 1

    @staticmethod
    async def _safe_close(sess):
        try:
            await sess.close()
        except Exception:
            pass

    def request(self, method, url, proxy=None, **kw):
        if proxy is None:
            return _DirectReq(self, method, url, **kw)
        if proxy.key.protocol in ("socks4", "socks5"):
            return _SocksReq(self, proxy.url, method, url, **kw)
        return _HttpProxyReq(self, proxy.url, method, url, **kw)

    async def close(self, timeout: float = 15.0):
        async with self._lock:
            if self._closed:
                return
            self._closed = True

        deadline = time.time() + timeout
        while time.time() < deadline:
            async with self._lock:
                total_ref = sum(e[1] for e in self._socks.values())
            if total_ref == 0:
                break
            await asyncio.sleep(0.1)

        async with self._lock:
            if self._http and not self._http.closed:
                try:
                    await self._http.close()
                except Exception:
                    pass
            self._http = None
            for _, entry in self._socks.items():
                try:
                    await entry[0].close()
                except Exception:
                    pass
            self._socks.clear()


class _DirectReq:
    __slots__ = ("_sm", "_m", "_u", "_kw", "_cm")
    def __init__(self, sm, m, u, **kw):
        self._sm, self._m, self._u, self._kw, self._cm = sm, m, u, kw, None
    async def __aenter__(self):
        s = await self._sm._http_session()
        self._cm = s.request(self._m, self._u, **self._kw)
        return await self._cm.__aenter__()
    async def __aexit__(self, *e):
        if self._cm: return await self._cm.__aexit__(*e)


class _HttpProxyReq:
    __slots__ = ("_sm", "_p", "_m", "_u", "_kw", "_cm")
    def __init__(self, sm, p, m, u, **kw):
        self._sm, self._p, self._m, self._u, self._kw, self._cm = sm, p, m, u, kw, None
    async def __aenter__(self):
        s = await self._sm._http_session()
        self._cm = s.request(self._m, self._u, proxy=self._p, **self._kw)
        return await self._cm.__aenter__()
    async def __aexit__(self, *e):
        if self._cm: return await self._cm.__aexit__(*e)


class _SocksReq:
    __slots__ = ("_sm", "_p", "_m", "_u", "_kw", "_cm", "_acq")
    def __init__(self, sm, p, m, u, **kw):
        self._sm, self._p, self._m, self._u, self._kw = sm, p, m, u, kw
        self._cm = None
        self._acq = False
    async def __aenter__(self):
        s = await self._sm._socks_acquire(self._p)
        self._acq = True
        self._cm = s.request(self._m, self._u, **self._kw)
        return await self._cm.__aenter__()
    async def __aexit__(self, *e):
        try:
            if self._cm:
                return await self._cm.__aexit__(*e)
        finally:
            if self._acq:
                self._acq = False
                await self._sm._socks_release(self._p)


# ==================== HEADERS ====================
def rheaders(extra=None):
    h = {
        "User-Agent": random.choice(USER_AGENTS),
        "Accept": "*/*",
        "Accept-Language": "en-US,en;q=0.9",
        "Origin": "https://discord.com",
        "Referer": "https://discord.com/register",
        "Sec-Fetch-Dest": "empty",
        "Sec-Fetch-Mode": "cors",
        "Sec-Fetch-Site": "same-origin",
        "X-Discord-Locale": "en-US",
        "X-Discord-Timezone": "UTC",
    }
    if extra:
        h.update(extra)
    return h


# ==================== LOAD PROXIES ====================
def load_proxies_from_file(path: str) -> List[Proxy]:
    if not os.path.exists(path):
        log(f"[red]Missing file: {path}[/]")
        return []

    proxies = []
    seen = set()
    rejected = 0
    with open(path, "r", encoding="utf-8-sig", errors="ignore") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            key = parse_proxy_line(line)
            if key is None:
                rejected += 1
                continue
            if key in seen:
                continue
            seen.add(key)
            proxies.append(Proxy(key=key))

    log(f"[green]✓[/] Loaded {len(proxies)} proxies from {path} "
        f"(rejected: {rejected})")
    return proxies


# ==================== USERNAME ====================
_ALLOWED = set(string.ascii_lowercase + string.digits + "._")


def valid_username(u):
    if not isinstance(u, str):
        return False
    if not (2 <= len(u) <= 32):
        return False
    if u in ("everyone", "here"):
        return False
    if u[0] in "._" or u[-1] in "._":
        return False
    if ".." in u:
        return False
    return all(c in _ALLOWED for c in u)


def generate_usernames(mode, limit):
    modes = {
        "4l": (string.ascii_lowercase, 4),
        "4c": (string.ascii_lowercase + string.digits, 4),
        "4n": (string.digits, 4),
        "3l": (string.ascii_lowercase, 3),
        "3c": (string.ascii_lowercase + string.digits, 3),
        "3n": (string.digits, 3),
        "2l": (string.ascii_lowercase, 2),
        "2c": (string.ascii_lowercase + string.digits, 2),
        "2n": (string.digits, 2),
    }
    if mode not in modes:
        raise ValueError(f"Unknown mode: {mode}")
    if limit <= 0:
        raise ValueError("limit must be > 0")

    chars, length = modes[mode]
    space = len(chars) ** length
    limit = min(limit, space)

    if space <= 100_000:
        all_items = ["".join(p)
                     for p in itertools.product(chars, repeat=length)]
        valid = [s for s in all_items if valid_username(s)]
        random.shuffle(valid)
        return valid[:limit]

    seen, out = set(), []
    max_attempts = limit * 30
    attempts = 0
    while len(out) < limit and attempts < max_attempts:
        attempts += 1
        s = "".join(random.choices(chars, k=length))
        if s in seen or not valid_username(s):
            continue
        seen.add(s)
        out.append(s)
    return out


# ==================== CLASSIFY ====================
def classify_response(code, body_text):
    body = {}
    if body_text:
        try:
            parsed = json.loads(body_text)
            if isinstance(parsed, dict):
                body = parsed
        except Exception:
            pass

    if code == 200:
        taken = body.get("taken")
        if taken is True:
            return "confirmed_taken", "", "ok", 0.0
        if taken is False:
            return "confirmed_available", " "", "ok", 0.0
        return "unknown", "200_unknown_shape", "ok", 0.0

    if code == 429:
        ra = 5.0
        try:
            ra = float(body.get("retry_after", 5.0))
        except Exception:
            pass
        ra = max(1.0, min(ra, 30.0))  # residential recovers faster
        return "rate_limited", f"ra={ra:.1f}", "cooldown", ra

    if code in (400, 422):
        cv = body.get("code")
        if cv == 50035:
            return "confirmed_invalid", "code_50035", "ok", 0.0
        msg = str(body.get("message", "")).lower()
        if "username" in msg and "invalid" in msg:
            returnconfirmed_invalid", "username_invalid", "ok", 0.0
        return "client_error", f"http_{code}", "none", 0.0

    if code == 401:
        return "client_error", "unauthorized", "ok", 0.0
    if code == 403:
        # Residential rarely gets 403. Cooldown briefly, don't kill.
        return "forbidden", "forbidden", "cooldown", 15.0
    if code in (407, 502, 503, 504):
        return "server_error", f"gateway_{code}", "cooldown", 10.0
    if code >= 500:
        return "server_error", f"http_{code}", "cooldown", 8.0
    return "unknown", f"http_{code}", "none", 0.0


# ==================== CHECKER ====================
class Checker:
    def __init__(self, pp, sm, session_id):
        self.pp = pp
        self.sm = sm
        self.session_id = session_id
        self.fp = open(RESULTS_FILE, "a", encoding="utf-8")
        self.fp_lock = asyncio.Lock()
        self.counters = defaultdict(int)
        self._recorded: Set[int] = set()
        self._recorded_lock = asyncio.Lock()
        self.completed = 0
        self._hit_lock = threading.Lock()

    def _write_hit(self, username):
        with self._hit_lock:
            try:
                with open(HITS_FILE, "a", encoding="utf-8") as f:
                    f.write(username + "\n")
                    f.flush()
            except Exception:
                pass

    async def _record(self, idx, username, status, http, reason, lat_ms=0.0):
        async with self._recorded_lock:
            if idx in self._recorded:
                return
            self._recorded.add(idx)
            self.completed += 1

        self.counters[status] += 1
        STATE.inc(f"check_{status}")
        rec = {
            "session": self.session_id,
            "ts": round(time.time(), 3),
            "idx": idx,
            "username": username,
            "status": status,
            "http": http,
            "reason": reason,
            "latency_ms": round(lat_ms, 1),
            "terminal": status in ("available", "taken", "invalid_format"),
        }
        async with self.fp_lock:
            self.fp.write(json.dumps(rec, ensure_ascii=False) + "\n")
            self.fp.flush()

    async def check_one(self, username, idx):
        if not valid_username(username):
            await self._record(idx, username, "invalid_format", 0, "precheck")
            plog("Err", f"@{username}", idx, "[dim]invalid[/]")
            return "invalid_format"

        proxy = await self.pp.acquire()
        if proxy is None:
            await self._record(idx, username, "no_proxy", 0, "no_alive_proxy")
            plog("Err", f"@{username}", idx, "[yellow]no_proxy[/]")
            return "no_proxy"

        bytes_used = 0
        try:
            headers = rheaders({
                "Content-Type": "application/json",
                "X-Fingerprint": hashlib.md5(
                    f"{random.random()}".encode()).hexdigest(),
            })
            payload = {"username": username}

            t0 = time.perf_counter()
            status_code = 0
            body_text = ""

            try:
                async with self.sm.request(
                    "POST", API_TOKENLESS, proxy=proxy,
                    headers=headers, json=payload,
                ) as r:
                    status_code = r.status
                    body_text = await r.text()
                    # Estimate bytes: request + response
                    bytes_used = len(body_text) + len(json.dumps(payload)) + 500
            except asyncio.TimeoutError:
                await self.pp.report_fail(proxy)
                await self._record(idx, username, "error", 0, "timeout")
                plog("Err", f"@{username}", idx, "[dim]timeout[/]")
                return "error"
            except asyncio.CancelledError:
                raise
            except Exception as e:
                await self.pp.report_fail(proxy)
                reason = f"exc:{type(e).__name__}"
                await self._record(idx, username, "error", 0, reason)
                plog("Err", f"@{username}", idx, f"[red]{reason}[/]")
                return "error"

            lat_ms = (time.perf_counter() - t0) * 1000
            STATE.add_bytes(bytes_used)

            kind, reason, action, cd = classify_response(status_code, body_text)

            if action == "ok":
                await self.pp.report_success(proxy, bytes_used)
            elif action == "cooldown":
                await self.pp.report_cooldown(proxy, cd)
            elif action == "transient":
                await self.pp.report_fail(proxy)

            if kind == "confirmed_available":
                status = "available"
                plog("Avb", f"@{username}", idx)
                STATE.hit(username)
                self._write_hit(username)
            elif kind == "confirmed_taken":
                status = "taken"
                plog("Usd", f"@{username}", idx)
            elif kind == "confirmed_invalid":
                status = "invalid_format"
                plog("Err", f"@{username}", idx, "[dim]invalid[/]")
            elif kind == "rate_limited":
                status = "rate_limited"
                plog("Err", f"@{username}", idx, "[yellow]rate_limited[/]")
            elif kind == "forbidden":
                status = "forbidden"
                plog("Err", f"@{username}", idx, "[yellow]forbidden[/]")
            elif kind == "server_error":
                status = "server_error"
                plog("Err", f"@{username}", idx, f"[yellow]{reason}[/]")
            elif kind == "client_error":
                status = "client_error"
                plog("Err", f"@{username}", idx, f"[red]{reason}[/]")
            else:
                status = "error"
                plog("Err", f"@{username}", idx, f"[red]{reason}[/]")

            await self._record(idx, username, status, status_code, reason, lat_ms)
            return status
        finally:
            await self.pp.release(proxy)

    async def run_batch(self, usernames, concurrency):
        queue = asyncio.Queue(maxsize=concurrency * 4)

        async def worker():
            while True:
                item = await queue.get()
                if item is None:
                    queue.task_done()
                    return
                idx, u = item
                try:
                    if STATE.stop.is_set():
                        await self._record(idx, u, "skipped", 0, "stop")
                    else:
                        await self.check_one(u, idx)
                except asyncio.CancelledError:
                    try:
                        await self._record(idx, u, "skipped", 0, "cancelled")
                    except Exception:
                        pass
                    queue.task_done()
                    raise
                except Exception as e:
                    await self._record(idx, u, "error", 0,
                                       f"unhandled:{type(e).__name__}")
                finally:
                    queue.task_done()

        workers = [asyncio.create_task(worker()) for _ in range(concurrency)]
        try:
            for i, u in enumerate(usernames, 1):
                await queue.put((i, u))
            for _ in workers:
                await queue.put(None)
            await queue.join()
        finally:
            for w in workers:
                if not w.done():
                    w.cancel()
            await asyncio.gather(*workers, return_exceptions=True)

    def close(self):
        try:
            self.fp.close()
        except Exception:
            pass


# ==================== BANDWIDTH ====================
def load_bandwidth_used() -> float:
    """Returns cumulative GB used across sessions."""
    if not os.path.exists(BANDWIDTH_FILE):
        return 0.0
    try:
        with open(BANDWIDTH_FILE, "r") as f:
            return float(json.load(f).get("gb_used", 0.0))
    except Exception:
        return 0.0


def save_bandwidth_used(gb: float):
    try:
        with open(BANDWIDTH_FILE, "w") as f:
            json.dump({"gb_used": round(gb, 4),
                       "updated": time.time()}, f)
    except Exception:
        pass


# ==================== SUITE ====================
class Suite:
    def __init__(self):
        STATE.reset()
        self.sm = SessionManager()
        self.pp = None
        self.checker = None
        self.session_id = time.strftime("%Y%m%d_%H%M%S")
        self.start = time.time()
        self.stats_task = None
        self.starting_gb = load_bandwidth_used()

    async def _stats_loop(self):
        try:
            while not STATE.stop.is_set():
                await asyncio.sleep(STATS_INTERVAL)
                if not self.pp:
                    continue
                ps = self.pp.stats()
                done = self.checker.completed if self.checker else 0
                rps = done / max(0.1, time.time() - self.start)
                hits = len(STATE.snapshot_hits())

                bytes_used = STATE.snapshot_bytes()
                gb_session = bytes_used / (1024 ** 3)
                gb_total = self.starting_gb + gb_session
                gb_remaining = BANDWIDTH_LIMIT_GB - gb_total

                log(f"[dim cyan]prx[a={ps['alive']} c={ps['cooldown']}] "
                    f"hits={hits} completed={done} rps={rps:.1f} | "
                    f"GB[session={gb_session:.3f} total={gb_total:.2f} "
                    f"left={gb_remaining:.1f}][/]")

                # Bandwidth safety
                if gb_remaining < STOP_AT_REMAINING_GB:
                    log(f"[red]⚠ Bandwidth limit reached "
                        f"({gb_total:.2f}/{BANDWIDTH_LIMIT_GB} GB). "
                        f"Stopping.[/]")
                    STATE.stop.set()
                elif gb_remaining < BANDWIDTH_WARN_GB:
                    log(f"[yellow]⚠ Low bandwidth: "
                        f"{gb_remaining:.1f} GB remaining[/]")
        except asyncio.CancelledError:
            return

    async def run(self, usernames):
        # Truncate hits file
        try:
            open(HITS_FILE, "w").close()
        except Exception:
            pass

        # Load proxies
        proxies = load_proxies_from_file(PROXY_FILE)
        if not proxies:
            log("[red]No proxies loaded. Create proxies.txt first.[/]")
            return

        self.pp = ProxyPool(proxies)

        if RICH:
            tbl = Table(title="Proxy Pool")
            tbl.add_column("Metric")
            tbl.add_column("Value", justify="right")
            tbl.add_row("Total", str(self.pp.size()))
            tbl.add_row("Workers", str(CHECK_WORKERS))
            tbl.add_row("Rate limit per IP",
                        f"{PROXY_MAX_PER_MIN}/min")
            tbl.add_row("Bandwidth used (before)",
                        f"{self.starting_gb:.2f} GB")
            tbl.add_row("Bandwidth remaining",
                        f"{BANDWIDTH_LIMIT_GB - self.starting_gb:.1f} GB")
            console.print(tbl)

        self.checker = Checker(self.pp, self.sm, self.session_id)
        self.stats_task = asyncio.create_task(self._stats_loop())

        log(f"[bold]Checking {len(usernames)} usernames, "
            f"concurrency={CHECK_WORKERS}[/]\n")

        try:
            await self.checker.run_batch(usernames, CHECK_WORKERS)
        finally:
            STATE.stop.set()
            if self.stats_task:
                self.stats_task.cancel()
                await asyncio.gather(self.stats_task, return_exceptions=True)
            await self._finalize()

    async def _finalize(self):
        elapsed = time.time() - self.start
        c = self.checker.counters if self.checker else {}
        hits = STATE.snapshot_hits()
        ps = self.pp.stats() if self.pp else {}

        bytes_session = STATE.snapshot_bytes()
        gb_session = bytes_session / (1024 ** 3)
        gb_total = self.starting_gb + gb_session
        save_bandwidth_used(gb_total)

        log(f"\n[bold green]═══ FINAL (session {self.session_id}) ═══[/]")
        log(f"  Elapsed:        {elapsed:.1f}s")
        log(f"  Available:      [green]{len(hits)}[/]")
        log(f"  Taken:          {c.get('taken', 0)}")
        log(f"  Invalid format: {c.get('invalid_format', 0)}")
        log(f"  Rate limited:   {c.get('rate_limited', 0)}")
        log(f"  Forbidden:      {c.get('forbidden', 0)}")
        log(f"  Server errors:  {c.get('server_error', 0)}")
        log(f"  Client errors:  {c.get('client_error', 0)}")
        log(f"  Other errors:   {c.get('error', 0)}")
        log(f"  No proxy:       {c.get('no_proxy', 0)}")
        log(f"  Skipped:        {c.get('skipped', 0)}")
        log(f"  ---------------")
        log(f"  GB this run:    {gb_session:.4f} GB")
        log(f"  GB total:       {gb_total:.3f} / {BANDWIDTH_LIMIT_GB:.1f} GB")
        log(f"  GB remaining:   {BANDWIDTH_LIMIT_GB - gb_total:.2f} GB")
        log(f"  Hits file:      {HITS_FILE} ({len(hits)} lines)")

        try:
            with open(SESSION_FILE, "w", encoding="utf-8") as f:
                json.dump({
                    "session_id": self.session_id,
                    "elapsed_s": round(elapsed, 1),
                    "counters": dict(c),
                    "proxies": ps,
                    "gb_session": round(gb_session, 4),
                    "gb_total": round(gb_total, 4),
                }, f, indent=2)
        except Exception:
            pass

        if self.checker:
            self.checker.close()
        await self.sm.close()


# ==================== MAIN ====================
_SIGINT_COUNT = [0]


def _install_sigint(loop):
    def on_sigint():
        _SIGINT_COUNT[0] += 1
        if _SIGINT_COUNT[0] >= 2:
            log("\n[red]Force exit[/]")
            os._exit(130)
        log("\n[yellow]Ctrl+C — stopping gracefully "
            "(press again to force)[/]")
        STATE.stop.set()

    try:
        loop.add_signal_handler(signal.SIGINT, on_sigint)
        return True
    except (NotImplementedError, RuntimeError):
        return False


def _prompt_mode():
    if RICH:
        console.print(Panel.fit(
            "[bold cyan]Discord Username Checker V11[/]\n"
            "[dim]Residential Proxies · 100GB · Tokenless[/]",
            border_style="cyan"))
        console.print("\n[bold]Mode:[/] "
                      "[yellow]4l[/] [yellow]4c[/] [yellow]4n[/]  "
                      "[yellow]3l[/] [yellow]3c[/] [yellow]3n[/]  "
                      "[yellow]2l[/] [yellow]2c[/] [yellow]2n[/]")
        return Prompt.ask("Mode", default="4c").strip().lower()
    return (input("Mode [4c]: ").strip() or "4c").lower()


def _prompt_int(p, default):
    if RICH:
        return IntPrompt.ask(p, default=default)
    v = input(f"{p} [{default}]: ").strip()
    try:
        return int(v) if v else default
    except ValueError:
        return default


async def amain():
    loop = asyncio.get_running_loop()
    _install_sigint(loop)

    try:
        mode = _prompt_mode()
    except (KeyboardInterrupt, EOFError):
        return

    limit = _prompt_int("How many usernames", 5000)
    if limit <= 0:
        log("[red]limit must be > 0[/]")
        return

    log(f"[bold]Generating {limit} usernames ({mode})...[/]")
    try:
        usernames = generate_usernames(mode, limit)
    except ValueError as e:
        log(f"[red]{e}[/]")
        return
    log(f"[green]✓[/] {len(usernames)} usernames\n")

    suite = Suite()
    try:
        await suite.run(usernames)
    except KeyboardInterrupt:
        STATE.stop.set()
        log("\n[yellow]Interrupted[/]")
        if suite.checker:
            suite.checker.close()
        try:
            await suite.sm.close()
        except Exception:
            pass


def main():
    try:
        asyncio.run(amain())
    except KeyboardInterrupt:
        print("\nForced exit")
    except Exception as e:
        print(f"Fatal: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()
