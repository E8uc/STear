#!/usr/bin/env python3
"""
Discord Username Checker V11 - Residential Proxies Edition
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


API_TOKENLESS = "https://discord.com/api/v9/unique-username/username-attempt-unauthed"

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.1 Safari/605.1.15",
    "Mozilla/5.0 (X11; Linux x86_64; rv:133.0) Gecko/20100101 Firefox/133.0",
]

VERIFY_TLS = True

CHECK_WORKERS       = 40
ACQUIRE_MAX_WAIT    = 6.0

TCP_LIMIT           = 500
TCP_LIMIT_PER_HOST  = 50
DNS_CACHE_TTL       = 300
KEEPALIVE_TIMEOUT   = 45

MAX_SOCKS_SESSIONS  = 300
SOCKS_PER_CONNECTOR = 20
SOCKS_PER_HOST      = 10

TIMEOUT_CONNECT     = 10
TIMEOUT_TOTAL       = 18

PROXY_MAX_PER_MIN   = 30
PROXY_MIN_GAP       = 0.3
PROXY_COOLDOWN_S    = 20
PROXY_FAIL_LIMIT    = 8

PROXY_FILE     = "proxies.txt"
RESULTS_FILE   = "results.jsonl"
HITS_FILE      = "available.txt"
BANDWIDTH_FILE = "bandwidth.json"
SESSION_FILE   = "session.json"

STATS_INTERVAL = 5

BANDWIDTH_LIMIT_GB   = 100.0
BANDWIDTH_WARN_GB    = 5.0
STOP_AT_REMAINING_GB = 0.5


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
                "[" + colors.get(tag, "white") + "][ " + tag + " ][/] "
                "[dim][ Api ][/] | [white]" + ident + "[/] | "
                "[dim]#" + ("%05d" % idx) + "[/] " + extra,
                highlight=False,
            )
        else:
            print("[ " + tag + " ] [ Api ] | " + ident + " | #" + ("%05d" % idx) + " " + extra, flush=True)


class State:
    def __init__(self):
        self.reset()

    def reset(self):
        self.stop = threading.Event()
        self.counters = defaultdict(int)
        self.counters_lock = threading.Lock()
        self.hits = []
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
            return self.key.protocol + "://" + u + ":" + pw + "@" + self.key.host + ":" + str(self.key.port)
        return self.key.protocol + "://" + self.key.host + ":" + str(self.key.port)

    @property
    def safe_url(self):
        return self.key.protocol + "://" + self.key.host + ":" + str(self.key.port)


_SCHEME_RE = re.compile(r"^([a-zA-Z][a-zA-Z0-9+.\-]*)://")


def _validate_host(h):
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


def _validate_port(p):
    try:
        v = int(p)
    except (TypeError, ValueError):
        return None
    return v if 0 < v < 65536 else None


def parse_proxy_line(line, proto_hint="http"):
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
        parts = line.split(":")
        if len(parts) == 4:
            hostport = parts[0] + ":" + parts[1]
            creds = parts[2] + ":" + parts[3]
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

    user = None
    password = None
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

    return ProxyKey(protocol=proto, host=host, port=port, user=user, password=password)


class ProxyPool:
    def __init__(self, proxies):
        self._lock = asyncio.Lock()
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

    async def acquire(self, max_wait=ACQUIRE_MAX_WAIT):
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
        if p is None:
            return
        async with self._lock:
            p.status = "cooldown"
            p.cooldown_until = time.time() + seconds

    async def report_fail(self, p):
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
            "cooldown": sum(1 for p in self.items if p.status == "cooldown" and p.cooldown_until > now),
            "dead": 0,
        }


class SessionManager:
    def __init__(self):
        self._http = None
        self._socks = OrderedDict()
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
                timeout=aiohttp.ClientTimeout(total=TIMEOUT_TOTAL, connect=TIMEOUT_CONNECT),
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
                _, entry = self._socks.pop(idle[0])
                asyncio.create_task(self._safe_close(entry[0]))

            connector = ProxyConnector.from_url(
                url, ssl=VERIFY_TLS, rdns=True,
                limit=SOCKS_PER_CONNECTOR, limit_per_host=SOCKS_PER_HOST,
            )
            sess = aiohttp.ClientSession(
                connector=connector,
                timeout=aiohttp.ClientTimeout(total=TIMEOUT_TOTAL, connect=TIMEOUT_CONNECT),
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

    async def close(self, timeout=15.0):
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
        self._sm = sm
        self._m = m
        self._u = u
        self._kw = kw
        self._cm = None

    async def __aenter__(self):
        s = await self._sm._http_session()
        self._cm = s.request(self._m, self._u, **self._kw)
        return await self._cm.__aenter__()

    async def __aexit__(self, *e):
        if self._cm:
            return await self._cm.__aexit__(*e)


class _HttpProxyReq:
    __slots__ = ("_sm", "_p", "_m", "_u", "_kw", "_cm")

    def __init__(self, sm, p, m, u, **kw):
        self._sm = sm
        self._p = p
        self._m = m
        self._u = u
        self._kw = kw
        self._cm = None

    async def __aenter__(self):
        s = await self._sm._http_session()
        self._cm = s.request(self._m, self._u, proxy=self._p, **self._kw)
        return await self._cm.__aenter__()

    async def __aexit__(self, *e):
        if self._cm:
            return await self._cm.__aexit__(*e)


class _SocksReq:
    __slots__ = ("_sm", "_p", "_m", "_u", "_kw", "_cm", "_acq")

    def __init__(self, sm, p, m, u, **kw):
        self._sm = sm
        self._p = p
        self._m = m
        self._u = u
        self._kw = kw
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


def load_proxies_from_file(path):
    if not os.path.exists(path):
        log("[red]Missing file: " + path + "[/]")
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

    log("[green]OK[/] Loaded " + str(len(proxies)) + " proxies from " + path + " (rejected: " + str(rejected) + ")")
    return proxies


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
        raise ValueError("Unknown mode: " + mode)
    if limit <= 0:
        raise ValueError("limit must be > 0")

    chars, length = modes[mode]
    space = len(chars) ** length
    limit = min(limit, space)

    if space <= 100000:
        all_items = ["".join(p) for p in itertools.product(chars, repeat=length)]
        valid = [s for s in all_items if valid_username(s)]
        random.shuffle(valid)
        return valid[:limit]

    seen = set()
    out = []
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
            return "confirmed_available", "", "ok", 0.0
        return "unknown", "200_unknown_shape", "ok", 0.0

    if code == 429:
        ra = 5.0
        try:
            ra = float(body.get("retry_after", 5.0))
        except Exception:
            pass
        ra = max(1.0, min(ra, 30.0))
        return "rate_limited", "ra=" + ("%.1f" % ra), "cooldown", ra

    if code in (400, 422):
        cv = body.get("code")
        if cv == 50035:
            return "confirmed_invalid", "code_50035", "ok", 0.0
        msg = str(body.get("message", "")).lower()
        if "username" in msg and "invalid" in msg:
            return "confirmed_invalid", "username_invalid", "ok", 0.0
        return "client_error", "http_" + str(code), "none", 0.0

    if code == 401:
        return "client_error", "unauthorized", "ok", 0.0
    if code == 403:
        return "forbidden", "forbidden", "cooldown", 15.0
    if code in (407, 502, 503, 504):
        return "server_error", "gateway_" + str(code), "cooldown", 10.0
    if code >= 500:
        return "server_error", "http_" + str(code), "cooldown", 8.0
    return "unknown", "http_" + str(code), "none", 0.0


class Checker:
    def __init__(self, pp, sm, session_id):
        self.pp = pp
        self.sm = sm
        self.session_id = session_id
        self.fp = open(RESULTS_FILE, "a", encoding="utf-8")
        self.fp_lock = asyncio.Lock()
        self.counters = defaultdict(int)
        self._recorded = set()
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
        STATE.inc("check_" + status)
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
            plog("Err", "@" + username, idx, "[dim]invalid[/]")
            return "invalid_format"

        proxy = await self.pp.acquire()
        if proxy is None:
            await self._record(idx, username, "no_proxy", 0, "no_alive_proxy")
            plog("Err", "@" + username, idx, "[yellow]no_proxy[/]")
            return "no_proxy"

        bytes_used = 0
        try:
            headers = rheaders({
                "Content-Type": "application/json",
                "X-Fingerprint": hashlib.md5(str(random.random()).encode()).hexdigest(),
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
                    bytes_used = len(body_text) + len(json.dumps(payload)) + 500
            except asyncio.TimeoutError:
                await self.pp.report_fail(proxy)
                await self._record(idx, username, "error", 0, "timeout")
                plog("Err", "@" + username, idx, "[dim]timeout[/]")
                return "error"
            except asyncio.CancelledError:
                raise
            except Exception as e:
                await self.pp.report_fail(proxy)
                reason = "exc:" + type(e).__name__
                await self._record(idx, username, "error", 0, reason)
                plog("Err", "@" + username, idx, "[red]" + reason + "[/]")
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
                plog("Avb", "@" + username, idx)
                STATE.hit(username)
                self._write_hit(username)
            elif kind == "confirmed_taken":
                status = "taken"
                plog("Usd", "@" + username, idx)
            elif kind == "confirmed_invalid":
                status = "invalid_format"
                plog("Err", "@" + username, idx, "[dim]invalid[/]")
            elif kind == "rate_limited":
                status = "rate_limited"
                plog("Err", "@" + username, idx, "[yellow]rate_limited[/]")
            elif kind == "forbidden":
                status = "forbidden"
                plog("Err", "@" + username, idx, "[yellow]forbidden[/]")
            elif kind == "server_error":
                status = "server_error"
                plog("Err", "@" + username, idx, "[yellow]" + reason + "[/]")
            elif kind == "client_error":
                status = "client_error"
                plog("Err", "@" + username, idx, "[red]" + reason + "[/]")
            else:
                status = "error"
                plog("Err", "@" + username, idx, "[red]" + reason + "[/]")

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
                    await self._record(idx, u, "error", 0, "unhandled:" + type(e).__name__)
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


def load_bandwidth_used():
    if not os.path.exists(BANDWIDTH_FILE):
        return 0.0
    try:
        with open(BANDWIDTH_FILE, "r") as f:
            return float(json.load(f).get("gb_used", 0.0))
    except Exception:
        return 0.0


def save_bandwidth_used(gb):
    try:
        with open(BANDWIDTH_FILE, "w") as f:
            json.dump({"gb_used": round(gb, 4), "updated": time.time()}, f)
    except Exception:
        pass


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

                log("[dim cyan]prx[a=" + str(ps["alive"]) + " c=" + str(ps["cooldown"]) + "] "
                    "hits=" + str(hits) + " completed=" + str(done) + " rps=" + ("%.1f" % rps) + " | "
                    "GB[session=" + ("%.3f" % gb_session) + " total=" + ("%.2f" % gb_total) + " "
                    "left=" + ("%.1f" % gb_remaining) + "][/]")

                if gb_remaining < STOP_AT_REMAINING_GB:
                    log("[red]WARN Bandwidth limit reached (" + ("%.2f" % gb_total) + "/" + str(BANDWIDTH_LIMIT_GB) + " GB). Stopping.[/]")
                    STATE.stop.set()
                elif gb_remaining < BANDWIDTH_WARN_GB:
                    log("[yellow]WARN Low bandwidth: " + ("%.1f" % gb_remaining) + " GB remaining[/]")
        except asyncio.CancelledError:
            return

    async def run(self, usernames):
        try:
            open(HITS_FILE, "w").close()
        except Exception:
            pass

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
            tbl.add_row("Rate limit per IP", str(PROXY_MAX_PER_MIN) + "/min")
            tbl.add_row("Bandwidth used (before)", "%.2f GB" % self.starting_gb)
            tbl.add_row("Bandwidth remaining", "%.1f GB" % (BANDWIDTH_LIMIT_GB - self.starting_gb))
            console.print(tbl)

        self.checker = Checker(self.pp, self.sm, self.session_id)
        self.stats_task = asyncio.create_task(self._stats_loop())

        log("[bold]Checking " + str(len(usernames)) + " usernames, concurrency=" + str(CHECK_WORKERS) + "[/]")
        log("")

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

        log("")
        log("[bold green]FINAL (session " + self.session_id + ")[/]")
        log("  Elapsed:        " + ("%.1f" % elapsed) + "s")
        log("  Available:      " + str(len(hits)))
        log("  Taken:          " + str(c.get("taken", 0)))
        log("  Invalid format: " + str(c.get("invalid_format", 0)))
        log("  Rate limited:   " + str(c.get("rate_limited", 0)))
        log("  Forbidden:      " + str(c.get("forbidden", 0)))
        log("  Server errors:  " + str(c.get("server_error", 0)))
        log("  Client errors:  " + str(c.get("client_error", 0)))
        log("  Other errors:   " + str(c.get("error", 0)))
        log("  No proxy:       " + str(c.get("no_proxy", 0)))
        log("  Skipped:        " + str(c.get("skipped", 0)))
        log("  ---------------")
        log("  GB this run:    " + ("%.4f" % gb_session) + " GB")
        log("  GB total:       " + ("%.3f" % gb_total) + " / " + ("%.1f" % BANDWIDTH_LIMIT_GB) + " GB")
        log("  GB remaining:   " + ("%.2f" % (BANDWIDTH_LIMIT_GB - gb_total)) + " GB")
        log("  Hits file:      " + HITS_FILE + " (" + str(len(hits)) + " lines)")

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


_SIGINT_COUNT = [0]


def _install_sigint(loop):
    def on_sigint():
        _SIGINT_COUNT[0] += 1
        if _SIGINT_COUNT[0] >= 2:
            log("")
            log("[red]Force exit[/]")
            os._exit(130)
        log("")
        log("[yellow]Ctrl+C - stopping gracefully (press again to force)[/]")
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
            "[dim]Residential Proxies . Tokenless[/]",
            border_style="cyan"))
        console.print("")
        console.print("[bold]Mode:[/] 4l 4c 4n  3l 3c 3n  2l 2c 2n")
        return Prompt.ask("Mode", default="4c").strip().lower()
    return (input("Mode [4c]: ").strip() or "4c").lower()


def _prompt_int(p, default):
    if RICH:
        return IntPrompt.ask(p, default=default)
    v = input(p + " [" + str(default) + "]: ").strip()
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

    log("[bold]Generating " + str(limit) + " usernames (" + mode + ")...[/]")
    try:
        usernames = generate_usernames(mode, limit)
    except ValueError as e:
        log("[red]" + str(e) + "[/]")
        return
    log("[green]OK[/] " + str(len(usernames)) + " usernames")
    log("")

    suite = Suite()
    try:
        await suite.run(usernames)
    except KeyboardInterrupt:
        STATE.stop.set()
        log("")
        log("[yellow]Interrupted[/]")
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
        print("")
        print("Forced exit")
    except Exception as e:
        print("Fatal: " + str(e))
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()
PYEOF
