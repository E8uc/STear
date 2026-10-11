#!/usr/bin/env python3
"""
Discord Username Checker V10.2 — iSH optimized
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
    from rich.prompt import Prompt, IntPrompt, Confirm
    from rich.table import Table
    RICH = True
    console = Console()
except ImportError:
    pass


# ==================== ENDPOINTS ====================
API_TOKENLESS = "https://discord.com/api/v9/unique-username/username-attempt-unauthed"
API_IPIFY     = "https://api.ipify.org?format=json"
API_GATEWAY   = "https://discord.com/api/v10/gateway"


# ==================== SOURCES ====================
SOURCES = [
    ("clearproxy_s5", "https://raw.githubusercontent.com/ClearProxy/checked-proxy-list/main/custom/discord/socks5.txt", "socks5"),
    ("clearproxy_h",  "https://raw.githubusercontent.com/ClearProxy/checked-proxy-list/main/custom/discord/http.txt",   "http"),
    ("proxifly_s5",   "https://cdn.jsdelivr.net/gh/proxifly/free-proxy-list@main/proxies/protocols/socks5/data.txt",   "socks5"),
    ("proxifly_h",    "https://cdn.jsdelivr.net/gh/proxifly/free-proxy-list@main/proxies/protocols/http/data.txt",     "http"),
    ("pxs_s5",        "https://cdn.jsdelivr.net/gh/ProxyScrape/free-proxy-list@main/proxies/protocols/socks5/data.txt", "socks5"),
    ("pxs_h",         "https://cdn.jsdelivr.net/gh/ProxyScrape/free-proxy-list@main/proxies/protocols/http/data.txt",   "http"),
    ("proxmint",      "https://raw.githubusercontent.com/proxmint/free-proxy-list/main/proxies/all.txt", "http"),
    ("monosans",      "https://raw.githubusercontent.com/monosans/proxy-list/main/proxies/all.txt",      "http"),
    ("6yyn",          "https://raw.githubusercontent.com/6yyn/free-proxy-list/main/checked_proxies.txt", "http"),
    ("xyzs996_s5",    "https://raw.githubusercontent.com/xyzs996/free-proxy-health-list/main/proxies/protocols/socks5/data.txt", "socks5"),
    ("xyzs996_h",     "https://raw.githubusercontent.com/xyzs996/free-proxy-health-list/main/proxies/protocols/http/data.txt",   "http"),
]


# ==================== CONFIG ====================
USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.1 Safari/605.1.15",
    "Mozilla/5.0 (X11; Linux x86_64; rv:133.0) Gecko/20100101 Firefox/133.0",
]

VERIFY_TLS = True

# iSH-friendly caps
CHECK_WORKERS     = 20
VALIDATE_WORKERS  = 200
SCRAPE_WORKERS    = 10
MAX_PROXIES_TO_VALIDATE = 8000

# HTTP pool
TCP_LIMIT          = 300
TCP_LIMIT_PER_HOST = 25
DNS_CACHE_TTL      = 300
KEEPALIVE_TIMEOUT  = 30

# SOCKS pool
MAX_SOCKS_SESSIONS  = 100
SOCKS_PER_CONNECTOR = 10
SOCKS_PER_HOST      = 3

# Timeouts
TIMEOUT_CONNECT    = 8
TIMEOUT_TOTAL      = 20
TCP_STAGE_TIMEOUT  = 1.5
HTTPS_STAGE_TMO    = 8.0
DISCORD_STAGE_TMO  = 10.0

# Proxy health
PROXY_MAX_PER_MIN   = 15
PROXY_MIN_GAP       = 1.0
PROXY_COOLDOWN_S    = 45
PROXY_FAIL_LIMIT    = 5
PROXY_SUSPECT_LIMIT = 3

# Files
RESULTS_FILE   = "results.jsonl"
HITS_FILE      = "available.txt"
CACHE_FILE     = "validated_proxies.json"
CACHE_TTL      = 900
DEAD_FILE      = "dead_proxies.txt"
USABLE_FILE    = "usable_proxies.txt"
SESSION_FILE   = "session.json"

STATS_INTERVAL = 5
MAX_SCRAPE_MB  = 8
EXHAUSTIVE_MAX = 100_000


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

    def inc(self, key, n=1):
        with self.counters_lock:
            self.counters[key] += n

    def hit(self, username):
        with self.hits_lock:
            self.hits.append(username)

    def snapshot_counters(self):
        with self.counters_lock:
            return dict(self.counters)

    def snapshot_hits(self):
        with self.hits_lock:
            return list(self.hits)


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
    sources: Set[str] = field(default_factory=set)
    status: str = "alive"
    fails: int = 0
    suspect: int = 0
    ok: int = 0
    busy_until: float = 0.0
    cooldown_until: float = 0.0
    last_used: float = 0.0
    request_times: deque = field(default_factory=deque)
    latency_ms: float = 0.0
    score: float = 0.0
    stage: int = 0

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
        self.items = sorted(proxies, key=lambda p: p.score, reverse=True)
        self.idx = -1

    def size(self):
        return len(self.items)

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

    async def acquire(self):
        async with self._lock:
            now = time.time()
            n = len(self.items)
            for _ in range(n):
                self.idx = (self.idx + 1) % n
                p = self.items[self.idx]
                if p.status == "cooldown" and p.cooldown_until <= now:
                    p.status = "alive"
                    p.fails = 0
                if self._ready(p, now):
                    p.busy_until = now + TIMEOUT_TOTAL
                    p.last_used = now
                    p.request_times.append(now)
                    return p
            return None

    async def release(self, p):
        if p is None:
            return
        async with self._lock:
            p.busy_until = 0.0

    async def report_success(self, p):
        if p is None:
            return
        async with self._lock:
            p.ok += 1
            p.fails = 0
            p.suspect = 0

    async def report_cooldown(self, p, seconds):
        if p is None:
            return
        async with self._lock:
            p.status = "cooldown"
            p.cooldown_until = time.time() + seconds

    async def report_transient_fail(self, p):
        if p is None:
            return
        async with self._lock:
            p.fails += 1
            if p.fails >= PROXY_FAIL_LIMIT:
                p.status = "dead"

    async def report_suspect(self, p):
        if p is None:
            return
        async with self._lock:
            p.suspect += 1
            if p.suspect >= PROXY_SUSPECT_LIMIT:
                p.status = "cooldown"
                p.cooldown_until = time.time() + 300
                p.suspect = 0

    def stats(self):
        now = time.time()
        by_proto = defaultdict(int)
        for p in self.items:
            if p.status == "alive":
                by_proto[p.key.protocol] += 1
        return {
            "total": len(self.items),
            "alive": sum(1 for p in self.items if p.status == "alive"),
            "cooldown": sum(1 for p in self.items
                            if p.status == "cooldown"
                            and p.cooldown_until > now),
            "dead": sum(1 for p in self.items if p.status == "dead"),
            "by_protocol": dict(by_proto),
        }

    def dead_keys(self):
        return [p.key for p in self.items if p.status == "dead"]


# ==================== SESSION MANAGER ====================
class SessionManager:
    def __init__(self):
        self._http = None
        self._socks: "OrderedDict[str, list]" = OrderedDict()
        self._lock = asyncio.Lock()
        self._closed = False

    async def _http_session(self):
        if self._closed:
            raise RuntimeError("SessionManager is closed")
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
            raise RuntimeError("SessionManager is closed")
        async with self._lock:
            if url in self._socks:
                entry = self._socks[url]
                entry[1] += 1
                self._socks.move_to_end(url)
                return entry[0]
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

            over = len(self._socks) - MAX_SOCKS_SESSIONS
            if over > 0:
                idle = [k for k, e in self._socks.items() if e[1] == 0]
                for k in idle[:over]:
                    _, [old, _] = self._socks.pop(k)
                    asyncio.create_task(self._safe_close(old))
                if len(self._socks) > MAX_SOCKS_SESSIONS:
                    log(f"[yellow]SOCKS cap exceeded: "
                        f"{len(self._socks)}/{MAX_SOCKS_SESSIONS} (all busy)[/]")
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

    async def close(self, timeout: float = 30.0):
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
        if self._cm:
            return await self._cm.__aexit__(*e)


class _HttpProxyReq:
    __slots__ = ("_sm", "_p", "_m", "_u", "_kw", "_cm")

    def __init__(self, sm, p, m, u, **kw):
        self._sm, self._p, self._m, self._u, self._kw, self._cm = sm, p, m, u, kw, None

    async def __aenter__(self):
        s = await self._sm._http_session()
        self._cm = s.request(self._m, self._u, proxy=self._p, **self._kw)
        return await self._cm.__aenter__()

    async def __aexit__(self, *e):
        if self._cm:
            return await self._cm.__aexit__(*e)


class _SocksReq:
    __slots__ = ("_sm", "_p", "_m", "_u", "_kw", "_cm", "_acquired")

    def __init__(self, sm, p, m, u, **kw):
        self._sm, self._p, self._m, self._u, self._kw = sm, p, m, u, kw
        self._cm = None
        self._acquired = False

    async def __aenter__(self):
        s = await self._sm._socks_acquire(self._p)
        self._acquired = True
        self._cm = s.request(self._m, self._u, **self._kw)
        return await self._cm.__aenter__()

    async def __aexit__(self, *e):
        try:
            if self._cm:
                return await self._cm.__aexit__(*e)
        finally:
            if self._acquired:
                self._acquired = False
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


# ==================== SCRAPER ====================
async def scrape_all(sm):
    lock = asyncio.Lock()
    result: Dict[ProxyKey, Proxy] = {}
    sem = asyncio.Semaphore(SCRAPE_WORKERS)

    async def fetch(tag, url, proto_hint):
        async with sem:
            try:
                async with sm.request("GET", url,
                                       timeout=aiohttp.ClientTimeout(total=40)) as r:
                    if r.status != 200:
                        log(f"[dim]  {tag}: HTTP {r.status}[/]")
                        return
                    raw = await r.content.read(MAX_SCRAPE_MB * 1024 * 1024)
                    text = raw.decode("utf-8", errors="ignore")
            except Exception as e:
                log(f"[dim]  {tag}: {type(e).__name__}: {str(e)[:50]}[/]")
                return

            added = 0
            async with lock:
                items = text.replace("\r", "\n").split("\n")
                if text.lstrip().startswith("["):
                    try:
                        arr = json.loads(text)
                        items = []
                        for o in arr:
                            if isinstance(o, dict):
                                ip, port = o.get("ip"), o.get("port")
                                if ip and port:
                                    items.append(f"{ip}:{port}")
                            elif isinstance(o, str):
                                items.append(o)
                    except Exception:
                        pass
                for raw_line in items:
                    key = parse_proxy_line(raw_line, proto_hint)
                    if not key:
                        continue
                    if key in result:
                        result[key].sources.add(tag)
                    else:
                        result[key] = Proxy(key=key, sources={tag})
                        added += 1
            if added:
                log(f"[green]  {tag}[/]: [dim]+{added}[/]")

    log(f"[bold]Scraping {len(SOURCES)} sources...[/]")
    await asyncio.gather(*[fetch(*s) for s in SOURCES], return_exceptions=True)
    log(f"[green]✓[/] Scraped [bold]{len(result)}[/] unique proxies\n")
    return result


# ==================== VALIDATION ====================
PROTO_WEIGHT = {"socks5": 1.0, "socks4": 0.85, "http": 0.7}


def score_proxy(lat, proto, bonus):
    lat = max(0.0, lat)
    lat_norm = 1.0 - min(1.0, lat / 3000.0)
    return 0.5 * lat_norm + 0.3 * PROTO_WEIGHT.get(proto, 0.5) + 0.2 * bonus


async def _tcp_probe(host, port, timeout):
    try:
        r, w = await asyncio.wait_for(
            asyncio.open_connection(host, port), timeout=timeout)
        w.close()
        try:
            await w.wait_closed()
        except Exception:
            pass
        return True
    except Exception:
        return False


async def _stage_https(sm, p, timeout):
    t0 = time.perf_counter()
    try:
        async with sm.request("GET", API_IPIFY, proxy=p,
                              timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            lat = (time.perf_counter() - t0) * 1000
            if r.status == 200:
                await r.read()
                return True, lat
            return False, 0.0
    except Exception:
        return False, 0.0


async def _stage_discord(sm, p, timeout):
    t0 = time.perf_counter()
    try:
        async with sm.request("GET", API_GATEWAY, proxy=p,
                              timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            lat = (time.perf_counter() - t0) * 1000
            if r.status == 200:
                await r.read()
                return True, lat
            return False, 0.0
    except Exception:
        return False, 0.0


async def _bounded_map(items, fn, workers, on_result=None):
    q = asyncio.Queue(maxsize=max(4, workers * 4))
    count = [0]
    count_lock = asyncio.Lock()

    async def worker():
        while True:
            item = await q.get()
            if item is None:
                q.task_done()
                return
            try:
                r = await fn(item)
                if r is not None:
                    if on_result is not None:
                        on_result(r)
                    async with count_lock:
                        count[0] += 1
            except Exception:
                pass
            finally:
                q.task_done()

    ws = [asyncio.create_task(worker()) for _ in range(workers)]
    try:
        for it in items:
            await q.put(it)
        for _ in ws:
            await q.put(None)
        await q.join()
    finally:
        for w in ws:
            if not w.done():
                w.cancel()
        await asyncio.gather(*ws, return_exceptions=True)
    return count[0]


async def validate_all(sm, proxies):
    if not proxies:
        return []

    items = list(proxies.values())

    log(f"[yellow]Stage 0: TCP on {len(items)}[/]")
    stage1: List[Proxy] = []
    counter = [0]
    total_items = len(items)

    async def s0(p):
        ok = await _tcp_probe(p.key.host, p.key.port, TCP_STAGE_TIMEOUT)
        counter[0] += 1
        if counter[0] % 500 == 0:
            pct = counter[0] * 100 / total_items
            log(f"[dim]  Stage0: {counter[0]}/{total_items} "
                f"({pct:.0f}%) alive={len(stage1)}[/]")
        return p if ok else None

    await _bounded_map(items, s0, VALIDATE_WORKERS,
                       on_result=stage1.append)
    log(f"[green]✓[/] Stage 0: {len(stage1)}/{len(items)}\n")
    if not stage1:
        return []

    log(f"[yellow]Stage 1: HTTPS on {len(stage1)}[/]")
    stage2: List[Tuple[Proxy, float]] = []
    counter1 = [0]
    total1 = len(stage1)

    async def s1(p):
        ok, lat = await _stage_https(sm, p, HTTPS_STAGE_TMO)
        counter1[0] += 1
        if counter1[0] % 100 == 0:
            pct = counter1[0] * 100 / total1
            log(f"[dim]  Stage1: {counter1[0]}/{total1} "
                f"({pct:.0f}%) alive={len(stage2)}[/]")
        return (p, lat) if ok else None

    await _bounded_map(stage1, s1, VALIDATE_WORKERS,
                       on_result=stage2.append)
    log(f"[green]✓[/] Stage 1: {len(stage2)}/{len(stage1)}\n")
    if not stage2:
        return []

    log(f"[yellow]Stage 2: Discord on {len(stage2)}[/]")
    stage3: List[Tuple[Proxy, float]] = []
    counter2 = [0]
    total2 = len(stage2)

    async def s2(item):
        p, h_lat = item
        ok, d_lat = await _stage_discord(sm, p, DISCORD_STAGE_TMO)
        counter2[0] += 1
        if counter2[0] % 50 == 0:
            pct = counter2[0] * 100 / total2
            log(f"[dim]  Stage2: {counter2[0]}/{total2} "
                f"({pct:.0f}%) alive={len(stage3)}[/]")
        return (p, (h_lat + d_lat) / 2) if ok else None

    await _bounded_map(stage2, s2, VALIDATE_WORKERS,
                       on_result=stage3.append)
    log(f"[green]✓[/] Stage 2: {len(stage3)}/{len(stage2)}\n")

    if stage3:
        final, stage_val, label = stage3, 2, "Discord-validated"
    else:
        log("[yellow]Discord unreachable via all proxies — "
            "using HTTPS-only fallback[/]")
        final, stage_val, label = stage2, 1, "HTTPS-only"

    for p, lat in final:
        p.latency_ms = lat
        p.stage = stage_val
        bonus = 0.15 if any(s.startswith("clearproxy") for s in p.sources) else 0.0
        p.score = score_proxy(lat, p.key.protocol, bonus)

    out = [p for p, _ in final]
    out.sort(key=lambda x: x.score, reverse=True)
    log(f"[bold green]═══ {len(out)} usable ({label}) ═══[/]\n")
    return out


# ==================== CACHE ====================
def _valid_cache_entry(e):
    if not isinstance(e, dict):
        return None
    p = e.get("p")
    h = e.get("h")
    port_raw = e.get("port")
    if p not in ("http", "socks4", "socks5"):
        return None
    if p in ("socks4", "socks5") and not SOCKS_OK:
        return None
    if not isinstance(h, str) or not _validate_host(h):
        return None
    try:
        port = int(port_raw)
    except (TypeError, ValueError):
        return None
    if not (0 < port < 65536):
        return None

    user = e.get("u")
    pw = e.get("pw")
    if user is not None and not isinstance(user, str):
        return None
    if pw is not None and not isinstance(pw, str):
        return None

    try:
        score = float(e.get("score", 0.0))
        lat = float(e.get("lat", 0.0))
        stage = int(e.get("stage", 0))
    except (TypeError, ValueError):
        return None
    if not math.isfinite(score) or not math.isfinite(lat):
        return None
    if not (0.0 <= score <= 1.0):
        return None
    if not (0.0 <= lat <= 60_000.0):
        return None
    if stage not in (0, 1, 2):
        return None

    src_raw = e.get("src", [])
    if not isinstance(src_raw, list):
        return None
    if not all(isinstance(s, str) and 0 < len(s) < 64 for s in src_raw):
        return None
    src = set(src_raw)

    return (ProxyKey(protocol=p, host=h, port=port, user=user, password=pw),
            score, lat, stage, src)


def load_cache():
    if not os.path.exists(CACHE_FILE):
        return []
    try:
        with open(CACHE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if time.time() - data.get("ts", 0) > CACHE_TTL:
            return []
        out = []
        rejected = 0
        for e in data.get("proxies", []):
            parsed = _valid_cache_entry(e)
            if parsed is None:
                rejected += 1
                continue
            key, score, lat, stage, src = parsed
            p = Proxy(key=key, sources=src)
            p.score = score
            p.latency_ms = lat
            p.stage = stage
            out.append(p)
        if rejected:
            log(f"[yellow]Cache: rejected {rejected} invalid entries[/]")
        return out
    except Exception as ex:
        log(f"[yellow]Cache load failed: {ex}[/]")
        return []


def save_cache(proxies):
    try:
        data = {"ts": time.time(), "proxies": [
            {"p": p.key.protocol, "h": p.key.host, "port": p.key.port,
             "u": p.key.user, "pw": p.key.password,
             "score": p.score, "lat": p.latency_ms, "stage": p.stage,
             "src": sorted(p.sources)}
            for p in proxies]}
        d = os.path.dirname(os.path.abspath(CACHE_FILE)) or "."
        tmp = None
        try:
            with tempfile.NamedTemporaryFile(
                "w", dir=d, delete=False, encoding="utf-8",
                prefix=".cache_", suffix=".tmp",
            ) as tf:
                json.dump(data, tf)
                tmp = tf.name
            os.replace(tmp, CACHE_FILE)
            try:
                os.chmod(CACHE_FILE, 0o600)
            except Exception:
                pass
        except Exception:
            if tmp and os.path.exists(tmp):
                try:
                    os.unlink(tmp)
                except Exception:
                    pass
            raise
    except Exception as e:
        log(f"[yellow]Cache save failed: {e}[/]")


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

    if space <= EXHAUSTIVE_MAX:
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
    if len(out) < limit:
        log(f"[yellow]Generated {len(out)}/{limit} "
            f"(attempts exhausted)[/]")
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
            return "confirmed_available", "", "ok", 0.0
        return "unknown", "200_unknown_shape", "ok", 0.0

    if code == 429:
        ra = 5.0
        try:
            ra = float(body.get("retry_after", 5.0))
        except Exception:
            pass
        ra = max(1.0, min(ra, 120.0))
        return "rate_limited", f"ra={ra:.1f}", "cooldown", ra

    if code in (400, 422):
        cv = body.get("code")
        if cv == 50035:
            return "confirmed_invalid", "code_50035", "ok", 0.0
        msg = str(body.get("message", "")).lower()
        if "username" in msg and "invalid" in msg:
            return "confirmed_invalid", "username_invalid", "ok", 0.0
        return "client_error", f"http_{code}", "none", 0.0

    if code == 401:
        return "client_error", "unauthorized", "ok", 0.0
    if code == 403:
        return "forbidden", "forbidden", "suspect", 5.0
    if code in (407, 502, 503, 504):
        return "server_error", f"gateway_{code}", "transient", 15.0
    if code >= 500:
        return "server_error", f"http_{code}", "transient", 10.0
    return "unknown", f"http_{code}", "none", 0.0


# ==================== CHECKER ====================
class Checker:
    def __init__(self, pp, sm, session_id, require_proxy=True):
        self.pp = pp
        self.sm = sm
        self.session_id = session_id
        self.require_proxy = require_proxy
        self.fp = open(RESULTS_FILE, "a", encoding="utf-8")
        self.fp_lock = asyncio.Lock()
        self.counters = defaultdict(int)
        self._recorded: Set[int] = set()
        self._recorded_lock = asyncio.Lock()
        self.completed = 0

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
        line = json.dumps(rec, ensure_ascii=False) + "\n"
        async with self.fp_lock:
            self.fp.write(line)
            self.fp.flush()

    async def check_one(self, username, idx):
        if not valid_username(username):
            await self._record(idx, username, "invalid_format", 0, "precheck")
            plog("Err", f"@{username}", idx, "[dim]invalid[/]")
            return "invalid_format"

        proxy = await self.pp.acquire()
        acquired = proxy is not None

        if proxy is None and self.require_proxy:
            reason = "pool_empty" if self.pp.size() == 0 else "all_busy"
            await self._record(idx, username, "no_proxy", 0, reason)
            plog("Err", f"@{username}", idx, "[yellow]no_proxy[/]")
            return "no_proxy"

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
            except asyncio.TimeoutError:
                await self.pp.report_transient_fail(proxy)
                await self._record(idx, username, "error", 0, "timeout")
                plog("Err", f"@{username}", idx, "[dim]timeout[/]")
                return "error"
            except asyncio.CancelledError:
                raise
            except Exception as e:
                await self.pp.report_transient_fail(proxy)
                reason = f"exc:{type(e).__name__}"
                await self._record(idx, username, "error", 0, reason)
                plog("Err", f"@{username}", idx, f"[red]{reason}[/]")
                return "error"

            lat_ms = (time.perf_counter() - t0) * 1000
            kind, reason, action, cd = classify_response(status_code, body_text)

            if action == "ok":
                await self.pp.report_success(proxy)
            elif action == "transient":
                await self.pp.report_transient_fail(proxy)
            elif action == "suspect":
                await self.pp.report_suspect(proxy)
            elif action == "cooldown":
                await self.pp.report_cooldown(proxy, cd)

            if kind == "confirmed_available":
                status = "available"
                plog("Avb", f"@{username}", idx)
                STATE.hit(username)
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
            if acquired:
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
                        await self._record(idx, u, "skipped", 0,
                                           "stop_requested")
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
        self.require_proxy = True

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
                log(f"[dim cyan]prx[a={ps['alive']} c={ps['cooldown']} "
                    f"d={ps['dead']}] hits={hits} completed={done} "
                    f"rps={rps:.1f}[/]")
        except asyncio.CancelledError:
            return

    async def run(self, usernames):
        cached = load_cache()
        if cached:
            log(f"[green]Loaded {len(cached)} proxies from cache[/]")
            proxies = cached
        else:
            raw = await scrape_all(self.sm)

            # Cap for iSH responsiveness
            if len(raw) > MAX_PROXIES_TO_VALIDATE:
                keys = random.sample(list(raw.keys()), MAX_PROXIES_TO_VALIDATE)
                raw_sampled = {k: raw[k] for k in keys}
                log(f"[yellow]Capped {len(raw)} → "
                    f"{len(raw_sampled)} for validation[/]")
                raw = raw_sampled

            proxies = await validate_all(self.sm, raw)
            save_cache(proxies)

        self.pp = ProxyPool(proxies)

        if proxies:
            with open(USABLE_FILE, "w", encoding="utf-8") as f:
                for p in proxies:
                    f.write(f"{p.safe_url}\t{p.key.protocol}\t"
                            f"stage={p.stage}\tlat={p.latency_ms:.0f}ms\t"
                            f"score={p.score:.3f}\t"
                            f"src={','.join(sorted(p.sources))}\n")

        if proxies and RICH:
            tbl = Table(title="Top 10 Proxies")
            for c in ("Proxy", "Proto", "Latency", "Score",
                      "Stage", "Sources"):
                tbl.add_column(c)
            for p in proxies[:10]:
                tbl.add_row(p.safe_url, p.key.protocol,
                            f"{p.latency_ms:.0f}ms", f"{p.score:.3f}",
                            "Discord" if p.stage == 2 else "HTTPS",
                            ",".join(sorted(p.sources))[:30])
            console.print(tbl)

        if self.pp.size() == 0:
            log("[red]No proxies available.[/]")
            if RICH:
                self.require_proxy = not Confirm.ask(
                    "Continue without proxy (direct connection)?",
                    default=False)
            else:
                self.require_proxy = True
            if self.require_proxy:
                log("[red]Aborting — no proxies and direct not allowed.[/]")
                await self.sm.close()
                return
            log("[yellow]WARNING: running direct — your IP will be used.[/]")

        self.checker = Checker(self.pp, self.sm, self.session_id,
                                require_proxy=self.require_proxy)
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
        log(f"  Proxies alive:  {ps.get('alive', 0)} "
            f"(dead={ps.get('dead', 0)}, cooling={ps.get('cooldown', 0)})")

        if hits:
            save = True
            if RICH:
                try:
                    save = Confirm.ask(
                        f"Save {len(hits)} available to {HITS_FILE}?",
                        default=True)
                except Exception:
                    save = True
            if save:
                with open(HITS_FILE, "w", encoding="utf-8") as f:
                    f.write("\n".join(hits))
                log(f"[green]✓[/] Saved {len(hits)} to {HITS_FILE}")

        if self.pp:
            dead = self.pp.dead_keys()
            if dead:
                with open(DEAD_FILE, "w", encoding="utf-8") as f:
                    for k in dead:
                        f.write(f"{k.protocol}://{k.host}:{k.port}\n")

        try:
            with open(SESSION_FILE, "w", encoding="utf-8") as f:
                json.dump({
                    "session_id": self.session_id,
                    "elapsed_s": round(elapsed, 1),
                    "counters": dict(c),
                    "proxies": ps,
                }, f, indent=2)
        except Exception:
            pass

        if self.checker:
            self.checker.close()
        await self.sm.close()


# ==================== MAIN ====================
def _prompt_mode():
    if RICH:
        console.print(Panel.fit(
            "[bold cyan]Discord Username Checker V10.2[/]\n"
            "[dim]Tokenless · iSH-optimized · SOCKS5/HTTP[/]",
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
        print("\nInterrupted")
    except Exception as e:
        print(f"Fatal: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()
