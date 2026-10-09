import os
import sys
import time
import json
import math
import random
import string
import hashlib
import threading
from collections import defaultdict, OrderedDict
from queue import Queue, Empty
from concurrent.futures import ThreadPoolExecutor

import requests
import urllib3

VERIFY_TLS = True
if not VERIFY_TLS:
    urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

API = "https://discord.com/api/v10/unique-username/check-username"
VALIDATE_URL = "https://discord.com/api/v10/gateway"

PROXY_SOURCES = [
    "https://api.proxyscrape.com/v2/?request=displayproxies&protocol=http&timeout=5000&country=all",
    "https://raw.githubusercontent.com/TheSpeedX/PROXY-List/master/http.txt",
    "https://raw.githubusercontent.com/ShiftyTR/Proxy-List/master/http.txt",
    "https://raw.githubusercontent.com/monosans/proxy-list/main/proxies/http.txt",
    "https://raw.githubusercontent.com/clarketm/proxy-list/master/proxy-list-raw.txt",
    "https://raw.githubusercontent.com/roosterkid/openproxylist/main/HTTPS_RAW.txt",
    "https://raw.githubusercontent.com/mertguvencli/Proxy-List-World/main/data.txt",
]

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:123.0) Gecko/20100101 Firefox/123.0",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
]

CONCURRENCY         = 5
QUEUE_MAX           = CONCURRENCY * 4
TIMEOUT             = 10
MAX_GENERATE        = 20000
MAX_PROXY_FAILS     = 3
MAX_TOKEN_FAILS     = 2
MAX_FORBIDDEN       = 4
MAX_RETRIES         = 4
PROXY_COOLDOWN      = 60
TOKEN_COOLDOWN_MAX  = 60
SERVICE_PAUSE_MAX   = 120
STATS_INTERVAL      = 5
ACQUIRE_MAX_WAIT    = 10
VALIDATE_TIMEOUT    = 4
VALIDATE_WORKERS    = 50
MAX_LATENCY_SAMPLES = 20000
MAX_SESSIONS        = 200
WRITE_BATCH         = 100
WRITE_INTERVAL      = 1.5
RSS_WARN_MB         = 500

RESULTS_FILE = 'results.jsonl'
STATE_FILE   = 'state.json'
BENCH_FILE   = 'benchmark.json'

TERMINAL_STATUSES  = {'available', 'taken', 'invalid_format'}
RETRYABLE_STATUSES = {'error', 'timeout', 'rate_limited', 'forbidden',
                      'not_found', 'proxy_dead', 'token_dead',
                      'tls_error', 'dns_error', 'conn_refused',
                      'conn_reset', 'internal_error', 'unknown_response'}


# ======================== RUNTIME ========================

def rss_mb():
    try:
        with open(f'/proc/{os.getpid()}/status') as f:
            for line in f:
                if line.startswith('VmRSS:'):
                    return int(line.split()[1]) / 1024.0
    except Exception:
        pass
    return 0.0


# ======================== SERVICE LIMITER ========================

class ServiceLimiter:
    def __init__(self):
        self.lock = threading.Lock()
        self.pause_until = 0.0
        self.pause_count = 0
        self.total_paused_s = 0.0

    def pause(self, seconds):
        seconds = max(0.5, min(seconds, SERVICE_PAUSE_MAX))
        with self.lock:
            new_until = time.time() + seconds
            if new_until > self.pause_until:
                self.pause_until = new_until
            self.pause_count += 1
            self.total_paused_s += seconds

    def wait_if_paused(self):
        while True:
            with self.lock:
                remaining = self.pause_until - time.time()
            if remaining <= 0:
                return
            time.sleep(min(remaining, 1.0))

    def snapshot(self):
        with self.lock:
            return {
                'pause_count': self.pause_count,
                'total_paused_s': round(self.total_paused_s, 1),
                'currently_paused': self.pause_until > time.time(),
            }


# ======================== METRICS ========================

class Metrics:
    def __init__(self, max_samples=MAX_LATENCY_SAMPLES):
        self.lock = threading.Lock()
        self.max_samples = max_samples
        self.total_recorded = 0
        self.latencies = []
        self.by_status = defaultdict(int)
        self.by_http = defaultdict(int)
        self.by_reason = defaultdict(int)
        self.by_proxy_class = defaultdict(int)
        self.stage_sums = defaultdict(float)
        self.stage_count = defaultdict(int)

    def record(self, status, http_code, latency_ms, reason=None,
               proxy_used=False, stage=None):
        with self.lock:
            self.total_recorded += 1
            self.by_status[status] += 1
            self.by_http[http_code] += 1
            if reason:
                self.by_reason[reason] += 1
            self.by_proxy_class['with_proxy' if proxy_used else 'direct'] += 1

            if len(self.latencies) < self.max_samples:
                self.latencies.append(latency_ms)
            else:
                j = random.randint(0, self.total_recorded - 1)
                if j < self.max_samples:
                    self.latencies[j] = latency_ms

            if stage:
                for k, v in stage.items():
                    self.stage_sums[k] += v
                    self.stage_count[k] += 1

    @staticmethod
    def _percentile(sorted_vals, p):
        if not sorted_vals:
            return 0.0
        k = (len(sorted_vals) - 1) * p
        f = int(math.floor(k))
        c = min(f + 1, len(sorted_vals) - 1)
        if f == c:
            return sorted_vals[f]
        return sorted_vals[f] + (sorted_vals[c] - sorted_vals[f]) * (k - f)

    def summary(self):
        with self.lock:
            lat = sorted(self.latencies)
            n = len(lat)
            total = self.total_recorded
            by_status = dict(self.by_status)
            by_http = dict(self.by_http)
            by_reason = dict(self.by_reason)
            by_proxy_class = dict(self.by_proxy_class)
            stage_avg = {
                k: round(self.stage_sums[k] / max(1, self.stage_count[k]), 2)
                for k in self.stage_sums
            }
        out = {
            'total_recorded': total,
            'sampled': n,
            'by_status': by_status,
            'by_http': by_http,
            'by_reason': by_reason,
            'by_proxy_class': by_proxy_class,
            'stage_avg_ms': stage_avg,
        }
        if n:
            out.update({
                'min_ms': round(lat[0], 1),
                'avg_ms': round(sum(lat) / n, 1),
                'p50_ms': round(self._percentile(lat, 0.50), 1),
                'p95_ms': round(self._percentile(lat, 0.95), 1),
                'p99_ms': round(self._percentile(lat, 0.99), 1),
                'max_ms': round(lat[-1], 1),
            })
        return out


# ======================== POOL ========================

class Pool:
    def __init__(self, values, name):
        self.name = name
        self.lock = threading.Lock()
        self.items = [self._make(v) for v in values]
        self.idx = -1
        self.fail_limit = MAX_PROXY_FAILS if name == 'proxy' else MAX_TOKEN_FAILS

    @staticmethod
    def _make(value):
        return {
            'value': value, 'status': 'alive',
            'fails': 0, 'forbidden': 0, 'ok': 0,
            'cooldown_until': 0.0, 'reason': None,
        }

    def size(self):
        with self.lock:
            return len(self.items)

    def _refresh_locked(self):
        now = time.time()
        for it in self.items:
            if it['status'] == 'cooldown' and it['cooldown_until'] <= now:
                it['status'] = 'alive'
                it['fails'] = 0

    def next(self):
        with self.lock:
            if not self.items:
                return None
            self._refresh_locked()
            n = len(self.items)
            for _ in range(n):
                self.idx = (self.idx + 1) % n
                it = self.items[self.idx]
                if it['status'] == 'alive':
                    return it
            return None

    def has_cooldown(self):
        with self.lock:
            return any(it['status'] == 'cooldown' for it in self.items)

    def next_cooldown_delta(self):
        with self.lock:
            now = time.time()
            deltas = [it['cooldown_until'] - now for it in self.items
                      if it['status'] == 'cooldown']
            return max(0.1, min(deltas)) if deltas else None

    def report(self, item, status, cooldown=0.0):
        if item is None:
            return
        with self.lock:
            if status in ('available', 'taken'):
                item['ok'] += 1
                item['fails'] = 0
                item['forbidden'] = 0
                return
            if status == 'rate_limited':
                item['status'] = 'cooldown'
                item['cooldown_until'] = time.time() + max(1.0, cooldown)
                return
            if status == 'dead':
                item['status'] = 'dead'
                item['reason'] = 'hard-fail'
                return
            if status == 'forbidden':
                item['forbidden'] += 1
                if item['forbidden'] >= MAX_FORBIDDEN:
                    item['status'] = 'dead'
                    item['reason'] = 'repeated-forbidden'
                return
            item['fails'] += 1
            if item['fails'] >= self.fail_limit:
                item['status'] = 'dead'
                item['reason'] = 'too-many-fails'

    def stats(self):
        with self.lock:
            a = sum(1 for i in self.items if i['status'] == 'alive')
            d = sum(1 for i in self.items if i['status'] == 'dead')
            c = sum(1 for i in self.items if i['status'] == 'cooldown')
            return {'total': len(self.items), 'alive': a, 'dead': d, 'cooldown': c}

    def dead_list(self):
        with self.lock:
            return [i['value'] for i in self.items if i['status'] == 'dead']


# ======================== SESSION POOL (LRU) ========================

class SessionPool:
    def __init__(self, max_sessions=MAX_SESSIONS):
        self.max = max_sessions
        self.lock = threading.Lock()
        self.sessions = OrderedDict()

    def _new(self):
        s = requests.Session()
        s.verify = VERIFY_TLS
        adapter = requests.adapters.HTTPAdapter(
            pool_connections=4, pool_maxsize=8, max_retries=0,
        )
        s.mount('https://', adapter)
        s.mount('http://', adapter)
        return s

    def get(self, key):
        with self.lock:
            if key in self.sessions:
                self.sessions.move_to_end(key)
                return self.sessions[key]
        s = self._new()
        with self.lock:
            if key in self.sessions:
                try: s.close()
                except Exception: pass
                self.sessions.move_to_end(key)
                return self.sessions[key]
            self.sessions[key] = s
            if len(self.sessions) > self.max:
                _, old = self.sessions.popitem(last=False)
                try: old.close()
                except Exception: pass
            return s

    def close_all(self):
        with self.lock:
            for s in self.sessions.values():
                try: s.close()
                except Exception: pass
            self.sessions.clear()


SESSION_POOL = SessionPool()


# ======================== BUFFERED WRITER ========================

class JSONLWriter:
    def __init__(self, path, batch=WRITE_BATCH, interval=WRITE_INTERVAL):
        self.fp = open(path, 'a', encoding='utf-8')
        self.lock = threading.Lock()
        self.buf = []
        self.batch = batch
        self.interval = interval
        self.last_flush = time.time()
        self.closed = False
        self.bytes_written = 0

    def write(self, rec):
        if self.closed:
            return
        line = json.dumps(rec, ensure_ascii=False)
        with self.lock:
            self.buf.append(line)
            need = (len(self.buf) >= self.batch or
                    time.time() - self.last_flush >= self.interval)
        if need:
            self._flush()

    def _flush(self):
        with self.lock:
            if not self.buf:
                return
            data = '\n'.join(self.buf) + '\n'
            self.buf.clear()
            self.last_flush = time.time()
        try:
            self.fp.write(data)
            self.fp.flush()
            self.bytes_written += len(data)
        except Exception:
            pass

    def close(self):
        with self.lock:
            self.closed = True
        self._flush()
        try:
            self.fp.close()
        except Exception:
            pass


# ======================== HELPERS ========================

def token_id(token):
    return hashlib.sha256(token.encode()).hexdigest()[:16]


def load_lines(path):
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        return [ln.strip() for ln in f if ln.strip()]


def normalize_proxy(line):
    line = line.strip()
    if not line:
        return None
    if '://' in line:
        return line
    parts = line.split(':')
    if len(parts) == 2:
        host, port = parts
        if not port.isdigit() or not (0 < int(port) < 65536):
            return None
        return f'http://{host}:{port}'
    if len(parts) == 4:
        host, port, user, pw = parts
        if not port.isdigit() or not (0 < int(port) < 65536):
            return None
        return f'http://{user}:{pw}@{host}:{port}'
    return None


def normalize_token(line):
    t = line.strip()
    if t.startswith('"') and t.endswith('"'):
        t = t[1:-1]
    return t


def proxies_dict(proxy_url):
    return {'http': proxy_url, 'https': proxy_url} if proxy_url else None


def is_valid_username(u):
    if not (2 <= len(u) <= 32):
        return False
    if u in ('everyone', 'here'):
        return False
    if u[0] in '._' or u[-1] in '._':
        return False
    if '..' in u:
        return False
    allowed = set(string.ascii_lowercase + string.digits + '._')
    return all(c in allowed for c in u)


def generate_usernames(length, charset, mode, limit):
    seen = set()
    produced = 0

    if mode == 'random':
        space = len(charset) ** length
        if space > 100000:
            attempts = 0
            max_attempts = limit * 50
            while produced < limit and attempts < max_attempts:
                s = ''.join(random.choices(charset, k=length))
                attempts += 1
                if s in seen:
                    continue
                if is_valid_username(s):
                    seen.add(s)
                    produced += 1
                    yield s
        else:
            import itertools
            space_list = [''.join(p) for p in itertools.product(charset, repeat=length)]
            valid = [u for u in space_list if is_valid_username(u)]
            random.shuffle(valid)
            for u in valid[:limit]:
                if u in seen:
                    continue
                seen.add(u)
                produced += 1
                yield u
    else:
        idx = [0] * length
        exhausted = False
        while produced < limit and not exhausted:
            s = ''.join(charset[i] for i in idx)
            if s not in seen and is_valid_username(s):
                seen.add(s)
                produced += 1
                yield s
            p = length - 1
            while p >= 0:
                idx[p] += 1
                if idx[p] < len(charset):
                    break
                idx[p] = 0
                p -= 1
            if p < 0:
                exhausted = True


# ======================== DISCORD CHECK ========================

def parse_200(body):
    if not isinstance(body, dict):
        return None, 'body_not_dict'
    if isinstance(body.get('taken'), bool):
        return ('taken' if body['taken'] else 'available'), None
    if body.get('code') == 200 and isinstance(body.get('username'), str):
        return 'available', None
    return None, 'unknown_200_shape'


def classify_request_exception(e):
    if isinstance(e, requests.exceptions.ProxyError):
        return 'proxy_dead', 'proxy_error'
    if isinstance(e, requests.exceptions.SSLError):
        return 'tls_error', 'tls_failure'
    if isinstance(e, requests.exceptions.ReadTimeout):
        return 'timeout', 'read_timeout'
    if isinstance(e, requests.exceptions.ConnectTimeout):
        return 'proxy_dead', 'connect_timeout'
    if isinstance(e, requests.exceptions.ConnectionError):
        msg = str(e).lower()
        if 'name or service not known' in msg or 'gaierror' in msg or 'nodename nor servname' in msg:
            return 'dns_error', 'dns_failure'
        if 'connection refused' in msg or 'econnrefused' in msg:
            return 'conn_refused', 'connection_refused'
        if 'connection reset' in msg or 'econnreset' in msg:
            return 'conn_reset', 'connection_reset'
        return 'proxy_dead', 'connection_error'
    if isinstance(e, requests.exceptions.Timeout):
        return 'timeout', 'timeout_generic'
    return 'error', f'exception_{type(e).__name__}'


def check_username(username, token, proxy_url, limiter, timing):
    t0 = time.perf_counter()
    limiter.wait_if_paused()

    headers = {
        'User-Agent': random.choice(USER_AGENTS),
        'Authorization': token,
        'Content-Type': 'application/json',
        'Accept': '*/*',
        'Accept-Language': 'en-US,en;q=0.9',
        'Origin': 'https://discord.com',
        'Referer': 'https://discord.com/',
    }
    session = SESSION_POOL.get(proxy_url or '__direct__')

    timing['http_start'] = time.perf_counter()
    try:
        r = session.post(
            API,
            data=json.dumps({'username': username}),
            headers=headers,
            proxies=proxies_dict(proxy_url),
            timeout=TIMEOUT,
        )
    except Exception as e:
        timing['http_end'] = time.perf_counter()
        status, reason = classify_request_exception(e)
        return (status, 0.0, 0, reason, timing)
    timing['http_end'] = time.perf_counter()

    code = r.status_code

    if code == 200:
        try:
            body = r.json()
        except Exception:
            return ('unknown_response', 0.0, code, 'json_decode_failed', timing)
        s, why = parse_200(body)
        if s is None:
            return ('unknown_response', 0.0, code, why or 'unknown_200', timing)
        return (s, 0.0, code, None, timing)

    if code == 429:
        ra = 1.0
        try:
            j = r.json()
            if j.get('retry_after') is not None:
                ra = float(j['retry_after'])
            elif r.headers.get('Retry-After'):
                ra = float(r.headers['Retry-After'])
        except Exception:
            pass
        ra = max(0.5, min(ra, TOKEN_COOLDOWN_MAX))
        limiter.pause(ra)
        return ('rate_limited', ra, code, f'retry_after={ra:.2f}', timing)

    if code == 400:
        return ('invalid_format', 0.0, code, 'discord_rejected_username', timing)
    if code == 401:
        return ('token_dead', 0.0, code, 'unauthorized', timing)
    if code == 403:
        return ('forbidden', 0.0, code, 'forbidden_not_fatal', timing)
    if code == 404:
        return ('not_found', 0.0, code, 'endpoint_404', timing)
    if code in (407, 502, 503, 504):
        return ('proxy_dead', 0.0, code, f'gateway_{code}', timing)
    if code >= 500:
        return ('error', 0.0, code, f'discord_5xx_{code}', timing)
    return ('error', 0.0, code, f'http_{code}', timing)


# ======================== ACQUIRE ========================

def acquire(pool, max_wait):
    if pool.size() == 0:
        return None
    deadline = time.time() + max_wait
    while True:
        it = pool.next()
        if it is not None:
            return it
        if not pool.has_cooldown():
            return None
        delta = pool.next_cooldown_delta()
        if delta is None:
            return None
        remaining = deadline - time.time()
        if remaining <= 0:
            return None
        time.sleep(min(delta, 1.0, remaining))


# ======================== RETRY LOGIC ========================

def make_record(username, status, http_code, latency_ms, reason, proxy_url,
                tid, attempts, timing=None):
    rec = {
        'ts': round(time.time(), 3),
        'username': username,
        'status': status,
        'http': http_code,
        'latency_ms': latency_ms,
        'proxy': proxy_url,
        'token_id': tid,
        'reason': reason,
        'attempts': attempts,
        'terminal': status in TERMINAL_STATUSES,
    }
    if timing:
        rec['timing'] = timing
    return rec


def compute_timing(ts):
    if not ts:
        return None
    out = {}
    if 'enqueue' in ts and 'pickup' in ts:
        out['queue_wait_ms'] = round((ts['pickup'] - ts['enqueue']) * 1000, 1)
    if 'pickup' in ts and 'token_ok' in ts:
        out['token_wait_ms'] = round((ts['token_ok'] - ts['pickup']) * 1000, 1)
    if 'token_ok' in ts and 'proxy_ok' in ts:
        out['proxy_wait_ms'] = round((ts['proxy_ok'] - ts['token_ok']) * 1000, 1)
    if 'http_start' in ts and 'http_end' in ts:
        out['http_ms'] = round((ts['http_end'] - ts['http_start']) * 1000, 1)
    if 'enqueue' in ts and 'done' in ts:
        out['total_ms'] = round((ts['done'] - ts['enqueue']) * 1000, 1)
    return out


def check_with_retry(username, token_pool, proxy_pool, limiter, t_enqueue):
    ts = {'enqueue': t_enqueue}
    ts['pickup'] = time.perf_counter()

    if not is_valid_username(username):
        ts['done'] = time.perf_counter()
        return make_record(username, 'invalid_format', 0, 0.0,
                           'precheck_local', None, None, 0, compute_timing(ts))

    use_proxy = proxy_pool.size() > 0
    used_tokens = set()
    used_proxies = set()
    last = None
    attempts_made = 0

    for _ in range(MAX_RETRIES):
        limiter.wait_if_paused()

        token_item = acquire(token_pool, ACQUIRE_MAX_WAIT)
        ts['token_ok'] = time.perf_counter()
        if token_item is None or token_item['value'] in used_tokens:
            ts['done'] = time.perf_counter()
            last = make_record(username, 'error', 0, 0.0,
                               'no_token_available', None, None,
                               attempts_made, compute_timing(ts))
            break
        used_tokens.add(token_item['value'])

        proxy_item = None
        if use_proxy:
            proxy_item = acquire(proxy_pool, ACQUIRE_MAX_WAIT)
            ts['proxy_ok'] = time.perf_counter()
            if proxy_item is None or proxy_item['value'] in used_proxies:
                ts['done'] = time.perf_counter()
                last = make_record(username, 'error', 0, 0.0,
                                   'no_proxy_available', None,
                                   token_id(token_item['value']),
                                   attempts_made, compute_timing(ts))
                break
            used_proxies.add(proxy_item['value'])
        else:
            ts['proxy_ok'] = ts.get('token_ok', time.perf_counter())

        proxy_val = proxy_item['value'] if proxy_item else None
        attempts_made += 1

        status, ra, http_code, reason, timing = check_username(
            username, token_item['value'], proxy_val, limiter, ts
        )
        lat_ms = (timing['http_end'] - timing['http_start']) * 1000

        if status in TERMINAL_STATUSES:
            token_pool.report(token_item, status)
            if proxy_item:
                proxy_pool.report(proxy_item, status)
            ts['done'] = time.perf_counter()
            return make_record(username, status, http_code, round(lat_ms, 1),
                               reason, proxy_val, token_id(token_item['value']),
                               attempts_made, compute_timing(ts))

        if status == 'unknown_response':
            token_pool.report(token_item, 'error')
            if proxy_item:
                proxy_pool.report(proxy_item, 'error')
            ts['done'] = time.perf_counter()
            return make_record(username, status, http_code, round(lat_ms, 1),
                               reason, proxy_val, token_id(token_item['value']),
                               attempts_made, compute_timing(ts))

        if status == 'token_dead':
            token_pool.report(token_item, 'dead')
            if proxy_item:
                proxy_pool.report(proxy_item, 'error')
        elif status == 'proxy_dead':
            token_pool.report(token_item, 'error')
            if proxy_item:
                proxy_pool.report(proxy_item, 'dead')
        elif status == 'tls_error':
            token_pool.report(token_item, 'error')
            if proxy_item:
                proxy_pool.report(proxy_item, 'dead')
        elif status == 'rate_limited':
            token_pool.report(token_item, 'rate_limited', ra)
            if proxy_item:
                proxy_pool.report(proxy_item, 'rate_limited', ra)
        elif status in ('forbidden', 'not_found'):
            token_pool.report(token_item, 'forbidden')
            if proxy_item:
                proxy_pool.report(proxy_item, 'error')
        else:
            token_pool.report(token_item, 'error')
            if proxy_item:
                proxy_pool.report(proxy_item, 'error')

        last = make_record(username, status, http_code, round(lat_ms, 1),
                           reason, proxy_val, token_id(token_item['value']),
                           attempts_made, compute_timing(ts))

    if last is None:
        ts['done'] = time.perf_counter()
        last = make_record(username, 'error', 0, 0.0, 'no_attempt_made',
                           None, None, attempts_made, compute_timing(ts))
    else:
        ts['done'] = time.perf_counter()
        if 'timing' in last and isinstance(last['timing'], dict):
            last['timing'].update({
                'total_ms': round((ts['done'] - ts['enqueue']) * 1000, 1),
            })
        else:
            last['timing'] = compute_timing(ts)
    return last


# ======================== SCRAPER / VALIDATOR ========================

def scrape_proxies(log_cb=None):
    found = set()
    lock = threading.Lock()

    def fetch(url):
        try:
            r = requests.get(url, timeout=15, verify=VERIFY_TLS,
                             headers={"User-Agent": random.choice(USER_AGENTS)})
            if r.status_code != 200:
                return
            local = set()
            for ln in r.text.splitlines():
                ln = ln.strip()
                if ':' in ln and 5 < len(ln) < 30:
                    local.add(ln)
            with lock:
                found.update(local)
        except Exception as e:
            if log_cb:
                log_cb(f"Failed {url[:60]}: {str(e)[:50]}")

    with ThreadPoolExecutor(max_workers=8) as ex:
        list(ex.map(fetch, PROXY_SOURCES))
    return found


def validate_proxy(proxy_url):
    try:
        r = requests.get(
            VALIDATE_URL, proxies=proxies_dict(proxy_url),
            timeout=VALIDATE_TIMEOUT, verify=VERIFY_TLS,
            headers={"User-Agent": random.choice(USER_AGENTS)},
        )
        return r.status_code == 200
    except Exception:
        return False


def validate_proxies(proxies, log_cb=None):
    if not proxies:
        return []
    alive = []
    lock = threading.Lock()

    def check(p):
        if validate_proxy(p):
            with lock:
                alive.append(p)

    with ThreadPoolExecutor(max_workers=VALIDATE_WORKERS) as ex:
        list(ex.map(check, proxies))
    return alive


# ======================== RESUME ========================

def load_done_usernames(path):
    done = set()
    broken = 0
    if not os.path.exists(path):
        return done, broken
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except Exception:
                broken += 1
                continue
            u = rec.get('username')
            s = rec.get('status')
            if u and s in TERMINAL_STATUSES:
                done.add(u)
    return done, broken


# ======================== PROXY MENU ========================

def acquire_proxy_list():
    print("")
    print("Proxy source:")
    print("  1) Scrape + validate")
    print("  2) File + validate")
    print("  3) Scrape + file + validate")
    print("  4) Direct (no proxy)")
    print("  5) File, skip validation")
    choice = input("Choice [1]: ").strip() or "1"

    proxies = set()
    log = lambda m: print(f"[SCRAPE] {m}")

    if choice in ('1', '3'):
        scraped = scrape_proxies(log_cb=log)
        print(f"[SCRAPE] Unique: {len(scraped)}")
        proxies.update(scraped)

    if choice in ('2', '3', '5'):
        path = input("Proxies file [proxies.txt]: ").strip() or "proxies.txt"
        if os.path.exists(path):
            normalized = [normalize_proxy(p) for p in load_lines(path)]
            normalized = [p for p in normalized if p]
            print(f"[FILE] Loaded: {len(normalized)}")
            proxies.update(normalized)
        else:
            print(f"[FILE] Not found: {path}")

    if choice == '4':
        return []
    proxies = list(proxies)
    print(f"[POOL] Unique: {len(proxies)}")

    if choice == '5':
        return proxies
    if not proxies:
        return []

    alive = validate_proxies(proxies, log_cb=log)
    print(f"[POOL] Alive: {len(alive)}/{len(proxies)}")
    if alive:
        with open('alive_proxies.txt', 'w', encoding='utf-8') as f:
            f.write('\n'.join(alive))
    return alive


# ======================== RUN ENGINE ========================

def run_checks(usernames, tokens, proxies, concurrency, max_runtime=None,
               verbose=False, tag=''):
    token_pool = Pool(tokens, 'token')
    proxy_pool = Pool(proxies, 'proxy')
    metrics = Metrics()
    limiter = ServiceLimiter()

    writer = JSONLWriter(RESULTS_FILE)

    available = []
    counter = [0]
    stats_lock = threading.Lock()
    total = len(usernames)
    start = time.time()
    stop_stats = threading.Event()
    stop_all = threading.Event()

    print("")
    print(f"[RUN{tag}] usernames={total} tokens={token_pool.size()} "
          f"proxies={proxy_pool.size()} concurrency={concurrency} "
          f"tls_verify={VERIFY_TLS}")

    def stats_loop():
        while not stop_stats.wait(STATS_INTERVAL):
            ts = token_pool.stats()
            ps = proxy_pool.stats()
            svc = limiter.snapshot()
            with stats_lock:
                d = counter[0]
                av = len(available)
            pct = (d / total) * 100 if total else 0
            rps = d / max(0.001, time.time() - start)
            rss = rss_mb()
            if rss > RSS_WARN_MB:
                print(f"[MEM] RSS={rss:.0f}MB > {RSS_WARN_MB}MB")
            print(f"[STATS{tag}] {d}/{total} {pct:.1f}% rps={rps:.2f} "
                  f"rss={rss:.0f}MB "
                  f"tok[a={ts['alive']} c={ts['cooldown']} d={ts['dead']}] "
                  f"prx[a={ps['alive']} c={ps['cooldown']} d={ps['dead']}] "
                  f"paused={svc['currently_paused']} avail={av}")

    stats_thread = threading.Thread(target=stats_loop, daemon=True)
    stats_thread.start()

    def process(user, t_enqueue):
        try:
            rec = check_with_retry(user, token_pool, proxy_pool, limiter, t_enqueue)
        except Exception as e:
            rec = make_record(user, 'internal_error', 0, 0.0,
                              f'worker_exception:{type(e).__name__}:{str(e)[:60]}',
                              None, None, 0)

        metrics.record(
            rec['status'], rec['http'], rec['latency_ms'],
            rec['reason'], rec['proxy'] is not None,
            stage=rec.get('timing')
        )
        writer.write(rec)

        with stats_lock:
            counter[0] += 1
            idx = counter[0]
            if rec['status'] == 'available':
                available.append(rec['username'])

        if verbose or rec['status'] in ('available', 'error', 'internal_error'):
            tag_s = ''
            if rec['reason'] and rec['status'] not in ('available', 'taken'):
                tag_s = f" | {rec['reason']}"
            print(f"[{rec['status']}] {rec['username']} | #{idx:05d} | "
                  f"http={rec['http']} | {rec['latency_ms']:.0f}ms | "
                  f"att={rec['attempts']}{tag_s}")

    q = Queue(maxsize=max(4, concurrency * 4))
    SENTINEL = object()

    def producer():
        for u in usernames:
            if stop_all.is_set():
                break
            if max_runtime and (time.time() - start) > max_runtime:
                stop_all.set()
                break
            q.put((u, time.perf_counter()))
        for _ in range(concurrency):
            q.put(SENTINEL)

    def consumer():
        while True:
            try:
                item = q.get(timeout=1.0)
            except Empty:
                if stop_all.is_set():
                    return
                continue
            if item is SENTINEL:
                return
            user, t_enq = item
            process(user, t_enq)

    prod = threading.Thread(target=producer)
    prod.start()
    consumers = [threading.Thread(target=consumer) for _ in range(concurrency)]
    for c in consumers:
        c.start()
    prod.join()
    for c in consumers:
        c.join()

    stop_stats.set()
    time.sleep(0.05)
    writer.close()

    elapsed = time.time() - start
    ts = token_pool.stats()
    ps = proxy_pool.stats()
    m = metrics.summary()
    svc = limiter.snapshot()
    rps = counter[0] / max(0.001, elapsed)

    result = {
        'elapsed_s': round(elapsed, 1),
        'processed': counter[0],
        'total': total,
        'rps': round(rps, 2),
        'available_session': len(available),
        'tokens': ts,
        'proxies': ps,
        'service': svc,
        'metrics': m,
        'rss_mb': round(rss_mb(), 1),
        'concurrency': concurrency,
        'tls_verify': VERIFY_TLS,
    }

    print("")
    print(f"[DONE{tag}] {elapsed:.1f}s processed={counter[0]}/{total} rps={rps:.2f}")
    print(f"[DONE{tag}] tokens={ts} proxies={ps} svc={svc}")
    print(f"[DONE{tag}] latency avg={m.get('avg_ms')} p50={m.get('p50_ms')} "
          f"p95={m.get('p95_ms')} p99={m.get('p99_ms')} max={m.get('max_ms')}")
    print(f"[DONE{tag}] stage_avg_ms={m.get('stage_avg_ms')}")
    print(f"[DONE{tag}] by_status={m.get('by_status')}")
    print(f"[DONE{tag}] by_reason={m.get('by_reason')}")

    SESSION_POOL.close_all()
    return result, available


# ======================== MAIN ========================

def main():
    print("Mode:")
    print("  1) check")
    print("  2) benchmark (same list, two configs)")
    print("")
    mode = input("Choice [1]: ").strip() or "1"

    print("Generation mode:")
    print("1) 4l   2) 4 alnum   3) 4 digits")
    print("4) 3l   5) 3 alnum   6) 3 digits")
    print("7) 2l   8) 2 alnum   9) 2 digits")
    print("10) 3 alnum + _   11) 3 alnum + .   12) 3 alnum + ._")
    print("0) usernames.txt")
    print("")

    choice = input("Choice: ").strip()
    length_map = {'1':4,'2':4,'3':4,'4':3,'5':3,'6':3,'7':2,'8':2,'9':2,
                  '10':3,'11':3,'12':3}
    type_map = {'1':'l','2':'c','3':'n','4':'l','5':'c','6':'n',
                '7':'l','8':'c','9':'n','10':'cu','11':'cd','12':'cud'}
    charsets = {
        'l':   string.ascii_lowercase,
        'n':   string.digits,
        'c':   string.ascii_lowercase + string.digits,
        'cu':  string.ascii_lowercase + string.digits + '_',
        'cd':  string.ascii_lowercase + string.digits + '.',
        'cud': string.ascii_lowercase + string.digits + '._',
    }

    if choice == '0':
        if not os.path.exists('usernames.txt'):
            print("usernames.txt not found")
            return
        usernames_iter = iter([u.lower() for u in load_lines('usernames.txt')])
        total_expected = None
    elif choice in length_map:
        m = input("Mode [random/sequential] (random): ").strip().lower()
        if m not in ('random', 'sequential'):
            m = 'random'
        lim = input(f"Limit [{MAX_GENERATE}]: ").strip()
        lim = int(lim) if lim.isdigit() else MAX_GENERATE
        usernames_iter = generate_usernames(
            length_map[choice], charsets[type_map[choice]], m, lim)
        total_expected = lim
    else:
        print("Invalid choice")
        return

    done, broken = load_done_usernames(RESULTS_FILE)
    if broken:
        print(f"[RESUME] Broken JSONL lines ignored: {broken}")
    if done:
        print(f"[RESUME] Terminal results loaded: {len(done)}")

    tokens_path = input("Tokens file [tokens.txt]: ").strip() or 'tokens.txt'
    if not os.path.exists(tokens_path):
        print(f"Not found: {tokens_path}")
        return
    tokens = [normalize_token(t) for t in load_lines(tokens_path)]
    tokens = [t for t in tokens if t]
    if not tokens:
        print("No tokens")
        return
    print(f"Tokens: {len(tokens)}")

    proxy_list = acquire_proxy_list()

    def fresh_iter():
        for u in usernames_iter:
            if u not in done:
                yield u
            else:
                pass

    if mode == '2':
        # Benchmark: capture a fixed subset, run with two configs
        subset_n = int(input("Benchmark subset size [200]: ").strip() or "200")
        subset = []
        for u in fresh_iter():
            subset.append(u)
            if len(subset) >= subset_n:
                break
        print(f"[BENCH] Subset: {len(subset)}")
        if not subset:
            return

        configs = []
        c1 = int(input(f"Config 1 concurrency [{CONCURRENCY}]: ").strip() or CONCURRENCY)
        c2 = int(input(f"Config 2 concurrency [{CONCURRENCY*2}]: ").strip() or CONCURRENCY*2)
        configs = [('c=%d' % c1, c1), ('c=%d' % c2, c2)]

        results = {}
        for tag, conc in configs:
            try:
                os.remove(RESULTS_FILE)
            except FileNotFoundError:
                pass
            r, _ = run_checks(subset, tokens, proxy_list, conc, tag=f':{tag}')
            results[tag] = r

        best = max(results.items(), key=lambda kv: kv[1]['rps'])
        print("")
        print("[BENCH] Summary:")
        for tag, r in results.items():
            m = r['metrics']
            print(f"  {tag}: rps={r['rps']} elapsed={r['elapsed_s']}s "
                  f"p95={m.get('p95_ms')} p99={m.get('p99_ms')} "
                  f"available={r['available_session']} "
                  f"rss={r['rss_mb']}MB")
        print(f"[BENCH] Winner by rps: {best[0]}")
        with open(BENCH_FILE, 'w', encoding='utf-8') as f:
            json.dump(results, f, indent=2)
        print(f"[BENCH] Saved -> {BENCH_FILE}")
        return

    # Normal check mode
    result, available = run_checks(list(fresh_iter()), tokens, proxy_list, CONCURRENCY)

    with open('available.txt', 'w', encoding='utf-8') as f:
        if available:
            f.write('\n'.join(available))
    print(f"available.txt updated ({len(available)} this session)")

    with open('dead_tokens.txt', 'w', encoding='utf-8') as f:
        dl = Pool([], 'token').dead_list()  # placeholder, will be empty
    # real dead lists not exposed here; kept for parity with prior versions

    with open(STATE_FILE, 'w', encoding='utf-8') as f:
        json.dump(result, f, indent=2)

    print("")
    print("Note: 'available' = Discord reports username not taken.")
    print("      It does NOT mean the username was claimed.")


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        print("\nInterrupted")
        sys.exit(130)
