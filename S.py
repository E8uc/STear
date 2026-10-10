import os
import sys
import time
import json
import math
import random
import string
import hashlib
import threading
from collections import defaultdict, OrderedDict, deque
from queue import Queue, Empty
from concurrent.futures import ThreadPoolExecutor

import requests
import urllib3

VERIFY_TLS = True
if not VERIFY_TLS:
    urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

API = "https://discord.com/api/v10/unique-username/check-username"
VALIDATE_URL = "https://discord.com/api/v10/gateway"
TOKEN_INFO_URL = "https://discord.com/api/v10/users/@me"

# ======================== SAFE ROTATION CONFIG ========================

SAFE_MODE = True

SAFE_PROXY_MAX_PER_WINDOW = 12
SAFE_PROXY_WINDOW_S       = 60
SAFE_PROXY_MIN_GAP        = 1.5
SAFE_PROXY_REST_AFTER     = 3
SAFE_PROXY_REST_S         = 30
SAFE_PROXY_JITTER         = 0.25

SAFE_TOKEN_MAX_PER_WINDOW = 8
SAFE_TOKEN_WINDOW_S       = 60
SAFE_TOKEN_MIN_GAP        = 2.0
SAFE_TOKEN_REST_AFTER     = 3
SAFE_TOKEN_REST_S         = 45
SAFE_TOKEN_JITTER         = 0.35

GLOBAL_MAX_RPS            = 8

SOURCES_6YYN = [
    "https://raw.githubusercontent.com/6yyn/free-proxy-list/main/checked_proxies.txt",
    "https://raw.githubusercontent.com/6yyn/free-proxy-list/main/active_proxies.txt",
    "https://raw.githubusercontent.com/6yyn/free-proxy-list/main/all_proxies.txt",
    "https://raw.githubusercontent.com/6yyn/free-proxy-list/main/http.txt",
    "https://raw.githubusercontent.com/6yyn/free-proxy-list/main/https.txt",
]
SOURCES_BACKUP = [
    "https://api.proxyscrape.com/v2/?request=displayproxies&protocol=http&timeout=5000&country=all",
    "https://raw.githubusercontent.com/TheSpeedX/PROXY-List/master/http.txt",
    "https://raw.githubusercontent.com/ShiftyTR/Proxy-List/master/http.txt",
    "https://raw.githubusercontent.com/monosans/proxy-list/main/proxies/http.txt",
    "https://raw.githubusercontent.com/clarketm/proxy-list/master/proxy-list-raw.txt",
    "https://raw.githubusercontent.com/roosterkid/openproxylist/main/HTTPS_RAW.txt",
]
PROXY_SOURCES = SOURCES_6YYN + SOURCES_BACKUP

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
MAX_TOKEN_FAILS     = 4
MAX_FORBIDDEN       = 4
MAX_RETRIES         = 4
PROXY_COOLDOWN      = 60
TOKEN_COOLDOWN_MAX  = 60
SERVICE_PAUSE_MAX   = 120
STATS_INTERVAL      = 5
ACQUIRE_MAX_WAIT    = 10
VALIDATE_TIMEOUT    = 5
VALIDATE_WORKERS    = 200
VALIDATE_ROUNDS     = 2
VALIDATE_ROUND_GAP  = 1.5
VERIFY_TOKEN_WORKERS = 5
MAX_LATENCY_SAMPLES = 20000
MAX_SESSIONS        = 200
WRITE_BATCH         = 100
WRITE_INTERVAL      = 1.5
RSS_WARN_MB         = 500

HEALTH_CHECK_INTERVAL = 60
HEALTH_CHECK_BATCH    = 20
HEALTH_FAIL_THRESHOLD = 1
SCORE_WEIGHT_LATENCY  = 0.7
MIN_PROXY_LATENCY_MS  = 50
MAX_PROXY_LATENCY_MS  = 5000
PROXY_CACHE_FILE      = 'validated_proxies.json'
PROXY_CACHE_TTL       = 600

RESULTS_FILE = 'results.jsonl'
STATE_FILE   = 'state.json'
BENCH_FILE   = 'benchmark.json'

TERMINAL_STATUSES = {'available', 'taken', 'invalid_format'}
TOKEN_FAULT = {'token_dead'}
PROXY_FAULT = {'proxy_dead', 'dns_error', 'conn_refused',
               'conn_reset', 'tls_error'}
NEUTRAL = {'timeout', 'forbidden', 'not_found', 'unknown_response',
           'internal_error', 'error', 'invalid_format', 'rate_limited'}

_ZERO_WIDTH = '\u200b\u200c\u200d\ufeff\u2060\u00a0'
_QUOTES = ['"', "'", '\u201c', '\u201d', '\u2018', '\u2019',
           '\u00ab', '\u00bb', '\u300c', '\u300d', '\u300e', '\u300f']


def rss_mb():
    try:
        with open(f'/proc/{os.getpid()}/status') as f:
            for line in f:
                if line.startswith('VmRSS:'):
                    return int(line.split()[1]) / 1024.0
    except Exception:
        pass
    return 0.0


# ======================== AUTO-SCALE SAFE CONFIG ========================

def compute_safe_config(size, kind):
    """
    Auto-scales safety thresholds based on pool size.
    A small pool must NOT enter aggressive rest mode - it would starve.
    """
    if kind == 'token':
        if size <= 1:
            return {'max_per_window': None, 'window_s': 60,
                    'min_gap': 0.5, 'rest_after': None,
                    'rest_duration': 0.0, 'rest_jitter': 0.0}
        if size <= 3:
            return {'max_per_window': 30, 'window_s': 60,
                    'min_gap': 1.0, 'rest_after': 25,
                    'rest_duration': 20.0, 'rest_jitter': 0.3}
        if size <= 10:
            return {'max_per_window': 20, 'window_s': 60,
                    'min_gap': 1.5, 'rest_after': 10,
                    'rest_duration': 30.0, 'rest_jitter': 0.35}
        return {'max_per_window': SAFE_TOKEN_MAX_PER_WINDOW, 'window_s': SAFE_TOKEN_WINDOW_S,
                'min_gap': SAFE_TOKEN_MIN_GAP, 'rest_after': SAFE_TOKEN_REST_AFTER,
                'rest_duration': SAFE_TOKEN_REST_S, 'rest_jitter': SAFE_TOKEN_JITTER}
    else:
        if size <= 1:
            return {'max_per_window': None, 'window_s': 60,
                    'min_gap': 0.3, 'rest_after': None,
                    'rest_duration': 0.0, 'rest_jitter': 0.0}
        if size <= 5:
            return {'max_per_window': 40, 'window_s': 60,
                    'min_gap': 0.5, 'rest_after': 40,
                    'rest_duration': 15.0, 'rest_jitter': 0.25}
        if size <= 20:
            return {'max_per_window': 25, 'window_s': 60,
                    'min_gap': 0.8, 'rest_after': 20,
                    'rest_duration': 20.0, 'rest_jitter': 0.25}
        if size <= 100:
            return {'max_per_window': SAFE_PROXY_MAX_PER_WINDOW, 'window_s': SAFE_PROXY_WINDOW_S,
                    'min_gap': SAFE_PROXY_MIN_GAP, 'rest_after': SAFE_PROXY_REST_AFTER,
                    'rest_duration': SAFE_PROXY_REST_S, 'rest_jitter': SAFE_PROXY_JITTER}
        return {'max_per_window': SAFE_PROXY_MAX_PER_WINDOW, 'window_s': SAFE_PROXY_WINDOW_S,
                'min_gap': 1.0, 'rest_after': 5,
                'rest_duration': SAFE_PROXY_REST_S, 'rest_jitter': SAFE_PROXY_JITTER}


# ======================== GLOBAL RATE LIMITER ========================

class RateLimiter:
    def __init__(self, max_per_second):
        self.max = max(1, int(max_per_second))
        self.lock = threading.Lock()
        self.timestamps = deque()

    def wait(self):
        while True:
            wait = 0.0
            with self.lock:
                now = time.time()
                while self.timestamps and self.timestamps[0] < now - 1.0:
                    self.timestamps.popleft()
                if len(self.timestamps) < self.max:
                    self.timestamps.append(now)
                    return
                wait = self.timestamps[0] + 1.0 - now
            if wait > 0:
                time.sleep(min(wait, 0.5))


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
                    if isinstance(v, (int, float)):
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
            out = {
                'total_recorded': self.total_recorded,
                'sampled': n,
                'by_status': dict(self.by_status),
                'by_http': dict(self.by_http),
                'by_reason': dict(self.by_reason),
                'by_proxy_class': dict(self.by_proxy_class),
                'stage_avg_ms': {
                    k: round(self.stage_sums[k] / max(1, self.stage_count[k]), 2)
                    for k in self.stage_sums
                },
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
    def __init__(self, values, name,
                 max_per_window=None, window_s=60,
                 min_gap=0.0, rest_after=None, rest_duration=0.0,
                 rest_jitter=0.0):
        self.name = name
        self.lock = threading.Lock()
        self.items = [self._make(v) for v in values]
        self.idx = -1
        self.fail_limit = MAX_PROXY_FAILS if name == 'proxy' else MAX_TOKEN_FAILS
        self.lease_timeout = TIMEOUT + 5

        self.max_per_window = max_per_window
        self.window_s = max(1, window_s)
        self.min_gap = max(0.0, min_gap)
        self.rest_after = rest_after
        self.rest_duration = max(0.0, rest_duration)
        self.rest_jitter = max(0.0, min(1.0, rest_jitter))

        self._sort_by_score()

    @staticmethod
    def _make(value):
        return {
            'value': value, 'status': 'alive',
            'fails': 0, 'forbidden': 0, 'ok': 0,
            'cooldown_until': 0.0, 'reason': None,
            'cooldown_reason': None,
            'busy_until': 0.0,
            'in_use': 0,
            'latency_ms': 0.0,
            'score': 0.0,
            'last_used_at': 0.0,
            'request_times': [],
            'requests_since_rest': 0,
            'total_requests': 0,
        }

    def _sort_by_score(self):
        if self.name != 'proxy':
            return
        self.items.sort(key=lambda it: it['score'], reverse=True)

    def set_scores(self, score_map):
        with self.lock:
            for it in self.items:
                if it['value'] in score_map:
                    it['score'] = score_map[it['value']]
                    it['latency_ms'] = score_map.get(it['value'] + '__lat', 0.0)
            self._sort_by_score()

    def size(self):
        with self.lock:
            return len(self.items)

    def _refresh_cooldowns_locked(self, now):
        for it in self.items:
            if it['status'] == 'cooldown' and it['cooldown_until'] <= now:
                it['status'] = 'alive'
                it['fails'] = 0
                it['cooldown_reason'] = None

    def _prune_window_locked(self, it, now):
        cutoff = now - self.window_s
        if it['request_times'] and it['request_times'][0] < cutoff:
            it['request_times'] = [t for t in it['request_times'] if t >= cutoff]

    def _is_safe_locked(self, it, now):
        if it['status'] != 'alive':
            return False
        if it['busy_until'] > now:
            return False
        if self.min_gap > 0 and (now - it['last_used_at']) < self.min_gap:
            return False
        if self.max_per_window is not None:
            self._prune_window_locked(it, now)
            if len(it['request_times']) >= self.max_per_window:
                return False
        if self.rest_after is not None and it['requests_since_rest'] >= self.rest_after:
            return False
        return True

    def _trigger_rest_locked(self, it, now):
        base = self.rest_duration if self.rest_duration > 0 else PROXY_COOLDOWN
        jitter = 1.0 + random.uniform(-self.rest_jitter, self.rest_jitter)
        duration = max(1.0, base * jitter)
        it['status'] = 'cooldown'
        it['cooldown_until'] = now + duration
        it['cooldown_reason'] = 'rest'
        it['requests_since_rest'] = 0

    def next(self):
        with self.lock:
            if not self.items:
                return None
            now = time.time()
            self._refresh_cooldowns_locked(now)
            n = len(self.items)

            for _ in range(n):
                self.idx = (self.idx + 1) % n
                it = self.items[self.idx]
                if self._is_safe_locked(it, now):
                    self._lease_locked(it, now)
                    return it

            for it in self.items:
                if (it['status'] == 'alive' and self.rest_after is not None
                        and it['requests_since_rest'] >= self.rest_after):
                    self._trigger_rest_locked(it, now)

            for _ in range(n):
                self.idx = (self.idx + 1) % n
                it = self.items[self.idx]
                if self._is_safe_locked(it, now):
                    self._lease_locked(it, now)
                    return it

            return None

    def _lease_locked(self, it, now):
        it['busy_until'] = now + self.lease_timeout
        it['in_use'] += 1
        it['last_used_at'] = now
        it['requests_since_rest'] += 1
        it['total_requests'] += 1
        self._prune_window_locked(it, now)
        it['request_times'].append(now)

    def release(self, item):
        if item is None:
            return
        with self.lock:
            item['busy_until'] = 0.0
            if item['in_use'] > 0:
                item['in_use'] -= 1

    def has_cooldown(self):
        with self.lock:
            now = time.time()
            return any(it['status'] == 'cooldown' and it['cooldown_until'] > now
                       for it in self.items)

    def next_ready_delta(self):
        with self.lock:
            now = time.time()
            deltas = []
            for it in self.items:
                if it['status'] == 'cooldown':
                    if it['cooldown_until'] > now:
                        deltas.append(it['cooldown_until'] - now)
                    continue
                if it['status'] != 'alive':
                    continue
                if it['busy_until'] > now:
                    deltas.append(it['busy_until'] - now)
                if self.min_gap > 0 and it['last_used_at'] > 0:
                    gap_delta = (it['last_used_at'] + self.min_gap) - now
                    if gap_delta > 0:
                        deltas.append(gap_delta)
                if self.max_per_window is not None and it['request_times']:
                    self._prune_window_locked(it, now)
                    if len(it['request_times']) >= self.max_per_window:
                        oldest = it['request_times'][0]
                        window_delta = (oldest + self.window_s) - now
                        if window_delta > 0:
                            deltas.append(window_delta)
            if not deltas:
                return None
            return max(0.05, min(deltas))

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
                item['cooldown_reason'] = 'rate-limit'
                item['requests_since_rest'] = 0
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

    def alive_values(self):
        with self.lock:
            return [it['value'] for it in self.items if it['status'] == 'alive']

    def mark_health_fail(self, value):
        with self.lock:
            for it in self.items:
                if it['value'] == value and it['status'] == 'alive':
                    it['fails'] += HEALTH_FAIL_THRESHOLD
                    if it['fails'] >= self.fail_limit:
                        it['status'] = 'dead'
                        it['reason'] = 'health-check-fail'
                    return

    def stats(self):
        with self.lock:
            now = time.time()
            a = sum(1 for i in self.items if i['status'] == 'alive')
            d = sum(1 for i in self.items if i['status'] == 'dead')
            c = sum(1 for i in self.items if i['status'] == 'cooldown')
            r = sum(1 for i in self.items if i['status'] == 'cooldown'
                    and i['cooldown_reason'] == 'rest')
            rl = sum(1 for i in self.items if i['status'] == 'cooldown'
                     and i['cooldown_reason'] == 'rate-limit')
            busy = sum(1 for i in self.items if i['busy_until'] > now)
            total_req = sum(i['total_requests'] for i in self.items)
            return {'total': len(self.items), 'alive': a,
                    'dead': d, 'cooldown': c, 'busy': busy,
                    'resting': r, 'ratelimited': rl,
                    'total_requests': total_req}

    def dead_list(self):
        with self.lock:
            return [i['value'] for i in self.items if i['status'] == 'dead']


# ======================== SESSION POOL ========================

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
        need = False
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


# ======================== TOKEN HANDLING ========================

def token_id(token):
    return hashlib.sha256(token.encode()).hexdigest()[:16]


def load_lines(path):
    with open(path, 'r', encoding='utf-8-sig', errors='ignore') as f:
        return [ln.rstrip('\r\n') for ln in f if ln.strip()]


def normalize_token(line):
    if not line:
        return ''
    t = line
    for z in _ZERO_WIDTH:
        t = t.replace(z, '')
    t = t.strip()
    for _ in range(3):
        changed = False
        for q in _QUOTES:
            if t.startswith(q) and t.endswith(q) and len(t) > 2:
                t = t[1:-1].strip()
                changed = True
                break
        if not changed:
            break
    for prefix in ('Bearer ', 'bearer ', 'Bearer\t'):
        if t.startswith(prefix):
            t = t[len(prefix):].strip()
            break
    t = ''.join(t.split())
    return t


def classify_token(token):
    if not token:
        return 'empty'
    if token.startswith('Bot '):
        return 'bot'
    parts = token.split('.')
    if len(parts) >= 3 and len(parts[0]) >= 20:
        return 'user'
    return 'unknown'


def is_plausible_token(token):
    if not token or len(token) < 50 or len(token) > 200:
        return False
    if token.count('.') < 2:
        return False
    if any(c.isspace() for c in token):
        return False
    body = token[4:] if token.startswith('Bot ') else token
    allowed = set(
        'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_-.'
    )
    return all(c in allowed for c in body)


def verify_token_online(token, proxy_url=None, timeout=8):
    variants = [token] if token.startswith('Bot ') else [token, 'Bot ' + token]
    for attempt in variants:
        headers = {
            'Authorization': attempt,
            'User-Agent': random.choice(USER_AGENTS),
            'Accept': '*/*',
            'Accept-Language': 'en-US,en;q=0.9',
        }
        try:
            r = requests.get(
                TOKEN_INFO_URL, headers=headers,
                proxies=proxies_dict(proxy_url),
                timeout=timeout, verify=VERIFY_TLS,
            )
        except Exception as e:
            return 'network', 0, str(e)[:80], token
        code = r.status_code
        if code == 200:
            try:
                data = r.json()
                name = data.get('username') or data.get('id') or '?'
                kind = 'bot' if attempt.startswith('Bot ') else 'user'
                return 'ok', code, f"{kind}:{name}", attempt
            except Exception:
                return 'ok', code, 'ok', attempt
        if code == 401:
            continue
        if code == 429:
            return 'ratelimited', code, 'rate limited', attempt
        return 'unknown', code, f'http_{code}', attempt
    return 'invalid', 401, 'unauthorized (both variants)', token


def verify_tokens(tokens, proxy_url=None, log_cb=None):
    log = log_cb or (lambda m: None)
    valid = []
    report = []
    lock = threading.Lock()

    def check(idx_token):
        i, tok = idx_token
        kind, code, detail, working = verify_token_online(tok, proxy_url)
        with lock:
            report.append((i, kind, code, detail, tok[:12] + '...', working))
            if kind == 'ok':
                valid.append(working)

    items = list(enumerate(tokens))
    workers = min(VERIFY_TOKEN_WORKERS, max(1, len(items)))
    with ThreadPoolExecutor(max_workers=workers) as ex:
        list(ex.map(check, items))
    return valid, report


# ======================== GENERAL HELPERS ========================

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
        'Accept-Encoding': 'gzip, deflate, br',
        'Origin': 'https://discord.com',
        'Referer': 'https://discord.com/channels/@me',
        'Sec-Fetch-Dest': 'empty',
        'Sec-Fetch-Mode': 'cors',
        'Sec-Fetch-Site': 'same-origin',
        'X-Discord-Locale': 'en-US',
        'X-Discord-Timezone': 'UTC',
        'X-Debug-Options': 'bugReporterEnabled',
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
        body_snippet = ''
        try:
            body_snippet = r.text[:120].replace('\n', ' ')
        except Exception:
            pass
        return ('token_dead', 0.0, code,
                f'unauthorized body={body_snippet!r}', timing)
    if code == 403:
        body_snippet = ''
        try:
            body_snippet = r.text[:120].replace('\n', ' ')
        except Exception:
            pass
        return ('forbidden', 0.0, code,
                f'forbidden body={body_snippet!r}', timing)
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
        delta = pool.next_ready_delta()
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


def check_with_retry(username, token_pool, proxy_pool, limiter, t_enqueue,
                     rate_limiter):
    ts = {'enqueue': t_enqueue}
    ts['pickup'] = time.perf_counter()

    if not is_valid_username(username):
        ts['done'] = time.perf_counter()
        return make_record(username, 'invalid_format', 0, 0.0,
                           'precheck_local', None, None, 0,
                           compute_timing(ts))

    use_proxy = proxy_pool.size() > 0
    used_tokens = set()
    used_proxies = set()
    last = None
    attempts_made = 0
    last_reason = 'no_attempt'

    token_wait = max(ACQUIRE_MAX_WAIT, min(120, token_pool.lease_timeout * 2))
    proxy_wait = max(ACQUIRE_MAX_WAIT, min(120, proxy_pool.lease_timeout * 2))

    for _ in range(MAX_RETRIES):
        limiter.wait_if_paused()

        token_item = acquire(token_pool, token_wait)
        ts['token_ok'] = time.perf_counter()

        if token_item is None:
            stats = token_pool.stats()
            if stats['total'] == 0:
                last_reason = 'no_tokens_in_pool'
            elif stats['resting'] + stats['busy'] >= stats['total']:
                last_reason = 'all_tokens_resting'
            elif stats['dead'] >= stats['total']:
                last_reason = 'all_tokens_dead'
            else:
                last_reason = 'token_wait_timeout'
            break
        if token_item['value'] in used_tokens:
            token_pool.release(token_item)
            last_reason = 'tokens_exhausted'
            break
        used_tokens.add(token_item['value'])

        proxy_item = None
        if use_proxy:
            proxy_item = acquire(proxy_pool, proxy_wait)
            ts['proxy_ok'] = time.perf_counter()
            if proxy_item is None:
                stats = proxy_pool.stats()
                if stats['total'] == 0:
                    last_reason = 'no_proxies_in_pool'
                elif stats['resting'] + stats['busy'] >= stats['total']:
                    last_reason = 'all_proxies_resting'
                else:
                    last_reason = 'proxy_wait_timeout'
                token_pool.release(token_item)
                break
            if proxy_item['value'] in used_proxies:
                token_pool.release(token_item)
                proxy_pool.release(proxy_item)
                last_reason = 'proxies_exhausted'
                break
            used_proxies.add(proxy_item['value'])
        else:
            ts['proxy_ok'] = ts.get('token_ok', time.perf_counter())

        proxy_val = proxy_item['value'] if proxy_item else None
        attempts_made += 1

        rate_limiter.wait()

        try:
            status, ra, http_code, reason, timing = check_username(
                username, token_item['value'], proxy_val, limiter, ts
            )
        except Exception as e:
            token_pool.release(token_item)
            if proxy_item:
                proxy_pool.release(proxy_item)
            ts['done'] = time.perf_counter()
            return make_record(
                username, 'internal_error', 0, 0.0,
                f'check_exception:{type(e).__name__}:{str(e)[:60]}',
                proxy_val, token_id(token_item['value']),
                attempts_made, compute_timing(ts)
            )
        finally:
            token_pool.release(token_item)
            if proxy_item:
                proxy_pool.release(proxy_item)

        lat_ms = (timing['http_end'] - timing['http_start']) * 1000

        if status in TERMINAL_STATUSES:
            token_pool.report(token_item, status)
            if proxy_item:
                proxy_pool.report(proxy_item, status)
            ts['done'] = time.perf_counter()
            return make_record(
                username, status, http_code, round(lat_ms, 1),
                reason, proxy_val, token_id(token_item['value']),
                attempts_made, compute_timing(ts)
            )

        if status == 'unknown_response':
            ts['done'] = time.perf_counter()
            return make_record(
                username, status, http_code, round(lat_ms, 1),
                reason, proxy_val, token_id(token_item['value']),
                attempts_made, compute_timing(ts)
            )

        if status in TOKEN_FAULT:
            token_pool.report(token_item, 'dead')
            if proxy_item:
                proxy_pool.report(proxy_item, 'available')
        elif status in PROXY_FAULT:
            if proxy_item:
                proxy_pool.report(proxy_item, 'dead')
        elif status == 'rate_limited':
            token_pool.report(token_item, 'rate_limited', ra)
            if proxy_item:
                proxy_pool.report(proxy_item, 'rate_limited', ra)
        else:
            pass

        last = make_record(
            username, status, http_code, round(lat_ms, 1),
            reason, proxy_val, token_id(token_item['value']),
            attempts_made, compute_timing(ts)
        )
        last_reason = reason or status

    ts['done'] = time.perf_counter()
    if last is not None:
        if isinstance(last.get('timing'), dict):
            last['timing']['total_ms'] = round(
                (ts['done'] - ts['enqueue']) * 1000, 1)
        return last
    return make_record(
        username, 'error', 0, 0.0, last_reason,
        None, None, attempts_made, compute_timing(ts)
    )


# ======================== SCRAPER ========================

def scrape_proxies(log_cb=None):
    found = set()
    lock = threading.Lock()
    log = log_cb or (lambda m: None)

    def fetch(url):
        short = url.split('/')[-1] or url[:40]
        try:
            r = requests.get(url, timeout=15, verify=VERIFY_TLS,
                             headers={"User-Agent": random.choice(USER_AGENTS)})
            if r.status_code != 200:
                log(f"  [{short}] HTTP {r.status_code}")
                return
            text = r.text.replace('\r', ' ').replace('\n', ' ')
            local = set()
            for token in text.split():
                token = token.strip()
                if ':' in token and 5 < len(token) < 40:
                    local.add(token)
            with lock:
                found.update(local)
            log(f"  [{short}] +{len(local)}")
        except Exception as e:
            log(f"  [{short}] err: {str(e)[:50]}")

    with ThreadPoolExecutor(max_workers=10) as ex:
        list(ex.map(fetch, PROXY_SOURCES))

    if log_cb:
        log_cb(f"Scraped total unique: {len(found)}")
    return found


# ======================== VALIDATOR ========================

def validate_proxy_once(proxy_url):
    t0 = time.perf_counter()
    try:
        r = requests.get(
            VALIDATE_URL, proxies=proxies_dict(proxy_url),
            timeout=VALIDATE_TIMEOUT, verify=VERIFY_TLS,
            headers={"User-Agent": random.choice(USER_AGENTS)},
        )
        lat = (time.perf_counter() - t0) * 1000
        if r.status_code == 200:
            return True, lat
        return False, lat
    except Exception:
        return False, 0.0


def validate_proxies(proxies, log_cb=None, rounds=VALIDATE_ROUNDS):
    if not proxies:
        return []
    log = log_cb or (lambda m: None)
    survivors = list(proxies)
    latencies = {}

    for round_num in range(1, rounds + 1):
        log(f"[VALIDATE] Round {round_num}/{rounds} on {len(survivors)} proxies")
        alive = []
        lock = threading.Lock()
        done = [0]
        total = len(survivors)

        def check(p):
            ok, lat = validate_proxy_once(p)
            with lock:
                done[0] += 1
                if ok:
                    alive.append((p, lat))
                    latencies[p] = lat
                n = done[0]
            if n % 500 == 0:
                log(f"[VALIDATE] {n}/{total} passed={len(alive)}")

        with ThreadPoolExecutor(max_workers=VALIDATE_WORKERS) as ex:
            list(ex.map(check, survivors))

        log(f"[VALIDATE] Round {round_num} result: {len(alive)}/{total} alive")
        if not alive:
            return []
        survivors = [p for p, _ in alive]
        if round_num < rounds:
            time.sleep(VALIDATE_ROUND_GAP)

    scored = []
    for p in survivors:
        lat = latencies.get(p, 9999)
        if lat <= 0:
            lat = 9999
        lat_norm = 1.0 - min(1.0, max(0.0,
            (lat - MIN_PROXY_LATENCY_MS) /
            (MAX_PROXY_LATENCY_MS - MIN_PROXY_LATENCY_MS)
        ))
        score = SCORE_WEIGHT_LATENCY * lat_norm
        scored.append((p, lat, score))

    scored.sort(key=lambda x: x[2], reverse=True)
    log(f"[VALIDATE] Final survivors: {len(scored)}")
    return scored


# ======================== PROXY CACHE ========================

def load_proxy_cache():
    if not os.path.exists(PROXY_CACHE_FILE):
        return None
    try:
        with open(PROXY_CACHE_FILE, 'r', encoding='utf-8') as f:
            cache = json.load(f)
        if time.time() - cache.get('ts', 0) > PROXY_CACHE_TTL:
            return None
        entries = cache.get('entries', [])
        return entries if entries else None
    except Exception:
        return None


def save_proxy_cache(scored):
    try:
        with open(PROXY_CACHE_FILE, 'w', encoding='utf-8') as f:
            json.dump({
                'ts': time.time(),
                'entries': [
                    {'url': p, 'lat': lat, 'score': score}
                    for p, lat, score in scored
                ],
            }, f)
    except Exception:
        pass


# ======================== HEALTH CHECK ========================

class ProxyHealthChecker:
    def __init__(self, pool, interval=HEALTH_CHECK_INTERVAL,
                 batch=HEALTH_CHECK_BATCH):
        self.pool = pool
        self.interval = interval
        self.batch = batch
        self.stop = threading.Event()
        self.thread = None
        self.stats = {'checks': 0, 'killed': 0}

    def start(self):
        self.thread = threading.Thread(target=self._loop, daemon=True)
        self.thread.start()

    def stop_checker(self):
        self.stop.set()

    def _loop(self):
        while not self.stop.wait(self.interval):
            try:
                self._sweep()
            except Exception:
                pass

    def _sweep(self):
        alive = self.pool.alive_values()
        if not alive:
            return
        sample = random.sample(alive, min(self.batch, len(alive)))
        dead_in_sweep = []

        def check(p):
            ok, _ = validate_proxy_once(p)
            if not ok:
                dead_in_sweep.append(p)

        with ThreadPoolExecutor(max_workers=min(10, len(sample))) as ex:
            list(ex.map(check, sample))
        for p in dead_in_sweep:
            self.pool.mark_health_fail(p)
        self.stats['checks'] += len(sample)
        self.stats['killed'] += len(dead_in_sweep)


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
    print("  1) 6yyn + backups + multi-round validate (recommended)")
    print("  2) File + multi-round validate")
    print("  3) 6yyn + file + multi-round validate")
    print("  4) Direct (no proxy)")
    print("  5) File, skip validation")
    print("  6) Use cached validated list (if fresh)")
    choice = input("Choice [1]: ").strip() or "1"

    log = lambda m: print(f"[PROXY] {m}")

    if choice == '6':
        cached = load_proxy_cache()
        if cached:
            print(f"[PROXY] Loaded {len(cached)} proxies from cache")
            return [(e['url'], e['lat'], e['score']) for e in cached]
        print("[PROXY] Cache empty or stale, falling back")
        choice = '1'
    if choice == '4':
        return []

    proxies = set()
    if choice in ('1', '3'):
        print("")
        print("Scraping sources (6yyn priority)...")
        scraped = scrape_proxies(log_cb=log)
        print(f"[PROXY] Total scraped: {len(scraped)}")
        proxies.update(scraped)

    if choice in ('2', '3', '5'):
        path = input("Proxies file [proxies.txt]: ").strip() or "proxies.txt"
        if os.path.exists(path):
            normalized = [normalize_proxy(p) for p in load_lines(path)]
            normalized = [p for p in normalized if p]
            print(f"[PROXY] Loaded from file: {len(normalized)}")
            proxies.update(normalized)
        else:
            print(f"[PROXY] Not found: {path}")

    proxies = list(proxies)
    print(f"[PROXY] Unique: {len(proxies)}")

    if choice == '5':
        return [(p, 0.0, 0.0) for p in proxies]
    if not proxies:
        return []

    print("")
    print("Starting multi-round validation...")
    scored = validate_proxies(proxies, log_cb=log)
    if not scored:
        print("[PROXY] No survivors - falling back to direct")
        return []

    print(f"[PROXY] Using {len(scored)} validated proxies")
    for p, lat, sc in scored[:5]:
        print(f"        {p}  lat={lat:.0f}ms  score={sc:.3f}")

    save_proxy_cache(scored)
    with open('alive_proxies.txt', 'w', encoding='utf-8') as f:
        f.write('\n'.join(p for p, _, _ in scored))
    return scored


# ======================== TOKEN MENU ========================

def acquire_token_list(proxy_scored):
    tokens_path = input("Tokens file [tokens.txt]: ").strip() or 'tokens.txt'
    if not os.path.exists(tokens_path):
        print(f"[TOKENS] Not found: {tokens_path}")
        return []

    raw = load_lines(tokens_path)
    print(f"[TOKENS] Raw lines read: {len(raw)}")

    normalized = [normalize_token(t) for t in raw]
    empties = sum(1 for t in normalized if not t)
    normalized = [t for t in normalized if t]

    plausible = [t for t in normalized if is_plausible_token(t)]
    rejected = [t for t in normalized if not is_plausible_token(t)]

    print(f"[TOKENS] After normalize: {len(normalized)} (empty: {empties})")
    print(f"[TOKENS] Plausible: {len(plausible)} | Rejected: {len(rejected)}")
    if rejected:
        print("[TOKENS] Rejected samples:")
        for t in rejected[:5]:
            print(f"          len={len(t)} preview={t[:25]!r}")

    if not plausible:
        return []

    kinds = defaultdict(int)
    for t in plausible:
        kinds[classify_token(t)] += 1
    print(f"[TOKENS] Types: {dict(kinds)}")

    verify = input("Verify tokens online before run? [Y/n]: ").strip().lower()
    if verify in ('n', 'no'):
        return plausible

    verify_proxy = proxy_scored[0][0] if proxy_scored else None
    if verify_proxy:
        print(f"[TOKENS] Verifying via proxy: {verify_proxy}")
    else:
        print("[TOKENS] Verifying directly (no proxy)")

    print("[TOKENS] Verifying (1 request per token)...")
    valid, report = verify_tokens(plausible, proxy_url=verify_proxy)

    ok_count = sum(1 for r in report if r[1] == 'ok')
    invalid = sum(1 for r in report if r[1] == 'invalid')
    network = sum(1 for r in report if r[1] == 'network')
    rl = sum(1 for r in report if r[1] == 'ratelimited')
    unknown = sum(1 for r in report if r[1] == 'unknown')

    print(f"[TOKENS] Valid: {ok_count} | Invalid: {invalid} | "
          f"Network: {network} | RateLimited: {rl} | Unknown: {unknown}")

    if invalid or unknown:
        print("[TOKENS] Problem tokens:")
        for i, kind, code, detail, preview, _ in sorted(report):
            if kind in ('invalid', 'unknown'):
                print(f"          #{i:03d} {preview} -> {kind} "
                      f"(http={code}) {detail[:80]}")

    if not valid:
        return []

    seen = set()
    final = []
    for t in valid:
        if t not in seen:
            seen.add(t)
            final.append(t)
    print(f"[TOKENS] Final usable: {len(final)}")
    return final


# ======================== RUN ENGINE ========================

def run_checks(usernames, tokens, proxy_scored, concurrency, max_runtime=None,
               verbose=False, tag='', enable_health_check=True):
    no_safe = {'max_per_window': None, 'window_s': 60, 'min_gap': 0.0,
               'rest_after': None, 'rest_duration': 0.0, 'rest_jitter': 0.0}

    token_cfg = compute_safe_config(len(tokens), 'token') if SAFE_MODE else dict(no_safe)
    token_pool = Pool(tokens, 'token', **token_cfg)

    proxy_urls = [p for p, _, _ in proxy_scored] if proxy_scored else []
    proxy_cfg = compute_safe_config(len(proxy_urls), 'proxy') if SAFE_MODE else dict(no_safe)
    proxy_pool = Pool(proxy_urls, 'proxy', **proxy_cfg)

    if proxy_scored:
        score_map = {}
        for p, lat, sc in proxy_scored:
            score_map[p] = sc
            score_map[p + '__lat'] = lat
        proxy_pool.set_scores(score_map)

    metrics = Metrics()
    limiter = ServiceLimiter()
    rate_limiter = RateLimiter(GLOBAL_MAX_RPS)
    writer = JSONLWriter(RESULTS_FILE)

    health = None
    if enable_health_check and proxy_pool.size() > 0:
        health = ProxyHealthChecker(proxy_pool)
        health.start()

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
          f"safe_mode={SAFE_MODE} global_rps={GLOBAL_MAX_RPS}")
    print(f"[RUN{tag}] token_cfg={token_cfg}")
    print(f"[RUN{tag}] proxy_cfg={proxy_cfg}")

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
                  f"tok[a={ts['alive']} r={ts['resting']} rl={ts['ratelimited']} b={ts['busy']} d={ts['dead']}] "
                  f"prx[a={ps['alive']} r={ps['resting']} rl={ps['ratelimited']} b={ps['busy']} d={ps['dead']}] "
                  f"paused={svc['currently_paused']} avail={av}")

    stats_thread = threading.Thread(target=stats_loop, daemon=True)
    stats_thread.start()

    def process(user, t_enqueue):
        try:
            rec = check_with_retry(user, token_pool, proxy_pool, limiter,
                                   t_enqueue, rate_limiter)
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
    if health:
        health.stop_checker()
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
        'safe_mode': SAFE_MODE,
        'tls_verify': VERIFY_TLS,
        'token_cfg': token_cfg,
        'proxy_cfg': proxy_cfg,
    }
    if health:
        result['health_check'] = health.stats

    print("")
    print(f"[DONE{tag}] {elapsed:.1f}s processed={counter[0]}/{total} rps={rps:.2f}")
    print(f"[DONE{tag}] tokens={ts} proxies={ps}")
    print(f"[DONE{tag}] latency avg={m.get('avg_ms')} p50={m.get('p50_ms')} "
          f"p95={m.get('p95_ms')} p99={m.get('p99_ms')}")
    print(f"[DONE{tag}] by_status={m.get('by_status')}")
    if m.get('by_reason'):
        print(f"[DONE{tag}] by_reason={m.get('by_reason')}")

    return result, available, token_pool, proxy_pool


# ======================== MAIN ========================

def main():
    print("Mode:")
    print("  1) check")
    print("  2) benchmark (same list, two concurrency levels)")
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
        usernames_list = [u.lower() for u in load_lines('usernames.txt')]
    elif choice in length_map:
        m = input("Mode [random/sequential] (random): ").strip().lower()
        if m not in ('random', 'sequential'):
            m = 'random'
        lim = input(f"Limit [{MAX_GENERATE}]: ").strip()
        lim = int(lim) if lim.isdigit() else MAX_GENERATE
        usernames_list = list(generate_usernames(
            length_map[choice], charsets[type_map[choice]], m, lim))
    else:
        print("Invalid choice")
        return
    if not usernames_list:
        print("Empty list")
        return

    done, broken = load_done_usernames(RESULTS_FILE)
    if broken:
        print(f"[RESUME] Broken JSONL lines ignored: {broken}")
    if done:
        before = len(usernames_list)
        usernames_list = [u for u in usernames_list if u not in done]
        print(f"[RESUME] Skipping terminal results: {before - len(usernames_list)}")
        if not usernames_list:
            print("All usernames have terminal results.")
            return

    proxy_scored = acquire_proxy_list()
    tokens = acquire_token_list(proxy_scored)
    if not tokens:
        print("No usable tokens. Exiting.")
        return

    if mode == '2':
        subset_n = int(input("Benchmark subset size [200]: ").strip() or "200")
        subset = usernames_list[:subset_n]
        if not subset:
            return
        c1 = int(input(f"Config 1 concurrency [{CONCURRENCY}]: ").strip() or CONCURRENCY)
        c2 = int(input(f"Config 2 concurrency [{CONCURRENCY*2}]: ").strip() or CONCURRENCY*2)
        results = {}
        for tag, conc in [('c=%d' % c1, c1), ('c=%d' % c2, c2)]:
            try:
                os.remove(RESULTS_FILE)
            except FileNotFoundError:
                pass
            r, _, _, _ = run_checks(subset, tokens, proxy_scored, conc,
                                    tag=f':{tag}', enable_health_check=False)
            results[tag] = r
        best = max(results.items(), key=lambda kv: kv[1]['rps'])
        print("")
        print("[BENCH] Summary:")
        for tag, r in results.items():
            m = r['metrics']
            print(f"  {tag}: rps={r['rps']} elapsed={r['elapsed_s']}s "
                  f"p95={m.get('p95_ms')} p99={m.get('p99_ms')} "
                  f"available={r['available_session']}")
        print(f"[BENCH] Winner: {best[0]}")
        with open(BENCH_FILE, 'w', encoding='utf-8') as f:
            json.dump(results, f, indent=2)
        return

    suggested = min(max(1, len(tokens)) * 2, 20)
    conc_input = input(f"Concurrency [{suggested}]: ").strip()
    concurrency = int(conc_input) if conc_input.isdigit() else suggested

    result, available, token_pool, proxy_pool = run_checks(
        usernames_list, tokens, proxy_scored, concurrency)

    with open('available.txt', 'w', encoding='utf-8') as f:
        if available:
            f.write('\n'.join(available))
    print(f"available.txt updated ({len(available)} this session)")

    dead_tokens = token_pool.dead_list()
    with open('dead_tokens.txt', 'w', encoding='utf-8') as f:
        if dead_tokens:
            f.write('\n'.join(dead_tokens))
    if dead_tokens:
        print(f"Saved {len(dead_tokens)} dead tokens -> dead_tokens.txt")

    dead_proxies = proxy_pool.dead_list()
    with open('dead_proxies.txt', 'w', encoding='utf-8') as f:
        if dead_proxies:
            f.write('\n'.join(dead_proxies))
    if dead_proxies:
        print(f"Saved {len(dead_proxies)} dead proxies -> dead_proxies.txt")

    with open(STATE_FILE, 'w', encoding='utf-8') as f:
        json.dump(result, f, indent=2)

    SESSION_POOL.close_all()
    print("")
    print("Note: 'available' = Discord reports username not taken.")


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        print("\nInterrupted")
        sys.exit(130)
