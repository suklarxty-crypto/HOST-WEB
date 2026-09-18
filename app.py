import os
import re
import json
import time
import shutil
import zipfile
import hashlib
import random
import subprocess
import threading
import py_compile
import io
from datetime import datetime
from collections import defaultdict, deque

from flask import Flask, render_template, render_template_string, request, redirect, url_for, session, jsonify, send_file
from werkzeug.security import generate_password_hash, check_password_hash

# ============================================================
# APP SETUP
# ============================================================
app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", os.urandom(32).hex())
app.config['SESSION_COOKIE_HTTPONLY'] = True
app.config['SESSION_COOKIE_SAMESITE'] = 'Lax'
app.config['MAX_CONTENT_LENGTH'] = 200 * 1024 * 1024  # 200MB hard ceiling (safety net, not a target)

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
UPLOAD_FOLDER = os.path.join(BASE_DIR, "uploads")
VENV_FOLDER = os.path.join(BASE_DIR, "venvs")
LOG_FOLDER = os.path.join(BASE_DIR, "logs")
DB_FILE = os.path.join(BASE_DIR, "database.json")
DB_LOCK = threading.Lock()

os.makedirs(UPLOAD_FOLDER, exist_ok=True)
os.makedirs(VENV_FOLDER, exist_ok=True)
os.makedirs(LOG_FOLDER, exist_ok=True)

ADMIN_PASS_ENV = os.environ.get("ADMIN_PASS", "112233")
ADMIN_INTERNAL_ID = "__admin__"   # internal folder/key used for admin's own unlimited apps

ENTRY_FILES_PY = ["main.py", "bot.py", "app.py", "run.py", "start.py"]
ENTRY_FILES_JS = ["index.js", "server.js", "bot.js", "app.js", "main.js"]

# ============================================================
# IN-MEMORY RUNTIME STATE (per-process, rebuilt from DB when needed)
# ============================================================
processes = {}          # (user, app_name) -> subprocess.Popen
proc_meta = {}          # (user, app_name) -> {"device": str, "started": ts, "restarts": int}
request_windows = defaultdict(lambda: deque())   # (user, app_name) -> deque of timestamps (outbound activity log, self-reported)
login_attempts = defaultdict(lambda: {"count": 0, "locked_until": 0})  # username -> attempt tracking

STATE_LOCK = threading.Lock()

# ============================================================
# DATABASE HELPERS
# ============================================================
def default_db():
    return {
        "users": {},               # email -> {"pw_hash":..., "vip": False, "created": ts}
        "admin_device_tokens": {}, # token -> True  (long-lived cookie tokens for admin device trust)
        "start_times": {},        # "user_app" -> epoch ms
        "app_settings": {},       # "user_app" -> {auto_on, auto_restart, sleep_until, req_hash, device, unlimited, public_token}
        "public_tokens": {},      # token -> "user_app"  (reverse lookup for public share links)
        "config": {
            "max_concurrent_per_user": 3,
            "max_concurrent_vip": 10,
            "max_concurrent_global": 25,
            "sleep_after_hours": 4,
            "auto_wake_after_minutes": 20,
            "request_baseline_per_min": 30
        }
    }

def load_db():
    with DB_LOCK:
        if not os.path.exists(DB_FILE):
            data = default_db()
            _write_db(data)
            return data
        try:
            with open(DB_FILE, "r") as f:
                data = json.load(f)
        except Exception:
            data = default_db()
            _write_db(data)
            return data

        # backfill any missing keys so old DB files never break new code
        defaults = default_db()
        for k, v in defaults.items():
            if k not in data:
                data[k] = v
        for k, v in defaults["config"].items():
            if k not in data.get("config", {}):
                data["config"][k] = v

        # migrate legacy (username-based, plaintext or hashed) users to the
        # new email-based structure. Old entries can't have a real email, so
        # they're kept under their old key but upgraded to dict form.
        migrated_users = {}
        for uname, val in data.get("users", {}).items():
            if isinstance(val, dict):
                migrated_users[uname] = val
            else:
                pw = val
                if not (isinstance(pw, str) and (pw.startswith("pbkdf2:") or pw.startswith("scrypt:"))):
                    pw = generate_password_hash(pw)
                migrated_users[uname] = {"pw_hash": pw, "vip": False, "created": int(time.time() * 1000)}
        data["users"] = migrated_users
        return data

def _write_db(data):
    temp_db = DB_FILE + ".tmp"
    with open(temp_db, "w") as f:
        json.dump(data, f, indent=2)
    os.replace(temp_db, DB_FILE)

def save_db(data):
    with DB_LOCK:
        _write_db(data)

def get_config(db, key):
    return db.get("config", {}).get(key, default_db()["config"].get(key))

def get_user_concurrency_limit(db, email):
    user_rec = db.get("users", {}).get(email, {})
    if user_rec.get("vip"):
        return get_config(db, "max_concurrent_vip")
    return get_config(db, "max_concurrent_per_user")

# ============================================================
# SECURITY HELPERS
# ============================================================
SAFE_NAME_RE = re.compile(r"^[A-Za-z0-9_\-\.]+$")

def is_safe_component(name):
    """Rejects path traversal, absolute paths, empty names."""
    if not name or name in (".", ".."):
        return False
    if "/" in name or "\\" in name:
        return False
    if not SAFE_NAME_RE.match(name):
        return False
    return True

def safe_join(base, *parts):
    """Joins paths and guarantees the result stays inside base. Raises ValueError otherwise."""
    base = os.path.abspath(base)
    target = os.path.abspath(os.path.join(base, *parts))
    if not (target == base or target.startswith(base + os.sep)):
        raise ValueError("Path traversal blocked")
    return target

def is_locked_out(username):
    rec = login_attempts[username]
    return time.time() < rec["locked_until"]

def register_failed_login(username):
    rec = login_attempts[username]
    rec["count"] += 1
    if rec["count"] >= 5:
        rec["locked_until"] = time.time() + 60
        rec["count"] = 0

def reset_login_attempts(username):
    login_attempts[username] = {"count": 0, "locked_until": 0}

EMAIL_RE = re.compile(r"^[A-Za-z0-9_.+\-]+@[A-Za-z0-9\-]+\.[A-Za-z0-9\-.]+$")

def is_valid_email(email):
    return bool(email) and len(email) <= 120 and bool(EMAIL_RE.match(email))

def user_folder_id(email):
    """Emails contain @ and . which aren't safe as raw folder names, so we
    derive a stable, filesystem-safe id from the email for storage purposes."""
    return hashlib.sha256(email.lower().encode()).hexdigest()[:24]

def generate_secret_token(nbytes=24):
    return os.urandom(nbytes).hex()

# ============================================================
# DEVICE FINGERPRINT POOL
# One is picked per app per run/restart, stays consistent for that
# run's lifetime (a real device doesn't change mid-session).
# ============================================================
DEVICE_POOL = [
    {"ua": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36", "platform": "Windows"},
    {"ua": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 Safari/605.1.15", "platform": "Windows"},
    {"ua": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 Safari/605.1.15", "platform": "Mac"},
    {"ua": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36", "platform": "Mac"},
    {"ua": "Mozilla/5.0 (iPhone; CPU iPhone OS 17_4 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 Mobile/15E148 Safari/604.1", "platform": "iOS"},
    {"ua": "Mozilla/5.0 (iPad; CPU OS 17_4 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 Mobile/15E148 Safari/604.1", "platform": "iOS"},
    {"ua": "Mozilla/5.0 (Linux; Android 14; SM-S928B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Mobile Safari/537.36", "platform": "Android"},
    {"ua": "Mozilla/5.0 (Linux; Android 13; SM-G991B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.0.0 Mobile Safari/537.36", "platform": "Android"},
    {"ua": "Mozilla/5.0 (Linux; Android 14; Pixel 8) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Mobile Safari/537.36", "platform": "Android"},
    {"ua": "Mozilla/5.0 (Linux; Android 12; CPH2449) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Mobile Safari/537.36", "platform": "Android"},
    {"ua": "Dalvik/2.1.0 (Linux; U; Android 14; SM-S918B Build/UP1A.231005.007)", "platform": "Android-App"},
    {"ua": "Dalvik/2.1.0 (Linux; U; Android 13; Pixel 7 Build/TQ3A.230901.001)", "platform": "Android-App"},
    {"ua": "Mozilla/5.0 (Windows NT 11.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.0.0 Safari/537.36 Edg/123.0.0.0", "platform": "Windows"},
    {"ua": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36", "platform": "Linux"},
    {"ua": "Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:125.0) Gecko/20100101 Firefox/125.0", "platform": "Linux"},
    {"ua": "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:125.0) Gecko/20100101 Firefox/125.0", "platform": "Windows"},
    {"ua": "Mozilla/5.0 (iPhone; CPU iPhone OS 16_6 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/16.6 Mobile/15E148 Safari/604.1", "platform": "iOS"},
    {"ua": "Mozilla/5.0 (Linux; Android 11; SM-G975F) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Mobile Safari/537.36", "platform": "Android"},
    {"ua": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.0.0 Safari/537.36 OPR/109.0.0.0", "platform": "Mac"},
    {"ua": "Mozilla/5.0 (Linux; Android 14; SM-A546E) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Mobile Safari/537.36", "platform": "Android"},
]

def assign_device(seed_key):
    """Deterministic-but-random pick, stable per app-run via seed_key (user_appname_starttime)."""
    rnd = random.Random(seed_key)
    device = rnd.choice(DEVICE_POOL)
    return device

def device_env_vars(device):
    """Environment variables injected into a child process so libraries that
    respect them (requests default headers via env, custom bots reading os.environ)
    can pick a consistent identity. The app's own code decides whether to use these."""
    return {
        "BOT_USER_AGENT": device["ua"],
        "BOT_DEVICE_PLATFORM": device["platform"],
    }

# ============================================================
# ADAPTIVE PROTECTION (no hard caps — baseline + spike detection)
# Goal: don't throttle normal traffic. Only step in when an app's
# self-reported activity deviates sharply from its own recent baseline.
# ============================================================
class AppActivityTracker:
    """Tracks a rolling window of activity per app and exposes a soft
    'should_slow_down' signal plus a circuit-breaker for repeated crashes."""
    def __init__(self):
        self.windows = defaultdict(lambda: deque())   # key -> timestamps
        self.crash_log = defaultdict(lambda: deque())  # key -> crash timestamps
        self.paused_until = {}                         # key -> epoch seconds
        self.lock = threading.Lock()

    def ping(self, key):
        now = time.time()
        with self.lock:
            dq = self.windows[key]
            dq.append(now)
            cutoff = now - 60
            while dq and dq[0] < cutoff:
                dq.popleft()

    def current_rate(self, key):
        with self.lock:
            return len(self.windows[key])

    def suggested_delay(self, key, baseline_per_min):
        """Returns a small random delay (seconds) to space out requests.
        Grows only if recent rate is far above the app's own historical baseline."""
        rate = self.current_rate(key)
        base_delay = random.uniform(0.4, 1.8)
        if baseline_per_min and rate > baseline_per_min * 3:
            # sharp spike vs configured baseline -> add gentle extra spacing
            return base_delay + random.uniform(1.5, 4.0)
        return base_delay

    def is_paused(self, key):
        return time.time() < self.paused_until.get(key, 0)

    def register_crash(self, key, cooldown_seconds=300):
        now = time.time()
        with self.lock:
            dq = self.crash_log[key]
            dq.append(now)
            cutoff = now - 600
            while dq and dq[0] < cutoff:
                dq.popleft()
            if len(dq) >= 4:
                self.paused_until[key] = now + cooldown_seconds
                return True
        return False

    def clear_pause(self, key):
        self.paused_until.pop(key, None)
        self.crash_log[key].clear()

activity = AppActivityTracker()

# ============================================================
# VALIDATION (pre-deploy syntax check)
# ============================================================
def validate_python_file(path):
    try:
        py_compile.compile(path, doraise=True)
        return {"ok": True}
    except py_compile.PyCompileError as e:
        msg = str(e.exc_value) if hasattr(e, "exc_value") else str(e)
        line = None
        m = re.search(r"line (\d+)", msg)
        if m:
            line = int(m.group(1))
        return {"ok": False, "line": line, "error": msg.strip()}
    except SyntaxError as e:
        return {"ok": False, "line": e.lineno, "error": f"{e.msg}"}
    except Exception as e:
        return {"ok": False, "line": None, "error": str(e)}

def validate_js_file(path):
    node_bin = shutil.which("node")
    if not node_bin:
        return {"ok": True, "skipped": True, "note": "Node not available on this server to validate JS"}
    try:
        result = subprocess.run([node_bin, "--check", path], capture_output=True, text=True, timeout=15)
        if result.returncode == 0:
            return {"ok": True}
        err = result.stderr.strip()
        line = None
        # Node's --check prints "path/to/file.js:LINE" as the very first line of stderr
        first_line = err.splitlines()[0] if err else ""
        m = re.search(re.escape(path) + r":(\d+)", first_line)
        if m:
            line = int(m.group(1))
        return {"ok": False, "line": line, "error": err}
    except Exception as e:
        return {"ok": False, "line": None, "error": str(e)}

def find_entry_file(extract_dir):
    for f in ENTRY_FILES_PY:
        if os.path.exists(os.path.join(extract_dir, f)):
            return f, "python"
    for f in ENTRY_FILES_JS:
        if os.path.exists(os.path.join(extract_dir, f)):
            return f, "node"
    return None, None

def validate_project(extract_dir):
    """Walks entry file + all .py/.js files it can find at top level and reports
    the first error with a line number, or ok:true if everything compiles."""
    entry, kind = find_entry_file(extract_dir)
    if not entry:
        return {"ok": False, "error": f"Entry file nahi mili. Inme se ek honi chahiye: {', '.join(ENTRY_FILES_PY + ENTRY_FILES_JS)}"}

    problems = []
    for root, dirs, files in os.walk(extract_dir):
        dirs[:] = [d for d in dirs if d not in ("venv", "node_modules", "__pycache__", ".git")]
        for fname in files:
            fpath = os.path.join(root, fname)
            rel = os.path.relpath(fpath, extract_dir)
            if fname.endswith(".py"):
                res = validate_python_file(fpath)
                if not res["ok"]:
                    problems.append({"file": rel, "line": res.get("line"), "error": res.get("error")})
            elif fname.endswith(".js") and kind == "node":
                res = validate_js_file(fpath)
                if not res.get("ok") and not res.get("skipped"):
                    problems.append({"file": rel, "line": res.get("line"), "error": res.get("error")})

    req_path = os.path.join(extract_dir, "requirements.txt")
    if os.path.exists(req_path):
        try:
            with open(req_path, "r", encoding="utf-8", errors="ignore") as f:
                for i, line in enumerate(f, 1):
                    line = line.strip()
                    if not line or line.startswith("#"):
                        continue
                    if not re.match(r"^[A-Za-z0-9_\-\.\[\]]+([=<>!~]=?[A-Za-z0-9_\-\.\*]+)?$", line):
                        problems.append({"file": "requirements.txt", "line": i, "error": f"Suspicious/invalid line: {line}"})
        except Exception as e:
            problems.append({"file": "requirements.txt", "line": None, "error": str(e)})

    if problems:
        return {"ok": False, "entry": entry, "kind": kind, "problems": problems}
    return {"ok": True, "entry": entry, "kind": kind}

# ============================================================
# SMART REQUIREMENTS INSTALL
# - one virtualenv per app
# - only installs what's missing / changed (hash of requirements.txt)
# - skips entirely if nothing changed since last successful install
# ============================================================
def venv_path_for(user, app_name):
    return safe_join(VENV_FOLDER, f"{user}__{app_name}")

def file_hash(path):
    if not os.path.exists(path):
        return None
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()

def get_installed_packages(python_bin):
    try:
        result = subprocess.run([python_bin, "-m", "pip", "list", "--format=freeze"],
                                 capture_output=True, text=True, timeout=30)
        installed = {}
        for line in result.stdout.splitlines():
            if "==" in line:
                name, ver = line.split("==", 1)
                installed[name.lower()] = ver
        return installed
    except Exception:
        return {}

def parse_requirements(req_path):
    reqs = []
    with open(req_path, "r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            reqs.append(line)
    return reqs

def ensure_venv(venv_dir):
    if not os.path.exists(os.path.join(venv_dir, "bin", "python")):
        subprocess.run(["python3", "-m", "venv", venv_dir], check=True, timeout=120)
    return os.path.join(venv_dir, "bin", "python")

def smart_install_python(extract_dir, venv_dir, log_callback):
    req_path = os.path.join(extract_dir, "requirements.txt")
    state_path = os.path.join(venv_dir, ".install_state.json")

    if not os.path.exists(req_path):
        log_callback("Koi requirements.txt nahi mili, install step skip.\n")
        return {"ok": True, "skipped": True}

    current_hash = file_hash(req_path)
    prev_state = {}
    if os.path.exists(state_path):
        try:
            with open(state_path) as f:
                prev_state = json.load(f)
        except Exception:
            prev_state = {}

    if prev_state.get("hash") == current_hash and prev_state.get("last_ok"):
        log_callback("requirements.txt me koi change nahi hai, install skip (already up to date).\n")
        return {"ok": True, "skipped": True}

    try:
        python_bin = ensure_venv(venv_dir)
    except Exception as e:
        log_callback(f"Virtual environment banane me error: {e}\n")
        return {"ok": False, "error": str(e)}

    installed = get_installed_packages(python_bin)
    wanted = parse_requirements(req_path)

    to_install = []
    for spec in wanted:
        pkg_name = re.split(r"[=<>!~\[]", spec, 1)[0].strip().lower()
        if "==" in spec:
            _, ver = spec.split("==", 1)
            if installed.get(pkg_name) == ver.strip():
                continue  # already installed at exact version, skip
        else:
            if pkg_name in installed:
                continue  # already installed, no version pinned, skip
        to_install.append(spec)

    if not to_install:
        log_callback("Sab packages already installed hain, kuch naya install nahi karna.\n")
        with open(state_path, "w") as f:
            json.dump({"hash": current_hash, "last_ok": True}, f)
        return {"ok": True, "skipped": True}

    log_callback(f"Installing/updating {len(to_install)} package(s): {', '.join(to_install)}\n")
    try:
        result = subprocess.run(
            [python_bin, "-m", "pip", "install", "--disable-pip-version-check"] + to_install,
            capture_output=True, text=True, timeout=600
        )
        log_callback(result.stdout[-3000:] + "\n")
        if result.returncode != 0:
            log_callback("PIP INSTALL WARNING (kuch packages fail ho sakte hain):\n" + result.stderr[-2000:] + "\n")
            with open(state_path, "w") as f:
                json.dump({"hash": current_hash, "last_ok": False}, f)
            return {"ok": False, "partial": True, "error": result.stderr[-500:]}
        with open(state_path, "w") as f:
            json.dump({"hash": current_hash, "last_ok": True}, f)
        log_callback("Dependencies installed successfully.\n")
        return {"ok": True}
    except subprocess.TimeoutExpired:
        log_callback("Install timeout ho gaya (10 min se zyada laga). App phir bhi start karne ki koshish karenge.\n")
        return {"ok": False, "error": "timeout"}
    except Exception as e:
        log_callback(f"Install error: {e}\n")
        return {"ok": False, "error": str(e)}

def smart_install_node(extract_dir, log_callback):
    pkg_path = os.path.join(extract_dir, "package.json")
    if not os.path.exists(pkg_path):
        log_callback("Koi package.json nahi mili, npm install skip.\n")
        return {"ok": True, "skipped": True}
    npm_bin = shutil.which("npm")
    if not npm_bin:
        log_callback("npm is server par available nahi hai, Node dependency install skip.\n")
        return {"ok": False, "error": "npm not found"}

    state_path = os.path.join(extract_dir, ".npm_install_state.json")
    current_hash = file_hash(pkg_path)
    prev_state = {}
    if os.path.exists(state_path):
        try:
            with open(state_path) as f:
                prev_state = json.load(f)
        except Exception:
            prev_state = {}

    if prev_state.get("hash") == current_hash and prev_state.get("last_ok"):
        log_callback("package.json me koi change nahi hai, npm install skip.\n")
        return {"ok": True, "skipped": True}

    log_callback("Running npm install...\n")
    try:
        result = subprocess.run([npm_bin, "install", "--no-audit", "--no-fund"],
                                 cwd=extract_dir, capture_output=True, text=True, timeout=600)
        log_callback(result.stdout[-3000:] + "\n")
        ok = result.returncode == 0
        if not ok:
            log_callback("NPM INSTALL WARNING:\n" + result.stderr[-2000:] + "\n")
        with open(state_path, "w") as f:
            json.dump({"hash": current_hash, "last_ok": ok}, f)
        return {"ok": ok}
    except subprocess.TimeoutExpired:
        log_callback("npm install timeout ho gaya.\n")
        return {"ok": False, "error": "timeout"}
    except Exception as e:
        log_callback(f"npm install error: {e}\n")
        return {"ok": False, "error": str(e)}

# ============================================================
# APP SETTINGS (per user_app: auto_on, auto_restart, sleep state, device)
# ============================================================
def app_settings_key(user, name):
    return f"{user}_{name}"

def get_app_settings(db, user, name):
    key = app_settings_key(user, name)
    settings = db.setdefault("app_settings", {}).setdefault(key, {})
    settings.setdefault("auto_on", False)
    settings.setdefault("auto_restart", False)
    settings.setdefault("sleep_until", 0)
    settings.setdefault("offline_at", 0)
    settings.setdefault("device_ua", None)
    settings.setdefault("device_platform", None)
    settings.setdefault("manual_stop", False)
    settings.setdefault("unlimited", False)   # True for admin apps -> skip 4h auto-sleep
    settings.setdefault("public_token", None) # secret token for the no-login share link
    return settings

def ensure_public_token(db, user, name):
    settings = get_app_settings(db, user, name)
    if not settings.get("public_token"):
        token = generate_secret_token()
        settings["public_token"] = token
        db.setdefault("public_tokens", {})[token] = app_settings_key(user, name)
        save_db(db)
    return settings["public_token"]

def revoke_public_token(db, user, name):
    settings = get_app_settings(db, user, name)
    old = settings.get("public_token")
    if old:
        db.get("public_tokens", {}).pop(old, None)
    settings["public_token"] = None
    save_db(db)

def app_dirs(user, name):
    app_dir = safe_join(UPLOAD_FOLDER, user, name)
    extract_dir = os.path.join(app_dir, "extracted")
    log_path = os.path.join(app_dir, "logs.txt")
    return app_dir, extract_dir, log_path

def append_log(log_path, text):
    try:
        with open(log_path, "a", encoding="utf-8", errors="ignore") as f:
            f.write(text)
    except Exception:
        pass

def trim_log_if_needed(log_path, max_bytes=500_000):
    try:
        if os.path.exists(log_path) and os.path.getsize(log_path) > max_bytes:
            with open(log_path, "r", encoding="utf-8", errors="ignore") as f:
                f.seek(-max_bytes // 2, os.SEEK_END)
                tail = f.read()
            with open(log_path, "w", encoding="utf-8", errors="ignore") as f:
                f.write("...[log truncated]...\n" + tail)
    except Exception:
        pass

def count_running_for_user(user):
    return sum(1 for (u, _), p in processes.items() if u == user and p.poll() is None)

def count_running_global():
    return sum(1 for p in processes.values() if p.poll() is None)

def start_app_process(user, name, db):
    """Core launcher: validates, installs deps if needed, assigns a device
    fingerprint, and starts the subprocess. Returns dict with ok/error info."""
    app_dir, extract_dir, log_path = app_dirs(user, name)
    key = (user, name)

    if key in processes and processes[key].poll() is None:
        return {"ok": True, "already_running": True}

    if activity.is_paused(f"{user}_{name}"):
        return {"ok": False, "error": "Ye app abhi cooldown me hai (baar baar crash hone ki wajah se). Thodi der baad try karo."}

    entry, kind = find_entry_file(extract_dir)
    if not entry:
        msg = f"Entry file nahi mili. Inme se ek honi chahiye: {', '.join(ENTRY_FILES_PY + ENTRY_FILES_JS)}"
        append_log(log_path, f"[{datetime.now()}] START FAILED: {msg}\n")
        return {"ok": False, "error": msg}

    settings = get_app_settings(db, user, name)

    # concurrency guards (soft, configurable — not meant to block normal usage)
    # admin's own apps are unlimited/unmanaged — only the server-wide global cap still applies
    max_global = get_config(db, "max_concurrent_global")
    if user != ADMIN_INTERNAL_ID:
        max_user = get_user_concurrency_limit(db, user)
        if count_running_for_user(user) >= max_user:
            return {"ok": False, "error": f"Aapki max {max_user} apps ek saath chal sakti hain. Koi ek stop karke try karo."}
    if count_running_global() >= max_global:
        return {"ok": False, "error": "Server abhi apni max capacity par hai, thodi der baad try karo."}

    append_log(log_path, f"\n[{datetime.now()}] ===== Deploy start =====\n")

    def log_cb(text):
        append_log(log_path, text)

    if kind == "python":
        venv_dir = venv_path_for(user, name)
        install_res = smart_install_python(extract_dir, venv_dir, log_cb)
        try:
            python_bin = ensure_venv(venv_dir)
        except Exception as e:
            append_log(log_path, f"Venv error: {e}\n")
            return {"ok": False, "error": f"Environment setup fail: {e}"}
        cmd = [python_bin, entry]
    else:
        install_res = smart_install_node(extract_dir, log_cb)
        node_bin = shutil.which("node") or "node"
        cmd = [node_bin, entry]

    # device fingerprint: stable for this run
    seed_key = f"{user}_{name}_{int(time.time())}"
    device = assign_device(seed_key)
    settings["device_ua"] = device["ua"]
    settings["device_platform"] = device["platform"]
    settings["manual_stop"] = False

    env = os.environ.copy()
    env.update(device_env_vars(device))
    env["PYTHONUNBUFFERED"] = "1"

    trim_log_if_needed(log_path)
    log_file = open(log_path, "a", encoding="utf-8", errors="ignore")
    try:
        proc = subprocess.Popen(cmd, cwd=extract_dir, stdout=log_file, stderr=log_file,
                                 text=True, env=env)
    except Exception as e:
        append_log(log_path, f"Process start error: {e}\n")
        return {"ok": False, "error": str(e)}

    processes[key] = proc
    proc_meta[key] = {"device": device, "started": time.time(), "restarts": proc_meta.get(key, {}).get("restarts", 0)}

    now_ms = int(time.time() * 1000)
    db["start_times"][app_settings_key(user, name)] = now_ms
    settings["offline_at"] = 0
    settings["sleep_until"] = 0
    save_db(db)

    append_log(log_path, f"[{datetime.now()}] Started with entry={entry}, device={device['platform']}\n")
    return {"ok": True, "install": install_res, "device": device["platform"]}

def stop_app_process(user, name, db, manual=True):
    key = (user, name)
    p = processes.get(key)
    if p and p.poll() is None:
        try:
            p.terminate()
            try:
                p.wait(timeout=5)
            except subprocess.TimeoutExpired:
                p.kill()
        except Exception:
            pass
    if key in processes:
        del processes[key]

    settings = get_app_settings(db, user, name)
    settings["manual_stop"] = manual
    tkey = app_settings_key(user, name)
    if tkey in db["start_times"]:
        del db["start_times"][tkey]
    save_db(db)

# ============================================================
# BACKGROUND SCHEDULER: sleep-after-4h, conditional auto-wake,
# crash detection -> circuit breaker, auto-restart if enabled
# ============================================================
def scheduler_loop():
    while True:
        try:
            db = load_db()
            sleep_hours = get_config(db, "sleep_after_hours")
            wake_minutes = get_config(db, "auto_wake_after_minutes")
            now = time.time()
            changed = False

            for tkey, started_ms in list(db.get("start_times", {}).items()):
                if "_" not in tkey:
                    continue
                user, name = tkey.split("_", 1)
                key = (user, name)
                settings = get_app_settings(db, user, name)
                started_s = started_ms / 1000.0

                p = processes.get(key)
                is_running = bool(p and p.poll() is None)

                if is_running and not settings.get("unlimited") and (now - started_s) >= sleep_hours * 3600:
                    _, _, log_path = app_dirs(user, name)
                    append_log(log_path, f"[{datetime.now()}] Auto-sleep: {sleep_hours}h reached, stopping.\n")
                    stop_app_process(user, name, db, manual=False)
                    settings = get_app_settings(db, user, name)
                    settings["offline_at"] = now
                    changed = True

                if p and not is_running and key in processes:
                    # process died on its own (crash)
                    tracker_key = f"{user}_{name}"
                    tripped = activity.register_crash(tracker_key)
                    del processes[key]
                    if tkey in db["start_times"]:
                        del db["start_times"][tkey]
                    settings["offline_at"] = now
                    changed = True
                    _, _, log_path = app_dirs(user, name)
                    if tripped:
                        append_log(log_path, f"[{datetime.now()}] Repeated crashes detected, cooling down for 5 min.\n")
                    elif settings.get("auto_restart") and not settings.get("manual_stop"):
                        append_log(log_path, f"[{datetime.now()}] Crash detected, auto-restart is ON, restarting.\n")
                        start_app_process(user, name, db)

                if not is_running and settings.get("offline_at") and settings.get("auto_on") and not settings.get("manual_stop"):
                    if (now - settings["offline_at"]) >= wake_minutes * 60 and not activity.is_paused(f"{user}_{name}"):
                        _, _, log_path = app_dirs(user, name)
                        append_log(log_path, f"[{datetime.now()}] Auto-On: {wake_minutes} min cooldown khatam, restarting.\n")
                        start_app_process(user, name, db)
                        changed = True

            if changed:
                save_db(db)
        except Exception:
            pass
        time.sleep(30)

def resume_apps_after_restart():
    """On server process restart, previously-running apps are NOT force-resumed
    automatically unless their auto_restart/auto_on flags say so — avoids
    surprising behavior, but we do clear stale start_times so the dashboard
    doesn't show a 'running' app that no longer has a process."""
    db = load_db()
    changed = False
    for tkey in list(db.get("start_times", {}).keys()):
        if "_" not in tkey:
            continue
        user, name = tkey.split("_", 1)
        key = (user, name)
        if key not in processes or processes[key].poll() is not None:
            del db["start_times"][tkey]
            settings = get_app_settings(db, user, name)
            settings["offline_at"] = time.time()
            changed = True
    if changed:
        save_db(db)

_scheduler_started = False
def ensure_scheduler():
    global _scheduler_started
    if not _scheduler_started:
        _scheduler_started = True
        resume_apps_after_restart()
        t = threading.Thread(target=scheduler_loop, daemon=True)
        t.start()

# ============================================================
# LOGIN PAGE
# ============================================================
LOGIN_HTML = '''
<!DOCTYPE html>
<html>
<head>
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Login | SHADMAN </title>
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css">
    <style>
        :root { --bg: #030508; --primary: #00ffff; --sec: #7000ff; --glass: rgba(255, 255, 255, 0.03); }
        body { background: var(--bg); color: white; font-family: 'Segoe UI', sans-serif; display: flex; justify-content: center; align-items: center; height: 100vh; margin: 0; }
        .login-card { position: relative; z-index: 10; background: var(--glass); padding: 40px 30px; border-radius: 25px; width: 340px; max-width: 90vw; text-align: center; border: 1px solid rgba(0, 255, 255, 0.15); backdrop-filter: blur(20px); box-shadow: 0 25px 45px rgba(0,0,0,0.5); }
        .lock-container { width: 80px; height: 80px; background: rgba(0, 255, 255, 0.1); border-radius: 50%; display: flex; align-items: center; justify-content: center; margin: 0 auto 20px; border: 2px solid var(--primary); }
        .lock-icon { font-size: 35px; color: var(--primary); }
        h2 { font-size: 20px; margin-bottom: 10px; letter-spacing: 3px; text-transform: uppercase; background: linear-gradient(to right, #fff, var(--primary)); -webkit-background-clip: text; -webkit-text-fill-color: transparent; }
        .sub { font-size: 11px; opacity: 0.6; margin-bottom: 15px; }
        .err { background: rgba(255,60,60,0.15); border: 1px solid #ff4757; color: #ff9a9a; padding: 10px; border-radius: 10px; font-size: 13px; margin-bottom: 10px; }
        input, select { width: 100%; padding: 14px; margin: 8px 0; border-radius: 12px; border: 1px solid rgba(255,255,255,0.1); background: rgba(255,255,255,0.05); color: #fff; outline: none; font-size: 14px; box-sizing: border-box; }
        button { width: 100%; padding: 15px; border-radius: 12px; border: none; background: linear-gradient(45deg, var(--sec), var(--primary)); color: #fff; font-weight: bold; font-size: 15px; cursor: pointer; margin-top: 10px; text-transform: uppercase; letter-spacing: 2px; }
    </style>
</head>
<body>
    <div class="login-card">
        <div class="lock-container"><i class="fa-solid fa-user-shield lock-icon"></i></div>
        <h2>SHADMAN </h2>
        <div class="sub">Email se login ya naya account turant ban jayega</div>
        {% if error %}<div class="err">{{ error }}</div>{% endif %}
        <form method="post" action="/login">
            <input type="email" name="email" placeholder="Email address" required maxlength="120">
            <input type="password" name="password" placeholder="Password" required maxlength="100" minlength="4">
            <button type="submit">Login / Register</button>
        </form>
    </div>
</body>
</html>
'''

ADMIN_LOGIN_HTML = '''
<!DOCTYPE html>
<html>
<head>
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Admin | SHADMAN </title>
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css">
    <style>
        :root { --bg: #030508; --primary: #00ffff; --sec: #7000ff; --glass: rgba(255, 255, 255, 0.03); }
        body { background: var(--bg); color: white; font-family: 'Segoe UI', sans-serif; display: flex; justify-content: center; align-items: center; height: 100vh; margin: 0; }
        .login-card { background: var(--glass); padding: 40px 30px; border-radius: 25px; width: 320px; max-width: 90vw; text-align: center; border: 1px solid rgba(255,0,100,0.2); backdrop-filter: blur(20px); }
        .lock-container { width: 80px; height: 80px; background: rgba(255,0,100,0.1); border-radius: 50%; display: flex; align-items: center; justify-content: center; margin: 0 auto 20px; border: 2px solid #ff0064; }
        .lock-icon { font-size: 35px; color: #ff0064; }
        h2 { font-size: 18px; letter-spacing: 3px; text-transform: uppercase; color: #fff; }
        .err { background: rgba(255,60,60,0.15); border: 1px solid #ff4757; color: #ff9a9a; padding: 10px; border-radius: 10px; font-size: 13px; margin-bottom: 10px; }
        input { width: 100%; padding: 14px; margin: 8px 0; border-radius: 12px; border: 1px solid rgba(255,255,255,0.1); background: rgba(255,255,255,0.05); color: #fff; outline: none; font-size: 14px; box-sizing: border-box; text-align: center; letter-spacing: 4px; }
        button { width: 100%; padding: 15px; border-radius: 12px; border: none; background: linear-gradient(45deg, #ff0064, #ff7a00); color: #fff; font-weight: bold; font-size: 15px; cursor: pointer; margin-top: 10px; text-transform: uppercase; letter-spacing: 2px; }
    </style>
</head>
<body>
    <div class="login-card">
        <div class="lock-container"><i class="fa-solid fa-shield-halved lock-icon"></i></div>
        <h2>Root Access</h2>
        {% if error %}<div class="err">{{ error }}</div>{% endif %}
        <form method="post" action="/admin">
            <input type="password" name="password" placeholder="••••••" required maxlength="50" autofocus>
            <button type="submit">Unlock</button>
        </form>
    </div>
</body>
</html>
'''

# ============================================================
# ADMIN PANEL
# ============================================================
ADMIN_HTML = '''
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Admin Root | SHADMAN </title>
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css">
    <script src="https://cdn.jsdelivr.net/npm/sweetalert2@11"></script>
    <style>
        :root { --bg: #030508; --card: rgba(22, 27, 34, 0.85); --accent: #00ffff; --text: #e6edf3; --glass: rgba(255, 255, 255, 0.05); }
        * { box-sizing: border-box; }
        body { background: var(--bg); color: var(--text); font-family: 'Segoe UI', sans-serif; margin: 0; padding: 15px; min-height: 100vh; padding-bottom: 60px; }
        .header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 20px; padding: 12px; background: var(--glass); border-radius: 15px; border: 1px solid rgba(0, 255, 255, 0.2); }
        .header h2 { font-size: 18px; color: var(--accent); margin: 0; }
        .stats-grid { display: grid; grid-template-columns: 1fr 1fr 1fr; gap: 10px; margin-bottom: 20px; }
        .stat-card { background: var(--card); padding: 12px; border-radius: 15px; border: 1px solid rgba(255,255,255,0.05); text-align: center; }
        .stat-card p { font-size: 11px; margin: 4px 0; opacity: 0.7; }
        .stat-card div.val { font-size: 17px; font-weight: bold; color: var(--accent); }
        .card { background: var(--card); padding: 15px; border-radius: 20px; border: 1px solid rgba(255,255,255,0.08); margin-bottom: 18px; }
        h3 { margin-top: 0; font-size: 15px; color: var(--accent); display: flex; align-items: center; gap: 8px; }
        .input-group { display: flex; flex-direction: column; gap: 10px; margin-top: 10px; }
        input, select { width: 100%; padding: 10px; border-radius: 10px; border: 1px solid #333; background: rgba(0,0,0,0.3); color: white; outline: none; font-size: 13px; box-sizing: border-box; }
        .btn { padding: 10px; border-radius: 10px; border: none; font-weight: bold; cursor: pointer; text-align: center; text-decoration: none; display: inline-flex; align-items: center; justify-content: center; gap: 6px; font-size: 13px; }
        .btn-primary { background: linear-gradient(45deg, #00ffff, #7000ff); color: #000; }
        .btn-logout { background: #ff4757; color: white; padding: 8px 14px; }
        .btn-danger { background: #ff4757; color: white; }
        .btn-gold { background: linear-gradient(45deg, #ffd700, #ff9500); color: #000; }
        .btn-small { padding: 6px 10px; font-size: 11px; }
        .user-item, .proxy-item { background: rgba(255,255,255,0.03); border-radius: 12px; padding: 12px; margin-bottom: 8px; border: 1px solid rgba(255,255,255,0.05); }
        .row { display: flex; justify-content: space-between; align-items: center; gap: 8px; flex-wrap: wrap; }
        .username { font-weight: bold; color: var(--accent); font-size: 13px; word-break: break-all; }
        .tag { padding: 3px 8px; border-radius: 6px; font-size: 10px; border: 1px solid; }
        .tag-green { color: #2ecc71; border-color: #2ecc71; background: rgba(46,204,113,0.1); }
        .tag-red { color: #ff4757; border-color: #ff4757; background: rgba(255,71,87,0.1); }
        .tag-gold { color: #ffd700; border-color: #ffd700; background: rgba(255,215,0,0.1); }
        .action-row { display: flex; gap: 6px; margin-top: 8px; flex-wrap: wrap; }
        .toggle-switch { position: relative; width: 44px; height: 24px; flex-shrink: 0; }
        .toggle-switch input { opacity: 0; width: 0; height: 0; }
        .slider { position: absolute; cursor: pointer; inset: 0; background: #444; border-radius: 24px; transition: .3s; }
        .slider:before { content: ""; position: absolute; height: 18px; width: 18px; left: 3px; bottom: 3px; background: white; border-radius: 50%; transition: .3s; }
        input:checked + .slider { background: #ffd700; }
        input:checked + .slider:before { transform: translateX(20px); }
        .small-text { font-size: 11px; opacity: 0.6; }
        .upload-mini { border: 2px dashed rgba(0,255,255,0.3); border-radius: 14px; padding: 15px; text-align: center; }
    </style>
</head>
<body>
    <div class="header"><h2><i class="fa-solid fa-shield-halved"></i> SHADMAN  ROOT</h2><a href="/logout" class="btn btn-logout"><i class="fa-solid fa-power-off"></i></a></div>

    <div class="stats-grid">
        <div class="stat-card"><p>Users</p><div class="val">{{ users|length }}</div></div>
        <div class="stat-card"><p>Running Apps</p><div class="val">{{ running_count }}</div></div>
        <div class="stat-card"><p>RAM Used</p><div class="val">{{ ram_percent }}%</div></div>
    </div>

    <div class="card">
        <h3><i class="fa-solid fa-infinity"></i> Admin Unlimited Apps (no 4h sleep)</h3>
        <div class="upload-mini">
            <input type="file" id="adminFileInput" accept=".zip" style="display:none;">
            <button class="btn btn-primary" onclick="document.getElementById('adminFileInput').click()"><i class="fa-solid fa-upload"></i> Upload Admin App</button>
            <div id="adminUploadStatus" class="small-text" style="margin-top:8px;"></div>
        </div>
        {% for a in admin_apps %}
        <div class="user-item" style="margin-top:10px;">
            <div class="row">
                <span><b>{{ a.name }}</b></span>
                {% if a.running %}<span class="tag tag-green">RUNNING</span>{% else %}<span class="tag tag-red">OFFLINE</span>{% endif %}
            </div>
            <div class="small-text">Device: {{ a.device or "—" }} | Unlimited runtime</div>
            <div class="action-row">
                {% if a.running %}
                <a href="/stop/{{ a.name }}" class="btn btn-danger btn-small">Stop</a>
                {% else %}
                <a href="/run/{{ a.name }}" class="btn btn-primary btn-small">Run</a>
                {% endif %}
                <button class="btn btn-primary btn-small" onclick="getAdminPublicLink('{{ a.name }}')"><i class="fa-solid fa-link"></i> Public Link</button>
                <a href="/delete/{{ a.name }}" class="btn btn-danger btn-small">Delete</a>
            </div>
        </div>
        {% endfor %}
        {% if not admin_apps %}<p class="small-text">Koi admin app upload nahi hui abhi tak.</p>{% endif %}
    </div>

    <div class="card">
        <h3><i class="fa-solid fa-sliders"></i> Global Limits</h3>
        <form action="/admin/update_config" method="post" class="input-group">
            <label class="small-text">Max apps per normal user (concurrent)</label>
            <input type="number" name="max_concurrent_per_user" value="{{ config.max_concurrent_per_user }}">
            <label class="small-text">Max apps per VIP user (concurrent)</label>
            <input type="number" name="max_concurrent_vip" value="{{ config.max_concurrent_vip }}">
            <label class="small-text">Max apps server-wide (concurrent)</label>
            <input type="number" name="max_concurrent_global" value="{{ config.max_concurrent_global }}">
            <label class="small-text">Auto-sleep after (hours)</label>
            <input type="number" step="0.1" name="sleep_after_hours" value="{{ config.sleep_after_hours }}">
            <label class="small-text">Auto-wake after (minutes)</label>
            <input type="number" name="auto_wake_after_minutes" value="{{ config.auto_wake_after_minutes }}">
            <button type="submit" class="btn btn-primary">Save Config</button>
        </form>
    </div>

    <div class="card">
        <h3><i class="fa-solid fa-user-gear"></i> User Management</h3>
        {% for u in users %}
        <div class="user-item">
            <div class="row">
                <span class="username"><i class="fa-solid fa-circle-user"></i> {{ u.email }}</span>
                <label class="toggle-switch" title="VIP">
                    <input type="checkbox" {% if u.vip %}checked{% endif %} onchange="toggleVip('{{ u.email }}', this)">
                    <span class="slider"></span>
                </label>
            </div>
            {% if u.vip %}<span class="tag tag-gold">VIP</span>{% endif %}
            <div class="action-row">
                <a href="/admin/login_as/{{ u.email }}" class="btn btn-primary btn-small"><i class="fa-solid fa-sign-in"></i> Login as</a>
                <form action="/admin/change_pw" method="post" style="display:flex; gap:5px; flex:1;">
                    <input type="hidden" name="email" value="{{ u.email }}">
                    <input type="text" name="new_pw" placeholder="New password">
                    <button type="submit" class="btn btn-primary btn-small"><i class="fa-solid fa-save"></i></button>
                </form>
            </div>
        </div>
        {% endfor %}
        {% if not users %}<p class="small-text">Koi user nahi bana abhi tak.</p>{% endif %}
    </div>

    <div class="card">
        <h3><i class="fa-solid fa-server"></i> All User Apps</h3>
        {% for a in all_apps %}
        <div class="user-item">
            <div class="row">
                <span style="font-size:12px;"><b>{{ a.user }}</b> / {{ a.name }}</span>
                {% if a.running %}<span class="tag tag-green">RUNNING</span>{% else %}<span class="tag tag-red">OFFLINE</span>{% endif %}
            </div>
            <div class="small-text">Device: {{ a.device or "—" }} | Auto-On: {{ "Yes" if a.auto_on else "No" }} | Auto-Restart: {{ "Yes" if a.auto_restart else "No" }}</div>
        </div>
        {% endfor %}
        {% if not all_apps %}<p class="small-text">Koi app upload nahi hui abhi tak.</p>{% endif %}
    </div>

<script>
function toggleVip(email, checkbox) {
    const fd = new FormData();
    fd.append('email', email);
    fetch('/admin/toggle_vip', { method: 'POST', body: fd })
        .then(r => r.json()).then(res => {
            if (!res.ok) { checkbox.checked = !checkbox.checked; }
            else { setTimeout(() => location.reload(), 300); }
        });
}

document.getElementById('adminFileInput').addEventListener('change', function(e) {
    const file = e.target.files[0];
    if (!file) return;
    const statusDiv = document.getElementById('adminUploadStatus');
    statusDiv.textContent = 'Uploading...';
    const fd = new FormData();
    fd.append('file', file, file.name);
    fetch('/admin/upload_admin_app', { method: 'POST', body: fd })
        .then(r => r.json()).then(res => {
            if (res.ok) { statusDiv.textContent = 'Deployed!'; setTimeout(() => location.reload(), 700); }
            else { statusDiv.textContent = ''; Swal.fire('Error', res.error || 'Upload fail', 'error'); }
        });
});

function getAdminPublicLink(name) {
    fetch('/admin/get_public_link/' + encodeURIComponent(name), { method: 'POST' })
        .then(r => r.json()).then(res => {
            if (res.ok) {
                Swal.fire({
                    title: 'Public Link',
                    html: '<input readonly style="width:100%;padding:8px;" value="' + res.url + '" onclick="this.select()">',
                    confirmButtonText: 'Close'
                });
            } else {
                Swal.fire('Error', res.error || 'Link nahi ban paya', 'error');
            }
        });
}
</script>
</body>
</html>
'''

# ============================================================
# PUBLIC SHARE PAGE (no login — status, start/stop, logs only)
# ============================================================
PUBLIC_HTML = '''
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{{ name or "Not found" }} | SHADMAN  Public</title>
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css">
    <script src="https://cdn.jsdelivr.net/npm/sweetalert2@11"></script>
    <style>
        :root { --bg: #030508; --primary: #00ffff; --card: rgba(22,27,34,0.85); --text: #e6edf3; }
        * { box-sizing: border-box; }
        body { background: var(--bg); color: var(--text); font-family: 'Segoe UI', sans-serif; margin: 0; padding: 15px; }
        .card { background: var(--card); border-radius: 18px; padding: 20px; border: 1px solid rgba(255,255,255,0.08); max-width: 500px; margin: 20px auto; }
        h2 { color: var(--primary); font-size: 18px; margin-top: 0; }
        .status-pill { font-size: 11px; padding: 5px 12px; border-radius: 20px; border: 1px solid; }
        .status-run { color: #2ecc71; border-color: #2ecc71; background: rgba(46,204,113,0.1); }
        .status-off { color: #ff4757; border-color: #ff4757; background: rgba(255,71,87,0.1); }
        .btn { padding: 12px; border-radius: 10px; border: none; font-weight: bold; cursor: pointer; font-size: 14px; width: 100%; margin-top: 10px; color: #fff; }
        .btn-primary { background: linear-gradient(45deg, #00ffff, #7000ff); color: #000; }
        .btn-danger { background: #ff4757; }
        #logBox { background: #000; color: #0f0; font-family: monospace; font-size: 11px; padding: 10px; border-radius: 8px; max-height: 300px; overflow-y: auto; white-space: pre-wrap; word-break: break-all; margin-top: 15px; }
        .small-text { font-size: 11px; opacity: 0.6; margin-top: 10px; }
    </style>
</head>
<body>
    {% if valid %}
    <div class="card">
        <div style="display:flex; justify-content:space-between; align-items:center;">
            <h2><i class="fa-solid fa-server"></i> {{ name }}</h2>
            <span class="status-pill {% if running %}status-run{% else %}status-off{% endif %}" id="statusPill">{% if running %}RUNNING{% else %}OFFLINE{% endif %}</span>
        </div>
        <p class="small-text">Public control link — sirf start/stop/logs. File edit ke liye account se login karo.</p>
        <button class="btn btn-primary" id="startBtn" onclick="doAction('start')" {% if running %}style="display:none;"{% endif %}><i class="fa-solid fa-play"></i> Start</button>
        <button class="btn btn-danger" id="stopBtn" onclick="doAction('stop')" {% if not running %}style="display:none;"{% endif %}><i class="fa-solid fa-stop"></i> Stop</button>
        <div id="logBox">Loading logs...</div>
    </div>
    <script>
        const token = "{{ token }}";
        function refresh() {
            fetch('/public/' + token + '/status').then(r => r.json()).then(res => {
                if (!res.ok) return;
                document.getElementById('logBox').textContent = res.log || '(Koi log nahi hai)';
                const pill = document.getElementById('statusPill');
                pill.textContent = res.running ? 'RUNNING' : 'OFFLINE';
                pill.className = 'status-pill ' + (res.running ? 'status-run' : 'status-off');
                document.getElementById('startBtn').style.display = res.running ? 'none' : 'block';
                document.getElementById('stopBtn').style.display = res.running ? 'block' : 'none';
            });
        }
        function doAction(action) {
            fetch('/public/' + token + '/' + action, { method: 'POST' }).then(r => r.json()).then(res => {
                if (!res.ok) Swal.fire('Error', res.error || 'Action fail ho gaya', 'error');
                setTimeout(refresh, 500);
            });
        }
        refresh();
        setInterval(refresh, 4000);
    </script>
    {% else %}
    <div class="card">
        <h2><i class="fa-solid fa-triangle-exclamation"></i> Link Invalid</h2>
        <p class="small-text">Ye public link expire ho chuka hai ya kabhi valid nahi tha.</p>
    </div>
    {% endif %}
</body>
</html>
'''

# ============================================================
# ROUTES — AUTH
# ============================================================
@app.before_request
def _boot():
    ensure_scheduler()

@app.route("/login", methods=["GET", "POST"])
def login():
    error = None
    if request.method == "POST":
        email = request.form.get("email", "").strip().lower()
        pw = request.form.get("password", "").strip()

        if not is_valid_email(email):
            error = "Sahi email address daalo (jaise you@example.com)."
            return render_template_string(LOGIN_HTML, error=error)
        if not pw or len(pw) < 4:
            error = "Password kam se kam 4 characters ka hona chahiye."
            return render_template_string(LOGIN_HTML, error=error)

        if is_locked_out(email):
            error = "Bohot zyada galat attempts. 1 minute baad try karo."
            return render_template_string(LOGIN_HTML, error=error)

        db = load_db()
        folder_id = user_folder_id(email)

        if email not in db["users"]:
            # first time seeing this email -> register it now
            db["users"][email] = {"pw_hash": generate_password_hash(pw), "vip": False, "created": int(time.time() * 1000)}
            save_db(db)
            session['is_admin'], session['username'], session['user_folder'] = False, email, folder_id
            reset_login_attempts(email)
            return redirect(url_for("index"))

        if check_password_hash(db["users"][email]["pw_hash"], pw):
            session['is_admin'], session['username'], session['user_folder'] = False, email, folder_id
            reset_login_attempts(email)
            return redirect(url_for("index"))

        register_failed_login(email)
        error = "Galat password is email ke liye."
    return render_template_string(LOGIN_HTML, error=error)

@app.route("/admin", methods=["GET", "POST"])
def admin_login():
    # already-logged-in-this-session admins go straight to the panel
    if session.get('is_admin'):
        return redirect(url_for("admin_panel"))

    db = load_db()
    trusted_cookie = request.cookies.get("admin_trust")
    if trusted_cookie and trusted_cookie in db.get("admin_device_tokens", {}):
        session['is_admin'], session['username'] = True, ADMIN_INTERNAL_ID
        return redirect(url_for("admin_panel"))

    error = None
    if request.method == "POST":
        pw = request.form.get("password", "").strip()
        if is_locked_out("__admin_pw__"):
            error = "Bohot zyada galat attempts. 1 minute baad try karo."
        elif pw == ADMIN_PASS_ENV:
            reset_login_attempts("__admin_pw__")
            session['is_admin'], session['username'] = True, ADMIN_INTERNAL_ID
            token = generate_secret_token()
            db.setdefault("admin_device_tokens", {})[token] = True
            save_db(db)
            resp = redirect(url_for("admin_panel"))
            resp.set_cookie("admin_trust", token, max_age=60 * 60 * 24 * 365, httponly=True, samesite="Lax")
            return resp
        else:
            register_failed_login("__admin_pw__")
            error = "Galat password."
    return render_template_string(ADMIN_LOGIN_HTML, error=error)

@app.route("/logout")
def logout():
    was_admin = session.get('is_admin', False)
    session.clear()
    if was_admin:
        resp = redirect(url_for("login"))
        resp.delete_cookie("admin_trust")
        return resp
    return redirect(url_for("login"))

def require_login():
    return 'username' in session

def require_admin():
    return session.get('is_admin', False)

def current_user_key():
    """Returns the filesystem-safe folder key for whoever is logged in:
    the admin gets a fixed internal id, normal users get a hash of their email."""
    if session.get('is_admin'):
        return ADMIN_INTERNAL_ID
    return session.get('user_folder') or user_folder_id(session.get('username', ''))

# ============================================================
# ROUTES — DASHBOARD
# ============================================================
@app.route("/")
def index():
    if not require_login():
        return redirect(url_for("login"))
    user_name = current_user_key()
    user_dir = safe_join(UPLOAD_FOLDER, user_name)
    os.makedirs(user_dir, exist_ok=True)
    db = load_db()
    apps_list = []
    for name in sorted(os.listdir(user_dir)):
        if not os.path.isdir(os.path.join(user_dir, name)):
            continue
        p = processes.get((user_name, name))
        running = bool(p and p.poll() is None)
        settings = get_app_settings(db, user_name, name)
        start_ms = db["start_times"].get(app_settings_key(user_name, name), 0)
        elapsed = (time.time() - start_ms / 1000.0) if start_ms else 0
        sleep_hours = get_config(db, "sleep_after_hours")
        wake_minutes = get_config(db, "auto_wake_after_minutes")
        remaining_run = max(0, sleep_hours * 3600 - elapsed) if running else 0
        remaining_wake = 0
        if not running and settings.get("offline_at") and settings.get("auto_on") and not settings.get("manual_stop"):
            remaining_wake = max(0, wake_minutes * 60 - (time.time() - settings["offline_at"]))
        apps_list.append({
            "name": name,
            "running": running,
            "auto_on": settings.get("auto_on", False),
            "auto_restart": settings.get("auto_restart", False),
            "device": settings.get("device_platform"),
            "remaining_run_min": round(remaining_run / 60, 1),
            "remaining_wake_min": round(remaining_wake / 60, 1),
        })
    display_name = "Admin" if session.get('is_admin') else session.get('username', user_name)
    return render_template("index.html", apps=apps_list, username=display_name)

# ============================================================
# ROUTES — UPLOAD / VALIDATE / DEPLOY
# ============================================================
def _do_upload(user_name, mark_unlimited=False):
    file = request.files.get("file")
    overwrite = request.form.get("overwrite") == "true"

    if not file or not file.filename:
        return jsonify({"ok": False, "error": "Koi file nahi mili."}), 400
    if not file.filename.lower().endswith(".zip"):
        return jsonify({"ok": False, "error": "Sirf .zip files allowed hain."}), 400

    app_name = re.sub(r"[^A-Za-z0-9_\-]", "_", file.filename.rsplit('.', 1)[0])[:50]
    if not app_name:
        return jsonify({"ok": False, "error": "App ka naam invalid hai."}), 400

    user_dir = safe_join(UPLOAD_FOLDER, user_name, app_name)
    already_exists = os.path.exists(user_dir)
    if already_exists and not overwrite:
        return jsonify({"ok": False, "needs_confirm": True, "error": f"'{app_name}' pehle se maujood hai. Overwrite karna hai?"}), 200

    tmp_zip = os.path.join(BASE_DIR, f"_tmp_{user_name}_{app_name}_{int(time.time())}.zip")
    file.save(tmp_zip)

    if not zipfile.is_zipfile(tmp_zip):
        os.remove(tmp_zip)
        return jsonify({"ok": False, "error": "Ye zip file corrupt hai ya invalid hai, dobara try karo."}), 400

    db = load_db()
    key = (user_name, app_name)
    if key in processes and processes[key].poll() is None:
        stop_app_process(user_name, app_name, db, manual=True)

    if os.path.exists(user_dir):
        shutil.rmtree(user_dir, ignore_errors=True)
    os.makedirs(user_dir, exist_ok=True)
    extract_dir = os.path.join(user_dir, "extracted")

    try:
        with zipfile.ZipFile(tmp_zip, 'r') as zip_ref:
            bad_file = zip_ref.testzip()
            if bad_file:
                raise zipfile.BadZipFile(f"Corrupt entry: {bad_file}")
            for member in zip_ref.namelist():
                member_path = os.path.abspath(os.path.join(extract_dir, member))
                if not member_path.startswith(os.path.abspath(extract_dir)):
                    raise ValueError("Zip me suspicious path mila (path traversal attempt), upload block kiya gaya.")
            zip_ref.extractall(extract_dir)
    except (zipfile.BadZipFile, ValueError) as e:
        shutil.rmtree(user_dir, ignore_errors=True)
        os.remove(tmp_zip)
        return jsonify({"ok": False, "error": str(e)}), 400
    except Exception as e:
        shutil.rmtree(user_dir, ignore_errors=True)
        if os.path.exists(tmp_zip):
            os.remove(tmp_zip)
        return jsonify({"ok": False, "error": f"Extract karte waqt error: {e}"}), 400
    finally:
        if os.path.exists(tmp_zip):
            os.remove(tmp_zip)

    if not os.path.exists(extract_dir) or not os.listdir(extract_dir):
        shutil.rmtree(user_dir, ignore_errors=True)
        return jsonify({"ok": False, "error": "Extraction ke baad koi file nahi mili, zip khali thi shayad."}), 400

    if mark_unlimited:
        settings = get_app_settings(db, user_name, app_name)
        settings["unlimited"] = True
        save_db(db)

    entry, kind = find_entry_file(extract_dir)
    if not entry:
        return jsonify({
            "ok": True,
            "warning": f"Upload ho gaya lekin entry file nahi mili. Inme se ek honi chahiye: {', '.join(ENTRY_FILES_PY + ENTRY_FILES_JS)}",
            "app_name": app_name
        })

    return jsonify({"ok": True, "app_name": app_name, "entry": entry, "kind": kind})

@app.route("/upload", methods=["POST"])
def upload():
    if not require_login():
        return jsonify({"ok": False, "error": "Login required"}), 401
    return _do_upload(current_user_key())

@app.route("/validate/<name>")
def validate_app(name):
    if not require_login():
        return jsonify({"ok": False, "error": "Login required"}), 401
    user_name = current_user_key()
    if not is_safe_component(name):
        return jsonify({"ok": False, "error": "Invalid app name"}), 400
    try:
        _, extract_dir, _ = app_dirs(user_name, name)
    except ValueError:
        return jsonify({"ok": False, "error": "Invalid path"}), 400
    if not os.path.exists(extract_dir):
        return jsonify({"ok": False, "error": "App nahi mili."}), 404
    result = validate_project(extract_dir)
    return jsonify(result)

@app.route("/run/<name>")
def run_app_route(name):
    if not require_login():
        return redirect(url_for("login"))
    user_name = current_user_key()
    if not is_safe_component(name):
        return jsonify({"ok": False, "error": "Invalid app name"}), 400
    db = load_db()
    result = start_app_process(user_name, name, db)
    if request.args.get("json") == "1":
        return jsonify(result)
    return redirect(url_for("index"))

@app.route("/stop/<name>")
def stop_app_route(name):
    if not require_login():
        return redirect(url_for("login"))
    user_name = current_user_key()
    if not is_safe_component(name):
        return jsonify({"ok": False, "error": "Invalid app name"}), 400
    db = load_db()
    stop_app_process(user_name, name, db, manual=True)
    activity.clear_pause(f"{user_name}_{name}")
    if request.args.get("json") == "1":
        return jsonify({"ok": True})
    return redirect(url_for("index"))

@app.route("/restart/<name>")
def restart_app_route(name):
    if not require_login():
        return redirect(url_for("login"))
    user_name = current_user_key()
    if not is_safe_component(name):
        return jsonify({"ok": False, "error": "Invalid app name"}), 400
    db = load_db()
    stop_app_process(user_name, name, db, manual=False)
    time.sleep(0.5)
    result = start_app_process(user_name, name, db)
    if request.args.get("json") == "1":
        return jsonify(result)
    return redirect(url_for("index"))

@app.route("/delete/<name>")
def delete_app_route(name):
    if not require_login():
        return redirect(url_for("login"))
    user_name = current_user_key()
    if not is_safe_component(name):
        return jsonify({"ok": False, "error": "Invalid app name"}), 400
    db = load_db()
    stop_app_process(user_name, name, db, manual=True)
    app_dir, _, _ = app_dirs(user_name, name)
    if os.path.exists(app_dir):
        shutil.rmtree(app_dir, ignore_errors=True)
    venv_dir = venv_path_for(user_name, name)
    if os.path.exists(venv_dir):
        shutil.rmtree(venv_dir, ignore_errors=True)
    key = app_settings_key(user_name, name)
    db.get("app_settings", {}).pop(key, None)
    db.get("start_times", {}).pop(key, None)
    save_db(db)
    return redirect(url_for("index"))

@app.route("/toggle_auto_on/<name>", methods=["POST"])
def toggle_auto_on(name):
    if not require_login():
        return jsonify({"ok": False}), 401
    user_name = current_user_key()
    if not is_safe_component(name):
        return jsonify({"ok": False, "error": "Invalid app name"}), 400
    db = load_db()
    settings = get_app_settings(db, user_name, name)
    settings["auto_on"] = not settings.get("auto_on", False)
    save_db(db)
    return jsonify({"ok": True, "auto_on": settings["auto_on"]})

@app.route("/toggle_auto_restart/<name>", methods=["POST"])
def toggle_auto_restart(name):
    if not require_login():
        return jsonify({"ok": False}), 401
    user_name = current_user_key()
    if not is_safe_component(name):
        return jsonify({"ok": False, "error": "Invalid app name"}), 400
    db = load_db()
    settings = get_app_settings(db, user_name, name)
    settings["auto_restart"] = not settings.get("auto_restart", False)
    save_db(db)
    return jsonify({"ok": True, "auto_restart": settings["auto_restart"]})

@app.route("/get_log/<name>")
def get_log(name):
    if not require_login():
        return jsonify({"log": "", "status": "OFFLINE"}), 401
    user_name = current_user_key()
    if not is_safe_component(name):
        return jsonify({"log": "", "status": "OFFLINE"}), 400
    _, _, log_path = app_dirs(user_name, name)
    log_content = ""
    if os.path.exists(log_path):
        with open(log_path, "r", encoding="utf-8", errors="ignore") as f:
            log_content = f.read()[-4000:]
    p = processes.get((user_name, name))
    db = load_db()
    is_running = bool(p and p.poll() is None)
    settings = get_app_settings(db, user_name, name)
    return jsonify({
        "log": log_content,
        "status": "RUNNING" if is_running else "OFFLINE",
        "start_time": db["start_times"].get(app_settings_key(user_name, name), 0),
        "device": settings.get("device_platform")
    })

@app.route("/download/<name>")
def download_app(name):
    if not require_login():
        return redirect(url_for("login"))
    user_name = current_user_key()
    if not is_safe_component(name):
        return "Invalid app name", 400
    _, extract_dir, _ = app_dirs(user_name, name)
    if not os.path.exists(extract_dir):
        return "App not found", 404
    memory_file = io.BytesIO()
    with zipfile.ZipFile(memory_file, 'w', zipfile.ZIP_DEFLATED) as zf:
        for root, dirs, files in os.walk(extract_dir):
            dirs[:] = [d for d in dirs if d not in ("venv", "__pycache__", "node_modules")]
            for f in files:
                fpath = os.path.join(root, f)
                zf.write(fpath, os.path.relpath(fpath, extract_dir))
    memory_file.seek(0)
    return send_file(memory_file, download_name=f"{name}.zip", as_attachment=True)

# ============================================================
# ROUTES — PUBLIC SHARE LINK (no login needed: view status, start/stop, logs only)
# ============================================================
@app.route("/get_public_link/<name>", methods=["POST"])
def get_public_link(name):
    if not require_login():
        return jsonify({"ok": False}), 401
    if not is_safe_component(name):
        return jsonify({"ok": False, "error": "Invalid name"}), 400
    user_name = current_user_key()
    _, extract_dir, _ = app_dirs(user_name, name)
    if not os.path.exists(extract_dir):
        return jsonify({"ok": False, "error": "App not found"}), 404
    db = load_db()
    token = ensure_public_token(db, user_name, name)
    return jsonify({"ok": True, "token": token, "url": url_for("public_view", token=token, _external=True)})

@app.route("/revoke_public_link/<name>", methods=["POST"])
def revoke_public_link_route(name):
    if not require_login():
        return jsonify({"ok": False}), 401
    if not is_safe_component(name):
        return jsonify({"ok": False, "error": "Invalid name"}), 400
    db = load_db()
    revoke_public_token(db, current_user_key(), name)
    return jsonify({"ok": True})

def _lookup_public_token(token):
    db = load_db()
    tkey = db.get("public_tokens", {}).get(token)
    if not tkey or "_" not in tkey:
        return None, None, None
    user, name = tkey.split("_", 1)
    return db, user, name

@app.route("/public/<token>")
def public_view(token):
    db, user, name = _lookup_public_token(token)
    if not user:
        return render_template_string(PUBLIC_HTML, valid=False, name=None, running=False, token=token)
    p = processes.get((user, name))
    running = bool(p and p.poll() is None)
    return render_template_string(PUBLIC_HTML, valid=True, name=name, running=running, token=token)

@app.route("/public/<token>/status")
def public_status(token):
    db, user, name = _lookup_public_token(token)
    if not user:
        return jsonify({"ok": False, "error": "Invalid or revoked link"}), 404
    p = processes.get((user, name))
    running = bool(p and p.poll() is None)
    _, _, log_path = app_dirs(user, name)
    log_content = ""
    if os.path.exists(log_path):
        with open(log_path, "r", encoding="utf-8", errors="ignore") as f:
            log_content = f.read()[-3000:]
    return jsonify({"ok": True, "running": running, "log": log_content, "name": name})

@app.route("/public/<token>/start", methods=["POST"])
def public_start(token):
    db, user, name = _lookup_public_token(token)
    if not user:
        return jsonify({"ok": False, "error": "Invalid or revoked link"}), 404
    result = start_app_process(user, name, db)
    return jsonify(result)

@app.route("/public/<token>/stop", methods=["POST"])
def public_stop(token):
    db, user, name = _lookup_public_token(token)
    if not user:
        return jsonify({"ok": False, "error": "Invalid or revoked link"}), 404
    stop_app_process(user, name, db, manual=True)
    return jsonify({"ok": True})

# ============================================================
# ROUTES — FILE MANAGER
# ============================================================
@app.route("/list_files/<name>")
def list_files(name):
    if not require_login():
        return jsonify({"files": []}), 401
    user_name = current_user_key()
    if not is_safe_component(name):
        return jsonify({"files": []}), 400
    _, extract_dir, _ = app_dirs(user_name, name)
    files = []
    if os.path.exists(extract_dir):
        for root, dirs, filenames in os.walk(extract_dir):
            dirs[:] = [d for d in dirs if d not in ("venv", "__pycache__", "node_modules", ".git")]
            for f in filenames:
                files.append(os.path.relpath(os.path.join(root, f), extract_dir))
    return jsonify({"files": sorted(files)})

def _resolve_project_file(user_name, project, filename):
    if not is_safe_component(project):
        raise ValueError("Invalid project name")
    _, extract_dir, _ = app_dirs(user_name, project)
    # filename may contain subfolders (relative path) but must not escape extract_dir
    target = os.path.abspath(os.path.join(extract_dir, filename))
    if not target.startswith(os.path.abspath(extract_dir) + os.sep) and target != os.path.abspath(extract_dir):
        raise ValueError("Path traversal blocked")
    return target

@app.route("/read_file", methods=["POST"])
def read_content():
    if not require_login():
        return jsonify({"content": ""}), 401
    data = request.json or {}
    try:
        path = _resolve_project_file(current_user_key(), data.get('project', ''), data.get('filename', ''))
    except ValueError as e:
        return jsonify({"content": "", "error": str(e)}), 400
    if os.path.exists(path) and os.path.isfile(path):
        try:
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                return jsonify({"content": f.read()})
        except Exception as e:
            return jsonify({"content": "", "error": str(e)}), 500
    return jsonify({"content": "", "error": "File not found"}), 404

@app.route("/save_file", methods=["POST"])
def save_content():
    if not require_login():
        return jsonify({"status": "error"}), 401
    data = request.json or {}
    try:
        path = _resolve_project_file(current_user_key(), data.get('project', ''), data.get('filename', ''))
    except ValueError as e:
        return jsonify({"status": "error", "error": str(e)}), 400
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            f.write(data.get('content', ''))
        return jsonify({"status": "success"})
    except Exception as e:
        return jsonify({"status": "error", "error": str(e)}), 500

@app.route("/delete_file", methods=["POST"])
def delete_file_api():
    if not require_login():
        return jsonify({"status": "error"}), 401
    data = request.json or {}
    try:
        path = _resolve_project_file(current_user_key(), data.get('project', ''), data.get('filename', ''))
    except ValueError as e:
        return jsonify({"status": "error", "error": str(e)}), 400
    if os.path.exists(path):
        os.remove(path)
        return jsonify({"status": "deleted"})
    return jsonify({"status": "error", "error": "File not found"}), 404

# ============================================================
# ROUTES — ADMIN
# ============================================================
@app.route("/admin/panel")
def admin_panel():
    if not require_admin():
        return redirect(url_for("admin_login"))
    db = load_db()
    running_count = count_running_global()
    try:
        import psutil
        ram_percent = psutil.virtual_memory().percent
    except Exception:
        ram_percent = "N/A"

    all_apps = []
    admin_apps = []
    if os.path.exists(UPLOAD_FOLDER):
        for user in sorted(os.listdir(UPLOAD_FOLDER)):
            user_dir = os.path.join(UPLOAD_FOLDER, user)
            if not os.path.isdir(user_dir):
                continue
            for name in sorted(os.listdir(user_dir)):
                if not os.path.isdir(os.path.join(user_dir, name)):
                    continue
                p = processes.get((user, name))
                running = bool(p and p.poll() is None)
                settings = get_app_settings(db, user, name)
                entry = {
                    "user": user, "name": name, "running": running,
                    "device": settings.get("device_platform"),
                    "auto_on": settings.get("auto_on"),
                    "auto_restart": settings.get("auto_restart"),
                }
                if user == ADMIN_INTERNAL_ID:
                    admin_apps.append(entry)
                else:
                    all_apps.append(entry)

    users_list = []
    for email, rec in db.get("users", {}).items():
        users_list.append({"email": email, "vip": rec.get("vip", False)})

    return render_template_string(ADMIN_HTML, users=users_list,
                                   config=db.get("config", default_db()["config"]),
                                   running_count=running_count, ram_percent=ram_percent,
                                   all_apps=all_apps, admin_apps=admin_apps)

@app.route("/admin/update_config", methods=["POST"])
def admin_update_config():
    if not require_admin():
        return redirect(url_for("admin_login"))
    db = load_db()
    cfg = db.setdefault("config", {})
    for field, cast in [("max_concurrent_per_user", int), ("max_concurrent_vip", int),
                         ("max_concurrent_global", int),
                         ("sleep_after_hours", float), ("auto_wake_after_minutes", int)]:
        val = request.form.get(field)
        if val is not None:
            try:
                cfg[field] = cast(val)
            except ValueError:
                pass
    save_db(db)
    return redirect(url_for("admin_panel"))

@app.route("/admin/toggle_vip", methods=["POST"])
def admin_toggle_vip():
    if not require_admin():
        return jsonify({"ok": False}), 401
    email = request.form.get("email", "").strip().lower()
    db = load_db()
    if email in db["users"]:
        db["users"][email]["vip"] = not db["users"][email].get("vip", False)
        save_db(db)
        return jsonify({"ok": True, "vip": db["users"][email]["vip"]})
    return jsonify({"ok": False, "error": "User not found"}), 404

@app.route("/admin/change_pw", methods=["POST"])
def change_pw():
    if not require_admin():
        return redirect(url_for("admin_login"))
    email, new_pw = request.form.get("email", "").strip().lower(), request.form.get("new_pw", "").strip()
    db = load_db()
    if email in db["users"] and new_pw:
        db["users"][email]["pw_hash"] = generate_password_hash(new_pw)
        save_db(db)
    return redirect(url_for("admin_panel"))

@app.route("/admin/login_as/<path:email>")
def login_as(email):
    if not require_admin():
        return redirect(url_for("admin_login"))
    db = load_db()
    email = email.strip().lower()
    if email not in db["users"]:
        return redirect(url_for("admin_panel"))
    session['username'], session['is_admin'] = email, False
    session['user_folder'] = user_folder_id(email)
    return redirect(url_for("index"))

@app.route("/admin/upload_admin_app", methods=["POST"])
def admin_upload_app():
    """Admin's own apps get uploaded through the same pipeline as user uploads,
    just stored under the internal admin folder and flagged unlimited (no 4h sleep)."""
    if not require_admin():
        return jsonify({"ok": False, "error": "Login required"}), 401
    return _do_upload(ADMIN_INTERNAL_ID, mark_unlimited=True)

@app.route("/admin/get_public_link/<name>", methods=["POST"])
def admin_get_public_link(name):
    if not require_admin():
        return jsonify({"ok": False}), 401
    if not is_safe_component(name):
        return jsonify({"ok": False, "error": "Invalid name"}), 400
    db = load_db()
    token = ensure_public_token(db, ADMIN_INTERNAL_ID, name)
    return jsonify({"ok": True, "token": token, "url": url_for("public_view", token=token, _external=True)})

if __name__ == "__main__":
    ensure_scheduler()
    port = int(os.environ.get("PORT", 3522))
    app.run(host="0.0.0.0", port=port, debug=False)
