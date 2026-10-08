#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
codex-model-watch —— 本地监控 Codex 的模型使用、额度水位、容量拒单，并主动探测模型偷换。

原理（详见 README）：
  1. 日志侧：Codex 会把每一轮会话写入 ~/.codex/sessions/**/*.jsonl（rollout 文件）。
     本工具无侵入地增量解析这些文件，得到：每个 turn 实际生效的模型（turn_context.model）、
     token 用量（token_usage_record）、时长、容量拒单错误（task_complete.error，例如
     "Selected model is at capacity"）、以及额度水位（token_count.rate_limits 里的
     5h/7d 窗口用量百分比）。
     注意：实测 Codex 会把被偷换后的模型一致化写进日志（请求字段与实际字段相同），
     因此「被偷换成了什么」无法从日志还原 —— 这正是探针存在的意义。
  2. 探针侧：用你本地的 Codex 登录态（~/.codex/auth.json）向
     chatgpt.com/backend-api/codex/responses 发一条最小请求，读取 SSE
     response.created 事件里服务端实际派出的模型，即可即时验证「请求 X 会被派什么」。
     每次探针只消耗极少量额度，可手动触发也可定时执行。
     ⚠ 2026-10 实测：服务端自报模型已不可信（被软换时自报仍为请求模型名），
     快探针只能证明"链路活着"，不能证明"货是真的"。
  3. 深度金丝雀（canary，2026-10 新增）：发一道固定的多步推理题（effort=high），
     测「首字延迟 + 推理深度 + 答案正确性」。真旗舰模型慢而深（TTFT 数秒、
     reasoning 上百 token），被换成的轻量模型秒回浅答。这是目前唯一能识破
     "自报造假型软换"的本地手段（与 BazaarLink 行为指纹同原理）。
     支持直接打中转站（--api-base/--api-key），可监控号池任意入口。

所有数据只存在本机（SQLite），面板为本地网页，没有任何遥测。
"""
import argparse
import glob
import json
import os
import sqlite3
import sys
import threading
import time
import webbrowser
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HOME = os.path.expanduser("~")
APP_DIR = os.path.join(HOME, ".codex-model-watch")
WEB_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "web")
BACKEND_URL = "https://chatgpt.com/backend-api/codex/responses"

g_lock = threading.Lock()
g_last_scan = 0.0
g_state = {"demo": False}


# ---------------------------------------------------------------- db

def db_connect(db_path):
    os.makedirs(os.path.dirname(db_path), exist_ok=True)
    # 单进程多线程，统一用 g_lock 串行化；check_same_thread 关掉以复用连接
    conn = sqlite3.connect(db_path, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    conn.executescript("""
    CREATE TABLE IF NOT EXISTS files(
        path TEXT PRIMARY KEY, offset INTEGER DEFAULT 0, size INTEGER DEFAULT 0,
        mtime REAL DEFAULT 0, lines INTEGER DEFAULT 0);
    CREATE TABLE IF NOT EXISTS turns(
        file TEXT, turn_id TEXT, ts TEXT, session_id TEXT, project TEXT,
        requested TEXT, served TEXT, effort TEXT,
        in_tokens INTEGER DEFAULT 0, cached_tokens INTEGER DEFAULT 0, out_tokens INTEGER DEFAULT 0,
        duration_ms INTEGER, ttft_ms INTEGER,
        error_kind TEXT, error_msg TEXT,
        UNIQUE(file, turn_id));
    CREATE INDEX IF NOT EXISTS idx_turns_ts ON turns(ts);
    CREATE TABLE IF NOT EXISTS quota(
        ts TEXT PRIMARY KEY, primary_used REAL, secondary_used REAL, raw TEXT);
    CREATE TABLE IF NOT EXISTS probes(
        ts TEXT PRIMARY KEY, requested TEXT, served TEXT, swapped INTEGER,
        latency_ms INTEGER, safety_header TEXT, error TEXT);
    CREATE TABLE IF NOT EXISTS threads(
        thread_id TEXT PRIMARY KEY, requested TEXT);
    """)
    # 2026-10 金丝雀列迁移：老库 ALTER 补列（新库 executescript 里没放，统一走这里）
    for ddl in ("ALTER TABLE probes ADD COLUMN ttft_ms INTEGER",
                "ALTER TABLE probes ADD COLUMN reasoning INTEGER",
                "ALTER TABLE probes ADD COLUMN answer TEXT",
                "ALTER TABLE probes ADD COLUMN verdict TEXT"):
        try:
            conn.execute(ddl)
        except sqlite3.OperationalError:
            pass  # 列已存在
    return conn


# ---------------------------------------------------------------- 扫描解析

def iso_now():
    now = datetime.now(timezone.utc).replace(tzinfo=None)
    return now.strftime("%Y-%m-%dT%H:%M:%S.") + "%03dZ" % (now.microsecond // 1000)


def classify_error(msg, info):
    if info:
        if not isinstance(info, str):
            info = json.dumps(info, ensure_ascii=False)
        return info[:60]
    m = (msg or "").lower()
    if "at capacity" in m:
        return "capacity"
    if "rate limit" in m:
        return "rate_limit"
    if "usage limit" in m or "limit reached" in m:
        return "usage_limit"
    return "error"


def parse_lines(lines, file_key, conn, stats):
    """解析一批 rollout 行；返回需写入的行集合。"""
    turns, quota_rows = [], []
    for raw in lines:
        raw = raw.strip()
        if not raw:
            continue
        try:
            obj = json.loads(raw)
        except Exception:
            continue
        ts = obj.get("timestamp") or ""
        t = obj.get("type")
        p = obj.get("payload")
        if not isinstance(p, dict):
            continue
        pt = p.get("type", "")
        if t == "turn_context":
            tid = p.get("turn_id")
            if not tid:
                continue
            collab = p.get("collaboration_mode") or {}
            settings = collab.get("settings") or {}
            requested = settings.get("model") or ""
            served = p.get("model") or ""
            cwd = p.get("cwd") or ""
            project = os.path.basename(cwd.rstrip("\\/")) if cwd else ""
            # turn 行必须遇到就立刻插入：同一文件里 token_usage/task_complete 的 UPDATE 在其后到达
            conn.execute("""INSERT INTO turns(file, turn_id, ts, session_id, project, requested, served, effort)
                            VALUES(?,?,?,?,?,?,?,?)
                            ON CONFLICT(file, turn_id) DO UPDATE SET
                              ts=COALESCE(excluded.ts, turns.ts),
                              project=CASE WHEN excluded.project!='' THEN excluded.project ELSE turns.project END,
                              requested=COALESCE(NULLIF(excluded.requested,''), turns.requested),
                              served=COALESCE(NULLIF(excluded.served,''), turns.served),
                              effort=COALESCE(NULLIF(excluded.effort,''), turns.effort)""",
                         (file_key, tid, ts or None, "", project, requested, served, p.get("effort") or ""))
            stats["turns"] += 1
        elif t == "event_msg" and pt == "thread_settings_applied":
            tid = p.get("thread_id")
            ts_model = ((p.get("thread_settings") or {}).get("model")) or ""
            if tid and ts_model:
                conn.execute("INSERT INTO threads(thread_id, requested) VALUES(?,?) "
                             "ON CONFLICT(thread_id) DO UPDATE SET requested=excluded.requested", (tid, ts_model))
        elif t == "token_usage_record":
            tid = p.get("turn_id")
            usage = p.get("turn_token_usage") or p.get("usage") or {}
            if tid and usage:
                conn.execute("UPDATE turns SET in_tokens=?, cached_tokens=?, out_tokens=? "
                             "WHERE file=? AND turn_id=?",
                             (usage.get("input_tokens") or 0, usage.get("cached_input_tokens") or 0,
                              usage.get("output_tokens") or 0, file_key, tid))
        elif t == "event_msg" and pt == "task_complete":
            tid = p.get("turn_id")
            if not tid:
                continue
            err = p.get("error") or None
            kind = msg = None
            if isinstance(err, dict):
                msg = err.get("message") or ""
                if not isinstance(msg, str):
                    msg = json.dumps(msg, ensure_ascii=False)
                msg = msg[:300]
                kind = classify_error(msg, err.get("codex_error_info"))
            conn.execute("UPDATE turns SET duration_ms=?, ttft_ms=?, error_kind=COALESCE(?,error_kind), "
                         "error_msg=? WHERE file=? AND turn_id=?",
                         (p.get("duration_ms"), p.get("time_to_first_token_ms"), kind, msg, file_key, tid))
            if kind:
                stats["errors"] += 1
        elif t == "event_msg" and pt == "token_count":
            rl = p.get("rate_limits") or {}
            prim = (rl.get("primary") or {}).get("used_percent")
            sec = (rl.get("secondary") or {}).get("used_percent")
            if ts and (prim is not None or sec is not None):
                conn.execute("INSERT INTO quota(ts, primary_used, secondary_used, raw) VALUES(?,?,?,?) "
                             "ON CONFLICT(ts) DO NOTHING", (ts, prim, sec, json.dumps(rl)))


def scan_sessions(conn, codex_home, max_age_days):
    """增量扫描 sessions 目录；返回统计。"""
    sessions_dir = os.path.join(codex_home, "sessions")
    if not os.path.isdir(sessions_dir):
        return {"files": 0, "turns": 0, "errors": 0, "note": "sessions 目录不存在: " + sessions_dir}
    pattern = os.path.join(sessions_dir, "**", "*.jsonl")
    files = glob.glob(pattern, recursive=True)
    cutoff_ts = 0
    if max_age_days > 0:
        cutoff = time.time() - max_age_days * 86400
        cutoff_ts = cutoff
    files = [f for f in files if os.path.getmtime(f) >= cutoff_ts] if max_age_days > 0 else files
    stats = {"files": 0, "turns": 0, "errors": 0}
    for fp in sorted(files):
        try:
            st = os.stat(fp)
        except OSError:
            continue
        row = conn.execute("SELECT offset, mtime, size, lines FROM files WHERE path=?", (fp,)).fetchone()
        # 续读策略：文件被截断/重写则从头解析，否则从上次 offset 续读新增部分
        start, resume, unchanged = 0, False, False
        if row:
            if st.st_size > row["offset"]:
                start, resume = row["offset"], True
            elif st.st_size == row["offset"] and row["mtime"] == st.st_mtime:
                unchanged = True
        if unchanged:
            continue  # 无新内容
        if not resume:
            conn.execute("DELETE FROM turns WHERE file=?", (fp,))
            start = 0
        with open(fp, "rb") as fh:
            fh.seek(start)
            consumed, lines = 0, []
            while True:
                chunk = fh.readline()
                if not chunk:
                    break
                consumed += len(chunk)
                lines.append(chunk)
            # 最后一行可能不完整，回退 offset 到最后一个完整换行
            if lines and not lines[-1].endswith(b"\n"):
                tail = lines.pop()
                consumed -= len(tail)
            if lines:
                text = b"".join(lines).decode("utf-8", errors="replace")
                parse_lines(text.splitlines(), fp, conn, stats)
        old_lines = row["lines"] if (row and resume) else 0
        conn.execute("""INSERT INTO files(path, offset, size, mtime, lines) VALUES(?,?,?,?,?)
                        ON CONFLICT(path) DO UPDATE SET offset=excluded.offset, size=excluded.size,
                          mtime=excluded.mtime, lines=excluded.lines""",
                     (fp, start + consumed, st.st_size, st.st_mtime, old_lines + len(lines)))
        stats["files"] += 1
    conn.commit()
    return stats


# ---------------------------------------------------------------- 探针

def load_auth(codex_home):
    path = os.path.join(codex_home, "auth.json")
    if not os.path.isfile(path):
        return None
    try:
        auth = json.load(open(path, encoding="utf-8"))
        tokens = auth.get("tokens") or {}
        tok = tokens.get("access_token")
        if not tok:
            return None
        return {"token": tok, "account": tokens.get("account_id", "")}
    except Exception:
        return None


def run_probe(codex_home, model):
    import urllib.request
    import urllib.error
    auth = load_auth(codex_home)
    if not auth:
        return {"error": "未找到 Codex 登录态（~/.codex/auth.json），请先用 Codex 登录"}
    body = json.dumps({
        "model": model,
        "instructions": "You are a helpful assistant.",
        "input": [{"type": "message", "role": "user",
                   "content": [{"type": "input_text", "text": "hi"}]}],
        "stream": True, "store": False, "reasoning": {"effort": "low"},
    }).encode()
    req = urllib.request.Request(BACKEND_URL, data=body, method="POST")
    for k, v in [("Authorization", "Bearer " + auth["token"]),
                 ("chatgpt-account-id", auth["account"]),
                 ("Content-Type", "application/json"),
                 ("Accept", "text/event-stream"),
                 ("originator", "codex_cli_rs"),
                 ("User-Agent", "codex_cli_rs/0.154.0")]:
        req.add_header(k, v)
    t0 = time.time()
    served, safety, error = "", "", None
    try:
        resp = urllib.request.urlopen(req, timeout=90)
        safety = resp.headers.get("x-codex-safety-buffering-enabled", "") or ""
        buf = b""
        while True:
            chunk = resp.read(4096)
            if not chunk:
                break
            buf += chunk
            if b"response.created" in buf:
                break
            if len(buf) > 200000:
                break
        text = buf.decode(errors="replace")
        i = text.find('"model":"')
        if i >= 0:
            served = text[i + 9:text.find('"', i + 9)]
        if not served:
            error = "响应里没有找到模型字段"
    except urllib.error.HTTPError as e:
        try:
            detail = e.read(300).decode(errors="replace")
        except Exception:
            detail = ""
        error = "HTTP %d %s" % (e.code, detail[:200])
    except Exception as e:
        error = str(e)[:200]
    latency = int((time.time() - t0) * 1000)
    swapped = 1 if (served and model and served != model) else 0
    row = (iso_now(), model, served, swapped, latency, safety, error)
    conn = db_connect(db_path())
    with g_lock:
        conn.execute("INSERT INTO probes(ts, requested, served, swapped, latency_ms, safety_header, error) "
                     "VALUES(?,?,?,?,?,?,?)", row)
        conn.commit()
    return {"ts": row[0], "requested": model, "served": served, "swapped": bool(swapped),
            "latency_ms": latency, "safety_header": safety, "error": error}


# ---------------------------------------------------------------- 深度金丝雀

# 固定推理题：答案唯一可校验（C(4,3)=4 全偶 + 4*C(5,2)=40 一偶两奇 = 44），
# 换题要同步改 EXPECT_ANSWER。深度判据与题目无关（TTFT + 推理量）。
CANARY_QUESTION = ("袋中有编号 1-9 的九个球（奇数号 5 个、偶数号 4 个）。"
                   "一次性取出 3 个，取法共有多少种使得三球编号之和为偶数？"
                   "先推理，最后一行只写答案数字。")
EXPECT_ANSWER = "44"
# 阈值初版（可按观测校准）：轻量模型的特征是"秒回 + 几乎不推理"。
CANARY_TTFT_SUSPECT_MS = 2500    # 首字快于此视为可疑（真旗舰思考数秒才吐首字）
CANARY_REASON_SUSPECT = 80       # reasoning token 少于此视为可疑

# 自我认知指纹题（2026-10-06 实证：软换后的旧壳会自报旧身份）：
# 实测被换 astra 自称 "OpenAI o3 / cutoff 2024-06 / ctx 114688"，luna 自称 o3-mini。
QS_SELFKNOW = ("Answer in 3 short lines, no preamble: (1) Your exact underlying model name "
               "and version. (2) Your training data cutoff (year-month). "
               "(3) Your maximum context window in tokens.")
LEGACY_NAME_PAT = r"(o1|o3|o4-mini|gpt-4|4o\b)"   # 自报含旧代名 → 旧壳指纹
LEGACY_CUTOFF_PAT = r"20(1[0-9]|2[0-3])"          # cutoff ≤2023-xx → 旧壳指纹（2024-06 为灰区另行加权）

# 知识截止实测（2026-10-08 加入，比自报可靠）：真 2024-06 旧壳答不出截止后的事实，
# 而"自报 cutoff 2024-06"被证实常是幻觉套话（本地真 6.1-sol 也这么自报过）。
# 每条 = (题目, 判对关键词列表, 截止后日期)；答对任一条即证明训练数据 ≥ 该日期。
POSTCUT_FACTS = [
    ("2024年巴黎奥运会中国拿了多少枚金牌？只答数字。", ["40"], "2024-08"),
    ("美国第47任总统是谁（2025年1月就职）？只答姓名。", ["特朗普", "Trump"], "2025-01"),
]


def _post_ask(model, prompt, effort, codex_home, api_base=None, api_key=None, want_reasoning=False):
    """通用单次提问：官方 backend（SSE）或中转站（chat/completions）。
    返回 dict(text, ttft_ms, reasoning, error)。reasoning：官方通道取 reasoning_tokens，
    中转通道取推理字符数（阈值在使用侧放大）。"""
    import urllib.request
    import urllib.error
    import re as _re
    t0 = time.time()
    if api_base:
        url = api_base.rstrip("/") + "/v1/chat/completions"
        body = json.dumps({"model": model, "max_tokens": 3000, "reasoning_effort": effort,
                           "messages": [{"role": "user", "content": prompt}]}).encode()
        req = urllib.request.Request(url, data=body, method="POST")
        req.add_header("Authorization", "Bearer " + (api_key or ""))
        req.add_header("Content-Type", "application/json")
        req.add_header("User-Agent", "codex_cli_rs/0.155.0")
        try:
            resp = urllib.request.urlopen(req, timeout=180)
            raw = resp.read().decode(errors="replace")
            ttft = int((time.time() - t0) * 1000)  # 非流式只能拿总时长当上界
            try:
                d = json.loads(raw)
                msg = (d.get("choices") or [{}])[0].get("message") or {}
                rc = len(str(msg.get("reasoning_content") or msg.get("reasoning") or "")) \
                    if want_reasoning else 0
                return {"text": str(msg.get("content") or "").strip(), "ttft_ms": ttft,
                        "reasoning": rc, "error": None}
            except Exception:
                return {"text": "", "ttft_ms": ttft, "reasoning": 0,
                        "error": "响应解析失败: " + raw[:120]}
        except urllib.error.HTTPError as e:
            return {"text": "", "ttft_ms": None, "reasoning": 0,
                    "error": "HTTP %d %s" % (e.code, e.read(200).decode(errors="replace"))}
        except Exception as e:
            return {"text": "", "ttft_ms": None, "reasoning": 0, "error": str(e)[:200]}
    auth = load_auth(codex_home)
    if not auth:
        return {"text": "", "ttft_ms": None, "reasoning": 0,
                "error": "未找到 Codex 登录态，或改用 --api-base 打中转站"}
    body = json.dumps({
        "model": model, "instructions": "You are a helpful assistant.",
        "input": [{"type": "message", "role": "user",
                   "content": [{"type": "input_text", "text": prompt}]}],
        "stream": True, "store": False, "reasoning": {"effort": effort},
    }).encode()
    req = urllib.request.Request(BACKEND_URL, data=body, method="POST")
    for k, v in [("Authorization", "Bearer " + auth["token"]),
                 ("chatgpt-account-id", auth["account"]),
                 ("Content-Type", "application/json"),
                 ("Accept", "text/event-stream"),
                 ("originator", "codex_cli_rs"),
                 ("User-Agent", "codex_cli_rs/0.154.0")]:
        req.add_header(k, v)
    try:
        resp = urllib.request.urlopen(req, timeout=180)
        buf, got_first = b"", False
        while True:
            chunk = resp.read(2048)
            if not chunk:
                break
            buf += chunk
            if not got_first and (b"response.output_item" in buf or b"delta" in buf):
                got_first, ttft = True, int((time.time() - t0) * 1000)
            if b"response.completed" in buf:
                break
            if len(buf) > 2000000:
                break
        text = buf.decode(errors="replace")
        m = _re.search(r'"reasoning_tokens"\s*:\s*(\d+)', text)
        reasoning = int(m.group(1)) if (m and want_reasoning) else 0
        acc = "".join(_re.findall(r'"delta"\s*:\s*"((?:[^"\\]|\\.)*)"', text))
        # 只反转义常见序列：对 UTF-8 中文整体 unicode_escape 会打乱多字节字符
        for a, b in (("\\n", "\n"), ("\\t", "\t"), ('\\"', '"'), ("\\\\", "\\")):
            acc = acc.replace(a, b)
        return {"text": acc.strip(), "ttft_ms": ttft if got_first else int((time.time() - t0) * 1000),
                "reasoning": reasoning, "error": None}
    except urllib.error.HTTPError as e:
        try:
            detail = e.read(300).decode(errors="replace")
        except Exception:
            detail = ""
        return {"text": "", "ttft_ms": None, "reasoning": 0,
                "error": "HTTP %d %s" % (e.code, detail[:200])}
    except Exception as e:
        return {"text": "", "ttft_ms": None, "reasoning": 0, "error": str(e)[:200]}


def run_canary(model, codex_home, api_base=None, api_key=None):
    """两阶段深度金丝雀：
    ① 自我认知指纹（便宜，effort=low）——旧壳会自报旧身份/cutoff/上下文
      （2026-10-06 实测：被换 astra 自称 o3、cutoff 2024-06、ctx 114688）；
    ② 推理金丝雀（effort=high）——测首字延迟/推理深度/答案。
    任一阶段命中旧壳特征即判 suspect；verdict 带具体命中维度。"""
    import re as _re
    # 阶段 1：身份指纹
    sk = _post_ask(model, QS_SELFKNOW, "low", codex_home, api_base, api_key)
    legacy_hits, sk_text = [], (sk["text"] or "")
    if not sk["error"] and sk_text:
        if _re.search(LEGACY_NAME_PAT, sk_text, _re.I):
            legacy_hits.append("旧身份")
        years = [int(y) for y in _re.findall(r"\b(20\d{2})\b", sk_text)]
        if years and min(years) <= 2024:
            legacy_hits.append("cutoff≤%d" % min(years))
        mc = _re.search(r"(\d[\d,]{4,})\s*tokens", sk_text, _re.I)
        if mc:
            ctx = int(mc.group(1).replace(",", ""))
            if ctx < 200000:
                legacy_hits.append("ctx=%d" % ctx)
    # 阶段 1.5：知识截止实测（自报不可靠的兜底——旧壳真的不知道截止后的事）
    knows_modern = None  # None=没测出，True=知道截止后事实，False=两条都答错
    for q, keys, after in POSTCUT_FACTS:
        kp = _post_ask(model, q, "low", codex_home, api_base, api_key)
        if kp["error"]:
            continue
        if any(k.lower() in (kp["text"] or "").lower() for k in keys):
            knows_modern = True
            break
        if knows_modern is None:
            knows_modern = False
    # 阶段 2：推理金丝雀
    ca = _post_ask(model, CANARY_QUESTION, "high", codex_home, api_base, api_key, want_reasoning=True)
    ttft_ms, reasoning, answer = ca["ttft_ms"], ca["reasoning"], ca["text"]
    error = ca["error"] or sk["error"]
    correct = EXPECT_ANSWER in (answer or "")[-40:]
    if error:
        verdict = "error"
    else:
        fast = (ttft_ms or 0) < CANARY_TTFT_SUSPECT_MS
        # 官方通道有真 reasoning_tokens；中转通道是字符数，阈值放大 5 倍
        shallow = (reasoning or 0) < (CANARY_REASON_SUSPECT * (1 if api_base else 5))
        # 判定 v3：知识实测最硬——知道截止后事实 = 不是旧壳（自报 2024-06 视为幻觉）；
        # 答错全部截止后事实 = 旧壳实锤；没测出时才退回自报指纹。
        if knows_modern is False:
            verdict = "suspect(旧壳实锤:截止后事实全不知)"
        elif knows_modern and legacy_hits:
            # 自报与知识实测矛盾：以知识实测为准，自报降级为幻觉备注
            verdict = "ok" if (not (fast and shallow) and correct) else \
                ("suspect(快而浅)" if (fast and shallow) else "ok+答错" if not correct else "ok")
            verdict += "(自报cutoff为幻觉)"
        elif legacy_hits:
            only_cutoff = legacy_hits == ["cutoff≤2024"]
            if only_cutoff and knows_modern is None:
                # 自报 cutoff 2024-06 已被证实常为幻觉套话；知识实测没测出时不能仅凭自报定罪
                verdict = "unknown(仅自报cutoff≤2024，知识实测未出，不定罪)"
            else:
                verdict = "suspect(旧壳:" + "+".join(legacy_hits) + ")"
        elif knows_modern is None and not _re.findall(r"\b(20\d{2})\b", sk_text):
            verdict = "unknown(指纹与知识实测均未取到)"
        elif fast and shallow:
            verdict = "suspect(快而浅)"
        else:
            verdict = "ok"
        if not correct and "+" not in verdict:
            verdict += "+答错"
    row_ts = iso_now()
    conn_ = db_connect(db_path())
    with g_lock:
        conn_.execute("INSERT INTO probes(ts, requested, served, swapped, latency_ms, safety_header, error, "
                      "ttft_ms, reasoning, answer, verdict) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                      (row_ts, model, model, 0, ttft_ms, "", error, ttft_ms, reasoning,
                       ("自报:" + sk_text.replace("\n", " ")[:60] + " | 答:" + (answer or "")[-40:])[:120],
                       verdict))
        conn_.commit()
    return {"ts": row_ts, "requested": model, "verdict": verdict, "ttft_ms": ttft_ms,
            "reasoning": reasoning, "answer_tail": (answer or "")[-40:],
            "self_report": sk_text[:160], "legacy_hits": legacy_hits,
            "correct": correct, "error": error}


# ---------------------------------------------------------------- 聚合输出

def api_data(conn, days=0):
    cutoff = ""
    if days and days > 0:
        cutoff = (datetime.now(timezone.utc).replace(tzinfo=None) - timedelta(days=days)).strftime("%Y-%m-%dT%H:%M:%SZ")

    def q(sql, args=()):
        return [dict(r) for r in conn.execute(sql, args).fetchall()]

    cov = conn.execute("SELECT MIN(ts) a, MAX(ts) b, COUNT(*) n FROM turns WHERE ts IS NOT NULL").fetchone()
    win = conn.execute("""SELECT COUNT(*) turns,
                                 COALESCE(SUM(in_tokens),0) tin, COALESCE(SUM(out_tokens),0) tout,
                                 COALESCE(SUM(cached_tokens),0) tcached,
                                 SUM(CASE WHEN error_kind IS NOT NULL THEN 1 ELSE 0 END) errors,
                                 SUM(CASE WHEN error_kind IN ('capacity','server_overloaded') THEN 1 ELSE 0 END) capacity,
                                 AVG(duration_ms) avg_dur
                          FROM turns WHERE (?='' OR ts>=?)""", (cutoff, cutoff)).fetchone()
    hourly = q("""SELECT substr(ts,1,13)||':00' bucket, COUNT(*) turns,
                         SUM(CASE WHEN error_kind IS NOT NULL THEN 1 ELSE 0 END) errors
                  FROM turns WHERE ts IS NOT NULL GROUP BY bucket ORDER BY bucket""")
    models = q("""SELECT COALESCE(NULLIF(served,''),'(未知)') model, COUNT(*) turns,
                         COALESCE(SUM(in_tokens),0) tin, COALESCE(SUM(out_tokens),0) tout,
                         AVG(duration_ms) avg_dur,
                         SUM(CASE WHEN error_kind IS NOT NULL THEN 1 ELSE 0 END) errors
                  FROM turns WHERE (?='' OR ts>=?) GROUP BY model ORDER BY turns DESC""", (cutoff, cutoff))
    projects = q("""SELECT COALESCE(NULLIF(project,''),'(未知)') project, COUNT(*) turns,
                           COALESCE(SUM(in_tokens+out_tokens),0) tokens
                    FROM turns WHERE (?='' OR ts>=?) GROUP BY project ORDER BY tokens DESC LIMIT 15""",
                 (cutoff, cutoff))
    errors_recent = q("""SELECT ts, COALESCE(NULLIF(served,''),'(未知)') model, error_kind, error_msg
                         FROM turns WHERE error_kind IS NOT NULL AND (?='' OR ts>=?)
                         ORDER BY ts DESC LIMIT 50""", (cutoff, cutoff))
    quota_latest = q("SELECT * FROM quota ORDER BY ts DESC LIMIT 1")
    quota_hist = q("SELECT ts, primary_used, secondary_used FROM quota ORDER BY ts DESC LIMIT 48")
    probes = q("SELECT * FROM probes ORDER BY ts DESC LIMIT 100")
    probe_summary = conn.execute("""SELECT COUNT(*) n, COALESCE(SUM(swapped),0) swapped,
                                    COALESCE(SUM(CASE WHEN verdict LIKE 'suspect%' THEN 1 ELSE 0 END),0) suspect
                                    FROM probes""").fetchone()
    total_models = sum(m["turns"] for m in models) or 1
    for m in models:
        m["share"] = round(m["turns"] * 100.0 / total_models, 1)
    return {
        "meta": {"generated_at": iso_now(), "demo": g_state["demo"]},
        "coverage": {"first": cov["a"], "last": cov["b"], "turns_total": cov["n"]},
        "summary": {"turns": win["turns"], "tokens_in": win["tin"], "tokens_out": win["tout"],
                    "tokens_cached": win["tcached"], "errors": win["errors"] or 0,
                    "capacity": win["capacity"] or 0,
                    "avg_duration_ms": int(win["avg_dur"] or 0)},
        "hourly": hourly, "models": models, "projects": projects,
        "errors_recent": errors_recent,
        "quota": {"latest": quota_latest[0] if quota_latest else None,
                  "history": list(reversed(quota_hist))},
        "probes": probes,
        "probe_summary": {"total": probe_summary["n"], "swapped": probe_summary["swapped"],
                          "suspect": probe_summary["suspect"]},
    }


# ---------------------------------------------------------------- demo 数据

def seed_demo(conn):
    """生成两周的演示数据（用于 README 截图与功能体验）。"""
    import random
    random.seed(42)
    models = [("gpt-5.6-sol", 0.52), ("gpt-6-astra", 0.24), ("gpt-5.6-terra", 0.12),
              ("gpt-5.6-luna", 0.08), ("codex-auto-review", 0.04)]
    projects = ["my-app", "blog", "data-scripts", "learn-rust"]
    now = datetime.now(timezone.utc)
    turns, quota, probes = [], [], []
    for day in range(13, -1, -1):
        base = now - timedelta(days=day)
        n_turn = random.randint(25, 90)
        # 剧情线：第 5 天起 astra 探针开始被偷换成 luna
        swapped_day = day <= 5
        q5 = max(0.0, min(100.0, 100 - day * random.uniform(6, 14)))
        for i in range(n_turn):
            r = random.random()
            acc = 0.0
            model = models[-1][0]
            for m, w in models:
                acc += w
                if r <= acc:
                    model = m
                    break
            ts = base.replace(hour=random.randint(8, 23), minute=random.randint(0, 59),
                              second=random.randint(0, 59), microsecond=0)
            tin = random.randint(8, 180) * 1000
            tout = random.randint(1, 40) * 100
            err = None
            if random.random() < 0.03:
                err = "capacity" if random.random() < 0.7 else "rate_limit"
            turns.append((("demo-%d-%d" % (day, i)), ts.strftime("%Y-%m-%dT%H:%M:%SZ"),
                          "demo-session", random.choice(projects), model, model, "high",
                          tin, int(tin * 0.3), tout,
                          random.randint(8000, 180000), random.randint(1200, 9000),
                          err, "Selected model is at capacity. Please try a different model." if err == "capacity" else None))
        quota.append((base.strftime("%Y-%m-%dT%H:00:00Z"), round(q5, 1),
                      round(min(100.0, q5 * 2.2), 1), "{}"))
        if day % 2 == 0 or swapped_day:
            for hm in (9, 15, 21):
                ts = base.replace(hour=hm, minute=random.randint(0, 59), second=0, microsecond=0)
                probes.append((ts.strftime("%Y-%m-%dT%H:%M:%SZ"), "gpt-6-astra",
                               "gpt-5.6-luna" if swapped_day else "gpt-6-astra",
                               1 if swapped_day else 0, random.randint(900, 4000),
                               "true" if swapped_day else "", None))
    conn.executemany("""INSERT INTO turns(file, turn_id, ts, session_id, project, requested, served, effort,
                        in_tokens, cached_tokens, out_tokens, duration_ms, ttft_ms, error_kind, error_msg)
                        VALUES('demo', ?,?,?,?,?,?,?,?,?,?,?,?,?,?) ON CONFLICT(file, turn_id) DO NOTHING""",
                     [(t[0],) + t[1:] for t in turns])
    conn.executemany("INSERT INTO quota VALUES(?,?,?,?) ON CONFLICT(ts) DO NOTHING", quota)
    conn.executemany("INSERT INTO probes VALUES(?,?,?,?,?,?,?) ON CONFLICT(ts) DO NOTHING", probes)
    conn.commit()


# ---------------------------------------------------------------- HTTP 服务

WEB_HTML = None


def load_index():
    global WEB_HTML
    if WEB_HTML is None:
        with open(os.path.join(WEB_DIR, "index.html"), "rb") as f:
            WEB_HTML = f.read()
    return WEB_HTML


class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass

    def _json(self, obj, code=200):
        data = json.dumps(obj, ensure_ascii=False).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        import urllib.parse
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        if path in ("/", "/index.html"):
            data = load_index()
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(data)
            return
        if path == "/api/data":
            global g_last_scan
            qs = urllib.parse.parse_qs(parsed.query)
            try:
                days = int((qs.get("days") or ["0"])[0])
            except ValueError:
                days = 0
            with g_lock:
                if not g_state["demo"] and time.time() - g_last_scan > 20:
                    scan_sessions(conn(), g_args.codex_home, g_args.max_age_days)
                    g_last_scan = time.time()
                self._json(api_data(conn(), days))
            return
        self.send_response(404)
        self.end_headers()

    def do_POST(self):
        if self.path.split("?")[0] == "/api/probe":
            length = int(self.headers.get("Content-Length") or 0)
            try:
                body = json.loads(self.rfile.read(length) or b"{}")
            except Exception:
                body = {}
            model = (body.get("model") or "").strip()
            if not model:
                self._json({"error": "缺少 model"}, 400)
                return
            if body.get("canary"):
                result = run_canary(model, g_args.codex_home,
                                    api_base=body.get("api_base") or g_args.api_base,
                                    api_key=body.get("api_key") or g_args.api_key)
            else:
                result = run_probe(g_args.codex_home, model)
            self._json(result)
            return
        self.send_response(404)
        self.end_headers()


# ---------------------------------------------------------------- 入口

conn_inst = None
g_args = None


def conn():
    global conn_inst
    if conn_inst is None:
        conn_inst = db_connect(db_path())
        if g_state["demo"]:
            seed_demo(conn_inst)
    return conn_inst


def db_path():
    return os.path.join(APP_DIR, "demo.db" if g_state["demo"] else "state.db")


def main():
    global g_args, g_last_scan
    ap = argparse.ArgumentParser(description="codex-model-watch —— 本地监控 Codex 模型使用/额度/拒单，并探测模型偷换")
    ap.add_argument("--port", type=int, default=8787, help="本地网页端口（默认 8787）")
    ap.add_argument("--codex-home", default=os.path.join(HOME, ".codex"), help="Codex 主目录（默认 ~/.codex）")
    ap.add_argument("--max-age-days", type=int, default=30, help="只解析最近 N 天的会话日志，0=全部（默认 30）")
    ap.add_argument("--demo", action="store_true", help="使用内置演示数据（不读取真实日志）")
    ap.add_argument("--scan-only", action="store_true", help="只扫描解析并打印摘要，不启动网页")
    ap.add_argument("--no-open", action="store_true", help="启动后不自动打开浏览器")
    ap.add_argument("--api-base", default="", help="金丝雀探针打中转站地址（如 https://api.funyoo.uk），留空用本地官方登录态")
    ap.add_argument("--api-key", default="", help="中转站 API key（配合 --api-base）")
    g_args = ap.parse_args()
    g_state["demo"] = g_args.demo

    conn_ = conn()
    with g_lock:
        if not g_args.demo:
            stats = scan_sessions(conn_, g_args.codex_home, g_args.max_age_days)
        else:
            stats = {"files": 0}
        g_last_scan = time.time()
    n_turn = conn_.execute("SELECT COUNT(*) FROM turns").fetchone()[0]
    n_probe = conn_.execute("SELECT COUNT(*) FROM probes").fetchone()[0]
    print("[codex-model-watch] 已解析 %d 个文件，累计 %d 轮会话、%d 次探针" %
          (stats.get("files", 0), n_turn, n_probe))
    if stats.get("note"):
        print("[codex-model-watch] " + stats["note"])
    if g_args.scan_only:
        top = conn_.execute("""SELECT served, COUNT(*) n FROM turns GROUP BY served
                               ORDER BY n DESC LIMIT 5""").fetchall()
        for r in top:
            print("  %-24s %d 轮" % (r[0], r[1]))
        return

    server = ThreadingHTTPServer(("127.0.0.1", g_args.port), Handler)
    url = "http://127.0.0.1:%d" % g_args.port
    print("[codex-model-watch] 面板地址: %s  （Ctrl+C 退出）" % url)
    if not g_args.no_open:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nbye")


if __name__ == "__main__":
    main()
