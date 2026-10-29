#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
LAN Transfer 2.0 - 局域网文件 / 文字传输工具
Windows  <->  Android / iOS / 其它电脑 ，纯浏览器操作，无需安装 App

设计要点（相比 1.x 的改进）
  1. 上传分块「按偏移直写」到最终文件的临时件，全部到齐只需一次改名 ——
     没有「分块暂存 + 合并时整文件复制」的二次写盘，大文件吞吐翻倍。
  2. 上传 / 下载都是零拷贝流式：请求体直接从 socket 落到磁盘，不经过
     cgi.FieldStorage 的临时文件，也不把整块读进内存。
  3. 断点续传：已上传分块记在 SQLite 会话表里，页面刷新 / 关浏览器 /
     断网 / 手机锁屏之后可以接着传，不必从头再来。
  4. 前端多路并发分块（默认 3~4 路），单流跑不满的 WiFi 也能压满带宽。
  5. 实时进度（速度 / 平均速度 / 剩余时间）、可取消、可重试。
  6. 文件夹递归上传保留目录结构；文件夹下载走标准 zip（流式分片）。
  7. 文字：收发 + 持久化历史 + 搜索 + 一键复制（含安卓 HTTP 降级）+ 剪贴板接收。

依赖：仅标准库（Python 3.8+）。可选安装 psutil 来更完整地列出网卡地址。

用法：
  python server.py                          # 默认端口 9876
  python server.py -p 8080 -d D:\\share      # 自定义端口 / 共享目录
  python server.py --read-only              # 只读（禁止上传 / 删除）
  python server.py --bind 127.0.0.1         # 只允许本机访问（更安全）
"""

from __future__ import annotations

import argparse
import hmac
import io
import json
import mimetypes
import os
import re
import secrets
import shutil
import socket
import sqlite3
import struct
import sys
import threading
import time
import urllib.parse
import uuid
import zipfile
import zlib
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

struct_pack = struct.pack

# ─────────────────────────── 常量 ───────────────────────────

APP_NAME = "LAN Transfer"
VERSION = "2.2"

DEFAULT_PORT = 9876
DEFAULT_DIR = "shared_files"

# 内部数据目录（SQLite），位于共享目录下的同名子目录
STATE_DIRNAME = ".lan_transfer"
INTERNAL_DIR_NAME = STATE_DIRNAME
# 流式读写块大小。1MB 与 NTFS / SSD 的最佳写块一致，再大只是多吃内存。
IO_CHUNK = 1024 * 1024
# 单个上传分块上限（前端最大 64MB 一片，这里留一倍余量）
MAX_CHUNK_BYTES = 128 * 1024 * 1024
# 未完成的落盘文件前缀：以 "." 开头，前端列表与 ZIP 都不会显示它
PART_PREFIX = ".ltmp_"
# 文字单条上限
MAX_TEXT_BYTES = 4 * 1024 * 1024
# 分块暂存区的过期时间（秒），超过且未续传的会话会被清理
STALE_UPLOAD_SECONDS = 7 * 24 * 3600

# ─────────────────────────── 全局状态 ───────────────────────────

# 启动参数（main() 里赋值）
SHARE_DIR = os.path.abspath(DEFAULT_DIR)
STATE_DIR = ""
STAGING_DIR = ""
DB_PATH = ""
READ_ONLY = False
HOST = "0.0.0.0"
PORT = DEFAULT_PORT
AUTH_TOKEN = ""          # 为空表示不校验
ALLOW_OVERWRITE = True   # 同名文件是否覆盖
_deleting: set = set()   # 正在合并的文件绝对路径，防止合并中被人删除
_state_lock = threading.Lock()
_tls = threading.local()  # 线程内复用的 SQLite 连接

_serve_time = time.time()
_stats = {
    "uploaded_files": 0,
    "uploaded_bytes": 0,
    "downloaded_files": 0,
    "downloaded_bytes": 0,
    "texts": 0,
    "errors": 0,
}
_stats_lock = threading.Lock()


# ─────────────────────────── 小工具 ───────────────────────────

def human_size(n: float) -> str:
    """字节数转人类可读字符串（服务端日志用）。"""
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:.1f} {unit}" if unit != "B" else f"{int(n)} B"
        n /= 1024
    return f"{n:.1f} TB"


def is_indexable(name: str) -> bool:
    """内部文件 / 目录是否应被隐藏（不展示、不打包、不可下载）。

    只隐藏服务自己的状态目录；用户的隐藏文件（.git、.DS_Store 等）
    是正常上传内容，照常展示。
    """
    return name == INTERNAL_DIR_NAME or name.startswith(".ltmp_")


def safe_join(base: str, rel: str):
    """
    把外部传入的相对路径安全地拼到 base 下。
    返回 (绝对路径, 规范化相对路径) 或 (None, 错误信息)。
    使用 realpath + 公共前缀判断，避免 startswith('shared_files') 被
    'shared_files_evil' 这类同前缀路径欺骗。
    """
    if rel is None:
        rel = ""
    rel = rel.replace("\\", "/").strip()
    if "\x00" in rel:
        return None, "路径包含非法字符"
    # 去掉盘符 / UNC 前缀，只允许相对路径
    if re.match(r"^[a-zA-Z]:", rel) or rel.startswith("//"):
        return None, "不允许使用绝对路径"
    parts = [p for p in rel.split("/") if p not in ("", ".")]
    for p in parts:
        if p == "..":
            return None, "路径不合法"
        # 只拦截服务内部目录；用户文件/目录以 "." 或 "_" 开头（如 .git、
        # .DS_Store、_cache）是合法的，不应拒绝 —— 否则上传包含它们的
        # 文件夹会整批失败。
        if p == INTERNAL_DIR_NAME:
            return None, "路径不合法"
        if any(ch in p for ch in '<>:"|?*'):
            return None, "路径含非法字符"
    norm = "/".join(parts)
    target = os.path.abspath(os.path.join(base, *parts)) if parts else os.path.abspath(base)
    base_real = os.path.realpath(base)
    target_real = os.path.realpath(target)
    if target_real != base_real and not target_real.startswith(base_real + os.sep):
        return None, "路径越界"
    return target, norm


_WINDOWS_RESERVED = {
    "CON", "PRN", "AUX", "NUL",
    *(f"COM{i}" for i in range(1, 10)),
    *(f"LPT{i}" for i in range(1, 10)),
}


def sanitize_filename(name: str, fallback: str = "unnamed") -> str:
    """清理浏览器传来的文件名（可能是路径）。"""
    name = (name or "").replace("\\", "/").split("/")[-1].strip()
    # 纯点（"..""、"..." 等）不能当文件名；正常隐藏文件（.DS_Store）保留前导点
    if not name.strip("."):
        return fallback
    name = re.sub(r'[<>:"|?*\x00-\x1f]', "_", name)
    # Windows 保留设备名（CON、NUL、COM1…，含带扩展名形式）不能直接当
    # 普通文件创建/删除 —— 会命中设备而非文件，加前缀规避。
    stem = name.split(".")[0].upper()
    if stem in _WINDOWS_RESERVED:
        name = "_" + name
    return name[:200] or fallback


def uniq_path(path: str) -> str:
    """若目标已存在，追加 _1 / _2 … 直到不冲突。"""
    if not os.path.exists(path):
        return path
    base, ext = os.path.splitext(path)
    n = 1
    while os.path.exists(f"{base}_{n}{ext}"):
        n += 1
    return f"{base}_{n}{ext}"


def content_disposition(filename: str, inline: bool = False) -> str:
    """
    生成兼容各浏览器的 Content-Disposition。
    同时给出 ASCII 回退名和 RFC 5987 的 UTF-8 名，中文名不会乱码。
    """
    disp = "inline" if inline else "attachment"
    ascii_name = filename.encode("ascii", "replace").decode("ascii")
    ascii_name = ascii_name.replace('"', "_").replace("\\", "_") or "download"
    quoted = urllib.parse.quote(filename, safe="")
    return f"{disp}; filename=\"{ascii_name}\"; filename*=UTF-8''{quoted}"


def fmt_speed(bps: float) -> str:
    return human_size(bps) + "/s"


# ─────────────────────────── 数据库（会话 / 文字历史 / 传输记录）───────────────────────────

def db() -> sqlite3.Connection:
    """
    每个线程复用一个连接。

    旧实现每次 db() 都新开一个连接、还要重放 3 条 PRAGMA —— 一块分块下来
    要开 3~4 个连接，在 1Gbps 局域网上这是实打实的开销。改成线程内复用后，
    一次连接服务整个 keep-alive 会话。
    """
    conn = getattr(_tls, "conn", None)
    if conn is not None:
        return conn
    conn = sqlite3.connect(DB_PATH, timeout=30, isolation_level=None)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA busy_timeout=15000")
    conn.execute("PRAGMA cache_size=-16384")
    conn.execute("PRAGMA temp_store=MEMORY")
    _tls.conn = conn
    return conn


def init_db() -> None:
    with db() as conn:
        conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS uploads (
                id            TEXT PRIMARY KEY,
                name          TEXT NOT NULL,
                rel_path      TEXT,
                size          INTEGER NOT NULL,
                chunk_size    INTEGER NOT NULL,
                total_chunks  INTEGER NOT NULL,
                mtime         REAL,
                created_at    REAL NOT NULL,
                updated_at    REAL NOT NULL,
                status        TEXT NOT NULL DEFAULT 'active',
                final_path    TEXT
            );
            -- 以「分块内容哈希」为主键：重复上传同一分块天然幂等，
            -- 这正是修复 1.x「缺少分块」bug 的关键。
            CREATE TABLE IF NOT EXISTS chunks (
                upload_id   TEXT NOT NULL,
                idx         INTEGER NOT NULL,
                size        INTEGER NOT NULL,
                sha1        TEXT NOT NULL,
                file        TEXT NOT NULL,
                created_at  REAL NOT NULL,
                PRIMARY KEY (upload_id, idx)
            );
            CREATE TABLE IF NOT EXISTS texts (
                id        TEXT PRIMARY KEY,
                ts        REAL NOT NULL,
                text      TEXT NOT NULL,
                source    TEXT,
                pinned    INTEGER NOT NULL DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS transfers (
                id         TEXT PRIMARY KEY,
                ts         REAL NOT NULL,
                direction  TEXT NOT NULL,
                name       TEXT NOT NULL,
                size       INTEGER NOT NULL,
                seconds    REAL,
                ok         INTEGER NOT NULL DEFAULT 1,
                note       TEXT
            );
            CREATE INDEX IF NOT EXISTS idx_texts_ts ON texts(ts DESC);
            CREATE INDEX IF NOT EXISTS idx_tr_ts ON transfers(ts DESC);
            """
        )


# ─────────────────────────── 会话（断点续传核心）───────────────────────────

def upload_get(upload_id: str):
    with db() as conn:
        row = conn.execute("SELECT * FROM uploads WHERE id=?", (upload_id,)).fetchone()
        return dict(row) if row else None


def upload_dest(rec) -> str:
    """会话对应的最终文件绝对路径。"""
    if rec["rel_path"]:
        dest, _ = safe_join(SHARE_DIR, rec["rel_path"])
        if dest is None:
            raise ValueError("路径不合法")
        return dest
    return os.path.join(SHARE_DIR, sanitize_filename(rec["name"]))


def upload_part_path(rec) -> str:
    """
    上传期间真正落盘的文件：与最终文件同目录（rename 才不会跨卷），
    名字以 ".ltmp_" 开头 —— 文件列表不显示、ZIP 不打包、不可下载。
    """
    dest = upload_dest(rec)
    return os.path.join(os.path.dirname(dest), f"{PART_PREFIX}{rec['id']}.part")


def upload_ensure_part(rec) -> str:
    part = upload_part_path(rec)
    parent = os.path.dirname(part)
    if parent:
        os.makedirs(parent, exist_ok=True)
    if not os.path.isfile(part):
        # 用 O_CREAT（不带 O_TRUNC）建空文件。
        # 不能写 open(part, "wb")：多路并发时两个线程会同时命中「文件不存在」，
        # 后一个的 CREATE_ALWAYS 会在前一个正写作时截断，Windows 上直接
        # 抛 Permission denied / 数据被清零。O_CREAT 谁先建都无害。
        # 另外这里不做 truncate 预分配：NTFS 预分配会把整个文件实写一遍
        # （1GB 约 1.3 秒），而按偏移写入本身不会触发零填充，实测乱序写与
        # 顺序写同为 ~1GB/s。
        try:
            os.close(os.open(part, os.O_CREAT | os.O_RDWR | getattr(os, "O_BINARY", 0), 0o666))
        except FileExistsError:
            pass
        except OSError:
            if not os.path.isfile(part):
                raise
    return part


def chunk_len(rec, idx: int) -> int:
    """第 idx 块应有的字节数（最后一块可能不足 chunk_size）。"""
    start = idx * rec["chunk_size"]
    return max(0, min(rec["chunk_size"], rec["size"] - start))


def upload_create(name, rel_path, size, chunk_size, total_chunks, mtime):
    """新建上传会话；若同名同大小同 chunk_size 的会话已存在，直接复用（断点续传）。"""
    now = time.time()
    with db() as conn:
        row = conn.execute(
            """SELECT * FROM uploads
               WHERE name=? AND IFNULL(rel_path,'')=IFNULL(?,'') AND size=?
                 AND chunk_size=? AND status='active'
               ORDER BY updated_at DESC LIMIT 1""",
            (name, rel_path, size, chunk_size),
        ).fetchone()
        if row:
            return dict(row)
        uid = uuid.uuid4().hex
        conn.execute(
            """INSERT INTO uploads
               (id,name,rel_path,size,chunk_size,total_chunks,mtime,created_at,updated_at,status)
               VALUES (?,?,?,?,?,?,?,?,?,'active')""",
            (uid, name, rel_path, size, chunk_size, total_chunks, mtime, now, now),
        )
        return upload_get(uid)


def chunk_receive(rec, idx: int, rfile, length: int) -> int:
    """
    把一个分块从 socket 直接流到最终文件的对应偏移。

    旧实现走 cgi.FieldStorage：先写系统临时目录 → 再整块读回内存 → 再写暂存
    目录 → 还要 fsync，一块数据落盘三次、内存里再复制两次。现在是「读一块、
    写一块」，内存只有 1MB 滚动缓冲，磁盘只写一次。
    """
    part = upload_ensure_part(rec)
    offset = idx * rec["chunk_size"]
    remaining = length
    buf = bytearray(IO_CHUNK)
    view = memoryview(buf)
    readinto = rfile.readinto
    with open(part, "r+b") as f:
        f.seek(offset)
        while remaining > 0:
            n = readinto(view[:IO_CHUNK if remaining > IO_CHUNK else remaining])
            if not n:
                raise ConnectionError("连接中断，分块未传完")
            f.write(view[:n])
            remaining -= n

    now = time.time()
    with db() as conn:
        conn.execute(
            """INSERT INTO chunks (upload_id,idx,size,sha1,file,created_at)
               VALUES (?,?,?,?,?,?)
               ON CONFLICT(upload_id,idx) DO UPDATE SET
                 size=excluded.size, created_at=excluded.created_at""",
            (rec["id"], idx, length, "", "", now),
        )
        conn.execute("UPDATE uploads SET updated_at=? WHERE id=?", (now, rec["id"]))
    return length


def upload_merge(upload_id: str):
    """
    收尾：校验分块齐全 → fsync → 改名。

    因为分块是直接按偏移写进最终文件的临时件，这一步没有整文件复制 ——
    10GB 的文件也是毫秒级完成（旧实现要再读+写一遍 10GB）。
    返回 (rel_path, size)。
    """
    rec = upload_get(upload_id)
    if not rec:
        raise FileNotFoundError("上传会话不存在")

    dest = upload_dest(rec)
    part = upload_part_path(rec)

    with db() as conn:
        rows = conn.execute(
            "SELECT idx FROM chunks WHERE upload_id=?", (upload_id,)
        ).fetchall()
    have = {r["idx"] for r in rows}
    missing = [i for i in range(rec["total_chunks"]) if i not in have]
    if missing:
        raise ValueError(f"缺少分块 {missing[:5]}{'...' if len(missing) > 5 else ''}")
    if not os.path.isfile(part):
        raise ValueError("临时文件已丢失，请重新选择该文件上传")
    if os.path.getsize(part) < rec["size"]:
        raise ValueError("数据不完整，请重新上传该文件")

    os.makedirs(os.path.dirname(dest), exist_ok=True)
    final = dest if ALLOW_OVERWRITE else uniq_path(dest)

    with _state_lock:
        _deleting.add(os.path.abspath(final))
    try:
        # 整个文件只刷一次盘。分块阶段不做 fsync —— 每 32MB 强制落盘一次
        # 会把顺序写打成同步写，实测能吃掉一半带宽。
        with open(part, "r+b") as f:
            os.fsync(f.fileno())
        if os.path.exists(final):
            try:
                os.remove(final)
            except OSError:
                final = uniq_path(final)
        os.replace(part, final)
    finally:
        with _state_lock:
            _deleting.discard(os.path.abspath(final))

    size = os.path.getsize(final)
    rel = os.path.relpath(final, SHARE_DIR).replace("\\", "/")

    with db() as conn:
        conn.execute(
            "UPDATE uploads SET status='done', final_path=?, updated_at=? WHERE id=?",
            (rel, time.time(), upload_id),
        )
        conn.execute(
            "INSERT INTO transfers (id,ts,direction,name,size,seconds,ok,note)"
            " VALUES (?,?,?,?,?,?,1,?)",
            (uuid.uuid4().hex, time.time(), "up", rel, size, None, "分块上传"),
        )
        conn.execute("DELETE FROM chunks WHERE upload_id=?", (upload_id,))

    with _stats_lock:
        _stats["uploaded_files"] += 1
        _stats["uploaded_bytes"] += size

    return rel, size


def upload_cancel(upload_id: str) -> None:
    rec = upload_get(upload_id)
    if not rec:
        return
    try:
        part = upload_part_path(rec)
    except Exception:
        part = ""
    with db() as conn:
        conn.execute("DELETE FROM chunks WHERE upload_id=?", (upload_id,))
        conn.execute("DELETE FROM uploads WHERE id=?", (upload_id,))
    if part:
        try:
            os.remove(part)
        except OSError:
            pass


def cleanup_stale() -> int:
    """清理长时间未续传的会话、遗留的 .part 和旧版本暂存分块。"""
    cutoff = time.time() - STALE_UPLOAD_SECONDS
    removed = 0
    with db() as conn:
        rows = conn.execute(
            "SELECT id FROM uploads WHERE status='active' AND updated_at < ?",
            (cutoff,),
        ).fetchall()
    for r in rows:
        upload_cancel(r["id"])
        removed += 1

    # 1.x / 2.0 遗留的内容哈希暂存分块
    try:
        for n in os.listdir(STAGING_DIR):
            p = os.path.join(STAGING_DIR, n)
            try:
                if os.path.getmtime(p) < cutoff:
                    os.remove(p)
                    removed += 1
            except OSError:
                pass
    except OSError:
        pass

    # 没有任何活动会话引用的 .ltmp_*.part（进程被强杀 / 磁盘写满等）
    alive = set()
    with db() as conn:
        for r in conn.execute("SELECT * FROM uploads WHERE status='active'"):
            try:
                alive.add(os.path.abspath(upload_part_path(dict(r))))
            except Exception:
                pass
    for root, dirs, files in os.walk(SHARE_DIR):
        dirs[:] = [d for d in dirs if d != INTERNAL_DIR_NAME]
        for fn in files:
            if not (fn.startswith(PART_PREFIX) and fn.endswith(".part")):
                continue
            p = os.path.abspath(os.path.join(root, fn))
            if p in alive:
                continue
            try:
                if os.path.getmtime(p) < cutoff:
                    os.remove(p)
                    removed += 1
            except OSError:
                pass
    return removed


# ─────────────────────────── 文字历史 ───────────────────────────

def text_add(text: str) -> dict:
    item = {
        "id": uuid.uuid4().hex[:12],
        "ts": time.time(),
        "text": text,
    }
    with db() as conn:
        conn.execute(
            "INSERT INTO texts (id,ts,text,source) VALUES (?,?,?,?)",
            (item["id"], item["ts"], text, "web"),
        )
    with _stats_lock:
        _stats["texts"] += 1
    return item


# ─────────────────────────── 目录打包（分片 ZIP，流式）───────────────────────────

def _crc_of_file(path: str) -> int:
    crc = 0
    with open(path, "rb") as f:
        while True:
            buf = f.read(IO_CHUNK)
            if not buf:
                break
            crc = zlib.crc32(buf, crc)
    return crc & 0xFFFFFFFF


def _dir_info(arcname: str) -> zipfile.ZipInfo:
    zi = zipfile.ZipInfo(arcname)
    zi.compress_type = zipfile.ZIP_STORED
    zi.external_attr = (0o40755 << 16) | 0x10
    zi.CRC = 0
    zi.file_size = 0
    zi.compress_size = 0
    return zi


def _file_info(arcname: str, st) -> zipfile.ZipInfo:
    zi = zipfile.ZipInfo(arcname, date_time=time.localtime(st.st_mtime)[:6])
    zi.compress_type = zipfile.ZIP_STORED
    zi.external_attr = (st.st_mode & 0xFFFF) << 16
    zi.file_size = st.st_size
    zi.compress_size = st.st_size
    return zi


def iter_folder_zip(folder_abs: str, root_name: str):
    """
    流式打包目录为 ZIP，可以边生成边发送。

    做法：ZIP_STORED（不压缩）+ 事先算好 CRC 与长度，local header 里就能写
    完整的 CRC/size，因此不需要 data descriptor，也不需要把文件读进内存。
    目录总表（central directory）最后一次性输出，那时各条目偏移已知。

    内存占用：O(条目数)，与文件大小无关。
    """
    base_real = os.path.realpath(folder_abs)
    dir_entries: list = []      # 目录条目
    file_entries: list = []     # (arcname, abspath, ZipInfo)

    for root, dirs, files in os.walk(base_real):
        dirs[:] = sorted(d for d in dirs if not is_indexable(d))
        rel_root = os.path.relpath(root, base_real)
        if rel_root != ".":
            arc = root_name + "/" + rel_root.replace("\\", "/") + "/"
            dir_entries.append((arc, _dir_info(arc)))
        for fn in sorted(files):
            if is_indexable(fn) or ".ltmp_" in fn:
                continue
            full = os.path.join(root, fn)
            rel = os.path.relpath(full, base_real).replace("\\", "/")
            arc = f"{root_name}/{rel}"
            try:
                st = os.stat(full)
            except OSError:
                continue
            file_entries.append((arc, full, _file_info(arc, st)))

    out = io.BytesIO()
    # 已写出的累计字节数（用于计算 local header 的绝对偏移，跨 flush 也准确）
    written = 0

    def flush():
        nonlocal written
        data = out.getvalue()
        if data:
            out.seek(0)
            out.truncate(0)
            written += len(data)
            return data
        return b""

    central: list = []

    def emit_local(zi: zipfile.ZipInfo, data: bytes):
        """手写 local file header + 数据，替换 zipfile 内部写法（便于流式）。"""
        zi.header_offset = written + out.tell()
        name = zi.filename.encode("utf-8")
        # local file header: 30 字节固定部分 + 文件名
        hdr = struct_pack(
            "<IHHHHHIIIHH",
            0x04034B50,                        # signature  PK\x03\x04
            20,                                # version needed
            0x0800,                            # flags: bit11 = 文件名是 UTF-8
            zi.compress_type,                  # method
            zi.date_time[3],                   # mod time (HHMMSS)
            zi.date_time[4],                   # mod date (YMD)
            zi.CRC,
            zi.compress_size,
            zi.file_size,
            len(name),                         # filename length
            0,                                 # extra length
        )
        out.write(hdr)
        out.write(name)
        if data:
            out.write(data)
        central.append(zi)

    # ── 逐个写 local header + 内容 ──
    for arc, zi in dir_entries:
        emit_local(zi, b"")
        yield flush()

    for arc, full, zi in file_entries:
        zi.CRC = _crc_of_file(full)
        emit_local(zi, b"")          # local header（CRC/size 已就绪）
        yield flush()
        with open(full, "rb") as src:
            while True:
                buf = src.read(IO_CHUNK)
                if not buf:
                    break
                out.write(buf)
                yield flush()

    # ── central directory ──
    cd_start = written + out.tell()
    for zi in central:
        name = zi.filename.encode("utf-8")
        # central directory header: 46 字节固定部分 + 文件名
        out.write(struct_pack(
            "<IHHHHHHIIIHHHHHII",
            0x02014B50,                        # signature  PK\x01\x02
            20,                                # version made by
            20,                                # version needed
            0x0800,                            # flags: bit11 = 文件名是 UTF-8
            zi.compress_type,                  # method
            zi.date_time[3],                   # mod time
            zi.date_time[4],                   # mod date
            zi.CRC,
            zi.compress_size,
            zi.file_size,
            len(name),                         # filename length
            0,                                 # extra length
            0,                                 # comment length
            0,                                 # disk number start
            0,                                 # internal attrs
            zi.external_attr,                  # external attrs
            zi.header_offset,                  # local header offset
        ))
        out.write(name)
    cd_size = written + out.tell() - cd_start
    # ── end of central directory ──
    out.write(struct_pack(
        "<IHHHHIIH",
        0x06054B50,                            # signature  PK\x05\x06
        0, 0,                                  # disk numbers
        len(central), len(central),
        cd_size, cd_start,
        0,                                     # comment length
    ))
    yield flush()


# ─────────────────────────── 前端页面 ───────────────────────────

HTML_PAGE = r"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no">
<meta name="theme-color" content="#f5f6f8">
<title>LAN Transfer</title>
<style>
  :root{
    --bg:#f5f6f8; --card:#ffffff; --card2:#f0f2f5; --line:#e3e6ea;
    --text:#1f2328; --text2:#6b7280; --brand:#2563eb; --brand2:#1d4ed8;
    --ok:#0f9d58; --okbg:#e7f6ed; --err:#d93025; --errbg:#fdecea;
    --warn:#b45309; --radius:14px; --shadow:0 1px 3px rgba(16,24,40,.07),0 1px 2px rgba(16,24,40,.04);
  }
  @media (prefers-color-scheme:dark){
    :root{
      --bg:#14161a; --card:#1c1f24; --card2:#23272d; --line:#31353c;
      --text:#e8eaed; --text2:#9aa1ab; --brand:#5b8ef7; --brand2:#4a7de8;
      --ok:#5cc98a; --okbg:#16301f; --err:#ff8a80; --errbg:#3a1a18;
      --warn:#e0a94a; --shadow:0 1px 3px rgba(0,0,0,.4);
    }
  }
  *{margin:0;padding:0;box-sizing:border-box;-webkit-tap-highlight-color:transparent}
  body{
    font-family:-apple-system,BlinkMacSystemFont,'Segoe UI','PingFang SC','Microsoft YaHei',Roboto,sans-serif;
    background:var(--bg);color:var(--text);min-height:100vh;padding:14px;
    font-size:15px;line-height:1.5;-webkit-text-size-adjust:100%;
  }
  .wrap{max-width:760px;margin:0 auto}
  header{display:flex;align-items:center;gap:10px;padding:4px 2px 14px}
  header .logo{font-size:1.5em}
  header h1{font-size:1.15em;font-weight:650;letter-spacing:.2px}
  header .ver{font-size:.72em;color:var(--text2);border:1px solid var(--line);padding:1px 6px;border-radius:6px}
  .card{background:var(--card);border:1px solid var(--line);border-radius:var(--radius);box-shadow:var(--shadow);padding:14px;margin-bottom:12px}
  .addr{display:flex;gap:8px;align-items:center;font-size:.85em;color:var(--text2);flex-wrap:wrap}
  .addr code{background:var(--card2);border:1px solid var(--line);border-radius:8px;padding:4px 9px;color:var(--text);font-size:.95em;user-select:all;font-family:ui-monospace,Menlo,Consolas,monospace}
  .tabs{display:flex;gap:8px;background:var(--card2);padding:4px;border-radius:12px;margin-bottom:12px}
  .tabs button{flex:1;padding:9px;border:0;background:transparent;color:var(--text2);font-size:.93em;font-weight:520;border-radius:9px;cursor:pointer;transition:.15s}
  .tabs button.active{background:var(--card);color:var(--text);box-shadow:var(--shadow)}
  .panel{display:none}.panel.active{display:block}
  textarea{width:100%;min-height:150px;padding:12px;border:1px solid var(--line);border-radius:12px;background:var(--card);color:var(--text);font:inherit;resize:vertical;outline:none;line-height:1.6}
  textarea:focus{border-color:var(--brand)}
  .row{display:flex;gap:8px;flex-wrap:wrap;margin-top:10px}
  button.b{padding:9px 18px;border:0;border-radius:10px;background:var(--brand);color:#fff;font-size:.92em;font-weight:520;cursor:pointer;transition:.15s}
  button.b:hover{background:var(--brand2)}button.b:active{transform:scale(.98)}
  button.b:disabled{opacity:.45;cursor:not-allowed}
  button.g{background:var(--card);color:var(--text);border:1px solid var(--line)}
  button.g:hover{background:var(--card2);border-color:var(--brand)}
  button.d{background:transparent;color:var(--err);border:1px solid var(--line)}
  button.d:hover{border-color:var(--err);background:var(--errbg)}
  button.xs{padding:5px 11px;font-size:.82em;border-radius:8px}
  .box{margin-top:12px;padding:12px;background:var(--card2);border:1px solid var(--line);border-radius:12px;white-space:pre-wrap;word-break:break-word;font-size:.92em;line-height:1.65}
  .hint{font-size:.8em;color:var(--text2);margin-top:8px}
  .drop{border:2px dashed var(--line);border-radius:var(--radius);padding:34px 16px;text-align:center;cursor:pointer;background:var(--card);transition:.2s}
  .drop:hover,.drop.over{border-color:var(--brand);background:var(--card2)}
  .drop .ic{font-size:2.2em;margin-bottom:6px}
  .drop p{color:var(--text2);font-size:.88em}
  .drop p.s{font-size:.78em;margin-top:4px}
  input[type=file]{display:none}
  .list{margin-top:10px}
  .item{display:flex;align-items:center;gap:10px;padding:10px 12px;background:var(--card);border:1px solid var(--line);border-radius:12px;margin-bottom:8px}
  .item+.item{margin-top:0}
  .item .nm{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:.92em}
  .item .sz{color:var(--text2);font-size:.79em;white-space:nowrap}
  .item a,button.act{padding:6px 13px;border:0;border-radius:9px;background:var(--brand);color:#fff;font-size:.83em;cursor:pointer;text-decoration:none;white-space:nowrap;display:inline-block}
  .item a:hover,button.act:hover{background:var(--brand2)}
  .item .rm{padding:6px 10px;background:transparent;border:1px solid var(--line);color:var(--text2);border-radius:9px;cursor:pointer;font-size:.83em}
  .item .rm:hover{color:var(--err);border-color:var(--err);background:var(--errbg)}
  .item.dir{cursor:pointer}.item.dir:hover{border-color:var(--brand)}
  .item.dir .nm{color:var(--brand);font-weight:520}
  .crumbs{display:flex;align-items:center;gap:2px;flex-wrap:wrap;font-size:.85em;padding:8px 10px;background:var(--card2);border:1px solid var(--line);border-radius:10px;margin-bottom:8px}
  .crumbs a{color:var(--brand);cursor:pointer;padding:2px 7px;border-radius:6px;text-decoration:none}
  .crumbs a:hover{background:var(--card)}
  .crumbs .sep{color:var(--text2)}
  .crumbs .cur{color:var(--text);font-weight:550;padding:2px 7px}
  .prog{margin-top:12px;display:none}
  .prog.on{display:block}
  .bar{height:8px;background:var(--card2);border-radius:5px;overflow:hidden;border:1px solid var(--line)}
  .bar i{display:block;height:100%;width:0;background:linear-gradient(90deg,var(--brand),#7aa5fb);transition:width .18s;border-radius:5px}
  .ptxt{font-size:.79em;color:var(--text2);margin-top:6px;display:flex;justify-content:space-between;gap:8px}
  .msg{margin-top:10px;padding:9px 12px;border-radius:10px;font-size:.86em;display:none}
  .msg.on{display:block}
  .msg.ok{background:var(--okbg);color:var(--ok)}
  .msg.err{background:var(--errbg);color:var(--err)}
  .msg.warn{background:var(--card2);color:var(--warn)}
  .fdetail{border:1px solid var(--errbg);border-radius:10px;padding:6px 10px;max-height:220px;overflow-y:auto;background:var(--card2)}
  .fdetail .fd-title{font-size:.82em;font-weight:600;opacity:.75;margin:4px 0 2px}
  .fdetail .fd-item{font-size:.82em;padding:5px 2px;border-bottom:1px solid var(--line);word-break:break-all}
  .fdetail .fd-item:last-child{border-bottom:none}
  .fdetail .fd-item .why{color:var(--err);display:block;margin-top:2px}
  .fdetail .fd-item .fn{font-weight:600}
  .scroll{max-height:340px;overflow-y:auto}
  .hitem{padding:10px 12px;background:var(--card);border:1px solid var(--line);border-radius:12px;margin-bottom:8px}
  .hitem .t{font-size:.73em;color:var(--text2);margin-bottom:5px;display:flex;justify-content:space-between;gap:8px}
  .hitem .x{font-size:.9em;line-height:1.55;white-space:pre-wrap;word-break:break-word;user-select:all}
  .empty{color:var(--text2);font-size:.88em;padding:14px 4px;text-align:center}
  .toast{position:fixed;left:50%;bottom:26px;transform:translateX(-50%) translateY(10px);background:#22262c;color:#fff;padding:10px 20px;border-radius:12px;font-size:.88em;opacity:0;transition:.22s;pointer-events:none;z-index:99;max-width:88vw;text-align:center}
  .toast.on{opacity:1;transform:translateX(-50%) translateY(0)}
  .spin{display:inline-block;width:13px;height:13px;border:2px solid var(--line);border-top-color:var(--brand);border-radius:50%;animation:sp .7s linear infinite;vertical-align:-2px}
  @keyframes sp{to{transform:rotate(360deg)}}
  .hidden{display:none}
  .flexbetween{display:flex;justify-content:space-between;align-items:center;gap:8px;flex-wrap:wrap}
  h3{font-size:.98em;font-weight:620}
  @media (max-width:480px){
    body{padding:10px;font-size:14.5px}
    .card{padding:12px}
    .item{padding:9px 10px;gap:8px}
    button.b{padding:8px 14px}
  }
</style>
</head>
<body>
<div class="wrap">
  <header>
    <span class="logo">📡</span>
    <h1>LAN Transfer</h1>
    <span class="ver">v__VERSION__</span>
  </header>

  <div class="card">
    <div class="addr">
      <span>继续接入地址</span>
      <code id="addr">…</code>
      <button class="b g xs" onclick="copy(location.href)">复制</button>
    </div>
    <div class="hint" id="statLine"></div>
  </div>

  <div class="tabs">
    <button class="active" onclick="tab('text',this)">📝 文字</button>
    <button onclick="tab('files',this)">📁 文件</button>
    <button onclick="tab('hist',this)">🕘 记录</button>
  </div>

  <!-- ═══ 文字 ═══ -->
  <div class="panel active" id="p-text">
    <div class="card">
      <textarea id="tin" placeholder="输入要传的文字，也可以在手机上复制好内容后点「读取剪贴板」…"></textarea>
      <div class="row">
        <button class="b" onclick="sendText()">发送</button>
        <button class="b g" onclick="readClip()">📋 读取剪贴板</button>
        <button class="b g" onclick="getLatest()">📥 获取最新</button>
      </div>
      <div class="msg" id="tmsg"></div>
      <div class="box hidden" id="tres"></div>
    </div>
  </div>

  <!-- ═══ 文件 ═══ -->
  <div class="panel" id="p-files">
    <div class="card">
      <div class="drop" id="drop">
        <div class="ic">📤</div>
        <p>点击选择文件，或把文件拖进来</p>
        <p class="s">支持多选 / 超大文件 · 自动分块 · 断点续传</p>
      </div>
      <input type="file" id="fin" multiple>
      <input type="file" id="fdin" webkitdirectory directory multiple>
      <div class="row">
        <button class="b g" onclick="document.getElementById('fdin').click()">📁 上传文件夹</button>
        <button class="b g" onclick="document.getElementById('fin').click()">📄 选择文件</button>
      </div>
      <div class="prog" id="prog">
        <div class="bar"><i id="fill"></i></div>
        <div class="ptxt"><span id="pl"></span><span id="pr"></span></div>
        <div class="row">
          <button class="b d xs" onclick="cancelUpload()">取消本次</button>
        </div>
      </div>
      <div class="msg" id="fmsg"></div>
      <div id="fdetail" style="display:none;margin-top:8px"></div>
    </div>

    <div class="card">
      <div class="flexbetween">
        <h3>📂 共享文件</h3>
        <div class="row" style="margin:0">
          <button class="b g xs" onclick="load()">🔄 刷新</button>
        </div>
      </div>
      <div class="crumbs hidden" id="crumb"></div>
      <div class="list" id="flist"><div class="empty">加载中…</div></div>
    </div>
  </div>

  <!-- ═══ 记录 ═══ -->
  <div class="panel" id="p-hist">
    <div class="card">
      <h3>📜 文字历史</h3>
      <div class="row">
        <button class="b g xs" onclick="loadHistory()">🔄 刷新</button>
        <button class="b d xs" onclick="clearHistory()">🗑️ 清空</button>
      </div>
      <div class="list scroll" id="hlist"><div class="empty">暂无历史</div></div>
    </div>
  </div>
</div>
<div class="toast" id="toast"></div>

<script>
const $=function(s){return document.querySelector(s)};
const API='';
const TOKEN=__TOKEN_JSON__;
let curPath='';
let upCtl={abort:null,running:false};

/* ── 基础 ── */
function toast(m,ms){ms=ms||2300;const t=$('#toast');t.textContent=m;t.classList.add('on');clearTimeout(t._h);t._h=setTimeout(function(){t.classList.remove('on')},ms)}
function esc(s){return String(s==null?'':s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;').replace(/'/g,'&#39;')}
function unesc(s){return String(s||'').replace(/&amp;/g,'&').replace(/&lt;/g,'<').replace(/&gt;/g,'>').replace(/&quot;/g,'"').replace(/&#39;/g,"'")}
function size(b){b=Number(b)||0;if(b<1024)return b+' B';if(b<1048576)return(b/1024).toFixed(1)+' KB';if(b<1073741824)return(b/1048576).toFixed(1)+' MB';return(b/1073741824).toFixed(2)+' GB'}
function secs(s){s=Math.max(0,Math.round(s||0));if(s<60)return s+' 秒';if(s<3600)return Math.floor(s/60)+' 分 '+(s%60)+' 秒';return Math.floor(s/3600)+' 时 '+Math.floor(s%3600/60)+' 分'}
function hdrs(extra){const h=Object.assign({},extra||{});if(TOKEN)h['X-Auth-Token']=TOKEN;return h}
function msg(el,cls,text){const e=typeof el==='string'?$(el):el;e.className='msg on '+cls;e.textContent=text}
function hidMsg(el){const e=typeof el==='string'?$(el):el;e.className='msg'}

function tab(name,btn){
  ['text','files','hist'].forEach(function(n){
    $('#p-'+n).classList.toggle('active',n===name);
  });
  [].forEach.call(document.querySelectorAll('.tabs button'),function(b){b.classList.remove('active')});
  if(btn)btn.classList.add('active');
  if(name==='files')load();
  if(name==='hist')loadHistory();
}

/* ── 剪贴板：兼容安卓 HTTP（无 clipboard API 时降级 execCommand）── */
async function copy(text){
  try{
    if(navigator.clipboard&&navigator.clipboard.writeText&&window.isSecureContext){
      await navigator.clipboard.writeText(text);toast('已复制');return;
    }
  }catch(e){}
  const ta=document.createElement('textarea');
  ta.value=text;ta.setAttribute('readonly','');
  ta.style.cssText='position:fixed;top:0;left:0;opacity:0;';
  document.body.appendChild(ta);ta.select();ta.setSelectionRange(0,ta.value.length);
  try{document.execCommand('copy');toast('已复制')}catch(e){toast('复制失败，请长按手动复制')}
  document.body.removeChild(ta);
}
async function readClip(){
  try{
    if(navigator.clipboard&&navigator.clipboard.readText&&window.isSecureContext){
      const t=await navigator.clipboard.readText();$('#tin').value=t;toast('已读取剪贴板');return;
    }
  }catch(e){}
  toast('当前环境不允许自动读取，请长按输入框粘贴');
  $('#tin').focus();
}
function unescAttr(el,attr){return unesc(el.getAttribute(attr))}

/* ── 文字 ── */
async function sendText(){
  const t=$('#tin').value;
  if(!t.trim()){msg('#tmsg','warn','请输入内容');return}
  try{
    const r=await fetch(API+'/api/text',{method:'POST',headers:hdrs({'Content-Type':'application/json'}),body:JSON.stringify({text:t})});
    const j=await r.json();
    if(!r.ok||!j.ok)throw new Error(j.error||('HTTP '+r.status));
    hidMsg('#tmsg');toast('已发送');$('#tin').value='';
  }catch(e){msg('#tmsg','err','发送失败：'+e.message)}
}
async function getLatest(){
  try{
    const r=await fetch(API+'/api/text/latest',{headers:hdrs()});
    const j=await r.json();
    const box=$('#tres');box.classList.remove('hidden');
    if(!j.text){box.innerHTML='<span style="color:var(--text2)">（暂无文字）</span>';return}
    box.innerHTML='<div style="color:var(--text2);font-size:.78em;margin-bottom:6px">最新文字 · '+size(new Blob([j.text]).size)+'</div>'
      +'<div style="user-select:all">'+esc(j.text)+'</div>'
      +'<div class="row"><button class="b g xs" onclick="copyText(this)">📋 复制</button></div>';
    box.querySelector('button')._t=j.text;
    toast('已获取');
  }catch(e){msg('#tmsg','err','获取失败：'+e.message)}
}
function copyText(btn){copy(btn._t||'')}

/* ── 文字历史 ── */
async function loadHistory(){
  const l=$('#hlist');
  try{
    const r=await fetch(API+'/api/text/history',{headers:hdrs()});
    const items=await r.json();
    if(!items.length){l.innerHTML='<div class="empty">暂无历史</div>';return}
    l.innerHTML=items.map(function(it){
      const txt=it.text||'';
      const long=txt.length>240;
      return '<div class="hitem"><div class="t"><span>'+new Date(it.ts*1000).toLocaleString()+' · '+esc(size(new Blob([txt]).size))+'</span></div>'
        +'<div class="x" data-full="'+esc(txt)+'" data-short="'+esc(long?txt.slice(0,240)+'…':txt)+'">'+esc(long?txt.slice(0,240)+'…':txt)+'</div>'
        +'<div class="row">'
        +'<button class="b g xs" onclick="copy(unescAttr(this,\'data-t\'))" data-t="'+esc(txt)+'">📋 复制</button>'
        +(long?'<button class="b g xs" onclick="expand(this)">展开</button>':'')
        +'<button class="b g xs" onclick="fill(this)" data-t="'+esc(txt)+'">填入输入框</button>'
        +'<button class="b d xs" onclick="delOne(\''+esc(it.id)+'\')">删除</button>'
        +'</div></div>';
    }).join('');
  }catch(e){l.innerHTML='<div class="empty" style="color:var(--err)">加载失败</div>'}
}
function expand(btn){
  const box=btn.parentNode.parentNode.querySelector('.x');
  const on=box.dataset.open==='1';
  box.textContent=on?unescAttr(box,'data-short'):unescAttr(box,'data-full');
  box.dataset.open=on?'0':'1';
  btn.textContent=on?'展开':'收起';
}
function fill(btn){$('#tin').value=unescAttr(btn,'data-t');toast('已填入输入框');tab('text',document.querySelectorAll('.tabs button')[0])}
async function delOne(id){
  if(!confirm('删除这条记录？'))return;
  await fetch(API+'/api/text/history/'+encodeURIComponent(id),{method:'DELETE',headers:hdrs()});
  toast('已删除');loadHistory();
}
async function clearHistory(){
  if(!confirm('清空全部文字历史？'))return;
  await fetch(API+'/api/text/history',{method:'DELETE',headers:hdrs()});
  toast('已清空');loadHistory();
}

/* ── 文件列表 ── */
function navigate(p){curPath=p||'';load()}
function crumb(){
  const c=$('#crumb');
  if(!curPath){c.classList.add('hidden');return}
  c.classList.remove('hidden');
  const parts=curPath.split('/').filter(Boolean);
  let html='<a onclick="navigate(\'\')">🏠 根目录</a>',built='';
  for(let i=0;i<parts.length;i++){
    built+=(i?'/':'')+parts[i];
    if(i<parts.length-1){html+='<span class="sep">/</span><a onclick="navigate(\''+esc(built)+'\')">'+esc(parts[i])+'</a>'}
    else{html+='<span class="sep">/</span><span class="cur">'+esc(parts[i])+'</span>'}
  }
  c.innerHTML=html;
}
async function load(){
  crumb();
  const l=$('#flist');
  try{
    let url=API+'/api/files';
    if(curPath)url+='?path='+encodeURIComponent(curPath);
    const r=await fetch(url,{headers:hdrs()});
    const files=await r.json();
    if(!Array.isArray(files))throw new Error(files.error||'返回异常');
    if(!files.length&&!curPath){l.innerHTML='<div class="empty">还没有共享文件，先上传一个吧</div>';return}
    let html='';
    if(curPath){
      const parent=curPath.indexOf('/')>=0?curPath.slice(0,curPath.lastIndexOf('/')):'';
      html+='<div class="item dir" onclick="navigate(\''+esc(parent)+'\')"><span class="nm">⬅️ 返回上一级</span><span class="sz"></span></div>';
    }
    html+=files.map(function(f){
      const full=curPath?curPath+'/'+f.name:f.name;
      if(f.isDir){
        return '<div class="item dir" onclick="navigate(\''+esc(full)+'\')">'
          +'<span class="nm">📁 '+esc(f.name)+'</span><span class="sz">'+(f.count!=null?f.count+' 项':'')+'</span>'
          +'<button class="act" onclick="event.stopPropagation();zipDl(\''+esc(full)+'\')">📦 ZIP</button>'
          +'<button class="rm" onclick="event.stopPropagation();delItem(\''+esc(full)+'\',true)">✕</button></div>';
      }
      return '<div class="item"><span class="nm">📄 '+esc(f.name)+'</span><span class="sz">'+esc(size(f.size))+'</span>'
        +'<a href="'+API+'/api/download/'+encodeURIComponent(full)+'" download>下载</a>'
        +'<button class="rm" onclick="delItem(\''+esc(full)+'\',false)">✕</button></div>';
    }).join('');
    l.innerHTML=html;
  }catch(e){l.innerHTML='<div class="empty" style="color:var(--err)">加载失败：'+esc(e.message)+'</div>'}
}
async function delItem(path,isDir){
  if(!confirm('删除「'+path+'」'+(isDir?' 及其中全部内容':'')+'？'))return;
  const r=await fetch(API+'/api/delete/'+encodeURIComponent(path)+(isDir?'?folder=1':''),{method:'DELETE',headers:hdrs()});
  const j=await r.json().catch(function(){return{}});
  if(r.ok&&j.ok){toast('已删除');load()}else{toast('删除失败：'+(j.error||r.status),3000)}
}
function zipDl(path){
  toast('正在打包，请稍候…',4000);
  const a=document.createElement('a');
  a.href=API+'/api/zip/'+encodeURIComponent(path);
  a.download=path.split('/').pop()+'.zip';
  document.body.appendChild(a);a.click();document.body.removeChild(a);
}

/* ── 拖拽 ── */
const drop=$('#drop');
['dragenter','dragover'].forEach(function(ev){drop.addEventListener(ev,function(e){e.preventDefault();drop.classList.add('over')})});
['dragleave','drop'].forEach(function(ev){drop.addEventListener(ev,function(e){e.preventDefault();drop.classList.remove('over')})});
drop.addEventListener('drop',function(e){if(e.dataTransfer.files.length)upload([].slice.call(e.dataTransfer.files))});
$('#fin').addEventListener('change',function(){if(this.files.length)upload([].slice.call(this.files));this.value=''});
$('#fdin').addEventListener('change',function(){if(this.files.length)upload([].slice.call(this.files));this.value=''});

/* ── 上传（分块 + 断点续传）── */
function cancelUpload(){if(upCtl.abort)upCtl.abort();toast('已取消')}

async function upload(files){
  if(upCtl.running){toast('已有传输进行中');return}
  upCtl.running=true;
  const prog=$('#prog');prog.classList.add('on');
  const fill=$('#fill'),pl=$('#pl'),pr=$('#pr');
  const detail=$('#fdetail');
  const total=files.length;
  let okCount=0;
  const failures=[];   // {name, why}

  function renderFailures(){
    if(!failures.length){detail.style.display='none';detail.innerHTML='';return}
    detail.style.display='block';
    detail.innerHTML='<div class="fdetail">'
      +'<div class="fd-title">失败明细（'+failures.length+' 个）</div>'
      +failures.map(function(f){
        return '<div class="fd-item"><span class="fn">📄 '+esc(f.name)+'</span>'
          +'<span class="why">原因：'+esc(f.why)+'</span></div>';
      }).join('')+'</div>';
  }

  for(let n=0;n<total;n++){
    const file=files[n];
    const rel=file.webkitRelativePath||'';
    const label='['+(n+1)+'/'+total+'] '+rel;
    let aborted=false;
    upCtl.abort=function(){aborted=true};

    try{
      await uploadOne(file,label,fill,pl,pr,function(){return aborted});
      okCount++;
      // 该文件此前若失败过（重传场景），从失败列表里移除
      const fi=failures.findIndex(function(f){return f.name===(rel||file.name)});
      if(fi>=0){failures.splice(fi,1);renderFailures()}
    }catch(e){
      failures.push({name:(rel||file.name),why:e.message});
      renderFailures();
      msg('#fmsg','err','❌ '+label+' 失败：'+e.message);
    }
    if(aborted){msg('#fmsg','warn','已取消，'+okCount+' 个文件已完成（未完成的可稍后重传，会自动续传）');break}
  }

  upCtl.running=false;upCtl.abort=null;
  setTimeout(function(){prog.classList.remove('on')},900);
  if(!failures.length&&okCount){
    msg('#fmsg','ok','✅ 全部完成，共 '+okCount+' 个文件');
    setTimeout(function(){detail.style.display='none'},1500);
  }else if(failures.length){
    msg('#fmsg','err','完成 '+okCount+' 个，失败 '+failures.length+' 个（明细见下方列表）');
  }
  load();
}

function uploadOne(file,label,fill,pl,pr,isAborted){
  // 分块策略：≤8MB 整传，否则 32MB 一片（原来 16MB）。片越大，每块的
  // JSON 往返、开文件、记账等固定开销摊得越薄。
  const SMALL=8*1024*1024;
  const CHUNK=32*1024*1024;
  const isSmall=file.size<=SMALL;
  const name=file.name;
  const rel=file.webkitRelativePath||'';
  const chunkSize=isSmall?Math.max(file.size,1):CHUNK;
  const totalChunks=isSmall?1:Math.ceil(file.size/CHUNK);
  // 并发路数：单条 TCP 流在 WiFi 上经常只跑到链路的一半（丢包把拥塞窗口
  // 压住），3~4 路并发能明显压满带宽；有线千兆下多路也不会更慢。
  const PAR=isSmall?1:(file.size>=256*1024*1024?4:3);
  const startTime=Date.now();
  let bytesDone=0;
  let uploadId=null;
  // ── 速度统计状态（setBar/onAck 共用，必须声明在 uploadOne 顶层，
  //    否则 setBar 引用不到会抛 ReferenceError: sessionStart is not defined）
  let sessionBytes=0,sessionStart=0,curSpeed=0;   // 服务端确认字节 / 首次确认时刻 / 平滑速度
  let lastAckTick=0,lastAcked=0;
  let ackedBase=0;                                // 续传时服务端已有字节的基数

  function setBar(done,totalBytes,speed,eta){
    const pct=totalBytes>0?Math.min(100,done/totalBytes*100):0;
    fill.style.width=pct.toFixed(1)+'%';
    pl.textContent=label+' · '+size(done)+' / '+size(totalBytes)+' ('+pct.toFixed(1)+'%)';
    let right='';
    if(speed>0)right=fmtSpeed(speed);
    if(eta>0&&eta<86400)right+=(right?' · ':'')+'剩 '+secs(eta);
    // 均速只用「服务端已确认」的字节 —— 否则续传时会把之前已传的算进来虚高
    if(sessionStart>0&&speed>0){
      const avg=sessionBytes/((Date.now()-sessionStart)/1000);
      if(avg>0)right+=(right?' · ':'')+'均 '+fmtSpeed(avg);
    }
    pr.textContent=right;
  }
  function fmtSpeed(bps){
    if(bps<1024)return bps.toFixed(0)+' B/s';
    if(bps<1048576)return(bps/1024).toFixed(1)+' KB/s';
    return(bps/1048576).toFixed(1)+' MB/s';
  }

  return new Promise(function(resolve,reject){
    let settled=false,finished=false,inflight=0,nextIdx=0;
    const todo=[];                 // 待传分块序号（续传时已剔除服务端已有的）
    const live=[];                 // 在途 xhr，取消时统一 abort
    const loaded={};               // 各在途请求已写出字节，仅用于进度条平滑

    function removeLive(x){
      const i=live.indexOf(x);if(i>=0)live.splice(i,1);
    }
    function abortAll(){
      for(let i=0;i<live.length;i++){try{live[i].abort()}catch(e){}}
      live.length=0;
    }
    function fail(e){
      if(settled)return;
      settled=true;finished=true;abortAll();reject(e);
    }
    function done(){
      if(settled)return;
      settled=true;finished=true;resolve();
    }

    // ── 速度统计只基于「服务端已确认收到」的字节 ──
    // xhr.upload.onprogress 统计的是浏览器写入本机 socket 缓冲区的字节，
    // 局域网上 TCP 缓冲会让它比服务端实际接收快 30%~50% —— 那正是
    // 「显示 90 多 MB/s、实际只有 60 多」的原因。分块 onload（服务端
    // 已落盘并应答）才是真实速度。
    function onAck(n){
      sessionBytes+=n;
      const now=Date.now();
      if(!sessionStart)sessionStart=now;
      if(lastAckTick){
        const dt=(now-lastAckTick)/1000;
        if(dt>=0.20){
          const inst=(sessionBytes+ackedBase-lastAcked)/dt;
          curSpeed=curSpeed?curSpeed*0.6+inst*0.4:inst;
          lastAckTick=now;lastAcked=sessionBytes+ackedBase;
        }
      }else{
        lastAckTick=now;lastAcked=sessionBytes+ackedBase;
      }
    }

    // 进度条用「已确认 + 在途已写出」更顺滑；速度/剩余时间只用已确认字节
    function paint(){
      if(!finished&&!settled&&isAborted()){fail(new Error('已取消'));return}
      let cur=bytesDone;
      for(const k in loaded)cur+=loaded[k];
      if(cur>file.size)cur=file.size;
      const remain=file.size-bytesDone;
      setBar(cur,file.size,curSpeed,curSpeed>0?remain/curSpeed:0);
    }

    function sendChunk(ci){
      const start=ci*chunkSize;
      const end=Math.min(start+chunkSize,file.size);
      const len=end-start;
      // 直接 send(Blob)，不经过 FormData / arrayBuffer / crypto.subtle。
      // crypto.subtle 只在安全上下文（HTTPS / localhost）可用，手机用
      // http://192.168.x.x 访问时它是 undefined —— 那正是「电脑能传、
      // 手机必失败」的原因。RequestBody 由浏览器直接从磁盘流式发出。
      const xhr=new XMLHttpRequest();
      live.push(xhr);inflight++;
      xhr.open('POST',API+'/api/upload/chunk?uploadId='+encodeURIComponent(uploadId)+'&index='+ci);
      xhr.setRequestHeader('Content-Type','application/octet-stream');
      if(TOKEN)xhr.setRequestHeader('X-Auth-Token',TOKEN);
      xhr.onload=function(){
        inflight--;removeLive(xhr);delete loaded[ci];
        if(xhr.status!==200){
          let em='HTTP '+xhr.status;
          try{em=JSON.parse(xhr.responseText).error||em}catch(e){}
          return fail(new Error('分块 '+(ci+1)+'/'+totalChunks+' 失败：'+em));
        }
        bytesDone+=len;onAck(len);paint();pump();
      };
      xhr.onerror=function(){
        inflight--;removeLive(xhr);delete loaded[ci];
        fail(new Error('网络中断或无法连接服务端（已传部分会保留，重新选择该文件可续传）'));
      };
      xhr.upload.onprogress=function(e){
        if(e.lengthComputable){loaded[ci]=e.loaded;paint()}
      };
      xhr.send(file.slice(start,end));
    }

    function pump(){
      if(finished||settled)return;
      if(isAborted()){fail(new Error('已取消'));return}
      while(inflight<PAR&&nextIdx<todo.length)sendChunk(todo[nextIdx++]);
      if(nextIdx>=todo.length&&inflight===0)doMerge();
    }

    function doMerge(){
      if(finished||settled)return;
      finished=true;
      fetch(API+'/api/upload/merge',{
        method:'POST',headers:hdrs({'Content-Type':'application/json'}),
        body:JSON.stringify({uploadId:uploadId})
      }).then(function(r){return r.json().then(function(j){return{r:r,j:j}})}).then(function(o){
        if(!o.r.ok||!o.j.ok)throw new Error(o.j.error||'收尾失败');
        fill.style.width='100%';
        pl.textContent=label+' · 完成';
        const dur=(Date.now()-(sessionStart||startTime))/1000;
        const avg=sessionBytes>0&&dur>0?sessionBytes/dur:file.size/((Date.now()-startTime)/1000);
        pr.textContent=size(file.size)+' · 平均 '+fmtSpeed(avg);
        done();
      }).catch(fail);
    }

    // 1) 建立（或复用）上传会话 → 拿到已传分块列表，实现续传
    fetch(API+'/api/upload/init',{
      method:'POST',headers:hdrs({'Content-Type':'application/json'}),
      body:JSON.stringify({name:name,relPath:rel,size:file.size,chunkSize:chunkSize,totalChunks:totalChunks,mtime:file.lastModified/1000})
    }).then(function(r){
      // HTTP 层错误也要给出可读信息，避免只显示 "失败" 却查不出原因
      if(!r.ok&&r.headers.get('Content-Type')&&r.headers.get('Content-Type').indexOf('json')>=0){
        return r.json().then(function(j){throw new Error(j.error||('HTTP '+r.status))});
      }
      if(!r.ok)throw new Error('服务端返回 HTTP '+r.status);
      return r.json();
    }).then(function(j){
      if(!j.ok)throw new Error(j.error||'初始化失败');
      uploadId=j.uploadId;
      const have={};(j.have||[]).forEach(function(i){have[i]=1});
      bytesDone=j.uploaded||0;
      if(j.done){done();return}
      ackedBase=bytesDone;
      setBar(bytesDone,file.size,0,0);

      for(let i=0;i<totalChunks;i++)if(!have[i])todo.push(i);
      if(!todo.length){doMerge();return}
      pump();
    }).catch(fail);
  });
}
</script>
</body>
</html>
"""


# ─────────────────────────── HTTP 处理 ───────────────────────────

class Handler(BaseHTTPRequestHandler):
    server_version = f"LANTransfer/{VERSION}"
    protocol_version = "HTTP/1.1"
    # 会话内多路并发时，Nagle 会让小响应（每次分块应答几百字节）等到
    # 下一个 ACK 才发，前端看到的「每一块都慢半拍」就是这么来的。
    disable_nagle_algorithm = True

    # ---- 日志 ----
    def log_message(self, fmt, *args):
        try:
            sys.stderr.write(f"  {self.address_string()} {fmt % args}\n")
        except Exception:
            pass

    # ---- 基础响应 ----
    def _cors(self):
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET,POST,DELETE,OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type,X-Auth-Token")
        self.send_header("Access-Control-Max-Age", "86400")

    def json_out(self, data, status=200):
        body = json.dumps(data, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self._cors()
        self.end_headers()
        try:
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def text_out(self, text, status=200, ctype="text/html; charset=utf-8"):
        body = text.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self._cors()
        self.end_headers()
        try:
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def err(self, message, status=400):
        self.json_out({"ok": False, "error": message}, status)

    def q(self):
        p = urllib.parse.urlparse(self.path)
        return p.path, dict(urllib.parse.parse_qsl(p.query))

    def body_json(self):
        n = int(self.headers.get("Content-Length") or 0)
        if n <= 0:
            return {}
        if n > MAX_TEXT_BYTES:
            raise ValueError("请求体过大")
        raw = self.rfile.read(n)
        try:
            return json.loads(raw.decode("utf-8"))
        except Exception:
            return {}

    def auth_ok(self) -> bool:
        if not AUTH_TOKEN:
            return True
        tok = self.headers.get("X-Auth-Token") or ""
        if not tok:
            _, qs = self.q()
            tok = qs.get("token", "")
        return hmac.compare_digest(tok, AUTH_TOKEN)

    def guard(self, write: bool = False) -> bool:
        """返回 True 表示已拒绝该请求。"""
        if not self.auth_ok():
            self.err("访问令牌无效", 401)
            return True
        if write and READ_ONLY:
            self.err("服务处于只读模式，禁止上传 / 删除", 403)
            return True
        return False

    # ---- OPTIONS ----
    def do_OPTIONS(self):
        self.send_response(204)
        self._cors()
        self.send_header("Content-Length", "0")
        self.end_headers()

    # ---- GET ----
    def do_GET(self):
        path, qs = self.q()

        if path in ("/", "/index.html"):
            page = (HTML_PAGE
                    .replace("__VERSION__", VERSION)
                    .replace("__TOKEN_JSON__", json.dumps(AUTH_TOKEN)))
            self.text_out(page)
            return

        if self.guard():
            return

        try:
            if path == "/api/text/latest":
                self._text_latest()
            elif path == "/api/text/history":
                self._text_history()
            elif path == "/api/files":
                self._files(qs)
            elif path == "/api/stat":
                self.json_out(self._stat())
            elif path.startswith("/api/download/"):
                self._download(path)
            elif path.startswith("/api/zip/"):
                self._zip(path)
            else:
                self.err("接口不存在", 404)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:
            with _stats_lock:
                _stats["errors"] += 1
            self.err(f"服务器错误：{e}", 500)

    # ---- 各接口实现 ----
    def _text_latest(self):
        with db() as conn:
            row = conn.execute(
                "SELECT text FROM texts ORDER BY ts DESC LIMIT 1"
            ).fetchone()
        self.json_out({"ok": True, "text": row["text"] if row else ""})

    def _text_history(self):
        _, qs = self.q()
        limit = min(int(qs.get("limit", 100)), 500)
        with db() as conn:
            rows = conn.execute(
                "SELECT id,ts,text FROM texts ORDER BY ts DESC LIMIT ?", (limit,)
            ).fetchall()
        self.json_out([dict(r) for r in rows])

    def _files(self, qs):
        sub = qs.get("path", "")
        target, norm = safe_join(SHARE_DIR, sub)
        if target is None:
            return self.err(norm, 400)
        if not os.path.isdir(target):
            return self.err("目录不存在", 404)

        out = []
        try:
            names = sorted(os.listdir(target), key=lambda s: s.lower())
        except OSError as e:
            return self.err(f"无法读取目录：{e}", 500)

        for n in names:
            if is_indexable(n):
                continue
            full = os.path.join(target, n)
            try:
                if os.path.isdir(full):
                    try:
                        cnt = len([x for x in os.listdir(full) if not is_indexable(x)])
                    except OSError:
                        cnt = None
                    out.append({"name": n, "isDir": True, "size": 0, "count": cnt})
                elif os.path.isfile(full):
                    out.append({"name": n, "isDir": False,
                                "size": os.path.getsize(full)})
            except OSError:
                continue
        # 目录在前，文件在后
        out.sort(key=lambda x: (not x["isDir"], x["name"].lower()))
        self.json_out(out)

    def _stat(self):
        with _stats_lock:
            s = dict(_stats)
        with db() as conn:
            s["texts"] = conn.execute("SELECT COUNT(*) c FROM texts").fetchone()["c"]
            s["sessions"] = conn.execute(
                "SELECT COUNT(*) c FROM uploads WHERE status='active'"
            ).fetchone()["c"]
        s["uptime"] = int(time.time() - _serve_time)
        s["version"] = VERSION
        s["read_only"] = READ_ONLY
        self.json_out({"ok": True, "stat": s})

    def _download(self, path):
        rel = urllib.parse.unquote(path[len("/api/download/"):])
        target, norm = safe_join(SHARE_DIR, rel)
        if target is None:
            return self.err(norm, 400)
        if not os.path.isfile(target):
            return self.err("文件不存在", 404)

        with _state_lock:
            busy = os.path.abspath(target) in _deleting
        size = os.path.getsize(target)
        ctype = mimetypes.guess_type(target)[0] or "application/octet-stream"
        inline = urllib.parse.parse_qs(
            urllib.parse.urlparse(self.path).query
        ).get("inline", ["0"])[0] == "1"

        rng = self.headers.get("Range")
        start, end = 0, size - 1
        partial = False
        if rng and rng.startswith("bytes=") and size > 0:
            spec = rng[6:].split(",")[0].strip()
            try:
                a, _, b = spec.partition("-")
                if a:
                    start = int(a)
                    end = int(b) if b else size - 1
                else:  # 后缀范围 bytes=-N
                    start = max(0, size - int(b))
                    end = size - 1
                if start > end or start >= size:
                    raise ValueError
                partial = True
            except Exception:
                start, end, partial = 0, size - 1, False

        length = end - start + 1
        self.send_response(206 if partial else 200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(length))
        self.send_header("Content-Disposition", content_disposition(os.path.basename(target), inline))
        self.send_header("Accept-Ranges", "bytes")
        if partial:
            self.send_header("Content-Range", f"bytes {start}-{end}/{size}")
        self.send_header("Cache-Control", "no-store")
        self._cors()
        self.end_headers()

        # 用 readinto + 复用缓冲发送：避免每次 read 都新建 1MB 对象，
        # 几十 GB 的下载下 GC 压力也是实打实的。
        sent = 0
        buf = bytearray(IO_CHUNK)
        view = memoryview(buf)
        write = self.wfile.write
        with open(target, "rb", buffering=0) as f:
            if start:
                f.seek(start)
            readinto = f.readinto
            while sent < length:
                want = IO_CHUNK if length - sent > IO_CHUNK else length - sent
                n = readinto(view[:want])
                if not n:
                    break
                write(view[:n])
                sent += n
        with _stats_lock:
            _stats["downloaded_files"] += 1
            _stats["downloaded_bytes"] += sent

    def _zip(self, path):
        rel = urllib.parse.unquote(path[len("/api/zip/"):])
        target, norm = safe_join(SHARE_DIR, rel)
        if target is None:
            return self.err(norm, 400)
        if not os.path.isdir(target):
            return self.err("文件夹不存在", 404)

        root_name = os.path.basename(target.rstrip("/\\")) or "folder"
        # ZIP_STORED 无法预知尺寸 → 用 chunked 传输编码流式发送
        self.send_response(200)
        self.send_header("Content-Type", "application/zip")
        self.send_header("Content-Disposition", content_disposition(root_name + ".zip"))
        self.send_header("Cache-Control", "no-store")
        self.send_header("Transfer-Encoding", "chunked")
        self._cors()
        self.end_headers()

        try:
            for piece in iter_folder_zip(target, root_name):
                if not piece:
                    continue
                self.wfile.write(f"{len(piece):X}\r\n".encode())
                self.wfile.write(piece)
                self.wfile.write(b"\r\n")
            self.wfile.write(b"0\r\n\r\n")
        except (BrokenPipeError, ConnectionResetError):
            self.close_connection = True
            return
        with _stats_lock:
            _stats["downloaded_files"] += 1

    # ---- POST ----
    def do_POST(self):
        if self.guard(write=True):
            return
        path, _ = self.q()
        try:
            if path == "/api/text":
                self._text_add()
            elif path == "/api/upload/init":
                self._upload_init()
            elif path == "/api/upload/chunk":
                self._upload_chunk()
            elif path == "/api/upload/merge":
                self._upload_merge()
            elif path == "/api/upload/cancel":
                self._upload_cancel()
            else:
                self.err("接口不存在", 404)
        except (BrokenPipeError, ConnectionResetError):
            self.close_connection = True
        except Exception as e:
            with _stats_lock:
                _stats["errors"] += 1
            # 出错时请求体大概率没读完。keep-alive 连接上残留的字节会被
            # 当成下一个请求行解析（日志里表现为「Bad request version」），
            # 因此直接结束这条连接，让浏览器重连，别串包。
            self.close_connection = True
            self.err(f"服务器错误：{e}", 500)

    def _text_add(self):
        data = self.body_json()
        text = data.get("text")
        if not isinstance(text, str) or not text.strip():
            return self.err("内容为空")
        if len(text.encode("utf-8")) > MAX_TEXT_BYTES:
            return self.err("文字过长")
        item = text_add(text)
        self.json_out({"ok": True, "id": item["id"], "length": len(text)})

    def _upload_init(self):
        data = self.body_json()
        name = sanitize_filename(str(data.get("name") or ""))
        if not name:
            return self.err("缺少文件名")
        try:
            size = int(data.get("size"))
            chunk_size = int(data.get("chunkSize"))
            total = int(data.get("totalChunks"))
        except (TypeError, ValueError):
            return self.err("参数格式错误")
        if size < 0 or chunk_size <= 0 or total <= 0:
            return self.err("参数不合法")
        if chunk_size > MAX_CHUNK_BYTES:
            return self.err("分块过大")
        if total > 200000:
            return self.err("分块数过多")
        # 分块数必须与偏移计算自洽，否则各块落点会错位
        if size == 0:
            if total != 1:
                return self.err("分块参数不匹配")
        elif total != (size + chunk_size - 1) // chunk_size:
            return self.err("分块参数不匹配")

        raw_rel = str(data.get("relPath") or "")
        rel_path = None
        if raw_rel:
            # 校验目录部分（文件名单独走 sanitize）
            parent = "/".join(raw_rel.replace("\\", "/").split("/")[:-1])
            if parent:
                target, norm = safe_join(SHARE_DIR, parent)
                if target is None:
                    return self.err(norm, 400)
                rel_path = norm + "/" + name
            else:
                rel_path = name
        mtime = float(data.get("mtime") or 0)

        rec = upload_create(name, rel_path, size, chunk_size, total, mtime)
        done = rec["status"] == "done"
        if done:
            # 会话标记为完成，但最终文件可能已被用户删除 —— 此时重置会话，
            # 让前端重新上传，而不是直接返回 done 导致「传了却没文件」。
            fp = rec["final_path"] or ""
            if not fp or not os.path.isfile(os.path.join(SHARE_DIR, fp)):
                with db() as conn:
                    conn.execute(
                        "UPDATE uploads SET status='active', final_path=NULL "
                        "WHERE id=?", (rec["id"],))
                    conn.execute(
                        "DELETE FROM chunks WHERE upload_id=?", (rec["id"],))
                rec = upload_get(rec["id"])
                done = False

        # 续传列表：分块记录 + 落盘文件的实际长度双重校验。分块可能因清理 /
        # 磁盘写满而丢失，若照常报告 have，前端会跳过它，收尾时才报错 ——
        # 这里按「这一块的数据确实落在文件里」过滤，前端会自动重传，续传自愈。
        try:
            # 在这里就把 .part 建好（单线程时机），并发上传第一块时不会撞车
            part = upload_ensure_part(rec)
            part_size = os.path.getsize(part)
        except (OSError, ValueError):
            part, part_size = "", 0
            with db() as conn:
                conn.execute("DELETE FROM chunks WHERE upload_id=?", (rec["id"],))

        with db() as conn:
            rows = conn.execute(
                "SELECT idx FROM chunks WHERE upload_id=?", (rec["id"],)
            ).fetchall()
        cs = rec["chunk_size"]
        have = sorted(
            r["idx"] for r in rows
            if 0 <= r["idx"] < rec["total_chunks"]
            and r["idx"] * cs + chunk_len(rec, r["idx"]) <= part_size
        )
        uploaded = sum(chunk_len(rec, i) for i in have)

        self.json_out({
            "ok": True,
            "uploadId": rec["id"],
            "have": have,
            "uploaded": uploaded,
            "done": done,
            "name": rec["name"],
            "totalChunks": rec["total_chunks"],
            "chunkSize": rec["chunk_size"],
        })

    def _upload_chunk(self):
        """
        接收一个分块：请求体就是原始字节（application/octet-stream），
        边读边按偏移写盘，不经 multipart 解析、不落系统临时目录。

        参数走 query：?uploadId=xxx&index=3
        """
        _, qs = self.q()
        upload_id = qs.get("uploadId") or ""
        index_raw = qs.get("index") or ""
        if not upload_id or not index_raw:
            return self.err("缺少参数")

        try:
            clen = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            clen = 0
        if clen < 0 or clen > MAX_CHUNK_BYTES:
            return self.err("分块大小不合法")

        rec = upload_get(upload_id)
        if not rec:
            # 会话过期/被清理：先把请求体丢掉，否则 keep-alive 连接会串包
            self._drain(clen)
            return self.err("上传会话不存在或已过期，请重新选择文件", 404)

        try:
            idx = int(index_raw)
        except ValueError:
            self._drain(clen)
            return self.err("分块序号非法")
        if idx < 0 or idx >= rec["total_chunks"]:
            self._drain(clen)
            return self.err("分块序号越界")

        expect = chunk_len(rec, idx)
        if clen != expect:
            self._drain(clen)
            return self.err(f"分块大小不符（应为 {expect}，收到 {clen}）")

        try:
            n = chunk_receive(rec, idx, self.rfile, clen)
        except ConnectionError as e:
            self.close_connection = True
            return self.err(str(e), 400)

        self.json_out({"ok": True, "uploadId": upload_id, "index": idx, "size": n})

    def _drain(self, n: int) -> None:
        """把不要的请求体读掉，保证 HTTP/1.1 连接上后续报文不错位。"""
        left = n
        while left > 0:
            buf = self.rfile.read(min(IO_CHUNK, left))
            if not buf:
                self.close_connection = True
                return
            left -= len(buf)

    def _upload_merge(self):
        data = self.body_json()
        upload_id = str(data.get("uploadId") or "")
        if not upload_id:
            return self.err("缺少 uploadId")
        try:
            rel, size = upload_merge(upload_id)
        except FileNotFoundError as e:
            return self.err(str(e), 404)
        except ValueError as e:
            return self.err(str(e), 400)
        self.json_out({"ok": True, "path": rel, "size": size})

    def _upload_cancel(self):
        data = self.body_json()
        upload_id = str(data.get("uploadId") or "")
        if not upload_id:
            return self.err("缺少 uploadId")
        upload_cancel(upload_id)
        self.json_out({"ok": True})

    # ---- DELETE ----
    def do_DELETE(self):
        if self.guard(write=True):
            return
        path, qs = self.q()
        try:
            if path == "/api/text/history":
                with db() as conn:
                    conn.execute("DELETE FROM texts")
                self.json_out({"ok": True})
            elif path.startswith("/api/text/history/"):
                tid = path[len("/api/text/history/"):]
                with db() as conn:
                    conn.execute("DELETE FROM texts WHERE id=?", (tid,))
                self.json_out({"ok": True})
            elif path.startswith("/api/uploads/"):
                upload_cancel(path[len("/api/uploads/"):])
                self.json_out({"ok": True})
            elif path.startswith("/api/delete/"):
                self._delete(path[len("/api/delete/"):], qs)
            else:
                self.err("接口不存在", 404)
        except Exception as e:
            self.err(f"服务器错误：{e}", 500)

    def _delete(self, raw, qs):
        rel = urllib.parse.unquote(raw)
        target, norm = safe_join(SHARE_DIR, rel)
        if target is None:
            return self.err(norm, 400)
        if os.path.abspath(target) == os.path.realpath(SHARE_DIR):
            return self.err("不能删除共享根目录", 400)

        is_dir = (qs.get("folder") == "1") or os.path.isdir(target)
        with _state_lock:
            busy = os.path.abspath(target) in _deleting
        if busy:
            return self.err("该文件正在合并中，请稍后再试", 409)

        if is_dir:
            if not os.path.isdir(target):
                return self.err("文件夹不存在", 404)
            shutil.rmtree(target, ignore_errors=True)
        else:
            if not os.path.isfile(target):
                return self.err("文件不存在", 404)
            os.remove(target)
        self.json_out({"ok": True})


# ─────────────────────────── 本机地址 / 启动 ───────────────────────────

def local_ips():
    """尽可能多地拿到本机可用的局域网 IPv4 地址。"""
    ips = []
    # 1) 通过 UDP connect 拿到默认出口地址（最常用、最准）
    for probe in (("8.8.8.8", 80), ("114.114.114.114", 53)):
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            s.connect(probe)
            ips.append(s.getsockname()[0])
        except Exception:
            pass
        finally:
            s.close()
    # 2) 补充解析主机名
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ips.append(info[4][0])
    except Exception:
        pass
    # 3) 可选：psutil 更完整
    try:
        import psutil  # type: ignore
        for name, addrs in psutil.net_if_addrs().items():
            for a in addrs:
                if a.family == socket.AF_INET and a.address:
                    ips.append(a.address)
    except Exception:
        pass

    out, seen = [], set()
    for ip in ips:
        if not ip or ip.startswith("127.") or ip.startswith("169.254."):
            continue
        if ip in seen:
            continue
        seen.add(ip)
        out.append(ip)
    return out or ["127.0.0.1"]


def banner(urls):
    line = "═" * 58
    print(f"\n  {line}")
    print(f"   LAN Transfer {VERSION}  已启动")
    print(f"  {line}")
    print(f"   共享目录 : {SHARE_DIR}")
    print(f"   共享大小 : {human_size(_dir_size(SHARE_DIR))}")
    if READ_ONLY:
        print("   运行模式 : 只读（禁止上传 / 删除）")
    if AUTH_TOKEN:
        print(f"   访问令牌 : {AUTH_TOKEN}")
    print(f"  {line}")
    print("   手机 / 其它电脑浏览器打开：")
    for u in urls:
        print(f"     👉  {u}")
    print(f"  {line}")
    print("   Ctrl+C 停止服务\n")


def _dir_size(path: str) -> int:
    total = 0
    for root, dirs, files in os.walk(path):
        dirs[:] = [d for d in dirs if not is_indexable(d)]
        for f in files:
            if is_indexable(f):
                continue
            try:
                total += os.path.getsize(os.path.join(root, f))
            except OSError:
                pass
    return total


def pick_port(host: str, port: int) -> int:
    """端口被占用时自动 +1，最多尝试 20 次。"""
    for i in range(20):
        p = port + i
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            s.bind((host, p))
            return p
        except OSError:
            continue
        finally:
            s.close()
    raise SystemExit(f"端口 {port}~{port + 19} 都被占用，请用 -p 指定其它端口")


def main():
    global SHARE_DIR, STATE_DIR, STAGING_DIR, DB_PATH
    global READ_ONLY, HOST, PORT, AUTH_TOKEN, ALLOW_OVERWRITE

    ap = argparse.ArgumentParser(
        description=f"{APP_NAME} {VERSION} - 局域网文件 / 文字传输",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "示例:\n"
            "  python server.py\n"
            "  python server.py -p 8080 -d D:\\share\n"
            "  python server.py --read-only --bind 127.0.0.1\n"
        ),
    )
    ap.add_argument("-p", "--port", type=int, default=DEFAULT_PORT, help=f"端口（默认 {DEFAULT_PORT}）")
    ap.add_argument("-d", "--dir", default=DEFAULT_DIR, help=f"共享目录（默认 {DEFAULT_DIR}）")
    ap.add_argument("--bind", default="0.0.0.0", help="监听地址（默认 0.0.0.0；用 127.0.0.1 则仅本机可访问）")
    ap.add_argument("--token", default="", help="访问令牌；留空则不校验（局域网内更省事）")
    ap.add_argument("--read-only", action="store_true", help="只读模式：禁止上传与删除")
    ap.add_argument("--no-overwrite", action="store_true", help="同名文件自动重命名，不覆盖")
    ap.add_argument("--open", action="store_true", help="启动后自动用默认浏览器打开本机页面")
    args = ap.parse_args()

    SHARE_DIR = os.path.abspath(os.path.expanduser(args.dir))
    os.makedirs(SHARE_DIR, exist_ok=True)
    STATE_DIR = os.path.join(SHARE_DIR, STATE_DIRNAME)
    STAGING_DIR = os.path.join(STATE_DIR, "chunks")
    DB_PATH = os.path.join(STATE_DIR, "index.db")
    os.makedirs(STAGING_DIR, exist_ok=True)

    READ_ONLY = bool(args.read_only)
    HOST = args.bind
    ALLOW_OVERWRITE = not args.no_overwrite
    AUTH_TOKEN = (args.token or os.environ.get("LAN_TRANSFER_TOKEN", "")).strip()

    init_db()
    n = cleanup_stale()
    if n:
        print(f"  已清理 {n} 个过期上传会话")

    PORT = pick_port(HOST, args.port)

    ThreadingHTTPServer.allow_reuse_address = True
    ThreadingHTTPServer.daemon_threads = True
    # 默认 backlog 只有 5：前端 4 路并发 + 页面刷新时容易直接被拒连
    ThreadingHTTPServer.request_queue_size = 128
    httpd = ThreadingHTTPServer((HOST, PORT), Handler)
    try:
        httpd.socket.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
    except OSError:
        pass
    # 注意：Windows 上 listening socket 的 SO_SNDBUF / SO_RCVBUF 不会传给
    # accepted socket，而且一旦显式设置就会关掉系统的接收窗口自动调优 ——
    # 所以这里不去动缓冲区大小，让 TCP 自己按 RTT 调。

    banner([f"http://{ip}:{PORT}" for ip in local_ips()])

    if args.open:
        import webbrowser
        threading.Timer(0.6, lambda: webbrowser.open(f"http://127.0.0.1:{PORT}")).start()

    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\n  正在停止…")
    finally:
        httpd.server_close()
        print("  已停止\n")


if __name__ == "__main__":
    main()
