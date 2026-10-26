#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
LAN Transfer 2.0 - 局域网文件 / 文字传输工具
Windows  <->  Android / iOS / 其它电脑 ，纯浏览器操作，无需安装 App

设计要点（相比 1.x 的改进）
  1. 上传分块以「内容哈希」寻址，重复上传天然幂等 —— 彻底修掉
     1.x 里每个分块生成不同 uploadId、导致合并报「缺少分块」的老 bug。
  2. 断点续传：已上传分块存在服务端 SQLite 会话表里，页面刷新 / 关浏览器 /
     断网 / 手机锁屏之后可以接着传，不必从头再来。
  3. 全链路流式：上传落盘、下载发送、文件夹 ZIP 打包都不再把整个文件读进内存，
     内存占用恒定，几百 GB 也不会 OOM。
  4. 实时进度（速度 / 平均速度 / 剩余时间）、可取消、可重试。
  5. 文件夹递归上传保留目录结构；文件夹下载走标准 zip（流式分片）。
  6. 文字：收发 + 持久化历史 + 搜索 + 一键复制（含安卓 HTTP 降级）+ 剪贴板接收。

依赖：仅标准库（Python 3.8+）。可选安装 psutil 来更完整地列出网卡地址。

用法：
  python server.py                          # 默认端口 9876
  python server.py -p 8080 -d D:\\share      # 自定义端口 / 共享目录
  python server.py --read-only              # 只读（禁止上传 / 删除）
  python server.py --bind 127.0.0.1         # 只允许本机访问（更安全）
"""

from __future__ import annotations

import argparse
import cgi
import hashlib
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
VERSION = "2.1"

DEFAULT_PORT = 9876
DEFAULT_DIR = "shared_files"

# 内部数据目录（分块暂存 + SQLite），位于共享目录下的同名子目录
STATE_DIRNAME = ".lan_transfer"
INTERNAL_DIR_NAME = STATE_DIRNAME
# 下载/上传时使用的套接字读写块大小
IO_CHUNK = 1024 * 1024
# 单个上传分块上限（前端按 16MB 切片，这里留足余量防滥用）
MAX_CHUNK_BYTES = 64 * 1024 * 1024
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
    conn = sqlite3.connect(DB_PATH, timeout=30, isolation_level=None)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA busy_timeout=10000")
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


def upload_wanted_chunks(upload_id: str):
    """返回服务端「还没有」的分块序号列表，前端据此续传。"""
    with db() as conn:
        rows = conn.execute(
            "SELECT idx FROM chunks WHERE upload_id=?", (upload_id,)
        ).fetchall()
    have = {r["idx"] for r in rows}
    rec = upload_get(upload_id)
    if not rec:
        return []
    return [i for i in range(rec["total_chunks"]) if i not in have]


def upload_uploaded_bytes(upload_id: str) -> int:
    with db() as conn:
        row = conn.execute(
            "SELECT COALESCE(SUM(size),0) AS s FROM chunks WHERE upload_id=?",
            (upload_id,),
        ).fetchone()
    return int(row["s"] or 0)


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


def chunk_save(upload_id, idx, data: bytes) -> int:
    """
    保存一个分块。分块文件以 sha1 命名 —— 相同内容只写一份，
    重复请求直接跳过写入，天然幂等。
    返回该分块字节数。
    """
    sha1 = hashlib.sha1(data).hexdigest()
    dst = os.path.join(STAGING_DIR, sha1)
    already = os.path.isfile(dst) and os.path.getsize(dst) == len(data)
    if not already:
        tmp = dst + ".part"
        with open(tmp, "wb") as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, dst)
    now = time.time()
    with db() as conn:
        conn.execute(
            """INSERT INTO chunks (upload_id,idx,size,sha1,file,created_at)
               VALUES (?,?,?,?,?,?)
               ON CONFLICT(upload_id,idx) DO UPDATE SET
                 size=excluded.size, sha1=excluded.sha1, file=excluded.file""",
            (upload_id, idx, len(data), sha1, sha1, now),
        )
        conn.execute("UPDATE uploads SET updated_at=? WHERE id=?", (now, upload_id))
    return len(data)


def upload_merge(upload_id: str):
    """
    合并分块 → 最终文件。全程流式，内存占用只有 IO_CHUNK。
    返回 (rel_path, size)。
    """
    rec = upload_get(upload_id)
    if not rec:
        raise FileNotFoundError("上传会话不存在")

    # 目标路径
    if rec["rel_path"]:
        dest, _ = safe_join(SHARE_DIR, rec["rel_path"])
        if dest is None:
            raise ValueError("路径不合法")
        os.makedirs(os.path.dirname(dest), exist_ok=True)
    else:
        dest = os.path.join(SHARE_DIR, sanitize_filename(rec["name"]))

    if ALLOW_OVERWRITE:
        final = dest
    else:
        final = uniq_path(dest)

    final_dir = os.path.dirname(final) or SHARE_DIR
    with _state_lock:
        _deleting.add(os.path.abspath(final))

    tmp_out = final + f".ltmp_{uuid.uuid4().hex[:8]}"
    try:
        with db() as conn:
            rows = conn.execute(
                "SELECT idx,file FROM chunks WHERE upload_id=? ORDER BY idx",
                (upload_id,),
            ).fetchall()
        have = {r["idx"]: r["file"] for r in rows}
        missing = [i for i in range(rec["total_chunks"]) if i not in have]
        if missing:
            raise ValueError(f"缺少分块 {missing[:5]}{'...' if len(missing) > 5 else ''}")

        with open(tmp_out, "wb") as out:
            for i in range(rec["total_chunks"]):
                src = os.path.join(STAGING_DIR, have[i])
                with open(src, "rb") as f:
                    shutil.copyfileobj(f, out, length=IO_CHUNK)
            out.flush()
            os.fsync(out.fileno())

        if os.path.exists(final):
            try:
                os.remove(final)
            except OSError:
                final = uniq_path(final)
        os.replace(tmp_out, final)
    except Exception:
        try:
            if os.path.exists(tmp_out):
                os.remove(tmp_out)
        except OSError:
            pass
        raise
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
    # 释放分块。分块文件按内容哈希跨会话共享 —— 必须确认没有其它会话
    # 还引用同一分块后才能删文件，否则同批上传内容相同（或共享相同分块，
    # 例如全零块）的文件，第二个合并时就会报「文件不存在」而失败。
    with db() as conn:
        sha_set = list(set(have.values()))
        marks = ",".join("?" * len(sha_set))
        still_used = {
            r["file"]
            for r in conn.execute(
                f"SELECT DISTINCT file FROM chunks "
                f"WHERE upload_id<>? AND file IN ({marks})",
                (upload_id, *sha_set),
            ).fetchall()
        }
        conn.execute("DELETE FROM chunks WHERE upload_id=?", (upload_id,))
    for f in sha_set:
        if f in still_used:
            continue
        p = os.path.join(STAGING_DIR, f)
        try:
            os.remove(p)
        except OSError:
            pass

    with _stats_lock:
        _stats["uploaded_files"] += 1
        _stats["uploaded_bytes"] += size

    return rel, size


def upload_cancel(upload_id: str) -> None:
    rec = upload_get(upload_id)
    if not rec:
        return
    with db() as conn:
        rows = conn.execute(
            "SELECT file FROM chunks WHERE upload_id=?", (upload_id,)
        ).fetchall()
        conn.execute("DELETE FROM chunks WHERE upload_id=?", (upload_id,))
        conn.execute("DELETE FROM uploads WHERE id=?", (upload_id,))
    # 只删除没有其它会话引用的分块文件
    for r in rows:
        f = os.path.join(STAGING_DIR, r["file"])
        with db() as conn:
            used = conn.execute(
                "SELECT 1 FROM chunks WHERE file=? LIMIT 1", (r["file"],)
            ).fetchone()
        if used is None:
            try:
                os.remove(f)
            except OSError:
                pass


def cleanup_stale() -> int:
    """清理长时间未续传的会话及其孤儿分块。"""
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
    # 孤儿分块（没有会话引用）
    try:
        names = set(os.listdir(STAGING_DIR))
    except OSError:
        names = set()
    with db() as conn:
        used = {r["file"] for r in conn.execute("SELECT DISTINCT file FROM chunks")}
    for n in names:
        if n in used or n.endswith(".part"):
            continue
        p = os.path.join(STAGING_DIR, n)
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
  // 分块大小：<8MB 整传，否则 16MB 一片
  const CHUNK=16*1024*1024;
  const isSmall=file.size<=CHUNK;
  const name=file.name;
  const rel=file.webkitRelativePath||'';
  const chunkSize=isSmall?Math.max(file.size,1):CHUNK;
  const totalChunks=isSmall?1:Math.ceil(file.size/CHUNK);
  const startTime=Date.now();
  let bytesDone=0;
  let uploadId=null;

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
      if(j.done){resolve();return}
      setBar(bytesDone,file.size,0,0);

      const todo=[];
      for(let i=0;i<totalChunks;i++)if(!have[i])todo.push(i);
      if(!todo.length){return doMerge()}

      // ── 速度统计只基于「服务端已确认收到」的字节 ──
      // xhr.upload.onprogress 统计的是浏览器写入本机 socket 缓冲区的字节，
      // 局域网上 TCP 缓冲会让它比服务端实际接收快 30%~50% —— 那正是
      // 「显示 90 多 MB/s、实际只有 60 多」的原因。分块 onload（服务端
      // 已落盘并应答）才是真实速度。
      let sessionBytes=0,sessionStart=0,curSpeed=0;
      let lastAckTick=0,lastAcked=0;
      const ackedBase=bytesDone;   // 续传时服务端已有字节的基数
      function onAck(n){
        sessionBytes+=n;
        const now=Date.now();
        if(!sessionStart)sessionStart=now;
        if(lastAckTick){
          const dt=(now-lastAckTick)/1000;
          if(dt>=0.25){
            const inst=(sessionBytes+ackedBase-lastAcked)/dt;
            curSpeed=curSpeed?curSpeed*0.6+inst*0.4:inst;
            lastAckTick=now;lastAcked=sessionBytes+ackedBase;
          }
        }else{
          lastAckTick=now;lastAcked=sessionBytes+ackedBase;
        }
      }

      let idx=0;
      function next(){
        if(isAborted()){reject(new Error('已取消'))}
        if(idx>=todo.length){return doMerge()}
        const ci=todo[idx];
        const start=ci*chunkSize;
        const end=Math.min(start+chunkSize,file.size);
        // 直接上传 Blob 切片，不经过 arrayBuffer / crypto.subtle。
        // crypto.subtle 只在安全上下文（HTTPS / localhost）可用，
        // 手机用 http://192.168.x.x 访问时它是 undefined —— 那正是
        // 「电脑能传、手机必失败」的原因。分块去重由服务端按内容哈希完成。
        const blob=file.slice(start,end);
        const fd=new FormData();
        fd.append('uploadId',uploadId);
        fd.append('index',String(ci));
        fd.append('chunk',blob,'chunk');
        const xhr=new XMLHttpRequest();
        xhr.open('POST',API+'/api/upload/chunk');
        if(TOKEN)xhr.setRequestHeader('X-Auth-Token',TOKEN);
        xhr.onload=function(){
          if(xhr.status!==200){
            let em='HTTP '+xhr.status;
            try{em=JSON.parse(xhr.responseText).error||em}catch(e){}
            reject(new Error('分块 '+(ci+1)+' 失败：'+em));return;
          }
          bytesDone+=(end-start);
          onAck(end-start);
          const remain=file.size-bytesDone;
          setBar(bytesDone,file.size,curSpeed,curSpeed>0?remain/curSpeed:0);
          idx++;next();
        };
        xhr.onerror=function(){
          reject(new Error('网络中断或无法连接服务端（已传部分会保留，重新选择该文件可续传）'))
        };
        // onprogress 只用来平滑进度条动画，不参与速度计算
        xhr.upload.onprogress=function(e){
          if(e.lengthComputable){
            const cur=Math.min(bytesDone+e.loaded,file.size);
            setBar(cur,file.size,curSpeed,curSpeed>0?(file.size-cur)/curSpeed:0);
          }
        };
        xhr.send(fd);
      }
      next();

      function doMerge(){
        fetch(API+'/api/upload/merge',{
          method:'POST',headers:hdrs({'Content-Type':'application/json'}),
          body:JSON.stringify({uploadId:uploadId})
        }).then(function(r){return r.json().then(function(j){return{r:r,j:j}})        }).then(function(o){
          if(!o.r.ok||!o.j.ok)throw new Error(o.j.error||'合并失败');
          fill.style.width='100%';
          pl.textContent=label+' · 完成';
          const dur=(Date.now()-(sessionStart||startTime))/1000;
          const avg=sessionBytes>0&&dur>0?sessionBytes/dur:file.size/((Date.now()-startTime)/1000);
          pr.textContent=size(file.size)+' · 平均 '+fmtSpeed(avg);
          resolve();
        }).catch(reject);
      }
    }).catch(reject);
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

        sent = 0
        with open(target, "rb") as f:
            if start:
                f.seek(start)
            while sent < length:
                buf = f.read(min(IO_CHUNK, length - sent))
                if not buf:
                    break
                self.wfile.write(buf)
                sent += len(buf)
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
            pass
        except Exception as e:
            with _stats_lock:
                _stats["errors"] += 1
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
        if total > 200000:
            return self.err("分块数过多")

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

        # 续传列表只报告分块文件真实存在的分块。分块文件可能因清理 / 异常
        # 丢失，若照常报告 have，前端会跳过它，合并时才报错 —— 这里剔除后
        # 前端会自动重传缺失分块，续传自愈。
        with db() as conn:
            rows = conn.execute(
                "SELECT idx, file FROM chunks WHERE upload_id=?", (rec["id"],)
            ).fetchall()
        have = sorted(
            r["idx"] for r in rows
            if os.path.isfile(os.path.join(STAGING_DIR, r["file"]))
        )
        uploaded = upload_uploaded_bytes(rec["id"])

        self.json_out({
            "ok": True,
            "uploadId": rec["id"],
            "have": have,
            "uploaded": uploaded,
            "done": done,
            "name": rec["name"],
            "totalChunks": rec["total_chunks"],
        })

    def _upload_chunk(self):
        ctype = self.headers.get("Content-Type", "")
        if "multipart/form-data" not in ctype:
            return self.err("需要 multipart/form-data")
        clen = int(self.headers.get("Content-Length") or 0)
        if clen <= 0 or clen > MAX_CHUNK_BYTES + 1024 * 1024:
            return self.err("分块大小不合法")

        # 用 cgi 解析（分块 ≤64MB，占用可控）
        env = {"REQUEST_METHOD": "POST", "CONTENT_TYPE": ctype,
               "CONTENT_LENGTH": str(clen)}
        fs = cgi.FieldStorage(fp=self.rfile, headers=self.headers,
                              environ=env, keep_blank_values=True)
        try:
            upload_id = fs.getvalue("uploadId", "")
            index_raw = fs.getvalue("index", "")
            data = fs.getvalue("chunk")
        except Exception as e:
            return self.err(f"解析失败：{e}")

        if not upload_id or not index_raw:
            return self.err("缺少参数")
        if isinstance(data, list):
            return self.err("只能上传单个分块")
        if not isinstance(data, (bytes, bytearray)):
            return self.err("缺少分块数据")

        rec = upload_get(upload_id)
        if not rec:
            return self.err("上传会话不存在或已过期，请重新选择文件", 404)

        try:
            idx = int(index_raw)
        except ValueError:
            return self.err("分块序号非法")
        if idx < 0 or idx >= rec["total_chunks"]:
            return self.err("分块序号越界")

        n = chunk_save(upload_id, idx, bytes(data))
        self.json_out({
            "ok": True,
            "uploadId": upload_id,
            "index": idx,
            "size": n,
            "uploaded": upload_uploaded_bytes(upload_id),
        })

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
    httpd = ThreadingHTTPServer((HOST, PORT), Handler)
    try:
        httpd.socket.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 1 << 20)
        httpd.socket.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 1 << 20)
        httpd.socket.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
    except OSError:
        pass

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
