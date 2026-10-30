#!/usr/bin/env python3
"""Warm Lean 4 (`lake serve`) + Rust semantic daemon for Anneal in Jetski.

Listens on a local mode-0600 Unix domain socket (`/tmp/anneal-lean-lsp.sock`) so:
1. The Jetski `stdio` MCP server (`anneal_lsp_mcp.py`),
2. Synchronous `<100ms` `PostToolUse` hooks (`hooks/post_tool_use.py`), and
3. The Jetski Web AuxPane Live InfoView UI sidecar (`sidecars/infoview/main.mjs`)
all share one warm LRU pool of `lake serve` (and optional `rust-analyzer`) workers
across `~/Projects/<ldap>/{anneal,anneal-private,zerocopy}`.
"""

from __future__ import annotations

import collections
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import socket
import socketserver
import subprocess
import sys
import threading
import time
from typing import Any
from urllib.parse import unquote, urlparse

DEFAULT_SOCKET_PATH = os.environ.get("ANNEAL_LSP_SOCKET", "/tmp/anneal-lean-lsp.sock")
LOCK_PATH = DEFAULT_SOCKET_PATH + ".lock"
MAX_WORKERS = int(os.environ.get("ANNEAL_LSP_MAX_WORKERS", "4"))
IDLE_TTL_SECONDS = int(os.environ.get("ANNEAL_LSP_IDLE_TTL_SECONDS", "900"))
MAX_INLINE_BYTES = 3800  # Keep MCP tool responses <4,000 bytes so Jetski never spills to temp files.

HOME_DIR = Path.home()
DEFAULT_ENV_PATH = (
    f"{HOME_DIR / '.anneal/toolchain/lean/bin'}:"
    f"{HOME_DIR / '.anneal/toolchain/rust/bin'}:"
    f"{HOME_DIR / '.elan/bin'}:{HOME_DIR / '.cargo/bin'}:"
    f"{HOME_DIR / '.local/bin'}:{os.environ.get('PATH', '/usr/bin:/bin')}"
)


def compute_script_sha256() -> str:
    try:
        return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()[:16]
    except OSError:
        return "unknown"


SCRIPT_SHA256 = compute_script_sha256()


def py_col_to_utf16(line_text: str, py_col: int) -> int:
    """Convert 0-based Python codepoint index to 0-based LSP UTF-16 code unit offset."""
    clamped = max(0, min(py_col, len(line_text)))
    return len(line_text[:clamped].encode("utf-16-le")) // 2


def utf16_to_py_col(line_text: str, utf16_col: int) -> int:
    """Convert 0-based LSP UTF-16 code unit offset to 0-based Python codepoint index."""
    if utf16_col <= 0:
        return 0
    units = 0
    for idx, ch in enumerate(line_text):
        units += 2 if ord(ch) > 0xFFFF else 1
        if units > utf16_col:
            return idx
        if units == utf16_col:
            return idx + 1
    return len(line_text)


def path_to_uri(path_str: str) -> str:
    p = Path(os.path.abspath(os.path.expanduser(path_str)))
    return p.as_uri()


def uri_to_path(uri: str) -> str:
    if uri.startswith("file://"):
        parsed = urlparse(uri)
        return unquote(parsed.path)
    return uri


def normalize_file_arg(args: dict[str, Any]) -> str:
    for key in ("file", "path", "file_path", "target_file", "uri", "Path", "TargetFile"):
        val = args.get(key)
        if isinstance(val, str) and val.strip():
            raw = val.strip()
            if raw.startswith("file://"):
                return uri_to_path(raw)
            return os.path.abspath(os.path.expanduser(raw))
    raise ValueError("Missing required `file` (absolute path to target file).")


def middle_clip(text: str, max_bytes: int = MAX_INLINE_BYTES) -> str:
    encoded = text.encode("utf-8")
    if len(encoded) <= max_bytes:
        return text
    marker = f"\n... [clipped {len(encoded) - max_bytes} bytes to stay inline <4 KiB] ...\n"
    m_bytes = len(marker.encode("utf-8"))
    budget = max(400, max_bytes - m_bytes)
    head_b = int(budget * 0.55)
    tail_b = budget - head_b
    head = encoded[:head_b].decode("utf-8", errors="ignore")
    tail = encoded[-tail_b:].decode("utf-8", errors="ignore")
    return head + marker + tail


def proc_rss_mb(pid: int | None) -> float:
    if not pid:
        return 0.0
    page_kb = max(1, os.sysconf("SC_PAGE_SIZE") // 1024)
    total_kb = 0
    my_uid = os.getuid()
    try:
        for entry in os.scandir("/proc"):
            if not entry.name.isdigit():
                continue
            try:
                if entry.stat(follow_symlinks=False).st_uid != my_uid:
                    continue
                p = int(entry.name)
                stat_txt = Path(f"/proc/{p}/stat").read_text(encoding="utf-8", errors="ignore")
                rparen = stat_txt.rfind(")")
                if rparen < 0:
                    continue
                fields = stat_txt[rparen + 2 :].split()
                if len(fields) < 22:
                    continue
                ppid = int(fields[1])
                pgrp = int(fields[2])
                sess = int(fields[3])
                if p == pid or ppid == pid or pgrp == pid or sess == pid:
                    rss_pages = int(fields[21])
                    if rss_pages > 0:
                        total_kb += rss_pages * page_kb
            except (OSError, ValueError):
                continue
    except OSError:
        return 0.0
    return round(total_kb / 1024.0, 1)


def resolve_lake_root(target_path: str) -> Path | None:
    """Locate the enclosing Anneal Lake workspace root (`lakefile.toml` or `lakefile.lean`).

    Handles all three Anneal directory layouts:
    1. Direct ancestor (`examples/Smoke.lean` -> `examples/`, `.anneal/generated/...` -> `.anneal/`)
    2. Sibling `.anneal/` (`<crate>/anneal/proofs/Proof/...` -> `<crate>/.anneal/`)
    3. Sibling `examples/` (`anneal/theory/...` or `anneal/trusted/lean/...` -> `anneal/examples/`)
    """
    abs_p = Path(os.path.abspath(os.path.expanduser(target_path)))
    candidates_to_walk: list[Path] = [abs_p if abs_p.is_dir() else abs_p.parent]
    real_p = abs_p.resolve(strict=False)
    real_start = real_p if real_p.is_dir() else real_p.parent
    if real_start not in candidates_to_walk:
        candidates_to_walk.append(real_start)

    for start in candidates_to_walk:
        cur = start
        while True:
            for lf in ("lakefile.toml", "lakefile.lean"):
                if (cur / lf).is_file():
                    return cur
            for sub in (".anneal", "examples"):
                for lf in ("lakefile.toml", "lakefile.lean"):
                    if (cur / sub / lf).is_file():
                        return cur / sub
            if cur.parent == cur:
                break
            cur = cur.parent
    return None


def resolve_cargo_root(target_path: str) -> Path | None:
    abs_p = Path(os.path.abspath(os.path.expanduser(target_path)))
    cur = abs_p if abs_p.is_dir() else abs_p.parent
    nearest: Path | None = None
    while True:
        if (cur / "Cargo.toml").is_file():
            if nearest is None:
                nearest = cur
            try:
                txt = (cur / "Cargo.toml").read_text(encoding="utf-8", errors="ignore")
                if "[workspace]" in txt:
                    return cur
            except OSError:
                pass
        if cur.parent == cur:
            break
        cur = cur.parent
    return nearest


def resolve_anneal_crate_root(target_path: str) -> Path | None:
    """Locate an Anneal Rust crate root (containing `.anneal/` or `anneal/proofs/`)."""
    abs_p = Path(os.path.abspath(os.path.expanduser(target_path)))
    cur = abs_p if abs_p.is_dir() else abs_p.parent
    while True:
        if (cur / ".anneal").is_dir() or (cur / "anneal" / "proofs").is_dir():
            return cur
        if cur.parent == cur:
            break
        cur = cur.parent
    return resolve_cargo_root(target_path)


class JsonRpcLspProcess:
    """Thread-safe JSON-RPC 2.0 LSP client over Content-Length framed stdio."""

    def __init__(self, cmd: list[str], cwd: Path, env: dict[str, str]) -> None:
        self.cmd = cmd
        self.cwd = cwd
        self.proc = subprocess.Popen(
            cmd,
            cwd=str(cwd),
            env=env,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
            start_new_session=True,
        )
        self._write_lock = threading.Lock()
        self._cond = threading.Condition()
        self._next_id = 1
        self._responses: dict[int, dict[str, Any]] = {}
        self._closed = False
        self.stderr_tail: collections.deque[str] = collections.deque(maxlen=60)
        self.on_notification = None  # Callable[[str, Any], None]

        self._reader_thread = threading.Thread(target=self._read_loop, daemon=True)
        self._stderr_thread = threading.Thread(target=self._stderr_loop, daemon=True)
        self._reader_thread.start()
        self._stderr_thread.start()

    def is_alive(self) -> bool:
        return not self._closed and self.proc.poll() is None

    def _stderr_loop(self) -> None:
        assert self.proc.stderr is not None
        try:
            for raw_line in iter(self.proc.stderr.readline, b""):
                line = raw_line.decode("utf-8", errors="replace").rstrip()
                if line:
                    self.stderr_tail.append(line)
        except Exception:
            pass

    def _read_exact(self, n: int) -> bytes:
        assert self.proc.stdout is not None
        chunks: list[bytes] = []
        rem = n
        while rem > 0:
            chunk = self.proc.stdout.read(rem)
            if not chunk:
                raise EOFError("LSP stdout closed")
            chunks.append(chunk)
            rem -= len(chunk)
        return b"".join(chunks)

    def _read_loop(self) -> None:
        assert self.proc.stdout is not None
        try:
            while True:
                content_length = None
                while True:
                    line = self.proc.stdout.readline()
                    if not line:
                        raise EOFError("LSP EOF while reading headers")
                    if line in (b"\r\n", b"\n"):
                        break
                    lower = line.lower()
                    if lower.startswith(b"content-length:"):
                        content_length = int(line.split(b":", 1)[1].strip())
                if content_length is None:
                    continue
                body = self._read_exact(content_length)
                msg = json.loads(body.decode("utf-8", errors="replace"))
                if "id" in msg and ("result" in msg or "error" in msg):
                    req_id = msg["id"]
                    with self._cond:
                        self._responses[req_id] = msg
                        self._cond.notify_all()
                elif "method" in msg:
                    if "id" in msg:
                        # Server-initiated request (e.g., client/registerCapability or workspace/configuration)
                        self._reply_server_request(msg["id"], msg["method"])
                    elif self.on_notification is not None:
                        try:
                            self.on_notification(msg["method"], msg.get("params"))
                        except Exception:
                            pass
        except Exception:
            pass
        finally:
            with self._cond:
                self._closed = True
                self._cond.notify_all()

    def _reply_server_request(self, req_id: Any, method: str) -> None:
        result: Any = None
        if method == "workspace/configuration":
            result = [{}]
        payload = {"jsonrpc": "2.0", "id": req_id, "result": result}
        try:
            self._send_raw(payload)
        except Exception:
            pass

    def _send_raw(self, payload: dict[str, Any]) -> None:
        raw = json.dumps(payload, separators=(",", ":")).encode("utf-8")
        frame = f"Content-Length: {len(raw)}\r\n\r\n".encode("ascii") + raw
        with self._write_lock:
            if self.proc.stdin is None or not self.is_alive():
                raise RuntimeError("LSP process is not running")
            self.proc.stdin.write(frame)
            self.proc.stdin.flush()

    def notify(self, method: str, params: Any) -> None:
        self._send_raw({"jsonrpc": "2.0", "method": method, "params": params})

    def request(self, method: str, params: Any, timeout_s: float = 30.0) -> Any:
        with self._cond:
            req_id = self._next_id
            self._next_id += 1
        self._send_raw({"jsonrpc": "2.0", "id": req_id, "method": method, "params": params})
        deadline = time.monotonic() + timeout_s
        with self._cond:
            while req_id not in self._responses and not self._closed:
                rem = deadline - time.monotonic()
                if rem <= 0:
                    raise TimeoutError(f"LSP request `{method}` timed out after {timeout_s:.1f}s")
                self._cond.wait(timeout=rem)
            if req_id not in self._responses:
                tail = "\n".join(list(self.stderr_tail)[-10:])
                raise RuntimeError(f"LSP process exited during `{method}`. stderr:\n{tail}")
            resp = self._responses.pop(req_id)
        if "error" in resp:
            err = resp["error"]
            raise RuntimeError(f"LSP `{method}` error ({err.get('code')}): {err.get('message')}")
        return resp.get("result")

    def terminate(self) -> None:
        with self._cond:
            self._closed = True
            self._cond.notify_all()
        try:
            os.killpg(os.getpgid(self.proc.pid), signal.SIGTERM)
        except Exception:
            try:
                self.proc.terminate()
            except Exception:
                pass
        try:
            self.proc.wait(timeout=1.5)
        except Exception:
            try:
                os.killpg(os.getpgid(self.proc.pid), signal.SIGKILL)
            except Exception:
                try:
                    self.proc.kill()
                except Exception:
                    pass


class LeanWorkspaceWorker:
    """Manages one warm `lake serve --` instance for a specific Lake root."""

    def __init__(self, lake_root: Path) -> None:
        self.lake_root = lake_root
        self.started_at = time.time()
        self.last_used = time.time()
        self.op_lock = threading.RLock()
        self._diag_cond = threading.Condition()
        self.open_docs: dict[str, tuple[int, str]] = {}  # uri -> (version, text)
        self.diagnostics: dict[str, tuple[int | None, list[dict[str, Any]]]] = {}
        self.file_progress: dict[str, tuple[int, list[Any]]] = {}
        self.sandboxed = False
        self.fingerprint = self._compute_fingerprint()
        self.lsp = self._spawn_lake_serve()

    def _compute_fingerprint(self) -> tuple[Any, ...]:
        items: list[Any] = []
        for name in ("lakefile.toml", "lakefile.lean", "lean-toolchain"):
            p = self.lake_root / name
            try:
                st = p.stat()
                items.append((name, st.st_ino, st.st_mtime_ns, st.st_size))
            except OSError:
                items.append((name, None))
        gen_dir = self.lake_root / "generated"
        try:
            st = gen_dir.stat()
            items.append(("generated", st.st_ino, st.st_mtime_ns))
        except OSError:
            items.append(("generated", None))
        return tuple(items)

    def needs_restart(self) -> bool:
        if not self.lsp.is_alive():
            return True
        return self._compute_fingerprint() != self.fingerprint

    def _build_env(self) -> dict[str, str]:
        env = os.environ.copy()
        env["PATH"] = f"{DEFAULT_ENV_PATH}:{env.get('PATH', '')}"
        return env

    def _spawn_lake_serve(self) -> JsonRpcLspProcess:
        lake_bin = shutil.which("lake", path=DEFAULT_ENV_PATH) or str(HOME_DIR / ".elan/bin/lake")
        dot_lake = self.lake_root / ".lake"
        dot_lake.mkdir(parents=True, exist_ok=True)
        lake_manifest = self.lake_root / "lake-manifest.json"
        if not lake_manifest.exists():
            try:
                lake_manifest.write_text('{"version": "1.1.0", "packagesDir": ".lake/packages", "packages": [], "name": "AnnealWorkspace", "lakeDir": ".lake"}\n', encoding="utf-8")
            except OSError:
                pass
        env = self._build_env()

        bwrap_bin = "/usr/bin/bwrap" if Path("/usr/bin/bwrap").is_file() else None
        choom_bin = "/usr/bin/choom" if Path("/usr/bin/choom").is_file() else None

        inner_cmd = [lake_bin, "serve", "--"]
        if choom_bin:
            inner_cmd = [choom_bin, "-n", "800", "--", *inner_cmd]

        if bwrap_bin and os.environ.get("ANNEAL_LSP_DISABLE_BWRAP") != "1":
            # Mount `/` read-only and `--unshare-net` so `#eval` metaprograms can never
            # mutate locked `Specs/` / `Assumptions/` or touch the network; bind `.lake`
            # (and `lake-manifest.json` if present) writable so Lake lockfiles/caches work.
            # Note: Do NOT pass `--die-with-parent` here because Linux `PR_SET_PDEATHSIG`
            # fires when the *spawning thread* exits (and `ThreadedUnixServer` uses per-RPC
            # threads). `--unshare-pid` + `stdin` EOF + `os.killpg` teardown handles cleanup.
            bwrap_cmd = [
                bwrap_bin,
                "--ro-bind", "/", "/",
                "--dev", "/dev",
                "--proc", "/proc",
                "--tmpfs", "/tmp",
                "--bind", str(dot_lake), str(dot_lake),
            ]
            if lake_manifest.is_file():
                bwrap_cmd.extend(["--bind", str(lake_manifest), str(lake_manifest)])
            bwrap_cmd.extend([
                "--unshare-pid",
                "--unshare-net",
                "--",
                *inner_cmd,
            ])
            try:
                client = self._init_client(bwrap_cmd, env, pid_namespaced=True)
                self.sandboxed = True
                return client
            except Exception:
                pass

        self.sandboxed = False
        return self._init_client(inner_cmd, env, pid_namespaced=False)

    def _init_client(self, cmd: list[str], env: dict[str, str], pid_namespaced: bool = False) -> JsonRpcLspProcess:
        client = JsonRpcLspProcess(cmd=cmd, cwd=self.lake_root, env=env)
        client.on_notification = self._on_notification
        root_uri = self.lake_root.as_uri()
        client.request(
            "initialize",
            {
                "processId": None if pid_namespaced else os.getpid(),
                "rootUri": root_uri,
                "capabilities": {
                    "textDocument": {
                        "hover": {"contentFormat": ["markdown", "plaintext"]},
                        "completion": {"completionItem": {"snippetSupport": False}},
                        "publishDiagnostics": {"versionSupport": True},
                    }
                },
                "workspaceFolders": [{"uri": root_uri, "name": self.lake_root.name}],
            },
            timeout_s=25.0,
        )
        client.notify("initialized", {})
        return client

    def _on_notification(self, method: str, params: Any) -> None:
        if not isinstance(params, dict):
            return
        if method == "textDocument/publishDiagnostics":
            uri = params.get("uri", "")
            ver = params.get("version")
            diags = params.get("diagnostics") or []
            with self._diag_cond:
                self.diagnostics[uri] = (ver, diags)
                self._diag_cond.notify_all()
        elif method == "$/lean/fileProgress":
            td = params.get("textDocument") or {}
            uri = td.get("uri", "")
            ver = td.get("version", 0)
            processing = params.get("processing") or []
            with self._diag_cond:
                self.file_progress[uri] = (ver, processing)
                self._diag_cond.notify_all()

    def sync_text(self, file_path: str, text: str, wait_timeout_s: float = 45.0) -> tuple[str, int, float, bool]:
        """Synchronize `text` for `file_path` into Lean's VFS and wait for elaboration.

        Returns `(uri, version, elapsed_ms, completed)`.
        """
        t0 = time.monotonic()
        uri = path_to_uri(file_path)
        with self.op_lock:
            self.last_used = time.time()
            prev = self.open_docs.get(uri)
            if prev is None:
                ver = 1
                self.open_docs[uri] = (ver, text)
                with self._diag_cond:
                    self.file_progress[uri] = (ver, [{"placeholder": True}])
                self.lsp.notify(
                    "textDocument/didOpen",
                    {
                        "textDocument": {
                            "uri": uri,
                            "languageId": "lean4",
                            "version": ver,
                            "text": text,
                        }
                    },
                )
                completed = self._wait_elaborated(uri, ver, wait_timeout_s)
            elif prev[1] != text:
                ver = prev[0] + 1
                self.open_docs[uri] = (ver, text)
                with self._diag_cond:
                    self.file_progress[uri] = (ver, [{"placeholder": True}])
                self.lsp.notify(
                    "textDocument/didChange",
                    {
                        "textDocument": {"uri": uri, "version": ver},
                        "contentChanges": [{"text": text}],
                    },
                )
                completed = self._wait_elaborated(uri, ver, wait_timeout_s)
            else:
                ver = prev[0]
                prog = self.file_progress.get(uri)
                if prog is not None and prog[0] >= ver and len(prog[1]) > 0:
                    completed = self._wait_elaborated(uri, ver, wait_timeout_s)
                else:
                    completed = True
            elapsed_ms = round((time.monotonic() - t0) * 1000.0, 1)
            return uri, ver, elapsed_ms, completed

    def sync_disk_file(self, file_path: str, wait_timeout_s: float = 45.0) -> tuple[str, str, int, float, bool]:
        p = Path(file_path)
        if not p.is_file():
            raise FileNotFoundError(f"Lean file does not exist: {file_path}")
        text = p.read_text(encoding="utf-8", errors="replace")
        uri, ver, elapsed_ms, completed = self.sync_text(file_path, text, wait_timeout_s=wait_timeout_s)
        return uri, text, ver, elapsed_ms, completed

    def _wait_elaborated(self, uri: str, target_ver: int, timeout_s: float) -> bool:
        deadline = time.monotonic() + timeout_s
        with self._diag_cond:
            while True:
                prog = self.file_progress.get(uri)
                if prog is not None and prog[0] >= target_ver and len(prog[1]) == 0:
                    break
                if not self.lsp.is_alive():
                    return False
                rem = deadline - time.monotonic()
                if rem <= 0:
                    return False
                self._diag_cond.wait(timeout=min(rem, 0.2))
        # Brief settle window for trailing publishDiagnostics packet after fileProgress=[].
        time.sleep(0.015)
        return True

    def get_diagnostics(self, uri: str) -> list[dict[str, Any]]:
        with self._diag_cond:
            entry = self.diagnostics.get(uri)
            return list(entry[1]) if entry else []

    def plain_goal(self, uri: str, line0: int, utf16_col: int, timeout_s: float = 10.0) -> dict[str, Any] | None:
        res = self.lsp.request(
            "$/lean/plainGoal",
            {
                "textDocument": {"uri": uri},
                "position": {"line": line0, "character": utf16_col},
            },
            timeout_s=timeout_s,
        )
        return res if isinstance(res, dict) else None

    def plain_term_goal(self, uri: str, line0: int, utf16_col: int, timeout_s: float = 10.0) -> dict[str, Any] | None:
        res = self.lsp.request(
            "$/lean/plainTermGoal",
            {
                "textDocument": {"uri": uri},
                "position": {"line": line0, "character": utf16_col},
            },
            timeout_s=timeout_s,
        )
        return res if isinstance(res, dict) else None

    def status_dict(self) -> dict[str, Any]:
        pid = self.lsp.proc.pid if self.lsp.is_alive() else None
        return {
            "kind": "lean4",
            "root": str(self.lake_root),
            "pid": pid,
            "alive": self.lsp.is_alive(),
            "sandboxed_bwrap": self.sandboxed,
            "rss_mb": proc_rss_mb(pid),
            "open_files": len(self.open_docs),
            "uptime_s": round(time.time() - self.started_at, 1),
            "idle_s": round(time.time() - self.last_used, 1),
        }

    def close(self) -> None:
        self.lsp.terminate()


class RustAnalyzerWorker:
    """Optional `rust-analyzer` LSP worker when a working binary is present."""

    def __init__(self, cargo_root: Path, ra_bin: str) -> None:
        self.cargo_root = cargo_root
        self.ra_bin = ra_bin
        self.started_at = time.time()
        self.last_used = time.time()
        self.op_lock = threading.RLock()
        self._diag_cond = threading.Condition()
        self.open_docs: dict[str, tuple[int, str]] = {}
        self.diagnostics: dict[str, list[dict[str, Any]]] = {}

        env = os.environ.copy()
        env["PATH"] = f"{DEFAULT_ENV_PATH}:{env.get('PATH', '')}"
        self.lsp = JsonRpcLspProcess([ra_bin], cwd=cargo_root, env=env)
        self.lsp.on_notification = self._on_notification
        root_uri = cargo_root.as_uri()
        self.lsp.request(
            "initialize",
            {
                "processId": os.getpid(),
                "rootUri": root_uri,
                "capabilities": {
                    "textDocument": {
                        "hover": {"contentFormat": ["markdown", "plaintext"]},
                        "publishDiagnostics": {"versionSupport": True},
                    }
                },
                "initializationOptions": {
                    "cargo": {"buildScripts": {"enable": True}},
                    "procMacro": {"enable": True},
                },
            },
            timeout_s=30.0,
        )
        self.lsp.notify("initialized", {})

    def _on_notification(self, method: str, params: Any) -> None:
        if method == "textDocument/publishDiagnostics" and isinstance(params, dict):
            uri = params.get("uri", "")
            with self._diag_cond:
                self.diagnostics[uri] = params.get("diagnostics") or []
                self._diag_cond.notify_all()

    def sync_disk_file(self, file_path: str) -> tuple[str, str]:
        text = Path(file_path).read_text(encoding="utf-8", errors="replace")
        uri = path_to_uri(file_path)
        with self.op_lock:
            self.last_used = time.time()
            prev = self.open_docs.get(uri)
            if prev is None:
                self.open_docs[uri] = (1, text)
                self.lsp.notify(
                    "textDocument/didOpen",
                    {"textDocument": {"uri": uri, "languageId": "rust", "version": 1, "text": text}},
                )
            elif prev[1] != text:
                ver = prev[0] + 1
                self.open_docs[uri] = (ver, text)
                self.lsp.notify(
                    "textDocument/didChange",
                    {"textDocument": {"uri": uri, "version": ver}, "contentChanges": [{"text": text}]},
                )
        return uri, text

    def status_dict(self) -> dict[str, Any]:
        pid = self.lsp.proc.pid if self.lsp.is_alive() else None
        return {
            "kind": "rust-analyzer",
            "root": str(self.cargo_root),
            "pid": pid,
            "alive": self.lsp.is_alive(),
            "sandboxed_bwrap": False,
            "rss_mb": proc_rss_mb(pid),
            "open_files": len(self.open_docs),
            "uptime_s": round(time.time() - self.started_at, 1),
            "idle_s": round(time.time() - self.last_used, 1),
        }

    def close(self) -> None:
        self.lsp.terminate()


def find_working_rust_analyzer() -> str | None:
    candidates = [
        os.environ.get("RUST_ANALYZER_BIN", ""),
        str(HOME_DIR / ".local/bin/rust-analyzer"),
        str(HOME_DIR / ".cargo/bin/rust-analyzer"),
        "/usr/local/bin/rust-analyzer",
        "/usr/bin/rust-analyzer",
    ]
    env = os.environ.copy()
    env["PATH"] = f"{DEFAULT_ENV_PATH}:{env.get('PATH', '')}"
    for cand in candidates:
        if not cand or not Path(cand).is_file():
            continue
        try:
            res = subprocess.run([cand, "--version"], capture_output=True, text=True, timeout=2.0, env=env)
            if res.returncode == 0:
                return cand
        except Exception:
            continue
    return None


def find_sorry_lines(text: str) -> list[tuple[int, int, str]]:
    """Return `(line1, py_col0, line_str)` for non-comment `sorry` / `admit` occurrences."""
    results: list[tuple[int, int, str]] = []
    in_block = 0
    for idx, raw_line in enumerate(text.splitlines(), start=1):
        # Strip simple `--` line comments while tracking `/- ... -/` block comments.
        i = 0
        cleaned_chars: list[str] = []
        n = len(raw_line)
        while i < n:
            two = raw_line[i : i + 2]
            if two == "/-":
                in_block += 1
                cleaned_chars.extend((" ", " "))
                i += 2
                continue
            if two == "-/" and in_block > 0:
                in_block -= 1
                cleaned_chars.extend((" ", " "))
                i += 2
                continue
            if in_block == 0 and two == "--":
                break
            cleaned_chars.append(" " if in_block > 0 else raw_line[i])
            i += 1
        cleaned = "".join(cleaned_chars)
        for m in re.finditer(r"\b(sorry|admit)\b", cleaned):
            results.append((idx, m.start(), raw_line))
    return results


def strip_line_comment(raw_line: str) -> str:
    idx = raw_line.find("--")
    return raw_line[:idx] if idx >= 0 else raw_line


class AnnealLspCoordinator:
    """Coordinates Lean 4 + Rust workers, Anneal checks, and Live InfoView state."""

    def __init__(self) -> None:
        self.started_at = time.time()
        self._pool_lock = threading.Lock()
        self.lean_workers: collections.OrderedDict[str, LeanWorkspaceWorker] = collections.OrderedDict()
        self.rust_workers: collections.OrderedDict[str, RustAnalyzerWorker] = collections.OrderedDict()
        self.ra_bin = find_working_rust_analyzer()

        self._ui_lock = threading.Lock()
        self.infoview_state: dict[str, Any] = {
            "active_file": None,
            "lake_root": None,
            "updated_at": None,
            "elapsed_ms": None,
            "completed": True,
            "status": "idle",
            "sorry_count": 0,
            "diagnostics": [],
            "goals": [],
            "audit": None,
            "recent_events": [],
        }

        self._reaper = threading.Thread(target=self._reap_loop, daemon=True)
        self._reaper.start()

    def _reap_loop(self) -> None:
        while True:
            time.sleep(30.0)
            now = time.time()
            to_close: list[Any] = []
            with self._pool_lock:
                for key in list(self.lean_workers.keys()):
                    w = self.lean_workers[key]
                    if not w.lsp.is_alive() or (now - w.last_used) > IDLE_TTL_SECONDS:
                        to_close.append(self.lean_workers.pop(key))
                for key in list(self.rust_workers.keys()):
                    rw = self.rust_workers[key]
                    if not rw.lsp.is_alive() or (now - rw.last_used) > IDLE_TTL_SECONDS:
                        to_close.append(self.rust_workers.pop(key))
            for w in to_close:
                try:
                    w.close()
                except Exception:
                    pass

    def get_lean_worker(self, file_or_dir: str) -> LeanWorkspaceWorker:
        lake_root = resolve_lake_root(file_or_dir)
        if lake_root is None:
            raise ValueError(
                f"Could not locate an enclosing `lakefile.toml` or `lakefile.lean` for `{file_or_dir}`. "
                "For a new Anneal crate, run `cargo anneal agent-context` or `cargo anneal lock-specs` first to generate `.anneal/lakefile.toml`."
            )
        key = str(lake_root.resolve())
        evicted: list[LeanWorkspaceWorker] = []
        with self._pool_lock:
            existing = self.lean_workers.get(key)
            if existing is not None:
                if existing.needs_restart():
                    evicted.append(self.lean_workers.pop(key))
                    existing = None
                else:
                    self.lean_workers.move_to_end(key)
                    existing.last_used = time.time()
            if existing is None:
                while len(self.lean_workers) >= MAX_WORKERS:
                    _, oldest = self.lean_workers.popitem(last=False)
                    evicted.append(oldest)
                worker = LeanWorkspaceWorker(lake_root.resolve())
                self.lean_workers[key] = worker
                existing = worker
        for old in evicted:
            try:
                old.close()
            except Exception:
                pass
        return existing

    def get_rust_worker(self, file_or_dir: str) -> RustAnalyzerWorker | None:
        if not self.ra_bin:
            self.ra_bin = find_working_rust_analyzer()
        if not self.ra_bin:
            return None
        cargo_root = resolve_cargo_root(file_or_dir)
        if cargo_root is None:
            return None
        key = str(cargo_root.resolve())
        with self._pool_lock:
            existing = self.rust_workers.get(key)
            if existing is not None and existing.lsp.is_alive():
                self.rust_workers.move_to_end(key)
                existing.last_used = time.time()
                return existing
            if existing is not None:
                self.rust_workers.pop(key, None)
                try:
                    existing.close()
                except Exception:
                    pass
            worker = RustAnalyzerWorker(cargo_root.resolve(), self.ra_bin)
            self.rust_workers[key] = worker
            return worker

    def _record_infoview(
        self,
        *,
        file_path: str,
        lake_root: Path,
        elapsed_ms: float,
        completed: bool,
        diags: list[dict[str, Any]],
        sorry_count: int,
        goals: list[dict[str, Any]],
        event_label: str,
        audit: dict[str, Any] | None = None,
    ) -> None:
        err_count = sum(1 for d in diags if d.get("severity") == 1)
        if not completed:
            status = "elaborating"
        elif err_count > 0:
            status = "error"
        elif sorry_count > 0 or any(g.get("goals") for g in goals):
            status = "open_goals"
        else:
            status = "verified_clean"

        formatted_diags = [self._compact_diag_dict(d) for d in diags[:30]]
        with self._ui_lock:
            events = list(self.infoview_state.get("recent_events") or [])
            events.insert(
                0,
                {
                    "ts": time.strftime("%H:%M:%S"),
                    "label": event_label,
                    "file": os.path.basename(file_path),
                    "full_path": file_path,
                    "elapsed_ms": elapsed_ms,
                    "errors": err_count,
                    "sorrys": sorry_count,
                },
            )
            self.infoview_state.update(
                {
                    "active_file": file_path,
                    "lake_root": str(lake_root),
                    "updated_at": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
                    "elapsed_ms": elapsed_ms,
                    "completed": completed,
                    "status": status,
                    "sorry_count": sorry_count,
                    "diagnostics": formatted_diags,
                    "goals": goals[:12],
                    "recent_events": events[:20],
                }
            )
            if audit is not None:
                self.infoview_state["audit"] = audit

    @staticmethod
    def _compact_diag_dict(d: dict[str, Any]) -> dict[str, Any]:
        sev_map = {1: "error", 2: "warning", 3: "info", 4: "hint"}
        rng = d.get("range") or {}
        start = rng.get("start") or {}
        return {
            "severity": sev_map.get(d.get("severity", 1), "info"),
            "line": int(start.get("line", 0)) + 1,
            "column": int(start.get("character", 0)) + 1,
            "message": middle_clip((d.get("message") or "").strip(), 600),
        }

    def _collect_sorry_goals(self, worker: LeanWorkspaceWorker, uri: str, text: str, limit: int = 5) -> list[dict[str, Any]]:
        sorrys = find_sorry_lines(text)
        out: list[dict[str, Any]] = []
        for line1, py_col0, raw_line in sorrys[:limit]:
            utf16_col = py_col_to_utf16(raw_line, py_col0)
            goal_res = None
            try:
                goal_res = worker.plain_goal(uri, line1 - 1, utf16_col, timeout_s=4.0)
                if not goal_res or not goal_res.get("goals"):
                    goal_res = worker.plain_term_goal(uri, line1 - 1, utf16_col, timeout_s=4.0)
            except Exception:
                pass
            goals_list = []
            if goal_res:
                if goal_res.get("goals"):
                    goals_list = goal_res["goals"]
                elif goal_res.get("goal"):
                    goals_list = [goal_res["goal"]]
            out.append(
                {
                    "label": f"sorry at L{line1}:{py_col0 + 1}",
                    "line": line1,
                    "column": py_col0 + 1,
                    "code": raw_line.strip(),
                    "goals": goals_list,
                }
            )
        return out

    # ---------------- Tool 1: lean_diagnostics ----------------
    def tool_lean_diagnostics(self, args: dict[str, Any]) -> dict[str, Any]:
        file_path = normalize_file_arg(args)
        timeout_s = float(args.get("timeout_s", 45.0))
        sev_filter = str(args.get("severity", "all")).lower()

        worker = self.get_lean_worker(file_path)
        with worker.op_lock:
            uri, text, _, elapsed_ms, completed = worker.sync_disk_file(file_path, wait_timeout_s=timeout_s)
            diags = worker.get_diagnostics(uri)
            sorrys = find_sorry_lines(text)
            sorry_goals = self._collect_sorry_goals(worker, uri, text, limit=4)

        self._record_infoview(
            file_path=file_path,
            lake_root=worker.lake_root,
            elapsed_ms=elapsed_ms,
            completed=completed,
            diags=diags,
            sorry_count=len(sorrys),
            goals=sorry_goals,
            event_label="lean_diagnostics",
        )

        # Sort errors (1) before warnings (2) before info (3)
        diags_sorted = sorted(diags, key=lambda d: (d.get("severity", 9), (d.get("range", {}).get("start", {}).get("line", 0))))
        if sev_filter == "error":
            diags_sorted = [d for d in diags_sorted if d.get("severity") == 1]
        elif sev_filter in ("warning", "warnings"):
            diags_sorted = [d for d in diags_sorted if d.get("severity") in (1, 2)]

        err_n = sum(1 for d in diags if d.get("severity") == 1)
        warn_n = sum(1 for d in diags if d.get("severity") == 2)
        status_note = "" if completed else " (WARNING: elaboration still in progress after timeout)"

        lines = [
            f"File: {file_path}",
            f"Lake root: {worker.lake_root} ({elapsed_ms} ms){status_note}",
            f"Summary: {err_n} error(s), {warn_n} warning(s), {len(sorrys)} sorry/admit token(s)",
        ]
        seen_msgs: set[tuple[int, str]] = set()
        for d in diags_sorted:
            cd = self._compact_diag_dict(d)
            dedup_key = (cd["line"], cd["message"][:120])
            if dedup_key in seen_msgs:
                continue
            seen_msgs.add(dedup_key)
            lines.append(f"\n[{cd['severity'].upper()}] L{cd['line']}:{cd['column']}: {cd['message']}")

        if sorry_goals:
            lines.append("\nOpen `sorry` Goals:")
            for sg in sorry_goals:
                g_txt = "\n---\n".join(sg["goals"]) if sg["goals"] else "(no tactic goal captured)"
                lines.append(f"  * {sg['label']} (`{sg['code']}`):\n{g_txt}")

        return {
            "text": middle_clip("\n".join(lines)),
            "errors": err_n,
            "warnings": warn_n,
            "sorrys": len(sorrys),
            "completed": completed,
            "elapsed_ms": elapsed_ms,
        }

    # ---------------- Tool 2: lean_goal ----------------
    def tool_lean_goal(self, args: dict[str, Any]) -> dict[str, Any]:
        file_path = normalize_file_arg(args)
        line1 = int(args.get("line") or args.get("line_number") or 1)
        req_col = args.get("column") if args.get("column") is not None else args.get("col")
        snippet = args.get("snippet")

        worker = self.get_lean_worker(file_path)
        with worker.op_lock:
            uri, text, _, elapsed_ms, completed = worker.sync_disk_file(file_path, wait_timeout_s=45.0)
            file_lines = text.splitlines()
            if not file_lines:
                raise ValueError(f"File is empty: {file_path}")
            line1 = max(1, min(line1, len(file_lines)))
            raw_line = file_lines[line1 - 1]
            code_only = strip_line_comment(raw_line)
            first_non_ws = len(code_only) - len(code_only.lstrip())
            end_non_ws = len(code_only.rstrip())

            # Determine probe columns (0-based Python indices)
            focus_py_col = first_non_ws
            if isinstance(snippet, str) and snippet.strip():
                idx = raw_line.find(snippet.strip())
                if idx >= 0:
                    focus_py_col = idx
            elif req_col is not None:
                focus_py_col = max(0, int(req_col) - 1)

            before_u16 = py_col_to_utf16(raw_line, first_non_ws)
            focus_u16 = py_col_to_utf16(raw_line, focus_py_col)
            after_u16 = py_col_to_utf16(raw_line, max(first_non_ws, end_non_ws))

            goal_before = worker.plain_goal(uri, line1 - 1, before_u16)
            goal_focus = goal_before if focus_u16 == before_u16 else worker.plain_goal(uri, line1 - 1, focus_u16)
            goal_after = goal_before if after_u16 == before_u16 else worker.plain_goal(uri, line1 - 1, after_u16)
            term_goal = worker.plain_term_goal(uri, line1 - 1, focus_u16)
            diags = worker.get_diagnostics(uri)
            sorrys = find_sorry_lines(text)

        before_list = (goal_before or {}).get("goals") or []
        focus_list = (goal_focus or {}).get("goals") or []
        after_list = (goal_after or {}).get("goals") or []
        term_str = (term_goal or {}).get("goal")

        clipped_before = [middle_clip(g, 2000) for g in before_list]
        clipped_after = [middle_clip(g, 2000) for g in after_list]
        clipped_term = middle_clip(term_str, 1500) if term_str else None
        ui_goals: list[dict[str, Any]] = []
        if clipped_before:
            ui_goals.append({"label": f"Before L{line1} (`{code_only.strip()}`)", "line": line1, "column": first_non_ws + 1, "code": code_only.strip(), "goals": clipped_before})
        if clipped_after != clipped_before:
            ui_goals.append({"label": f"After L{line1}", "line": line1, "column": end_non_ws + 1, "code": code_only.strip(), "goals": clipped_after or ["no goals (closed!)"]})
        if not ui_goals and clipped_term:
            ui_goals.append({"label": f"Expected Term Type at L{line1}:{focus_py_col + 1}", "line": line1, "column": focus_py_col + 1, "code": code_only.strip(), "goals": [clipped_term]})

        self._record_infoview(
            file_path=file_path,
            lake_root=worker.lake_root,
            elapsed_ms=elapsed_ms,
            completed=completed,
            diags=diags,
            sorry_count=len(sorrys),
            goals=ui_goals,
            event_label=f"lean_goal L{line1}",
        )

        out = [
            f"File: {file_path}:{line1} ({elapsed_ms} ms)",
            f"Line {line1}: `{raw_line}`",
        ]
        if req_col is not None or snippet:
            out.append(f"\n--- Goal at requested cursor (col {focus_py_col + 1}) ---")
            out.append("\n\n".join(focus_list) if focus_list else "no tactic goals at cursor")
        out.append(f"\n--- Goal BEFORE tactic on L{line1} (col {first_non_ws + 1}) ---")
        out.append("\n\n".join(before_list) if before_list else "no tactic goals")
        out.append(f"\n--- Goal AFTER tactic on L{line1} (col {max(first_non_ws, end_non_ws) + 1}) ---")
        out.append("\n\n".join(after_list) if after_list else "no goals")
        if term_str:
            out.append(f"\n--- Term Goal (expected expression type at col {focus_py_col + 1}) ---\n{term_str}")

        line_diags = [self._compact_diag_dict(d) for d in diags if abs((d.get("range", {}).get("start", {}).get("line", -99) + 1) - line1) <= 2]
        if line_diags:
            out.append("\n--- Nearby Diagnostics ---")
            for cd in line_diags[:6]:
                out.append(f"[{cd['severity'].upper()}] L{cd['line']}:{cd['column']}: {cd['message']}")

        return {"text": middle_clip("\n".join(out)), "goals_before": clipped_before, "goals_after": clipped_after, "term_goal": clipped_term}

    # ---------------- Tool 3: lean_multi_attempt ----------------
    def tool_lean_multi_attempt(self, args: dict[str, Any]) -> dict[str, Any]:
        """Test multiple candidate tactic snippets at `line` purely via in-memory LSP `didChange`."""
        file_path = normalize_file_arg(args)
        line1 = int(args.get("line") or args.get("line_number") or 1)
        raw_tactics = args.get("tactics") or args.get("snippets") or args.get("attempts") or []
        if isinstance(raw_tactics, str):
            tactics = [t.strip() for t in raw_tactics.splitlines() if t.strip()]
        else:
            tactics = [str(t).strip() for t in raw_tactics if str(t).strip()]
        if not tactics:
            raise ValueError("Provide a non-empty `tactics` array of candidate Lean tactics/snippets.")
        tactics = tactics[:12]

        worker = self.get_lean_worker(file_path)
        results: list[dict[str, Any]] = []
        with worker.op_lock:
            uri, orig_text, _, base_ms, _ = worker.sync_disk_file(file_path, wait_timeout_s=45.0)
            orig_lines = orig_text.splitlines()
            if not (1 <= line1 <= len(orig_lines)):
                raise ValueError(f"`line` {line1} out of range (1..{len(orig_lines)}).")
            target_raw = orig_lines[line1 - 1]
            indent = target_raw[: len(target_raw) - len(target_raw.lstrip())]
            sorry_match = re.search(r"\b(sorry|admit)\b", strip_line_comment(target_raw))

            try:
                for cand in tactics:
                    t_cand = time.monotonic()
                    mod_lines = list(orig_lines)
                    cand_indented = "\n".join(
                        (indent + sub if i > 0 and not sub.startswith(indent) else sub)
                        for i, sub in enumerate(cand.splitlines())
                    )
                    if sorry_match:
                        s, e = sorry_match.span()
                        replacement_line = target_raw[:s] + cand_indented + target_raw[e:]
                    else:
                        replacement_line = indent + cand_indented
                    rep_split = replacement_line.splitlines()
                    mod_lines[line1 - 1 : line1] = rep_split
                    mod_text = "\n".join(mod_lines) + ("\n" if orig_text.endswith("\n") else "")

                    _, _, _, completed = worker.sync_text(file_path, mod_text, wait_timeout_s=15.0)
                    diags = worker.get_diagnostics(uri)
                    last_line_idx = (line1 - 1) + len(rep_split) - 1
                    last_line_str = mod_lines[last_line_idx]
                    end_u16 = py_col_to_utf16(last_line_str, len(strip_line_comment(last_line_str).rstrip()))
                    after_goal = worker.plain_goal(uri, last_line_idx, end_u16, timeout_s=5.0) if completed else None
                    goals_after = (after_goal or {}).get("goals") or []

                    cand_errs = [
                        self._compact_diag_dict(d)
                        for d in diags
                        if d.get("severity") == 1 and (line1 - 1) <= cd_line0(d) <= (last_line_idx + 2)
                    ]
                    all_errs = sum(1 for d in diags if d.get("severity") == 1)
                    dt_ms = round((time.monotonic() - t_cand) * 1000.0, 1)
                    closes_goal = completed and len(cand_errs) == 0 and len(goals_after) == 0
                    results.append(
                        {
                            "tactic": cand,
                            "closes_goal": closes_goal,
                            "ok_step": completed and len(cand_errs) == 0,
                            "remaining_goals": goals_after,
                            "errors": cand_errs,
                            "total_file_errors": all_errs,
                            "elapsed_ms": dt_ms,
                            "timed_out": not completed,
                        }
                    )
            finally:
                # Always restore exact on-disk contents in the LSP worker!
                worker.sync_text(file_path, orig_text, wait_timeout_s=15.0)

        out = [
            f"In-Memory Multi-Attempt on {file_path}:{line1} (0 disk writes; warm base {base_ms} ms)",
            f"Original L{line1}: `{target_raw.strip()}`\n",
        ]
        for idx, r in enumerate(results, start=1):
            if r["timed_out"]:
                badge = "⏱ TIMEOUT"
            elif r["closes_goal"]:
                badge = "✅ CLOSES GOAL (0 remaining goals, 0 errors)"
            elif r["ok_step"]:
                badge = f"🟢 VALID STEP ({len(r['remaining_goals'])} subgoal(s) remaining)"
            else:
                badge = f"❌ ERROR ({len(r['errors'])} local error(s))"
            out.append(f"[{idx}] `{r['tactic']}` -> {badge} ({r['elapsed_ms']} ms)")
            if r["errors"]:
                out.append(f"    Error: {r['errors'][0]['message'][:260]}")
            elif r["remaining_goals"]:
                preview = "\n    ".join(r["remaining_goals"][0].splitlines()[:8])
                out.append(f"    Remaining goal[0]:\n    {preview}")

        return {"text": middle_clip("\n".join(out)), "attempts": results}

    # ---------------- Tool 4: lean_hover ----------------
    def tool_lean_hover(self, args: dict[str, Any]) -> dict[str, Any]:
        file_path = normalize_file_arg(args)
        line1 = int(args.get("line") or args.get("line_number") or 1)
        sym_or_col = args.get("symbol") or args.get("column") or args.get("col") or args.get("symbol_or_column")

        worker = self.get_lean_worker(file_path)
        with worker.op_lock:
            uri, text, _, elapsed_ms, _ = worker.sync_disk_file(file_path, wait_timeout_s=45.0)
            lines = text.splitlines()
            line1 = max(1, min(line1, len(lines)))
            raw_line = lines[line1 - 1]
            py_col = resolve_symbol_or_col(raw_line, sym_or_col)
            res = worker.lsp.request(
                "textDocument/hover",
                {"textDocument": {"uri": uri}, "position": {"line": line1 - 1, "character": py_col_to_utf16(raw_line, py_col)}},
                timeout_s=10.0,
            )

        contents = extract_hover_markdown(res)
        header = f"Hover at {file_path}:{line1}:{py_col + 1} (`{raw_line.strip()}`) [{elapsed_ms} ms]:\n"
        return {"text": middle_clip(header + (contents or "(no hover info at this position)"))}

    # ---------------- Tool 5: lean_definition ----------------
    def tool_lean_definition(self, args: dict[str, Any]) -> dict[str, Any]:
        file_path = normalize_file_arg(args)
        line1 = int(args.get("line") or args.get("line_number") or 1)
        sym_or_col = args.get("symbol") or args.get("column") or args.get("col") or args.get("symbol_or_column")

        worker = self.get_lean_worker(file_path)
        with worker.op_lock:
            uri, text, _, elapsed_ms, _ = worker.sync_disk_file(file_path, wait_timeout_s=45.0)
            lines = text.splitlines()
            line1 = max(1, min(line1, len(lines)))
            raw_line = lines[line1 - 1]
            py_col = resolve_symbol_or_col(raw_line, sym_or_col)
            res = worker.lsp.request(
                "textDocument/definition",
                {"textDocument": {"uri": uri}, "position": {"line": line1 - 1, "character": py_col_to_utf16(raw_line, py_col)}},
                timeout_s=10.0,
            )

        locs = normalize_lsp_locations(res)
        if not locs:
            return {"text": f"No definition found at {file_path}:{line1}:{py_col + 1} (`{raw_line.strip()}`)."}
        out = [f"Definition(s) for {file_path}:{line1}:{py_col + 1} [{elapsed_ms} ms]:"]
        for loc_path, loc_line1, loc_col1 in locs[:5]:
            out.append(f"\n* {loc_path}:{loc_line1}:{loc_col1}")
            out.append(read_snippet(loc_path, loc_line1, context_lines=7))
        return {"text": middle_clip("\n".join(out)), "locations": locs}

    # ---------------- Tool 6: lean_completions ----------------
    def tool_lean_completions(self, args: dict[str, Any]) -> dict[str, Any]:
        file_path = normalize_file_arg(args)
        line1 = int(args.get("line") or args.get("line_number") or 1)
        col_arg = args.get("column") or args.get("col")

        worker = self.get_lean_worker(file_path)
        with worker.op_lock:
            uri, text, _, elapsed_ms, _ = worker.sync_disk_file(file_path, wait_timeout_s=45.0)
            lines = text.splitlines()
            line1 = max(1, min(line1, len(lines)))
            raw_line = lines[line1 - 1]
            py_col = (int(col_arg) - 1) if col_arg is not None else len(strip_line_comment(raw_line).rstrip())
            res = worker.lsp.request(
                "textDocument/completion",
                {"textDocument": {"uri": uri}, "position": {"line": line1 - 1, "character": py_col_to_utf16(raw_line, py_col)}},
                timeout_s=10.0,
            )

        items = res.get("items", []) if isinstance(res, dict) else (res if isinstance(res, list) else [])
        out = [f"Completions at {file_path}:{line1}:{py_col + 1} ({len(items)} total, showing top 30) [{elapsed_ms} ms]:"]
        for it in items[:30]:
            lbl = it.get("label", "")
            detail = (it.get("detail") or "").replace("\n", " ").strip()
            out.append(f"  - {lbl}" + (f" : {detail}" if detail else ""))
        return {"text": middle_clip("\n".join(out))}

    # ---------------- Tool 7: lean_outline ----------------
    def tool_lean_outline(self, args: dict[str, Any]) -> dict[str, Any]:
        """Instant parser-free Lean 4 declaration & signature outline (never times out)."""
        target = normalize_file_arg(args)
        p = Path(target)
        files = sorted(p.rglob("*.lean"))[:25] if p.is_dir() else [p]
        decl_re = re.compile(
            r"^\s*(?:@\[[^\]]+\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
            r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|namespace|end)\s+([^\s:({]+)(.*)"
        )
        out = [f"Lean 4 Outline for {target}:"]
        for f in files:
            if not f.is_file():
                continue
            if p.is_dir():
                out.append(f"\n## {f}")
            raw_lines = f.read_text(encoding="utf-8", errors="replace").splitlines()
            for idx, line in enumerate(raw_lines, start=1):
                m = decl_re.match(strip_line_comment(line))
                if not m:
                    continue
                kind, name, rest = m.group(1), m.group(2), m.group(3).strip()
                if kind in ("namespace", "end"):
                    out.append(f"  L{idx}: {kind} {name}")
                    continue
                # Capture multi-line signature up to `:=` or `where` (max 4 lines)
                sig_parts = [f"{kind} {name} {rest}".strip()]
                j = idx
                while j < min(len(raw_lines), idx + 3) and ":=" not in sig_parts[-1] and " where" not in sig_parts[-1]:
                    nxt = strip_line_comment(raw_lines[j]).strip()
                    if nxt:
                        sig_parts.append(nxt)
                    j += 1
                sig = " ".join(sig_parts)
                if ":=" in sig:
                    sig = sig.split(":=", 1)[0].rstrip()
                out.append(f"  L{idx}: {sig[:220]}")
        return {"text": middle_clip("\n".join(out))}

    # ---------------- Tool 8: lean_local_search ----------------
    def tool_lean_local_search(self, args: dict[str, Any]) -> dict[str, Any]:
        query = str(args.get("query") or args.get("symbol") or args.get("pattern") or "").strip()
        if not query:
            raise ValueError("Provide a non-empty `query` substring or regex.")
        scope = args.get("workspace") or args.get("scope") or args.get("path")
        roots: list[Path] = []
        if isinstance(scope, str) and scope.strip():
            sp = Path(os.path.abspath(os.path.expanduser(scope.strip())))
            crate = resolve_anneal_crate_root(str(sp))
            if crate:
                for sub in ("trusted/lean", "theory", ".anneal/generated", "anneal/proofs", "examples"):
                    cand = (crate / sub).resolve(strict=False)
                    if cand.is_dir() and cand not in roots:
                        roots.append(cand)
            if sp.is_dir() and sp not in roots:
                roots.append(sp)
            elif sp.parent.is_dir() and sp.parent not in roots:
                roots.append(sp.parent)
        else:
            projects_dir = HOME_DIR / "Projects"
            if projects_dir.is_dir():
                for user_dir in sorted(projects_dir.iterdir()):
                    for sub in ("anneal/trusted/lean", "anneal/theory", "anneal/examples"):
                        cand = user_dir / sub
                        if cand.is_dir():
                            roots.append(cand)
                            break
                    if roots:
                        break

        try:
            rx = re.compile(query, re.IGNORECASE)
        except re.error:
            rx = re.compile(re.escape(query), re.IGNORECASE)

        decl_kw = re.compile(
            r"^\s*(?:@\[[^\]]+\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
            r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom)\s+([A-Za-z0-9_'.]+)"
        )
        hits: list[str] = []
        for r in roots:
            for lf in sorted(r.rglob("*.lean")):
                if ".lake" in lf.parts:
                    continue
                try:
                    lines = lf.read_text(encoding="utf-8", errors="replace").splitlines()
                except OSError:
                    continue
                for idx, line in enumerate(lines, start=1):
                    m = decl_kw.match(line)
                    if m and (rx.search(m.group(2)) or rx.search(line)):
                        sig = line.strip()
                        if idx < len(lines) and ":=" not in sig:
                            sig += " " + lines[idx].strip()
                        sig = sig.split(":=", 1)[0].strip()
                        hits.append(f"* {lf}:{idx}\n    {sig[:200]}")
                        if len(hits) >= 35:
                            break
                if len(hits) >= 35:
                    break
        header = f"Lean 4 Declaration Search for `{query}` ({len(hits)} match(es)):"
        return {"text": middle_clip(header + "\n" + ("\n".join(hits) if hits else "(no matching declarations)"))}

    # ---------------- Tool 9: anneal_audit_preview ----------------
    def tool_anneal_audit_preview(self, args: dict[str, Any]) -> dict[str, Any]:
        """Pre-flight Anneal `TrustedBoundary` check: diagnostics, statement isolation, spec-lock, and kernel `#print axioms`."""
        file_path = normalize_file_arg(args)
        worker = self.get_lean_worker(file_path)
        crate_root = resolve_anneal_crate_root(file_path)
        spec_lock_path = (crate_root / ".anneal" / "spec-lock.json") if crate_root else None
        spec_lock_data = None
        if spec_lock_path and spec_lock_path.is_file():
            try:
                spec_lock_data = json.loads(spec_lock_path.read_text(encoding="utf-8"))
            except Exception:
                pass

        with worker.op_lock:
            uri, orig_text, _, base_ms, completed = worker.sync_disk_file(file_path, wait_timeout_s=45.0)
            base_diags = worker.get_diagnostics(uri)
            sorrys = find_sorry_lines(orig_text)

            # Detect target theorem (`verified` inside namespace, or last theorem in module)
            ns_match = re.search(r"^\s*namespace\s+([A-Za-z0-9_.]+)", orig_text, re.MULTILINE)
            thm_matches = list(re.finditer(r"^\s*theorem\s+([A-Za-z0-9_']+)([\s\S]*?):=", orig_text, re.MULTILINE))
            target_thm = None
            target_stmt = ""
            for tm in thm_matches:
                if tm.group(1) == "verified":
                    target_thm = f"{ns_match.group(1)}.verified" if ns_match else "verified"
                    target_stmt = tm.group(2)
                    break
            if target_thm is None and thm_matches:
                last_tm = thm_matches[-1]
                target_thm = f"{ns_match.group(1)}.{last_tm.group(1)}" if ns_match else last_tm.group(1)
                target_stmt = last_tm.group(2)

            # Statement-origin check: `Anneal.*` (`theory/`) must NOT leak into theorem statement type
            anneal_leak = bool(re.search(r"\bAnneal\.", target_stmt))

            # Run `#print axioms <target_thm>` purely in memory via LSP `didChange`!
            axioms_msg = "(no theorem found to inspect axioms)"
            if target_thm and completed:
                probe_text = orig_text.rstrip() + f"\n\n#print axioms {target_thm}\n"
                probe_line0 = len(probe_text.splitlines()) - 1
                try:
                    worker.sync_text(file_path, probe_text, wait_timeout_s=15.0)
                    probe_diags = worker.get_diagnostics(uri)
                    for d in probe_diags:
                        if cd_line0(d) >= probe_line0 - 1 and ("depends on axioms" in d.get("message", "") or "does not depend on any axioms" in d.get("message", "")):
                            axioms_msg = d["message"].strip()
                            break
                finally:
                    worker.sync_text(file_path, orig_text, wait_timeout_s=15.0)

        err_n = sum(1 for d in base_diags if d.get("severity") == 1)
        has_sorry_ax = "sorryAx" in axioms_msg or len(sorrys) > 0
        has_native_decide_ax = "Lean.ofReduceBool" in axioms_msg or "Lean.trustCompiler" in axioms_msg
        locked_assumptions = len((spec_lock_data or {}).get("locked_assumptions_files") or [])

        passed = (err_n == 0) and (not has_sorry_ax) and (not has_native_decide_ax) and (not anneal_leak) and completed
        audit_summary = {
            "passed": passed,
            "theorem": target_thm,
            "errors": err_n,
            "sorrys": len(sorrys),
            "statement_origin_clean": not anneal_leak,
            "axioms_report": axioms_msg,
            "has_sorryAx": has_sorry_ax,
            "has_native_decide_axiom": has_native_decide_ax,
            "spec_locked": spec_lock_data is not None,
            "locked_assumptions_count": locked_assumptions,
        }

        with self._ui_lock:
            self.infoview_state["audit"] = audit_summary

        verdict = "✅ PASS (Ready for `cargo anneal agent-verify`)" if passed else "❌ AUDIT ISSUES DETECTED"
        lines = [
            f"Anneal Audit Preview: {verdict}",
            f"File: {file_path} ({base_ms} ms)",
            f"Target theorem: `{target_thm or 'NONE'}`",
            f"1. Compiler diagnostics: {err_n} error(s)",
            f"2. `sorry` / `admit` tokens: {len(sorrys)}",
            f"3. Statement-origin isolation (`Anneal.*` absent from theorem statement): {'✅ CLEAN' if not anneal_leak else '❌ VIOLATION (`Anneal.*` referenced in theorem type)'}",
            f"4. Kernel `#print axioms`: {axioms_msg}",
            f"5. Forbidden kernel axioms (`sorryAx` / `Lean.ofReduceBool`): {'✅ NONE' if not (has_sorry_ax or has_native_decide_ax) else '❌ PRESENT'}",
            f"6. Spec lock (`.anneal/spec-lock.json`): {'🔒 ACTIVE (' + str(locked_assumptions) + ' locked assumptions)' if spec_lock_data else '🔓 UNLOCKED'}",
        ]
        return {"text": middle_clip("\n".join(lines)), "audit": audit_summary}

    # ---------------- Tool 10: anneal_item_bridge ----------------
    def tool_anneal_item_bridge(self, args: dict[str, Any]) -> dict[str, Any]:
        """Map between Rust verification items and generated/authored Lean 4 modules (`Mir`, `Obligations`, `Specs`, `Proof`)."""
        query = str(args.get("query") or args.get("item") or args.get("symbol") or "").strip().lower()
        ws_arg = args.get("workspace") or args.get("crate_root") or args.get("path") or args.get("file")

        crate_root: Path | None = None
        if isinstance(ws_arg, str) and ws_arg.strip():
            crate_root = resolve_anneal_crate_root(ws_arg.strip())
        if crate_root is None:
            # Auto-discover active `.anneal` workspaces under ~/Projects
            for lf in sorted((HOME_DIR / "Projects").glob("*/*/**/.anneal/lakefile.toml")):
                crate_root = lf.parent.parent
                break

        if crate_root is None:
            return {"text": "No initialized Anneal crate (`.anneal/`) found. Pass `workspace` pointing to the crate directory or run `cargo anneal agent-context`."}

        dot_anneal = crate_root / ".anneal"
        spec_lock_file = dot_anneal / "spec-lock.json"
        lock_data = json.loads(spec_lock_file.read_text(encoding="utf-8")) if spec_lock_file.is_file() else None
        locked_records = {r.get("lean_module_name", "").removeprefix("Mir."): r for r in (lock_data or {}).get("locked_records", [])}

        oblig_dir = dot_anneal / "generated" / "Obligations"
        items: list[dict[str, Any]] = []
        if oblig_dir.is_dir():
            for ob_file in sorted(oblig_dir.rglob("*.lean")):
                rel = ob_file.relative_to(oblig_dir).with_suffix("")
                suffix = ".".join(rel.parts)  # e.g. ZerocopySlice.BigEndianU16_new
                if query and query not in suffix.lower() and query not in (locked_records.get(suffix, {}).get("def_id", "").lower()):
                    continue
                mir_f = dot_anneal / "generated" / "Mir" / rel.with_suffix(".lean")
                spec_f = crate_root / "anneal" / "proofs" / "Specs" / rel.with_suffix(".lean")
                proof_f = crate_root / "anneal" / "proofs" / "Proof" / rel.with_suffix(".lean")
                spec_txt = spec_f.read_text(encoding="utf-8", errors="ignore") if spec_f.is_file() else ""
                proof_exists = proof_f.is_file()
                proof_txt = proof_f.read_text(encoding="utf-8", errors="ignore") if proof_exists else ""
                is_stateful = bool(
                    re.search(r"\b(StatefulItemSpec|refineStatefulSpec|refineSafeStatefulSpec)\b", spec_txt)
                    or re.search(r"\b(StatefulVerificationResult|statefulClaim)\b", proof_txt)
                )
                item_kind = locked_records.get(suffix, {}).get("item_kind") or "subject"
                proof_sorrys = len(find_sorry_lines(proof_txt)) if proof_exists else None
                items.append(
                    {
                        "suffix": suffix,
                        "def_id": locked_records.get(suffix, {}).get("def_id"),
                        "item_kind": item_kind,
                        "is_stateful": is_stateful,
                        "mir_file": str(mir_f) if mir_f.is_file() else None,
                        "obligations_file": str(ob_file),
                        "spec_file": str(spec_f) if spec_f.is_file() else None,
                        "proof_file": str(proof_f),
                        "proof_exists": proof_exists,
                        "proof_sorrys": proof_sorrys,
                    }
                )

        complete_n = sum(1 for it in items if it["proof_exists"] and it["proof_sorrys"] == 0)
        lines = [
            f"Anneal Crate Bridge: {crate_root}",
            f"Spec Lock: {'🔒 LOCKED (' + str(spec_lock_file) + ')' if lock_data else '🔓 UNLOCKED'}",
            f"Matched Obligations: {len(items)} ({complete_n} proof-files present with 0 `sorry` tokens)",
        ]
        for it in items[:25]:
            kind_lbl = "Stateful" if it["is_stateful"] else "Stateless"
            if not it["proof_exists"]:
                p_badge = "⬜ MISSING PROOF"
            elif it["proof_sorrys"] == 0:
                p_badge = "✅ PROOF PRESENT (0 sorry)"
            else:
                p_badge = f"🟡 IN PROGRESS ({it['proof_sorrys']} sorry)"
            lines.append(f"\n* `{it['suffix']}` [{kind_lbl}] — {p_badge}")
            if it["def_id"]:
                lines.append(f"  Rust DefId: `{it['def_id']}`")
            lines.append(f"  Proof: {it['proof_file']}")
            lines.append(f"  Obligations: {it['obligations_file']}")
            if it["spec_file"]:
                lines.append(f"  Locked Spec: {it['spec_file']}")
            if it["mir_file"]:
                lines.append(f"  Lowered MIR: {it['mir_file']}")
        return {"text": middle_clip("\n".join(lines)), "crate_root": str(crate_root), "locked": lock_data is not None, "items": items[:50]}

    # ---------------- Tool 11: rust_diagnostics ----------------
    def tool_rust_diagnostics(self, args: dict[str, Any]) -> dict[str, Any]:
        target = normalize_file_arg(args)
        cargo_root = resolve_cargo_root(target)
        if cargo_root is None:
            raise ValueError(f"Could not find enclosing `Cargo.toml` for `{target}`.")

        ra_worker = self.get_rust_worker(target)
        if ra_worker is not None and Path(target).is_file() and target.endswith(".rs"):
            uri, _ = ra_worker.sync_disk_file(target)
            time.sleep(0.25)
            with ra_worker._diag_cond:
                diags = list(ra_worker.diagnostics.get(uri, []))
            lines = [f"Rust Diagnostics via `rust-analyzer` for {target} ({len(diags)} diagnostic(s)):"]
            for d in diags[:25]:
                cd = self._compact_diag_dict(d)
                lines.append(f"[{cd['severity'].upper()}] L{cd['line']}:{cd['column']}: {cd['message']}")
            return {"text": middle_clip("\n".join(lines)), "engine": "rust-analyzer"}

        # Offline fallback: `cargo check --offline --message-format=json`
        t0 = time.monotonic()
        env = os.environ.copy()
        env["PATH"] = f"{DEFAULT_ENV_PATH}:{env.get('PATH', '')}"
        cargo_bin = shutil.which("cargo", path=DEFAULT_ENV_PATH) or str(HOME_DIR / ".cargo/bin/cargo")
        res = subprocess.run(
            [cargo_bin, "check", "--offline", "--message-format=json"],
            cwd=str(cargo_root),
            env=env,
            capture_output=True,
            text=True,
            timeout=90.0,
        )
        elapsed_ms = round((time.monotonic() - t0) * 1000.0, 1)
        msgs: list[str] = []
        err_n = 0
        warn_n = 0
        for raw in res.stdout.splitlines():
            if not raw.startswith("{"):
                continue
            try:
                obj = json.loads(raw)
            except json.JSONDecodeError:
                continue
            if obj.get("reason") != "compiler-message":
                continue
            m = obj.get("message") or {}
            level = m.get("level", "info")
            if level == "error":
                err_n += 1
            elif level == "warning":
                warn_n += 1
            spans = m.get("spans") or []
            primary = next((s for s in spans if s.get("is_primary")), spans[0] if spans else {})
            loc = f"{primary.get('file_name', '?')}:{primary.get('line_start', '?')}:{primary.get('column_start', '?')}"
            msgs.append(f"[{level.upper()}] {loc}: {m.get('message', '')}")

        header = (
            f"Rust Workspace Check (`cargo check --offline`, {elapsed_ms} ms) in {cargo_root}:\n"
            f"Summary: {err_n} error(s), {warn_n} warning(s) (exit {res.returncode})"
        )
        body = "\n".join(msgs[:25]) if msgs else "✓ Clean (`0` compiler errors)."
        if res.returncode != 0 and not msgs and res.stderr.strip():
            body = res.stderr.strip()
        return {"text": middle_clip(header + "\n" + body), "engine": "cargo-check-json", "errors": err_n, "warnings": warn_n}

    # ---------------- Tool 12: rust_symbols_and_def ----------------
    def tool_rust_symbols_and_def(self, args: dict[str, Any]) -> dict[str, Any]:
        """Rust symbol outline, workspace search, hover doc/attribute inspection, and go-to-definition."""
        raw_target = args.get("file") or args.get("path") or args.get("workspace")
        query = str(args.get("query") or args.get("symbol") or "").strip()
        line_arg = args.get("line") or args.get("line_number")

        target_path = normalize_file_arg(args) if raw_target else str(HOME_DIR / "Projects")
        ra_worker = self.get_rust_worker(target_path) if Path(target_path).exists() else None

        # 1. If rust-analyzer is live and a specific file + line is given, use LSP hover + definition!
        if ra_worker is not None and Path(target_path).is_file() and line_arg is not None:
            line1 = int(line_arg)
            uri, text = ra_worker.sync_disk_file(target_path)
            raw_line = text.splitlines()[max(0, min(line1 - 1, len(text.splitlines()) - 1))]
            py_col = resolve_symbol_or_col(raw_line, query or args.get("column"))
            pos = {"line": line1 - 1, "character": py_col_to_utf16(raw_line, py_col)}
            hov = extract_hover_markdown(ra_worker.lsp.request("textDocument/hover", {"textDocument": {"uri": uri}, "position": pos}, timeout_s=10.0))
            defs = normalize_lsp_locations(ra_worker.lsp.request("textDocument/definition", {"textDocument": {"uri": uri}, "position": pos}, timeout_s=10.0))
            out = [f"Rust LSP (`rust-analyzer`) at {target_path}:{line1}:{py_col + 1}:"]
            if hov:
                out.append(hov)
            for dp, dl, dc in defs[:4]:
                out.append(f"\nDefinition: {dp}:{dl}:{dc}\n" + read_snippet(dp, dl, 8))
            return {"text": middle_clip("\n".join(out)), "engine": "rust-analyzer"}

        # 2. Fast built-in Rust item + `#[anneal...]` / `#[spec]` attribute indexer
        p = Path(target_path)
        if p.is_file() and line_arg is not None and not query:
            lines = p.read_text(encoding="utf-8", errors="replace").splitlines()
            l1 = max(1, min(int(line_arg), len(lines)))
            col0 = resolve_symbol_or_col(lines[l1 - 1], args.get("column"))
            m_tok = re.search(r"[A-Za-z_][A-Za-z0-9_]*", lines[l1 - 1][max(0, col0 - 1) :])
            if m_tok:
                query = m_tok.group(0)

        search_root = resolve_cargo_root(target_path) or (p if p.is_dir() else p.parent)
        rs_files = [p] if (p.is_file() and not query) else sorted(search_root.rglob("*.rs"))
        item_re = re.compile(
            r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?(?:async\s+)?(?:unsafe\s+)?"
            r"(fn|struct|enum|trait|type|const|static|mod|impl|macro_rules!)\s+([A-Za-z_][A-Za-z0-9_]*)"
        )
        hits: list[str] = []
        for rf in rs_files:
            if "target" in rf.parts or ".git" in rf.parts:
                continue
            try:
                rlines = rf.read_text(encoding="utf-8", errors="replace").splitlines()
            except OSError:
                continue
            for idx, rline in enumerate(rlines, start=1):
                m = item_re.match(rline)
                if not m:
                    continue
                kind, name = m.group(1), m.group(2)
                if query and query.lower() not in name.lower():
                    continue
                # Collect preceding doc comments (`///`) and attributes (`#[...]`)
                attrs: list[str] = []
                k = idx - 2
                while k >= 0 and (rlines[k].strip().startswith("#[") or rlines[k].strip().startswith("///")):
                    attrs.insert(0, rlines[k].strip())
                    k -= 1
                attr_preview = ("\n    " + "\n    ".join(attrs[-4:])) if attrs else ""
                hits.append(f"* {rf}:{idx} [{kind} `{name}`]{attr_preview}\n    {rline.strip()}")
                if len(hits) >= 30:
                    break
            if len(hits) >= 30:
                break

        note = "" if self.ra_bin else " (static Rust indexer; `rust-analyzer` component not installed in nightly-2026-06-01)"
        title = f"Rust Symbols{' matching `' + query + '`' if query else ''} in {search_root}{note}:"
        return {"text": middle_clip(title + "\n" + ("\n".join(hits) if hits else "(no matching Rust items)"))}

    # ---------------- Hook & UI Sidecar Fast Endpoints ----------------
    def hook_post_edit(self, args: dict[str, Any]) -> dict[str, Any]:
        """Fast `<3.5s` PostToolUse handler for `.lean` edits."""
        file_path = normalize_file_arg(args)
        budget_s = float(args.get("timeout_s", 3.5))
        worker = self.get_lean_worker(file_path)
        with worker.op_lock:
            uri, text, _, elapsed_ms, completed = worker.sync_disk_file(file_path, wait_timeout_s=budget_s)
            diags = worker.get_diagnostics(uri)
            sorrys = find_sorry_lines(text)
            sorry_goals = self._collect_sorry_goals(worker, uri, text, limit=3) if completed else []

        self._record_infoview(
            file_path=file_path,
            lake_root=worker.lake_root,
            elapsed_ms=elapsed_ms,
            completed=completed,
            diags=diags,
            sorry_count=len(sorrys),
            goals=sorry_goals,
            event_label="PostToolUse auto-check",
        )

        if not completed:
            return {
                "feedback": (
                    f"[Anneal Lean 4 LSP] Warming imports for `{os.path.basename(file_path)}` in background "
                    f"(>{budget_s:.1f}s cold import); call `lean_diagnostics` or `lean_goal` in a moment."
                )
            }

        errs = [self._compact_diag_dict(d) for d in diags if d.get("severity") == 1]
        warns = [self._compact_diag_dict(d) for d in diags if d.get("severity") == 2]
        if not errs and not sorrys:
            return {
                "feedback": (
                    f"[Anneal Lean 4 LSP ✓] `{os.path.basename(file_path)}` elaborated cleanly in {elapsed_ms} ms "
                    f"(0 errors, {len(warns)} warning(s), 0 `sorry` tokens)."
                )
            }

        parts = [
            f"[Anneal Lean 4 LSP] `{os.path.basename(file_path)}` ({elapsed_ms} ms): "
            f"{len(errs)} error(s), {len(warns)} warning(s), {len(sorrys)} `sorry` token(s)."
        ]
        for e in errs[:4]:
            parts.append(f"  [ERROR L{e['line']}:{e['column']}] {e['message'][:240]}")
        for sg in sorry_goals[:2]:
            g_str = sg["goals"][0] if sg["goals"] else "(no tactic goal)"
            parts.append(f"  [OPEN GOAL {sg['label']}]\n" + "\n".join("    " + gl for gl in g_str.splitlines()[:10]))
        return {"feedback": middle_clip("\n".join(parts), max_bytes=1600)}

    def get_ui_state(self) -> dict[str, Any]:
        with self._pool_lock:
            workers = [w.status_dict() for w in self.lean_workers.values()] + [
                rw.status_dict() for rw in self.rust_workers.values()
            ]
        with self._ui_lock:
            iv = dict(self.infoview_state)
        return {
            "daemon_pid": os.getpid(),
            "script_sha256": SCRIPT_SHA256,
            "uptime_s": round(time.time() - self.started_at, 1),
            "rust_analyzer_available": self.ra_bin is not None,
            "rust_analyzer_bin": self.ra_bin,
            "workers": workers,
            "infoview": iv,
        }

    def restart_worker(self, args: dict[str, Any]) -> dict[str, Any]:
        target = args.get("root") or args.get("file") or args.get("path")
        closed_roots: list[str] = []
        to_close: list[Any] = []
        with self._pool_lock:
            if not target or target == "all":
                for k, w in list(self.lean_workers.items()):
                    closed_roots.append(k)
                    to_close.append(self.lean_workers.pop(k))
                for k, rw in list(self.rust_workers.items()):
                    closed_roots.append(k)
                    to_close.append(self.rust_workers.pop(k))
            else:
                lr = resolve_lake_root(str(target))
                key = str(lr.resolve()) if lr else str(Path(str(target)).resolve())
                if key in self.lean_workers:
                    closed_roots.append(key)
                    to_close.append(self.lean_workers.pop(key))
                if key in self.rust_workers:
                    closed_roots.append(key)
                    to_close.append(self.rust_workers.pop(key))
        for w in to_close:
            try:
                w.close()
            except Exception:
                pass
        return {"text": f"Restarted {len(closed_roots)} LSP worker(s): {closed_roots or '(none active)'}", "restarted": closed_roots}

    def shutdown_all(self) -> None:
        with self._pool_lock:
            all_w = list(self.lean_workers.values()) + list(self.rust_workers.values())
            self.lean_workers.clear()
            self.rust_workers.clear()
        for w in all_w:
            try:
                w.close()
            except Exception:
                pass


def cd_line0(diag: dict[str, Any]) -> int:
    return int(((diag.get("range") or {}).get("start") or {}).get("line", 0))


def resolve_symbol_or_col(raw_line: str, sym_or_col: Any) -> int:
    if sym_or_col is None:
        return len(raw_line) - len(raw_line.lstrip())
    if isinstance(sym_or_col, int) or (isinstance(sym_or_col, str) and sym_or_col.strip().isdigit()):
        return max(0, int(sym_or_col) - 1)
    sym = str(sym_or_col).strip()
    idx = raw_line.find(sym)
    if idx >= 0:
        return idx
    return len(raw_line) - len(raw_line.lstrip())


def extract_hover_markdown(res: Any) -> str:
    if not isinstance(res, dict):
        return ""
    contents = res.get("contents")
    if isinstance(contents, dict):
        return str(contents.get("value") or "").strip()
    if isinstance(contents, list):
        parts = [c.get("value", "") if isinstance(c, dict) else str(c) for c in contents]
        return "\n\n".join(p.strip() for p in parts if p.strip())
    if isinstance(contents, str):
        return contents.strip()
    return ""


def normalize_lsp_locations(res: Any) -> list[tuple[str, int, int]]:
    if not res:
        return []
    items = res if isinstance(res, list) else [res]
    out: list[tuple[str, int, int]] = []
    for it in items:
        if not isinstance(it, dict):
            continue
        uri = it.get("uri") or it.get("targetUri") or ""
        rng = it.get("targetSelectionRange") or it.get("targetRange") or it.get("range") or {}
        start = rng.get("start") or {}
        if uri:
            out.append((uri_to_path(uri), int(start.get("line", 0)) + 1, int(start.get("character", 0)) + 1))
    return out


def read_snippet(file_path: str, center_line1: int, context_lines: int = 6) -> str:
    try:
        lines = Path(file_path).read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return "  (unable to read target file)"
    lo = max(1, center_line1 - 1)
    hi = min(len(lines), center_line1 + context_lines)
    return "\n".join(f"  {ln:4d} | {lines[ln - 1]}" for ln in range(lo, hi + 1))


class ThreadedUnixServer(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
    daemon_threads = True


def serve_daemon(sock_path: str = DEFAULT_SOCKET_PATH) -> None:
    coordinator = AnnealLspCoordinator()
    try:
        os.unlink(sock_path)
    except FileNotFoundError:
        pass

    dispatch = {
        "lean_diagnostics": coordinator.tool_lean_diagnostics,
        "lean_goal": coordinator.tool_lean_goal,
        "lean_multi_attempt": coordinator.tool_lean_multi_attempt,
        "lean_hover": coordinator.tool_lean_hover,
        "lean_definition": coordinator.tool_lean_definition,
        "lean_completions": coordinator.tool_lean_completions,
        "lean_outline": coordinator.tool_lean_outline,
        "lean_local_search": coordinator.tool_lean_local_search,
        "anneal_audit_preview": coordinator.tool_anneal_audit_preview,
        "anneal_item_bridge": coordinator.tool_anneal_item_bridge,
        "rust_diagnostics": coordinator.tool_rust_diagnostics,
        "rust_symbols_and_def": coordinator.tool_rust_symbols_and_def,
        "lean_restart_workspace": coordinator.restart_worker,
        "hook_post_edit": coordinator.hook_post_edit,
    }

    server_ref: list[ThreadedUnixServer] = []

    class Handler(socketserver.StreamRequestHandler):
        def handle(self) -> None:
            raw = self.rfile.readline()
            if not raw:
                return
            try:
                req = json.loads(raw.decode("utf-8", errors="replace"))
                action = req.get("action")
                args = req.get("args") or {}
                if action == "ping":
                    resp = {"ok": True, "pid": os.getpid(), "script_sha256": SCRIPT_SHA256}
                elif action == "ui_state":
                    resp = {"ok": True, "result": coordinator.get_ui_state()}
                elif action == "shutdown":
                    resp = {"ok": True, "shutting_down": True}
                    self.wfile.write((json.dumps(resp) + "\n").encode("utf-8"))
                    self.wfile.flush()
                    threading.Thread(target=lambda: server_ref[0].shutdown(), daemon=True).start()
                    return
                elif action in dispatch:
                    resp = {"ok": True, "result": dispatch[action](args)}
                else:
                    resp = {"ok": False, "error": f"Unknown daemon action: {action}"}
            except Exception as exc:
                resp = {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
            try:
                self.wfile.write((json.dumps(resp) + "\n").encode("utf-8"))
                self.wfile.flush()
            except BrokenPipeError:
                pass

    srv = ThreadedUnixServer(sock_path, Handler)
    os.chmod(sock_path, 0o600)
    server_ref.append(srv)

    def _sig_handler(_signum: int, _frame: Any) -> None:
        threading.Thread(target=srv.shutdown, daemon=True).start()

    signal.signal(signal.SIGTERM, _sig_handler)
    signal.signal(signal.SIGINT, _sig_handler)
    try:
        srv.serve_forever()
    finally:
        coordinator.shutdown_all()
        try:
            os.unlink(sock_path)
        except OSError:
            pass


def daemon_rpc(action: str, args: dict[str, Any] | None = None, timeout_s: float = 120.0, sock_path: str = DEFAULT_SOCKET_PATH) -> dict[str, Any]:
    ensure_daemon_running(sock_path=sock_path)
    return _raw_unix_call(action, args or {}, timeout_s=timeout_s, sock_path=sock_path)


def _raw_unix_call(action: str, args: dict[str, Any], timeout_s: float, sock_path: str) -> dict[str, Any]:
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as s:
        s.settimeout(timeout_s)
        s.connect(sock_path)
        payload = json.dumps({"action": action, "args": args}) + "\n"
        s.sendall(payload.encode("utf-8"))
        buf = bytearray()
        while True:
            chunk = s.recv(65536)
            if not chunk:
                break
            buf.extend(chunk)
            if b"\n" in chunk:
                break
    line = bytes(buf).split(b"\n", 1)[0]
    return json.loads(line.decode("utf-8", errors="replace"))


def ensure_daemon_running(sock_path: str = DEFAULT_SOCKET_PATH) -> None:
    disk_sha = compute_script_sha256()
    try:
        ping = _raw_unix_call("ping", {}, timeout_s=2.0, sock_path=sock_path)
        if ping.get("ok") and ping.get("script_sha256") == disk_sha:
            return
    except Exception:
        ping = None

    os.makedirs(os.path.dirname(LOCK_PATH) or "/tmp", exist_ok=True)
    with open(LOCK_PATH, "w", encoding="utf-8") as lf:
        fcntl.flock(lf.fileno(), fcntl.LOCK_EX)
        disk_sha = compute_script_sha256()
        try:
            ping2 = _raw_unix_call("ping", {}, timeout_s=2.0, sock_path=sock_path)
            if ping2.get("ok"):
                if ping2.get("script_sha256") == disk_sha:
                    return
                try:
                    _raw_unix_call("shutdown", {}, timeout_s=2.0, sock_path=sock_path)
                    time.sleep(0.25)
                except Exception:
                    pass
        except Exception:
            pass

        mem_max = os.environ.get("ANNEAL_LSP_MEMORY_MAX", "48G")
        daemon_cmd = [sys.executable, os.path.abspath(__file__), "--serve", "--socket", sock_path]
        systemd_run = "/usr/bin/systemd-run" if Path("/usr/bin/systemd-run").is_file() else None
        spawned = False
        if systemd_run:
            scoped_cmd = [
                systemd_run,
                "--user",
                "--scope",
                "--quiet",
                "-p", f"MemoryMax={mem_max}",
                "-p", "MemorySwapMax=0",
                "-p", "OOMPolicy=continue",
                "--",
                *daemon_cmd,
            ]
            try:
                log_f = open("/tmp/anneal-lean-lsp-daemon.log", "ab")
                subprocess.Popen(scoped_cmd, stdin=subprocess.DEVNULL, stdout=log_f, stderr=log_f, start_new_session=True)
                spawned = True
            except Exception:
                spawned = False
        if not spawned:
            log_f = open("/tmp/anneal-lean-lsp-daemon.log", "ab")
            subprocess.Popen(daemon_cmd, stdin=subprocess.DEVNULL, stdout=log_f, stderr=log_f, start_new_session=True)

        deadline = time.monotonic() + 5.0
        while time.monotonic() < deadline:
            try:
                p = _raw_unix_call("ping", {}, timeout_s=0.5, sock_path=sock_path)
                if p.get("ok"):
                    return
            except Exception:
                time.sleep(0.08)
        raise RuntimeError("Failed to start `anneal_lsp_daemon.py` on " + sock_path)


if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--serve", action="store_true", help="Run the Unix socket daemon in foreground")
    ap.add_argument("--socket", default=DEFAULT_SOCKET_PATH, help="Unix domain socket path")
    ap.add_argument("--call", help="Invoke a single daemon action and print JSON")
    ap.add_argument("--args", default="{}", help="JSON arguments for --call")
    ns = ap.parse_args()
    if ns.serve:
        serve_daemon(sock_path=ns.socket)
    elif ns.call:
        print(json.dumps(daemon_rpc(ns.call, json.loads(ns.args), sock_path=ns.socket), indent=2))
    else:
        ensure_daemon_running(sock_path=ns.socket)
        print(json.dumps(_raw_unix_call("ping", {}, timeout_s=2.0, sock_path=ns.socket)))
