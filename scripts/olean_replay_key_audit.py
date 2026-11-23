#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Real Lean 4.34.1 `.olean` replay-key, mutual-`.all`, extension, source, and kernel-replay auditor.

Stages a read-only Lean 4.34.1 inspector inside `tempfile.TemporaryDirectory()` (never calling
`enableInitializersExecution` on untrusted `.olean` modules) to inspect real deserialized
`ModuleData`, `SMap` constant tables (`map₁` and `map₂`), persistent environment extensions,
import DAGs, direct constant-closure axiom cones, defense-in-depth source lexing + AST parsing,
and clean-environment `baseEnv.toKernelEnv.replay`.
"""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import argparse
import errno
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import tempfile
import time
from typing import Any, Mapping, Sequence


SCHEMA_VERSION = 1
PINNED_TOOLCHAIN = "leanprover/lean4:v4.34.1"
PINNED_LEAN_REL = ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
REPO_ROOT = Path(__file__).resolve().parent.parent
FIXTURES_DIR = REPO_ROOT / "tests" / "audit_tamper_fixtures"
CHILD_TIMEOUT_SEC = 180

PRESERVED_ENV_EXACT: frozenset[str] = frozenset(
    {
        "HOME",
        "USER",
        "LOGNAME",
        "PATH",
        "TMPDIR",
        "TEMP",
        "TMP",
        "XDG_RUNTIME_DIR",
        "XDG_CONFIG_HOME",
        "XDG_CACHE_HOME",
        "LANG",
        "LC_ALL",
    }
)
PRESERVED_ENV_PREFIXES: tuple[str, ...] = ("ANNEAL_LEAN_RUN_",)
SCRUBBED_ENV_PREFIXES: tuple[str, ...] = ("LEAN", "LAKE", "ELAN", "DYLD_", "LD_PRELOAD")


class AuditOperationalError(Exception):
    """Operational / CLI / toolchain / fail-closed filesystem error (exit code 2)."""


class AuditPolicyError(Exception):
    """Deterministic policy / tamper violation (exit code 1)."""

    def __init__(self, category: str, module: str, detail: str, names: list[str] | None = None):
        super().__init__(f"{category} in {module}: {detail}" if detail else f"{category} in {module}")
        self.category = category
        self.module = module
        self.detail = detail
        self.names = list(names or ([module] if module else []))

    def to_dict(self) -> dict[str, Any]:
        return {
            "category": self.category,
            "code": self.category,
            "module": self.module,
            "names": self.names,
            "detail": self.detail,
        }


# ---------------------------------------------------------------------------
# Fail-closed filesystem stat helpers (`zerocopy#4161`)
# ---------------------------------------------------------------------------


def _check_intermediate_dirs_fail_closed(
    path: Path, base_dir: Path, *, allow_symlink: bool = False
) -> bool:
    """Walks components from `base_dir` to `path.parent` via `os.lstat`.

    Returns False if an intermediate component is genuinely missing (`ENOENT`),
    and raises `AuditOperationalError` on any non-`ENOENT` `OSError`, disallowed
    symlink, or non-directory component.
    """
    try:
        rel_parts = path.parent.relative_to(base_dir).parts
    except ValueError:
        return True

    cur = base_dir
    for part in rel_parts:
        if part in ("", "."):
            continue
        if part == "..":
            raise AuditOperationalError(f"parent traversal '..' disallowed under {base_dir}: {path}")
        cur = cur / part
        try:
            st = os.lstat(cur)
        except OSError as exc:
            if exc.errno == errno.ENOENT:
                return False
            raise AuditOperationalError(
                f"filesystem error inspecting path component {cur}: {exc}"
            ) from exc
        if stat.S_ISLNK(st.st_mode):
            if not allow_symlink:
                raise AuditOperationalError(f"disallowed symlink in path component: {cur}")
            try:
                st = os.stat(cur)
            except OSError as exc:
                raise AuditOperationalError(
                    f"broken or inaccessible symlink directory {cur}: {exc}"
                ) from exc
        if not stat.S_ISDIR(st.st_mode):
            raise AuditOperationalError(
                f"non-directory intermediate component (mode={oct(st.st_mode)}): {cur}"
            )
    return True


def stat_regular_fail_closed(
    path: Path,
    *,
    base_dir: Path | None = None,
    allow_symlink: bool = False,
) -> os.stat_result | None:
    """Fail-closed regular-file stat & readability verification (`zerocopy#4161`).

    - Returns `None` ONLY on genuine `FileNotFoundError` (`errno.ENOENT`).
    - Raises `AuditOperationalError` (exit code 2) on ANY non-`ENOENT` `OSError`
      (`PermissionError`/`EACCES`, `ELOOP`, `ENOTDIR`, `ENAMETOOLONG`, `EIO`),
      any non-regular `lstat` mode (symlink when disallowed, broken symlink,
      directory, FIFO, socket, device), unreadable file permissions, or TOCTOU swap.
    """
    p = Path(path)
    if base_dir is not None:
        if not _check_intermediate_dirs_fail_closed(p, Path(base_dir), allow_symlink=allow_symlink):
            return None

    try:
        st = os.lstat(p)
    except OSError as exc:
        if exc.errno == errno.ENOENT:
            return None
        raise AuditOperationalError(f"filesystem error inspecting {p}: {exc}") from exc

    if stat.S_ISLNK(st.st_mode):
        if not allow_symlink:
            raise AuditOperationalError(f"disallowed symlink artifact: {p}")
        try:
            st = os.stat(p)
        except OSError as exc:
            raise AuditOperationalError(
                f"broken or inaccessible symlink {p}: {exc}"
            ) from exc

    if not stat.S_ISREG(st.st_mode):
        raise AuditOperationalError(
            f"expected regular file, found mode {oct(st.st_mode)}: {p}"
        )

    open_flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0)
    if not allow_symlink:
        open_flags |= getattr(os, "O_NOFOLLOW", 0)

    fd: int | None = None
    try:
        fd = os.open(p, open_flags)
        fst = os.fstat(fd)
        if not stat.S_ISREG(fst.st_mode):
            raise AuditOperationalError(
                f"TOCTOU non-regular file after open (mode={oct(fst.st_mode)}): {p}"
            )
        if (fst.st_dev, fst.st_ino) != (st.st_dev, st.st_ino):
            raise AuditOperationalError(f"TOCTOU inode change detected while opening {p}")
        _ = os.read(fd, 1)
    except AuditOperationalError:
        raise
    except OSError as exc:
        raise AuditOperationalError(f"cannot read regular file {p}: {exc}") from exc
    finally:
        if fd is not None:
            try:
                os.close(fd)
            except OSError:
                pass

    return st


def stat_dir_fail_closed(path: Path, *, allow_symlink: bool = False) -> os.stat_result:
    """Fail-closed directory stat & search/read permission verification."""
    p = Path(path)
    try:
        st = os.lstat(p)
    except OSError as exc:
        raise AuditOperationalError(f"cannot access directory {p}: {exc}") from exc

    if stat.S_ISLNK(st.st_mode):
        if not allow_symlink:
            raise AuditOperationalError(f"disallowed symlink directory: {p}")
        try:
            st = os.stat(p)
        except OSError as exc:
            raise AuditOperationalError(f"broken symlink directory {p}: {exc}") from exc

    if not stat.S_ISDIR(st.st_mode):
        raise AuditOperationalError(f"expected directory, found mode {oct(st.st_mode)}: {p}")

    try:
        _ = os.listdir(p)
    except OSError as exc:
        raise AuditOperationalError(f"cannot list directory {p}: {exc}") from exc

    return st


def probe_entry_exists_fail_closed(path: Path) -> bool:
    """Returns True if any filesystem entry exists at `path` (regular, dir, etc.),
    False ONLY on `ENOENT`, and raises `AuditOperationalError` on any other `OSError`
    or symlink."""
    try:
        st = os.lstat(path)
    except OSError as exc:
        if exc.errno == errno.ENOENT:
            return False
        raise AuditOperationalError(f"filesystem error probing {path}: {exc}") from exc
    if stat.S_ISLNK(st.st_mode):
        raise AuditOperationalError(f"disallowed symlink entry in search root: {path}")
    return True


# ---------------------------------------------------------------------------
# Subprocess environment & `anneal-lean-run` resolution
# ---------------------------------------------------------------------------


def build_sanitized_lean_env(base_env: Mapping[str, str] | None = None) -> dict[str, str]:
    """Sanitizes subprocess env (`LEAN_PATH`/`LAKE_*`/`ELAN_*` scrubbed) while preserving
    `ANNEAL_LEAN_RUN_*`, `XDG_RUNTIME_DIR`, and `PATH` for re-entrant `_exec_passthrough`."""
    raw = os.environ if base_env is None else base_env
    clean: dict[str, str] = {}
    for k, v in raw.items():
        if any(k.startswith(pref) for pref in PRESERVED_ENV_PREFIXES):
            clean[k] = v
            continue
        if any(k.startswith(pref) for pref in SCRUBBED_ENV_PREFIXES):
            continue
        if k in PRESERVED_ENV_EXACT:
            clean[k] = v

    home = clean.get("HOME") or str(Path.home())
    clean["HOME"] = home
    extra_bins = [
        str(Path(home) / ".local" / "bin"),
        str(Path(home) / ".elan" / "bin"),
    ]
    cur_path = clean.get("PATH", "")
    path_parts = [p for p in cur_path.split(os.pathsep) if p]
    for b in reversed(extra_bins):
        if b not in path_parts:
            path_parts.insert(0, b)
    if "/usr/bin" not in path_parts:
        path_parts.append("/usr/bin")
    if "/bin" not in path_parts:
        path_parts.append("/bin")
    clean["PATH"] = os.pathsep.join(path_parts)
    return clean


def resolve_anneal_lean_run() -> Path:
    """Resolves `anneal-lean-run` wrapper (repo `scripts/anneal-lean-run` or `~/.local/bin`)."""
    candidates = [
        REPO_ROOT / "scripts" / "anneal-lean-run",
        Path.home() / ".local" / "bin" / "anneal-lean-run",
    ]
    which_hit = shutil.which("anneal-lean-run")
    if which_hit:
        candidates.append(Path(which_hit))
    for cand in candidates:
        if cand.is_file() and os.access(cand, os.X_OK):
            return cand.resolve()
    raise AuditOperationalError("cannot locate executable `anneal-lean-run` wrapper")


def resolve_lean_toolchain(explicit_lean: Path | None = None) -> tuple[Path, Path]:
    """Returns `(lean_bin, sysroot)` verified against pinned `leanprover/lean4:v4.34.1`."""
    if explicit_lean is not None:
        if not explicit_lean.is_absolute():
            raise AuditOperationalError("--lean path must be absolute")
        lean_bin = explicit_lean
    else:
        lean_bin = Path.home() / PINNED_LEAN_REL

    st = stat_regular_fail_closed(lean_bin, allow_symlink=True)
    if st is None or not os.access(lean_bin, os.X_OK):
        raise AuditOperationalError(f"pinned Lean binary not found or not executable: {lean_bin}")

    env = build_sanitized_lean_env()
    try:
        ver = subprocess.run(
            [str(lean_bin), "--version"],
            env=env,
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        pref = subprocess.run(
            [str(lean_bin), "--print-prefix"],
            env=env,
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise AuditOperationalError(f"failed probing Lean binary {lean_bin}: {exc}") from exc

    if ver.returncode != 0 or "4.34.1" not in ver.stdout:
        raise AuditOperationalError(
            f"unexpected Lean version (expected 4.34.1): {ver.stdout.strip() or ver.stderr.strip()}"
        )
    if pref.returncode != 0 or not pref.stdout.strip():
        raise AuditOperationalError(f"failed querying Lean --print-prefix: {pref.stderr.strip()}")
    sysroot = Path(pref.stdout.strip())
    stat_dir_fail_closed(sysroot / "lib" / "lean", allow_symlink=True)
    return lean_bin, sysroot


def run_governed_cmd(
    argv: Sequence[str],
    *,
    cwd: Path,
    extra_env: Mapping[str, str] | None = None,
    mode: str = "file",
    timeout_sec: int = CHILD_TIMEOUT_SEC,
) -> subprocess.CompletedProcess[str]:
    """Executes `argv` through `anneal-lean-run` with sanitized environment."""
    wrapper = resolve_anneal_lean_run()
    env = build_sanitized_lean_env()
    if extra_env:
        env.update(extra_env)
    full_cmd = [str(wrapper), "--mode", mode, "--", *argv]
    try:
        return subprocess.run(
            full_cmd,
            cwd=str(cwd),
            env=env,
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=timeout_sec,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise AuditOperationalError(
            f"governed subprocess timed out after {timeout_sec}s: {' '.join(argv)}"
        ) from exc
    except OSError as exc:
        raise AuditOperationalError(f"failed executing governed subprocess: {exc}") from exc


# ---------------------------------------------------------------------------
# Python port of Episode 1's `Anneal.ReplayKeyAndTamperAudit.SourceScanner`
# ---------------------------------------------------------------------------


def _is_letter_like(c: str) -> bool:
    cp = ord(c)
    if cp < 0xC0:
        return False
    return (
        (0x3B1 <= cp <= 0x3C9 and cp != 0x3BB)
        or (0x391 <= cp <= 0x3A9 and cp not in (0x3A0, 0x3A3))
        or (0x3CA <= cp <= 0x3FB)
        or (0x1F00 <= cp <= 0x1FFE)
        or (0x2100 <= cp <= 0x214F)
        or (0x1D49C <= cp <= 0x1D59F)
        or (0xC0 <= cp <= 0xFF and cp not in (0xD7, 0xF7))
        or (0x100 <= cp <= 0x17F)
    )


def _is_subscript_alnum(c: str) -> bool:
    cp = ord(c)
    if cp < 0x1D62:
        return False
    return (
        (0x2080 <= cp <= 0x2089)
        or (0x2090 <= cp <= 0x209C)
        or (0x1D62 <= cp <= 0x1D6A)
        or cp == 0x2C7C
    )


def _is_id_first(c: str) -> bool:
    return ("A" <= c <= "Z") or ("a" <= c <= "z") or c == "_" or _is_letter_like(c)


def _is_id_rest(c: str) -> bool:
    return (
        ("A" <= c <= "Z")
        or ("a" <= c <= "z")
        or ("0" <= c <= "9")
        or c in ("_", "'", "!", "?")
        or _is_letter_like(c)
        or _is_subscript_alnum(c)
    )


def _is_token_char(c: str) -> bool:
    return (
        ("A" <= c <= "Z")
        or ("a" <= c <= "z")
        or ("0" <= c <= "9")
        or c in ("_", ".", "'", "!", "?")
    )


def _visible(c: str) -> str:
    return c if _is_token_char(c) else "_"


def _is_radix_digit(radix: str, c: str) -> bool:
    if radix == "bin":
        return c in ("0", "1")
    if radix == "oct":
        return "0" <= c <= "7"
    return ("0" <= c <= "9") or ("a" <= c <= "f") or ("A" <= c <= "F")


FORBIDDEN_OPTION_TOKENS: tuple[str, ...] = (
    "skipKernelTC",
    "allowUnsafeReducibility",
    "privateInPublic",
    "quotPrecheck",
    "hygiene",
)

META_EXEC_TOKENS: tuple[str, ...] = (
    "by_elab",
    "run_tac",
    "run_cmd",
    "run_meta",
    "run_elab",
    "#eval",
    "#reduce",
    "#guard",
    "#guard_panic",
    "#guard_expr",
    "#exit",
    "#with_exporting",
    "#time",
    "#synth",
    "#check_tactic",
    "#check_tactic_failure",
    "#check_simp",
    "#check_failure",
    "#check_assertions",
    "#version",
    "#where",
    "#discr_tree_key",
    "#discr_tree_simp_key",
    "#dump_async_env_state",
    "#grind_lint",
    "#import_path",
    "#info_trees",
    "#show_deprecated_modules",
    "#widget",
    "meta",
)

SYNTAX_EXTENSION_TOKENS: tuple[str, ...] = (
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "syntax",
    "macro",
    "macro_rules",
    "elab",
    "elab_rules",
    "declare_syntax_cat",
    "binder_predicate",
    "declare_simp_like_tactic",
)

EXT_HOOK_TOKENS: tuple[str, ...] = (
    "initialize",
    "builtin_initialize",
    "command_elab",
    "term_elab",
    "tactic_elab",
    "doElem_elab",
    "inductive_elab",
    "delab",
    "app_unexpander",
    "simproc",
    "dsimproc",
    "cbv_simproc",
    "simproc_decl",
    "dsimproc_decl",
    "cbv_simproc_decl",
    "unif_hint",
    "unification_hint",
    "export",
    "csimp",
    "cpass",
    "cbv_eval",
    "cbv_opaque",
    "coinductive",
    "builtin_tactic",
    "grind_tactic",
    "try_tactic",
    "sym_simproc",
    "sym_dsimproc",
    "sym_discharger",
    "run_parser_attribute_hooks",
    "run_builtin_parser_attribute_hooks",
)

LEAN_PRIMITIVE_CONST_TOKENS: tuple[str, ...] = (
    "ofReduceBool",
    "ofReduceNat",
    "trustCompiler",
    "reduceBool",
    "reduceNat",
    "nativeEqTrue",
)

ALWAYS_FORBIDDEN_TOKENS: tuple[str, ...] = (
    "implemented_by",
    "extern",
    "unsafe",
    "partial",
    *META_EXEC_TOKENS,
    *SYNTAX_EXTENSION_TOKENS,
    *EXT_HOOK_TOKENS,
)

NATIVE_TACTIC_TOKENS: tuple[str, ...] = ("native_decide", "bv_decide", "bv_check")


def lex_lean_source(src: str) -> str:
    """Faithful port of `Anneal.ReplayKeyAndTamperAudit.SourceScanner.lexSource`
    with `+1]'` checked strictly outside comments and string/char literals."""
    state: tuple[Any, ...] = ("code", "other")
    out: list[str] = []
    code_tail = ""
    last_raw_char = ""

    def step_code(prev: str, c: str) -> tuple[tuple[Any, ...], str]:
        sep = " " if prev == "escIdent" else ""
        if prev == "ident" and _is_id_rest(c):
            return (("code", "ident"), _visible(c))
        if prev == "symIdent" and (_is_id_rest(c) or c in ('"', "#")):
            if c in ("'", '"', "#") or ("0" <= c <= "9"):
                raise ValueError("literal glued to a symbol keyword")
            return (("code", "symIdent"), _visible(c))
        if prev == "sym" and c == "'":
            raise ValueError("quote glued to a symbol that may absorb it")
        if _is_id_first(c):
            if prev == "sym":
                return (("code", "symIdent"), _visible(c))
            if c == "r" and prev in ("other", "escIdent", "quoteTok"):
                return (("rawR",), sep)
            if c == "r" and prev == "dot":
                return (("dotR",), "")
            return (("code", "ident"), sep + _visible(c))
        if c == ".":
            nxt = "identDot" if prev in ("ident", "escIdent") else "dot"
            return (("code", nxt), ".")
        if "0" <= c <= "9":
            if prev in ("identDot", "dot"):
                return (("fieldIdx",), c)
            if c == "0":
                return (("numZero",), sep + c)
            return (("numDec",), sep + c)
        if c == '"':
            if prev == "ident" and last_raw_char == "!":
                return (("str",), " ")
            return (("plainStr",), " ")
        if c == "'":
            if prev == "quoteTok":
                return (("code", "other"), " ")
            return (("chrOpen",), " ")
        if c == "`":
            if prev == "tick":
                raise ValueError("doubled backtick")
            return (("code", "tick"), " ")
        if c == "«":
            return (("guillemet",), "" if prev in ("identDot", "dot") else " ")
        if c == "»":
            raise ValueError("unmatched identifier escape")
        if c == "-":
            return (("dash",), " ")
        if c == "/":
            return (("slash",), " ")
        if c == "<":
            return (("lt",), " ")
        if c == "\\":
            return (("bslash",), " ")
        if c == "@":
            return (("code", "other"), " @ ")
        if c == "[":
            return (("code", "other"), " [ ")
        if c == "]":
            return (("code", "quoteTok"), " ] ")
        if c in ("×", "Σ", "⊕"):
            return (("code", "quoteTok"), " ")
        if c == "#":
            return (("code", "sym"), " #")
        if c == "~":
            return (("code", "sym"), " ")
        return (("code", "other"), " ")

    def step_block(depth: int, c: str) -> tuple[Any, ...]:
        if c == "-":
            return ("blockDash", depth)
        if c == "/":
            return ("blockSlash", depth)
        return ("block", depth)

    def step_hole(depth: int, prev: str, c: str) -> tuple[tuple[Any, ...], str]:
        if c == "{":
            return (("hole", depth + 1, "other"), " ")
        if c == "}":
            if depth <= 1:
                return (("str",), " ")
            return (("hole", depth - 1, "other"), " ")
        if c in ('"', "\\", "«", "»"):
            raise ValueError("literal or escape inside an interpolation hole")
        if c == "'":
            if prev == "ident":
                return (("hole", depth, "ident"), "'")
            if prev == "quoteTok":
                return (("hole", depth, "other"), " ")
            raise ValueError("character literal inside an interpolation hole")
        if c == "-":
            return (("holeDash", depth), " ")
        if c == "/":
            return (("holeSlash", depth), " ")
        if c == "@":
            return (("hole", depth, "other"), " @ ")
        if c == "[":
            return (("hole", depth, "other"), " [ ")
        if c == "]":
            return (("hole", depth, "quoteTok"), " ] ")
        if c in ("×", "Σ", "⊕"):
            return (("hole", depth, "quoteTok"), " ")
        if c == "#":
            return (("hole", depth, "sym"), " #")
        if c == "~":
            return (("hole", depth, "sym"), " ")
        if "0" <= c <= "9":
            if prev == "symIdent":
                raise ValueError("literal glued to a symbol keyword")
            return (("hole", depth, "ident" if prev == "ident" else "num"), c)
        if _is_id_first(c):
            if prev in ("sym", "symIdent"):
                return (("hole", depth, "symIdent"), _visible(c))
            return (("hole", depth, "num" if prev == "num" else "ident"), _visible(c))
        if _is_id_rest(c):
            return (("hole", depth, "symIdent" if prev == "symIdent" else prev), _visible(c))
        if c == ".":
            return (("hole", depth, "other"), ".")
        return (("hole", depth, "other"), " ")

    non_code_tags = {
        "lineComment",
        "blockStart",
        "block",
        "blockDash",
        "blockSlash",
        "str",
        "strEsc",
        "plainStr",
        "plainStrEsc",
        "raw",
        "rawEnd",
        "chrOpen",
        "chrEsc",
        "chrEscN",
        "chrEnd",
    }

    for ch in src:
        tag = state[0]
        if tag not in non_code_tags:
            code_tail = (code_tail + ch)[-4:]
            if code_tail == "+1]'":
                raise ValueError("quote glued to a successor bracket")
        else:
            code_tail = ""
        if tag == "code":
            state, chunk = step_code(state[1], ch)
        elif tag == "dash":
            if ch == "-":
                state, chunk = (("lineComment",), "")
            else:
                state, chunk = step_code("other", ch)
        elif tag == "slash":
            if ch == "-":
                state, chunk = (("blockStart", 1), "")
            elif ch == "/":
                state, chunk = (("slashAmb",), "")
            elif ch == "\\":
                state, chunk = (("code", "other"), "")
            elif ch == ".":
                raise ValueError("slash glued to a dot")
            else:
                state, chunk = step_code("other", ch)
        elif tag == "slashAmb":
            if ch in ("-", "."):
                raise ValueError("comment opener or dot glued to a slash token")
            if ch == "/":
                state, chunk = (("slashAmb",), "")
            else:
                state, chunk = step_code("other", ch)
        elif tag == "lt":
            if ch == "-":
                state, chunk = (("ltDash",), "")
            else:
                state, chunk = step_code("other", ch)
        elif tag == "ltDash":
            if ch == "-":
                raise ValueError("line comment opener glued to a left arrow")
            state, chunk = step_code("other", ch)
        elif tag == "bslash":
            if ch == "/":
                state, chunk = (("slashAmb",), "")
            elif _is_id_first(ch):
                raise ValueError("identifier glued to a backslash")
            else:
                state, chunk = step_code("other", ch)
        elif tag == "dotR":
            if ch in ('"', "#"):
                raise ValueError("raw string prefix after a dot")
            st2, ch2 = step_code("ident", ch)
            state, chunk = (st2, "r" + ch2)
        elif tag == "lineComment":
            state, chunk = ((("code", "other") if ch == "\n" else ("lineComment",)), "")
        elif tag == "blockStart":
            d = state[1]
            state, chunk = ((("block", d) if ch in ("-", "!") else step_block(d, ch)), "")
        elif tag == "block":
            state, chunk = (step_block(state[1], ch), "")
        elif tag == "blockDash":
            d = state[1]
            if ch == "/":
                state, chunk = ((("code", "other") if d <= 1 else ("block", d - 1)), "")
            else:
                state, chunk = (step_block(d, ch), "")
        elif tag == "blockSlash":
            d = state[1]
            if ch == "-":
                state, chunk = (("block", d + 1), "")
            else:
                state, chunk = (step_block(d, ch), "")
        elif tag == "str":
            if ch == '"':
                state, chunk = (("code", "other"), "")
            elif ch == "\\":
                state, chunk = (("strEsc",), "")
            elif ch == "{":
                state, chunk = (("hole", 1, "other"), " ")
            else:
                state, chunk = (("str",), "")
        elif tag == "strEsc":
            state, chunk = (("str",), "")
        elif tag == "plainStr":
            if ch == '"':
                state, chunk = (("code", "other"), "")
            elif ch == "\\":
                state, chunk = (("plainStrEsc",), "")
            else:
                state, chunk = (("plainStr",), "")
        elif tag == "plainStrEsc":
            state, chunk = (("plainStr",), "")
        elif tag == "hole":
            state, chunk = step_hole(state[1], state[2], ch)
        elif tag in ("holeDash", "holeSlash"):
            if ch == "-":
                raise ValueError("comment inside an interpolation hole")
            state, chunk = step_hole(state[1], "other", ch)
        elif tag == "chrOpen":
            if ch == "\\":
                state, chunk = (("chrEsc",), "")
            elif ch == "'":
                raise ValueError("empty character literal")
            else:
                state, chunk = (("chrEnd",), "")
        elif tag == "chrEsc":
            if ch == "x":
                state, chunk = (("chrEscN", 2), "")
            elif ch == "u":
                state, chunk = (("chrEscN", 4), "")
            else:
                state, chunk = (("chrEnd",), "")
        elif tag == "chrEscN":
            k = state[1]
            state, chunk = ((("chrEnd",) if k <= 1 else ("chrEscN", k - 1)), "")
        elif tag == "chrEnd":
            if ch == "'":
                state, chunk = (("code", "other"), "")
            else:
                raise ValueError("missing end of character literal")
        elif tag == "rawR":
            if ch == '"':
                state, chunk = (("raw", 0), " ")
            elif ch == "#":
                state, chunk = (("rawHash", 1), "")
            else:
                st2, ch2 = step_code("ident", ch)
                state, chunk = (st2, "r" + ch2)
        elif tag == "rawHash":
            n = state[1]
            if ch == "#":
                state, chunk = (("rawHash", n + 1), "")
            elif ch == '"':
                state, chunk = (("raw", n), " ")
            else:
                st2, ch2 = step_code("sym", ch)
                state, chunk = (st2, "r #" + ch2)
        elif tag == "raw":
            n = state[1]
            if ch == '"':
                state, chunk = ((("code", "other") if n == 0 else ("rawEnd", n, 0)), "")
            else:
                state, chunk = (("raw", n), "")
        elif tag == "rawEnd":
            n, seen = state[1], state[2]
            if ch == "#":
                state, chunk = ((("code", "other") if seen + 1 == n else ("rawEnd", n, seen + 1)), "")
            elif ch == '"':
                state, chunk = (("rawEnd", n, 0), "")
            else:
                state, chunk = (("raw", n), "")
        elif tag == "guillemet":
            if ch == "»":
                state, chunk = (("code", "escIdent"), "")
            else:
                state, chunk = (("guillemet",), _visible(ch))
        elif tag == "numZero":
            if ch in ("b", "B"):
                state, chunk = (("numRadix", "bin"), ch)
            elif ch in ("o", "O"):
                state, chunk = (("numRadix", "oct"), ch)
            elif ch in ("x", "X"):
                state, chunk = (("numRadix", "hex"), ch)
            elif ("0" <= ch <= "9") or ch == "_":
                state, chunk = (("numDec",), ch)
            elif ch == ".":
                state, chunk = (("numDot",), "")
            elif ch in ("e", "E"):
                state, chunk = (("numExpStart",), ch)
            else:
                st2, ch2 = step_code("other", ch)
                state, chunk = (st2, " " + ch2)
        elif tag == "numRadix":
            r = state[1]
            if ch == "_" or _is_radix_digit(r, ch):
                state, chunk = (("numRadix", r), ch)
            else:
                st2, ch2 = step_code("other", ch)
                state, chunk = (st2, " " + ch2)
        elif tag == "numDec":
            if ("0" <= ch <= "9") or ch == "_":
                state, chunk = (("numDec",), ch)
            elif ch == ".":
                state, chunk = (("numDot",), "")
            elif ch in ("e", "E"):
                state, chunk = (("numExpStart",), ch)
            else:
                st2, ch2 = step_code("other", ch)
                state, chunk = (st2, " " + ch2)
        elif tag == "numDot":
            if "0" <= ch <= "9":
                state, chunk = (("numFrac",), "." + ch)
            elif ch == ".":
                state, chunk = (("code", "other"), " ")
            elif ch in ("e", "E"):
                state, chunk = (("numExpStart",), "." + ch)
            elif _is_id_first(ch) or ch == "«":
                raise ValueError("identifier after a decimal point")
            else:
                st2, ch2 = step_code("other", ch)
                state, chunk = (st2, " " + ch2)
        elif tag == "numFrac":
            if ("0" <= ch <= "9") or ch == "_":
                state, chunk = (("numFrac",), ch)
            elif ch in ("e", "E"):
                state, chunk = (("numExpStart",), ch)
            else:
                st2, ch2 = step_code("other", ch)
                state, chunk = (st2, " " + ch2)
        elif tag == "numExpStart":
            if ch in ("+", "-"):
                state, chunk = (("numExpSign",), "")
            elif "0" <= ch <= "9":
                state, chunk = (("numExp",), ch)
            else:
                raise ValueError("missing exponent digits in a scientific literal")
        elif tag == "numExpSign":
            if "0" <= ch <= "9":
                state, chunk = (("numExp",), ch)
            else:
                raise ValueError("missing exponent digits in a scientific literal")
        elif tag == "numExp":
            if ("0" <= ch <= "9") or ch == "_":
                state, chunk = (("numExp",), ch)
            else:
                st2, ch2 = step_code("other", ch)
                state, chunk = (st2, " " + ch2)
        elif tag == "fieldIdx":
            if "0" <= ch <= "9":
                state, chunk = (("fieldIdx",), ch)
            else:
                st2, ch2 = step_code("other", ch)
                state, chunk = (st2, " " + ch2)
        else:
            raise ValueError(f"unknown lexer state {tag}")
        last_raw_char = ch
        if chunk:
            out.append(chunk)

    terminal_ok = {
        "code",
        "dash",
        "slash",
        "slashAmb",
        "lt",
        "ltDash",
        "bslash",
        "dotR",
        "lineComment",
        "rawR",
        "rawHash",
        "numZero",
        "numRadix",
        "numDec",
        "numDot",
        "numFrac",
        "numExp",
        "fieldIdx",
    }
    if state[0] not in terminal_ok:
        raise ValueError("input ends inside a literal, comment, or escape")
    if state[0] in ("rawR", "dotR", "rawHash"):
        out.append("r")
    return "".join(out)


def _strip_tactic_suffix(seg: str) -> str:
    if seg.endswith(("?", "!")):
        return seg[:-1]
    return seg


def _segment_is_keyword(kw: str, seg: str) -> bool:
    s0 = _strip_tactic_suffix(seg)
    s = s0 if kw.startswith("#") else (s0[1:] if s0.startswith("#") else s0)
    if s == kw:
        return True
    return bool(s) and ("0" <= s[0] <= "9") and s.endswith(kw)


def _token_has_keyword(kw: str, tok: str) -> bool:
    return any(_segment_is_keyword(kw, seg) for seg in tok.split("."))


def _is_standalone_keyword(kw: str, tok: str) -> bool:
    return ("." not in tok) and _segment_is_keyword(kw, tok)


def _is_allowed_option_name(opt: str) -> bool:
    return (
        opt in ("maxHeartbeats", "maxRecDepth")
        or opt.startswith("pp.")
        or opt.startswith("linter.")
    )


def classify_module_role_py(mod_name: str) -> str | None:
    parts = [p for p in mod_name.split(".")]
    if not mod_name or any(not p for p in parts):
        return None
    root = parts[0]
    if root == "Lean":
        return None
    if root in ("Init", "Std"):
        return "foundation"
    if root == "Trusted":
        return "trusted"
    if root == "Anneal":
        return "theory"
    if root == "Assumptions":
        return "assumptions" if len(parts) >= 2 else None
    if root == "Verify":
        return "verify" if len(parts) >= 2 else None
    if root == "CrateVerify":
        return "verify"
    has_proof = ("Proof" in parts) or ("Proofs" in parts)
    has_test = ("Test" in parts) or ("Tests" in parts)
    if has_proof and has_test:
        return None
    if has_proof:
        return "proof"
    if has_test:
        return "test"
    if parts[-1] == "Defs":
        return "defsExempt"
    return "spec"


def scan_source_defense_in_depth(
    mod_name: str,
    src_text: str,
    *,
    allow_provisional_native: bool = False,
    allow_assumptions: bool = False,
    allow_module_header: bool = False,
) -> None:
    """Runs Episode 1's hardened `SourceScanner` rules on `src_text`.

    Raises `AuditPolicyError` (`unsupportedSourceLexing` / `forbiddenSourceOption` /
    `forbiddenImportAll` / `forbiddenImportModifier` / `forbiddenAxiom`) on violation.
    """
    role = classify_module_role_py(mod_name) or "spec"
    try:
        code = lex_lean_source(src_text)
    except ValueError as exc:
        raise AuditPolicyError("unsupportedSourceLexing", mod_name, str(exc)) from exc

    toks = [t for t in code.split(" ") if t]

    for idx, tok in enumerate(toks):
        if _token_has_keyword("set_option", tok):
            if idx + 1 >= len(toks):
                raise AuditPolicyError("forbiddenSourceOption", mod_name, "set_option")
            opt = toks[idx + 1]
            if not _is_allowed_option_name(opt):
                raise AuditPolicyError("forbiddenSourceOption", mod_name, opt)

    for kw in FORBIDDEN_OPTION_TOKENS:
        if any(_token_has_keyword(kw, t) for t in toks):
            raise AuditPolicyError("forbiddenSourceOption", mod_name, kw)

    for kw in ALWAYS_FORBIDDEN_TOKENS:
        if any(_token_has_keyword(kw, t) for t in toks):
            raise AuditPolicyError("forbiddenSourceOption", mod_name, kw)

    decl_intro_kws = {"def", "theorem", "abbrev", "opaque", "axiom", "inductive", "structure"}
    for idx, t in enumerate(toks):
        segs = t.split(".")
        leaf = segs[-1]
        prev_tok = toks[idx - 1] if idx > 0 else ""
        for pkw in LEAN_PRIMITIVE_CONST_TOKENS:
            if _segment_is_keyword(pkw, leaf):
                is_lean_qual = len(segs) >= 2 and segs[-2] in ("Lean", "Meta")
                is_unqual_ref = len(segs) == 1 and prev_tok not in decl_intro_kws
                if is_lean_qual or is_unqual_ref:
                    raise AuditPolicyError("forbiddenSourceOption", mod_name, pkw)

    # `builtin_<kw>` & `*_parser`
    for t in toks:
        for seg in t.split("."):
            s = _strip_tactic_suffix(seg).lstrip("#").lstrip("0123456789")
            if s.startswith("builtin_"):
                rest = s[len("builtin_") :]
                if rest in ALWAYS_FORBIDDEN_TOKENS:
                    raise AuditPolicyError("forbiddenSourceOption", mod_name, s)
            if _strip_tactic_suffix(seg).endswith("_parser"):
                raise AuditPolicyError("forbiddenSourceOption", mod_name, seg)

    # `@[... init ...]` or `attribute [... init ...]`
    depth = 0
    i = 0
    while i < len(toks):
        if depth == 0:
            if i + 1 < len(toks) and (
                toks[i] == "@" or _token_has_keyword("attribute", toks[i])
            ) and toks[i + 1] == "[":
                depth = 1
                i += 2
                continue
            i += 1
        else:
            if toks[i] == "[":
                depth += 1
            elif toks[i] == "]":
                depth -= 1
            elif _token_has_keyword("init", toks[i]):
                raise AuditPolicyError("forbiddenSourceOption", mod_name, "init")
            i += 1

    # Header & import modifiers (`module`, `prelude`, `import all`, `private import`, `public import`)
    if toks:
        idx0 = 0
        if _is_standalone_keyword("module", toks[0]):
            if not allow_module_header:
                raise AuditPolicyError("forbiddenSourceOption", mod_name, "module")
            idx0 = 1
        if idx0 < len(toks) and _is_standalone_keyword("prelude", toks[idx0]):
            raise AuditPolicyError("forbiddenSourceOption", mod_name, "prelude")
        for j in range(len(toks) - 1):
            if _is_standalone_keyword("import", toks[j]) and _is_standalone_keyword("all", toks[j + 1]):
                target_mod = toks[j + 2] if j + 2 < len(toks) else "<unknown>"
                raise AuditPolicyError(
                    "forbiddenImportAll", mod_name, "import all", [mod_name, target_mod]
                )
            if _is_standalone_keyword("private", toks[j]) and _is_standalone_keyword("import", toks[j + 1]):
                target_mod = toks[j + 2] if j + 2 < len(toks) else "<unknown>"
                raise AuditPolicyError(
                    "forbiddenImportModifier", mod_name, "private", [mod_name, target_mod]
                )
            if _is_standalone_keyword("public", toks[j]) and _is_standalone_keyword("import", toks[j + 1]):
                if not allow_module_header:
                    raise AuditPolicyError("forbiddenSourceOption", mod_name, "import")

    # Axiom keyword outside `Assumptions.*` (unless test with local test axioms)
    if not (allow_assumptions and role == "assumptions") and role != "assumptions":
        if any(_is_standalone_keyword("axiom", t) for t in toks):
            raise AuditPolicyError("forbiddenAxiom", mod_name, "unapproved axiom keyword in source")

    if not (allow_provisional_native and role == "proof"):
        for kw in NATIVE_TACTIC_TOKENS:
            if any(_token_has_keyword(kw, t) for t in toks):
                raise AuditPolicyError("forbiddenSourceOption", mod_name, kw)
        if any(_token_has_keyword("decide", t) for t in toks) and any(
            _token_has_keyword("native", t)
            or _token_has_keyword("config", t)
            or _token_has_keyword("DecideConfig", t)
            for t in toks
        ):
            raise AuditPolicyError("forbiddenSourceOption", mod_name, "decide with a configuration")


# ---------------------------------------------------------------------------
# Embedded Read-Only Lean 4.34.1 `.olean` Inspector (`OleanReplayInspector.lean`)
# ---------------------------------------------------------------------------
# IMPORTANT SECURITY INVARIANT:
# `OleanReplayInspector.lean` NEVER calls `enableInitializersExecution` and NEVER
# passes `loadExts := true` to `importModules`! All extension tables are read
# statically via `getModuleEntries` / `getModuleIREntries` / `ModuleData.entries`.

INSPECTOR_LEAN_SOURCE = r"""import Lean
import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Elab.Util
import Lean.PrettyPrinter.Delaborator.Basic
import Lean.Meta.Instances
import Lean.Meta.CoeAttr
import Lean.ReducibilityAttrs
import Lean.ResolveName
import Lean.Compiler.InitAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.ExportAttr
import Lean.Replay

open Lean

namespace OleanReplayInspector

structure Violation where
  category : String
  modName  : String
  names    : Array String
  detail   : String

def policyFail (category : String) (modName : Name) (names : Array Name) (detail : String := "") : IO α := do
  let j := Json.mkObj [
    ("category", toJson category),
    ("module", toJson modName.toString),
    ("names", toJson (names.map Name.toString)),
    ("detail", toJson detail)
  ]
  throw <| IO.userError ("POLICY_JSON:" ++ j.compress)

def opFail (detail : String) : IO α :=
  throw <| IO.userError ("OPERATIONAL:" ++ detail)

def field [FromJson α] (j : Json) (key : String) : IO α :=
  match j.getObjValAs? α key with
  | .ok v => pure v
  | .error e => opFail s!"malformed request field '{key}': {e}"

def isWellFormedName : Name → Bool
  | .anonymous => false
  | .str p s =>
    !s.isEmpty && !(s.contains '.') &&
      (if p.isAnonymous then true else isWellFormedName p)
  | .num p _ =>
    !p.isAnonymous && isWellFormedName p

def nameComponents : Name → List String
  | .anonymous => []
  | .str p s => nameComponents p ++ [s]
  | .num p n => nameComponents p ++ [toString n]

def hasRootComp (n : Name) (r : String) : Bool :=
  match nameComponents n with
  | h :: _ => h == r
  | [] => false

def isStdlibMod (m : Name) : Bool :=
  isWellFormedName m && (hasRootComp m "Init" || hasRootComp m "Std")

def isLeanCompilerMod (m : Name) : Bool :=
  hasRootComp m "Lean"

def isTrustedMod (m : Name) : Bool :=
  isWellFormedName m && hasRootComp m "Trusted"

def isInternalPart (s : String) : Bool :=
  s.startsWith "_" || (!s.isEmpty && s.all Char.isDigit)

def hasInternalPart (n : Name) : Bool :=
  (nameComponents n).any isInternalPart

def properSuffixes (n : Name) : List Name :=
  let rec go : List String → List (List String)
    | [] => []
    | _ :: rest => (if rest.isEmpty then [] else [rest]) ++ go rest
  (go (nameComponents n)).map fun ps => ps.foldl Name.str .anonymous

def classifyModuleRole (m : Name) : IO String := do
  if !isWellFormedName m then
    policyFail "moduleRoleMismatch" m #[m] "malformed module name"
  let parts := nameComponents m
  let root := parts.headD ""
  if root == "Lean" then
    policyFail "stdlibNamedPackageModule" m #[m] "Lean compiler namespace is disallowed"
  if root == "Init" || root == "Std" then
    return "foundation"
  if root == "Trusted" then
    return "trusted"
  if root == "Anneal" then
    return "theory"
  if root == "Assumptions" then
    if parts.length < 2 then
      policyFail "moduleRoleMismatch" m #[m] "bare Assumptions module name disallowed"
    return "assumptions"
  if root == "Verify" then
    if parts.length < 2 then
      policyFail "moduleRoleMismatch" m #[m] "bare Verify module name disallowed"
    return "verify"
  if root == "CrateVerify" then
    return "verify"
  let hasProof := parts.contains "Proof" || parts.contains "Proofs"
  let hasTest := parts.contains "Test" || parts.contains "Tests"
  if hasProof && hasTest then
    policyFail "moduleRoleMismatch" m #[m] "ambiguous hybrid Proof/Test module name"
  if hasProof && parts.getLast? == some "Defs" then
    policyFail "spoofedExemptModule" m #[m] "Proof module cannot spoof Defs exemption"
  if hasProof then return "proof"
  if hasTest then return "test"
  if parts.getLast? == some "Defs" then return "defsExempt"
  return "spec"

def isStatementSideRole (r : String) : Bool :=
  r == "foundation" || r == "trusted" || r == "spec" || r == "defsExempt" || r == "assumptions"

def importRoleAllowed (importer imported : String) : Bool :=
  if imported == "foundation" || imported == "trusted" then true
  else if importer == "test" then true
  else if imported == "test" then false
  else if importer == "verify" then true
  else if imported == "verify" then false
  else if importer == "proof" then true
  else if imported == "proof" then false
  else if importer == "theory" then true
  else if imported == "theory" then false
  else true

def kindTag (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "definition"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

def sameStoredDecl (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.type == b.type && a.levelParams == b.levelParams &&
  a.isUnsafe == b.isUnsafe && a.isPartial == b.isPartial &&
  match a, b with
  | .axiomInfo x, .axiomInfo y => x.isUnsafe == y.isUnsafe
  | .defnInfo x, .defnInfo y =>
    x.value == y.value && x.hints == y.hints && x.safety == y.safety && x.all == y.all
  | .thmInfo x, .thmInfo y => x.value == y.value && x.all == y.all
  | .opaqueInfo x, .opaqueInfo y => x.value == y.value && x.isUnsafe == y.isUnsafe && x.all == y.all
  | .quotInfo x, .quotInfo y =>
    match x.kind, y.kind with
    | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
    | _, _ => false
  | .inductInfo x, .inductInfo y =>
    x.numParams == y.numParams && x.numIndices == y.numIndices && x.all == y.all &&
    x.ctors == y.ctors && x.numNested == y.numNested && x.isRec == y.isRec &&
    x.isUnsafe == y.isUnsafe && x.isReflexive == y.isReflexive
  | .ctorInfo x, .ctorInfo y =>
    x.induct == y.induct && x.cidx == y.cidx && x.numParams == y.numParams &&
    x.numFields == y.numFields && x.isUnsafe == y.isUnsafe
  | .recInfo x, .recInfo y =>
    x.all == y.all && x.numParams == y.numParams && x.numIndices == y.numIndices &&
    x.numMotives == y.numMotives && x.numMinors == y.numMinors &&
    x.k == y.k && x.isUnsafe == y.isUnsafe &&
    x.rules.length == y.rules.length &&
    (x.rules.zip y.rules).all fun (r1, r2) =>
      r1.ctor == r2.ctor && r1.nfields == r2.nfields && r1.rhs == r2.rhs
  | _, _ => false

def verifyPartKeysOnly (modName : Name) (data : ModuleData) : IO Unit := do
  unless data.constNames.size == data.constants.size do
    policyFail "constNamesSizeMismatch" modName #[modName]
      s!"{data.constNames.size} constNames vs {data.constants.size} constants"
  let mut seen : NameSet := {}
  for i in [:data.constNames.size] do
    let k := data.constNames[i]!
    let ci := data.constants[i]!
    unless isWellFormedName k && isWellFormedName ci.name do
      policyFail "anonymousConstantName" modName #[modName] "anonymous or dot-smuggled constant name"
    unless k == ci.name do
      policyFail "keyNameMismatch" modName #[modName, k, ci.name]
        s!"map key {k} != ConstantInfo.name {ci.name}"
    if seen.contains k then
      policyFail "duplicateConstName" modName #[modName, k] s!"duplicate constant name {k}"
    seen := seen.insert k

def verifyMutualAllAndLinks (modName : Name) (byName : Std.HashMap Name ConstantInfo)
    (env? : Option Environment) (ci : ConstantInfo) : IO Unit := do
  let checkAllHygiene (all : List Name) : IO Unit := do
    if all.isEmpty then
      policyFail "invalidMutualAll" modName #[modName, ci.name] "empty .all"
    let mut seen : NameSet := {}
    for a in all do
      unless isWellFormedName a do
        policyFail "invalidMutualAll" modName #[modName, ci.name] "anonymous or malformed entry in .all"
      if seen.contains a then
        policyFail "invalidMutualAll" modName #[modName, ci.name] s!"duplicate entry {a} in .all"
      seen := seen.insert a

  let checkMutualGroup (all : List Name) : IO Unit := do
    checkAllHygiene all
    unless all.contains ci.name do
      policyFail "invalidMutualAll" modName #[modName, ci.name] "ci.name missing from .all"
    for peer in all do
      let some peerCi := byName[peer]?
        | policyFail "invalidMutualAll" modName #[modName, ci.name] s!"missing mutual peer {peer}"
      unless kindTag peerCi == kindTag ci do
        policyFail "invalidMutualAll" modName #[modName, ci.name] s!"incompatible mutual peer kind for {peer}"
      let peerAll := match peerCi with
        | .defnInfo v => v.all | .thmInfo v => v.all
        | .opaqueInfo v => v.all | .inductInfo v => v.all
        | _ => []
      unless peerAll == all do
        policyFail "invalidMutualAll" modName #[modName, ci.name] s!"asymmetric mutual .all with {peer}"

  match ci with
  | .defnInfo v => checkMutualGroup v.all
  | .thmInfo v => checkMutualGroup v.all
  | .opaqueInfo v => checkMutualGroup v.all
  | .inductInfo v =>
    checkMutualGroup v.all
    let mut seenCtors : NameSet := {}
    for c in v.ctors do
      if seenCtors.contains c then
        policyFail "invalidMutualAll" modName #[modName, ci.name] s!"duplicate constructor {c}"
      seenCtors := seenCtors.insert c
      let some cc := byName[c]?
        | policyFail "invalidMutualAll" modName #[modName, ci.name] s!"missing constructor {c}"
      match cc with
      | .ctorInfo cv =>
        unless cv.induct == ci.name do
          policyFail "invalidMutualAll" modName #[modName, ci.name] s!"constructor {c} parent mismatch"
      | _ =>
        policyFail "invalidMutualAll" modName #[modName, ci.name] s!"{c} is not a constructor"
  | .ctorInfo v =>
    let some ic := byName[v.induct]?
      | policyFail "invalidMutualAll" modName #[modName, ci.name] s!"missing parent inductive {v.induct}"
    match ic with
    | .inductInfo iv =>
      unless iv.ctors.contains ci.name do
        policyFail "invalidMutualAll" modName #[modName, ci.name] s!"constructor {ci.name} not listed by {v.induct}"
    | _ =>
      policyFail "invalidMutualAll" modName #[modName, ci.name] s!"parent {v.induct} is not an inductive"
  | .recInfo v =>
    checkAllHygiene v.all
    let mut hasNested := false
    for indName in v.all do
      let some ic := byName[indName]?
        | policyFail "invalidMutualAll" modName #[modName, ci.name] s!"missing recursor target {indName}"
      match ic with
      | .inductInfo iv =>
        if iv.numNested > 0 then hasNested := true
        unless iv.all == v.all do
          policyFail "invalidMutualAll" modName #[modName, ci.name] "recursor .all differs from inductive .all"
      | _ =>
        policyFail "invalidMutualAll" modName #[modName, ci.name] s!"recursor target {indName} is not an inductive"
    let mut seenRuleCtors : NameSet := {}
    for r in v.rules do
      if seenRuleCtors.contains r.ctor then
        policyFail "invalidMutualAll" modName #[modName, ci.name] s!"duplicate recursor rule for {r.ctor}"
      seenRuleCtors := seenRuleCtors.insert r.ctor
      match byName[r.ctor]? with
      | some (.ctorInfo cv) =>
        unless v.all.contains cv.induct do
          policyFail "invalidMutualAll" modName #[modName, ci.name] s!"recursor rule ctor {r.ctor} outside .all"
      | some _ =>
        policyFail "invalidMutualAll" modName #[modName, ci.name] s!"recursor rule target {r.ctor} not ctor"
      | none =>
        if hasNested then
          if let some env := env? then
            match env.checked.get.find? r.ctor with
            | some (.ctorInfo _) => pure ()
            | _ => policyFail "invalidMutualAll" modName #[modName, ci.name] s!"nested recursor rule target {r.ctor} missing"
        else
          policyFail "invalidMutualAll" modName #[modName, ci.name] s!"recursor rule names missing ctor {r.ctor}"
    let isPrimaryRec := v.all.any (fun indName => ci.name == indName.str "rec")
    if !hasNested || isPrimaryRec then
      for indName in v.all do
        if let some (.inductInfo iv) := byName[indName]? then
          for c in iv.ctors do
            unless seenRuleCtors.contains c do
              policyFail "invalidMutualAll" modName #[modName, ci.name] s!"recursor missing rule for {c}"
  | .quotInfo _ =>
    unless isStdlibMod modName do
      policyFail "foreignQuotDecl" modName #[modName, ci.name] "quotInfo outside standard library"
  | .axiomInfo _ => pure ()

def verifyModuleInventory (modName : Name) (data : ModuleData)
    (env? : Option Environment := none) : IO (Std.HashMap Name ConstantInfo) := do
  verifyPartKeysOnly modName data
  let mut byName : Std.HashMap Name ConstantInfo := {}
  for ci in data.constants do
    byName := byName.insert ci.name ci
  for ci in data.constants do
    if let .quotInfo _ := ci then
      unless isStdlibMod modName do
        policyFail "foreignQuotDecl" modName #[modName, ci.name] "quotInfo outside standard library"
    verifyMutualAllAndLinks modName byName env? ci
  let mut seenExtra : NameSet := {}
  for e in data.extraConstNames do
    unless isWellFormedName e do
      policyFail "anonymousConstantName" modName #[modName] "malformed extraConstNames entry"
    if seenExtra.contains e then
      policyFail "duplicateConstName" modName #[modName, e] s!"duplicate extraConstName {e}"
    seenExtra := seenExtra.insert e
  return byName

def expressionEdges (modName declName : Name) (e : Expr) : IO NameSet := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    policyFail "kernelTypeError" modName #[declName] "open expression in stored declaration"
  let mut res := e.getUsedConstantsAsSet
  if (e.find? fun | .lit (.natVal _) => true | _ => false).isSome then
    res := res.insert `Nat
  if (e.find? fun | .lit (.strVal _) => true | _ => false).isSome then
    res := res.insert `String
  -- Also include `.proj structName _ _` structure constants explicitly
  let rec collectProj (x : Expr) (acc : NameSet) : NameSet :=
    match x with
    | .proj s _ inner => collectProj inner (acc.insert s)
    | .app f a => collectProj a (collectProj f acc)
    | .lam _ t b _ => collectProj b (collectProj t acc)
    | .forallE _ t b _ => collectProj b (collectProj t acc)
    | .letE _ t v b _ => collectProj b (collectProj v (collectProj t acc))
    | .mdata _ inner => collectProj inner acc
    | _ => acc
  res := collectProj e res
  return res

def declarationEdges (modName : Name) (ci : ConstantInfo) : IO NameSet := do
  let mut res ← expressionEdges modName ci.name ci.type
  if let some val := ci.value? (allowOpaque := true) then
    res := res ++ (← expressionEdges modName ci.name val)
  match ci with
  | .defnInfo v   => res := res ++ .ofList v.all
  | .thmInfo v    => res := res ++ .ofList v.all
  | .opaqueInfo v => res := res ++ .ofList v.all
  | .inductInfo v => res := res ++ .ofList (v.all ++ v.ctors)
  | .ctorInfo v   => res := res.insert v.induct
  | .recInfo v    =>
    res := res ++ .ofList v.all
    for rule in v.rules do
      res := (res.insert rule.ctor) ++ (← expressionEdges modName ci.name rule.rhs)
  | _ => pure ()
  return res

def isCompilerTrustConst (n : Name) : Bool :=
  n == `Lean.trustCompiler

def hasNativeMarker (n : Name) : Bool :=
  (nameComponents n).contains "_native"

def isProvisionalNativeName (n : Name) : Bool :=
  let ps := nameComponents n
  ps.contains "_native" && ps.length >= 3 &&
    ps.head? != some "_native" && ps.getLast? != some "_native"

def isNativeReductionConst (n : Name) : Bool :=
  n == `Lean.ofReduceBool || n == `Lean.ofReduceNat ||
  n == `Lean.reduceBool || n == `Lean.reduceNat ||
  hasNativeMarker n

def isFoundationalAxiom (n : Name) : Bool :=
  n == `propext || n == `Classical.choice || n == `Quot.sound

/-- Unfold `.defnInfo` and `.opaqueInfo` + beta-reduce to check if a provisional native
    axiom's LHS evaluates to `Bool.false` (runtime-faithful refutation). -/
partial def whnfAllowOpaque (env : Environment) (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match e with
    | .mdata _ inner => whnfAllowOpaque env fuel' inner
    | .letE _ _ v b _ => whnfAllowOpaque env fuel' (b.instantiate1 v)
    | .const c _ =>
      match env.checked.get.find? c with
      | some (.defnInfo dv) => whnfAllowOpaque env fuel' dv.value
      | some (.opaqueInfo ov) => whnfAllowOpaque env fuel' ov.value
      | _ => some e
    | .app f a =>
      match whnfAllowOpaque env fuel' f with
      | none => none
      | some (.lam _ _ b _) => whnfAllowOpaque env fuel' (b.instantiate1 a)
      | some f' => some (.app f' a)
    | _ => some e

def checkValidProvisionalNativeAxiom (env : Environment) (user axName : Name) (ci : ConstantInfo) : IO Unit := do
  -- Must be `@Eq Bool e Bool.true` (`Eq` applied to `[Bool, e, Bool.true]`) with closed `e`.
  let fn := ci.type.getAppFn
  let args := ci.type.getAppArgs
  unless fn.isConstOf ``Eq && args.size == 3 &&
         args[0]!.isConstOf ``Bool && args[2]!.isConstOf ``Bool.true do
    policyFail "invalidNativeAxiomType" axName #[user, axName]
      "provisional native axiom must have type `@Eq Bool e Bool.true`"
  let lhs := args[1]!
  if lhs.hasFVar || lhs.hasMVar || lhs.hasLooseBVars then
    policyFail "invalidNativeAxiomType" axName #[user, axName] "open LHS in native axiom"
  match whnfAllowOpaque env 2048 lhs with
  | none =>
    policyFail "invalidNativeAxiomType" axName #[user, axName] "native axiom LHS reduction exhausted budget"
  | some (.const c _) =>
    if c == ``Bool.false then
      policyFail "invalidNativeAxiomType" axName #[user, axName] "native axiom LHS reduces to Bool.false"
  | some _ => pure ()

def isCodegenUnsafeRec (byName : Std.HashMap Name ConstantInfo) (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ =>
    if ci.isUnsafe || !ci.isPartial then false
    else match ci.name with
      | .str parent "_unsafe_rec" =>
        match byName[parent]? with
        | some (.defnInfo pv) => pv.safety == .safe && pv.type == ci.type
        | _ => false
      | _ => false
  | _ => false

/-- Normalize an expression by unfolding `.defnInfo` and beta-reducing, then strip leading `forallE`/`lam`. -/
partial def normExprInEnv (env : Environment) (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match e with
    | .mdata _ inner => normExprInEnv env fuel' inner
    | .letE _ _ v b _ => normExprInEnv env fuel' (b.instantiate1 v)
    | .const c _ =>
      match env.checked.get.find? c with
      | some (.defnInfo dv) => normExprInEnv env fuel' dv.value
      | _ => some e
    | .app f a =>
      match normExprInEnv env fuel' f, normExprInEnv env fuel' a with
      | some (.lam _ _ b _), some a' => normExprInEnv env fuel' (b.instantiate1 a')
      | some f', some a' => some (.app f' a')
      | _, _ => none
    | .forallE n d b bi =>
      match normExprInEnv env fuel' d, normExprInEnv env fuel' b with
      | some d', some b' => some (.forallE n d' b' bi)
      | _, _ => none
    | .lam n d b bi =>
      match normExprInEnv env fuel' d, normExprInEnv env fuel' b with
      | some d', some b' => some (.lam n d' b' bi)
      | _, _ => none
    | .proj s i x => (normExprInEnv env fuel' x).map (.proj s i)
    | _ => some e

partial def stripForallAndLam : Expr → Expr
  | .forallE _ _ b _ => stripForallAndLam b
  | .lam _ _ b _ => stripForallAndLam b
  | .mdata _ e => stripForallAndLam e
  | e => e

def isOutParamDomain (d : Expr) : Bool :=
  let hd := (stripForallAndLam d).getAppFn
  hd.isConstOf ``outParam || hd.isConstOf ``semiOutParam

def nonOutParamArgs (env : Environment) (cls : Name) (args : Array Expr) : Array Expr := Id.run do
  let some ci := env.checked.get.find? cls | return args
  let mut curTy := ci.type
  let mut kept : Array Expr := #[]
  for i in [:args.size] do
    match curTy with
    | .forallE _ dom body _ =>
      if !isOutParamDomain dom then
        kept := kept.push args[i]!
      curTy := body.instantiate1 args[i]!
    | _ =>
      kept := kept.push args[i]!
  return kept

def isBaseInstanceAnchor (localReplayable : NameSet) (localReducibilityOverridden : NameSet)
    (byName : Std.HashMap Name ConstantInfo) (d : Name) : Bool :=
  localReplayable.contains d && !localReducibilityOverridden.contains d &&
  match byName[d]? with
  | some (.inductInfo _) | some (.ctorInfo _) | some (.opaqueInfo _) | some (.axiomInfo _) => true
  | _ => false

def isRigidHeadInEnv (env : Environment) (c : Name) : Bool :=
  match env.checked.get.find? c with
  | some (.inductInfo _) | some (.ctorInfo _) | some (.opaqueInfo _) | some (.axiomInfo _) => true
  | _ => false

partial def hasRigidBaseAnchor (env : Environment) (localReplayable localRedOver : NameSet)
    (byName : Std.HashMap Name ConstantInfo) (e : Expr) : Bool :=
  match e with
  | .mdata _ inner => hasRigidBaseAnchor env localReplayable localRedOver byName inner
  | .const c _ => isBaseInstanceAnchor localReplayable localRedOver byName c
  | .forallE _ d b _ =>
    hasRigidBaseAnchor env localReplayable localRedOver byName d ||
    hasRigidBaseAnchor env localReplayable localRedOver byName b
  | .lam _ _ b _ =>
    hasRigidBaseAnchor env localReplayable localRedOver byName b
  | .app f a =>
    match e.getAppFn with
    | .const hd _ =>
      isBaseInstanceAnchor localReplayable localRedOver byName hd ||
      (isRigidHeadInEnv env hd &&
        ((match f with | .const _ _ => false | _ => hasRigidBaseAnchor env localReplayable localRedOver byName f) ||
         hasRigidBaseAnchor env localReplayable localRedOver byName a))
    | _ => false
  | _ => false

def isAutoSizeOfInst (byName : Std.HashMap Name ConstantInfo) (instDecl cls : Name) : Bool :=
  if cls != ``SizeOf then false
  else match instDecl with
    | .str indName "_sizeOf_inst" =>
      match byName[indName]? with
      | some (.inductInfo _) => true
      | _ => false
    | _ => false

def verifyCertificateHead (headConst : Expr) : Bool :=
  headConst.isConstOf `Trusted.VerificationResult.VerificationResult ||
  headConst.isConstOf `Trusted.VerificationResult.StatefulVerificationResult ||
  headConst.isConstOf `Trusted.VerificationResult.ModularVerificationResult ||
  headConst.isConstOf `Trusted.VerificationResult.TraceVerificationResult ||
  headConst.isConstOf `Trusted.VerificationResult.TotalVerificationResult ||
  headConst.isConstOf `Trusted.VerificationResult.StatefulEquivVerificationResult ||
  headConst.isConstOf `Trusted.VerificationResult.UbExceptionVerificationResult ||
  headConst.isConstOf `Trusted.VerificationResult.CrateVerificationResult

def computeInitMultiNames (initEnv : Environment) : NameSet × NameSet := Id.run do
  let mut mods : NameSet := {}
  let mut s : NameSet := {}
  for h : idx in [:initEnv.header.modules.size] do
    let m := initEnv.header.modules[idx].module
    mods := mods.insert m
    let d := initEnv.header.moduleData[idx]!
    for ci in d.constants do
      let ge2 := match ci.name with
        | .str p _ | .num p _ => !p.isAnonymous
        | .anonymous => false
      if !isPrivateName ci.name && ge2 then
        s := s.insert ci.name
  return (mods, s)

def insertReplayLocalUnique (env : Environment) (m : Name)
    (acc : Std.HashMap Name ConstantInfo) (ci : ConstantInfo) :
    IO (Std.HashMap Name ConstantInfo) := do
  if let some existing := acc[ci.name]? then
    unless Lean.isReservedName env ci.name && sameStoredDecl existing ci do
      policyFail "duplicateConstName" m #[m, ci.name]
        s!"replayLocals collision on {ci.name}"
    return acc
  return acc.insert ci.name ci

def auditOleans (j : Json) (cachedInitEnv? : Option Environment := none)
    (cachedInitMods : NameSet := {}) (cachedInitMulti? : Option NameSet := none) : IO Json := do
  let sysrootStr ← field (α := String) j "sysroot"
  let sysroot := System.FilePath.mk sysrootStr
  let stdRoot ← IO.FS.realPath (sysroot / "lib" / "lean")
  let trustedRootStr ← field (α := String) j "trustedOleanRoot"
  let trustedRoot? : Option System.FilePath ←
    if trustedRootStr.isEmpty then pure none
    else some <$> IO.FS.realPath (System.FilePath.mk trustedRootStr)

  let searchDirsRaw ← field (α := Array String) j "searchPath"
  let searchDirs := searchDirsRaw.toList.map System.FilePath.mk
  initSearchPath sysroot searchDirs
  searchPathRef.set (searchDirs ++ [sysroot / "lib" / "lean"])

  let targetModStrs ← field (α := Array String) j "targetModules"
  if targetModStrs.isEmpty then opFail "targetModules must not be empty"
  let targetMods := targetModStrs.map String.toName

  let strictProofs ← field (α := Bool) j "strictProofs"
  let moduleMode ← field (α := Bool) j "moduleMode"
  let allowAssumptions ← field (α := Bool) j "allowAssumptions"
  let allowProvisionalNative ← field (α := Bool) j "allowProvisionalNative"
  let allowLocalTestAxioms ← field (α := Bool) j "allowLocalTestAxioms"
  let oleanSpecs ← field (α := Array Json) j "oleanFiles"

  -- 1. Pre-check target module names & raw on-disk ModuleData BEFORE `importModules`
  --    (catches size mismatch, duplicate keys, key!=ci.name, and missing .olean.{server,private}
  --    even when `finalizeImport` would throw a generic `already imported` error).
  for m in targetMods do
    let _ ← classifyModuleRole m
    if isStdlibMod m || isLeanCompilerMod m then
      policyFail "stdlibNamedPackageModule" m #[m] "cannot audit a module claiming Init/Std/Lean namespace"

  for specObj in oleanSpecs do
    let modStr ← field (α := String) specObj "module"
    let oleanPathStr ← field (α := String) specObj "path"
    let hasServer ← field (α := Bool) specObj "hasServer"
    let hasPrivate ← field (α := Bool) specObj "hasPrivate"
    let modName := modStr.toName
    let mFile := System.FilePath.mk oleanPathStr
    let main ← try
      unsafe CompactedRegion.read (α := ModuleData) mFile #[]
    catch ex =>
      opFail s!"failed deserializing .olean {mFile}: {ex}"
    let effModMode := moduleMode || main.1.isModule
    if effModMode && !hasServer then
      policyFail "missingOleanServer" modName #[modName] s!"missing {oleanPathStr}.server"
    if effModMode && !hasPrivate then
      policyFail "missingOleanPrivate" modName #[modName] s!"missing {oleanPathStr}.private"
    if moduleMode && !main.1.isModule then
      policyFail "missingOleanServer" modName #[modName] "artifact was not compiled in module mode"
    verifyPartKeysOnly modName main.1
    if main.1.isModule && hasServer && hasPrivate then
      let sFile := OLeanLevel.server.adjustFileName mFile
      let pFile := OLeanLevel.private.adjustFileName mFile
      let server ← unsafe CompactedRegion.read (α := ModuleData) sFile #[main.2]
      let priv ← unsafe CompactedRegion.read (α := ModuleData) pFile #[main.2, server.2]
      verifyPartKeysOnly modName server.1
      let _ ← verifyModuleInventory modName priv.1
    else
      let _ ← verifyModuleInventory modName main.1

  -- 2. Import environment strictly with `loadExts := false` (ZERO initializer execution!)
  let env ← try
    importModules (targetMods.map fun n => { module := n }) {}
      (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  catch ex =>
    opFail s!"importModules failed: {ex}"
  unless env.header.modules.size == env.header.moduleData.size do
    opFail "env.header.modules / moduleData size mismatch"
  let publicEnv := env.setExporting true
  let env := env.setExporting false

  -- 3. Verify search-path & stdlib/Trusted provenance (`Patch 8`) and module-name uniqueness
  let sp ← searchPathRef.get
  for root in sp do
    let realRoot ← try IO.FS.realPath root catch _ => pure root
    unless realRoot == stdRoot do
      for top in ["Init", "Std", "Lean"] do
        if (← (root / top).pathExists) || (← (root / s!"{top}.olean").pathExists) then
          policyFail "stdlibNamedPackageModule" top.toName #[top.toName]
            s!"search-path root {root} shadows {top}"
      if let some tRoot := trustedRoot? then
        unless realRoot == tRoot do
          if (← (root / "Trusted").pathExists) || (← (root / "Trusted.olean").pathExists) then
            policyFail "trustedNamedPackageModule" `Trusted #[`Trusted]
              s!"search-path root {root} shadows Trusted"

  let mut seenModNames : NameSet := {}
  let mut modRoles : Std.HashMap Name String := {}
  let mut auditedSet : NameSet := {}
  let mut baseMods : Array Name := #[]
  for h : idx in [:env.header.modules.size] do
    let m := env.header.modules[idx].module
    let d := env.header.moduleData[idx]!
    if seenModNames.contains m then
      policyFail "duplicateModuleName" m #[m] "duplicate module in header"
    seenModNames := seenModNames.insert m
    if isLeanCompilerMod m then
      policyFail "foreignImport" m #[m] "Lean compiler module cannot be imported by audited code"
    let role ← classifyModuleRole m
    modRoles := modRoles.insert m role
    if isStdlibMod m then
      if !cachedInitMods.contains m then
        let oleanPath ← findOLean m
        let realOlean ← IO.FS.realPath oleanPath
        unless realOlean.toString.startsWith (stdRoot.toString ++ "/") do
          policyFail "stdlibNamedPackageModule" m #[m]
            s!"stdlib module {m} resolved outside sysroot at {realOlean}"
      baseMods := baseMods.push m
    else if isTrustedMod m && !targetMods.contains m then
      let oleanPath ← findOLean m
      let realOlean ← IO.FS.realPath oleanPath
      match trustedRoot? with
      | some tRoot =>
        unless realOlean.toString.startsWith (tRoot.toString ++ "/") do
          policyFail "trustedNamedPackageModule" m #[m]
            s!"Trusted module {m} resolved outside pinned build root at {realOlean}"
        let _ ← verifyModuleInventory m d (some env)
        baseMods := baseMods.push m
      | none =>
        policyFail "trustedNamedPackageModule" m #[m]
          s!"untrusted search path attempted to load {m}"
    else
      let oleanPath ← findOLean m
      if d.isModule then
        let sFile := OLeanLevel.server.adjustFileName oleanPath
        let pFile := OLeanLevel.private.adjustFileName oleanPath
        unless (← sFile.pathExists) do
          policyFail "missingOleanServer" m #[m] s!"missing {sFile}"
        unless (← pFile.pathExists) do
          policyFail "missingOleanPrivate" m #[m] s!"missing {pFile}"
      auditedSet := auditedSet.insert m

  -- 4. Verify inventory, SMap key bijection (`map₁` & `map₂`), cross-module duplicates, & extraConstNames
  if cachedInitMods.isEmpty then
    for (n, ci) in env.checked.get.constants do
      unless n == ci.name do
        policyFail "keyNameMismatch" n #[n, ci.name] s!"env.checked SMap key {n} != ci.name {ci.name}"
    for (n, ci) in publicEnv.constants do
      unless n == ci.name do
        policyFail "keyNameMismatch" n #[n, ci.name] s!"public SMap key {n} != ci.name {ci.name}"
  else
    for (n, ci) in env.checked.get.constants.map₂ do
      unless n == ci.name do
        policyFail "keyNameMismatch" n #[n, ci.name] s!"env.checked map₂ key {n} != ci.name {ci.name}"
    for (n, ci) in publicEnv.constants.map₂ do
      unless n == ci.name do
        policyFail "keyNameMismatch" n #[n, ci.name] s!"public map₂ key {n} != ci.name {ci.name}"

  let mut byModMap : Std.HashMap Name (Std.HashMap Name ConstantInfo) := {}
  let mut modIdxMap : Std.HashMap Name Nat := {}
  let mut replayLocals : Std.HashMap Name ConstantInfo := {}
  let mut crossDecls : Std.HashMap Name (Name × ConstantInfo) := {}

  for h : idx in [:env.header.modules.size] do
    let m := env.header.modules[idx].module
    let d := env.header.moduleData[idx]!
    modIdxMap := modIdxMap.insert m idx
    if auditedSet.contains m then
      let byName ← verifyModuleInventory m d (some env)
      byModMap := byModMap.insert m byName
      for ci in d.constants do
        if let some (prevMod, prevCi) := crossDecls[ci.name]? then
          unless Lean.isReservedName env ci.name && sameStoredDecl prevCi ci do
            policyFail "duplicateConstName" prevMod #[prevMod, ci.name]
              s!"cross-module duplicate or subsumesInfo body-swap on {ci.name} ({prevMod} vs {m})"
        else
          crossDecls := crossDecls.insert ci.name (m, ci)
        let some origIdx := env.getModuleIdxFor? ci.name
          | policyFail "keyNameMismatch" m #[m, ci.name] "missing const2ModIdx entry"
        let origMod := env.header.modules[origIdx]!.module
        if origMod != m then
          unless auditedSet.contains origMod && Lean.isReservedName env ci.name do
            policyFail "reservedOriginMissingSibling" m #[m, ci.name, origMod]
              s!"origin mismatch: {ci.name} in {m} claims {origMod}"
          let some stored := env.checked.get.find? ci.name
            | policyFail "keyNameMismatch" m #[m, ci.name] "missing stored constant"
          unless sameStoredDecl stored ci do
            policyFail "duplicateConstName" origMod #[origMod, ci.name]
              "stored declaration differs from inventory copy"
        if !isCodegenUnsafeRec byName ci then
          replayLocals ← insertReplayLocalUnique env m replayLocals ci
      for extra in d.extraConstNames do
        if let some origIdx := env.getModuleIdxFor? extra then
          let origMod := env.header.modules[origIdx]!.module
          if origMod != m then
            policyFail "extraConstNameProvenance" m #[m, extra]
              s!"extraConstName {extra} belongs to {origMod}"

  -- Precompute stdlib >=2-segment public names & statement-side audited names for V15 shadowing
  let mut stdMultiNames : NameSet := cachedInitMulti?.getD {}
  let coreSingleProtected : NameSet := .ofList [`Nat, `Bool, `String, `True, `False, `Eq, `Quot]
  for h : idx in [:env.header.modules.size] do
    let m := env.header.modules[idx].module
    let d := env.header.moduleData[idx]!
    let alreadyCachedInit := cachedInitMulti?.isSome && cachedInitMods.contains m
    if isStdlibMod m && !alreadyCachedInit then
      for ci in d.constants do
        let ge2 := match ci.name with
          | .str p _ | .num p _ => !p.isAnonymous
          | .anonymous => false
        if !isPrivateName ci.name && ge2 then
          stdMultiNames := stdMultiNames.insert ci.name

  -- Precompute private instances per module for `V14` (`privateInstanceLeakViaImportAll`)
  let findPrivateInstanceInMod (targetMod : Name) : Option Name := Id.run do
    let some tIdx := modIdxMap[targetMod]? | return none
    let tData := env.header.moduleData[tIdx]!
    let insts := Meta.instanceExtension.ext.getModuleEntries env tIdx
    for entry in insts do
      match entry with
      | .global ie | .scoped _ ie =>
        match ie.globalName? with
        | some gn =>
          if isPrivateName gn || ie.attrKind == .local ||
             (tData.isModule && !(publicEnv.contains gn)) then
            return some gn
        | none => return some (`_local_instance)
    return none

  -- Helper: compute transitive import closure of each audited module
  let mut directImportsMap : Std.HashMap Name (Array Import) := {}
  for h : idx in [:env.header.modules.size] do
    let m := env.header.modules[idx].module
    if auditedSet.contains m then
      directImportsMap := directImportsMap.insert m env.header.moduleData[idx]!.imports

  let computeImportClosure (startMod : Name) : IO NameSet := do
    let mut visited : NameSet := {}
    let initImps := (directImportsMap[startMod]?.getD #[]).toList.map (·.module)
    let mut pending : List Name := initImps
    while !pending.isEmpty do
      let curr := pending.head!
      pending := pending.tail!
      if curr == startMod then
        policyFail "importCycle" startMod #[startMod] "cycle in module imports"
      if !visited.contains curr then
        visited := visited.insert curr
        if let some more := directImportsMap[curr]? then
          pending := (more.toList.map (·.module)) ++ pending
    return visited

  -- 5. Audit imports, persistent extensions, shadowing, declarations, & reference-vs-import closure
  let forbiddenRawExtSubstrings : List String := [
    "macro", "Elab", "elab", "delab", "unexpander", "simproc", "unif_hint", "parserExtension"
  ]

  for h : idx in [:env.header.modules.size] do
    let m := env.header.modules[idx].module
    let d := env.header.moduleData[idx]!
    if auditedSet.contains m then
      let role := modRoles[m]!
      let byName := byModMap[m]!
      let mut localConstSet : NameSet := {}
      let mut localReplayable : NameSet := {}
      for ci in d.constants do
        localConstSet := localConstSet.insert ci.name
        if !isCodegenUnsafeRec byName ci then
          localReplayable := localReplayable.insert ci.name

      -- Check `unsafe`/`partial` declarations BEFORE extension hooks so `unsafe def` / `unsafe t`
      -- (which also synthesizes `@[implemented_by ..._unsafe_impl]`) reports `unsafeOrPartialDecl`.
      for ci in d.constants do
        if isCodegenUnsafeRec byName ci then
          pure ()
        else if ci.isUnsafe || ci.isPartial then
          policyFail "unsafeOrPartialDecl" m #[m, ci.name] "unsafe or partial declaration"

      -- 5a. Imports (`V14`, `B2`, `A2`, `B3`)
      for imp in d.imports do
        if imp.importAll then
          if let some privInst := findPrivateInstanceInMod imp.module then
            policyFail "privateInstanceLeakViaImportAll" m #[m, imp.module, privInst]
              s!"import all exposes private instance {privInst} from {imp.module}"
          else
            policyFail "forbiddenImportAll" m #[m, imp.module] "import all is forbidden"
        if !imp.isExported then
          -- Note: in `module` mode without `public import`, Lean sets `isExported := false` on ordinary
          -- `import`. Only reject `!imp.isExported` when NOT in `d.isModule` (`private import` in
          -- non-module file) OR when `imp.module == `Init` was explicitly made private.
          if !d.isModule then
            policyFail "forbiddenImportModifier" m #[m, imp.module] "private"
        if imp.isMeta && imp.module != `Init then
          policyFail "forbiddenImportModifier" m #[m, imp.module] "meta"
        if !isWellFormedName imp.module || isLeanCompilerMod imp.module || !seenModNames.contains imp.module then
          policyFail "foreignImport" m #[m, imp.module] s!"foreign or disallowed import {imp.module}"
        let impRole := modRoles[imp.module]?.getD "spec"
        unless importRoleAllowed role impRole do
          policyFail "forbiddenImportDirection" m #[m, imp.module] s!"{role} -> {impRole}"
      let visClosure ← computeImportClosure m

      -- 5b. Persistent extensions (zero initializers executed!)
      let macros := Elab.macroAttribute.ext.ext.getModuleEntries env idx
      for entry in macros do
        match entry with
        | .global e => policyFail "forbiddenMacroOrElab" m #[m, e.declName] "macro"
        | .scoped _ e => policyFail "forbiddenMacroOrElab" m #[m, e.declName] "scoped_macro"

      let parsers := Parser.parserExtension.ext.getModuleEntries env idx
      for entry in parsers do
        match entry with
        | .global _ => policyFail "forbiddenMacroOrElab" m #[m] "syntax"
        | .scoped _ _ => policyFail "forbiddenMacroOrElab" m #[m] "scoped_syntax"

      let cmdElabs := Elab.Command.commandElabAttribute.ext.ext.getModuleEntries env idx
      for entry in cmdElabs do
        match entry with
        | .global e => policyFail "forbiddenMacroOrElab" m #[m, e.declName] "command_elab"
        | .scoped _ e => policyFail "forbiddenMacroOrElab" m #[m, e.declName] "scoped_elab"

      let termElabs := Elab.Term.termElabAttribute.ext.ext.getModuleEntries env idx
      for entry in termElabs do
        match entry with
        | .global e => policyFail "forbiddenMacroOrElab" m #[m, e.declName] "term_elab"
        | .scoped _ e => policyFail "forbiddenMacroOrElab" m #[m, e.declName] "scoped_term_elab"

      let delabs := PrettyPrinter.Delaborator.delabAttribute.ext.ext.getModuleEntries env idx
      for entry in delabs do
        match entry with
        | .global e | .scoped _ e => policyFail "forbiddenMacroOrElab" m #[m, e.declName] "delab"

      let unexps := PrettyPrinter.Delaborator.appUnexpanderAttribute.ext.ext.getModuleEntries env idx
      for entry in unexps do
        match entry with
        | .global e | .scoped _ e => policyFail "forbiddenMacroOrElab" m #[m, e.declName] "app_unexpander"

      -- Raw `d.entries` catch-all for any other macro/elab/simproc/unif_hint extension
      for (extName, rawArr) in d.entries do
        if !rawArr.isEmpty then
          let es := extName.toString
          -- Note: `Lean.Elab.Term.elabAsElim` & `Lean.Elab.Structural.eqnInfoExt` are standard Lean
          -- recursor/structural-recursion bookkeeping, NOT user syntax/macro/elab hooks.
          if es != "Lean.Elab.Term.elabAsElim" && es != "Lean.Elab.Structural.eqnInfoExt" then
            if forbiddenRawExtSubstrings.any (fun sub => (es.splitOn sub).length > 1) then
              policyFail "forbiddenMacroOrElab" m #[m, extName] es

      -- Init / codegen hooks (`V10`): check BOTH `.olean` (`getModuleEntries`) AND `.ir` (`getModuleIREntries`)!
      let regInits := regularInitAttr.ext.getModuleEntries env idx ++
                      regularInitAttr.ext.getModuleIREntries env idx
      if let some (decl, _) := regInits[0]? then
        policyFail "forbiddenInitOrCodegenHook" m #[m, decl] "initialize"

      let builtinInits := builtinInitAttr.ext.getModuleEntries env idx ++
                          builtinInitAttr.ext.getModuleIREntries env idx
      if let some (decl, _) := builtinInits[0]? then
        policyFail "forbiddenInitOrCodegenHook" m #[m, decl] "builtin_initialize"

      let implBys := Compiler.implementedByAttr.ext.getModuleEntries env idx ++
                     Compiler.implementedByAttr.ext.getModuleIREntries env idx
      if let some (decl, _) := implBys[0]? then
        policyFail "forbiddenInitOrCodegenHook" m #[m, decl] "implemented_by"

      let externs := externAttr.ext.getModuleEntries env idx ++
                     externAttr.ext.getModuleIREntries env idx
      if let some (decl, _) := externs[0]? then
        policyFail "forbiddenInitOrCodegenHook" m #[m, decl] "extern"

      let cExports := exportAttr.ext.getModuleEntries env idx ++
                      exportAttr.ext.getModuleIREntries env idx
      if let some (decl, _) := cExports[0]? then
        policyFail "forbiddenInitOrCodegenHook" m #[m, decl] "c_export"

      -- `export Ns (x)` aliases (`V15`)
      let aliases := aliasExtension.getModuleEntries env idx
      if let some (alName, _) := aliases[0]? then
        policyFail "forbiddenShadowingOrExport" m #[m, alName] "export"

      -- Reducibility overrides (`V13`)
      let mut localRedOver : NameSet := {}
      for (target, _) in reducibilityCoreExt.getModuleEntries env idx do
        unless localReplayable.contains target do
          policyFail "forbiddenReducibilityOverride" m #[m, target] "reducibilityCore on non-local decl"
      for entry in reducibilityExtraExt.ext.getModuleEntries env idx do
        let target := match entry with | .global (t, _) => t | .scoped _ (t, _) => t
        unless localReplayable.contains target do
          policyFail "forbiddenReducibilityOverride" m #[m, target] "reducibility override on foreign decl"
        localRedOver := localRedOver.insert target

      -- Default instances & coercions (`V12`)
      let defInsts := Meta.defaultInstanceExtension.getModuleEntries env idx
      for de in defInsts do
        unless role == "defsExempt" do
          policyFail "forbiddenInstanceOrCoe" m #[m, de.instanceName] "default_instance"
        unless localReplayable.contains de.instanceName &&
               isBaseInstanceAnchor localReplayable localRedOver byName de.className do
          policyFail "forbiddenInstanceOrCoe" m #[m, de.instanceName] "default_instance_of_imported_target"

      let coes := Meta.coeExt.ext.getModuleEntries env idx
      for ce in coes do
        let decl := match ce with | .global (n, _) => n | .scoped _ (n, _) => n
        unless role == "defsExempt" && localReplayable.contains decl do
          policyFail "forbiddenInstanceOrCoe" m #[m, decl] "coe"
        let some ci := byName[decl]?
          | policyFail "forbiddenInstanceOrCoe" m #[m, decl] "coe"
        let some normTy := normExprInEnv env 1024 ci.type
          | policyFail "forbiddenInstanceOrCoe" m #[m, decl] "coe"
        unless hasRigidBaseAnchor env localReplayable localRedOver byName normTy do
          policyFail "forbiddenInstanceOrCoe" m #[m, decl] "coe_between_imported_types"

      -- Instances (`V11`, `V12`, Episode 1 orphan-instance hardening)
      let insts := Meta.instanceExtension.ext.getModuleEntries env idx
      for entry in insts do
        match entry with
        | .scoped ns ie =>
          let some dName := ie.globalName?
            | policyFail "forbiddenInstanceOrCoe" m #[m] "anonymous_scoped_instance"
          unless role == "defsExempt" do
            policyFail "forbiddenInstanceOrCoe" m #[m, dName] "scoped_instance"
          unless localReplayable.contains dName do
            policyFail "forbiddenInstanceOrCoe" m #[m, dName] "imported_instance"
          let some ci := byName[dName]?
            | policyFail "forbiddenInstanceOrCoe" m #[m, dName] "imported_instance"
          let some normConcl := (normExprInEnv env 1024 ci.type).map stripForallAndLam
            | policyFail "forbiddenInstanceOrCoe" m #[m, dName] "scoped_instance_of_imported_target"
          let .const cls _ := normConcl.getAppFn
            | policyFail "forbiddenInstanceOrCoe" m #[m, dName] "scoped_instance_of_imported_target"
          unless isBaseInstanceAnchor localReplayable localRedOver byName cls do
            policyFail "forbiddenInstanceOrCoe" m #[m, dName] "scoped_instance_of_imported_target"
          unless (nameComponents m).isPrefixOf (nameComponents ns) do
            policyFail "forbiddenInstanceOrCoe" m #[m, dName] "invalid_instance_scope"
        | .global ie =>
          let some dName := ie.globalName?
            | policyFail "forbiddenInstanceOrCoe" m #[m] "anonymous_local_instance"
          unless localReplayable.contains dName do
            policyFail "forbiddenInstanceOrCoe" m #[m, dName] "imported_instance"
          let some ci := byName[dName]?
            | policyFail "forbiddenInstanceOrCoe" m #[m, dName] "imported_instance"
          let some normConcl := (normExprInEnv env 1024 ci.type).map stripForallAndLam
            | policyFail "forbiddenInstanceOrCoe" m #[m, dName] "orphan_instance_of_imported_class"
          let .const cls _ := normConcl.getAppFn
            | policyFail "forbiddenInstanceOrCoe" m #[m, dName] "orphan_instance_of_imported_class"
          if isAutoSizeOfInst byName dName cls then
            pure ()
          else if isBaseInstanceAnchor localReplayable localRedOver byName cls then
            pure ()
          else
            if role == "proof" || role == "verify" || (strictProofs && role != "defsExempt") then
              policyFail "forbiddenInstanceOrCoe" m #[m, dName] "instance_of_imported_class"
            let inputArgs := nonOutParamArgs env cls normConcl.getAppArgs
            unless inputArgs.any (hasRigidBaseAnchor env localReplayable localRedOver byName) do
              policyFail "forbiddenInstanceOrCoe" m #[m, dName] "orphan_instance_of_imported_class"

      -- 5c. Public namespace suffix shadowing (`V15`)
      let mut stmtProtected : NameSet := {}
      for h2 : idx2 in [:env.header.modules.size] do
        let m2 := env.header.modules[idx2].module
        if auditedSet.contains m2 && m2 != m && isStatementSideRole (modRoles[m2]!) then
          let m2Parts := nameComponents m2
          for ci2 in env.header.moduleData[idx2]!.constants do
            if !isPrivateName ci2.name && !hasInternalPart ci2.name then
              stmtProtected := stmtProtected.insert ci2.name
              let cParts := nameComponents ci2.name
              if m2Parts.isPrefixOf cParts && cParts.length > m2Parts.length then
                let stripped := (cParts.drop m2Parts.length).foldl Name.str .anonymous
                stmtProtected := stmtProtected.insert stripped

      for ci in d.constants do
        if !isPrivateName ci.name then
          let cParts := nameComponents ci.name
          if cParts.length == 2 then
            let leaf := Name.mkSimple cParts[1]!
            if coreSingleProtected.contains leaf then
              policyFail "forbiddenShadowingOrExport" m #[m, ci.name] "namespace_shadow"
          for suf in properSuffixes ci.name do
            if !hasInternalPart suf then
              if stdMultiNames.contains suf || stmtProtected.contains suf then
                policyFail "forbiddenShadowingOrExport" m #[m, ci.name] "namespace_shadow"

      -- 5d. Declaration safety, unreferenced axioms (`V04`), & reference-vs-import closure (`B3`)
      for ci in d.constants do
        if isCodegenUnsafeRec byName ci then
          pure ()
        else if ci.isUnsafe || ci.isPartial then
          policyFail "unsafeOrPartialDecl" m #[m, ci.name] "unsafe or partial declaration"

        if ci.isAxiom then
          if ci.name == `sorryAx then
            policyFail "forbiddenAxiom" m #[ci.name, `sorryAx, m] "sorryAx"
          if isCompilerTrustConst ci.name then
            policyFail "forbiddenNativeReductionAxiom" m #[ci.name, ci.name] "Lean.trustCompiler"
          if isNativeReductionConst ci.name then
            unless allowProvisionalNative && role == "proof" && isProvisionalNativeName ci.name do
              policyFail "forbiddenNativeReductionAxiom" m #[ci.name, ci.name] "native reduction axiom"
            checkValidProvisionalNativeAxiom env ci.name ci.name ci
          else if role == "assumptions" then
            unless allowAssumptions do
              policyFail "forbiddenAxiom" m #[ci.name, ci.name, m] "assumption axiom requires --allow-assumptions"
          else if role == "test" && allowLocalTestAxioms then
            pure ()
          else
            policyFail "forbiddenAxiom" m #[ci.name, ci.name, m] "unapproved axiom"

        let edges ← declarationEdges m ci
        for dep in edges do
          if let some depIdx := env.getModuleIdxFor? dep then
            let depMod := env.header.modules[depIdx]!.module
            if auditedSet.contains depMod && depMod != m && !visClosure.contains depMod then
              policyFail "referenceOutsideImportClosure" m #[m, ci.name, dep, depMod]
                s!"{ci.name} references {dep} from unimported {depMod}"

  -- 6. Direct Constant-Closure Walk (explicitly ignoring `exportedAxiomsExt` — `V05`, `V06`)
  let edgesCache ← IO.mkRef ({} : Std.HashMap Name NameSet)
  let getEdgesCached (ownerMod : Name) (ci : ConstantInfo) : IO NameSet := do
    if let some hit := (← edgesCache.get)[ci.name]? then return hit
    let computed ← declarationEdges ownerMod ci
    edgesCache.modify (·.insert ci.name computed)
    return computed

  let checkDepNode (rootMod rootName dep : Name) (isTestRoot : Bool) : IO (ConstantInfo × Name × String) := do
    if dep == `sorryAx then
      let declMod := match env.getModuleIdxFor? dep with
        | some i => env.header.modules[i]!.module
        | none => `Init.Prelude
      policyFail "forbiddenAxiom" rootMod #[rootName, `sorryAx, declMod] "depends on sorryAx"
    let some depCi := env.checked.get.find? dep
      | policyFail "unknownConstant" rootMod #[dep] s!"unknown constant {dep}"
    let some depIdx := env.getModuleIdxFor? dep
      | policyFail "unknownConstant" rootMod #[dep] s!"missing module index for {dep}"
    let depMod := env.header.modules[depIdx]!.module
    let depRole := modRoles[depMod]?.getD "foundation"
    if dep != rootName then
      if depCi.isUnsafe || depCi.isPartial then
        policyFail "unsafeOrPartialDecl" depMod #[depMod, dep] "depends on unsafe/partial declaration"
    else if depCi.isUnsafe then
      policyFail "unsafeOrPartialDecl" depMod #[depMod, dep] "unsafe declaration"
    if isCompilerTrustConst dep then
      policyFail "forbiddenNativeReductionAxiom" rootMod #[rootName, dep] "depends on Lean.trustCompiler"
    if isNativeReductionConst dep then
      if isTestRoot then
        policyFail "forbiddenNativeReductionAxiom" rootMod #[rootName, dep] "native reduction in test module"
      unless allowProvisionalNative && depRole == "proof" && depCi.isAxiom && isProvisionalNativeName dep do
        policyFail "forbiddenNativeReductionAxiom" rootMod #[rootName, dep] "depends on native reduction axiom"
      checkValidProvisionalNativeAxiom env rootName dep depCi
    else if depCi.isAxiom then
      let isFound := isStdlibMod depMod && isFoundationalAxiom dep
      if !isFound then
        if isTestRoot then
          unless allowLocalTestAxioms && depMod == rootMod do
            policyFail "testModuleForeignAxiom" rootMod #[rootMod, rootName, dep] "foreign axiom in test module"
        else
          unless allowAssumptions && depRole == "assumptions" do
            policyFail "forbiddenAxiom" rootMod #[rootName, dep, depMod] "depends on unapproved axiom"
    return (depCi, depMod, depRole)

  let walkRootsClosure (rootMod : Name) (roots : List Name) (isTestRoot : Bool)
      (allowRootUnsafeRec : NameSet := {}) : IO (Array Name × Array Name × Nat) := do
    let mut pending : List Name := roots
    let mut visited : NameSet := {}
    let mut reachedProv : NameSet := {}
    let mut reachedAssum : NameSet := {}
    while !pending.isEmpty do
      let curr := pending.head!
      pending := pending.tail!
      if !visited.contains curr then
        visited := visited.insert curr
        let isExcusedRoot := allowRootUnsafeRec.contains curr
        let (depCi, depMod, _) ← checkDepNode rootMod (if isExcusedRoot then curr else roots.headD curr) curr isTestRoot
        if depCi.isAxiom then
          if isNativeReductionConst curr then
            reachedProv := reachedProv.insert curr
          else if !(isStdlibMod depMod && isFoundationalAxiom curr) then
            reachedAssum := reachedAssum.insert curr
        if !isStdlibMod depMod then
          let es ← getEdgesCached depMod depCi
          -- Ensure normal declarations never reference an `_unsafe_rec` companion
          if !isExcusedRoot then
            for e in es do
              if let some eCi := env.checked.get.find? e then
                if eCi.isUnsafe || eCi.isPartial then
                  let eMod := match env.getModuleIdxFor? e with
                    | some i => env.header.modules[i]!.module
                    | none => rootMod
                  policyFail "unsafeOrPartialDecl" eMod #[eMod, e] "depends on unsafe/partial declaration"
          pending := es.toList ++ pending
    return (reachedProv.toArray.qsort Name.lt, reachedAssum.toArray.qsort Name.lt, visited.size)

  let mut allReachedAxioms : NameSet := {}
  for h : idx in [:env.header.modules.size] do
    let m := env.header.modules[idx].module
    let d := env.header.moduleData[idx]!
    if auditedSet.contains m then
      let role := modRoles[m]!
      let isTest := role == "test"
      let byName := byModMap[m]!
      let mut normalRoots : List Name := []
      let mut unsafeRecRoots : List Name := []
      let mut unsafeRecSet : NameSet := {}
      for ci in d.constants do
        if isCodegenUnsafeRec byName ci then
          unsafeRecRoots := ci.name :: unsafeRecRoots
          unsafeRecSet := unsafeRecSet.insert ci.name
        else
          normalRoots := ci.name :: normalRoots
      if !normalRoots.isEmpty then
        let (prov, assum, _) ← walkRootsClosure m normalRoots.reverse isTest {}
        for p in prov do allReachedAxioms := allReachedAxioms.insert p
        for a in assum do allReachedAxioms := allReachedAxioms.insert a
      for ur in unsafeRecRoots.reverse do
        let (prov, assum, _) ← walkRootsClosure m [ur] isTest (NameSet.empty.insert ur)
        for p in prov do allReachedAxioms := allReachedAxioms.insert p
        for a in assum do allReachedAxioms := allReachedAxioms.insert a

  -- 7. Verify-module coverage, statement-origin separation, & isolated per-item status (`B3` + `A2`)
  let mut itemReports : Array Json := #[]
  for h : idx in [:env.header.modules.size] do
    let m := env.header.modules[idx].module
    if auditedSet.contains m && modRoles[m]! == "verify" then
      let thmName := m.str "verified"
      let byName := byModMap[m]!
      let some ci := byName[thmName]?
        | policyFail "invalidVerifyRoot" m #[thmName] "Verify module missing <Mod>.verified theorem"
      unless ci matches .thmInfo _ do
        policyFail "invalidVerifyRoot" m #[thmName] "verified must be a theorem"
      let headConst := (stripForallAndLam ci.type).getAppFn
      unless verifyCertificateHead headConst do
        policyFail "invalidVerifyRoot" m #[thmName]
          "verified theorem statement must have a Trusted.VerificationResult certificate head"
      -- Statement-origin walk: unfold everything except `foundation` (`Init`/`Std`) and `trusted` (`Trusted.*`),
      -- rejecting any `theory` (`Anneal.*`) constant in `ci.type`!
      let initStmtEdges ← expressionEdges m thmName ci.type
      let mut stmtPending := initStmtEdges.toList
      let mut stmtVisited : NameSet := {}
      while !stmtPending.isEmpty do
        let curr := stmtPending.head!
        stmtPending := stmtPending.tail!
        if !stmtVisited.contains curr then
          stmtVisited := stmtVisited.insert curr
          let some sIdx := env.getModuleIdxFor? curr
            | policyFail "unknownConstant" m #[curr] s!"unknown constant {curr} in statement"
          let sMod := env.header.modules[sIdx]!.module
          let sRole := modRoles[sMod]?.getD "foundation"
          if sRole == "theory" then
            policyFail "statementTheoryLeak" m #[thmName, curr, sMod]
              s!"statement of {thmName} depends on theory declaration {curr} from {sMod}"
          if sRole != "foundation" && sRole != "trusted" then
            let some sCi := env.checked.get.find? curr
              | policyFail "unknownConstant" m #[curr] s!"missing {curr}"
            let es ← getEdgesCached sMod sCi
            stmtPending := es.toList ++ stmtPending
      -- Fresh isolated closure walk per verify item (ZERO shared `cleanNonWorkspace` cache!)
      let (prov, assum, _) ← walkRootsClosure m [thmName] false {}
      let status :=
        if prov.isEmpty && assum.isEmpty then "VerifiedUnconditional"
        else if prov.isEmpty then "VerifiedConditional"
        else if assum.isEmpty then "ProvisionalNative"
        else "ProvisionalNativeConditional"
      itemReports := itemReports.push <| Json.mkObj [
        ("module", toJson m.toString),
        ("root", toJson thmName.toString),
        ("status", toJson status),
        ("provisional", toJson (prov.map Name.toString)),
        ("assumptions", toJson (assum.map Name.toString))
      ]

  -- 8. Clean-Environment Kernel Replay (`V03`, `V09`, `lean4#16677`)
  for (k, ci) in replayLocals.toList do
    unless k == ci.name do
      policyFail "keyNameMismatch" k #[k, ci.name] "replayLocals key != ci.name"

  let canReuseCleanInit := !cachedInitMods.isEmpty && baseMods.all cachedInitMods.contains
  let baseEnv ← match cachedInitEnv?, canReuseCleanInit with
    | some ie, true => pure ie
    | _, _ =>
      importModules (baseMods.map fun n => { module := n }) {}
        (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  try
    let _ ← baseEnv.toKernelEnv.replay replayLocals
  catch ex =>
    policyFail "kernelTypeError" targetMods[0]! #[targetMods[0]!] ex.toString

  let sortedAxioms := (allReachedAxioms.toArray.qsort Name.lt).map Name.toString
  return Json.mkObj [
    ("auditedModules", toJson (auditedSet.toArray.qsort Name.lt |>.map Name.toString)),
    ("replayedDeclarations", toJson replayLocals.size),
    ("reachedAxioms", toJson sortedAxioms),
    ("items", .arr itemReports),
    ("replay", toJson true)
  ]

end OleanReplayInspector

def runOneItem (j : Json) (cachedInitEnv? : Option Environment := none)
    (cachedInitMods : NameSet := {})
    (cachedInitMulti? : Option NameSet := none) : IO (Json × UInt32) := do
  try
    let res ← OleanReplayInspector.auditOleans j cachedInitEnv? cachedInitMods cachedInitMulti?
    return (Json.mkObj [("ok", toJson true), ("result", res)], 0)
  catch ex =>
    let msg := ex.toString
    let pfx := "POLICY_JSON:"
    if (msg.splitOn pfx).length > 1 then
      let payload := String.intercalate pfx ((msg.splitOn pfx).drop 1)
      let vJson := match Json.parse payload with
        | .ok vj => vj
        | .error _ => Json.mkObj [
            ("category", toJson "policyViolation"),
            ("module", toJson ""),
            ("names", toJson (#[] : Array String)),
            ("detail", toJson msg)
          ]
      return (Json.mkObj [("ok", toJson false), ("kind", toJson "policy"), ("violation", vJson)], 1)
    else
      return (Json.mkObj [("ok", toJson false), ("kind", toJson "operational"), ("message", toJson msg)], 2)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--batch", reqPath, respPath] =>
    try
      let raw ← IO.FS.readFile reqPath
      let j ← match Json.parse raw with
        | .ok v => pure v
        | .error e => OleanReplayInspector.opFail s!"invalid batch JSON: {e}"
      let items ← OleanReplayInspector.field (α := Array Json) j "items"
      let sysrootStr ← OleanReplayInspector.field (α := String) j "sysroot"
      initSearchPath (System.FilePath.mk sysrootStr) []
      searchPathRef.set [System.FilePath.mk sysrootStr / "lib" / "lean"]
      let cleanInit ← importModules #[{ module := `Init }] {}
        (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
      for (n, ci) in cleanInit.checked.get.constants do
        unless n == ci.name do
          OleanReplayInspector.opFail s!"cleanInit SMap key mismatch: {n} != {ci.name}"
      let (initMods, initMulti) := OleanReplayInspector.computeInitMultiNames cleanInit
      let mut outs : Array Json := #[]
      for item in items do
        let (outJ, _) ← runOneItem item (some cleanInit) initMods (some initMulti)
        outs := outs.push outJ
      IO.FS.writeFile respPath (Json.mkObj [("items", .arr outs)]).pretty
      return 0
    catch ex =>
      IO.eprintln ex.toString
      return 2
  | [reqPath, respPath] =>
    let raw ← IO.FS.readFile reqPath
    match Json.parse raw with
    | .error e =>
      let out := Json.mkObj [("ok", toJson false), ("kind", toJson "operational"), ("message", toJson e)]
      IO.FS.writeFile respPath out.pretty
      return 2
    | .ok j =>
      let (out, rc) ← runOneItem j none {} none
      IO.FS.writeFile respPath out.pretty
      return rc
  | _ =>
    IO.eprintln "usage: OleanReplayInspector [--batch] <request.json> <response.json>"
    return 2
"""


# ---------------------------------------------------------------------------
# Embedded Lean 4.34.1 Binary `.olean` Tamper Generator (`TamperForge.lean`)
# ---------------------------------------------------------------------------
# Used strictly inside `with tempfile.TemporaryDirectory():` during `--run-tamper-suite`
# to produce real binary `.olean` files on disk via `Lean.saveModuleData` for vectors
# that Lean's compiler refuses to emit honestly (`01`, `02`, `03`, `V06`, `V09`,
# key-aligned `inductInfo.all`, foreign `quotInfo`, reference outside import closure,
# forged `_unsafe_rec`).

FORGE_LEAN_SOURCE = r"""import Lean
import Lean.Replay

open Lean

def writeOlean (outDir : System.FilePath) (modName : Name) (mdata : ModuleData) : IO Unit := do
  let parts := modName.components.map Name.toString
  let rel := System.mkFilePath parts |>.addExtension "olean"
  let full := outDir / rel
  if let some parent := full.parent then
    IO.FS.createDirAll parent
  saveModuleData full modName mdata

def readSingleOlean (oleanPath : System.FilePath) : IO ModuleData := do
  let (mdata, _) ← readModuleData oleanPath
  return mdata

def main (args : List String) : IO UInt32 := do
  let [baseDirStr, outDirStr] := args
    | throw <| IO.userError "usage: TamperForge <compiledBaseDir> <forgedOutDir>"
  let baseDir := System.FilePath.mk baseDirStr
  let outDir := System.FilePath.mk outDirStr
  let sysroot ← findSysroot "lean"
  initSearchPath sysroot [baseDir]

  -- 01: `leanprover/lean4#16677` recursor key-name mismatch (+ sub-variants ctor, quot, thm_dup, induct)
  let d01 ← readSingleOlean (baseDir / "Proof" / "Tamper01.olean")
  let ciInd := d01.constants.find? (·.name == `Proof.Tamper01.T) |>.get!
  let ciCtor := d01.constants.find? (·.name == `Proof.Tamper01.T.mk) |>.get!
  let ciRec := d01.constants.find? (·.name == `Proof.Tamper01.T.rec) |>.get!
  let ciThm := d01.constants.find? (·.name == `Proof.Tamper01.validWitness) |>.get!

  let forgedRec : ConstantInfo := match ciRec with
    | .recInfo v => .recInfo { v with toConstantVal := { v.toConstantVal with type := mkConst ``False } }
    | _ => unreachable!
  writeOlean (outDir / "01_rec") `Proof.Tamper01 {
    d01 with
    constNames := d01.constNames.push `Proof.Tamper01.forgedFalse
    constants  := d01.constants.push forgedRec
  }

  -- Verify empirically that unpatched Lean 4.34.1 `Kernel.Environment.replay` ACCEPTS `01_rec`!
  let cleanBase ← importModules #[{ module := `Init }] {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let mut map01 : Std.HashMap Name ConstantInfo := {}
  for i in [:d01.constNames.size] do
    map01 := map01.insert d01.constNames[i]! d01.constants[i]!
  map01 := map01.insert `Proof.Tamper01.forgedFalse forgedRec
  let _ ← cleanBase.toKernelEnv.replay map01

  let forgedCtor : ConstantInfo := match ciCtor with
    | .ctorInfo v => .ctorInfo { v with toConstantVal := { v.toConstantVal with type := mkConst ``False } }
    | _ => unreachable!
  writeOlean (outDir / "01b_ctor") `Proof.Tamper01 {
    d01 with
    constNames := d01.constNames.push `Proof.Tamper01.forgedCtorFalse
    constants  := d01.constants.push forgedCtor
  }

  let forgedQuot : ConstantInfo := .quotInfo {
    name := `Quot, levelParams := [], type := mkConst ``False, kind := .type
  }
  writeOlean (outDir / "01c_quot") `Proof.Tamper01 {
    d01 with
    constNames := d01.constNames.push `Proof.Tamper01.forgedQuotFalse
    constants  := d01.constants.push forgedQuot
  }

  let forgedThmDup : ConstantInfo := match ciThm with
    | .thmInfo v => .thmInfo { v with value := mkApp2 (mkConst ``sorryAx [Level.zero]) (mkConst ``True) (mkConst ``Bool.false) }
    | _ => unreachable!
  writeOlean (outDir / "01d_thm_dup") `Proof.Tamper01 {
    d01 with
    constNames := d01.constNames.push `Proof.Tamper01.aliasedSorryThm
    constants  := d01.constants.push forgedThmDup
  }

  let forgedInd : ConstantInfo := match ciInd with
    | .inductInfo v => .inductInfo { v with toConstantVal := { v.toConstantVal with type := mkConst ``False } }
    | _ => unreachable!
  writeOlean (outDir / "01e_induct") `Proof.Tamper01 {
    d01 with
    constNames := #[`Proof.Tamper01.aForgedInd] ++ d01.constNames
    constants  := #[forgedInd] ++ d01.constants
  }

  -- 02: Duplicate constNames (`subsumesInfo` theorem body swap) + `TrustedBoundary` `replayLocals` overwrite
  let d02 ← readSingleOlean (baseDir / "Proof" / "Tamper02.olean")
  let baseThm02 := d02.constants.find? (·.name == `Proof.Tamper02.sharedThm) |>.get!
  let sorryThm02 : ConstantInfo := match baseThm02 with
    | .thmInfo v => .thmInfo { v with value := mkApp2 (mkConst ``sorryAx [Level.zero]) (mkConst ``True) (mkConst ``Bool.false) }
    | _ => unreachable!
  writeOlean (outDir / "02_dup") `Proof.Tamper02 {
    d02 with
    constNames := #[`Proof.Tamper02.sharedThm, `Proof.Tamper02.sharedThm]
    constants  := #[baseThm02, sorryThm02]
  }

  -- 02b: `replayLocals` overwrite (`constNames = #[forged, helper]`, both `.name == forged`)
  let forgedVerified02 : ConstantInfo := .thmInfo {
    name := `Proof.Tamper02.verifiedClaim
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
    all := [`Proof.Tamper02.verifiedClaim]
  }
  let benignVerified02 : ConstantInfo := .thmInfo {
    name := `Proof.Tamper02.verifiedClaim
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro
    all := [`Proof.Tamper02.verifiedClaim]
  }
  writeOlean (outDir / "02b_overwrite") `Proof.Tamper02 {
    isModule := false
    imports := #[{ module := `Init }]
    constNames := #[`Proof.Tamper02.verifiedClaim, `Proof.Tamper02.helperSlot]
    constants := #[forgedVerified02, benignVerified02]
    extraConstNames := #[]
    entries := #[]
  }

  -- 03: `constNames.size != constants.size` (parallel `for` silent truncation)
  let d03 ← readSingleOlean (baseDir / "Proof" / "Tamper03.olean")
  writeOlean (outDir / "03_size") `Proof.Tamper03 {
    d03 with
    constNames := d03.constNames
    constants  := d03.constants.pop
  }

  -- V06 isolated: theorem using `sorryAx` with `entries := #[]` (empty `exportedAxiomsExt`!)
  let v06SorryThm : ConstantInfo := .thmInfo {
    name := `Proof.V06Isolated.secretSorry
    levelParams := []
    type := mkConst ``True
    value := mkApp2 (mkConst ``sorryAx [Level.zero]) (mkConst ``True) (mkConst ``Bool.false)
    all := [`Proof.V06Isolated.secretSorry]
  }
  writeOlean (outDir / "v06_isolated") `Proof.V06Isolated {
    isModule := false
    imports := #[{ module := `Init }]
    constNames := #[`Proof.V06Isolated.secretSorry]
    constants := #[v06SorryThm]
    extraConstNames := #[]
    entries := #[]
  }

  -- V09 isolated: clean-replay-only ill-typed theorem (`False := True.intro`), 0 axioms, 0 exts, clean source
  let v09IllTyped : ConstantInfo := .thmInfo {
    name := `Proof.V09ReplayOnly.illTypedFalse
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
    all := [`Proof.V09ReplayOnly.illTypedFalse]
  }
  writeOlean (outDir / "v09_replay_only") `Proof.V09ReplayOnly {
    isModule := false
    imports := #[{ module := `Init }]
    constNames := #[`Proof.V09ReplayOnly.illTypedFalse]
    constants := #[v09IllTyped]
    extraConstNames := #[]
    entries := #[]
  }

  -- 18b: Key-aligned inductive with `ci.name ∉ ci.all` (`lowmem_lean` / `B1` bypass #6)
  let fakeAlignedInd : ConstantInfo := .inductInfo {
    name := `Proof.Tamper18Aligned.FakeInd
    levelParams := []
    type := mkConst ``False
    numParams := 0
    numIndices := 0
    all := [`Proof.Tamper01.T]
    ctors := []
    numNested := 0
    isRec := false
    isUnsafe := false
    isReflexive := false
  }
  writeOlean (outDir / "18b_aligned_induct_all") `Proof.Tamper18Aligned {
    isModule := false
    imports := #[{ module := `Init }]
    constNames := d01.constNames.push `Proof.Tamper18Aligned.FakeInd
    constants  := d01.constants.push fakeAlignedInd
    extraConstNames := #[]
    entries := #[]
  }

  -- 18c: Key-aligned foreign `quotInfo` outside `Init`
  let fakeAlignedQuot : ConstantInfo := .quotInfo {
    name := `Proof.Tamper18Quot.fakeQuot
    levelParams := []
    type := mkConst ``False
    kind := .type
  }
  writeOlean (outDir / "18c_foreign_quot") `Proof.Tamper18Quot {
    isModule := false
    imports := #[{ module := `Init }]
    constNames := #[`Proof.Tamper18Quot.fakeQuot]
    constants  := #[fakeAlignedQuot]
    extraConstNames := #[]
    entries := #[]
  }

  -- 13b: Forged `_unsafe_rec` with mismatched type `False` vs safe parent `Nat`
  let safeParent : ConstantInfo := .defnInfo {
    name := `Proof.Tamper13UnsafeRec.safeFn
    levelParams := []
    type := mkConst ``Nat
    value := mkConst ``Nat.zero
    hints := .opaque
    safety := .safe
    all := [`Proof.Tamper13UnsafeRec.safeFn]
  }
  let badUnsafeRecType : ConstantInfo := .defnInfo {
    name := `Proof.Tamper13UnsafeRec.safeFn._unsafe_rec
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
    hints := .opaque
    safety := .partial
    all := [`Proof.Tamper13UnsafeRec.safeFn._unsafe_rec]
  }
  writeOlean (outDir / "13b_forged_unsafe_rec_type") `Proof.Tamper13UnsafeRec {
    isModule := false
    imports := #[{ module := `Init }]
    constNames := #[`Proof.Tamper13UnsafeRec.safeFn, `Proof.Tamper13UnsafeRec.safeFn._unsafe_rec]
    constants  := #[safeParent, badUnsafeRecType]
    extraConstNames := #[]
    entries := #[]
  }

  -- 13c: Forged `_unsafe_rec` matching parent type `Nat` but hiding `sorryAx` in body
  let badUnsafeRecSorry : ConstantInfo := .defnInfo {
    name := `Proof.Tamper13UnsafeRecSorry.safeFn._unsafe_rec
    levelParams := []
    type := mkConst ``Nat
    value := mkApp2 (mkConst ``sorryAx [Level.one]) (mkConst ``Nat) (mkConst ``Bool.false)
    hints := .opaque
    safety := .partial
    all := [`Proof.Tamper13UnsafeRecSorry.safeFn._unsafe_rec]
  }
  let safeParent2 : ConstantInfo := .defnInfo {
    name := `Proof.Tamper13UnsafeRecSorry.safeFn
    levelParams := []
    type := mkConst ``Nat
    value := mkConst ``Nat.zero
    hints := .opaque
    safety := .safe
    all := [`Proof.Tamper13UnsafeRecSorry.safeFn]
  }
  writeOlean (outDir / "13c_forged_unsafe_rec_sorry") `Proof.Tamper13UnsafeRecSorry {
    isModule := false
    imports := #[{ module := `Init }]
    constNames := #[`Proof.Tamper13UnsafeRecSorry.safeFn, `Proof.Tamper13UnsafeRecSorry.safeFn._unsafe_rec]
    constants  := #[safeParent2, badUnsafeRecSorry]
    extraConstNames := #[]
    entries := #[]
  }

  -- B3 referenceOutsideImportClosure: `Specs.UnimportedRef` references `Proof.HelperMod.lem` without importing it
  let helperLem : ConstantInfo := .thmInfo {
    name := `Proof.HelperMod.lem
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro
    all := [`Proof.HelperMod.lem]
  }
  writeOlean (outDir / "b3_ref_outside") `Proof.HelperMod {
    isModule := false
    imports := #[{ module := `Init }]
    constNames := #[`Proof.HelperMod.lem]
    constants  := #[helperLem]
    extraConstNames := #[]
    entries := #[]
  }
  let sneakSpec : ConstantInfo := .thmInfo {
    name := `Specs.UnimportedRef.usesProofWithoutImport
    levelParams := []
    type := mkConst ``True
    value := mkConst `Proof.HelperMod.lem
    all := [`Specs.UnimportedRef.usesProofWithoutImport]
  }
  writeOlean (outDir / "b3_ref_outside") `Specs.UnimportedRef {
    isModule := false
    imports := #[{ module := `Init }]
    constNames := #[`Specs.UnimportedRef.usesProofWithoutImport]
    constants  := #[sneakSpec]
    extraConstNames := #[]
    entries := #[]
  }

  return 0
"""


# ---------------------------------------------------------------------------
# Inspector Compilation & Audit Execution
# ---------------------------------------------------------------------------


def compile_lean_helper_binary(
    lean_bin: Path,
    src_code: str,
    stem_name: str,
    stage_dir: Path,
    *,
    sysroot: Path | None = None,
) -> Path | None:
    """Compiles a Lean helper program into a native executable inside `stage_dir`
    (`lean -R <dir> -c` + `leanc -O0 -rdynamic -Wl,-rpath,<sysroot>/lib/lean -lleanshared`)
    so repeated fresh-process runs take ~0.05s without re-elaborating `OleanReplayInspector.lean`."""
    leanc = lean_bin.parent / "leanc"
    if stat_regular_fail_closed(leanc, allow_symlink=True) is None:
        return None
    eff_sysroot = sysroot if sysroot is not None else lean_bin.parent.parent
    rpath_dir = (eff_sysroot / "lib" / "lean").resolve()
    lean_file = stage_dir / f"{stem_name}.lean"
    c_file = stage_dir / f"{stem_name}.c"
    bin_file = stage_dir / stem_name
    lean_file.write_text(src_code, encoding="utf-8")
    res_c = run_governed_cmd(
        [str(lean_bin), "-R", str(stage_dir), "-c", str(c_file), str(lean_file)],
        cwd=stage_dir,
        mode="file",
    )
    if res_c.returncode != 0 or not c_file.is_file():
        return None
    res_bin = run_governed_cmd(
        [
            str(leanc),
            "-O0",
            "-rdynamic",
            f"-Wl,-rpath,{rpath_dir}",
            "-lleanshared",
            "-o",
            str(bin_file),
            str(c_file),
        ],
        cwd=stage_dir,
        mode="file",
    )
    if res_bin.returncode != 0 or not bin_file.is_file():
        return None
    bin_file.chmod(0o755)
    return bin_file


def load_source_map(
    source_map_arg: Path | None,
    target_modules: Sequence[str],
    *,
    auto_repo_sources: bool = False,
) -> dict[str, Path]:
    """Resolves module -> `.lean` source path mapping with fail-closed stat checks."""
    mapping: dict[str, Path] = {}
    if source_map_arg is not None:
        p = Path(source_map_arg)
        try:
            st = os.lstat(p)
        except OSError as exc:
            raise AuditOperationalError(f"cannot access --source-map {p}: {exc}") from exc
        if stat.S_ISLNK(st.st_mode):
            raise AuditOperationalError(f"disallowed symlink --source-map: {p}")
        if stat.S_ISDIR(st.st_mode):
            stat_dir_fail_closed(p)
            for mod in target_modules:
                cand = p / (mod.replace(".", "/") + ".lean")
                if stat_regular_fail_closed(cand, base_dir=p) is not None:
                    mapping[mod] = cand
        elif stat.S_ISREG(st.st_mode):
            stat_regular_fail_closed(p)
            try:
                raw = json.loads(p.read_text(encoding="utf-8"))
            except (ValueError, OSError) as exc:
                raise AuditOperationalError(f"malformed JSON --source-map {p}: {exc}") from exc
            if not isinstance(raw, dict) or not all(
                isinstance(k, str) and isinstance(v, str) for k, v in raw.items()
            ):
                raise AuditOperationalError(
                    "--source-map JSON must be an object mapping module names to file paths"
                )
            for mod, spath_str in raw.items():
                spath = Path(spath_str)
                if stat_regular_fail_closed(spath) is None:
                    raise AuditPolicyError("missingSourceText", mod, f"missing source {spath}")
                mapping[mod] = spath
        else:
            raise AuditOperationalError(
                f"unsupported --source-map file mode {oct(st.st_mode)}: {p}"
            )
    elif auto_repo_sources:
        repo_roots = [
            REPO_ROOT / "theory",
            REPO_ROOT / "trusted" / "lean",
            REPO_ROOT / "examples",
            REPO_ROOT / "tests",
        ]
        for mod in target_modules:
            rel = mod.replace(".", "/") + ".lean"
            for rdir in repo_roots:
                if rdir.is_dir():
                    cand = rdir / rel
                    if stat_regular_fail_closed(cand, base_dir=rdir) is not None:
                        mapping[mod] = cand
                        break
    return mapping


def precheck_olean_dirs_and_locate_modules(
    target_modules: Sequence[str],
    olean_dirs: Sequence[Path],
    sysroot: Path,
    trusted_olean_root: Path | None,
    *,
    module_mode: bool = False,
) -> list[tuple[str, Path, bool, bool]]:
    """Fail-closed filesystem validation of `--olean-dir` roots and `.olean*` artifacts."""
    std_lib_dir = (sysroot / "lib" / "lean").resolve()
    trusted_resolved = trusted_olean_root.resolve() if trusted_olean_root is not None else None

    validated_dirs: list[Path] = []
    for d in olean_dirs:
        stat_dir_fail_closed(d)
        d_res = d.resolve()
        if d_res != std_lib_dir:
            for reserved_top in ("Init", "Std", "Lean"):
                if probe_entry_exists_fail_closed(d / reserved_top) or probe_entry_exists_fail_closed(
                    d / f"{reserved_top}.olean"
                ):
                    raise AuditPolicyError(
                        "stdlibNamedPackageModule",
                        reserved_top,
                        f"olean search directory {d} shadows {reserved_top}",
                        [reserved_top],
                    )
            if trusted_resolved is None or d_res != trusted_resolved:
                if probe_entry_exists_fail_closed(d / "Trusted") or probe_entry_exists_fail_closed(
                    d / "Trusted.olean"
                ):
                    raise AuditPolicyError(
                        "trustedNamedPackageModule",
                        "Trusted",
                        f"olean search directory {d} shadows Trusted",
                        ["Trusted"],
                    )
        validated_dirs.append(d)

    located: list[tuple[str, Path, bool, bool]] = []
    for mod in target_modules:
        if not mod or any(not seg or "." in seg for seg in mod.split(".")):
            raise AuditPolicyError("anonymousConstantName", mod or "<anonymous>", "malformed module name")
        root = mod.split(".")[0]
        if root in ("Init", "Std", "Lean"):
            raise AuditPolicyError(
                "stdlibNamedPackageModule", mod, f"disallowed package module name {mod}"
            )
        rel_base = mod.replace(".", "/")
        found_olean: Path | None = None
        found_dir: Path | None = None
        for d in validated_dirs:
            cand = d / f"{rel_base}.olean"
            if stat_regular_fail_closed(cand, base_dir=d) is not None:
                found_olean = cand
                found_dir = d
                break
        if found_olean is None or found_dir is None:
            raise AuditPolicyError(
                "missingOleanPart", mod, f"compiled artifact {rel_base}.olean not found"
            )
        srv_cand = found_dir / f"{rel_base}.olean.server"
        prv_cand = found_dir / f"{rel_base}.olean.private"
        has_srv = stat_regular_fail_closed(srv_cand, base_dir=found_dir) is not None
        has_prv = stat_regular_fail_closed(prv_cand, base_dir=found_dir) is not None
        if module_mode and not has_srv:
            raise AuditPolicyError("missingOleanServer", mod, f"missing {srv_cand}")
        if module_mode and not has_prv:
            raise AuditPolicyError("missingOleanPrivate", mod, f"missing {prv_cand}")
        located.append((mod, found_olean, has_srv, has_prv))

    return located


def _prepare_audit_case(
    target_modules: Sequence[str],
    *,
    olean_dirs: Sequence[Path],
    sysroot: Path,
    trusted_root: Path | None,
    strict_proofs: bool = False,
    module_mode: bool = False,
    allow_assumptions: bool = False,
    allow_provisional_native: bool = False,
    allow_local_test_axioms: bool = False,
) -> tuple[dict[str, Any] | None, dict[str, Any] | None]:
    """Runs Python fail-closed prechecks and builds the Lean inspector JSON request."""
    if not target_modules:
        raise AuditOperationalError("no modules specified for audit")
    try:
        located = precheck_olean_dirs_and_locate_modules(
            target_modules,
            olean_dirs,
            sysroot,
            trusted_root,
            module_mode=module_mode,
        )
    except AuditPolicyError as pol:
        return (
            {
                "ok": False,
                "schema_version": SCHEMA_VERSION,
                "toolchain": PINNED_TOOLCHAIN,
                "violations": [pol.to_dict()],
                "summary": {"audited_modules": list(target_modules), "replayed_declarations": 0},
            },
            None,
        )

    search_dirs_str = [str(d.resolve()) for d in olean_dirs]
    if trusted_root is not None and str(trusted_root.resolve()) not in search_dirs_str:
        search_dirs_str.append(str(trusted_root.resolve()))

    req = {
        "sysroot": str(sysroot),
        "trustedOleanRoot": str(trusted_root.resolve()) if trusted_root is not None else "",
        "searchPath": search_dirs_str,
        "targetModules": list(target_modules),
        "oleanFiles": [
            {
                "module": m,
                "path": str(op.resolve()),
                "hasServer": hs,
                "hasPrivate": hp,
            }
            for (m, op, hs, hp) in located
        ],
        "strictProofs": bool(strict_proofs),
        "moduleMode": bool(module_mode),
        "allowAssumptions": bool(allow_assumptions),
        "allowProvisionalNative": bool(allow_provisional_native),
        "allowLocalTestAxioms": bool(allow_local_test_axioms),
    }
    return None, req


def _finalize_audit_case(
    resp: dict[str, Any],
    *,
    target_modules: Sequence[str],
    olean_dirs: Sequence[Path],
    trusted_root: Path | None,
    source_map: Mapping[str, Path] | None = None,
    require_sources: bool = False,
    module_mode: bool = False,
    allow_assumptions: bool = False,
    allow_provisional_native: bool = False,
) -> dict[str, Any]:
    """Validates a single Lean inspector item response, fail-closed transitive `.olean*`
    stats, and defense-in-depth source scanning."""
    if resp.get("ok") is False:
        if resp.get("kind") == "policy":
            v = resp.get("violation", {})
            cat = str(v.get("category", "policyViolation"))
            mod = str(v.get("module", target_modules[0]))
            names = [str(x) for x in v.get("names", [])]
            det = str(v.get("detail", ""))
            return {
                "ok": False,
                "schema_version": SCHEMA_VERSION,
                "toolchain": PINNED_TOOLCHAIN,
                "violations": [
                    {
                        "category": cat,
                        "code": cat,
                        "module": mod,
                        "names": names,
                        "detail": det,
                    }
                ],
                "summary": {"audited_modules": list(target_modules), "replayed_declarations": 0},
            }
        raise AuditOperationalError(
            f"Lean inspector operational failure: {resp.get('message', 'unknown error')}"
        )

    audited_mods: list[str] = list(resp["result"].get("auditedModules", target_modules))

    # Fail-closed stat check on all transitively loaded audited `.olean*` artifacts
    all_artifact_dirs = list(olean_dirs) + ([trusted_root] if trusted_root is not None else [])
    try:
        for mod in audited_mods:
            rel_base = mod.replace(".", "/")
            found_d: Path | None = None
            for d in all_artifact_dirs:
                cand = d / f"{rel_base}.olean"
                if stat_regular_fail_closed(cand, base_dir=d) is not None:
                    found_d = d
                    break
            if found_d is not None:
                has_srv = (
                    stat_regular_fail_closed(found_d / f"{rel_base}.olean.server", base_dir=found_d)
                    is not None
                )
                has_prv = (
                    stat_regular_fail_closed(found_d / f"{rel_base}.olean.private", base_dir=found_d)
                    is not None
                )
                if module_mode and not has_srv:
                    raise AuditPolicyError("missingOleanServer", mod, f"missing {rel_base}.olean.server")
                if module_mode and not has_prv:
                    raise AuditPolicyError("missingOleanPrivate", mod, f"missing {rel_base}.olean.private")
    except AuditPolicyError as pol:
        return {
            "ok": False,
            "schema_version": SCHEMA_VERSION,
            "toolchain": PINNED_TOOLCHAIN,
            "violations": [pol.to_dict()],
            "summary": {"audited_modules": audited_mods, "replayed_declarations": 0},
        }

    # Defense-in-depth source scan on supplied / required sources
    eff_sources = dict(source_map or {})
    check_src_mods = list(target_modules) if not require_sources else audited_mods
    try:
        for mod in check_src_mods:
            if mod in eff_sources:
                src_path = eff_sources[mod]
                if stat_regular_fail_closed(src_path) is None:
                    raise AuditPolicyError("missingSourceText", mod, f"missing source {src_path}")
                text = src_path.read_text(encoding="utf-8")
                scan_source_defense_in_depth(
                    mod,
                    text,
                    allow_provisional_native=allow_provisional_native,
                    allow_assumptions=allow_assumptions,
                    allow_module_header=True,
                )
            elif require_sources:
                raise AuditPolicyError(
                    "missingSourceText", mod, f"no source supplied for audited module {mod}"
                )
    except AuditPolicyError as pol:
        return {
            "ok": False,
            "schema_version": SCHEMA_VERSION,
            "toolchain": PINNED_TOOLCHAIN,
            "violations": [pol.to_dict()],
            "summary": {"audited_modules": audited_mods, "replayed_declarations": 0},
        }

    res = resp["result"]
    return {
        "ok": True,
        "schema_version": SCHEMA_VERSION,
        "toolchain": PINNED_TOOLCHAIN,
        "violations": [],
        "summary": {
            "audited_modules": res.get("auditedModules", []),
            "replayed_declarations": res.get("replayedDeclarations", 0),
            "reached_axioms": res.get("reachedAxioms", []),
            "items": res.get("items", []),
            "replay": res.get("replay", True),
        },
    }


def audit_modules(
    target_modules: Sequence[str],
    *,
    olean_dirs: Sequence[Path],
    source_map: Mapping[str, Path] | None = None,
    require_sources: bool = False,
    strict_proofs: bool = False,
    module_mode: bool = False,
    allow_assumptions: bool = False,
    allow_provisional_native: bool = False,
    allow_local_test_axioms: bool = False,
    lean_bin: Path | None = None,
    sysroot: Path | None = None,
    compiled_inspector: Path | None = None,
    stage_dir: Path | None = None,
    include_repo_trusted_root: bool = True,
) -> dict[str, Any]:
    """Runs the complete `.olean` + source defense-in-depth + kernel replay audit."""
    if lean_bin is None or sysroot is None:
        lean_bin, sysroot = resolve_lean_toolchain(lean_bin)

    repo_olean_root = REPO_ROOT / ".lake" / "build" / "lib" / "lean"
    trusted_root: Path | None = (
        repo_olean_root if (include_repo_trusted_root and repo_olean_root.is_dir()) else None
    )

    early_report, req = _prepare_audit_case(
        target_modules,
        olean_dirs=olean_dirs,
        sysroot=sysroot,
        trusted_root=trusted_root,
        strict_proofs=strict_proofs,
        module_mode=module_mode,
        allow_assumptions=allow_assumptions,
        allow_provisional_native=allow_provisional_native,
        allow_local_test_axioms=allow_local_test_axioms,
    )
    if early_report is not None or req is None:
        return early_report  # type: ignore[return-value]

    def _run_in_stage(work_dir: Path) -> dict[str, Any]:
        req_path = work_dir / "audit_request.json"
        resp_path = work_dir / "audit_response.json"
        req_path.write_text(json.dumps(req, sort_keys=True), encoding="utf-8")

        if compiled_inspector is not None and compiled_inspector.is_file():
            proc = run_governed_cmd(
                [str(compiled_inspector), str(req_path), str(resp_path)],
                cwd=work_dir,
                mode="file",
            )
        else:
            insp_lean = work_dir / "OleanReplayInspector.lean"
            insp_lean.write_text(INSPECTOR_LEAN_SOURCE, encoding="utf-8")
            proc = run_governed_cmd(
                [str(lean_bin), "--run", str(insp_lean), str(req_path), str(resp_path)],
                cwd=work_dir,
                mode="file",
            )

        if not resp_path.is_file():
            raise AuditOperationalError(
                f"Lean inspector exited {proc.returncode} without writing response: "
                f"{proc.stderr.strip() or proc.stdout.strip()}"
            )
        try:
            resp = json.loads(resp_path.read_text(encoding="utf-8"))
        except (ValueError, OSError) as exc:
            raise AuditOperationalError(f"malformed inspector JSON output: {exc}") from exc

        if resp.get("ok") is True and proc.returncode != 0:
            raise AuditOperationalError(
                f"Lean inspector exited {proc.returncode}: {proc.stderr.strip()}"
            )

        return _finalize_audit_case(
            resp,
            target_modules=target_modules,
            olean_dirs=olean_dirs,
            trusted_root=trusted_root,
            source_map=source_map,
            require_sources=require_sources,
            module_mode=module_mode,
            allow_assumptions=allow_assumptions,
            allow_provisional_native=allow_provisional_native,
        )

    if stage_dir is not None:
        with tempfile.TemporaryDirectory(prefix="audit-req-", dir=stage_dir) as sub_td:
            return _run_in_stage(Path(sub_td))
    with tempfile.TemporaryDirectory(prefix="anneal-olean-audit-") as td:
        return _run_in_stage(Path(td))


def batch_audit_modules(
    cases: Sequence[dict[str, Any]],
    *,
    lean_bin: Path,
    sysroot: Path,
    stage_dir: Path,
    compiled_inspector: Path | None = None,
    chunk_size: int = 5,
    include_repo_trusted_root: bool = True,
) -> list[dict[str, Any]]:
    """Executes multiple independent module audits in bounded-memory chunks (`chunk_size`
    items per process so `.olean` `CompactedRegion` mappings are reclaimed by the OS well
    below the `anneal-lean-run` cgroup `MemoryMax` ceiling) while running identical
    fail-closed Python prechecks and postchecks per case."""
    repo_olean_root = REPO_ROOT / ".lake" / "build" / "lib" / "lean"
    trusted_root: Path | None = (
        repo_olean_root if (include_repo_trusted_root and repo_olean_root.is_dir()) else None
    )

    reports_by_idx: list[dict[str, Any] | None] = [None] * len(cases)
    batch_indices: list[int] = []
    batch_reqs: list[dict[str, Any]] = []

    for idx, c in enumerate(cases):
        early_rep, req = _prepare_audit_case(
            c["target_modules"],
            olean_dirs=c["olean_dirs"],
            sysroot=sysroot,
            trusted_root=trusted_root,
            strict_proofs=bool(c.get("strict_proofs", False)),
            module_mode=bool(c.get("module_mode", False)),
            allow_assumptions=bool(c.get("allow_assumptions", False)),
            allow_provisional_native=bool(c.get("allow_provisional_native", False)),
            allow_local_test_axioms=bool(c.get("allow_local_test_axioms", False)),
        )
        if early_rep is not None or req is None:
            reports_by_idx[idx] = early_rep
        else:
            batch_indices.append(idx)
            batch_reqs.append(req)

    eff_chunk = max(1, chunk_size)
    for start in range(0, len(batch_reqs), eff_chunk):
        chunk_reqs = batch_reqs[start : start + eff_chunk]
        chunk_idxs = batch_indices[start : start + eff_chunk]
        with tempfile.TemporaryDirectory(prefix="audit-batch-", dir=stage_dir) as sub_td:
            work_dir = Path(sub_td)
            req_path = work_dir / "batch_request.json"
            resp_path = work_dir / "batch_response.json"
            req_path.write_text(
                json.dumps({"sysroot": str(sysroot), "items": chunk_reqs}, sort_keys=True),
                encoding="utf-8",
            )
            if compiled_inspector is not None and compiled_inspector.is_file():
                proc = run_governed_cmd(
                    [str(compiled_inspector), "--batch", str(req_path), str(resp_path)],
                    cwd=work_dir,
                    mode="file",
                )
            else:
                insp_lean = work_dir / "OleanReplayInspector.lean"
                insp_lean.write_text(INSPECTOR_LEAN_SOURCE, encoding="utf-8")
                proc = run_governed_cmd(
                    [str(lean_bin), "--run", str(insp_lean), "--batch", str(req_path), str(resp_path)],
                    cwd=work_dir,
                    mode="file",
                )
            if proc.returncode != 0 or not resp_path.is_file():
                raise AuditOperationalError(
                    f"Lean batch inspector failed (exit {proc.returncode}): "
                    f"{proc.stderr.strip() or proc.stdout.strip()}"
                )
            try:
                batch_resp = json.loads(resp_path.read_text(encoding="utf-8"))
            except (ValueError, OSError) as exc:
                raise AuditOperationalError(f"malformed batch inspector JSON: {exc}") from exc
            out_items = batch_resp.get("items", [])
            if not isinstance(out_items, list) or len(out_items) != len(chunk_idxs):
                raise AuditOperationalError(
                    f"batch response item count mismatch: expected {len(chunk_idxs)}, got {len(out_items)}"
                )
            for b_pos, case_idx in enumerate(chunk_idxs):
                c = cases[case_idx]
                reports_by_idx[case_idx] = _finalize_audit_case(
                    out_items[b_pos],
                    target_modules=c["target_modules"],
                    olean_dirs=c["olean_dirs"],
                    trusted_root=trusted_root,
                    source_map=c.get("source_map"),
                    require_sources=bool(c.get("require_sources", False)),
                    module_mode=bool(c.get("module_mode", False)),
                    allow_assumptions=bool(c.get("allow_assumptions", False)),
                    allow_provisional_native=bool(c.get("allow_provisional_native", False)),
                )

    return [r for r in reports_by_idx if r is not None]


# ---------------------------------------------------------------------------
# `--emit-patch-spec` (`PROTOTYPE_REPORT.md` §4 Patches 1–12)
# ---------------------------------------------------------------------------


def build_trusted_boundary_patch_spec() -> dict[str, Any]:
    """Structured ready-to-apply specification for `trusted/audit/TrustedBoundary.lean`
    once the `ws-main-prep-fuchsia-phase-b` human main-prep freeze clears."""
    patches = [
        {
            "id": "Patch-01",
            "target_file": "trusted/audit/TrustedBoundary.lean",
            "target_symbols": ["isCompilerTrustAxiom", "isNativeDecideAxiom", "verifyAudit"],
            "lines": "95-97, 602-604, 659-662, 722-724",
            "summary": (
                "Split `isCompilerTrustAxiom` (`Lean.trustCompiler`, unconditionally banned even "
                "under `--provisional`) from `isNativeDecideAxiom`, scope provisional `._native.*` "
                "axioms strictly to `Proof.*` modules, and verify `@Eq Bool e Bool.true` closed shape."
            ),
        },
        {
            "id": "Patch-02",
            "target_file": "trusted/audit/TrustedBoundary.lean",
            "target_symbols": ["isCodegenUnsafeRec"],
            "lines": "255-260",
            "summary": (
                "Require `.defnInfo` kind on both `parent._unsafe_rec` and `parent`, require "
                "`ci.type == parentCi.type`, and audit `declarationEdges` of `_unsafe_rec` companions "
                "against `sorryAx`, `Lean.trustCompiler`, `unsafe`, and unknown constants."
            ),
        },
        {
            "id": "Patch-03",
            "target_file": "trusted/audit/TrustedBoundary.lean",
            "target_symbols": [
                "verifyModuleInventory",
                "verifyMutualAll",
                "rejectForeignQuot",
                "verifyCheckedEnvKeys",
                "sameStoredDecl",
                "insertReplayLocalUnique",
            ],
            "lines": "insert before 308",
            "summary": (
                "Enforce `constNames.size == constants.size`, well-formed non-anonymous names, "
                "`constNames[i] == constants[i].name` (`lean4#16677`), duplicate rejection, "
                "`lowmem_lean` mutual `.all` & `.recInfo` target/rule completeness, foreign `quotInfo` "
                "ban, `env.checked.get.constants` (`SMap.map₁`/`map₂`) key verification, and "
                "collision-refusing `insertReplayLocalUnique` with full structural `sameStoredDecl`."
            ),
        },
        {
            "id": "Patch-04",
            "target_file": "trusted/audit/TrustedBoundary.lean",
            "target_symbols": ["audit"],
            "lines": "318-360",
            "summary": (
                "Wire `verifyModuleInventory`, `insertReplayLocalUnique`, and `verifyCheckedEnvKeys` "
                "into `TrustedBoundary.audit`."
            ),
        },
        {
            "id": "Patch-05",
            "target_file": "trusted/audit/TrustedBoundary.lean",
            "target_symbols": ["downstreamAudit"],
            "lines": "394-452",
            "summary": (
                "Wire `verifyModuleInventory`, `insertReplayLocalUnique`, and `verifyCheckedEnvKeys` "
                "into `downstreamAudit`; pass `claimModules ++ examples` to `checkStatementOrigins`; "
                "replay non-axiom `testModules` declarations; reject `isNativeDecideAxiom` before `isSameFile`."
            ),
        },
        {
            "id": "Patch-06",
            "target_file": "trusted/audit/TrustedBoundary.lean",
            "target_symbols": ["verifyAudit"],
            "lines": "558, 583-734",
            "summary": (
                "Wire `verifyModuleInventory`, `insertReplayLocalUnique` (closing the `Verify.Foo.verified` "
                "overwrite exploit), `verifyCheckedEnvKeys`, and `.olean.{server,private}` presence checks "
                "into `verifyAudit`."
            ),
        },
        {
            "id": "Patch-07",
            "target_file": "trusted/audit/TrustedBoundary.lean",
            "target_symbols": ["closure", "checkStatementOrigins", "checkInventoryOrigin"],
            "lines": "240-306",
            "summary": (
                "Preserve unbounded worklist completeness in `closure` and `checkStatementOrigins` "
                "and upgrade `checkInventoryOrigin` to compare full `sameStoredDecl`."
            ),
        },
        {
            "id": "Patch-08",
            "target_file": "trusted/audit/TrustedBoundary.lean",
            "target_symbols": ["verifyStdlibProvenance", "isStdlibMod"],
            "lines": "30-32, 536, 563-592, 792",
            "summary": (
                "Verify every `Init.*`/`Std.*` `.olean` resolves inside `<sysroot>/lib/lean`, reject "
                "any workspace search-path root shadowing `Init`/`Std`/`Lean`/`Trusted`, and pin "
                "`Trusted.*`/`Anneal.*` `baseMods` provenance."
            ),
        },
        {
            "id": "Patch-09",
            "target_file": "trusted/audit/TrustedBoundary.lean",
            "target_symbols": ["inspectSyntax", "syntaxKindWithin"],
            "lines": "102-133",
            "summary": (
                "Reject `Lean.Parser.Tactic.{bvDecide,bvTrace,bvCheck}`, "
                "`Lean.Parser.Tactic.Grind.{bvDecide,bvTrace,bvCheck}`, and positional/opaque "
                "`Lean.Parser.Tactic.valConfigItem` inside `decide` unless `--provisional` on `Proof.*`."
            ),
        },
        {
            "id": "Patch-10",
            "target_file": "trusted/audit/TrustedBoundary.lean",
            "target_symbols": ["verifyAudit", "cleanNonWorkspace"],
            "lines": "609, 644-670, 731",
            "summary": (
                "Only merge `visitedNonWorkspace` into `cleanNonWorkspace` when "
                "`reachedProvisional.isEmpty && reachedAssumptions.isEmpty` so conditional/provisional "
                "non-workspace helpers never poison subsequent verify items."
            ),
        },
        {
            "id": "Patch-11",
            "target_file": "trusted/audit/TrustedBoundary.lean",
            "target_symbols": ["verifyAudit"],
            "lines": "543-557, 583-592",
            "summary": (
                "Require every transitively loaded `Verify.*`/`CrateVerify*` module to be listed in "
                "`allAuditModules` and require source coverage for every loaded workspace module."
            ),
        },
        {
            "id": "Patch-12",
            "target_file": "trusted/audit/TrustedBoundary.lean",
            "target_symbols": ["commandKinds", "allowedAttributeNames", "verifyAudit"],
            "lines": "63-93, 674-731",
            "summary": (
                "Combine `inspectSource` with `.olean` persistent-extension auditing (`export`, "
                "`notation`, `mixfix`, `coe`, `default_instance`, foreign `reducible`, orphan `instance`) "
                "and report combined `ProvisionalNativeConditional` / `UbException` / `CrateVerify` item statuses."
            ),
        },
    ]
    return {
        "ok": True,
        "schema_version": SCHEMA_VERSION,
        "target_file": "trusted/audit/TrustedBoundary.lean",
        "freeze_workstream": "ws-main-prep-fuchsia-phase-b",
        "toolchain": PINNED_TOOLCHAIN,
        "patch_count": len(patches),
        "patches": patches,
    }


# ---------------------------------------------------------------------------
# `--run-tamper-suite` (`00_clean_positive` + `18` Canonical Fixtures + Sub-Checks)
# ---------------------------------------------------------------------------


def load_fixture_manifest(fixtures_dir: Path = FIXTURES_DIR) -> dict[str, Any]:
    manifest_path = fixtures_dir / "manifest.json"
    if stat_regular_fail_closed(manifest_path, base_dir=fixtures_dir) is None:
        raise AuditOperationalError(f"missing fixture manifest: {manifest_path}")
    try:
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (ValueError, OSError) as exc:
        raise AuditOperationalError(f"malformed fixture manifest {manifest_path}: {exc}") from exc
    if not isinstance(data, dict):
        raise AuditOperationalError("fixture manifest must be a JSON object")
    return data


_BATCH_COMPILE_DRIVER = """import json, os, subprocess, sys
jobs = json.loads(open(sys.argv[1], encoding="utf-8").read())
for job in jobs:
    os.makedirs(os.path.dirname(job["out"]), exist_ok=True)
    env = dict(os.environ)
    if job["lean_path"]:
        env["LEAN_PATH"] = job["lean_path"]
    else:
        env.pop("LEAN_PATH", None)
    r = subprocess.run(
        [job["lean"], "-R", job["root"], "-o", job["out"], job["src"]],
        cwd=job["root"],
        env=env,
        stdin=subprocess.DEVNULL,
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        sys.stderr.write(f"compile failed ({job['src']}):\\n{r.stdout}\\n{r.stderr}\\n")
        sys.exit(r.returncode)
"""


def _compile_lean_jobs(
    lean_bin: Path,
    stage_dir: Path,
    jobs: Sequence[tuple[Path, Path, Path, Sequence[Path]]],
) -> None:
    """Compiles a sequence of `(root_dir, src_file, out_olean, lean_path_dirs)` fixtures
    strictly sequentially inside a single governed `anneal-lean-run` invocation."""
    if not jobs:
        return
    driver_py = stage_dir / "_compile_fixtures_seq.py"
    jobs_json = stage_dir / "_compile_fixtures_jobs.json"
    driver_py.write_text(_BATCH_COMPILE_DRIVER, encoding="utf-8")
    payload = [
        {
            "lean": str(lean_bin),
            "root": str(rdir),
            "src": str(src),
            "out": str(out),
            "lean_path": os.pathsep.join(str(p) for p in lp_dirs),
        }
        for (rdir, src, out, lp_dirs) in jobs
    ]
    jobs_json.write_text(json.dumps(payload), encoding="utf-8")
    res = run_governed_cmd(
        [sys.executable, "-B", str(driver_py), str(jobs_json)],
        cwd=stage_dir,
        mode="file",
        timeout_sec=CHILD_TIMEOUT_SEC,
    )
    if res.returncode != 0:
        raise AuditOperationalError(
            f"failed compiling fixture batch (exit {res.returncode}):\n"
            f"{res.stdout}\n{res.stderr}"
        )


def run_tamper_suite(
    *,
    lean_bin: Path | None = None,
    fixtures_dir: Path = FIXTURES_DIR,
) -> dict[str, Any]:
    """Compiles and audits `00_clean_positive` (+ 4-module package) + all `18` canonical
    negative fixtures + structural isolation sub-checks (`V06`, `V09`, `V17`, `V18`,
    `01b..01e`, `02b`, `13b..13c`, `18b..18c`, `B3` unimported reference, `Std` shadow,
    and live `Anneal.ReplayKeyAndTamperAudit`) strictly inside `tempfile.TemporaryDirectory()`."""
    t0 = time.monotonic()
    stat_dir_fail_closed(fixtures_dir)
    manifest = load_fixture_manifest(fixtures_dir)
    lean_bin, sysroot = resolve_lean_toolchain(lean_bin)

    pos_specs = manifest.get("positive_fixtures", [])
    neg_specs = manifest.get("negative_fixtures", [])
    if len(pos_specs) != 1 or len(neg_specs) != 18:
        raise AuditOperationalError(
            f"expected 1 positive + 18 negative fixtures in manifest, got {len(pos_specs)} + {len(neg_specs)}"
        )

    with tempfile.TemporaryDirectory(prefix="anneal-tamper-suite-") as tmp_str:
        tmp = Path(tmp_str)
        bin_stage = tmp / "bin_stage"
        bin_stage.mkdir(parents=True, exist_ok=True)
        t_p0 = time.monotonic()
        compiled_insp = compile_lean_helper_binary(
            lean_bin, INSPECTOR_LEAN_SOURCE, "OleanReplayInspector", bin_stage, sysroot=sysroot
        )
        t_compile_insp = round(time.monotonic() - t_p0, 3)

        # Stage standalone, `15_import_all_leak`, and `00_clean_positive_pkg` `.lean` fixtures
        compiled_base = tmp / "compiled_base"
        src_stage = tmp / "src_stage"
        compile_jobs: list[tuple[Path, Path, Path, Sequence[Path]]] = []
        for entry in [*pos_specs, *neg_specs]:
            fname = entry["file"]
            mod = entry["module"]
            fpath = fixtures_dir / fname
            if stat_regular_fail_closed(fpath, base_dir=fixtures_dir) is None:
                raise AuditOperationalError(f"missing fixture source file: {fpath}")
            if entry["mode"] == "compile_module_pkg":
                continue
            rel = mod.replace(".", "/")
            staged_src = src_stage / f"{rel}.lean"
            staged_src.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(fpath, staged_src)
            out_olean = compiled_base / f"{rel}.olean"
            compile_jobs.append((src_stage, staged_src, out_olean, ()))

        pkg15_dir = tmp / "pkg15"
        shutil.copytree(fixtures_dir / "15_import_all_pkg", pkg15_dir)
        (pkg15_dir / "Proof").mkdir(parents=True, exist_ok=True)
        shutil.copyfile(fixtures_dir / "15_import_all_leak.lean", pkg15_dir / "Proof" / "Tamper15.lean")
        for rel in ("Topic/Defs", "Proof/Tamper15"):
            compile_jobs.append(
                (pkg15_dir, pkg15_dir / f"{rel}.lean", pkg15_dir / f"{rel}.olean", [pkg15_dir])
            )

        pkg00_dir = tmp / "pkg00"
        shutil.copytree(fixtures_dir / "00_clean_positive_pkg", pkg00_dir)
        repo_olean = REPO_ROOT / ".lake" / "build" / "lib" / "lean"
        pkg00_deps = [pkg00_dir] + ([repo_olean] if repo_olean.is_dir() else [])
        for rel in ("Topic/Defs", "Anneal/TheoryHelper", "Topic/Proofs", "Verify/Topic"):
            compile_jobs.append(
                (pkg00_dir, pkg00_dir / f"{rel}.lean", pkg00_dir / f"{rel}.olean", pkg00_deps)
            )

        t_p1 = time.monotonic()
        _compile_lean_jobs(lean_bin, tmp, compile_jobs)
        t_compile_fx = round(time.monotonic() - t_p1, 3)

        # Generate all binary-tampered `.olean` files on disk via `Lean.saveModuleData` in one shot!
        t_p2 = time.monotonic()
        forged_root = tmp / "forged"
        forge_script = tmp / "TamperForge.lean"
        forge_script.write_text(FORGE_LEAN_SOURCE, encoding="utf-8")
        forge_res = run_governed_cmd(
            [str(lean_bin), "--run", str(forge_script), str(compiled_base), str(forged_root)],
            cwd=tmp,
            mode="file",
        )
        t_forge = round(time.monotonic() - t_p2, 3)
        if forge_res.returncode != 0:
            raise AuditOperationalError(
                f"TamperForge failed generating forged .olean fixtures:\n"
                f"{forge_res.stdout}\n{forge_res.stderr}"
            )

        results: list[dict[str, Any]] = []
        failures: list[str] = []

        def _record_case(
            case_id: str,
            report: dict[str, Any],
            *,
            expected_ok: bool,
            expected_category: str | None,
            canonical: bool,
        ) -> None:
            actual_ok = bool(report.get("ok"))
            violations = report.get("violations", [])
            actual_cat = violations[0]["category"] if violations else None
            matched = (actual_ok == expected_ok) and (
                (expected_category is None and actual_cat is None)
                or (actual_cat == expected_category)
            )
            results.append(
                {
                    "id": case_id,
                    "canonical": canonical,
                    "expected_ok": expected_ok,
                    "actual_ok": actual_ok,
                    "expected_category": expected_category,
                    "actual_category": actual_cat,
                    "passed": matched,
                }
            )
            if not matched:
                failures.append(
                    f"{case_id}: expected ok={expected_ok} category={expected_category}, "
                    f"got ok={actual_ok} category={actual_cat} violations={violations}"
                )

        # Collect `00_clean_positive` + all `18` canonical negative fixtures + all structural/isolation
        # sub-checks and execute them in bounded `--batch` chunks (plus single-item live `ReplayKeyAndTamperAudit`).
        batched_specs: list[tuple[str, bool, str | None, bool, dict[str, Any]]] = []
        pos0 = pos_specs[0]
        pos0_src = src_stage / (pos0["module"].replace(".", "/") + ".lean")
        batched_specs.append(
            (
                pos0["id"],
                True,
                None,
                True,
                {
                    "target_modules": [pos0["module"]],
                    "olean_dirs": [compiled_base],
                    "source_map": {pos0["module"]: pos0_src},
                    "require_sources": True,
                    "strict_proofs": True,
                },
            )
        )

        forge_dir_by_mode = {
            "forge_recursor_key_mismatch": forged_root / "01_rec",
            "forge_duplicate_const_names": forged_root / "02_dup",
            "forge_const_names_size_mismatch": forged_root / "03_size",
        }
        for entry in neg_specs:
            fid = entry["id"]
            mod = entry["module"]
            mode = entry["mode"]
            exp_cat = entry["expected_category"]
            if mode in forge_dir_by_mode:
                odirs = [forge_dir_by_mode[mode]]
                smap = {mod: src_stage / (mod.replace(".", "/") + ".lean")}
                mod_mode = False
            elif mode == "compile_module_pkg":
                odirs = [pkg15_dir]
                smap = {
                    "Topic.Defs": pkg15_dir / "Topic" / "Defs.lean",
                    "Proof.Tamper15": pkg15_dir / "Proof" / "Tamper15.lean",
                }
                mod_mode = True
            else:
                odirs = [compiled_base]
                smap = {mod: src_stage / (mod.replace(".", "/") + ".lean")}
                mod_mode = False

            batched_specs.append(
                (
                    fid,
                    False,
                    exp_cat,
                    True,
                    {
                        "target_modules": [mod],
                        "olean_dirs": odirs,
                        "source_map": smap,
                        "require_sources": True,
                        "strict_proofs": bool(entry.get("strict_proofs", True)),
                        "module_mode": mod_mode,
                    },
                )
            )

        # 3. Structural & isolation sub-checks (`00_clean_positive_pkg`, `01b..01e`, `02b`,
        #    `V06`, `V09`, `13b..13c`, `V17`, `V18`, `18b..18c`, `B3` reference outside import closure,
        #    `Std` search-path shadow, `04`/`05` provisional behavior, live `Anneal.ReplayKeyAndTamperAudit`)
        pkg00_smap = {
            "Topic.Defs": pkg00_dir / "Topic" / "Defs.lean",
            "Anneal.TheoryHelper": pkg00_dir / "Anneal" / "TheoryHelper.lean",
            "Topic.Proofs": pkg00_dir / "Topic" / "Proofs.lean",
            "Verify.Topic": pkg00_dir / "Verify" / "Topic.lean",
        }
        batched_specs.append(
            (
                "subcheck_00_clean_4mod_package",
                True,
                None,
                False,
                {
                    "target_modules": ["Verify.Topic"],
                    "olean_dirs": [pkg00_dir],
                    "source_map": pkg00_smap,
                    "require_sources": True,
                    "strict_proofs": True,
                },
            )
        )

        clean_v09_src = tmp / "V09Clean.lean"
        clean_v09_src.write_text(
            "namespace Proof.V09ReplayOnly\ntheorem illTypedFalse : True := True.intro\nend Proof.V09ReplayOnly\n",
            encoding="utf-8",
        )
        sub_forged_cases = [
            ("subcheck_01b_ctor_key_mismatch", "Proof.Tamper01", forged_root / "01b_ctor", "keyNameMismatch"),
            ("subcheck_01c_quot_key_mismatch", "Proof.Tamper01", forged_root / "01c_quot", "keyNameMismatch"),
            ("subcheck_01d_thm_dup_key_mismatch", "Proof.Tamper01", forged_root / "01d_thm_dup", "keyNameMismatch"),
            ("subcheck_01e_induct_key_mismatch", "Proof.Tamper01", forged_root / "01e_induct", "keyNameMismatch"),
            ("subcheck_02b_replay_locals_overwrite", "Proof.Tamper02", forged_root / "02b_overwrite", "keyNameMismatch"),
            ("subcheck_V06_isolated_empty_exported_axioms", "Proof.V06Isolated", forged_root / "v06_isolated", "forbiddenAxiom"),
            ("subcheck_V09_isolated_clean_replay_only", "Proof.V09ReplayOnly", forged_root / "v09_replay_only", "kernelTypeError"),
            ("subcheck_13b_forged_unsafe_rec_type", "Proof.Tamper13UnsafeRec", forged_root / "13b_forged_unsafe_rec_type", "unsafeOrPartialDecl"),
            ("subcheck_13c_forged_unsafe_rec_sorry", "Proof.Tamper13UnsafeRecSorry", forged_root / "13c_forged_unsafe_rec_sorry", "forbiddenAxiom"),
            ("subcheck_18b_key_aligned_induct_all", "Proof.Tamper18Aligned", forged_root / "18b_aligned_induct_all", "invalidMutualAll"),
            ("subcheck_18c_foreign_quot_decl", "Proof.Tamper18Quot", forged_root / "18c_foreign_quot", "foreignQuotDecl"),
            ("subcheck_B3_reference_outside_import_closure", "Specs.UnimportedRef", forged_root / "b3_ref_outside", "referenceOutsideImportClosure"),
        ]
        for sub_id, sub_mod, sub_dir, sub_cat in sub_forged_cases:
            sub_smap = (
                {sub_mod: clean_v09_src}
                if sub_id == "subcheck_V09_isolated_clean_replay_only"
                else {}
            )
            target_mods_sub = (
                [sub_mod, "Proof.HelperMod"]
                if sub_id == "subcheck_B3_reference_outside_import_closure"
                else [sub_mod]
            )
            batched_specs.append(
                (
                    sub_id,
                    False,
                    sub_cat,
                    False,
                    {
                        "target_modules": target_mods_sub,
                        "olean_dirs": [sub_dir]
                        + ([compiled_base] if sub_id == "subcheck_18b_key_aligned_induct_all" else []),
                        "source_map": sub_smap,
                        "require_sources": bool(sub_smap),
                        "strict_proofs": True,
                    },
                )
            )

        # V17 & V18: missing `.olean.server` and missing `.olean.private` in `--module-mode`
        for v_id, missing_ext, v_cat in (
            ("subcheck_V17_missing_olean_server", ".server", "missingOleanServer"),
            ("subcheck_V18_missing_olean_private", ".private", "missingOleanPrivate"),
        ):
            v_dir = tmp / v_id
            shutil.copytree(pkg15_dir, v_dir)
            os.remove(v_dir / "Topic" / f"Defs.olean{missing_ext}")
            batched_specs.append(
                (
                    v_id,
                    False,
                    v_cat,
                    False,
                    {
                        "target_modules": ["Topic.Defs"],
                        "olean_dirs": [v_dir],
                        "module_mode": True,
                        "strict_proofs": True,
                    },
                )
            )

        # Std search-path shadowing (`B2` / Patch 8)
        std_shadow_dir = tmp / "std_shadow"
        (std_shadow_dir / "Std").mkdir(parents=True, exist_ok=True)
        shutil.copyfile(
            compiled_base / "Proof" / "CleanPositive.olean",
            std_shadow_dir / "Proof_Clean.olean",
        )
        batched_specs.append(
            (
                "subcheck_B2_stdlib_search_path_shadow",
                False,
                "stdlibNamedPackageModule",
                False,
                {
                    "target_modules": ["Proof.CleanPositive"],
                    "olean_dirs": [std_shadow_dir, compiled_base],
                    "strict_proofs": True,
                },
            )
        )

        # `04` under `--allow-provisional-native` must STILL be rejected (`Lean.ofReduceNat` is Init-only deprecated!)
        batched_specs.append(
            (
                "subcheck_04_ofReduceNat_still_banned_under_provisional",
                False,
                "forbiddenNativeReductionAxiom",
                False,
                {
                    "target_modules": ["Proof.Tamper04"],
                    "olean_dirs": [compiled_base],
                    "allow_provisional_native": True,
                    "strict_proofs": True,
                },
            )
        )

        # `05` (`by native_decide` in `Proof.Tamper05`) IS admitted under `--allow-provisional-native` and recorded!
        batched_specs.append(
            (
                "subcheck_05_provisional_native_admitted_in_proof",
                True,
                None,
                False,
                {
                    "target_modules": ["Proof.Tamper05"],
                    "olean_dirs": [compiled_base],
                    "source_map": {"Proof.Tamper05": src_stage / "Proof" / "Tamper05.lean"},
                    "require_sources": True,
                    "allow_provisional_native": True,
                    "strict_proofs": True,
                },
            )
        )

        batch_reports = batch_audit_modules(
            [spec_cfg for (_, _, _, _, spec_cfg) in batched_specs],
            lean_bin=lean_bin,
            sysroot=sysroot,
            stage_dir=tmp,
            compiled_inspector=compiled_insp,
            chunk_size=10,
        )
        for (cid, exp_ok, exp_cat, is_canon, _), rep in zip(batched_specs, batch_reports):
            _record_case(cid, rep, expected_ok=exp_ok, expected_category=exp_cat, canonical=is_canon)

        # Live audit of compiled `Anneal.ReplayKeyAndTamperAudit` in its own bounded process
        if (repo_olean / "Anneal" / "ReplayKeyAndTamperAudit.olean").is_file():
            rep_live = audit_modules(
                ["Anneal.ReplayKeyAndTamperAudit"],
                olean_dirs=[repo_olean],
                source_map={
                    "Anneal.ReplayKeyAndTamperAudit": REPO_ROOT
                    / "theory"
                    / "Anneal"
                    / "ReplayKeyAndTamperAudit.lean"
                },
                require_sources=True,
                strict_proofs=False,
                lean_bin=lean_bin,
                sysroot=sysroot,
                compiled_inspector=compiled_insp,
                stage_dir=tmp,
            )
            _record_case(
                "subcheck_live_Anneal_ReplayKeyAndTamperAudit",
                rep_live,
                expected_ok=True,
                expected_category=None,
                canonical=False,
            )

    elapsed = round(time.monotonic() - t0, 3)
    canonical_neg = [r for r in results if r["canonical"] and not r["expected_ok"]]
    canonical_pos = [r for r in results if r["canonical"] and r["expected_ok"]]
    neg_passed = sum(1 for r in canonical_neg if r["passed"])
    pos_passed = sum(1 for r in canonical_pos if r["passed"])
    sub_results = [r for r in results if not r["canonical"]]
    sub_passed = sum(1 for r in sub_results if r["passed"])

    return {
        "ok": len(failures) == 0,
        "schema_version": SCHEMA_VERSION,
        "toolchain": PINNED_TOOLCHAIN,
        "violations": [
            {"category": "tamperSuiteMismatch", "code": "tamperSuiteMismatch", "detail": f}
            for f in failures
        ],
        "summary": {
            "positive_passed": pos_passed,
            "positive_total": len(canonical_pos),
            "negative_rejected": neg_passed,
            "negative_total": len(canonical_neg),
            "subchecks_passed": sub_passed,
            "subchecks_total": len(sub_results),
            "elapsed_seconds": elapsed,
            "phase_seconds": {
                "compile_inspector": t_compile_insp,
                "compile_fixtures": t_compile_fx,
                "forge_oleans": t_forge,
                "audit_cases": round(max(0.0, elapsed - t_compile_insp - t_compile_fx - t_forge), 3),
            },
        },
        "cases": results,
    }


# ---------------------------------------------------------------------------
# CLI Argument Parser & Entrypoint
# ---------------------------------------------------------------------------


class _ExitCodeArgumentParser(argparse.ArgumentParser):
    def error(self, message: str) -> None:
        raise AuditOperationalError(f"CLI argument error: {message}")


def build_arg_parser() -> argparse.ArgumentParser:
    parser = _ExitCodeArgumentParser(
        prog="olean_replay_key_audit.py",
        description=__doc__,
    )
    parser.add_argument(
        "--audit-module",
        "--module",
        dest="modules",
        action="append",
        default=[],
        metavar="MOD",
        help="Compiled Lean module name to audit (repeatable).",
    )
    parser.add_argument(
        "--olean-dir",
        dest="olean_dirs",
        action="append",
        type=Path,
        default=[],
        metavar="DIR",
        help="Search directory for compiled `.olean` artifacts (repeatable; defaults to `.lake/build/lib/lean`).",
    )
    parser.add_argument(
        "--source-map",
        type=Path,
        default=None,
        metavar="JSON_OR_DIR",
        help="JSON mapping `{module: path}` or root source directory for defense-in-depth source auditing.",
    )
    parser.add_argument(
        "--strict-proofs",
        action="store_true",
        help="Enforce strict proof-module extension and source coverage discipline.",
    )
    parser.add_argument(
        "--module-mode",
        action="store_true",
        help="Require multi-part `.olean`, `.olean.server`, and `.olean.private` artifacts.",
    )
    parser.add_argument(
        "--allow-assumptions",
        action="store_true",
        help="Admit axioms declared in `Assumptions.*` modules and classify items as conditional.",
    )
    parser.add_argument(
        "--allow-provisional-native",
        action="store_true",
        help="Admit well-shaped `._native.*` axioms in `Proof.*` modules (never `Lean.trustCompiler`).",
    )
    parser.add_argument(
        "--allow-local-test-axioms",
        action="store_true",
        help="Admit file-local axioms inside `.test` modules.",
    )
    parser.add_argument(
        "--run-tamper-suite",
        "--self-test",
        dest="run_tamper_suite",
        action="store_true",
        help="Compile and verify `00_clean_positive` + all `18` negative tamper fixtures inside TemporaryDirectory.",
    )
    parser.add_argument(
        "--emit-patch-spec",
        action="store_true",
        help="Emit the structured Patch 1-12 specification for `trusted/audit/TrustedBoundary.lean`.",
    )
    parser.add_argument(
        "--lean",
        type=Path,
        default=None,
        metavar="ABS_LEAN_PATH",
        help="Optional absolute path to pinned Lean 4.34.1 binary.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit deterministic machine-readable JSON output.",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    json_requested = bool(argv is not None and "--json" in argv) or (
        argv is None and "--json" in sys.argv[1:]
    )
    parser = build_arg_parser()
    try:
        args = parser.parse_args(list(argv) if argv is not None else None)
        json_requested = bool(args.json)

        modes_chosen = sum(
            [
                bool(args.emit_patch_spec),
                bool(args.run_tamper_suite),
                bool(args.modules),
            ]
        )
        if modes_chosen == 0:
            raise AuditOperationalError(
                "specify one of `--audit-module <Mod>`, `--run-tamper-suite`, or `--emit-patch-spec`"
            )
        if modes_chosen > 1:
            raise AuditOperationalError(
                "`--audit-module`, `--run-tamper-suite`, and `--emit-patch-spec` are mutually exclusive"
            )

        if args.emit_patch_spec:
            spec = build_trusted_boundary_patch_spec()
            if args.json:
                print(json.dumps(spec, indent=2, sort_keys=True))
            else:
                print(
                    f"# TrustedBoundary.lean Patch Specification ({spec['patch_count']} patches, "
                    f"frozen under {spec['freeze_workstream']})"
                )
                for p in spec["patches"]:
                    syms = ", ".join(p["target_symbols"])
                    print(f"- {p['id']} ({p['lines']}) [{syms}]: {p['summary']}")
            return 0

        if args.run_tamper_suite:
            report = run_tamper_suite(lean_bin=args.lean)
            if args.json:
                print(json.dumps(report, indent=2, sort_keys=True))
            else:
                s = report["summary"]
                status_word = "PASS" if report["ok"] else "FAIL"
                print(
                    f"{status_word}: tamper suite — positive {s['positive_passed']}/{s['positive_total']} accepted, "
                    f"negative {s['negative_rejected']}/{s['negative_total']} rejected, "
                    f"subchecks {s['subchecks_passed']}/{s['subchecks_total']} passed "
                    f"({s['elapsed_seconds']}s)"
                )
                for v in report["violations"]:
                    print(f"  MISMATCH: {v['detail']}", file=sys.stderr)
            return 0 if report["ok"] else 1

        olean_dirs = list(args.olean_dirs) if args.olean_dirs else [REPO_ROOT / ".lake" / "build" / "lib" / "lean"]
        auto_repo = not bool(args.olean_dirs) and args.source_map is None
        smap = load_source_map(args.source_map, args.modules, auto_repo_sources=auto_repo)
        require_sources = bool(args.strict_proofs or args.source_map is not None or auto_repo)

        report = audit_modules(
            args.modules,
            olean_dirs=olean_dirs,
            source_map=smap,
            require_sources=require_sources,
            strict_proofs=args.strict_proofs,
            module_mode=args.module_mode,
            allow_assumptions=args.allow_assumptions,
            allow_provisional_native=args.allow_provisional_native,
            allow_local_test_axioms=args.allow_local_test_axioms,
            lean_bin=args.lean,
        )
        if args.json:
            print(json.dumps(report, indent=2, sort_keys=True))
        else:
            if report["ok"]:
                s = report["summary"]
                print(
                    f"PASS: audited {len(s['audited_modules'])} module(s), "
                    f"kernel-replayed {s['replayed_declarations']} declaration(s), "
                    f"axioms={s['reached_axioms']}"
                )
            else:
                for v in report["violations"]:
                    print(
                        f"AUDIT FAIL [{v['category']}] in {v.get('module', '<unknown>')}: {v.get('detail', '')}",
                        file=sys.stderr,
                    )
        return 0 if report["ok"] else 1

    except AuditOperationalError as exc:
        if json_requested:
            err_obj = {
                "ok": False,
                "schema_version": SCHEMA_VERSION,
                "operational_error": True,
                "violations": [
                    {
                        "category": "operationalError",
                        "code": "operationalError",
                        "detail": str(exc),
                    }
                ],
            }
            print(json.dumps(err_obj, indent=2, sort_keys=True))
        else:
            print(f"Operational error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
