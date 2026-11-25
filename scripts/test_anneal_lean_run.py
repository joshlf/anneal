#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and integration tests for `scripts/anneal-lean-run`."""

from __future__ import annotations

import contextlib
import fcntl
import importlib.machinery
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import shlex
import stat
import subprocess
import sys
import tempfile
from typing import Any, Callable, Iterator, MutableMapping
import unittest
from unittest import mock

sys.dont_write_bytecode = True

SCRIPT_PATH = Path(__file__).resolve().parent / "anneal-lean-run"


def _load_anneal_lean_run():
    loader = importlib.machinery.SourceFileLoader(
        "anneal_lean_run", str(SCRIPT_PATH)
    )
    spec = importlib.util.spec_from_loader("anneal_lean_run", loader)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    return module


alr = _load_anneal_lean_run()
MIB = 1024 * 1024

# Hermetic Git for every repository these tests create (and for every `git`
# subprocess spawned by `anneal-lean-run` itself): ignore host/user Git config
# (hooks, aliases, signing, git-secrets) and fix commit identities.
_HERMETIC_GIT_ENV = {
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_NOSYSTEM": "1",
    "GIT_TERMINAL_PROMPT": "0",
    "GIT_AUTHOR_NAME": "Test User",
    "GIT_AUTHOR_EMAIL": "test@example.com",
    "GIT_COMMITTER_NAME": "Test User",
    "GIT_COMMITTER_EMAIL": "test@example.com",
}
_AMBIENT_ANNEAL_ENV_PREFIXES: tuple[str, ...] = (
    "ANNEAL_LEAN_",
    "ANNEAL_WORKTREE_",
    "ANNEAL_LSP_",
    "ANNEAL_OOM_",
)
_ENV_PATCHER: Any = None
# Every Python-level way to replace the current process image ends in `os.execv` or
# `os.execve` (`os.execl*` / `os.execvp*` are wrappers around them).
_GUARDED_EXEC_FUNCTIONS: tuple[str, ...] = ("execv", "execve", "execvp", "execvpe")
_EXEC_GUARDS: list[Any] = []
_ORIG_ACQUIRE_BUILD_SLOT = alr.acquire_build_slot
_ORIG_COUNT_ACTIVE_BUILD_SLOTS = alr.count_active_build_slots
_ORIG_STAMP_LAST_OOM = alr.stamp_last_oom
_ORIG_EVICT_LSP_WORKERS = alr._evict_lsp_workers
_SLOT_LOCK_GUARD: Any = None
# Module-wide redirects of `count_active_build_slots` / `stamp_last_oom` /
# `_evict_lsp_workers` away from live host state (started in `setUpModule`, stopped in
# `tearDownModule`).
_HOST_RUNTIME_GUARDS: list[Any] = []
# Module-wide host-state audit: every in-process audit event and every `_isolated_cli_env`
# subprocess (through a `sitecustomize` on `PYTHONPATH`) that touches live host build-slot
# locks, OOM memos, or the default host LSP socket is recorded and fails `tearDownModule`.
_HOST_AUDIT_TMPDIR: tempfile.TemporaryDirectory[str] | None = None
_HOST_AUDIT_ACTIVE = False
_HOST_AUDIT_HOOKED = False
_HOST_AUDIT_SINK: list[dict[str, Any]] = []
_HOST_AUDIT_ENV_LOG = "ALR_HOST_AUDIT_LOG"
_XDG_TMPDIR: tempfile.TemporaryDirectory[str] | None = None
_XDG_RUNTIME_TMPDIR: tempfile.TemporaryDirectory[str] | None = None
# Text of the `anneal-workloads.slice` unit `ensure_workloads_slice` reconciles on this
# host, or `None` when it refuses to write one (no delegated `systemd --user`).
_SLICE_UNIT_SEED: str | None = None


def _scrub_ambient_anneal_env(env: MutableMapping[str, str]) -> None:
    for key in list(env):
        if key.startswith(_AMBIENT_ANNEAL_ENV_PREFIXES):
            env.pop(key, None)


# Shared by the in-process audit hook and the child `sitecustomize`: classify one audit
# event as a live host-state touch (`dict`) or not (`None`). Paths are checked lexically
# and through `realpath`, so symlinks into `/run/user/<uid>` or `/tmp` are caught too.
_HOST_AUDIT_CORE = """\
import os, socket as _socket

_UID = os.getuid()
_SLOT_DIR_NAME = f"anneal-build-slots-{_UID}"
_OOM_PREFIX = f"anneal-last-oom-{_UID}."
_BASES = []
for _b in (f"/run/user/{_UID}", "/tmp"):
    for _v in {_b, os.path.realpath(_b)}:
        if _v not in _BASES:
            _BASES.append(_v)
_LSP_SOCKS = {"/tmp/anneal-lean-lsp.sock", os.path.realpath("/tmp/anneal-lean-lsp.sock")}
_PATH_EVENTS = {
    "open": (0,), "os.mkdir": (0,), "os.scandir": (0,), "os.listdir": (0,),
    "os.remove": (0,), "os.rmdir": (0,), "os.rename": (0, 1), "os.chmod": (0,),
    "os.truncate": (0,), "os.utime": (0,), "shutil.rmtree": (0,),
}


def _host_state_path(raw):
    if not isinstance(raw, (str, bytes, os.PathLike)):
        return None
    try:
        path = os.path.abspath(os.fsdecode(raw))
    except (TypeError, ValueError):
        return None
    cands = (
        path,
        os.path.join(os.path.realpath(os.path.dirname(path)), os.path.basename(path)),
        os.path.realpath(path),
    )
    for cand in cands:
        for base in _BASES:
            if not cand.startswith(base + os.sep):
                continue
            rel = cand[len(base) + 1:]
            if (
                rel == _SLOT_DIR_NAME
                or rel.startswith(_SLOT_DIR_NAME + os.sep)
                or rel.startswith(_OOM_PREFIX)
            ):
                return cand
    return None


def classify_host_state_event(event, args):
    idxs = _PATH_EVENTS.get(event)
    if idxs is not None:
        for i in idxs:
            if i < len(args):
                hit = _host_state_path(args[i])
                if hit is not None:
                    return {"event": event, "path": hit}
        return None
    if event == "socket.connect" and len(args) > 1 and isinstance(args[1], (str, bytes)):
        try:
            addr = os.path.abspath(os.fsdecode(args[1]))
        except (TypeError, ValueError):
            return None
        if addr in _LSP_SOCKS or os.path.realpath(addr) in _LSP_SOCKS:
            return {"event": event, "path": addr}
    return None
"""

_HOST_AUDIT_SITECUSTOMIZE = _HOST_AUDIT_CORE + """
import importlib.machinery as _ilm, importlib.util as _ilu, json as _json, sys as _sys

ALR_HOST_STATE_AUDIT = True
_LOG = os.environ.get("ALR_HOST_AUDIT_LOG")
_IN_HOOK = False


def _alr_host_audit_hook(event, args):
    global _IN_HOOK
    if not _LOG or _IN_HOOK:
        return
    hit = classify_host_state_event(event, args)
    if hit is None:
        return
    hit["pid"] = os.getpid()
    hit["argv"] = list(_sys.argv[:8])
    _IN_HOOK = True
    try:
        fd = os.open(_LOG, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
        try:
            os.write(fd, (_json.dumps(hit) + "\\n").encode("utf-8"))
        finally:
            os.close(fd)
    except OSError:
        pass
    finally:
        _IN_HOOK = False


_sys.addaudithook(_alr_host_audit_hook)

# Chain to the next `sitecustomize` on `sys.path` (e.g. the distro's) so behavior is
# otherwise unchanged.
_here = os.path.dirname(os.path.abspath(__file__))
_rest = [p for p in _sys.path if os.path.abspath(p or os.curdir) != _here]
_spec = _ilm.PathFinder.find_spec("sitecustomize", _rest)
if _spec is not None and _spec.loader is not None:
    _mod = _ilu.module_from_spec(_spec)
    try:
        _spec.loader.exec_module(_mod)
    except Exception:
        pass
"""

_HOST_AUDIT_NS: dict[str, Any] = {}
exec(compile(_HOST_AUDIT_CORE, "<alr-host-audit-core>", "exec"), _HOST_AUDIT_NS)
_classify_host_state_event = _HOST_AUDIT_NS["classify_host_state_event"]


def _in_process_host_audit_hook(event: str, args: tuple[Any, ...]) -> None:
    # Audit hooks cannot be removed; this one is inert outside this module's lifetime.
    if not _HOST_AUDIT_ACTIVE:
        return
    hit = _classify_host_state_event(event, args)
    if hit is not None:
        _HOST_AUDIT_SINK.append(hit)


def _host_audit_log_path() -> Path | None:
    if _HOST_AUDIT_TMPDIR is None:
        return None
    return Path(_HOST_AUDIT_TMPDIR.name) / "violations.jsonl"


def _collect_host_audit_violations() -> list[dict[str, Any]]:
    found = list(_HOST_AUDIT_SINK)
    log_path = _host_audit_log_path()
    if log_path is not None and log_path.exists():
        for line in log_path.read_text(encoding="utf-8", errors="replace").splitlines():
            if not line.strip():
                continue
            try:
                found.append(json.loads(line))
            except ValueError:
                found.append({"event": "corrupt_audit_line", "raw": line})
    return found


def _isolated_cli_env(
    xdg_config_home: Path,
    env_extra: dict[str, str] | None = None,
    *,
    xdg_runtime_dir: Path | None = None,
) -> dict[str, str]:
    env = dict(os.environ)
    _scrub_ambient_anneal_env(env)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["XDG_CONFIG_HOME"] = str(xdg_config_home)
    if xdg_runtime_dir is not None:
        env["XDG_RUNTIME_DIR"] = str(xdg_runtime_dir)
    elif _XDG_RUNTIME_TMPDIR is not None:
        env["XDG_RUNTIME_DIR"] = _XDG_RUNTIME_TMPDIR.name
    else:
        env.pop("XDG_RUNTIME_DIR", None)
    log_path = _host_audit_log_path()
    if log_path is not None:
        env[_HOST_AUDIT_ENV_LOG] = str(log_path)
    if env_extra:
        env.update(env_extra)
    # Prepend the auditing `sitecustomize` directory AFTER `env_extra` so an explicit
    # `env_extra={"PYTHONPATH": ...}` chains cleanly behind it instead of disabling it.
    if log_path is not None:
        assert _HOST_AUDIT_TMPDIR is not None
        existing_pp = env.get("PYTHONPATH", "")
        parts = [p for p in existing_pp.split(os.pathsep) if p and p != _HOST_AUDIT_TMPDIR.name]
        env["PYTHONPATH"] = os.pathsep.join([_HOST_AUDIT_TMPDIR.name, *parts])
    return env


@contextlib.contextmanager
def _guarded_acquire_build_slot(
    max_slots: int,
    timeout_sec: float,
    enabled: bool,
    *,
    exclusive: bool = False,
    runtime_base: Path | None = None,
    poll_interval: float = 0.5,
) -> Iterator[int | list[int] | None]:
    if enabled and max_slots > 0:
        uid = os.getuid()
        eff_base = (
            Path(runtime_base)
            if runtime_base is not None
            else alr.resolve_runtime_base()[0]
        )
        forbidden_bases = {
            Path(f"/run/user/{uid}").resolve(),
            Path("/tmp").resolve(),
        }
        slot_subdir = f"anneal-build-slots-{uid}"
        forbidden_slot_dirs = {base / slot_subdir for base in forbidden_bases}
        resolved_base = eff_base.resolve()
        resolved_slot_dir = (resolved_base / slot_subdir).resolve()
        if resolved_base in forbidden_bases or resolved_slot_dir in forbidden_slot_dirs:
            raise AssertionError(
                f"test attempted to acquire a live host build-slot lock under {resolved_base}"
            )
    with _ORIG_ACQUIRE_BUILD_SLOT(
        max_slots,
        timeout_sec,
        enabled,
        exclusive=exclusive,
        runtime_base=runtime_base,
        poll_interval=poll_interval,
    ) as slots:
        yield slots


def _host_runtime_bases() -> frozenset[Path]:
    """Resolved live host runtime bases `resolve_runtime_base()` can return."""
    bases: set[Path] = set()
    for base in (Path(f"/run/user/{os.getuid()}"), Path("/tmp")):
        try:
            bases.add(base.resolve())
        except OSError:
            pass
    return frozenset(bases)


def _redirect_host_runtime_base(runtime_base: Path | str | None) -> Path:
    """Map a live host runtime base (`/run/user/<uid>` or `/tmp`, also via symlinks or
    symlinked `anneal-build-slots-<uid>` subdirs) to the module-scoped isolated
    `XDG_RUNTIME_DIR`; pass any other base through unchanged."""
    uid = os.getuid()
    eff = Path(runtime_base) if runtime_base is not None else alr.resolve_runtime_base()[0]
    host_bases = _host_runtime_bases()
    slot_subdir = f"anneal-build-slots-{uid}"
    host_slot_dirs = {b / slot_subdir for b in host_bases}
    try:
        resolved = eff.resolve()
        resolved_slot = (resolved / slot_subdir).resolve()
    except OSError:
        return eff
    if resolved in host_bases or resolved_slot in host_slot_dirs:
        if _XDG_RUNTIME_TMPDIR is None:
            raise AssertionError(f"host runtime base {eff} touched outside module setup")
        return Path(_XDG_RUNTIME_TMPDIR.name)
    return eff


def _isolated_count_active_build_slots(
    runtime_base: Path, uid: int | None = None
) -> int:
    # `probe_host_envelope` counts held slots under `resolve_runtime_base()` (always
    # `/run/user/<uid>` when it exists, regardless of `XDG_RUNTIME_DIR`): never take even a
    # transient `LOCK_SH` on live host slot locks, and keep probes independent of host load.
    return _ORIG_COUNT_ACTIVE_BUILD_SLOTS(_redirect_host_runtime_base(runtime_base), uid=uid)


def _isolated_stamp_last_oom(runtime_base: Path, *args: Any, **kwargs: Any) -> Path:
    # Never rewrite the live host `anneal-last-oom-<uid>.json` OOM-budget memo.
    return _ORIG_STAMP_LAST_OOM(_redirect_host_runtime_base(runtime_base), *args, **kwargs)


def _isolated_evict_lsp_workers(
    env_info: dict[str, Any], *, sock_path: Path | None = None, **kwargs: Any
) -> bool:
    # Build-mode runs evict warm LSP workers through the default host socket
    # (`/tmp/anneal-lean-lsp.sock`) whenever headroom is short: never restart the live
    # host daemon's workers from a test unless one opts in via `sock_path` / `ANNEAL_LSP_SOCKET`.
    if sock_path is None and "ANNEAL_LSP_SOCKET" not in os.environ:
        if _XDG_RUNTIME_TMPDIR is None:
            raise AssertionError("host LSP eviction attempted outside module setup")
        sock_path = Path(_XDG_RUNTIME_TMPDIR.name) / "anneal-lean-lsp.sock"
    return _ORIG_EVICT_LSP_WORKERS(env_info, sock_path=sock_path, **kwargs)


# Child-side twin of the module guards for real `scripts/anneal-lean-run` CLI subprocesses
# (`TestCliSubprocess._cli`): loads the script exactly as `__main__` would run it (same
# `sys.argv[0]`, same `main()` entry), but redirects build-slot counting / locking and OOM
# memos from the live host runtime base to the per-invocation isolated directory `argv[2]`,
# and points default-socket LSP eviction there too (a missing socket: a no-op).
# Everything else (`resolve_runtime_base`, `systemd-run --user` scopes) stays live.
_ISOLATED_CLI_SHIM = """\
import importlib.machinery, importlib.util, os, pathlib, sys
script, iso = sys.argv[1], pathlib.Path(sys.argv[2])
name = "anneal_lean_run_isolated_cli"
loader = importlib.machinery.SourceFileLoader(name, script)
spec = importlib.util.spec_from_loader(name, loader)
mod = importlib.util.module_from_spec(spec)
sys.modules[name] = mod
loader.exec_module(mod)
uid = os.getuid()
host = set()
for base in (pathlib.Path(f"/run/user/{uid}"), pathlib.Path("/tmp")):
    try:
        host.add(base.resolve())
    except OSError:
        pass
slot_subdir = f"anneal-build-slots-{uid}"
host_slot_dirs = {b / slot_subdir for b in host}
if not iso.is_dir() or iso.resolve() in host or (iso.resolve() / slot_subdir).resolve() in host_slot_dirs:
    sys.exit(f"anneal-lean-run test shim: refusing non-isolated runtime base {iso}")
def redirect(base):
    eff = pathlib.Path(base) if base is not None else mod.resolve_runtime_base()[0]
    try:
        resolved = eff.resolve()
        if resolved in host or (resolved / slot_subdir).resolve() in host_slot_dirs:
            return iso
        return eff
    except OSError:
        return eff
orig_count = mod.count_active_build_slots
orig_acquire = mod.acquire_build_slot
orig_stamp = mod.stamp_last_oom
def count_active_build_slots(runtime_base, uid=None):
    return orig_count(redirect(runtime_base), uid=uid)
def acquire_build_slot(max_slots, timeout_sec, enabled, *, runtime_base=None, **kw):
    return orig_acquire(max_slots, timeout_sec, enabled, runtime_base=redirect(runtime_base), **kw)
def stamp_last_oom(runtime_base, *args, **kw):
    return orig_stamp(redirect(runtime_base), *args, **kw)
orig_evict = mod._evict_lsp_workers
def _evict_lsp_workers(env_info, *, sock_path=None, **kw):
    if sock_path is None and "ANNEAL_LSP_SOCKET" not in os.environ:
        sock_path = iso / "anneal-lean-lsp.sock"
    return orig_evict(env_info, sock_path=sock_path, **kw)
mod.count_active_build_slots = count_active_build_slots
mod.acquire_build_slot = acquire_build_slot
mod.stamp_last_oom = stamp_last_oom
mod._evict_lsp_workers = _evict_lsp_workers
sys.argv = [script, *sys.argv[3:]]
sys.exit(mod.main())
"""


def _forbid_in_process_exec(file: str, args: Any, *rest: Any) -> None:
    raise AssertionError(
        f"in-process exec of {args!r} would replace the unittest runner and report the "
        "command's exit status as the suite's (did ANNEAL_LEAN_RUN_IN_SCOPE leak into "
        "the test process?)"
    )


def _render_live_workloads_slice_unit() -> str | None:
    """Unit text `ensure_workloads_slice` renders on this host (`None` if it refuses)."""
    try:
        info = alr.probe_host_envelope(is_probe=True)
    except Exception:  # noqa: BLE001 - seeding is best-effort; the probe has its own tests
        return None
    if not (info.get("user_systemd_active") and info.get("t_cg_is_user_service")):
        return None
    return alr.render_workloads_slice_unit(
        int(info["w_slice_high_mb"]), int(info["w_slice_max_mb"])
    )


def _seed_workloads_slice_unit(xdg_config_home: Path) -> Path | None:
    """Pre-renders `anneal-workloads.slice` under an isolated `XDG_CONFIG_HOME`.

    A command-executing `anneal-lean-run` first reconciles
    `$XDG_CONFIG_HOME/systemd/user/anneal-workloads.slice`.  Under an *empty* isolated
    `XDG_CONFIG_HOME` the unit looks absent, so every such run would write it there and
    then `systemctl --user daemon-reload` the host's live user manager.  Seeding the exact
    text the script would render keeps that reconciliation a content-diff no-op: tests
    neither read the host's real unit file nor reload the host's `systemd --user`.

    Returns the seeded path, or `None` when this host never reconciles the unit.
    """
    if _SLICE_UNIT_SEED is None:
        return None
    unit = xdg_config_home / "systemd" / "user" / "anneal-workloads.slice"
    unit.parent.mkdir(parents=True, exist_ok=True)
    unit.write_text(_SLICE_UNIT_SEED, encoding="utf-8")
    return unit


def _can_launch_live_systemd_scope() -> bool:
    """True only when user systemd is active and `systemd-run --user --scope`
    can actually launch a trivial transient scope on this host.
    """
    if not sys.platform.startswith("linux") or not alr.check_user_systemd_active():
        return False
    srun_bin = alr._find_systemd_run()
    if not srun_bin:
        return False
    rb, sock_alive = alr.resolve_runtime_base()
    try:
        res = subprocess.run(
            [srun_bin, "--user", "--scope", "--collect", "--quiet", "--", "true"],
            env=alr._systemd_env(rb, sock_alive),
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=5.0,
            check=False,
        )
        return res.returncode == 0
    except (OSError, subprocess.SubprocessError):
        return False


def _file_identity(path: Path) -> tuple[int, int, str]:
    """`(inode, mtime_ns, text)`: changes whenever the file is rewritten or replaced."""
    st = path.stat()
    return st.st_ino, st.st_mtime_ns, path.read_text(encoding="utf-8")


def setUpModule() -> None:
    global _ENV_PATCHER, _SLOT_LOCK_GUARD, _XDG_TMPDIR, _XDG_RUNTIME_TMPDIR, _SLICE_UNIT_SEED
    global _HOST_AUDIT_TMPDIR, _HOST_AUDIT_ACTIVE, _HOST_AUDIT_HOOKED
    try:
        _HOST_AUDIT_TMPDIR = tempfile.TemporaryDirectory(prefix="anneal-test-host-audit-")
        (Path(_HOST_AUDIT_TMPDIR.name) / "sitecustomize.py").write_text(
            _HOST_AUDIT_SITECUSTOMIZE, encoding="utf-8"
        )
        _HOST_AUDIT_SINK.clear()
        if not _HOST_AUDIT_HOOKED:
            sys.addaudithook(_in_process_host_audit_hook)
            _HOST_AUDIT_HOOKED = True
        _HOST_AUDIT_ACTIVE = True
        _XDG_TMPDIR = tempfile.TemporaryDirectory(prefix="anneal-test-xdg-")
        _XDG_RUNTIME_TMPDIR = tempfile.TemporaryDirectory(prefix="anneal-test-xdg-rt-")
        os.chmod(_XDG_RUNTIME_TMPDIR.name, 0o700)
        patch_vals = {
            **_HERMETIC_GIT_ENV,
            "XDG_CONFIG_HOME": _XDG_TMPDIR.name,
            "XDG_RUNTIME_DIR": _XDG_RUNTIME_TMPDIR.name,
        }
        _ENV_PATCHER = mock.patch.dict(os.environ, patch_vals)
        _ENV_PATCHER.start()
        # `patch.dict` restores the full original environment on stop.
        for name in alr._GIT_LOCAL_ENV_VARS:
            os.environ.pop(name, None)
        _scrub_ambient_anneal_env(os.environ)
        # The re-entrancy pass-through of `alr.main` `os.execvp`s its command.  In-process that
        # would replace the unittest runner and end the run early with the command's own exit
        # status (`true` -> 0: a truncated run reported as success), so fail loudly instead.
        # Subprocesses are unaffected (`subprocess` does not go through `os.exec*`).
        for name in _GUARDED_EXEC_FUNCTIONS:
            guard = mock.patch.object(os, name, side_effect=_forbid_in_process_exec)
            guard.start()
            _EXEC_GUARDS.append(guard)
        # Fail loudly if any in-process test attempts to acquire a live host build-slot lock
        # under `/run/user/<uid>` or `/tmp`.
        _SLOT_LOCK_GUARD = mock.patch.object(
            alr, "acquire_build_slot", side_effect=_guarded_acquire_build_slot
        )
        _SLOT_LOCK_GUARD.start()
        # `resolve_runtime_base()` always prefers a live `/run/user/<uid>` over
        # `XDG_RUNTIME_DIR`, so env isolation alone cannot keep probes off host slot locks:
        # redirect slot counting and OOM memos to the module-scoped runtime dir as well.
        for attr, replacement in (
            ("count_active_build_slots", _isolated_count_active_build_slots),
            ("stamp_last_oom", _isolated_stamp_last_oom),
            ("_evict_lsp_workers", _isolated_evict_lsp_workers),
        ):
            runtime_guard = mock.patch.object(alr, attr, side_effect=replacement)
            runtime_guard.start()
            _HOST_RUNTIME_GUARDS.append(runtime_guard)
        # In-process `alr.main([... "--", cmd])` runs reconcile the unit under this module-wide
        # `XDG_CONFIG_HOME`; seed it so they never reload the live user manager either.
        _SLICE_UNIT_SEED = _render_live_workloads_slice_unit()
        _seed_workloads_slice_unit(Path(_XDG_TMPDIR.name))
    except BaseException:
        tearDownModule()
        raise


def tearDownModule() -> None:
    global _HOST_AUDIT_TMPDIR, _HOST_AUDIT_ACTIVE
    _HOST_AUDIT_ACTIVE = False
    violations: list[dict[str, Any]] = []
    try:
        violations = _collect_host_audit_violations()
    finally:
        try:
            _teardown_module_state()
        finally:
            _HOST_AUDIT_SINK.clear()
            if _HOST_AUDIT_TMPDIR is not None:
                _HOST_AUDIT_TMPDIR.cleanup()
                _HOST_AUDIT_TMPDIR = None
    if violations:
        raise AssertionError(
            "tests touched live host build-slot / OOM-memo / LSP-socket state: "
            + json.dumps(violations[:20])
        )


def _teardown_module_state() -> None:
    global _ENV_PATCHER, _SLOT_LOCK_GUARD, _XDG_TMPDIR, _XDG_RUNTIME_TMPDIR, _SLICE_UNIT_SEED
    try:
        try:
            while _HOST_RUNTIME_GUARDS:
                _HOST_RUNTIME_GUARDS.pop().stop()
        finally:
            if _SLOT_LOCK_GUARD is not None:
                _SLOT_LOCK_GUARD.stop()
                _SLOT_LOCK_GUARD = None
    finally:
        try:
            while _EXEC_GUARDS:
                _EXEC_GUARDS.pop().stop()
        finally:
            try:
                if _ENV_PATCHER is not None:
                    _ENV_PATCHER.stop()
                    _ENV_PATCHER = None
            finally:
                try:
                    if _XDG_TMPDIR is not None:
                        _XDG_TMPDIR.cleanup()
                        _XDG_TMPDIR = None
                finally:
                    if _XDG_RUNTIME_TMPDIR is not None:
                        _XDG_RUNTIME_TMPDIR.cleanup()
                        _XDG_RUNTIME_TMPDIR = None
                    _SLICE_UNIT_SEED = None


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------


def _write_cgroup_file(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


# Synthetic hosts: 16 logical cores, 64 GiB RAM, one process in `/user.slice/job.scope`
# whose only (optional) memory ceiling is `user.slice/memory.max`.
SYNTHETIC_HOST_CORES = 16


def _write_synthetic_host_base(root: Path) -> None:
    """Writes the `/proc/meminfo` and `/proc/self/cgroup` stand-ins shared by every host."""
    _write_cgroup_file(
        root / "meminfo",
        "MemTotal:       67108864 kB\nMemAvailable:   50331648 kB\n",
    )
    _write_cgroup_file(root / "proc_cgroup", "0::/user.slice/job.scope\n")


def _write_synthetic_cgroup_root(
    root: Path, name: str, user_slice_max_mib: int | None
) -> Path:
    """Writes cgroup v2 root `root/name`; `user_slice_max_mib=None` leaves it uncapped."""
    cg = root / name
    ceiling = "max" if user_slice_max_mib is None else str(user_slice_max_mib * MIB)
    _write_cgroup_file(cg / "user.slice" / "memory.max", f"{ceiling}\n")
    _write_cgroup_file(cg / "user.slice" / "job.scope" / "memory.max", "max\n")
    _write_cgroup_file(
        cg / "user.slice" / "job.scope" / "memory.stat",
        f"anon {512 * MIB}\nshmem 0\nfile {1024 * MIB}\n",
    )
    return cg


# `(cgroup root name, user.slice memory.max in MiB, is_cg_capped, s_heavy_safe)`.
SYNTHETIC_HOSTS: tuple[tuple[str, int | None, bool, int], ...] = (
    ("cg_uncapped", None, False, 2),
    ("cg_capped_1", 12288, True, 1),
    ("cg_capped_2", 32768, True, 2),
)

# Runs the real `main()` of `scripts/anneal-lean-run` in a fresh interpreter with only the
# host probe's inputs redirected to a synthetic host, so argument parsing, environment and
# `$XDG_CONFIG_HOME` handling and the JSON contract are exercised end to end for a cgroup
# regime the machine running the tests may not have.
# argv: <script> <host root> <cgroup root name> [anneal-lean-run args...]
_SYNTHETIC_HOST_CLI_SHIM = f"""\
import functools, importlib.machinery, importlib.util, os, pathlib, sys
script, root, cg_name = sys.argv[1], pathlib.Path(sys.argv[2]), sys.argv[3]
name = "anneal_lean_run_synthetic"
loader = importlib.machinery.SourceFileLoader(name, script)
spec = importlib.util.spec_from_loader(name, loader)
mod = importlib.util.module_from_spec(spec)
sys.modules[name] = mod
loader.exec_module(mod)
uid = os.getuid()
host = set()
for base in (pathlib.Path(f"/run/user/{{uid}}"), pathlib.Path("/tmp")):
    try:
        host.add(base.resolve())
    except OSError:
        pass
slot_subdir = f"anneal-build-slots-{{uid}}"
host_slot_dirs = {{b / slot_subdir for b in host}}
def redirect(base):
    eff = pathlib.Path(base) if base is not None else root
    try:
        resolved = eff.resolve()
        if resolved in host or (resolved / slot_subdir).resolve() in host_slot_dirs:
            return root
        return eff
    except OSError:
        return eff
orig_count = mod.count_active_build_slots
orig_acquire = mod.acquire_build_slot
orig_stamp = mod.stamp_last_oom
orig_evict = mod._evict_lsp_workers
mod.count_active_build_slots = lambda runtime_base, uid=None: orig_count(redirect(runtime_base), uid=uid)
mod.acquire_build_slot = lambda max_slots, timeout_sec, enabled, *, runtime_base=None, **kw: orig_acquire(max_slots, timeout_sec, enabled, runtime_base=redirect(runtime_base), **kw)
mod.stamp_last_oom = lambda runtime_base, *args, **kw: orig_stamp(redirect(runtime_base), *args, **kw)
def _evict_lsp_workers(env_info, *, sock_path=None, **kw):
    if sock_path is None and "ANNEAL_LSP_SOCKET" not in os.environ:
        sock_path = root / "anneal-lean-lsp.sock"
    return orig_evict(env_info, sock_path=sock_path, **kw)
mod._evict_lsp_workers = _evict_lsp_workers
mod.probe_host_envelope = functools.partial(
    mod.probe_host_envelope,
    meminfo_path=root / "meminfo",
    cgroup_root=root / cg_name,
    proc_cgroup_path=root / "proc_cgroup",
    cpu_cores={SYNTHETIC_HOST_CORES},
    user_systemd_active=False,
    runtime_base=root,
)
sys.exit(mod.main(sys.argv[4:]))
"""


FAKE_CGROUP_INFO: dict[str, Any] = {
    "cgroup_v2": True,
    "cgroup_path": "/fake.slice/test.scope",
    "cgroup_anon_mib": 1000,
    "cgroup_shmem_mib": 234,
    "cgroup_anon_shmem_mib": 1234,
    "cgroup_file_cache_mib": 5678,
    "cgroup_current_mib": 6912,
    "cgroup_memory_max_mib": None,
    "cgroup_avail_mib": None,
}

FIXED_HW: dict[str, Any] = {
    "cpu_cores": 8,
    "mem_total_mb": 32768,
    "mem_avail_mb": 24576,
    "cgroup_v2": True,
    "cgroup_path": "/user.slice/anneal.scope",
    "cgroup_anon_mib": 900,
    "cgroup_shmem_mib": 100,
    "cgroup_anon_shmem_mib": 1000,
    "cgroup_file_cache_mib": 3000,
    "cgroup_current_mib": 4200,
    "cgroup_memory_max_mib": 20480,
    "cgroup_avail_mib": 19480,
}


# ---------------------------------------------------------------------------
# Cgroup v2 probing
# ---------------------------------------------------------------------------


class TestCgroupV2Probing(unittest.TestCase):
    """Tests cgroup v2 discovery, `memory.stat` parsing, and `anon + shmem` budgeting."""

    def test_parse_proc_cgroup_v2_variants(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "cgroup"

            # Standard systemd unified cgroup v2 path
            p.write_text(
                "0::/user.slice/user-1000.slice/session-1.scope\n",
                encoding="utf-8",
            )
            self.assertEqual(
                alr.parse_proc_cgroup_v2(p),
                "/user.slice/user-1000.slice/session-1.scope",
            )

            # Hybrid v1 + v2 hierarchy with (deleted) suffix
            p.write_text(
                "12:pids:/user.slice\n0::/app.slice/worker.scope (deleted)\n",
                encoding="utf-8",
            )
            self.assertEqual(
                alr.parse_proc_cgroup_v2(p), "/app.slice/worker.scope"
            )

            # Colons inside the path survive (`0::` is split only once)
            p.write_text("0::/app.slice/a:b.scope\n", encoding="utf-8")
            self.assertEqual(alr.parse_proc_cgroup_v2(p), "/app.slice/a:b.scope")

            # Root unified hierarchy inside container namespace
            p.write_text("0::/\n", encoding="utf-8")
            self.assertEqual(alr.parse_proc_cgroup_v2(p), "/")

            # Cgroup v1 only (no 0:: line), including a named v1 hierarchy
            p.write_text(
                "11:memory:/user.slice\n10:cpu:/user.slice\n1:name=systemd:/x\n",
                encoding="utf-8",
            )
            self.assertIsNone(alr.parse_proc_cgroup_v2(p))

            # Empty file and non-existent file
            p.write_text("", encoding="utf-8")
            self.assertIsNone(alr.parse_proc_cgroup_v2(p))
            self.assertIsNone(alr.parse_proc_cgroup_v2(Path(tmp) / "missing"))

    def test_parse_memory_stat(self) -> None:
        raw = (
            "anon 2147483648\n"
            "file 30064771072\n"
            "shmem 536870912\n"
            "inactive_file 25769803776\n"
            "active_file 4294967296\n"
            "malformed_line_without_val\n"
            "bad_int not_a_number\n"
            "neg_val -100\n"
        )
        stats = alr.parse_memory_stat(raw)
        self.assertEqual(stats["anon"], 2147483648)
        self.assertEqual(stats["file"], 30064771072)
        self.assertEqual(stats["shmem"], 536870912)
        self.assertEqual(stats["inactive_file"], 25769803776)
        self.assertEqual(stats["active_file"], 4294967296)
        self.assertNotIn("bad_int", stats)
        self.assertNotIn("neg_val", stats)
        self.assertNotIn("malformed_line_without_val", stats)

        with tempfile.TemporaryDirectory() as tmp:
            stat_file = Path(tmp) / "memory.stat"
            stat_file.write_text(raw, encoding="utf-8")
            self.assertEqual(alr.parse_memory_stat(stat_file), stats)
            self.assertEqual(alr.parse_memory_stat(str(stat_file)), stats)
            self.assertEqual(alr.parse_memory_stat(Path(tmp) / "missing"), {})

    def test_reclaimable_file_cache_does_not_throttle_available_memory(
        self,
    ) -> None:
        """32 GiB cgroup with 28 GiB `.olean` file cache and 2 GiB `anon + shmem`
        must report 30 GiB available (`32 - 2`), NOT 2 GiB (`32 - 30`)."""
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "user.slice" / "anneal.scope"
            leaf.mkdir(parents=True)
            # Notice: root cgroup does NOT have memory.stat (standard systemd host)
            (leaf / "memory.max").write_text(
                f"{32768 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.current").write_text(
                f"{30720 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.stat").write_text(
                f"anon {1536 * MIB}\n"
                f"shmem {512 * MIB}\n"
                f"file {28672 * MIB}\n"
                f"inactive_file {24576 * MIB}\n"
                f"active_file {4096 * MIB}\n",
                encoding="utf-8",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text(
                "0::/user.slice/anneal.scope\n", encoding="utf-8"
            )
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       67108864 kB\nMemAvailable:   49152000 kB\n",
                encoding="utf-8",
            )

            hw = alr.probe_host_hardware(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
            )
            self.assertTrue(hw["cgroup_v2"])
            self.assertEqual(hw["cgroup_path"], "/user.slice/anneal.scope")
            self.assertEqual(hw["cgroup_anon_mib"], 1536)
            self.assertEqual(hw["cgroup_shmem_mib"], 512)
            self.assertEqual(hw["cgroup_anon_shmem_mib"], 2048)
            self.assertEqual(hw["cgroup_file_cache_mib"], 28672)
            self.assertEqual(hw["cgroup_current_mib"], 30720)
            self.assertEqual(hw["cgroup_memory_max_mib"], 32768)
            # Headroom MUST be 32768 - 2048 = 30720 MiB (not 32768 - 30720 = 2048 MiB),
            # while raw `/proc/meminfo` fields stay un-clamped (`65536` / `48000`) for `c_high_mb`.
            self.assertEqual(hw["cgroup_avail_mib"], 30720)
            self.assertEqual(hw["mem_total_mb"], 65536)
            self.assertEqual(hw["mem_avail_mb"], 48000)

            limits = alr.compute_limits(hw, mode="build", concurrency=1)
            self.assertTrue(limits["is_cg_capped"])
            self.assertGreater(limits["w_slice_max_mb"], 24576)
            self.assertEqual(limits["cgroup_avail_mib"], 30720)
            self.assertEqual(limits["cgroup_memory_max_mib"], 32768)
            # Reclaimable `.olean` file cache (28 GiB) must NOT throttle a build down to 2048 MiB.
            self.assertGreater(limits["memory_max_mb"], 14000)

    def test_high_anon_shmem_throttles_available_memory(self) -> None:
        """32 GiB cgroup with 28 GiB `anon + shmem` and 2 GiB `file` cache
        must drop `cgroup_avail_mib` to 4 GiB (`4096 MiB`) and throttle `memory_max_mb`."""
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "user.slice" / "anneal.scope"
            leaf.mkdir(parents=True)
            (leaf / "memory.max").write_text(
                f"{32768 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.current").write_text(
                f"{30720 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.stat").write_text(
                f"anon {28000 * MIB}\n"
                f"shmem {672 * MIB}\n"
                f"file {2048 * MIB}\n",
                encoding="utf-8",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text(
                "0::/user.slice/anneal.scope\n", encoding="utf-8"
            )
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       67108864 kB\nMemAvailable:   49152000 kB\n",
                encoding="utf-8",
            )

            hw = alr.probe_host_hardware(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
            )
            self.assertEqual(hw["cgroup_anon_shmem_mib"], 28672)
            self.assertEqual(hw["cgroup_avail_mib"], 4096)
            self.assertEqual(hw["mem_avail_mb"], 48000)

            limits = alr.compute_limits(hw, mode="build", concurrency=1)
            self.assertTrue(limits["is_cg_capped"])
            self.assertLessEqual(limits["memory_max_mb"], 4096)
            # File cache must stay un-penalized while 28 GiB anon+shmem throttles build budget
            hw_reclaimable = dict(hw, mem_avail_mb=30720, cgroup_avail_mib=30720, cgroup_anon_shmem_mib=2048)
            limits_reclaimable = alr.compute_limits(hw_reclaimable, mode="build", concurrency=1)
            self.assertLess(limits["memory_max_mb"], limits_reclaimable["memory_max_mb"])

    def test_cgroup_avail_exhausted_floors_mem_avail_at_512(self) -> None:
        """`anon + shmem` above `memory.max` clamps headroom to 0 and `mem_avail_mb` to 512."""
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "job.scope"
            _write_cgroup_file(leaf / "memory.max", f"{4096 * MIB}\n")
            _write_cgroup_file(leaf / "memory.current", f"{4200 * MIB}\n")
            _write_cgroup_file(
                leaf / "memory.stat",
                f"anon {4000 * MIB}\nshmem {200 * MIB}\nfile 0\n",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/job.scope\n", encoding="utf-8")
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       67108864 kB\nMemAvailable:   50331648 kB\n",
                encoding="utf-8",
            )
            hw = alr.probe_host_hardware(
                meminfo_path=meminfo, cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertEqual(hw["cgroup_avail_mib"], 0)
            self.assertEqual(hw["cgroup_memory_max_mib"], 4096)
            self.assertEqual(hw["mem_total_mb"], 65536)
            self.assertEqual(hw["mem_avail_mb"], 49152)
            build = alr.compute_limits(hw, mode="build", concurrency=1)
            # Fail-closed admission: exhausted 4 GiB cgroup must NOT unsafely clamp up to >= 2048 MiB.
            self.assertLess(build["memory_max_mb"], 2048)
            file_limits = alr.compute_limits(hw, mode="file", concurrency=1)
            self.assertLessEqual(file_limits["memory_max_mb"], 1024)

    def test_ancestor_hierarchy_walk_and_root_container_cgroup(self) -> None:
        """Leaf has `memory.max = max`, parent and grandparent have finite limits."""
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            user_slice = cg_root / "user.slice"
            svc = user_slice / "agent-host.service"
            leaf = svc / "server"
            leaf.mkdir(parents=True)

            # Root: 30 GiB max, 5 GiB anon+shmem -> 25 GiB avail
            (cg_root / "memory.max").write_text(
                f"{30720 * MIB}\n", encoding="utf-8"
            )
            (cg_root / "memory.stat").write_text(
                f"anon {5120 * MIB}\nshmem 0\nfile {10240 * MIB}\n",
                encoding="utf-8",
            )

            # user.slice: 24 GiB max, 10 GiB anon+shmem -> 14 GiB avail (tightest avail)
            (user_slice / "memory.max").write_text(
                f"{24576 * MIB}\n", encoding="utf-8"
            )
            (user_slice / "memory.stat").write_text(
                f"anon {9216 * MIB}\nshmem {1024 * MIB}\nfile {8192 * MIB}\n",
                encoding="utf-8",
            )

            # svc: 20 GiB max (tightest max), 3 GiB anon+shmem -> 17 GiB avail
            (svc / "memory.max").write_text(
                f"{20480 * MIB}\n", encoding="utf-8"
            )
            (svc / "memory.stat").write_text(
                f"anon {3072 * MIB}\nshmem 0\nfile {6144 * MIB}\n",
                encoding="utf-8",
            )

            # leaf: unbounded max, 1 GiB anon+shmem
            (leaf / "memory.max").write_text("max\n", encoding="utf-8")
            (leaf / "memory.current").write_text(
                f"{4096 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.stat").write_text(
                f"anon {900 * MIB}\nshmem {124 * MIB}\nfile {3072 * MIB}\n",
                encoding="utf-8",
            )

            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text(
                "0::/user.slice/agent-host.service/server\n", encoding="utf-8"
            )

            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            self.assertEqual(
                cg["cgroup_path"], "/user.slice/agent-host.service/server"
            )
            self.assertEqual(cg["cgroup_anon_shmem_mib"], 1024)
            self.assertEqual(cg["cgroup_file_cache_mib"], 3072)
            self.assertEqual(cg["cgroup_current_mib"], 4096)
            self.assertEqual(cg["cgroup_memory_max_mib"], 20480)
            self.assertEqual(cg["cgroup_avail_mib"], 14336)

            # Also test 0::/ container root mapping
            proc_cg_root = Path(tmp) / "proc_cgroup_root"
            proc_cg_root.write_text("0::/\n", encoding="utf-8")
            cg_at_root = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg_root
            )
            self.assertTrue(cg_at_root["cgroup_v2"])
            self.assertEqual(cg_at_root["cgroup_path"], "/")
            self.assertEqual(cg_at_root["cgroup_memory_max_mib"], 30720)
            self.assertEqual(cg_at_root["cgroup_avail_mib"], 25600)

    def test_unbounded_hierarchy_keeps_host_ram_and_reports_unbounded(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "user.slice" / "a.scope"
            _write_cgroup_file(cg_root / "user.slice" / "memory.max", "max\n")
            _write_cgroup_file(leaf / "memory.max", "max\n")
            _write_cgroup_file(leaf / "memory.current", f"{3000 * MIB}\n")
            _write_cgroup_file(
                leaf / "memory.stat",
                f"anon {700 * MIB}\nshmem {100 * MIB}\nfile {2000 * MIB}\n",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/user.slice/a.scope\n", encoding="utf-8")
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       16777216 kB\nMemAvailable:   12582912 kB\n",
                encoding="utf-8",
            )
            hw = alr.probe_host_hardware(
                meminfo_path=meminfo, cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(hw["cgroup_v2"])
            self.assertIsNone(hw["cgroup_memory_max_mib"])
            self.assertIsNone(hw["cgroup_avail_mib"])
            self.assertEqual(hw["cgroup_anon_shmem_mib"], 800)
            self.assertEqual(hw["mem_total_mb"], 16384)
            self.assertEqual(hw["mem_avail_mb"], 12288)

            limits = alr.compute_limits(hw, mode="build", concurrency=1)
            line = alr.format_cgroup_probe_line(limits)
            self.assertIn("Cgroup v2 Envelope", line)
            self.assertIn("regime=uncapped", line)
            self.assertIn("W_slice_max=", line)

            bounded = dict(
                limits,
                is_cg_capped=True,
                c_high_mb=4096,
                a_lim_path="/sys/fs/cgroup/user.slice",
                w_slice_max_mb=3072,
                w_slice_high_mb=2764,
                w_live_mb=2500,
            )
            bounded_line = alr.format_cgroup_probe_line(bounded)
            self.assertIn("regime=capped", bounded_line)
            self.assertIn("C_high=4096 MiB (/sys/fs/cgroup/user.slice)", bounded_line)
            unavailable = alr.format_cgroup_probe_line(alr._empty_cgroup_info())
            self.assertIn("unavailable", unavailable)

    def test_ancestor_without_memory_stat_falls_back_to_current(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            parent = cg_root / "svc.slice"
            leaf = parent / "job.scope"
            # Parent: finite max, `memory.current` but no `memory.stat`.
            _write_cgroup_file(parent / "memory.max", f"{8192 * MIB}\n")
            _write_cgroup_file(parent / "memory.current", f"{6144 * MIB}\n")
            _write_cgroup_file(leaf / "memory.max", "max\n")
            _write_cgroup_file(leaf / "memory.current", f"{5120 * MIB}\n")
            _write_cgroup_file(
                leaf / "memory.stat",
                f"anon {1024 * MIB}\nshmem 0\nfile {4096 * MIB}\n",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/svc.slice/job.scope\n", encoding="utf-8")
            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            self.assertEqual(cg["cgroup_anon_shmem_mib"], 1024)
            self.assertEqual(cg["cgroup_memory_max_mib"], 8192)
            # 8192 - memory.current (6144) = 2048
            self.assertEqual(cg["cgroup_avail_mib"], 2048)

    def test_missing_memory_stat_fallback_and_non_v2_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            # Ancestor with memory.max and memory.current + inactive_file only
            cg_root = Path(tmp) / "cgroup"
            cg_root.mkdir()
            (cg_root / "memory.max").write_text(
                f"{16384 * MIB}\n", encoding="utf-8"
            )
            (cg_root / "memory.current").write_text(
                f"{10240 * MIB}\n", encoding="utf-8"
            )
            (cg_root / "memory.stat").write_text(
                f"inactive_file {6144 * MIB}\n", encoding="utf-8"
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/\n", encoding="utf-8")

            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            # used = current (10240) - inactive_file (6144) = 4096 -> avail = 16384 - 4096 = 12288
            self.assertEqual(cg["cgroup_avail_mib"], 12288)

            # Missing cgroup_root entirely -> graceful fallback
            cg_none = alr.probe_cgroup_v2_memory(
                cgroup_root=Path(tmp) / "nonexistent",
                proc_cgroup_path=proc_cg,
            )
            self.assertEqual(cg_none, alr._empty_cgroup_info())

    def test_cgroup_v1_only_and_escaping_paths_fall_back(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            _write_cgroup_file(cg_root / "memory.stat", f"anon {MIB}\n")
            _write_cgroup_file(cg_root / "memory.max", f"{1024 * MIB}\n")
            proc_cg = Path(tmp) / "proc_cgroup"

            # cgroup v1-only host: no `0::` line even though files exist.
            proc_cg.write_text(
                "11:memory:/user.slice\n10:cpu:/user.slice\n", encoding="utf-8"
            )
            self.assertEqual(
                alr.probe_cgroup_v2_memory(
                    cgroup_root=cg_root, proc_cgroup_path=proc_cg
                ),
                alr._empty_cgroup_info(),
            )

            # A path escaping the namespace root must never be followed.
            proc_cg.write_text("0::/../../escape.scope\n", encoding="utf-8")
            self.assertFalse(
                alr.probe_cgroup_v2_memory(
                    cgroup_root=cg_root, proc_cgroup_path=proc_cg
                )["cgroup_v2"]
            )

    def test_probe_never_raises(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "job.scope"
            _write_cgroup_file(leaf / "memory.max", f"{8192 * MIB}\n")
            _write_cgroup_file(leaf / "memory.stat", f"anon {MIB}\n")
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/job.scope\n", encoding="utf-8")
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       16777216 kB\nMemAvailable:   12582912 kB\n",
                encoding="utf-8",
            )

            with mock.patch.object(
                alr, "parse_memory_stat", side_effect=RuntimeError("boom")
            ):
                cg = alr.probe_cgroup_v2_memory(
                    cgroup_root=cg_root, proc_cgroup_path=proc_cg
                )
            self.assertEqual(cg, alr._empty_cgroup_info())

            with mock.patch.object(
                alr,
                "_probe_cgroup_v2_memory_impl",
                side_effect=PermissionError("EACCES"),
            ):
                hw = alr.probe_host_hardware(
                    meminfo_path=meminfo,
                    cgroup_root=cg_root,
                    proc_cgroup_path=proc_cg,
                )
                self.assertFalse(hw["cgroup_v2"])
                self.assertEqual(hw["mem_total_mb"], 16384)
                self.assertEqual(hw["mem_avail_mb"], 12288)
                self.assertEqual(alr.format_cgroup_diagnostic_snapshot(), "")


# ---------------------------------------------------------------------------
# CLI, limits, and bounded execution
# ---------------------------------------------------------------------------


class _FakePopen:
    """Records the argv/kwargs of `subprocess.Popen` without running anything."""

    calls: list[tuple[list[str], dict[str, Any]]] = []

    def __init__(self, argv: list[str], **kwargs: Any) -> None:
        _FakePopen.calls.append((list(argv), kwargs))
        self.pid = 2**22 + 12345
        self.returncode = 0

    def wait(self, timeout: float | None = None) -> int:
        return 0

    def poll(self) -> int:
        return 0


class TestCliAndLimits(unittest.TestCase):
    """Tests mode detection, `-M` flag injection, `--probe` / `--print-limits`, and execution."""

    INT_KEYS = (
        "concurrency",
        "cpu_cores",
        "mem_total_mb",
        "mem_avail_mb",
        "threads",
        "memory_max_mb",
        "lean_m_mb",
        "timeout_sec",
        "build_slots",
    )
    OPTIONAL_INT_KEYS = (
        "cgroup_anon_mib",
        "cgroup_shmem_mib",
        "cgroup_anon_shmem_mib",
        "cgroup_file_cache_mib",
        "cgroup_current_mib",
        "cgroup_memory_max_mib",
        "cgroup_avail_mib",
    )

    def _assert_probe_json_schema(self, data: dict[str, Any]) -> None:
        for key in self.INT_KEYS:
            self.assertIn(key, data)
            self.assertIsInstance(data[key], int, key)
            self.assertNotIsInstance(data[key], bool, key)
        self.assertIsInstance(data["mode"], str)
        self.assertIsInstance(data["systemd_user_scope"], bool)
        self.assertIsInstance(data["cgroup_v2"], bool)
        self.assertTrue(
            data["cgroup_path"] is None or isinstance(data["cgroup_path"], str)
        )
        for key in self.OPTIONAL_INT_KEYS:
            self.assertIn(key, data)
            value = data[key]
            self.assertTrue(
                value is None
                or (isinstance(value, int) and not isinstance(value, bool)),
                f"{key}={value!r}",
            )

    def test_detect_mode_and_inject_lean_m_flag(self) -> None:
        self.assertEqual(alr.detect_mode(["lean", "Foo.lean"], "auto"), "file")
        self.assertEqual(
            alr.detect_mode(["lake", "env", "lean", "Foo.lean"], "auto"),
            "file",
        )
        self.assertEqual(
            alr.detect_mode(["lean", "--run", "Foo.lean"], "auto"), "build"
        )
        self.assertEqual(alr.detect_mode(["lake", "build"], "auto"), "build")
        self.assertEqual(
            alr.detect_mode(["lake", "build"], "file"), "file"
        )

        self.assertEqual(
            alr.inject_lean_m_flag(["lean", "Foo.lean"], 4096),
            ["lean", "-M", "4096", "Foo.lean"],
        )
        self.assertEqual(
            alr.inject_lean_m_flag(["lake", "env", "lean", "Foo.lean"], 4096),
            ["lake", "env", "lean", "-M", "4096", "Foo.lean"],
        )
        self.assertEqual(
            alr.inject_lean_m_flag(["lean", "-M", "2048", "Foo.lean"], 4096),
            ["lean", "-M", "2048", "Foo.lean"],
        )
        self.assertEqual(
            alr.inject_lean_m_flag(["lean", "-M2048", "Foo.lean"], 4096),
            ["lean", "-M2048", "Foo.lean"],
        )
        self.assertEqual(
            alr.inject_lean_m_flag(["lake", "build"], 4096),
            ["lake", "build"],
        )

    def test_probe_and_print_limits_cli_and_json(self) -> None:
        """Live host probe: both flags succeed and keep the full JSON schema."""
        for flag in ("--probe", "--print-limits"):
            buf = io.StringIO()
            with mock.patch("sys.stdout", buf):
                rc = alr.main([flag, "--json"])
            self.assertEqual(rc, 0)
            self._assert_probe_json_schema(json.loads(buf.getvalue()))

            text_buf = io.StringIO()
            with mock.patch("sys.stdout", text_buf):
                rc_txt = alr.main([flag])
            self.assertEqual(rc_txt, 0)
            self.assertIn("Cgroup v2", text_buf.getvalue())

    def test_probe_and_print_limits_are_identical_aliases(self) -> None:
        outputs: dict[tuple[str, bool], str] = {}
        fixed_env = alr.compute_limits(dict(FIXED_HW), mode="build", concurrency=2)
        with mock.patch.object(alr, "probe_host_envelope", return_value=fixed_env):
            for flag in ("--probe", "--print-limits"):
                for as_json in (False, True):
                    buf = io.StringIO()
                    argv = [flag, "--concurrency", "2"] + (
                        ["--json"] if as_json else []
                    )
                    with mock.patch("sys.stdout", buf):
                        self.assertEqual(alr.main(argv), 0)
                    outputs[(flag, as_json)] = buf.getvalue()

        self.assertEqual(outputs[("--probe", False)], outputs[("--print-limits", False)])
        self.assertEqual(outputs[("--probe", True)], outputs[("--print-limits", True)])

        data = json.loads(outputs[("--probe", True)])
        self._assert_probe_json_schema(data)
        for key, value in fixed_env.items():
            self.assertEqual(data[key], value, key)
        self.assertEqual(data["mem_total_mb"], 32768)
        self.assertEqual(data["c_high_mb"], 20480)
        self.assertTrue(data["is_cg_capped"])
        self.assertFalse(data["systemd_user_scope"])

        text = outputs[("--probe", False)]
        self.assertIn("Cgroup v2 Envelope : regime=capped", text)
        self.assertIn("W_slice_max=", text)
        self.assertIn(f"(mode=build, W={data['w_eff']})", text)

    def test_systemd_scope_keeps_memory_max_and_zero_swap(self) -> None:
        _FakePopen.calls = []
        with tempfile.TemporaryDirectory(prefix="anneal-scope-rt-") as rt_tmp:
            rt_path = Path(rt_tmp)
            limits = alr.compute_workload_memory_envelope(
                cpu_cores=int(FIXED_HW["cpu_cores"]),
                mem_total_mb=int(FIXED_HW["mem_total_mb"]),
                mem_avail_mb=int(FIXED_HW["mem_avail_mb"]),
                user_systemd_active=True,
                t_cg_is_user_service=True,
                cli_concurrency=2,
                mode="file",
                runtime_base=str(rt_path),
            )
            with mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
                 mock.patch.object(alr, "resolve_runtime_base", return_value=(rt_path, True)), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc = alr.main(
                    [
                        "--mode",
                        "file",
                        "--concurrency",
                        "2",
                        "--no-slot-lock",
                        "--",
                        "lean",
                        "Foo.lean",
                    ]
                )
        self.assertEqual(rc, 0)
        self.assertEqual(len(_FakePopen.calls), 1)
        argv, kwargs = _FakePopen.calls[0]
        self.assertEqual(argv[:4], ["/usr/bin/systemd-run", "--user", "--scope", "--collect"])
        self.assertIn("--quiet", argv)
        self.assertIn("--slice=anneal-workloads.slice", argv)
        self.assertIn(f"MemoryMax={limits['memory_max_mb']}M", argv)
        self.assertIn("MemorySwapMax=0", argv)
        self.assertIn("OOMPolicy=kill", argv)
        self.assertIn(f"CPUQuota={limits['threads'] * 100}%", argv)
        self.assertIn(f"RuntimeMaxSec={limits['timeout_sec'] + 5}s", argv)
        sep_idx = argv.index("--")
        inner = argv[sep_idx + 1 :]
        self.assertIn("oom_score_adj", inner[2])
        self.assertEqual(inner[4:], ["lean", "-M", str(limits["lean_m_mb"]), "Foo.lean"])
        self.assertTrue(kwargs.get("start_new_session"))
        self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_IN_SCOPE"], "1")
        self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_ACTIVE"], "1")
        expected_lean_threads = str(
            alr._resolve_thread_env(limits["threads"], limits["is_cg_capped"])["LEAN_NUM_THREADS"]
        )
        self.assertEqual(kwargs["env"]["LEAN_NUM_THREADS"], expected_lean_threads)

    def test_run_bounded_command_success_and_timeout(self) -> None:
        rc_file = alr.main(
            ["--mode", "file", "--no-slot-lock", "--concurrency", "1", "--", "true"]
        )
        self.assertEqual(rc_file, 0)

        rc_build = alr.main(
            [
                "--mode",
                "build",
                "--no-slot-lock",
                "--concurrency",
                "1",
                "--",
                "true",
            ]
        )
        self.assertEqual(rc_build, 0)

        rc_exit = alr.main(
            ["--no-slot-lock", "--concurrency", "1", "--", "sh", "-c", "exit 3"]
        )
        self.assertEqual(rc_exit, 3)

        err_buf = io.StringIO()
        with mock.patch("sys.stderr", err_buf), mock.patch.object(
            alr, "probe_cgroup_v2_memory", return_value=dict(FAKE_CGROUP_INFO)
        ):
            rc_timeout = alr.main(
                [
                    "--mode",
                    "file",
                    "--timeout",
                    "1",
                    "--no-slot-lock",
                    "--",
                    "python3",
                    "-c",
                    "import time; time.sleep(10)",
                ]
            )
        self.assertEqual(rc_timeout, 124)
        err = err_buf.getvalue()
        self.assertIn("Command timed out after 1s", err)
        self.assertIn(
            "Cgroup v2 Snapshot : anon+shmem=1234M, file=5678M, current=6912M, "
            "memory.max=unbounded",
            err,
        )

    def test_in_process_passthrough_cannot_replace_the_test_runner(self) -> None:
        """A leaked `ANNEAL_LEAN_RUN_IN_SCOPE=1` fails loudly instead of `exec`ing the
        command over the unittest runner (which would end the run early with exit 0)."""
        self.assertNotIn("ANNEAL_LEAN_RUN_IN_SCOPE", os.environ)
        # Check the guards before provoking the pass-through: without them the call below
        # would really replace this process.  The direct calls name a missing binary, so
        # even an unguarded primitive could only raise.
        self.assertEqual(len(_EXEC_GUARDS), len(_GUARDED_EXEC_FUNCTIONS))
        missing_bin = "/nonexistent/anneal-test-exec"
        for name, call_args in (
            ("execv", (missing_bin, ["anneal-test-exec"])),
            ("execve", (missing_bin, ["anneal-test-exec"], {})),
            ("execvp", (missing_bin, ["anneal-test-exec"])),
            ("execvpe", (missing_bin, ["anneal-test-exec"], {})),
        ):
            self.assertIsInstance(getattr(os, name), mock.Mock, name)
            with self.assertRaisesRegex(AssertionError, "replace the unittest runner"):
                getattr(os, name)(*call_args)
        for name, call_args in (
            ("execl", (missing_bin, "anneal-test-exec")),
            ("execle", (missing_bin, "anneal-test-exec", {})),
            ("execlp", (missing_bin, "anneal-test-exec")),
            ("execlpe", (missing_bin, "anneal-test-exec", {})),
        ):
            with self.assertRaisesRegex(AssertionError, "replace the unittest runner"):
                getattr(os, name)(*call_args)
        with mock.patch.dict(os.environ, {"ANNEAL_LEAN_RUN_IN_SCOPE": "1"}):
            with self.assertRaisesRegex(AssertionError, "replace the unittest runner"):
                alr.main(["--mode", "file", "--no-slot-lock", "--", "true"])
        self.assertNotIn("ANNEAL_LEAN_RUN_IN_SCOPE", os.environ)

    def test_command_execution_leaves_live_user_systemd_alone(self) -> None:
        """Under the isolated module-wide `XDG_CONFIG_HOME`, running a command neither
        rewrites `anneal-workloads.slice` nor reloads the host's `systemd --user`."""
        if _SLICE_UNIT_SEED is None:
            self.skipTest("no delegated systemd --user: the slice unit is never reconciled")
        unit = alr._workloads_slice_unit_path()
        assert _XDG_TMPDIR is not None
        self.assertEqual(unit.parents[2], Path(_XDG_TMPDIR.name))
        before = _file_identity(unit)
        self.assertEqual(before[2], _SLICE_UNIT_SEED)

        real_run = subprocess.run
        seen: list[list[str]] = []

        def spy(argv: list[str], *args: Any, **kwargs: Any) -> Any:
            seen.append([str(a) for a in argv])
            return real_run(argv, *args, **kwargs)

        with mock.patch.object(alr.subprocess, "run", side_effect=spy):
            rc = alr.main(
                ["--mode", "file", "--no-slot-lock", "--concurrency", "1", "--", "true"]
            )
        self.assertEqual(rc, 0)
        self.assertEqual([argv for argv in seen if "daemon-reload" in argv], [])
        self.assertEqual(_file_identity(unit), before)

        # Positive control: the same run under an *unseeded* `XDG_CONFIG_HOME` does
        # reconcile the unit (reload stubbed out), so the checks above are not vacuous.
        seen.clear()

        def stub(argv: list[str], *args: Any, **kwargs: Any) -> Any:
            seen.append([str(a) for a in argv])
            if "daemon-reload" in seen[-1]:
                return subprocess.CompletedProcess(argv, 0, "", "")
            return real_run(argv, *args, **kwargs)

        with tempfile.TemporaryDirectory(prefix="anneal-unseeded-xdg-") as empty_xdg:
            with mock.patch.dict(os.environ, {"XDG_CONFIG_HOME": empty_xdg}), mock.patch.object(
                alr.subprocess, "run", side_effect=stub
            ):
                rc = alr.main(
                    ["--mode", "file", "--no-slot-lock", "--concurrency", "1", "--", "true"]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len([argv for argv in seen if "daemon-reload" in argv]), 1)
            written = Path(empty_xdg) / "systemd" / "user" / "anneal-workloads.slice"
            self.assertEqual(written.read_text(encoding="utf-8"), _SLICE_UNIT_SEED)

    def test_timeout_captures_cgroup_snapshot_before_terminating_process(self) -> None:
        """On timeout, the live child scope (`pid=proc.pid`) must be sampled before `_kill_systemd_scope`."""
        events: list[tuple[str, int | None]] = []
        orig_snap = alr.format_cgroup_diagnostic_snapshot
        orig_kill = alr._kill_systemd_scope

        def spy_snap(
            cg: dict[str, Any] | None = None, pid: int | None = None
        ) -> str:
            events.append(("snap", pid))
            return orig_snap(cg=dict(FAKE_CGROUP_INFO), pid=pid)

        def spy_kill(unit_name, proc, rt_base, sock_alive, grace_sec=2.0) -> None:
            events.append(("term", proc.pid))
            orig_kill(unit_name, proc, rt_base, sock_alive, grace_sec=grace_sec)

        err_buf = io.StringIO()
        with mock.patch("sys.stderr", err_buf), mock.patch.object(
            alr, "format_cgroup_diagnostic_snapshot", side_effect=spy_snap
        ), mock.patch.object(
            alr, "_kill_systemd_scope", side_effect=spy_kill
        ):
            rc = alr.main(
                [
                    "--mode",
                    "file",
                    "--timeout",
                    "1",
                    "--no-slot-lock",
                    "--",
                    "python3",
                    "-c",
                    "import time; time.sleep(10)",
                ]
            )
        self.assertEqual(rc, 124)
        self.assertEqual([e[0] for e in events], ["snap", "term"])
        self.assertIsNotNone(events[0][1])
        self.assertEqual(events[0][1], events[1][1])

    def test_snapshot_probes_child_pid_cgroup_first(self) -> None:
        if not Path("/proc/self/cgroup").is_file():
            self.skipTest("requires Linux /proc/<pid>/cgroup")
        child = subprocess.Popen(
            [sys.executable, "-c", "import time; time.sleep(30)"],
            stdin=subprocess.DEVNULL,
        )
        try:
            probed: list[Path] = []

            def spy(
                cgroup_root: Path = Path("/sys/fs/cgroup"),
                proc_cgroup_path: Path = Path("/proc/self/cgroup"),
            ) -> dict[str, Any]:
                probed.append(proc_cgroup_path)
                return dict(FAKE_CGROUP_INFO)

            with mock.patch.object(alr, "probe_cgroup_v2_memory", side_effect=spy):
                snap = alr.format_cgroup_diagnostic_snapshot(pid=child.pid)
            self.assertEqual(probed, [Path(f"/proc/{child.pid}/cgroup")])
            self.assertIn("anon+shmem=1234M", snap)
        finally:
            child.kill()
            child.wait()

    def test_timeout_snapshot_samples_live_child_scope(self) -> None:
        """End to end: the 124 snapshot reports the child's own systemd scope
        (its `MemoryMax` and resident `anon` heap), sampled before the kill."""
        if not sys.platform.startswith("linux") or not alr.systemd_user_scope_available():
            self.skipTest("systemd-run --user --scope unavailable")
        err_buf = io.StringIO()
        with mock.patch("sys.stderr", err_buf):
            rc = alr.main(
                [
                    "--mode",
                    "file",
                    "--timeout",
                    "3",
                    "--memory-max-mb",
                    "1536",
                    "--no-slot-lock",
                    "--",
                    sys.executable,
                    "-c",
                    "import time; b = bytearray(128 * 1024 * 1024); time.sleep(30)",
                ]
            )
        self.assertEqual(rc, 124)
        err = err_buf.getvalue()
        self.assertIn("memory.max=1536M (avail=", err)
        match = re.search(r"Cgroup v2 Snapshot : anon\+shmem=(\d+)M", err)
        self.assertIsNotNone(match, err)
        assert match is not None
        self.assertGreaterEqual(int(match.group(1)), 120)

    def test_oom_exit_137_diagnostic_includes_cgroup_snapshot(self) -> None:
        err_buf = io.StringIO()
        with mock.patch("sys.stderr", err_buf), mock.patch.object(
            alr, "probe_cgroup_v2_memory", return_value=dict(FAKE_CGROUP_INFO)
        ), mock.patch.object(alr, "stamp_last_oom"):
            rc = alr.main(
                ["--mode", "file", "--no-slot-lock", "--", "sh", "-c", "exit 137"]
            )
        self.assertEqual(rc, 137)
        err = err_buf.getvalue()
        self.assertIn("terminated by the OS memory guard", err)
        self.assertIn("MemorySwapMax=0", err)
        self.assertIn("Cgroup v2 Snapshot : anon+shmem=1234M, file=5678M", err)


class TestCallerLoweredThreadCount(unittest.TestCase):
    """A caller's lower positive `LEAN_NUM_THREADS` is what the command runs with and what
    the timeout / OOM diagnostics report, never the envelope's larger thread budget."""

    THREAD_VARS = ("LEAN_NUM_THREADS", "CARGO_BUILD_JOBS", "RAYON_NUM_THREADS")

    def _limits(self, cpu_cores: int, mode: str = "file", **overrides: Any) -> dict[str, Any]:
        """Synthetic uncapped host envelope whose thread budget is `cpu_cores`."""
        limits = alr.compute_workload_memory_envelope(
            cpu_cores=cpu_cores,
            mem_total_mb=262144,
            mem_avail_mb=200000,
            user_systemd_active=False,
            cli_concurrency=1,
            mode=mode,
        )
        self.assertEqual(limits["threads"], cpu_cores)
        self.assertFalse(limits["is_cg_capped"])
        self.assertFalse(limits["user_systemd_active"])
        limits.update(overrides)
        return limits

    def _run(
        self,
        limits: dict[str, Any] | list[dict[str, Any]],
        argv: list[str],
        thread_env: dict[str, str],
        *,
        direct: bool = False,
    ) -> tuple[int, str, list[dict[str, str]]]:
        """Runs `alr.main(argv)` (or `run_bounded_command` when `direct`) against synthetic
        `limits` with exactly `thread_env` of the three thread variables exported.

        Returns `(exit code, stderr, environments of the launched commands)`."""
        real_popen = subprocess.Popen
        child_envs: list[dict[str, str]] = []

        def spy_popen(popen_argv: Any, *args: Any, **kwargs: Any) -> Any:
            env = kwargs.get("env")
            if env is not None and env.get("ANNEAL_LEAN_RUN_IN_SCOPE") == "1":
                child_envs.append(dict(env))
            return real_popen(popen_argv, *args, **kwargs)

        probe_replies = [dict(lim) for lim in (limits if isinstance(limits, list) else [limits])]
        probe_calls = 0

        def fake_probe(**kwargs: Any) -> dict[str, Any]:
            nonlocal probe_calls
            reply = dict(probe_replies[min(probe_calls, len(probe_replies) - 1)])
            probe_calls += 1
            # Like the real probe, honor `--timeout` (`override_timeout_sec`).
            override_timeout = kwargs.get("override_timeout_sec")
            if override_timeout is not None and override_timeout > 0:
                reply["timeout_sec"] = int(override_timeout)
            return reply

        err_buf = io.StringIO()
        with contextlib.ExitStack() as stack:
            stack.enter_context(mock.patch.dict(os.environ, thread_env))
            for var in self.THREAD_VARS:
                if var not in thread_env:
                    os.environ.pop(var, None)
            stack.enter_context(mock.patch.object(alr, "probe_host_envelope", side_effect=fake_probe))
            stack.enter_context(
                mock.patch.object(alr, "probe_cgroup_v2_memory", return_value=dict(FAKE_CGROUP_INFO))
            )
            stack.enter_context(mock.patch.object(alr, "stamp_last_oom"))
            stack.enter_context(mock.patch.object(alr, "_try_oom_offload", return_value=None))
            stack.enter_context(mock.patch.object(alr.subprocess, "Popen", side_effect=spy_popen))
            stack.enter_context(mock.patch("sys.stderr", err_buf))
            if direct:
                rc = alr.run_bounded_command(
                    argv,
                    probe_replies[0],
                    use_slot_lock=False,
                    probe_fn=fake_probe,
                    evict_fn=lambda _limits: True,
                )
            else:
                rc = alr.main(argv)
        return rc, err_buf.getvalue(), child_envs

    def test_oversized_thread_counts_fall_back_to_the_budget_without_raising(self) -> None:
        parse = alr._parse_positive_thread_count
        limit = alr._MAX_THREAD_COUNT_DIGITS
        self.assertEqual(limit, 9)
        # Up to `limit` significant digits parse; leading zeros are not significant.
        self.assertEqual(parse("9" * limit), 10**limit - 1)
        self.assertEqual(parse("0" * 5000 + "8"), 8)
        self.assertEqual(parse(" 007 "), 7)
        # All-zero strings of any length are not positive.
        for zeros in ("0", "000", "0" * 5000):
            self.assertIsNone(parse(zeros), len(zeros))
        # One digit more overflows the tools' 32-bit job counts, and past
        # `sys.get_int_max_str_digits()` (4300) digits `int()` raises `ValueError`.
        oversized = ("1" + "0" * limit, "9" * 4300, "9" * 4301, "9" * 20000, "0" * 3 + "9" * 5000)
        for raw in oversized:
            self.assertIsNone(parse(raw), len(raw))
        for capped in (False, True):
            for raw in oversized:
                env = dict.fromkeys(self.THREAD_VARS, raw)
                self.assertEqual(
                    alr._resolve_thread_env(3, capped, env),
                    dict.fromkeys(self.THREAD_VARS, 3),
                    (capped, len(raw)),
                )
                self.assertEqual(alr.format_threads_diagnostic(3, env), "threads=3", (capped, len(raw)))
        # The child environment never carries the oversized value through.
        with mock.patch.dict(os.environ, dict.fromkeys(self.THREAD_VARS, "9" * 5000)):
            child = alr._build_child_env(
                threads=4,
                lean_m_mb=1024,
                is_cg_capped=False,
                runtime_base=Path("/tmp"),
                user_systemd_sock_alive=False,
            )
        self.assertEqual({var: child[var] for var in self.THREAD_VARS}, dict.fromkeys(self.THREAD_VARS, "4"))

    def test_resolve_thread_env_keeps_lower_positive_caller_values(self) -> None:
        resolve = alr._resolve_thread_env
        self.assertEqual(alr._THREAD_ENV_VARS, self.THREAD_VARS)
        for capped in (False, True):
            for budget in (1, 3, 64):
                at_budget = dict.fromkeys(self.THREAD_VARS, budget)
                # Unset, blank, non-numeric, zero, negative, signed, underscore, non-ASCII
                # digit, or non-ASCII whitespace values: fall back to the envelope's budget.
                self.assertEqual(resolve(budget, capped, {}), at_budget)
                for raw in (
                    "",
                    "   ",
                    "abc",
                    "1.5",
                    "0",
                    "-2",
                    "+1",
                    "1_2",
                    "\u0661",
                    "\u00a01\u00a0",
                    "\u20032",
                    "\u30004",
                    "\x851",
                ):
                    env = dict.fromkeys(self.THREAD_VARS, raw)
                    self.assertEqual(resolve(budget, capped, env), at_budget, (capped, budget, raw))
                # A positive value at or below the budget always wins, in both regimes.
                for raw, want in (("1", 1), (" 1 ", 1), (str(budget), budget)):
                    env = dict.fromkeys(self.THREAD_VARS, raw)
                    self.assertEqual(
                        resolve(budget, capped, env),
                        dict.fromkeys(self.THREAD_VARS, want),
                        (capped, budget, raw),
                    )
        # Defensive clamp: a non-positive budget still yields at least 1 thread.
        for bad_budget in (0, -3):
            self.assertEqual(resolve(bad_budget, True, {}), dict.fromkeys(self.THREAD_VARS, 1))
            self.assertEqual(
                resolve(bad_budget, True, {"LEAN_NUM_THREADS": "4"}),
                dict.fromkeys(self.THREAD_VARS, 1),
            )
            self.assertEqual(alr.format_threads_diagnostic(bad_budget, None), "threads=1")
            self.assertEqual(
                alr.format_threads_diagnostic(bad_budget, {"LEAN_NUM_THREADS": "4"}),
                "threads=4, thread_budget=1",
            )
        # A value above the budget is clamped on a memory-capped slice only.
        self.assertEqual(resolve(3, True, {"LEAN_NUM_THREADS": "64"})["LEAN_NUM_THREADS"], 3)
        self.assertEqual(resolve(3, False, {"LEAN_NUM_THREADS": "64"})["LEAN_NUM_THREADS"], 64)
        # Each variable is resolved on its own.
        self.assertEqual(
            resolve(8, True, {"LEAN_NUM_THREADS": "1", "CARGO_BUILD_JOBS": "4"}),
            {"LEAN_NUM_THREADS": 1, "CARGO_BUILD_JOBS": 4, "RAYON_NUM_THREADS": 8},
        )
        # Default source is the ambient environment, which is only read.
        with mock.patch.dict(os.environ, {"LEAN_NUM_THREADS": "1"}):
            for var in self.THREAD_VARS[1:]:
                os.environ.pop(var, None)
            before = dict(os.environ)
            self.assertEqual(
                resolve(64, False),
                {"LEAN_NUM_THREADS": 1, "CARGO_BUILD_JOBS": 64, "RAYON_NUM_THREADS": 64},
            )
            self.assertEqual(dict(os.environ), before)

    def test_build_child_env_and_diagnostic_field_report_the_lowered_count(self) -> None:
        for budget in (3, 64):
            for capped in (False, True):
                base_env = {"PATH": "/usr/bin", "LEAN_NUM_THREADS": "1"}
                env = alr._build_child_env(
                    threads=budget,
                    lean_m_mb=1024,
                    is_cg_capped=capped,
                    runtime_base=Path("/tmp"),
                    user_systemd_sock_alive=False,
                    base_env=base_env,
                )
                self.assertEqual(base_env, {"PATH": "/usr/bin", "LEAN_NUM_THREADS": "1"})
                self.assertEqual(env["LEAN_NUM_THREADS"], "1")
                self.assertEqual(env["CARGO_BUILD_JOBS"], str(budget))
                self.assertEqual(env["RAYON_NUM_THREADS"], str(budget))
                self.assertEqual(
                    alr.format_threads_diagnostic(budget, env), f"threads=1, thread_budget={budget}"
                )
        # No caller value: the budget itself, with no separate budget field.
        env = alr._build_child_env(
            threads=3,
            lean_m_mb=1024,
            is_cg_capped=True,
            runtime_base=Path("/tmp"),
            user_systemd_sock_alive=False,
            base_env={"PATH": "/usr/bin"},
        )
        self.assertEqual([env[var] for var in self.THREAD_VARS], ["3", "3", "3"])
        self.assertEqual(alr.format_threads_diagnostic(3, env), "threads=3")
        # A larger caller value: clamped (and reported as the budget) on a capped slice,
        # kept (and reported with the budget next to it) on an uncapped host.
        for capped, lean_threads, diag in (
            (True, "3", "threads=3"),
            (False, "64", "threads=64, thread_budget=3"),
        ):
            env = alr._build_child_env(
                threads=3,
                lean_m_mb=1024,
                is_cg_capped=capped,
                runtime_base=Path("/tmp"),
                user_systemd_sock_alive=False,
                base_env={"PATH": "/usr/bin", "LEAN_NUM_THREADS": "64"},
            )
            self.assertEqual(env["LEAN_NUM_THREADS"], lean_threads)
            self.assertEqual(alr.format_threads_diagnostic(3, env), diag)
        # Without a usable child value the field falls back to the budget.
        for child_env in (
            None,
            {},
            {"LEAN_NUM_THREADS": ""},
            {"LEAN_NUM_THREADS": "x"},
            {"LEAN_NUM_THREADS": "0"},
            {"LEAN_NUM_THREADS": "-1"},
            {"LEAN_NUM_THREADS": "+1"},
            {"LEAN_NUM_THREADS": "1_2"},
            {"LEAN_NUM_THREADS": "\u0661"},
            {"LEAN_NUM_THREADS": "\u00a01\u00a0"},
            {"LEAN_NUM_THREADS": "\u20031"},
        ):
            self.assertEqual(alr.format_threads_diagnostic(3, child_env), "threads=3", child_env)

    def test_build_child_env_exports_slots_and_mem_mb_overwriting_stale(self) -> None:
        """`_build_child_env` exports integer-formatted `ANNEAL_LEAN_RUN_SLOTS`
        and `ANNEAL_LEAN_RUN_MEM_MB` and overwrites any stale inherited values.
        """
        base_env = {
            "PATH": "/usr/bin",
            "ANNEAL_LEAN_RUN_SLOTS": "99",
            "ANNEAL_LEAN_RUN_MEM_MB": "999999",
        }
        child = alr._build_child_env(
            threads=4,
            lean_m_mb=3072,
            is_cg_capped=False,
            runtime_base=Path("/tmp"),
            user_systemd_sock_alive=False,
            base_env=base_env,
            granted_slots=3,
            memory_max_mb=4096,
        )
        self.assertEqual(base_env["ANNEAL_LEAN_RUN_SLOTS"], "99")
        self.assertEqual(base_env["ANNEAL_LEAN_RUN_MEM_MB"], "999999")
        self.assertEqual(child["ANNEAL_LEAN_RUN_SLOTS"], "3")
        self.assertEqual(child["ANNEAL_LEAN_RUN_MEM_MB"], "4096")
        self.assertEqual(child["ANNEAL_LEAN_RUN_LEAN_M_MB"], "3072")

        zero_child = alr._build_child_env(
            threads=1,
            lean_m_mb=0,
            is_cg_capped=True,
            runtime_base=Path("/tmp"),
            user_systemd_sock_alive=False,
            base_env=base_env,
            granted_slots=0,
            memory_max_mb=0,
        )
        self.assertEqual(zero_child["ANNEAL_LEAN_RUN_SLOTS"], "0")
        self.assertEqual(zero_child["ANNEAL_LEAN_RUN_MEM_MB"], "0")

        neg_child = alr._build_child_env(
            threads=1,
            lean_m_mb=-5,
            is_cg_capped=True,
            runtime_base=Path("/tmp"),
            user_systemd_sock_alive=False,
            base_env=base_env,
            granted_slots=-2,
            memory_max_mb=-10,
        )
        self.assertEqual(neg_child["ANNEAL_LEAN_RUN_SLOTS"], "0")
        self.assertEqual(neg_child["ANNEAL_LEAN_RUN_MEM_MB"], "0")
        self.assertEqual(neg_child["ANNEAL_LEAN_RUN_LEAN_M_MB"], "0")

    def test_systemd_scope_and_direct_exec_export_budget_env_vars(self) -> None:
        """Both `systemd-run --user --scope` and direct non-systemd execution
        export `ANNEAL_LEAN_RUN_SLOTS` (0 for unslotted/`--no-slot-lock`, 1 for
        shared-slot, `build_slots` for `--exclusive`) and
        `ANNEAL_LEAN_RUN_MEM_MB` (`memory_max_mb`), overwriting stale values.
        """
        stale_env = {
            "ANNEAL_LEAN_RUN_SLOTS": "99",
            "ANNEAL_LEAN_RUN_MEM_MB": "999999",
        }

        with tempfile.TemporaryDirectory(prefix="anneal-slots-rt-") as rt_tmp:
            rt_path = Path(rt_tmp)

            # 1. `systemd-run --user --scope` shared-slot build -> SLOTS=1.
            _FakePopen.calls = []
            scope_limits = alr.compute_workload_memory_envelope(
                cpu_cores=int(FIXED_HW["cpu_cores"]),
                mem_total_mb=int(FIXED_HW["mem_total_mb"]),
                mem_avail_mb=int(FIXED_HW["mem_avail_mb"]),
                user_systemd_active=True,
                t_cg_is_user_service=True,
                cli_concurrency=3,
                mode="build",
                runtime_base=str(rt_path),
            )
            self.assertEqual(scope_limits["build_slots"], 3)
            with mock.patch.dict(os.environ, stale_env, clear=False), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=scope_limits), \
                 mock.patch.object(alr, "resolve_runtime_base", return_value=(rt_path, True)), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr, "_evict_lsp_workers", return_value=False), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc = alr.main(
                    ["--mode", "build", "--concurrency", "3", "--", "true"]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len(_FakePopen.calls), 1)
            argv, kwargs = _FakePopen.calls[0]
            self.assertEqual(argv[:4], ["/usr/bin/systemd-run", "--user", "--scope", "--collect"])
            self.assertIn(f"MemoryMax={scope_limits['memory_max_mb']}M", argv)
            self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_SLOTS"], "1")
            self.assertEqual(
                kwargs["env"]["ANNEAL_LEAN_RUN_MEM_MB"], str(scope_limits["memory_max_mb"])
            )

            # 2. `systemd-run --user --scope` with `--exclusive` sets
            # SLOTS=build_slots.
            _FakePopen.calls = []
            excl_limits = alr.compute_workload_memory_envelope(
                cpu_cores=int(FIXED_HW["cpu_cores"]),
                mem_total_mb=int(FIXED_HW["mem_total_mb"]),
                mem_avail_mb=int(FIXED_HW["mem_avail_mb"]),
                user_systemd_active=True,
                t_cg_is_user_service=True,
                cli_concurrency=3,
                exclusive=True,
                mode="build",
                runtime_base=str(rt_path),
            )
            self.assertEqual(excl_limits["build_slots"], 3)
            with mock.patch.dict(os.environ, stale_env, clear=False), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=excl_limits), \
                 mock.patch.object(alr, "resolve_runtime_base", return_value=(rt_path, True)), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr, "_evict_lsp_workers", return_value=False), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc = alr.main(
                    ["--mode", "build", "--concurrency", "3", "--exclusive", "--", "true"]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len(_FakePopen.calls), 1)
            argv, kwargs = _FakePopen.calls[0]
            self.assertEqual(argv[:4], ["/usr/bin/systemd-run", "--user", "--scope", "--collect"])
            self.assertEqual(
                kwargs["env"]["ANNEAL_LEAN_RUN_SLOTS"], str(excl_limits["build_slots"])
            )
            self.assertEqual(
                kwargs["env"]["ANNEAL_LEAN_RUN_MEM_MB"], str(excl_limits["memory_max_mb"])
            )

            # 3. `--no-slot-lock` on build mode -> SLOTS=0.
            _FakePopen.calls = []
            with mock.patch.dict(os.environ, stale_env, clear=False), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=scope_limits), \
                 mock.patch.object(alr, "resolve_runtime_base", return_value=(rt_path, True)), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr, "_evict_lsp_workers", return_value=False), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc = alr.main(
                    ["--mode", "build", "--concurrency", "3", "--no-slot-lock", "--", "true"]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len(_FakePopen.calls), 1)
            _, kwargs = _FakePopen.calls[0]
            self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_SLOTS"], "0")
            self.assertEqual(
                kwargs["env"]["ANNEAL_LEAN_RUN_MEM_MB"], str(scope_limits["memory_max_mb"])
            )

            # 4. Direct non-systemd execution (unslotted file mode -> SLOTS=0,
            #    shared-slot build mode -> SLOTS=1, `--exclusive` -> SLOTS=2).
            direct_file = alr.compute_workload_memory_envelope(
                cpu_cores=8,
                mem_total_mb=32768,
                mem_avail_mb=24576,
                user_systemd_active=False,
                t_cg_is_user_service=False,
                cli_concurrency=2,
                mode="file",
                override_mem_mb=6144,
                runtime_base=str(rt_path),
            )
            self.assertEqual(direct_file["build_slots"], 2)
            self.assertEqual(direct_file["memory_max_mb"], 6144)
            _FakePopen.calls = []
            with mock.patch("sys.stderr", io.StringIO()), \
                 mock.patch.dict(os.environ, stale_env, clear=False), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=direct_file), \
                 mock.patch.object(alr, "resolve_runtime_base", return_value=(rt_path, False)), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc = alr.main(
                    [
                        "--mode",
                        "file",
                        "--concurrency",
                        "2",
                        "--memory-max-mb",
                        "6144",
                        "--",
                        "true",
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len(_FakePopen.calls), 1)
            argv, kwargs = _FakePopen.calls[0]
            self.assertEqual(argv[:2], ["/bin/sh", "-c"])
            self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_SLOTS"], "0")
            self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_MEM_MB"], "6144")

            direct_build = alr.compute_workload_memory_envelope(
                cpu_cores=8,
                mem_total_mb=32768,
                mem_avail_mb=24576,
                user_systemd_active=False,
                t_cg_is_user_service=False,
                cli_concurrency=2,
                mode="build",
                override_mem_mb=6144,
                runtime_base=str(rt_path),
            )
            for extra_args, want_slots in (([], "1"), (["--exclusive"], "2"), (["--no-slot-lock"], "0")):
                _FakePopen.calls = []
                with mock.patch("sys.stderr", io.StringIO()), \
                     mock.patch.dict(os.environ, stale_env, clear=False), \
                     mock.patch.object(alr, "probe_host_envelope", return_value=direct_build), \
                     mock.patch.object(alr, "resolve_runtime_base", return_value=(rt_path, False)), \
                     mock.patch.object(alr, "_evict_lsp_workers", return_value=False), \
                     mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                    rc = alr.main(
                        [
                            "--mode",
                            "build",
                            "--concurrency",
                            "2",
                            "--memory-max-mb",
                            "6144",
                            *extra_args,
                            "--",
                            "true",
                        ]
                    )
                self.assertEqual(rc, 0)
                self.assertEqual(len(_FakePopen.calls), 1)
                argv, kwargs = _FakePopen.calls[0]
                self.assertEqual(argv[:2], ["/bin/sh", "-c"])
                self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_SLOTS"], want_slots, extra_args)
                self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_MEM_MB"], "6144", extra_args)

    def test_cpu_quota_stays_at_the_thread_budget(self) -> None:
        with mock.patch.dict(os.environ, {"LEAN_NUM_THREADS": "1"}), mock.patch.object(
            alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"
        ):
            argv, in_scope = alr._build_scope_launch_cmd(
                ["lake", "build"],
                b_max_mb=4096,
                threads=64,
                timeout_sec=60,
                user_systemd_active=True,
                unit_name="anneal-run-test.scope",
            )
        self.assertTrue(in_scope)
        self.assertIn("CPUQuota=6400%", argv)
        self.assertEqual([a for a in argv if a.startswith("CPUQuota=")], ["CPUQuota=6400%"])

    def test_timeout_diagnostic_logs_caller_lowered_lean_num_threads(self) -> None:
        sleeper = ["--mode", "file", "--timeout", "1", "--no-slot-lock", "--", "sleep", "30"]
        for budget in (3, 64):
            rc, err, child_envs = self._run(self._limits(budget), sleeper, {"LEAN_NUM_THREADS": "1"})
            self.assertEqual(rc, 124)
            self.assertEqual(len(child_envs), 1)
            self.assertEqual(child_envs[0]["LEAN_NUM_THREADS"], "1")
            self.assertEqual(child_envs[0]["CARGO_BUILD_JOBS"], str(budget))
            self.assertIn("Command timed out after 1s (mode=file, MemoryMax=", err)
            self.assertIn(f"M, threads=1, thread_budget={budget}).\n", err)
            self.assertNotIn(f"threads={budget}", err)
            self.assertEqual(re.findall(r"\bthreads=(\d+)", err), ["1"])

    def test_timeout_diagnostic_without_caller_value_logs_the_budget(self) -> None:
        sleeper = ["--mode", "file", "--timeout", "1", "--no-slot-lock", "--", "sleep", "30"]
        rc, err, child_envs = self._run(self._limits(3), sleeper, {})
        self.assertEqual(rc, 124)
        self.assertEqual([env["LEAN_NUM_THREADS"] for env in child_envs], ["3"])
        self.assertIn("M, threads=3).\n", err)
        self.assertNotIn("thread_budget", err)

    def test_timeout_diagnostic_on_capped_slice_clamps_high_and_rejects_invalid(self) -> None:
        sleeper = ["--mode", "file", "--timeout", "1", "--no-slot-lock", "--", "sleep", "30"]
        capped = self._limits(3, is_cg_capped=True)
        for thread_env, want_threads, want_field in (
            ({"LEAN_NUM_THREADS": "1"}, "1", "threads=1, thread_budget=3"),
            ({"LEAN_NUM_THREADS": "64"}, "3", "threads=3"),
            ({"LEAN_NUM_THREADS": "1_2"}, "3", "threads=3"),
        ):
            rc, err, child_envs = self._run(capped, sleeper, thread_env)
            self.assertEqual(rc, 124, thread_env)
            self.assertEqual([env["LEAN_NUM_THREADS"] for env in child_envs], [want_threads], thread_env)
            self.assertIn(f"M, {want_field}).\n", err, thread_env)
            self.assertEqual(re.findall(r"\bthreads=(\d+)", err), [want_threads], thread_env)

    def test_pressure_abort_diagnostic_logs_effective_lean_num_threads(self) -> None:
        # Watchdog ancestor-pressure aborts report the same effective thread count as
        # timeout / OOM diagnostics.
        capped = self._limits(
            3,
            mode="build",
            is_cg_capped=True,
            user_systemd_active=True,
            t_cg_is_user_service=False,
        )

        class _InstantAbortWatchdog:
            def __init__(self, **_kwargs: Any) -> None:
                pass

            def tick(self, _now: float) -> dict[str, Any]:
                return {"action": "abort_pressure", "tier1_triggered": True, "shed_fired": False, "breach_ticks": 3}

        class _TimeoutOnceProc:
            pid = 424242

            def __init__(self, *_args: Any, **_kwargs: Any) -> None:
                self._done = False

            def wait(self, timeout: float | None = None) -> int:
                if not self._done:
                    self._done = True
                    raise subprocess.TimeoutExpired(cmd=["sleep"], timeout=timeout or 0)
                return -9

            def poll(self) -> int | None:
                return -9 if self._done else None

        for thread_env, want_field in (
            ({"LEAN_NUM_THREADS": "1"}, "threads=1, thread_budget=3"),
            ({}, "threads=3"),
        ):
            err_buf = io.StringIO()
            with contextlib.ExitStack() as stack:
                stack.enter_context(mock.patch.dict(os.environ, thread_env))
                for var in self.THREAD_VARS:
                    if var not in thread_env:
                        os.environ.pop(var, None)
                stack.enter_context(mock.patch.object(alr, "_build_scope_launch_cmd", return_value=(["true"], True)))
                stack.enter_context(mock.patch.object(alr, "BuildWatchdog", _InstantAbortWatchdog))
                stack.enter_context(mock.patch.object(alr.subprocess, "Popen", _TimeoutOnceProc))
                stack.enter_context(mock.patch.object(alr, "_kill_systemd_scope"))
                stack.enter_context(mock.patch.object(alr, "stamp_last_oom"))
                stack.enter_context(mock.patch("sys.stderr", err_buf))
                rc = alr.run_bounded_command(
                    ["lake", "build"],
                    capped,
                    use_slot_lock=False,
                    probe_fn=lambda **_kw: dict(capped),
                    evict_fn=lambda _lim: False,
                )
            self.assertEqual(rc, 137, thread_env)
            err = err_buf.getvalue()
            self.assertIn("USER_SLICE_PRESSURE_ABORT:", err)
            self.assertIn(f"(mode=build, {want_field}, budget_gb=", err, thread_env)

    def test_oom_diagnostic_logs_caller_lowered_lean_num_threads(self) -> None:
        oom = ["--mode", "file", "--no-slot-lock", "--", "sh", "-c", "exit 137"]
        for budget, thread_env, lean_threads, field in (
            (3, {"LEAN_NUM_THREADS": "1"}, "1", "threads=1, thread_budget=3"),
            (64, {"LEAN_NUM_THREADS": "1"}, "1", "threads=1, thread_budget=64"),
            (64, {"LEAN_NUM_THREADS": " 2 "}, "2", "threads=2, thread_budget=64"),
            (3, {}, "3", "threads=3"),
            (3, {"LEAN_NUM_THREADS": "0"}, "3", "threads=3"),
            (3, {"LEAN_NUM_THREADS": "64"}, "64", "threads=64, thread_budget=3"),
        ):
            rc, err, child_envs = self._run(self._limits(budget), oom, thread_env)
            self.assertEqual(rc, 137, thread_env)
            self.assertEqual([env["LEAN_NUM_THREADS"] for env in child_envs], [lean_threads], thread_env)
            self.assertIn("terminated by the OS memory guard (exit 137, MemoryMax=", err)
            self.assertIn(f"MemorySwapMax=0, mode=file, {field}, budget_gb=", err, thread_env)
            self.assertEqual(re.findall(r"\bthreads=(\d+)", err), [lean_threads], thread_env)
        # On a memory-capped slice a larger caller value is clamped to the budget.
        capped = self._limits(3, is_cg_capped=True)
        rc, err, child_envs = self._run(capped, oom, {"LEAN_NUM_THREADS": "64"})
        self.assertEqual(rc, 137)
        self.assertEqual([env["LEAN_NUM_THREADS"] for env in child_envs], ["3"])
        self.assertIn("mode=file, threads=3, budget_gb=", err)
        self.assertNotIn("thread_budget", err)

    def test_oom_retry_diagnostic_reports_the_retry_attempt_threads(self) -> None:
        # Attempt 1 runs under a 64-thread budget, the single on-OOM retry under a re-probed
        # 8-thread budget: the final diagnostic describes the attempt that actually failed last.
        first = self._limits(64, mode="build", memory_max_mb=4096, b_max_evict_mb=8192, skip_evict=True)
        retry = self._limits(8, mode="build", memory_max_mb=8192, b_max_evict_mb=8192, skip_evict=True)
        for thread_env, lean_threads, field in (
            ({"LEAN_NUM_THREADS": "1"}, ["1", "1"], "threads=1, thread_budget=8"),
            ({}, ["64", "8"], "threads=8"),
        ):
            rc, err, child_envs = self._run([first, retry], ["sh", "-c", "exit 137"], thread_env, direct=True)
            self.assertEqual(rc, 137, thread_env)
            self.assertIn("Attempt 1 OOMed at 4096M; evicted LSP workers and retrying once at 8192M", err)
            self.assertEqual([env["LEAN_NUM_THREADS"] for env in child_envs], lean_threads, thread_env)
            self.assertIn(f"MemoryMax=8192M, MemorySwapMax=0, mode=build, {field}, budget_gb=", err, thread_env)
            self.assertNotIn("thread_budget=64", err)

    def test_probe_text_reports_effective_lean_num_threads(self) -> None:
        for limits, cases in (
            (
                self._limits(64, mode="build"),
                (
                    ({"LEAN_NUM_THREADS": "1"}, 1),
                    ({"LEAN_NUM_THREADS": "64"}, 64),
                    ({"LEAN_NUM_THREADS": "128"}, 128),
                    ({}, 64),
                    ({"LEAN_NUM_THREADS": "-1"}, 64),
                    ({"LEAN_NUM_THREADS": "1_2"}, 64),
                ),
            ),
            (
                self._limits(3, mode="build", is_cg_capped=True),
                (
                    ({"LEAN_NUM_THREADS": "1"}, 1),
                    ({"LEAN_NUM_THREADS": "64"}, 3),
                    ({}, 3),
                    ({"LEAN_NUM_THREADS": "0"}, 3),
                    ({"LEAN_NUM_THREADS": "abc"}, 3),
                    ({"LEAN_NUM_THREADS": "\u0661"}, 3),
                ),
            ),
        ):
            budget = limits["threads"]
            for thread_env, lean_threads in cases:
                out = io.StringIO()
                with mock.patch("sys.stdout", out):
                    rc, _err, child_envs = self._run(limits, ["--probe"], thread_env)
                self.assertEqual(rc, 0)
                self.assertEqual(child_envs, [])
                self.assertIn(
                    f"Thread Budget (-j) : {budget} threads (LEAN_NUM_THREADS={lean_threads})\n",
                    out.getvalue(),
                    (limits["is_cg_capped"], thread_env),
                )
                # The JSON contract keeps reporting the envelope's budget.
                out = io.StringIO()
                with mock.patch("sys.stdout", out):
                    rc, _err, _envs = self._run(limits, ["--probe", "--json"], thread_env)
                self.assertEqual(rc, 0)
                self.assertEqual(json.loads(out.getvalue()), limits)


class TestCliSubprocess(unittest.TestCase):
    """Runs `scripts/anneal-lean-run` as a real subprocess (stdin=/dev/null).

    Every subprocess is isolated from the invoking host: ambient `ANNEAL_LEAN_*` /
    `ANNEAL_WORKTREE_*` / `ANNEAL_LSP_*` / `ANNEAL_OOM_*` variables are scrubbed,
    `XDG_CONFIG_HOME` is a fresh empty directory, and `XDG_RUNTIME_DIR` is a fresh
    `0700` directory unless `env_extra` provides an explicit override. Because
    `resolve_runtime_base()` prefers a live `/run/user/<uid>` over `XDG_RUNTIME_DIR`,
    `_cli` additionally runs the script through `_ISOLATED_CLI_SHIM`, which pins build-slot
    counting / locking and OOM memos to that fresh per-invocation directory.
    """

    def _run_isolated(
        self,
        argv: list[str] | Callable[[Path], list[str]],
        env_extra: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        """Run `argv` (or `argv(rt_dir)`, given the fresh per-invocation runtime dir)."""
        with tempfile.TemporaryDirectory(prefix="anneal-cli-xdg-") as xdg_dir, \
             tempfile.TemporaryDirectory(prefix="anneal-cli-rt-") as rt_dir:
            os.chmod(rt_dir, 0o700)
            return subprocess.run(
                argv(Path(rt_dir)) if callable(argv) else argv,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                check=False,
                env=_isolated_cli_env(
                    Path(xdg_dir), env_extra, xdg_runtime_dir=Path(rt_dir)
                ),
                timeout=120,
            )

    def _cli(
        self, *args: str, env_extra: dict[str, str] | None = None
    ) -> subprocess.CompletedProcess[str]:
        return self._run_isolated(
            lambda rt_dir: [
                sys.executable,
                "-B",
                "-c",
                _ISOLATED_CLI_SHIM,
                str(SCRIPT_PATH),
                str(rt_dir),
                *args,
            ],
            env_extra,
        )

    def _direct_cli(
        self, *args: str, env_extra: dict[str, str] | None = None
    ) -> subprocess.CompletedProcess[str]:
        """Execute `scripts/anneal-lean-run` directly via its `#!/usr/bin/env python3`
        shebang (exercising the executable bit and shebang), with `python3` on `PATH`
        applying `_ISOLATED_CLI_SHIM` strictly for `SCRIPT_PATH` using `_run_isolated`'s
        private `rt_dir` and restoring `PATH` so child `python3` commands run normally."""
        with tempfile.TemporaryDirectory(prefix="anneal-cli-bin-") as bin_tmp:
            bin_dir = Path(bin_tmp)
            shim_file = bin_dir / "anneal_lean_run_isolated_cli.py"
            shim_file.write_text(_ISOLATED_CLI_SHIM, encoding="utf-8")
            wrapper = bin_dir / "python3"
            base_path = (
                env_extra["PATH"]
                if env_extra is not None and "PATH" in env_extra
                else os.environ.get("PATH", "")
            )
            path_env = os.pathsep.join(p for p in (str(bin_dir), base_path) if p)
            merged_env = {**(env_extra or {}), "PATH": path_env}

            def _prepare_argv(rt_dir: Path) -> list[str]:
                wrapper.write_text(
                    "#!/bin/sh\n"
                    f'if [ "$1" = {shlex.quote(str(SCRIPT_PATH))} ]; then\n'
                    '  script="$1"; shift\n'
                    f"  PATH={shlex.quote(base_path)}; export PATH\n"
                    f"  exec {shlex.quote(sys.executable)} -B {shlex.quote(str(shim_file))} "
                    f'"$script" {shlex.quote(str(rt_dir))} "$@"\n'
                    "fi\n"
                    f'exec {shlex.quote(sys.executable)} "$@"\n',
                    encoding="utf-8",
                )
                wrapper.chmod(0o700)
                return [str(SCRIPT_PATH), *args]

            return self._run_isolated(_prepare_argv, merged_env)

    def _synthetic_cli(
        self,
        host_root: Path,
        cgroup_name: str,
        *args: str,
        env_extra: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        """`_cli` against synthetic host `host_root` / `cgroup_name` (same isolation)."""
        return self._run_isolated(
            [
                sys.executable,
                "-B",
                "-c",
                _SYNTHETIC_HOST_CLI_SHIM,
                str(SCRIPT_PATH),
                str(host_root),
                cgroup_name,
                *args,
            ],
            env_extra,
        )

    def _probe_json(self, res: subprocess.CompletedProcess[str]) -> dict[str, Any]:
        self.assertEqual(res.returncode, 0, res.stderr)
        data = json.loads(res.stdout)
        self.assertIsInstance(data, dict)
        return data

    def _assert_concurrency(self, data: dict[str, Any], expected: int) -> None:
        for key in ("concurrency", "w_eff", "build_slots"):
            self.assertEqual(data[key], expected, key)

    @staticmethod
    def _host_bounded(requested: int, data: dict[str, Any]) -> int:
        """Concurrency the probed host grants for `requested`: cgroup-capped hosts clamp
        it to `s_heavy_safe`, uncapped hosts honor it."""
        if data["is_cg_capped"]:
            return min(requested, data["s_heavy_safe"])
        return requested

    def test_cli_backward_compatible_probe_and_execution(self) -> None:
        if os.access(SCRIPT_PATH, os.X_OK):
            direct = self._direct_cli("--print-limits", "--json")
            self.assertIn("cgroup_avail_mib", self._probe_json(direct))

        probe = self._cli("--probe")
        self.assertEqual(probe.returncode, 0, probe.stderr)
        self.assertIn("Cgroup v2", probe.stdout)
        self.assertIn("Hard RAM Cap", probe.stdout)

        # An isolated probe sees no host override at all: neither ambient `ANNEAL_*`
        # variables nor `{$XDG_CONFIG_HOME,~/.config}/anneal/concurrency`.
        default = self._probe_json(self._cli("--probe", "--json"))
        self._assert_concurrency(default, 1)
        self.assertEqual(default["mode"], "build")
        self.assertEqual(default["timeout_sec"], 900)

        data = self._probe_json(
            self._cli(
                "--probe",
                "--json",
                env_extra={
                    "ANNEAL_WORKTREE_CONCURRENCY": "2",
                    "ANNEAL_LEAN_MEMORY_MAX_MB": "3000",
                    "ANNEAL_LEAN_TIMEOUT_SEC": "77",
                },
            )
        )
        self._assert_concurrency(data, self._host_bounded(2, data))
        expected_mem = (
            min(3000, data["w_slice_max_mb"]) if data["is_cg_capped"] else 3000
        )
        self.assertEqual(data["memory_max_mb"], expected_mem)
        if data["w_slice_max_mb"] >= 3000:
            self.assertEqual(data["memory_max_mb"], 3000)
        self.assertEqual(data["timeout_sec"], 77)

        # `--unsafe-ignore-cgroup` only lifts the `w_slice_max_mb` clamp on an explicit
        # `--memory-max-mb`.  It neither flips `is_cg_capped` nor un-clamps concurrency, so
        # the sibling probe reports `is_cg_capped is False` / `concurrency == 2` exactly on
        # uncapped hosts and stays clamped to `s_heavy_safe` on capped ones.
        unsafe = self._probe_json(
            self._cli(
                "--unsafe-ignore-cgroup",
                "--probe",
                "--json",
                env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
            )
        )
        self.assertIs(unsafe["is_cg_capped"], data["is_cg_capped"])
        self._assert_concurrency(unsafe, self._host_bounded(2, unsafe))

        over_cap_mb = data["w_slice_max_mb"] + 1024
        capped_data = self._probe_json(
            self._cli(
                "--memory-max-mb",
                str(over_cap_mb),
                "--probe",
                "--json",
                env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
            )
        )
        self.assertEqual(
            capped_data["memory_max_mb"],
            min(over_cap_mb, capped_data["w_slice_max_mb"])
            if capped_data["is_cg_capped"]
            else over_cap_mb,
        )
        self._assert_concurrency(capped_data, self._host_bounded(2, capped_data))

        unsafe_data = self._probe_json(
            self._cli(
                "--unsafe-ignore-cgroup",
                "--memory-max-mb",
                str(over_cap_mb),
                "--probe",
                "--json",
                env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
            )
        )
        self.assertEqual(unsafe_data["memory_max_mb"], over_cap_mb)
        self.assertIs(unsafe_data["is_cg_capped"], data["is_cg_capped"])
        self._assert_concurrency(unsafe_data, self._host_bounded(2, unsafe_data))

        # A populated `$XDG_CONFIG_HOME/anneal/concurrency` is read, and is subject to the
        # same host bound with or without `--unsafe-ignore-cgroup`.
        with tempfile.TemporaryDirectory(prefix="anneal-xdg-cfg-") as cfg_dir:
            _write_cgroup_file(Path(cfg_dir) / "anneal" / "concurrency", "3\n")
            for flags in ((), ("--unsafe-ignore-cgroup",)):
                cfg_data = self._probe_json(
                    self._cli(
                        *flags,
                        "--probe",
                        "--json",
                        env_extra={"XDG_CONFIG_HOME": cfg_dir},
                    )
                )
                self._assert_concurrency(cfg_data, self._host_bounded(3, cfg_data))

        bad_env = self._probe_json(
            self._cli(
                "--probe", "--json", env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "abc"}
            )
        )
        self._assert_concurrency(bad_env, 1)

        flag_data = self._probe_json(
            self._cli(
                "--concurrency", "1", "--memory-max-mb", "2500", "--timeout", "60",
                "--probe", "--json",
            )
        )
        self._assert_concurrency(flag_data, 1)
        self.assertEqual(
            flag_data["memory_max_mb"],
            min(2500, flag_data["w_slice_max_mb"])
            if flag_data["is_cg_capped"]
            else 2500,
        )
        self.assertEqual(flag_data["timeout_sec"], 60)

        # Command-executing runs reconcile `anneal-workloads.slice` under `XDG_CONFIG_HOME`.
        # Give them a seeded one and check they leave it untouched: no rewrite, hence no
        # `systemctl --user daemon-reload` of the host's live user manager.
        with tempfile.TemporaryDirectory(prefix="anneal-cli-run-xdg-") as run_xdg:
            unit = _seed_workloads_slice_unit(Path(run_xdg))
            before = None if unit is None else _file_identity(unit)
            for argv, expected_rc in (
                (["--mode", "file", "--no-slot-lock", "--concurrency", "1", "--", "true"], 0),
                (["--mode", "build", "--no-slot-lock", "--concurrency", "1", "--", "true"], 0),
                (["--no-slot-lock", "--", "sh", "-c", "exit 5"], 5),
            ):
                res = self._cli(*argv, env_extra={"XDG_CONFIG_HOME": run_xdg})
                self.assertEqual(res.returncode, expected_rc, (argv, res.stderr))
            if unit is not None:
                self.assertEqual(_file_identity(unit), before)

        usage = self._cli()
        self.assertEqual(usage.returncode, 2)

    def test_cli_synthetic_hosts_cover_uncapped_and_capped_regimes(self) -> None:
        """Both cgroup regimes through the real CLI, whichever host runs the tests.

        The live probes of `test_cli_backward_compatible_probe_and_execution` only ever see
        the regime of the machine they run on: a cgroup-capped 8 GiB host never reports
        `is_cg_capped == False`, and an uncapped workstation never exercises the
        `s_heavy_safe` clamp.  Here the same subprocess CLI runs against synthetic hosts,
        so `ANNEAL_WORKTREE_CONCURRENCY=2 -> 2` and `$XDG_CONFIG_HOME/anneal/concurrency`
        `3 -> 3` (uncapped) and both `s_heavy_safe` clamps (capped) hold on every machine.
        """
        # host -> concurrency granted for a requested 2 (environment / `--concurrency`)
        # and for a requested 3 (`$XDG_CONFIG_HOME/anneal/concurrency`).
        granted = {"cg_uncapped": (2, 3), "cg_capped_1": (1, 1), "cg_capped_2": (2, 2)}
        with tempfile.TemporaryDirectory(prefix="anneal-synth-host-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            xdg_three = root / "xdg_three"
            _write_cgroup_file(xdg_three / "anneal" / "concurrency", "3\n")
            for cg_name, ceiling_mib, capped, s_heavy_safe in SYNTHETIC_HOSTS:
                _write_synthetic_cgroup_root(root, cg_name, ceiling_mib)
                conc_for_2, conc_for_3 = granted[cg_name]

                def probe(
                    *args: str,
                    env_extra: dict[str, str] | None = None,
                    cg_name: str = cg_name,
                ) -> dict[str, Any]:
                    return self._probe_json(
                        self._synthetic_cli(
                            root, cg_name, *args, "--probe", "--json", env_extra=env_extra
                        )
                    )

                with self.subTest(host=cg_name):
                    default = probe()
                    self.assertIs(default["is_cg_capped"], capped)
                    self.assertEqual(default["s_heavy_safe"], s_heavy_safe)
                    self.assertEqual(default["cpu_cores"], SYNTHETIC_HOST_CORES)
                    self.assertEqual(default["mem_total_mb"], 65536)
                    self._assert_concurrency(default, 1)
                    self.assertEqual(default["timeout_sec"], 900)
                    w_slice_max_mb = default["w_slice_max_mb"]
                    self.assertGreater(w_slice_max_mb, 3000)

                    overridden = probe(
                        env_extra={
                            "ANNEAL_WORKTREE_CONCURRENCY": "2",
                            "ANNEAL_LEAN_MEMORY_MAX_MB": "3000",
                            "ANNEAL_LEAN_TIMEOUT_SEC": "77",
                        }
                    )
                    self._assert_concurrency(overridden, conc_for_2)
                    self.assertEqual(overridden["memory_max_mb"], 3000)
                    self.assertEqual(overridden["timeout_sec"], 77)

                    unsafe = probe(
                        "--unsafe-ignore-cgroup",
                        env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
                    )
                    self.assertIs(unsafe["is_cg_capped"], capped)
                    self._assert_concurrency(unsafe, conc_for_2)

                    self._assert_concurrency(probe("--concurrency", "2"), conc_for_2)

                    for flags in ((), ("--unsafe-ignore-cgroup",)):
                        from_file = probe(
                            *flags, env_extra={"XDG_CONFIG_HOME": str(xdg_three)}
                        )
                        self.assertIs(from_file["is_cg_capped"], capped)
                        self._assert_concurrency(from_file, conc_for_3)

                    # Host concurrency file acts as the floor for env concurrency, while
                    # explicit `--concurrency` during `--probe` overrides `w_eff` yet leaves
                    # `build_slots` pinned to the host file value.
                    file_plus_env = probe(
                        env_extra={
                            "XDG_CONFIG_HOME": str(xdg_three),
                            "ANNEAL_WORKTREE_CONCURRENCY": "2",
                        }
                    )
                    self._assert_concurrency(file_plus_env, conc_for_3)
                    file_plus_cli = probe(
                        "--concurrency",
                        "1",
                        env_extra={"XDG_CONFIG_HOME": str(xdg_three)},
                    )
                    self.assertEqual(file_plus_cli["concurrency"], 1)
                    self.assertEqual(file_plus_cli["w_eff"], 1)
                    self.assertEqual(file_plus_cli["build_slots"], conc_for_3)

                    over_cap_mb = w_slice_max_mb + 1024
                    for clamp_args, clamp_env in (
                        (("--memory-max-mb", str(over_cap_mb)), None),
                        ((), {"ANNEAL_LEAN_MEMORY_MAX_MB": str(over_cap_mb)}),
                    ):
                        clamped = probe(*clamp_args, env_extra=clamp_env)
                        expected_clamped = w_slice_max_mb if capped else over_cap_mb
                        self.assertEqual(clamped["memory_max_mb"], expected_clamped)
                        self.assertEqual(
                            clamped["lean_m_mb"], (75 * expected_clamped) // 100
                        )
                        lifted = probe(
                            "--unsafe-ignore-cgroup", *clamp_args, env_extra=clamp_env
                        )
                        self.assertEqual(lifted["memory_max_mb"], over_cap_mb)
                        self.assertEqual(lifted["lean_m_mb"], (75 * over_cap_mb) // 100)
                        self.assertIs(lifted["is_cg_capped"], capped)
                        self._assert_concurrency(lifted, 1)

    def test_scrubbed_prefixes_cover_every_anneal_variable_of_the_script(self) -> None:
        """An `ANNEAL_*` variable added to `scripts/anneal-lean-run` must be scrubbed too."""
        names = set(
            re.findall(r"ANNEAL_[A-Z0-9_]+", SCRIPT_PATH.read_text(encoding="utf-8"))
        )
        for known in (
            "ANNEAL_WORKTREE_CONCURRENCY",
            "ANNEAL_LEAN_MEMORY_MAX_MB",
            "ANNEAL_LEAN_TIMEOUT_SEC",
            "ANNEAL_LEAN_RUN_IN_SCOPE",
        ):
            self.assertIn(known, names)
        self.assertEqual(
            sorted(n for n in names if not n.startswith(_AMBIENT_ANNEAL_ENV_PREFIXES)),
            [],
        )

    def test_cli_isolation_scrubs_poisoned_ambient_environment(self) -> None:
        """Neither ambient `ANNEAL_*` overrides nor host concurrency files reach `_cli`.

        Runs on an uncapped synthetic host, where a leaked concurrency override would be
        honored verbatim instead of being hidden by a capped host's `s_heavy_safe == 1` clamp.
        """
        ambient_overrides = {
            "ANNEAL_WORKTREE_CONCURRENCY": "6",
            "ANNEAL_LEAN_MEMORY_MAX_MB": "17",
            "ANNEAL_LEAN_TIMEOUT_SEC": "55",
        }
        with tempfile.TemporaryDirectory(prefix="anneal-ambient-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            _write_synthetic_cgroup_root(root, "cg_uncapped", None)
            poisoned_xdg = root / "poisoned_xdg"
            _write_cgroup_file(poisoned_xdg / "anneal" / "concurrency", "7\n")
            poisoned_home = root / "poisoned_home"
            _write_cgroup_file(
                poisoned_home / ".config" / "anneal" / "concurrency", "5\n"
            )
            poison = {
                **ambient_overrides,
                "HOME": str(poisoned_home),
                "XDG_CONFIG_HOME": str(poisoned_xdg),
                "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                "ANNEAL_LEAN_RUN_ACTIVE": "1",
                "ANNEAL_LEAN_RUN_LEAN_M_MB": "99",
                "ANNEAL_LSP_NO_EVICT": "1",
                "ANNEAL_LSP_SOCKET": str(root / "no-such.sock"),
                "ANNEAL_OOM_OFFLOAD_CMD": "false",
            }

            def synthetic(env_extra: dict[str, str] | None = None) -> dict[str, Any]:
                return self._probe_json(
                    self._synthetic_cli(
                        root, "cg_uncapped", "--probe", "--json", env_extra=env_extra
                    )
                )

            clean = synthetic()
            self.assertIs(clean["is_cg_capped"], False)
            self._assert_concurrency(clean, 1)
            self.assertEqual(clean["timeout_sec"], 900)
            clean_file = self._probe_json(
                self._synthetic_cli(
                    root, "cg_uncapped", "--mode", "file", "--probe", "--json"
                )
            )
            self.assertGreater(clean_file["lean_m_mb"], 99)
            live_clean = self._probe_json(self._cli("--probe", "--json"))
            child_env_cmd = [
                sys.executable,
                "-c",
                "import json, os; print(json.dumps({"
                "k: os.environ.get(k) for k in ("
                "'ANNEAL_LEAN_RUN_LEAN_M_MB', 'ANNEAL_LSP_NO_EVICT', 'ANNEAL_OOM_OFFLOAD_CMD'"
                ")}))",
            ]

            with mock.patch.dict(os.environ, poison):
                fresh_xdg = root / "fresh_xdg"
                env = _isolated_cli_env(fresh_xdg)
                self.assertEqual(
                    [k for k in env if k.startswith(_AMBIENT_ANNEAL_ENV_PREFIXES)], []
                )
                self.assertEqual(env["XDG_CONFIG_HOME"], str(fresh_xdg))
                # `env_extra` is applied after the scrub, so explicit overrides survive it.
                explicit = _isolated_cli_env(
                    fresh_xdg,
                    {
                        "ANNEAL_WORKTREE_CONCURRENCY": "2",
                        "XDG_CONFIG_HOME": str(poisoned_xdg),
                    },
                )
                self.assertEqual(explicit["ANNEAL_WORKTREE_CONCURRENCY"], "2")
                self.assertEqual(explicit["XDG_CONFIG_HOME"], str(poisoned_xdg))
                self.assertNotIn("ANNEAL_LEAN_MEMORY_MAX_MB", explicit)
                self.assertNotIn("ANNEAL_LEAN_TIMEOUT_SEC", explicit)

                isolated = synthetic()
                isolated_exec = self._synthetic_cli(
                    root,
                    "cg_uncapped",
                    "--mode",
                    "file",
                    "--no-slot-lock",
                    "--",
                    *child_env_cmd,
                )
                live = self._probe_json(self._cli("--probe", "--json"))
                direct = (
                    self._probe_json(
                        self._direct_cli("--print-limits", "--json")
                    )
                    if os.access(SCRIPT_PATH, os.X_OK)
                    else None
                )

            # The synthetic host is deterministic: a poisoned parent changes nothing.
            self.assertEqual(isolated, clean)
            self.assertEqual(isolated_exec.returncode, 0, isolated_exec.stderr)
            self.assertEqual(
                json.loads(isolated_exec.stdout),
                {
                    "ANNEAL_LEAN_RUN_LEAN_M_MB": str(clean_file["lean_m_mb"]),
                    "ANNEAL_LSP_NO_EVICT": None,
                    "ANNEAL_OOM_OFFLOAD_CMD": None,
                },
            )
            for live_data in (live, direct):
                if live_data is not None:
                    self._assert_concurrency(live_data, 1)
                    self.assertEqual(live_data["timeout_sec"], 900)
                    if live_clean["memory_max_mb"] != 17:
                        self.assertNotEqual(live_data["memory_max_mb"], 17)

            # Positive controls: each poison is honored once passed explicitly, so the
            # equality above is not vacuous.
            leaked_env = synthetic(env_extra=ambient_overrides)
            self._assert_concurrency(leaked_env, 6)
            self.assertEqual(leaked_env["memory_max_mb"], 17)
            self.assertEqual(leaked_env["timeout_sec"], 55)
            leaked_xdg = synthetic(env_extra={"XDG_CONFIG_HOME": str(poisoned_xdg)})
            self._assert_concurrency(leaked_xdg, 7)
            # `XDG_CONFIG_HOME=""` falls back to `$HOME/.config`, which the isolated
            # non-empty `XDG_CONFIG_HOME` of `_cli` therefore masks.
            leaked_home = synthetic(
                env_extra={"HOME": str(poisoned_home), "XDG_CONFIG_HOME": ""}
            )
            self._assert_concurrency(leaked_home, 5)
            leaked_passthrough = self._synthetic_cli(
                root,
                "cg_uncapped",
                "--mode",
                "file",
                "--no-slot-lock",
                "--",
                *child_env_cmd,
                env_extra={
                    "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                    "ANNEAL_LEAN_RUN_LEAN_M_MB": "99",
                    "ANNEAL_LSP_NO_EVICT": "1",
                    "ANNEAL_OOM_OFFLOAD_CMD": "false",
                },
            )
            self.assertEqual(leaked_passthrough.returncode, 0, leaked_passthrough.stderr)
            self.assertEqual(
                json.loads(leaked_passthrough.stdout),
                {
                    "ANNEAL_LEAN_RUN_LEAN_M_MB": "99",
                    "ANNEAL_LSP_NO_EVICT": "1",
                    "ANNEAL_OOM_OFFLOAD_CMD": "false",
                },
            )

    def test_cli_synthetic_hosts_honor_caller_lowered_lean_num_threads_end_to_end(self) -> None:
        """Real subprocess CLI on both uncapped and cgroup-capped synthetic hosts:
        `LEAN_NUM_THREADS=1` flows to `--probe` text and the executed child while
        leaving `CARGO_BUILD_JOBS`/`RAYON_NUM_THREADS` at the host budget, and
        oversized values clamp strictly on the capped host."""
        dump_threads = [
            sys.executable,
            "-c",
            "import json, os; print(json.dumps({k: os.environ.get(k) for k in "
            "('LEAN_NUM_THREADS', 'CARGO_BUILD_JOBS', 'RAYON_NUM_THREADS')}))",
        ]
        with tempfile.TemporaryDirectory(prefix="anneal-synth-threads-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            for cg_name, ceiling_mib, capped in (
                ("cg_uncapped", None, False),
                ("cg_capped_1", 12288, True),
            ):
                _write_synthetic_cgroup_root(root, cg_name, ceiling_mib)
                probe_json = self._probe_json(
                    self._synthetic_cli(root, cg_name, "--mode", "build", "--probe", "--json")
                )
                self.assertIs(probe_json["is_cg_capped"], capped)
                budget = probe_json["threads"]
                self.assertGreater(budget, 1)

                # Lower positive `LEAN_NUM_THREADS=1` wins in both regimes.
                probe_txt = self._synthetic_cli(
                    root,
                    cg_name,
                    "--mode",
                    "build",
                    "--probe",
                    env_extra={"LEAN_NUM_THREADS": "1"},
                )
                self.assertEqual(probe_txt.returncode, 0, probe_txt.stderr)
                self.assertIn(
                    f"Thread Budget (-j) : {budget} threads (LEAN_NUM_THREADS=1)\n",
                    probe_txt.stdout,
                )
                run_low = self._synthetic_cli(
                    root,
                    cg_name,
                    "--mode",
                    "build",
                    "--no-slot-lock",
                    "--",
                    *dump_threads,
                    env_extra={"LEAN_NUM_THREADS": "1", "CARGO_BUILD_JOBS": "", "RAYON_NUM_THREADS": ""},
                )
                self.assertEqual(run_low.returncode, 0, run_low.stderr)
                self.assertEqual(
                    json.loads(run_low.stdout),
                    {
                        "LEAN_NUM_THREADS": "1",
                        "CARGO_BUILD_JOBS": str(budget),
                        "RAYON_NUM_THREADS": str(budget),
                    },
                )

                # Oversized `LEAN_NUM_THREADS=99` clamps on capped hosts and is kept on uncapped hosts.
                want_high = budget if capped else 99
                run_high = self._synthetic_cli(
                    root,
                    cg_name,
                    "--mode",
                    "build",
                    "--no-slot-lock",
                    "--",
                    *dump_threads,
                    env_extra={"LEAN_NUM_THREADS": "99", "CARGO_BUILD_JOBS": "", "RAYON_NUM_THREADS": ""},
                )
                self.assertEqual(run_high.returncode, 0, run_high.stderr)
                self.assertEqual(
                    json.loads(run_high.stdout)["LEAN_NUM_THREADS"],
                    str(want_high),
                )

    def test_cli_subprocess_exports_budget_env_vars_end_to_end(self) -> None:
        """End-to-end subprocess checks across synthetic direct execution,
        re-entrancy pass-through vs `--nested-ok`, and live `systemd-run` scope.
        """
        inspect_cmd = [
            sys.executable,
            "-c",
            "import json, os; print(json.dumps({"
            "k: os.environ.get(k) for k in ("
            "'ANNEAL_LEAN_RUN_SLOTS', 'ANNEAL_LEAN_RUN_MEM_MB'"
            ")}))",
        ]
        with tempfile.TemporaryDirectory(prefix="anneal-budget-env-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            _write_synthetic_cgroup_root(root, "cg_uncapped", None)
            probe = self._probe_json(
                self._synthetic_cli(
                    root,
                    "cg_uncapped",
                    "--mode",
                    "file",
                    "--concurrency",
                    "2",
                    "--memory-max-mb",
                    "2048",
                    "--probe",
                    "--json",
                )
            )
            self.assertEqual(probe["build_slots"], 2)
            self.assertEqual(probe["memory_max_mb"], 2048)

            # Unslotted `--no-slot-lock` overwrites stale parent values to 0.
            res_direct = self._synthetic_cli(
                root,
                "cg_uncapped",
                "--mode",
                "file",
                "--concurrency",
                "2",
                "--memory-max-mb",
                "2048",
                "--no-slot-lock",
                "--",
                *inspect_cmd,
                env_extra={
                    "ANNEAL_LEAN_RUN_SLOTS": "88",
                    "ANNEAL_LEAN_RUN_MEM_MB": "888888",
                },
            )
            self.assertEqual(res_direct.returncode, 0, res_direct.stderr)
            self.assertEqual(
                json.loads(res_direct.stdout),
                {"ANNEAL_LEAN_RUN_SLOTS": "0", "ANNEAL_LEAN_RUN_MEM_MB": "2048"},
            )

            # Pass-through inside an outer scope preserves the outer budget.
            res_passthrough = self._synthetic_cli(
                root,
                "cg_uncapped",
                "--mode",
                "file",
                "--concurrency",
                "2",
                "--memory-max-mb",
                "2048",
                "--no-slot-lock",
                "--",
                *inspect_cmd,
                env_extra={
                    "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                    "ANNEAL_LEAN_RUN_SLOTS": "5",
                    "ANNEAL_LEAN_RUN_MEM_MB": "12345",
                },
            )
            self.assertEqual(res_passthrough.returncode, 0, res_passthrough.stderr)
            self.assertEqual(
                json.loads(res_passthrough.stdout),
                {"ANNEAL_LEAN_RUN_SLOTS": "5", "ANNEAL_LEAN_RUN_MEM_MB": "12345"},
            )

            # `--nested-ok` bypasses pass-through and overwrites stale values.
            res_nested = self._synthetic_cli(
                root,
                "cg_uncapped",
                "--nested-ok",
                "--mode",
                "file",
                "--concurrency",
                "2",
                "--memory-max-mb",
                "2048",
                "--no-slot-lock",
                "--",
                *inspect_cmd,
                env_extra={
                    "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                    "ANNEAL_LEAN_RUN_SLOTS": "5",
                    "ANNEAL_LEAN_RUN_MEM_MB": "12345",
                },
            )
            self.assertEqual(res_nested.returncode, 0, res_nested.stderr)
            self.assertEqual(
                json.loads(res_nested.stdout),
                {"ANNEAL_LEAN_RUN_SLOTS": "0", "ANNEAL_LEAN_RUN_MEM_MB": "2048"},
            )

        if _can_launch_live_systemd_scope():
            with tempfile.TemporaryDirectory(prefix="anneal-cli-live-xdg-") as live_xdg:
                _seed_workloads_slice_unit(Path(live_xdg))
                live_probe = self._probe_json(
                    self._cli(
                        "--mode",
                        "file",
                        "--concurrency",
                        "2",
                        "--memory-max-mb",
                        "2048",
                        "--probe",
                        "--json",
                        env_extra={"XDG_CONFIG_HOME": live_xdg},
                    )
                )
                live_res = self._cli(
                    "--mode",
                    "file",
                    "--concurrency",
                    "2",
                    "--memory-max-mb",
                    "2048",
                    "--no-slot-lock",
                    "--",
                    *inspect_cmd,
                    env_extra={
                        "XDG_CONFIG_HOME": live_xdg,
                        "ANNEAL_LEAN_RUN_SLOTS": "77",
                        "ANNEAL_LEAN_RUN_MEM_MB": "777777",
                    },
                )
                self.assertEqual(live_res.returncode, 0, live_res.stderr)
                self.assertEqual(
                    json.loads(live_res.stdout),
                    {
                        "ANNEAL_LEAN_RUN_SLOTS": "0",
                        "ANNEAL_LEAN_RUN_MEM_MB": str(live_probe["memory_max_mb"]),
                    },
                )

    def test_run_isolated_and_cli_provide_unique_0700_xdg_runtime_dir_and_clean_up(
        self,
    ) -> None:
        """Module setup and every `_run_isolated` / `_cli` subprocess receive a unique,
        existing `0700` `XDG_RUNTIME_DIR` distinct from host `/run/user/<uid>` and `/tmp`
        (unless overridden via `env_extra`), and clean it up after returning or raising."""
        uid = os.getuid()
        host_run_user = Path(f"/run/user/{uid}").resolve()
        host_tmp = Path("/tmp").resolve()

        # Module-level isolation in `setUpModule()`.
        self.assertIsNotNone(_XDG_RUNTIME_TMPDIR)
        assert _XDG_RUNTIME_TMPDIR is not None
        mod_rt = Path(_XDG_RUNTIME_TMPDIR.name)
        self.assertEqual(os.environ.get("XDG_RUNTIME_DIR"), _XDG_RUNTIME_TMPDIR.name)
        self.assertTrue(mod_rt.is_dir())
        self.assertEqual(stat.S_IMODE(mod_rt.stat().st_mode), 0o700)
        self.assertNotIn(mod_rt.resolve(), {host_run_user, host_tmp})

        inspect_rt_cmd = [
            sys.executable,
            "-c",
            (
                "import json, os, pathlib, stat; "
                "rt = os.environ.get('XDG_RUNTIME_DIR'); "
                "p = pathlib.Path(rt) if rt else None; "
                "print(json.dumps({"
                "'rt': rt, "
                "'exists': bool(p and p.is_dir()), "
                "'mode': stat.S_IMODE(p.stat().st_mode) if (p and p.exists()) else None"
                "}))"
            ),
        ]

        seen_rts: list[Path] = []
        for _ in range(2):
            res = self._run_isolated(inspect_rt_cmd)
            self.assertEqual(res.returncode, 0, res.stderr)
            info = json.loads(res.stdout)
            self.assertTrue(info["exists"], info)
            self.assertEqual(info["mode"], 0o700, info)
            rt_path = Path(info["rt"])
            self.assertTrue(rt_path.name.startswith("anneal-cli-rt-"), rt_path)
            self.assertNotIn(rt_path.resolve(), {host_run_user, host_tmp, mod_rt.resolve()})
            self.assertFalse(rt_path.exists(), f"per-invocation rt dir leaked: {rt_path}")
            seen_rts.append(rt_path)
        self.assertNotEqual(seen_rts[0], seen_rts[1])

        # `_cli` pass-through receives a fresh `0700` `XDG_RUNTIME_DIR` and cleans it up.
        cli_res = self._cli(
            "--mode",
            "file",
            "--no-slot-lock",
            "--",
            *inspect_rt_cmd,
            env_extra={"ANNEAL_LEAN_RUN_IN_SCOPE": "1"},
        )
        self.assertEqual(cli_res.returncode, 0, cli_res.stderr)
        cli_info = json.loads(cli_res.stdout)
        self.assertTrue(cli_info["exists"], cli_info)
        self.assertEqual(cli_info["mode"], 0o700, cli_info)
        cli_rt = Path(cli_info["rt"])
        self.assertTrue(cli_rt.name.startswith("anneal-cli-rt-"), cli_rt)
        self.assertNotIn(cli_rt.resolve(), {host_run_user, host_tmp, mod_rt.resolve()})
        self.assertNotIn(cli_rt, seen_rts)
        self.assertFalse(cli_rt.exists(), f"_cli rt dir leaked: {cli_rt}")

        # Explicit `env_extra={"XDG_RUNTIME_DIR": ...}` override wins and is left intact,
        # while `_run_isolated`'s unused temp dir is still cleaned up.
        with tempfile.TemporaryDirectory(prefix="anneal-custom-rt-") as custom_rt:
            os.chmod(custom_rt, 0o700)
            override_res = self._run_isolated(
                inspect_rt_cmd, env_extra={"XDG_RUNTIME_DIR": custom_rt}
            )
            self.assertEqual(override_res.returncode, 0, override_res.stderr)
            override_info = json.loads(override_res.stdout)
            self.assertEqual(override_info["rt"], custom_rt)
            self.assertTrue(Path(custom_rt).is_dir())

        # Cleanup also holds when `subprocess.run` raises (e.g., timeout or OSError).
        captured_exc_rt: list[Path] = []

        def raising_run(*_args: Any, **kwargs: Any) -> Any:
            rt = Path(kwargs["env"]["XDG_RUNTIME_DIR"])
            self.assertTrue(rt.is_dir())
            self.assertEqual(stat.S_IMODE(rt.stat().st_mode), 0o700)
            captured_exc_rt.append(rt)
            raise subprocess.TimeoutExpired(cmd=["sleep"], timeout=1)

        with mock.patch.object(subprocess, "run", side_effect=raising_run):
            with self.assertRaises(subprocess.TimeoutExpired):
                self._run_isolated(["true"])
        self.assertEqual(len(captured_exc_rt), 1)
        self.assertFalse(
            captured_exc_rt[0].exists(),
            f"per-invocation rt dir leaked after exception: {captured_exc_rt[0]}",
        )

    def test_ambient_xdg_runtime_dir_slot_lock_does_not_block_isolated_tests(
        self,
    ) -> None:
        """Holding an exclusive `flock` on a simulated ambient
        `XDG_RUNTIME_DIR/anneal-build-slots-<uid>/slot-1.lock` must not block
        `_isolated_cli_env`, `_run_isolated`, or slot tests."""
        uid = os.getuid()
        with tempfile.TemporaryDirectory(prefix="anneal-ambient-rt-") as amb_tmp:
            ambient_rt = Path(amb_tmp)
            os.chmod(ambient_rt, 0o700)
            slot_dir = ambient_rt / f"anneal-build-slots-{uid}"
            slot_dir.mkdir(parents=True)
            lock_path = slot_dir / "slot-1.lock"
            fd = os.open(str(lock_path), os.O_CREAT | os.O_RDWR, 0o600)
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            try:
                # Positive control: ambient slot-1 really is locked and blocks acquisition.
                self.assertEqual(alr.count_active_build_slots(ambient_rt), 1)
                err_buf = io.StringIO()
                with mock.patch("sys.stderr", err_buf), self.assertRaises(TimeoutError):
                    with alr.acquire_build_slot(
                        1, 0.06, enabled=True, runtime_base=ambient_rt, poll_interval=0.02
                    ):
                        self.fail("Expected ambient slot-1 lock to block")

                with mock.patch.dict(os.environ, {"XDG_RUNTIME_DIR": str(ambient_rt)}):
                    with tempfile.TemporaryDirectory(prefix="anneal-iso-cfg-") as cfg_tmp:
                        iso_env = _isolated_cli_env(Path(cfg_tmp))
                    iso_rt = Path(iso_env["XDG_RUNTIME_DIR"])
                    self.assertNotEqual(iso_rt.resolve(), ambient_rt.resolve())
                    self.assertEqual(alr.count_active_build_slots(iso_rt), 0)
                    with alr.acquire_build_slot(
                        1, 0.5, enabled=True, runtime_base=iso_rt, poll_interval=0.02
                    ) as acquired:
                        self.assertEqual(acquired, 1)

                    # `_run_isolated` subprocess acquiring slot-1 under its isolated
                    # `XDG_RUNTIME_DIR` succeeds immediately despite ambient lock.
                    slot_probe_code = (
                        "import importlib.machinery, importlib.util, os, pathlib, sys\n"
                        "loader = importlib.machinery.SourceFileLoader('alr_sub', sys.argv[1])\n"
                        "spec = importlib.util.spec_from_loader('alr_sub', loader)\n"
                        "mod = importlib.util.module_from_spec(spec)\n"
                        "loader.exec_module(mod)\n"
                        "rt = pathlib.Path(os.environ['XDG_RUNTIME_DIR'])\n"
                        "assert mod.count_active_build_slots(rt) == 0\n"
                        "with mod.acquire_build_slot(1, 0.5, enabled=True, runtime_base=rt, poll_interval=0.02) as s:\n"
                        "    assert s == 1\n"
                        "print(str(rt))\n"
                    )
                    res = self._run_isolated(
                        [sys.executable, "-B", "-c", slot_probe_code, str(SCRIPT_PATH)]
                    )
                    self.assertEqual(res.returncode, 0, res.stderr)
                    child_rt = Path(res.stdout.strip())
                    self.assertNotEqual(child_rt.resolve(), ambient_rt.resolve())
                    self.assertFalse(child_rt.exists())
            finally:
                fcntl.flock(fd, fcntl.LOCK_UN)
                os.close(fd)

    def test_alr_main_and_cli_never_lock_or_mutate_host_build_slot_dirs(self) -> None:
        """`alr.main` / CLI tests never acquire locks or create files under host
        `/run/user/<uid>/anneal-build-slots-<uid>` or `/tmp/anneal-build-slots-<uid>`."""
        uid = os.getuid()
        forbidden_slot_dirs = {
            Path(f"/run/user/{uid}").resolve() / f"anneal-build-slots-{uid}",
            Path("/tmp").resolve() / f"anneal-build-slots-{uid}",
        }

        # Positive control: the module-wide slot-lock guard catches live host lock attempts.
        self.assertIsNotNone(_SLOT_LOCK_GUARD)
        for forbidden_base in (Path(f"/run/user/{uid}"), Path("/tmp")):
            with self.assertRaisesRegex(AssertionError, "live host build-slot lock"):
                with alr.acquire_build_slot(
                    1, 0.05, enabled=True, runtime_base=forbidden_base
                ):
                    pass

        real_open = os.open
        # Any open at all (including the read-only `LOCK_SH` probes of
        # `count_active_build_slots`) of a host slot lock is a host build-slot touch.
        host_slot_writes: list[str] = []

        def spy_open(path: Any, flags: int, *args: Any, **kwargs: Any) -> int:
            try:
                resolved = Path(os.fsdecode(path)).resolve()
            except (OSError, TypeError):
                resolved = None
            if resolved is not None and any(
                resolved == d or d in resolved.parents for d in forbidden_slot_dirs
            ):
                host_slot_writes.append(str(resolved))
            return real_open(path, flags, *args, **kwargs)

        with mock.patch("os.open", side_effect=spy_open):
            out_buf = io.StringIO()
            with mock.patch("sys.stdout", out_buf):
                self.assertEqual(alr.main(["--probe", "--json"]), 0)
            self.assertEqual(
                alr.main(["--mode", "file", "--no-slot-lock", "--concurrency", "1", "--", "true"]),
                0,
            )
            self.assertEqual(
                alr.main(["--mode", "build", "--no-slot-lock", "--concurrency", "1", "--", "true"]),
                0,
            )
        self.assertEqual(host_slot_writes, [])

        # Enabled build-slot locking in `_synthetic_cli` creates `slot-1.lock` strictly
        # inside the synthetic temp root, never under `/run/user/<uid>` or `/tmp`.
        with tempfile.TemporaryDirectory(prefix="anneal-slot-audit-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            _write_synthetic_cgroup_root(root, "cg_uncapped", None)
            res = self._synthetic_cli(
                root, "cg_uncapped", "--mode", "build", "--concurrency", "1", "--", "true"
            )
            self.assertEqual(res.returncode, 0, res.stderr)
            synth_lock = root / f"anneal-build-slots-{uid}" / "slot-1.lock"
            self.assertTrue(synth_lock.is_file(), f"expected synthetic lock at {synth_lock}")
            self.assertNotIn(synth_lock.parent.resolve(), forbidden_slot_dirs)

    def test_cli_subprocesses_confine_slot_locks_and_oom_memos_to_isolated_runtime_dir(
        self,
    ) -> None:
        """Real CLI subprocesses (`_cli` and shebang `_direct_cli`) never open anything under
        the live host `/run/user/<uid>` or `/tmp` slot / OOM-memo paths, even though
        `resolve_runtime_base()` prefers `/run/user/<uid>` over the isolated
        `XDG_RUNTIME_DIR`: probes, `--exclusive` slot locking, and exit-137 OOM memos all
        land in the per-invocation `anneal-cli-rt-*` directory instead."""
        uid = os.getuid()
        markers = (f"anneal-build-slots-{uid}", f"anneal-last-oom-{uid}", "anneal-lean-lsp.sock")
        host_bases = sorted(str(b) for b in _host_runtime_bases())
        audit_code = (
            "import json, os, sys\n"
            "_LOG = os.environ.get('ALR_TEST_AUDIT_LOG')\n"
            f"_MARKERS = {markers!r}\n"
            "def _hook(event, args):\n"
            "    if not _LOG:\n"
            "        return\n"
            "    if event in ('open', 'os.mkdir'):\n"
            "        path = args[0]\n"
            "        flags = args[2] if event == 'open' and len(args) > 2 else None\n"
            "    elif event == 'socket.connect':\n"
            "        path = args[1] if len(args) > 1 else None\n"
            "        flags = None\n"
            "    else:\n"
            "        return\n"
            "    if not isinstance(path, (str, bytes, os.PathLike)):\n"
            "        return\n"
            "    path = os.path.abspath(os.fsdecode(path))\n"
            "    if not any(m in path for m in _MARKERS):\n"
            "        return\n"
            "    with open(_LOG, 'a', encoding='utf-8') as fh:\n"
            "        fh.write(json.dumps({'event': event, 'path': path, 'flags': flags,\n"
            "                             'pid': os.getpid()}) + '\\n')\n"
            "sys.addaudithook(_hook)\n"
        )
        with tempfile.TemporaryDirectory(prefix="anneal-cli-audit-") as audit_tmp, \
             tempfile.TemporaryDirectory(prefix="anneal-cli-audit-xdg-") as run_xdg:
            audit_dir = Path(audit_tmp)
            (audit_dir / "sitecustomize.py").write_text(audit_code, encoding="utf-8")
            log_path = audit_dir / "touches.jsonl"
            _seed_workloads_slice_unit(Path(run_xdg))
            env = {
                "PYTHONPATH": str(audit_dir),
                "ALR_TEST_AUDIT_LOG": str(log_path),
                "XDG_CONFIG_HOME": run_xdg,
            }
            self._probe_json(self._cli("--probe", "--json", env_extra=env))
            if os.access(SCRIPT_PATH, os.X_OK):
                self.assertIn(
                    "cgroup_avail_mib",
                    self._probe_json(self._direct_cli("--print-limits", "--json", env_extra=env)),
                )
                # `_direct_cli` still isolates to its private `rt_dir` even when `env_extra`
                # overrides `XDG_RUNTIME_DIR` to `/tmp`, and restores `PATH` so child `python3`
                # invocations are never hijacked by the shebang wrapper.
                direct_override = self._probe_json(
                    self._direct_cli(
                        "--print-limits",
                        "--json",
                        env_extra={**env, "XDG_RUNTIME_DIR": "/tmp"},
                    )
                )
                self.assertIn("cgroup_avail_mib", direct_override)
                direct_py = self._direct_cli(
                    "--mode",
                    "file",
                    "--no-slot-lock",
                    "--concurrency",
                    "1",
                    "--",
                    "python3",
                    "-c",
                    "print('direct-child-ok')",
                    env_extra=env,
                )
                self.assertEqual(direct_py.returncode, 0, direct_py.stderr)
                self.assertEqual(direct_py.stdout.strip(), "direct-child-ok")
            # `_synthetic_cli` in build mode on a capped host also stays completely off the
            # default host LSP socket (`/tmp/anneal-lean-lsp.sock`) and host slot/OOM paths.
            with tempfile.TemporaryDirectory(prefix="anneal-synth-audit-") as synth_tmp:
                synth_root = Path(synth_tmp)
                _write_synthetic_host_base(synth_root)
                _write_synthetic_cgroup_root(synth_root, "cg_capped_1", 12288)
                synth_build = self._synthetic_cli(
                    synth_root,
                    "cg_capped_1",
                    "--mode",
                    "build",
                    "--concurrency",
                    "1",
                    "--",
                    "true",
                    env_extra=env,
                )
                self.assertEqual(synth_build.returncode, 0, synth_build.stderr)
            excl = self._cli(
                "--mode", "file", "--exclusive", "--concurrency", "1",
                "--", sys.executable, "-c", "pass",
                env_extra=env,
            )
            self.assertEqual(excl.returncode, 0, excl.stderr)
            oom = self._cli(
                "--mode", "file", "--no-slot-lock", "--no-oom-retry", "--concurrency", "1",
                "--", "sh", "-c", "exit 137",
                env_extra=env,
            )
            self.assertEqual(oom.returncode, 137, oom.stderr)
            touches = [
                json.loads(line)
                for line in log_path.read_text(encoding="utf-8").splitlines()
                if line.strip()
            ] if log_path.exists() else []

        # A host touch is any path directly under a live host runtime base whose first
        # component is a slot / OOM-memo marker (`/tmp/anneal-cli-rt-*/...` is isolated).
        host_touches = [
            t for t in touches
            if any(
                t["path"].startswith(b + os.sep)
                and t["path"][len(b) + 1:].startswith(markers)
                for b in host_bases
            )
        ]
        self.assertEqual(host_touches, [], "CLI subprocess touched live host slot/OOM state")
        rt_touches = [
            t for t in touches
            if any(part.startswith("anneal-cli-rt-") for part in Path(t["path"]).parts)
        ]
        # Positive controls: the redirected paths really were exercised.
        self.assertTrue(
            any(
                t["event"] == "open"
                and t["path"].endswith(f"anneal-build-slots-{uid}{os.sep}slot-1.lock")
                and isinstance(t["flags"], int)
                and t["flags"] & os.O_CREAT
                for t in rt_touches
            ),
            touches,
        )
        self.assertTrue(any(f"anneal-last-oom-{uid}" in t["path"] for t in rt_touches), touches)

    def test_in_process_probes_redirect_host_slot_counts_oom_memos_and_lsp_eviction(
        self,
    ) -> None:
        """Module guards keep in-process `probe_host_envelope` / `count_active_build_slots`
        / `stamp_last_oom` / default-socket `_evict_lsp_workers` off live host state, while
        explicitly isolated bases and sockets pass through unchanged."""
        uid = os.getuid()
        self.assertIsNotNone(_XDG_RUNTIME_TMPDIR)
        assert _XDG_RUNTIME_TMPDIR is not None
        mod_rt = Path(_XDG_RUNTIME_TMPDIR.name)
        host_bases = _host_runtime_bases()
        host_slot_dirs = {b / f"anneal-build-slots-{uid}" for b in host_bases}
        opened: list[Path] = []
        real_open = os.open

        def spy_open(path: Any, flags: int, *args: Any, **kwargs: Any) -> int:
            try:
                opened.append(Path(os.fsdecode(path)).resolve())
            except (OSError, TypeError):
                pass
            return real_open(path, flags, *args, **kwargs)

        mod_slot_dir = mod_rt / f"anneal-build-slots-{uid}"
        mod_slot_dir.mkdir(exist_ok=True)
        lock_fd = os.open(str(mod_slot_dir / "slot-1.lock"), os.O_CREAT | os.O_RDWR, 0o600)
        try:
            fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            with mock.patch("os.open", side_effect=spy_open):
                alr.probe_host_envelope()
                # Positive control: counting the host base sees the isolated held lock.
                for base in (Path(f"/run/user/{uid}"), Path("/tmp")):
                    self.assertEqual(alr.count_active_build_slots(base), 1, base)
        finally:
            fcntl.flock(lock_fd, fcntl.LOCK_UN)
            os.close(lock_fd)
            for lock_file in mod_slot_dir.glob("slot-*.lock"):
                lock_file.unlink()
            mod_slot_dir.rmdir()
        self.assertEqual(
            [p for p in opened if any(p == d or d in p.parents for d in host_slot_dirs)], []
        )

        with tempfile.TemporaryDirectory(prefix="anneal-own-rt-") as own_tmp:
            own_rt = Path(own_tmp)
            self.assertEqual(alr.count_active_build_slots(own_rt), 0)
            for base in (Path(f"/run/user/{uid}"), Path("/tmp")):
                stamped = alr.stamp_last_oom(base, "build", "oom", 1.5)
                self.assertEqual(stamped.parent.resolve(), mod_rt.resolve(), base)
                stamped.unlink()
                for lock_file in mod_rt.glob("anneal-last-oom-*.lock"):
                    lock_file.unlink()
            own_stamp = alr.stamp_last_oom(own_rt, "build", "oom", 1.5)
            self.assertEqual(own_stamp.parent.resolve(), own_rt.resolve())

        seen_socks: list[Path | None] = []

        def fake_orig_evict(
            _env_info: dict[str, Any], *, sock_path: Path | None = None, **_kw: Any
        ) -> bool:
            seen_socks.append(sock_path)
            return False

        with mock.patch.object(
            sys.modules[__name__], "_ORIG_EVICT_LSP_WORKERS", side_effect=fake_orig_evict
        ):
            with mock.patch.dict(os.environ):
                os.environ.pop("ANNEAL_LSP_SOCKET", None)
                self.assertFalse(alr._evict_lsp_workers({}))
            explicit = Path("/nonexistent/explicit.sock")
            self.assertFalse(alr._evict_lsp_workers({}, sock_path=explicit))
            with mock.patch.dict(os.environ, {"ANNEAL_LSP_SOCKET": "/nonexistent/env.sock"}):
                self.assertFalse(alr._evict_lsp_workers({}))
        self.assertEqual(
            seen_socks, [mod_rt / "anneal-lean-lsp.sock", explicit, None]
        )
        self.assertNotIn(Path("/tmp/anneal-lean-lsp.sock"), seen_socks)

    def test_module_host_state_audit_detects_and_isolates_violations(self) -> None:
        """The module-wide host-state audit (`tearDownModule` fails on any hit) is live:
        its classifier flags live host slot / OOM-memo paths (directly or via symlinked
        parents) and the default host LSP socket while passing isolated paths; the
        in-process hook records into its sink; and `_isolated_cli_env` subprocesses load
        the auditing `sitecustomize` (chaining the distro one) and log real touches."""
        uid = os.getuid()
        slots = f"anneal-build-slots-{uid}"
        classify = _classify_host_state_event
        for event, args in (
            ("open", (f"/run/user/{uid}/{slots}/slot-1.lock", None, os.O_RDONLY)),
            ("open", (f"/tmp/{slots}/slot-2.lock", "rb", 0)),
            ("os.mkdir", (f"/tmp/{slots}", 0o777, -1)),
            ("os.scandir", (f"/run/user/{uid}/{slots}",)),
            ("open", (f"/run/user/{uid}/anneal-last-oom-{uid}.json", None, os.O_RDWR)),
            ("os.rename", ("/x/elsewhere", f"/run/user/{uid}/anneal-last-oom-{uid}.json", -1, -1)),
            ("socket.connect", (None, "/tmp/anneal-lean-lsp.sock")),
        ):
            self.assertIsNotNone(classify(event, args), (event, args))
        for event, args in (
            ("open", (f"/tmp/anneal-cli-rt-abc/{slots}/slot-1.lock", None, os.O_CREAT)),
            ("open", (f"/tmp/anneal-test-xdg-rt-abc/anneal-last-oom-{uid}.json", None, 0)),
            ("open", (f"/tmp/anneal-build-slots-{uid}0/slot-1.lock", None, 0)),
            ("open", (f"/tmp/anneal-last-oom-{uid}0.json", None, 0)),
            ("open", (f"/run/user/{uid}/bus", None, 0)),
            ("os.mkdir", (f"/tmp/not-{slots}", 0o777, -1)),
            ("socket.connect", (None, "/tmp/anneal-cli-rt-abc/anneal-lean-lsp.sock")),
            ("socket.connect", (None, ("127.0.0.1", 80))),
            ("open", (3, None, 0)),
            ("exec", ("/bin/true",)),
        ):
            self.assertIsNone(classify(event, args), (event, args))
        with tempfile.TemporaryDirectory(prefix="anneal-audit-link-") as link_tmp:
            link = Path(link_tmp) / "rt"
            link.symlink_to("/tmp")
            self.assertIsNotNone(classify("open", (str(link / slots / "slot-1.lock"), None, 0)))
            # Direct leaf symlink pointing to a host lock file / slot dir is caught too.
            leaf_link = Path(link_tmp) / "direct-lock"
            leaf_link.symlink_to(f"/tmp/{slots}/slot-1.lock")
            self.assertIsNotNone(classify("open", (str(leaf_link), None, 0)))

        # In-process hook: live, routed into the sink (restored afterwards).
        self.assertTrue(_HOST_AUDIT_ACTIVE)
        saved = list(_HOST_AUDIT_SINK)
        probe_path = f"/tmp/{slots}/alr-audit-probe-never-created"
        try:
            with self.assertRaises(OSError):
                os.open(probe_path, os.O_RDONLY)
            self.assertEqual(_HOST_AUDIT_SINK[len(saved):], [{"event": "open", "path": probe_path}])
        finally:
            _HOST_AUDIT_SINK[:] = saved

        # Subprocesses: the auditing `sitecustomize` loads (and chains to custom
        # `env_extra["PYTHONPATH"]` without being overwritten) and logs a real touch.
        with tempfile.TemporaryDirectory(prefix="anneal-audit-child-") as child_tmp:
            scratch_log = Path(child_tmp) / "child.jsonl"
            extra_pp = Path(child_tmp) / "extra_pp"
            extra_pp.mkdir()
            (extra_pp / "sitecustomize.py").write_text(
                "import os; os.environ['ALR_CHAINED_CUSTOM_SC'] = '1'\n",
                encoding="utf-8",
            )
            res = self._run_isolated(
                [
                    sys.executable,
                    "-c",
                    "import json, os, sitecustomize\n"
                    "print(json.dumps({'audit': getattr(sitecustomize, 'ALR_HOST_STATE_AUDIT', False), "
                    "'chained': os.environ.get('ALR_CHAINED_CUSTOM_SC')}))\n"
                    "try:\n"
                    f"    os.open({probe_path!r}, os.O_RDONLY)\n"
                    "except OSError:\n"
                    "    pass\n",
                ],
                {"PYTHONPATH": str(extra_pp), _HOST_AUDIT_ENV_LOG: str(scratch_log)},
            )
            self.assertEqual(res.returncode, 0, res.stderr)
            self.assertEqual(json.loads(res.stdout), {"audit": True, "chained": "1"})
            logged = [json.loads(x) for x in scratch_log.read_text(encoding="utf-8").splitlines()]
            self.assertEqual([(h["event"], h["path"]) for h in logged], [("open", probe_path)])


class TestWorkloadMemoryEnvelopeV2(unittest.TestCase):
    """Tests v2 `anneal-workloads.slice`, `--exclusive`, re-entrancy, and OOM retry guards."""

    def test_ensure_slice_gate_and_content_diff(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-slice-") as td:
            unit_p = Path(td) / "anneal-workloads.slice"
            bad_env = {
                "user_systemd_active": False,
                "t_cg_is_user_service": False,
                "w_slice_high_mb": 7768,
                "w_slice_max_mb": 8264,
            }
            ok, ch, _ = alr.ensure_workloads_slice(bad_env, unit_path=unit_p, reload_systemd=False)
            self.assertFalse(ok)
            self.assertFalse(ch)
            self.assertFalse(unit_p.exists())

            good_env = {
                "user_systemd_active": True,
                "t_cg_is_user_service": True,
                "w_slice_high_mb": 7768,
                "w_slice_max_mb": 8264,
                "runtime_base": td,
            }
            # Stub the `systemctl` lookup too, so the test does not depend
            # on the host (e.g. a sandboxed CI image without systemd).
            with mock.patch.object(alr.subprocess, "run") as mock_run, \
                 mock.patch.object(alr, "_find_systemctl", return_value="/usr/bin/systemctl"):
                mock_run.return_value = subprocess.CompletedProcess([], 0, "", "")
                ok1, ch1, _ = alr.ensure_workloads_slice(good_env, unit_path=unit_p, reload_systemd=True)
                self.assertTrue(ok1)
                self.assertTrue(ch1)
                self.assertEqual(mock_run.call_count, 1)
                txt = unit_p.read_text(encoding="utf-8")
                self.assertIn("MemoryHigh=7768M", txt)
                self.assertIn("MemoryMax=8264M", txt)
                self.assertIn("MemorySwapMax=0", txt)

                ok2, ch2, _ = alr.ensure_workloads_slice(good_env, unit_path=unit_p, reload_systemd=True)
                self.assertTrue(ok2)
                self.assertFalse(ch2)
                self.assertEqual(mock_run.call_count, 1)

    def test_exclusive_multi_lock_and_in_scope_passthrough(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-excl-") as td:
            rt = Path(td)
            slot_dir = rt / f"anneal-build-slots-{os.getuid()}"
            slot_dir.mkdir(parents=True)
            fd2 = os.open(str(slot_dir / "slot-2.lock"), os.O_CREAT | os.O_RDWR, 0o600)
            fcntl.flock(fd2, fcntl.LOCK_EX | fcntl.LOCK_NB)
            try:
                err_buf = io.StringIO()
                with mock.patch("sys.stderr", err_buf):
                    with self.assertRaises(TimeoutError):
                        with alr.acquire_build_slot(
                            3, 0.12, enabled=True, exclusive=True, runtime_base=rt, poll_interval=0.03
                        ):
                            self.fail("Expected timeout while slot-2 locked")
                self.assertIn("Waiting for exclusive access", err_buf.getvalue())
                fd1 = os.open(str(slot_dir / "slot-1.lock"), os.O_CREAT | os.O_RDWR, 0o600)
                try:
                    fcntl.flock(fd1, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    fcntl.flock(fd1, fcntl.LOCK_UN)
                finally:
                    os.close(fd1)
            finally:
                fcntl.flock(fd2, fcntl.LOCK_UN)
                os.close(fd2)

            with alr.acquire_build_slot(3, 1.0, enabled=True, exclusive=True, runtime_base=rt) as slots:
                self.assertEqual(slots, [1, 2, 3])
                self.assertEqual(alr.count_active_build_slots(rt), 3)

            with tempfile.TemporaryDirectory(prefix="anneal-excl-xdg-") as xdg_dir:
                env_in = _isolated_cli_env(
                    Path(xdg_dir),
                    {
                        "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                        "XDG_RUNTIME_DIR": str(rt),
                    },
                )
                res = subprocess.run(
                    [
                        sys.executable,
                        "-B",
                        "-c",
                        _ISOLATED_CLI_SHIM,
                        str(SCRIPT_PATH),
                        str(rt),
                        "--mode",
                        "build",
                        "--",
                        sys.executable,
                        "-c",
                        "print('ok')",
                    ],
                    env=env_in,
                    stdin=subprocess.DEVNULL,
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=10.0,
                )
            self.assertEqual(res.returncode, 0, res.stderr)
            self.assertEqual(res.stdout.strip(), "ok")

    def test_concurrency_isolation_uncapped_and_capped(self) -> None:
        """Hermetically verifies `XDG_CONFIG_HOME` / `HOME` isolation and
        `ANNEAL_WORKTREE_CONCURRENCY` behavior under both uncapped and cgroup-capped
        regimes (even when tests run on a 1-slot cgroup-capped host)."""
        with tempfile.TemporaryDirectory(prefix="anneal-conc-iso-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            meminfo = root / "meminfo"
            proc_cg = root / "proc_cgroup"
            uncapped_cg, capped_1slot_cg, capped_2slot_cg = (
                _write_synthetic_cgroup_root(root, name, ceiling_mib)
                for name, ceiling_mib, _capped, _s_heavy_safe in SYNTHETIC_HOSTS
            )

            fake_home = root / "home"
            _write_cgroup_file(fake_home / ".config" / "anneal" / "concurrency", "5\n")
            empty_xdg = root / "xdg_empty"
            empty_xdg.mkdir()
            populated_xdg = root / "xdg_three"
            _write_cgroup_file(populated_xdg / "anneal" / "concurrency", "3\n")

            # Empty XDG_CONFIG_HOME masks $HOME/.config/anneal/concurrency; unset XDG falls back to HOME.
            with mock.patch.dict(
                os.environ,
                {"HOME": str(fake_home), "XDG_CONFIG_HOME": str(empty_xdg)},
                clear=False,
            ):
                os.environ.pop("ANNEAL_WORKTREE_CONCURRENCY", None)
                self.assertIsNone(alr.read_concurrency_config_file())
                env_default = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=uncapped_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertFalse(env_default["is_cg_capped"])
                self.assertEqual(env_default["concurrency"], 1)
                self.assertEqual(env_default["build_slots"], 1)

            with mock.patch.dict(
                os.environ,
                {"HOME": str(fake_home), "XDG_CONFIG_HOME": ""},
                clear=False,
            ):
                self.assertEqual(alr.read_concurrency_config_file(), 5)

            # Uncapped regime: ANNEAL_WORKTREE_CONCURRENCY=2 -> 2; XDG file "3" -> 3.
            with mock.patch.dict(
                os.environ,
                {
                    "XDG_CONFIG_HOME": str(empty_xdg),
                    "ANNEAL_WORKTREE_CONCURRENCY": "2",
                },
                clear=False,
            ):
                uncapped_env = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=uncapped_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertFalse(uncapped_env["is_cg_capped"])
                self.assertEqual(uncapped_env["concurrency"], 2)
                self.assertEqual(uncapped_env["build_slots"], 2)

            with mock.patch.dict(
                os.environ,
                {"XDG_CONFIG_HOME": str(populated_xdg)},
                clear=False,
            ):
                os.environ.pop("ANNEAL_WORKTREE_CONCURRENCY", None)
                uncapped_cfg = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=uncapped_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertFalse(uncapped_cfg["is_cg_capped"])
                self.assertEqual(uncapped_cfg["concurrency"], 3)
                self.assertEqual(uncapped_cfg["build_slots"], 3)

            # Capped 1-slot regime: env=2 and xdg=3 both clamp to s_heavy_safe == 1,
            # and unsafe_ignore_cgroup lifts only override_mem_mb above w_slice_max_mb.
            with mock.patch.dict(
                os.environ,
                {
                    "XDG_CONFIG_HOME": str(empty_xdg),
                    "ANNEAL_WORKTREE_CONCURRENCY": "2",
                },
                clear=False,
            ):
                cap1 = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=capped_1slot_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertTrue(cap1["is_cg_capped"])
                self.assertEqual(cap1["s_heavy_safe"], 1)
                self.assertEqual(cap1["concurrency"], 1)
                self.assertEqual(cap1["build_slots"], 1)
                over_mb = cap1["w_slice_max_mb"] + 1024
                cap1_mem_clamped = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=capped_1slot_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                    override_mem_mb=over_mb,
                    unsafe_ignore_cgroup=False,
                )
                self.assertEqual(cap1_mem_clamped["memory_max_mb"], cap1["w_slice_max_mb"])
                cap1_mem_unsafe = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=capped_1slot_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                    override_mem_mb=over_mb,
                    unsafe_ignore_cgroup=True,
                )
                self.assertEqual(cap1_mem_unsafe["memory_max_mb"], over_mb)
                self.assertEqual(cap1_mem_unsafe["concurrency"], 1)

            with mock.patch.dict(
                os.environ,
                {"XDG_CONFIG_HOME": str(populated_xdg)},
                clear=False,
            ):
                os.environ.pop("ANNEAL_WORKTREE_CONCURRENCY", None)
                cap1_xdg = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=capped_1slot_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertTrue(cap1_xdg["is_cg_capped"])
                self.assertEqual(cap1_xdg["s_heavy_safe"], 1)
                self.assertEqual(cap1_xdg["concurrency"], 1)
                self.assertEqual(cap1_xdg["build_slots"], 1)

            # Capped 2-slot regime: s_heavy_safe == 2 keeps env=2 and clamps xdg=3 to 2.
            with mock.patch.dict(
                os.environ,
                {
                    "XDG_CONFIG_HOME": str(empty_xdg),
                    "ANNEAL_WORKTREE_CONCURRENCY": "2",
                },
                clear=False,
            ):
                cap2_env = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=capped_2slot_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertTrue(cap2_env["is_cg_capped"])
                self.assertEqual(cap2_env["s_heavy_safe"], 2)
                self.assertEqual(cap2_env["concurrency"], 2)
                self.assertEqual(cap2_env["build_slots"], 2)

            with mock.patch.dict(
                os.environ,
                {"XDG_CONFIG_HOME": str(populated_xdg)},
                clear=False,
            ):
                os.environ.pop("ANNEAL_WORKTREE_CONCURRENCY", None)
                cap2 = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=capped_2slot_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertTrue(cap2["is_cg_capped"])
                self.assertEqual(cap2["s_heavy_safe"], 2)
                self.assertEqual(cap2["concurrency"], 2)
                self.assertEqual(cap2["build_slots"], 2)

    def test_exclusive_probe_matches_execution_w_eff_with_cli_concurrency(self) -> None:
        """`--exclusive` forces `w_eff = 1` in `--probe` just as in execution, even when
        `--concurrency` (`cli_concurrency`) is also supplied, while preserving `build_slots`."""
        for is_cg_capped, s_heavy_safe, w_file, cli_c, want_slots in (
            (False, 4, None, 4, 4),
            (False, 4, 3, 2, 3),
            (True, 2, None, 4, 2),
            (True, 2, 4, 3, 2),
        ):
            probe_res = alr.resolve_effective_concurrency(
                is_cg_capped=is_cg_capped,
                s_heavy_safe=s_heavy_safe,
                w_file=w_file,
                cli_concurrency=cli_c,
                env_concurrency=None,
                exclusive=True,
                is_probe=True,
            )
            exec_res = alr.resolve_effective_concurrency(
                is_cg_capped=is_cg_capped,
                s_heavy_safe=s_heavy_safe,
                w_file=w_file,
                cli_concurrency=cli_c,
                env_concurrency=None,
                exclusive=True,
                is_probe=False,
            )
            self.assertEqual(probe_res, (1, want_slots))
            self.assertEqual(probe_res, exec_res)

        probe_env = alr.compute_workload_memory_envelope(
            cpu_cores=16,
            mem_total_mb=32768,
            mem_avail_mb=28672,
            w_file=4,
            cli_concurrency=4,
            exclusive=True,
            is_probe=True,
            mode="build",
        )
        exec_env = alr.compute_workload_memory_envelope(
            cpu_cores=16,
            mem_total_mb=32768,
            mem_avail_mb=28672,
            w_file=4,
            cli_concurrency=4,
            exclusive=True,
            is_probe=False,
            mode="build",
        )
        self.assertEqual(probe_env["w_eff"], 1)
        self.assertEqual(probe_env["build_slots"], 4)
        self.assertEqual(probe_env["memory_max_mb"], exec_env["memory_max_mb"])

    def test_probe_cap_brackets_execution_cap_on_multi_slot_hosts(self) -> None:
        """Contract `run_nightly_verification_suite._probe_lean_run_memory_max_mib` relies on.

        A non-exclusive `--probe --concurrency w` plans for `w` slots, while execution
        runs at `build_slots` when the host's concurrency file asks for more. Then
        `--probe --concurrency <build_slots>` reproduces the execution plan, and the
        execution `memory_max_mb` lies in `[probe * w // build_slots, probe]`.
        """
        reprobed = 0
        for mem_total, mem_avail, cores in (
            (16384, 14000, 8),
            (32768, 28672, 16),
            (65536, 60000, 32),
            (262144, 200000, 96),
        ):
            for c_high in (None, mem_total // 2, (3 * mem_total) // 4):
                ancestors = (
                    []
                    if c_high is None
                    else [
                        {
                            "path": "/sys/fs/cgroup/user.slice",
                            "name": "user.slice",
                            "c_high_mb": c_high,
                            "w_mb": 512,
                            "is_shared_user_slice": False,
                        }
                    ]
                )
                for w_file in (2, 3, 4):
                    for cli_c in (1, 2, 3):
                        for mode in ("build", "file"):
                            for l_ws, w_cg in ((0, 0), (1500, 2500)):

                                def plan(concurrency: int, is_probe: bool) -> dict:
                                    return alr.compute_workload_memory_envelope(
                                        cpu_cores=cores,
                                        mem_total_mb=mem_total,
                                        mem_avail_mb=mem_avail,
                                        ancestors=ancestors,
                                        w_cg_mb=w_cg,
                                        w_cg_nonrecl_mb=w_cg,
                                        l_ws_mb=l_ws,
                                        w_file=w_file,
                                        cli_concurrency=concurrency,
                                        is_probe=is_probe,
                                        mode=mode,
                                    )

                                case = (mem_total, c_high, w_file, cli_c, mode, l_ws)
                                probe, execd = plan(cli_c, True), plan(cli_c, False)
                                slots = probe["build_slots"]
                                self.assertEqual(slots, execd["build_slots"], case)
                                if probe["w_eff"] >= slots:
                                    # Nothing to reconcile: the probe already is the plan.
                                    self.assertEqual(probe["w_eff"], execd["w_eff"], case)
                                    self.assertEqual(
                                        probe["memory_max_mb"], execd["memory_max_mb"], case
                                    )
                                    continue
                                reprobed += 1
                                self.assertEqual(execd["w_eff"], slots, case)
                                again = plan(slots, True)
                                self.assertEqual(again["w_eff"], slots, case)
                                self.assertEqual(
                                    again["memory_max_mb"], execd["memory_max_mb"], case
                                )
                                self.assertLessEqual(
                                    execd["memory_max_mb"], probe["memory_max_mb"], case
                                )
                                self.assertGreaterEqual(
                                    execd["memory_max_mb"],
                                    probe["memory_max_mb"] * probe["w_eff"] // slots,
                                    case,
                                )
        self.assertGreater(reprobed, 0)

    def test_oom_retry_guard_blocks_watchdog_and_timeout(self) -> None:
        common = dict(
            rc=137,
            oom_event_detected=False,
            watchdog_aborted=False,
            timed_out=False,
            mode="build",
            no_oom_retry=False,
            skip_evict_at_launch=True,
            b_max_at_launch=10777,
            b_max_evict_at_launch=11699,
            rem_timeout=800,
            lsp_no_evict=False,
        )
        self.assertTrue(alr._should_retry_oom(**common))
        self.assertFalse(alr._should_retry_oom(**{**common, "watchdog_aborted": True}))
        self.assertFalse(alr._should_retry_oom(**{**common, "timed_out": True}))
        self.assertFalse(alr._should_retry_oom(**{**common, "lsp_no_evict": True}))


if __name__ == "__main__":
    unittest.main()
