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
import subprocess
import sys
import tempfile
from typing import Any, Iterator
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
_XDG_TMPDIR: tempfile.TemporaryDirectory[str] | None = None


def _scrub_ambient_anneal_env(env: dict[str, str]) -> None:
    for key in list(env):
        if key.startswith(_AMBIENT_ANNEAL_ENV_PREFIXES):
            env.pop(key, None)


def _isolated_cli_env(
    xdg_config_home: Path, env_extra: dict[str, str] | None = None
) -> dict[str, str]:
    env = dict(os.environ)
    _scrub_ambient_anneal_env(env)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["XDG_CONFIG_HOME"] = str(xdg_config_home)
    if env_extra:
        env.update(env_extra)
    return env


def setUpModule() -> None:
    global _ENV_PATCHER, _XDG_TMPDIR
    _XDG_TMPDIR = tempfile.TemporaryDirectory(prefix="anneal-test-xdg-")
    patch_vals = {**_HERMETIC_GIT_ENV, "XDG_CONFIG_HOME": _XDG_TMPDIR.name}
    _ENV_PATCHER = mock.patch.dict(os.environ, patch_vals)
    _ENV_PATCHER.start()
    # `patch.dict` restores the full original environment on stop.
    for name in alr._GIT_LOCAL_ENV_VARS:
        os.environ.pop(name, None)
    _scrub_ambient_anneal_env(os.environ)


def tearDownModule() -> None:
    global _XDG_TMPDIR
    if _ENV_PATCHER is not None:
        _ENV_PATCHER.stop()
    if _XDG_TMPDIR is not None:
        _XDG_TMPDIR.cleanup()
        _XDG_TMPDIR = None


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------


def _write_cgroup_file(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


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
        limits = alr.compute_workload_memory_envelope(
            cpu_cores=int(FIXED_HW["cpu_cores"]),
            mem_total_mb=int(FIXED_HW["mem_total_mb"]),
            mem_avail_mb=int(FIXED_HW["mem_avail_mb"]),
            user_systemd_active=True,
            t_cg_is_user_service=True,
            cli_concurrency=2,
            mode="file",
        )
        with mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
             mock.patch.object(alr, "resolve_runtime_base", return_value=(Path("/tmp"), True)), \
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
        self.assertEqual(
            kwargs["env"]["LEAN_NUM_THREADS"],
            os.environ.get("LEAN_NUM_THREADS", str(limits["threads"])),
        )

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
        ):
            rc = alr.main(
                ["--mode", "file", "--no-slot-lock", "--", "sh", "-c", "exit 137"]
            )
        self.assertEqual(rc, 137)
        err = err_buf.getvalue()
        self.assertIn("terminated by the OS memory guard", err)
        self.assertIn("MemorySwapMax=0", err)
        self.assertIn("Cgroup v2 Snapshot : anon+shmem=1234M, file=5678M", err)


class TestCliSubprocess(unittest.TestCase):
    """Runs `scripts/anneal-lean-run` as a real subprocess (stdin=/dev/null)."""

    def _cli(
        self, *args: str, env_extra: dict[str, str] | None = None
    ) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory(prefix="anneal-cli-xdg-") as xdg_dir:
            env = _isolated_cli_env(Path(xdg_dir), env_extra)
            return subprocess.run(
                [sys.executable, str(SCRIPT_PATH), *args],
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                check=False,
                env=env,
                timeout=120,
            )

    def test_cli_backward_compatible_probe_and_execution(self) -> None:
        if os.access(SCRIPT_PATH, os.X_OK):
            with tempfile.TemporaryDirectory(prefix="anneal-cli-xdg-") as xdg_dir:
                direct = subprocess.run(
                    [str(SCRIPT_PATH), "--print-limits", "--json"],
                    stdin=subprocess.DEVNULL,
                    capture_output=True,
                    text=True,
                    check=False,
                    env=_isolated_cli_env(Path(xdg_dir)),
                    timeout=120,
                )
            self.assertEqual(direct.returncode, 0, direct.stderr)
            self.assertIn("cgroup_avail_mib", json.loads(direct.stdout))

        probe = self._cli("--probe")
        self.assertEqual(probe.returncode, 0, probe.stderr)
        self.assertIn("Cgroup v2", probe.stdout)
        self.assertIn("Hard RAM Cap", probe.stdout)

        env_json = self._cli(
            "--probe",
            "--json",
            env_extra={
                "ANNEAL_WORKTREE_CONCURRENCY": "2",
                "ANNEAL_LEAN_MEMORY_MAX_MB": "3000",
                "ANNEAL_LEAN_TIMEOUT_SEC": "77",
            },
        )
        self.assertEqual(env_json.returncode, 0, env_json.stderr)
        data = json.loads(env_json.stdout)
        expected_conc = (
            min(2, data["s_heavy_safe"]) if data["is_cg_capped"] else 2
        )
        expected_mem = (
            min(3000, data["w_slice_max_mb"]) if data["is_cg_capped"] else 3000
        )
        self.assertEqual(data["concurrency"], expected_conc)
        self.assertEqual(data["w_eff"], expected_conc)
        self.assertEqual(data["build_slots"], expected_conc)
        self.assertEqual(data["memory_max_mb"], expected_mem)
        if data["w_slice_max_mb"] >= 3000:
            self.assertEqual(data["memory_max_mb"], 3000)
        self.assertEqual(data["timeout_sec"], 77)

        # `--unsafe-ignore-cgroup` bypasses the `w_slice_max_mb` cap on explicit
        # `--memory-max-mb` overrides while keeping `is_cg_capped` and
        # `s_heavy_safe` concurrency clamping fail-closed.
        over_cap_mb = data["w_slice_max_mb"] + 1024
        capped_override = self._cli(
            "--memory-max-mb",
            str(over_cap_mb),
            "--probe",
            "--json",
            env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
        )
        self.assertEqual(capped_override.returncode, 0, capped_override.stderr)
        capped_data = json.loads(capped_override.stdout)
        self.assertEqual(
            capped_data["memory_max_mb"],
            capped_data["w_slice_max_mb"]
            if capped_data["is_cg_capped"]
            else over_cap_mb,
        )
        self.assertEqual(capped_data["concurrency"], expected_conc)

        unsafe_override = self._cli(
            "--unsafe-ignore-cgroup",
            "--memory-max-mb",
            str(over_cap_mb),
            "--probe",
            "--json",
            env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
        )
        self.assertEqual(unsafe_override.returncode, 0, unsafe_override.stderr)
        unsafe_data = json.loads(unsafe_override.stdout)
        self.assertEqual(unsafe_data["memory_max_mb"], over_cap_mb)
        self.assertEqual(unsafe_data["is_cg_capped"], data["is_cg_capped"])
        self.assertEqual(unsafe_data["concurrency"], expected_conc)

        # Populated `$XDG_CONFIG_HOME/anneal/concurrency` is read and subject to
        # the same host cgroup cap (`min(3, s_heavy_safe)` when capped else `3`).
        with tempfile.TemporaryDirectory(prefix="anneal-xdg-cfg-") as cfg_dir:
            cfg_file = Path(cfg_dir) / "anneal" / "concurrency"
            cfg_file.parent.mkdir(parents=True, exist_ok=True)
            cfg_file.write_text("3\n", encoding="utf-8")
            cfg_probe = self._cli(
                "--probe",
                "--json",
                env_extra={"XDG_CONFIG_HOME": cfg_dir},
            )
            self.assertEqual(cfg_probe.returncode, 0, cfg_probe.stderr)
            cfg_data = json.loads(cfg_probe.stdout)
            expected_cfg_conc = (
                min(3, cfg_data["s_heavy_safe"])
                if cfg_data["is_cg_capped"]
                else 3
            )
            self.assertEqual(cfg_data["concurrency"], expected_cfg_conc)
            self.assertEqual(cfg_data["w_eff"], expected_cfg_conc)
            self.assertEqual(cfg_data["build_slots"], expected_cfg_conc)

        bad_env = self._cli(
            "--probe", "--json", env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "abc"}
        )
        self.assertEqual(bad_env.returncode, 0, bad_env.stderr)
        self.assertEqual(json.loads(bad_env.stdout)["concurrency"], 1)

        flags = self._cli(
            "--concurrency", "1", "--memory-max-mb", "2500", "--timeout", "60",
            "--probe", "--json",
        )
        self.assertEqual(flags.returncode, 0, flags.stderr)
        flag_data = json.loads(flags.stdout)
        self.assertEqual(flag_data["concurrency"], 1)
        self.assertEqual(
            flag_data["memory_max_mb"],
            min(2500, flag_data["w_slice_max_mb"])
            if flag_data["is_cg_capped"]
            else 2500,
        )
        self.assertEqual(flag_data["timeout_sec"], 60)

        for argv, expected_rc in (
            (["--mode", "file", "--no-slot-lock", "--concurrency", "1", "--", "true"], 0),
            (["--mode", "build", "--no-slot-lock", "--concurrency", "1", "--", "true"], 0),
            (["--no-slot-lock", "--", "sh", "-c", "exit 5"], 5),
        ):
            res = self._cli(*argv)
            self.assertEqual(res.returncode, expected_rc, (argv, res.stderr))

        usage = self._cli()
        self.assertEqual(usage.returncode, 2)


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
            with mock.patch.object(alr.subprocess, "run") as mock_run:
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
                with self.assertRaises(TimeoutError):
                    with alr.acquire_build_slot(
                        3, 0.12, enabled=True, exclusive=True, runtime_base=rt, poll_interval=0.03
                    ):
                        self.fail("Expected timeout while slot-2 locked")
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
                    [sys.executable, str(SCRIPT_PATH), "--mode", "build", "--", sys.executable, "-c", "print('ok')"],
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
        regimes (even when tests run on a 1-slot cgroup-capped capsule)."""
        with tempfile.TemporaryDirectory(prefix="anneal-conc-iso-") as tmp:
            root = Path(tmp)
            meminfo = root / "meminfo"
            meminfo.write_text(
                "MemTotal:       67108864 kB\nMemAvailable:   50331648 kB\n",
                encoding="utf-8",
            )
            proc_cg = root / "proc_cgroup"
            proc_cg.write_text("0::/user.slice/job.scope\n", encoding="utf-8")

            uncapped_cg = root / "cg_uncapped"
            _write_cgroup_file(uncapped_cg / "user.slice" / "memory.max", "max\n")
            _write_cgroup_file(uncapped_cg / "user.slice" / "job.scope" / "memory.max", "max\n")
            _write_cgroup_file(
                uncapped_cg / "user.slice" / "job.scope" / "memory.stat",
                f"anon {512 * MIB}\nshmem 0\nfile {1024 * MIB}\n",
            )

            capped_1slot_cg = root / "cg_capped_1"
            _write_cgroup_file(
                capped_1slot_cg / "user.slice" / "memory.max", f"{12288 * MIB}\n"
            )
            _write_cgroup_file(
                capped_1slot_cg / "user.slice" / "job.scope" / "memory.max", "max\n"
            )
            _write_cgroup_file(
                capped_1slot_cg / "user.slice" / "job.scope" / "memory.stat",
                f"anon {512 * MIB}\nshmem 0\nfile {1024 * MIB}\n",
            )

            capped_2slot_cg = root / "cg_capped_2"
            _write_cgroup_file(
                capped_2slot_cg / "user.slice" / "memory.max", f"{32768 * MIB}\n"
            )
            _write_cgroup_file(
                capped_2slot_cg / "user.slice" / "job.scope" / "memory.max", "max\n"
            )
            _write_cgroup_file(
                capped_2slot_cg / "user.slice" / "job.scope" / "memory.stat",
                f"anon {512 * MIB}\nshmem 0\nfile {1024 * MIB}\n",
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
                    cpu_cores=16,
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
                    cpu_cores=16,
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
                    cpu_cores=16,
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
                    cpu_cores=16,
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
                    cpu_cores=16,
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
                    cpu_cores=16,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                    override_mem_mb=over_mb,
                    unsafe_ignore_cgroup=True,
                )
                self.assertEqual(cap1_mem_unsafe["memory_max_mb"], over_mb)
                self.assertEqual(cap1_mem_unsafe["concurrency"], 1)

            # Capped 2-slot regime: s_heavy_safe == 2 keeps env=2 and clamps xdg=3 to 2.
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
                    cpu_cores=16,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertTrue(cap2["is_cg_capped"])
                self.assertEqual(cap2["s_heavy_safe"], 2)
                self.assertEqual(cap2["concurrency"], 2)
                self.assertEqual(cap2["build_slots"], 2)

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
