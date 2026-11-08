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
_ENV_PATCHER: Any = None


def setUpModule() -> None:
    global _ENV_PATCHER
    _ENV_PATCHER = mock.patch.dict(os.environ, _HERMETIC_GIT_ENV)
    _ENV_PATCHER.start()
    # `patch.dict` restores the full original environment on stop.
    for name in (
        *alr._GIT_LOCAL_ENV_VARS,
        "ANNEAL_WORKTREE_CONCURRENCY",
        "ANNEAL_LEAN_MEMORY_MAX_MB",
        "ANNEAL_LEAN_TIMEOUT_SEC",
    ):
        os.environ.pop(name, None)


def tearDownModule() -> None:
    if _ENV_PATCHER is not None:
        _ENV_PATCHER.stop()


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------


def _git(repo: Path, *args: str) -> str:
    res = subprocess.run(
        ["git", *args],
        cwd=str(repo),
        env=alr._git_env(),
        stdin=subprocess.DEVNULL,
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0:
        raise AssertionError(
            f"git {' '.join(args)} failed in {repo}: {res.stderr.strip()}"
        )
    return res.stdout.strip()


def _rev(repo: Path, rev: str) -> str | None:
    """Returns the commit `rev` points to in `repo`, or None if absent."""
    res = subprocess.run(
        ["git", "rev-parse", "--verify", "--quiet", f"{rev}^{{commit}}"],
        cwd=str(repo),
        env=alr._git_env(),
        stdin=subprocess.DEVNULL,
        capture_output=True,
        text=True,
        check=False,
    )
    out = res.stdout.strip().lower()
    return out if (res.returncode == 0 and out) else None


def _has_object(repo: Path, sha: str) -> bool:
    return (
        subprocess.run(
            ["git", "cat-file", "-e", f"{sha}^{{commit}}"],
            cwd=str(repo),
            env=alr._git_env(),
            stdin=subprocess.DEVNULL,
            capture_output=True,
            check=False,
        ).returncode
        == 0
    )


def _init_repo(path: Path, object_format: str | None = None) -> None:
    path.mkdir(parents=True, exist_ok=True)
    args = ["init", "-q", "-b", "main"]
    if object_format:
        args.append(f"--object-format={object_format}")
    _git(path, *args)


def _commit_file(repo: Path, filename: str, content: str, msg: str) -> str:
    (repo / filename).write_text(content, encoding="utf-8")
    _git(repo, "add", filename)
    _git(repo, "commit", "-q", "-m", msg)
    return _git(repo, "rev-parse", "HEAD").lower()


def _make_bundle(repo: Path, dest: Path, *refs: str) -> Path:
    _git(repo, "bundle", "create", str(dest), *refs)
    return dest


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
            # Headroom MUST be 32768 - 2048 = 30720 MiB (not 32768 - 30720 = 2048 MiB)
            self.assertEqual(hw["cgroup_avail_mib"], 30720)
            self.assertEqual(hw["mem_total_mb"], 32768)
            self.assertEqual(hw["mem_avail_mb"], 30720)

            limits = alr.compute_limits(hw, mode="build", concurrency=1)
            # per_worker_total_share = int(32768 * 0.70) = 22937
            # avail_share = int(30720 * 0.80) = 24576
            self.assertEqual(limits["memory_max_mb"], 22937)
            self.assertEqual(limits["cgroup_avail_mib"], 30720)
            self.assertEqual(limits["cgroup_memory_max_mib"], 32768)
            # A `memory.current`-based budget would have throttled to the
            # 2048 MiB build floor; guard against regressing to it.
            self.assertGreater(limits["memory_max_mb"], 2048)

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
            self.assertEqual(hw["mem_avail_mb"], 4096)

            limits = alr.compute_limits(hw, mode="build", concurrency=1)
            # avail_share = int(4096 * 0.80) = 3276 MiB
            self.assertEqual(limits["memory_max_mb"], 3276)

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
            self.assertEqual(hw["mem_total_mb"], 4096)
            self.assertEqual(hw["mem_avail_mb"], 512)
            build = alr.compute_limits(hw, mode="build", concurrency=1)
            self.assertEqual(build["memory_max_mb"], 2048)
            file_limits = alr.compute_limits(hw, mode="file", concurrency=1)
            self.assertEqual(file_limits["memory_max_mb"], 1024)

    def test_ancestor_hierarchy_walk_and_root_container_cgroup(self) -> None:
        """Leaf has `memory.max = max`, parent and grandparent have finite limits."""
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            user_slice = cg_root / "user.slice"
            svc = user_slice / "jetski.service"
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
                "0::/user.slice/jetski.service/server\n", encoding="utf-8"
            )

            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            self.assertEqual(
                cg["cgroup_path"], "/user.slice/jetski.service/server"
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
            self.assertIn("Cgroup v2 Memory", line)
            self.assertIn("anon+shmem=800 MiB (anon=700 MiB, shmem=100 MiB)", line)
            self.assertIn("file=2000 MiB", line)
            self.assertIn("current=3000 MiB", line)
            self.assertIn("memory.max=unbounded", line)

            bounded = dict(limits, cgroup_memory_max_mib=4096, cgroup_avail_mib=3296)
            self.assertIn(
                "memory.max=4096 MiB (avail=3296 MiB)",
                alr.format_cgroup_probe_line(bounded),
            )
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
            self.assertIn("Cgroup v2 Memory", text_buf.getvalue())

    def test_probe_and_print_limits_are_identical_aliases(self) -> None:
        outputs: dict[tuple[str, bool], str] = {}
        with mock.patch.object(
            alr, "probe_host_hardware", return_value=dict(FIXED_HW)
        ), mock.patch.object(
            alr, "systemd_user_scope_available", return_value=False
        ):
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
        expected = alr.compute_limits(dict(FIXED_HW), mode="build", concurrency=2)
        for key, value in expected.items():
            self.assertEqual(data[key], value, key)
        self.assertEqual(data["mem_total_mb"], 20480)  # bounded by memory.max
        self.assertEqual(data["mem_avail_mb"], 19480)  # memory.max - (anon+shmem)
        self.assertFalse(data["systemd_user_scope"])

        text = outputs[("--probe", False)]
        self.assertIn(
            "Cgroup v2 Memory   : anon+shmem=1000 MiB (anon=900 MiB, shmem=100 MiB), "
            "file=3000 MiB, current=4200 MiB, memory.max=20480 MiB (avail=19480 MiB)",
            text,
        )
        self.assertIn("(mode=build, W=2)", text)

    def test_systemd_scope_keeps_memory_max_and_zero_swap(self) -> None:
        _FakePopen.calls = []
        with mock.patch.object(
            alr, "probe_host_hardware", return_value=dict(FIXED_HW)
        ), mock.patch.object(
            alr, "systemd_user_scope_available", return_value=True
        ), mock.patch.object(alr.subprocess, "Popen", _FakePopen):
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
        limits = alr.compute_limits(dict(FIXED_HW), mode="file", concurrency=2)
        self.assertEqual(
            argv,
            [
                "systemd-run",
                "--user",
                "--scope",
                "--quiet",
                "-p",
                f"MemoryMax={limits['memory_max_mb']}M",
                "-p",
                "MemorySwapMax=0",
                "-p",
                f"CPUQuota={limits['threads'] * 100}%",
                "-p",
                f"RuntimeMaxSec={limits['timeout_sec'] + 5}s",
                "--",
                "lean",
                "-M",
                str(limits["lean_m_mb"]),
                "Foo.lean",
            ],
        )
        self.assertTrue(kwargs.get("start_new_session"))
        self.assertEqual(
            kwargs["env"]["LEAN_NUM_THREADS"],
            os.environ.get("LEAN_NUM_THREADS", str(limits["threads"])),
        )

    def test_run_bounded_command_success_and_timeout(self) -> None:
        rc_file = alr.main(
            ["--mode", "file", "--concurrency", "1", "--", "true"]
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
        """On timeout, the live child scope (`pid=proc.pid`) must be sampled before `terminate_process_group`."""
        events: list[tuple[str, int | None]] = []
        orig_snap = alr.format_cgroup_diagnostic_snapshot
        orig_term = alr.terminate_process_group

        def spy_snap(
            cg: dict[str, Any] | None = None, pid: int | None = None
        ) -> str:
            events.append(("snap", pid))
            return orig_snap(cg=dict(FAKE_CGROUP_INFO), pid=pid)

        def spy_term(pid: int) -> None:
            events.append(("term", pid))
            orig_term(pid)

        err_buf = io.StringIO()
        with mock.patch("sys.stderr", err_buf), mock.patch.object(
            alr, "format_cgroup_diagnostic_snapshot", side_effect=spy_snap
        ), mock.patch.object(
            alr, "terminate_process_group", side_effect=spy_term
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


# ---------------------------------------------------------------------------
# `--verify-bundle-ff` / `--check-unstable-ff` ancestry guard
# ---------------------------------------------------------------------------


class TestVerifyBundleFF(unittest.TestCase):
    """Tests `--verify-bundle-ff` / `--check-unstable-ff` across all ancestry cases."""

    def test_normalize_git_ref(self) -> None:
        self.assertEqual(alr.normalize_git_ref("unstable"), "refs/heads/unstable")
        self.assertEqual(alr.normalize_git_ref(" unstable "), "refs/heads/unstable")
        self.assertEqual(alr.normalize_git_ref("heads/x"), "refs/heads/x")
        self.assertEqual(alr.normalize_git_ref("tags/v1"), "refs/tags/v1")
        self.assertEqual(alr.normalize_git_ref("refs/heads/unstable"), "refs/heads/unstable")
        self.assertEqual(alr.normalize_git_ref("HEAD"), "HEAD")
        self.assertEqual(alr.normalize_git_ref(""), "refs/heads/unstable")

    def test_no_remote_bundle_and_corrupt_bundle_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            _init_repo(repo)
            c1 = _commit_file(repo, "a.txt", "1\n", "c1")
            _git(repo, "branch", "unstable", c1)

            # 1. Non-existent local bundle -> ok=True, status="no_remote_bundle"
            missing_bundle = tmp_p / "does_not_exist.bundle"
            v_missing = alr.verify_bundle_ff(missing_bundle, repo_dir=repo)
            self.assertTrue(v_missing["ok"])
            self.assertEqual(v_missing["status"], "no_remote_bundle")
            self.assertEqual(v_missing["local_tip"], c1)
            self.assertFalse(v_missing["synced"])

            # 2. Empty (0-byte) bundle -> fail closed
            empty_bundle = tmp_p / "empty.bundle"
            empty_bundle.write_bytes(b"")
            v_empty = alr.verify_bundle_ff(empty_bundle, repo_dir=repo)
            self.assertFalse(v_empty["ok"])
            self.assertEqual(v_empty["status"], "bundle_error")

            # 3. Corrupt non-bundle file -> fail closed
            corrupt_bundle = tmp_p / "corrupt.bundle"
            corrupt_bundle.write_text("not a git bundle\n", encoding="utf-8")
            v_corrupt = alr.verify_bundle_ff(corrupt_bundle, repo_dir=repo)
            self.assertFalse(v_corrupt["ok"])
            self.assertEqual(v_corrupt["status"], "bundle_error")

            # 4. Valid signature with a garbage ref line -> fail closed
            garbage = tmp_p / "garbage.bundle"
            garbage.write_text(
                "# v2 git bundle\nnot-a-sha refs/heads/unstable\n\n",
                encoding="utf-8",
            )
            v_garbage = alr.verify_bundle_ff(garbage, repo_dir=repo)
            self.assertFalse(v_garbage["ok"])
            self.assertEqual(v_garbage["status"], "bundle_error")

            # 5. Directory passed as bundle path -> fail closed
            v_dir = alr.verify_bundle_ff(repo, repo_dir=repo)
            self.assertFalse(v_dir["ok"])
            self.assertEqual(v_dir["status"], "bundle_error")

            # 6. Broken symlink -> fail closed
            broken_link = tmp_p / "broken.bundle"
            broken_link.symlink_to(tmp_p / "nonexistent_target.bundle")
            v_link = alr.verify_bundle_ff(broken_link, repo_dir=repo)
            self.assertFalse(v_link["ok"])
            self.assertEqual(v_link["status"], "bundle_error")

            # 7. Valid bundle carrying <ref>, but repo_dir is not a git repo
            good = _make_bundle(repo, tmp_p / "good.bundle", "refs/heads/unstable")
            not_repo = tmp_p / "not_a_repo"
            not_repo.mkdir()
            for sync in (False, True):
                v_norepo = alr.verify_bundle_ff(
                    good, repo_dir=not_repo, sync_if_behind=sync
                )
                self.assertFalse(v_norepo["ok"])
                self.assertEqual(v_norepo["status"], "missing_local_ref")
                self.assertEqual(v_norepo["remote_tip"], c1)
            v_nodir = alr.verify_bundle_ff(good, repo_dir=tmp_p / "no_such_dir")
            self.assertFalse(v_nodir["ok"])
            self.assertEqual(v_nodir["status"], "missing_local_ref")

    def test_up_to_date_fast_forward_stale_behind_and_diverged(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            _init_repo(repo)
            c1 = _commit_file(repo, "a.txt", "1\n", "c1")
            c2 = _commit_file(repo, "a.txt", "2\n", "c2")
            c3 = _commit_file(repo, "a.txt", "3\n", "c3")

            # Bundle with only main (no unstable ref)
            main_only_bundle = _make_bundle(
                repo, tmp_p / "main_only.bundle", "refs/heads/main"
            )
            v_no_ref = alr.verify_bundle_ff(main_only_bundle, repo_dir=repo)
            self.assertTrue(v_no_ref["ok"])
            self.assertEqual(v_no_ref["status"], "no_remote_ref")

            # Bundle with refs/heads/unstable at c2 plus an unrelated `side` at c3
            _git(repo, "branch", "-f", "unstable", c2)
            _git(repo, "branch", "-f", "side", c3)
            bundle_c2 = _make_bundle(
                repo, tmp_p / "c2.bundle", "refs/heads/unstable", "refs/heads/side"
            )
            _git(repo, "branch", "-f", "side", c1)  # local side diverges from bundle

            # Case: up_to_date (local unstable == c2)
            v_eq = alr.verify_bundle_ff(bundle_c2, repo_dir=repo)
            self.assertTrue(v_eq["ok"])
            self.assertEqual(v_eq["status"], "up_to_date")
            self.assertEqual(v_eq["remote_tip"], c2)
            self.assertEqual(v_eq["local_tip"], c2)
            self.assertEqual(
                set(v_eq),
                {"ok", "status", "bundle_path", "ref", "remote_tip", "local_tip", "synced", "message"},
            )

            # Case: fast_forward (local unstable == c3, remote == c2)
            _git(repo, "branch", "-f", "unstable", c3)
            v_ff = alr.verify_bundle_ff(bundle_c2, ref="unstable", repo_dir=repo)
            self.assertTrue(v_ff["ok"])
            self.assertEqual(v_ff["status"], "fast_forward")
            self.assertEqual(v_ff["ref"], "refs/heads/unstable")
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c3)

            # Case: stale_behind (local unstable == c1, remote == c2)
            _git(repo, "branch", "-f", "unstable", c1)
            v_behind = alr.verify_bundle_ff(bundle_c2, repo_dir=repo)
            self.assertFalse(v_behind["ok"])
            self.assertFalse(v_behind["synced"])
            self.assertEqual(v_behind["status"], "stale_behind")
            self.assertIn("1 commit(s) behind", v_behind["message"])
            self.assertIn(c1, v_behind["message"])
            self.assertIn(c2, v_behind["message"])
            self.assertIn("git x20-pull", v_behind["message"])
            self.assertIn("--sync-if-behind", v_behind["message"])
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c1)

            # CLI exit code 1 + JSON verdict + stderr diagnostics, no mutation
            out_buf = io.StringIO()
            err_buf = io.StringIO()
            with mock.patch("sys.stdout", out_buf), mock.patch(
                "sys.stderr", err_buf
            ):
                rc_fail = alr.main(
                    [
                        "--check-unstable-ff",
                        str(bundle_c2),
                        "--repo-dir",
                        str(repo),
                        "--json",
                    ]
                )
            self.assertEqual(rc_fail, 1)
            self.assertEqual(json.loads(out_buf.getvalue())["status"], "stale_behind")
            self.assertIn("ERROR:", err_buf.getvalue())
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c1)

            # `--local-rev` override + `--sync-if-behind` must refuse to mutate
            v_override = alr.verify_bundle_ff(
                bundle_c2, repo_dir=repo, local_rev=c1, sync_if_behind=True
            )
            self.assertFalse(v_override["ok"])
            self.assertFalse(v_override["synced"])
            self.assertEqual(v_override["status"], "stale_behind")
            self.assertIn(
                f"Local {c1} [--local-rev for refs/heads/unstable] ({c1})",
                v_override["message"],
            )
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c1)

            # Case: synced_fast_forward (non-checked-out branch) moves ONLY <ref>
            v_synced = alr.verify_bundle_ff(
                bundle_c2, repo_dir=repo, sync_if_behind=True
            )
            self.assertTrue(v_synced["ok"])
            self.assertTrue(v_synced["synced"])
            self.assertEqual(v_synced["status"], "synced_fast_forward")
            self.assertEqual(v_synced["local_tip"], c2)
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c2)
            self.assertEqual(_rev(repo, "refs/heads/side"), c1)
            self.assertEqual(_rev(repo, "refs/heads/main"), c3)
            reflog = _git(repo, "reflog", "show", "--format=%gs", "refs/heads/unstable")
            self.assertIn("anneal-lean-run --sync-if-behind", reflog)

            # Case: diverged branch (with and without --sync-if-behind)
            _git(repo, "checkout", "-q", "-b", "div_branch", c1)
            c_div = _commit_file(repo, "div.txt", "diverged\n", "c_div")
            _git(repo, "checkout", "-q", "main")
            _git(repo, "branch", "-f", "unstable", c_div)
            for sync in (False, True):
                v_div = alr.verify_bundle_ff(
                    bundle_c2, repo_dir=repo, sync_if_behind=sync
                )
                self.assertFalse(v_div["ok"])
                self.assertFalse(v_div["synced"])
                self.assertEqual(v_div["status"], "diverged")
                self.assertIn("diverged", v_div["message"])
                self.assertEqual(_rev(repo, "refs/heads/unstable"), c_div)

    def test_unfetched_remote_tip_and_missing_local_ref_sync(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            remote_repo = tmp_p / "remote_repo"
            local_repo = tmp_p / "local_repo"
            _init_repo(remote_repo)
            c1 = _commit_file(remote_repo, "f.txt", "v1\n", "c1")
            _git(remote_repo, "branch", "unstable", c1)
            _git(remote_repo, "branch", "side", c1)

            # Clone remote_repo into local_repo at c1
            subprocess.run(
                ["git", "clone", "-q", str(remote_repo), str(local_repo)],
                env=alr._git_env(),
                check=True,
                capture_output=True,
            )
            _git(local_repo, "branch", "unstable", c1)
            _git(local_repo, "branch", "side", c1)

            # Advance remote unstable to c2 and side to c3 (unfetched locally)
            _git(remote_repo, "checkout", "-q", "unstable")
            c2 = _commit_file(remote_repo, "f.txt", "v2\n", "c2")
            _git(remote_repo, "checkout", "-q", "side")
            c3 = _commit_file(remote_repo, "g.txt", "side\n", "c3")
            bundle_c2 = _make_bundle(
                remote_repo,
                tmp_p / "remote_c2.bundle",
                "refs/heads/unstable",
                "refs/heads/side",
            )

            # Without --sync-if-behind: unfetched_remote_tip, nothing fetched/moved
            v_unfetched = alr.verify_bundle_ff(
                bundle_c2, repo_dir=local_repo, sync_if_behind=False
            )
            self.assertFalse(v_unfetched["ok"])
            self.assertEqual(v_unfetched["status"], "unfetched_remote_tip")
            self.assertIn("git x20-pull", v_unfetched["message"])
            self.assertFalse(_has_object(local_repo, c2))
            self.assertEqual(_rev(local_repo, "refs/heads/unstable"), c1)

            # With --sync-if-behind: fetches c2 and fast-forwards ONLY unstable
            v_sync_unfetched = alr.verify_bundle_ff(
                bundle_c2, repo_dir=local_repo, sync_if_behind=True
            )
            self.assertTrue(v_sync_unfetched["ok"])
            self.assertTrue(v_sync_unfetched["synced"])
            self.assertEqual(v_sync_unfetched["status"], "synced_fast_forward")
            self.assertEqual(v_sync_unfetched["local_tip"], c2)
            self.assertEqual(_rev(local_repo, "refs/heads/unstable"), c2)
            # Unrelated refs carried by the same bundle are never clobbered.
            self.assertEqual(_rev(local_repo, "refs/heads/side"), c1)
            self.assertNotEqual(_rev(local_repo, "refs/heads/side"), c3)

            # Delete local unstable to test missing_local_ref
            _git(local_repo, "branch", "-D", "unstable")
            v_missing_ref = alr.verify_bundle_ff(
                bundle_c2, repo_dir=local_repo, sync_if_behind=False
            )
            self.assertFalse(v_missing_ref["ok"])
            self.assertEqual(v_missing_ref["status"], "missing_local_ref")
            self.assertIsNone(_rev(local_repo, "refs/heads/unstable"))

            # With --sync-if-behind and explicit --local-rev override -> refuses to sync
            v_override = alr.verify_bundle_ff(
                bundle_c2,
                repo_dir=local_repo,
                local_rev="refs/heads/nonexistent",
                sync_if_behind=True,
            )
            self.assertFalse(v_override["ok"])
            self.assertEqual(v_override["status"], "missing_local_ref")
            self.assertIsNone(_rev(local_repo, "refs/heads/unstable"))

            # With --sync-if-behind and default --local-rev -> recreates unstable at c2
            v_sync_missing = alr.verify_bundle_ff(
                bundle_c2, repo_dir=local_repo, sync_if_behind=True
            )
            self.assertTrue(v_sync_missing["ok"])
            self.assertTrue(v_sync_missing["synced"])
            self.assertEqual(v_sync_missing["status"], "synced_missing_local_ref")
            self.assertEqual(v_sync_missing["local_tip"], c2)
            self.assertEqual(_rev(local_repo, "refs/heads/unstable"), c2)
            self.assertEqual(_rev(local_repo, "refs/heads/side"), c1)

    def test_worktree_safety_dirty_and_linked_worktrees(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            _init_repo(repo)
            c1 = _commit_file(repo, "a.txt", "1\n", "c1")
            c2 = _commit_file(repo, "a.txt", "2\n", "c2")
            _git(repo, "branch", "unstable", c2)
            bundle_c2 = _make_bundle(repo, tmp_p / "c2.bundle", "refs/heads/unstable")

            # Reset unstable to c1 and check it out in `repo`
            _git(repo, "checkout", "-q", "-B", "unstable", c1)

            # 1. Dirty checked-out worktree -> --sync-if-behind must refuse!
            (repo / "dirty.txt").write_text("uncommitted\n", encoding="utf-8")
            v_dirty = alr.verify_bundle_ff(
                bundle_c2, repo_dir=repo, sync_if_behind=True
            )
            self.assertFalse(v_dirty["ok"])
            self.assertFalse(v_dirty["synced"])
            self.assertEqual(v_dirty["status"], "stale_behind")
            self.assertIn("dirty worktree", v_dirty["message"])
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c1)
            self.assertEqual(
                (repo / "dirty.txt").read_text(encoding="utf-8"), "uncommitted\n"
            )
            self.assertEqual((repo / "a.txt").read_text(encoding="utf-8"), "1\n")

            # 1b. Dirty tracked file (no untracked files) -> refuse as well
            (repo / "dirty.txt").unlink()
            (repo / "a.txt").write_text("local edit\n", encoding="utf-8")
            v_dirty2 = alr.verify_bundle_ff(
                bundle_c2, repo_dir=repo, sync_if_behind=True
            )
            self.assertFalse(v_dirty2["ok"])
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c1)
            self.assertEqual(
                (repo / "a.txt").read_text(encoding="utf-8"), "local edit\n"
            )
            _git(repo, "checkout", "--", "a.txt")

            # 2. Clean checked-out worktree -> fast-forwards via merge --ff-only
            v_clean_co = alr.verify_bundle_ff(
                bundle_c2, repo_dir=repo, sync_if_behind=True
            )
            self.assertTrue(v_clean_co["ok"])
            self.assertTrue(v_clean_co["synced"])
            self.assertEqual(v_clean_co["status"], "synced_fast_forward")
            self.assertEqual((repo / "a.txt").read_text(encoding="utf-8"), "2\n")
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c2)
            self.assertEqual(_rev(repo, "HEAD"), c2)
            self.assertEqual(_git(repo, "status", "--porcelain"), "")

            # 3. `unstable` checked out in `repo`; run from linked worktree `wt2`
            _git(repo, "reset", "-q", "--hard", c1)
            wt2 = tmp_p / "wt2"
            _git(repo, "worktree", "add", "-q", "-b", "feature", str(wt2), c1)
            v_linked = alr.verify_bundle_ff(
                bundle_c2, repo_dir=wt2, sync_if_behind=True
            )
            self.assertFalse(v_linked["ok"])
            self.assertFalse(v_linked["synced"])
            self.assertEqual(v_linked["status"], "stale_behind")
            self.assertIn("linked worktree", v_linked["message"])
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c1)

            # 4. `unstable` checked out (clean) in the linked worktree that IS
            #    `--repo-dir` -> allowed, and that worktree is updated.
            _git(repo, "checkout", "-q", "main")
            _git(wt2, "checkout", "-q", "unstable")
            v_in_linked = alr.verify_bundle_ff(
                bundle_c2, repo_dir=wt2, sync_if_behind=True
            )
            self.assertTrue(v_in_linked["ok"])
            self.assertEqual(v_in_linked["status"], "synced_fast_forward")
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c2)
            self.assertEqual((wt2 / "a.txt").read_text(encoding="utf-8"), "2\n")
            self.assertEqual(_git(wt2, "status", "--porcelain"), "")

    def test_sync_never_moves_head_tags_or_non_branch_refs(self) -> None:
        """`update-ref HEAD` would move the checked-out branch under its index."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            _init_repo(repo)
            c1 = _commit_file(repo, "a.txt", "1\n", "c1")
            c2 = _commit_file(repo, "a.txt", "2\n", "c2")
            _git(repo, "tag", "v1", c2)
            bundle = _make_bundle(repo, tmp_p / "b.bundle", "HEAD", "refs/tags/v1")
            _git(repo, "reset", "-q", "--hard", c1)
            _git(repo, "tag", "-f", "v1", c1)

            v_head = alr.verify_bundle_ff(
                bundle, ref="HEAD", repo_dir=repo, sync_if_behind=True
            )
            self.assertFalse(v_head["ok"])
            self.assertFalse(v_head["synced"])
            self.assertEqual(v_head["status"], "stale_behind")
            self.assertIn("refs/heads/*", v_head["message"])
            self.assertEqual(_rev(repo, "refs/heads/main"), c1)
            self.assertEqual(_git(repo, "status", "--porcelain"), "")

            v_tag = alr.verify_bundle_ff(
                bundle, ref="refs/tags/v1", repo_dir=repo, sync_if_behind=True
            )
            self.assertFalse(v_tag["ok"])
            self.assertEqual(v_tag["status"], "stale_behind")
            self.assertEqual(_rev(repo, "refs/tags/v1"), c1)

    def test_local_rev_shorthand_resolves_branch_not_same_named_tag(self) -> None:
        """git DWIM resolves `unstable` to `refs/tags/unstable` before the branch."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            _init_repo(repo)
            c1 = _commit_file(repo, "a.txt", "1\n", "c1")
            c2 = _commit_file(repo, "a.txt", "2\n", "c2")
            _git(repo, "branch", "unstable", c2)
            bundle = _make_bundle(repo, tmp_p / "b.bundle", "refs/heads/unstable")
            _git(repo, "branch", "-f", "unstable", c1)  # stale branch
            _git(repo, "tag", "unstable", c2)  # same-named tag at the remote tip

            for spelled in ("unstable", "heads/unstable", "refs/heads/unstable"):
                v = alr.verify_bundle_ff(bundle, repo_dir=repo, local_rev=spelled)
                self.assertFalse(v["ok"], spelled)
                self.assertEqual(v["status"], "stale_behind", spelled)
                self.assertEqual(v["local_tip"], c1, spelled)

            # `--local-rev unstable` is not an override, so syncing is allowed
            v_sync = alr.verify_bundle_ff(
                bundle, repo_dir=repo, local_rev="unstable", sync_if_behind=True
            )
            self.assertTrue(v_sync["ok"])
            self.assertEqual(v_sync["status"], "synced_fast_forward")
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c2)

    def test_inherited_git_env_does_not_redirect_repo_dir(self) -> None:
        """A `pre-push` hook exports `GIT_DIR`; `--repo-dir` must stay authoritative."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            stale = tmp_p / "stale"
            _init_repo(stale)
            c1 = _commit_file(stale, "a.txt", "1\n", "c1")
            c2 = _commit_file(stale, "a.txt", "2\n", "c2")
            _git(stale, "branch", "unstable", c2)
            bundle = _make_bundle(stale, tmp_p / "b.bundle", "refs/heads/unstable")
            other = tmp_p / "other"
            subprocess.run(
                ["git", "clone", "-q", str(stale), str(other)],
                env=alr._git_env(),
                check=True,
                capture_output=True,
            )
            _git(other, "branch", "unstable", "origin/unstable")
            _git(stale, "branch", "-f", "unstable", c1)

            hook_env = {
                "GIT_DIR": str(other / ".git"),
                "GIT_WORK_TREE": str(other),
                "GIT_INDEX_FILE": str(other / ".git" / "index"),
            }
            with mock.patch.dict(os.environ, hook_env):
                v = alr.verify_bundle_ff(bundle, repo_dir=stale)
                self.assertFalse(v["ok"])
                self.assertEqual(v["status"], "stale_behind")
                self.assertEqual(v["local_tip"], c1)
                v_sync = alr.verify_bundle_ff(
                    bundle, repo_dir=stale, sync_if_behind=True
                )
            self.assertTrue(v_sync["ok"])
            self.assertEqual(_rev(stale, "refs/heads/unstable"), c2)
            self.assertEqual(_rev(other, "refs/heads/unstable"), c2)

    def test_sha256_repository_bundle(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo256"
            try:
                _init_repo(repo, object_format="sha256")
            except AssertionError:
                self.skipTest("git lacks --object-format=sha256 support")
            c1 = _commit_file(repo, "a.txt", "1\n", "c1")
            c2 = _commit_file(repo, "a.txt", "2\n", "c2")
            self.assertEqual(len(c2), 64)
            _git(repo, "branch", "unstable", c2)
            bundle = _make_bundle(repo, tmp_p / "b.bundle", "refs/heads/unstable")
            v_eq = alr.verify_bundle_ff(bundle, repo_dir=repo)
            self.assertTrue(v_eq["ok"], v_eq["message"])
            self.assertEqual(v_eq["status"], "up_to_date")
            _git(repo, "branch", "-f", "unstable", c1)
            v_behind = alr.verify_bundle_ff(bundle, repo_dir=repo)
            self.assertEqual(v_behind["status"], "stale_behind")
            v_sync = alr.verify_bundle_ff(bundle, repo_dir=repo, sync_if_behind=True)
            self.assertEqual(v_sync["status"], "synced_fast_forward")
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c2)

    def test_sync_if_behind_blocks_active_rebase_bisect_and_sequencer_state(self) -> None:
        """A worktree mid-rebase, mid-bisect, or mid-merge on `<ref>` must not have `<ref>` moved underneath it."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            _init_repo(repo)
            c1 = _commit_file(repo, "a.txt", "1\n", "c1")
            c2 = _commit_file(repo, "a.txt", "2\n", "c2")
            _git(repo, "branch", "unstable", c2)
            bundle = _make_bundle(repo, tmp_p / "b.bundle", "refs/heads/unstable")
            _git(repo, "branch", "-f", "unstable", c1)

            # 1. Linked worktree has detached HEAD while rebasing `refs/heads/unstable`.
            wt = tmp_p / "wt-rebase"
            _git(repo, "worktree", "add", "-q", "--detach", str(wt), c1)
            wt_git_dir = alr._worktree_git_dir(wt)
            self.assertIsNotNone(wt_git_dir)
            assert wt_git_dir is not None
            rb_dir = wt_git_dir / "rebase-merge"
            rb_dir.mkdir(parents=True)
            (rb_dir / "head-name").write_text("refs/heads/unstable\n", encoding="utf-8")

            v_rb = alr.verify_bundle_ff(bundle, repo_dir=repo, sync_if_behind=True)
            self.assertFalse(v_rb["ok"])
            self.assertEqual(v_rb["status"], "stale_behind")
            self.assertIn("active rebase or bisect", v_rb["message"])
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c1)
            (rb_dir / "head-name").unlink()
            rb_dir.rmdir()

            # 2. Linked worktree has detached HEAD while bisecting `unstable`.
            (wt_git_dir / "BISECT_START").write_text("unstable\n", encoding="utf-8")
            v_bi = alr.verify_bundle_ff(bundle, repo_dir=repo, sync_if_behind=True)
            self.assertFalse(v_bi["ok"])
            self.assertEqual(v_bi["status"], "stale_behind")
            self.assertIn("active rebase or bisect", v_bi["message"])
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c1)
            (wt_git_dir / "BISECT_START").unlink()
            _git(repo, "worktree", "remove", "--force", str(wt))

            # 3. Checked-out worktree on `unstable` has an in-progress MERGE_HEAD.
            _git(repo, "checkout", "-q", "unstable")
            main_git_dir = alr._worktree_git_dir(repo)
            assert main_git_dir is not None
            (main_git_dir / "MERGE_HEAD").write_text(f"{c2}\n", encoding="utf-8")
            v_mh = alr.verify_bundle_ff(bundle, repo_dir=repo, sync_if_behind=True)
            self.assertFalse(v_mh["ok"])
            self.assertEqual(v_mh["status"], "stale_behind")
            self.assertIn("in-progress git operation (MERGE_HEAD)", v_mh["message"])
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c1)
            (main_git_dir / "MERGE_HEAD").unlink()

    def test_option_injection_and_relative_bundle_path_hardening(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            _init_repo(repo)
            c1 = _commit_file(repo, "a.txt", "1\n", "c1")
            _git(repo, "branch", "unstable", c1)
            bundle = _make_bundle(repo, tmp_p / "b.bundle", "refs/heads/unstable")

            # Leading-dash `--local-rev` values must not be interpreted as git flags.
            for bad_rev in ("-n", "--branches", "--all"):
                v_bad = alr.verify_bundle_ff(bundle, repo_dir=repo, local_rev=bad_rev)
                self.assertFalse(v_bad["ok"], bad_rev)
                self.assertEqual(v_bad["status"], "missing_local_ref", bad_rev)

            # Relative bundle_file passed to `parse_bundle_heads` when `cwd` is `repo`
            # must resolve against the caller's cwd rather than `repo`.
            prev_cwd = os.getcwd()
            try:
                os.chdir(tmp_p)
                ok_rel, heads_rel, err_rel = alr.parse_bundle_heads(
                    Path("b.bundle"), cwd=repo
                )
            finally:
                os.chdir(prev_cwd)
            self.assertTrue(ok_rel, err_rel)
            self.assertEqual(heads_rel.get("refs/heads/unstable"), c1)

    def test_bundle_with_conflicting_duplicate_ref_tips_fails_closed(self) -> None:
        """`git bundle list-heads` accepts a header naming <ref> twice; refuse it."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            _init_repo(repo)
            c1 = _commit_file(repo, "a.txt", "1\n", "c1")
            c2 = _commit_file(repo, "a.txt", "2\n", "c2")
            _git(repo, "branch", "unstable", c2)
            good = _make_bundle(repo, tmp_p / "good.bundle", "refs/heads/unstable")
            data = good.read_bytes()
            hdr_end = data.index(b"\n\n")

            def with_extra_head(sha: str) -> Path:
                out = tmp_p / f"dup-{sha[:7]}.bundle"
                out.write_bytes(
                    data[:hdr_end] + f"\n{sha} refs/heads/unstable".encode() + data[hdr_end:]
                )
                return out

            conflicting = with_extra_head(c1)
            listed = _git(repo, "bundle", "list-heads", str(conflicting))
            self.assertEqual(len(listed.splitlines()), 2)  # git itself accepts it
            _git(repo, "branch", "-f", "unstable", c1)
            for sync in (False, True):
                v = alr.verify_bundle_ff(conflicting, repo_dir=repo, sync_if_behind=sync)
                self.assertFalse(v["ok"])
                self.assertEqual(v["status"], "bundle_error")
                self.assertIn("conflicting tips", v["message"])
                self.assertEqual(_rev(repo, "refs/heads/unstable"), c1)

            # An identical duplicate is unambiguous and still verified normally.
            identical = with_extra_head(c2)
            v_same = alr.verify_bundle_ff(identical, repo_dir=repo)
            self.assertEqual(v_same["status"], "stale_behind")

    def test_sync_missing_ref_on_unborn_checked_out_branch(self) -> None:
        """`git init -b unstable` checks out an unborn <ref>: create it via
        `reset --hard` only when that worktree is clean."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            src = tmp_p / "src"
            _init_repo(src)
            c1 = _commit_file(src, "a.txt", "1\n", "c1")
            _git(src, "branch", "unstable", c1)
            bundle = _make_bundle(src, tmp_p / "b.bundle", "refs/heads/unstable")

            fresh = tmp_p / "fresh"
            fresh.mkdir()
            _git(fresh, "init", "-q", "-b", "unstable")
            (fresh / "notes.txt").write_text("wip\n", encoding="utf-8")
            v_dirty = alr.verify_bundle_ff(bundle, repo_dir=fresh, sync_if_behind=True)
            self.assertFalse(v_dirty["ok"])
            self.assertFalse(v_dirty["synced"])
            self.assertEqual(v_dirty["status"], "missing_local_ref")
            self.assertIn("dirty worktree", v_dirty["message"])
            self.assertIsNone(_rev(fresh, "refs/heads/unstable"))
            self.assertEqual(
                (fresh / "notes.txt").read_text(encoding="utf-8"), "wip\n"
            )

            (fresh / "notes.txt").unlink()
            v = alr.verify_bundle_ff(bundle, repo_dir=fresh, sync_if_behind=True)
            self.assertTrue(v["ok"], v["message"])
            self.assertTrue(v["synced"])
            self.assertEqual(v["status"], "synced_missing_local_ref")
            self.assertEqual(_rev(fresh, "refs/heads/unstable"), c1)
            self.assertEqual(_git(fresh, "symbolic-ref", "HEAD"), "refs/heads/unstable")
            self.assertEqual((fresh / "a.txt").read_text(encoding="utf-8"), "1\n")
            self.assertEqual(_git(fresh, "status", "--porcelain"), "")

    def test_sync_refuses_during_real_interactive_rebase_of_ref(self) -> None:
        """A real `git rebase -i` stop detaches HEAD (so `worktree list` shows no
        branch); <ref> must still not be moved underneath the rebase."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            _init_repo(repo)
            c0 = _commit_file(repo, "a.txt", "0\n", "c0")
            c1 = _commit_file(repo, "a.txt", "1\n", "c1")
            c2 = _commit_file(repo, "a.txt", "2\n", "c2")
            _git(repo, "branch", "unstable", c2)
            bundle = _make_bundle(repo, tmp_p / "b.bundle", "refs/heads/unstable")
            _git(repo, "checkout", "-q", "-B", "unstable", c1)

            env = dict(alr._git_env(), GIT_SEQUENCE_EDITOR="sed -i -e 's/^pick/edit/'")
            stop = subprocess.run(
                ["git", "rebase", "-i", c0],
                cwd=str(repo),
                env=env,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(stop.returncode, 0, stop.stderr)
            wt_list = _git(repo, "worktree", "list", "--porcelain")
            self.assertIn("detached", wt_list)
            self.assertNotIn("branch refs/heads/unstable", wt_list)

            v = alr.verify_bundle_ff(bundle, repo_dir=repo, sync_if_behind=True)
            self.assertFalse(v["ok"])
            self.assertFalse(v["synced"])
            self.assertEqual(v["status"], "stale_behind")
            self.assertIn("active rebase or bisect", v["message"])
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c1)

            subprocess.run(
                ["git", "rebase", "--abort"],
                cwd=str(repo),
                env=env,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                check=True,
            )
            v_after = alr.verify_bundle_ff(bundle, repo_dir=repo, sync_if_behind=True)
            self.assertTrue(v_after["ok"], v_after["message"])
            self.assertEqual(v_after["status"], "synced_fast_forward")
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c2)
            self.assertEqual((repo / "a.txt").read_text(encoding="utf-8"), "2\n")

    def test_unfetched_diverged_remote_with_sync_fetches_then_refuses(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            remote = tmp_p / "remote"
            local = tmp_p / "local"
            _init_repo(remote)
            c1 = _commit_file(remote, "f.txt", "v1\n", "c1")
            _git(remote, "branch", "unstable", c1)
            subprocess.run(
                ["git", "clone", "-q", str(remote), str(local)],
                env=alr._git_env(),
                check=True,
                capture_output=True,
            )
            _git(local, "checkout", "-q", "-b", "unstable", "origin/unstable")
            c_local = _commit_file(local, "local.txt", "mine\n", "c_local")
            _git(local, "checkout", "-q", "main")
            _git(remote, "checkout", "-q", "unstable")
            c2 = _commit_file(remote, "f.txt", "v2\n", "c2")
            bundle = _make_bundle(remote, tmp_p / "b.bundle", "refs/heads/unstable")

            v_no_sync = alr.verify_bundle_ff(bundle, repo_dir=local)
            self.assertEqual(v_no_sync["status"], "unfetched_remote_tip")
            self.assertFalse(_has_object(local, c2))

            v_sync = alr.verify_bundle_ff(bundle, repo_dir=local, sync_if_behind=True)
            self.assertFalse(v_sync["ok"])
            self.assertFalse(v_sync["synced"])
            self.assertEqual(v_sync["status"], "diverged")
            self.assertEqual(v_sync["remote_tip"], c2)
            self.assertEqual(v_sync["local_tip"], c_local)
            self.assertTrue(_has_object(local, c2))  # fetched to decide, never applied
            self.assertEqual(_rev(local, "refs/heads/unstable"), c_local)


# ---------------------------------------------------------------------------
# x20 staging via `fileutil` (never through the `x20fsd` FUSE mount)
# ---------------------------------------------------------------------------

# Verbatim `fileutil` messages captured on a Team Capsule (paths shortened).
_URI = "/x20/teams/anneal-agent/u/anneal.bundle"
REAL_CP_REMOTE_NOT_FOUND = (
    "E1108 19:40:48.692519 2132517 fileutil.cc:1786] couldn't copy "
    f"`{_URI}' to `/tmp/anneal-bundle-ff-x/remote.bundle': generic::not_found: "
    f"{_URI}: File not found: /teams/anneal-agent/u/anneal.bundle "
    "[storage_x20.pb.Error] { code: NO_SUCH_FILE_OR_DIRECTORY }"
)
REAL_STAT_REMOTE_NOT_FOUND = (
    "E1108 19:42:12.326550 2136735 fileutil.cc:6923] Failed to stat "
    f"{_URI}: NOT_FOUND: {_URI}: File not found: /teams/anneal-agent/u/anneal.bundle "
    "at version: 1794166930727722 [type.googleapis.com/util.MessageSetPayload="
    "'[storage_x20.pb.Error] { code: NO_SUCH_FILE_OR_DIRECTORY }']"
)
REAL_CP_LOCAL_ENOENT = (
    "E1108 19:41:18.402671 2134521 fileutil.cc:1786] couldn't copy "
    f"`{_URI}' to `/tmp/anneal-bundle-ff-x/remote.bundle': generic::not_found: "
    "open failed for /tmp/anneal-bundle-ff-x/remote.bundle: No such file or directory"
)

MOCK_FILEUTIL_SRC = r'''#!/usr/bin/env python3
import json, os, shutil, sys, time

argv = sys.argv[1:]
try:
    stdin_is_devnull = os.path.samestat(os.fstat(0), os.stat(os.devnull))
except OSError:
    stdin_is_devnull = False
with open(os.environ["MOCK_FILEUTIL_LOG"], "a", encoding="utf-8") as f:
    f.write(json.dumps({"argv": argv, "stdin_is_devnull": stdin_is_devnull}) + "\n")

mode = os.environ.get("MOCK_FILEUTIL_MODE", "ok")
op = argv[1] if len(argv) > 1 else ""
uri = argv[2] if op == "stat" else (argv[3] if len(argv) > 3 else "")
dest = argv[4] if (op == "cp" and len(argv) > 4) else ""
rel = uri[len("/x20"):] if uri.startswith("/x20/") else uri
remote_nf_cp = ("E0000 fileutil.cc:1786] couldn't copy `%s' to `%s': generic::not_found: "
                "%s: File not found: %s [storage_x20.pb.Error] "
                "{ code: NO_SUCH_FILE_OR_DIRECTORY }\n" % (uri, dest, uri, rel))
remote_nf_stat = ("E0000 fileutil.cc:6923] Failed to stat %s: NOT_FOUND: %s: File not "
                  "found: %s at version: 1 [type.googleapis.com/util.MessageSetPayload="
                  "'[storage_x20.pb.Error] { code: NO_SUCH_FILE_OR_DIRECTORY }']\n"
                  % (uri, uri, rel))

def fail(msg):
    sys.stderr.write(msg)
    sys.exit(1)

if op == "stat":
    if mode in ("not_found",):
        fail(remote_nf_stat)
    if mode == "cp_not_found_stat_rpc":
        fail("E0000 Failed to stat %s: DEADLINE_EXCEEDED: RPC timed out\n" % uri)
    sys.stdout.write('version: "0"\nlength: 1\nfile_type: FILE\n')
    sys.exit(0)

if op != "cp":
    fail("unexpected op %r\n" % op)
if mode == "ok":
    shutil.copyfile(os.environ["MOCK_FILEUTIL_SRC_BUNDLE"], dest)
    sys.exit(0)
if mode in ("not_found", "cp_not_found_stat_exists", "cp_not_found_stat_rpc"):
    fail(remote_nf_cp)
if mode == "local_enoent":
    fail("E0000 fileutil.cc:1786] couldn't copy `%s' to `%s': generic::not_found: "
         "open failed for %s: No such file or directory\n" % (uri, dest, dest))
if mode == "rpc_err":
    fail("E0000 couldn't copy `%s': DEADLINE_EXCEEDED: RPC timed out\n" % uri)
if mode == "perm_denied":
    fail("E0000 couldn't copy `%s': PERMISSION_DENIED: %s: No such file or directory "
         "[storage_x20.pb.Error] { code: NO_SUCH_FILE_OR_DIRECTORY }\n" % (uri, uri))
if mode == "empty":
    open(dest, "wb").close()
    sys.exit(0)
if mode == "corrupt":
    with open(dest, "w", encoding="utf-8") as f:
        f.write("this is not a git bundle\n")
    sys.exit(0)
if mode == "no_dest":
    sys.exit(0)
if mode == "slow":
    time.sleep(30)
    sys.exit(0)
fail("unknown mode %r\n" % mode)
'''


@contextlib.contextmanager
def _stdin_as_pipe() -> Iterator[None]:
    """Temporarily points fd 0 at an (EOF) pipe so that an inherited stdin is
    distinguishable from `stdin=subprocess.DEVNULL` inside child processes.

    Also works when fd 0 starts out closed (as under `rshelld` / `cpl exec`).
    """
    try:
        saved: int | None = os.dup(0)
    except OSError:
        saved = None
    r_fd, w_fd = os.pipe()
    os.close(w_fd)
    try:
        if r_fd != 0:
            os.dup2(r_fd, 0)
            os.close(r_fd)
        yield
    finally:
        if saved is not None:
            os.dup2(saved, 0)
            os.close(saved)
        else:
            os.close(0)


class TestX20Staging(unittest.TestCase):
    """Tests `fileutil` staging, not-found classification, and FUSE bypass."""

    FUSE_PATH = "/google/data/rw/teams/anneal-agent/testuser/anneal.bundle"
    X20_URI = "/x20/teams/anneal-agent/testuser/anneal.bundle"

    def test_x20_path_translation(self) -> None:
        for path in (
            "/google/data/rw/teams/anneal-agent/markdittmer/anneal.bundle",
            "/google/data/ro/teams/anneal-agent/markdittmer/anneal.bundle",
            "/x20/teams/anneal-agent/markdittmer/anneal.bundle",
            "/google/data/rw//teams//anneal-agent/markdittmer//anneal.bundle",
            "/x20//teams//anneal-agent/markdittmer/anneal.bundle",
        ):
            self.assertTrue(alr.is_x20_path(path), path)
            self.assertEqual(
                alr.to_x20_uri(path),
                "/x20/teams/anneal-agent/markdittmer/anneal.bundle",
            )
        for path in ("/tmp/x.bundle", "x20/teams/a.bundle", "/google/data/rwx/a"):
            self.assertFalse(alr.is_x20_path(path), path)
            self.assertEqual(alr.to_x20_uri(path), path)

    def test_remote_not_found_classifier_on_real_fileutil_messages(self) -> None:
        self.assertTrue(alr._is_x20_remote_not_found(REAL_CP_REMOTE_NOT_FOUND, _URI))
        self.assertTrue(alr._is_x20_remote_not_found(REAL_STAT_REMOTE_NOT_FOUND, _URI))
        # Local staging-destination ENOENT is NOT a missing remote bundle.
        self.assertFalse(alr._is_x20_remote_not_found(REAL_CP_LOCAL_ENOENT, _URI))
        # NOT_FOUND for some other x20 path is not about our bundle.
        self.assertFalse(
            alr._is_x20_remote_not_found(
                REAL_CP_REMOTE_NOT_FOUND, "/x20/teams/anneal-agent/v/anneal.bundle"
            )
        )
        for veto in ("PERMISSION_DENIED", "DEADLINE_EXCEEDED", "UNAVAILABLE"):
            self.assertFalse(
                alr._is_x20_remote_not_found(f"{veto}: {REAL_CP_REMOTE_NOT_FOUND}", _URI)
            )
        self.assertFalse(alr._is_x20_remote_not_found("No such file or directory", _URI))
        self.assertFalse(alr._is_x20_remote_not_found("", _URI))

        # Veto markers that only occur inside the echoed path do not count...
        odd_uri = "/x20/teams/unavailable-internal error/anneal.bundle"
        odd_msg = REAL_CP_REMOTE_NOT_FOUND.replace(_URI, odd_uri).replace(
            "/teams/anneal-agent/u/anneal.bundle", odd_uri[len("/x20") :]
        )
        self.assertTrue(alr._is_x20_remote_not_found(odd_msg, odd_uri))
        # ...but a real veto outside the path still fails closed.
        self.assertFalse(
            alr._is_x20_remote_not_found(f"DEADLINE_EXCEEDED: rpc\n{odd_msg}", odd_uri)
        )

    def _setup(self, tmp_p: Path) -> tuple[Path, Path, Path, str]:
        repo = tmp_p / "repo"
        _init_repo(repo)
        c1 = _commit_file(repo, "a.txt", "1\n", "c1")
        _git(repo, "branch", "unstable", c1)
        real_bundle = _make_bundle(repo, tmp_p / "real.bundle", "refs/heads/unstable")
        mock_fileutil = tmp_p / "mock_fileutil.py"
        mock_fileutil.write_text(MOCK_FILEUTIL_SRC, encoding="utf-8")
        mock_fileutil.chmod(0o755)
        return repo, real_bundle, mock_fileutil, c1

    def _run_case(
        self,
        tmp_p: Path,
        repo: Path,
        real_bundle: Path,
        mock_fileutil: Path,
        mode: str,
        bundle_path: str,
        sync_if_behind: bool = False,
    ) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]:
        log_file = tmp_p / f"log-{mode}.jsonl"
        log_file.unlink(missing_ok=True)
        scratch = tmp_p / f"scratch-{mode}"
        scratch.mkdir(exist_ok=True)
        real_run = subprocess.run
        fileutil_kwargs: list[dict[str, Any]] = []

        def spy_run(*args: Any, **kwargs: Any) -> Any:
            cmd = args[0] if args else kwargs.get("args")
            if cmd and str(cmd[0]) == str(mock_fileutil):
                fileutil_kwargs.append(kwargs)
            return real_run(*args, **kwargs)

        env = {
            "MOCK_FILEUTIL_MODE": mode,
            "MOCK_FILEUTIL_LOG": str(log_file),
            "MOCK_FILEUTIL_SRC_BUNDLE": str(real_bundle),
        }
        with mock.patch.dict(os.environ, env), mock.patch.object(
            alr.tempfile, "tempdir", str(scratch)
        ), mock.patch.object(
            alr.subprocess, "run", side_effect=spy_run
        ), mock.patch.object(
            alr, "FILEUTIL_CP_TIMEOUT_SEC", 1.0
        ), _stdin_as_pipe():
            verdict = alr.verify_bundle_ff(
                bundle_path,
                repo_dir=repo,
                fileutil_bin=str(mock_fileutil),
                sync_if_behind=sync_if_behind,
            )
        calls = [
            json.loads(line)
            for line in log_file.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ] if log_file.exists() else []
        # Staged temp dirs are always removed, on every success/failure path.
        self.assertEqual(list(scratch.iterdir()), [], mode)
        return verdict, calls, fileutil_kwargs

    def test_fileutil_staging_matrix(self) -> None:
        cases = [
            # (mode, expected status, expected ok, expected fileutil ops)
            ("ok", "up_to_date", True, ["cp"]),
            ("not_found", "no_remote_bundle", True, ["cp", "stat"]),
            ("local_enoent", "bundle_error", False, ["cp"]),
            ("cp_not_found_stat_exists", "bundle_error", False, ["cp", "stat"]),
            ("cp_not_found_stat_rpc", "bundle_error", False, ["cp", "stat"]),
            ("rpc_err", "bundle_error", False, ["cp"]),
            ("perm_denied", "bundle_error", False, ["cp"]),
            ("empty", "bundle_error", False, ["cp"]),
            ("corrupt", "bundle_error", False, ["cp"]),
            ("no_dest", "bundle_error", False, ["cp"]),
            ("slow", "bundle_error", False, ["cp"]),
        ]
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo, real_bundle, mock_fileutil, c1 = self._setup(tmp_p)
            for mode, status, ok, ops in cases:
                with self.subTest(mode=mode):
                    verdict, calls, kwargs_list = self._run_case(
                        tmp_p, repo, real_bundle, mock_fileutil, mode, self.FUSE_PATH
                    )
                    self.assertEqual(verdict["status"], status, verdict["message"])
                    self.assertEqual(verdict["ok"], ok)
                    self.assertEqual([c["argv"][1] for c in calls], ops)
                    for call in calls:
                        self.assertEqual(
                            call["argv"][0], "--x20_force_client_creation_at_head"
                        )
                        self.assertTrue(call["stdin_is_devnull"], call)
                        # The FUSE path is never handed to fileutil.
                        self.assertNotIn(self.FUSE_PATH, call["argv"])
                    cp_argv = calls[0]["argv"]
                    self.assertEqual(cp_argv[1:4], ["cp", "-f", self.X20_URI])
                    if "stat" in ops:
                        self.assertEqual(calls[1]["argv"][1:], ["stat", self.X20_URI])
                    self.assertEqual(len(kwargs_list), len(ops))
                    for kwargs in kwargs_list:
                        self.assertIs(kwargs.get("stdin"), subprocess.DEVNULL)
                    if mode == "ok":
                        self.assertEqual(verdict["remote_tip"], c1)
                    if mode == "local_enoent":
                        self.assertIn("open failed", verdict["message"])

    def test_ro_and_x20_uris_and_fuse_symlinks_are_staged_via_fileutil(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo, real_bundle, mock_fileutil, _ = self._setup(tmp_p)
            ro_path = "/google/data/ro/teams/anneal-agent/testuser/anneal.bundle"
            verdict, calls, _ = self._run_case(
                tmp_p, repo, real_bundle, mock_fileutil, "ok", ro_path
            )
            self.assertEqual(verdict["status"], "up_to_date")
            self.assertEqual(calls[0]["argv"][3], self.X20_URI)

            # A local symlink (or multi-hop symlink chain) whose target is an x20
            # URI or FUSE path must be staged through fileutil without relying on
            # `os.path.realpath` mocks.
            link1 = tmp_p / "x20link1.bundle"
            link1.symlink_to(self.FUSE_PATH)
            link2 = tmp_p / "x20link2.bundle"
            link2.symlink_to("x20link1.bundle")
            verdict_link, calls_link, _ = self._run_case(
                tmp_p, repo, real_bundle, mock_fileutil, "not_found", str(link2)
            )
            self.assertEqual(verdict_link["status"], "no_remote_bundle")
            self.assertEqual(calls_link[0]["argv"][1:4], ["cp", "-f", self.X20_URI])

            # Redundant slashes in a FUSE path normalize to the canonical `/x20/` URI.
            slashed_fuse = "/google/data/rw//teams//anneal-agent/testuser//anneal.bundle"
            verdict_slashed, calls_slashed, _ = self._run_case(
                tmp_p, repo, real_bundle, mock_fileutil, "not_found", slashed_fuse
            )
            self.assertEqual(verdict_slashed["status"], "no_remote_bundle")
            self.assertEqual(calls_slashed[0]["argv"][1:4], ["cp", "-f", self.X20_URI])

    def test_x20_staged_bundle_supports_sync_end_to_end(self) -> None:
        """`--sync-if-behind` fetches the unfetched tip from the fileutil-staged
        temp copy (still alive inside the `with` body), then cleans it up."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo, _, mock_fileutil, c1 = self._setup(tmp_p)
            other = tmp_p / "other"
            subprocess.run(
                ["git", "clone", "-q", str(repo), str(other)],
                env=alr._git_env(),
                check=True,
                capture_output=True,
            )
            _git(other, "checkout", "-q", "-b", "unstable", "origin/unstable")
            c2 = _commit_file(other, "a.txt", "2\n", "c2")
            ahead = _make_bundle(other, tmp_p / "ahead.bundle", "refs/heads/unstable")
            self.assertFalse(_has_object(repo, c2))

            verdict, calls, _ = self._run_case(
                tmp_p, repo, ahead, mock_fileutil, "ok", self.FUSE_PATH, sync_if_behind=True
            )
            self.assertTrue(verdict["ok"], verdict["message"])
            self.assertTrue(verdict["synced"])
            self.assertEqual(verdict["status"], "synced_fast_forward")
            self.assertEqual(verdict["remote_tip"], c2)
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c2)
            self.assertEqual([c["argv"][1] for c in calls], ["cp"])
            self.assertNotEqual(c1, c2)

    def test_unrunnable_fileutil_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo, _, _, _ = self._setup(tmp_p)
            verdict = alr.verify_bundle_ff(
                self.FUSE_PATH,
                repo_dir=repo,
                fileutil_bin=str(tmp_p / "no-such-fileutil"),
            )
            self.assertFalse(verdict["ok"])
            self.assertEqual(verdict["status"], "bundle_error")


# ---------------------------------------------------------------------------
# Real CLI subprocess integration
# ---------------------------------------------------------------------------


class TestCliSubprocess(unittest.TestCase):
    """Runs `scripts/anneal-lean-run` as a real subprocess (stdin=/dev/null)."""

    def _cli(
        self, *args: str, env_extra: dict[str, str] | None = None
    ) -> subprocess.CompletedProcess[str]:
        env = dict(os.environ)
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        if env_extra:
            env.update(env_extra)
        return subprocess.run(
            [sys.executable, str(SCRIPT_PATH), *args],
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            check=False,
            env=env,
            timeout=120,
        )

    def test_cli_verify_exit_codes_streams_and_sync(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            _init_repo(repo)
            c1 = _commit_file(repo, "a.txt", "1\n", "c1")
            c2 = _commit_file(repo, "a.txt", "2\n", "c2")
            _git(repo, "branch", "unstable", c2)
            bundle = str(
                _make_bundle(repo, tmp_p / "b.bundle", "refs/heads/unstable")
            )

            ok_json = self._cli(
                "--check-unstable-ff", bundle, "--repo-dir", str(repo), "--json"
            )
            self.assertEqual(ok_json.returncode, 0, ok_json.stderr)
            self.assertEqual(json.loads(ok_json.stdout)["status"], "up_to_date")
            self.assertEqual(ok_json.stderr, "")

            ok_text = self._cli(
                "--verify-bundle-ff", bundle, "--ref", "unstable", "--repo-dir", str(repo)
            )
            self.assertEqual(ok_text.returncode, 0)
            self.assertTrue(ok_text.stdout.startswith("[anneal-lean-run] OK (up_to_date)"))

            _git(repo, "branch", "-f", "unstable", c1)
            stale_json = self._cli(
                "--json", "--verify-bundle-ff", bundle, "--repo-dir", str(repo)
            )
            self.assertEqual(stale_json.returncode, 1)
            self.assertEqual(json.loads(stale_json.stdout)["status"], "stale_behind")
            self.assertIn("ERROR", stale_json.stderr)

            stale_text = self._cli("--verify-bundle-ff", bundle, "--repo-dir", str(repo))
            self.assertEqual(stale_text.returncode, 1)
            self.assertEqual(stale_text.stdout, "")
            self.assertIn("stale", stale_text.stderr)
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c1)

            synced = self._cli(
                "--verify-bundle-ff",
                bundle,
                "--repo-dir",
                str(repo),
                "--sync-if-behind",
                "--json",
            )
            self.assertEqual(synced.returncode, 0, synced.stderr)
            self.assertEqual(json.loads(synced.stdout)["status"], "synced_fast_forward")
            self.assertEqual(_rev(repo, "refs/heads/unstable"), c2)

            missing = self._cli(
                "--verify-bundle-ff", str(tmp_p / "absent.bundle"), "--repo-dir", str(repo)
            )
            self.assertEqual(missing.returncode, 0)
            self.assertIn("no_remote_bundle", missing.stdout)

    def test_cli_flag_conflicts_and_remainder_interaction(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            _init_repo(repo)
            c1 = _commit_file(repo, "a.txt", "1\n", "c1")
            _git(repo, "branch", "unstable", c1)
            bundle = str(
                _make_bundle(repo, tmp_p / "b.bundle", "refs/heads/unstable")
            )

            for argv in (
                ["--verify-bundle-ff", bundle, "--", "true"],
                ["--verify-bundle-ff", bundle, "lake", "build"],
                ["--probe", "--verify-bundle-ff", bundle],
                ["--verify-bundle-ff", bundle, "--print-limits"],
            ):
                res = self._cli(*argv)
                self.assertEqual(res.returncode, 2, (argv, res.stderr))
                self.assertIn("cannot be combined", res.stderr)

            no_value = self._cli("--verify-bundle-ff")
            self.assertEqual(no_value.returncode, 2)
            self.assertIn("expected one argument", no_value.stderr)

            # A bare trailing `--` carries no command and is accepted.
            trailing = self._cli(
                "--verify-bundle-ff", bundle, "--repo-dir", str(repo), "--json", "--"
            )
            self.assertEqual(trailing.returncode, 0, trailing.stderr)
            self.assertEqual(json.loads(trailing.stdout)["status"], "up_to_date")

    def test_cli_backward_compatible_probe_and_execution(self) -> None:
        if os.access(SCRIPT_PATH, os.X_OK):
            direct = subprocess.run(
                [str(SCRIPT_PATH), "--print-limits", "--json"],
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                check=False,
                timeout=120,
            )
            self.assertEqual(direct.returncode, 0, direct.stderr)
            self.assertIn("cgroup_avail_mib", json.loads(direct.stdout))

        probe = self._cli("--probe")
        self.assertEqual(probe.returncode, 0)
        self.assertIn("Cgroup v2 Memory", probe.stdout)
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
        data = json.loads(env_json.stdout)
        self.assertEqual(data["concurrency"], 2)
        self.assertEqual(data["memory_max_mb"], 3000)
        self.assertEqual(data["timeout_sec"], 77)

        bad_env = self._cli(
            "--probe", "--json", env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "abc"}
        )
        self.assertEqual(bad_env.returncode, 0, bad_env.stderr)
        self.assertEqual(json.loads(bad_env.stdout)["concurrency"], 1)

        flags = self._cli(
            "--concurrency", "1", "--memory-max-mb", "2500", "--timeout", "60",
            "--probe", "--json",
        )
        flag_data = json.loads(flags.stdout)
        self.assertEqual(flag_data["memory_max_mb"], 2500)
        self.assertEqual(flag_data["timeout_sec"], 60)

        for argv, expected_rc in (
            (["--mode", "file", "--concurrency", "1", "--", "true"], 0),
            (["--mode", "build", "--no-slot-lock", "--concurrency", "1", "--", "true"], 0),
            (["--no-slot-lock", "--", "sh", "-c", "exit 5"], 5),
        ):
            res = self._cli(*argv)
            self.assertEqual(res.returncode, expected_rc, (argv, res.stderr))

        usage = self._cli()
        self.assertEqual(usage.returncode, 2)


if __name__ == "__main__":
    unittest.main()
