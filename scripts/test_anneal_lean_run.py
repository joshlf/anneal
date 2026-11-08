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

import importlib.machinery
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
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

            # Root unified hierarchy inside container namespace
            p.write_text("0::/\n", encoding="utf-8")
            self.assertEqual(alr.parse_proc_cgroup_v2(p), "/")

            # Cgroup v1 only (no 0:: line)
            p.write_text(
                "11:memory:/user.slice\n10:cpu:/user.slice\n",
                encoding="utf-8",
            )
            self.assertIsNone(alr.parse_proc_cgroup_v2(p))

            # Non-existent file
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

        with tempfile.TemporaryDirectory() as tmp:
            stat_file = Path(tmp) / "memory.stat"
            stat_file.write_text(raw, encoding="utf-8")
            self.assertEqual(alr.parse_memory_stat(stat_file), stats)
            self.assertEqual(alr.parse_memory_stat(str(stat_file)), stats)

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
            self.assertFalse(cg_none["cgroup_v2"])
            self.assertIsNone(cg_none["cgroup_path"])
            self.assertIsNone(cg_none["cgroup_anon_shmem_mib"])
            self.assertIsNone(cg_none["cgroup_memory_max_mib"])
            self.assertIsNone(cg_none["cgroup_avail_mib"])


class TestCliAndLimits(unittest.TestCase):
    """Tests mode detection, `-M` flag injection, `--probe` / `--print-limits`, and execution."""

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
        for flag in ("--probe", "--print-limits"):
            buf = io.StringIO()
            with mock.patch("sys.stdout", buf):
                rc = alr.main([flag, "--json"])
            self.assertEqual(rc, 0)
            data = json.loads(buf.getvalue())
            required_keys = {
                "mode",
                "concurrency",
                "cpu_cores",
                "mem_total_mb",
                "mem_avail_mb",
                "threads",
                "memory_max_mb",
                "lean_m_mb",
                "timeout_sec",
                "build_slots",
                "systemd_user_scope",
                "cgroup_v2",
                "cgroup_path",
                "cgroup_anon_mib",
                "cgroup_shmem_mib",
                "cgroup_anon_shmem_mib",
                "cgroup_file_cache_mib",
                "cgroup_current_mib",
                "cgroup_memory_max_mib",
                "cgroup_avail_mib",
            }
            self.assertTrue(required_keys.issubset(data.keys()))

            text_buf = io.StringIO()
            with mock.patch("sys.stdout", text_buf):
                rc_txt = alr.main([flag])
            self.assertEqual(rc_txt, 0)
            self.assertIn("Cgroup v2 Memory", text_buf.getvalue())

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

        err_buf = io.StringIO()
        with mock.patch("sys.stderr", err_buf):
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
        self.assertIn("Command timed out after 1s", err_buf.getvalue())


class TestVerifyBundleFF(unittest.TestCase):
    """Tests `--verify-bundle-ff` / `--check-unstable-ff` across all ancestry and x20 cases."""

    def _init_repo(self, path: Path) -> None:
        path.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "init", "-b", "main"],
            cwd=str(path),
            check=True,
            capture_output=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test User"],
            cwd=str(path),
            check=True,
            capture_output=True,
        )
        subprocess.run(
            ["git", "config", "user.email", "test@example.com"],
            cwd=str(path),
            check=True,
            capture_output=True,
        )

    def _commit_file(
        self, repo: Path, filename: str, content: str, msg: str
    ) -> str:
        (repo / filename).write_text(content, encoding="utf-8")
        subprocess.run(
            ["git", "add", filename],
            cwd=str(repo),
            check=True,
            capture_output=True,
        )
        subprocess.run(
            ["git", "commit", "-m", msg],
            cwd=str(repo),
            check=True,
            capture_output=True,
        )
        res = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=str(repo),
            check=True,
            capture_output=True,
            text=True,
        )
        return res.stdout.strip().lower()

    def test_no_remote_bundle_and_corrupt_bundle_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            self._init_repo(repo)
            c1 = self._commit_file(repo, "a.txt", "1\n", "c1")
            subprocess.run(
                ["git", "branch", "unstable", c1],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )

            # 1. Non-existent local bundle -> ok=True, status="no_remote_bundle"
            missing_bundle = tmp_p / "does_not_exist.bundle"
            v_missing = alr.verify_bundle_ff(
                missing_bundle, repo_dir=repo
            )
            self.assertTrue(v_missing["ok"])
            self.assertEqual(v_missing["status"], "no_remote_bundle")
            self.assertEqual(v_missing["local_tip"], c1)

            # 2. Empty (0-byte) bundle -> fail closed (ok=False, status="bundle_error")
            empty_bundle = tmp_p / "empty.bundle"
            empty_bundle.write_bytes(b"")
            v_empty = alr.verify_bundle_ff(empty_bundle, repo_dir=repo)
            self.assertFalse(v_empty["ok"])
            self.assertEqual(v_empty["status"], "bundle_error")

            # 3. Corrupt non-bundle file -> fail closed (ok=False, status="bundle_error")
            corrupt_bundle = tmp_p / "corrupt.bundle"
            corrupt_bundle.write_text("not a git bundle\n", encoding="utf-8")
            v_corrupt = alr.verify_bundle_ff(corrupt_bundle, repo_dir=repo)
            self.assertFalse(v_corrupt["ok"])
            self.assertEqual(v_corrupt["status"], "bundle_error")

            # 4. Directory passed as bundle path -> fail closed
            v_dir = alr.verify_bundle_ff(repo, repo_dir=repo)
            self.assertFalse(v_dir["ok"])
            self.assertEqual(v_dir["status"], "bundle_error")

            # 5. Broken symlink -> fail closed
            broken_link = tmp_p / "broken.bundle"
            broken_link.symlink_to(tmp_p / "nonexistent_target.bundle")
            v_link = alr.verify_bundle_ff(broken_link, repo_dir=repo)
            self.assertFalse(v_link["ok"])
            self.assertEqual(v_link["status"], "bundle_error")

    def test_up_to_date_fast_forward_stale_behind_and_diverged(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            self._init_repo(repo)
            c1 = self._commit_file(repo, "a.txt", "1\n", "c1")
            c2 = self._commit_file(repo, "a.txt", "2\n", "c2")
            c3 = self._commit_file(repo, "a.txt", "3\n", "c3")

            # Create bundle with only main (no unstable ref)
            main_only_bundle = tmp_p / "main_only.bundle"
            subprocess.run(
                [
                    "git",
                    "bundle",
                    "create",
                    str(main_only_bundle),
                    "refs/heads/main",
                ],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )
            v_no_ref = alr.verify_bundle_ff(main_only_bundle, repo_dir=repo)
            self.assertTrue(v_no_ref["ok"])
            self.assertEqual(v_no_ref["status"], "no_remote_ref")

            # Create bundle with refs/heads/unstable at c2
            subprocess.run(
                ["git", "branch", "-f", "unstable", c2],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )
            bundle_c2 = tmp_p / "c2.bundle"
            subprocess.run(
                [
                    "git",
                    "bundle",
                    "create",
                    str(bundle_c2),
                    "refs/heads/unstable",
                ],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )

            # Case: up_to_date (local unstable == c2)
            v_eq = alr.verify_bundle_ff(bundle_c2, repo_dir=repo)
            self.assertTrue(v_eq["ok"])
            self.assertEqual(v_eq["status"], "up_to_date")
            self.assertEqual(v_eq["remote_tip"], c2)
            self.assertEqual(v_eq["local_tip"], c2)

            # Case: fast_forward (local unstable == c3, remote == c2)
            subprocess.run(
                ["git", "branch", "-f", "unstable", c3],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )
            v_ff = alr.verify_bundle_ff(
                bundle_c2, ref="unstable", repo_dir=repo
            )
            self.assertTrue(v_ff["ok"])
            self.assertEqual(v_ff["status"], "fast_forward")
            self.assertEqual(v_ff["ref"], "refs/heads/unstable")

            # Case: stale_behind (local unstable == c1, remote == c2)
            subprocess.run(
                ["git", "branch", "-f", "unstable", c1],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )
            v_behind = alr.verify_bundle_ff(bundle_c2, repo_dir=repo)
            self.assertFalse(v_behind["ok"])
            self.assertEqual(v_behind["status"], "stale_behind")
            self.assertIn("1 commit(s) behind", v_behind["message"])

            # Verify CLI exit codes for fast_forward (0) and stale_behind (1)
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

            # Case: synced_fast_forward with --sync-if-behind (non-checked-out branch)
            v_synced = alr.verify_bundle_ff(
                bundle_c2, repo_dir=repo, sync_if_behind=True
            )
            self.assertTrue(v_synced["ok"])
            self.assertTrue(v_synced["synced"])
            self.assertEqual(v_synced["status"], "synced_fast_forward")
            self.assertEqual(v_synced["local_tip"], c2)

            # Case: diverged branch
            subprocess.run(
                ["git", "checkout", "-b", "div_branch", c1],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )
            c_div = self._commit_file(repo, "div.txt", "diverged\n", "c_div")
            subprocess.run(
                ["git", "checkout", "main"],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )
            subprocess.run(
                ["git", "branch", "-f", "unstable", c_div],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )
            v_div = alr.verify_bundle_ff(
                bundle_c2, repo_dir=repo, sync_if_behind=True
            )
            self.assertFalse(v_div["ok"])
            self.assertFalse(v_div["synced"])
            self.assertEqual(v_div["status"], "diverged")

    def test_unfetched_remote_tip_and_missing_local_ref_sync(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            remote_repo = tmp_p / "remote_repo"
            local_repo = tmp_p / "local_repo"
            self._init_repo(remote_repo)
            c1 = self._commit_file(remote_repo, "f.txt", "v1\n", "c1")
            subprocess.run(
                ["git", "branch", "unstable", c1],
                cwd=str(remote_repo),
                check=True,
                capture_output=True,
            )

            # Clone remote_repo into local_repo at c1
            subprocess.run(
                ["git", "clone", str(remote_repo), str(local_repo)],
                check=True,
                capture_output=True,
            )
            subprocess.run(
                ["git", "branch", "unstable", c1],
                cwd=str(local_repo),
                check=True,
                capture_output=True,
            )

            # Advance remote_repo unstable to c2 (unfetched in local_repo)
            subprocess.run(
                ["git", "checkout", "unstable"],
                cwd=str(remote_repo),
                check=True,
                capture_output=True,
            )
            c2 = self._commit_file(remote_repo, "f.txt", "v2\n", "c2")
            bundle_c2 = tmp_p / "remote_c2.bundle"
            subprocess.run(
                [
                    "git",
                    "bundle",
                    "create",
                    str(bundle_c2),
                    "refs/heads/unstable",
                ],
                cwd=str(remote_repo),
                check=True,
                capture_output=True,
            )

            # Without --sync-if-behind: unfetched_remote_tip
            v_unfetched = alr.verify_bundle_ff(
                bundle_c2, repo_dir=local_repo, sync_if_behind=False
            )
            self.assertFalse(v_unfetched["ok"])
            self.assertEqual(v_unfetched["status"], "unfetched_remote_tip")

            # With --sync-if-behind: fetches c2 from bundle and fast-forwards local unstable
            v_sync_unfetched = alr.verify_bundle_ff(
                bundle_c2, repo_dir=local_repo, sync_if_behind=True
            )
            self.assertTrue(v_sync_unfetched["ok"])
            self.assertTrue(v_sync_unfetched["synced"])
            self.assertEqual(
                v_sync_unfetched["status"], "synced_fast_forward"
            )
            self.assertEqual(v_sync_unfetched["local_tip"], c2)

            # Delete local unstable to test missing_local_ref
            subprocess.run(
                ["git", "branch", "-D", "unstable"],
                cwd=str(local_repo),
                check=True,
                capture_output=True,
            )
            v_missing_ref = alr.verify_bundle_ff(
                bundle_c2, repo_dir=local_repo, sync_if_behind=False
            )
            self.assertFalse(v_missing_ref["ok"])
            self.assertEqual(v_missing_ref["status"], "missing_local_ref")

            # With --sync-if-behind and explicit --local-rev override -> refuses to sync
            v_override = alr.verify_bundle_ff(
                bundle_c2,
                repo_dir=local_repo,
                local_rev="refs/heads/nonexistent",
                sync_if_behind=True,
            )
            self.assertFalse(v_override["ok"])
            self.assertEqual(v_override["status"], "missing_local_ref")

            # With --sync-if-behind and default --local-rev -> recreates local unstable at c2
            v_sync_missing = alr.verify_bundle_ff(
                bundle_c2, repo_dir=local_repo, sync_if_behind=True
            )
            self.assertTrue(v_sync_missing["ok"])
            self.assertTrue(v_sync_missing["synced"])
            self.assertEqual(
                v_sync_missing["status"], "synced_missing_local_ref"
            )
            self.assertEqual(v_sync_missing["local_tip"], c2)

    def test_worktree_safety_dirty_and_linked_worktrees(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            self._init_repo(repo)
            c1 = self._commit_file(repo, "a.txt", "1\n", "c1")
            c2 = self._commit_file(repo, "a.txt", "2\n", "c2")
            subprocess.run(
                ["git", "branch", "unstable", c2],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )
            bundle_c2 = tmp_p / "c2.bundle"
            subprocess.run(
                [
                    "git",
                    "bundle",
                    "create",
                    str(bundle_c2),
                    "refs/heads/unstable",
                ],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )

            # Reset unstable to c1 and check it out in `repo`
            subprocess.run(
                ["git", "checkout", "-B", "unstable", c1],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )

            # 1. Dirty checked-out worktree -> --sync-if-behind must refuse!
            (repo / "dirty.txt").write_text("uncommitted\n", encoding="utf-8")
            v_dirty = alr.verify_bundle_ff(
                bundle_c2, repo_dir=repo, sync_if_behind=True
            )
            self.assertFalse(v_dirty["ok"])
            self.assertFalse(v_dirty["synced"])
            self.assertEqual(v_dirty["status"], "stale_behind")
            self.assertIn("dirty worktree", v_dirty["message"])

            # 2. Clean checked-out worktree -> --sync-if-behind fast-forwards via merge --ff-only
            (repo / "dirty.txt").unlink()
            v_clean_co = alr.verify_bundle_ff(
                bundle_c2, repo_dir=repo, sync_if_behind=True
            )
            self.assertTrue(v_clean_co["ok"])
            self.assertTrue(v_clean_co["synced"])
            self.assertEqual(v_clean_co["status"], "synced_fast_forward")
            self.assertEqual((repo / "a.txt").read_text(encoding="utf-8"), "2\n")

            # 3. Reset unstable to c1 in `repo`, and create a linked worktree `wt2` on branch `feature`
            subprocess.run(
                ["git", "reset", "--hard", c1],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )
            wt2 = tmp_p / "wt2"
            subprocess.run(
                ["git", "worktree", "add", "-b", "feature", str(wt2), c1],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )
            # Running --sync-if-behind from `wt2` while `unstable` is checked out in `repo` must refuse!
            v_linked = alr.verify_bundle_ff(
                bundle_c2, repo_dir=wt2, sync_if_behind=True
            )
            self.assertFalse(v_linked["ok"])
            self.assertFalse(v_linked["synced"])
            self.assertEqual(v_linked["status"], "stale_behind")
            self.assertIn("linked worktree", v_linked["message"])

    def test_x20_fileutil_staging_and_fuse_bypass(self) -> None:
        self.assertTrue(
            alr.is_x20_path(
                "/google/data/rw/teams/anneal-agent/markdittmer/anneal.bundle"
            )
        )
        self.assertTrue(
            alr.is_x20_path(
                "/google/data/ro/teams/anneal-agent/markdittmer/anneal.bundle"
            )
        )
        self.assertTrue(
            alr.is_x20_path(
                "/x20/teams/anneal-agent/markdittmer/anneal.bundle"
            )
        )
        self.assertEqual(
            alr.to_x20_uri(
                "/google/data/rw/teams/anneal-agent/markdittmer/anneal.bundle"
            ),
            "/x20/teams/anneal-agent/markdittmer/anneal.bundle",
        )

        with tempfile.TemporaryDirectory() as tmp:
            tmp_p = Path(tmp)
            repo = tmp_p / "repo"
            self._init_repo(repo)
            c1 = self._commit_file(repo, "a.txt", "1\n", "c1")
            subprocess.run(
                ["git", "branch", "unstable", c1],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )
            real_bundle = tmp_p / "real.bundle"
            subprocess.run(
                [
                    "git",
                    "bundle",
                    "create",
                    str(real_bundle),
                    "refs/heads/unstable",
                ],
                cwd=str(repo),
                check=True,
                capture_output=True,
            )

            # Create a mock fileutil executable script that checks args and stdin EOF
            mock_fileutil = tmp_p / "mock_fileutil.py"
            log_file = tmp_p / "fileutil_calls.json"
            mock_fileutil.write_text(
                "#!/usr/bin/env python3\n"
                "import json, os, shutil, sys\n"
                "stdin_data = sys.stdin.read()\n"
                f"log_p = {str(log_file)!r}\n"
                "with open(log_p, 'w', encoding='utf-8') as f:\n"
                "    json.dump({'argv': sys.argv[1:], 'stdin': stdin_data}, f)\n"
                "mode = os.environ.get('MOCK_FILEUTIL_MODE', 'ok')\n"
                "if mode == 'not_found':\n"
                "    sys.stderr.write('generic::not_found: File not found [storage_x20.pb.Error] { code: NO_SUCH_FILE_OR_DIRECTORY }\\n')\n"
                "    sys.exit(1)\n"
                "if mode == 'rpc_err':\n"
                "    sys.stderr.write('DEADLINE_EXCEEDED: RPC timed out\\n')\n"
                "    sys.exit(1)\n"
                f"shutil.copyfile({str(real_bundle)!r}, sys.argv[-1])\n"
                "sys.exit(0)\n",
                encoding="utf-8",
            )
            mock_fileutil.chmod(0o755)

            fuse_path = (
                "/google/data/rw/teams/anneal-agent/testuser/anneal.bundle"
            )

            # 1. Successful x20 staging via /google/data/rw/... translated to /x20/...
            with mock.patch.dict(os.environ, {"MOCK_FILEUTIL_MODE": "ok"}):
                v_ok = alr.verify_bundle_ff(
                    fuse_path,
                    repo_dir=repo,
                    fileutil_bin=str(mock_fileutil),
                )
            self.assertTrue(v_ok["ok"])
            self.assertEqual(v_ok["status"], "up_to_date")
            recorded = json.loads(log_file.read_text(encoding="utf-8"))
            self.assertEqual(
                recorded["argv"][:4],
                [
                    "--x20_force_client_creation_at_head",
                    "cp",
                    "-f",
                    "/x20/teams/anneal-agent/testuser/anneal.bundle",
                ],
            )
            self.assertEqual(recorded["stdin"], "")
            # Temporary staged file must have been cleaned up in finally
            staged_arg = Path(recorded["argv"][4])
            self.assertFalse(staged_arg.exists())

            # 2. Missing remote bundle on x20 -> ok=True, status="no_remote_bundle"
            with mock.patch.dict(
                os.environ, {"MOCK_FILEUTIL_MODE": "not_found"}
            ):
                v_nf = alr.verify_bundle_ff(
                    fuse_path,
                    repo_dir=repo,
                    fileutil_bin=str(mock_fileutil),
                )
            self.assertTrue(v_nf["ok"])
            self.assertEqual(v_nf["status"], "no_remote_bundle")

            # 3. Transient fileutil RPC failure -> fail closed (ok=False, status="bundle_error")
            with mock.patch.dict(
                os.environ, {"MOCK_FILEUTIL_MODE": "rpc_err"}
            ):
                v_err = alr.verify_bundle_ff(
                    fuse_path,
                    repo_dir=repo,
                    fileutil_bin=str(mock_fileutil),
                )
            self.assertFalse(v_err["ok"])
            self.assertEqual(v_err["status"], "bundle_error")


if __name__ == "__main__":
    unittest.main()
