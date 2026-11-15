#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `scripts/run_nightly_verification_suite.py`."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_nightly_verification_suite as suite  # noqa: E402


REPO_ROOT = Path(__file__).resolve().parent.parent


class NightlyVerificationSuiteTests(unittest.TestCase):
    def test_stage_a_syntactic_completeness_on_repo(self) -> None:
        stage_a = suite.compute_stage_a_syntactic_completeness(REPO_ROOT)
        mir = stage_a["anneal_mir_ast"]
        self.assertEqual(mir["total_variants"], 95)
        self.assertGreaterEqual(mir["proved_corresponding"], 65)
        self.assertEqual(
            mir["total_variants"],
            mir["proved_corresponding"]
            + mir["supported_and_tested"]
            + mir["supported_untested"]
            + mir["unsupported_fail_closed"],
        )
        self.assertGreaterEqual(mir["stage1_lowered_lintrinsic_op_variants"], 30)

        mr = stage_a["minirust_authority"]
        self.assertEqual(mr["spec_files"], 27)
        self.assertEqual(mr["shallow_types_translated"], 100)
        self.assertEqual(mr["interp_anchored_items"], 104)
        self.assertGreater(mr["audited_declarations"], 500)

        lm = stage_a["lean_miri_authority"]
        self.assertEqual(lm["vendored_miri_files"], 608)
        self.assertIn("LM-1.1", lm["milestones_merged"])
        self.assertIn("LM-3.3", lm["milestones_merged"])
        self.assertGreater(lm["audited_declarations"], 500)

    def test_stage_b_blended_completeness_and_marginal_unlock_math(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            sample_rs = tmp_dir / "sample.rs"
            sample_rs.write_text(
                """
                pub fn pure_add(a: u32, b: u32) -> u32 {
                    let c = a.wrapping_add(b);
                    c
                }

                pub fn partially_blocked_float(x: u32) -> u32 {
                    let a = x + 1;
                    let b = a * 2;
                    let c = b - 1;
                    let _f: f64 = 1.0;
                    c
                }

                pub fn multi_blocked(x: u32) -> u32 {
                    let _f: f32 = 0.0;
                    unsafe { core::arch::asm!("nop") };
                    x
                }
                """,
                encoding="utf-8",
            )
            res = suite.analyze_corpus_completeness("synthetic", [sample_rs], alpha=0.5)
            self.assertEqual(res["total_fns"], 3)
            lifter = res["layers"]["anneal_proof_lifters"]
            self.assertEqual(lifter["fully_verifiable_fns"], 1)
            self.assertEqual(lifter["partially_covered_fns"], 2)
            self.assertEqual(lifter["uncovered_fns"], 0)
            self.assertGreater(lifter["within_blocked_fns_stmt_coverage_pct"], 50.0)
            self.assertAlmostEqual(lifter["within_blocked_fns_cfg_prefix_pct"], 37.5)
            self.assertGreater(
                lifter["blended_completeness_score_pct"],
                lifter["fully_verifiable_stmt_pct"],
            )

            # `float_arith_or_cast` is the sole blocker on `partially_blocked_float` (1 fn),
            # whereas `inline_asm` only appears alongside `float_arith_or_cast` (0 sole-blocker fns).
            blockers = {b["construct"]: b for b in res["top_marginal_unlock_blockers"]}
            self.assertEqual(blockers["float_arith_or_cast"]["sole_blocker_fn_count"], 1)
            self.assertEqual(blockers["float_arith_or_cast"]["blocked_fn_count"], 2)
            self.assertEqual(blockers["inline_asm"]["sole_blocker_fn_count"], 0)
            self.assertEqual(blockers["inline_asm"]["blocked_fn_count"], 1)

    def test_correspondence_divergence_switch_to_pass_detection(self) -> None:
        divs = suite.discover_correspondence_divergences(REPO_ROOT)
        self.assertGreaterEqual(divs["actionable_anneal_bugs_count"], 5)
        ids = {d["id"] for d in divs["actionable_anneal_bugs"]}
        self.assertIn("DIV-MR-CALL-TARGET-LOCAL", ids)
        self.assertIn("DIV-LM-RAW-OVERWRITE-CHAR-COPY", ids)
        self.assertEqual(divs["known_miri_diff_manifest_bugs"], [])

    def test_census_only_end_to_end_dashboard_and_ratchet(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp) / "state_out"
            code, dashboard, report_md = suite.run_suite_and_generate_dashboard(
                repo_root=REPO_ROOT,
                profile="census-only",
                state_dir=state_dir,
            )
            self.assertEqual(code, 0)
            self.assertEqual(
                dashboard["pillar_2_correctness_and_correspondence"]["overall_status"],
                "PASS",
            )
            self.assertIn("Pillar 1: 10,000-Foot Project Completeness", report_md)
            self.assertTrue((state_dir / "reports/LATEST_DASHBOARD_STATE.json").is_file())
            self.assertTrue((state_dir / "reports/LATEST_SUITE_REPORT.md").is_file())
            self.assertTrue((state_dir / "state/correspondence_ratchet.json").is_file())
            self.assertTrue((state_dir / "state/completeness_history.jsonl").is_file())

            loaded = json.loads(
                (state_dir / "reports/LATEST_DASHBOARD_STATE.json").read_text(encoding="utf-8")
            )
            self.assertEqual(loaded["schema_version"], 1)

    def test_build_suite_steps_ordering_core_theory_and_profile_isolation(self) -> None:
        census_steps = suite.build_suite_steps(REPO_ROOT, "census-only")
        census_names = [s[0] for s in census_steps]
        self.assertEqual(
            census_names,
            ["lean_miri_semantic_source_lint", "ci_check_non_stable_version"],
        )
        for _name, _cat, cmd, _timeout in census_steps:
            self.assertNotIn("lake", cmd)
            self.assertNotIn("cargo", cmd)

        quick_steps = suite.build_suite_steps(REPO_ROOT, "quick")
        quick_names = [s[0] for s in quick_steps]
        self.assertIn("lake_build_core_theory", quick_names)
        self.assertIn("check_trusted_fast", quick_names)
        self.assertLess(
            quick_names.index("lake_build_core_theory"),
            quick_names.index("check_trusted_fast"),
        )
        self.assertNotIn("check_trusted_self_test", quick_names)
        self.assertNotIn("lake_build_minirust_spec", quick_names)

        nightly_steps = suite.build_suite_steps(REPO_ROOT, "nightly")
        nightly_names = [s[0] for s in nightly_steps]
        core_idx = nightly_names.index("lake_build_core_theory")
        for dependent in (
            "check_trusted_fast",
            "check_trusted_self_test",
            "tests_mir_bit_validity_stage1",
            "tests_mir_byte_codec",
            "tests_mir_cast_stage1",
            "lake_build_correspondence",
            "lake_build_minirust_spec",
            "lake_build_lean_miri_spec",
        ):
            self.assertIn(dependent, nightly_names)
            self.assertLess(
                core_idx,
                nightly_names.index(dependent),
                f"lake_build_core_theory must precede {dependent}",
            )

        core_step = dict((s[0], s) for s in nightly_steps)["lake_build_core_theory"]
        self.assertEqual(core_step[1], "cat1_trusted_boundary")
        self.assertEqual(
            core_step[2][-5:],
            ["lake", "build", "Trusted", "Anneal", "MiniRust"],
        )

        # `lake env lean` never builds imports: every `tests_mir_*` file's workspace
        # imports must be built (`lake build +<Module>`) before it runs. `Anneal.ByteCodec`
        # and `Anneal.Mir.Cast` are outside the `Trusted`/`Anneal`/`MiniRust` closure, so
        # on a cold checkout `lake_build_core_theory` alone leaves them without `.olean`s.
        self.assertNotIn("lake_build_mir_test_modules", quick_names)
        self.assertNotIn("lake_build_mir_test_modules", census_names)
        by_name = dict((s[0], s) for s in nightly_steps)
        mods_step = by_name["lake_build_mir_test_modules"]
        sep = mods_step[2].index("--") if "--" in mods_step[2] else -1
        inner = mods_step[2][sep + 1 :]
        self.assertEqual(inner[:2], ["lake", "build"])
        built = {t[1:] for t in inner[2:] if t.startswith("+")}
        mods_idx = nightly_names.index("lake_build_mir_test_modules")
        self.assertLess(core_idx, mods_idx)
        import_re = re.compile(r"^import\s+(\S+)", re.MULTILINE)
        for step_name, rel in suite.MIR_STANDALONE_LEAN_TESTS:
            self.assertLess(mods_idx, nightly_names.index(step_name))
            self.assertEqual(by_name[step_name][2][-4:], ["lake", "env", "lean", rel])
            imports = import_re.findall((REPO_ROOT / rel).read_text(encoding="utf-8"))
            self.assertTrue(imports, rel)
            for mod in imports:
                if mod.split(".")[0] in suite.CORE_THEORY_LIBS + ("Correspondence", "MiniRustSpec"):
                    self.assertIn(mod, built, f"{rel} imports {mod}, which must be pre-built")
        self.assertTrue({"Anneal.ByteCodec", "Anneal.Mir.Cast"} <= built)
        self.assertEqual(sorted(built), sorted(suite._MIR_TEST_MODULE_FALLBACK))

    def test_timeout_propagation_and_calibrated_step_timeouts(self) -> None:
        nightly_by_name = {
            name: (cat, cmd, timeout_sec)
            for name, cat, cmd, timeout_sec in suite.build_suite_steps(REPO_ROOT, "nightly")
        }
        expected_timeouts = {
            "lake_build_core_theory": 900,
            "check_trusted_fast": 600,
            "rust_workspace_unit_tests": 600,
            "check_trusted_self_test": 600,
            "tests_mir_bit_validity_stage1": 300,
            "tests_mir_byte_codec": 300,
            "tests_mir_cast_stage1": 300,
            "lake_build_correspondence": 900,
            "lake_build_minirust_spec": 1200,
            "lake_build_lean_miri_spec": 1800,
            "domain_integration_tests_anneal_difftest": 900,
            "cargo_anneal_e2e_minirust_correspondence": 600,
            "cargo_anneal_e2e_pipeline_and_adoption": 900,
        }
        expected_timeouts["lake_build_mir_test_modules"] = 900
        for step_name, exp_timeout in expected_timeouts.items():
            self.assertIn(step_name, nightly_by_name)
            _cat, cmd, timeout_sec = nightly_by_name[step_name]
            self.assertEqual(timeout_sec, exp_timeout, f"Unexpected timeout for {step_name}")
            self.assertEqual(Path(cmd[0]).name, "anneal-lean-run", f"{step_name} must be wrapped")
            self.assertIn("--timeout", cmd)
            t_idx = cmd.index("--timeout")
            self.assertEqual(int(cmd[t_idx + 1]), timeout_sec)

        # Every wrapped step in every profile hands its exact step budget to the wrapper.
        for profile in ("census-only", "quick", "nightly"):
            for name, _cat, cmd, timeout_sec in suite.build_suite_steps(REPO_ROOT, profile):
                if not suite._is_lean_run_wrapped(cmd):
                    continue
                mode, inner_timeout, slot_lock = suite._lean_run_wrapper_flags(cmd)
                self.assertEqual(inner_timeout, timeout_sec, f"{profile}/{name}")
                self.assertTrue(slot_lock, f"{profile}/{name}")
                expected_mode = "file" if name.startswith("tests_mir_") else "build"
                self.assertEqual(mode, expected_mode, f"{profile}/{name}")

    def test_run_step_wrapper_timeout_grace_and_exit_124_classification(self) -> None:
        # When a wrapped command exits with 124 (inner anneal-lean-run timeout),
        # `_run_step` classifies status as TIMEOUT and preserves diagnostic stderr.
        res = suite._run_step(
            name="simulated_inner_timeout",
            category="cat2_correspondence_suites",
            cmd=[
                sys.executable,
                "-c",
                "import sys; sys.stderr.write('[anneal-lean-run] ERROR: Command timed out\\n'); sys.exit(124)",
            ],
            cwd=REPO_ROOT,
            timeout_sec=10,
        )
        self.assertEqual(res["status"], "TIMEOUT")
        self.assertEqual(res["exit_code"], 124)
        self.assertIn("[anneal-lean-run] ERROR: Command timed out", res["failure_excerpt"])

        # Verify `_ensure_toolchain_path` populates existing user toolchain dirs into minimal PATH.
        minimal_env = {"PATH": "/usr/bin:/bin"}
        suite._ensure_toolchain_path(minimal_env)
        for rel in (".elan/bin", ".cargo/bin", ".local/bin"):
            cand = Path.home() / rel
            if cand.is_dir():
                self.assertIn(str(cand), minimal_env["PATH"].split(":"))

    def test_outer_timeout_covers_wrapper_slot_wait_and_grace(self) -> None:
        lr = str(REPO_ROOT / "scripts/anneal-lean-run")
        grace = suite.WRAPPER_TIMEOUT_GRACE_SEC
        # Direct commands: the step budget is the only deadline.
        self.assertEqual(suite._outer_timeout_sec(["cargo", "test"], 600), 600)
        # `--mode build` may queue up to `max(30, T)` s for a build slot before its own
        # `T`-second clock starts, so the outer deadline must exceed `T + max(30, T)`.
        build = [lr, "--mode", "build", "--concurrency", "1", "--timeout", "1200", "--", "lake", "build"]
        self.assertEqual(suite._outer_timeout_sec(build, 1200), 1200 + 1200 + grace)
        short = [lr, "--mode", "build", "--timeout", "10", "--", "lake", "build"]
        self.assertEqual(suite._outer_timeout_sec(short, 10), 10 + 30 + grace)
        # `file` mode and `--no-slot-lock` never queue.
        file_cmd = [lr, "--mode", "file", "--timeout", "300", "--", "lake", "env", "lean", "X.lean"]
        self.assertEqual(suite._outer_timeout_sec(file_cmd, 300), 300 + grace)
        nolock = [lr, "--mode", "build", "--no-slot-lock", "--timeout=900", "--", "lake", "build"]
        self.assertEqual(suite._lean_run_wrapper_flags(nolock), ("build", 900, False))
        self.assertEqual(suite._outer_timeout_sec(nolock, 900), 900 + grace)
        # `auto` resolves like the wrapper; without `--timeout` the wrapper defaults apply.
        auto_file = [lr, "--", "lake", "env", "lean", "X.lean"]
        self.assertEqual(suite._lean_run_wrapper_flags(auto_file), ("file", None, True))
        self.assertEqual(suite._outer_timeout_sec(auto_file, 60), 180 + grace)
        auto_file_nosep = [lr, "lake", "env", "lean", "X.lean"]
        self.assertEqual(suite._lean_run_wrapper_flags(auto_file_nosep), ("file", None, True))
        self.assertEqual(suite._outer_timeout_sec(auto_file_nosep, 60), 180 + grace)
        auto_build = [lr, "--", "lake", "build", "Anneal"]
        self.assertEqual(suite._lean_run_wrapper_flags(auto_build), ("build", None, True))
        self.assertEqual(suite._outer_timeout_sec(auto_build, 60), 900 + 900 + grace)
        # Inner command `--` and inner flags (e.g. `cargo test -- --no-slot-lock --timeout 5`)
        # must never be mistaken for wrapper flags.
        inner_sep = [
            lr,
            "--mode",
            "build",
            "--timeout",
            "600",
            "cargo",
            "test",
            "--",
            "--no-slot-lock",
            "--mode",
            "file",
            "--timeout",
            "5",
        ]
        self.assertEqual(suite._lean_run_wrapper_flags(inner_sep), ("build", 600, True))
        self.assertEqual(suite._outer_timeout_sec(inner_sep, 600), 600 + 600 + grace)
        # `argparse` long-option prefix abbreviations (`--time`, `--no-slot`, `--conc`) and
        # `ANNEAL_LEAN_TIMEOUT_SEC` env fallback when `--timeout` is omitted.
        abbrev = [lr, "--mo", "build", "--no-slot", "--conc=1", "--time", "450", "--", "lake", "build"]
        self.assertEqual(suite._lean_run_wrapper_flags(abbrev), ("build", 450, False))
        self.assertEqual(suite._outer_timeout_sec(abbrev, 300), 450 + grace)
        self.assertEqual(
            suite._outer_timeout_sec(auto_build, 60, env={"ANNEAL_LEAN_TIMEOUT_SEC": "1500"}),
            1500 + 1500 + grace,
        )
        self.assertEqual(
            suite._outer_timeout_sec(auto_file, 60, env={"ANNEAL_LEAN_TIMEOUT_SEC": "240"}),
            240 + grace,
        )
        # A wrapped step never gets a shorter outer deadline than its own budget.
        for profile in ("quick", "nightly"):
            for name, _cat, cmd, timeout_sec in suite.build_suite_steps(REPO_ROOT, profile):
                outer = suite._outer_timeout_sec(cmd, timeout_sec)
                if suite._is_lean_run_wrapped(cmd):
                    mode, _t, _lock = suite._lean_run_wrapper_flags(cmd)
                    slot = max(30, timeout_sec) if mode == "build" else 0
                    self.assertEqual(outer, timeout_sec + slot + grace, f"{profile}/{name}")
                else:
                    self.assertEqual(outer, timeout_sec, f"{profile}/{name}")

    def _assert_pid_gone(self, pid: int, what: str) -> None:
        deadline = time.monotonic() + 10.0
        while time.monotonic() < deadline:
            try:
                state = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[0]
            except (OSError, IndexError):
                return
            if state == "Z":
                return
            time.sleep(0.05)
        try:
            os.kill(pid, 9)
        except OSError:
            pass
        self.fail(f"{what} (pid {pid}) survived the step timeout")

    def test_run_step_timeout_terminates_whole_step_process_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            pid_file = Path(tmp) / "pids"
            # A same-group grandchild (as `cargo` children are) must not outlive the step.
            script = (
                "import subprocess, sys, time\n"
                f"child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])\n"
                f"open({str(pid_file)!r}, 'w').write(str(child.pid))\n"
                "print('partial-output-before-timeout', flush=True)\n"
                "time.sleep(60)\n"
            )
            t0 = time.monotonic()
            res = suite._run_step(
                name="hung_step",
                category="cat7_python_and_ci_tests",
                cmd=[sys.executable, "-c", script],
                cwd=REPO_ROOT,
                timeout_sec=2,
            )
            self.assertLess(time.monotonic() - t0, 30.0)
            self.assertEqual(res["status"], "TIMEOUT")
            self.assertEqual(res["exit_code"], 124)
            self.assertIn("partial-output-before-timeout", res["failure_excerpt"])
            self.assertIn("Timed out after", res["failure_excerpt"])
            self._assert_pid_gone(int(pid_file.read_text()), "same-group grandchild")

    def test_run_step_timeout_lets_wrapper_reap_its_separate_session_scope(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            pid_file = Path(tmp) / "pids"
            # Mirrors `anneal-lean-run`: the build runs in its own session and is only
            # reaped by the wrapper's SIGTERM handler, so a bare SIGKILL of the wrapper
            # (what `subprocess.run(timeout=...)` does) would orphan it.
            script = (
                "import os, signal, subprocess, sys, time\n"
                "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'],\n"
                "                         start_new_session=True)\n"
                f"open({str(pid_file)!r}, 'w').write(str(child.pid))\n"
                "def on_term(signum, frame):\n"
                "    os.killpg(child.pid, signal.SIGKILL)\n"
                "    child.wait()\n"
                "    sys.exit(128 + signum)\n"
                "signal.signal(signal.SIGTERM, on_term)\n"
                "time.sleep(60)\n"
            )
            res = suite._run_step(
                name="hung_wrapper",
                category="cat2_correspondence_suites",
                cmd=[sys.executable, "-c", script],
                cwd=REPO_ROOT,
                timeout_sec=2,
            )
            self.assertEqual(res["status"], "TIMEOUT")
            self._assert_pid_gone(int(pid_file.read_text()), "separate-session build scope")

    def test_run_step_reports_launch_failure_and_undecodable_output(self) -> None:
        missing = suite._run_step(
            name="missing_tool",
            category="cat7_python_and_ci_tests",
            cmd=[str(REPO_ROOT / "scripts" / "no-such-tool-ep2")],
            cwd=REPO_ROOT,
            timeout_sec=5,
        )
        self.assertEqual(missing["status"], "FAIL")
        self.assertEqual(missing["exit_code"], 127)
        garbage = suite._run_step(
            name="binary_output",
            category="cat7_python_and_ci_tests",
            cmd=[sys.executable, "-c", "import sys; sys.stdout.buffer.write(b'\\xff\\xfe bad'); sys.exit(3)"],
            cwd=REPO_ROOT,
            timeout_sec=10,
        )
        self.assertEqual(garbage["status"], "FAIL")
        self.assertEqual(garbage["exit_code"], 3)
        self.assertIn("bad", garbage["failure_excerpt"])

    def test_lean_header_imports_parses_module_system_and_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / "T.lean"
            f.write_text(
                "/- header /- nested -/ comment -/\n"
                "module\n"
                "-- line comment import Fake.Module\n"
                "public import Anneal.ByteCodec\n"
                "meta import all Anneal.Mir.Cast  -- trailing\n"
                "import «Anneal».BitValidity import Foo.«a b».c\n"
                "import Bar.«x--y».«z/-w» -- comment after guillemets\n"
                "\n"
                "theorem t : True := by\n"
                "  trivial\n"
                "import Not.A.Header.Import\n",
                encoding="utf-8",
            )
            self.assertEqual(
                suite._lean_header_imports(f),
                [
                    "Anneal.ByteCodec",
                    "Anneal.Mir.Cast",
                    "Anneal.BitValidity",
                    "Foo.a b.c",
                    "Bar.x--y.z/-w",
                ],
            )
            self.assertIsNone(suite._lean_header_imports(Path(tmp) / "missing.lean"))

    def test_terminate_step_grants_grace_window_to_same_group_descendants(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            marker = Path(tmp) / "cleaned"
            # Leader exits immediately on SIGTERM while its same-group child takes 0.25s
            # to write `marker` before exiting cleanly on SIGTERM.
            child_code = (
                "import pathlib, signal, sys, time\n"
                "def handler(s, f):\n"
                "    time.sleep(0.25)\n"
                f"    pathlib.Path({str(marker)!r}).write_text('grace-ok')\n"
                "    sys.exit(0)\n"
                "signal.signal(signal.SIGTERM, handler)\n"
                "time.sleep(60)\n"
            )
            leader_code = (
                "import signal, subprocess, sys, time\n"
                f"subprocess.Popen([sys.executable, '-c', {child_code!r}])\n"
                "signal.signal(signal.SIGTERM, lambda s, f: sys.exit(0))\n"
                "time.sleep(60)\n"
            )
            res = suite._run_step(
                name="leader_exits_first",
                category="cat7_python_and_ci_tests",
                cmd=[sys.executable, "-c", leader_code],
                cwd=REPO_ROOT,
                timeout_sec=1,
            )
            self.assertEqual(res["status"], "TIMEOUT")
            self.assertTrue(marker.is_file(), "same-group child was SIGKILLed before grace window")
            self.assertEqual(marker.read_text(), "grace-ok")


if __name__ == "__main__":
    unittest.main()
