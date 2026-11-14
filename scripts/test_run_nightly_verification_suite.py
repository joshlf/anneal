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
from pathlib import Path
import sys
import tempfile
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
        for step_name, exp_timeout in expected_timeouts.items():
            self.assertIn(step_name, nightly_by_name)
            _cat, cmd, timeout_sec = nightly_by_name[step_name]
            self.assertEqual(timeout_sec, exp_timeout, f"Unexpected timeout for {step_name}")
            self.assertEqual(Path(cmd[0]).name, "anneal-lean-run", f"{step_name} must be wrapped")
            self.assertIn("--timeout", cmd)
            t_idx = cmd.index("--timeout")
            self.assertEqual(int(cmd[t_idx + 1]), timeout_sec)

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


if __name__ == "__main__":
    unittest.main()
