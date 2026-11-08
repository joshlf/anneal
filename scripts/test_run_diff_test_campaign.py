#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `scripts/run_diff_test_campaign.py`."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import run_diff_test_campaign as campaign


def make_healthy_miri_report(
    state_dir: Path,
    seed: str = "0x10010001",
    fingerprints: list[str] | None = None,
    obs_path_signatures: list[str] | None = None,
    mutator_bonus: int = 0,
) -> dict:
    fps = fingerprints if fingerprints is not None else []
    obs = (
        obs_path_signatures
        if obs_path_signatures is not None
        else [
            "miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree",
            "miri:s02_slice_get@BoundsCheckElimMutator:ub_vs_ub:agree",
        ]
    )
    findings = []
    for idx, fp in enumerate(fps):
        parts = fp.split(":", 2)
        cause = parts[0]
        div_class = parts[1] if len(parts) > 1 else "false_positive_ub"
        lean_tag = parts[2] if len(parts) > 2 else "MirDiffTag.ub:invalid_value_load"
        bundle_dir = state_dir / "findings" / f"miri_f{idx}"
        bundle_dir.mkdir(parents=True, exist_ok=True)
        repro_rs = bundle_dir / "repro.rs"
        repro_rs.write_text("fn main() {}\n", encoding="utf-8")
        findings.append(
            {
                "finding_id": f"miri_f{idx}",
                "fn_name": f"b0_c{idx}__entry",
                "seed_name": "s01_checked_add",
                "applied_mutators": [cause],
                "divergence_class": div_class,
                "miri_outcome": "pass",
                "anneal_outcome": f"ub:{lean_tag}",
                "anneal_lean_tag": lean_tag,
                "miri_excerpt": "clean execution",
                "repro_path": str(repro_rs),
                "kernel_confirmed": True,
            }
        )

    n_div = len(findings)
    div_classes = {k: 0 for k in campaign.VALID_DIVERGENCE_CLASSES}
    for f in findings:
        div_classes[f["divergence_class"]] += 1

    return {
        "harness": "miri-difftest",
        "mode": "seeded",
        "oracle_comparison": "performed",
        "seed": seed,
        "batches": 2,
        "batch_size": 4,
        "total_candidates": 8,
        "compiled_candidates": 8,
        "compile_failed_candidates": 0,
        "compared_candidates": 8,
        "agree_count": 8 - n_div,
        "diverge_count": n_div,
        "not_compared_count": 0,
        "kernel_confirmed_divergences": n_div,
        "elapsed_ms": 250.0,
        "miri_verdicts": {
            "pass": 8,
            "panic": 0,
            "ub": 0,
            "error": 0,
        },
        "anneal_outcomes": {
            "pass": 8 - n_div,
            "panic": 0,
            "ub": n_div,
            "unsupported": 0,
            "out_of_fuel": 0,
            "external_call": 0,
            "error": 0,
        },
        "divergence_classes": div_classes,
        "not_compared_reasons": {k: 0 for k in campaign.VALID_NOT_COMPARED_REASONS},
        "unmodeled_external_calls": {},
        "mutator_applications": {
            "BitValidityTransmuteMutator": 4 + mutator_bonus,
            "PlaceProjectionWrapper": 4,
        },
        "obs_path_signatures": obs,
        "findings": findings,
    }


def make_healthy_itree_report(
    state_dir: Path,
    seed: str = "0x20020002",
    fingerprints: list[str] | None = None,
    obs_path_signatures: list[str] | None = None,
    not_compared_candidates: int = 0,
    mutator_bonus: int = 0,
) -> dict:
    fps = fingerprints if fingerprints is not None else []
    obs = (
        obs_path_signatures
        if obs_path_signatures is not None
        else [
            "itree:it01_pure_return@IdentityMutator:0011223344556677:ok",
            "itree:it02_single_ext_call@CallBoundaryOutliner:8899aabbccddeeff:ok",
        ]
    )
    findings = []
    for idx, fp in enumerate(fps):
        parts = fp.split(":", 2)
        cause = parts[0]
        bundle_dir = state_dir / "findings" / f"itree_f{idx}"
        bundle_dir.mkdir(parents=True, exist_ok=True)
        repro_rs = bundle_dir / "repro.rs"
        repro_rs.write_text("fn main() {}\n", encoding="utf-8")
        findings.append(
            {
                "finding_id": f"itree_f{idx}",
                "fn_name": f"b0_c{idx}__kernel_step",
                "seed_index": 0,
                "applied_mutators": [cause],
                "case_ident": f"case_{idx}",
                "diag_tag": "outcome_mismatch",
                "diag_repr": "TraceReplayDiag.outcome_mismatch",
                "trace_hex": "0011",
                "checked_mir_module": "Mir.ItreeDiffStaged",
                "repro_path": str(repro_rs),
                "kernel_confirmed": True,
            }
        )

    n_div = len(findings)
    compared = 8 - not_compared_candidates
    diag_counts = {k: 0 for k in campaign.VALID_ITREE_DIAG_TAGS}
    diag_counts["ok"] = 16 - n_div
    diag_counts["outcome_mismatch"] = n_div

    return {
        "harness": "itree-difftest",
        "mode": "seeded",
        "oracle_comparison": "performed",
        "seed": seed,
        "batches": 2,
        "batch_size": 4,
        "trials_per_candidate": 4,
        "total_candidates": 8,
        "unsafe_token_violations": 0,
        "opt_level_0_compiled": 8,
        "opt_level_2_compiled": 8,
        "opt_level_0_and_2_compiled": 8,
        "instrumented_compiled": compared,
        "compared_candidates": compared,
        "agree_candidates": compared - n_div,
        "diverge_candidates": n_div,
        "not_compared_candidates": not_compared_candidates,
        "not_compared_reasons": {
            "compile_failed": 0,
            "staging_failed": 0,
            "empty_trace": 0,
            "lean_probe_failed": not_compared_candidates,
            "lean_confirm_failed": 0,
        },
        "total_traces_executed": compared * 4,
        "distinct_traces_checked": 16,
        "agree_traces": 16 - n_div,
        "diverge_traces": n_div,
        "kernel_confirmed_traces": 16,
        "kernel_confirmed_divergences": n_div,
        "distinct_obs_paths": len(obs) + mutator_bonus,
        "elapsed_ms": 250.0,
        "diag_tag_counts": diag_counts,
        "per_candidate_distinct_traces": {
            "b0_c0__kernel_step": 4,
            "b0_c1__kernel_step": 4,
        },
        "mutator_applications": {
            "CallBoundaryOutliner": 4 + mutator_bonus,
            "LayoutPaddingPerturber": 4,
        },
        "obs_path_signatures": obs,
        "findings": findings,
    }


def write_initial_ledger(state_dir: Path, **overrides) -> Path:
    ledger = {
        "schema_version": 1,
        "total_campaigns_run": 10,
        "per_suite_runs": {"miri": 10, "itree": 10},
        "last_miri_seed": "0x10000000",
        "last_itree_seed": "0x20000000",
        "next_miri_seed": "0x10010001",
        "next_itree_seed": "0x20020002",
        "active_fingerprints": [
            "BitValidityTransmuteMutator:false_positive_ub:MirDiffTag.ub:invalid_value_load",
            "PlaceProjectionWrapper:false_positive_ub:MirDiffTag.ub:invalid_value_load",
        ],
        "quarantined_fingerprints": [],
        "fingerprint_history": {
            "BitValidityTransmuteMutator:false_positive_ub:MirDiffTag.ub:invalid_value_load": {
                "suite": "miri-difftest",
                "first_seen_date": "2026-04-06",
                "last_seen_date": "2026-04-10",
                "campaigns_failing": 4,
            },
            "PlaceProjectionWrapper:false_positive_ub:MirDiffTag.ub:invalid_value_load": {
                "suite": "miri-difftest",
                "first_seen_date": "2026-04-06",
                "last_seen_date": "2026-04-10",
                "campaigns_failing": 4,
            },
        },
        "resolved_history": {},
    }
    ledger.update(overrides)
    path = state_dir / "state" / "campaign_ledger.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(ledger, indent=2) + "\n", encoding="utf-8")
    return path


class RunDiffTestCampaignTest(unittest.TestCase):
    def setUp(self) -> None:
        campaign.LAST_HARNESS_DIAGNOSTICS.clear()

    def test_partial_suite_failure_miri_healthy_itree_crashed(self) -> None:
        """1. miri-difftest healthy + itree-difftest crash -> miri seed advances, itree fixed, exit 2."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            itree_fp = "CallBoundaryOutliner:itree_outcome_mismatch:TraceReplayDiag.outcome_mismatch"
            miri_fp = "BitValidityTransmuteMutator:false_positive_ub:MirDiffTag.ub:invalid_value_load"
            miri_resolved_fp = "PlaceProjectionWrapper:false_positive_ub:MirDiffTag.ub:invalid_value_load"
            write_initial_ledger(
                state_dir,
                active_fingerprints=[miri_fp, miri_resolved_fp, itree_fp],
                fingerprint_history={
                    miri_fp: {
                        "suite": "miri-difftest",
                        "first_seen_date": "2026-04-06",
                        "last_seen_date": "2026-04-10",
                        "campaigns_failing": 4,
                    },
                    miri_resolved_fp: {
                        "suite": "miri-difftest",
                        "first_seen_date": "2026-04-06",
                        "last_seen_date": "2026-04-10",
                        "campaigns_failing": 4,
                    },
                    itree_fp: {
                        "suite": "itree-difftest",
                        "first_seen_date": "2026-04-08",
                        "last_seen_date": "2026-04-10",
                        "campaigns_failing": 2,
                    },
                },
            )

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                if bin_name == "miri-difftest":
                    campaign.LAST_HARNESS_DIAGNOSTICS[bin_name] = {
                        "exit_code": 0,
                        "oracle_error_reason": None,
                        "stderr_tail": "",
                        "elapsed_s": 1.25,
                    }
                    return make_healthy_miri_report(state_dir, fingerprints=[miri_fp])
                campaign.LAST_HARNESS_DIAGNOSTICS[bin_name] = {
                    "exit_code": 101,
                    "oracle_error_reason": "lake env lean failed (status exit status: 137)",
                    "stderr_tail": "Thread 1: lake env lean killed by SIGKILL (OOM)",
                    "elapsed_s": 14.5,
                }
                return None

            fileutil_calls: list[list[str]] = []

            def fake_run_fileutil(args: list[str]) -> subprocess.CompletedProcess[str]:
                fileutil_calls.append(list(args))
                return subprocess.CompletedProcess(args, 0, "", "")

            with mock.patch.object(
                campaign, "run_harness", side_effect=fake_run_harness
            ), mock.patch.object(
                campaign, "has_x20_fileutil", return_value=True
            ), mock.patch.object(
                campaign, "run_fileutil", side_effect=fake_run_fileutil
            ):
                rc = campaign.main(
                    [
                        "--profile",
                        "smoke",
                        "--state-dir",
                        str(state_dir),
                        "--x20-uri",
                        "/x20/teams/anneal-agent/difftest",
                    ]
                )

            self.assertEqual(rc, campaign.EXIT_HARNESS_FAILED)
            ledger = json.loads(
                (state_dir / "state" / "campaign_ledger.json").read_text(encoding="utf-8")
            )
            self.assertEqual(ledger["schema_version"], 1)
            self.assertEqual(ledger["total_campaigns_run"], 11)
            # miri seed advances; itree seed stays fixed!
            self.assertEqual(ledger["last_miri_seed"], "0x10010001")
            expected_next_miri = f"0x{campaign.advance_seed(0x10010001):08x}"
            self.assertEqual(ledger["next_miri_seed"], expected_next_miri)
            self.assertEqual(ledger["last_itree_seed"], "0x20000000")
            self.assertEqual(ledger["next_itree_seed"], "0x20020002")
            self.assertEqual(
                ledger["per_suite_runs"],
                {"miri": 11, "itree": 10},
            )
            # miri_fp (still failing) and itree_fp (untouched because itree crashed) stay active,
            # while miri_resolved_fp transitions cleanly to resolved_history even though itree failed!
            self.assertIn(miri_fp, ledger["active_fingerprints"])
            self.assertNotIn(miri_resolved_fp, ledger["active_fingerprints"])
            self.assertIn(miri_resolved_fp, ledger["resolved_history"])
            self.assertEqual(
                ledger["resolved_history"][miri_resolved_fp]["suite"], "miri-difftest"
            )
            self.assertIn(itree_fp, ledger["active_fingerprints"])
            self.assertNotIn(itree_fp, ledger["resolved_history"])
            self.assertEqual(
                ledger["fingerprint_history"][miri_fp]["campaigns_failing"], 5
            )
            self.assertEqual(
                ledger["fingerprint_history"][itree_fp]["campaigns_failing"], 2
            )

            # coverage_ratchet.json updated from miri-difftest only and uploaded to stub x20
            ratchet_path = state_dir / "state" / "coverage_ratchet.json"
            self.assertTrue(ratchet_path.is_file())
            ratchet = json.loads(ratchet_path.read_text(encoding="utf-8"))
            self.assertEqual(
                ratchet["per_suite_distinct_obs_paths"]["miri"],
                2,
            )
            self.assertEqual(
                ratchet["per_suite_distinct_obs_paths"]["itree"],
                0,
            )
            cp_calls = [c for c in fileutil_calls if c and c[0] == "cp"]
            self.assertTrue(
                any(c[3].endswith("/state/coverage_ratchet.json") for c in cp_calls),
                f"expected coverage_ratchet.json upload to x20 in {cp_calls}",
            )

    def test_reverse_partial_suite_failure_miri_crashed_itree_healthy(self) -> None:
        """2. miri-difftest fails + itree-difftest healthy -> itree seed advances, miri fixed, exit 2."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            miri_fp = "BitValidityTransmuteMutator:false_positive_ub:MirDiffTag.ub:invalid_value_load"
            write_initial_ledger(state_dir, active_fingerprints=[miri_fp])

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                if bin_name == "miri-difftest":
                    campaign.LAST_HARNESS_DIAGNOSTICS[bin_name] = {
                        "exit_code": 1,
                        "oracle_error_reason": "miri sysroot compile failed",
                        "stderr_tail": "error: could not find cargo-miri",
                        "elapsed_s": 0.5,
                    }
                    return None
                campaign.LAST_HARNESS_DIAGNOSTICS[bin_name] = {
                    "exit_code": 0,
                    "oracle_error_reason": None,
                    "stderr_tail": "",
                    "elapsed_s": 2.0,
                }
                return make_healthy_itree_report(state_dir, not_compared_candidates=1)

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = campaign.main(
                    ["--profile", "smoke", "--state-dir", str(state_dir), "--x20-uri", ""]
                )

            self.assertEqual(rc, campaign.EXIT_HARNESS_FAILED)
            ledger = json.loads(
                (state_dir / "state" / "campaign_ledger.json").read_text(encoding="utf-8")
            )
            # miri seed stays fixed; itree seed advances!
            self.assertEqual(ledger["last_miri_seed"], "0x10000000")
            self.assertEqual(ledger["next_miri_seed"], "0x10010001")
            self.assertEqual(ledger["last_itree_seed"], "0x20020002")
            expected_next_itree = f"0x{campaign.advance_seed(0x20020002):08x}"
            self.assertEqual(ledger["next_itree_seed"], expected_next_itree)
            self.assertEqual(
                ledger["per_suite_runs"],
                {"miri": 10, "itree": 11},
            )
            # miri_fp must NOT be falsely resolved when miri crashed!
            self.assertIn(miri_fp, ledger["active_fingerprints"])
            self.assertNotIn(miri_fp, ledger["resolved_history"])

            ratchet = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                ratchet["per_suite_distinct_obs_paths"]["miri"],
                0,
            )
            self.assertEqual(
                ratchet["per_suite_distinct_obs_paths"]["itree"],
                2,
            )

    def test_total_suite_failure_leaves_ledger_and_ratchet_untouched(self) -> None:
        """3. Neither suite healthy -> campaign_ledger.json and coverage_ratchet.json untouched, exit 2."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            ledger_path = write_initial_ledger(state_dir)
            before_bytes = ledger_path.read_bytes()

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                campaign.LAST_HARNESS_DIAGNOSTICS[bin_name] = {
                    "exit_code": 2,
                    "oracle_error_reason": "oracle failed",
                    "stderr_tail": "fatal harness failure",
                    "elapsed_s": 0.1,
                }
                return None

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = campaign.main(
                    ["--profile", "smoke", "--state-dir", str(state_dir), "--x20-uri", ""]
                )

            self.assertEqual(rc, campaign.EXIT_HARNESS_FAILED)
            self.assertEqual(ledger_path.read_bytes(), before_bytes)
            self.assertFalse((state_dir / "state" / "coverage_ratchet.json").exists())

    def test_fingerprint_aging_and_resolved_history_transition(self) -> None:
        """4. Active fingerprints increment campaigns_failing or move to resolved_history when fixed."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            fp_bit = "BitValidityTransmuteMutator:false_positive_ub:MirDiffTag.ub:invalid_value_load"
            fp_place = "PlaceProjectionWrapper:false_positive_ub:MirDiffTag.ub:invalid_value_load"
            fp_new = "RawPtrOffsetMutator:false_positive_ub:MirDiffTag.ub:out_of_bounds"
            write_initial_ledger(state_dir, active_fingerprints=[fp_bit, fp_place])

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                campaign.LAST_HARNESS_DIAGNOSTICS[bin_name] = {
                    "exit_code": 0,
                    "oracle_error_reason": None,
                    "stderr_tail": "",
                    "elapsed_s": 1.0,
                }
                if bin_name == "miri-difftest":
                    # fp_bit and fp_place are both fixed in this run; fp_new is newly observed!
                    return make_healthy_miri_report(state_dir, fingerprints=[fp_new])
                return make_healthy_itree_report(state_dir)

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = campaign.main(
                    ["--profile", "smoke", "--state-dir", str(state_dir), "--x20-uri", ""]
                )

            # fp_new is an unquarantined divergence -> EXIT_DIVERGENCE_DETECTED (4)
            self.assertEqual(rc, campaign.EXIT_DIVERGENCE_DETECTED)
            ledger = json.loads(
                (state_dir / "state" / "campaign_ledger.json").read_text(encoding="utf-8")
            )
            self.assertEqual(ledger["active_fingerprints"], [fp_new])
            self.assertNotIn(fp_bit, ledger["active_fingerprints"])
            self.assertNotIn(fp_place, ledger["active_fingerprints"])
            self.assertIn(fp_bit, ledger["resolved_history"])
            self.assertIn(fp_place, ledger["resolved_history"])
            self.assertIn("resolved_date", ledger["resolved_history"][fp_bit])
            self.assertEqual(
                ledger["resolved_history"][fp_bit]["suite"], "miri-difftest"
            )
            self.assertEqual(
                ledger["fingerprint_history"][fp_new]["campaigns_failing"], 1
            )
            self.assertEqual(
                ledger["fingerprint_history"][fp_new]["suite"], "miri-difftest"
            )

    def test_coverage_ratchet_monotonicity_and_x20_sync_round_trip(self) -> None:
        """5. coverage_ratchet.json grows monotonically across runs and syncs with x20."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            write_initial_ledger(state_dir, active_fingerprints=[])

            run_counter = {"count": 0}

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                campaign.LAST_HARNESS_DIAGNOSTICS[bin_name] = {
                    "exit_code": 0,
                    "oracle_error_reason": None,
                    "stderr_tail": "",
                    "elapsed_s": 0.8,
                }
                idx = run_counter["count"]
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(
                        state_dir,
                        obs_path_signatures=[
                            "miri:s01@M1:pass_vs_pass:agree",
                            f"miri:s02@M{idx}:ub_vs_ub:agree",
                        ],
                        mutator_bonus=idx,
                    )
                return make_healthy_itree_report(
                    state_dir,
                    obs_path_signatures=[
                        "itree:it01@I1:0011223344556677:ok",
                        f"itree:it02@I{idx}:8899aabbccddeeff:ok",
                    ],
                    mutator_bonus=idx,
                )

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc1 = campaign.main(
                    ["--profile", "smoke", "--state-dir", str(state_dir), "--x20-uri", ""]
                )
                self.assertEqual(rc1, campaign.EXIT_SUCCESS)
                ratchet1 = json.loads(
                    (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
                )
                miri_before = ratchet1["per_suite_distinct_obs_paths"]["miri"]
                itree_before = ratchet1["per_suite_distinct_obs_paths"]["itree"]
                total_before = ratchet1["cumulative_distinct_obs_paths"]
                self.assertEqual(miri_before, 2)
                self.assertEqual(itree_before, 2)
                self.assertEqual(total_before, 4)

                run_counter["count"] = 1
                rc2 = campaign.main(
                    ["--profile", "smoke", "--state-dir", str(state_dir), "--x20-uri", ""]
                )
                self.assertEqual(rc2, campaign.EXIT_SUCCESS)
                ratchet2 = json.loads(
                    (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
                )
                miri_after = ratchet2["per_suite_distinct_obs_paths"]["miri"]
                itree_after = ratchet2["per_suite_distinct_obs_paths"]["itree"]
                total_after = ratchet2["cumulative_distinct_obs_paths"]
                self.assertGreaterEqual(miri_after, miri_before)
                self.assertGreaterEqual(itree_after, itree_before)
                self.assertGreaterEqual(total_after, total_before)
                self.assertEqual(miri_after, 3)
                self.assertEqual(itree_after, 3)
                self.assertEqual(total_after, 6)

            # Verify x20 sync round-trip includes state/coverage_ratchet.json
            fileutil_calls: list[list[str]] = []

            def fake_run_fileutil(args: list[str]) -> subprocess.CompletedProcess[str]:
                fileutil_calls.append(list(args))
                return subprocess.CompletedProcess(args, 0, "", "")

            with mock.patch.object(
                campaign, "has_x20_fileutil", return_value=True
            ), mock.patch.object(
                campaign, "run_fileutil", side_effect=fake_run_fileutil
            ):
                campaign.sync_state_from_x20(
                    "/x20/teams/anneal-agent/difftest", state_dir, include_ratchet=True
                )
                campaign.sync_state_to_x20(
                    state_dir,
                    "/x20/teams/anneal-agent/difftest",
                    [
                        state_dir / "state" / "campaign_ledger.json",
                        state_dir / "state" / "coverage_ratchet.json",
                    ],
                )

            cp_calls = [c for c in fileutil_calls if c and c[0] == "cp"]
            self.assertTrue(
                any(
                    c[2].endswith("/state/coverage_ratchet.json")
                    for c in cp_calls
                ),
                f"expected pull of coverage_ratchet.json in cp_calls: {cp_calls}",
            )
            self.assertTrue(
                any(
                    c[3].endswith("/state/coverage_ratchet.json")
                    for c in cp_calls
                ),
                f"expected push of coverage_ratchet.json in cp_calls: {cp_calls}",
            )

    def test_report_mode_cell_honesty_and_diagnostics_on_itree_failure(self) -> None:
        """6. LATEST_REPORT.md renders `harness-failed` (never `compile-only`) when itree returns None."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            write_initial_ledger(state_dir, active_fingerprints=[])

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                if bin_name == "miri-difftest":
                    campaign.LAST_HARNESS_DIAGNOSTICS[bin_name] = {
                        "exit_code": 0,
                        "oracle_error_reason": None,
                        "stderr_tail": "",
                        "elapsed_s": 1.1,
                    }
                    return make_healthy_miri_report(state_dir)
                campaign.LAST_HARNESS_DIAGNOSTICS[bin_name] = {
                    "exit_code": 2,
                    "oracle_error_reason": "Stage 1 Lean probe crashed",
                    "stderr_tail": "error: lean process exited with code 137",
                    "elapsed_s": 9.4,
                }
                return None

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = campaign.main(
                    ["--profile", "smoke", "--state-dir", str(state_dir), "--x20-uri", ""]
                )

            self.assertEqual(rc, campaign.EXIT_HARNESS_FAILED)
            report_md = (state_dir / "reports" / "LATEST_REPORT.md").read_text(
                encoding="utf-8"
            )
            self.assertIn("| Mode | `seeded` | `harness-failed` |", report_md)
            self.assertNotIn("`compile-only`", report_md)
            self.assertIn("## Harness Subprocess Diagnostics", report_md)
            self.assertIn("Stage 1 Lean probe crashed", report_md)
            self.assertIn("error: lean process exited with code 137", report_md)

            summary = json.loads(
                (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertIn("harness_diagnostics", summary)
            self.assertEqual(
                summary["harness_diagnostics"]["itree-difftest"]["exit_code"], 2
            )
            self.assertEqual(
                summary["harness_diagnostics"]["itree-difftest"]["oracle_error_reason"],
                "Stage 1 Lean probe crashed",
            )


if __name__ == "__main__":
    unittest.main()
