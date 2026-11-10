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

import contextlib
import copy
import io
import json
import os
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
    kernel_confirmed_traces: int = 16,
) -> dict:
    """An internally consistent live `itree-difftest` summary.

    `not_compared_candidates` candidates compiled everywhere but were dropped
    by an isolated Lean probe failure (`lean_probe_failed`).
    """
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
        "instrumented_compiled": 8,
        "compared_candidates": compared,
        "agree_candidates": compared - n_div,
        "diverge_candidates": n_div,
        "not_compared_candidates": not_compared_candidates,
        "not_compared_reasons": {
            "compile_failed": 0,
            "staging_failed": 0,
            "trace_collect_failed": 0,
            "opt_level_trace_mismatch": 0,
            "empty_trace": 0,
            "lean_build_failed": 0,
            "lean_probe_failed": not_compared_candidates,
            "lean_confirm_failed": 0,
        },
        "total_traces_executed": compared * 4,
        "distinct_traces_checked": 16,
        "agree_traces": 16 - n_div,
        "diverge_traces": n_div,
        "kernel_confirmed_traces": kernel_confirmed_traces,
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

            remote_sync_calls: list[list[str]] = []

            def fake_run_remote_sync(args: list[str]) -> subprocess.CompletedProcess[str]:
                remote_sync_calls.append(list(args))
                return subprocess.CompletedProcess(args, 0, "", "")

            with mock.patch.object(
                campaign, "run_harness", side_effect=fake_run_harness
            ), mock.patch.object(
                campaign, "has_remote_sync", return_value=True
            ), mock.patch.object(
                campaign, "run_remote_sync", side_effect=fake_run_remote_sync
            ):
                rc = campaign.main(
                    [
                        "--profile",
                        "smoke",
                        "--state-dir",
                        str(state_dir),
                        "--remote-uri",
                        "/remote/teams/anneal-agent/difftest",
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

            # coverage_ratchet.json updated from miri-difftest only and uploaded to stub remote
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
            cp_calls = [c for c in remote_sync_calls if c and c[0] == "cp"]
            self.assertTrue(
                any(c[3].endswith("/state/coverage_ratchet.json") for c in cp_calls),
                f"expected coverage_ratchet.json upload to remote in {cp_calls}",
            )

    def test_reverse_partial_suite_failure_miri_crashed_itree_healthy(self) -> None:
        """2. miri-difftest fails + itree-difftest healthy -> itree seed advances, miri fixed, exit 2."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            miri_fp = "BitValidityTransmuteMutator:false_positive_ub:MirDiffTag.ub:invalid_value_load"
            ledger_path = write_initial_ledger(state_dir, active_fingerprints=[miri_fp])
            before = json.loads(ledger_path.read_text(encoding="utf-8"))
            junit = state_dir / "diff_test_report.xml"

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
                return make_healthy_itree_report(state_dir)

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = campaign.main(
                    [
                        "--profile",
                        "smoke",
                        "--state-dir",
                        str(state_dir),
                        "--remote-uri",
                        "",
                        "--junit-xml",
                        str(junit),
                    ]
                )

            self.assertEqual(rc, campaign.EXIT_HARNESS_FAILED)
            ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
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
            self.assertEqual(ledger["last_oracle_comparison"], "miri_failed_itree_performed")
            # miri_fp must NOT be falsely resolved or aged when miri crashed!
            self.assertIn(miri_fp, ledger["active_fingerprints"])
            self.assertNotIn(miri_fp, ledger["resolved_history"])
            self.assertEqual(
                ledger["fingerprint_history"][miri_fp],
                before["fingerprint_history"][miri_fp],
            )

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
            report_md = (state_dir / "reports" / "LATEST_REPORT.md").read_text(
                encoding="utf-8"
            )
            self.assertIn("| Mode | `harness-failed` | `seeded` |", report_md)
            self.assertIn("could not find cargo-miri", report_md)
            junit_xml = junit.read_text(encoding="utf-8")
            self.assertIn('<failure message="harness failed">', junit_xml)
            self.assertNotIn("red-flag vacuity check failed", junit_xml)

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
                    ["--profile", "smoke", "--state-dir", str(state_dir), "--remote-uri", ""]
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
                    ["--profile", "smoke", "--state-dir", str(state_dir), "--remote-uri", ""]
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

    def test_coverage_ratchet_monotonicity_and_remote_sync_round_trip(self) -> None:
        """5. coverage_ratchet.json grows monotonically across runs and syncs with remote."""
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
                    ["--profile", "smoke", "--state-dir", str(state_dir), "--remote-uri", ""]
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
                    ["--profile", "smoke", "--state-dir", str(state_dir), "--remote-uri", ""]
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

            # Verify remote sync round-trip includes state/coverage_ratchet.json
            remote_sync_calls: list[list[str]] = []

            def fake_run_remote_sync(args: list[str]) -> subprocess.CompletedProcess[str]:
                remote_sync_calls.append(list(args))
                return subprocess.CompletedProcess(args, 0, "", "")

            with mock.patch.object(
                campaign, "has_remote_sync", return_value=True
            ), mock.patch.object(
                campaign, "run_remote_sync", side_effect=fake_run_remote_sync
            ):
                campaign.sync_state_from_remote(
                    "/remote/teams/anneal-agent/difftest", state_dir, include_ratchet=True
                )
                campaign.sync_state_to_remote(
                    state_dir,
                    "/remote/teams/anneal-agent/difftest",
                    [
                        state_dir / "state" / "campaign_ledger.json",
                        state_dir / "state" / "coverage_ratchet.json",
                    ],
                )

            cp_calls = [c for c in remote_sync_calls if c and c[0] == "cp"]
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
                        "stderr_tail": "Compiling miri_diff_corpus (healthy progress noise)",
                        "elapsed_s": 1.1,
                    }
                    return make_healthy_miri_report(state_dir)
                campaign.LAST_HARNESS_DIAGNOSTICS[bin_name] = {
                    "exit_code": 2,
                    "oracle_error_reason": "Stage 1 Lean probe crashed",
                    "stderr_tail": "error: lean process exited with code 137\n```\nraw fence in stderr",
                    "elapsed_s": 9.4,
                }
                return None

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = campaign.main(
                    ["--profile", "smoke", "--state-dir", str(state_dir), "--remote-uri", ""]
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
            # Only failed suites are diagnosed, and stderr fences cannot be broken.
            self.assertNotIn("healthy progress noise", report_md)
            self.assertIn("````text", report_md)

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


# The real `/remote/teams/anneal-agent/differential-testing/state/campaign_ledger.json`
# snapshot taken before the `2026-11-08` nightly (no `schema_version`,
# `per_suite_runs`, `fingerprint_history`, or `resolved_history`).
LEGACY_REMOTE_LEDGER = {
    "active_fingerprints": [
        "BitValidityTransmuteMutator:missed_ub:MirDiffTag.normalScalar",
        "PlaceProjectionWrapper:missed_ub:MirDiffTag.normalScalar",
    ],
    "cumulative_distinct_obs_paths": 0,
    "last_itree_seed": "0x8d17c13c",
    "last_itree_signature": {
        "diag_tag_counts": {"ok": 8564},
        "distinct_obs_paths": 4022,
        "mutator_applications": {"BranchLoopWeaver": 286},
    },
    "last_miri_seed": "0x8d17c13b",
    "last_miri_signature": {
        "anneal_outcomes": {"pass": 287},
        "miri_verdicts": {"pass": 274},
        "mutator_applications": {"ArithmeticCastMutator": 314},
    },
    "last_oracle_comparison": "performed",
    "last_profile": "nightly",
    "last_run_utc": "2026-11-07T07:12:52Z",
    "next_itree_seed": "0x2b4f3af5",
    "next_miri_seed": "0x2b4f3af4",
    "quarantined_fingerprints": [],
    "total_campaigns_run": 5,
    "total_itree_candidates_evaluated": 2560,
    "total_itree_candidates_generated": 2720,
    "total_itree_traces_checked": 27455,
    "total_miri_candidates_evaluated": 2700,
    "total_miri_candidates_generated": 2720,
}


def healthy_diag(bin_name: str) -> None:
    campaign.LAST_HARNESS_DIAGNOSTICS[bin_name] = {
        "exit_code": 0,
        "oracle_error_reason": None,
        "stderr_tail": "",
        "elapsed_s": 1.0,
    }


def run_main(state_dir: Path, *extra: str) -> int:
    return campaign.main(
        ["--profile", "smoke", "--state-dir", str(state_dir), "--remote-uri", "", *extra]
    )


def read_ledger(state_dir: Path) -> dict:
    return json.loads(
        (state_dir / "state" / "campaign_ledger.json").read_text(encoding="utf-8")
    )


class RedFlagAndLedgerHardeningTest(unittest.TestCase):
    """Targeted regression tests for issues found in adversarial pass B1."""

    def setUp(self) -> None:
        campaign.LAST_HARNESS_DIAGNOSTICS.clear()

    def test_isolated_itree_lean_failures_are_oracle_errors_not_silent_health(self) -> None:
        """A candidate dropped by a Lean probe failure trips `itree_oracle_error_threshold`."""
        for max_errors, expect_rc, expect_healthy in (
            (None, campaign.EXIT_HARNESS_FAILED, False),
            ("1", campaign.EXIT_SUCCESS, True),
        ):
            with self.subTest(max_oracle_errors=max_errors), tempfile.TemporaryDirectory() as tmp:
                state_dir = Path(tmp)
                write_initial_ledger(state_dir, active_fingerprints=[])

                def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                    healthy_diag(bin_name)
                    if bin_name == "miri-difftest":
                        return make_healthy_miri_report(state_dir)
                    return make_healthy_itree_report(state_dir, not_compared_candidates=1)

                extra = ["--max-oracle-errors", max_errors] if max_errors else []
                with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                    rc = run_main(state_dir, *extra)

                self.assertEqual(rc, expect_rc)
                ledger = read_ledger(state_dir)
                report_md = (state_dir / "reports" / "LATEST_REPORT.md").read_text(
                    encoding="utf-8"
                )
                self.assertIn(
                    "## Not-Compared Breakdown by Reason (`itree-difftest`)", report_md
                )
                self.assertIn("| `lean_probe_failed` | 1 |", report_md)
                # miri always advances: it was healthy either way.
                self.assertEqual(
                    ledger["next_miri_seed"], f"0x{campaign.advance_seed(0x10010001):08x}"
                )
                if expect_healthy:
                    self.assertIn("| `itree_oracle_error_threshold` | PASS |", report_md)
                    self.assertEqual(
                        ledger["next_itree_seed"],
                        f"0x{campaign.advance_seed(0x20020002):08x}",
                    )
                    self.assertEqual(ledger["per_suite_runs"], {"miri": 11, "itree": 11})
                else:
                    self.assertIn("| `itree_oracle_error_threshold` | **FAIL** |", report_md)
                    self.assertIn("itree_oracle_errors_exceeded", report_md)
                    self.assertIn("lean_probe_failed=1", report_md)
                    self.assertEqual(ledger["next_itree_seed"], "0x20020002")
                    self.assertEqual(ledger["per_suite_runs"], {"miri": 11, "itree": 10})

    def test_itree_not_compared_accounting_mismatch_is_red_flag(self) -> None:
        """`sum(not_compared_reasons)` must equal `not_compared_candidates`."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            write_initial_ledger(state_dir, active_fingerprints=[])
            itree = make_healthy_itree_report(state_dir, not_compared_candidates=1)
            # Hide the dropped candidate's reason: compared + not_compared still
            # equals total, but the drop is unexplained.
            itree["not_compared_reasons"]["lean_probe_failed"] = 0
            red = campaign.evaluate_itree_red_flags(
                itree, 0x20020002, {}, 50.0, max_oracle_errors=5
            )
            self.assertFalse(red.passed)
            self.assertFalse(red.checks["itree_oracle_invoked"])
            self.assertTrue(
                any("sum(not_compared_reasons) (0)" in r for r in red.failure_reasons),
                red.failure_reasons,
            )

            # Legacy summaries without `not_compared_reasons` keep the strict
            # `compared == opt_level_0_and_2_compiled` contract.
            legacy = make_healthy_itree_report(state_dir, not_compared_candidates=1)
            del legacy["not_compared_reasons"]
            red_legacy = campaign.evaluate_itree_red_flags(legacy, 0x20020002, {}, 50.0, 5)
            self.assertFalse(red_legacy.checks["itree_oracle_invoked"])

    def test_itree_kernel_confirmed_trace_bounds(self) -> None:
        """Subset kernel confirmation is honest; fewer than one per candidate is not."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            honest_subset = make_healthy_itree_report(state_dir, kernel_confirmed_traces=8)
            red = campaign.evaluate_itree_red_flags(honest_subset, 0x20020002, {}, 50.0)
            self.assertTrue(red.passed, red.failure_reasons)
            too_few = make_healthy_itree_report(state_dir, kernel_confirmed_traces=7)
            red_few = campaign.evaluate_itree_red_flags(too_few, 0x20020002, {}, 50.0)
            self.assertFalse(red_few.checks["itree_oracle_invoked"])
            too_many = make_healthy_itree_report(state_dir, kernel_confirmed_traces=17)
            red_many = campaign.evaluate_itree_red_flags(too_many, 0x20020002, {}, 50.0)
            self.assertFalse(red_many.checks["itree_oracle_invoked"])

    def test_invalid_itree_performed_summary_with_healthy_miri_reports_cleanly(self) -> None:
        """An invalid `performed` ITree summary must not crash report rendering."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            write_initial_ledger(state_dir, active_fingerprints=[])

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir)
                return {
                    "harness": "itree-difftest",
                    "oracle_comparison": "performed",
                    "total_candidates": 4,
                }

            junit_xml = state_dir / "reports" / "junit_results.xml"
            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = run_main(state_dir, "--junit-xml", str(junit_xml))

            self.assertEqual(rc, campaign.EXIT_HARNESS_FAILED)
            report_md = (state_dir / "reports" / "LATEST_REPORT.md").read_text(
                encoding="utf-8"
            )
            self.assertIn("Status: RED FLAG / HARNESS FAILED.", report_md)
            self.assertIn("| Mode | `seeded` | `harness-failed` |", report_md)
            self.assertIn("itree_invalid_summary", report_md)
            summary = json.loads(
                (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(summary["itree_oracle_comparison"], "failed")
            self.assertIn(
                "invalid_summary",
                summary["harness_diagnostics"]["itree-difftest"]["oracle_error_reason"],
            )
            ledger = read_ledger(state_dir)
            self.assertEqual(
                ledger["next_miri_seed"], f"0x{campaign.advance_seed(0x10010001):08x}"
            )
            self.assertEqual(ledger["next_itree_seed"], "0x20020002")
            junit_text = junit_xml.read_text(encoding="utf-8")
            self.assertIn('<failure message="harness failed">', junit_text)
            self.assertNotIn("red-flag vacuity check failed", junit_text)

    def test_legacy_remote_ledger_upgrade_on_partial_failure(self) -> None:
        """The real pre-2026-11-08 remote ledger upgrades cleanly when itree crashes."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            itree_legacy_fp = (
                "CallBoundaryOutliner:itree_outcome_mismatch:TraceReplayDiag.outcome_mismatch"
            )
            legacy = copy.deepcopy(LEGACY_REMOTE_LEDGER)
            legacy["active_fingerprints"].append(itree_legacy_fp)
            ledger_path = state_dir / "state" / "campaign_ledger.json"
            ledger_path.parent.mkdir(parents=True)
            ledger_path.write_text(json.dumps(legacy, indent=2) + "\n", encoding="utf-8")

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                if bin_name == "miri-difftest":
                    healthy_diag(bin_name)
                    # Root Cause D fixed both missed_ub fingerprints: 0 findings.
                    return make_healthy_miri_report(state_dir, seed="0x2b4f3af4")
                campaign.LAST_HARNESS_DIAGNOSTICS[bin_name] = {
                    "exit_code": 1,
                    "oracle_error_reason": "process_exit_1",
                    "stderr_tail": "ItreeDiffBatchConfirm.lean failed kernel confirmation",
                    "elapsed_s": 708.0,
                }
                return None

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = run_main(state_dir)

            self.assertEqual(rc, campaign.EXIT_HARNESS_FAILED)
            ledger = read_ledger(state_dir)
            today = campaign.utc_date_prefix()
            self.assertEqual(ledger["schema_version"], 1)
            self.assertEqual(ledger["total_campaigns_run"], 6)
            self.assertEqual(ledger["per_suite_runs"], {"miri": 1, "itree": 0})
            self.assertEqual(ledger["last_miri_seed"], "0x2b4f3af4")
            self.assertEqual(
                ledger["next_miri_seed"], f"0x{campaign.advance_seed(0x2b4f3af4):08x}"
            )
            self.assertEqual(ledger["total_miri_candidates_generated"], 2728)
            self.assertEqual(ledger["total_miri_candidates_evaluated"], 2708)
            # itree state is untouched.
            for key in (
                "next_itree_seed",
                "last_itree_seed",
                "last_itree_signature",
                "total_itree_candidates_generated",
                "total_itree_candidates_evaluated",
                "total_itree_traces_checked",
            ):
                self.assertEqual(ledger[key], legacy[key], key)
            self.assertEqual(ledger["last_oracle_comparison"], "miri_performed_itree_failed")
            # Both legacy Miri fingerprints resolve, dated by when they were last seen.
            for fp in LEGACY_REMOTE_LEDGER["active_fingerprints"]:
                self.assertNotIn(fp, ledger["active_fingerprints"])
                self.assertEqual(
                    ledger["resolved_history"][fp],
                    {
                        "first_seen_date": "2026-11-07",
                        "last_seen_date": "2026-11-07",
                        "campaigns_failing": 1,
                        "resolved_date": today,
                        "suite": "miri-difftest",
                    },
                )
            # The unhealthy suite's legacy fingerprint stays active, gets no
            # fabricated "seen today" history entry, and is not resolved.
            self.assertIn(itree_legacy_fp, ledger["active_fingerprints"])
            self.assertNotIn(itree_legacy_fp, ledger["fingerprint_history"])
            self.assertNotIn(itree_legacy_fp, ledger["resolved_history"])
            self.assertGreater(ledger["cumulative_distinct_obs_paths"], 0)

    def test_quarantined_observation_is_not_resolved(self) -> None:
        """A fingerprint still observed (but now quarantined) is never 'resolved'."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            fp = "BitValidityTransmuteMutator:false_positive_ub:MirDiffTag.ub:invalid_value_load"
            write_initial_ledger(state_dir, active_fingerprints=[fp])
            quarantine = state_dir / "quarantine.json"
            quarantine.write_text(json.dumps({"quarantined": [fp]}), encoding="utf-8")

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir, fingerprints=[fp])
                return make_healthy_itree_report(state_dir)

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = run_main(state_dir, "--quarantine-file", str(quarantine))

            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            ledger = read_ledger(state_dir)
            self.assertNotIn(fp, ledger["active_fingerprints"])
            self.assertIn(fp, ledger["quarantined_fingerprints"])
            self.assertNotIn(fp, ledger["resolved_history"])
            hist = ledger["fingerprint_history"][fp]
            self.assertEqual(hist["last_seen_date"], campaign.utc_date_prefix())
            self.assertEqual(hist["campaigns_failing"], 4)
            self.assertEqual(hist["first_seen_date"], "2026-04-06")

    def test_regressed_fingerprint_keeps_first_seen_date(self) -> None:
        """A resolved fingerprint that reappears continues its original history."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            fp = "RawPtrOffsetMutator:false_positive_ub:MirDiffTag.ub:out_of_bounds"
            write_initial_ledger(
                state_dir,
                active_fingerprints=[],
                fingerprint_history={},
                resolved_history={
                    fp: {
                        "first_seen_date": "2026-01-01",
                        "last_seen_date": "2026-02-01",
                        "campaigns_failing": 3,
                        "resolved_date": "2026-02-02",
                        "suite": "miri-difftest",
                    }
                },
            )

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir, fingerprints=[fp])
                return make_healthy_itree_report(state_dir)

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = run_main(state_dir)

            self.assertEqual(rc, campaign.EXIT_DIVERGENCE_DETECTED)
            ledger = read_ledger(state_dir)
            self.assertEqual(ledger["active_fingerprints"], [fp])
            self.assertNotIn(fp, ledger["resolved_history"])
            self.assertEqual(ledger["fingerprint_history"][fp]["first_seen_date"], "2026-01-01")
            self.assertEqual(ledger["fingerprint_history"][fp]["campaigns_failing"], 4)

    def test_miri_only_leaves_itree_state_untouched(self) -> None:
        """`--miri-only` neither ages nor resolves ITree fingerprints or counters."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            itree_fp = "CallBoundaryOutliner:itree_outcome_mismatch:TraceReplayDiag.outcome_mismatch"
            ledger_path = write_initial_ledger(
                state_dir,
                active_fingerprints=[itree_fp],
                fingerprint_history={
                    itree_fp: {
                        "suite": "itree-difftest",
                        "first_seen_date": "2026-04-08",
                        "last_seen_date": "2026-04-10",
                        "campaigns_failing": 2,
                    }
                },
            )
            before = json.loads(ledger_path.read_text(encoding="utf-8"))

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                self.assertEqual(bin_name, "miri-difftest")
                healthy_diag(bin_name)
                return make_healthy_miri_report(state_dir)

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = run_main(state_dir, "--miri-only")

            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            ledger = read_ledger(state_dir)
            self.assertEqual(ledger["per_suite_runs"], {"miri": 11, "itree": 10})
            self.assertEqual(ledger["next_itree_seed"], before["next_itree_seed"])
            self.assertEqual(ledger["active_fingerprints"], [itree_fp])
            self.assertEqual(
                ledger["fingerprint_history"][itree_fp],
                before["fingerprint_history"][itree_fp],
            )
            self.assertEqual(ledger["last_oracle_comparison"], "performed")
            report_md = (state_dir / "reports" / "LATEST_REPORT.md").read_text(
                encoding="utf-8"
            )
            self.assertIn("| Mode | `seeded` | skipped |", report_md)

    def test_obs_path_signatures_are_never_fabricated_for_live_summaries(self) -> None:
        """An empty live signature list stays empty; only absent keys are derived."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            write_initial_ledger(state_dir, active_fingerprints=[])
            ratchet_path = state_dir / "state" / "coverage_ratchet.json"

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir, obs_path_signatures=[])
                report = make_healthy_itree_report(state_dir)
                del report["obs_path_signatures"]
                return report

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = run_main(state_dir)

            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            ratchet = json.loads(ratchet_path.read_text(encoding="utf-8"))
            self.assertEqual(ratchet["per_suite_distinct_obs_paths"]["miri"], 0)
            itree_entries = {
                k: v for k, v in ratchet["observed_paths"].items() if v["suite"] == "itree"
            }
            self.assertTrue(itree_entries)
            self.assertTrue(all(v.get("derived") is True for v in itree_entries.values()))
            self.assertTrue(all(k.startswith("itree:derived:") for k in itree_entries))
            self.assertEqual(
                ratchet["cumulative_distinct_obs_paths"], len(ratchet["observed_paths"])
            )

    def test_corrupt_ratchet_values_do_not_crash_and_stay_monotonic(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            write_initial_ledger(
                state_dir, active_fingerprints=[], cumulative_distinct_obs_paths=50
            )
            ratchet_path = state_dir / "state" / "coverage_ratchet.json"
            ratchet_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "cumulative_distinct_obs_paths": "not-a-number",
                        "per_suite_distinct_obs_paths": {"miri": "bad", "itree": 7},
                        "observed_paths": {
                            "miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree": {
                                "suite": "miri",
                                "hit_count": "x",
                            },
                            "garbage": 5,
                        },
                    }
                ),
                encoding="utf-8",
            )

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir)
                return make_healthy_itree_report(state_dir)

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = run_main(state_dir)

            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            ratchet = json.loads(ratchet_path.read_text(encoding="utf-8"))
            sig = "miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree"
            self.assertEqual(ratchet["observed_paths"][sig]["hit_count"], 2)
            self.assertEqual(ratchet["per_suite_distinct_obs_paths"], {"miri": 2, "itree": 7})
            # The ledger floor (50) dominates the 4 observed paths.
            self.assertEqual(ratchet["cumulative_distinct_obs_paths"], 50)
            self.assertEqual(read_ledger(state_dir)["cumulative_distinct_obs_paths"], 50)

    def test_quarantined_fingerprint_full_lifecycle(self) -> None:
        """Quarantined fingerprints track history, pop from resolved on regression, and resolve when fixed."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            fp = "BitValidityTransmuteMutator:false_positive_ub:MirDiffTag.ub:invalid_value_load"
            write_initial_ledger(
                state_dir,
                active_fingerprints=[],
                fingerprint_history={},
                resolved_history={
                    fp: {
                        "first_seen_date": "2026-01-10",
                        "last_seen_date": "2026-01-12",
                        "campaigns_failing": 2,
                        "resolved_date": "2026-01-13",
                        "suite": "miri-difftest",
                    }
                },
            )
            quarantine = state_dir / "quarantine.json"
            quarantine.write_text(json.dumps({"quarantined": [fp]}), encoding="utf-8")

            observed_miri_fps = [fp]
            call_round = [0]

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                bonus = call_round[0]
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(
                        state_dir,
                        seed=harness_args[harness_args.index("--seed") + 1],
                        fingerprints=list(observed_miri_fps),
                        mutator_bonus=bonus,
                    )
                return make_healthy_itree_report(
                    state_dir,
                    seed=harness_args[harness_args.index("--seed") + 1],
                    mutator_bonus=bonus,
                )

            # Campaign 1: `fp` reappears while quarantined -> popped from `resolved_history`,
            # recorded in `fingerprint_history` with preserved `first_seen_date` and `campaigns_failing = 2`.
            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc1 = run_main(state_dir, "--quarantine-file", str(quarantine))
            self.assertEqual(rc1, campaign.EXIT_SUCCESS)
            ledger1 = read_ledger(state_dir)
            self.assertEqual(ledger1["active_fingerprints"], [])
            self.assertEqual(ledger1["quarantined_fingerprints"], [fp])
            self.assertNotIn(fp, ledger1["resolved_history"])
            self.assertEqual(ledger1["fingerprint_history"][fp]["first_seen_date"], "2026-01-10")
            self.assertEqual(ledger1["fingerprint_history"][fp]["campaigns_failing"], 2)

            # Campaign 2: `fp` is fixed (0 findings) while still listed in quarantine file ->
            # removed from `quarantined_fingerprints` and moved to `resolved_history`.
            observed_miri_fps.clear()
            call_round[0] = 1
            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc2 = run_main(state_dir, "--quarantine-file", str(quarantine))
            self.assertEqual(rc2, campaign.EXIT_SUCCESS)
            ledger2 = read_ledger(state_dir)
            self.assertEqual(ledger2["active_fingerprints"], [])
            self.assertEqual(ledger2["quarantined_fingerprints"], [])
            self.assertNotIn(fp, ledger2["fingerprint_history"])
            self.assertIn(fp, ledger2["resolved_history"])
            self.assertEqual(ledger2["resolved_history"][fp]["first_seen_date"], "2026-01-10")
            self.assertEqual(ledger2["resolved_history"][fp]["campaigns_failing"], 2)

    def test_itree_red_flags_enforce_candidate_trace_divergence_consistency_and_kc_floor(self) -> None:
        """`diverge_candidates` vs `diverge_traces` and `agree_candidates + diverge_traces` floor are enforced."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            repro_file = state_dir / "repro.rs"
            repro_file.write_text("fn main() {}\n", encoding="utf-8")
            # 1. diverge_candidates == 0 with diverge_traces > 0 is dishonest.
            inconsistent = make_healthy_itree_report(state_dir)
            inconsistent["agree_traces"] = 15
            inconsistent["diverge_traces"] = 1
            inconsistent["kernel_confirmed_divergences"] = 1
            inconsistent["diag_tag_counts"]["ok"] = 15
            inconsistent["diag_tag_counts"]["outcome_mismatch"] = 1
            inconsistent["findings"] = [
                {
                    "finding_id": "f0",
                    "diag_tag": "outcome_mismatch",
                    "kernel_confirmed": True,
                    "repro_path": str(repro_file),
                }
            ]
            red1 = campaign.evaluate_itree_red_flags(inconsistent, 0x20020002, {}, 50.0)
            self.assertFalse(red1.checks["itree_oracle_invoked"])

            # 2. With 1 diverging candidate (3 diverging traces) + 7 agreeing candidates,
            # Stage 2 must kernel-confirm at least 7 + 3 = 10 traces.
            div_report = make_healthy_itree_report(state_dir)
            div_report["agree_candidates"] = 7
            div_report["diverge_candidates"] = 1
            div_report["agree_traces"] = 13
            div_report["diverge_traces"] = 3
            div_report["kernel_confirmed_divergences"] = 3
            div_report["diag_tag_counts"]["ok"] = 13
            div_report["diag_tag_counts"]["outcome_mismatch"] = 3
            div_report["findings_count"] = 3
            div_report["findings"] = [
                {
                    "finding_id": f"f{i}",
                    "diag_tag": "outcome_mismatch",
                    "kernel_confirmed": True,
                    "repro_path": str(repro_file),
                }
                for i in range(3)
            ]

            div_report["kernel_confirmed_traces"] = 9
            red_low = campaign.evaluate_itree_red_flags(div_report, 0x20020002, {}, 50.0)
            self.assertFalse(red_low.checks["itree_oracle_invoked"])

            div_report["kernel_confirmed_traces"] = 10
            red_ok = campaign.evaluate_itree_red_flags(div_report, 0x20020002, {}, 50.0)
            self.assertTrue(red_ok.passed, red_ok.failure_reasons)

    def test_compile_only_preserves_live_history_and_strips_only_legacy_keys(self) -> None:
        """`--compile-only` strips only the legacy prototype keys, never live-oracle history.

        The capsule launcher uploads `state/` after every run, so stripping
        `fingerprint_history` / `resolved_history` / `last_*_signature` /
        `per_suite_runs` on a pass-through `--compile-only` run would erase the
        shared remote ledger's aging history and seed-sensitivity baselines.
        """
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            ledger_path = write_initial_ledger(
                state_dir,
                total_miri_candidates_evaluated=99,
                cumulative_distinct_obs_paths=7,
                last_miri_signature={"miri_verdicts": {"pass": 3}},
                quarantined_fingerprints=["PlaceProjectionWrapper:missed_ub:MirDiffTag.normalScalar"],
            )
            before = json.loads(ledger_path.read_text(encoding="utf-8"))

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                return {
                    "harness": bin_name,
                    "oracle_comparison": "not_performed",
                    "mode": "seeded",
                    "batches": 2,
                    "batch_size": 4,
                    "total_candidates": 8,
                    "compiled_candidates": 8,
                    "opt_level_0_and_2_compiled": 8,
                    "elapsed_ms": 4.0,
                }

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = run_main(state_dir, "--compile-only")
            self.assertEqual(rc, campaign.EXIT_NOT_EVALUATED)
            ledger = read_ledger(state_dir)
            for key in campaign.OBSOLETE_LEDGER_KEYS:
                self.assertNotIn(key, ledger, key)
            for key in (
                "schema_version",
                "per_suite_runs",
                "fingerprint_history",
                "resolved_history",
                "quarantined_fingerprints",
                "last_miri_seed",
                "last_miri_signature",
                "last_itree_seed",
            ):
                self.assertEqual(ledger[key], before[key], key)
            self.assertEqual(ledger["total_campaigns_run"], before["total_campaigns_run"] + 1)
            self.assertEqual(ledger["last_oracle_comparison"], "not_performed")
            self.assertFalse((state_dir / "state" / "coverage_ratchet.json").exists())

    def test_missing_ratchet_baseline_is_flagged_not_hidden(self) -> None:
        """A ledger floor without the prior ratchet set is surfaced, never passed off as cumulative."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            # The capsule launcher copies only `campaign_ledger.json` into a fresh
            # state directory, so the prior `coverage_ratchet.json` is absent.
            write_initial_ledger(
                state_dir, active_fingerprints=[], cumulative_distinct_obs_paths=120
            )

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir)
                return make_healthy_itree_report(state_dir)

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
                rc = run_main(state_dir)

            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            ratchet = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            self.assertIs(ratchet.get("baseline_missing"), True)
            self.assertEqual(len(ratchet["observed_paths"]), 4)
            self.assertEqual(ratchet["cumulative_distinct_obs_paths"], 120)
            self.assertEqual(read_ledger(state_dir)["cumulative_distinct_obs_paths"], 120)
            summary = json.loads(
                (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertIs(summary["coverage_ratchet_baseline_missing"], True)
            report_md = (state_dir / "reports" / "LATEST_REPORT.md").read_text(
                encoding="utf-8"
            )
            self.assertIn("Coverage ratchet warning", report_md)

            # A later run that does see the (partial) ratchet accumulates into it, but
            # keeps flagging the gap until the union catches up with the floor.
            def fake_run_harness_2(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(
                        state_dir,
                        obs_path_signatures=[
                            "miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree",
                            "miri:s03_new_path@M9:panic_vs_panic:agree",
                        ],
                        mutator_bonus=1,
                    )
                return make_healthy_itree_report(state_dir, mutator_bonus=1)

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness_2):
                rc2 = run_main(state_dir)
            self.assertEqual(rc2, campaign.EXIT_SUCCESS)
            ratchet2 = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            self.assertEqual(len(ratchet2["observed_paths"]), 5)
            self.assertIs(ratchet2.get("baseline_missing"), True)
            self.assertEqual(ratchet2["cumulative_distinct_obs_paths"], 120)

            # Once a subsequent run's union catches up with the recorded floor
            # (here floor = 6 and the run adds a 6th distinct path), `baseline_missing`
            # clears immediately on that catch-up run.
            ratchet2["cumulative_distinct_obs_paths"] = 6
            (state_dir / "state" / "coverage_ratchet.json").write_text(
                json.dumps(ratchet2), encoding="utf-8"
            )
            ledger2 = read_ledger(state_dir)
            ledger2["cumulative_distinct_obs_paths"] = 6
            (state_dir / "state" / "campaign_ledger.json").write_text(
                json.dumps(ledger2), encoding="utf-8"
            )

            def fake_run_harness_3(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(
                        state_dir,
                        obs_path_signatures=[
                            "miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree",
                            "miri:s04_catchup_path@M10:pass_vs_pass:agree",
                        ],
                        mutator_bonus=2,
                    )
                return make_healthy_itree_report(state_dir, mutator_bonus=2)

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness_3):
                rc3 = run_main(state_dir)
            self.assertEqual(rc3, campaign.EXIT_SUCCESS)
            ratchet3 = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            self.assertEqual(len(ratchet3["observed_paths"]), 6)
            self.assertEqual(ratchet3["cumulative_distinct_obs_paths"], 6)
            self.assertNotIn("baseline_missing", ratchet3)
            summary3 = json.loads(
                (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertIs(summary3["coverage_ratchet_baseline_missing"], False)
            report3 = (state_dir / "reports" / "LATEST_REPORT.md").read_text(
                encoding="utf-8"
            )
            self.assertNotIn("Coverage ratchet warning", report3)

            # Conversely, if `cumulative_distinct_obs_paths` is 0 in both files
            # while `per_suite_distinct_obs_paths` records a higher per-suite floor
            # than `observed_paths` contains, `baseline_missing` is still detected.
            ratchet3["cumulative_distinct_obs_paths"] = 0
            ratchet3["per_suite_distinct_obs_paths"] = {"miri": 4, "itree": 10}
            (state_dir / "state" / "coverage_ratchet.json").write_text(
                json.dumps(ratchet3), encoding="utf-8"
            )
            ledger3 = read_ledger(state_dir)
            ledger3["cumulative_distinct_obs_paths"] = 0
            (state_dir / "state" / "campaign_ledger.json").write_text(
                json.dumps(ledger3), encoding="utf-8"
            )

            def fake_run_harness_4(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir, mutator_bonus=3)
                return make_healthy_itree_report(state_dir, mutator_bonus=3)

            with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness_4):
                rc4 = run_main(state_dir)
            self.assertEqual(rc4, campaign.EXIT_SUCCESS)
            ratchet4 = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            self.assertEqual(ratchet4["cumulative_distinct_obs_paths"], 14)
            self.assertIs(ratchet4.get("baseline_missing"), True)

    def test_new_itree_reasons_count_as_oracle_errors(self) -> None:
        """Trace-collector, `-O0`/`-O2` mismatch, and Lean build drops are oracle errors."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            self.assertEqual(
                set(campaign.ITREE_ORACLE_ERROR_REASONS),
                set(campaign.VALID_ITREE_NOT_COMPARED_REASONS) - {"compile_failed"},
            )
            for reason in (
                "trace_collect_failed",
                "opt_level_trace_mismatch",
                "lean_build_failed",
            ):
                with self.subTest(reason=reason):
                    report = make_healthy_itree_report(state_dir, not_compared_candidates=1)
                    report["not_compared_reasons"]["lean_probe_failed"] = 0
                    report["not_compared_reasons"][reason] = 1
                    self.assertEqual(
                        campaign.validate_performed_itree_summary(report), (True, "ok")
                    )
                    red = campaign.evaluate_itree_red_flags(report, 0x20020002, {}, 50.0)
                    self.assertFalse(red.checks["itree_oracle_error_threshold"])
                    self.assertTrue(red.checks["itree_oracle_invoked"], red.failure_reasons)
                    self.assertTrue(
                        any(f"{reason}=1" in r for r in red.failure_reasons), red.failure_reasons
                    )
            # Summaries from older harness builds with an unknown reason key set are invalid.
            stale = make_healthy_itree_report(state_dir)
            del stale["not_compared_reasons"]["lean_build_failed"]
            self.assertFalse(campaign.validate_performed_itree_summary(stale)[0])

    def test_baseline_ratchet_recovery_from_remote_uri_and_local_env_var(self) -> None:
        """`--baseline-ratchet-uri` and `ANNEAL_BASELINE_RATCHET_URI` recover missing ratchets and union-merge monotonically."""
        baseline_payload = {
            "schema_version": 1,
            "updated_utc": "2026-10-01T00:00:00Z",
            "cumulative_distinct_obs_paths": 5,
            "per_suite_distinct_obs_paths": {"miri": 3, "itree": 2},
            "observed_paths": {
                "miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree": {
                    "suite": "miri",
                    "first_seen_utc": "2026-10-01T00:00:00Z",
                    "last_seen_utc": "2026-10-01T00:00:00Z",
                    "first_seen_seed": "0x00001111",
                    "last_seen_seed": "0x00001111",
                    "hit_count": 3,
                },
                "miri:s99_prior_only@M0:pass_vs_pass:agree": {
                    "suite": "miri",
                    "first_seen_utc": "2026-10-01T00:00:00Z",
                    "last_seen_utc": "2026-10-01T00:00:00Z",
                    "first_seen_seed": "0x00001111",
                    "last_seen_seed": "0x00001111",
                    "hit_count": 1,
                },
                "itree:it01_pure_return@IdentityMutator:0011223344556677:ok": {
                    "suite": "itree",
                    "first_seen_utc": "2026-10-01T00:00:00Z",
                    "last_seen_utc": "2026-10-01T00:00:00Z",
                    "first_seen_seed": "0x00002222",
                    "last_seen_seed": "0x00002222",
                    "hit_count": 2,
                },
                "itree:it99_prior_only@I0:aaaa:ok": {
                    "suite": "itree",
                    "first_seen_utc": "2026-10-01T00:00:00Z",
                    "last_seen_utc": "2026-10-01T00:00:00Z",
                    "first_seen_seed": "0x00002222",
                    "last_seen_seed": "0x00002222",
                    "hit_count": 1,
                },
            },
        }

        # 1. Recovery via mocked `/remote/...` `--baseline-ratchet-uri` when `--remote-uri ""`.
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            write_initial_ledger(
                state_dir, active_fingerprints=[], cumulative_distinct_obs_paths=5
            )
            remote_baseline_uri = (
                "/remote/teams/anneal-agent/difftest/state/coverage_ratchet.json"
            )
            remote_calls: list[list[str]] = []

            def fake_run_remote_sync(args: list[str]) -> subprocess.CompletedProcess[str]:
                remote_calls.append(list(args))
                if args[:2] == ["cp", "-f"] and args[2] == remote_baseline_uri:
                    Path(args[3]).write_text(
                        json.dumps(baseline_payload), encoding="utf-8"
                    )
                return subprocess.CompletedProcess(args, 0, "", "")

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir)
                return make_healthy_itree_report(state_dir)

            stderr_buf = io.StringIO()
            with mock.patch.object(
                campaign, "run_harness", side_effect=fake_run_harness
            ), mock.patch.object(
                campaign, "has_remote_sync", return_value=True
            ), mock.patch.object(
                campaign, "run_remote_sync", side_effect=fake_run_remote_sync
            ), mock.patch("sys.stderr", stderr_buf):
                rc = run_main(state_dir, "--baseline-ratchet-uri", remote_baseline_uri)

            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            self.assertIn("populated missing", stderr_buf.getvalue())
            self.assertIn(remote_baseline_uri, stderr_buf.getvalue())
            self.assertEqual(len(remote_calls), 1)
            ratchet = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            # 4 baseline paths + 1 new miri path (`s02_slice_get`) + 1 new itree path (`it02_single_ext_call`) = 6
            self.assertEqual(len(ratchet["observed_paths"]), 6)
            self.assertEqual(ratchet["per_suite_distinct_obs_paths"], {"miri": 3, "itree": 3})
            self.assertEqual(ratchet["cumulative_distinct_obs_paths"], 6)
            self.assertNotIn("baseline_missing", ratchet)
            overlap_miri = ratchet["observed_paths"][
                "miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree"
            ]
            self.assertEqual(overlap_miri["first_seen_utc"], "2026-10-01T00:00:00Z")
            self.assertEqual(overlap_miri["first_seen_seed"], "0x00001111")
            self.assertEqual(overlap_miri["last_seen_seed"], "0x10010001")
            self.assertEqual(overlap_miri["hit_count"], 4)
            prior_only = ratchet["observed_paths"]["miri:s99_prior_only@M0:pass_vs_pass:agree"]
            self.assertEqual(prior_only["hit_count"], 1)
            self.assertEqual(prior_only["last_seen_utc"], "2026-10-01T00:00:00Z")
            summary = json.loads(
                (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertIs(summary["coverage_ratchet_baseline_missing"], False)

            # Subsequent run where `state/coverage_ratchet.json` ALREADY exists must NOT
            # re-fetch or overwrite from `--baseline-ratchet-uri`.
            remote_calls.clear()
            stderr_buf_2 = io.StringIO()

            def fake_run_harness_next(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir, mutator_bonus=1)
                return make_healthy_itree_report(state_dir, mutator_bonus=1)

            with mock.patch.object(
                campaign, "run_harness", side_effect=fake_run_harness_next
            ), mock.patch.object(
                campaign, "has_remote_sync", return_value=True
            ), mock.patch.object(
                campaign, "run_remote_sync", side_effect=fake_run_remote_sync
            ), mock.patch("sys.stderr", stderr_buf_2):
                rc2 = run_main(state_dir, "--baseline-ratchet-uri", remote_baseline_uri)
            self.assertEqual(rc2, campaign.EXIT_SUCCESS)
            self.assertEqual(remote_calls, [])
            self.assertNotIn("populated missing", stderr_buf_2.getvalue())

        # 2. Recovery via `ANNEAL_BASELINE_RATCHET_URI` pointing to a local baseline JSON file.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            state_dir = tmp_path / "run_state"
            state_dir.mkdir()
            local_baseline = tmp_path / "seed_ratchet.json"
            local_baseline.write_text(json.dumps(baseline_payload), encoding="utf-8")
            write_initial_ledger(
                state_dir, active_fingerprints=[], cumulative_distinct_obs_paths=6
            )

            def fake_run_harness_local(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir)
                return make_healthy_itree_report(state_dir)

            stderr_local = io.StringIO()
            with mock.patch.dict(
                os.environ, {"ANNEAL_BASELINE_RATCHET_URI": f"  {local_baseline}  "}
            ), mock.patch.object(
                campaign, "run_harness", side_effect=fake_run_harness_local
            ), mock.patch("sys.stderr", stderr_local):
                rc_local = run_main(state_dir)

            self.assertEqual(rc_local, campaign.EXIT_SUCCESS)
            self.assertIn("populated missing", stderr_local.getvalue())
            ratchet_local = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            self.assertEqual(len(ratchet_local["observed_paths"]), 6)
            self.assertEqual(ratchet_local["cumulative_distinct_obs_paths"], 6)
            self.assertNotIn("baseline_missing", ratchet_local)

    def test_baseline_ratchet_uri_rejects_fuse_paths(self) -> None:
        """`/mnt/fuse/rw/...` passed via `--baseline-ratchet-uri` or env var fails with `EXIT_HARNESS_FAILED`."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            for bad_uri in (
                "/mnt/fuse/rw/teams/anneal-agent/difftest/state/coverage_ratchet.json",
                "/mnt/fuse/rw/../rw/teams/anneal-agent/ratchet.json",
                "/mnt/fuse/rw",
            ):
                with self.subTest(bad_uri=bad_uri):
                    stderr_buf = io.StringIO()
                    with mock.patch("sys.stderr", stderr_buf):
                        rc = run_main(state_dir, "--baseline-ratchet-uri", bad_uri)
                    self.assertEqual(rc, campaign.EXIT_HARNESS_FAILED)
                    self.assertIn("Refusing FUSE path", stderr_buf.getvalue())

            # Symlink resolving into `/mnt/fuse/rw/...` is also rejected.
            fuse_link = state_dir / "fuse_ratchet_link.json"
            fuse_link.symlink_to(
                "/mnt/fuse/rw/teams/anneal-agent/difftest/state/coverage_ratchet.json"
            )
            stderr_link = io.StringIO()
            with mock.patch("sys.stderr", stderr_link):
                rc_link = run_main(state_dir, "--baseline-ratchet-uri", str(fuse_link))
            self.assertEqual(rc_link, campaign.EXIT_HARNESS_FAILED)
            self.assertIn("Refusing FUSE path", stderr_link.getvalue())

    def test_baseline_ratchet_fetch_failure_and_corrupt_json_warn_and_preserve_missing_flag(
        self,
    ) -> None:
        """Failed `/remote/` fetch or missing/corrupt baseline logs a warning and keeps `baseline_missing: True`."""
        # 1. `/remote/...` fetch fails after leaving a partial corrupt file.
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            write_initial_ledger(
                state_dir, active_fingerprints=[], cumulative_distinct_obs_paths=120
            )
            remote_uri = "/remote/teams/anneal-agent/difftest/state/coverage_ratchet.json"

            def failing_remote_sync(args: list[str]) -> subprocess.CompletedProcess[str]:
                if args[:2] == ["cp", "-f"]:
                    Path(args[3]).write_text("{partial", encoding="utf-8")
                return subprocess.CompletedProcess(args, 1, "", "not_found: missing remote file")

            def fake_run_harness(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir)
                return make_healthy_itree_report(state_dir)

            stderr_buf = io.StringIO()
            with mock.patch.object(
                campaign, "run_harness", side_effect=fake_run_harness
            ), mock.patch.object(
                campaign, "has_remote_sync", return_value=True
            ), mock.patch.object(
                campaign, "run_remote_sync", side_effect=failing_remote_sync
            ), mock.patch("sys.stderr", stderr_buf):
                rc = run_main(state_dir, "--baseline-ratchet-uri", remote_uri)

            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            err_text = stderr_buf.getvalue()
            self.assertIn("warning: failed to fetch baseline coverage ratchet", err_text)
            self.assertNotIn("populated missing", err_text)
            ratchet = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            self.assertIs(ratchet.get("baseline_missing"), True)
            self.assertEqual(ratchet["cumulative_distinct_obs_paths"], 120)
            summary = json.loads(
                (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertIs(summary["coverage_ratchet_baseline_missing"], True)

        # 2. Local baseline missing, truncated JSON, or non-object JSON degrades cleanly.
        for label, content in (
            ("missing", None),
            ("malformed_json", "{corrupted_json"),
            ("non_dict_json", "[1, 2, 3]"),
        ):
            with self.subTest(case=label), tempfile.TemporaryDirectory() as tmp:
                tmp_path = Path(tmp)
                state_dir = tmp_path / "state_dir"
                state_dir.mkdir()
                write_initial_ledger(
                    state_dir, active_fingerprints=[], cumulative_distinct_obs_paths=80
                )
                baseline_file = tmp_path / f"{label}.json"
                if content is not None:
                    baseline_file.write_text(content, encoding="utf-8")

                def fake_run_harness_case(repo_root, bin_name, harness_args, json_path):
                    healthy_diag(bin_name)
                    if bin_name == "miri-difftest":
                        return make_healthy_miri_report(state_dir)
                    return make_healthy_itree_report(state_dir)

                stderr_case = io.StringIO()
                with mock.patch.object(
                    campaign, "run_harness", side_effect=fake_run_harness_case
                ), mock.patch("sys.stderr", stderr_case):
                    rc_case = run_main(
                        state_dir, "--baseline-ratchet-uri", str(baseline_file)
                    )
                self.assertEqual(rc_case, campaign.EXIT_SUCCESS)
                self.assertIn("warning:", stderr_case.getvalue())
                self.assertNotIn("populated missing", stderr_case.getvalue())
                ratchet_case = json.loads(
                    (state_dir / "state" / "coverage_ratchet.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.assertIs(ratchet_case.get("baseline_missing"), True)
                self.assertEqual(ratchet_case["cumulative_distinct_obs_paths"], 80)

        # 3. Direct `load_coverage_ratchet` on malformed / non-object ratchet logs warning & returns `{}`.
        with tempfile.TemporaryDirectory() as tmp:
            bad_ratchet = Path(tmp) / "bad_ratchet.json"
            bad_ratchet.write_text("{not valid json", encoding="utf-8")
            err_malformed = io.StringIO()
            with mock.patch("sys.stderr", err_malformed):
                self.assertEqual(campaign.load_coverage_ratchet(bad_ratchet), {})
            self.assertIn("warning: ignoring malformed", err_malformed.getvalue())

            bad_ratchet.write_text("[1, 2]", encoding="utf-8")
            err_list = io.StringIO()
            with mock.patch("sys.stderr", err_list):
                self.assertEqual(campaign.load_coverage_ratchet(bad_ratchet), {})
            self.assertIn("warning: ignoring non-object", err_list.getvalue())


class BaselineRatchetAdversarialTest(unittest.TestCase):
    """Regression tests for coverage-ratchet recovery issues found in adversarial pass A1."""

    @staticmethod
    def _fake_run_harness(state_dir: Path):
        def fake_run_harness(repo_root, bin_name, harness_args, json_path):
            healthy_diag(bin_name)
            if bin_name == "miri-difftest":
                return make_healthy_miri_report(state_dir)
            return make_healthy_itree_report(state_dir)

        return fake_run_harness

    @staticmethod
    def _prior_ratchet() -> dict:
        def entry(suite: str, seed: str, hits: int) -> dict:
            return {
                "suite": suite,
                "first_seen_utc": "2026-10-01T00:00:00Z",
                "last_seen_utc": "2026-10-01T00:00:00Z",
                "first_seen_seed": seed,
                "last_seen_seed": seed,
                "hit_count": hits,
            }

        return {
            "schema_version": 1,
            "updated_utc": "2026-10-01T00:00:00Z",
            "cumulative_distinct_obs_paths": 4,
            "per_suite_distinct_obs_paths": {"miri": 2, "itree": 2},
            "observed_paths": {
                "miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree": entry(
                    "miri", "0x00001111", 3
                ),
                "miri:s99_prior_only@M0:pass_vs_pass:agree": entry("miri", "0x00001111", 1),
                "itree:it01_pure_return@IdentityMutator:0011223344556677:ok": entry(
                    "itree", "0x00002222", 2
                ),
                "itree:it99_prior_only@I0:aaaa:ok": entry("itree", "0x00002222", 1),
            },
        }

    def test_failed_remote_state_fetch_keeps_existing_local_ledger_and_ratchet(self) -> None:
        """A transient `/remote/` read failure must not delete a reused state dir's state.

        Deleting the local ledger/ratchet resets seeds and counters, erases the
        floors that `baseline_missing` detection relies on, and lets
        `sync_state_to_remote` publish the reset state over the remote history.
        """
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            write_initial_ledger(
                state_dir, active_fingerprints=[], cumulative_distinct_obs_paths=4
            )
            ratchet_path = state_dir / "state" / "coverage_ratchet.json"
            prior = self._prior_ratchet()
            ratchet_path.write_text(json.dumps(prior), encoding="utf-8")
            remote_uri = "/remote/teams/anneal-agent/difftest"

            def flaky_remote_sync(args: list[str]) -> subprocess.CompletedProcess[str]:
                if args[:2] == ["cp", "-f"] and args[2].startswith(remote_uri):
                    # Transient read failure that leaves the destination untouched.
                    return subprocess.CompletedProcess(
                        args, 1, "", "UNAVAILABLE: deadline exceeded"
                    )
                return subprocess.CompletedProcess(args, 0, "", "")

            with mock.patch.object(
                campaign, "run_harness", side_effect=self._fake_run_harness(state_dir)
            ), mock.patch.object(
                campaign, "has_remote_sync", return_value=True
            ), mock.patch.object(
                campaign, "run_remote_sync", side_effect=flaky_remote_sync
            ), mock.patch("sys.stderr", io.StringIO()):
                rc = campaign.main(
                    [
                        "--profile",
                        "smoke",
                        "--state-dir",
                        str(state_dir),
                        "--remote-uri",
                        remote_uri,
                    ]
                )

            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            ledger = read_ledger(state_dir)
            # The reused local ledger (10 campaigns, next seed 0x10010001) is
            # extended rather than silently reset to a fresh ledger.
            self.assertEqual(ledger["total_campaigns_run"], 11)
            self.assertEqual(ledger["last_miri_seed"], "0x10010001")
            ratchet = json.loads(ratchet_path.read_text(encoding="utf-8"))
            for sig in prior["observed_paths"]:
                self.assertIn(sig, ratchet["observed_paths"])
            self.assertEqual(
                ratchet["observed_paths"][
                    "miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree"
                ]["hit_count"],
                4,
            )
            self.assertEqual(len(ratchet["observed_paths"]), 6)

    def test_unusable_configured_baseline_flags_baseline_missing_without_ledger_floor(
        self,
    ) -> None:
        """A configured baseline that exists but cannot be merged is surfaced honestly.

        With no ledger floor, a corrupt baseline file or a non-absent `/remote/`
        fetch error must still set `baseline_missing`: the run knows a prior
        cumulative set exists that it failed to merge, so its own union must not
        be passed off as the cumulative history.
        """
        for case in ("corrupt_local_baseline", "remote_fetch_unavailable"):
            with self.subTest(case=case), tempfile.TemporaryDirectory() as tmp:
                tmp_path = Path(tmp)
                state_dir = tmp_path / "state_dir"
                state_dir.mkdir()
                # Seeds match the mocked harness reports; no cumulative floor.
                write_initial_ledger(state_dir, active_fingerprints=[])
                stderr_buf = io.StringIO()
                with contextlib.ExitStack() as stack:
                    stack.enter_context(
                        mock.patch.object(
                            campaign,
                            "run_harness",
                            side_effect=self._fake_run_harness(state_dir),
                        )
                    )
                    stack.enter_context(mock.patch("sys.stderr", stderr_buf))
                    if case == "corrupt_local_baseline":
                        baseline = tmp_path / "coverage_ratchet.json"
                        baseline.write_text(
                            '{"schema_version": 1, "observed_paths": {', encoding="utf-8"
                        )
                        uri = str(baseline)
                    else:
                        uri = "/remote/teams/anneal-agent/difftest/state/coverage_ratchet.json"
                        stack.enter_context(
                            mock.patch.object(campaign, "has_remote_sync", return_value=True)
                        )
                        stack.enter_context(
                            mock.patch.object(
                                campaign,
                                "run_remote_sync",
                                return_value=subprocess.CompletedProcess(
                                    [], 1, "", "UNAVAILABLE: deadline exceeded"
                                ),
                            )
                        )
                    rc = run_main(state_dir, "--baseline-ratchet-uri", uri)

                self.assertEqual(rc, campaign.EXIT_SUCCESS)
                self.assertIn("warning:", stderr_buf.getvalue())
                ratchet = json.loads(
                    (state_dir / "state" / "coverage_ratchet.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.assertIs(ratchet.get("baseline_missing"), True, f"{case}: {ratchet}")
                summary = json.loads(
                    (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.assertIs(summary["coverage_ratchet_baseline_missing"], True)
                report_md = (state_dir / "reports" / "LATEST_REPORT.md").read_text(
                    encoding="utf-8"
                )
                self.assertIn("Coverage ratchet warning", report_md)

    def test_corrupt_local_ratchet_recovers_from_configured_baseline(self) -> None:
        """An unparseable local ratchet must not shadow a valid `--baseline-ratchet-uri`.

        Otherwise the corrupt file is overwritten with this run's partial union
        while the configured baseline's paths and floors are silently discarded.
        """
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            state_dir = tmp_path / "state_dir"
            state_dir.mkdir()
            write_initial_ledger(
                state_dir, active_fingerprints=[], cumulative_distinct_obs_paths=4
            )
            ratchet_path = state_dir / "state" / "coverage_ratchet.json"
            ratchet_path.write_text('{"schema_version": 1, "observed_pa', encoding="utf-8")
            baseline = tmp_path / "baseline_ratchet.json"
            prior = self._prior_ratchet()
            baseline.write_text(json.dumps(prior), encoding="utf-8")

            with mock.patch.object(
                campaign, "run_harness", side_effect=self._fake_run_harness(state_dir)
            ), mock.patch("sys.stderr", io.StringIO()):
                rc = run_main(state_dir, "--baseline-ratchet-uri", str(baseline))

            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            ratchet = json.loads(ratchet_path.read_text(encoding="utf-8"))
            for sig in prior["observed_paths"]:
                self.assertIn(sig, ratchet["observed_paths"])
            self.assertEqual(len(ratchet["observed_paths"]), 6)
            self.assertEqual(ratchet["per_suite_distinct_obs_paths"], {"miri": 3, "itree": 3})
            self.assertEqual(ratchet["cumulative_distinct_obs_paths"], 6)
            self.assertNotIn("baseline_missing", ratchet)

    def test_unmerged_baseline_persists_across_runs_until_recovered_and_merged(
        self,
    ) -> None:
        """A failed baseline fetch stays flagged across subsequent runs until recovered and union-merged."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            state_dir = tmp_path / "state_dir"
            state_dir.mkdir()
            write_initial_ledger(state_dir, active_fingerprints=[])
            remote_uri = "/remote/teams/anneal-agent/difftest/state/coverage_ratchet.json"
            prior = self._prior_ratchet()

            # Run 1: `--baseline-ratchet-uri` fails with transient `UNAVAILABLE` (no ledger floor).
            with mock.patch.object(
                campaign, "run_harness", side_effect=self._fake_run_harness(state_dir)
            ), mock.patch.object(
                campaign, "has_remote_sync", return_value=True
            ), mock.patch.object(
                campaign,
                "run_remote_sync",
                return_value=subprocess.CompletedProcess(
                    [], 1, "", "UNAVAILABLE: transient backend error"
                ),
            ), mock.patch("sys.stderr", io.StringIO()):
                rc1 = run_main(state_dir, "--baseline-ratchet-uri", remote_uri)
            self.assertEqual(rc1, campaign.EXIT_SUCCESS)
            r1 = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            self.assertIs(r1.get("baseline_missing"), True)

            # Run 2: Runs without `--baseline-ratchet-uri` -> still honestly flagged `baseline_missing`.
            def fake_run_harness_2(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir, mutator_bonus=1)
                return make_healthy_itree_report(state_dir, mutator_bonus=1)

            with mock.patch.object(
                campaign, "run_harness", side_effect=fake_run_harness_2
            ), mock.patch("sys.stderr", io.StringIO()):
                rc2 = run_main(state_dir)
            self.assertEqual(rc2, campaign.EXIT_SUCCESS)
            r2 = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            self.assertIs(r2.get("baseline_missing"), True)

            # Run 3: `--baseline-ratchet-uri` succeeds -> union-merges baseline + prior runs and clears flag.
            def ok_remote_sync(args: list[str]) -> subprocess.CompletedProcess[str]:
                if args[:2] == ["cp", "-f"] and args[2] == remote_uri:
                    Path(args[3]).write_text(json.dumps(prior), encoding="utf-8")
                return subprocess.CompletedProcess(args, 0, "", "")

            def fake_run_harness_3(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir, mutator_bonus=2)
                return make_healthy_itree_report(state_dir, mutator_bonus=2)

            with mock.patch.object(
                campaign, "run_harness", side_effect=fake_run_harness_3
            ), mock.patch.object(
                campaign, "has_remote_sync", return_value=True
            ), mock.patch.object(
                campaign, "run_remote_sync", side_effect=ok_remote_sync
            ), mock.patch("sys.stderr", io.StringIO()):
                rc3 = run_main(state_dir, "--baseline-ratchet-uri", remote_uri)
            self.assertEqual(rc3, campaign.EXIT_SUCCESS)
            r3 = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            self.assertEqual(len(r3["observed_paths"]), 6)
            self.assertNotIn("baseline_missing", r3)
            self.assertNotIn("baseline_unmerged", r3)


if __name__ == "__main__":
    unittest.main()
