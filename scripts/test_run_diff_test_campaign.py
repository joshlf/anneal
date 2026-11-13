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
import re
import subprocess
import sys
import tempfile
import tomllib
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

    def _run_twice_with_varied_reports(self, state_dir: Path, *extra: str) -> None:
        for run_idx in range(2):

            def fake_run_harness(repo_root, bin_name, harness_args, json_path, i=run_idx):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(state_dir, mutator_bonus=i)
                return make_healthy_itree_report(state_dir, mutator_bonus=i)

            with mock.patch.object(
                campaign, "run_harness", side_effect=fake_run_harness
            ), mock.patch("sys.stderr", io.StringIO()):
                rc = run_main(state_dir, *extra)
            self.assertEqual(rc, campaign.EXIT_SUCCESS)

    def test_repeated_baseline_merges_do_not_inflate_hit_counts(self) -> None:
        """Re-merging the same configured baseline must be idempotent.

        While `baseline_missing` stays set (here the ledger floor of 50 exceeds
        the union), every run re-fetches the baseline. Summing the baseline's
        `hit_count` into the local ratchet again on each run inflates counts for
        paths that were never re-observed.
        """
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            state_dir = tmp_path / "state_dir"
            state_dir.mkdir()
            write_initial_ledger(
                state_dir, active_fingerprints=[], cumulative_distinct_obs_paths=50
            )
            baseline = tmp_path / "baseline_ratchet.json"
            baseline.write_text(json.dumps(self._prior_ratchet()), encoding="utf-8")

            self._run_twice_with_varied_reports(
                state_dir, "--baseline-ratchet-uri", str(baseline)
            )

            ratchet = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            self.assertIs(ratchet.get("baseline_missing"), True)
            obs = ratchet["observed_paths"]
            # Baseline hits plus one per run that observed the path.
            self.assertEqual(
                obs["miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree"]["hit_count"], 5
            )
            self.assertEqual(
                obs["itree:it01_pure_return@IdentityMutator:0011223344556677:ok"]["hit_count"],
                4,
            )
            # Baseline-only paths were never re-observed.
            self.assertEqual(obs["miri:s99_prior_only@M0:pass_vs_pass:agree"]["hit_count"], 1)
            self.assertEqual(obs["itree:it99_prior_only@I0:aaaa:ok"]["hit_count"], 1)
            # Paths first seen by this campaign were observed exactly twice.
            self.assertEqual(
                obs["miri:s02_slice_get@BoundsCheckElimMutator:ub_vs_ub:agree"]["hit_count"], 2
            )
            self.assertEqual(
                obs["miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree"]["first_seen_seed"],
                "0x00001111",
            )

    def test_corrupt_local_ratchet_without_baseline_clears_after_catch_up(self) -> None:
        """With no configured baseline there is nothing left to merge.

        A corrupt local ratchet may be flagged when it is detected, but it must
        not pin `baseline_missing` forever: as for an absent ratchet
        (`test_missing_ratchet_baseline_is_flagged_not_hidden`), the flag clears
        once the union catches up with every recorded floor.
        """
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            write_initial_ledger(
                state_dir, active_fingerprints=[], cumulative_distinct_obs_paths=4
            )
            ratchet_path = state_dir / "state" / "coverage_ratchet.json"
            ratchet_path.write_text('{"schema_version": 1, "observed_pa', encoding="utf-8")

            with mock.patch.object(
                campaign, "run_harness", side_effect=self._fake_run_harness(state_dir)
            ), mock.patch("sys.stderr", io.StringIO()):
                rc1 = run_main(state_dir)
            self.assertEqual(rc1, campaign.EXIT_SUCCESS)

            def fake_run_harness_2(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                if bin_name == "miri-difftest":
                    return make_healthy_miri_report(
                        state_dir,
                        obs_path_signatures=[
                            "miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree",
                            "miri:s02_slice_get@BoundsCheckElimMutator:ub_vs_ub:agree",
                            "miri:s03_new_path@M9:panic_vs_panic:agree",
                        ],
                        mutator_bonus=1,
                    )
                return make_healthy_itree_report(
                    state_dir,
                    obs_path_signatures=[
                        "itree:it01_pure_return@IdentityMutator:0011223344556677:ok",
                        "itree:it02_single_ext_call@CallBoundaryOutliner:8899aabbccddeeff:ok",
                        "itree:it03_new_path@I9:ffffffffffffffff:ok",
                    ],
                    mutator_bonus=1,
                )

            with mock.patch.object(
                campaign, "run_harness", side_effect=fake_run_harness_2
            ), mock.patch("sys.stderr", io.StringIO()):
                rc2 = run_main(state_dir)
            self.assertEqual(rc2, campaign.EXIT_SUCCESS)
            ratchet2 = json.loads(ratchet_path.read_text(encoding="utf-8"))
            self.assertEqual(len(ratchet2["observed_paths"]), 6)
            self.assertEqual(ratchet2["cumulative_distinct_obs_paths"], 6)
            self.assertNotIn("baseline_missing", ratchet2)
            self.assertNotIn("baseline_unmerged", ratchet2)
            summary2 = json.loads(
                (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertIs(summary2["coverage_ratchet_baseline_missing"], False)

    def test_remote_status_errors_mentioning_not_found_are_not_absent(self) -> None:
        """Only file-absence errors classify a baseline as absent.

        RPC status errors (`UNAVAILABLE`, `DEADLINE_EXCEEDED`, `PERMISSION_DENIED`)
        whose message merely contains "not found" are fetch failures, so they
        must still force `baseline_missing` (cf. the launcher's
        `is_absent_error` tokens: `not_found`, `no files matched`, `no such file`).
        """
        for err in (
            "UNAVAILABLE: upstream host not found",
            "PERMISSION_DENIED: caller identity not found in access group",
        ):
            with self.subTest(err=err), tempfile.TemporaryDirectory() as tmp:
                state_dir = Path(tmp)
                write_initial_ledger(state_dir, active_fingerprints=[])
                with mock.patch.object(
                    campaign, "run_harness", side_effect=self._fake_run_harness(state_dir)
                ), mock.patch.object(
                    campaign, "has_remote_sync", return_value=True
                ), mock.patch.object(
                    campaign,
                    "run_remote_sync",
                    return_value=subprocess.CompletedProcess([], 1, "", err),
                ), mock.patch("sys.stderr", io.StringIO()):
                    rc = run_main(
                        state_dir,
                        "--baseline-ratchet-uri",
                        "/remote/teams/anneal-agent/difftest/state/coverage_ratchet.json",
                    )
                self.assertEqual(rc, campaign.EXIT_SUCCESS)
                ratchet = json.loads(
                    (state_dir / "state" / "coverage_ratchet.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.assertIs(ratchet.get("baseline_missing"), True, f"{err}: {ratchet}")

    def test_unreadable_local_baseline_directory_warns_without_crashing(self) -> None:
        """A baseline under an unsearchable directory degrades with a warning.

        `Path.exists()` / `is_file()` raise `PermissionError` there, which must
        not abort the campaign after the harnesses ran (losing the ledger and
        reports); an unreadable configured baseline is a failed recovery.
        """
        if hasattr(os, "geteuid") and os.geteuid() == 0:
            self.skipTest("permission bits are not enforced for root")
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            state_dir = tmp_path / "state_dir"
            state_dir.mkdir()
            write_initial_ledger(state_dir, active_fingerprints=[])
            locked_dir = tmp_path / "locked"
            locked_dir.mkdir()
            baseline = locked_dir / "coverage_ratchet.json"
            baseline.write_text(json.dumps(self._prior_ratchet()), encoding="utf-8")
            locked_dir.chmod(0)
            stderr_buf = io.StringIO()
            try:
                with mock.patch.object(
                    campaign, "run_harness", side_effect=self._fake_run_harness(state_dir)
                ), mock.patch("sys.stderr", stderr_buf):
                    rc = run_main(state_dir, "--baseline-ratchet-uri", str(baseline))
            finally:
                locked_dir.chmod(0o755)

            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            self.assertIn("warning:", stderr_buf.getvalue())
            ratchet = json.loads(
                (state_dir / "state" / "coverage_ratchet.json").read_text(encoding="utf-8")
            )
            self.assertIs(ratchet.get("baseline_missing"), True)
            self.assertTrue((state_dir / "reports" / "LATEST_REPORT.md").is_file())
            self.assertEqual(read_ledger(state_dir)["total_campaigns_run"], 11)

    def test_corrupt_numeric_values_in_baseline_degrade_without_crashing(self) -> None:
        """Corrupt numbers in a recovered baseline must not crash after the harness ran.

        `json.loads` raises a plain `ValueError` (not `JSONDecodeError`) for
        integer literals over 4300 digits, and `str.isdigit()` accepts strings
        such as "²" or 5000-digit runs that `int()` then rejects.
        """
        sig = "miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree"
        huge = "1" * 5000
        cases = {
            "huge_int_literal": (
                '{"schema_version": 1, "cumulative_distinct_obs_paths": '
                + huge
                + ', "observed_paths": {}}'
            ),
            "superscript_digit_strings": json.dumps(
                {
                    "schema_version": 1,
                    "cumulative_distinct_obs_paths": "\u00b2",
                    "per_suite_distinct_obs_paths": {"miri": "\u00b3", "itree": 1},
                    "observed_paths": {sig: {"suite": "miri", "hit_count": "\u00b2"}},
                }
            ),
            "huge_digit_string_hit_count": json.dumps(
                {
                    "schema_version": 1,
                    "observed_paths": {sig: {"suite": "miri", "hit_count": huge}},
                }
            ),
        }
        for label, text in cases.items():
            with self.subTest(case=label), tempfile.TemporaryDirectory() as tmp:
                tmp_path = Path(tmp)
                state_dir = tmp_path / "state_dir"
                state_dir.mkdir()
                write_initial_ledger(state_dir, active_fingerprints=[])
                baseline = tmp_path / "coverage_ratchet.json"
                baseline.write_text(text, encoding="utf-8")
                with mock.patch.object(
                    campaign, "run_harness", side_effect=self._fake_run_harness(state_dir)
                ), mock.patch("sys.stderr", io.StringIO()):
                    rc = run_main(state_dir, "--baseline-ratchet-uri", str(baseline))
                self.assertEqual(rc, campaign.EXIT_SUCCESS)
                ratchet = json.loads(
                    (state_dir / "state" / "coverage_ratchet.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.assertIn(sig, ratchet["observed_paths"])
                self.assertTrue((state_dir / "reports" / "LATEST_REPORT.md").is_file())
                if label == "huge_int_literal":
                    self.assertIs(ratchet.get("baseline_missing"), True)

    def test_boundary_4300_digit_ints_and_nan_in_baseline_do_not_crash_json_dumps(
        self,
    ) -> None:
        """4300-digit ints (`+ 1` -> 4301 digits) and `NaN` constants must not crash `json.dumps`."""
        sig = "miri:s01_checked_add@AddToSubMutator:pass_vs_pass:agree"
        nines_4300 = "9" * 4300
        cases = {
            "boundary_4300_nines_hit_count": (
                '{"schema_version": 1, "observed_paths": {"'
                + sig
                + '": {"suite": "miri", "hit_count": '
                + nines_4300
                + "}}}",
                False,
            ),
            "nan_constant": (
                '{"schema_version": 1, "cumulative_distinct_obs_paths": NaN, "observed_paths": {}}',
                True,
            ),
        }
        for label, (text, expect_missing) in cases.items():
            with self.subTest(case=label), tempfile.TemporaryDirectory() as tmp:
                tmp_path = Path(tmp)
                state_dir = tmp_path / "state_dir"
                state_dir.mkdir()
                write_initial_ledger(state_dir, active_fingerprints=[])
                baseline = tmp_path / "coverage_ratchet.json"
                baseline.write_text(text, encoding="utf-8")
                with mock.patch.object(
                    campaign, "run_harness", side_effect=self._fake_run_harness(state_dir)
                ), mock.patch("sys.stderr", io.StringIO()):
                    rc = run_main(state_dir, "--baseline-ratchet-uri", str(baseline))
                self.assertEqual(rc, campaign.EXIT_SUCCESS)
                ratchet = json.loads(
                    (state_dir / "state" / "coverage_ratchet.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.assertEqual(ratchet["observed_paths"][sig]["hit_count"], 2 if not expect_missing else 1)
                if expect_missing:
                    self.assertIs(ratchet.get("baseline_missing"), True)
                else:
                    self.assertNotIn("baseline_missing", ratchet)

    def test_non_absent_remote_state_read_failure_skips_uploading_state_subdir(
        self,
    ) -> None:
        """When initial `/remote/` state pull fails with a non-absent error, `state/` is not overwritten remotely."""
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            remote_uri = "/remote/teams/anneal-agent/difftest"
            remote_calls: list[list[str]] = []

            def flaky_remote_sync(args: list[str]) -> subprocess.CompletedProcess[str]:
                remote_calls.append(list(args))
                if args[:2] == ["cp", "-f"] and args[2].startswith(f"{remote_uri}/state/"):
                    return subprocess.CompletedProcess(
                        args, 1, "", "UNAVAILABLE: transient backend error"
                    )
                return subprocess.CompletedProcess(args, 0, "", "")

            stderr_buf = io.StringIO()
            with mock.patch.object(
                campaign, "run_harness", side_effect=self._fake_run_harness(state_dir)
            ), mock.patch.object(
                campaign, "has_remote_sync", return_value=True
            ), mock.patch.object(
                campaign, "run_remote_sync", side_effect=flaky_remote_sync
            ), mock.patch("sys.stderr", stderr_buf):
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
            self.assertIn("skipping upload of state/", stderr_buf.getvalue())
            upload_dests = [
                c[3]
                for c in remote_calls
                if c[:2] == ["cp", "-f"] and c[3].startswith(remote_uri)
            ]
            self.assertTrue(
                any(d.endswith("/reports/LATEST_REPORT.md") for d in upload_dests),
                upload_dests,
            )
            self.assertFalse(
                any("/state/" in d for d in upload_dests),
                f"state/ must not be uploaded after failed remote read: {upload_dests}",
            )

    def test_successful_merge_of_flagged_baseline_clears_unmerged_marker(self) -> None:
        """`baseline_unmerged` tracks this ratchet's configured baseline, not the baseline's own.

        A baseline snapshot that itself carries `baseline_unmerged` (e.g. a
        backup of the shared ratchet taken after one transient failure) must not
        re-set the marker on every successful merge, or the marker can never
        clear. The baseline's floors still govern `baseline_missing`.
        """
        for label, floor in (("floors_met", 4), ("floors_unmet", 50)):
            with self.subTest(case=label), tempfile.TemporaryDirectory() as tmp:
                tmp_path = Path(tmp)
                state_dir = tmp_path / "state_dir"
                state_dir.mkdir()
                write_initial_ledger(state_dir, active_fingerprints=[])
                flagged = self._prior_ratchet()
                flagged["cumulative_distinct_obs_paths"] = floor
                flagged["baseline_missing"] = True
                flagged["baseline_unmerged"] = True
                baseline = tmp_path / "baseline_ratchet.json"
                baseline.write_text(json.dumps(flagged), encoding="utf-8")

                self._run_twice_with_varied_reports(
                    state_dir, "--baseline-ratchet-uri", str(baseline)
                )

                ratchet = json.loads(
                    (state_dir / "state" / "coverage_ratchet.json").read_text(
                        encoding="utf-8"
                    )
                )
                self.assertEqual(len(ratchet["observed_paths"]), 6)
                self.assertNotIn("baseline_unmerged", ratchet)
                if floor > 6:
                    self.assertIs(ratchet.get("baseline_missing"), True)
                    self.assertEqual(ratchet["cumulative_distinct_obs_paths"], floor)
                else:
                    self.assertNotIn("baseline_missing", ratchet)

    def test_unmerged_marker_clears_once_configured_baseline_is_absent(self) -> None:
        """Nothing is left to merge once the configured baseline is genuinely absent.

        After a transient `UNAVAILABLE` failure sets `baseline_unmerged`, a
        later `not_found` for the same URI (absent, as in the launcher's
        `is_absent_error`) must drop the marker instead of pinning
        `baseline_missing` forever; floors keep governing the flag.
        """
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            write_initial_ledger(state_dir, active_fingerprints=[])
            uri = "/remote/teams/anneal-agent/difftest/state/coverage_ratchet.json"
            responses = [
                subprocess.CompletedProcess([], 1, "", "UNAVAILABLE: transient backend error"),
                subprocess.CompletedProcess(
                    [], 1, "", f"not_found: no such file or directory: {uri}"
                ),
            ]
            for run_idx, response in enumerate(responses):

                def fake_run_harness(repo_root, bin_name, harness_args, json_path, i=run_idx):
                    healthy_diag(bin_name)
                    if bin_name == "miri-difftest":
                        return make_healthy_miri_report(state_dir, mutator_bonus=i)
                    return make_healthy_itree_report(state_dir, mutator_bonus=i)

                with mock.patch.object(
                    campaign, "run_harness", side_effect=fake_run_harness
                ), mock.patch.object(
                    campaign, "has_remote_sync", return_value=True
                ), mock.patch.object(
                    campaign, "run_remote_sync", return_value=response
                ), mock.patch("sys.stderr", io.StringIO()):
                    rc = run_main(state_dir, "--baseline-ratchet-uri", uri)
                self.assertEqual(rc, campaign.EXIT_SUCCESS)
                ratchet = json.loads(
                    (state_dir / "state" / "coverage_ratchet.json").read_text(
                        encoding="utf-8"
                    )
                )
                if run_idx == 0:
                    self.assertIs(ratchet.get("baseline_missing"), True)

            self.assertNotIn("baseline_unmerged", ratchet)
            self.assertNotIn("baseline_missing", ratchet)



# ---------------------------------------------------------------------------
# Episode 2 gates: semantic-mutant self-check, stale quarantine / known-bug
# ratchet, `error` vs. `unsupported` boundary, and per-item verdict audit.
# ---------------------------------------------------------------------------

REPO_ROOT = SCRIPT_DIR.parent
MIRI_EVAL_RS = REPO_ROOT / "crates" / "anneal-difftest" / "src" / "miri_eval.rs"
LIVE_MANIFEST = REPO_ROOT / "tests" / "miri-diff" / "manifest.toml"


def _make_valid_miri_summary() -> dict[str, object]:
    return {
        "harness": "miri-difftest",
        "oracle_comparison": "performed",
        "mode": "seeded",
        "seed": "0x5eed0001",
        "batches": 1,
        "batch_size": 8,
        "total_candidates": 8,
        "compiled_candidates": 8,
        "compile_failed_candidates": 0,
        "compared_candidates": 7,
        "agree_count": 7,
        "diverge_count": 0,
        "not_compared_count": 1,
        "kernel_confirmed_divergences": 0,
        "miri_verdicts": {"pass": 6, "panic": 1, "ub": 1, "error": 0},
        "anneal_outcomes": {
            "pass": 5,
            "panic": 1,
            "ub": 1,
            "unsupported": 1,
            "out_of_fuel": 0,
            "external_call": 0,
            "error": 0,
        },
        "divergence_classes": {
            "wrong_value": 0,
            "false_positive_ub": 0,
            "missed_ub": 0,
            "ub_location_mismatch": 0,
            "panic_vs_return": 0,
            "return_vs_panic": 0,
            "panic_site_mismatch": 0,
        },
        "not_compared_reasons": {
            "compile_failed": 0,
            "capture_failed": 0,
            "miri_oracle_error": 0,
            "unsupported": 1,
            "out_of_fuel": 0,
            "external_call": 0,
        },
        "unmodeled_external_calls": {},
        "mutator_applications": {"ArithmeticCastMutator": 8},
        "findings": [],
        "elapsed_ms": 250.0,
    }


def _with_consistent_item_outcomes(
    summary: dict[str, object], direct_call: str = "unsupported"
) -> dict[str, object]:
    """Attaches `item_outcomes` (real `summary_tag` formats, including the
    `file:l:c: l:c` span rendering) consistent with `_make_valid_miri_summary`'s counts:
    5 agreeing passes, 1 agreeing panic, 1 agreeing UB, and 1 not-compared item whose
    Anneal outcome is `direct_call` (`"unsupported"`, `"external_call"`, or `"agree"`)."""
    items: dict[str, dict[str, str]] = {
        f"pass_item_{i}": {
            "verdict": "agree",
            "miri_outcome": f"pass:scalar:{i}:4",
            "anneal_outcome": f"pass:scalar:{i}:4",
            "anneal_lean_tag": f"(MirDiffTag.normalScalar {i} 4)",
        }
        for i in range(5)
    }
    items["panic_item"] = {
        "verdict": "agree",
        "miri_outcome": "panic@/tmp/anneal_miri_eval_seeded/src/lib.rs:30:7",
        "anneal_outcome": "panic@src/lib.rs:30:5: 30:12",
        "anneal_lean_tag": "MirDiffTag.panic",
    }
    items["ub_item"] = {
        "verdict": "agree",
        "miri_outcome": "ub@src/lib.rs:41:14",
        "anneal_outcome": "ub@src/lib.rs:41:9: 41:20",
        "anneal_lean_tag": "MirDiffTag.ub",
    }
    if direct_call == "unsupported":
        items["pass_direct_fn_call"] = {
            "verdict": "not_compared",
            "miri_outcome": "pass:scalar:42:4",
            "anneal_outcome": "unsupported@src/lib.rs:50:5: 50:20",
            "anneal_lean_tag": "MirDiffTag.unsupported",
        }
    elif direct_call == "external_call":
        items["pass_direct_fn_call"] = {
            "verdict": "not_compared",
            "miri_outcome": "pass:scalar:42:4",
            "anneal_outcome": "externalCall:miri_diff_corpus::helper_add_ten",
            "anneal_lean_tag": '(MirDiffTag.externalCall "miri_diff_corpus::helper_add_ten")',
        }
        summary["anneal_outcomes"]["unsupported"] = 0  # type: ignore[index]
        summary["anneal_outcomes"]["external_call"] = 1  # type: ignore[index]
        summary["not_compared_reasons"]["unsupported"] = 0  # type: ignore[index]
        summary["not_compared_reasons"]["external_call"] = 1  # type: ignore[index]
    else:
        items["pass_direct_fn_call"] = {
            "verdict": "agree",
            "miri_outcome": "pass:scalar:42:4",
            "anneal_outcome": "pass:scalar:42:4",
            "anneal_lean_tag": "(MirDiffTag.normalScalar 42 4)",
        }
        summary["anneal_outcomes"]["unsupported"] = 0  # type: ignore[index]
        summary["anneal_outcomes"]["pass"] = 6  # type: ignore[index]
        summary["not_compared_reasons"]["unsupported"] = 0  # type: ignore[index]
        summary["not_compared_count"] = 0
        summary["compared_candidates"] = 8
        summary["agree_count"] = 8
    summary["item_outcomes"] = items
    return summary


def _with_reconciled_panic_macro_item(summary: dict[str, object]) -> dict[str, object]:
    """Turns `panic_item` into the identity shape of `panic_explicit_macro`: Miri
    reports the `panic!` call site in the staged `src/lib.rs` while Anneal's panic
    span lies in `library/core/src/panic.rs`, so the strict comparator says
    `panic_site_mismatch` and the harness agrees only through the panic-site
    reconciliation that `reconciled_panic_sites` records."""
    miri_pos = "src/lib.rs:12:5"
    anneal_span = "/rustc/0123456789abcdef/library/core/src/panic.rs:57:9: 57:51"
    summary["item_outcomes"]["panic_item"] = {  # type: ignore[index]
        "verdict": "agree",
        "miri_outcome": f"panic@{miri_pos}",
        "anneal_outcome": f"panic@{anneal_span}",
        "anneal_lean_tag": "MirDiffTag.panic",
    }
    summary["reconciled_panic_sites_count"] = 1
    summary["reconciled_panic_sites"] = [
        {
            "fn_name": "panic_item",
            "seed_name": "panic_item",
            "batch_miri_pos": miri_pos,
            "anneal_span": anneal_span,
            "anneal_panic_frame": "miri_diff_corpus::panic_item",
            "anneal_panic_message": "explicit panic in corpus",
            "kernel_confirmed": True,
        }
    ]
    return summary


def _live_manifest_known_bug_names() -> list[str]:
    data = tomllib.loads(LIVE_MANIFEST.read_text(encoding="utf-8"))
    return [
        t.get("name")
        for t in data.get("tests", [])
        if isinstance(t, dict) and "known_anneal_bug" in t
    ]


def _rust_const_body(name: str) -> str:
    """Returns the body of `const <name>: ... = [ ... ];` in `miri_eval.rs`."""
    src = MIRI_EVAL_RS.read_text(encoding="utf-8")
    start = src.index(f"const {name}:")
    end = src.index("\n    ];", start)
    return src[start:end]


def _quiet_main(argv: list[str]) -> int:
    with mock.patch("sys.stdout", io.StringIO()), mock.patch("sys.stderr", io.StringIO()):
        return campaign.main(argv)


def _read_summary(state_dir: Path) -> dict:
    return json.loads(
        (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(encoding="utf-8")
    )


class StaleRatchetGateTest(unittest.TestCase):
    def test_real_manifest_and_valid_quarantine_pass(self) -> None:
        known_bugs = _live_manifest_known_bug_names()
        with tempfile.TemporaryDirectory() as tmp:
            q_file = Path(tmp) / "quarantine.toml"
            q_file.write_text(
                '[[quarantined]]\n'
                'fingerprint = "RawPtrOffsetMutator:ub_location_mismatch:MirDiffTag.ub"\n'
                'expires = "2027-01-01"\n'
                'reason = "tracked pointer offset span mismatch"\n',
                encoding="utf-8",
            )
            for resolved_history in ({}, []):
                with self.subTest(resolved_history=type(resolved_history).__name__):
                    audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                        quarantine_file=q_file,
                        manifest_path=LIVE_MANIFEST,
                        ledger={"resolved_history": resolved_history},
                        evaluated_fingerprints=[
                            "RawPtrOffsetMutator:ub_location_mismatch:MirDiffTag.ub"
                        ],
                        reference_date="2026-11-09",
                    )
                    self.assertTrue(audit["passed"], audit)
                    self.assertEqual(audit["stale_entries"], [])
                    self.assertEqual(audit["checked_quarantine_count"], 1)
                    # Dynamic: whatever `known_anneal_bug` entries the live manifest has
                    # (0 after the last one was retired), never a hard-coded count.
                    self.assertEqual(audit["checked_known_bug_count"], len(known_bugs))

    def test_expired_malformed_resolved_and_unobserved_quarantine_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q_file = Path(tmp) / "quarantine.toml"
            q_file.write_text(
                '[[quarantined]]\n'
                'fingerprint = "ArithmeticCastMutator:wrong_value:MirDiffTag.normalScalar"\n'
                'expires = "2026-01-15"\n'
                'reason = "expired"\n'
                '[[quarantined]]\n'
                'fingerprint = "bad_no_colon"\n'
                '[[quarantined]]\n'
                'fingerprint = "bad no colon"\n'
                '[[quarantined]]\n'
                'fingerprint = "PlaceProjectionWrapper:missed_ub:MirDiffTag.normalScalar"\n'
                'expires = "2027-06-01"\n'
                'reason = "resolved since"\n',
                encoding="utf-8",
            )
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file,
                ledger={
                    "resolved_history": [
                        "PlaceProjectionWrapper:missed_ub:MirDiffTag.normalScalar"
                    ],
                    "active_fingerprints": [],
                },
                evaluated_fingerprints=[],
                reference_date="2026-11-09",
            )
            self.assertFalse(audit["passed"])
            reasons = " | ".join(e["reason"] for e in audit["stale_quarantine_entries"])
            self.assertIn("expired_quarantine_entry", reasons)
            self.assertIn("malformed_or_missing_fingerprint", reasons)
            self.assertIn("already_resolved_in_ledger", reasons)
            self.assertIn("unobserved_quarantine_entry", reasons)

    def test_manifest_known_bug_missing_metadata_or_now_passing_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            m_file = Path(tmp) / "manifest.toml"
            m_file.write_text(
                '[[tests]]\n'
                'name = "bug_missing_reason"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                '\n'
                '[[tests]]\n'
                'name = "bug_fixed_now_agrees"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'summary = "previously raised false positive UB"\n'
                '\n'
                '[[tests]]\n'
                'name = "bug_tag_drifted"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'reason = "previously raised UB"\n',
                encoding="utf-8",
            )
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_file,
                manifest_eval_results={
                    "bug_fixed_now_agrees": {"verdict": "Agree"},
                    "bug_tag_drifted": {
                        "verdict": "Diverge",
                        "observed_anneal_tag": "MirDiffTag.panic",
                    },
                },
                reference_date="2026-11-09",
            )
            self.assertFalse(audit["passed"])
            reasons = " | ".join(e["reason"] for e in audit["stale_known_anneal_bugs"])
            self.assertIn("missing_known_anneal_bug_metadata", reasons)
            self.assertIn("stale_known_anneal_bug_now_passes", reasons)
            self.assertIn("stale_known_anneal_bug_tag_mismatch", reasons)


class KnownAnnealBugCountTest(unittest.TestCase):
    """The manifest `known_anneal_bug` audit handles any number of entries (the live
    manifest has none after `panic_explicit_macro` was retired)."""

    @staticmethod
    def _manifest(tmp: str, *bugs: tuple[str, str]) -> Path:
        text = "schema_version = 1\n\n[[tests]]\nname = \"plain_test\"\nmiri_verdict = \"pass:unit\"\n"
        for name, tag in bugs:
            text += (
                f'\n[[tests]]\nname = "{name}"\n'
                f'[tests.known_anneal_bug]\nobserved_anneal_tag = "{tag}"\n'
                f'summary = "open bug {name}"\n'
            )
        path = Path(tmp) / "manifest.toml"
        path.write_text(text, encoding="utf-8")
        return path

    def test_live_manifest_known_bug_count_is_dynamic(self) -> None:
        names = _live_manifest_known_bug_names()
        audit = campaign.verify_no_stale_quarantine_or_known_bugs(manifest_path=LIVE_MANIFEST)
        self.assertEqual(audit["checked_known_bug_count"], len(names))
        self.assertEqual(audit["stale_known_anneal_bugs"], [])
        self.assertTrue(audit["passed"], audit)

    def test_zero_known_bugs_pass_even_when_every_test_agrees(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            m_file = self._manifest(tmp)
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_file,
                manifest_eval_results={"plain_test": {"verdict": "agree"}},
            )
            self.assertTrue(audit["passed"], audit)
            self.assertEqual(audit["checked_known_bug_count"], 0)

    def test_single_active_known_bug_that_still_reproduces_passes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            m_file = self._manifest(tmp, ("open_ub", "MirDiffTag.ub"))
            for ev in (
                {"verdict": "diverge", "anneal_outcome": "ub@src/lib.rs:3:5: 3:9", "anneal_lean_tag": "MirDiffTag.ub"},
                "MirDiffTag.ub",
            ):
                with self.subTest(ev=ev):
                    audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                        manifest_path=m_file, manifest_eval_results={"open_ub": ev}
                    )
                    self.assertTrue(audit["passed"], audit)
                    self.assertEqual(audit["checked_known_bug_count"], 1)
            # Not evaluated by this run: never assumed to agree.
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_file, manifest_eval_results={"other": {"verdict": "agree"}}
            )
            self.assertTrue(audit["passed"], audit)

    def test_multiple_known_bugs_flag_exactly_the_stale_ones(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            m_file = self._manifest(
                tmp,
                ("still_open", "MirDiffTag.ub"),
                ("now_agrees", "MirDiffTag.ub"),
                ("tag_drifted", "externalCall:core::fmt::Arguments::<'a>::from_str"),
                ("errored", "MirDiffTag.ub"),
                ("unevaluated", "MirDiffTag.ub"),
            )
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_file,
                manifest_eval_results={
                    "still_open": {"verdict": "diverge", "anneal_outcome": "ub@src/lib.rs:4:1: 4:9", "anneal_lean_tag": "MirDiffTag.ub"},
                    "now_agrees": {"verdict": "agree", "anneal_outcome": "pass:unit", "anneal_lean_tag": "MirDiffTag.normalUnit"},
                    "tag_drifted": {"verdict": "diverge", "anneal_outcome": "pass:unit", "anneal_lean_tag": "MirDiffTag.normalUnit"},
                    "errored": {"verdict": "not_compared", "miri_outcome": "pass:unit", "anneal_outcome": "capture_error:lean crashed", "anneal_lean_tag": "none"},
                },
            )
            self.assertFalse(audit["passed"])
            self.assertEqual(audit["checked_known_bug_count"], 5)
            by_entry = {e["entry"]: e["reason"] for e in audit["stale_known_anneal_bugs"]}
            self.assertEqual(sorted(by_entry), ["errored", "now_agrees", "tag_drifted"])
            self.assertTrue(by_entry["now_agrees"].startswith("stale_known_anneal_bug_now_passes"))
            self.assertTrue(by_entry["tag_drifted"].startswith("stale_known_anneal_bug_tag_mismatch"))
            self.assertTrue(by_entry["errored"].startswith("stale_known_anneal_bug_unconfirmed"))

    def test_malformed_manifests_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            cases = {
                "missing_name.toml": (
                    '[[tests]]\n[tests.known_anneal_bug]\nobserved_anneal_tag = "MirDiffTag.ub"\nsummary = "x"\n',
                    "missing_test_name_on_known_anneal_bug",
                ),
                "not_a_table.toml": (
                    '[[tests]]\nname = "t"\nknown_anneal_bug = "open"\n',
                    "malformed_known_anneal_bug",
                ),
                "no_metadata.toml": (
                    '[[tests]]\nname = "t"\n[tests.known_anneal_bug]\nstatus = "open_bug"\n',
                    "missing_known_anneal_bug_metadata",
                ),
                "tests_not_array.toml": ('tests = "nope"\n', "malformed_manifest_toml"),
                "bad_syntax.toml": ("[[tests]\nname=\n", "malformed_manifest_toml"),
            }
            for name, (text, reason) in cases.items():
                with self.subTest(manifest=name):
                    path = tmp_path / name
                    path.write_text(text, encoding="utf-8")
                    audit = campaign.verify_no_stale_quarantine_or_known_bugs(manifest_path=path)
                    self.assertFalse(audit["passed"])
                    self.assertIn(reason, " | ".join(e["reason"] for e in audit["stale_entries"]))
            missing = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=tmp_path / "absent.toml"
            )
            self.assertFalse(missing["passed"])
            self.assertIn("manifest_file_missing", missing["stale_entries"][0]["reason"])


class SemanticMutantSelfCheckTest(unittest.TestCase):
    def test_default_5_mutants_all_killed(self) -> None:
        mutant_ids = [m["id"] for m in campaign.SEEDED_SEMANTIC_MUTANTS]
        self.assertEqual(
            mutant_ids,
            [
                "bool_valid_range",
                "storage_dead_tag",
                "provenance_frag",
                "div_by_zero",
                "wide_shift",
            ],
        )
        res = campaign.run_semantic_mutant_self_check()
        self.assertTrue(res["passed"], res)
        self.assertEqual(res["total_mutants"], 5)
        self.assertEqual(res["killed_count"], 5)
        self.assertEqual(len(res["killed_mutants"]), 5)
        self.assertEqual(res["survived_mutants"], [])
        self.assertEqual(res["exit_code"], campaign.EXIT_SUCCESS)

    def test_surviving_mutant_fails_closed(self) -> None:
        def surviving_wide_shift_eval(mutant: dict[str, object]) -> dict[str, object]:
            if mutant["id"] == "wide_shift":
                return {"verdict": "Agree"}
            return {
                "verdict": "Diverge",
                "divergence_class": tuple(mutant["expected_kill_classes"])[0],
            }

        res = campaign.run_semantic_mutant_self_check(evaluator=surviving_wide_shift_eval)
        self.assertFalse(res["passed"])
        self.assertEqual(res["killed_count"], 4)
        self.assertEqual(res["survived_mutants"], ["wide_shift"])
        self.assertEqual(res["exit_code"], campaign.EXIT_HARNESS_FAILED)

    def test_unexpected_kill_class_fails_closed(self) -> None:
        def wrong_class_eval(mutant: dict[str, object]) -> dict[str, object]:
            if mutant["id"] == "bool_valid_range":
                return {"killed": True, "kill_class": "panic_site_mismatch"}
            return {
                "killed": True,
                "kill_class": tuple(mutant["expected_kill_classes"])[0],
            }

        res = campaign.run_semantic_mutant_self_check(evaluator=wrong_class_eval)
        self.assertFalse(res["passed"])
        self.assertIn("bool_valid_range", res["survived_mutants"])


class ErrorVsUnsupportedBoundaryTest(unittest.TestCase):
    def test_valid_unsupported_summary_passes_boundary(self) -> None:
        summary = _make_valid_miri_summary()
        ok, reasons = campaign.validate_error_vs_unsupported_boundary(summary)
        self.assertTrue(ok, reasons)
        self.assertEqual(reasons, [])

        rf = campaign.evaluate_miri_red_flags(summary, 0x5EED0001, {}, 50.0, 0)
        self.assertTrue(rf.passed, rf.failure_reasons)
        self.assertTrue(rf.checks["error_vs_unsupported_boundary"])

    def test_oracle_errors_exceeding_budget_fail_closed(self) -> None:
        for field_kind in ("anneal_error", "capture_failed", "miri_oracle_error"):
            summary = _make_valid_miri_summary()
            if field_kind == "anneal_error":
                summary["anneal_outcomes"]["error"] = 1  # type: ignore[index]
                summary["anneal_outcomes"]["unsupported"] = 0  # type: ignore[index]
                summary["not_compared_reasons"]["capture_failed"] = 1  # type: ignore[index]
                summary["not_compared_reasons"]["unsupported"] = 0  # type: ignore[index]
            elif field_kind == "capture_failed":
                summary["not_compared_reasons"]["capture_failed"] = 1  # type: ignore[index]
            else:
                summary["not_compared_reasons"]["miri_oracle_error"] = 1  # type: ignore[index]
            ok, reasons = campaign.validate_error_vs_unsupported_boundary(
                summary, max_oracle_errors=0
            )
            self.assertFalse(ok, field_kind)
            self.assertTrue(
                any("oracle_errors_exceeded" in r for r in reasons),
                f"{field_kind}: {reasons}",
            )

    def test_crash_or_malformed_marker_masked_as_unsupported_fails_closed(self) -> None:
        summary = _make_valid_miri_summary()
        summary["diagnostics"] = [
            {
                "fn_name": "wide_shift_cand",
                "not_compared_reason": "unsupported",
                "message": "SIGABRT: INTERNAL PANIC: Nat.shiftl exponent is too big",
            }
        ]
        ok, reasons = campaign.validate_error_vs_unsupported_boundary(summary)
        self.assertFalse(ok)
        self.assertTrue(
            any(r.startswith("error_masked_as_unsupported") for r in reasons),
            reasons,
        )

        rf = campaign.evaluate_miri_red_flags(summary, 0x5EED0001, {}, 50.0, 0)
        self.assertFalse(rf.passed)
        self.assertFalse(rf.checks["error_vs_unsupported_boundary"])
        self.assertTrue(
            any("error_masked_as_unsupported" in r for r in rf.failure_reasons)
        )

    def test_unsupported_count_exceeding_anneal_unsupported_fails_closed(self) -> None:
        summary = _make_valid_miri_summary()
        summary["anneal_outcomes"]["unsupported"] = 0  # type: ignore[index]
        summary["anneal_outcomes"]["pass"] = 6  # type: ignore[index]
        summary["not_compared_reasons"]["unsupported"] = 1  # type: ignore[index]
        ok, reasons = campaign.validate_error_vs_unsupported_boundary(summary)
        self.assertFalse(ok)
        self.assertTrue(
            any("error_masked_as_unsupported" in r for r in reasons),
            reasons,
        )

    def test_distinct_errored_items_count_once_against_max_oracle_errors(self) -> None:
        # One capture failure is both an `anneal_outcomes.error` and a
        # `capture_failed`: it is one errored item, so `--max-oracle-errors 1` admits
        # it (the runner used to count it twice) and 0 rejects it.
        summary = _make_valid_miri_summary()
        summary["anneal_outcomes"]["error"] = 1  # type: ignore[index]
        summary["anneal_outcomes"]["pass"] = 4  # type: ignore[index]
        summary["not_compared_reasons"]["capture_failed"] = 1  # type: ignore[index]
        summary["not_compared_count"] = 2
        summary["compared_candidates"] = 6
        summary["agree_count"] = 6
        self.assertEqual(campaign.count_distinct_miri_errored_items(summary), 1)
        rf1 = campaign.evaluate_miri_red_flags(summary, 0x5EED0001, {}, 50.0, 1)
        self.assertTrue(rf1.passed, rf1.failure_reasons)
        rf0 = campaign.evaluate_miri_red_flags(summary, 0x5EED0001, {}, 50.0, 0)
        self.assertFalse(rf0.checks["oracle_error_threshold"])
        self.assertTrue(rf0.checks["error_vs_unsupported_boundary"], rf0.failure_reasons)
        self.assertEqual(
            sum("oracle_errors_exceeded" in r for r in rf0.failure_reasons), 1, rf0.failure_reasons
        )
        # A second errored item (a Miri error shadowing an `unsupported` outcome)
        # exceeds a budget of 1.
        summary["miri_verdicts"]["error"] = 1  # type: ignore[index]
        summary["miri_verdicts"]["pass"] = 5  # type: ignore[index]
        summary["not_compared_reasons"]["miri_oracle_error"] = 1  # type: ignore[index]
        summary["not_compared_reasons"]["unsupported"] = 0  # type: ignore[index]
        self.assertEqual(campaign.count_distinct_miri_errored_items(summary), 2)
        rf1b = campaign.evaluate_miri_red_flags(summary, 0x5EED0001, {}, 50.0, 1)
        self.assertFalse(rf1b.checks["oracle_error_threshold"])

    def test_itree_crash_masked_as_compile_failed_is_a_red_flag(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            itree = make_healthy_itree_report(Path(tmp))
            red = campaign.evaluate_itree_red_flags(itree, 0x20020002, {}, 50.0)
            self.assertTrue(red.passed, red.failure_reasons)
            self.assertTrue(red.checks["itree_error_vs_compile_failed_boundary"])
            itree["diagnostics"] = [
                {
                    "fn_name": "b0_c3__kernel_step",
                    "not_compared_reason": "compile_failed",
                    "message": "error: internal compiler error: unexpected panic",
                },
                {
                    "fn_name": "b0_c4__kernel_step",
                    "not_compared_reason": "compile_failed",
                    "message": "error[E0308]: mismatched types",
                },
            ]
            red = campaign.evaluate_itree_red_flags(itree, 0x20020002, {}, 50.0)
            self.assertFalse(red.passed)
            self.assertFalse(red.checks["itree_error_vs_compile_failed_boundary"])
            masked = [r for r in red.failure_reasons if r.startswith("itree_error_masked")]
            self.assertEqual(len(masked), 1, red.failure_reasons)
            self.assertIn("b0_c3__kernel_step", masked[0])


class CliGateIntegrationTest(unittest.TestCase):
    def setUp(self) -> None:
        campaign.LAST_HARNESS_DIAGNOSTICS.clear()

    def test_standalone_self_check_mutants_and_stale_ratchet_cli(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp) / "state"
            rc = _quiet_main(["--self-check-mutants", "--state-dir", str(state_dir)])
            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            summary = _read_summary(state_dir)
            self.assertEqual(summary["mode"], "standalone_gate")
            self.assertTrue(summary["semantic_mutant_self_check"]["passed"])
            self.assertEqual(summary["semantic_mutant_self_check"]["killed_count"], 5)
            self.assertIsNone(summary["stale_ratchet_audit"])

            expired_q = Path(tmp) / "expired_quarantine.toml"
            expired_q.write_text(
                '[[quarantined]]\n'
                'fingerprint = "RawPtrOffsetMutator:ub_location_mismatch:MirDiffTag.ub"\n'
                'expires = "2020-01-01"\n'
                'reason = "long gone"\n',
                encoding="utf-8",
            )
            rc_fail = _quiet_main(
                [
                    "--check-stale-ratchet",
                    "--quarantine-file",
                    str(expired_q),
                    "--state-dir",
                    str(state_dir),
                ]
            )
            self.assertEqual(rc_fail, campaign.EXIT_HARNESS_FAILED)
            failed = _read_summary(state_dir)
            self.assertFalse(failed["passed"])
            self.assertIn(
                "expired_quarantine_entry",
                failed["stale_ratchet_audit"]["stale_entries"][0]["reason"],
            )

    def test_campaign_run_with_gates_records_sections_in_summary(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp) / "campaign_state"
            stub_summary = _make_valid_miri_summary()
            with mock.patch.object(campaign, "run_harness", return_value=dict(stub_summary)):
                rc = _quiet_main(
                    [
                        "--profile",
                        "smoke",
                        "--miri-only",
                        "--self-check-mutants",
                        "--check-stale-ratchet",
                        "--state-dir",
                        str(state_dir),
                    ]
                )
            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            summary = _read_summary(state_dir)
            self.assertTrue(summary["semantic_mutant_self_check"]["passed"])
            self.assertTrue(summary["stale_ratchet_audit"]["passed"])
            self.assertEqual(
                summary["gates"],
                {"passed": True, "self_check_mutants": True, "check_stale_ratchet": True},
            )

    def test_miri_only_campaign_does_not_flag_itree_quarantine_entries_as_stale(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp) / "campaign_state"
            q_file = Path(tmp) / "quarantine.toml"
            q_file.write_text(
                "[[quarantined]]\n"
                'fingerprint = "ArithmeticCastMutator:itree_outcome_mismatch:'
                'TraceReplayDiag.outcome_mismatch"\n'
                'expires = "2099-01-01"\n'
                'reason = "tracked ITree outcome mismatch"\n',
                encoding="utf-8",
            )
            argv = [
                "--profile",
                "smoke",
                "--miri-only",
                "--check-stale-ratchet",
                "--quarantine-file",
                str(q_file),
                "--state-dir",
                str(state_dir),
            ]
            with mock.patch.object(
                campaign, "run_harness", return_value=_make_valid_miri_summary()
            ):
                rc = _quiet_main(argv)
            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            summary = _read_summary(state_dir)
            self.assertEqual(summary["stale_ratchet_audit"]["stale_entries"], [])


class OracleOutcomeClassificationTest(unittest.TestCase):
    """`classify_oracle_outcome_tags` mirrors `compare_miri_and_anneal`."""

    def test_classification_table_and_precedence(self) -> None:
        table = [
            ("pass:scalar:5:4", "pass:scalar:5:4", ("agree", "")),
            ("pass:unit", "pass:unit", ("agree", "")),
            ("pass:scalar:5:4", "pass:scalar:6:4", ("diverge", "wrong_value")),
            ("pass:scalar:5:4", "pass:scalar:5:8", ("diverge", "wrong_value")),
            ("pass:scalar:5:4", "abort@src/lib.rs:3:5: 3:9", ("diverge", "wrong_value")),
            ("pass:unit", "pass:other", ("diverge", "wrong_value")),
            ("pass:unit", "panic@src/lib.rs:3:5: 3:9", ("diverge", "return_vs_panic")),
            ("pass:unit", "ub@src/lib.rs:3:5: 3:9", ("diverge", "false_positive_ub")),
            ("panic@src/lib.rs:3:7", "pass:unit", ("diverge", "panic_vs_return")),
            ("panic@src/lib.rs:3:7", "abort@src/lib.rs:3:5: 3:9", ("diverge", "panic_vs_return")),
            ("panic@src/lib.rs:3:7", "ub@src/lib.rs:3:5: 3:9", ("diverge", "false_positive_ub")),
            ("panic@src/lib.rs:3:7", "panic@src/lib.rs:3:5: 3:9", ("agree", "")),
            ("panic@src/lib.rs:9:7", "panic@src/lib.rs:3:5: 3:9", ("diverge", "panic_site_mismatch")),
            ("panic", "panic@src/lib.rs:3:5: 3:9", ("diverge", "panic_site_mismatch")),
            ("ub@src/lib.rs:3:7", "ub@src/lib.rs:3:5: 3:9", ("agree", "")),
            ("ub@src/lib.rs:4:1", "ub@src/lib.rs:3:5: 3:9", ("diverge", "ub_location_mismatch")),
            ("ub", "ub@src/lib.rs:3:5: 3:9", ("diverge", "ub_location_mismatch")),
            ("ub@src/lib.rs:3:7", "ub", ("diverge", "ub_location_mismatch")),
            ("ub@src/lib.rs:3:7", "pass:unit", ("diverge", "missed_ub")),
            ("ub@src/lib.rs:3:7", "panic@src/lib.rs:3:5: 3:9", ("diverge", "missed_ub")),
            ("ub@src/lib.rs:3:7", "abort", ("diverge", "missed_ub")),
            # Not-compared precedence: Miri error > capture error > external call >
            # unsupported > fuel.
            ("oracle_error:boom", "capture_error:x", ("not_compared", "miri_oracle_error")),
            ("ub@src/lib.rs:3:7", "capture_error:x", ("not_compared", "capture_failed")),
            ("pass:unit", "externalCall:core::f", ("not_compared", "external_call")),
            ("pass:unit", "unsupported@src/lib.rs:3:5: 3:9", ("not_compared", "unsupported")),
            ("pass:unit", "outOfFuel", ("not_compared", "out_of_fuel")),
        ]
        for miri_tag, anneal_tag, expected in table:
            with self.subTest(miri=miri_tag, anneal=anneal_tag):
                self.assertEqual(
                    campaign.classify_oracle_outcome_tags(miri_tag, anneal_tag), expected
                )

    def test_span_parsing_is_a_faithful_port_of_parse_anneal_span(self) -> None:
        # `SourceSpan::parse_anneal_span` splits a range only at `": "` (as
        # `display_short` renders it): an unspaced `file:3:5:3:9` is the single
        # point `3:9` in a file named `file:3:5`, which never matches `src/lib.rs`.
        self.assertEqual(
            campaign._parse_src_span("src/lib.rs:3:5: 3:9"), ("src/lib.rs", 3, 5, 3, 9)
        )
        self.assertEqual(
            campaign._parse_src_span("src/lib.rs:3:5:3:9"), ("src/lib.rs:3:5", 3, 9, 3, 9)
        )
        self.assertEqual(
            campaign.classify_oracle_outcome_tags("ub@src/lib.rs:3:7", "ub@src/lib.rs:3:5:3:9"),
            ("diverge", "ub_location_mismatch"),
        )
        # `str::parse::<u32>`: an optional `+`, ASCII digits only, at most u32::MAX;
        # Unicode digits never crash the parser.
        self.assertEqual(campaign._parse_src_pos("src/lib.rs:+3:+7"), ("src/lib.rs", 3, 7))
        self.assertIsNone(campaign._parse_src_pos("src/lib.rs:\u00b2:7"))
        self.assertIsNone(campaign._parse_src_pos("src/lib.rs:4294967296:7"))
        self.assertIsNone(campaign._parse_src_pos("src/lib.rs:-3:7"))
        self.assertEqual(
            campaign._parse_src_pos("src/lib.rs:4294967295:7"), ("src/lib.rs", 4294967295, 7)
        )
        self.assertIsNone(campaign._parse_src_span("src/lib.rs:3:5: 3:9:1"))
        self.assertIsNone(campaign._parse_src_span("none"))
        self.assertEqual(
            campaign.classify_oracle_outcome_tags("ub@src/lib.rs:\u00b2:5", "ub@src/lib.rs:3:5: 3:9"),
            ("diverge", "ub_location_mismatch"),
        )
        # Trailing `:` after a position is stripped like `trim_end_matches(':')`.
        self.assertEqual(campaign._parse_src_pos(" src/lib.rs:3:7: "), ("src/lib.rs", 3, 7))


class SemanticMutantDifferentialTest(unittest.TestCase):
    """The default self-check is differential: unmutated semantics must pass the
    campaign pipeline and every mutated variant must be rejected by it."""

    def test_default_self_check_records_clean_baselines_and_killed_variants(self) -> None:
        res = campaign.run_semantic_mutant_self_check()
        self.assertTrue(res["passed"], res)
        by_id = {r["id"]: r for r in res["results"]}
        for mutant_id, r in by_id.items():
            self.assertEqual(r["baseline_verdict"], "agree", mutant_id)
            self.assertEqual(r["baseline_exit_code"], campaign.EXIT_SUCCESS, mutant_id)
            self.assertTrue(r["variants"], mutant_id)
            self.assertTrue(all(v["killed"] for v in r["variants"]), r)
        wide = by_id["wide_shift"]["variants"]
        self.assertEqual(
            [(v["label"], v["exit_code"], v["kill_class"]) for v in wide],
            [
                ("guard_omitted_lean_abort", campaign.EXIT_HARNESS_FAILED, "harness_error"),
                (
                    "guard_omitted_abort_masked_as_unsupported",
                    campaign.EXIT_HARNESS_FAILED,
                    "harness_error",
                ),
                ("guard_masks_exponent_silently", campaign.EXIT_DIVERGENCE_DETECTED, "missed_ub"),
            ],
        )
        self.assertIn("error_masked_as_unsupported", wide[1]["detail"])
        self.assertIn("oracle_errors_exceeded", wide[0]["detail"])
        self.assertEqual(by_id["div_by_zero"]["kill_class"], "panic_vs_return")
        frag = by_id["provenance_frag"]["variants"]
        self.assertEqual(
            [(v["label"], v["exit_code"], v["kill_class"]) for v in frag],
            [("integer_bytes_keep_provenance", campaign.EXIT_DIVERGENCE_DETECTED, "missed_ub")],
        )

    def test_self_check_detects_a_campaign_pipeline_that_swallows_divergences(self) -> None:
        real_dedup = campaign.deduplicate_and_quarantine_findings

        def quarantine_everything(findings, known, rules):  # type: ignore[no-untyped-def]
            all_dedup, _, _ = real_dedup(findings, known, rules)
            for d in all_dedup:
                d.quarantined = True
            return all_dedup, [], all_dedup

        with mock.patch.object(
            campaign, "deduplicate_and_quarantine_findings", quarantine_everything
        ):
            res = campaign.run_semantic_mutant_self_check()
        self.assertFalse(res["passed"])
        self.assertEqual(res["exit_code"], campaign.EXIT_HARNESS_FAILED)
        self.assertEqual(
            res["survived_mutants"],
            ["bool_valid_range", "storage_dead_tag", "provenance_frag", "div_by_zero", "wide_shift"],
        )
        wide = next(r for r in res["results"] if r["id"] == "wide_shift")
        self.assertEqual(wide["survived_variants"], ["guard_masks_exponent_silently"])

    def test_self_check_detects_a_disabled_error_vs_unsupported_boundary(self) -> None:
        with mock.patch.object(
            campaign, "validate_error_vs_unsupported_boundary", return_value=(True, [])
        ):
            res = campaign.run_semantic_mutant_self_check()
        self.assertFalse(res["passed"])
        self.assertEqual(res["survived_mutants"], ["wide_shift"])
        wide = next(r for r in res["results"] if r["id"] == "wide_shift")
        self.assertEqual(
            wide["survived_variants"], ["guard_omitted_abort_masked_as_unsupported"]
        )

    def test_self_check_detects_a_campaign_that_rejects_agreeing_runs(self) -> None:
        # A pipeline that fails every run would "kill" every mutant; the baseline check
        # must expose it instead.
        with mock.patch.object(
            campaign,
            "validate_performed_miri_summary",
            return_value=(False, "always broken"),
        ):
            res = campaign.run_semantic_mutant_self_check()
        self.assertFalse(res["passed"])
        self.assertEqual(res["killed_count"], 0)
        self.assertTrue(all(r["kill_class"] == "baseline_not_clean" for r in res["results"]))

    def test_invalid_baseline_and_equivalent_mutant_both_fail_closed(self) -> None:
        base = dict(campaign.SEEDED_SEMANTIC_MUTANTS[0])
        bad_baseline = dict(base, id="bad_baseline", baseline_anneal_outcome="pass:scalar:2:4")
        equivalent = dict(
            base,
            id="equivalent_mutant",
            mutant_variants=(
                {
                    "label": "same_as_baseline",
                    "anneal_outcome": base["baseline_anneal_outcome"],
                    "anneal_lean_tag": base["baseline_anneal_lean_tag"],
                },
            ),
        )
        res = campaign.run_semantic_mutant_self_check(mutants=[bad_baseline, equivalent])
        self.assertFalse(res["passed"])
        self.assertEqual(res["survived_mutants"], ["bad_baseline", "equivalent_mutant"])
        by_id = {r["id"]: r for r in res["results"]}
        self.assertEqual(by_id["bad_baseline"]["kill_class"], "baseline_not_clean")
        self.assertEqual(by_id["equivalent_mutant"]["survived_variants"], ["same_as_baseline"])

    def test_seeded_probe_sources_match_the_live_validated_rust_probes(self) -> None:
        # `semantic_mutant_probes_agree_live_and_known_provenance_gaps_stay_pinned` runs
        # these exact probe sources through the live, unmutated Miri + Anneal pipeline,
        # which is what justifies each simulated clean baseline.
        body = _rust_const_body("SEMANTIC_MUTANT_PROBES")
        rust_probes = dict(re.findall(r'\(\s*"(\w+)",\s*r#"(.*?)"#,\s*\)', body, re.S))
        py_probes = {
            str(m["id"]): str(m["probe_rust_source"]) for m in campaign.SEEDED_SEMANTIC_MUTANTS
        }
        self.assertEqual(list(rust_probes), list(py_probes))
        for mutant_id, source in py_probes.items():
            with self.subTest(mutant=mutant_id):
                self.assertEqual(rust_probes[mutant_id], source)

    def test_seeded_baselines_replay_the_live_outcomes_pinned_in_rust(self) -> None:
        # The live Rust test pins each probe's probe-relative Miri outcome, Anneal
        # outcome, and Lean tag in `SEMANTIC_MUTANT_PROBE_OUTCOMES`; the simulated
        # baselines must be exactly those outcomes.
        body = _rust_const_body("SEMANTIC_MUTANT_PROBE_OUTCOMES")
        pinned = re.findall(
            r'\(\s*"(\w+)",\s*"([^"]*)",\s*"([^"]*)",\s*"([^"]*)",?\s*\)', body, re.S
        )
        self.assertEqual(len(pinned), 5, body)
        py = [
            (
                str(m["id"]),
                str(m["reference_miri_outcome"]),
                str(m["baseline_anneal_outcome"]),
                str(m["baseline_anneal_lean_tag"]),
            )
            for m in campaign.SEEDED_SEMANTIC_MUTANTS
        ]
        self.assertEqual(py, [tuple(p) for p in pinned])
        for mutant_id, miri_tag, anneal_tag, _ in py:
            with self.subTest(mutant=mutant_id):
                self.assertEqual(
                    campaign.classify_oracle_outcome_tags(miri_tag, anneal_tag), ("agree", "")
                )

    def test_provenance_frag_probe_strips_provenance_at_a_live_address(self) -> None:
        frag = next(m for m in campaign.SEEDED_SEMANTIC_MUTANTS if m["id"] == "provenance_frag")
        source = str(frag["probe_rust_source"])
        # No bogus unmapped constant address: every pointer byte is overwritten with
        # the integer value of `x`'s own address, so only provenance is lost.
        self.assertNotIn("[4u8", source)
        for needle in (
            "let addr: usize = p as usize;",
            "let slot: *mut usize = (&raw mut p) as *mut usize;",
            "*slot = addr;",
            "        *p\n",
        ):
            self.assertIn(needle, source)
        self.assertTrue(str(frag["reference_miri_outcome"]).startswith("ub@"))
        self.assertTrue(str(frag["baseline_anneal_outcome"]).startswith("ub@"))
        self.assertEqual(frag["baseline_anneal_lean_tag"], "MirDiffTag.ub")
        self.assertEqual(
            [(v["anneal_outcome"], v["anneal_lean_tag"]) for v in frag["mutant_variants"]],
            [("pass:scalar:7:4", "(MirDiffTag.normalScalar 7 4)")],
        )
        # The Rust test runs live controls proving the rewritten pointer holds `x`'s
        # address (returns 1) and that this address reads `x`'s value 7 with
        # provenance: a semantics that accepts the provenance-free pointer reads 7.
        controls = re.findall(
            r'\(\s*"(\w+)",\s*r#"(.*?)"#,\s*(\d+),\s*\)',
            _rust_const_body("PROVENANCE_FRAG_CONTROL_PROBES"),
            re.S,
        )
        self.assertEqual(
            [(name, int(value)) for name, _, value in controls],
            [("probe_ctrl_provenance_addr_preserved", 1), ("probe_ctrl_provenance_exposed_addr", 7)],
        )
        for name, control_source, _ in controls:
            self.assertIn("let x: u32 = 7u32;", control_source, name)
            self.assertIn("let addr: usize = p as usize;", control_source, name)
            self.assertIn("*slot = addr;", control_source, name)
        gaps = re.findall(r'\(\s*"(\w+)",', _rust_const_body("KNOWN_PROVENANCE_GAP_PROBES"))
        self.assertEqual(
            gaps,
            [
                "probe_gap_provenance_overwritten_byte",
                "probe_gap_provenance_u8_roundtrip",
                "probe_gap_provenance_mixed_fragments",
            ],
        )

    def test_evaluator_exception_counts_as_survival(self) -> None:
        def flaky(mutant: dict[str, object]) -> bool:
            if mutant["id"] == "provenance_frag":
                raise RuntimeError("lean worker crashed")
            return True

        res = campaign.run_semantic_mutant_self_check(evaluator=flaky)
        self.assertFalse(res["passed"])
        self.assertEqual(res["survived_mutants"], ["provenance_frag"])
        frag = next(r for r in res["results"] if r["id"] == "provenance_frag")
        self.assertEqual(frag["kill_class"], "evaluator_error")

    def test_simulation_and_normalization_crashes_count_as_survival(self) -> None:
        base = dict(campaign.SEEDED_SEMANTIC_MUTANTS[0])
        no_reference = {k: v for k, v in base.items() if k != "reference_miri_outcome"}
        no_reference["id"] = "no_reference"
        res = campaign.run_semantic_mutant_self_check(mutants=[no_reference, {"name": "no_id"}])
        self.assertFalse(res["passed"])
        self.assertEqual(res["killed_count"], 0)
        self.assertEqual(res["survived_mutants"], ["no_reference", "<mutant[1]>"])
        self.assertTrue(all(r["kill_class"] == "evaluator_error" for r in res["results"]), res)

        bad_exit = campaign.run_semantic_mutant_self_check(
            evaluator=lambda m: {"killed": True, "kill_class": "missed_ub", "exit_code": "4"},
            mutants=[base],
        )
        self.assertFalse(bad_exit["passed"])
        self.assertEqual(bad_exit["results"][0]["kill_class"], "evaluator_error")

    def test_kill_with_an_unexpected_class_is_survival_and_empty_list_fails(self) -> None:
        base = dict(campaign.SEEDED_SEMANTIC_MUTANTS[0], expected_kill_classes=("wrong_value",))
        res = campaign.run_semantic_mutant_self_check(mutants=[base])
        self.assertFalse(res["passed"])
        self.assertEqual(res["results"][0]["variants"][0]["kill_class"], "missed_ub")
        self.assertFalse(res["results"][0]["variants"][0]["killed"])
        empty = campaign.run_semantic_mutant_self_check(mutants=[])
        self.assertFalse(empty["passed"])
        self.assertEqual(empty["exit_code"], campaign.EXIT_HARNESS_FAILED)


class ErrorBoundaryAccountingTest(unittest.TestCase):
    def test_properly_classified_oracle_error_item_is_not_reported_as_masked(self) -> None:
        summary = _make_valid_miri_summary()
        summary["miri_verdicts"]["error"] = 1  # type: ignore[index]
        summary["miri_verdicts"]["pass"] = 5  # type: ignore[index]
        summary["not_compared_reasons"]["miri_oracle_error"] = 1  # type: ignore[index]
        summary["not_compared_count"] = 2
        summary["compared_candidates"] = 6
        summary["agree_count"] = 6
        summary["anneal_outcomes"]["unsupported"] = 2  # type: ignore[index]
        summary["anneal_outcomes"]["pass"] = 4  # type: ignore[index]
        summary["item_reports"] = [
            {
                "name": "c3",
                "miri_outcome": "oracle_error:driver exited before entering item",
                "anneal_outcome": "unsupported@src/lib.rs:4:5: 4:9",
                "not_compared_reason": "miri_oracle_error",
            }
        ]
        ok, reasons = campaign.validate_error_vs_unsupported_boundary(
            summary, max_oracle_errors=1
        )
        self.assertTrue(ok, reasons)
        self.assertEqual(reasons, [])

    def test_miri_error_routed_into_unsupported_is_masking(self) -> None:
        summary = _make_valid_miri_summary()
        summary["miri_verdicts"]["error"] = 1  # type: ignore[index]
        summary["miri_verdicts"]["pass"] = 5  # type: ignore[index]
        ok, reasons = campaign.validate_error_vs_unsupported_boundary(
            summary, max_oracle_errors=5
        )
        self.assertFalse(ok)
        self.assertTrue(
            any(r.startswith("error_masked_as_unsupported: 1 Miri oracle error") for r in reasons),
            reasons,
        )

    def test_single_capture_failure_is_counted_once_against_the_budget(self) -> None:
        summary = _make_valid_miri_summary()
        summary["anneal_outcomes"]["error"] = 1  # type: ignore[index]
        summary["anneal_outcomes"]["pass"] = 4  # type: ignore[index]
        summary["not_compared_reasons"]["capture_failed"] = 1  # type: ignore[index]
        summary["not_compared_count"] = 2
        summary["compared_candidates"] = 6
        summary["agree_count"] = 6
        ok, reasons = campaign.validate_error_vs_unsupported_boundary(
            summary, max_oracle_errors=1
        )
        self.assertTrue(ok, reasons)
        ok0, reasons0 = campaign.validate_error_vs_unsupported_boundary(
            summary, max_oracle_errors=0
        )
        self.assertFalse(ok0)
        self.assertTrue(any("oracle_errors_exceeded: 1 errored items" in r for r in reasons0))

    def test_item_outcome_audit_accepts_consistent_real_format_summary(self) -> None:
        summary = _with_consistent_item_outcomes(_make_valid_miri_summary())
        self.assertEqual(campaign.audit_item_outcomes_against_summary(summary), [])
        ok, reasons = campaign.validate_error_vs_unsupported_boundary(summary)
        self.assertTrue(ok, reasons)
        rf = campaign.evaluate_miri_red_flags(summary, 0x5EED0001, {}, 50.0, 0)
        self.assertTrue(rf.passed, rf.failure_reasons)

    def test_item_outcome_audit_catches_capture_error_hidden_in_unsupported(self) -> None:
        # Every aggregate invariant holds (the harness even "counted" the item as an
        # Anneal `unsupported` outcome); only the per-item recomputation sees that the
        # reported Anneal outcome is a capture / Lean crash.
        summary = _with_consistent_item_outcomes(_make_valid_miri_summary())
        summary["item_outcomes"]["pass_direct_fn_call"]["anneal_outcome"] = (  # type: ignore[index]
            "capture_error:INTERNAL PANIC: Nat.shiftl exponent is too big"
        )
        ok, reasons = campaign.validate_error_vs_unsupported_boundary(summary, max_oracle_errors=5)
        self.assertFalse(ok)
        self.assertTrue(
            any(
                r.startswith("error_masked_as_unsupported: not_compared_reasons.capture_failed")
                for r in reasons
            ),
            reasons,
        )
        self.assertTrue(
            any(r.startswith("item_accounting_mismatch: not_compared_reasons.unsupported") for r in reasons),
            reasons,
        )

    def test_item_outcome_audit_catches_verdict_flips_and_missing_items(self) -> None:
        summary = _with_consistent_item_outcomes(_make_valid_miri_summary())
        # A missed UB reported as agreement (and counted as such).
        summary["item_outcomes"]["ub_item"]["anneal_outcome"] = "pass:unit"  # type: ignore[index]
        reasons = campaign.audit_item_outcomes_against_summary(summary)
        self.assertTrue(
            any("item 'ub_item' reported 'agree'" in r and "diverge:missed_ub" in r for r in reasons),
            reasons,
        )
        self.assertTrue(any("divergence_classes.missed_ub reported 0" in r for r in reasons), reasons)
        # A dropped item.
        summary = _with_consistent_item_outcomes(_make_valid_miri_summary())
        del summary["item_outcomes"]["pass_item_0"]  # type: ignore[attr-defined]
        reasons = campaign.audit_item_outcomes_against_summary(summary)
        self.assertTrue(any("covers 7 items but compiled_candidates is 8" in r for r in reasons))
        ok, _ = campaign.validate_error_vs_unsupported_boundary(summary)
        self.assertFalse(ok)

    def test_span_parser_matches_harness_rendering_and_file_suffixes(self) -> None:
        # `SourceSpan::display_short` renders `file:l:c: l:c`; Miri positions may be
        # absolute paths ending in the span's relative file.
        self.assertEqual(
            campaign.classify_oracle_outcome_tags(
                "panic@/tmp/x/src/lib.rs:12:7", "panic@src/lib.rs:12:5: 12:14"
            ),
            ("agree", ""),
        )
        self.assertEqual(
            campaign.classify_oracle_outcome_tags(
                "panic@/tmp/x/src/main.rs:12:7", "panic@src/lib.rs:12:5: 12:14"
            ),
            ("diverge", "panic_site_mismatch"),
        )
        self.assertEqual(
            campaign.classify_oracle_outcome_tags("ub@./src/lib.rs:3:1", "ub@src/lib.rs:2:5: 3:9"),
            ("agree", ""),
        )
        # Single-point Anneal span (`SourceSpan::parse_anneal_span` fallback).
        self.assertEqual(
            campaign.classify_oracle_outcome_tags(
                "panic@/tmp/x/src/lib.rs:12:7", "panic@src/lib.rs:12:7"
            ),
            ("agree", ""),
        )
        # Zero line/column or empty filename is rejected (`SourcePos::parse_rustc_pos`).
        self.assertEqual(
            campaign.classify_oracle_outcome_tags("ub@src/lib.rs:0:5", "ub@src/lib.rs:0:1: 1:9"),
            ("diverge", "ub_location_mismatch"),
        )
        self.assertEqual(
            campaign.classify_oracle_outcome_tags("ub@:3:5", "ub@:3:1: 3:9"),
            ("diverge", "ub_location_mismatch"),
        )
        # `pass:other` is never classified as agreement (`compare_miri_and_anneal`).
        self.assertEqual(
            campaign.classify_oracle_outcome_tags("pass:other", "pass:other"),
            ("diverge", "wrong_value"),
        )

    def test_item_outcomes_crash_marker_and_shadowed_capture_error_caught(self) -> None:
        # 1. Crash marker masked inside an `item_outcomes` entry classified as `unsupported`.
        summary = _with_consistent_item_outcomes(_make_valid_miri_summary())
        summary["item_outcomes"]["pass_direct_fn_call"]["anneal_outcome"] = (  # type: ignore[index]
            "unsupported@src/lib.rs:50:5: 50:20 (SIGABRT: Nat.shiftl exponent is too big)"
        )
        ok, reasons = campaign.validate_error_vs_unsupported_boundary(summary, max_oracle_errors=5)
        self.assertFalse(ok)
        self.assertTrue(
            any("item_outcomes['pass_direct_fn_call'] masks" in r for r in reasons),
            reasons,
        )

        # 2. Item with both `oracle_error` and `capture_error`: `not_compared_reasons`
        #    legitimately reports `miri_oracle_error=1, capture_failed=0`, but hiding the
        #    Anneal capture error in `anneal_outcomes.unsupported=1, error=0` is caught.
        shadowed = _with_consistent_item_outcomes(_make_valid_miri_summary())
        shadowed["miri_verdicts"]["pass"] = 5  # type: ignore[index]
        shadowed["miri_verdicts"]["error"] = 1  # type: ignore[index]
        shadowed["not_compared_reasons"]["unsupported"] = 0  # type: ignore[index]
        shadowed["not_compared_reasons"]["miri_oracle_error"] = 1  # type: ignore[index]
        shadowed["item_outcomes"]["pass_direct_fn_call"] = {  # type: ignore[index]
            "verdict": "not_compared",
            "miri_outcome": "oracle_error:driver crashed",
            "anneal_outcome": "capture_error:INTERNAL PANIC: Nat.shiftl exponent is too big",
            "anneal_lean_tag": "none",
        }
        ok2, reasons2 = campaign.validate_error_vs_unsupported_boundary(
            shadowed, max_oracle_errors=5
        )
        self.assertFalse(ok2)
        self.assertTrue(
            any(
                r.startswith("error_masked_as_unsupported: anneal_outcomes.error reported 0")
                for r in reasons2
            ),
            reasons2,
        )

    def test_findings_with_not_compared_outcome_tags_are_rejected(self) -> None:
        for anneal_tag in (
            "unsupported@src/lib.rs:4:5: 4:9",
            "capture_error:INTERNAL PANIC: Nat.shiftl exponent is too big",
            "externalCall:core::fmt::write",
            "outOfFuel",
        ):
            with self.subTest(anneal_tag=anneal_tag), tempfile.TemporaryDirectory() as tmp:
                repro = Path(tmp) / "repro.rs"
                repro.write_text("pub fn f() {}\n", encoding="utf-8")
                summary = _make_valid_miri_summary()
                summary["findings"] = [
                    {
                        "finding_id": "finding_0000_f",
                        "fn_name": "f",
                        "seed_name": "f",
                        "divergence_class": "missed_ub",
                        "miri_outcome": "ub@src/lib.rs:4:7",
                        "anneal_outcome": anneal_tag,
                        "anneal_lean_tag": "MirDiffTag.unsupported",
                        "miri_excerpt": "error: Undefined Behavior",
                        "repro_path": str(repro),
                        "kernel_confirmed": True,
                    }
                ]
                ok, reason = campaign.validate_performed_miri_summary(summary)
                self.assertFalse(ok)
                self.assertIn("not-compared outcome", reason)
        summary = _make_valid_miri_summary()
        summary["findings"] = [
            {
                "finding_id": "finding_0000_f",
                "fn_name": "f",
                "seed_name": "f",
                "divergence_class": "missed_ub",
                "miri_outcome": "oracle_error:driver crashed",
                "anneal_outcome": "pass:unit",
                "anneal_lean_tag": "MirDiffTag.normalUnit",
                "miri_excerpt": "x",
                "repro_path": "/nonexistent/repro.rs",
                "kernel_confirmed": True,
            }
        ]
        self.assertFalse(campaign.validate_performed_miri_summary(summary)[0])

    def test_reconciled_panic_macro_site_is_accepted_only_as_the_harness_records_it(self) -> None:
        summary = _with_reconciled_panic_macro_item(
            _with_consistent_item_outcomes(_make_valid_miri_summary())
        )
        # The strict comparator alone says `panic_site_mismatch` ...
        item = summary["item_outcomes"]["panic_item"]  # type: ignore[index]
        self.assertEqual(
            campaign.classify_oracle_outcome_tags(item["miri_outcome"], item["anneal_outcome"]),
            ("diverge", "panic_site_mismatch"),
        )
        # ... but the recorded reconciliation justifies the harness's `agree`.
        self.assertEqual(campaign.audit_item_outcomes_against_summary(summary), [])
        rf = campaign.evaluate_miri_red_flags(summary, 0x5EED0001, {}, 50.0, 0)
        self.assertTrue(rf.passed, rf.failure_reasons)

        def site_mutation(mutate) -> list[str]:  # type: ignore[no-untyped-def]
            s = _with_reconciled_panic_macro_item(
                _with_consistent_item_outcomes(_make_valid_miri_summary())
            )
            mutate(s)
            return campaign.audit_item_outcomes_against_summary(s)

        cases = {
            "site_missing": lambda s: (s.pop("reconciled_panic_sites"), s.pop("reconciled_panic_sites_count")),
            "span_differs": lambda s: s["reconciled_panic_sites"][0].update(
                anneal_span="/rustc/0123456789abcdef/library/core/src/panic.rs:58:9: 58:51"
            ),
            "user_code_span": lambda s: (
                s["item_outcomes"]["panic_item"].update(anneal_outcome="panic@src/lib.rs:40:5: 40:9"),
                s["reconciled_panic_sites"][0].update(anneal_span="src/lib.rs:40:5: 40:9"),
            ),
            "miri_outside_lib": lambda s: (
                s["item_outcomes"]["panic_item"].update(miri_outcome="panic@src/main.rs:12:5"),
                s["reconciled_panic_sites"][0].update(batch_miri_pos="src/main.rs:12:5"),
            ),
            "not_kernel_confirmed": lambda s: s["reconciled_panic_sites"][0].update(kernel_confirmed=False),
            "no_frame": lambda s: s["reconciled_panic_sites"][0].update(anneal_panic_frame=None),
            "count_mismatch": lambda s: s.update(reconciled_panic_sites_count=2),
        }
        for label, mutate in cases.items():
            with self.subTest(case=label):
                reasons = site_mutation(mutate)
                self.assertTrue(
                    any(r.startswith("item_accounting_mismatch") for r in reasons), reasons
                )
        # A site listed for an item that agrees strictly is not a reconciliation.
        bogus = _with_consistent_item_outcomes(_make_valid_miri_summary())
        bogus["reconciled_panic_sites"] = [
            {
                "fn_name": "ub_item",
                "batch_miri_pos": "src/lib.rs:41:14",
                "anneal_span": "src/lib.rs:41:9: 41:20",
                "anneal_panic_frame": "f",
                "kernel_confirmed": True,
            }
        ]
        self.assertTrue(
            any(
                "reconciled_panic_sites lists 'ub_item'" in r
                for r in campaign.audit_item_outcomes_against_summary(bogus)
            )
        )

    def test_miri_error_reported_as_agree_is_error_masking(self) -> None:
        summary = _with_consistent_item_outcomes(_make_valid_miri_summary())
        summary["item_outcomes"]["pass_item_1"]["miri_outcome"] = "oracle_error:driver crashed"  # type: ignore[index]
        reasons = campaign.audit_item_outcomes_against_summary(summary)
        self.assertTrue(
            any(
                r.startswith("error_masked_as_unsupported: item 'pass_item_1' reported 'agree'")
                for r in reasons
            ),
            reasons,
        )
        self.assertTrue(
            any(r.startswith("error_masked_as_unsupported: miri_verdicts.error") for r in reasons),
            reasons,
        )
        bad_entry = _with_consistent_item_outcomes(_make_valid_miri_summary())
        bad_entry["item_outcomes"]["pass_item_2"] = {"verdict": "agree"}  # type: ignore[index]
        self.assertTrue(
            any(
                "lacks string miri_outcome / anneal_outcome" in r
                for r in campaign.audit_item_outcomes_against_summary(bad_entry)
            )
        )


class QuarantineKeyAndCoverageTest(unittest.TestCase):
    def _finding(self, repro: Path) -> dict[str, object]:
        return {
            "finding_id": "finding_0000_seed_x__b0_c1",
            "fn_name": "seed_x__b0_c1",
            "seed_name": "seed_x",
            "applied_mutators": ["RawPtrOffsetMutator"],
            "divergence_class": "missed_ub",
            "miri_outcome": "ub@src/lib.rs:4:7",
            "anneal_outcome": "pass:unit",
            "anneal_lean_tag": "MirDiffTag.normalUnit",
            "miri_excerpt": "error: Undefined Behavior",
            "repro_path": str(repro),
            "kernel_confirmed": True,
        }

    def test_every_dedup_quarantine_key_quarantines_and_counts_as_observed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repro = Path(tmp) / "repro.rs"
            repro.write_text("pub fn f() {}\n", encoding="utf-8")
            finding = self._finding(repro)
            fp, keys = campaign.quarantine_match_keys_for_miri_finding(finding, set())
            self.assertEqual(fp, "RawPtrOffsetMutator:missed_ub:MirDiffTag.normalUnit")
            for token in sorted(keys):
                with self.subTest(token=token):
                    _, unq, q = campaign.deduplicate_and_quarantine_findings(
                        [finding], set(), {token}
                    )
                    self.assertEqual((len(unq), len(q)), (0, 1))
                    q_file = Path(tmp) / "q.json"
                    q_file.write_text(json.dumps({"quarantined": [token]}), encoding="utf-8")
                    audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                        quarantine_file=q_file,
                        evaluated_fingerprints=[fp],
                        observed_quarantine_keys=keys,
                        covered_harnesses={"miri"},
                        reference_date="2026-11-09",
                    )
                    self.assertTrue(audit["passed"], audit)
            _, unq, q = campaign.deduplicate_and_quarantine_findings(
                [finding], set(), {"unrelated_seed"}
            )
            self.assertEqual((len(unq), len(q)), (1, 0))

    def test_every_itree_dedup_quarantine_key_quarantines(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            itree = make_healthy_itree_report(
                Path(tmp),
                fingerprints=["CallBoundaryOutliner:itree_outcome_mismatch:TraceReplayDiag.outcome_mismatch"],
            )
            finding = itree["findings"][0]
            fp, keys = campaign.quarantine_match_keys_for_itree_finding(finding)
            self.assertEqual(
                fp, "CallBoundaryOutliner:itree_outcome_mismatch:TraceReplayDiag.outcome_mismatch"
            )
            for token in sorted(keys):
                with self.subTest(token=token):
                    _, unq, q = campaign.deduplicate_and_quarantine_itree_findings([finding], {token})
                    self.assertEqual((len(unq), len(q)), (0, 1))
                    self.assertEqual(campaign.quarantine_entry_harness(token) in (None, "itree"), True)

    def test_unobserved_rule_only_applies_to_covered_harnesses(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q_file = Path(tmp) / "q.json"
            itree_token = "ArithmeticCastMutator:itree_outcome_mismatch:TraceReplayDiag.outcome_mismatch"
            q_file.write_text(json.dumps({"quarantined": [itree_token]}), encoding="utf-8")
            miri_only = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file,
                evaluated_fingerprints=[],
                observed_quarantine_keys=set(),
                covered_harnesses={"miri"},
                reference_date="2026-11-09",
            )
            self.assertTrue(miri_only["passed"], miri_only)
            both = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file,
                evaluated_fingerprints=[],
                observed_quarantine_keys=set(),
                covered_harnesses={"miri", "itree"},
                reference_date="2026-11-09",
            )
            self.assertFalse(both["passed"])
            self.assertIn(
                "unobserved_quarantine_entry",
                both["stale_quarantine_entries"][0]["reason"],
            )
            self.assertEqual(campaign.quarantine_entry_harness(itree_token), "itree")
            self.assertEqual(
                campaign.quarantine_entry_harness("RawPtrOffsetMutator:missed_ub"), "miri"
            )
            self.assertIsNone(campaign.quarantine_entry_harness("pass_ptr_offset_within_array"))
            # No healthy suite evaluated anything: nothing can be unobserved.
            nothing = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file,
                evaluated_fingerprints=[],
                observed_quarantine_keys=set(),
                covered_harnesses=set(),
                reference_date="2026-11-09",
            )
            self.assertTrue(nothing["passed"], nothing)
            # An unmarked (seed-name) token can only match Miri findings: a run whose
            # Miri suite failed (only ITree covered) cannot call it unobserved, a
            # healthy Miri suite can.
            seed_file = Path(tmp) / "q_seed.json"
            seed_file.write_text(json.dumps({"seeds": ["pass_integer_arith_basic"]}), encoding="utf-8")
            for covered, expect_pass in (({"itree"}, True), ({"miri"}, False), ({"miri", "itree"}, False)):
                with self.subTest(covered=sorted(covered)):
                    audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                        quarantine_file=seed_file,
                        evaluated_fingerprints=[],
                        observed_quarantine_keys=set(),
                        covered_harnesses=covered,
                    )
                    self.assertEqual(audit["passed"], expect_pass, audit)

    def test_quarantine_entry_harness_classification(self) -> None:
        expected = {
            "CallBoundaryOutliner": "itree",
            "LayoutPaddingPerturber:itree_step_faulted": "itree",
            "outcome_mismatch": "itree",
            "b0_c1__kernel_step": "itree",
            "itree_seed_3": "itree",
            "BitValidityTransmuteMutator": "miri",
            "TreeBorrowsRetagInterleaver:false_positive_ub": "miri",
            "seed_x:panic_site_mismatch": "miri",
            "s01_checked_add:MirDiffTag.ub": "miri",
            "pass_integer_arith_basic": None,
        }
        for token, harness in expected.items():
            with self.subTest(token=token):
                self.assertEqual(campaign.quarantine_entry_harness(token), harness)

    def test_quarantine_loader_applies_audited_table_entries_but_never_expired_ones(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q_file = Path(tmp) / "quarantine.toml"
            q_file.write_text(
                '[[quarantined]]\n'
                'fingerprint = "RawPtrOffsetMutator:missed_ub:MirDiffTag.normalUnit"\n'
                'expires = "2099-01-01"\n'
                'reason = "tracked"\n'
                '[[quarantined]]\n'
                'fingerprint = "ArithmeticCastMutator:wrong_value:MirDiffTag.normalScalar"\n'
                'expires = "2020-01-01"\n'
                '[[quarantined]]\n'
                'fingerprint = "PlaceProjectionWrapper:missed_ub:MirDiffTag.normalUnit"\n'
                'expires = "not-a-date"\n'
                '[[quarantined]]\n'
                'reason = "missing fingerprint"\n',
                encoding="utf-8",
            )
            rules = campaign.load_quarantine_rules(q_file)
            self.assertEqual(rules, {"RawPtrOffsetMutator:missed_ub:MirDiffTag.normalUnit"})
            j_file = Path(tmp) / "quarantine.json"
            j_file.write_text(
                json.dumps(
                    {
                        "fingerprints": [
                            "legacy_token",
                            {"fingerprint": "A:missed_ub:MirDiffTag.ub", "expires": "2099-12-31"},
                            {"fingerprint": "B:missed_ub:MirDiffTag.ub", "expires": "2001-01-01"},
                        ]
                    }
                ),
                encoding="utf-8",
            )
            self.assertEqual(
                campaign.load_quarantine_rules(j_file),
                {"legacy_token", "A:missed_ub:MirDiffTag.ub"},
            )

    def test_table_entries_need_expiry_to_apply_and_metadata_to_pass_the_audit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q_file = Path(tmp) / "q.json"
            q_file.write_text(
                json.dumps(
                    {
                        "quarantined": [
                            {"fingerprint": "seed_a:missed_ub", "reason": "no expiry"},
                            {"fingerprint": "seed_b:missed_ub", "expires": "2099-01-01"},
                            {"id": "seed_c:missed_ub", "expires": "2099-01-01", "summary": "ok"},
                        ]
                    }
                ),
                encoding="utf-8",
            )
            # A table without `expires` would never lapse: never applied.
            self.assertEqual(
                campaign.load_quarantine_rules(q_file), {"seed_b:missed_ub", "seed_c:missed_ub"}
            )
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file, reference_date="2026-11-09"
            )
            self.assertFalse(audit["passed"])
            by_entry = {}
            for e in audit["stale_quarantine_entries"]:
                by_entry.setdefault(e["entry"], []).append(e["reason"])
            self.assertEqual(sorted(by_entry), ["seed_a:missed_ub", "seed_b:missed_ub"])
            self.assertTrue(by_entry["seed_a:missed_ub"][0].startswith("missing_quarantine_expiry"))
            self.assertTrue(by_entry["seed_b:missed_ub"][0].startswith("missing_quarantine_metadata"))

    def test_loader_and_audit_reject_the_same_malformed_tokens_and_structures(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q_file = Path(tmp) / "q.json"
            q_file.write_text(
                json.dumps(
                    {
                        "quarantined": ["ok:missed_ub", "has space", "empty::segment", "", 7],
                        "seeds": "not_a_list",
                    }
                ),
                encoding="utf-8",
            )
            # No character-splitting of the non-list value, no malformed token applied.
            self.assertEqual(campaign.load_quarantine_rules(q_file), {"ok:missed_ub"})
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file, reference_date="2026-11-09"
            )
            reasons = [e["reason"] for e in audit["stale_entries"]]
            self.assertEqual(sum(r.startswith("malformed_or_missing_fingerprint") for r in reasons), 3)
            self.assertEqual(sum(r.startswith("malformed_quarantine_entry") for r in reasons), 1)
            self.assertIn("malformed_quarantine_file: key 'seeds' must be a list", reasons)
            self.assertEqual(audit["checked_quarantine_count"], 5)

            t_file = Path(tmp) / "q.toml"
            t_file.write_text('quarantined = "fp"\ntests = ["not a table"]\n', encoding="utf-8")
            self.assertEqual(campaign.load_quarantine_rules(t_file), set())
            t_audit = campaign.verify_no_stale_quarantine_or_known_bugs(quarantine_file=t_file)
            t_reasons = " | ".join(e["reason"] for e in t_audit["stale_entries"])
            self.assertIn("key 'quarantined' must be a list", t_reasons)
            self.assertIn("tests[0] must be a table", t_reasons)

    def test_unreadable_or_invalid_quarantine_files_fail_the_audit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            (tmp_path / "bad.json").write_text("{not json", encoding="utf-8")
            (tmp_path / "nan.json").write_text('{"quarantined": [NaN]}', encoding="utf-8")
            (tmp_path / "bad.toml").write_text("quarantined = [", encoding="utf-8")
            (tmp_path / "scalar.json").write_text("42", encoding="utf-8")
            for name, reason in (
                ("bad.json", "malformed_quarantine_file"),
                ("nan.json", "malformed_quarantine_file"),
                ("bad.toml", "malformed_quarantine_file"),
                ("scalar.json", "malformed_quarantine_file: expected list or table"),
                ("absent.json", "quarantine_file_missing"),
            ):
                with self.subTest(file=name):
                    audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                        quarantine_file=tmp_path / name
                    )
                    self.assertFalse(audit["passed"])
                    self.assertIn(reason, audit["stale_entries"][0]["reason"])
            with self.assertRaises(ValueError):
                campaign.load_quarantine_rules(tmp_path / "nan.json")
            with self.assertRaises(ValueError):
                campaign.load_quarantine_rules(tmp_path / "scalar.json")

    def test_unknown_top_level_keys_fail_closed_even_beside_valid_keys(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q_file = Path(tmp) / "q.json"
            q_file.write_text(
                json.dumps({"quarantined": ["seed_x:missed_ub"], "quarantned": ["typo:missed_ub"]}),
                encoding="utf-8",
            )
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(quarantine_file=q_file)
            self.assertFalse(audit["passed"])
            self.assertEqual(
                [e["reason"] for e in audit["stale_entries"]],
                ["malformed_quarantine_file: unrecognized quarantine keys ['quarantned']"],
            )
            # The manifest itself (metadata keys plus `[[tests]]`) is a valid
            # quarantine file: none of its keys are unknown.
            manifest_audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=LIVE_MANIFEST
            )
            self.assertTrue(manifest_audit["passed"], manifest_audit)
            self.assertEqual(
                manifest_audit["checked_quarantine_count"], len(_live_manifest_known_bug_names())
            )

    def test_quarantine_keys_unified_between_loader_and_ratchet_audit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            # JSON `seeds` and `mutators` must be audited by `verify_no_stale_quarantine_or_known_bugs`
            # just like `quarantined` and `fingerprints`.
            j_file = Path(tmp) / "q_seeds.json"
            j_file.write_text(
                json.dumps(
                    {
                        "seeds": ["pass_integer_arith_basic"],
                        "mutators": ["RawPtrOffsetMutator"],
                    }
                ),
                encoding="utf-8",
            )
            self.assertEqual(
                campaign.load_quarantine_rules(j_file),
                {"pass_integer_arith_basic", "RawPtrOffsetMutator"},
            )
            audit_unobs = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=j_file,
                evaluated_fingerprints=[],
                observed_quarantine_keys=set(),
                covered_harnesses={"miri"},
                reference_date="2026-11-09",
            )
            self.assertFalse(audit_unobs["passed"])
            self.assertEqual(audit_unobs["checked_quarantine_count"], 2)

            # TOML `entries` and `rules` must be loaded by `load_quarantine_rules` too.
            t_file = Path(tmp) / "q_entries.toml"
            t_file.write_text(
                'entries = ["RawPtrOffsetMutator:missed_ub"]\n'
                'rules = ["ArithmeticCastMutator:wrong_value"]\n',
                encoding="utf-8",
            )
            self.assertEqual(
                campaign.load_quarantine_rules(t_file),
                {"RawPtrOffsetMutator:missed_ub", "ArithmeticCastMutator:wrong_value"},
            )

            # Unrecognized quarantine dictionary keys fail closed.
            bad_file = Path(tmp) / "q_typo.json"
            bad_file.write_text(
                json.dumps({"quarantned": ["RawPtrOffsetMutator:missed_ub"]}),
                encoding="utf-8",
            )
            audit_bad = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=bad_file,
                reference_date="2026-11-09",
            )
            self.assertFalse(audit_bad["passed"])
            self.assertTrue(
                any("unrecognized quarantine keys" in e["reason"] for e in audit_bad["stale_entries"])
            )

    def test_resolved_history_map_flags_resolved_entries_unless_observed_again(self) -> None:
        fp = "PlaceProjectionWrapper:missed_ub:MirDiffTag.normalScalar"
        ledger = {
            "active_fingerprints": [],
            "resolved_history": {
                fp: {
                    "first_seen_date": "2026-10-01",
                    "last_seen_date": "2026-10-05",
                    "campaigns_failing": 2,
                    "resolved_date": "2026-10-06",
                    "suite": "miri-difftest",
                }
            },
        }
        with tempfile.TemporaryDirectory() as tmp:
            q_file = Path(tmp) / "q.json"
            q_file.write_text(json.dumps({"quarantined": [fp]}), encoding="utf-8")
            stale = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file, ledger=ledger
            )
            self.assertFalse(stale["passed"])
            self.assertTrue(
                stale["stale_entries"][0]["reason"].startswith("already_resolved_in_ledger")
            )
            # Observed again in this run: a regression, not a stale entry.
            regressed = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file,
                ledger=ledger,
                evaluated_fingerprints=[fp],
                observed_quarantine_keys={fp},
                covered_harnesses={"miri"},
            )
            self.assertTrue(regressed["passed"], regressed)

    def test_identity_run_wires_manifest_eval_results_into_stale_ratchet(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            m_file = Path(tmp) / "manifest.toml"
            m_file.write_text(
                '[[tests]]\n'
                'name = "pass_direct_fn_call"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "externalCall:miri_diff_corpus::helper_add_ten"\n'
                'summary = "unlinked intra-crate callee"\n',
                encoding="utf-8",
            )
            summary = _with_consistent_item_outcomes(
                _make_valid_miri_summary(), direct_call="external_call"
            )
            summary["mode"] = "identity"
            ok, reasons = campaign.validate_error_vs_unsupported_boundary(summary)
            self.assertTrue(ok, reasons)
            extracted = campaign.extract_manifest_eval_results_from_miri_summary(summary, m_file)
            audit_ok = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_file,
                manifest_eval_results=extracted,
                reference_date="2026-11-09",
            )
            self.assertTrue(audit_ok["passed"], audit_ok)

            # Now suppose the bug was fixed and `pass_direct_fn_call` agrees in identity mode.
            summary = _with_consistent_item_outcomes(
                _make_valid_miri_summary(), direct_call="agree"
            )
            summary["mode"] = "identity"
            ok, reasons = campaign.validate_error_vs_unsupported_boundary(summary)
            self.assertTrue(ok, reasons)
            state_dir = Path(tmp) / "state"
            with mock.patch.object(campaign, "run_harness", return_value=summary):
                rc = _quiet_main(
                    [
                        "--profile",
                        "smoke",
                        "--miri-only",
                        "--miri-identity",
                        "--check-stale-ratchet",
                        "--manifest-path",
                        str(m_file),
                        "--state-dir",
                        str(state_dir),
                    ]
                )
            self.assertEqual(rc, campaign.EXIT_HARNESS_FAILED)
            report = _read_summary(state_dir)
            self.assertFalse(report["stale_ratchet_audit"]["passed"])
            self.assertTrue(
                any(
                    "stale_known_anneal_bug_now_passes" in e["reason"]
                    for e in report["stale_ratchet_audit"]["stale_known_anneal_bugs"]
                )
            )
            # The harness failure is due to the ratchet alone, not to the red flags.
            self.assertTrue(report["red_flags"]["passed"], report["red_flags"])
            report_md = (state_dir / "reports" / "LATEST_REPORT.md").read_text(encoding="utf-8")
            self.assertIn("GATE FAILED", report_md)

    def test_identity_run_with_reconciled_panic_site_passes_the_audit_and_ratchet(self) -> None:
        # `panic_explicit_macro`'s identity agreement rests on the harness's panic-site
        # reconciliation; the per-item audit must accept it instead of failing every
        # `--miri-identity` run.
        with tempfile.TemporaryDirectory() as tmp:
            summary = _with_reconciled_panic_macro_item(
                _with_consistent_item_outcomes(_make_valid_miri_summary(), direct_call="agree")
            )
            summary["mode"] = "identity"
            state_dir = Path(tmp) / "state"
            with mock.patch.object(campaign, "run_harness", return_value=summary):
                rc = _quiet_main(
                    [
                        "--profile",
                        "smoke",
                        "--miri-only",
                        "--miri-identity",
                        "--check-stale-ratchet",
                        "--state-dir",
                        str(state_dir),
                    ]
                )
            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            report = _read_summary(state_dir)
            self.assertTrue(report["red_flags"]["checks"]["error_vs_unsupported_boundary"])
            self.assertTrue(report["stale_ratchet_audit"]["passed"], report["stale_ratchet_audit"])

    def test_identity_summary_without_item_outcomes_never_fabricates_agree_verdicts(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            m_file = Path(tmp) / "manifest.toml"
            m_file.write_text(
                '[[tests]]\n'
                'name = "ub_not_evaluated_in_this_run"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'summary = "open bug"\n',
                encoding="utf-8",
            )
            # A fully compared identity summary from a harness that does not emit
            # `item_outcomes`: nothing is known about `ub_not_evaluated_in_this_run`.
            summary = _make_valid_miri_summary()
            summary["mode"] = "identity"
            summary["anneal_outcomes"]["unsupported"] = 0  # type: ignore[index]
            summary["anneal_outcomes"]["pass"] = 6  # type: ignore[index]
            summary["not_compared_reasons"]["unsupported"] = 0  # type: ignore[index]
            summary["not_compared_count"] = 0
            summary["compared_candidates"] = 8
            summary["agree_count"] = 8
            self.assertIsNone(
                campaign.extract_manifest_eval_results_from_miri_summary(summary, m_file)
            )
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_file,
                manifest_eval_results=campaign.extract_manifest_eval_results_from_miri_summary(
                    summary, m_file
                ),
                reference_date="2026-11-09",
            )
            self.assertTrue(audit["passed"], audit)

            # A divergent identity finding is still reported under its test name.
            with_finding = dict(summary)
            with_finding["findings"] = [
                {
                    "fn_name": "ub_not_evaluated_in_this_run",
                    "seed_name": "ub_not_evaluated_in_this_run",
                    "divergence_class": "missed_ub",
                    "anneal_outcome": "pass:unit",
                    "anneal_lean_tag": "MirDiffTag.normalUnit",
                }
            ]
            extracted = campaign.extract_manifest_eval_results_from_miri_summary(with_finding)
            self.assertEqual(
                extracted,
                {
                    "ub_not_evaluated_in_this_run": {
                        "verdict": "diverge",
                        "divergence_class": "missed_ub",
                        "anneal_outcome": "pass:unit",
                        "anneal_lean_tag": "MirDiffTag.normalUnit",
                    }
                },
            )
            mismatch = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_file,
                manifest_eval_results=extracted,
                reference_date="2026-11-09",
            )
            self.assertFalse(mismatch["passed"])
            self.assertIn(
                "stale_known_anneal_bug_tag_mismatch",
                mismatch["stale_known_anneal_bugs"][0]["reason"],
            )

    def test_external_call_and_out_of_fuel_error_masking_rejected(self) -> None:
        for key in ("external_call", "out_of_fuel"):
            with self.subTest(key=key):
                summary = _make_valid_miri_summary()
                summary["not_compared_reasons"][key] = 1  # type: ignore[index]
                summary["anneal_outcomes"][key] = 0  # type: ignore[index]
                ok, reasons = campaign.validate_error_vs_unsupported_boundary(summary)
                self.assertFalse(ok)
                self.assertTrue(
                    any(f"not_compared_reasons.{key}" in r for r in reasons),
                    reasons,
                )

    def test_bare_middle_segment_token_does_not_bypass_unobserved_quarantine_audit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repro = Path(tmp) / "repro.rs"
            repro.write_text("pub fn f() {}\n", encoding="utf-8")
            finding = self._finding(repro)
            fp, keys = campaign.quarantine_match_keys_for_miri_finding(finding, set())
            # `"missed_ub"` is not a valid match key in `quarantine_match_keys_for_miri_finding`
            # and therefore does not quarantine `finding`.
            self.assertNotIn("missed_ub", keys)
            _, unq, q = campaign.deduplicate_and_quarantine_findings(
                [finding], set(), {"missed_ub"}
            )
            self.assertEqual((len(unq), len(q)), (1, 0))
            q_file = Path(tmp) / "q_dead.json"
            q_file.write_text(json.dumps({"quarantined": ["missed_ub"]}), encoding="utf-8")
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file,
                evaluated_fingerprints=[fp],
                observed_quarantine_keys=keys,
                covered_harnesses={"miri"},
                reference_date="2026-11-09",
            )
            self.assertFalse(audit["passed"])
            self.assertIn(
                "unobserved_quarantine_entry",
                audit["stale_quarantine_entries"][0]["reason"],
            )

    def test_tests_entry_that_quarantined_a_finding_is_not_reported_unobserved(self) -> None:
        # A `[[tests]]` known_anneal_bug entry with `expires` but no `divergence_class`
        # is applied by `load_quarantine_rules` as the bare test name; the audit must check
        # that same token (it quarantined the run's finding), not a synthesized one.
        with tempfile.TemporaryDirectory() as tmp:
            repro = Path(tmp) / "repro.rs"
            repro.write_text("pub fn f() {}\n", encoding="utf-8")
            q_file = Path(tmp) / "q.toml"
            q_file.write_text(
                '[[tests]]\n'
                'name = "seed_x"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'summary = "tracked"\n'
                'expires = "2099-01-01"\n',
                encoding="utf-8",
            )
            finding = self._finding(repro)
            finding["seed_name"] = "seed_x"
            finding["fn_name"] = "seed_x__b0_c1"
            finding["applied_mutators"] = []
            rules = campaign.load_quarantine_rules(q_file)
            self.assertEqual(rules, {"seed_x"})
            _, unq, q = campaign.deduplicate_and_quarantine_findings([finding], set(), rules)
            self.assertEqual((len(unq), len(q)), (0, 1))
            fp, keys = campaign.quarantine_match_keys_for_miri_finding(finding, set())
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file,
                evaluated_fingerprints=[fp],
                observed_quarantine_keys=keys,
                covered_harnesses={"miri"},
                reference_date="2026-11-09",
            )
            self.assertTrue(audit["passed"], audit)
            self.assertEqual(audit["checked_quarantine_count"], 1)
            # Once it expires it is reported (and no longer applied by the loader).
            expired = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file,
                evaluated_fingerprints=[fp],
                observed_quarantine_keys=keys,
                covered_harnesses={"miri"},
                reference_date="2099-06-01",
            )
            self.assertFalse(expired["passed"])
            self.assertIn("expired_quarantine_entry", expired["stale_entries"][0]["reason"])

    def test_quarantine_tests_known_anneal_bug_entries_audited_and_validated(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q_valid = Path(tmp) / "q_valid.toml"
            q_valid.write_text(
                '[[tests]]\n'
                'name = "valid_seed"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_bug_class = "incompleteness"\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'divergence_class = "missed_ub"\n'
                'expires = "2099-01-01"\n'
                'summary = "tracked bug"\n',
                encoding="utf-8",
            )
            # When `divergence_class` is present, only `valid_seed:missed_ub` is loaded
            # (not bare `valid_seed`, which would over-quarantine other divergence classes)
            # and observing `valid_seed:missed_ub` satisfies the 1-entry audit.
            self.assertEqual(campaign.load_quarantine_rules(q_valid), {"valid_seed:missed_ub"})
            valid_audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_valid,
                evaluated_fingerprints=[],
                observed_quarantine_keys={"valid_seed:missed_ub"},
                covered_harnesses={"miri"},
                reference_date="2026-11-09",
            )
            self.assertTrue(valid_audit["passed"], valid_audit)
            self.assertEqual(valid_audit["checked_quarantine_count"], 1)

            q_file = Path(tmp) / "q_tests.toml"
            q_file.write_text(
                '[[tests]]\n'
                'name = "valid_seed"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_bug_class = "incompleteness"\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'divergence_class = "missed_ub"\n'
                'expires = "2099-01-01"\n'
                'summary = "tracked bug"\n'
                '\n'
                '[[tests]]\n'
                'name = "expired_seed"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'divergence_class = "missed_ub"\n'
                'expires = "2020-01-01"\n'
                'summary = "expired"\n'
                '\n'
                '[[tests]]\n'
                'name = "missing_meta_seed"\n'
                '[tests.known_anneal_bug]\n'
                'divergence_class = "missed_ub"\n'
                '\n'
                '[[tests]]\n'
                'name = "bad_class_seed"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'divergence_class = "not_a_real_class"\n'
                'summary = "bad class"\n',
                encoding="utf-8",
            )
            rules = campaign.load_quarantine_rules(q_file)
            self.assertEqual(rules, {"valid_seed:missed_ub"})
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file,
                evaluated_fingerprints=[],
                observed_quarantine_keys=set(),
                covered_harnesses={"miri"},
                reference_date="2026-11-09",
            )
            self.assertFalse(audit["passed"])
            self.assertEqual(audit["checked_quarantine_count"], 4)
            reasons = " | ".join(e["reason"] for e in audit["stale_quarantine_entries"])
            self.assertIn("expired_quarantine_entry", reasons)
            self.assertIn("missing_known_anneal_bug_metadata", reasons)
            self.assertIn("invalid divergence_class", reasons)
            self.assertIn("unobserved_quarantine_entry", reasons)

    def test_json_quarantine_tests_entries_match_toml_semantics(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q_file = Path(tmp) / "q.json"
            q_file.write_text(
                json.dumps(
                    {
                        "tests": [
                            {"name": "plain_test", "miri_verdict": "pass:unit"},
                            {
                                "name": "seed_y",
                                "known_anneal_bug": {
                                    "observed_anneal_tag": "MirDiffTag.ub",
                                    "summary": "tracked",
                                },
                            },
                        ]
                    }
                ),
                encoding="utf-8",
            )
            self.assertEqual(campaign.load_quarantine_rules(q_file), {"seed_y"})
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(quarantine_file=q_file)
            self.assertTrue(audit["passed"], audit)
            self.assertEqual(audit["checked_quarantine_count"], 1)

    def test_mutator_tokens_of_current_mutators_attribute_findings(self) -> None:
        expected = {
            "__null_p": "RawPtrOffsetMutator",
            "__unaligned_pair": "RawPtrOffsetMutator",
            "__u8_base": "RawPtrOffsetMutator",
            "__panic_arr": "BitValidityTransmuteMutator",
            "__panic_idx": "BitValidityTransmuteMutator",
            "__ovf_a": "ArithmeticCastMutator",
            "__udf_a": "ArithmeticCastMutator",
            "__div_a": "ArithmeticCastMutator",
            "__shl_v": "ArithmeticCastMutator",
            "__ub_step": "ArithmeticCastMutator",
            "__dangling_ptr": "PlaceProjectionWrapper",
            "__dead_slot": "PlaceProjectionWrapper",
        }
        for token, mutator in expected.items():
            with self.subTest(token=token):
                finding = {
                    "seed_name": "seed_z",
                    "applied_mutators": ["TreeBorrowsRetagInterleaver"],
                    "mutant_source": (
                        "pub fn seed_z__b0_c0() -> u32 {\n"
                        f"    let {token}: u32 = 1u32;\n"
                        f"    let __probe: u32 = {token};\n"
                        "    __probe\n"
                        "}\n"
                    ),
                    "miri_pos": "src/lib.rs:3:5",
                }
                self.assertTrue(any(t in token for t in campaign.ALL_MIRI_MUTATOR_TOKENS))
                self.assertEqual(campaign.infer_finding_cause(finding, set()), mutator)


class GateProfileAndModeTest(unittest.TestCase):
    """`nightly` enables both gates by default (with `--no-*` opt-outs); other
    profiles keep them opt-in; requesting gates without a harness selection runs
    them alone."""

    def setUp(self) -> None:
        campaign.LAST_HARNESS_DIAGNOSTICS.clear()

    def test_resolve_gate_flags_per_profile_and_override(self) -> None:
        for profile_name in sorted(campaign.PROFILES):
            for argv_extra, expect in (
                ([], (profile_name == "nightly", profile_name == "nightly")),
                (["--self-check-mutants"], (True, profile_name == "nightly")),
                (["--no-self-check-mutants"], (False, profile_name == "nightly")),
                (["--check-stale-ratchet"], (profile_name == "nightly", True)),
                (["--no-check-stale-ratchet"], (profile_name == "nightly", False)),
                (["--no-self-check-mutants", "--no-check-stale-ratchet"], (False, False)),
                (["--self-check-mutants", "--check-stale-ratchet"], (True, True)),
            ):
                with self.subTest(profile=profile_name, extra=argv_extra):
                    args = campaign.parse_args(["--profile", profile_name, *argv_extra])
                    self.assertEqual(
                        campaign.resolve_gate_flags(args, campaign.PROFILES[args.profile]), expect
                    )
        default_args = campaign.parse_args([])
        self.assertEqual(default_args.profile, "quick")
        self.assertFalse(default_args.explicit_profile)
        self.assertEqual(
            campaign.resolve_gate_flags(default_args, campaign.PROFILES["quick"]), (False, False)
        )

    def test_standalone_gate_mode_selection(self) -> None:
        cases = [
            (["--self-check-mutants"], True),
            (["--check-stale-ratchet"], True),
            (["--self-check-mutants", "--check-stale-ratchet", "--quarantine-file", "q.json"], True),
            (["--no-self-check-mutants", "--no-check-stale-ratchet"], False),
            ([], False),
            (["--self-check-mutants", "--profile", "quick"], False),
            (["--self-check-mutants", "--profile", "nightly"], False),
            (["--self-check-mutants", "--miri-seed", "0x1"], False),
            (["--self-check-mutants", "--itree-seed", "0x1"], False),
            (["--self-check-mutants", "--miri-identity"], False),
            (["--self-check-mutants", "--miri-only"], False),
            (["--self-check-mutants", "--compile-only"], False),
            (["--self-check-mutants", "--remote-uri", "/remote/x"], False),
            (["--self-check-mutants", "--junit-xml", "out.xml"], False),
        ]
        for argv, expect in cases:
            with self.subTest(argv=argv):
                self.assertEqual(
                    campaign.is_standalone_gate_invocation(campaign.parse_args(argv)), expect
                )

    def _run_profile(self, state_dir: Path, *argv: str) -> int:
        def fake_run_harness(repo_root, bin_name, harness_args, json_path):
            healthy_diag(bin_name)
            if bin_name == "miri-difftest":
                return make_healthy_miri_report(state_dir)
            return make_healthy_itree_report(state_dir)

        with mock.patch.object(campaign, "run_harness", side_effect=fake_run_harness):
            return _quiet_main(["--state-dir", str(state_dir), "--remote-uri", "", *argv])

    def test_nightly_enables_both_gates_by_default_and_records_them(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            junit = state_dir / "junit.xml"
            rc = self._run_profile(state_dir, "--profile", "nightly", "--junit-xml", str(junit))
            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            summary = _read_summary(state_dir)
            self.assertEqual(
                summary["gates"],
                {"passed": True, "self_check_mutants": True, "check_stale_ratchet": True},
            )
            self.assertEqual(summary["semantic_mutant_self_check"]["killed_count"], 5)
            self.assertTrue(summary["stale_ratchet_audit"]["passed"])
            self.assertEqual(
                summary["stale_ratchet_audit"]["checked_known_bug_count"],
                len(_live_manifest_known_bug_names()),
            )
            report_md = (state_dir / "reports" / "LATEST_REPORT.md").read_text(encoding="utf-8")
            self.assertIn("## Semantic-Mutant Self-Check (`--self-check-mutants`)", report_md)
            self.assertIn("## Stale Quarantine & Known-Bug Ratchet Audit", report_md)
            junit_xml = junit.read_text(encoding="utf-8")
            self.assertIn('name="semantic-mutant-self-check"', junit_xml)
            self.assertIn('name="stale-ratchet-audit"', junit_xml)
            self.assertIn('failures="0"', junit_xml)

    def test_nightly_opt_outs_and_other_profiles_leave_gates_off(self) -> None:
        for argv in (
            ["--profile", "nightly", "--no-self-check-mutants", "--no-check-stale-ratchet"],
            ["--profile", "smoke"],
            ["--profile", "quick"],
            ["--profile", "weekend"],
        ):
            with self.subTest(argv=argv), tempfile.TemporaryDirectory() as tmp:
                state_dir = Path(tmp)
                with mock.patch.object(
                    campaign, "run_semantic_mutant_self_check", side_effect=AssertionError("ran")
                ), mock.patch.object(
                    campaign,
                    "verify_no_stale_quarantine_or_known_bugs",
                    side_effect=AssertionError("ran"),
                ):
                    rc = self._run_profile(state_dir, *argv)
                self.assertEqual(rc, campaign.EXIT_SUCCESS)
                summary = _read_summary(state_dir)
                self.assertNotIn("gates", summary)
                self.assertNotIn("semantic_mutant_self_check", summary)
                self.assertNotIn("stale_ratchet_audit", summary)
        with tempfile.TemporaryDirectory() as tmp:
            # Only one of the two nightly gates opted out.
            rc = self._run_profile(Path(tmp), "--profile", "nightly", "--no-check-stale-ratchet")
            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            summary = _read_summary(Path(tmp))
            self.assertEqual(
                summary["gates"],
                {"passed": True, "self_check_mutants": True, "check_stale_ratchet": False},
            )

    def test_failing_gate_turns_a_healthy_campaign_into_exit_2_but_commits_the_ledger(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            write_initial_ledger(state_dir, active_fingerprints=[])
            q_file = state_dir / "q.json"
            q_file.write_text(
                json.dumps({"quarantined": ["RawPtrOffsetMutator:missed_ub:MirDiffTag.ub"]}),
                encoding="utf-8",
            )
            junit = state_dir / "junit.xml"
            rc = self._run_profile(
                state_dir,
                "--profile",
                "nightly",
                "--quarantine-file",
                str(q_file),
                "--junit-xml",
                str(junit),
            )
            self.assertEqual(rc, campaign.EXIT_HARNESS_FAILED)
            summary = _read_summary(state_dir)
            self.assertTrue(summary["red_flags"]["passed"], summary["red_flags"])
            self.assertFalse(summary["gates"]["passed"])
            self.assertEqual(
                [e["reason"].split(":", 1)[0] for e in summary["stale_ratchet_audit"]["stale_entries"]],
                ["unobserved_quarantine_entry"],
            )
            report_md = (state_dir / "reports" / "LATEST_REPORT.md").read_text(encoding="utf-8")
            self.assertIn("Status: GATE FAILED (campaign verdict: PASS (0 divergences))", report_md)
            self.assertIn('<testcase classname="anneal_difftest" name="stale-ratchet-audit">', junit.read_text(encoding="utf-8"))
            self.assertIn('failures="1"', junit.read_text(encoding="utf-8"))
            # Both suites were healthy, so their ledger state is still committed.
            ledger = read_ledger(state_dir)
            self.assertEqual(ledger["per_suite_runs"], {"miri": 11, "itree": 11})

    def test_malformed_quarantine_file_with_ratchet_runs_without_rules_and_fails(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            q_file = state_dir / "q.json"
            q_file.write_text("{broken", encoding="utf-8")
            rc = self._run_profile(
                state_dir, "--profile", "smoke", "--check-stale-ratchet", "--quarantine-file", str(q_file)
            )
            self.assertEqual(rc, campaign.EXIT_HARNESS_FAILED)
            summary = _read_summary(state_dir)
            self.assertTrue(summary["red_flags"]["passed"])
            self.assertIn(
                "malformed_quarantine_file",
                summary["stale_ratchet_audit"]["stale_entries"][0]["reason"],
            )
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            q_file = state_dir / "q.json"
            q_file.write_text("{broken", encoding="utf-8")
            with mock.patch.object(campaign, "run_harness", side_effect=AssertionError("ran")):
                rc = _quiet_main(
                    ["--profile", "smoke", "--state-dir", str(state_dir), "--quarantine-file", str(q_file)]
                )
            self.assertEqual(rc, campaign.EXIT_HARNESS_FAILED)
            self.assertFalse((state_dir / "reports").exists())

    def test_compile_only_and_harness_failure_paths_still_run_requested_gates(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)

            def compile_only(repo_root, bin_name, harness_args, json_path):
                healthy_diag(bin_name)
                return {
                    "harness": bin_name,
                    "oracle_comparison": "not_performed",
                    "total_candidates": 8,
                    "compiled_candidates": 8,
                    "opt_level_0_and_2_compiled": 8,
                }

            junit = state_dir / "junit.xml"
            with mock.patch.object(campaign, "run_harness", side_effect=compile_only):
                rc = _quiet_main(
                    [
                        "--profile",
                        "nightly",
                        "--compile-only",
                        "--state-dir",
                        str(state_dir),
                        "--remote-uri",
                        "",
                        "--junit-xml",
                        str(junit),
                    ]
                )
            self.assertEqual(rc, campaign.EXIT_NOT_EVALUATED)
            report_md = (state_dir / "reports" / "LATEST_REPORT.md").read_text(encoding="utf-8")
            self.assertIn("## Semantic-Mutant Self-Check", report_md)
            self.assertIn("## Stale Quarantine & Known-Bug Ratchet Audit", report_md)
            junit_xml = junit.read_text(encoding="utf-8")
            # Two not-evaluated harness failures plus two passing gate cases.
            self.assertIn('tests="4"', junit_xml)
            self.assertIn('failures="2"', junit_xml)
            self.assertIn('name="semantic-mutant-self-check"', junit_xml)
            self.assertIn('name="stale-ratchet-audit"', junit_xml)

            with mock.patch.object(
                campaign,
                "run_semantic_mutant_self_check",
                return_value={"passed": False, "total_mutants": 5, "killed_count": 4, "survived_mutants": ["x"], "results": []},
            ), mock.patch.object(campaign, "run_harness", side_effect=compile_only):
                rc_fail = _quiet_main(
                    ["--profile", "nightly", "--compile-only", "--state-dir", str(state_dir), "--remote-uri", ""]
                )
            self.assertEqual(rc_fail, campaign.EXIT_HARNESS_FAILED)

            with mock.patch.object(campaign, "run_harness", return_value=None):
                rc_crash = _quiet_main(
                    ["--profile", "smoke", "--self-check-mutants", "--state-dir", str(state_dir), "--remote-uri", ""]
                )
            self.assertEqual(rc_crash, campaign.EXIT_HARNESS_FAILED)
            report_md = (state_dir / "reports" / "LATEST_REPORT.md").read_text(encoding="utf-8")
            self.assertIn("## Semantic-Mutant Self-Check", report_md)

    def test_standalone_gate_leaves_ledger_and_ratchet_untouched(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp)
            fp = "PlaceProjectionWrapper:missed_ub:MirDiffTag.normalScalar"
            ledger_path = write_initial_ledger(
                state_dir,
                resolved_history={
                    fp: {"first_seen_date": "2026-10-01", "last_seen_date": "2026-10-02",
                         "campaigns_failing": 1, "resolved_date": "2026-10-03", "suite": "miri-difftest"}
                },
            )
            ratchet_path = state_dir / "state" / "coverage_ratchet.json"
            ratchet_path.write_text('{"schema_version": 1, "observed_paths": {}}\n', encoding="utf-8")
            before = (ledger_path.read_bytes(), ratchet_path.read_bytes())
            with mock.patch.object(campaign, "run_harness", side_effect=AssertionError("ran")):
                rc = _quiet_main(["--self-check-mutants", "--check-stale-ratchet", "--state-dir", str(state_dir)])
            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            self.assertEqual((ledger_path.read_bytes(), ratchet_path.read_bytes()), before)
            reports = sorted(p.name for p in (state_dir / "reports").iterdir())
            self.assertEqual(
                [n for n in reports if not n.startswith("20")],
                ["LATEST_CAMPAIGN_SUMMARY.json", "LATEST_REPORT.md"],
            )
            self.assertEqual(len(reports), 4)

            # A quarantine entry the ledger already resolved fails the standalone gate.
            q_file = state_dir / "q.json"
            q_file.write_text(json.dumps({"quarantined": [fp]}), encoding="utf-8")
            rc_stale = _quiet_main(
                ["--check-stale-ratchet", "--quarantine-file", str(q_file), "--state-dir", str(state_dir)]
            )
            self.assertEqual(rc_stale, campaign.EXIT_HARNESS_FAILED)
            self.assertTrue(
                _read_summary(state_dir)["stale_ratchet_audit"]["stale_entries"][0]["reason"].startswith(
                    "already_resolved_in_ledger"
                )
            )
            self.assertEqual((ledger_path.read_bytes(), ratchet_path.read_bytes()), before)


class PassB1AdversarialRegressionTest(unittest.TestCase):
    """Regression tests for Pass B1 audit findings across the Miri/ITree error boundaries,
    oracle tag classification, item-outcome accounting, stale-ratchet audit, and
    semantic-mutant self-check."""

    def test_reconciled_panic_site_rejects_foreign_frame_and_prefixed_miri_path(self) -> None:
        base = _with_reconciled_panic_macro_item(
            _with_consistent_item_outcomes(_make_valid_miri_summary())
        )
        # 1. A frame belonging to std/core or another function must not reconcile `panic_item`.
        for bad_frame in (
            "core::panicking::panic_fmt",
            "miri_diff_corpus::other_item",
            "panic_item_other",
        ):
            with self.subTest(frame=bad_frame):
                s = copy.deepcopy(base)
                s["reconciled_panic_sites"][0]["anneal_panic_frame"] = bad_frame
                reasons = campaign.audit_item_outcomes_against_summary(s)
                self.assertTrue(
                    any("item_accounting_mismatch" in r for r in reasons),
                    f"{bad_frame}: {reasons}",
                )

        # 2. `batch_miri_pos` in `miri_eval.rs` must normalize to `"src/lib.rs"`, not an
        #    arbitrary absolute prefix `/tmp/other/src/lib.rs`.
        s_path = copy.deepcopy(base)
        s_path["item_outcomes"]["panic_item"]["miri_outcome"] = "panic@/tmp/other/src/lib.rs:12:5"
        s_path["reconciled_panic_sites"][0]["batch_miri_pos"] = "/tmp/other/src/lib.rs:12:5"
        reasons_path = campaign.audit_item_outcomes_against_summary(s_path)
        self.assertTrue(any("item_accounting_mismatch" in r for r in reasons_path), reasons_path)

        # 3. Non-zero `reconciled_panic_sites_count` when `reconciled_panic_sites` is omitted
        #    or boolean `reconciled_panic_sites_count = True` must fail closed.
        s_no_list = _with_consistent_item_outcomes(_make_valid_miri_summary())
        s_no_list["reconciled_panic_sites_count"] = 1
        self.assertTrue(
            any(
                "reconciled_panic_sites_count" in r
                for r in campaign.audit_item_outcomes_against_summary(s_no_list)
            )
        )
        s_bool_cnt = copy.deepcopy(base)
        s_bool_cnt["reconciled_panic_sites_count"] = True
        self.assertTrue(
            any(
                "reconciled_panic_sites_count" in r
                for r in campaign.audit_item_outcomes_against_summary(s_bool_cnt)
            )
        )

    def test_item_outcomes_non_dict_and_lean_tag_contradictions_fail_closed(self) -> None:
        # Non-dict `item_outcomes` must not silently return `[]`.
        s_list = _make_valid_miri_summary()
        s_list["item_outcomes"] = []
        reasons = campaign.audit_item_outcomes_against_summary(s_list)
        self.assertTrue(any("item_outcomes is not a dict" in r for r in reasons), reasons)

        # `anneal_lean_tag == "none"` masked under `anneal_outcome: "unsupported@..."` is an
        # Anneal capture/Lean error disguised as unsupported.
        s_masked = _with_consistent_item_outcomes(_make_valid_miri_summary())
        s_masked["item_outcomes"]["pass_direct_fn_call"]["anneal_lean_tag"] = "none"  # type: ignore[index]
        reasons_masked = campaign.audit_item_outcomes_against_summary(s_masked)
        self.assertTrue(
            any(r.startswith("error_masked_as_unsupported") for r in reasons_masked),
            reasons_masked,
        )

        # Contradictory `anneal_lean_tag` vs `anneal_outcome` (e.g. `MirDiffTag.ub` on `pass:unit`).
        s_contradict = _with_consistent_item_outcomes(_make_valid_miri_summary())
        s_contradict["item_outcomes"]["pass_item_0"]["anneal_lean_tag"] = "MirDiffTag.ub"  # type: ignore[index]
        reasons_contradict = campaign.audit_item_outcomes_against_summary(s_contradict)
        self.assertTrue(
            any("does not match anneal_outcome" in r for r in reasons_contradict),
            reasons_contradict,
        )

    def test_classify_oracle_outcome_tags_strict_pass_and_error_precedence(self) -> None:
        # `pass:` tags never carry `@span` suffixes and must not have `@...` stripped.
        self.assertEqual(
            campaign.classify_oracle_outcome_tags("pass:unit@a", "pass:unit@b"),
            ("not_compared", "miri_oracle_error"),
        )
        self.assertEqual(
            campaign.classify_oracle_outcome_tags("pass:unit", "pass:unit@b"),
            ("not_compared", "capture_failed"),
        )
        # Scalar bits > u128::MAX or size == 0 are not valid `pass:scalar` tags and never agree.
        self.assertEqual(
            campaign.classify_oracle_outcome_tags(
                f"pass:scalar:{1 << 128}:4", f"pass:scalar:{1 << 128}:4"
            ),
            ("diverge", "wrong_value"),
        )
        self.assertEqual(
            campaign.classify_oracle_outcome_tags("pass:scalar:1:0", "pass:scalar:1:0"),
            ("diverge", "wrong_value"),
        )
        # Unrecognized Miri error tag takes precedence over Anneal `unsupported` / `capture_error`.
        self.assertEqual(
            campaign.classify_oracle_outcome_tags(
                "error:miri_driver_failed", "unsupported@src/lib.rs:1:1: 1:5"
            ),
            ("not_compared", "miri_oracle_error"),
        )
        # Unrecognized Anneal error tag is `("not_compared", "capture_failed")`, matching
        # `audit_item_outcomes_against_summary`'s `anneal_counts["error"]`.
        self.assertEqual(
            campaign.classify_oracle_outcome_tags("pass:unit", "error:lean_crashed"),
            ("not_compared", "capture_failed"),
        )

    def test_itree_compile_failed_exceeding_uncompiled_candidates_is_flagged(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            itree = make_healthy_itree_report(Path(tmp))
            # All 8 candidates compiled `-O0`/`-O2` and `instrumented` with 0 unsafe tokens,
            # so `max_compile_failed == 0`. Routing a dropped candidate into `compile_failed`
            # must be caught by `validate_itree_error_boundary`.
            itree["compared_candidates"] = 7
            itree["agree_candidates"] = 7
            itree["not_compared_candidates"] = 1
            itree["not_compared_reasons"]["compile_failed"] = 1
            ok, reasons = campaign.validate_itree_error_boundary(itree)
            self.assertFalse(ok)
            self.assertTrue(
                any(
                    "not_compared_reasons.compile_failed (1) exceeds maximum compile/unsafe rejections (0)"
                    in r
                    for r in reasons
                ),
                reasons,
            )

    def test_manifest_known_bug_expires_and_divergence_class_and_findings_merge(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            m_file = Path(tmp) / "manifest.toml"
            m_file.write_text(
                '[[tests]]\n'
                'name = "expired_bug"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'divergence_class = "missed_ub"\n'
                'expires = "2020-01-01"\n'
                'summary = "expired in manifest"\n'
                '\n'
                '[[tests]]\n'
                'name = "bad_div_cls"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'divergence_class = "not_a_valid_class"\n'
                'summary = "bad class"\n',
                encoding="utf-8",
            )
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_file, reference_date="2026-11-09"
            )
            self.assertFalse(audit["passed"])
            reasons = " | ".join(e["reason"] for e in audit["stale_known_anneal_bugs"])
            self.assertIn("expired_quarantine_entry", reasons)
            self.assertIn("invalid divergence_class", reasons)

            # A dict evaluation with `verdict: "diverge"` but no Anneal outcome tags is
            # `stale_known_anneal_bug_unconfirmed`, and a mismatched `divergence_class` is
            # `stale_known_anneal_bug_divergence_class_mismatch`.
            m_open = Path(tmp) / "manifest_open.toml"
            m_open.write_text(
                '[[tests]]\n'
                'name = "open_bug"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "ub@repro.rs:4:1: 4:9"\n'
                'divergence_class = "false_positive_ub"\n'
                'summary = "tracked"\n',
                encoding="utf-8",
            )
            unconfirmed = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_open,
                manifest_eval_results={"open_bug": {"verdict": "diverge"}},
            )
            self.assertFalse(unconfirmed["passed"])
            self.assertIn(
                "stale_known_anneal_bug_unconfirmed",
                unconfirmed["stale_known_anneal_bugs"][0]["reason"],
            )

            # When `item_outcomes` has the batch span (`src/lib.rs:40:1: 40:9`) and `findings`
            # has the `repro.rs`-mapped span (`ub@repro.rs:4:1: 4:9`) plus `divergence_class`,
            # `extract_manifest_eval_results_from_miri_summary` merges both so the repro tag
            # matches and `divergence_class` is checked.
            miri_summary = {
                "mode": "identity",
                "item_outcomes": {
                    "open_bug": {
                        "verdict": "diverge",
                        "miri_outcome": "pass:unit",
                        "anneal_outcome": "ub@src/lib.rs:40:1: 40:9",
                        "anneal_lean_tag": "MirDiffTag.ub",
                    }
                },
                "findings": [
                    {
                        "fn_name": "open_bug",
                        "divergence_class": "false_positive_ub",
                        "anneal_outcome": "ub@repro.rs:4:1: 4:9",
                        "anneal_lean_tag": "MirDiffTag.ub",
                    }
                ],
            }
            merged = campaign.extract_manifest_eval_results_from_miri_summary(miri_summary)
            audit_merged = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_open, manifest_eval_results=merged
            )
            self.assertTrue(audit_merged["passed"], audit_merged)

            # If the live finding's `divergence_class` drifted to `missed_ub`, it fails closed.
            miri_summary["findings"][0]["divergence_class"] = "missed_ub"  # type: ignore[index]
            merged_drifted = campaign.extract_manifest_eval_results_from_miri_summary(miri_summary)
            audit_drifted = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_open, manifest_eval_results=merged_drifted
            )
            self.assertFalse(audit_drifted["passed"])
            self.assertIn(
                "stale_known_anneal_bug_divergence_class_mismatch",
                audit_drifted["stale_known_anneal_bugs"][0]["reason"],
            )

    def test_mutant_self_check_enforces_per_variant_kill_class_and_strict_normalization(self) -> None:
        # If `wide_shift`'s `guard_masks_exponent_silently` variant fails with `harness_error`
        # instead of `missed_ub`, the mutant must NOT be counted as killed even though
        # `"harness_error"` is in `wide_shift`'s family-level `expected_kill_classes`.
        wide = copy.deepcopy(
            next(m for m in campaign.SEEDED_SEMANTIC_MUTANTS if m["id"] == "wide_shift")
        )
        wide["mutant_variants"] = tuple(
            dict(v, anneal_outcome="capture_error:crash", anneal_lean_tag="none")
            if v["label"] == "guard_masks_exponent_silently"
            else dict(v)
            for v in wide["mutant_variants"]
        )
        res = campaign.run_semantic_mutant_self_check(mutants=[wide])
        self.assertFalse(res["passed"])
        self.assertEqual(res["survived_mutants"], ["wide_shift"])
        self.assertEqual(
            res["results"][0]["survived_variants"], ["guard_masks_exponent_silently"]
        )
        self.assertEqual(
            res["results"][0]["missing_expected_kill_classes"], ["missed_ub"]
        )

        # Custom evaluator returning `{"killed": True, "exit_code": 0}` or
        # `{"verdict": "diverge"}` without `divergence_class` must fail closed.
        base = dict(campaign.SEEDED_SEMANTIC_MUTANTS[0])
        for bad_eval in (
            lambda _m: {"killed": True, "kill_class": "missed_ub", "exit_code": 0},
            lambda _m: {"verdict": "diverge"},
        ):
            r = campaign.run_semantic_mutant_self_check(evaluator=bad_eval, mutants=[base])
            self.assertFalse(r["passed"], r)



def _with_one_reported_missed_ub(summary: dict[str, object], repro: Path) -> dict[str, object]:
    """Turns `ub_item` of an all-agreeing `_with_consistent_item_outcomes(...,
    direct_call="agree")` summary into a kernel-confirmed `missed_ub` divergence
    with its finding, keeping every aggregate consistent."""
    summary["item_outcomes"]["ub_item"] = {  # type: ignore[index]
        "verdict": "diverge",
        "miri_outcome": "ub@src/lib.rs:41:14",
        "anneal_outcome": "pass:unit",
        "anneal_lean_tag": "MirDiffTag.normalUnit",
    }
    summary["anneal_outcomes"]["pass"] = 7  # type: ignore[index]
    summary["anneal_outcomes"]["ub"] = 0  # type: ignore[index]
    summary["agree_count"] = 7
    summary["diverge_count"] = 1
    summary["kernel_confirmed_divergences"] = 1
    summary["divergence_classes"]["missed_ub"] = 1  # type: ignore[index]
    summary["findings"] = [
        {
            "finding_id": "finding_0000_ub_item",
            "fn_name": "ub_item",
            "seed_name": "ub_item",
            "applied_mutators": [],
            "divergence_class": "missed_ub",
            "miri_outcome": "ub@src/lib.rs:4:14",
            "anneal_outcome": "pass:unit",
            "anneal_lean_tag": "MirDiffTag.normalUnit",
            "miri_excerpt": "error: Undefined Behavior",
            "repro_path": str(repro),
            "kernel_confirmed": True,
        }
    ]
    return summary


class PassA1AdversarialRegressionTest(unittest.TestCase):
    """Regression tests for issues found in adversarial pass A1."""

    def test_toml_native_dates_expire_like_their_iso_text(self) -> None:
        # `expires = 2099-01-01` (unquoted) is a TOML date that `tomllib` returns as
        # `datetime.date`; it used to be rejected as `malformed_expires_date`.
        with tempfile.TemporaryDirectory() as tmp:
            q_file = Path(tmp) / "q.toml"
            q_file.write_text(
                '[[quarantined]]\n'
                'fingerprint = "seed_a:missed_ub"\n'
                'expires = 2099-01-01\n'
                'reason = "native date"\n'
                '[[quarantined]]\n'
                'fingerprint = "seed_b:missed_ub"\n'
                'expires = 2099-01-01T08:00:00Z\n'
                'reason = "native offset datetime"\n'
                '[[quarantined]]\n'
                'fingerprint = "seed_c:missed_ub"\n'
                'expires = 2020-01-01\n'
                'reason = "native date, expired"\n'
                '[[quarantined]]\n'
                'fingerprint = "seed_d:missed_ub"\n'
                'expires = 08:00:00\n'
                'reason = "a time is not a date"\n'
                '\n'
                '[[tests]]\n'
                'name = "seed_e"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'summary = "tracked"\n'
                'expires = 2099-06-01\n',
                encoding="utf-8",
            )
            self.assertEqual(
                campaign.load_quarantine_rules(q_file),
                {"seed_a:missed_ub", "seed_b:missed_ub", "seed_e"},
            )
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file, reference_date="2026-11-13"
            )
            by_entry = {e["entry"]: e["reason"] for e in audit["stale_quarantine_entries"]}
            self.assertEqual(sorted(by_entry), ["seed_c:missed_ub", "seed_d:missed_ub"])
            self.assertEqual(
                by_entry["seed_c:missed_ub"],
                "expired_quarantine_entry: expires 2020-01-01 < 2026-11-13",
            )
            self.assertTrue(by_entry["seed_d:missed_ub"].startswith("malformed_expires_date"))
            # The same holds for the manifest's own `known_anneal_bug` expiry.
            m_file = Path(tmp) / "manifest.toml"
            m_file.write_text(
                '[[tests]]\n'
                'name = "open_bug"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'summary = "tracked"\n'
                'expires = 2026-01-01\n',
                encoding="utf-8",
            )
            m_audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_file, reference_date="2026-11-13"
            )
            self.assertEqual(
                [e["reason"] for e in m_audit["stale_known_anneal_bugs"]],
                ["expired_quarantine_entry: expires 2026-01-01 < 2026-11-13"],
            )

    def test_findings_must_map_one_to_one_onto_diverging_item_outcomes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repro = Path(tmp) / "repro.rs"
            repro.write_text("pub fn ub_item() {}\n", encoding="utf-8")

            def fresh() -> dict:
                return _with_one_reported_missed_ub(
                    _with_consistent_item_outcomes(_make_valid_miri_summary(), direct_call="agree"),
                    repro,
                )

            summary = fresh()
            self.assertEqual(campaign.validate_performed_miri_summary(summary), (True, "ok"))
            self.assertEqual(campaign.audit_item_outcomes_against_summary(summary), [])
            rf = campaign.evaluate_miri_red_flags(summary, 0x5EED0001, {}, 50.0, 0)
            self.assertTrue(rf.passed, rf.failure_reasons)

            # The real divergence's finding attributed to an agreeing item: every count
            # still adds up, and a quarantine of that item would have hidden the
            # unquarantined `ub_item` divergence.
            swapped = fresh()
            swapped["findings"][0]["fn_name"] = "pass_item_0"
            swapped["findings"][0]["seed_name"] = "pass_item_0"
            _, unq, q = campaign.deduplicate_and_quarantine_findings(
                swapped["findings"], set(), {"pass_item_0"}
            )
            self.assertEqual((len(unq), len(q)), (0, 1))
            reasons = campaign.audit_item_outcomes_against_summary(swapped)
            self.assertTrue(any("divergence of 'pass_item_0'" in r for r in reasons), reasons)
            self.assertTrue(any("item 'ub_item' diverges (missed_ub) but has 0 findings" in r for r in reasons), reasons)
            rf_swapped = campaign.evaluate_miri_red_flags(swapped, 0x5EED0001, {}, 50.0, 0)
            self.assertFalse(rf_swapped.passed)
            self.assertFalse(rf_swapped.checks["error_vs_unsupported_boundary"])

            wrong_class = fresh()
            wrong_class["findings"][0]["divergence_class"] = "wrong_value"
            self.assertTrue(
                any(
                    "divergence_class 'wrong_value'" in r
                    for r in campaign.audit_item_outcomes_against_summary(wrong_class)
                )
            )
            unknown = fresh()
            unknown["findings"][0]["fn_name"] = "not_an_item"
            self.assertTrue(
                any(
                    "names 'not_an_item', which has no item_outcomes entry" in r
                    for r in campaign.audit_item_outcomes_against_summary(unknown)
                )
            )
            doubled = fresh()
            doubled["findings"].append(dict(doubled["findings"][0], finding_id="finding_0001_ub_item"))
            self.assertTrue(
                any(
                    "has 2 findings instead of exactly 1" in r
                    for r in campaign.audit_item_outcomes_against_summary(doubled)
                )
            )

    def test_itree_findings_must_reproduce_diag_tag_counts_and_name_each_trace_once(self) -> None:
        fp = "CallBoundaryOutliner:itree_outcome_mismatch:TraceReplayDiag.outcome_mismatch"
        with tempfile.TemporaryDirectory() as tmp:
            healthy = make_healthy_itree_report(Path(tmp), fingerprints=[fp, fp])
            red = campaign.evaluate_itree_red_flags(healthy, 0x20020002, {}, 50.0)
            self.assertTrue(red.passed, red.failure_reasons)

            retagged = make_healthy_itree_report(Path(tmp), fingerprints=[fp, fp])
            retagged["findings"][1]["diag_tag"] = "step_faulted"
            retagged["findings"][1]["diag_repr"] = "TraceReplayDiag.step_faulted"
            red = campaign.evaluate_itree_red_flags(retagged, 0x20020002, {}, 50.0)
            self.assertFalse(red.checks["itree_oracle_invoked"])
            self.assertTrue(
                any("findings per diag_tag" in r for r in red.failure_reasons), red.failure_reasons
            )

            repeated = make_healthy_itree_report(Path(tmp), fingerprints=[fp, fp])
            repeated["findings"][1]["case_ident"] = repeated["findings"][0]["case_ident"]
            red = campaign.evaluate_itree_red_flags(repeated, 0x20020002, {}, 50.0)
            self.assertFalse(red.checks["itree_oracle_invoked"])
            self.assertTrue(any("repeat traces ['case_0']" in r for r in red.failure_reasons))

    def test_legacy_error_tags_count_as_errored_items_everywhere(self) -> None:
        summary = _with_consistent_item_outcomes(_make_valid_miri_summary())
        summary["item_outcomes"]["pass_direct_fn_call"]["miri_outcome"] = "error: driver crashed"  # type: ignore[index]
        self.assertEqual(campaign.count_distinct_miri_errored_items(summary), 1)
        self.assertEqual(
            campaign._record_bucket(summary["item_outcomes"]["pass_direct_fn_call"]),  # type: ignore[index]
            "miri_oracle_error",
        )
        with tempfile.TemporaryDirectory() as tmp:
            m_file = Path(tmp) / "manifest.toml"
            m_file.write_text(
                '[[tests]]\nname = "open_bug"\n[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\nsummary = "tracked"\n',
                encoding="utf-8",
            )
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_file,
                manifest_eval_results={
                    "open_bug": {
                        "verdict": "not_compared",
                        "miri_outcome": "ub@src/lib.rs:3:5",
                        "anneal_outcome": "error: lean crashed",
                        "anneal_lean_tag": "none",
                    }
                },
            )
            self.assertTrue(
                audit["stale_known_anneal_bugs"][0]["reason"].startswith(
                    "stale_known_anneal_bug_unconfirmed"
                ),
                audit,
            )

    def test_gate_report_table_cells_cannot_break_rows(self) -> None:
        report = campaign.render_gate_report_sections(
            None,
            {
                "passed": False,
                "checked_quarantine_count": 1,
                "checked_known_bug_count": 0,
                "stale_entries": [
                    {
                        "source": "/tmp/q|x.json",
                        "entry": "a`b|c",
                        "reason": "malformed_quarantine_file: unrecognized quarantine keys ['x|y']\nsecond line",
                    }
                ],
            },
        )
        rows = [line for line in report.splitlines() if line.startswith("| `/tmp")]
        self.assertEqual(len(rows), 1, report)
        unescaped_pipes = re.findall(r"(?<!\\)\|", rows[0])
        self.assertEqual(len(unescaped_pipes), 4, rows[0])
        self.assertIn("`a'b\\|c`", rows[0])
        self.assertNotIn("\nsecond line", report)

    def test_identity_run_reports_known_anneal_bugs_it_did_not_evaluate(self) -> None:
        # An identity run evaluates one candidate per manifest test, so a
        # `known_anneal_bug` test missing from its `item_outcomes` (renamed, removed
        # from the corpus, or failing to compile) did not reproduce its open bug.
        with tempfile.TemporaryDirectory() as tmp:
            m_file = Path(tmp) / "manifest.toml"
            m_file.write_text(
                '[[tests]]\n'
                'name = "pass_direct_fn_call"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "externalCall:miri_diff_corpus::helper_add_ten"\n'
                'summary = "unlinked intra-crate callee"\n'
                '\n'
                '[[tests]]\n'
                'name = "renamed_away_bug"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'summary = "no corpus item carries this name any more"\n',
                encoding="utf-8",
            )
            summary = _with_consistent_item_outcomes(
                _make_valid_miri_summary(), direct_call="external_call"
            )
            summary["mode"] = "identity"
            self.assertTrue(campaign.miri_summary_evaluates_every_manifest_test(summary))
            self.assertFalse(
                campaign.miri_summary_evaluates_every_manifest_test(dict(summary, mode="seeded"))
            )
            legacy = dict(summary)
            del legacy["item_outcomes"]
            self.assertFalse(campaign.miri_summary_evaluates_every_manifest_test(legacy))

            extracted = campaign.extract_manifest_eval_results_from_miri_summary(summary)
            assert extracted is not None
            self.assertNotIn("renamed_away_bug", extracted)
            exhaustive = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_file,
                manifest_eval_results=extracted,
                reference_date="2026-11-13",
                manifest_eval_exhaustive=True,
            )
            self.assertEqual(
                [(e["entry"], e["reason"].split(":")[0]) for e in exhaustive["stale_entries"]],
                [("renamed_away_bug", "stale_known_anneal_bug_unconfirmed")],
            )
            self.assertEqual(exhaustive["checked_known_bug_count"], 2)
            # A partial (seeded) evaluation never judges tests it did not report.
            partial = campaign.verify_no_stale_quarantine_or_known_bugs(
                manifest_path=m_file, manifest_eval_results=extracted, reference_date="2026-11-13"
            )
            self.assertTrue(partial["passed"], partial)

            for mode, argv_extra, expected_rc in (
                ("identity", ["--miri-identity"], campaign.EXIT_HARNESS_FAILED),
                ("seeded", [], campaign.EXIT_SUCCESS),
            ):
                with self.subTest(mode=mode):
                    run_summary = dict(summary, mode=mode)
                    state_dir = Path(tmp) / f"state_{mode}"
                    with mock.patch.object(campaign, "run_harness", return_value=run_summary):
                        rc = _quiet_main(
                            [
                                "--profile",
                                "smoke",
                                "--miri-only",
                                *argv_extra,
                                "--check-stale-ratchet",
                                "--manifest-path",
                                str(m_file),
                                "--state-dir",
                                str(state_dir),
                            ]
                        )
                    self.assertEqual(rc, expected_rc)
                    report = _read_summary(state_dir)
                    self.assertTrue(report["red_flags"]["passed"], report["red_flags"])
                    stale = report["stale_ratchet_audit"]["stale_known_anneal_bugs"]
                    if mode == "identity":
                        self.assertEqual([e["entry"] for e in stale], ["renamed_away_bug"])
                    else:
                        self.assertEqual(stale, [])

    def test_known_corpus_bug_seeds_need_a_known_anneal_bug_table(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            m_file = Path(tmp) / "manifest.toml"
            m_file.write_text(
                '[[tests]]\n'
                'name = "table_bug"\n'
                '[tests.known_anneal_bug]\n'
                'observed_anneal_tag = "MirDiffTag.ub"\n'
                'summary = "tracked"\n'
                '\n'
                '[[tests]]\n'
                'name = "flag_bug"\n'
                'known_anneal_bug = false\n'
                '\n'
                '[[tests]]\n'
                'name = "plain_test"\n',
                encoding="utf-8",
            )
            # `known_anneal_bug = false` must not quarantine `flag_bug`'s findings.
            self.assertEqual(
                campaign.load_known_corpus_bug_seeds(Path(tmp), m_file), {"table_bug"}
            )
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(manifest_path=m_file)
            self.assertEqual(
                [(e["entry"], e["reason"]) for e in audit["stale_entries"]],
                [("flag_bug", "malformed_known_anneal_bug: expected table")],
            )
            for text in ("tests = 5\n", 'tests = "nope"\n', "tests = { name = \"t\" }\n"):
                with self.subTest(tests=text):
                    m_file.write_text(text, encoding="utf-8")
                    self.assertEqual(campaign.load_known_corpus_bug_seeds(Path(tmp), m_file), set())

    def test_simulated_summaries_bucket_legacy_error_tags_as_errors(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repro = Path(tmp) / "repro.rs"
            repro.write_text("pub fn probe_p() {}\n", encoding="utf-8")
            for miri_tag, anneal_tag, lean_tag in (
                ("error: miri driver crashed", "pass:unit", "MirDiffTag.normalUnit"),
                ("ub@src/lib.rs:3:5", "error: lean crashed", "none"),
            ):
                with self.subTest(miri=miri_tag, anneal=anneal_tag):
                    summary = campaign.build_simulated_miri_summary(
                        "p", miri_tag, anneal_tag, lean_tag, repro
                    )
                    self.assertEqual(
                        campaign.validate_performed_miri_summary(summary), (True, "ok")
                    )
                    self.assertEqual(campaign.audit_item_outcomes_against_summary(summary), [])
                    rc, kill_class, detail = campaign.campaign_exit_for_miri_summary(summary)
                    self.assertEqual((rc, kill_class), (campaign.EXIT_HARNESS_FAILED, "harness_error"))
                    self.assertIn("oracle_errors_exceeded", detail)


if __name__ == "__main__":
    unittest.main()
