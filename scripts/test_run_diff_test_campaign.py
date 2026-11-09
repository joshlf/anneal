#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
# https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
# <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
# license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
# option. This file may not be copied, modified, or distributed except
# according to those terms.

"""Unit tests for `scripts/run_diff_test_campaign.py`."""

from __future__ import annotations

import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import run_diff_test_campaign as campaign  # noqa: E402


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


class StaleRatchetGateTest(unittest.TestCase):
    def test_real_manifest_and_valid_quarantine_pass(self) -> None:
        repo_root = SCRIPT_DIR.parent
        manifest_path = repo_root / "tests" / "miri-diff" / "manifest.toml"
        with tempfile.TemporaryDirectory() as tmp:
            q_file = Path(tmp) / "quarantine.toml"
            q_file.write_text(
                '[[quarantined]]\n'
                'fingerprint = "RawPtrOffsetMutator:ub_location_mismatch:MirDiffTag.ub"\n'
                'expires = "2027-01-01"\n'
                'reason = "tracked pointer offset span mismatch"\n',
                encoding="utf-8",
            )
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file,
                manifest_path=manifest_path,
                ledger={"resolved_history": []},
                evaluated_fingerprints=[
                    "RawPtrOffsetMutator:ub_location_mismatch:MirDiffTag.ub"
                ],
                reference_date="2026-11-09",
            )
            self.assertTrue(audit["passed"], audit)
            self.assertEqual(audit["stale_entries"], [])
            self.assertEqual(audit["checked_quarantine_count"], 1)
            self.assertGreaterEqual(audit["checked_known_bug_count"], 2)

    def test_expired_malformed_resolved_and_unobserved_quarantine_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            q_file = Path(tmp) / "quarantine.toml"
            q_file.write_text(
                '[[quarantined]]\n'
                'fingerprint = "ArithmeticCastMutator:wrong_value:MirDiffTag.normalScalar"\n'
                'expires = "2026-01-15"\n'
                '[[quarantined]]\n'
                'fingerprint = "bad_no_colon"\n'
                '[[quarantined]]\n'
                'fingerprint = "PlaceProjectionWrapper:missed_ub:MirDiffTag.normalScalar"\n'
                'expires = "2027-06-01"\n',
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


class CliGateIntegrationTest(unittest.TestCase):
    def test_standalone_self_check_mutants_and_stale_ratchet_cli(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp) / "state"
            buf = io.StringIO()
            with mock.patch("sys.stdout", buf):
                rc = campaign.main(
                    ["--self-check-mutants", "--state-dir", str(state_dir)]
                )
            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            summary = json.loads(
                (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertTrue(summary["semantic_mutant_self_check"]["passed"])
            self.assertEqual(summary["semantic_mutant_self_check"]["killed_count"], 5)

            expired_q = Path(tmp) / "expired_quarantine.toml"
            expired_q.write_text(
                '[[quarantined]]\n'
                'fingerprint = "RawPtrOffsetMutator:ub_location_mismatch:MirDiffTag.ub"\n'
                'expires = "2020-01-01"\n',
                encoding="utf-8",
            )
            with mock.patch("sys.stdout", io.StringIO()):
                rc_fail = campaign.main(
                    [
                        "--check-stale-ratchet",
                        "--quarantine-file",
                        str(expired_q),
                        "--state-dir",
                        str(state_dir),
                    ]
                )
            self.assertEqual(rc_fail, campaign.EXIT_HARNESS_FAILED)

    def test_campaign_run_with_gates_records_sections_in_summary(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp) / "campaign_state"
            stub_summary = _make_valid_miri_summary()
            with (
                mock.patch.object(
                    campaign, "run_harness", return_value=dict(stub_summary)
                ),
                mock.patch("sys.stdout", io.StringIO()),
            ):
                rc = campaign.main(
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
            summary = json.loads(
                (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertTrue(summary["semantic_mutant_self_check"]["passed"])
            self.assertTrue(summary["stale_ratchet_audit"]["passed"])


if __name__ == "__main__":
    unittest.main()
