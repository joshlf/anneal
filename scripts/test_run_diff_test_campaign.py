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
import re
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

    def test_miri_only_campaign_does_not_flag_itree_quarantine_entries_as_stale(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp) / "campaign_state"
            q_file = Path(tmp) / "quarantine.toml"
            q_file.write_text(
                "[[quarantined]]\n"
                'fingerprint = "ArithmeticCastMutator:itree_outcome_mismatch:'
                'TraceReplayDiag.outcome_mismatch"\n'
                'expires = "2099-01-01"\n',
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
            with (
                mock.patch.object(
                    campaign, "run_harness", return_value=_make_valid_miri_summary()
                ),
                mock.patch("sys.stdout", io.StringIO()),
            ):
                rc = campaign.main(argv)
            self.assertEqual(rc, campaign.EXIT_SUCCESS)
            summary = json.loads(
                (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(summary["stale_ratchet_audit"]["stale_entries"], [])


class OracleOutcomeClassificationTest(unittest.TestCase):
    """`classify_oracle_outcome_tags` mirrors `compare_miri_and_anneal`."""

    def test_classification_table_and_precedence(self) -> None:
        table = [
            ("pass:scalar:5:4", "pass:scalar:5:4", ("agree", "")),
            ("pass:unit", "pass:unit", ("agree", "")),
            ("pass:scalar:5:4", "pass:scalar:6:4", ("diverge", "wrong_value")),
            ("pass:scalar:5:4", "abort@src/lib.rs:3:5:3:9", ("diverge", "wrong_value")),
            ("pass:unit", "panic@src/lib.rs:3:5:3:9", ("diverge", "return_vs_panic")),
            ("pass:unit", "ub@src/lib.rs:3:5:3:9", ("diverge", "false_positive_ub")),
            ("panic@src/lib.rs:3:7", "pass:unit", ("diverge", "panic_vs_return")),
            ("panic@src/lib.rs:3:7", "ub@src/lib.rs:3:5:3:9", ("diverge", "false_positive_ub")),
            ("panic@src/lib.rs:3:7", "panic@src/lib.rs:3:5:3:9", ("agree", "")),
            ("panic@src/lib.rs:9:7", "panic@src/lib.rs:3:5:3:9", ("diverge", "panic_site_mismatch")),
            ("ub@src/lib.rs:3:7", "ub@src/lib.rs:3:5:3:9", ("agree", "")),
            ("ub@src/lib.rs:4:1", "ub@src/lib.rs:3:5:3:9", ("diverge", "ub_location_mismatch")),
            ("ub", "ub@src/lib.rs:3:5:3:9", ("diverge", "ub_location_mismatch")),
            ("ub@src/lib.rs:3:7", "pass:unit", ("diverge", "missed_ub")),
            ("ub@src/lib.rs:3:7", "panic@src/lib.rs:3:5:3:9", ("diverge", "missed_ub")),
            # Not-compared precedence: Miri error > capture error > external call >
            # unsupported > fuel.
            ("oracle_error:boom", "capture_error:x", ("not_compared", "miri_oracle_error")),
            ("ub@src/lib.rs:3:7", "capture_error:x", ("not_compared", "capture_failed")),
            ("pass:unit", "externalCall:core::f", ("not_compared", "external_call")),
            ("pass:unit", "unsupported@src/lib.rs:3:5:3:9", ("not_compared", "unsupported")),
            ("pass:unit", "outOfFuel", ("not_compared", "out_of_fuel")),
        ]
        for miri_tag, anneal_tag, expected in table:
            with self.subTest(miri=miri_tag, anneal=anneal_tag):
                self.assertEqual(
                    campaign.classify_oracle_outcome_tags(miri_tag, anneal_tag), expected
                )


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
        rust_src = (
            SCRIPT_DIR.parent / "crates" / "anneal-difftest" / "src" / "miri_eval.rs"
        ).read_text(encoding="utf-8")
        start = rust_src.index("const SEMANTIC_MUTANT_PROBES")
        end = rust_src.index("const KNOWN_PROVENANCE_GAP_PROBES", start)
        rust_probes = dict(
            re.findall(r'\(\s*"(\w+)",\s*r#"(.*?)"#,\s*\)', rust_src[start:end], re.S)
        )
        py_probes = {
            str(m["id"]): str(m["probe_rust_source"]) for m in campaign.SEEDED_SEMANTIC_MUTANTS
        }
        self.assertEqual(sorted(rust_probes), sorted(py_probes))
        for mutant_id, source in py_probes.items():
            with self.subTest(mutant=mutant_id):
                self.assertEqual(rust_probes[mutant_id], source)

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
                "anneal_outcome": "unsupported@src/lib.rs:4:5:4:9",
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
            "unsupported@src/lib.rs:4:5:4:9",
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
            with (
                mock.patch.object(campaign, "run_harness", return_value=summary),
                mock.patch("sys.stdout", io.StringIO()),
            ):
                rc = campaign.main(
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
            report = json.loads(
                (state_dir / "reports" / "LATEST_CAMPAIGN_SUMMARY.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertFalse(report["stale_ratchet_audit"]["passed"])
            self.assertTrue(
                any(
                    "stale_known_anneal_bug_now_passes" in e["reason"]
                    for e in report["stale_ratchet_audit"]["stale_known_anneal_bugs"]
                )
            )
            # The harness failure is due to the ratchet alone, not to the red flags.
            self.assertTrue(report["red_flags"]["passed"], report["red_flags"])

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
        summary = _make_valid_miri_summary()
        summary["not_compared_reasons"]["external_call"] = 1  # type: ignore[index]
        summary["anneal_outcomes"]["external_call"] = 0  # type: ignore[index]
        ok, reasons = campaign.validate_error_vs_unsupported_boundary(summary)
        self.assertFalse(ok)
        self.assertTrue(
            any("not_compared_reasons.external_call" in r for r in reasons),
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

    def test_quarantine_tests_known_anneal_bug_entries_audited_and_validated(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
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
                'divergence_class = "missed_ub"\n',
                encoding="utf-8",
            )
            rules = campaign.load_quarantine_rules(q_file)
            self.assertEqual(rules, {"valid_seed", "valid_seed:missed_ub"})
            audit = campaign.verify_no_stale_quarantine_or_known_bugs(
                quarantine_file=q_file,
                evaluated_fingerprints=[],
                observed_quarantine_keys={"valid_seed:missed_ub"},
                covered_harnesses={"miri"},
                reference_date="2026-11-09",
            )
            self.assertFalse(audit["passed"])
            reasons = " | ".join(e["reason"] for e in audit["stale_quarantine_entries"])
            self.assertIn("expired_quarantine_entry", reasons)
            self.assertIn("missing_known_anneal_bug_metadata", reasons)
            self.assertIn("unobserved_quarantine_entry", reasons)


if __name__ == "__main__":
    unittest.main()
