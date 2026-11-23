#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Unit tests for `workbench` host scripts and static validators."""

from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import farkas_cert_gen  # noqa: E402
import preflight_syntax_check  # noqa: E402
import proof_health_scan  # noqa: E402
import split_lean_module  # noqa: E402


class ProofHealthScanTests(unittest.TestCase):
    def test_clean_pass1_file_passes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            p = pathlib.Path(tmp) / "Clean.lean"
            p.write_text(
                "prelude\nimport Init.Core\nimport Init.Data.Nat.Basic\n"
                "-- omega in comment is ignored\n"
                "theorem t (n : Nat) : n = n := by rfl\n",
                encoding="utf-8",
            )
            findings = proof_health_scan.scan_file(p, force_pass1=True, allow_import_prefixes=())
            self.assertEqual(findings, [])

    def test_module_syntax_pass1_and_public_import_check(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            ok_p = pathlib.Path(tmp) / "ModOk.lean"
            ok_p.write_text(
                "module\nprelude\npublic import Init.Core\npublic section\n"
                "public theorem t (n : Nat) : n = n := by rfl\nend\n",
                encoding="utf-8",
            )
            self.assertEqual(
                proof_health_scan.scan_file(ok_p, force_pass1=True, allow_import_prefixes=()),
                [],
            )
            bad_p = pathlib.Path(tmp) / "ModBad.lean"
            bad_p.write_text(
                "module\nprelude\npublic import Std\n",
                encoding="utf-8",
            )
            codes = {
                f["code"]
                for f in proof_health_scan.scan_file(bad_p, force_pass1=True, allow_import_prefixes=())
            }
            self.assertIn("DISALLOWED_IMPORT", codes)

    def test_catches_banned_pass1_constructs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            p = pathlib.Path(tmp) / "Bad.lean"
            big_list = "[" + ", ".join(str(i) for i in range(34)) + "]"
            p.write_text(
                "import Std\n"
                "noncomputable section\n"
                f"def xs : List Nat := {big_list}\n"
                "theorem bad (a b : Nat) (h : a < b) : a ≤ b := by omega\n"
                "theorem k : True := by decide +kernel\n",
                encoding="utf-8",
            )
            findings = proof_health_scan.scan_file(p, force_pass1=True, allow_import_prefixes=())
            codes = {f["code"] for f in findings}
            self.assertIn("MISSING_PRELUDE", codes)
            self.assertIn("DISALLOWED_IMPORT", codes)
            self.assertIn("NONCOMPUTABLE_SECTION", codes)
            self.assertIn("LARGE_LIST_LITERAL", codes)
            self.assertIn("BANNED_TACTIC", codes)
            self.assertIn("BANNED_TACTIC_CONFIG", codes)


class FarkasCertGenTests(unittest.TestCase):
    def test_solves_parity_chvatal_gomory_cut(self) -> None:
        # 2*a <= 2*b + 1 and 2*b + 1 <= 2*a has rational solution b = a - 1/2,
        # so refuting it (proving 1 <= 0) strictly requires a Chvatal-Gomory divCut!
        res = farkas_cert_gen.generate_certificate(
            domain="int",
            hyp_strings=["2*a <= 2*b + 1", "2*b + 1 <= 2*a"],
            goal_string="1 <= 0",
            thm_name="parity_impossible_test",
        )
        self.assertTrue(res["solved"])
        ops = [s["op"] for s in res["steps"]]
        self.assertIn("divCut", ops)
        self.assertIn("checkIntCutGoal_sound", res["lean_snippet"])

        res_nat = farkas_cert_gen.generate_certificate(
            domain="nat",
            hyp_strings=["2*i + 1 <= 2*n"],
            goal_string="i < n",
            thm_name="parity_stride_test",
        )
        self.assertTrue(res_nat["solved"])
        self.assertIn("checkNatCutGoal_sound", res_nat["lean_snippet"])

    def test_solves_nat_implicit_nonnegativity(self) -> None:
        res = farkas_cert_gen.generate_certificate(
            domain="nat",
            hyp_strings=["a + b <= 10"],
            goal_string="a <= 10",
            thm_name="sub_bound",
        )
        self.assertTrue(res["solved"])
        self.assertTrue(len(res["implicit_nat_zero_le_vars"]) > 0)

    def test_rejects_invalid_bound(self) -> None:
        res = farkas_cert_gen.generate_certificate(
            domain="int",
            hyp_strings=["x <= y"],
            goal_string="x + 1 <= y",
            thm_name="invalid_bound",
        )
        self.assertFalse(res["solved"])


class SplitLeanModuleTests(unittest.TestCase):
    def test_detects_cross_chunk_eq1_hazard(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            p = pathlib.Path(tmp) / "Big.lean"
            p.write_text(
                "def helperFn (n : Nat) : Nat :=\n  n + 1\n\n"
                "theorem step1 (n : Nat) : helperFn n = n + 1 := by\n  rfl\n\n"
                "theorem step2 (n : Nat) : helperFn n = n + 1 := by\n  unfold helperFn\n  rfl\n",
                encoding="utf-8",
            )
            plan = split_lean_module.analyze_lean_module(p, target_lines=4)
            self.assertGreaterEqual(len(plan["proposed_chunks"]), 2)
            self.assertEqual(len(plan["cross_chunk_eq1_hazards"]), 1)
            self.assertEqual(plan["cross_chunk_eq1_hazards"][0]["target_def"], "helperFn")


class PreflightSyntaxCheckTests(unittest.TestCase):
    def test_collect_lean_targets_skips_lake_cache(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            keep = root / "Mod.lean"
            skip_dir = root / ".lake" / "packages"
            skip_dir.mkdir(parents=True)
            skip = skip_dir / "Cached.lean"
            keep.write_text("prelude\n", encoding="utf-8")
            skip.write_text("prelude\n", encoding="utf-8")
            found = preflight_syntax_check.collect_lean_targets([str(root)])
            self.assertEqual(found, [keep.resolve()])


if __name__ == "__main__":
    unittest.main()
