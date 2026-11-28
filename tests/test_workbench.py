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

import audit_lean_hygiene  # noqa: E402
import build_lean_dag  # noqa: E402
import diff_oracle_runner  # noqa: E402
import farkas_cert_gen  # noqa: E402
import olean_profiler  # noqa: E402
import preflight_syntax_check  # noqa: E402
import proof_health_scan  # noqa: E402
import split_lean_module  # noqa: E402
import stage_ref_pkg  # noqa: E402
import verify_quorum  # noqa: E402


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

    def test_pure_ref_and_import_guards_match_trusted_boundary(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            clean_mod = root / "CleanMod.lean"
            clean_mod.write_text(
                "module\nprelude\npublic import Init.Core\nimport all Init.Data.Nat.Bitwise.Basic\n\n"
                "public section\nnamespace Demo\npublic theorem ok_rfl : 1 = 1 := by rfl\nend Demo\nend\n",
                encoding="utf-8",
            )
            bad_mod = root / "BadMod.lean"
            bad_mod.write_text(
                "prelude\nimport Init.Core\nimport Init.System.FilePath\n\n"
                "def bad1 (x : Nat) : Nat := dbgTrace \"hi\" (fun _ => x)\n"
                "open System in\ndef bad2 : Nat := 0\n",
                encoding="utf-8",
            )
            report = preflight_syntax_check.run_syntax_preflight([clean_mod, bad_mod], role="theory")
            by_name = {pathlib.Path(f["file"]).name: f for f in report["files"]}
            self.assertTrue(by_name["CleanMod.lean"]["clean"], by_name["CleanMod.lean"]["violations"])
            self.assertFalse(by_name["BadMod.lean"]["clean"])
            msgs = "\n".join(v["message"] for v in by_name["BadMod.lean"]["violations"])
            self.assertIn("Init.System.FilePath", msgs)
            self.assertIn("dbgTrace", msgs)
            self.assertIn("System", msgs)

    def test_local_semireducible_allowlist_and_shadow_guards(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            admitted = root / "Admitted.lean"
            admitted.write_text(
                "prelude\nimport Init.Core\nimport Init.Data.Nat.Bitwise.Basic\n\n"
                "attribute [local semireducible] _root_.Nat.bitwise in\n"
                "private theorem ok_unfold : 1 = 1 := by rfl\n",
                encoding="utf-8",
            )
            unqual = root / "Unqualified.lean"
            unqual.write_text(
                "prelude\nimport Init.Core\nimport Init.Data.Nat.Bitwise.Basic\n\n"
                "attribute [local semireducible] Nat.bitwise in\n"
                "theorem bad_unqual : 1 = 1 := by rfl\n",
                encoding="utf-8",
            )
            shadow = root / "Shadow.lean"
            shadow.write_text(
                "prelude\nimport Init.Core\n\n"
                "namespace Foo.Nat\ndef bitwise : Nat := 0\nend Foo.Nat\n",
                encoding="utf-8",
            )
            theory_rep = preflight_syntax_check.run_syntax_preflight(
                [admitted, unqual, shadow], role="theory"
            )
            by_name = {pathlib.Path(f["file"]).name: f for f in theory_rep["files"]}
            self.assertTrue(by_name["Admitted.lean"]["clean"], by_name["Admitted.lean"]["violations"])
            self.assertFalse(by_name["Unqualified.lean"]["clean"])
            self.assertFalse(by_name["Shadow.lean"]["clean"])
            shadow_msgs = "\n".join(v["message"] for v in by_name["Shadow.lean"]["violations"])
            self.assertIn("localSemireducibleAllowlist", shadow_msgs)

            corr_rep = preflight_syntax_check.run_syntax_preflight([admitted], role="correspondence")
            self.assertFalse(corr_rep["clean"])

            trusted_rep = preflight_syntax_check.run_syntax_preflight([admitted], role="trusted")
            self.assertFalse(trusted_rep["clean"])

    def test_pr4492_autoparam_lean_root_meta_import_and_export_guards(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            bad_meta_imp = root / "BadMetaImp.lean"
            bad_meta_imp.write_text(
                "prelude\nimport Init.Core\nimport Init.Meta\nimport Std.Async.Basic\n",
                encoding="utf-8",
            )
            bad_autoparam = root / "BadAutoParam.lean"
            bad_autoparam.write_text(
                "prelude\nimport Init.Core\n"
                "def bad1 (x : autoParam Nat `foo) : Nat := x\n"
                "def bad2 (x : optParam Nat 0) : Nat := x\n",
                encoding="utf-8",
            )
            bad_lean = root / "BadLean.lean"
            bad_lean.write_text(
                "prelude\nimport Init.Core\n"
                "open Lean in\ndef bad_open : Nat := 0\n"
                "def bad_ref := Lean.Syntax.missing\n",
                encoding="utf-8",
            )
            ok_loop = root / "OkLoop.lean"
            ok_loop.write_text(
                "prelude\nimport Init.Core\nimport Init.Control.Do\n"
                "def loopTy : Type := Lean.Loop\n",
                encoding="utf-8",
            )
            bad_export = root / "BadExport.lean"
            bad_export.write_text(
                "prelude\nimport Init.Core\n"
                "namespace Trusted\nexport Foo (bar)\nend Trusted\n"
                "namespace Demo\nexport IO (println)\nend Demo\n",
                encoding="utf-8",
            )
            rep = preflight_syntax_check.run_syntax_preflight(
                [bad_meta_imp, bad_autoparam, bad_lean, ok_loop, bad_export],
                role="theory",
            )
            by_name = {pathlib.Path(f["file"]).name: f for f in rep["files"]}
            self.assertFalse(by_name["BadMetaImp.lean"]["clean"])
            meta_msgs = "\n".join(v["message"] for v in by_name["BadMetaImp.lean"]["violations"])
            self.assertIn("Init.Meta", meta_msgs)
            self.assertIn("Std.Async.Basic", meta_msgs)

            self.assertFalse(by_name["BadAutoParam.lean"]["clean"])
            ap_msgs = "\n".join(v["message"] for v in by_name["BadAutoParam.lean"]["violations"])
            self.assertIn("autoParam", ap_msgs)
            self.assertIn("optParam", ap_msgs)

            self.assertFalse(by_name["BadLean.lean"]["clean"])
            self.assertTrue(by_name["OkLoop.lean"]["clean"], by_name["OkLoop.lean"]["violations"])
            # `Lean.Loop` is permitted in theory/correspondence, rejected in trusted.
            trusted_loop = preflight_syntax_check.run_syntax_preflight([ok_loop], role="trusted")
            self.assertFalse(trusted_loop["clean"])

            self.assertFalse(by_name["BadExport.lean"]["clean"])
            exp_msgs = "\n".join(v["message"] for v in by_name["BadExport.lean"]["violations"])
            self.assertIn("Trusted", exp_msgs)
            self.assertIn("IO", exp_msgs)

            # Static scanner also flags direct `import Init.Meta`.
            scan_codes = {
                f["code"]
                for f in proof_health_scan.scan_file(
                    bad_meta_imp, force_pass1=True, allow_import_prefixes=()
                )
            }
            self.assertIn("DISALLOWED_IMPORT", scan_codes)


class BuildLeanDagTests(unittest.TestCase):
    def test_lake_free_module_dag_build_cache_and_audit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            src_root = root / "src"
            (src_root / "Demo").mkdir(parents=True)
            out_dir = root / "out"
            (src_root / "Demo" / "Base.lean").write_text(
                "module\nprelude\npublic import Init.Core\n@[expose] public section\n"
                "namespace Demo\npublic def idNat (n : Nat) : Nat := n\nend Demo\nend\n",
                encoding="utf-8",
            )
            (src_root / "Demo" / "Top.lean").write_text(
                "module\nprelude\npublic import Demo.Base\npublic section\n"
                "namespace Demo\npublic theorem idNat_eq (n : Nat) : idNat n = n := rfl\nend Demo\nend\n",
                encoding="utf-8",
            )
            lean_bin, sysroot = build_lean_dag.resolve_lean_toolchain(None)
            roots = build_lean_dag.parse_root_specs(None, [str(src_root)])

            cold = build_lean_dag.build_dag(
                targets=["Demo.Top"],
                roots=roots,
                out_dir=out_dir,
                extra_lean_paths=[],
                lean_bin=lean_bin,
                sysroot=sysroot,
                jobs=2,
                quiet=True,
            )
            self.assertTrue(cold["clean"], cold["failed"])
            self.assertEqual(sorted(cold["built"]), ["Demo.Base", "Demo.Top"])
            self.assertEqual(cold["cached"], [])

            warm = build_lean_dag.build_dag(
                targets=["Demo.Top"],
                roots=roots,
                out_dir=out_dir,
                extra_lean_paths=[],
                lean_bin=lean_bin,
                sysroot=sysroot,
                jobs=2,
                quiet=True,
            )
            self.assertTrue(warm["clean"])
            self.assertEqual(warm["built"], [])
            self.assertEqual(warm["cached"], ["Demo.Base", "Demo.Top"])

            hygiene = audit_lean_hygiene.run_environment_audit(
                lake_dir=None,
                modules=["Demo.Top"],
                namespaces=["Demo"],
                lean_paths=[out_dir],
            )
            self.assertTrue(hygiene["clean"], hygiene)
            self.assertGreaterEqual(hygiene["total_constants"], 2)

            prof = olean_profiler.profile_module_exprs(
                out_dir, "Demo.Top", "Demo", 10, False, []
            )
            self.assertTrue(any(r["decl"] == "Demo.idNat_eq" for r in prof))


class VerifyQuorumTests(unittest.TestCase):
    def test_requires_explicit_export_root(self) -> None:
        rc, rep = verify_quorum.run_quorum(
            lean_file=None,
            dep_files=[],
            root_dir=None,
            module_name="Demo",
            export_roots=[],
            extra_lean_paths=[],
            neg_files=[],
            permitted_axioms=list(verify_quorum.DEFAULT_PERMITTED_AXIOMS),
        )
        self.assertEqual(rc, 2)
        self.assertEqual(rep["stage"], "export_roots")

    def test_clean_quorum_nat_land_guard_and_forged_axiom_tamper(self) -> None:
        try:
            verify_quorum.resolve_tc_435(None)
        except FileNotFoundError:
            self.skipTest("Lean v4.35.0 toolchain not installed on this host")

        with tempfile.TemporaryDirectory() as tmp:
            td = pathlib.Path(tmp)
            clean_src = td / "QuorumClean.lean"
            clean_src.write_text(
                "prelude\nimport Init.Prelude\n"
                "def pack8 (a b : Nat) : Nat := Nat.add (Nat.mul a 8) b\n"
                "theorem pack8_div : Eq (Nat.div (pack8 9 3) 8) 9 := rfl\n",
                encoding="utf-8",
            )
            bad_neg = td / "QuorumNeg.lean"
            bad_neg.write_text(
                "prelude\nimport Init.Prelude\n"
                "theorem wrong_eq : Eq 1 2 := rfl\n",
                encoding="utf-8",
            )
            rc_ok, rep_ok = verify_quorum.run_quorum(
                lean_file=clean_src,
                dep_files=[],
                root_dir=td,
                module_name="QuorumClean",
                export_roots=["pack8_div"],
                extra_lean_paths=[],
                neg_files=[bad_neg],
                permitted_axioms=list(verify_quorum.DEFAULT_PERMITTED_AXIOMS),
            )
            self.assertEqual(rc_ok, 0, rep_ok)
            self.assertTrue(rep_ok["passed"])
            self.assertIn("nanoda_bin", rep_ok["kernels"])
            self.assertEqual(rep_ok["kernels"]["nanoda_bin"]["rc"], 0)
            self.assertNotEqual(rep_ok["tamper_forged_axiom"]["nanoda_bin"]["rc"], 0)
            self.assertTrue(rep_ok["negative_mutations"][0]["rejected_as_expected"])

            nat_land_src = td / "QuorumNatLand.lean"
            nat_land_src.write_text(
                "prelude\nimport Init.Core\nimport Init.Data.Nat.Bitwise.Basic\n"
                "theorem bad_land : Eq (Nat.land 5 7) 5 := rfl\n",
                encoding="utf-8",
            )
            rc_land, rep_land = verify_quorum.run_quorum(
                lean_file=nat_land_src,
                dep_files=[],
                root_dir=td,
                module_name="QuorumNatLand",
                export_roots=["bad_land"],
                extra_lean_paths=[],
                neg_files=[],
                permitted_axioms=list(verify_quorum.DEFAULT_PERMITTED_AXIOMS),
            )
            self.assertEqual(rc_land, 2)
            self.assertEqual(rep_land["stage"], "nat_land_guard")
            self.assertIn("Anneal.NatBitwise", rep_land["error"])
            self.assertIn("4444", rep_land["error"])

            mut_nd = td / "corrupted_mutant.ndjson"
            mut_nd.write_text('{"in":1,"str":{"pre":0,"str":"bad"}}\n{"thm":{"name":1}}\n', encoding="utf-8")
            rc_mut, rep_mut = verify_quorum.run_quorum(
                lean_file=clean_src,
                dep_files=[],
                root_dir=td,
                module_name="QuorumClean",
                export_roots=["pack8_div"],
                extra_lean_paths=[],
                neg_files=[],
                permitted_axioms=list(verify_quorum.DEFAULT_PERMITTED_AXIOMS),
                mutant_ndjsons=[mut_nd],
            )
            self.assertEqual(rc_mut, 0, rep_mut)
            self.assertTrue(rep_mut["mutant_ndjsons"][0]["rejected_by_all"])


class DiffOracleRunnerTests(unittest.TestCase):
    def test_f64_signed_zero_nan_outcomes_and_mutant_kill(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            td = pathlib.Path(tmp)
            model_p = td / "model.jsonl"
            oracle_p = td / "oracle.jsonl"
            mut_bad_zero = td / "mut_zero.jsonl"
            mut_ident = td / "mut_ident.jsonl"

            rows_model = [
                '{"id":"neg_zero","outcome":"returned","f64_bits":"0x8000000000000000"}',
                '{"id":"qnan_a","outcome":"returned","f64_bits":"0x7ff8000000000001"}',
                '{"id":"throw_case","outcome":"unwound","error_tag":"RangeError"}',
                '{"id":"bytes_case","outcome":"returned","bytes_hex":"0102ff"}',
            ]
            rows_oracle = [
                '{"id":"neg_zero","outcome":"returned","f64_bits":"0x8000000000000000"}',
                '{"id":"qnan_a","outcome":"returned","f64_bits":"0xfff8000000000000"}',
                '{"id":"throw_case","outcome":"unwound","error_tag":"RangeError"}',
                '{"id":"bytes_case","outcome":"returned","bytes_hex":"0102ff"}',
            ]
            rows_mut_zero = [
                '{"id":"neg_zero","outcome":"returned","f64_bits":"0x0000000000000000"}',
                *rows_model[1:],
            ]
            model_p.write_text("\n".join(rows_model) + "\n", encoding="utf-8")
            oracle_p.write_text("\n".join(rows_oracle) + "\n", encoding="utf-8")
            mut_bad_zero.write_text("\n".join(rows_mut_zero) + "\n", encoding="utf-8")
            mut_ident.write_text("\n".join(rows_model) + "\n", encoding="utf-8")

            rc_ok, rep_ok = diff_oracle_runner.run_differential_suite(
                cases_jsonl=None,
                model_jsonl=model_p,
                oracle_jsonl=oracle_p,
                model_cmd=None,
                oracle_cmd=None,
                mutant_model_jsonls=[mut_bad_zero],
                mutant_model_cmds=[],
                exact_nan_bits=False,
                min_cases=4,
            )
            self.assertEqual(rc_ok, 0, rep_ok)
            self.assertEqual(rep_ok["primary"]["matched_cases"], 4)
            self.assertTrue(rep_ok["mutants"][0]["killed_as_expected"])

            # Exact NaN payload mode flags differing NaN bit patterns.
            rc_exact, _ = diff_oracle_runner.run_differential_suite(
                cases_jsonl=None,
                model_jsonl=model_p,
                oracle_jsonl=oracle_p,
                model_cmd=None,
                oracle_cmd=None,
                mutant_model_jsonls=[],
                mutant_model_cmds=[],
                exact_nan_bits=True,
            )
            self.assertEqual(rc_exact, 1)

            # Unkilled mutant fails closed.
            rc_survive, rep_survive = diff_oracle_runner.run_differential_suite(
                cases_jsonl=None,
                model_jsonl=model_p,
                oracle_jsonl=oracle_p,
                model_cmd=None,
                oracle_cmd=None,
                mutant_model_jsonls=[mut_ident],
                mutant_model_cmds=[],
            )
            self.assertEqual(rc_survive, 1)
            self.assertEqual(rep_survive["stage"], "mutant_kill_gate")


class StageRefPkgTests(unittest.TestCase):
    def test_stages_standalone_under_100kib_and_passes_reference_check(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            td = pathlib.Path(tmp)
            try:
                stage_ref_pkg.resolve_corpus_repo_and_ref(None, None)
                has_git_corpus = True
            except FileNotFoundError:
                has_git_corpus = False

            if has_git_corpus:
                out_git = td / "staged_from_git"
                rc, rep = stage_ref_pkg.stage_package(
                    out_dir=out_git,
                    slug="demo-standalone-stage",
                    topics=["anneal/architecture", "verification/soundness"],
                    with_support=True,
                    max_bytes=102400,
                )
                self.assertEqual(rc, 0, rep)
                self.assertTrue(rep["passed"])
                self.assertLess(rep["total_bytes"], 102400)
                self.assertEqual(rep["check_rc"], 0)
                self.assertTrue((out_git / "CATALOG.json").is_file())
                self.assertTrue((out_git / "reports" / "demo-standalone-stage" / "support").is_dir())

                out_tpl = td / "staged_from_tpl"
                rc2, rep2 = stage_ref_pkg.stage_package(
                    out_dir=out_tpl,
                    slug="second-package-check",
                    template_dir=str(out_git),
                    max_bytes=102400,
                )
                self.assertEqual(rc2, 0, rep2)
                self.assertLess(rep2["total_bytes"], 102400)

            rc_bad, _ = stage_ref_pkg.stage_package(
                out_dir=td / "bad_slug",
                slug="Invalid_Slug!",
            )
            self.assertEqual(rc_bad, 2)


if __name__ == "__main__":
    unittest.main()
