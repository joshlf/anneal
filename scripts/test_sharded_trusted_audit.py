#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tests for `scripts/sharded_trusted_audit.py` and the Episode 2 `check_trusted.py` gates."""

from __future__ import annotations

import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))

import sharded_trusted_audit as sta  # noqa: E402

ct = sta.ct
REPO = sta.REPO_ROOT
BASE_SHA = "9d6e61cf6cdab349cd63aac1bb71d77dfddada42"
LEAN = sta.LEAN


def lean_available() -> bool:
    return LEAN.is_file()


class OrphanGateTests(unittest.TestCase):
    def _fixture(self, tmp: Path) -> Path:
        (tmp / "src/Foo").mkdir(parents=True)
        (tmp / "lakefile.toml").write_text('name = "X"\n[[lean_lib]]\nname = "Foo"\nsrcDir = "src"\n')
        (tmp / "src/Foo.lean").write_text("")
        (tmp / "src/Foo/A.lean").write_text("")
        (tmp / "tests").mkdir()
        (tmp / "tests/T.lean").write_text("")
        return tmp

    def _manifest(self, tmp: Path, shards, lakefile: bool = True) -> Path:
        path = tmp / "manifest.json"
        path.write_text(json.dumps({"lakefile_check": lakefile, "shards": shards}))
        return path

    def test_live_plan_is_complete_and_sub_second(self):
        start = time.monotonic()
        summary = sta.orphan_gate(REPO, delegate=False)
        self.assertLess(time.monotonic() - start, 1.0)
        self.assertLess(summary["seconds"], sta.ORPHAN_BUDGET_SECS)
        self.assertGreaterEqual(summary["modules"], len(ct.DOWNSTREAM_TARGETS))

    def test_live_cli_orphan_only_passes_with_delegation(self):
        proc = subprocess.run([sys.executable, "-B", str(REPO / "scripts/sharded_trusted_audit.py"), "--orphan-only"],
                              capture_output=True, text=True, check=False)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn('"delegated": true', proc.stdout)

    def test_orphaned_downstream_module_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._fixture(Path(tmp))
            targets = [("T", "tests/T.lean", [], "test"), ("Foo", "src/Foo.lean", [], "theory")]
            manifest = self._manifest(root, [{"name": "a", "modules": ["Foo"]}], lakefile=False)
            with self.assertRaises(ct.Failure) as ctx:
                ct.orphan_check(root, manifest, targets)
            self.assertEqual((ctx.exception.code, ctx.exception.phase), (1, "orphan-check"))
            self.assertIn("T", str(ctx.exception))

    def test_orphaned_lakefile_module_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._fixture(Path(tmp))
            manifest = self._manifest(root, [{"name": "a", "modules": ["Foo"]}])
            with self.assertRaises(ct.Failure) as ctx:
                ct.orphan_check(root, manifest, [])
            self.assertIn("Foo.A", str(ctx.exception))
            ok = self._manifest(root, [{"name": "a", "modules": ["Foo"]}, {"name": "b", "modules": ["Foo.A"]}])
            self.assertEqual(ct.orphan_check(root, ok, [])["modules"], 2)

    def test_unknown_module_in_manifest_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._fixture(Path(tmp))
            manifest = self._manifest(root, [{"name": "a", "modules": ["Foo", "Foo.A", "Foo.Ghost"]}])
            with self.assertRaisesRegex(ct.Failure, "unknown module"):
                ct.orphan_check(root, manifest, [])

    def test_empty_shard_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._fixture(Path(tmp))
            manifest = self._manifest(root, [{"name": "a", "modules": ["Foo", "Foo.A"]}, {"name": "b", "modules": []}])
            with self.assertRaisesRegex(ct.Failure, "empty or malformed shard"):
                ct.orphan_check(root, manifest, [])

    def test_case_folding_collision_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._fixture(Path(tmp))
            (root / "src/Foo/a.lean").write_text("")
            if not (root / "src/Foo/A.lean").is_file() or len(list((root / "src/Foo").iterdir())) < 2:
                self.skipTest("case-insensitive filesystem")
            manifest = self._manifest(root, [{"name": "a", "modules": ["Foo", "Foo.A", "Foo.a"]}])
            with self.assertRaisesRegex(ct.Failure, "case-folding"):
                ct.orphan_check(root, manifest, [])

    def test_malformed_manifest_and_cli_exit_code(self):
        with tempfile.TemporaryDirectory() as tmp:
            bad = Path(tmp) / "bad.json"
            bad.write_text("{not json")
            with self.assertRaisesRegex(ct.Failure, "unreadable shard manifest"):
                ct.orphan_check(REPO, bad)
            proc = subprocess.run([sys.executable, "-B", str(REPO / "trusted/audit/check_trusted.py"),
                                   "--orphan-only", "--shard-manifest", str(bad)],
                                  capture_output=True, text=True, check=False)
            self.assertEqual(proc.returncode, 1)
            self.assertIn("orphan-check", proc.stderr)

    def test_duplicate_in_shard_bad_flag_and_mutually_exclusive_cli_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._fixture(Path(tmp))
            dup = self._manifest(root, [{"name": "a", "modules": ["Foo", "Foo", "Foo.A"]}])
            with self.assertRaisesRegex(ct.Failure, "duplicate module"):
                ct.orphan_check(root, dup, [])
            bad_flag = root / "bad_flag.json"
            bad_flag.write_text(json.dumps({"lakefile_check": "true", "shards": [{"name": "a", "modules": ["Foo"]}]}))
            with self.assertRaisesRegex(ct.Failure, "malformed lakefile_check"):
                ct.orphan_check(root, bad_flag, [])
            proc = subprocess.run([sys.executable, "-B", str(REPO / "trusted/audit/check_trusted.py"),
                                   "--orphan-only", "--exact-modules", "Anneal.Memory"],
                                  capture_output=True, text=True, check=False)
            self.assertEqual(proc.returncode, 1)

    def test_lakefile_package_srcdir_and_symlink_rejection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "pkg/Foo").mkdir(parents=True)
            (root / "lakefile.toml").write_text('name = "X"\nsrcDir = "pkg"\n[[lean_lib]]\nname = "Foo"\n')
            (root / "pkg/Foo.lean").write_text("")
            self.assertEqual(ct.lake_modules(root), {"Foo": "pkg/Foo.lean"})
            (root / "pkg/Foo/Link.lean").symlink_to(root / "pkg/Foo.lean")
            with self.assertRaises(ct.Failure):
                ct.lake_modules(root)


class ExactModulesTests(unittest.TestCase):
    def test_transitive_closure(self):
        names = [t[0] for t in ct.resolve_exact_modules("Anneal.SepLogic")]
        for dep in ("Anneal.SepLogic", "Anneal.Memory", "Anneal.UnsafeObligations", "Anneal.ITreeWP",
                    "Anneal.EffectWP", "Anneal.ITree", "Anneal.Refinement", "Anneal.Effect"):
            self.assertIn(dep, names)
        self.assertNotIn("Anneal.PureLift.Lens", names)
        self.assertNotIn("SmokeTest", names)
        order = [t[0] for t in ct.DOWNSTREAM_TARGETS]
        self.assertEqual(names, [n for n in order if n in names])

    def test_closure_of_claim_includes_umbrella(self):
        names = {t[0] for t in ct.resolve_exact_modules("SmokeTest")}
        self.assertTrue({"SmokeTest", "Anneal", "Anneal.PureLift", "Anneal.SepLogic"} <= names)

    def test_fail_closed_on_bad_specs(self):
        for spec in ("", " ", "Anneal.Memory,", "Anneal.Memory,Anneal.Memory", "Anneal.Nope", "bad name", "a..b"):
            with self.assertRaises(ct.Failure, msg=spec) as ctx:
                ct.resolve_exact_modules(spec)
            self.assertEqual((ctx.exception.code, ctx.exception.phase), (1, "exact-modules"))

    def test_cli_rejects_unknown_module(self):
        proc = subprocess.run([sys.executable, "-B", str(REPO / "trusted/audit/check_trusted.py"),
                               "--exact-modules", "Anneal.DoesNotExist"], capture_output=True, text=True, check=False)
        self.assertEqual(proc.returncode, 1)
        self.assertIn("exact-modules", proc.stderr)

    @unittest.skipUnless(lean_available(), "pinned Lean toolchain not installed")
    def test_cli_exact_modules_positive_audit(self):
        proc = subprocess.run([sys.executable, "-B", str(REPO / "trusted/audit/check_trusted.py"), "--fast",
                               "--exact-modules", "Anneal.PureLift.Lens"], capture_output=True, text=True, check=False)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("replay-swept (lean4#16717)", proc.stdout)


FORGE_SOURCE = """namespace Forge
inductive Color where
  | red | green
inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree
end Forge
"""

FORGER_SOURCE = r"""import Lean
open Lean
def mapInd (n : Name) (f : InductiveVal → InductiveVal) : ConstantInfo → ConstantInfo
  | .inductInfo v => if v.name == n then .inductInfo (f v) else .inductInfo v
  | c => c
def main (args : List String) : IO Unit := do
  let [inp, out, mode] := args | throw (IO.userError "usage: IN OUT MODE")
  let (d, _) ← readModuleData inp
  let C := `Forge.Color
  let cs := d.constants
  let cs := match mode with
    | "self_not_in_all" => cs.map (mapInd C fun v => { v with all := [`Forge.Tree] })
    | "empty_all" => cs.map (mapInd C fun v => { v with all := [] })
    | "non_induct_in_all" => cs.map (mapInd C fun v => { v with all := [C, `Forge.Color.red] })
    | "non_ctor_in_ctors" => cs.map (mapInd C fun v => { v with ctors := v.ctors ++ [`Forge.Color.rec] })
    | "num_indices" => cs.map (mapInd C fun v => { v with numIndices := 1 })
    | "num_params" => cs.map (mapInd C fun v => { v with numParams := 1 })
    | "is_rec" => cs.map (mapInd C fun v => { v with isRec := true })
    | "is_reflexive" => cs.map (mapInd `Forge.Tree fun v => { v with isReflexive := true })
    | "dangling_ctor" => cs.map (mapInd C fun v => { v with ctors := [`Forge.Color.red] })
    | "dangling_rec" => cs.map fun c => match c with
      | .recInfo r => if r.name == `Forge.Tree.rec then .recInfo { r with all := [`Forge.Nope] } else c
      | _ => c
    | "dropped_rec" => cs.filter (·.name != `Forge.Color.rec)
    | "ctor_cidx" => cs.map fun c => match c with
      | .ctorInfo v => if v.name == `Forge.Color.green then .ctorInfo { v with cidx := 0 } else c
      | _ => c
    | "rec_minors" => cs.map fun c => match c with
      | .recInfo r => if r.name == `Forge.Color.rec then .recInfo { r with numMinors := 3 } else c
      | _ => c
    | "in_module_duplicate" =>
      match cs.find? (·.name == `Forge.Color.red) with
      | some c => cs.push c
      | none => cs
    | "replaced_rec_with_axiom" => cs.map fun c => match c with
      | .recInfo r => if r.name == `Forge.Color.rec then
          .axiomInfo { name := r.name, levelParams := r.levelParams, type := r.type, isUnsafe := false }
        else c
      | _ => c
    | "unsafe_inductive" => cs.map fun c => match c with
      | .inductInfo v => if v.name == C then .inductInfo { v with isUnsafe := true } else c
      | .ctorInfo v => if v.induct == C then .ctorInfo { v with isUnsafe := true } else c
      | .recInfo r => if r.all.contains C then .recInfo { r with isUnsafe := true } else c
      | _ => c
    | "extra_forged_recursor" =>
      match cs.find? (·.name == `Forge.Color.rec) with
      | some (.recInfo r) => cs.push (.recInfo { r with name := `Forge.Color.fakeRec })
      | _ => cs
    | _ => cs
  let names := cs.map (·.name)
  let names := if mode == "missing_constname" then names.pop else names
  saveModuleData out `Forge { d with constants := cs, constNames := names }
"""

FORGERY_MODES = ("self_not_in_all", "empty_all", "non_induct_in_all", "non_ctor_in_ctors", "num_indices",
                 "num_params", "is_rec", "is_reflexive", "dangling_ctor", "dangling_rec", "dropped_rec", "ctor_cidx",
                 "rec_minors", "missing_constname", "in_module_duplicate", "replaced_rec_with_axiom",
                 "unsafe_inductive", "extra_forged_recursor")


@unittest.skipUnless(lean_available(), "pinned Lean toolchain not installed")
class InductiveReplayForgeryTests(unittest.TestCase):
    """Real binary `.olean` forgeries (`Lean.saveModuleData`) against the `lean4#16717` check."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix="anneal-forge-")
        root = Path(cls.tmp.name)
        (root / "Forge.lean").write_text(FORGE_SOURCE)
        (root / "Forger.lean").write_text(FORGER_SOURCE)
        subprocess.run([str(LEAN), "-o", str(root / "Forge.olean"), str(root / "Forge.lean")],
                       cwd=root, check=True, capture_output=True)
        cls.forged: dict[str, Path] = {}
        for mode in ("clean",) + FORGERY_MODES:
            out = root / f"{mode}" / "Forge.olean"
            out.parent.mkdir()
            subprocess.run([str(LEAN), "--run", str(root / "Forger.lean"), str(root / "Forge.olean"), str(out), mode],
                           cwd=root, check=True, capture_output=True)
            cls.forged[mode] = out
        cls.checker = ct.Checker(REPO, fast=True)
        cls.checker.tool_admission()

    @classmethod
    def tearDownClass(cls):
        ct.make_tree_writable(cls.checker.stage)
        shutil.rmtree(cls.checker.stage, ignore_errors=True)
        cls.tmp.cleanup()

    def replay(self, mode: str) -> dict:
        self.checker.artifacts["Forge"] = [[str(self.forged[mode])], []]
        try:
            return self.checker.inspect("inductive-replay-downstream", targets=["Forge"], roots=["Forge"])
        finally:
            self.checker.artifacts.pop("Forge", None)

    def assert_rejected(self, mode: str, needle: str | None = None) -> None:
        with self.assertRaises(ct.Failure, msg=mode) as ctx:
            self.replay(mode)
        self.assertEqual(ctx.exception.code, 1, f"{mode}: {ctx.exception}")
        if needle:
            self.assertIn(needle, str(ctx.exception))

    def test_clean_module_passes(self):
        result = self.replay("clean")
        self.assertEqual(result["inductiveConstants"], 8)  # 2 inductives + 4 constructors + 2 recursors

    def test_self_not_in_all(self):
        self.assert_rejected("self_not_in_all", "malformed all/ctors")

    def test_empty_all(self):
        self.assert_rejected("empty_all", "malformed all/ctors")

    def test_non_inductive_in_all(self):
        self.assert_rejected("non_induct_in_all", "non-inductive")

    def test_non_constructor_in_ctors(self):
        self.assert_rejected("non_ctor_in_ctors", "non-constructor")

    def test_forged_num_indices_caught_only_after_replay(self):
        self.assert_rejected("num_indices")

    def test_forged_num_params(self):
        self.assert_rejected("num_params")

    def test_forged_is_rec_caught_only_after_replay(self):
        self.assert_rejected("is_rec")

    def test_forged_is_reflexive_caught_only_after_replay(self):
        self.assert_rejected("is_reflexive", "post-replay metadata mismatch")

    def test_dangling_constructor(self):
        self.assert_rejected("dangling_ctor", "dangling constructor")

    def test_dangling_recursor(self):
        self.assert_rejected("dangling_rec", "dangling recursor")

    def test_dropped_kernel_recursor(self):
        self.assert_rejected("dropped_rec", "dropped from module data")

    def test_constructor_index(self):
        self.assert_rejected("ctor_cidx", "constructor metadata mismatch")

    def test_post_replay_recursor_mismatch(self):
        self.assert_rejected("rec_minors")

    def test_missing_const_name_entry(self):
        self.assert_rejected("missing_constname", "missing_constName_entry")

    def test_pre_replay_self_comparison_alone_misses_post_replay_forgeries(self):
        # The stored entries of these forgeries are internally consistent: every structural
        # (pre-replay) invariant holds, and only the kernel-regenerated comparison rejects them.
        for mode in ("is_reflexive", "is_rec", "num_indices"):
            with self.assertRaises(ct.Failure) as ctx:
                self.replay(mode)
            message = str(ctx.exception)
            self.assertTrue("post-replay" in message or "kernel replay rejected" in message, f"{mode}: {message}")

    def test_in_module_duplicate_replaced_rec_unsafe_and_extra_rec_rejected(self):
        self.assert_rejected("in_module_duplicate", "duplicate")
        self.assert_rejected("replaced_rec_with_axiom", "replaced in module data")
        self.assert_rejected("unsafe_inductive")
        self.assert_rejected("extra_forged_recursor", "Forge.Color.fakeRec")

    def test_cross_module_inductive_axiom_kind_conflation_rejected(self):
        # Module Forge defines `inductive Forge.Color`; sibling module ForgeSib defines
        # `axiom Forge.Color : Type` with identical type/levelParams (both `value? true = none`).
        root = Path(self.tmp.name)
        sib_src = root / "ForgeSib.lean"
        sib_src.write_text("namespace Forge\naxiom Color : Type\nend Forge\n")
        sib_olean = root / "ForgeSib.olean"
        subprocess.run([str(LEAN), "-o", str(sib_olean), str(sib_src)], cwd=root, check=True, capture_output=True)
        self.checker.artifacts["Forge"] = [[str(self.forged["clean"])], []]
        self.checker.artifacts["ForgeSib"] = [[str(sib_olean)], []]
        try:
            with self.assertRaises(ct.Failure) as ctx:
                self.checker.inspect("inductive-replay-downstream", targets=["Forge", "ForgeSib"],
                                     roots=["Forge", "ForgeSib"])
            self.assertEqual(ctx.exception.code, 1)
            self.assertIn("conflicting duplicate target constant", str(ctx.exception))
        finally:
            self.checker.artifacts.pop("Forge", None)
            self.checker.artifacts.pop("ForgeSib", None)


RECONCILE_A = "namespace Shared\ndef lit : Nat := 3\naxiom conflated : Nat\ntheorem same : True := trivial\nend Shared\n"
RECONCILE_B = ("namespace Shared\ndef lit : Nat := 18446744073709551619\ndef conflated : Nat := 0\n"
               "theorem same : True := True.intro\nend Shared\n")
RECONCILE_C = "namespace Other\ndef unique : Nat := 1\nend Other\n"


@unittest.skipUnless(lean_available(), "pinned Lean toolchain not installed")
class ReconciliationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix="anneal-reconcile-test-")
        root = Path(cls.tmp.name)
        cls.oleans = {}
        for name, source in (("A", RECONCILE_A), ("B", RECONCILE_B), ("C", RECONCILE_C)):
            (root / f"{name}.lean").write_text(source)
            subprocess.run([str(LEAN), "-o", str(root / f"{name}.olean"), str(root / f"{name}.lean")],
                           cwd=root, check=True, capture_output=True)
            cls.oleans[name] = root / f"{name}.olean"

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_conflicting_siblings_detected(self):
        result = sta.reconcile({"s1": [("A", self.oleans["A"])], "s2": [("B", self.oleans["B"])]})
        conflicting = {c[0] for c in result["conflicts"]}
        # `2 ^ 64`-apart literals and an axiom vs a definition of the same name and type.
        self.assertIn("Shared.lit", conflicting)
        self.assertIn("Shared.conflated", conflicting)
        # Theorems are compared by statement (proof irrelevance): benign.
        self.assertNotIn("Shared.same", conflicting)
        self.assertGreaterEqual(result["candidates"], 3)

    def test_identical_and_disjoint_shards_are_clean(self):
        same = sta.reconcile({"s1": [("A", self.oleans["A"])], "s2": [("A", self.oleans["A"])]})
        self.assertEqual(same["conflicts"], [])
        disjoint = sta.reconcile({"s1": [("A", self.oleans["A"])], "s2": [("C", self.oleans["C"])]})
        self.assertEqual((disjoint["candidates"], disjoint["conflicts"]), (0, []))

    def test_headers_are_bijective_9_tuples(self):
        result = sta.reconcile({"s1": [("A", self.oleans["A"])], "s2": [("C", self.oleans["C"])]})
        self.assertEqual(result["declarations"], result["headers"]["s1"] + result["headers"]["s2"])

    def test_live_lake_reconciliation_has_no_conflicts(self):
        result = sta.reconcile_lake(REPO, required=False)
        self.assertEqual(result["conflicts"], [])
        self.assertLessEqual(result["unbuiltOrStaleModules"], len(ct.lake_modules(REPO)))

    def test_foreign_or_stale_lake_builds_are_never_reconciled(self):
        import os
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "src").mkdir()
            source = root / "src/Foo.lean"
            source.write_text("def x := 1\n")
            build = root / ".lake/build/lib/lean"
            build.mkdir(parents=True)
            olean, trace = build / "Foo.olean", build / "Foo.trace"
            olean.write_bytes(b"olean")
            # Built from this checkout: usable.
            trace.write_text(json.dumps({"inputs": [[str(source.resolve()), "0123"]]}))
            self.assertEqual(sta.fresh_lake_olean(root, "Foo", "src/Foo.lean"), olean)
            # Built from a different checkout (a copied `.lake`): rejected.
            trace.write_text(json.dumps({"inputs": [["/elsewhere/src/Foo.lean", "0123"]]}))
            self.assertIsNone(sta.fresh_lake_olean(root, "Foo", "src/Foo.lean"))
            # Built from this checkout but older than the source: rejected.
            trace.write_text(json.dumps({"inputs": [[str(source.resolve()), "0123"]]}))
            stamp = source.stat().st_mtime
            os.utime(olean, (stamp - 100, stamp - 100))
            self.assertIsNone(sta.fresh_lake_olean(root, "Foo", "src/Foo.lean"))
            # Missing trace: rejected.
            os.utime(olean, (stamp + 100, stamp + 100))
            trace.unlink()
            self.assertIsNone(sta.fresh_lake_olean(root, "Foo", "src/Foo.lean"))
            # Wrong Module.name in trace: rejected.
            trace.write_text(json.dumps({"inputs": [[str(source.resolve()), "0123"], ["Module.name: Bar", "4567"]]}))
            self.assertIsNone(sta.fresh_lake_olean(root, "Foo", "src/Foo.lean"))
            # Matching Module.name: accepted.
            trace.write_text(json.dumps({"inputs": [[str(source.resolve()), "0123"], ["Module.name: Foo", "4567"]]}))
            self.assertEqual(sta.fresh_lake_olean(root, "Foo", "src/Foo.lean"), olean)
            # Substring-only match inside an unrelated nested field: rejected.
            trace.write_text(json.dumps({"inputs": [["note", str(source.resolve())]]}))
            self.assertIsNone(sta.fresh_lake_olean(root, "Foo", "src/Foo.lean"))
            # Symlink olean: rejected.
            real_olean = build / "Real.olean"
            olean.rename(real_olean)
            olean.symlink_to(real_olean)
            trace.write_text(json.dumps({"inputs": [[str(source.resolve()), "0123"]]}))
            self.assertIsNone(sta.fresh_lake_olean(root, "Foo", "src/Foo.lean"))

    def test_declaration_names_hash_distinguishes_equal_count_different_sets(self):
        r_a = sta.reconcile({"s": [("A", self.oleans["A"])]})
        r_c = sta.reconcile({"s": [("C", self.oleans["C"])]})
        self.assertNotEqual(r_a["declarationNamesHash"], r_c["declarationNamesHash"])
        r_a2 = sta.reconcile({"s": [("A", self.oleans["A"])]})
        self.assertEqual(r_a["declarationNamesHash"], r_a2["declarationNamesHash"])

    def test_same_shard_conflict_and_bijective_numeric_dotted_names_detected(self):
        # Two conflicting modules in the SAME shard must still be detected.
        same_shard = sta.reconcile({"s1": [("A", self.oleans["A"]), ("B", self.oleans["B"])]})
        self.assertIn("Shared.lit", {c[0] for c in same_shard["conflicts"]})
        # Synthesize two `.olean`s with conflicting `Name.num` and dotted `Name.str` constants
        # where naive `Name.toString` / `String.toName` roundtrip loses the distinction.
        root = Path(self.tmp.name)
        synth = root / "SynthNames.lean"
        synth.write_text(r"""import Lean
open Lean
def mkConst (n : Name) (v : Nat) : ConstantInfo :=
  .defnInfo { name := n, levelParams := [], type := .const `Nat [],
              value := .lit (.natVal v), hints := .opaque, safety := .safe }
def main (args : List String) : IO Unit := do
  let [inp, out1, out2] := args | throw (IO.userError "bad args")
  let (d, _) ← readModuleData inp
  let nNum : Name := .num (.str .anonymous "Shared") 1
  let nDot : Name := .str (.str .anonymous "Shared") "a.b"
  let cs1 := #[mkConst nNum 1, mkConst nDot 1]
  let cs2 := #[mkConst nNum 2, mkConst nDot 2]
  saveModuleData out1 `N1 { d with constants := cs1, constNames := cs1.map (·.name) }
  saveModuleData out2 `N2 { d with constants := cs2, constNames := cs2.map (·.name) }
""")
        n1, n2 = root / "N1.olean", root / "N2.olean"
        subprocess.run([str(LEAN), "--run", str(synth), str(self.oleans["C"]), str(n1), str(n2)],
                       cwd=root, check=True, capture_output=True)
        res = sta.reconcile({"s1": [("N1", n1)], "s2": [("N2", n2)]})
        self.assertEqual(res["candidates"], 2)
        self.assertEqual(len(res["conflicts"]), 2)


class PlannerTests(unittest.TestCase):
    def test_plan_is_deterministic_and_complete(self):
        a, b = sta.plan_shards(REPO), sta.plan_shards(REPO)
        self.assertEqual(a, b)
        covered = {m for s in a["shards"] for m in s["modules"]}
        self.assertTrue({t[0] for t in ct.DOWNSTREAM_TARGETS} <= covered)
        self.assertTrue(set(ct.lake_modules(REPO)) <= covered)

    def test_rustc_mir_is_sub_sharded_and_balanced(self):
        shards = [s for s in sta.plan_shards(REPO)["shards"] if s["name"].startswith("lake/RustcMir-")]
        self.assertEqual(len(shards), sta.RUSTC_MIR_SUBSHARDS)
        mods = ct.lake_modules(REPO)
        loads = [sum((REPO / mods[m]).stat().st_size for m in s["modules"]) for s in shards]
        biggest = max((REPO / mods[m]).stat().st_size for s in shards for m in s["modules"])
        self.assertLessEqual(max(loads) - min(loads), biggest)

    def test_balanced_split_properties(self):
        bins = sta.balanced_split([("a", 5), ("b", 4), ("c", 3), ("d", 3), ("e", 1)], 2)
        self.assertEqual(sorted(sum(bins, [])), ["a", "b", "c", "d", "e"])
        self.assertEqual(len(bins), 2)
        self.assertEqual(sta.balanced_split([("a", 1)], 4), [["a"]])


def scan_text(text: str, name: str = "Fixture.lean") -> dict:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / name
        path.write_text(text)
        return sta.scan_peer_guards([path], Path(tmp))


class PeerGuardScannerTests(unittest.TestCase):
    def assert_violation(self, text: str, guard: str, needle: str = ""):
        with self.assertRaises(sta.GuardViolation) as ctx:
            scan_text(text)
        self.assertEqual(ctx.exception.guard, guard)
        self.assertIn(needle, ctx.exception.reason)

    def test_6a_antecedent_placement_passes(self):
        scan_text("axiom assumesHold : Prop\ntheorem t (h : assumesHold) : True := trivial\n"
                  "theorem u : assumesHold → True := fun _ => trivial\n"
                  "theorem v : ∀ (h : assumesHold) (n : Nat), n = n := fun _ _ => rfl\n")

    def test_6a_positive_iff_if_and_negated_antecedent_rejected(self):
        self.assert_violation("theorem t : True ∧ assumesHold := sorry\n", "6a", "positive")
        self.assert_violation("theorem t : assumesHold ↔ True := sorry\n", "6a", "iff")
        self.assert_violation("theorem t : (if assumesHold then True else False) := sorry\n", "6a", "if condition")
        self.assert_violation("theorem t (h : ¬ assumesHold) : True := sorry\n", "6a", "antecedent")
        self.assert_violation("theorem t : decide assumesHold = true → True := sorry\n", "6a", "unclean")

    def test_6a_let_alias_inlining_and_depth_bound(self):
        self.assert_violation("theorem t : let h := assumesHold; True ∧ h := sorry\n", "6a", "positive")
        scan_text("theorem t : let h := assumesHold; h → True := sorry\n")
        chain = "".join(f"let a{i} := {'assumesHold' if i == 0 else f'a{i - 1}'}; " for i in range(9))
        self.assert_violation(f"theorem t : {chain}a8 → True := sorry\n", "6a", "depth 8")

    def test_6a_helper_definition_indirection(self):
        self.assert_violation("def helper : Prop := ¬ assumesHold\ntheorem t : helper → True := sorry\n", "6a")
        self.assert_violation("abbrev bad : Prop := assumesHold\n", "6a", "positive")

    def test_6a_dot_notation_constructor_is_not_the_atom(self):
        scan_text("inductive F | assumesHold | tt\ndef e : F → Prop | .assumesHold => True | .tt => False\n"
                  "theorem x : e F.assumesHold := trivial\n")

    def test_6a_red_team_bypasses_match_nested_if_pi_let_and_multifile(self):
        # `match` inside theorem statement must NOT truncate `sig` at `|`!
        self.assert_violation(
            "theorem evil (x : Nat) : match x with | 0 => assumesHold | _ => True := trivial\n", "6a")
        # Keyword inside parens must NOT truncate declaration bounds!
        self.assert_violation("theorem evil (end : Nat) : assumesHold := sorry\n", "6a", "positive")
        # Nested unparenthesized `if` must match inner/outer `else` properly!
        self.assert_violation("theorem evil : if a then if b then True else assumesHold else True := sorry\n",
                              "6a", "positive")
        # `Π` and dependent arrow `(h : assumesHold) → P`
        scan_text("theorem ok1 : Π (h : assumesHold), True := fun _ => trivial\n"
                  "theorem ok2 : (h : assumesHold) → True := fun _ => trivial\n"
                  "theorem ok3 : let p := assumesHold in p → True := fun _ => trivial\n")
        self.assert_violation("theorem bad1 : Π (h : ¬ assumesHold), True := sorry\n", "6a", "antecedent")
        self.assert_violation("theorem bad2 : (h : ¬ assumesHold) → True := sorry\n", "6a", "antecedent")
        self.assert_violation("theorem bad3 : let p : assumesHold := h; True := sorry\n", "6a", "type annotation")
        self.assert_violation("theorem bad4 : let p := assumesHold in True ∧ p := sorry\n", "6a", "positive")
        # Multi-file transitive helper chain (FileA -> FileB -> FileC with namespace prefix)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "A.lean").write_text("namespace Foo\ndef h1 : Prop := ¬ assumesHold\nend Foo\n")
            (root / "B.lean").write_text("namespace Foo\ndef h2 : Prop := h1\nend Foo\n")
            (root / "C.lean").write_text("theorem leak : Foo.h2 → True := sorry\n")
            with self.assertRaises(sta.GuardViolation) as ctx:
                sta.scan_peer_guards([root], root)
            self.assertEqual(ctx.exception.guard, "6a")

    def test_6b_sealed_structure_with_smart_constructor_passes(self):
        scan_text("/-- @invariant lo ≤ hi -/\nstructure R where\n  private mk ::\n  lo : Nat\n  hi : Nat\n  h : lo ≤ hi\n\n"
                  "private def rawHelper (a : Nat) : R := R.mk a a (Nat.le_refl a)\n"
                  "/-- @smart_constructor -/\ndef R.make (a : Nat) : R := rawHelper a\n"
                  "def R.width (r : R) : Nat := r.hi - r.lo\n"
                  "def shadow (mk : Nat → Nat) : Nat := mk 0\n"
                  "open R in\n/-- @smart_constructor -/\ndef R.makeOpen (a : Nat) : R := mk a a (Nat.le_refl a)\n"
                  "def unrelatedAfterOpenIn : Nat := mk 0\n"
                  "section\nopen R\n/-- @smart_constructor -/\ndef R.makeSec (a : Nat) : R := mk a a (Nat.le_refl a)\nend\n"
                  "def unrelatedAfterSection : Nat := mk 0\n")

    def test_6b_unsealed_and_inhabited_rejected(self):
        self.assert_violation("/-- @invariant -/\nstructure R where\n  mk ::\n  lo : Nat\n", "6b", "private")
        self.assert_violation("/-- @invariant -/\nstructure R where\n  lo : Nat\n", "6b", "private")
        self.assert_violation("/-- @invariant -/\nstructure R where\n  private mk ::\n  lo : Nat\nderiving Inhabited\n",
                              "6b", "Inhabited")
        self.assert_violation("/-- @invariant -/\nstructure R where\n  private mk ::\n  lo : Nat\n\n"
                              "deriving instance Inhabited for R\n", "6b", "Inhabited")
        self.assert_violation("/-- @invariant -/\nstructure R where\n  private mk ::\n  lo : Nat\n\n"
                              "instance : Inhabited R := ⟨R.mk 0⟩\n", "6b", "Inhabited")
        self.assert_violation("/-- @invariant -/\nstructure R where\n  private mk ::\n  lo : Nat\nderiving\n  Inhabited\n",
                              "6b", "Inhabited")
        self.assert_violation("/-- @invariant -/\nstructure R where\n  private mk ::\n  lo : Nat\n\n"
                              "deriving instance\n  Inhabited\n  for R\n", "6b", "Inhabited")

    def test_6b_constructor_leaks_rejected(self):
        head = "/-- @invariant -/\nstructure R where\n  private mk ::\n  lo : Nat\n\n"
        self.assert_violation(head + "def leak (n : Nat) : R := R.mk n\n", "6b", "raw constructor")
        self.assert_violation(head + "namespace R\ndef leak (n : Nat) : R := mk n\nend R\n", "6b", "raw constructor")
        self.assert_violation(head + "open R in\ndef leak (n : Nat) : R := mk n\n", "6b", "raw constructor")
        self.assert_violation(head + "open R renaming mk → build\ndef leak (n : Nat) : R := build n\n", "6b",
                              "raw constructor")
        self.assert_violation(head + "open R renaming\n  mk → build\ndef leak (n : Nat) : R := build n\n", "6b",
                              "raw constructor")
        self.assert_violation(head + "abbrev Build := R.mk\ndef leak (n : Nat) : R := Build n\n", "6b",
                              "raw constructor")
        self.assert_violation(head + "abbrev RAlias := R\ndef leak (n : Nat) : R := RAlias.mk n\n", "6b",
                              "raw constructor")
        self.assert_violation(head + "abbrev RAlias := R\nderiving instance Inhabited for RAlias\n", "6b", "Inhabited")
        self.assert_violation(head + "abbrev RAlias := R\nclass Carrier extends RAlias where\n  extra : Nat\n", "6b",
                              "carrier")
        self.assert_violation(head + "structure Carrier extends R where\n  extra : Nat\n", "6b", "carrier")
        # Private helper transitive forwarding to non-@smart_constructor public def
        self.assert_violation(head + "private def rawH (n : Nat) : R := R.mk n\ndef leak (n : Nat) : R := rawH n\n",
                              "6b", "raw constructor")
        # Lexical shadowing bypasses: inner `fun mk` or later `let mk` must NOT hide unshadowed `mk`!
        self.assert_violation(head + "open R\ndef leak (n : Nat) : R := let _ := (fun mk => mk) 0; mk n\n",
                              "6b", "raw constructor")
        self.assert_violation(head + "open R\ndef leak (n : Nat) : R := let x := mk n; let mk := 0; x\n",
                              "6b", "raw constructor")
        # Anonymous constructor, structure literal, nested-paren, instance, and `.mk` dot-notation bypasses
        self.assert_violation(head + "def leak (n : Nat) : R := ⟨n⟩\n", "6b", "raw constructor")
        self.assert_violation(head + "def leak (n : Nat) : R := id (⟨n⟩)\n", "6b", "raw constructor")
        self.assert_violation(head + "def leak (n : Nat) : R := { lo := n }\n", "6b", "raw constructor")
        self.assert_violation(head + "def leak (n : Nat) : R := let r := ({ lo := n }); r\n", "6b", "raw constructor")
        self.assert_violation(head + "def leak (n : Nat) : Nat × R := (0, { lo := n })\n", "6b", "raw constructor")
        self.assert_violation(head + "def leak (n : Nat) : R := .mk n\n", "6b", "raw constructor")
        self.assert_violation(head + "def leak (n : Nat) : Option R := some (.mk n)\n", "6b", "raw constructor")
        self.assert_violation(head + "class Maker (α : Type) where make : Nat → α\n"
                              "instance : Maker R where make n := ⟨n⟩\n", "6b", "raw constructor")
        self.assert_violation(head + "class Maker (α : Type) where make : Nat → α\n"
                              "instance : Maker R where make n := .mk n\n", "6b", "raw constructor")
        # Namespace-qualified `@invariant` structure accessed from outside namespace
        ns_head = "namespace Foo\n/-- @invariant -/\nstructure R where\n  private mk ::\n  lo : Nat\nend Foo\n\n"
        self.assert_violation(ns_head + "def leak (n : Nat) : Foo.R := Foo.R.mk n\n", "6b", "raw constructor")

    def test_6a_spelling_renaming_and_notation_bypasses_rejected(self):
        self.assert_violation("theorem t : True \u2227 \u00abassumesHold\u00bb := sorry\n", "6a", "positive")
        self.assert_violation("theorem t : True \u2227 _root_.assumesHold := sorry\n", "6a", "positive")
        self.assert_violation("theorem t : True \u2227 Verifrag.\u00abassumesHold\u00bb := sorry\n", "6a", "positive")
        self.assert_violation("open Verifrag renaming assumesHold \u2192 ok\ntheorem t : True \u2227 ok := sorry\n",
                              "6a", "positive")
        scan_text("open Verifrag renaming assumesHold \u2192 ok\ntheorem t : ok \u2192 True := fun _ => trivial\n")
        self.assert_violation("local notation \"AH\" => assumesHold\ntheorem t : AH := sorry\n", "6a", "notation")
        self.assert_violation("macro \"AH\" : term => `(assumesHold)\ntheorem t : AH := sorry\n", "6a", "notation")
        self.assert_violation("def h : Prop := assumesHold \u2192 True\nnotation \"H\" => h\n", "6a", "notation")

    def test_live_theory_has_zero_false_positives(self):
        summary = sta.scan_peer_guards([REPO / "theory/Anneal"])
        self.assertGreater(summary["files"], 50)


class CheckTrustedBudgetTests(unittest.TestCase):
    def test_check_trusted_net_added_lines_within_budget(self):
        out = subprocess.run(["git", "diff", "--numstat", BASE_SHA, "--", "trusted/audit/check_trusted.py"],
                             cwd=REPO, capture_output=True, text=True, check=True).stdout.split()
        added, deleted = (int(out[0]), int(out[1])) if out else (0, 0)
        self.assertLessEqual(added - deleted, 250)
        self.assertLessEqual(len((REPO / "trusted/audit/check_trusted.py").read_text().splitlines()), 7963 + 250)

    def test_shared_auditor_block_byte_identical(self):
        def block(path: Path) -> str:
            text = path.read_text()
            start = text.index("# BEGIN SHARED WAIVER-PIN & 3-AXIS AUDITOR")
            return text[start: text.index("# END SHARED WAIVER-PIN & 3-AXIS AUDITOR")]
        self.assertEqual(block(REPO / "trusted/audit/check_trusted.py"),
                         block(REPO / "tools/anneal-lsp/server/proof_health.py"))

    def test_check_trusted_stays_stdlib_only_and_never_imports_this_script(self):
        text = (REPO / "trusted/audit/check_trusted.py").read_text()
        self.assertNotIn("sharded_trusted_audit", text)
        self.assertIn("INDUCTIVE_REPLAY_SOURCE", text)


if __name__ == "__main__":
    unittest.main()
