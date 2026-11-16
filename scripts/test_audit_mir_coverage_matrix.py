#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `scripts/audit_mir_coverage_matrix.py`.

Each check is exercised on a temporary fixture repository holding only the files the audit
reads (real copies, plus small textual stand-ins for the two big theory modules and a synthetic
correspondence test), and every check is shown to reject a targeted mutant.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import audit_mir_coverage_matrix as audit  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent
AUDIT_SCRIPT = REPO_ROOT / "scripts" / "audit_mir_coverage_matrix.py"
SUITE = "scripts/run_nightly_verification_suite.py"
STATEMENTS = f"{audit.MIR_AST_DIR}/Statements.lean"
STEP_LEAN = "lean-miri/vendor/Miri/Interpreter/Step.lean"
CORR = audit.UNTESTED_VARIANT_TEST

COPIED_FILES: tuple[str, ...] = (
    SUITE,
    *audit.MIR_AST_FILES,
    "trusted/rustc-capture/src/rustc_2026_06_01/mir_lower.rs",
    "minirust/coverage.json",
    audit.LEAN_MIRI_PIN,
    audit.MINIRUST_LOCK,
    audit.SLICE_LENS_TEST,
    *sorted({rel for rel, _snippet in audit.REQUIRED_SOURCE_ANCHORS}),
)

# Textual stand-in for `theory/Anneal/SepLogicLenses.lean` (the audit never compiles it).
SEP_LOGIC_LENSES_STUB = """\
namespace Anneal.SepLogicLenses

def DisjointSlice (base₁ len₁ base₂ len₂ : Nat) : Prop :=
  base₁ + len₁ ≤ base₂ ∨ base₂ + len₂ ≤ base₁

theorem DisjointSlice.adjacent (base len₁ len₂ : Nat) :
    DisjointSlice base len₁ (base + len₁) len₂ := Or.inl (Nat.le_refl _)

section SliceWidePtrLenses

abbrev WidePtrVal : Type := Nat × Nat

def SliceTypedAt (wide : WidePtrVal) (xs : List Nat) : Prop := wide.2 = xs.length

namespace SliceTypedAt

theorem splitAt {wide : WidePtrVal} {xs : List Nat} (h : SliceTypedAt wide xs) : True := trivial

theorem of_splitAt {wide : WidePtrVal} {xs : List Nat} (h : SliceTypedAt wide xs) : True := trivial

end SliceTypedAt

def ActiveTypedSliceBorrow (wide : WidePtrVal) : Prop := True

def ActiveTypedSliceMutBorrow (wide : WidePtrVal) : Prop := True

end SliceWidePtrLenses

end Anneal.SepLogicLenses
"""

MANIFEST_LINES = (
    "-- @mir-variant-coverage StatementKind.constEvalCounter trusted=cec_trusted_step "
    "minirust=cec_minirust_skip leanmiri=cec_leanmiri_noop positive=cec_positive negative=cec_negative",
    "-- @mir-variant-coverage TerminatorKind.tailCall trusted=tail_trusted_frame "
    "minirust=tail_minirust_translate leanmiri=tail_leanmiri_root positive=tail_positive "
    "negative=tail_negative_arity,tail_negative_root",
    "-- @mir-variant-coverage ProjectionElem.opaqueCast trusted=opaque_trusted_read "
    "minirust=opaque_minirust leanmiri=opaque_leanmiri_guard positive=opaque_positive "
    "negative=opaque_negative",
)

# Synthetic stand-in for the correspondence test: satisfies every textual check of (c)/(e).
CORRESPONDENCE_TEMPLATE = """\
/-
Synthetic fixture (never compiled). Comments may say sorry, admit, axiom, native_decide,
sorryAx or Lean.ofReduceBool, and mention `@source-anchor` / `@mir-variant-coverage` in prose.
-/
import Trusted
import Lean.Elab.Command

{manifest}

{anchors}

namespace Anneal.FixtureCoverage

/-- Docstrings are comments too: `sorry`, `axiom`, `unsafe`. -/
def constEvalCounterStmt : Nat := 0

def cecProgram : Nat := constEvalCounterStmt + 1

theorem cec_trusted_step : cecProgram = 1 := rfl
theorem cec_minirust_skip : constEvalCounterStmt = 0 := rfl
theorem cec_leanmiri_noop : cecProgram = cecProgram := rfl
theorem cec_positive : cecProgram ≠ 0 := by decide
@[simp] theorem cec_negative : cecProgram ≠ 2 := by decide

def tailCallTerm : Nat := 7

theorem tail_trusted_frame : tailCallTerm = 7 := rfl
theorem tail_minirust_translate : tailCallTerm + 0 = 7 := rfl
theorem tail_leanmiri_root : tailCallTerm ≠ 0 := by decide
theorem tail_positive : tailCallTerm > 6 := by decide
/-- Arity mismatch is UB. -/
theorem tail_negative_arity : tailCallTerm ≠ 8 := by decide
private theorem tail_negative_root : tailCallTerm ≠ 9 := by decide

def opaqueCastProj : Nat := 3

theorem opaque_trusted_read : opaqueCastProj = 3 := rfl
theorem opaque_minirust : opaqueCastProj ≠ 0 := by decide
theorem opaque_leanmiri_guard : opaqueCastProj < 4 := by decide
theorem opaque_positive : opaqueCastProj > 2 := by decide
theorem opaque_negative : opaqueCastProj ≠ 5 := by decide

def banner : String := "strings may say sorry, admit, axiom or native_decide"
def braceChar : Char := '"'

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ns := `Anneal.FixtureCoverage
  let forbidden : List Name := [``sorryAx, ``Lean.ofReduceBool]
  let manifest : List Name := [`cec_trusted_step, `cec_minirust_skip, `cec_leanmiri_noop,
    `cec_positive, `cec_negative, `tail_trusted_frame, `tail_minirust_translate,
    `tail_leanmiri_root, `tail_positive, `tail_negative_arity, `tail_negative_root,
    `opaque_trusted_read, `opaque_minirust, `opaque_leanmiri_guard, `opaque_positive,
    `opaque_negative]
  for short in manifest do
    unless (env.find? (ns ++ short)).isSome do throwError "missing manifest theorem {{short}}"
  for (n, _) in env.constants.map₂.toList do
    if ns.isPrefixOf n then
      let axs ← liftCoreM <| collectAxioms n
      for a in axs do
        if forbidden.contains a then
          throwError "{{n}} depends on forbidden axiom {{a}}"

end Anneal.FixtureCoverage
"""


def correspondence_source(manifest: tuple[str, ...] = MANIFEST_LINES, anchors: tuple[tuple[str, str], ...] | None = None) -> str:
    anchor_list = audit.REQUIRED_SOURCE_ANCHORS if anchors is None else anchors
    return CORRESPONDENCE_TEMPLATE.format(
        manifest="\n".join(manifest),
        anchors="\n".join(f"-- @source-anchor {rel}#{snippet}" for rel, snippet in anchor_list),
    )


def lintrinsic_stub() -> str:
    """The real `inductive LIntrinsicOp` block of `theory/Anneal/Mir/AdtAndControl.lean`."""
    lines = (REPO_ROOT / audit.LINTRINSIC_FILE).read_text(encoding="utf-8").splitlines()
    start = next(i for i, ln in enumerate(lines) if ln.startswith("inductive LIntrinsicOp"))
    end = next(i for i in range(start + 1, len(lines)) if lines[i].strip().startswith("deriving"))
    return "namespace Anneal.Mir\n\n" + "\n".join(lines[start : end + 1]) + "\n\nend Anneal.Mir\n"


def build_fixture(dest: Path) -> None:
    for rel in COPIED_FILES:
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(REPO_ROOT / rel, target)
    (dest / audit.LINTRINSIC_FILE).parent.mkdir(parents=True, exist_ok=True)
    (dest / audit.LINTRINSIC_FILE).write_text(lintrinsic_stub(), encoding="utf-8")
    (dest / audit.SEP_LOGIC_LENSES).write_text(SEP_LOGIC_LENSES_STUB, encoding="utf-8")
    (dest / CORR).write_text(correspondence_source(), encoding="utf-8")


class AuditFixtureTestCase(unittest.TestCase):
    """Builds one pristine fixture per class; every test mutates its own copy."""

    _base_dir: tempfile.TemporaryDirectory[str]
    base: Path

    @classmethod
    def setUpClass(cls) -> None:
        cls._base_dir = tempfile.TemporaryDirectory(prefix="mir_cov_audit_base_")
        cls.base = Path(cls._base_dir.name) / "repo"
        build_fixture(cls.base)

    @classmethod
    def tearDownClass(cls) -> None:
        cls._base_dir.cleanup()

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory(prefix="mir_cov_audit_case_")
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name) / "repo"
        shutil.copytree(self.base, self.root)

    # -- helpers ----------------------------------------------------------

    def edit(self, rel: str, old: str, new: str, count: int = 1) -> None:
        path = self.root / rel
        text = path.read_text(encoding="utf-8")
        self.assertIn(old, text, f"mutation anchor missing from {rel}: {old!r}")
        path.write_text(text.replace(old, new, count), encoding="utf-8")

    def write_correspondence(self, text: str) -> None:
        (self.root / CORR).write_text(text, encoding="utf-8")

    def run_checks(self) -> dict:
        return audit.run_audit(self.root)

    def assert_only_failures(self, report: dict, expected: set[str]) -> None:
        self.assertEqual(set(report["failed_checks"]), expected, json.dumps(report["checks"], indent=1)[:6000])

    def assert_error(self, report: dict, check_id: str, fragment: str) -> None:
        errors = report["checks"][check_id]["errors"]
        self.assertTrue(any(fragment in e for e in errors), f"{fragment!r} not in {check_id} errors: {errors}")

    def repin_lean_miri(self, rel: str) -> None:
        """Re-pin the vendored `rel` (sha256 entry and manifest digest) after editing it."""
        pin_path = self.root / audit.LEAN_MIRI_PIN
        pin = json.loads(pin_path.read_text(encoding="utf-8"))
        key = rel[len(audit.LEAN_MIRI_VENDOR) :]
        digest = hashlib.sha256((self.root / rel).read_bytes()).hexdigest()
        files = pin["vendor_tree"]["files"]
        for entry in files:
            if entry["path"] == key:
                entry["sha256"] = digest
        manifest = "".join(f"{f['sha256']}  {f['path']}\n" for f in files)
        pin["vendor_tree"]["manifest_sha256"] = hashlib.sha256(manifest.encode("utf-8")).hexdigest()
        pin_path.write_text(json.dumps(pin, indent=2) + "\n", encoding="utf-8")


class BaselineAndCliTests(AuditFixtureTestCase):
    def test_pristine_fixture_passes_every_check(self) -> None:
        report = self.run_checks()
        self.assert_only_failures(report, set())
        self.assertEqual(list(report["checks"]), list(audit.CHECK_ORDER))
        surface = report["surface"]
        self.assertEqual(surface["trusted_mir_ast_constructors"], audit.EXPECTED_MIR_AST_TOTAL)
        self.assertEqual(surface["stage1_lintrinsic_op_variants"], surface["stage1_lintrinsic_op_variants_parsed"])
        self.assertGreaterEqual(surface["combined_surface_total"], audit.COMBINED_SURFACE_FLOOR)
        self.assertGreaterEqual(audit.COMBINED_SURFACE_FLOOR, audit.COMBINED_SURFACE_BRIEF_EXPECTATION)
        manifest = report["checks"]["c_variant_manifest"]["details"]["entries"]
        self.assertEqual(sorted(manifest), sorted(audit.REQUIRED_MANIFEST_VARIANTS))
        self.assertEqual(manifest["TerminatorKind.tailCall"]["negative"], ["tail_negative_arity", "tail_negative_root"])

    def test_cli_check_json_and_repo_root(self) -> None:
        ok = subprocess.run(
            [sys.executable, "-B", str(AUDIT_SCRIPT), "--check", "--json", "--repo-root", str(self.root)],
            capture_output=True,
            text=True,
            timeout=300,
            check=False,
        )
        self.assertEqual(ok.returncode, 0, ok.stdout[-4000:] + ok.stderr[-4000:])
        report = json.loads(ok.stdout)
        self.assertTrue(report["ok"])
        self.assertEqual(report["schema_version"], audit.SCHEMA_VERSION)
        self.assertEqual(Path(report["repo_root"]), self.root.resolve())

        self.edit(CORR, "theorem cec_positive", "theorem cec_positive_renamed")
        failing = subprocess.run(
            [sys.executable, "-B", str(AUDIT_SCRIPT), "--check", "--repo-root", str(self.root)],
            capture_output=True,
            text=True,
            timeout=300,
            check=False,
        )
        self.assertEqual(failing.returncode, 1)
        self.assertIn("[FAIL] c_variant_manifest", failing.stdout)
        # Without `--check` the report is produced and the exit code stays 0.
        report_only = subprocess.run(
            [sys.executable, "-B", str(AUDIT_SCRIPT), "--json", "--repo-root", str(self.root)],
            capture_output=True,
            text=True,
            timeout=300,
            check=False,
        )
        self.assertEqual(report_only.returncode, 0)
        self.assertEqual(json.loads(report_only.stdout)["failed_checks"], ["c_variant_manifest"])


class ConstructorCensusTests(AuditFixtureTestCase):
    def test_constructor_missing_from_lean_is_a_phantom_census_entry(self) -> None:
        self.edit(STATEMENTS, "  | nop : StatementKind\n", "")
        report = self.run_checks()
        self.assert_only_failures(report, {"a_mir_ast_constructors"})
        self.assert_error(report, "a_mir_ast_constructors", "no `StatementKind` constructor")
        self.assert_error(report, "a_mir_ast_constructors", "parsed 93 Trusted.MirAst constructors")

    def test_extra_lean_constructor_must_be_censused(self) -> None:
        self.edit(
            STATEMENTS,
            "  | nop : StatementKind\n",
            "  | nop : StatementKind\n  /-- A future rustc variant. -/\n  | fakeRead (place : Place) : StatementKind\n",
        )
        report = self.run_checks()
        self.assert_only_failures(report, {"a_mir_ast_constructors"})
        self.assert_error(report, "a_mir_ast_constructors", "constructors missing from MIR_AST_CATEGORIES: ['fakeRead']")

    def test_constructor_inside_comment_does_not_count(self) -> None:
        self.edit(STATEMENTS, "  | nop : StatementKind\n", "  -- | nop : StatementKind\n  /- | nop : StatementKind -/\n")
        report = self.run_checks()
        self.assert_error(report, "a_mir_ast_constructors", "no `StatementKind` constructor")

    def test_constructor_modifiers_and_attributes_are_skipped(self) -> None:
        self.edit(STATEMENTS, "  | nop : StatementKind\n", "  | protected nop : StatementKind\n")
        self.edit(STATEMENTS, "  | coverage : StatementKind\n", "  | @[match_pattern] private coverage : StatementKind\n")
        self.assert_only_failures(self.run_checks(), set())
        code, _errors = audit.strip_lean_source("inductive T where | a | b (x : Nat) : T | «c d»\n  deriving Repr\n")
        self.assertEqual(audit.parse_inductive_constructors(code, "T"), ["a", "b", "c d"])
        self.assertIsNone(audit.parse_inductive_constructors(code, "U"))

    def test_duplicate_and_unknown_status_census_entries(self) -> None:
        self.edit(
            SUITE,
            '            ("nop", "proved_corresponding"),\n',
            '            ("nop", "proved_corresponding"),\n            ("nop", "proved_correspondng"),\n',
        )
        report = self.run_checks()
        self.assert_error(report, "a_mir_ast_constructors", "duplicate census entries ['nop']")
        self.assert_error(report, "a_mir_ast_constructors", "unknown status 'proved_correspondng'")
        self.assert_error(report, "a_mir_ast_constructors", "lists 95 variants, expected 94")

    def test_reintroduced_phantom_coroutine_closure_entry(self) -> None:
        self.edit(
            SUITE,
            '            ("coroutine", "unsupported_fail_closed"),\n',
            '            ("coroutine", "unsupported_fail_closed"),\n            ("coroutineClosure", "unsupported_fail_closed"),\n',
        )
        report = self.run_checks()
        self.assert_error(report, "a_mir_ast_constructors", "['coroutineClosure']")

    def test_fold_requires_the_capture_lowering_arm(self) -> None:
        self.edit(
            "trusted/rustc-capture/src/rustc_2026_06_01/mir_lower.rs",
            "| AggregateKind::CoroutineClosure(def_id, _args) => {",
            "| AggregateKind::CoroutineClosure(def_id, _args) => { // lowered elsewhere",
        )
        report = self.run_checks()
        self.assert_only_failures(report, {"a_mir_ast_constructors"})
        self.assert_error(report, "a_mir_ast_constructors", "lowering arm folding rustc `AggregateKind::CoroutineClosure`")

    def test_reintroduced_supported_untested_is_rejected(self) -> None:
        self.edit(SUITE, '("constEvalCounter", "proved_corresponding")', '("constEvalCounter", "supported_untested")')
        report = self.run_checks()
        self.assert_only_failures(report, {"b_untested_variants_zero"})
        self.assert_error(report, "b_untested_variants_zero", "supported_untested == 1")
        self.assert_error(report, "b_untested_variants_zero", "StatementKind.constEvalCounter")

    def test_combined_surface_floor_catches_a_collapsed_denominator(self) -> None:
        (self.root / "minirust/coverage.json").unlink()
        report = self.run_checks()
        self.assert_only_failures(report, {"a_surface_totals"})
        self.assert_error(report, "a_surface_totals", f"< floor {audit.COMBINED_SURFACE_FLOOR}")

    def test_lintrinsic_cross_parse_disagreement(self) -> None:
        # A constructor written on the `where` line is invisible to the Stage-A line regex but
        # not to the audit's parser, so the two counts disagree.
        self.edit(audit.LINTRINSIC_FILE, "inductive LIntrinsicOp : Type where\n", "inductive LIntrinsicOp : Type where | fma\n")
        report = self.run_checks()
        self.assert_error(report, "a_surface_totals", "disagrees with the parsed 31")


class ManifestTests(AuditFixtureTestCase):
    def test_manifest_theorem_not_declared(self) -> None:
        self.edit(CORR, "theorem opaque_leanmiri_guard :", "theorem opaque_leanmiri_guard2 :")
        report = self.run_checks()
        self.assert_only_failures(report, {"c_variant_manifest"})
        self.assert_error(report, "c_variant_manifest", "theorem `opaque_leanmiri_guard` is not declared in code")

    def test_manifest_theorem_only_declared_in_comments_or_strings(self) -> None:
        self.edit(
            CORR,
            "theorem cec_leanmiri_noop : cecProgram = cecProgram := rfl\n",
            "-- theorem cec_leanmiri_noop : cecProgram = cecProgram := rfl\n"
            "/- theorem cec_leanmiri_noop : cecProgram = cecProgram := rfl -/\n"
            'def fake : String := "theorem cec_leanmiri_noop"\n',
        )
        report = self.run_checks()
        self.assert_only_failures(report, {"c_variant_manifest"})
        self.assert_error(report, "c_variant_manifest", "theorem `cec_leanmiri_noop` is not declared in code")

    def test_manifest_name_must_be_a_theorem(self) -> None:
        self.edit(CORR, "theorem tail_positive : tailCallTerm > 6 := by decide", "def tail_positive : Bool := tailCallTerm > 6")
        report = self.run_checks()
        self.assert_error(report, "c_variant_manifest", "theorem `tail_positive` is not declared in code")

    def test_manifest_line_missing_duplicated_malformed_or_unknown(self) -> None:
        self.write_correspondence(
            correspondence_source(
                manifest=(
                    MANIFEST_LINES[0],
                    MANIFEST_LINES[0],
                    MANIFEST_LINES[1].replace(" negative=", " "),
                    "-- @mir-variant-coverage StatementKind.nop trusted=cec_trusted_step minirust=cec_minirust_skip "
                    "leanmiri=cec_leanmiri_noop positive=cec_positive negative=cec_negative",
                )
            )
        )
        report = self.run_checks()
        self.assert_only_failures(report, {"c_variant_manifest"})
        self.assert_error(report, "c_variant_manifest", "duplicate manifest line for StatementKind.constEvalCounter")
        self.assert_error(report, "c_variant_manifest", "malformed @mir-variant-coverage line")
        self.assert_error(report, "c_variant_manifest", "StatementKind.nop is a censused variant outside")
        self.assert_error(report, "c_variant_manifest", "no @mir-variant-coverage line for TerminatorKind.tailCall")
        self.assert_error(report, "c_variant_manifest", "no @mir-variant-coverage line for ProjectionElem.opaqueCast")

    def test_manifest_lists_must_be_non_empty_distinct_and_disjoint(self) -> None:
        self.write_correspondence(
            correspondence_source(
                manifest=(
                    MANIFEST_LINES[0].replace("positive=cec_positive", "positive=cec_positive,,cec_negative"),
                    MANIFEST_LINES[1].replace("trusted=tail_trusted_frame", "trusted=tail_trusted_frame,tail_trusted_frame"),
                    MANIFEST_LINES[2],
                )
            )
        )
        report = self.run_checks()
        self.assert_error(report, "c_variant_manifest", "empty or invalid theorem name")
        self.assert_error(report, "c_variant_manifest", "as both positive and negative witnesses")
        self.assert_error(report, "c_variant_manifest", "trusted= repeats ['tail_trusted_frame']")

    def test_manifest_theorem_must_reference_its_variant(self) -> None:
        self.edit(CORR, "theorem opaque_negative : opaqueCastProj ≠ 5 := by decide", "theorem opaque_negative : 1 ≠ 5 := by decide")
        report = self.run_checks()
        self.assert_only_failures(report, {"c_variant_manifest"})
        self.assert_error(report, "c_variant_manifest", "`opaque_negative` never references ProjectionElem.opaqueCast")

        # Even if the theorem's own name contains the variant token (`opaqueCast`), a body that
        # never references the variant or a helper that does must still be rejected.
        self.edit(CORR, "negative=opaque_negative", "negative=opaqueCast_vacuous")
        self.edit(CORR, "`opaque_negative]", "`opaqueCast_vacuous]")
        self.edit(CORR, "theorem opaque_negative : 1 ≠ 5 := by decide", "theorem opaqueCast_vacuous : 1 ≠ 5 := by decide")
        report = self.run_checks()
        self.assert_only_failures(report, {"c_variant_manifest"})
        self.assert_error(report, "c_variant_manifest", "`opaqueCast_vacuous` never references ProjectionElem.opaqueCast")

    def test_manifest_theorem_after_the_audit_is_rejected(self) -> None:
        text = correspondence_source().replace("theorem opaque_positive : opaqueCastProj > 2 := by decide\n", "")
        text = text.replace(
            "end Anneal.FixtureCoverage\n",
            "theorem opaque_positive : opaqueCastProj > 2 := by decide\n\nend Anneal.FixtureCoverage\n",
        )
        self.write_correspondence(text)
        report = self.run_checks()
        self.assert_error(report, "c_variant_manifest", "`opaque_positive` is declared after the run_cmd audit")
        self.assert_error(report, "c_variant_manifest", "no trailing run_cmd audit to re-check the manifest")
        self.assert_error(report, "c_correspondence_test_hygiene", "no trailing `run_cmd` audit block")

    def test_run_cmd_audit_and_comment_manifest_must_not_drift(self) -> None:
        # A manifest theorem the audit does not name (only mentioned in a comment / string) ...
        self.edit(CORR, "`opaque_minirust, ", "")
        self.edit(CORR, "  for short in manifest do\n", "  -- `opaque_minirust\n  for short in manifest do\n")
        # ... and a theorem of the file that the audit names but the manifest does not list.
        self.edit(CORR, "    `opaque_negative]", "    `opaque_negative, `cec_extra]")
        self.edit(CORR, "def tailCallTerm", "theorem cec_extra : cecProgram = 1 := rfl\n\ndef tailCallTerm")
        report = self.run_checks()
        self.assert_only_failures(report, {"c_variant_manifest"})
        self.assert_error(report, "c_variant_manifest", "`opaque_minirust` is not named in code by the trailing run_cmd audit")
        self.assert_error(report, "c_variant_manifest", "names theorem `cec_extra`, which no @mir-variant-coverage line lists")


class HygieneTests(AuditFixtureTestCase):
    def test_sorry_in_code_is_rejected_but_not_in_comments_or_strings(self) -> None:
        self.edit(CORR, "theorem cec_positive : cecProgram ≠ 0 := by decide", "theorem cec_positive : cecProgram ≠ 0 := by sorry")
        report = self.run_checks()
        self.assert_only_failures(report, {"c_correspondence_test_hygiene"})
        self.assert_error(report, "c_correspondence_test_hygiene", "forbidden `sorry` in code")

    def test_forbidden_tokens_hidden_in_interpolations_and_after_char_literals(self) -> None:
        self.edit(
            CORR,
            "def braceChar : Char := '\"'\n",
            "def braceChar : Char := '\"'\ndef hidden : String := s!\"{(sorry : Nat)}\"\n"
            "def quoted : String := s!\"{if '}' == '\\\"' then \\\"a\\\" else \\\"b\\\"}\"\n"
            "theorem t : 1 = 1 := by native_decide\n",
        )
        report = self.run_checks()
        self.assert_error(report, "c_correspondence_test_hygiene", "forbidden `sorry` in code")
        self.assert_error(report, "c_correspondence_test_hygiene", "forbidden `native_decide` in code")

    def test_axiom_unsafe_and_kernel_bypasses_are_rejected(self) -> None:
        self.edit(
            CORR,
            "def banner : String",
            "axiom cheat : False\nunsafe def u : Nat := 0\nset_option debug.skipKernelTC true in\n"
            "theorem d : True := by decide +native\n@[implemented_by u] def v : Nat := 1\ndef banner : String",
        )
        report = self.run_checks()
        for label in ("axiom declaration", "unsafe", "debug.skipKernelTC", "decide +native", "implemented_by"):
            self.assert_error(report, "c_correspondence_test_hygiene", f"forbidden `{label}` in code")

    def test_sorry_ax_outside_the_audit_is_rejected(self) -> None:
        self.edit(CORR, "def banner : String", "def cheat : False := sorryAx False\ndef banner : String")
        report = self.run_checks()
        self.assert_only_failures(report, {"c_correspondence_test_hygiene"})
        self.assert_error(report, "c_correspondence_test_hygiene", "`sorryAx` outside the trailing run_cmd audit")

    def test_audit_only_names_smuggled_through_strings_are_rejected(self) -> None:
        self.edit(
            CORR,
            "def banner : String",
            'def smuggled : Lean.Name := Lean.Name.mkSimple "ofReduceBool"\ndef banner : String',
        )
        report = self.run_checks()
        self.assert_only_failures(report, {"c_correspondence_test_hygiene"})
        self.assert_error(report, "c_correspondence_test_hygiene", "`ofReduceBool` outside the trailing run_cmd audit")

    def test_missing_or_hollow_run_cmd_audit_is_rejected(self) -> None:
        text = correspondence_source()
        head = text[: text.index("open Lean Elab Command in")]
        self.write_correspondence(head + "end Anneal.FixtureCoverage\n")
        report = self.run_checks()
        # The manifest cross-check needs the audit too.
        self.assert_only_failures(report, {"c_correspondence_test_hygiene", "c_variant_manifest"})
        self.assert_error(report, "c_correspondence_test_hygiene", "no trailing `run_cmd` audit block")
        self.assert_error(report, "c_variant_manifest", "no trailing run_cmd audit to re-check the manifest")

        # An audit that only names the axioms in a string or comment does not count.
        self.write_correspondence(
            head
            + "open Lean Elab Command in\nrun_cmd do\n  -- collectAxioms sorryAx Lean.ofReduceBool\n"
            + '  logInfo "checked collectAxioms, sorryAx and Lean.ofReduceBool"\n\nend Anneal.FixtureCoverage\n'
        )
        report = self.run_checks()
        for word in audit.REQUIRED_AUDIT_MENTIONS:
            self.assert_error(report, "c_correspondence_test_hygiene", f"does not reference `{word}` in code")

    def test_declaration_after_the_audit_makes_it_non_trailing(self) -> None:
        self.edit(
            CORR,
            "end Anneal.FixtureCoverage\n",
            "theorem late : True := by sorry\n\nend Anneal.FixtureCoverage\n",
        )
        report = self.run_checks()
        self.assert_error(report, "c_correspondence_test_hygiene", "no trailing `run_cmd` audit block")
        self.assert_error(report, "c_correspondence_test_hygiene", "forbidden `sorry` in code")

    def test_unterminated_comment_fails_closed(self) -> None:
        self.edit(CORR, "def banner : String", "/- unterminated\ntheorem x : False := sorry\ndef banner : String")
        report = self.run_checks()
        self.assert_error(report, "c_correspondence_test_hygiene", "unterminated block comment")

    def test_slice_lens_suite_keeps_hygiene_and_non_vacuity(self) -> None:
        self.edit(audit.SLICE_LENS_TEST, audit.SLICE_LENS_NON_VACUITY_MESSAGE, "theorems unchecked")
        report = self.run_checks()
        self.assert_only_failures(report, {"c_slice_lens_test_hygiene"})
        self.assert_error(report, "c_slice_lens_test_hygiene", "lost its check")

        self.edit(audit.SLICE_LENS_TEST, "theorems unchecked", audit.SLICE_LENS_NON_VACUITY_MESSAGE)
        self.edit(audit.SLICE_LENS_TEST, "\nend Anneal.MirSliceWidePtrLensTests", "\ntheorem z : True := by admit\nend Anneal.MirSliceWidePtrLensTests")
        report = self.run_checks()
        self.assert_error(report, "c_slice_lens_test_hygiene", "forbidden `admit` in code")
        self.assert_error(report, "c_slice_lens_test_hygiene", "no trailing `run_cmd` audit block")

    def test_strip_lean_source_preserves_layout(self) -> None:
        src = (
            "def a := \"x -- y /- z\" -- tail\n/- outer /- inner -/ still -/ def b := '\"'\n"
            "def c := r#\"raw \" sorry\"# ++ s!\"{d} and {\"e\"}\"\n«weird--name» := 1\n"
        )
        code, errors = audit.strip_lean_source(src)
        self.assertEqual(errors, [])
        self.assertEqual(len(code), len(src))
        self.assertEqual(code.count("\n"), src.count("\n"))
        self.assertNotIn("tail", code)
        self.assertNotIn("inner", code)
        self.assertNotIn("sorry", code)
        self.assertIn("def b", code)
        self.assertRegex(code, r"s!\s+d\s")  # interpolation code stays visible, "e" does not
        self.assertEqual(code.split("s!", 1)[1].split("\n", 1)[0].split(), ["d"])
        self.assertIn("«weird--name»", code)
        kept, _ = audit.strip_lean_source(src, keep_strings=True)
        self.assertIn('"x -- y /- z"', kept)
        self.assertNotIn("tail", kept)


class LensAndBlockerTests(AuditFixtureTestCase):
    def test_lens_definitions_and_lemmas_are_required(self) -> None:
        self.edit(audit.SEP_LOGIC_LENSES, "def ActiveTypedSliceMutBorrow", "theorem ActiveTypedSliceMutBorrow")
        self.edit(audit.SEP_LOGIC_LENSES, "theorem of_splitAt", "-- theorem of_splitAt")
        report = self.run_checks()
        self.assert_only_failures(report, {"d_slice_lens_declarations"})
        self.assert_error(report, "d_slice_lens_declarations", "no `def`/`structure`/`abbrev` ActiveTypedSliceMutBorrow")
        self.assert_error(report, "d_slice_lens_declarations", "no declaration of `SliceTypedAt.of_splitAt`")

    def test_lemma_outside_its_namespace_does_not_count(self) -> None:
        self.edit(audit.SEP_LOGIC_LENSES, "theorem splitAt", "theorem splitAtX")
        self.edit(audit.SEP_LOGIC_LENSES, "end SliceTypedAt\n", "end SliceTypedAt\n\ntheorem splitAt : True := trivial\n")
        report = self.run_checks()
        self.assert_error(report, "d_slice_lens_declarations", "no declaration of `SliceTypedAt.splitAt`")

    def test_dogfood_proofs_checked_when_examples_present(self) -> None:
        for rel in audit.REQUIRED_DOGFOOD_PROOFS:
            target = self.root / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(REPO_ROOT / rel, target)
        report = self.run_checks()
        self.assert_only_failures(report, set())
        dogfood = report["checks"]["d_slice_lens_declarations"]["details"]["dogfood_companions"]
        self.assertEqual(sorted(dogfood), sorted(audit.REQUIRED_DOGFOOD_PROOFS))
        for rel, thms in dogfood.items():
            self.assertTrue(thms, f"{rel} has no companion theorems")
        # Hollowing out a dogfood file (removing its slice-lens companion theorems) is caught.
        fidl_rel = "examples/fuchsia-usercopy/anneal/proofs/Proof/FuchsiaUsercopy/fidl_chunk_padding_len.lean"
        (self.root / fidl_rel).write_text("theorem verified : True := trivial\n", encoding="utf-8")
        report = self.run_checks()
        self.assert_only_failures(report, {"d_slice_lens_declarations"})
        self.assert_error(report, "d_slice_lens_declarations", f"{fidl_rel}: no companion theorem")

    def _install_dogfood(self) -> None:
        for rel in audit.REQUIRED_DOGFOOD_PROOFS:
            target = self.root / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(REPO_ROOT / rel, target)

    def test_dogfood_companion_must_be_connected_to_the_function(self) -> None:
        self._install_dogfood()
        rel = "examples/fxfs-storage-boundary/anneal/proofs/Proof/FxfsStorageBoundary/vmo_subslice_bounds_valid.lean"
        # A generic lens fact that never mentions the item's MIR body, its spec, or `verified`.
        (self.root / rel).write_text(
            "theorem verified : StatefulVerificationResult "
            "Obligations.FxfsStorageBoundary.vmo_subslice_bounds_valid.statefulClaim := by\n  exact x\n\n"
            "theorem lens_only {w : WidePtrVal} : SliceTypedAt c w [] b := by\n  exact h\n",
            encoding="utf-8",
        )
        report = self.run_checks()
        self.assert_only_failures(report, {"d_slice_lens_declarations"})
        self.assert_error(report, "d_slice_lens_declarations", f"{rel}: no slice-lens companion theorem is connected")

    def test_dogfood_verified_signature_is_pinned(self) -> None:
        self._install_dogfood()
        rel = "examples/fuchsia-usercopy/anneal/proofs/Proof/FuchsiaUsercopy/assume_initialized_until_split_len.lean"
        self.edit(
            rel,
            "theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.assume_initialized_until_split_len.statefulClaim",
            "theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.assume_initialized_until_split_len.statefulClaim ∧ Anneal.SepLogicLenses.WidePtrVal = WidePtrVal",
        )
        report = self.run_checks()
        self.assert_only_failures(report, {"d_slice_lens_declarations"})
        self.assert_error(report, "d_slice_lens_declarations", f"{rel}: `theorem verified` must state")
        # A different obligation's claim is rejected too.
        self.assertFalse(
            audit._verified_signature_ok(
                "theorem verified : VerificationResult Obligations.FuchsiaUsercopy.other_item.claim",
                "FuchsiaUsercopy",
                "assume_initialized_until_split_len",
            )
        )

    def _assert_blocker_mutant_rejected(self, old: str, new: str, fragment: str) -> None:
        self.edit(SUITE, old, new)
        report = self.run_checks()
        self.assert_only_failures(report, {"d_stage_b_blocker_separation"})
        self.assert_error(report, "d_stage_b_blocker_separation", fragment)

    def test_over_broad_exemption_qsized_moved_into_lifted_blocker(self) -> None:
        self.edit(
            SUITE,
            'r"\\b(?:slice::from_raw_parts(?:_mut)?|slice_from_raw_parts(?:_mut)?)\\b"',
            'r"\\b(?:slice::from_raw_parts(?:_mut)?|slice_from_raw_parts(?:_mut)?)\\b|\\?\\s*Sized\\b"',
        )
        self._assert_blocker_mutant_rejected(
            'r"\\?\\s*Sized\\b"\n            r"|\\b(?:size|align)_of_val',
            'r"\\b(?:size|align)_of_val',
            "probe lifted_slice_in_qsized_generic_fn: expected 'unsized_dst_or_ptr_metadata' to block",
        )

    def test_over_broad_exemption_generic_from_raw_parts_swallowed(self) -> None:
        self.edit(
            SUITE,
            'r"\\b(?:slice::from_raw_parts(?:_mut)?|slice_from_raw_parts(?:_mut)?)\\b"',
            'r"\\b(?:\\w+::)?(?:slice_)?from_raw_parts(?:_mut)?\\b"',
        )
        self._assert_blocker_mutant_rejected(
            '\n            r"|(?:\\b(?:ptr|NonNull)|>)::from_raw_parts(?:_mut)?\\b"',
            "",
            "probe generic_ptr_from_raw_parts: expected 'unsized_dst_or_ptr_metadata' to block",
        )

    def test_unsized_blocker_must_keep_blocking_lifters(self) -> None:
        self._assert_blocker_mutant_rejected(
            '|\\.)to_raw_parts\\b"\n        ),\n        {"anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},',
            '|\\.)to_raw_parts\\b"\n        ),\n        {"minirust_correspondence", "lean_miri_correspondence"},',
            "no longer affects anneal_proof_lifters",
        )

    def test_to_raw_parts_mutant_is_rejected(self) -> None:
        self._assert_blocker_mutant_rejected(
            '\n            r"|(?:(?:\\b(?:ptr|NonNull)|>)::_|\\.)to_raw_parts\\b"'.replace("::_", "::"),
            "",
            "probe unsized_ptr_to_raw_parts: expected 'unsized_dst_or_ptr_metadata' to block",
        )

    def test_dropping_the_signature_guard_is_rejected(self) -> None:
        self._assert_blocker_mutant_rejected(
            "SIGNATURE_GUARDED_BLOCKERS: dict[str, str] = {LIFTED_SLICE_WIDE_PTR_BLOCKER: UNSIZED_DST_BLOCKER}",
            "SIGNATURE_GUARDED_BLOCKERS: dict[str, str] = {}",
            "probe lifted_slice_in_qsized_impl: expected 'unsized_dst_or_ptr_metadata' to block",
        )

    def test_lifted_blocker_must_not_block_lifters(self) -> None:
        self._assert_blocker_mutant_rejected(
            'slice_from_raw_parts(?:_mut)?)\\b"),\n        {"minirust_correspondence", "lean_miri_correspondence"},',
            'slice_from_raw_parts(?:_mut)?)\\b"),\n        {"anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},',
            "still affects anneal_proof_lifters",
        )


class SourceAnchorTests(AuditFixtureTestCase):
    def test_anchor_snippet_absent_from_vendored_file(self) -> None:
        snippet = "| .ConstEvalCounter => hooks.incrementConstEvalCounter choice state"
        self.edit(STEP_LEAN, snippet, "| .ConstEvalCounter => hooks.incrementConstEvalCounter choice state'")
        self.repin_lean_miri(STEP_LEAN)  # isolate the snippet failure from the hash failure
        report = self.run_checks()
        self.assert_only_failures(report, {"e_vendored_source_anchors", "e_source_anchor_quotes"})
        self.assert_error(report, "e_vendored_source_anchors", "anchor snippet not found as a line")
        self.assertFalse(any("sha256" in e for e in report["checks"]["e_vendored_source_anchors"]["errors"]))

    def test_anchor_not_quoted_in_the_lean_file(self) -> None:
        dropped = audit.REQUIRED_SOURCE_ANCHORS[7]
        self.write_correspondence(
            correspondence_source(anchors=tuple(a for a in audit.REQUIRED_SOURCE_ANCHORS if a != dropped))
        )
        report = self.run_checks()
        self.assert_only_failures(report, {"e_source_anchor_quotes"})
        self.assert_error(report, "e_source_anchor_quotes", f"required anchor not quoted: -- @source-anchor {dropped[0]}#")

    def test_extra_valid_anchors_are_accepted_and_validated(self) -> None:
        extra = (
            (STEP_LEAN, "| .FakeRead .. | .AscribeUserType .. | .Coverage .. | .Nop"),
            ("lean-miri/vendor/Miri/Interpreter/Call.lean", "| .goto ret unwind => pure (ret, unwind)"),
        )
        self.write_correspondence(correspondence_source(anchors=audit.REQUIRED_SOURCE_ANCHORS + extra))
        report = self.run_checks()
        self.assert_only_failures(report, set())
        details = report["checks"]["e_source_anchor_quotes"]["details"]
        self.assertEqual(details["distinct_quoted_anchors"], len(audit.REQUIRED_SOURCE_ANCHORS) + len(extra))
        # The extra anchors are held to the same standard: drift in their file is caught.
        self.edit("lean-miri/vendor/Miri/Interpreter/Call.lean", "| .goto ret unwind => pure (ret, unwind)", "| .goto ret unwind => pure (unwind, ret)")
        self.repin_lean_miri("lean-miri/vendor/Miri/Interpreter/Call.lean")
        report = self.run_checks()
        self.assert_only_failures(report, {"e_source_anchor_quotes"})
        self.assert_error(report, "e_source_anchor_quotes", "| .goto ret unwind => pure (ret, unwind)")

    def test_quoted_anchor_must_be_valid(self) -> None:
        extra = (
            ("lean-miri/vendor/Miri/Interpreter/Step.lean", "this line is not in Step.lean"),
            ("theory/Anneal/SepLogicLenses.lean", "namespace Anneal.SepLogicLenses"),
            ("minirust/vendor/0000000000000000000000000000000000000000/tooling/minimize/src/bb.rs", "x"),
        )
        self.write_correspondence(correspondence_source(anchors=audit.REQUIRED_SOURCE_ANCHORS + extra))
        self.edit(CORR, "-- @source-anchor lean-miri/vendor/Miri/Interpreter/Step.lean#if old", "-- @source-anchor  #if old")
        report = self.run_checks()
        self.assert_only_failures(report, {"e_source_anchor_quotes"})
        self.assert_error(report, "e_source_anchor_quotes", "anchor snippet not found as a line: 'this line is not in Step.lean'")
        self.assert_error(report, "e_source_anchor_quotes", "anchors must point into")
        self.assert_error(report, "e_source_anchor_quotes", "not under the pinned MiniRust snapshot")
        self.assert_error(report, "e_source_anchor_quotes", "malformed @source-anchor line")

    def test_vendored_file_hash_must_match_its_pin(self) -> None:
        with (self.root / STEP_LEAN).open("a", encoding="utf-8") as fh:
            fh.write("\n-- local drift\n")
        rvalue = next(rel for rel, _ in audit.REQUIRED_SOURCE_ANCHORS if rel.endswith("rvalue.rs"))
        with (self.root / rvalue).open("a", encoding="utf-8") as fh:
            fh.write("\n// local drift\n")
        report = self.run_checks()
        self.assert_only_failures(report, {"e_vendored_source_anchors", "e_source_anchor_quotes"})
        self.assert_error(report, "e_vendored_source_anchors", f"{STEP_LEAN}: sha256")
        self.assert_error(report, "e_vendored_source_anchors", f"{rvalue}: sha256")

    def test_tampered_pin_entry_breaks_the_manifest_digest(self) -> None:
        pin_path = self.root / audit.LEAN_MIRI_PIN
        pin = json.loads(pin_path.read_text(encoding="utf-8"))
        with (self.root / STEP_LEAN).open("a", encoding="utf-8") as fh:
            fh.write("\n-- drift hidden by a re-pinned entry\n")
        digest = hashlib.sha256((self.root / STEP_LEAN).read_bytes()).hexdigest()
        for entry in pin["vendor_tree"]["files"]:
            if entry["path"] == STEP_LEAN[len(audit.LEAN_MIRI_VENDOR) :]:
                entry["sha256"] = digest
        pin_path.write_text(json.dumps(pin, indent=2) + "\n", encoding="utf-8")
        report = self.run_checks()
        self.assert_error(report, "e_vendored_source_anchors", "manifest_sha256 does not match")


class RealRepositoryTests(unittest.TestCase):
    def test_checks_independent_of_the_correspondence_test_pass(self) -> None:
        report = audit.run_audit(REPO_ROOT)
        independent = (
            "a_mir_ast_constructors",
            "a_surface_totals",
            "b_untested_variants_zero",
            "c_slice_lens_test_hygiene",
            "d_slice_lens_declarations",
            "d_stage_b_blocker_separation",
            "e_vendored_source_anchors",
        )
        for check_id in independent:
            self.assertTrue(report["checks"][check_id]["ok"], f"{check_id}: {report['checks'][check_id]['errors']}")
        self.assertEqual(report["surface"]["combined_surface_total"], audit.COMBINED_SURFACE_FLOOR)

    @unittest.skipUnless((REPO_ROOT / CORR).is_file(), f"{CORR} not written yet")
    def test_real_repository_passes_check(self) -> None:
        proc = subprocess.run(
            [sys.executable, "-B", str(AUDIT_SCRIPT), "--check"],
            capture_output=True,
            text=True,
            timeout=300,
            check=False,
        )
        self.assertEqual(proc.returncode, 0, proc.stdout[-6000:] + proc.stderr[-2000:])


if __name__ == "__main__":
    unittest.main()
