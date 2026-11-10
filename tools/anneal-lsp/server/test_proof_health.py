#!/usr/bin/env python3
"""Unit and integration test suite for `proof_health.py` and `post_tool_use.py`."""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
import unittest

SERVER_DIR = Path(__file__).resolve().parent
HOOK_PATH = SERVER_DIR.parent / "hooks" / "post_tool_use.py"
REPO_ROOT = SERVER_DIR.parent.parent.parent

if str(SERVER_DIR) not in sys.path:
    sys.path.insert(0, str(SERVER_DIR))

import proof_health  # noqa: E402

R1 = proof_health.RULE_DSIMP_FORBIDDEN_SYM
R2 = proof_health.RULE_DSIMP_MIR_BODY_UNFOLD
R3 = proof_health.RULE_RAW_BITWISE_UNFOLD
R4 = proof_health.RULE_LOW_PROFILER_THRESHOLD
R5 = proof_health.RULE_DUPLICATE_PRIVATE_LEMMA


def scan(src: str) -> list[tuple[str, int, str]]:
    return [
        (f.rule, f.line, f.symbol)
        for f in proof_health.scan_lean_text(src, scan_siblings=False)
    ]


def best_of_ms(fn, runs: int = 15, budget_ms: float = 5.0, rounds: int = 3) -> float:
    """Best wall-clock time of `fn` over up to `rounds` rounds of `runs` calls (after
    one warm-up call), stopping early once the best is under `budget_ms`. Rounds are
    spaced 0.25 s apart so a transient load spike on a shared machine does not decide
    the result; under sustained overload the budget check still fails."""
    fn()
    best = float("inf")
    for round_idx in range(rounds):
        if round_idx:
            time.sleep(0.25)
        for _ in range(runs):
            t0 = time.perf_counter()
            fn()
            best = min(best, (time.perf_counter() - t0) * 1000.0)
        if best < budget_ms:
            break
    return best


def jetski_edit(path: Path, target: str, replacement: str) -> dict:
    return {"toolCall": {"args": {"Path": str(path), "Target": target, "Replacement": replacement}}}


def settle(*paths: Path) -> None:
    """Backdate files by a minute, as if written long before the check (a file
    modified within `RACY_MTIME_WINDOW_NS` is deliberately not persisted)."""
    old = time.time() - 60
    for p in paths:
        os.utime(p, (old, old))


def clear_in_process_caches() -> None:
    proof_health._SIBLING_PRIVATE_CACHE.clear()
    proof_health._DIR_LEAN_FILES_CACHE.clear()
    proof_health._FILE_TEXTS_CACHE.clear()
    proof_health._NORM_SIG_CACHE.clear()


class TestStripLeanCommentsAndStrings(unittest.TestCase):
    def test_line_and_nested_block_comments_preserve_lines(self) -> None:
        src = (
            "theorem t1 : True := by\n"
            "  -- dsimp [wpMirExecSym]\n"
            "  /- outer comment\n"
            "     /- nested comment with dsimp [wpMirExecSym] and \"unclosed quote -/\n"
            "     still in outer comment set_option trace.profiler.threshold 1\n"
            "  -/\n"
            "  trivial\n"
        )
        stripped = proof_health.strip_lean_comments_and_strings(src)
        self.assertEqual(src.count("\n"), stripped.count("\n"))
        self.assertEqual(len(src), len(stripped))
        self.assertNotIn("wpMirExecSym", stripped)
        self.assertNotIn("profiler.threshold", stripped)
        self.assertIn("theorem t1", stripped)
        self.assertIn("trivial", stripped)

    def test_strings_and_identifier_primes(self) -> None:
        src = (
            'def msg : String := "dsimp [wpMirExecSym] \\"escaped\\" /- not comment"\n'
            "theorem t2 (st' fuel' : Nat) : st' = st' := by\n"
            "  have c : Char := 'a'\n"
            "  rfl\n"
        )
        stripped = proof_health.strip_lean_comments_and_strings(src)
        self.assertEqual(src.count("\n"), stripped.count("\n"))
        self.assertNotIn("wpMirExecSym", stripped)
        self.assertIn("st'", stripped)
        self.assertIn("fuel'", stripped)
        self.assertEqual(proof_health.scan_lean_text(src, scan_siblings=False), [])

    def test_blanking_preserves_every_offset(self) -> None:
        src = (
            'def x := "a\\"b" -- trailing comment\n'
            "/-- doc\n  /- nested -/ still doc -/\n"
            "theorem y : True := trivial\n"
        )
        stripped = proof_health.strip_lean_comments_and_strings(src)
        self.assertEqual(len(stripped), len(src))
        for raw_ch, out_ch in zip(src, stripped):
            if raw_ch != out_ch:
                self.assertEqual(out_ch, " ")
                self.assertNotEqual(raw_ch, "\n")
        self.assertEqual(stripped.index("theorem y"), src.index("theorem y"))
        self.assertNotIn("doc", stripped)
        self.assertNotIn("trailing", stripped)

    def test_raw_strings_and_quote_char_literals(self) -> None:
        # In `r"C:\"` the backslash is literal and the next `"` closes the string, so
        # the `simp` on line 3 is code. Inside `r#"..."#` an embedded `"` does not close
        # the string, so the `simp` text after it on line 4 is not code. `'"'` is a
        # character literal and must not open a string swallowing line 7.
        src = (
            'def a := r"C:\\"\n'
            "theorem t1 : True := by\n"
            "  simp [wpMirExecSym]\n"
            'def b := r#"quote " then simp [wpMirExecSym] "#\n'
            'def s := "x"\n'
            "def c : Char := '\"'\n"
            "theorem t2 : True := by simp only [Trusted.Sequence.length]\n"
        )
        self.assertEqual(
            scan(src),
            [(R1, 3, "wpMirExecSym"), (R1, 7, "Trusted.Sequence.length")],
        )

    def test_keep_strings_blanks_only_comments(self) -> None:
        src = 'def x := "keep me" -- drop me\n/- drop too -/ def y := r"also kept"\n'
        kept = proof_health.strip_lean_comments_and_strings(src, keep_strings=True)
        self.assertEqual(len(kept), len(src))
        self.assertIn('"keep me"', kept)
        self.assertIn('r"also kept"', kept)
        self.assertNotIn("drop", kept)

    def test_guillemets_field_r_and_prime_before_string(self) -> None:
        # `--` inside `«foo--bar»` is part of the identifier, not a line comment.
        # `.r"..."` is a field projection applied to a normal string (not raw `r"..."`).
        # `x'"'"` is `x'` followed by string `"'"` (not a char literal `'"'`).
        src = (
            "private theorem «dup--id» : True := trivial\n"
            "private theorem «dup--id» : True := trivial\n"
            'def p := obj.r"\\" still inside normal string dsimp [wpMirExecSym]"\n'
            'def q := f x\'"\'" -- closed string, then comment\n'
            "theorem after_q : True := by dsimp [wpMirExecSym]\n"
        )
        stripped = proof_health.strip_lean_comments_and_strings(src)
        self.assertEqual(len(stripped), len(src))
        self.assertEqual(
            scan(src),
            [(R5, 2, "«dup--id»"), (R1, 5, "wpMirExecSym")],
        )


class TestFiveStructuralAntiPatterns(unittest.TestCase):
    def test_rule1_dsimp_forbidden_sym(self) -> None:
        src = (
            "theorem bad1 : True := by\n"
            "  dsimp [foo, wpMirExecSym]\n"
            "  dsimp only [\n"
            "    bar,\n"
            "    Trusted.Sequence.length\n"
            "  ]\n"
            "  simp [Sequence.length]\n"
            "  simp? only [wpMirExecSym]\n"
        )
        self.assertEqual(
            scan(src),
            [
                (R1, 2, "wpMirExecSym"),
                (R1, 5, "Trusted.Sequence.length"),
                (R1, 7, "Sequence.length"),
                (R1, 8, "wpMirExecSym"),
            ],
        )

    def test_rule1_negatives(self) -> None:
        src = (
            "theorem ok1 (bs : List Nat) (h : Trusted.Sequence.length bs = 4) : True := by\n"
            "  have h2 := wpMirExecSym\n"
            "  rw [wpMirExecSym_helper]\n"
            "  rw [Trusted.Sequence.length]\n"
            "  simp [-Trusted.Sequence.length, foo]\n"
            "  simp only [Trusted.Sequence.length_append, Sequence.length_nil]\n"
            "  simp [wpMirExecSym?, wpMirExecSymFast, myNs.wpMirExecSym.helper]\n"
            "  -- simp [wpMirExecSym]\n"
            "  trivial\n"
        )
        self.assertEqual(scan(src), [])

    def test_rule1_has_no_location_or_identifier_exemptions(self) -> None:
        # The shapes of the Episode 1 list-length normalizations: the rule is syntactic,
        # so neither the other list entries nor an `at` clause exempt an occurrence.
        src = (
            "theorem e1 : True := by\n"
            "  simp [tBytes, Trusted.Sequence.length, hLen]\n"
            "  simp [Trusted.Sequence.length] at hL1 hL2 ⊢\n"
            "  simp [Trusted.Sequence.length, List.length_take] at hLen ⊢\n"
        )
        self.assertEqual(
            scan(src),
            [
                (R1, 2, "Trusted.Sequence.length"),
                (R1, 3, "Trusted.Sequence.length"),
                (R1, 4, "Trusted.Sequence.length"),
            ],
        )

    def test_rule1_qualified_names_equation_lemmas_and_simp_variants(self) -> None:
        src = (
            "theorem v : True := by\n"
            "  simp only [Anneal.Rustc.V2026_06_01.wpMirExecSym]\n"
            "  simp [wpMirExecSym.eq_def]\n"
            "  simp (config := { zeta := false }) only [wpMirExecSym]\n"
            "  simp +arith [Sequence.length]\n"
            "  simpa [wpMirExecSym] using h\n"
            "  simp_all [Trusted.Sequence.length]\n"
            "  dsimp! only [wpMirExecSym]\n"
            "  simp? (disch := omega) [wpMirExecSym]\n"
        )
        findings = proof_health.scan_lean_text(src, scan_siblings=False)
        self.assertEqual(
            [(f.rule, f.line, f.symbol) for f in findings],
            [
                (R1, 2, "Anneal.Rustc.V2026_06_01.wpMirExecSym"),
                (R1, 3, "wpMirExecSym"),
                (R1, 4, "wpMirExecSym"),
                (R1, 5, "Sequence.length"),
                (R1, 6, "wpMirExecSym"),
                (R1, 7, "Trusted.Sequence.length"),
                (R1, 8, "wpMirExecSym"),
                (R1, 9, "wpMirExecSym"),
            ],
        )
        self.assertIn("`simp_all [...]`", findings[5].message)
        self.assertIn("`dsimp! [...]`", findings[6].message)

    def test_rule1_explicit_and_parenthesized_entries(self) -> None:
        # `@name`, `(name)` and `(name : T)` entries still put the definition's
        # equations in the simp set; an argument position or a `←` rewrite does not.
        src = (
            "theorem w : True := by\n"
            "  simp [@wpMirExecSym]\n"
            "  simp only [foo, (Trusted.Sequence.length)]\n"
            "  simp [(wpMirExecSym : Nat → Nat)]\n"
            "  simp [f (wpMirExecSym)]\n"
            "  simp [← @wpMirExecSym]\n"
            "  simp [g x, @Trusted.Sequence.length]\n"
        )
        self.assertEqual(
            scan(src),
            [
                (R1, 2, "wpMirExecSym"),
                (R1, 3, "Trusted.Sequence.length"),
                (R1, 4, "wpMirExecSym"),
                (R1, 7, "Trusted.Sequence.length"),
            ],
        )

    def test_rule2_dsimp_mir_body_unfold(self) -> None:
        src = (
            "def itemBB0 := Mir.Crate.Item.body[0]!\n"
            "theorem bad2 : True := by\n"
            "  dsimp only [Mir.Crate.Item.body]\n"
            "  simp [foo, Mir.Mod.Sub.fn.body]\n"
            "  unfold Mir.Crate.Item.body\n"
            "  simp [Anneal.Mir.Crate.Item.body.eq_def]\n"
            "  simp [-Mir.Crate.Item.body]\n"
            "theorem lookup : lookupBlock Mir.Crate.Item.body 0 = some itemBB0 := rfl\n"
        )
        self.assertEqual(
            scan(src),
            [
                (R2, 3, "Mir.Crate.Item.body"),
                (R2, 4, "Mir.Mod.Sub.fn.body"),
                (R2, 5, "Mir.Crate.Item.body"),
                (R2, 6, "Anneal.Mir.Crate.Item.body"),
            ],
        )

    def test_rule3_raw_bitwise_unfold_and_exclusions(self) -> None:
        src = (
            "theorem bitwise_test : True := by\n"
            "  dsimp [bitwiseAndBitsFast, bitwiseOrBitsFast]\n"
            "  simp [bitwiseAndBits_32_mul256_add, bitwiseOrBits_eq]\n"
            "  rw [bitwiseAndBits_zero]\n"
            "  dsimp only [bitwiseAndBits]\n"
            "  simp [Trusted.MirSemantics.bitwiseOrBits]\n"
            "  unfold bitwiseAndBits\n"
            "  simp [bitwiseAndBits.eq_def]\n"
            "  simp [bitwiseAndBits.mod_two_eq, -bitwiseOrBits]\n"
            "  unfold bitwiseOrBitsFast\n"
        )
        self.assertEqual(
            scan(src),
            [
                (R3, 5, "bitwiseAndBits"),
                (R3, 6, "bitwiseOrBits"),
                (R3, 7, "bitwiseAndBits"),
                (R3, 8, "bitwiseAndBits"),
            ],
        )

    def test_rule4_low_profiler_threshold(self) -> None:
        src = (
            "set_option trace.profiler.threshold 100\n"
            "set_option trace.profiler.threshold 50\n"
            "set_option trace.profiler.threshold 49\n"
            "set_option trace.profiler.threshold 1\n"
            "set_option trace.profiler.threshold 0\n"
            "-- set_option trace.profiler.threshold 0\n"
        )
        self.assertEqual(
            scan(src),
            [
                (R4, 3, "trace.profiler.threshold=49"),
                (R4, 4, "trace.profiler.threshold=1"),
                (R4, 5, "trace.profiler.threshold=0"),
            ],
        )

    def test_rule5_duplicate_private_lemma_intra_and_sibling(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            sibling = tmp_dir / "Sibling.lean"
            sibling.write_text(
                "private theorem shared_helper (x : Nat) : x + 0 = x := Nat.add_zero x\n"
                "private lemma sig_match (a : Nat) (b : Bool) : a = a := rfl\n"
                "@[simp] private theorem attr_helper (n : Nat) : n * 1 = n := Nat.mul_one n\n",
                encoding="utf-8",
            )
            target = tmp_dir / "Target.lean"
            target.write_text(
                "private theorem local_dup (n : Nat) : n = n := rfl\n"
                "private lemma local_dup (n : Nat) : n = n := rfl\n"
                "private theorem alpha_one (u : Nat) : u + 1 = 1 + u := by omega\n"
                "private theorem alpha_two (v : Nat) : v + 1 = 1 + v := by omega\n"
                "private theorem shared_helper (z : Nat) : z = z := rfl\n"
                "private theorem sibling_sig_copy (x : Nat) (y : Bool) : x = x := rfl\n"
                "private noncomputable def attr_helper : Nat := 1\n",
                encoding="utf-8",
            )
            findings = proof_health.scan_lean_file(target, scan_siblings=True)
            self.assertEqual(
                [(f.line, f.symbol) for f in findings if f.rule == R5],
                [
                    (2, "local_dup"),
                    (4, "alpha_two"),
                    (5, "shared_helper"),
                    (6, "sibling_sig_copy"),
                    (7, "attr_helper"),
                ],
            )

    def test_rule5_dotted_and_question_mark_names_are_distinct(self) -> None:
        src = (
            "private theorem MirStepStar.mono (n : Nat) : n ≤ n + 1 := by omega\n"
            "private theorem MirStepStar.trans (a b : Nat) : a + b = b + a := by omega\n"
            "private def IsFamily (n : Nat) : Prop := n = 0\n"
            "private theorem IsFamily.of_eq (n : Nat) (h : n = 0) : IsFamily n := h\n"
            "private theorem get?_set?_ne (a : Nat) : a = a := rfl\n"
            "private theorem get?_length_eq_none (b : Nat) : b + 0 = b := rfl\n"
            "private theorem MirStepStar.mono (k : Nat) : k ≤ k + 2 := by omega\n"
        )
        self.assertEqual(scan(src), [(R5, 7, "MirStepStar.mono")])

    def test_rule5_definitions_need_equal_bodies(self) -> None:
        src = (
            'private def tyEnum : Ty := { kind := .adt "stmt_div::E" [], layoutIdx := 0 }\n'
            'private def tyUnion : Ty := { kind := .adt "stmt_div::U" [], layoutIdx := 0 }\n'
            "private def maxU8 : Nat := 255\n"
            "private def maxU16 : Nat := 65535\n"
            "private def tyEnumCopy : Ty :=\n"
            '  { kind := .adt "stmt_div::E" [],   -- same body, other layout\n'
            "    layoutIdx := 0 }\n"
        )
        findings = proof_health.scan_lean_text(src, scan_siblings=False)
        self.assertEqual([(f.rule, f.line, f.symbol) for f in findings], [(R5, 5, "tyEnumCopy")])
        self.assertIn("signature and body as `private def tyEnum` on L1", findings[0].message)

    def test_rule5_equation_and_match_arm_headers(self) -> None:
        # Pattern-matching proofs end their statement at the first `| ...` equation;
        # `| ...` arms of a `match` inside a statement are part of the statement.
        src = (
            "private theorem eqn_a : ∀ (l : List Nat), l ++ [] = l\n"
            "  | [] => rfl\n"
            "  | x :: xs => by simp\n"
            "private theorem eqn_b : ∀ (m : List Nat), m ++ [] = m\n"
            "  | m => List.append_nil m\n"
            "private theorem arm_a (b : Bool) : (match b with\n"
            "    | true => 1\n"
            "    | false => 0) ≤ 1 := by cases b <;> decide\n"
            "private theorem arm_b (c : Bool) : (match c with\n"
            "    | true => 1\n"
            "    | false => 1) ≤ 1 := by cases c <;> decide\n"
        )
        self.assertEqual(scan(src), [(R5, 4, "eqn_b")])

    def test_deep_simp_configs_entry_heads_and_multiline_unfold(self) -> None:
        src = (
            "theorem deep_and_unfold : True := by\n"
            "  simp (disch := by exact f (g (h x))) only [↓ wpMirExecSym]\n"
            "  dsimpa [wpMirExecSym]\n"
            "  dsimp_all [wpMirExecSym]\n"
            "  simp only' [wpMirExecSym]\n"
            "  simp [← Trusted.Sequence.length, lookupBlock_zero Mir.Crate.Item.body]\n"
            "  simp [h (Trusted.Sequence.length bs)]\n"
            "  unfold\n"
            "    foo\n"
            "    Mir.Crate.Item.body\n"
            "  delta\n"
            "    at'\n"
            "    bitwiseAndBits\n"
            "  have := Stream.unfold bitwiseOrBits\n"
            "  have := (by unfold foo) Mir.Crate.Item.body\n"
            "  set_option trace.profiler.threshold 4_9\n"
            "  set_option trace.profiler.threshold 5_0\n"
            "  Foo.set_option trace.profiler.threshold 1\n"
        )
        findings = proof_health.scan_lean_text(src, scan_siblings=False)
        self.assertEqual(
            [(f.rule, f.line, f.symbol) for f in findings],
            [
                (R1, 2, "wpMirExecSym"),
                (R2, 10, "Mir.Crate.Item.body"),
                (R3, 13, "bitwiseAndBits"),
                (R4, 16, "trace.profiler.threshold=49"),
            ],
        )
        self.assertIn("via `delta`", findings[2].message)

    def test_rule5_alpha_normalized_def_bodies_nested_binders_and_indented_sections(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            sibling = tmp_dir / "SibDef.lean"
            sibling.write_text(
                "private def addOne (x : Nat) : Nat := x + 1\n",
                encoding="utf-8",
            )
            target = tmp_dir / "TargetDef.lean"
            target.write_text(
                "section Inner\n"
                "  private def incVal (value : Nat) : Nat := value + 1\n"
                '  private def strOne : String := "a  b"\n'
                '  private def strTwo : String := "a b"\n'
                '  private def strDup : String := "a  b"\n'
                "  private theorem nested_one (xs : List (Nat × Nat)) [Decidable (xs = [])] :\n"
                "      xs.length = xs.length := rfl\n"
                "  private theorem nested_two (ys : List (Nat × Nat)) [Decidable (ys = [])] :\n"
                "      ys.length = ys.length := rfl\n"
                "end Inner\n",
                encoding="utf-8",
            )
            clear_in_process_caches()
            findings = proof_health.scan_lean_file(target, scan_siblings=True)
            self.assertEqual(
                [(f.line, f.symbol) for f in findings if f.rule == R5],
                [
                    (2, "incVal"),
                    (5, "strDup"),
                    (8, "nested_two"),
                ],
            )


class TestDeltaOnlyPostEditCheck(unittest.TestCase):
    def test_delta_only_jetski_and_claude_payloads(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            cache_file = tmp_dir / "cache.json"
            lean_file = tmp_dir / "Proof.lean"

            # 1. Clean edit -> no warning
            clean_v1 = "theorem t : True := by\n  dsimp only [foo]\n  trivial\n"
            lean_file.write_text(clean_v1, encoding="utf-8")
            fb1 = proof_health.check_post_edit_proof_health(
                lean_file,
                jetski_edit(lean_file, "  trivial\n", "  dsimp only [foo]\n  trivial\n"),
                cache_path=cache_file,
            )
            self.assertEqual(fb1, "")

            # 2. Introduce `dsimp [wpMirExecSym]` via Jetski `Target`/`Replacement` -> warning (+1)
            bad_v2 = "theorem t : True := by\n  dsimp only [foo, wpMirExecSym]\n  trivial\n"
            lean_file.write_text(bad_v2, encoding="utf-8")
            fb2 = proof_health.check_post_edit_proof_health(
                lean_file,
                jetski_edit(lean_file, "  dsimp only [foo]\n", "  dsimp only [foo, wpMirExecSym]\n"),
                cache_path=cache_file,
            )
            self.assertIn("[Anneal Proof Health]", fb2)
            self.assertIn("dsimp_forbidden_sym (+1", fb2)
            self.assertIn("L2", fb2)

            # 3. Unrelated Claude `Edit` while `wpMirExecSym` remains -> delta 0 -> ""
            same_v3 = "-- comment added\n" + bad_v2
            lean_file.write_text(same_v3, encoding="utf-8")
            payload_v3 = {
                "tool_input": {
                    "file_path": str(lean_file),
                    "old_string": "theorem t : True := by\n",
                    "new_string": "-- comment added\ntheorem t : True := by\n",
                }
            }
            self.assertEqual(
                proof_health.check_post_edit_proof_health(lean_file, payload_v3, cache_path=cache_file),
                "",
            )

            # 4. Fix the anti-pattern via Claude `MultiEdit` -> delta -1 -> ""
            fixed_v4 = "-- comment added\ntheorem t : True := by\n  dsimp only [foo]\n  trivial\n"
            lean_file.write_text(fixed_v4, encoding="utf-8")
            payload_v4 = {
                "tool_input": {
                    "file_path": str(lean_file),
                    "edits": [
                        {
                            "old_string": "  dsimp only [foo, wpMirExecSym]\n",
                            "new_string": "  dsimp only [foo]\n",
                        }
                    ],
                }
            }
            self.assertEqual(
                proof_health.check_post_edit_proof_health(lean_file, payload_v4, cache_path=cache_file),
                "",
            )

            # 5. `write_file` overwrite (no diff pair) falls back to the persisted cache
            bad_v5 = "set_option trace.profiler.threshold 10\n" + fixed_v4
            lean_file.write_text(bad_v5, encoding="utf-8")
            payload_v5 = {
                "toolCall": {"args": {"Path": str(lean_file), "Content": bad_v5, "Overwrite": True}}
            }
            fb5 = proof_health.check_post_edit_proof_health(lean_file, payload_v5, cache_path=cache_file)
            self.assertIn("low_profiler_threshold (+1", fb5)
            self.assertIn("L1", fb5)

    def test_deletion_or_overwrite_of_unseen_file_is_silent(self) -> None:
        # Without a cached baseline, neither a deletion nor an overwrite can be
        # inverted, so pre-existing findings must not be reported as new.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            lean_file = tmp_dir / "Old.lean"
            text = "theorem t : True := by\n  dsimp [wpMirExecSym]\n  trivial\n"
            lean_file.write_text(text, encoding="utf-8")
            deletion = jetski_edit(lean_file, "  -- obsolete note\n", "")
            self.assertEqual(
                proof_health.check_post_edit_proof_health(
                    lean_file, deletion, cache_path=tmp_dir / "c1.json"
                ),
                "",
            )
            overwrite = {"toolCall": {"args": {"Path": str(lean_file), "Content": text, "Overwrite": True}}}
            self.assertEqual(
                proof_health.check_post_edit_proof_health(
                    lean_file, overwrite, cache_path=tmp_dir / "c2.json"
                ),
                "",
            )
            claude_write = {"tool_input": {"file_path": str(lean_file), "content": text}}
            self.assertEqual(
                proof_health.check_post_edit_proof_health(
                    lean_file, claude_write, cache_path=tmp_dir / "c3.json"
                ),
                "",
            )

    def test_new_file_and_append_writes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            cache_file = tmp_dir / "cache.json"
            lean_file = tmp_dir / "New.lean"
            text = "theorem t : True := by\n  simp [wpMirExecSym]\n  trivial\n"
            lean_file.write_text(text, encoding="utf-8")
            # Jetski `write_file` without `Overwrite`/`Append` only succeeds on a new file.
            created = {"toolCall": {"args": {"Path": str(lean_file), "Content": text}}}
            fb = proof_health.check_post_edit_proof_health(lean_file, created, cache_path=cache_file)
            self.assertIn("`dsimp_forbidden_sym` (+1 at L2)", fb)

            appended = "theorem u : True := by\n  dsimp only [bitwiseOrBits]\n  trivial\n"
            lean_file.write_text(text + appended, encoding="utf-8")
            append_payload = {
                "toolCall": {"args": {"Path": str(lean_file), "Content": appended, "Append": True}}
            }
            fb2 = proof_health.check_post_edit_proof_health(
                lean_file, append_payload, cache_path=tmp_dir / "fresh.json"
            )
            self.assertIn("`raw_bitwise_unfold` (+1 at L5)", fb2)
            self.assertNotIn("dsimp_forbidden_sym", fb2)

            # Claude `Write` reporting `type: "create"`
            other = tmp_dir / "Created.lean"
            other.write_text(text, encoding="utf-8")
            claude_create = {
                "tool_input": {"file_path": str(other), "content": text},
                "tool_response": {"type": "create", "filePath": str(other)},
            }
            fb3 = proof_health.check_post_edit_proof_health(
                other, claude_create, cache_path=tmp_dir / "fresh2.json"
            )
            self.assertIn("`dsimp_forbidden_sym` (+1 at L2)", fb3)

    def test_insertion_before_identical_occurrence_reports_inserted_line(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            lean_file = tmp_dir / "Order.lean"
            body = "  simp [Trusted.Sequence.length]\n"
            before = "theorem t : True := by\n  skip\n" + body + "  trivial\n"
            after = "theorem t : True := by\n" + body + "  skip\n" + body + "  trivial\n"
            lean_file.write_text(after, encoding="utf-8")
            res = proof_health.evaluate_post_edit_proof_health(
                lean_file,
                jetski_edit(lean_file, "theorem t : True := by\n", "theorem t : True := by\n" + body),
                cache_path=tmp_dir / "cache.json",
            )
            self.assertEqual(res["deltas"][R1], 1)
            self.assertEqual([f.line for f in res["new_findings"]], [2])
            self.assertIn("(+1 at L2)", res["feedback"])
            self.assertEqual(before.count(body), 1)

    def test_claude_original_file_is_used_as_pre_edit_text(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            lean_file = tmp_dir / "Orig.lean"
            before = "theorem t : True := by\n  trivial\n"
            after = "theorem t : True := by\n  dsimp [wpMirExecSym]\n  trivial\n"
            lean_file.write_text(after, encoding="utf-8")
            # The diff pair alone is ambiguous; `originalFile` gives the exact pre-edit text.
            payload = {
                "tool_input": {"file_path": str(lean_file), "old_string": "x", "new_string": "y"},
                "tool_response": {"originalFile": before},
            }
            res = proof_health.evaluate_post_edit_proof_health(
                lean_file, payload, cache_path=tmp_dir / "cache.json"
            )
            self.assertEqual(res["before_counts"][R1], 0)
            self.assertEqual(res["deltas"][R1], 1)

    def test_cache_reuse_skips_second_scan_only_for_identical_text(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            cache_file = tmp_dir / "cache.json"
            lean_file = tmp_dir / "Reuse.lean"
            v1 = "theorem t : True := by\n  trivial\n"
            lean_file.write_text(v1, encoding="utf-8")
            proof_health.check_post_edit_proof_health(lean_file, None, cache_path=cache_file)

            calls: list[int] = []
            original_scan = proof_health.scan_lean_text

            def counting_scan(*args, **kwargs):
                calls.append(1)
                return original_scan(*args, **kwargs)

            proof_health.scan_lean_text = counting_scan
            try:
                v2 = "theorem t : True := by\n  skip\n  trivial\n"
                lean_file.write_text(v2, encoding="utf-8")
                fb = proof_health.check_post_edit_proof_health(
                    lean_file,
                    jetski_edit(lean_file, "  trivial\n", "  skip\n  trivial\n"),
                    cache_path=cache_file,
                )
                self.assertEqual(fb, "")
                self.assertEqual(len(calls), 1)  # the pre-edit text matched the cache entry

                # The file changed behind the hook's back: the cache entry no longer
                # describes the reconstructed pre-edit text, which is scanned instead.
                lean_file.write_text(
                    "theorem t : True := by\n  dsimp [wpMirExecSym]\n  dsimp [wpMirExecSym]\n",
                    encoding="utf-8",
                )
                calls.clear()
                fb2 = proof_health.check_post_edit_proof_health(
                    lean_file,
                    jetski_edit(
                        lean_file,
                        "\n  dsimp [wpMirExecSym]\n",
                        "\n  dsimp [wpMirExecSym]\n  dsimp [wpMirExecSym]\n",
                    ),
                    cache_path=cache_file,
                )
                self.assertEqual(len(calls), 2)
                self.assertIn("`dsimp_forbidden_sym` (+1 at L3)", fb2)
            finally:
                proof_health.scan_lean_text = original_scan

    def test_cache_file_is_robust_and_written_atomically(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            lean_file = tmp_dir / "Robust.lean"
            text = "theorem t : True := by\n  dsimp [wpMirExecSym]\n"
            lean_file.write_text(text, encoding="utf-8")
            key = str(lean_file.resolve())

            # Malformed counts read as 0 instead of raising.
            cache_file = tmp_dir / "cache.json"
            version = proof_health.CACHE_FORMAT_VERSION
            cache_file.write_text(
                json.dumps({key: {R1: "not-a-number", "_ver": version}}), encoding="utf-8"
            )
            fb = proof_health.check_post_edit_proof_health(
                lean_file, {"toolCall": {"args": {"Path": str(lean_file)}}}, cache_path=cache_file
            )
            self.assertIn("dsimp_forbidden_sym (+1", fb)

            # Counts written under another cache format version are never compared
            # (their rules may differ), so they cannot produce a false increase.
            cache_file.write_text(
                json.dumps({key: {R1: 0, "_ver": version - 1}}), encoding="utf-8"
            )
            self.assertEqual(
                proof_health.check_post_edit_proof_health(
                    lean_file, {"toolCall": {"args": {"Path": str(lean_file)}}}, cache_path=cache_file
                ),
                "",
            )

            # Garbage content reads as an empty cache.
            cache_file.write_text("{ not json", encoding="utf-8")
            self.assertEqual(
                proof_health.check_post_edit_proof_health(lean_file, None, cache_path=cache_file), ""
            )
            data = json.loads(cache_file.read_text(encoding="utf-8"))
            self.assertEqual(data[key][R1], 1)
            self.assertEqual(sorted(p.name for p in tmp_dir.iterdir() if p.name.endswith(".tmp")), [])

            # A symlink planted at the cache path is replaced, not written through.
            victim = tmp_dir / "victim.txt"
            victim.write_text("precious", encoding="utf-8")
            link = tmp_dir / "link-cache.json"
            link.symlink_to(victim)
            proof_health.check_post_edit_proof_health(lean_file, None, cache_path=link)
            self.assertEqual(victim.read_text(encoding="utf-8"), "precious")
            self.assertFalse(link.is_symlink())
            self.assertIn(key, json.loads(link.read_text(encoding="utf-8")))

    def test_persisted_sibling_index_avoids_relexing_siblings(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            cache_file = tmp_dir / "cache.json"
            sibling = tmp_dir / "Sibling.lean"
            sibling.write_text("private theorem helper (n : Nat) : n = n := rfl\n", encoding="utf-8")
            target = tmp_dir / "Target.lean"
            target.write_text("private theorem other (k : Nat) : k + 0 = k := rfl\n", encoding="utf-8")
            settle(sibling)
            clear_in_process_caches()
            proof_health.check_post_edit_proof_health(target, None, cache_path=cache_file)
            index_file = proof_health.sibling_index_path(cache_file, target.parent)
            index = json.loads(index_file.read_text(encoding="utf-8"))
            self.assertIn(str(sibling), index)
            self.assertNotIn(str(sibling), json.loads(cache_file.read_text(encoding="utf-8")))

            lexed: list[str] = []
            original_extract = proof_health.extract_private_decls

            def counting_extract(stripped, *args, **kwargs):
                lexed.append(kwargs.get("file_path", ""))
                return original_extract(stripped, *args, **kwargs)

            proof_health.extract_private_decls = counting_extract
            try:
                clear_in_process_caches()  # as in a fresh hook process
                target.write_text(
                    "private theorem other (k : Nat) : k + 0 = k := rfl\n"
                    "private theorem helper (m : Nat) : m = m := rfl\n",
                    encoding="utf-8",
                )
                fb = proof_health.check_post_edit_proof_health(
                    target,
                    {"toolCall": {"args": {"Path": str(target)}}},
                    cache_path=cache_file,
                )
                self.assertIn("`duplicate_private_lemma` (+1 at L2)", fb)
                self.assertNotIn(str(sibling), lexed)  # restored from the persisted index

                # A changed sibling (new mtime/size) is lexed again.
                sibling.write_text(
                    "private theorem helper2 (n : Nat) : n = n := rfl\n", encoding="utf-8"
                )
                clear_in_process_caches()
                lexed.clear()
                proof_health.check_post_edit_proof_health(target, None, cache_path=cache_file)
                self.assertIn(str(sibling), lexed)
            finally:
                proof_health.extract_private_decls = original_extract

    def test_persisted_formats_are_versioned_and_fresh_files_not_persisted(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            cache_file = tmp_dir / "cache.json"
            sibling = tmp_dir / "Sib.lean"
            sibling.write_text("private theorem s (n : Nat) : n = n := rfl\n", encoding="utf-8")
            target = tmp_dir / "Tgt.lean"
            target.write_text("private theorem t (k : Nat) : k + 0 = k := rfl\n", encoding="utf-8")
            index_file = proof_health.sibling_index_path(cache_file, tmp_dir)
            self.assertIn(f".siblings-v{proof_health.CACHE_FORMAT_VERSION}-", index_file.name)

            # A sibling written just now may still change within the same timestamp
            # tick, so it is lexed but not persisted.
            clear_in_process_caches()
            proof_health.check_post_edit_proof_health(target, None, cache_path=cache_file)
            self.assertFalse(index_file.exists())
            entry = json.loads(cache_file.read_text(encoding="utf-8"))[str(target.resolve())]
            self.assertEqual(entry["_ver"], proof_health.CACHE_FORMAT_VERSION)

            settle(sibling)
            clear_in_process_caches()
            proof_health.check_post_edit_proof_health(target, None, cache_path=cache_file)
            self.assertIn(str(sibling), json.loads(index_file.read_text(encoding="utf-8")))

    def test_sibling_signature_is_stable_across_processes(self) -> None:
        # Consecutive edits with unchanged siblings reuse the cached pre-edit counts
        # (one scan) even when the second process restores sibling declarations from
        # the persisted index instead of lexing them.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            cache_file = tmp_dir / "cache.json"
            sibling = tmp_dir / "Sib.lean"
            sibling.write_text(
                "private theorem a1 (n : Nat) : n = n := rfl\n"
                "private theorem a2 (n : Nat) : n + 0 = n := rfl\n"
                "private def d1 : Nat := 1\n",
                encoding="utf-8",
            )
            settle(sibling)
            target = tmp_dir / "Tgt.lean"
            v1 = "private theorem b (k : Nat) : k * 1 = k := by omega\n"
            target.write_text(v1, encoding="utf-8")
            clear_in_process_caches()
            proof_health.check_post_edit_proof_health(target, None, cache_path=cache_file)

            calls: list[int] = []
            original_scan = proof_health.scan_lean_text

            def counting_scan(*args, **kwargs):
                calls.append(1)
                return original_scan(*args, **kwargs)

            proof_health.scan_lean_text = counting_scan
            try:
                clear_in_process_caches()  # fresh process: siblings come from the index
                target.write_text(v1 + "-- note\n", encoding="utf-8")
                fb = proof_health.check_post_edit_proof_health(
                    target,
                    jetski_edit(target, "by omega\n", "by omega\n-- note\n"),
                    cache_path=cache_file,
                )
                self.assertEqual(fb, "")
                self.assertEqual(len(calls), 1)
            finally:
                proof_health.scan_lean_text = original_scan

    def test_persisted_sibling_index_on_episode1_directory_under_5ms(self) -> None:
        bit_validity = REPO_ROOT / "theory" / "Anneal" / "BitValidity.lean"
        self.assertTrue(bit_validity.is_file())
        index: dict = {}
        clear_in_process_caches()
        decls = proof_health._collect_sibling_private_decls(bit_validity, persisted=index)
        self.assertGreater(len(decls), 0)
        snapshot = json.loads(json.dumps(index))  # what a later hook process loads

        def restore() -> None:
            clear_in_process_caches()
            proof_health._collect_sibling_private_decls(bit_validity, persisted=dict(snapshot))

        elapsed_ms = best_of_ms(restore)
        self.assertLess(elapsed_ms, 5.0, f"sibling index restore took {elapsed_ms:.2f} ms")

    def test_ambiguous_single_occurrence_edits_and_sibling_sig_invalidation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            # 1. Uncached Claude `Edit` (`replace_all` unset) where `new_string` already
            # existed on L2: only 1 occurrence was added (+1 at L5, NOT +2).
            claude_file = tmp_dir / "ClaudeAmbig.lean"
            after = (
                "theorem t1 : True := by\n"
                "  dsimp [wpMirExecSym]\n"
                "  trivial\n"
                "theorem t2 : True := by\n"
                "  dsimp [wpMirExecSym]\n"
                "  trivial\n"
            )
            claude_file.write_text(after, encoding="utf-8")
            claude_payload = {
                "tool_input": {
                    "file_path": str(claude_file),
                    "old_string": "  skip\n",
                    "new_string": "  dsimp [wpMirExecSym]\n",
                }
            }
            res_c = proof_health.evaluate_post_edit_proof_health(
                claude_file, claude_payload, cache_path=tmp_dir / "c_claude.json"
            )
            self.assertEqual(res_c["deltas"][R1], 1)
            self.assertEqual(len(res_c["new_findings"]), 1)

            # 2. Uncached Jetski `edit_file` carrying `Made 1 replacement ... starting at line 5`:
            # exact line L5 reconstructed and attributed (+1 at L5).
            jetski_file = tmp_dir / "JetskiAmbig.lean"
            jetski_file.write_text(after, encoding="utf-8")
            jetski_payload = {
                "result": f"Made 1 replacement in {jetski_file} starting at line 5 (+1/-1 lines).",
                **jetski_edit(jetski_file, "  skip\n", "  dsimp [wpMirExecSym]\n"),
            }
            res_j = proof_health.evaluate_post_edit_proof_health(
                jetski_file, jetski_payload, cache_path=tmp_dir / "c_jetski.json"
            )
            self.assertEqual(res_j["deltas"][R1], 1)
            self.assertEqual([f.line for f in res_j["new_findings"]], [5])
            self.assertIn("(+1 at L5)", res_j["feedback"])

            # 3. Sibling signature edit in-place invalidates `_sib` cache on Target, and
            # deleting the sibling prunes it from the persisted sibling index.
            sib = tmp_dir / "Sib.lean"
            sib.write_text("private theorem h (n : Nat) : n = 0 := sorry\n", encoding="utf-8")
            settle(sib)
            tgt = tmp_dir / "Tgt.lean"
            tgt_v1 = "private theorem g (m : Nat) : m = 1 := sorry\n"
            tgt.write_text(tgt_v1, encoding="utf-8")
            scache = tmp_dir / "scache.json"
            clear_in_process_caches()
            self.assertEqual(proof_health.check_post_edit_proof_health(tgt, None, cache_path=scache), "")
            # Edit `Sib.lean` on the same line with the same name so its signature now matches `g`:
            sib.write_text("private theorem h (n : Nat) : n = 1 := sorry\n", encoding="utf-8")
            clear_in_process_caches()
            tgt_v2 = tgt_v1 + "-- touch\n"
            tgt.write_text(tgt_v2, encoding="utf-8")
            # Pre-edit `tgt_v1` now ALREADY conflicted with updated `Sib.lean`, so adding a comment
            # to `Tgt.lean` must NOT reuse the stale 0-count cache entry or claim a false +1!
            fb_sib = proof_health.check_post_edit_proof_health(
                tgt, jetski_edit(tgt, "sorry\n", "sorry\n-- touch\n"), cache_path=scache
            )
            self.assertEqual(fb_sib, "")
            # Delete `Sib.lean` and verify persisted sibling index prunes it.
            settle(sib)
            clear_in_process_caches()
            proof_health.check_post_edit_proof_health(tgt, None, cache_path=scache)
            sib.unlink()
            clear_in_process_caches()
            proof_health.check_post_edit_proof_health(tgt, None, cache_path=scache)
            idx_data = json.loads(
                proof_health.sibling_index_path(scache, tmp_dir).read_text(encoding="utf-8")
            )
            self.assertNotIn(str(sib), idx_data)


class TestPerformanceAndDogfood(unittest.TestCase):
    def test_synthetic_6000_line_file_under_5ms(self) -> None:
        block = (
            "/-- Docstring mentioning dsimp [wpMirExecSym] and Mir.Foo.body -/\n"
            "theorem synthetic_lemma_{i} (a b : Nat) (h : a = b) : a + 0 = b := by\n"
            "  -- single line comment bitwiseAndBits\n"
            "  simp only [Nat.add_zero, Trusted.Sequence.length_append] at h ⊢\n"
            "  rw [show a = b from h]\n"
            "  exact h\n"
        )
        parts = []
        for i in range(1000):
            parts.append(block.format(i=i))
            if i % 100 == 0:
                parts.append(f"private theorem helper_{i} (n : Nat) : n + {i} = {i} + n := by omega\n")
        parts.insert(500, "theorem planted : True := by\n  dsimp only [wpMirExecSym]\n  trivial\n")
        text = "".join(parts)
        self.assertGreaterEqual(text.count("\n"), 6000)
        planted_line = text[: text.index("dsimp only [wpMirExecSym]")].count("\n") + 1

        findings = proof_health.scan_lean_text(text, scan_siblings=False)
        self.assertEqual([(f.rule, f.line) for f in findings], [(R1, planted_line)])
        elapsed_ms = best_of_ms(lambda: proof_health.scan_lean_text(text, scan_siblings=False))
        self.assertLess(elapsed_ms, 5.0, f"6,000-line synthetic scan took {elapsed_ms:.2f} ms")

    def test_definition_heavy_files_have_no_quadratic_blowup(self) -> None:
        # Regression guard for the private-definition comparison: many same-typed
        # definitions, indented inside a namespace or with large bodies, must cost
        # roughly linear time. (A quadratic comparison took 25-40 ms on the first.)
        indented = ["namespace Foo\n"]
        for i in range(300):
            indented.append(
                f"  private def val{i} : Nat :=\n    let a := {i}\n    let b := a + {i}\n    a * b + {i}\n"
            )
        indented.append("end Foo\n")
        large = []
        for i in range(150):
            stmts = "\n".join(
                f"    stmt{j} := .assign (.local {j}) (.use (.copy (.local {i + j}))),"
                for j in range(30)
            )
            large.append(
                f"private def body{i} : Body :=\n  {{ locals := #[x],\n{stmts}\n    blocks := #[] }}\n"
            )
        for label, text in (("indented", "".join(indented)), ("large", "".join(large))):
            self.assertEqual(proof_health.scan_lean_text(text, scan_siblings=False), [])
            elapsed_ms = best_of_ms(
                lambda: proof_health.scan_lean_text(text, scan_siblings=False), budget_ms=15.0
            )
            self.assertLess(elapsed_ms, 15.0, f"{label} definitions took {elapsed_ms:.2f} ms")

    def test_dogfood_episode1_files_under_5ms(self) -> None:
        bit_validity = REPO_ROOT / "theory" / "Anneal" / "BitValidity.lean"
        mir_cast = REPO_ROOT / "theory" / "Anneal" / "Mir" / "Cast.lean"
        for path in (bit_validity, mir_cast):
            self.assertTrue(path.is_file(), f"Missing {path}")
            elapsed_ms = best_of_ms(lambda: proof_health.scan_lean_file(path, scan_siblings=True))
            self.assertLess(elapsed_ms, 5.0, f"{path.name} scan took {elapsed_ms:.2f} ms")

        self.assertEqual(proof_health.scan_lean_file(bit_validity), [])

        # Episode 1 normalizes list lengths with `simp [..., Trusted.Sequence.length, ...]`
        # (5 sites, all added in Episode 1). The rule as specified covers `simp [...]`
        # lists, so these are reported rather than exempted; `theory/` is outside this
        # episode's scope. Nothing else in the file may fire, and no new site may appear.
        cast_findings = proof_health.scan_lean_file(mir_cast)
        lines = mir_cast.read_text(encoding="utf-8").split("\n")
        self.assertLessEqual(len(cast_findings), 5)
        for f in cast_findings:
            self.assertEqual((f.rule, f.symbol), (R1, "Trusted.Sequence.length"))
            source = lines[f.line - 1]
            self.assertIn("simp [", source)
            self.assertNotIn("dsimp", source)


class TestTranscriptLatencyTelemetry(unittest.TestCase):
    def test_compute_unbatched_tool_latencies_events_and_jsonl(self) -> None:
        events = [
            # Standalone unbatched fast LSP calls: 10 ms, 20 ms, 30 ms -> mean=20.0, median=20.0
            {"tool": "lean_goal", "duration_ms": 10.0, "batch_id": "turn_1"},
            {"tool": "lean_hover", "duration_ms": 20.0, "batch_id": "turn_2"},
            {"tool": "lean_goal", "duration_ms": 30.0, "batch_id": "turn_3"},
            # Parallel batch with a long-running `run_command` (4500 ms >= 1000 ms):
            # both calls are `batched_with_long_call` and excluded from unbatched stats
            {"tool": "lean_goal", "duration_ms": 4500.0, "batch_id": "turn_4"},
            {"tool": "run_command", "duration_ms": 4500.0, "batch_id": "turn_4"},
            # Malformed/partial entry with no timestamp -> ignored cleanly without crashing
            {"tool": "lean_goal"},
        ]
        stats = proof_health.compute_unbatched_tool_latencies(events)
        self.assertEqual(stats["unbatched_count"], 3)
        self.assertEqual(stats["batched_with_long_call_count"], 2)
        self.assertAlmostEqual(stats["unbatched_mean_ms"], 20.0)
        self.assertAlmostEqual(stats["unbatched_median_ms"], 20.0)
        self.assertEqual(stats["by_tool"]["lean_goal"]["unbatched_count"], 2)
        self.assertEqual(stats["by_tool"]["lean_goal"]["batched_with_long_call_count"], 1)
        self.assertAlmostEqual(stats["by_tool"]["lean_goal"]["unbatched_mean_ms"], 20.0)

        # Also read a `.jsonl` file whose step objects carry per-call timings
        with tempfile.TemporaryDirectory() as tmp:
            jsonl_path = Path(tmp) / "transcript.jsonl"
            steps = [
                {
                    "step_index": 1,
                    "type": "PLANNER_RESPONSE",
                    "tool_calls": [
                        {
                            "name": "lean_diagnostics",
                            "started_at": "2026-11-09T12:00:00.000Z",
                            "completed_at": "2026-11-09T12:00:00.025Z",
                        }
                    ],
                },
                {
                    "step_index": 2,
                    "type": "PLANNER_RESPONSE",
                    "tool_calls": [
                        {"name": "lean_goal", "duration_ms": 15.0},
                        {"name": "run_command", "duration_ms": 3200.0},
                    ],
                },
            ]
            jsonl_path.write_text("\n".join(json.dumps(s) for s in steps) + "\n", encoding="utf-8")
            jstats = proof_health.compute_unbatched_tool_latencies(jsonl_path)
            self.assertEqual(jstats["unbatched_count"], 1)
            self.assertEqual(jstats["batched_with_long_call_count"], 2)
            self.assertAlmostEqual(jstats["unbatched_mean_ms"], 25.0, places=3)

    def test_jetski_transcript_result_steps_are_paired_with_planner_calls(self) -> None:
        # Real Jetski transcripts: the planner step lists its calls without timings and
        # each call's result step follows (in order) with `Created At` / `Completed At`
        # timestamps in its content. System messages in between carry no result.
        def result(ts0: str, ts1: str, idx: int) -> dict:
            return {
                "step_index": idx,
                "type": "GENERIC",
                "content": f"Created At: {ts0}\nCompleted At: {ts1}\nCommand exited with code 0.",
            }

        steps = [
            {"step_index": 0, "type": "USER_INPUT", "content": "go"},
            {
                "step_index": 1,
                "type": "PLANNER_RESPONSE",
                "tool_calls": [{"name": "read_file", "args": {}}, {"name": "run_command", "args": {}}],
            },
            {
                "step_index": 2,
                "type": "SYSTEM_MESSAGE",
                "content": "Created At: 2026-11-09T12:00:00Z\nCompleted At: 2026-11-09T12:09:00Z",
            },
            result("2026-11-09T12:00:00Z", "2026-11-09T12:00:00Z", 3),
            result("2026-11-09T12:00:00Z", "2026-11-09T12:00:04Z", 4),
            {"step_index": 5, "type": "PLANNER_RESPONSE", "tool_calls": [{"name": "read_file"}]},
            result("2026-11-09T12:00:05Z", "2026-11-09T12:00:06Z", 6),
            {"step_index": 7, "type": "PLANNER_RESPONSE", "tool_calls": [{"name": "edit_file"}]},
            result("2026-11-09T12:00:07Z", "2026-11-09T12:00:07Z", 8),
        ]
        stats = proof_health.compute_unbatched_tool_latencies(steps)
        self.assertEqual(stats["total_count"], 4)
        self.assertEqual(stats["batched_with_long_call_count"], 2)
        self.assertEqual(
            sorted(e["tool"] for e in stats["batched_with_long_call"]), ["read_file", "run_command"]
        )
        self.assertEqual(stats["unbatched_count"], 2)
        self.assertAlmostEqual(stats["unbatched_mean_ms"], 500.0)
        self.assertAlmostEqual(stats["unbatched_median_ms"], 500.0)
        self.assertEqual(stats["by_tool"]["read_file"]["unbatched_count"], 1)
        self.assertEqual(stats["by_tool"]["read_file"]["batched_with_long_call_count"], 1)

        # The same steps read from a `.jsonl` file (with a corrupt line) agree.
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "transcript.jsonl"
            path.write_text(
                "\n".join(json.dumps(s) for s in steps) + "\n{not json\n", encoding="utf-8"
            )
            self.assertEqual(
                proof_health.compute_unbatched_tool_latencies(str(path))["unbatched_count"], 2
            )

    def test_batch_keys_and_malformed_fields_do_not_crash(self) -> None:
        events = [
            # `step_index` 0 is a real batch id: both calls share batch 0.
            {"tool": "a", "duration_ms": 5.0, "step_index": 0},
            {"tool": "b", "duration_ms": 2000.0, "step_index": 0},
            {"tool": "c", "duration_ms": 7.0, "batch_size": "many"},
            {"tool": "d", "started_at": "garbage", "completed_at": None},
            {"tool": "e", "duration_ms": -3},
            "not a dict",
        ]
        stats = proof_health.compute_unbatched_tool_latencies(events)
        self.assertEqual(stats["batched_with_long_call_count"], 2)
        self.assertEqual(stats["unbatched_count"], 1)
        self.assertAlmostEqual(stats["unbatched_mean_ms"], 7.0)
        empty = proof_health.compute_unbatched_tool_latencies([])
        self.assertIsNone(empty["unbatched_mean_ms"])
        self.assertIsNone(empty["unbatched_median_ms"])
        self.assertEqual(empty["unbatched_count"], 0)

    def test_running_background_tasks_error_steps_and_nonfinite_durations(self) -> None:
        # Batch 1: `run_command` backgrounds (`status == "RUNNING"`, no `Completed At:`)
        # alongside `lean_goal` (`0s`). `lean_goal` must keep its own tool name AND be
        # classified as `batched_with_long_call` because its sibling backgrounded.
        # Batch 2: `read_file` errors without timestamps alongside `lean_hover` (`0s`).
        # `lean_hover` must NOT be misattributed to `read_file`.
        steps = [
            {
                "step_index": 10,
                "type": "PLANNER_RESPONSE",
                "tool_calls": [{"name": "run_command"}, {"name": "lean_goal"}],
            },
            {
                "step_index": 11,
                "source": "MODEL",
                "type": "GENERIC",
                "status": "RUNNING",
                "content": "Created At: 2026-11-10T00:50:16Z\nTool is running as a background task",
            },
            {
                "step_index": 12,
                "source": "MODEL",
                "type": "GENERIC",
                "status": "DONE",
                "content": "Created At: 2026-11-10T00:50:16Z\nCompleted At: 2026-11-10T00:50:16Z\nok",
            },
            {
                "step_index": 20,
                "type": "PLANNER_RESPONSE",
                "tool_calls": [{"name": "read_file"}, {"name": "lean_hover"}],
            },
            {
                "step_index": 21,
                "source": "MODEL",
                "type": "GENERIC",
                "status": "ERROR",
                "content": "Error: file not found",
            },
            {
                "step_index": 22,
                "source": "MODEL",
                "type": "GENERIC",
                "status": "DONE",
                "content": "Created At: 2026-11-10T00:51:00Z\nCompleted At: 2026-11-10T00:51:00Z\nok",
            },
            # Reject bool, NaN, Inf, and empty-string batch_id merging
            {"tool": "bad_bool", "duration_ms": True},
            {"tool": "bad_inf", "duration_ms": float("inf")},
            {"tool": "bad_nan", "duration_ms": float("nan")},
            {"tool": "solo_1", "duration_ms": 12.0, "batch_id": ""},
            {"tool": "solo_2", "duration_ms": 2500.0, "batch_id": ""},
        ]
        stats = proof_health.compute_unbatched_tool_latencies(steps)
        self.assertEqual([e["tool"] for e in stats["batched_with_long_call"]], ["lean_goal"])
        self.assertEqual(
            sorted(e["tool"] for e in stats["unbatched"]),
            ["lean_hover", "solo_1", "solo_2"],
        )
        self.assertNotIn("bad_bool", stats["by_tool"])
        self.assertNotIn("bad_inf", stats["by_tool"])
        self.assertNotIn("bad_nan", stats["by_tool"])


class TestPostToolUseHookIntegration(unittest.TestCase):
    def run_hook(self, payload: object, env: dict[str, str], runner: str | None = None) -> dict:
        stdin = payload if isinstance(payload, str) else json.dumps(payload)
        argv = [sys.executable, "-B"] + ([str(HOOK_PATH)] if runner is None else ["-c", runner])
        proc = subprocess.run(argv, input=stdin, text=True, capture_output=True, env=env, check=True)
        return json.loads(proc.stdout.strip())

    def hook_env(self, cache_file: Path) -> dict[str, str]:
        env = dict(os.environ)
        env.pop("ANNEAL_DISABLE_LSP_HOOK", None)
        env["ANNEAL_PROOF_HEALTH_CACHE"] = str(cache_file)
        return env

    def test_hook_subprocess_offline_and_opt_out(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            lean_file = tmp_dir / "OfflineProof.lean"
            lean_file.write_text(
                "theorem t : True := by\n  dsimp [wpMirExecSym]\n  trivial\n", encoding="utf-8"
            )
            payload = {
                "result": "Edited OfflineProof.lean",
                **jetski_edit(lean_file, "  trivial\n", "  dsimp [wpMirExecSym]\n  trivial\n"),
            }
            env = self.hook_env(tmp_dir / "hook-cache.json")

            # No lakefile -> no LSP feedback, but the proof-health check still runs.
            out = self.run_hook(payload, env)
            self.assertIn("[Anneal Proof Health]", out["overwriteResult"])
            self.assertTrue(out["overwriteResult"].startswith("Edited OfflineProof.lean"))
            self.assertIn("dsimp_forbidden_sym", out["hookSpecificOutput"]["additionalContext"])
            self.assertEqual(out["hookSpecificOutput"]["hookEventName"], "PostToolUse")

            # Second run with unchanged file -> delta is 0 -> `{}`
            self.assertEqual(self.run_hook({"toolCall": {"args": {"Path": str(lean_file)}}}, env), {})

            # Opt-out via ANNEAL_DISABLE_LSP_HOOK=1 -> `{}`
            self.assertEqual(self.run_hook(payload, dict(env, ANNEAL_DISABLE_LSP_HOOK="1")), {})

    def test_hook_fails_open_on_bad_input(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            env = self.hook_env(tmp_dir / "cache.json")
            no_lsp_dir = tmp_dir / "no_lsp"
            no_lsp_dir.mkdir()
            opted_out = no_lsp_dir / "Skip.lean"
            opted_out.write_text("theorem t : True := by\n  dsimp [wpMirExecSym]\n", encoding="utf-8")
            text_file = tmp_dir / "notes.txt"
            text_file.write_text("dsimp [wpMirExecSym]\n", encoding="utf-8")
            for payload in (
                "",
                "{ not json",
                "[1, 2, 3]",
                {"error": "tool failed", **jetski_edit(opted_out, "a", "b")},
                {"toolCall": {"args": {"Path": str(tmp_dir / "Missing.lean")}}},
                {"toolCall": {"args": {"Path": str(text_file)}}},
                jetski_edit(opted_out, "  trivial\n", "  dsimp [wpMirExecSym]\n"),
            ):
                self.assertEqual(self.run_hook(payload, env), {}, payload)

    def test_hook_subprocess_mocked_combined_lsp_and_proof_health(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            lean_file = tmp_dir / "CombinedProof.lean"
            lean_file.write_text(
                "set_option trace.profiler.threshold 10\ntheorem t : True := by\n  trivial\n",
                encoding="utf-8",
            )
            payload = {
                "result": "Updated CombinedProof.lean",
                "tool_input": {
                    "file_path": str(lean_file),
                    "old_string": "theorem t : True := by\n  trivial\n",
                    "new_string": (
                        "set_option trace.profiler.threshold 10\n"
                        "theorem t : True := by\n  trivial\n"
                    ),
                },
            }
            runner = (
                "import runpy, sys, types\n"
                "m = types.ModuleType('anneal_lsp_daemon')\n"
                "m.resolve_lake_root = lambda p: '/fake/lake'\n"
                "m.daemon_rpc = lambda *a, **k: {\n"
                "    'ok': True, 'result': {'feedback': '[Lean LSP] L2: unsolved goals'}}\n"
                "sys.modules['anneal_lsp_daemon'] = m\n"
                f"runpy.run_path({str(HOOK_PATH)!r}, run_name='__main__')\n"
            )
            out = self.run_hook(payload, self.hook_env(tmp_dir / "combined-cache.json"), runner)
            for field in (out["overwriteResult"], out["hookSpecificOutput"]["additionalContext"]):
                self.assertIn("[Lean LSP] L2: unsolved goals", field)
                self.assertIn("[Anneal Proof Health]", field)
                self.assertIn("low_profiler_threshold", field)

    def test_hook_reports_proof_health_when_daemon_raises(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            lean_file = tmp_dir / "Broken.lean"
            text = "theorem t : True := by\n  unfold bitwiseAndBits\n  trivial\n"
            lean_file.write_text(text, encoding="utf-8")
            runner = (
                "import runpy, sys, types\n"
                "m = types.ModuleType('anneal_lsp_daemon')\n"
                "def boom(*a, **k):\n"
                "    raise RuntimeError('daemon offline')\n"
                "m.resolve_lake_root = boom\n"
                "m.daemon_rpc = boom\n"
                "sys.modules['anneal_lsp_daemon'] = m\n"
                f"runpy.run_path({str(HOOK_PATH)!r}, run_name='__main__')\n"
            )
            created = {"toolCall": {"args": {"Path": str(lean_file), "Content": text}}}
            out = self.run_hook(created, self.hook_env(tmp_dir / "cache.json"), runner)
            context = out["hookSpecificOutput"]["additionalContext"]
            self.assertIn("`raw_bitwise_unfold` (+1 at L2)", context)
            self.assertNotIn("[Lean LSP]", context)


if __name__ == "__main__":
    unittest.main()
