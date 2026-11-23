#!/usr/bin/env python3
"""Unit and integration test suite for `proof_health.py` and `post_tool_use.py`."""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
import unittest
from unittest.mock import patch

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


def cpu_ms(fn) -> float:
    """Milliseconds of this process's CPU time (user + system) spent in one `fn()`
    call. Unlike wall-clock time it excludes time spent runnable but descheduled, so
    other processes saturating the host's cores cannot inflate it (a 2x oversubscribed
    8-core host made wall-clock scans of the dogfood files read 3-6x slower)."""
    t0 = time.process_time()
    fn()
    return (time.process_time() - t0) * 1000.0


def best_of_ms(fn, runs: int = 15, budget_ms: float = 5.0, rounds: int = 3) -> float:
    """Best CPU time (`cpu_ms`) of `fn` over up to `rounds` rounds of `runs` calls
    (after one warm-up call), stopping early once the best is under `budget_ms`.
    Rounds are spaced 0.25 s apart so a transient cache-thrashing spike on a shared
    machine does not decide the result; a genuine slowdown still fails the budget."""
    fn()
    best = float("inf")
    for round_idx in range(rounds):
        if round_idx:
            time.sleep(0.25)
        for _ in range(runs):
            best = min(best, cpu_ms(fn))
        if best < budget_ms:
            break
    return best


def target_replacement_edit(path: Path, target: str, replacement: str) -> dict:
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
    # Also the `scan_lean_text` result memo and the shared auditor's memo tables.
    proof_health.clear_in_process_caches()


def drop_scan_memo() -> None:
    """Forget every memo of scanned texts -- the `scan_lean_file` text memo, the
    `_scan_text_meta` lexing index, the `scan_lean_text` result memo, the incremental
    splicing baselines and the shared auditor's per-theorem tables -- but keep sibling
    caches warm: the state of every fresh PostToolUse hook process (or of a just-edited
    file), whose text was never scanned before."""
    prefixes = (proof_health._SCAN_META_KEY_PREFIX, proof_health._SCAN_FILE_KEY_PREFIX)
    for key in [k for k in proof_health._FILE_TEXTS_CACHE if k.startswith(prefixes)]:
        del proof_health._FILE_TEXTS_CACHE[key]
    for memo in (
        proof_health._SCAN_RESULT_CACHE,
        proof_health._LAST_LEAN_SCAN,
        proof_health._LAST_LEAN_AUDIT,
        proof_health._THM_AUDIT_CACHE,
        proof_health._META_CACHE,
        proof_health._NORM_CACHE,
    ):
        memo.clear()


def uncached(fn):
    """`fn` wrapped to run without the scan memo (see `drop_scan_memo`), so timing
    loops measure real lexing and scanning instead of repeated memo hits."""

    def run():
        drop_scan_memo()
        return fn()

    return run


def _no_audit_findings(*_args, **_kwargs) -> list:
    return []


def uncached_rules_1_to_5(fn):
    """`uncached(fn)` with rules 6 and 7 (the shared waiver-pin & 3-axis auditor) stubbed
    out: the decoding, lexing, rules 1-5 and sibling work that the rules 1-5 timing budgets
    were calibrated for (the auditor's cold cost is budgeted by
    `test_sub_5ms_runtime_benchmark`). Memos are dropped again afterwards, so no result
    computed without rules 6 and 7 can ever be served to a later scan."""

    def run():
        drop_scan_memo()
        try:
            with patch.object(
                proof_health, "_lean_waiver_and_vacuity_findings", _no_audit_findings
            ):
                return fn()
        finally:
            drop_scan_memo()

    return run


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

    def test_escaped_quote_character_literal(self) -> None:
        # `'\"'` is a character literal (escaped double quote): the backslash, not a
        # quote, precedes the `"`, which must not open a string swallowing lines 2-3.
        src = (
            "def c : Char := '\\\"'\n"
            "theorem t : True := by\n"
            "  simp [wpMirExecSym]\n"
            'def s := "x"\n'
        )
        self.assertEqual(src.splitlines()[0], "def c : Char := '\\\"'")
        self.assertEqual(scan(src), [(R1, 3, "wpMirExecSym")])
        kept = proof_health.strip_lean_comments_and_strings(src, keep_strings=True)
        self.assertEqual(kept, src)

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

    def test_guillemet_char_literal_and_adjacent_escaped_single_quote(self) -> None:
        # `'«'` is a Char literal, not an opening guillemet: a `»` inside a trailing
        # `--` comment must never pair with it and expose the rest of the comment.
        # Likewise `f '\''"'"` has `'\''` followed by string `"'"`, not char `'"'`.
        src = (
            "def openGui : Char := '«' -- note: » closes guillemet; do not dsimp [wpMirExecSym]\n"
            "def adj := f '\\''\"'\" -- closed string, then comment dsimp [wpMirExecSym]\n"
            "theorem after_adj : True := by dsimp [wpMirExecSym]\n"
        )
        self.assertEqual(scan(src), [(R1, 3, "wpMirExecSym")])
        kept = proof_health.strip_lean_comments_and_strings(src, keep_strings=True)
        self.assertIn("'«'", kept)
        self.assertNotIn("closes guillemet", kept)


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

    def test_rule4_prefixed_and_oversized_literals(self) -> None:
        # Lean `numLit` values may be `0x`/`0b`/`0o` prefixed or zero-padded, and a
        # literal past Python's 4300-digit `int()` limit must not crash the scan.
        src = (
            "set_option trace.profiler.threshold 0x10\n"
            "set_option trace.profiler.threshold 0x40\n"
            "set_option trace.profiler.threshold 0b110001\n"
            "set_option trace.profiler.threshold 0o62\n"
            "set_option trace.profiler.threshold 049\n"
            "set_option trace.profiler.threshold " + "0" * 5000 + "1\n"
            "set_option trace.profiler.threshold " + "9" * 5000 + "\n"
            "set_option trace.profiler.threshold 0xg\n"
            "set_option trace.profiler.threshold 0b1000000\n"
            "set_option trace.profiler.threshold 0o61\n"
            "set_option trace.profiler.threshold 49.5\n"
            "set_option trace.profiler.threshold 1.foo\n"
        )
        self.assertEqual(
            scan(src),
            [
                (R4, 1, "trace.profiler.threshold=16"),
                (R4, 3, "trace.profiler.threshold=49"),
                (R4, 5, "trace.profiler.threshold=49"),
                (R4, 6, "trace.profiler.threshold=1"),
                (R4, 10, "trace.profiler.threshold=49"),
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

    def test_rule1_and_rule2_parenthesized_propositions_tuples_and_indexing_not_flagged(self) -> None:
        # Parenthesized equality propositions, tuples, and block/field indexing do not
        # unfold the symbol, whereas `(@sym : T)`, `((sym))`, `↓ @sym`, and `sym.eq_def x` do.
        src = (
            "theorem entry_tails : True := by\n"
            "  simp [(Trusted.Sequence.length bs = 4)]\n"
            "  simp [Trusted.Sequence.length bs = 4]\n"
            "  simp [(wpMirExecSym, foo)]\n"
            "  simp [Mir.Crate.Item.body[0]!]\n"
            "  simp [(Mir.Crate.Item.body)[0]!]\n"
            "  simp [(Mir.Crate.Item.body).length]\n"
            "  simp [(bitwiseAndBits.eq_def, foo)]\n"
            "  simp [(@wpMirExecSym : Nat → Nat)]\n"
            "  simp [((Trusted.Sequence.length))]\n"
            "  simp [↓ @wpMirExecSym, @↓Trusted.Sequence.length]\n"
            "  simp [wpMirExecSym.eq_def cfg]\n"
        )
        self.assertEqual(
            scan(src),
            [
                (R1, 9, "wpMirExecSym"),
                (R1, 10, "Trusted.Sequence.length"),
                (R1, 11, "Trusted.Sequence.length"),
                (R1, 11, "wpMirExecSym"),
                (R1, 12, "wpMirExecSym"),
            ],
        )

    def test_rule5_guillemet_binders_and_large_def_table_past_budget(self) -> None:
        # 1. Guillemet-quoted binder variables (`«x-1»`, `«z».length`) alpha-rename
        # identically to standard identifiers, while `«a.b»` is not split at `.`.
        src_gui = (
            "private theorem g1 («x-1» : Nat) : «x-1» + 1 = 1 + «x-1» := by omega\n"
            "private theorem g2 (y : Nat) : y + 1 = 1 + y := by omega\n"
            "private def gd1 («z» : List Nat) : Nat := «z».length + 1\n"
            "private def gd2 (w : List Nat) : Nat := w.length + 1\n"
            "private def dotA («a.b» : Nat) : Nat := «a.b»\n"
            "private def dotB (x : Nat) : Nat := x.b\n"
        )
        self.assertEqual(
            scan(src_gui),
            [(R5, 2, "g2"), (R5, 4, "gd2")],
        )

        # 2. Large binderless `private def` table (>250 KB, identical punctuation counts)
        # must still detect a duplicate at the very end without silent 64 KB truncation.
        blocks: list[str] = []
        for i in range(150):
            stmts = "\n".join(
                f"    stmt{j} := .assign (.local {j}) (.use (.copy (.local {i + j}))),"
                for j in range(30)
            )
            blocks.append(
                f"private def body{i} : Body :=\n  {{ locals := #[x],\n{stmts}\n    blocks := #[] }}\n"
            )
        dup_line = "".join(blocks).count("\n") + 1
        blocks.append(blocks[-1].replace("private def body149", "private def body149Copy"))
        large_src = "".join(blocks)
        self.assertGreater(len(large_src), 250_000)
        self.assertEqual(scan(large_src), [(R5, dup_line, "body149Copy")])

        # 3. Tight `_BODY_COMPARE_BUDGET` on binder-bearing defs must never wipe `pending3`
        # once `target` already collided on `(sig, key1, key2)`.
        old_budget = proof_health._BODY_COMPARE_BUDGET
        proof_health._BODY_COMPARE_BUDGET = 40
        try:
            tight_src = (
                "private def b1 (x : Nat) : Nat := x + 100000000000000000000000000000\n"
                "private def b2 (y : Nat) : Nat := y + 100000000000000000000000000000\n"
            )
            # Budget allows `key2(b2)` (leaves >0? test with budget=90 so `key2(b2)`, `key2(b1)`
            # and `exact_key(b2)` exhaust budget right before `exact_key(b1)` in `pending3`):
            proof_health._BODY_COMPARE_BUDGET = 90
            self.assertEqual(scan(tight_src), [(R5, 2, "b2")])
        finally:
            proof_health._BODY_COMPARE_BUDGET = old_budget

    def test_dotted_guillemet_names_comma_ascription_and_unfold_config(self) -> None:
        # Dotted guillemet decl names (`Foo.«bar»`, `«Ns».dup`), guillemet-escaped
        # Rust keyword segments in `Mir.Crate.«match».body`, comma-containing `∀` type
        # ascriptions `(sym : ∀ {T}, ...)`, and `unfold (config := ...) / +opt`.
        src = (
            "private theorem Foo.«bar» : True := trivial\n"
            "private theorem Foo.«baz» : False → True := fun h => False.elim h\n"
            "private theorem «Ns».dup : True ∧ True := ⟨trivial, trivial⟩\n"
            "private theorem «Ns».dup : Nat = Nat := rfl\n"
            "theorem mir_and_ascr : True := by\n"
            "  simp [Mir.Crate.«match».body]\n"
            "  unfold (config := { zeta := false }) Mir.«from».item.body\n"
            "  unfold +zeta bitwiseAndBits\n"
            "  simp [(Trusted.Sequence.length : ∀ {T : Type}, List T → Nat)]\n"
        )
        self.assertEqual(
            scan(src),
            [
                (R5, 4, "«Ns».dup"),
                (R2, 6, "Mir.Crate.«match».body"),
                (R2, 7, "Mir.«from».item.body"),
                (R3, 8, "bitwiseAndBits"),
                (R1, 9, "Trusted.Sequence.length"),
            ],
        )


class TestDeltaOnlyPostEditCheck(unittest.TestCase):
    def test_delta_only_target_replacement_and_claude_payloads(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            cache_file = tmp_dir / "cache.json"
            lean_file = tmp_dir / "Proof.lean"

            # 1. Clean edit -> no warning
            clean_v1 = "theorem t : True := by\n  dsimp only [foo]\n  trivial\n"
            lean_file.write_text(clean_v1, encoding="utf-8")
            fb1 = proof_health.check_post_edit_proof_health(
                lean_file,
                target_replacement_edit(lean_file, "  trivial\n", "  dsimp only [foo]\n  trivial\n"),
                cache_path=cache_file,
            )
            self.assertEqual(fb1, "")

            # 2. Introduce `dsimp [wpMirExecSym]` via `Target`/`Replacement` -> warning (+1)
            bad_v2 = "theorem t : True := by\n  dsimp only [foo, wpMirExecSym]\n  trivial\n"
            lean_file.write_text(bad_v2, encoding="utf-8")
            fb2 = proof_health.check_post_edit_proof_health(
                lean_file,
                target_replacement_edit(lean_file, "  dsimp only [foo]\n", "  dsimp only [foo, wpMirExecSym]\n"),
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
            deletion = target_replacement_edit(lean_file, "  -- obsolete note\n", "")
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
            # `write_file` without `Overwrite`/`Append` only succeeds on a new file.
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
                target_replacement_edit(lean_file, "theorem t : True := by\n", "theorem t : True := by\n" + body),
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
                    target_replacement_edit(lean_file, "  trivial\n", "  skip\n  trivial\n"),
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
                    target_replacement_edit(
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
                    target_replacement_edit(target, "by omega\n", "by omega\n-- note\n"),
                    cache_path=cache_file,
                )
                self.assertEqual(fb, "")
                self.assertEqual(len(calls), 1)
            finally:
                proof_health.scan_lean_text = original_scan

    def test_persisted_body_keys_spare_sibling_reads(self) -> None:
        # Sibling definition bodies are compared through body keys stored in the
        # sibling index; the sibling text is read again only when keys match.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            cache_file = tmp_dir / "cache.json"
            sibling = tmp_dir / "Sib.lean"
            sibling.write_text(
                'private def tyA : Ty := { kind := .adt "A" [], layoutIdx := 0 }\n'
                'private def tyB : Ty := { kind := .adt "B" [], layoutIdx := 0 }\n',
                encoding="utf-8",
            )
            settle(sibling)
            target = tmp_dir / "Tgt.lean"
            target.write_text(
                'private def tyC : Ty := { kind := .adt "C" [], layoutIdx := 0 }\n',
                encoding="utf-8",
            )
            clear_in_process_caches()
            proof_health.check_post_edit_proof_health(target, None, cache_path=cache_file)
            index = json.loads(
                proof_health.sibling_index_path(cache_file, tmp_dir).read_text(encoding="utf-8")
            )
            records = index[str(sibling)][3]
            self.assertTrue(all(rec[8] is not None for rec in records))

            reads: list[str] = []
            original_texts = proof_health._file_texts

            def counting_texts(path_str):
                reads.append(path_str)
                return original_texts(path_str)

            proof_health._file_texts = counting_texts
            try:
                clear_in_process_caches()
                self.assertEqual(
                    proof_health.check_post_edit_proof_health(target, None, cache_path=cache_file),
                    "",
                )
                self.assertEqual(reads, [])

                clear_in_process_caches()
                target.write_text(
                    'private def tyC : Ty := { kind := .adt "C" [], layoutIdx := 0 }\n'
                    'private def tyA2 : Ty := { kind := .adt "A" [], layoutIdx := 0 }\n',
                    encoding="utf-8",
                )
                fb = proof_health.check_post_edit_proof_health(
                    target, {"toolCall": {"args": {"Path": str(target)}}}, cache_path=cache_file
                )
                self.assertIn("`duplicate_private_lemma` (+1 at L2)", fb)
                self.assertIn("same normalized signature and body as `private def tyA`", fb)
                self.assertEqual(reads, [str(sibling)])
            finally:
                proof_health._file_texts = original_texts

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

            # 2. Uncached `edit_file` carrying `Made 1 replacement ... starting at line 5`:
            # exact line L5 reconstructed and attributed (+1 at L5).
            target_file = tmp_dir / "AmbigTarget.lean"
            target_file.write_text(after, encoding="utf-8")
            target_payload = {
                "result": f"Made 1 replacement in {target_file} starting at line 5 (+1/-1 lines).",
                **target_replacement_edit(target_file, "  skip\n", "  dsimp [wpMirExecSym]\n"),
            }
            res_j = proof_health.evaluate_post_edit_proof_health(
                target_file, target_payload, cache_path=tmp_dir / "c_target.json"
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
                tgt, target_replacement_edit(tgt, "sorry\n", "sorry\n-- touch\n"), cache_path=scache
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

    def test_same_tick_same_size_sibling_edit_invalidates_count_cache(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            cache_file = tmp_dir / "cache.json"
            sib = tmp_dir / "Sib.lean"
            tgt = tmp_dir / "Tgt.lean"

            # 1. Same-tick, same-size theorem header rewrite (`n = 0` -> `n = 1`)
            v_sib1 = "private theorem h (n : Nat) : n = 0 := sorry\n"
            v_sib2 = "private theorem h (n : Nat) : n = 1 := sorry\n"
            self.assertEqual(len(v_sib1), len(v_sib2))
            sib.write_text(v_sib1, encoding="utf-8")
            st0 = sib.stat()
            tgt_v1 = "private theorem g (m : Nat) : m = 1 := sorry\n"
            tgt.write_text(tgt_v1, encoding="utf-8")
            clear_in_process_caches()
            self.assertEqual(
                proof_health.check_post_edit_proof_health(tgt, None, cache_path=cache_file), ""
            )

            # Overwrite `Sib.lean` and pin exact `(atime_ns, mtime_ns)` to simulate one tick.
            sib.write_text(v_sib2, encoding="utf-8")
            os.utime(sib, ns=(st0.st_atime_ns, st0.st_mtime_ns))
            self.assertEqual((sib.stat().st_mtime_ns, sib.stat().st_size), (st0.st_mtime_ns, st0.st_size))

            tgt_v2 = tgt_v1 + "-- harmless comment\n"
            tgt.write_text(tgt_v2, encoding="utf-8")
            # Both in-process and cross-process checks must see the updated sibling CRC
            # and re-scan `tgt_v1` (delta 1 - 1 = 0 -> ""), never claiming a false +1.
            self.assertEqual(
                proof_health.check_post_edit_proof_health(
                    tgt, target_replacement_edit(tgt, "sorry\n", "sorry\n-- harmless comment\n"), cache_path=cache_file
                ),
                "",
            )

            # 2. Same-tick, same-size `private def` body rewrite (`:= 0` -> `:= 1`)
            sib_d1 = "private def c : Nat := 0\n"
            sib_d2 = "private def c : Nat := 1\n"
            sib.write_text(sib_d1, encoding="utf-8")
            st1 = sib.stat()
            tgt_d1 = "private def d : Nat := 1\n"
            tgt.write_text(tgt_d1, encoding="utf-8")
            cache2 = tmp_dir / "cache2.json"
            clear_in_process_caches()
            self.assertEqual(
                proof_health.check_post_edit_proof_health(tgt, None, cache_path=cache2), ""
            )
            sib.write_text(sib_d2, encoding="utf-8")
            os.utime(sib, ns=(st1.st_atime_ns, st1.st_mtime_ns))
            clear_in_process_caches()
            tgt.write_text(tgt_d1 + "-- touch\n", encoding="utf-8")
            self.assertEqual(
                proof_health.check_post_edit_proof_health(
                    tgt, target_replacement_edit(tgt, ":= 1\n", ":= 1\n-- touch\n"), cache_path=cache2
                ),
                "",
            )

    def test_insertion_above_identical_line_and_mixed_delete_insert_multiedit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            # 1. Inserting an identical `new_string` at L2 above a pre-existing L5 occurrence
            # must attribute the new finding to L2, not L5.
            f1 = tmp_dir / "Above.lean"
            before = (
                "theorem t1 : True := by\n"
                "  skip\n"
                "  trivial\n"
                "theorem t2 : True := by\n"
                "  dsimp [wpMirExecSym]\n"
                "  trivial\n"
            )
            after = (
                "theorem t1 : True := by\n"
                "  dsimp [wpMirExecSym]\n"
                "  trivial\n"
                "theorem t2 : True := by\n"
                "  dsimp [wpMirExecSym]\n"
                "  trivial\n"
            )
            f1.write_text(after, encoding="utf-8")
            payload = {
                "tool_input": {
                    "file_path": str(f1),
                    "old_string": "  skip\n",
                    "new_string": "  dsimp [wpMirExecSym]\n",
                },
                "tool_response": {"originalFile": before},
            }
            res = proof_health.evaluate_post_edit_proof_health(
                f1, payload, cache_path=tmp_dir / "c1.json"
            )
            self.assertEqual(res["deltas"][R1], 1)
            self.assertEqual([f.line for f in res["new_findings"]], [2])
            self.assertIn("(+1 at L2)", res["feedback"])

            # 2. Uncached `MultiEdit` combining a deletion (`new_string == ""`) with an
            # anti-pattern insertion must still flag the new anti-pattern (+1).
            f2 = tmp_dir / "MixedMulti.lean"
            f2.write_text(
                "theorem m : True := by\n  dsimp [wpMirExecSym]\n  trivial\n",
                encoding="utf-8",
            )
            mixed_payload = {
                "tool_input": {
                    "file_path": str(f2),
                    "edits": [
                        {"old_string": "-- obsolete comment\n", "new_string": ""},
                        {
                            "old_string": "  trivial\n",
                            "new_string": "  dsimp [wpMirExecSym]\n  trivial\n",
                        },
                    ],
                }
            }
            res2 = proof_health.evaluate_post_edit_proof_health(
                f2, mixed_payload, cache_path=tmp_dir / "c2.json"
            )
            self.assertEqual(res2["deltas"][R1], 1)
            self.assertEqual([f.line for f in res2["new_findings"]], [2])

    def test_multi_replacement_starting_at_line_and_sibling_body_budget(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            # 1. Pre-existing `dsimp [wpMirExecSym]` at L2, plus 2 replacements starting
            # at line 5 (L5 and L8): exact pre-edit text is recovered and [5, 8] reported.
            lean_file = tmp_dir / "MultiLineHint.lean"
            after = (
                "theorem t1 : True := by\n"
                "  dsimp [wpMirExecSym]\n"
                "  trivial\n"
                "theorem t2 : True := by\n"
                "  dsimp [wpMirExecSym]\n"
                "  trivial\n"
                "theorem t3 : True := by\n"
                "  dsimp [wpMirExecSym]\n"
                "  trivial\n"
            )
            lean_file.write_text(after, encoding="utf-8")
            payload = {
                "result": f"Made 2 replacements in {lean_file} starting at line 5 (+2/-2 lines).",
                **target_replacement_edit(lean_file, "  skip\n", "  dsimp [wpMirExecSym]\n"),
            }
            res = proof_health.evaluate_post_edit_proof_health(
                lean_file, payload, cache_path=tmp_dir / "c_multi.json"
            )
            self.assertEqual(res["deltas"][R1], 2)
            self.assertEqual([f.line for f in res["new_findings"]], [5, 8])

            # 2. Sibling body-key budget cap leaves over-budget binder-bearing defs lazy
            # without dropping duplicate detection, and malformed `fp`/`bkeys` entries reload.
            sib = tmp_dir / "SibBudget.lean"
            sib.write_text(
                "private def sb1 (x : Nat) : Nat := x + 10000000000000000000\n"
                "private def sb2 (x : Nat) : Nat := x + 20000000000000000000\n",
                encoding="utf-8",
            )
            settle(sib)
            tgt = tmp_dir / "TgtBudget.lean"
            tgt.write_text(
                "private def tb2 (y : Nat) : Nat := y + 20000000000000000000\n",
                encoding="utf-8",
            )
            old_budget = proof_health._BODY_COMPARE_BUDGET
            proof_health._BODY_COMPARE_BUDGET = 15
            try:
                clear_in_process_caches()
                bcache = tmp_dir / "bcache.json"
                # First lexes sibling under tight budget (`sb2.body_keys` stays None);
                # restore budget for target check to confirm lazy fallback still catches `sb2`.
                proof_health._collect_sibling_private_decls(tgt, persisted={})
                self.assertIsNone(proof_health._SIBLING_PRIVATE_CACHE[str(sib)][3][1].body_keys)
                proof_health._BODY_COMPARE_BUDGET = old_budget
                fb = proof_health.check_post_edit_proof_health(
                    tgt, {"Path": str(tgt), "Content": tgt.read_text()}, cache_path=bcache
                )
                self.assertIn("same normalized signature and body as `private def sb2`", fb)
            finally:
                proof_health._BODY_COMPARE_BUDGET = old_budget

    def test_oversized_replacement_result_numbers_are_not_hints(self) -> None:
        # A replacement count or start line too long to be real (past Python's
        # 4300-digit `int()` limit) is ignored instead of raising.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            lean_file = tmp_dir / "HugeHint.lean"
            lean_file.write_text(
                "theorem t : True := by\n  dsimp [wpMirExecSym]\n  trivial\n", encoding="utf-8"
            )
            results = (
                "Made " + "2" * 5000 + " replacements starting at line 2.",
                "Made 1 replacement starting at line " + "2" * 5000 + ".",
            )
            for idx, result in enumerate(results):
                payload = {
                    "result": result,
                    **target_replacement_edit(lean_file, "  skip\n", "  dsimp [wpMirExecSym]\n"),
                }
                res = proof_health.evaluate_post_edit_proof_health(
                    lean_file, payload, cache_path=tmp_dir / f"c{idx}.json"
                )
                self.assertEqual(res["deltas"][R1], 1)
                self.assertEqual([f.line for f in res["new_findings"]], [2])

    def test_negative_cached_counts_nul_paths_and_zero_hints_never_crash(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            lean_file = tmp_dir / "NegCache.lean"
            lean_file.write_text("private theorem clean : True := trivial\n", encoding="utf-8")
            cache_file = tmp_dir / "cache.json"
            cache_file.write_text(
                json.dumps(
                    {
                        str(lean_file.resolve()): {
                            "_ver": proof_health.CACHE_FORMAT_VERSION,
                            R1: -5,
                        }
                    }
                ),
                encoding="utf-8",
            )
            # Negative cached count clamps to 0 instead of raising `IndexError` on `shown[0]`.
            res = proof_health.evaluate_post_edit_proof_health(
                lean_file, {"Path": str(lean_file)}, cache_path=cache_file
            )
            self.assertEqual(res["deltas"][R1], 0)
            self.assertEqual(res["feedback"], "")

            # Embedded NULs in sibling-index keys, `cache_path`, or `target_file` never raise `ValueError`.
            idx_file = proof_health.sibling_index_path(cache_file, tmp_dir)
            idx_file.write_text(json.dumps({"bad\x00sib": [1, 2, 3, []]}), encoding="utf-8")
            self.assertEqual(
                proof_health.check_post_edit_proof_health(lean_file, None, cache_path=cache_file),
                "",
            )
            self.assertEqual(
                proof_health.check_post_edit_proof_health(
                    lean_file, None, cache_path="bad\x00cache.json"
                ),
                "",
            )
            self.assertEqual(
                proof_health.check_post_edit_proof_health(
                    "bad\x00.lean", None, after_text="theorem t : True := trivial\n"
                ),
                "",
            )

            # Zero replacement counts / zero line hints are ignored as invalid 1-based hints.
            zfile = tmp_dir / "ZeroHint.lean"
            zfile.write_text(
                "theorem a : True := trivial\n"
                "theorem b : True := by\n"
                "  dsimp [wpMirExecSym]\n",
                encoding="utf-8",
            )
            for bad_hint in (
                "Made 0 replacements starting at line 0.",
                "Made 1 replacement starting at line 0.",
            ):
                zres = proof_health.evaluate_post_edit_proof_health(
                    zfile,
                    {
                        "result": bad_hint,
                        **target_replacement_edit(zfile, "  skip\n", "  dsimp [wpMirExecSym]\n"),
                    },
                    cache_path=tmp_dir / f"z_{len(bad_hint)}.json",
                )
                self.assertEqual([f.line for f in zres["new_findings"]], [3])


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
        # Same proportional large-file budget as the dogfood files (2 ms per 1,000
        # lines, at least 5 ms, capped at 15 ms): a fixed 5 ms left under 1.5x headroom
        # for a real (unmemoized) 6,000-line scan, which SMT contention alone exceeds.
        # Timed without rules 6/7 (their 1,000 theorems are the auditor's cold
        # throughput, budgeted by `test_sub_5ms_runtime_benchmark`).
        line_count = text.count("\n") + 1
        budget_ms = min(15.0, max(5.0, 2.0 * (line_count / 1000.0)))
        elapsed_ms = best_of_ms(
            uncached_rules_1_to_5(lambda: proof_health.scan_lean_text(text, scan_siblings=False)),
            budget_ms=budget_ms,
        )
        self.assertLess(
            elapsed_ms,
            budget_ms,
            f"{line_count}-line synthetic scan took {elapsed_ms:.2f} ms (budget {budget_ms:.2f} ms)",
        )

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
                uncached(lambda: proof_health.scan_lean_text(text, scan_siblings=False)), budget_ms=15.0
            )
            self.assertLess(elapsed_ms, 15.0, f"{label} definitions took {elapsed_ms:.2f} ms")

    def test_dogfood_episode1_files_under_5ms(self) -> None:
        bit_validity = REPO_ROOT / "theory" / "Anneal" / "BitValidity.lean"
        mir_cast = REPO_ROOT / "theory" / "Anneal" / "Mir" / "Cast.lean"
        adt_and_control = REPO_ROOT / "theory" / "Anneal" / "Mir" / "AdtAndControl.lean"
        sym_reflect = REPO_ROOT / "theory" / "Anneal" / "Rustc" / "V2026_06_01" / "SymReflect.lean"

        def min_of_3_after_warmup(fn) -> float:
            # Scan latency as on-CPU time (`cpu_ms`): host load cannot flake it.
            fn()
            return min(cpu_ms(fn) for _ in range(3))

        for path in (bit_validity, mir_cast, adt_and_control, sym_reflect):
            self.assertTrue(path.is_file(), f"Missing {path}")
            line_count = path.read_text(encoding="utf-8", errors="replace").count("\n") + 1
            scaled_budget_ms = min(15.0, max(5.0, 2.0 * (line_count / 1000.0)))

            def warm(p: Path = path) -> object:
                return proof_health.scan_lean_file(p, scan_siblings=True)

            # Warm rescans of an unchanged file (the long-lived LSP daemon) hit the
            # `(mtime_ns, size)`-validated text memo and the `scan_lean_text` result memo.
            warm_ms = min_of_3_after_warmup(warm)
            if warm_ms >= scaled_budget_ms:
                warm_ms = best_of_ms(warm, runs=3, budget_ms=scaled_budget_ms)
            self.assertLess(
                warm_ms,
                scaled_budget_ms,
                f"{path.name} ({line_count} lines) warm scan took {warm_ms:.2f} ms "
                f"(budget {scaled_budget_ms:.2f} ms)",
            )
            if path in (bit_validity, mir_cast):
                self.assertLess(warm_ms, 5.0, f"{path.name} warm scan took {warm_ms:.2f} ms")

            # An edited file (and every fresh PostToolUse hook process) never hits the
            # memo: it pays decode + comment/string stripping + every scan pass. Guard
            # that real cost against algorithmic regressions (per-line regexes,
            # quadratic passes) with a ~1 ms per 1,000 lines budget that also scales with
            # the stripping pass timed just before it (3-5.5x of a scan today), so host
            # load inflates budget and measurement alike instead of flaking the test.
            # This budget covers rules 1-5; rules 6/7 are bounded relative to it below.
            text = path.read_bytes().decode("utf-8", errors="replace")
            strip_ms = min_of_3_after_warmup(
                lambda t=text: proof_health.strip_lean_comments_and_strings(t)
            )
            uncached_budget_ms = max(8.0, 1.25 * (line_count / 1000.0), 6.0 * strip_ms)
            cold = uncached_rules_1_to_5(warm)
            uncached_ms = min_of_3_after_warmup(cold)
            if uncached_ms >= uncached_budget_ms:
                uncached_ms = best_of_ms(cold, runs=3, budget_ms=uncached_budget_ms)
            self.assertLess(
                uncached_ms,
                uncached_budget_ms,
                f"{path.name} ({line_count} lines) uncached scan took {uncached_ms:.2f} ms "
                f"(budget {uncached_budget_ms:.2f} ms, strip {strip_ms:.2f} ms)",
            )

            # Rules 6/7 reuse that scan's single lexing pass (`_preparsed`), so a cold
            # rules 1-7 scan costs no more than the rules 1-5 scan plus a standalone cold
            # audit of the same text (which even lexes it again): a second lexing or
            # audit pass in the combined pipeline fails this bound.
            def audit_alone(t: str = text, p: Path = path) -> object:
                drop_scan_memo()
                return proof_health._lean_waiver_and_vacuity_findings(t, file_path=p)

            full = uncached(warm)
            full_ms, rules_ms, audit_ms = (
                min_of_3_after_warmup(full),
                min_of_3_after_warmup(cold),
                min_of_3_after_warmup(audit_alone),
            )
            if full_ms >= 1.25 * (rules_ms + audit_ms):  # re-measure once against host noise
                full_ms = min(full_ms, min_of_3_after_warmup(full))
                rules_ms = min(rules_ms, min_of_3_after_warmup(cold))
                audit_ms = min(audit_ms, min_of_3_after_warmup(audit_alone))
            self.assertLess(
                full_ms,
                1.25 * (rules_ms + audit_ms),
                f"{path.name} cold rules 1-7 scan took {full_ms:.2f} ms vs rules 1-5 "
                f"{rules_ms:.2f} ms + standalone audit {audit_ms:.2f} ms",
            )

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

    def test_prefilter_soundness_on_multiline_qualified_and_large_files(self) -> None:
        # Verify module-level regexes are pre-compiled at import time.
        for attr in (
            "_FORBIDDEN_SIMP_SYM_RE",
            "_MIR_BODY_RE",
            "_RAW_BITWISE_RE",
            "_PROFILER_THRESHOLD_RE",
            "_PRIVATE_LIT_RE",
            "_DECL_BOUNDARY_RE",
            "_EQN_ALT_LINE_RE",
            "_MATCH_OR_FUN_RE",
            "_HDR_TOKEN_RE",
            "_REPL_RESULT_RE",
            "_CREATED_COMPLETED_RE",
        ):
            self.assertIsNotNone(getattr(proof_health, attr), f"{attr} must be pre-compiled")

        # Large (>8192 char) file exercising every pre-filter edge case:
        # 1. Qualified `Anneal.Mir.Crate.Item.body` inside multiline `dsimp only [\n ...\n]`
        #    with no earlier unqualified `Mir.` token
        # 2. Repeated `Mir.` segment `Mir.Crate.Mir.body`
        # 3. Nested guillemet `«a«b».wpMirExecSym` inside multiline `simp [\n ...\n]`
        # 4. Multiline `unfold\n  bitwiseAndBits`
        # 5. Multiline `set_option\n  trace.profiler.threshold 10`
        # 6. Multiline `private\ntheorem` duplicate
        pad = "-- padding line without tactic keywords\n" * 250
        src = (
            pad
            + "theorem prefilter_edges : True := by\n"
            + "  dsimp only [\n    Anneal.Mir.Crate.Item.body,\n    Mir.Crate.Mir.body\n  ]\n"
            + "  simp [\n    «a«b».wpMirExecSym\n  ]\n"
            + "  unfold\n    bitwiseAndBits\n"
            + "  trivial\n"
            + "set_option\n  trace.profiler.threshold 10\n"
            + "private\ntheorem dup_multiline (x : Nat) : x = x := rfl\n"
            + "private\nlemma dup_multiline (y : Nat) : y = y := rfl\n"
        )
        self.assertGreater(len(src), 9000)
        findings = [(f.rule, f.symbol) for f in proof_health.scan_lean_text(src, scan_siblings=False)]
        self.assertEqual(
            findings,
            [
                (R2, "Anneal.Mir.Crate.Item.body"),
                (R2, "Mir.Crate.Mir.body"),
                (R1, "«a«b».wpMirExecSym"),
                (R3, "bitwiseAndBits"),
                (R4, "trace.profiler.threshold=10"),
                (R5, "dup_multiline"),
            ],
        )

    def test_large_file_windows_match_unfiltered_scan(self) -> None:
        # Files over 8,192 chars only search simp lists reachable from keyword-anchored
        # windows. Every case below is reported by the unfiltered scan and must stay
        # reported: `.eq_` inside a qualified name makes any entry tail acceptable,
        # `unfold`/`delta` target lists may run far past 2,048 chars, and a window
        # anchored at a non-entry occurrence can be the only one reaching a long list.
        pad = "-- padding line without tactic keywords\n" * 250
        filler = ",\n    ".join(f"lemma_{i}" for i in range(300))
        defs = "\n    ".join(f"defn_{i}" for i in range(300))
        cases = [
            (
                "theorem a : True := by\n  simpa [\n    Mir.Crate.foo.body_lemma,\n    Mir.eq_1.body a\n  ]\n",
                [(R2, 254, "Mir.eq_1.body")],
            ),
            ("theorem a : True := by\n  simp [Foo.eq_1.wpMirExecSym x]\n", [(R1, 252, "Foo.eq_1.wpMirExecSym")]),
            (
                f"theorem a : True := by\n  unfold\n    {defs}\n    bitwiseOrBits\n    Mir.Crate.foo.body\n",
                [(R3, 553, "bitwiseOrBits"), (R2, 554, "Mir.Crate.foo.body")],
            ),
            (
                "theorem a : True := by\n  delta " + " ".join(f"defn_{i}" for i in range(300)) + " bitwiseAndBits\n",
                [(R3, 252, "bitwiseAndBits")],
            ),
            (
                f"theorem a : True := by\n  simp only [(wpMirExecSym x),\n    {filler},\n    wpMirExecSym]\n",
                [(R1, 553, "wpMirExecSym")],
            ),
            (
                f"theorem a : True := by\n  simp only [foo.body x,\n    {filler},\n    bitwiseAndBits]\n  exact Mir.x\n",
                [(R3, 553, "bitwiseAndBits")],
            ),
        ]
        for body, expected in cases:
            src = pad + body
            self.assertGreater(len(src), 8192)
            drop_scan_memo()
            self.assertEqual(scan(src), expected, body[:60])
            self.assertEqual(scan(src), expected, "memoized rescan must agree")

    def test_exact_mir_body_gate_only_skips_impossible_rule2_work(self) -> None:
        # `Mir.` and `.body` far apart (no `Mir.<...>.body` identifier) cannot yield a
        # rule-2 finding; a real identifier anywhere (even qualified or guillemet-quoted
        # segments) must keep rule-2 checks on for simp lists and `unfold` targets.
        self.assertFalse(proof_health._has_mir_body_ident("open Mir.Foo\nx.body\n"))
        self.assertFalse(proof_health._has_mir_body_ident("Mir.x.bodyX\nMir.y.body_lemma\n"))
        self.assertTrue(proof_health._has_mir_body_ident("foo.body Mir.C.«match».body\n"))
        self.assertTrue(proof_health._has_mir_body_ident("Anneal.Mir.C.I.body.eq_def\n"))
        # When Rules 1, 2, and 3 are all absent from `stripped`, `.body` does not anchor windows.
        kws_none, has_mb, has_bw = proof_health._active_simp_keywords("open Mir.Foo\nsimp [x.body]\n")
        self.assertEqual((kws_none, has_mb, has_bw), ({}, False, False))
        # When Rule 3 (or Rule 1) is present, `.body` stays in `kw_offsets` to anchor long lists.
        kws_bw, has_mb2, has_bw2 = proof_health._active_simp_keywords(
            "open Mir.Foo\nsimp [x.body, bitwiseAndBits]\n"
        )
        self.assertIn(".body", kws_bw)
        self.assertFalse(has_mb2)
        self.assertTrue(has_bw2)
        pad = "-- padding line without tactic keywords\n" * 250
        src = pad + "open Mir.Foo\ntheorem a : True := by\n  unfold x.body\n  delta\n    Mir.C.«match».body\n"
        self.assertEqual(scan(src), [(R2, 255, "Mir.C.«match».body")])

    def test_scan_lean_file_memo_never_serves_text_mode_sibling_texts(self) -> None:
        # Sibling lexing reads files in text mode (`\r` becomes `\n`), while
        # `scan_lean_file` decodes bytes (a lone `\r` stays whitespace inside a `--`
        # comment). Scanning `b.lean` first caches `a.lean`'s text-mode text; a later
        # `scan_lean_file(a.lean)` must still see the bytes-decoded text.
        with tempfile.TemporaryDirectory() as tmp:
            a = Path(tmp) / "a.lean"
            b = Path(tmp) / "b.lean"
            a.write_bytes(
                b"private theorem a_priv (n : Nat) : n = n := rfl\n"
                b"-- note\r  simp [wpMirExecSym]\n"
            )
            b.write_text("private theorem b_priv (m : Nat) : m + 0 = m := rfl\n", encoding="utf-8")
            settle(a, b)
            clear_in_process_caches()
            fresh = proof_health.scan_lean_file(a, scan_siblings=False)
            self.assertEqual(fresh, [])
            clear_in_process_caches()
            proof_health.scan_lean_file(b, scan_siblings=True)  # caches a.lean as a sibling
            self.assertEqual(proof_health.scan_lean_file(a, scan_siblings=False), fresh)

    def test_scan_lean_file_memo_skips_racy_files(self) -> None:
        # A file stamped within `RACY_MTIME_WINDOW_NS` may be rewritten within the same
        # timestamp tick at the same size; caching it would serve stale text later.
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / "r.lean"
            f.write_text("theorem t : True := by\n  simp [abcdefghijkl]\n", encoding="utf-8")
            settle(f)
            mtime_ns = f.stat().st_mtime_ns
            clear_in_process_caches()
            real_is_racy = proof_health._is_racy
            proof_health._is_racy = lambda st: True
            try:
                self.assertEqual(proof_health.scan_lean_file(f, scan_siblings=False), [])
            finally:
                proof_health._is_racy = real_is_racy
            size = f.stat().st_size
            f.write_text("theorem t : True := by\n  simp [wpMirExecSym]\n", encoding="utf-8")
            os.utime(f, ns=(mtime_ns, mtime_ns))
            self.assertEqual(f.stat().st_size, size)  # same size, same stamp, new text
            self.assertEqual(
                [(x.rule, x.symbol) for x in proof_health.scan_lean_file(f, scan_siblings=False)],
                [(R1, "wpMirExecSym")],
            )

    def test_scan_text_meta_memo_returns_fresh_keyword_dicts(self) -> None:
        text = ("-- pad\n" * 800) + "theorem t : True := by\n  simp [Trusted.Sequence.length]\n"
        drop_scan_memo()
        first = proof_health._scan_text_meta(text)[2]
        first.clear()
        second = proof_health._scan_text_meta(text)[2]
        self.assertIn("Sequence.length", second)
        self.assertEqual(scan(text), [(R1, 802, "Trusted.Sequence.length")])

    def test_racy_sibling_edit_never_poisons_post_window_cache_and_fifo_eviction(self) -> None:
        # A sibling scanned while `_is_racy` is True and then overwritten in the same
        # timestamp tick at the same size must be re-read once `_is_racy` becomes False,
        # rather than serving the pre-rewrite entry from `_SIBLING_PRIVATE_CACHE` or
        # `_FILE_TEXTS_CACHE`.
        with tempfile.TemporaryDirectory() as tmp:
            sib = Path(tmp) / "Sib.lean"
            tgt = Path(tmp) / "Tgt.lean"
            sib.write_text(
                "private theorem h (n : Nat) : n = 0 := sorry\n"
                "private def d (x : Nat) : Nat := x + 1\n",
                encoding="utf-8",
            )
            tgt.write_text(
                "private theorem g (m : Nat) : m = 1 := sorry\n"
                "private def e (y : Nat) : Nat := y + 2\n",
                encoding="utf-8",
            )
            settle(sib, tgt)
            st0 = sib.stat()
            clear_in_process_caches()
            real_is_racy = proof_health._is_racy
            proof_health._is_racy = lambda st: True
            try:
                self.assertEqual(proof_health.scan_lean_file(tgt, scan_siblings=True), [])
            finally:
                proof_health._is_racy = real_is_racy
            # Same-tick, same-size rewrite of `Sib.lean` while it was racy:
            sib.write_text(
                "private theorem h (n : Nat) : n = 1 := sorry\n"
                "private def d (x : Nat) : Nat := x + 2\n",
                encoding="utf-8",
            )
            os.utime(sib, ns=(st0.st_atime_ns, st0.st_mtime_ns))
            self.assertEqual((sib.stat().st_mtime_ns, sib.stat().st_size), (st0.st_mtime_ns, st0.st_size))
            # Now `_is_racy` is False (settled stamp); scan must detect both sibling duplicates.
            findings = proof_health.scan_lean_file(tgt, scan_siblings=True)
            self.assertEqual([(f.rule, f.line, f.symbol) for f in findings], [(R5, 1, "g"), (R5, 2, "e")])

        # FIFO eviction on `_FILE_TEXTS_CACHE` preserves recent entries instead of wiping all.
        clear_in_process_caches()
        for i in range(proof_health._FILE_TEXTS_CACHE_MAX + 5):
            proof_health._put_file_texts_cache(f"k{i}", (i,))
        self.assertEqual(len(proof_health._FILE_TEXTS_CACHE), proof_health._FILE_TEXTS_CACHE_MAX)
        self.assertNotIn("k0", proof_health._FILE_TEXTS_CACHE)
        self.assertIn(f"k{proof_health._FILE_TEXTS_CACHE_MAX + 4}", proof_health._FILE_TEXTS_CACHE)

    def test_decl_header_fast_path_defers_any_pipe_to_the_full_walk(self) -> None:
        # With a `«` later before the declaration boundary, the full header walk only
        # accepts a top-level `:` reached through correctly nested brackets. A `|`
        # header whose colons are all nested (`[inst : C] ||`) or whose brackets are
        # out of order has no complete header, so these private theorems are not
        # duplicates of each other; a whole-slice fast path must not invent headers.
        pair = (
            "private theorem t [inst : C] || := by\n  exact «q»\n"
            "private theorem u [inst : C] || := by\n  exact «q»\n"
        )
        self.assertEqual(scan(pair), [])
        start = len("private theorem t")
        for hdr in (
            "private theorem t [inst : C] || := by\n  exact «q»\n",
            "private theorem t (x : Nat) ) (h : a | b : True := by\n  exact «x»\n",
        ):
            self.assertEqual(proof_health._decl_header_span(hdr, start, 0), ("", -1), hdr)
        # A set-builder `|` header with a real top-level `:` keeps its header, and
        # guillemet-free `||` / inline `match` headers stay on the fast path.
        set_builder = "private theorem t {s : Set Nat} (h : s = {x | x > 0}) : s = s := by\n  exact «q»\n"
        self.assertEqual(
            proof_health._decl_header_span(set_builder, start, 0),
            (" {s : Set Nat} (h : s = {x | x > 0}) : s = s ", set_builder.index(":= by") + 2),
        )
        self.assertEqual(scan(set_builder + set_builder.replace(" t ", " u ", 1)), [(R5, 3, "u")])
        no_gui_or = "private theorem t (a b : Bool) (h : (a || b) = true) : True := trivial\n"
        self.assertEqual(
            proof_health._decl_header_span(no_gui_or, start, 0),
            (" (a b : Bool) (h : (a || b) = true) : True ", no_gui_or.index(":= trivial") + 2),
        )
        self.assertEqual(scan(no_gui_or + no_gui_or.replace(" t ", " u ", 1)), [(R5, 2, "u")])

    def test_rule5_fingerprint_prefilter_is_kind_agnostic(self) -> None:
        # Renaming a guillemet binder (`«p:q»` -> `_v0`) drops the punctuation inside
        # it, so the alpha-equivalent theorems `a` and `b` have different structural
        # fingerprints. They are still compared because the defs `c` / `d` share those
        # fingerprints: the pre-filter counts collisions across all kinds, and a
        # per-kind count would silently drop both reported duplicates.
        src = (
            "private theorem a («p:q» : Nat) : «p:q» = «p:q» := rfl\n"
            "private theorem b (x : Nat) : x = x := rfl\n"
            "private def c («r:s» : Nat) : «r:s» = «r:s» := rfl\n"
            "private def d (y : Nat) : y = y := rfl\n"
        )
        self.assertEqual(scan(src), [(R5, 2, "b"), (R5, 4, "d")])

    def test_shared_lexer_code_matches_rules_1_to_5_stripper(self) -> None:
        # Rules 1-5 run on the code of the shared auditor's single-pass lexer
        # (`_scan_lean_comments_and_strings`, whose comment blocks rules 6/7 reuse), while
        # siblings and `_scan_text_meta` lex with `strip_lean_comments_and_strings`: both must
        # blank exactly the same characters, on the dogfood files and on delimiter soups.
        import random

        rnd = random.Random(20261115)
        toks = ["--", "/-", "-/", "/--", "/-!", '"', "\\", "'", "«", "»", 'r"', 'r#"', '"#', "#"]
        toks += ["r", "a", "x'", "'\"'", "'\\\"'", "'«'", "\n", " ", "é", "\r", "-", "/", "."]
        samples = ["".join(rnd.choice(toks) for _ in range(rnd.randint(0, 40))) for _ in range(3000)]
        for path in (
            REPO_ROOT / "theory" / "Anneal" / "BitValidity.lean",
            REPO_ROOT / "theory" / "Anneal" / "Mir" / "Cast.lean",
            REPO_ROOT / "theory" / "Anneal" / "Rustc" / "V2026_06_01" / "SymReflect.lean",
            EPISODE1_BYTECODEC,
            EPISODE1_ADT_AND_CONTROL,
        ):
            samples.append(path.read_bytes().decode("utf-8", errors="replace"))
        for src in samples:
            self.assertEqual(
                proof_health._scan_lean_comments_and_strings(src)[0],
                proof_health.strip_lean_comments_and_strings(src),
                repr(src[:80]),
            )

    def test_scan_lean_file_text_memo_forwards_vacuity_scope(self) -> None:
        # A settled file's text is served from the stat-validated `scan_lean_file` memo on
        # rescans; `include_unannotated_vacuity` (`--all-theorems`) must still reach the scan
        # instead of yielding the annotated-scope result of the same text.
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / "V.lean"
            f.write_text("theorem t : True := trivial\n", encoding="utf-8")
            settle(f)
            clear_in_process_caches()
            self.assertEqual(proof_health.scan_lean_file(f, scan_siblings=False), [])
            self.assertIn(proof_health._SCAN_FILE_KEY_PREFIX + str(f), proof_health._FILE_TEXTS_CACHE)
            every = proof_health.scan_lean_file(f, scan_siblings=False, include_unannotated_vacuity=True)
            self.assertEqual(
                [(x.rule, x.subrule) for x in every],
                [(proof_health.RULE_TRIVIAL_OR_VACUOUS_CLAIM, "trivial_conclusion")],
            )
            self.assertEqual(proof_health.scan_lean_file(f, scan_siblings=False), [])

    def test_scan_text_meta_memo_matches_code_and_skips_splice_windows(self) -> None:
        text = ("-- pad\n" * 800) + "theorem t : True := by\n  simp [Trusted.Sequence.length]\n"
        code = proof_health._scan_lean_comments_and_strings(text)[0]
        drop_scan_memo()
        keys = set(proof_health._FILE_TEXTS_CACHE)
        self.assertIs(proof_health._scan_text_meta(text, code, memo=False)[0], code)
        self.assertEqual(set(proof_health._FILE_TEXTS_CACHE), keys)  # `memo=False` stores nothing
        self.assertIn("Sequence.length", proof_health._scan_text_meta(text, code)[2])
        # A memo entry describes the code it was computed from: different code for the same
        # text is indexed afresh instead of being served the other code's index.
        simp_call = "simp [Trusted.Sequence.length]"
        other = code.replace(simp_call, " " * len(simp_call))
        self.assertEqual(proof_health._scan_text_meta(text, other)[2], {})

        # Incremental splicing re-scans a one-off window of an edited large file; those
        # windows skip the memo so they never evict sibling texts from the shared FIFO.
        big = EPISODE1_BYTECODEC.read_text(encoding="utf-8")
        anchor = "theorem scalarValidRange_isExactWidth (sz : Nat)"
        self.assertIn(anchor, big)
        edited = big.replace(anchor, f"{anchor} (hMemo : 0 ≤ 1)", 1)
        drop_scan_memo()
        cold = proof_health.scan_lean_text(edited, scan_siblings=False)
        drop_scan_memo()
        proof_health.scan_lean_text(big, scan_siblings=False)  # full scan: splice baseline
        real_meta = proof_health._scan_text_meta
        calls: list[tuple[int, bool]] = []

        def recording_meta(t: str, stripped: str | None = None, *, memo: bool = True):
            calls.append((len(t), memo))
            return real_meta(t, stripped, memo=memo)

        with patch.object(proof_health, "_scan_text_meta", recording_meta):
            spliced = proof_health.scan_lean_text(edited, scan_siblings=False)
        self.assertEqual(spliced, cold)
        self.assertTrue(calls)
        self.assertTrue(all(n < len(edited) and not memo for n, memo in calls), calls)

    def test_cold_scan_lexes_once_for_rules_1_to_7(self) -> None:
        # Rules 1-5 and the shared auditor (rules 6/7, via `_preparsed`) share one lexing
        # pass of a cold full scan; neither re-lexes the whole text.
        text = EPISODE1_BYTECODEC.read_text(encoding="utf-8")
        expected = proof_health.scan_lean_text(text, scan_siblings=False)
        real_lex = proof_health._scan_lean_comments_and_strings
        real_strip = proof_health.strip_lean_comments_and_strings
        full_lexes: list[str] = []

        def counting_lex(t: str):
            if len(t) == len(text):
                full_lexes.append("shared")
            return real_lex(t)

        def counting_strip(t: str, *, keep_strings: bool = False):
            if len(t) == len(text):
                full_lexes.append("strip")
            return real_strip(t, keep_strings=keep_strings)

        drop_scan_memo()
        with patch.object(proof_health, "_scan_lean_comments_and_strings", counting_lex), patch.object(
            proof_health, "strip_lean_comments_and_strings", counting_strip
        ):
            self.assertEqual(proof_health.scan_lean_text(text, scan_siblings=False), expected)
        self.assertEqual(full_lexes, ["shared"])


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

    def test_structured_transcript_result_steps_are_paired_with_planner_calls(self) -> None:
        # Structured transcripts: the planner step lists its calls without timings and
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

    def test_zero_epoch_timestamps_and_interrupted_turn_reset(self) -> None:
        steps = [
            # Monotonic `start_time: 0.0` must not be dropped by truthiness checks.
            {"tool": "lean_goal", "start_time": 0.0, "end_time": 0.025, "batch_id": "m1"},
            # Interrupted planner step: 2 calls emitted, only 1 result arrives before USER_INPUT.
            {
                "step_index": 30,
                "type": "PLANNER_RESPONSE",
                "tool_calls": [{"name": "lean_hover"}, {"name": "stale_call"}],
            },
            {
                "step_index": 31,
                "type": "GENERIC",
                "content": "Created At: 2026-11-10T01:00:00Z\nCompleted At: 2026-11-10T01:00:00Z\nok",
            },
            {"step_index": 32, "type": "USER_INPUT", "content": "stop and retry"},
            {"step_index": 33, "type": "PLANNER_RESPONSE", "content": "acknowledged"},
            # Stray generic step after turn reset must not attach to `stale_call`.
            {
                "step_index": 34,
                "type": "GENERIC",
                "content": "Created At: 2026-11-10T01:00:05Z\nCompleted At: 2026-11-10T01:00:06Z\nstray",
            },
        ]
        stats = proof_health.compute_unbatched_tool_latencies(steps)
        self.assertEqual(stats["unbatched_count"], 2)
        self.assertEqual(sorted(stats["by_tool"].keys()), ["lean_goal", "lean_hover"])
        self.assertAlmostEqual(stats["by_tool"]["lean_goal"]["unbatched_mean_ms"], 25.0)
        self.assertNotIn("stale_call", stats["by_tool"])

    def test_unhashable_nonfinite_and_oversized_fields_never_crash(self) -> None:
        events = [
            # Unhashable or non-finite ids are skipped: a call stands alone unless a
            # later key (`step_index`, `turn_id`) holds a usable id.
            {"tool": "a", "duration_ms": 5.0, "batch_id": [1]},
            {"tool": "b", "duration_ms": 9000.0, "batch_id": [1]},
            {"tool": "c", "duration_ms": 7.0, "batch_id": {"k": 1}, "step_index": float("nan")},
            {"tool": "d", "duration_ms": 3.0, "batch_id": float("inf"), "turn_id": [2]},
            {"tool": "e", "duration_ms": 4.0, "batch_id": ["x"], "step_index": 77},
            {"tool": "f", "duration_ms": 6000.0, "step_index": 77},
            # JSON integers too large for a float, and an overflow to `inf` ms.
            {"tool": "g", "duration_ms": 10**400},
            {"tool": "h", "started_at": 10**400, "completed_at": 10**400 + 5},
            {"tool": "i", "duration_s": 1e306},
            {"tool": "j", "started_at": -1.7e308, "completed_at": 1.7e308},
            # `int(inf)` / `int(nan)` batch sizes fall back to 1.
            {"tool": "k", "duration_ms": 8.0, "batch_size": float("inf")},
            {"tool": "l", "duration_ms": 2.0, "batch_size": float("nan")},
            # A long-call marker whose only id is unhashable.
            {"tool": "m", "is_long_call": True, "batch_id": {"k": 2}},
        ]
        stats = proof_health.compute_unbatched_tool_latencies(events)
        self.assertEqual(sorted(e["tool"] for e in stats["batched_with_long_call"]), ["e", "f"])
        self.assertEqual(
            sorted(e["tool"] for e in stats["unbatched"]), ["a", "b", "c", "d", "k", "l"]
        )
        for tool in ("g", "h", "i", "j", "m"):
            self.assertNotIn(tool, stats["by_tool"])

    def test_inline_jsonl_longer_than_name_max_and_overlong_paths(self) -> None:
        pad = "p" * 6000
        lines = [
            json.dumps({"tool": "lean_goal", "duration_ms": 10.0, "batch_id": "t1", "pad": pad}),
            json.dumps({"tool": "lean_hover", "duration_ms": 30.0, "batch_id": "t2", "pad": pad}),
        ]
        stats = proof_health.compute_unbatched_tool_latencies("\n".join(lines))
        self.assertEqual(stats["unbatched_count"], 2)
        self.assertAlmostEqual(stats["unbatched_mean_ms"], 20.0)
        self.assertEqual(proof_health.compute_unbatched_tool_latencies(lines[0])["unbatched_count"], 1)
        for missing in ("x" * 5000, Path(tempfile.gettempdir()) / ("y" * 300)):
            self.assertEqual(proof_health.compute_unbatched_tool_latencies(missing)["total_count"], 0)

    def test_oversized_int_and_container_tool_names_single_dict_and_nan_threshold(self) -> None:
        events = [
            # 5000-digit int tool name must not raise `ValueError` in `str(name)`.
            {"tool": 10**5000, "duration_ms": 5.0},
            # Non-string `tool` falls through to valid string `name` instead of `"True"`.
            {"tool": True, "name": "lean_goal", "duration_ms": 15.0, "batch_id": "s1"},
            # Container tool names are ignored rather than stringified to `"['x']"`.
            {"tool": ["x"], "duration_ms": 5.0},
            {"tool": {"k": 1}, "duration_ms": 5.0},
            {
                "type": "PLANNER_RESPONSE",
                "tool_calls": [{"name": 10**5000, "duration_ms": 20.0}],
            },
        ]
        stats = proof_health.compute_unbatched_tool_latencies(
            events, long_call_threshold_ms=float("nan")
        )
        self.assertEqual(stats["unbatched_count"], 2)
        self.assertEqual(sorted(stats["by_tool"].keys()), ["lean_goal", "unknown"])
        single = proof_health.compute_unbatched_tool_latencies(
            {"tool": "lean_hover", "duration_ms": 8.0}
        )
        self.assertEqual(single["unbatched_count"], 1)
        self.assertEqual(proof_health.compute_unbatched_tool_latencies(b"raw")["total_count"], 0)


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
                **target_replacement_edit(lean_file, "  trivial\n", "  dsimp [wpMirExecSym]\n  trivial\n"),
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
                {"error": "tool failed", **target_replacement_edit(opted_out, "a", "b")},
                {"toolCall": {"args": {"Path": str(tmp_dir / "Missing.lean")}}},
                {"toolCall": {"args": {"Path": str(text_file)}}},
                target_replacement_edit(opted_out, "  trivial\n", "  dsimp [wpMirExecSym]\n"),
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

    def test_hook_accepts_flat_payload_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            lean_file = tmp_dir / "Flat.lean"
            text = "theorem t : True := by\n  dsimp [wpMirExecSym]\n  trivial\n"
            lean_file.write_text(text, encoding="utf-8")
            out = self.run_hook(
                {"Path": str(lean_file), "Content": text},
                self.hook_env(tmp_dir / "flat-cache.json"),
            )
            self.assertIn("`dsimp_forbidden_sym` (+1 at L2)", out["overwriteResult"])


# ---------------------------------------------------------------------------
# Rules 6 & 7: shared waiver-pin & 3-axis auditor. The 100 unit / mutation tests below are
# ported from the validated prototype suite (`test_waiver_pin_audit_proto.py`, `2dd38e6d`)
# and run through `audit`, which serves the prototype's API names from `proof_health`.
# ---------------------------------------------------------------------------


class _SharedAuditorAPI:
    """Prototype `waiver_pin_audit_proto` names, resolved against `proof_health`."""

    _RENAMED = {
        "scan_lean_text": "audit_lean_text",
        "scan_rust_text": "audit_rust_text",
        "scan_file": "audit_file",
        "count_findings_by_rule": "count_audit_findings_by_rule",
        "ALL_RULES": "ALL_WAIVER_AUDIT_RULES",
    }

    def __getattr__(self, name: str):
        return getattr(proof_health, self._RENAMED.get(name, name))


audit = _SharedAuditorAPI()
EPISODE1_BYTECODEC = REPO_ROOT / "theory" / "Anneal" / "ByteCodec.lean"
EPISODE1_ADT_AND_CONTROL = REPO_ROOT / "theory" / "Anneal" / "Mir" / "AdtAndControl.lean"


def pin_rust_snippet(directive_prefix: str, item_code: str) -> str:
    """Pin `item_code` with a standalone `/// pin:sha256:<12hex>` doc line (the only placement
    spec.rs accepts for every waiver directive)."""
    draft = f"{directive_prefix}\n{item_code}\n"
    pins = audit.compute_rust_item_pins(draft)
    assert pins, "expected at least one Rust item pin"
    pin_tag = next(iter(pins.values()))
    return f"{directive_prefix}\n/// {pin_tag}\n{item_code}\n"


def pin_lean_decl(doc_lines: list[str], decl: str) -> str:
    """Pin a Lean declaration with a standalone `pin:` line inside its `/-- -/` docstring."""
    body = "\n".join(doc_lines)
    draft = f"/--\n{body}\n-/\n{decl}"
    pin_tag = audit.compute_lean_decl_pins(draft)[_lean_decl_name(decl)]
    return f"/--\n{body}\n{pin_tag}\n-/\n{decl}"


def _lean_decl_name(decl: str) -> str:
    head = decl.split("\n", 1)[0].split()
    return head[1].split("(")[0].split(":")[0]


class TestWaiverPinRecordImmutability(unittest.TestCase):
    def test_finding_immutability_and_value_equality(self) -> None:
        f1 = audit.WaiverPinFinding(
            rule=audit.RULE_UNPINNED_WAIVER,
            line=10,
            message="msg",
            suggestion="sug",
            symbol="foo",
            expected_pin="pin:sha256:0123456789ab",
            actual_pin="",
            tier="S1",
        )
        f2 = audit.WaiverPinFinding(
            rule=audit.RULE_UNPINNED_WAIVER,
            line=10,
            message="msg",
            suggestion="sug",
            symbol="foo",
            expected_pin="pin:sha256:0123456789ab",
            actual_pin="",
            tier="S1",
        )
        self.assertEqual(f1, f2)
        self.assertEqual(hash(f1), hash(f2))
        self.assertIn("WaiverPinFinding", repr(f1))
        self.assertEqual(f1.to_dict()["rule"], audit.RULE_UNPINNED_WAIVER)
        with self.assertRaises(AttributeError):
            f1.line = 20  # type: ignore[misc]

    def test_annotation_and_metadata_record_immutability(self) -> None:
        ann = audit.WaiverAnnotation(
            directive="allow_compile_time_guard",
            tier="S1",
            reason="guard",
            pin_tokens=("pin:sha256:0123456789ab",),
            line=1,
            raw_line="anneal:allow_compile_time_guard pin:sha256:0123456789ab",
        )
        with self.assertRaises(AttributeError):
            ann.tier = "S3"  # type: ignore[misc]

        rec = audit.TheoremMetadataRecord(
            name="thm",
            line=5,
            kind="safety",
            witness="universal",
            assumes="S0",
            subject="foo",
            hypotheses=("x : Nat",),
            conclusion="x = x",
        )
        with self.assertRaises(AttributeError):
            rec.kind = "helper"  # type: ignore[misc]


class TestRustWaiverPinningAndMutations(unittest.TestCase):
    def test_valid_rust_s1_allow_compile_time_guard_pin(self) -> None:
        s1_src = pin_rust_snippet(
            "/// anneal:allow_compile_time_guard",
            "pub fn guarded_transmute(x: [u8; 4]) -> u32 {\n"
            "    const { assert!(core::mem::size_of::<u32>() == 4); }\n"
            "    u32::from_le_bytes(x)\n"
            "}",
        )
        self.assertEqual(audit.scan_rust_text(s1_src), [])

    def test_valid_rust_s2_documented_intent_pin(self) -> None:
        s2_src = pin_rust_snippet(
            "/// anneal:documented_intent Upstream RFC guarantees niche layout",
            "pub fn niche_opt(x: core::num::NonZeroU32) -> Option<core::num::NonZeroU32> {\n"
            "    Some(x)\n"
            "}",
        )
        self.assertEqual(audit.scan_rust_text(s2_src), [])

    def test_valid_rust_s3_pinned_compiler_coupled_pin(self) -> None:
        s3_src = pin_rust_snippet(
            "/// anneal:pinned_compiler_coupled Tuple layout pinned to rustc 1.98",
            "pub fn pair_bytes(p: (u16, u16)) -> u32 {\n"
            "    (p.0 as u32) | ((p.1 as u32) << 16)\n"
            "}",
        )
        self.assertEqual(audit.scan_rust_text(s3_src), [])

    def test_valid_rust_tcb_trusted_reason_pin(self) -> None:
        tcb_src = pin_rust_snippet(
            '/// anneal:trusted reason = "Hardware MMIO volatile register read"',
            "pub unsafe fn read_mmio(addr: *const u32) -> u32 {\n"
            "    unsafe { core::ptr::read_volatile(addr) }\n"
            "}",
        )
        self.assertEqual(audit.scan_rust_text(tcb_src), [])

    def test_valid_rust_multi_directive_doc_block(self) -> None:
        item = "pub unsafe fn multi_dir(x: usize) -> usize { x }"
        draft = (
            "/// anneal:requires x != 0\n"
            "/// anneal:spec ensures(ret == x)\n"
            "/// anneal:allow_compile_time_guard\n"
            "/// anneal:documented_intent Non-zero identity check\n"
            f"{item}\n"
        )
        pin = audit.compute_rust_item_pins(draft)["multi_dir"]
        pinned = (
            "/// anneal:requires x != 0\n"
            "/// anneal:spec ensures(ret == x)\n"
            "/// anneal:allow_compile_time_guard\n"
            "/// anneal:documented_intent Non-zero identity check\n"
            f"/// {pin}\n"
            f"{item}\n"
        )
        self.assertEqual(audit.scan_rust_text(pinned), [])
        # One standalone pin line covers every waiver of the block; an extra inline pin on the
        # free-form rationale must agree with it.
        agreeing = pinned.replace("identity check\n", f"identity check {pin}\n")
        self.assertEqual(audit.scan_rust_text(agreeing), [])

    def test_rust_comment_only_edits_preserve_pin(self) -> None:
        base_item = (
            "#[repr(C)]\n"
            "pub struct Packet {\n"
            "    pub tag: u16,\n"
            "    pub payload: u16,\n"
            "}"
        )
        pinned_src = pin_rust_snippet(
            "/// anneal:pinned_compiler_coupled C ABI packet header",
            base_item,
        )
        self.assertEqual(audit.scan_rust_text(pinned_src), [])

        commented_src = pinned_src.replace(
            "pub tag: u16,",
            "// interior line comment\n    /* outer /* nested { } ; */ comment */\n    pub   tag : u16 ,",
        )
        self.assertEqual(audit.scan_rust_text(commented_src), [])

    def test_rust_code_mutation_breaks_pin(self) -> None:
        base_item = (
            "#[repr(C)]\n"
            "pub struct Packet {\n"
            "    pub tag: u16,\n"
            "    pub payload: u16,\n"
            "}"
        )
        pinned_src = pin_rust_snippet(
            "/// anneal:pinned_compiler_coupled C ABI packet header",
            base_item,
        )
        drifted_field = pinned_src.replace("pub payload: u16", "pub payload: u32")
        findings = audit.scan_rust_text(drifted_field)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].rule, audit.RULE_DRIFTED_WAIVER_PIN)
        self.assertEqual(findings[0].symbol, "Packet")
        self.assertEqual(findings[0].tier, "S3")

    def test_rust_repr_c_to_repr_rust_mutation_breaks_pin(self) -> None:
        base_item = (
            "#[repr(C)]\n"
            "pub struct Packet {\n"
            "    pub tag: u16,\n"
            "    pub payload: u16,\n"
            "}"
        )
        pinned_src = pin_rust_snippet(
            "/// anneal:pinned_compiler_coupled C ABI packet header",
            base_item,
        )
        drifted_repr = pinned_src.replace("#[repr(C)]", "#[repr(Rust)]")
        findings = audit.scan_rust_text(drifted_repr)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].rule, audit.RULE_DRIFTED_WAIVER_PIN)

    def test_rust_repr_attribute_above_doc_comment_is_pinned_and_detects_drift(self) -> None:
        draft = (
            "#[repr(C)]\n"
            "/// anneal:pinned_compiler_coupled C layout above doc comment\n"
            "pub struct Header(pub u32, pub u32);\n"
        )
        pin = audit.compute_rust_item_pins(draft)["Header"]
        pinned = draft.replace(
            "C layout above doc comment",
            f"C layout above doc comment {pin}",
        )
        self.assertEqual(audit.scan_rust_text(pinned), [])

        drifted = pinned.replace("#[repr(C)]", "#[repr(transparent)]")
        findings = audit.scan_rust_text(drifted)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].rule, audit.RULE_DRIFTED_WAIVER_PIN)

    def test_rust_string_literal_mutation_breaks_pin(self) -> None:
        pinned = pin_rust_snippet(
            '/// anneal:trusted reason = "Panic message contract"',
            'pub fn fail_with() { panic!("expected message A"); }',
        )
        self.assertEqual(audit.scan_rust_text(pinned), [])
        drifted = pinned.replace("expected message A", "expected message B")
        findings = audit.scan_rust_text(drifted)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].rule, audit.RULE_DRIFTED_WAIVER_PIN)

    def test_rust_semicolon_tuple_and_unit_structs_and_trait_methods(self) -> None:
        s_tuple = pin_rust_snippet(
            "/// anneal:pinned_compiler_coupled Newtype tuple struct",
            "#[repr(transparent)]\npub struct Wrapper(pub u64);",
        )
        self.assertEqual(audit.scan_rust_text(s_tuple), [])

        s_unit = pin_rust_snippet(
            "/// anneal:documented_intent ZST marker struct",
            "pub struct Marker;",
        )
        self.assertEqual(audit.scan_rust_text(s_unit), [])

    def test_rust_lifetimes_char_literals_and_raw_strings(self) -> None:
        item = (
            "pub fn lifetime_and_chars<'a, 'b>(buf: &'a [u8], fallback: &'b u8) -> &'a u8 {\n"
            "    let open_brace: char = '{';\n"
            "    let close_brace: char = '}';\n"
            "    let escaped_quote: char = '\\'';\n"
            "    let semi_byte: u8 = b';';\n"
            '    let fake_doc = r##"/// anneal:trusted reason = "fake inside raw string"}"##;\n'
            "    let _ = (open_brace, close_brace, escaped_quote, semi_byte, fake_doc);\n"
            "    if buf.is_empty() { fallback } else { &buf[0] }\n"
            "}"
        )
        pinned = pin_rust_snippet(
            '/// anneal:trusted reason = "Lifetime-heavy slice indexing"',
            item,
        )
        self.assertEqual(audit.scan_rust_text(pinned), [])

        drifted = pinned.replace("&buf[0]", "&buf[1]")
        findings = audit.scan_rust_text(drifted)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].rule, audit.RULE_DRIFTED_WAIVER_PIN)

    def test_rust_raw_byte_and_c_strings_do_not_trigger_false_positives(self) -> None:
        src = (
            'pub const RAW_BYTES: &[u8] = br#"/// anneal:trusted reason = "ignored""#;\n'
            'pub const RAW_CSTR: &core::ffi::CStr = cr#"/// anneal:allow_compile_time_guard"#;\n'
        )
        self.assertEqual(audit.scan_rust_text(src), [])

    def test_rust_non_doc_comments_and_strings_ignored(self) -> None:
        src = (
            "// anneal:trusted reason = \"plain line comment is ignored by rustc\"\n"
            "//// anneal:allow_compile_time_guard\n"
            "/* anneal:pinned_compiler_coupled ignored block comment\n"
            "   /* nested /// anneal:trusted reason = \"ignored\" */ */\n"
            "/*** anneal:documented_intent ignored 3-star comment */\n"
            'pub const MSG: &str = "/// anneal:trusted reason = \\"inside string\\"";\n'
        )
        self.assertEqual(audit.scan_rust_text(src), [])

    def test_rust_doc_attribute_and_raw_doc_attribute_syntax(self) -> None:
        draft = (
            '#[doc = "anneal:allow_compile_time_guard"]\n'
            "pub fn attr_guarded(x: u64) -> u64 { x }\n"
        )
        pin = audit.compute_rust_item_pins(draft)["attr_guarded"]
        pinned = (
            '#[doc = "anneal:allow_compile_time_guard"]\n'
            f'#[doc = "{pin}"]\n'
            "pub fn attr_guarded(x: u64) -> u64 { x }\n"
        )
        self.assertEqual(audit.scan_rust_text(pinned), [])

        pinned_raw = (
            '#[doc = r#"anneal:allow_compile_time_guard"#]\n'
            f"/// {pin}\n"
            "pub fn attr_guarded(x: u64) -> u64 { x }\n"
        )
        self.assertEqual(audit.scan_rust_text(pinned_raw), [])

    def test_rust_unpinned_waiver_detection(self) -> None:
        unpinned = (
            "/// anneal:allow_compile_time_guard\n"
            "pub fn f1(x: u32) -> u32 { x }\n"
        )
        f_unpinned = audit.scan_rust_text(unpinned)
        self.assertEqual(len(f_unpinned), 1)
        self.assertEqual(f_unpinned[0].rule, audit.RULE_UNPINNED_WAIVER)
        self.assertEqual(f_unpinned[0].tier, "S1")

    def test_rust_malformed_pin_short_hex(self) -> None:
        src = "/// anneal:allow_compile_time_guard\n/// pin:sha256:12345\npub fn f() {}\n"
        res = audit.scan_rust_text(src)
        self.assertEqual(len(res), 1)
        self.assertEqual(res[0].rule, audit.RULE_MALFORMED_WAIVER_PIN)

    def test_rust_malformed_pin_uppercase_hex(self) -> None:
        src = "/// anneal:allow_compile_time_guard\n/// pin:sha256:ABCDEF012345\npub fn f() {}\n"
        res = audit.scan_rust_text(src)
        self.assertEqual(len(res), 1)
        self.assertEqual(res[0].rule, audit.RULE_MALFORMED_WAIVER_PIN)

    def test_rust_malformed_pin_wrong_algorithm(self) -> None:
        src = "/// anneal:allow_compile_time_guard\n/// pin:md5:0123456789ab\npub fn f() {}\n"
        res = audit.scan_rust_text(src)
        self.assertEqual(len(res), 1)
        self.assertEqual(res[0].rule, audit.RULE_MALFORMED_WAIVER_PIN)

    def test_rust_malformed_pin_conflicting_multiple_pins(self) -> None:
        src = (
            "/// anneal:allow_compile_time_guard\n"
            "/// pin:sha256:0123456789ab\n"
            "/// pin:sha256:fedcba987654\n"
            "pub fn f() {}\n"
        )
        res = audit.scan_rust_text(src)
        self.assertEqual(len(res), 1)
        self.assertEqual(res[0].rule, audit.RULE_MALFORMED_WAIVER_PIN)

    def test_rust_dangling_waiver_at_eof(self) -> None:
        dangling_eof = '/// anneal:trusted reason = "eof"\n/// pin:sha256:0123456789ab\n'
        res_eof = audit.scan_rust_text(dangling_eof)
        self.assertEqual(len(res_eof), 1)
        self.assertEqual(res_eof[0].rule, audit.RULE_DANGLING_WAIVER)

    def test_rust_dangling_waiver_before_closing_brace(self) -> None:
        dangling_mod = (
            "mod m {\n"
            '    /// anneal:trusted reason = "end of mod"\n'
            "    /// pin:sha256:0123456789ab\n"
            "}\n"
        )
        res_mod = audit.scan_rust_text(dangling_mod)
        self.assertEqual(len(res_mod), 1)
        self.assertEqual(res_mod[0].rule, audit.RULE_DANGLING_WAIVER)

    def test_rust_invalid_waiver_syntax_not_at_line_start(self) -> None:
        src = (
            "/// prefix text anneal:allow_compile_time_guard pin:sha256:0123456789ab\n"
            "pub fn f(x: usize) -> usize { x }\n"
        )
        res = audit.scan_rust_text(src)
        self.assertEqual(len(res), 1)
        self.assertEqual(res[0].rule, audit.RULE_INVALID_WAIVER_SYNTAX)

    def test_rust_invalid_waiver_syntax_missing_or_empty_reason(self) -> None:
        for bad_line in (
            "/// anneal:trusted pin:sha256:0123456789ab",
            '/// anneal:trusted reason = "" pin:sha256:0123456789ab',
            "/// anneal:documented_intent pin:sha256:0123456789ab",
            "/// anneal:pinned_compiler_coupled pin:sha256:0123456789ab",
        ):
            src = f"{bad_line}\npub fn f(x: usize) -> usize {{ x }}\n"
            res = audit.scan_rust_text(src)
            self.assertEqual(len(res), 1, f"failed on {bad_line}")
            self.assertEqual(res[0].rule, audit.RULE_INVALID_WAIVER_SYNTAX)

    def test_rust_invalid_waiver_syntax_unknown_directive_and_bad_requires(self) -> None:
        for bad_line in (
            "/// anneal:unknown_directive foo pin:sha256:0123456789ab",
            "/// anneal:requires x == 0",
        ):
            src = f"{bad_line}\npub fn f(x: usize) -> usize {{ x }}\n"
            res = audit.scan_rust_text(src)
            self.assertEqual(len(res), 1, f"failed on {bad_line}")
            self.assertEqual(res[0].rule, audit.RULE_INVALID_WAIVER_SYNTAX)


class TestLeanWaiverPinningAnd3AxisVacuity(unittest.TestCase):
    def test_lean_waiver_pin_and_nested_comment_insensitivity(self) -> None:
        decl = (
            "theorem demo_pinned (n : Nat) (h : 0 < n) : 1 ≤ n := by\n"
            "  omega\n"
        )
        doc = [
            "anneal:pinned_compiler_coupled Demo layout theorem",
            "Kind: safety",
            "Witness: universal",
            "Assumes: S3",
        ]
        src = pin_lean_decl(doc, decl)
        self.assertEqual(audit.scan_lean_text(src), [])
        # The pin binds the directive set: a bare-declaration hash no longer validates.
        bare_pin = audit.compute_lean_decl_pins(decl)["demo_pinned"]
        self.assertNotIn(bare_pin, src)

        with_comments = src.replace(
            "omega",
            "-- line comment\n  /- outer /- inner -/ block -/\n  omega",
        )
        self.assertEqual(audit.scan_lean_text(with_comments), [])

        drifted = src.replace("1 ≤ n", "2 ≤ n + 1")
        findings = audit.scan_lean_text(drifted)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].rule, audit.RULE_DRIFTED_WAIVER_PIN)

    def test_lean_where_structure_and_def_waiver_pinning(self) -> None:
        struct_decl = (
            "structure PinnedStruct where\n"
            "  a : Nat\n"
            "  b : Nat\n"
        )
        src = pin_lean_decl(["anneal:pinned_compiler_coupled Layout structure"], struct_decl)
        self.assertEqual(audit.scan_lean_text(src), [])

        drifted = src.replace("b : Nat", "b : UInt32")
        findings = audit.scan_lean_text(drifted)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].rule, audit.RULE_DRIFTED_WAIVER_PIN)

    def test_lean_guillemet_identifiers_and_primes_lexing(self) -> None:
        src = (
            "def «item--with--dashes» (st' : Nat) : Char := '\"'\n"
            "theorem «thm--ok» (st' fuel' : Nat) (h : st' < fuel') : st' ≤ fuel' := by\n"
            "  have c : Char := '«'\n"
            "  omega\n"
        )
        self.assertEqual(audit.scan_lean_text(src), [])

    def test_lean_dangling_waiver_before_end_and_eof(self) -> None:
        src_end = (
            "namespace Foo\n"
            "/-- anneal:allow_compile_time_guard\npin:sha256:0123456789ab -/\n"
            "end Foo\n"
        )
        f_end = audit.scan_lean_text(src_end)
        self.assertEqual(len(f_end), 1)
        self.assertEqual(f_end[0].rule, audit.RULE_DANGLING_WAIVER)

        src_eof = "/-- anneal:allow_compile_time_guard\npin:sha256:0123456789ab -/\n"
        f_eof = audit.scan_lean_text(src_eof)
        self.assertEqual(len(f_eof), 1)
        self.assertEqual(f_eof[0].rule, audit.RULE_DANGLING_WAIVER)

    def test_lean_syntactic_contradiction_false_and_bool(self) -> None:
        for src in (
            "theorem t_false (x : Nat) (h : False) : x = 42 := False.elim h",
            "theorem t_bool (x : Nat) (h : true = false) : x = 42 := by nomatch h",
        ):
            findings = audit.scan_lean_text(src)
            self.assertIn(
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                [f.rule for f in findings],
            )

    def test_lean_syntactic_contradiction_numeric_and_nat_lt_zero(self) -> None:
        for src in (
            "theorem t_zero_one (x : Nat) (h : 0 = 1) : x = 42 := by omega",
            "theorem t_num_neq (x : Nat) (h : 2 = 4) : x = 42 := by omega",
            "theorem t_nat_lt_zero (n : Nat) (h : n < 0) : n = 99 := by omega",
        ):
            findings = audit.scan_lean_text(src)
            self.assertIn(
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                [f.rule for f in findings],
            )

    def test_lean_syntactic_contradiction_irreflexive_and_option_clash(self) -> None:
        for src in (
            "theorem t_irrefl_ne (x : Nat) (h : x ≠ x) : x = 42 := False.elim (h rfl)",
            "theorem t_irrefl_not_eq (x : Nat) (h : ¬ (x = x)) : x = 42 := False.elim (h rfl)",
            "theorem t_opt_clash (x : Nat) (h : some x = none) : x = 0 := by nomatch h",
        ):
            findings = audit.scan_lean_text(src)
            self.assertIn(
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                [f.rule for f in findings],
            )

    def test_lean_syntactic_contradiction_simultaneous_pos_and_neg_hyps(self) -> None:
        src = "theorem t_both (x : Nat) (h1 : x = 5) (h2 : x ≠ 5) : x = 99 := False.elim (h2 h1)\n"
        findings = audit.scan_lean_text(src)
        self.assertIn(
            audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
            [f.rule for f in findings],
        )

    def test_lean_trivial_conclusion_true_and_reflexive_eq(self) -> None:
        f_true = audit.scan_lean_text("theorem bad_true (x : Nat) : True := trivial\n")
        self.assertIn(audit.RULE_TRIVIAL_CONCLUSION, [f.rule for f in f_true])

        f_refl = audit.scan_lean_text("theorem bad_refl (x : Nat) : x + 1 = x + 1 := rfl\n")
        self.assertIn(audit.RULE_TRIVIAL_CONCLUSION, [f.rule for f in f_refl])

    def test_lean_trivial_conclusion_helper_exemption(self) -> None:
        src_helper = (
            "/--\nKind: helper\nWitness: universal\nAssumes: S0\n-/\n"
            "theorem ok_helper (x : Nat) : x = x := rfl\n"
        )
        self.assertEqual(audit.scan_lean_text(src_helper), [])

    def test_lean_tautological_implication_detection(self) -> None:
        src = "theorem taut_imp (P Q : Prop) (hP : P) (hQ : Q) : P := hP\n"
        findings = audit.scan_lean_text(src)
        self.assertIn(audit.RULE_TAUTOLOGICAL_IMPLICATION, [f.rule for f in findings])

    def test_lean_unused_subject_explicit_and_bound_param(self) -> None:
        src_explicit = (
            "/--\n"
            "Kind: safety\n"
            "Witness: universal\n"
            "Assumes: S0\n"
            "Subject: evalDeinitPlace\n"
            "-/\n"
            "theorem disconnected_subject (n : Nat) (h : 0 < n) : 0 ≤ n := by omega\n"
        )
        f1 = audit.scan_lean_text(src_explicit)
        self.assertIn(audit.RULE_UNUSED_SUBJECT_IN_CONCLUSION, [f.rule for f in f1])

        src_bound = (
            "/--\n"
            "Kind: safety\n"
            "Witness: universal\n"
            "Assumes: S0\n"
            "-/\n"
            "theorem unused_param (body : MirBody) (n : Nat) (h : 0 < n) : 1 ≤ n := by omega\n"
        )
        f2 = audit.scan_lean_text(src_bound)
        self.assertIn(audit.RULE_UNUSED_SUBJECT_IN_CONCLUSION, [f.rule for f in f2])

    def test_lean_tier_assumption_mismatch_s0_with_pinned_rust_padding(self) -> None:
        src_s0_pad = (
            "/--\n"
            "Kind: safety\n"
            "Witness: universal\n"
            "Assumes: S0\n"
            "-/\n"
            "theorem bad_s0_pinned (fs : List FieldLayout) (hRepr : spec.repr = .rust)\n"
            "    (hPad : paddingFree 0 fs = true) : fs.length = fs.length + 0 := by omega\n"
        )
        f1 = audit.scan_lean_text(src_s0_pad)
        self.assertIn(audit.RULE_TIER_ASSUMPTION_MISMATCH, [f.rule for f in f1])

    def test_lean_tier_assumption_mismatch_s0_with_compile_time_guard(self) -> None:
        src_s0_cte = (
            "/--\n"
            "Kind: safety\n"
            "Witness: universal\n"
            "Assumes: S0\n"
            "-/\n"
            "theorem bad_s0_cte (w : SymbolicPairPad)\n"
            "    (h : evalConstGuard cond k ≠ .compileTimeError) : w.pad0 = 0 := by sorry\n"
        )
        f2 = audit.scan_lean_text(src_s0_cte)
        self.assertIn(audit.RULE_TIER_ASSUMPTION_MISMATCH, [f.rule for f in f2])

    def test_lean_tier_assumption_mismatch_invalid_witness_and_axes(self) -> None:
        for src in (
            "/--\nKind: safety\nWitness: vacuous\nAssumes: S0\n-/\n"
            "theorem bad_witness (n : Nat) : n ≤ n + 1 := by omega\n",
            "/--\nKind: safety\nWitness: exists-sat\nAssumes: S0\n-/\n"
            "theorem bad_exists (n : Nat) : n ≤ n + 1 := by omega\n",
            "/--\nKind: safety\nWitness: negative\nAssumes: S0\n-/\n"
            "theorem bad_neg (n : Nat) : n ≤ n + 1 := by omega\n",
            "/--\nKind: invalid_kind\nWitness: universal\nAssumes: S9\n-/\n"
            "theorem bad_axes (n : Nat) : n ≤ n + 1 := by omega\n",
        ):
            res = audit.scan_lean_text(src)
            self.assertIn(audit.RULE_TIER_ASSUMPTION_MISMATCH, [f.rule for f in res])


class TestCliBenchmarkAndLivePrototypeSelfAudit(unittest.TestCase):
    """Prototype CLI / benchmark / live self-audit tests, retargeted at the promoted
    `proof_health.py` CLI and at Episode 1's promoted Lean files (the prototype Lean file
    itself is not promoted)."""

    def test_cli_exit_codes_and_json_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            clean_p = Path(tmp) / "clean.lean"
            clean_p.write_text(
                "theorem ok_add (n : Nat) : n + 0 = n := Nat.add_zero n\n",
                encoding="utf-8",
            )
            bad_p = Path(tmp) / "bad.lean"
            bad_p.write_text(
                "theorem bad_vac (n : Nat) (h : 0 = 1) : n = 99 := by omega\n",
                encoding="utf-8",
            )

            buf = io.StringIO()
            with patch("sys.stdout", buf):
                rc_clean = proof_health.main(["--json", str(clean_p)])
            self.assertEqual(rc_clean, 0)
            payload_clean = json.loads(buf.getvalue())
            self.assertTrue(payload_clean["ok"])
            self.assertEqual(payload_clean["finding_count"], 0)

            buf_bad = io.StringIO()
            with patch("sys.stdout", buf_bad):
                rc_bad = proof_health.main(["--json", str(bad_p)])
            self.assertEqual(rc_bad, 1)
            payload_bad = json.loads(buf_bad.getvalue())
            self.assertFalse(payload_bad["ok"])
            self.assertEqual(payload_bad["finding_count"], 1)
            self.assertEqual(payload_bad["findings"][0]["rule"], proof_health.RULE_TRIVIAL_OR_VACUOUS_CLAIM)
            self.assertEqual(
                payload_bad["findings"][0]["subrule"],
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
            )

            err_buf = io.StringIO()
            with patch("sys.stderr", err_buf):
                rc_missing = proof_health.main([str(Path(tmp) / "nonexistent.lean")])
                rc_no_args = proof_health.main([])
                rc_bad_flag = proof_health.main(["--unknown-flag"])
            self.assertEqual(rc_missing, 2)
            self.assertEqual(rc_no_args, 2)
            self.assertEqual(rc_bad_flag, 2)

    def test_live_self_audit_on_episode1_lean_files(self) -> None:
        for path in (EPISODE1_BYTECODEC, EPISODE1_ADT_AND_CONTROL):
            self.assertTrue(path.is_file(), f"missing {path}")
            # Every theorem, every check (`vacuity_scope="all"`, the prototype default).
            self.assertEqual(audit.scan_file(path, check_3axis=True), [], path.name)
            self.assertEqual(proof_health.scan_lean_file(path), [], path.name)
            self.assertEqual(
                proof_health.scan_lean_file(path, include_unannotated_vacuity=True), [], path.name
            )

        pins = audit.compute_lean_decl_pins(EPISODE1_BYTECODEC.read_text(encoding="utf-8"))
        self.assertIn("pinnedZeroPadPair_isIntoBytes_and_transmute_sound", pins)
        pins = audit.compute_lean_decl_pins(EPISODE1_ADT_AND_CONTROL.read_text(encoding="utf-8"))
        self.assertIn("evalConst_size_eq_forces_zero_pad_and_intoBytes", pins)

    def test_sub_5ms_runtime_benchmark(self) -> None:
        text = EPISODE1_BYTECODEC.read_text(encoding="utf-8")
        n_lines = text.count("\n") + 1
        # Cold budgets scale with the single lexing pass every cold run starts with (timed the
        # same way), so a slower or loaded host inflates budget and measurement alike instead
        # of flaking: the flat 5 ms / 1.75 us/line targets apply wherever this file lexes in
        # under 5 / 3 ms, and anywhere a cold waiver pass may cost 3x and a cold full 3-axis
        # pass 10x the lexing pass (2.1x and 7.3x measured on a 2.2 GHz Xeon host, where
        # both flat targets are out of reach even for the unmodified auditor).
        lex_ms = best_of_ms(lambda: audit._scan_lean_comments_and_strings(text), budget_ms=0.0)
        # Cold waiver pass (every module cache cleared before each timed run, what a fresh CLI
        # process pays) over a file that does carry a waiver, so the `anneal:` fast path is off.
        waived = text + "\n/-- anneal:documented_intent benchmark waiver -/\ndef benchWaiver : Nat := 0\n"
        waiver_budget_ms = max(5.0, 3.0 * lex_ms)
        cold_waiver_ms = best_of_ms(
            lambda: (_clear_audit_caches(), audit.scan_lean_text(waived, check_3axis=False)),
            budget_ms=waiver_budget_ms,
        )
        self.assertLess(
            cold_waiver_ms,
            waiver_budget_ms,
            f"cold waiver-pin pass took {cold_waiver_ms:.2f} ms "
            f"(budget {waiver_budget_ms:.2f} ms, lexing {lex_ms:.2f} ms)",
        )
        # Warm/incremental (LSP keystroke) = re-scan after editing ONE theorem: exactly one
        # audit-cache miss per run (a fresh hypothesis each time), every other theorem a sound hit.
        anchor = "theorem scalarValidRange_isExactWidth (sz : Nat)"
        self.assertIn(anchor, text)
        counter = iter(range(10**6))

        def edited_scan() -> None:
            k = next(counter)
            audit.scan_lean_text(text.replace(anchor, f"{anchor} (hEdit{k} : {k} ≤ {k} + 1)", 1))

        warm_ms = best_of_ms(edited_scan, budget_ms=5.0)
        self.assertLess(warm_ms, 5.0, f"incremental full scan took {warm_ms:.2f} ms (expected < 5.0 ms)")
        # Cold full 3-axis scan: throughput regression guard (the flat `< 5 ms` holds warm, not
        # cold, on files of this size -- see PROTOTYPE_REPORT.md §3.4).
        cold_full_ms = best_of_ms(
            lambda: (_clear_audit_caches(), audit.scan_lean_text(text, check_3axis=True)), budget_ms=0.0
        )
        full_budget_us = max(1.75, 10.0 * lex_ms * 1000.0 / n_lines)
        self.assertLess(
            cold_full_ms * 1000.0 / n_lines,
            full_budget_us,
            f"cold full scan took {cold_full_ms:.2f} ms ({cold_full_ms * 1000.0 / n_lines:.2f} us/line, "
            f"budget {full_budget_us:.2f} us/line, lexing {lex_ms:.2f} ms)",
        )


def _clear_audit_caches() -> None:
    audit._LAST_LEAN_AUDIT.clear()
    audit._LAST_LEAN_SCAN.clear()
    audit._THM_AUDIT_CACHE.clear()
    audit._META_CACHE.clear()
    audit._NORM_CACHE.clear()


# ---------------------------------------------------------------------------
# [adv B1] spec.rs fidelity, directive-bound pins, lexer bypasses, Lean doc-only waivers
# ---------------------------------------------------------------------------


def _rules(findings: list) -> list[str]:
    return [f.rule for f in findings]


class TestB1SpecRsDirectiveFidelity(unittest.TestCase):
    """`b1f15f743c:trusted/rustc-capture/src/spec.rs` (`parse_doc`) grammar fidelity."""

    ITEM = "pub fn f(x: usize) -> usize { x }"

    def _scan(self, doc: str) -> list:
        return audit.scan_rust_text(f"{doc}\n{self.ITEM}\n")

    def test_inline_pin_on_allow_compile_time_guard_is_rejected_like_spec_rs(self) -> None:
        res = self._scan("/// anneal:allow_compile_time_guard pin:sha256:0123456789ab")
        self.assertEqual(_rules(res), [audit.RULE_INVALID_WAIVER_SYNTAX])
        self.assertIn("entire doc line", res[0].message)
        self.assertIn("pin:sha256:", res[0].suggestion)

    def test_inline_pin_after_trusted_reason_is_rejected_like_spec_rs(self) -> None:
        res = self._scan('/// anneal:trusted reason = "MMIO" pin:sha256:0123456789ab')
        self.assertEqual(_rules(res), [audit.RULE_INVALID_WAIVER_SYNTAX])
        self.assertIn("breaks the spec.rs grammar", res[0].message)

    def test_allow_compile_time_guard_accepts_no_rationale_or_reason(self) -> None:
        for doc in (
            '/// anneal:allow_compile_time_guard reason = "size guard"',
            "/// anneal:allow_compile_time_guard because the const assert prunes padding",
        ):
            self.assertEqual(_rules(self._scan(doc)), [audit.RULE_INVALID_WAIVER_SYNTAX], doc)

    def test_free_form_rationale_uses_untrimmed_strip_prefix(self) -> None:
        # spec.rs strips `documented_intent` from the *untrimmed* remainder, so a space after
        # `anneal:` falls through to the structured lexer and is rejected.
        self.assertEqual(
            _rules(self._scan("/// anneal: documented_intent Upstream RFC 1234")),
            [audit.RULE_INVALID_WAIVER_SYNTAX],
        )
        # `anneal: allow_compile_time_guard` IS accepted (spec.rs trims for that comparison).
        self.assertEqual(
            _rules(self._scan("/// anneal: allow_compile_time_guard")), [audit.RULE_UNPINNED_WAIVER]
        )

    def test_structured_lexer_is_ascii_only_and_u128_bounded(self) -> None:
        for doc in (
            "/// anneal:requires x != ٣",  # Arabic-Indic digit: Python isdigit() but not ASCII
            "/// anneal:requires é != 0",  # non-ASCII identifier
            "/// anneal:requires x != 340282366920938463463374607431768211456",  # u128::MAX + 1
        ):
            self.assertEqual(_rules(self._scan(doc)), [audit.RULE_INVALID_WAIVER_SYNTAX], doc)
        self.assertEqual(self._scan("/// anneal:requires x != 340282366920938463463374607431768211455"), [])

    def test_valid_non_waiver_directives_need_no_pin(self) -> None:
        self.assertEqual(self._scan("/// anneal:requires x != 0\n/// anneal:spec well_formed"), [])


class TestB1DirectiveBoundPins(unittest.TestCase):
    """The pin binds the doc block's directives as well as the item."""

    ITEM = "pub fn layout_dependent(p: (u16, u16)) -> u32 { (p.0 as u32) | ((p.1 as u32) << 16) }"

    def test_tier_swap_with_unchanged_pin_is_drift(self) -> None:
        pinned = pin_rust_snippet("/// anneal:documented_intent Upstream layout RFC", self.ITEM)
        self.assertEqual(audit.scan_rust_text(pinned), [])
        swapped = pinned.replace("anneal:documented_intent", "anneal:pinned_compiler_coupled")
        res = audit.scan_rust_text(swapped)
        self.assertEqual(_rules(res), [audit.RULE_DRIFTED_WAIVER_PIN])
        self.assertEqual(res[0].tier, "S3")

    def test_adding_a_waiver_to_a_pinned_block_is_drift(self) -> None:
        pinned = pin_rust_snippet("/// anneal:documented_intent Upstream layout RFC", self.ITEM)
        escalated = "/// anneal:allow_compile_time_guard\n" + pinned
        self.assertEqual(
            sorted(_rules(audit.scan_rust_text(escalated))), [audit.RULE_DRIFTED_WAIVER_PIN] * 2
        )

    def test_trusted_reason_edit_is_drift_but_prose_edit_is_not(self) -> None:
        pinned = pin_rust_snippet(
            '/// Reads a register.\n/// anneal:trusted reason = "MMIO volatile read"', self.ITEM
        )
        self.assertEqual(audit.scan_rust_text(pinned), [])
        self.assertEqual(
            _rules(audit.scan_rust_text(pinned.replace("volatile read", "plain read"))),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )
        self.assertEqual(
            audit.scan_rust_text(pinned.replace("Reads a register.", "Reads a 32-bit register.")), []
        )

    def test_doc_comment_and_doc_attribute_forms_hash_identically(self) -> None:
        pinned = pin_rust_snippet("/// anneal:documented_intent Upstream layout RFC", self.ITEM)
        as_attr = pinned.replace(
            "/// anneal:documented_intent Upstream layout RFC",
            '#[doc = "anneal:documented_intent   Upstream layout RFC"]',
        )
        self.assertEqual(audit.scan_rust_text(as_attr), [])


class TestB1RustLexerAndSpanBypasses(unittest.TestCase):
    def test_escaped_quote_char_literals_do_not_desync_normalization(self) -> None:
        item = (
            "pub fn quotes(x: u8) -> (char, char, u8, u8) {\n"
            "    let a = '\\'';\n"
            "    let b = '\"';\n"
            "    let c = b'\"';\n"
            "    (a, b, c, x)\n"
            "}"
        )
        pinned = pin_rust_snippet('/// anneal:trusted reason = "quote-heavy literals"', item)
        self.assertEqual(audit.scan_rust_text(pinned), [])
        # Whitespace-only edits after a `'"'` literal must keep the pin...
        self.assertEqual(audit.scan_rust_text(pinned.replace("(a, b, c, x)", "( a , b , c , x )")), [])
        # ...while a real edit after it must break the pin.
        self.assertEqual(
            _rules(audit.scan_rust_text(pinned.replace("(a, b, c, x)", "(a, b, c, x + 1)"))),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

    def test_const_generic_block_in_signature_does_not_truncate_the_pinned_span(self) -> None:
        item = (
            "pub fn sized() -> Wrapper<{ SIZE }> {\n"
            "    unsafe { core::mem::transmute(make()) }\n"
            "}"
        )
        pinned = pin_rust_snippet("/// anneal:allow_compile_time_guard", item)
        self.assertEqual(audit.scan_rust_text(pinned), [])
        self.assertEqual(
            _rules(audit.scan_rust_text(pinned.replace("make()", "make_other()"))),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

    def test_struct_literal_initializer_tail_stays_inside_const_and_type_spans(self) -> None:
        const_item = "pub const CFG: Config = Config { mode: 1 }.with_padding(2);"
        pinned = pin_rust_snippet("/// anneal:pinned_compiler_coupled pinned config", const_item)
        self.assertEqual(audit.scan_rust_text(pinned), [])
        self.assertEqual(
            _rules(audit.scan_rust_text(pinned.replace("with_padding(2)", "with_padding(3)"))),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )
        type_item = "pub type Buf = Wrapper<{ N }, u8>;"
        pinned_t = pin_rust_snippet("/// anneal:documented_intent alias layout", type_item)
        self.assertEqual(audit.scan_rust_text(pinned_t), [])
        self.assertEqual(
            _rules(audit.scan_rust_text(pinned_t.replace("u8>", "u16>"))),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

    def test_hex_escaped_doc_attribute_cannot_hide_a_waiver(self) -> None:
        src = '#[doc = "anneal\\x3atrusted reason = \\"hidden\\""]\npub fn f() {}\n'
        self.assertNotIn("anneal:", src)
        self.assertEqual(_rules(audit.scan_rust_text(src)), [audit.RULE_UNPINNED_WAIVER])

    def test_computed_doc_attributes_are_flagged_unauditable(self) -> None:
        for attr in (
            '#[cfg_attr(all(), doc = "anneal:trusted reason = \\"x\\"")]',
            '#[doc = concat!("anneal:", "trusted reason = \\"x\\"")]',
            '#[doc = include_str!("waivers.md")]',
        ):
            res = audit.scan_rust_text(f"{attr}\npub fn f() {{}}\n")
            self.assertEqual(_rules(res), [audit.RULE_INVALID_WAIVER_SYNTAX], attr)
        # Semantic `doc(...)` attributes are not doc text, and `#[doc = #var]` inside a
        # proc-macro `quote!` body is a token template, not an attribute: both stay unflagged.
        self.assertEqual(audit.scan_rust_text("#[doc(hidden)]\npub fn f() {}\n"), [])
        self.assertEqual(
            audit.scan_rust_text("fn gen() -> T { quote! { #[doc = #marker] pub fn g() {} } }\n"), []
        )

    def test_inner_doc_directives_are_dangling(self) -> None:
        for src in (
            '//! anneal:trusted reason = "crate-level"\npub fn f() {}\n',
            '#![doc = "anneal:allow_compile_time_guard"]\npub fn f() {}\n',
        ):
            self.assertEqual(_rules(audit.scan_rust_text(src)), [audit.RULE_DANGLING_WAIVER], src)


class TestB1LeanDocstringOnlyWaiversAndWhitespaceSemantics(unittest.TestCase):
    def test_plain_lean_comments_never_carry_waivers(self) -> None:
        src = (
            "-- anneal:trusted reason = \"line comment\"\n"
            "/- anneal:allow_compile_time_guard -/\n"
            "theorem plain_comments (n : Nat) : n + 0 = n := Nat.add_zero n\n"
        )
        self.assertEqual(audit.scan_lean_text(src), [])

    def test_module_docstring_directive_is_dangling(self) -> None:
        src = "/-! anneal:pinned_compiler_coupled module-wide -/\ndef x : Nat := 1\n"
        self.assertEqual(_rules(audit.scan_lean_text(src)), [audit.RULE_DANGLING_WAIVER])

    def _pinned(self, decl: str) -> str:
        return pin_lean_decl(["anneal:documented_intent Lean whitespace semantics"], decl)

    def test_index_vs_application_whitespace_is_semantic(self) -> None:
        pinned = self._pinned("def pick (xs : Array Nat) (i : Nat) : Nat := xs[i]!\n")
        self.assertEqual(audit.scan_lean_text(pinned), [])
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned.replace("xs[i]!", "xs [i]!"))),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

    def test_projection_vs_leading_dot_whitespace_is_semantic(self) -> None:
        pinned = self._pinned("def proj (f : Nat → Nat) (x : Nat × Nat) : Nat := f x.1\n")
        self.assertEqual(audit.scan_lean_text(pinned), [])
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned.replace("f x.1", "f x .1"))),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

    def test_tactic_indentation_is_semantic_but_trailing_comments_are_not(self) -> None:
        decl = (
            "theorem indent_demo (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n"
            "  refine ⟨?_, ?_⟩\n"
            "  · exact hp\n"
            "  · exact hq\n"
        )
        pinned = self._pinned(decl)
        self.assertEqual(audit.scan_lean_text(pinned), [])
        self.assertEqual(
            audit.scan_lean_text(pinned.replace("exact hp\n", "exact hp -- left conjunct\n")), []
        )
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned.replace("  · exact hq\n", "    · exact hq\n"))),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

    def test_column_zero_where_block_is_part_of_the_pinned_declaration(self) -> None:
        decl = "def outer : Nat := helper + 1\nwhere\n  helper : Nat := 41\n"
        pinned = self._pinned(decl)
        self.assertEqual(audit.scan_lean_text(pinned), [])
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned.replace(":= 41", ":= 42"))),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

    def test_lean_quote_char_literal_keeps_whitespace_normalization_in_sync(self) -> None:
        decl = "def quoteChar : Char × Nat := ('\"', 1 + 2)\n"
        pinned = self._pinned(decl)
        self.assertEqual(audit.scan_lean_text(pinned), [])
        self.assertEqual(audit.scan_lean_text(pinned.replace("1 + 2", "1  +  2")), [])
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned.replace("1 + 2", "1 + 3"))),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )


class TestB1ThreeAxisHardening(unittest.TestCase):
    def test_conflicting_duplicate_axis_lines_are_flagged(self) -> None:
        src = (
            "/--\nKind: safety\nWitness: universal\nAssumes: S0\nKind: helper\n-/\n"
            "theorem sneaky (x : Nat) : x = x := rfl\n"
        )
        self.assertIn(audit.RULE_TIER_ASSUMPTION_MISMATCH, _rules(audit.scan_lean_text(src)))

    def test_conjunction_of_trivial_facts_is_a_trivial_conclusion(self) -> None:
        for conc in ("True ∧ x = x", "x + 1 = x + 1 ∧ (p ↔ p)", "¬ False ∧ x ≤ x"):
            src = f"theorem padded_triv (x : Nat) (p : Prop) : {conc} := by simp\n"
            self.assertIn(audit.RULE_TRIVIAL_CONCLUSION, _rules(audit.scan_lean_text(src)), conc)
        self.assertNotIn(
            audit.RULE_TRIVIAL_CONCLUSION,
            _rules(audit.scan_lean_text("theorem real (x : Nat) : x = x ∧ x < x + 1 := by omega\n")),
        )

    def test_int_negative_bound_is_not_a_contradiction(self) -> None:
        src = "theorem neg_int (x : Int) (h : x < 0) : x ≤ -1 := by omega\n"
        self.assertNotIn(audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS, _rules(audit.scan_lean_text(src)))
        src_nat = "theorem neg_nat (x : Nat) (h : x < 0) : x = 7 := by omega\n"
        self.assertIn(audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS, _rules(audit.scan_lean_text(src_nat)))

    def test_struct_literal_canonical_order_pin_on_s0_is_a_tier_mismatch(self) -> None:
        src = (
            "/--\nKind: safety\nWitness: universal\nAssumes: S0\n-/\n"
            "theorem reprRust_literal_pin (fs : List FieldLayout)\n"
            "    (hWF : ({ shape := .struct fs, repr := .rust, reprAlign := none,\n"
            "              rustOrderCanonical := true } : AdtLayoutSpec).WF) :\n"
            "    fs.length = fs.length + 0 := by omega\n"
        )
        self.assertIn(audit.RULE_TIER_ASSUMPTION_MISMATCH, _rules(audit.scan_lean_text(src)))


# ---------------------------------------------------------------------------
# [adv A1] Rust attribute whitespace/string-bracket bypasses, angle-depth `<<`/`<=`,
#          Lean multi-attribute/modifier 3-axis lookup, disjunctive & inequality vacuity
# ---------------------------------------------------------------------------


class TestA1AdversarialHardening(unittest.TestCase):
    def test_rust_spaced_hash_bracket_doc_and_inner_doc_attributes(self) -> None:
        outer_spaced = '# [doc = "anneal:trusted reason = \\"spaced hash\\""]\npub fn f() {}\n'
        self.assertEqual(_rules(audit.scan_rust_text(outer_spaced)), [audit.RULE_UNPINNED_WAIVER])
        inner_spaced = '# ! [doc = "anneal:allow_compile_time_guard"]\npub fn f() {}\n'
        self.assertEqual(_rules(audit.scan_rust_text(inner_spaced)), [audit.RULE_DANGLING_WAIVER])
        computed_spaced = '#\n[doc = include_str!("waiver.md")]\npub fn f() {}\n'
        self.assertEqual(_rules(audit.scan_rust_text(computed_spaced)), [audit.RULE_INVALID_WAIVER_SYNTAX])

    def test_rust_preceding_attribute_with_brackets_inside_string_literal(self) -> None:
        item = "pub struct S { pub a: u8, pub b: u32 }"
        pre_attrs = '#[repr(C)]\n#[deprecated(note = "use foo[0] or bar[1")]\n'
        doc = "/// anneal:pinned_compiler_coupled C ABI layout"
        anns, _ = audit._collect_block_directives([(1, "anneal:pinned_compiler_coupled C ABI layout")])
        norm = audit._normalize_rust_item(pre_attrs + "\n" + item)
        pin = audit.format_pin_tag(audit.compute_sha256_pin12(audit.waiver_hash_input(anns, norm)))
        full = f"{pre_attrs}{doc}\n/// {pin}\n{item}\n"
        self.assertEqual(audit.scan_rust_text(full), [])
        # Mutating `#[repr(C)]` above `#[deprecated(note = "use foo[0] or bar[1")]` MUST break the pin!
        mutated = full.replace("#[repr(C)]", "#[repr(Rust)]")
        self.assertEqual(_rules(audit.scan_rust_text(mutated)), [audit.RULE_DRIFTED_WAIVER_PIN])

    def test_rust_where_clause_shift_and_le_operators_do_not_desync_angle_depth(self) -> None:
        item = (
            "pub fn shifted<const N: usize>(x: u32) -> u32\n"
            "where\n"
            "    [(); 1 << N]: Sized,\n"
            "    [(); (N <= 4) as usize]: Sized,\n"
            "{\n"
            "    x + 1\n"
            "}"
        )
        pinned = pin_rust_snippet("/// anneal:allow_compile_time_guard", item)
        self.assertEqual(audit.scan_rust_text(pinned), [])
        self.assertEqual(
            _rules(audit.scan_rust_text(pinned.replace("x + 1", "x + 2"))),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

    def test_rust_raw_identifier_item_names_extracted(self) -> None:
        item = "pub fn r#try(x: u8) -> u8 { x }"
        pinned = pin_rust_snippet("/// anneal:documented_intent raw ident fn", item)
        self.assertEqual(audit.scan_rust_text(pinned), [])
        pins = audit.compute_rust_item_pins(pinned)
        self.assertIn("r#try", pins)

    def test_lean_multi_attribute_and_modifier_lines_preserve_3axis_metadata(self) -> None:
        src = (
            "/--\n"
            "Kind: safety\n"
            "Witness: exists-sat\n"
            "Assumes: S0\n"
            "-/\n"
            "@[simp]\n"
            "@[nolint unusedArguments]\n"
            "private\n"
            "theorem multi_attr_bad_exists (n : Nat) : n ≤ n + 1 := by omega\n"
        )
        self.assertIn(audit.RULE_TIER_ASSUMPTION_MISMATCH, _rules(audit.scan_lean_text(src)))

    def test_lean_disjunctive_and_standalone_reflexive_trivial_conclusions(self) -> None:
        for conc in (
            "x ≤ x",
            "p ↔ p",
            "p ∨ True",
            "True ∨ p",
            "x = x ∨ p",
            "p ∨ ¬ False",
        ):
            src = f"theorem triv_conc (x : Nat) (p : Prop) : {conc} := by sorry\n"
            self.assertIn(audit.RULE_TRIVIAL_CONCLUSION, _rules(audit.scan_lean_text(src)), conc)
        # Non-trivial disjunction must NOT be flagged
        clean_or = "theorem real_or (x : Nat) : x = 0 ∨ 0 < x := by omega\n"
        self.assertEqual(audit.scan_lean_text(clean_or), [])

    def test_lean_numeric_inequality_and_constructor_contradictions(self) -> None:
        for hyp in (
            "5 < 3",
            "3 < 3",
            "5 ≤ 3",
            "3 > 5",
            "x > x",
            "0 > x",
            "¬ True",
            "[] = x :: xs",
            "[x] = []",
            "Sum.inl x = Sum.inr y",
            "Except.ok x = Except.error y",
        ):
            src = f"theorem bad_hyp (x y : Nat) (xs : List Nat) (h : {hyp}) : x = 42 := by sorry\n"
            self.assertIn(
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                _rules(audit.scan_lean_text(src)),
                hyp,
            )


# ---------------------------------------------------------------------------
# [adv B2] Cross-scan audit-cache soundness, parse clamping, and `∧`/`∨` precedence
# ---------------------------------------------------------------------------


class TestB2AuditCacheSoundnessAndPrecedence(unittest.TestCase):
    """A1 made `_THM_AUDIT_CACHE` survive across scans but keyed it on the header text truncated
    at the first `:=`, which can sit inside a binder's structure literal: later edits to the
    conclusion or to a later hypothesis then hit a stale entry (false negatives in one process)."""

    def test_struct_literal_binder_edit_to_conclusion_is_not_served_stale(self) -> None:
        v1 = "theorem t (h : ({ a := 1 } : Foo).P) : x = 1 := sorry\n"
        v2 = "theorem t (h : ({ a := 1 } : Foo).P) : True := sorry\n"
        self.assertEqual(audit.scan_lean_text(v1), [])
        self.assertEqual(_rules(audit.scan_lean_text(v2)), [audit.RULE_TRIVIAL_CONCLUSION])

    def test_struct_literal_binder_edit_to_later_hypothesis_is_not_served_stale(self) -> None:
        w1 = "theorem u (s : ({ k := 0 } : S).Q) (h : 0 < 1) : y = 2 := sorry\n"
        w2 = "theorem u (s : ({ k := 0 } : S).Q) (h : 1 = 2) : y = 2 := sorry\n"
        self.assertEqual(audit.scan_lean_text(w1), [])
        self.assertEqual(
            _rules(audit.scan_lean_text(w2)), [audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS]
        )

    def test_header_parse_never_reads_past_the_next_theorem(self) -> None:
        # A body-less statement used to run (via `_find_lean_decl_end`) into the indented next
        # theorem, hiding `x = x` and making `t1`'s result depend on text outside its cache key.
        for t2_conc in ("y = 3", "y = 4", "True"):
            src = f"theorem t1 : x = x\n  theorem t2 : {t2_conc} := trivial\n"
            findings = audit.scan_lean_text(src)
            t1_rules = [f.rule for f in findings if f.symbol == "t1"]
            self.assertEqual(t1_rules, [audit.RULE_TRIVIAL_CONCLUSION], t2_conc)

    def test_cached_findings_track_shifted_line_numbers(self) -> None:
        src = "theorem bad (h : False) : 1 = 2 := sorry\n"
        first = audit.scan_lean_text(src)
        shifted = audit.scan_lean_text("\n\n\n" + src)
        self.assertEqual([f.line for f in first], [1])
        self.assertEqual([f.line for f in shifted], [4])
        self.assertEqual(_rules(first), _rules(shifted))

    def test_metadata_edit_invalidates_cached_audit(self) -> None:
        base = "theorem m (n : Nat) : ∃ k, k = n := ⟨n, rfl⟩\n"
        good = "/--\nKind: refinement\nWitness: exists-sat\nAssumes: S0\n-/\n" + base
        bad = "/--\nKind: refinement\nWitness: negative\nAssumes: S0\n-/\n" + base
        self.assertEqual(audit.scan_lean_text(good), [])
        self.assertEqual(_rules(audit.scan_lean_text(bad)), [audit.RULE_TIER_ASSUMPTION_MISMATCH])

    def test_looser_connectives_and_binders_do_not_fake_a_top_level_disjunction(self) -> None:
        # `↔` (20) and `→` (25) bind looser than `∨` (30) / `∧` (35); binder bodies extend right.
        for conc in (
            "p ↔ q ∨ True",
            "x = x ∨ p ↔ q",
            "p ↔ x = x ∧ True",
            "f = fun y => y ∨ True",
            "∃ y : Nat, y = y ∨ p",
            "g <| p ∨ True",
        ):
            src = f"theorem prec (p q : Prop) (x : Nat) (f g : Prop → Prop) : {conc} := sorry\n"
            self.assertNotIn(audit.RULE_TRIVIAL_CONCLUSION, _rules(audit.scan_lean_text(src)), conc)
        for conc in ("p ∨ True", "(p ↔ q) ∨ True", "x = x ∧ (p → p) = (p → p)", "(fun y => y) = (fun y => y)"):
            src = f"theorem prec (p q : Prop) (x : Nat) : {conc} := sorry\n"
            self.assertIn(audit.RULE_TRIVIAL_CONCLUSION, _rules(audit.scan_lean_text(src)), conc)

    def test_negative_bound_rule_fires_only_on_nat_valued_operands(self) -> None:
        # A0-A1 flagged every `e < 0` / `0 > e` whose operand was not a declared `Int` binder.
        for binders, hyp in (
            ("(x : Real)", "x < 0"),
            ("(f : Nat → Int)", "f 0 < 0"),
            ("(z : ℚ)", "0 > z"),
            ("(n : Nat) (g : Nat → Int)", "g n < 0"),
        ):
            src = f"theorem nb {binders} (h : {hyp}) (w : Nat) : w = w + 0 := by omega\n"
            self.assertNotIn(
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS, _rules(audit.scan_lean_text(src)), hyp
            )
        for binders, hyp in (
            ("(xs : List Nat)", "xs.length < 0"),
            ("(i : Fin 4)", "i < 0"),
            ("{n : ℕ}", "0 > n"),
            ("(u : UInt32)", "u < 0"),
        ):
            src = f"theorem nb {binders} (h : {hyp}) (w : Nat) : w = w + 0 := by omega\n"
            self.assertIn(
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS, _rules(audit.scan_lean_text(src)), hyp
            )


    def test_nested_bracket_attribute_waiver_is_pinned_not_dangling(self) -> None:
        decl = "@[aesop safe [constructors]]\ntheorem nestedAttr : 1 + 1 = 2 := rfl\n"
        doc = "/--\nanneal:documented_intent nested attribute arguments\n"
        pin_tag = audit.compute_lean_decl_pins(f"{doc}-/\n{decl}")["nestedAttr"]
        pinned = f"{doc}{pin_tag}\n-/\n{decl}"
        self.assertEqual(audit.scan_lean_text(pinned, check_3axis=False), [])
        for old, new in (("1 + 1 = 2", "2 + 0 = 2"), ("[constructors]", "[cases]")):
            self.assertEqual(
                _rules(audit.scan_lean_text(pinned.replace(old, new), check_3axis=False)),
                [audit.RULE_DRIFTED_WAIVER_PIN],
                old,
            )


# ---------------------------------------------------------------------------
# [adv A2] Prefix-binder scope vs. looser infix precedence, compound Nat bounds,
# and indented namespace/section declaration boundaries
# ---------------------------------------------------------------------------


class TestA2AdversarialHardening(unittest.TestCase):
    def test_prefix_binder_after_top_level_or_and_is_caught_not_suppressed(self) -> None:
        # B2's `_has_looser_top_level_structure` returned True whenever `∀`, `∃`, `fun`, `if`, or
        # `match` appeared anywhere at depth 0, missing `True ∨ ∀ x, P x` (provable by `Or.inl trivial`)
        # and `True ∧ ∀ x, x = x` (provable by `⟨trivial, fun _ => rfl⟩`).
        for conc in (
            "True ∨ ∀ y : Nat, P y",
            "x = x ∨ ∃ y : Nat, y > x",
            "True ∨ if c then P x else P 0",
            "¬ False ∨ match x with | 0 => P 0 | n + 1 => P n",
            "True ∧ ∀ y : Nat, y = y",
            "x = x ∧ ∀ (a b : Nat), a + b = a + b",
            "∀ y : Nat, y = y",
        ):
            src = (
                "/--\nKind: safety\nWitness: universal\nAssumes: S0\nSubject: P\n-/\n"
                f"theorem t_triv (P : Nat → Prop) (c : Bool) (x : Nat) : {conc} := by sorry\n"
            )
            self.assertIn(
                audit.RULE_TRIVIAL_CONCLUSION,
                _rules(audit.scan_lean_text(src)),
                conc,
            )
        # Non-trivial right-hand universal conjunct or prefix binder / looser `↔` before `∨` must NOT be flagged:
        for conc in (
            "True ∧ ∀ y : Nat, P y",
            "∃ y : Nat, y = y ∨ P y",
            "P x ↔ ∀ y : Nat, y = y ∨ P y",
        ):
            src = (
                "/--\nKind: safety\nWitness: universal\nAssumes: S0\nSubject: P\n-/\n"
                f"theorem t_ok (P : Nat → Prop) (x : Nat) : {conc} := by sorry\n"
            )
            self.assertNotIn(
                audit.RULE_TRIVIAL_CONCLUSION,
                _rules(audit.scan_lean_text(src)),
                conc,
            )

    def test_compound_nat_expressions_and_domain_projections_in_negative_bounds(self) -> None:
        for binders, hyp in (
            ("(n m : Nat)", "n + m < 0"),
            ("(n : Nat)", "n + 1 < 0"),
            ("(xs : List Nat)", "xs.length + 1 < 0"),
            ("(w : SymbolicPairPad)", "w.totalPad < 0"),
            ("(w : StructLayoutWorld)", "w.totalSize < 0"),
            ("(fs : List FieldLayout)", "0 > sumSizes fs"),
            ("(n : Nat)", "0 > n * 2 + 1"),
        ):
            src = f"theorem bad_nat {binders} (h : {hyp}) (k : Nat) : k = k + 0 := by omega\n"
            self.assertIn(
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                _rules(audit.scan_lean_text(src)),
                hyp,
            )
        for binders, hyp in (
            ("(x : Int)", "x + 1 < 0"),
            ("(f : Nat → Int)", "f 0 + 1 < 0"),
            ("(x y : Real)", "x + y < 0"),
        ):
            src = f"theorem ok_signed {binders} (h : {hyp}) (k : Nat) : k = k + 0 := by omega\n"
            self.assertNotIn(
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                _rules(audit.scan_lean_text(src)),
                hyp,
            )

    def test_indented_namespace_declarations_do_not_merge_into_pinned_span(self) -> None:
        draft = (
            "namespace IndentedTest\n"
            "  /--\n"
            "  anneal:allow_compile_time_guard\n"
            "  -/\n"
            "  def guardedFn (x : Nat) : Nat := x + 1\n\n"
            "  def siblingHelper (y : Nat) : Nat := y + 2\n"
            "end IndentedTest\n"
        )
        pins = audit.compute_lean_decl_pins(draft)
        self.assertIn("guardedFn", pins)
        self.assertIn("siblingHelper", pins)
        pinned = draft.replace(
            "  anneal:allow_compile_time_guard\n",
            f"  anneal:allow_compile_time_guard\n  {pins['guardedFn']}\n",
        )
        self.assertEqual(audit.scan_lean_text(pinned, check_3axis=False), [])
        # Editing `siblingHelper` or `end IndentedTest` must NOT break `guardedFn`'s pin:
        edited_sibling = pinned.replace("y + 2", "y + 99")
        self.assertEqual(audit.scan_lean_text(edited_sibling, check_3axis=False), [])
        # Editing `guardedFn` itself MUST trigger `RULE_DRIFTED_WAIVER_PIN`:
        edited_target = pinned.replace("x + 1", "x + 99")
        self.assertEqual(
            _rules(audit.scan_lean_text(edited_target, check_3axis=False)),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )


# ---------------------------------------------------------------------------
# [adv B3] Indented-boundary pin bypasses and generic-projection `Nat` false positives
# ---------------------------------------------------------------------------


def _pin_lean_named(doc_line: str, decl: str, name: str) -> str:
    doc = f"/--\n{doc_line}\n"
    pin_tag = audit.compute_lean_decl_pins(f"{doc}-/\n{decl}")[name]
    return f"{doc}{pin_tag}\n-/\n{decl}"


class TestB3IndentedBoundariesAndNatProjections(unittest.TestCase):
    def test_indented_modifier_fields_and_where_attributes_stay_in_the_pinned_span(self) -> None:
        # A2 ended a declaration at ANY indented `private`/`protected`/`@[` line, so the fields
        # after `protected b` (or a `where` auxiliary's body) fell outside the pin: edits there
        # were silently accepted.
        for decl, name, old, new in (
            ("structure S where\n  a : Nat\n  protected b : Nat\n  c : Nat\n", "S", "c : Nat", "c : Int"),
            (
                "class C (α : Type) where\n  op : α → α\n  private aux : α\n  law : ∀ x, op x = x\n",
                "C",
                "op x = x",
                "op x = op x",
            ),
            (
                "theorem w : 1 = 1 := by\n  exact aux\nwhere\n  @[simp] aux : 1 = 1 := rfl\n",
                "w",
                ":= rfl",
                ":= by rfl",
            ),
        ):
            pinned = _pin_lean_named("anneal:documented_intent indented members", decl, name)
            self.assertEqual(audit.scan_lean_text(pinned, check_3axis=False), [], name)
            self.assertEqual(
                _rules(audit.scan_lean_text(pinned.replace(old, new), check_3axis=False)),
                [audit.RULE_DRIFTED_WAIVER_PIN],
                name,
            )

    def test_indented_sibling_commands_behind_modifiers_still_end_the_span(self) -> None:
        src_tpl = (
            "namespace Foo\n  /--\n  anneal:documented_intent demo\n  PIN\n  -/\n  def pinned : Nat := 1\n"
            "  private def sibling : Nat := 2\n  @[simp] theorem sib2 : sibling = 2 := rfl\n"
            "  #check sibling\nend Foo\n"
        )
        tag = audit.compute_lean_decl_pins(src_tpl.replace("  PIN\n", ""))["pinned"]
        src = src_tpl.replace("PIN", tag)
        self.assertEqual(audit.scan_lean_text(src, check_3axis=False), [])
        for old, new in ((":= 2", ":= 3"), ("sibling = 2", "sibling = 3"), ("#check sibling", "#check pinned")):
            self.assertEqual(audit.scan_lean_text(src.replace(old, new), check_3axis=False), [], old)
        self.assertEqual(
            _rules(audit.scan_lean_text(src.replace(":= 1", ":= 5"), check_3axis=False)),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

    def test_generic_fst_and_val_projections_are_not_nat_valued(self) -> None:
        for binders, hyp in (
            ("(p : Int × Nat)", "p.fst < 0"),
            ("(x : {z : Int // z < 5})", "x.val < 0"),
            ("(q : Int × Int)", "0 > q.fst"),
        ):
            src = f"theorem nb {binders} (h : {hyp}) (w : Nat) : w = w + 0 := by omega\n"
            self.assertNotIn(
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS, _rules(audit.scan_lean_text(src)), hyp
            )
        src = "theorem nb (n m : Nat) (h : n + m < 0) (w : Nat) : w = w + 0 := by omega\n"
        self.assertIn(audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS, _rules(audit.scan_lean_text(src)))


# ---------------------------------------------------------------------------
# [adv A3] Indented `decl_indent` boundaries with nested-bracket / multi-line
# attributes, `where` `def` auxiliaries, and quantified conjunctive/disjunctive conclusions
# ---------------------------------------------------------------------------


class TestA3AdversarialHardening(unittest.TestCase):
    def test_indented_namespace_sibling_with_nested_bracket_or_multiline_attribute(self) -> None:
        # B3's `(?:@\[[^\n]*?\][ \t]*)*` boundary regex stopped at the first `]` in nested
        # `@[aesop safe [constructors]] def sib1` and failed on multi-line `  @[simp]\n  def sib2`,
        # merging `sib1` or `  @[simp]` into `pinned`'s span.
        src_tpl = (
            "namespace Foo\n"
            "  /--\n"
            "  anneal:documented_intent demo\n"
            "  PIN1\n"
            "  -/\n"
            "  def pinned : Nat := 1\n"
            "  @[aesop safe [constructors]] def sib1 : Nat := 2\n"
            "  /--\n"
            "  anneal:documented_intent sib2-doc\n"
            "  PIN2\n"
            "  -/\n"
            "  @[simp]\n"
            "  def sib2 : Nat := 3\n"
            "end Foo\n"
        )
        pins = audit.compute_lean_decl_pins(src_tpl.replace("  PIN1\n", "").replace("  PIN2\n", ""))
        self.assertIn("pinned", pins)
        self.assertIn("sib1", pins)
        self.assertIn("sib2", pins)
        src = src_tpl.replace("PIN1", pins["pinned"]).replace("PIN2", pins["sib2"])
        self.assertEqual(audit.scan_lean_text(src, check_3axis=False), [])
        # Editing `sib1` must NOT break `pinned`'s pin:
        self.assertEqual(
            audit.scan_lean_text(src.replace("sib1 : Nat := 2", "sib1 : Nat := 99"), check_3axis=False),
            [],
        )
        # Editing `sib2`'s `@[simp]` attribute must break `sib2`'s pin, NOT `pinned`'s pin:
        drift_sib2 = audit.scan_lean_text(src.replace("@[simp]", "@[inline]"), check_3axis=False)
        self.assertEqual([(f.symbol, f.rule) for f in drift_sib2], [("sib2", audit.RULE_DRIFTED_WAIVER_PIN)])

    def test_where_auxiliary_with_def_keyword_stays_inside_pinned_span(self) -> None:
        # B3's `_LEAN_TOPLEVEL_BOUNDARY_RE` matched any indented `def` keyword regardless of
        # whether its indentation exceeded `decl_indent`, cutting `where\n  def aux` out of the pin.
        decl = "def parentFn (x : Nat) : Nat :=\n  aux x\nwhere\n  def aux (n : Nat) : Nat := n + 1\n"
        pinned = _pin_lean_named("anneal:documented_intent where-def", decl, "parentFn")
        self.assertEqual(audit.scan_lean_text(pinned, check_3axis=False), [])
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned.replace("n + 1", "n + 99"), check_3axis=False)),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

    def test_universal_quantifier_wrapping_conjunctive_or_disjunctive_trivial_body(self) -> None:
        for conc in (
            "True ∧ ∀ y : Nat, (y = y ∧ True)",
            "True ∧ ∀ y : Nat, (True ∨ P y)",
        ):
            src = (
                "/--\nKind: safety\nWitness: universal\nAssumes: S0\nSubject: P\n-/\n"
                f"theorem t_q (P : Nat → Prop) : {conc} := by sorry\n"
            )
            self.assertIn(audit.RULE_TRIVIAL_CONCLUSION, _rules(audit.scan_lean_text(src)), conc)


# ---------------------------------------------------------------------------
# [adv B4] Column-0 term bodies stay inside the pinned span
# ---------------------------------------------------------------------------


class TestB4ColumnZeroBodies(unittest.TestCase):
    def test_column_zero_term_bodies_are_pinned(self) -> None:
        # Lean accepts term bodies at column 0 (`def layoutSize : Nat :=\n8` elaborates); A0-A3 ended
        # the span at ANY column-0 line, so editing such a body kept the old pin valid.
        for decl, name, old, new in (
            ("def layoutSize : Nat :=\n8\n", "layoutSize", ":=\n8", ":=\n16"),
            ("def f (n : Nat) : Nat :=\nn + 1\n\ntheorem next : True := trivial\n", "f", "n + 1", "n + 2"),
            ("def p : Nat × Nat := (1,\n2)\n", "p", "\n2)", "\n3)"),
        ):
            pinned = _pin_lean_named("anneal:pinned_compiler_coupled column-0 body", decl, name)
            self.assertEqual(audit.scan_lean_text(pinned, check_3axis=False), [], name)
            self.assertEqual(
                _rules(audit.scan_lean_text(pinned.replace(old, new, 1), check_3axis=False)),
                [audit.RULE_DRIFTED_WAIVER_PIN],
                name,
            )

    def test_column_zero_commands_still_end_the_span(self) -> None:
        decl = (
            "def q : Nat := 1\n\nopen Nat in\ntheorem next2 : True := trivial\n"
            "set_option maxHeartbeats 1000 in\n#check q\nattribute [simp] q\n"
        )
        pinned = _pin_lean_named("anneal:pinned_compiler_coupled command boundaries", decl, "q")
        self.assertEqual(audit.scan_lean_text(pinned, check_3axis=False), [])
        for old, new in (
            ("True := trivial", "True := True.intro"),
            ("maxHeartbeats 1000", "maxHeartbeats 2000"),
            ("#check q", "#check (q)"),
            ("[simp] q", "[reducible] q"),
            ("open Nat in", "open List in"),
        ):
            self.assertEqual(audit.scan_lean_text(pinned.replace(old, new), check_3axis=False), [], old)
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned.replace(":= 1", ":= 2"), check_3axis=False)),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )


# ---------------------------------------------------------------------------
# [adv A4] Column-0 `protected`/`private`/`@[...]` structure fields and `where`
# auxiliaries stay inside the pinned span (require a command keyword after modifiers)
# ---------------------------------------------------------------------------


class TestA4FinalHardening(unittest.TestCase):
    def test_column_zero_structure_fields_and_where_auxiliaries_with_modifiers_stay_pinned(self) -> None:
        # B4's `_LEAN_COMMAND_START_RE` matched bare `@\[` and `private`/`protected` at column 0
        # without requiring a following command keyword (`theorem`, `def`, ...), so a column-0
        # `protected b : Nat` field or `@[simp] aux : 1 = 1 := rfl` in a column-0 `where` block
        # prematurely terminated the pinned span!
        for decl, name, old, new in (
            (
                "structure S0 where\na : Nat\nprotected b : Nat\nc : Nat\n",
                "S0",
                "c : Nat",
                "c : Int",
            ),
            (
                "theorem w0 : 1 = 1 := by\n  exact aux\nwhere\n@[simp] aux : 1 = 1 := rfl\n",
                "w0",
                ":= rfl",
                ":= by rfl",
            ),
        ):
            pinned = _pin_lean_named("anneal:documented_intent col0-modifier-member", decl, name)
            self.assertEqual(audit.scan_lean_text(pinned, check_3axis=False), [], name)
            self.assertEqual(
                _rules(audit.scan_lean_text(pinned.replace(old, new), check_3axis=False)),
                [audit.RULE_DRIFTED_WAIVER_PIN],
                name,
            )

    def test_column_zero_and_indented_modifiers_followed_by_commands_end_the_span(self) -> None:
        decl = (
            "def first : Nat := 1\n"
            "@[simp]\nprivate theorem second : first = 1 := rfl\n"
        )
        pinned = _pin_lean_named("anneal:documented_intent mod-cmd-boundary", decl, "first")
        self.assertEqual(audit.scan_lean_text(pinned, check_3axis=False), [])
        self.assertEqual(
            audit.scan_lean_text(pinned.replace("first = 1", "1 = 1"), check_3axis=False),
            [],
        )
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned.replace(":= 1", ":= 9"), check_3axis=False)),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )


# ---------------------------------------------------------------------------
# Rules 6 & 7 integration: `ProofHealthFinding` extras, scoping, Rust, post-edit deltas,
# CLI, result-cache soundness, shared-section identity with `check_trusted.py`, dogfood.
# ---------------------------------------------------------------------------

R6 = proof_health.RULE_UNPINNED_OR_DRIFTED_WAIVER
R7 = proof_health.RULE_TRIVIAL_OR_VACUOUS_CLAIM
CHECK_TRUSTED_PATH = REPO_ROOT / "trusted" / "audit" / "check_trusted.py"
_SHARED_BEGIN = "# ===========================================================================\n# BEGIN SHARED WAIVER-PIN & 3-AXIS AUDITOR\n"
_SHARED_END = "# END SHARED WAIVER-PIN & 3-AXIS AUDITOR\n# ===========================================================================\n"


def _shared_section(text: str) -> str:
    begin = text.index(_SHARED_BEGIN)
    return text[begin : text.index(_SHARED_END, begin) + len(_SHARED_END)]


def _load_check_trusted():
    import importlib.util

    spec = importlib.util.spec_from_file_location("check_trusted_under_test", CHECK_TRUSTED_PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # type: ignore[union-attr]
    return module


def scan67(src: str, **kw) -> list[tuple[str, str, int]]:
    return [
        (f.rule, f.subrule, f.line)
        for f in proof_health.scan_lean_text(src, scan_siblings=False, **kw)
        if f.rule in (R6, R7)
    ]


_PINNED_DOC = ["Pinned layout constant.", "anneal:pinned_compiler_coupled rustc 1.90 layout"]
_META = "/-- Kind: safety\nWitness: universal\nAssumes: S0 -/\n"


class TestRules6And7Integration(unittest.TestCase):
    def setUp(self) -> None:
        proof_health.clear_in_process_caches()

    def test_finding_positional_compat_extras_and_dict(self) -> None:
        a = proof_health.ProofHealthFinding(R1, 3, "m", "s", "sym")
        b = proof_health.ProofHealthFinding(rule=R1, line=3, message="m", suggestion="s", symbol="sym")
        self.assertEqual(a, b)
        self.assertEqual(hash(a), hash(b))
        self.assertEqual(a.to_dict(), {"rule": R1, "line": 3, "message": "m", "suggestion": "s", "symbol": "sym"})
        self.assertNotIn("subrule", repr(a))
        c = proof_health.ProofHealthFinding(
            R6, 3, "m", "s", "sym", subrule="drifted_waiver_pin", expected_pin="pin:sha256:0123456789ab"
        )
        self.assertNotEqual(c, proof_health.ProofHealthFinding(R6, 3, "m", "s", "sym"))
        self.assertEqual(c.to_dict()["subrule"], "drifted_waiver_pin")
        self.assertNotIn("actual_pin", c.to_dict())
        self.assertIn("expected_pin='pin:sha256:0123456789ab'", repr(c))
        with self.assertRaises(AttributeError):
            c.subrule = "x"  # type: ignore[misc]
        with self.assertRaises(TypeError):
            proof_health.ProofHealthFinding(R1, 3, "m", "s", "sym", "positional-subrule")  # type: ignore[misc]

    def test_rule_registry_and_cache_format_version(self) -> None:
        self.assertEqual(proof_health.ALL_RULES[:5], (R1, R2, R3, R4, R5))
        self.assertEqual(proof_health.ALL_RULES[5:], (R6, R7))
        self.assertGreaterEqual(proof_health.CACHE_FORMAT_VERSION, 7)
        counts = proof_health.count_findings_by_rule([])
        self.assertEqual(counts[R6], 0)
        self.assertEqual(counts[R7], 0)

    def test_rule6_waiver_subrules_in_scan_lean_text(self) -> None:
        pinned = pin_lean_decl(_PINNED_DOC, "def pinnedMagic : Nat := 7\n")
        self.assertEqual(scan67(pinned), [])
        cases = {
            "unpinned_waiver": "/-- anneal:documented_intent kept for ABI parity -/\ndef unpinnedMagic : Nat := 7\n",
            "drifted_waiver_pin": pinned.replace(":= 7", ":= 8"),
            "malformed_waiver_pin": pinned.replace("pin:sha256:", "pin:sha256:zz", 1),
            "dangling_waiver": "/-! anneal:documented_intent module-wide -/\ndef x : Nat := 0\n",
            "invalid_waiver_syntax": "/-- anneal:trusted reason = -/\ndef y : Nat := 0\n",
        }
        for subrule, src in cases.items():
            got = scan67(src)
            self.assertEqual([(r, s) for r, s, _ in got], [(R6, subrule)], (subrule, got))
        drifted = [
            f for f in proof_health.scan_lean_text(cases["drifted_waiver_pin"], scan_siblings=False) if f.rule == R6
        ][0]
        self.assertTrue(drifted.expected_pin.startswith("pin:sha256:"))
        self.assertTrue(drifted.actual_pin.startswith("pin:sha256:"))
        self.assertNotEqual(drifted.expected_pin, drifted.actual_pin)
        self.assertEqual(drifted.tier, "S3")

    def test_rule7_default_scope_vs_all_theorems(self) -> None:
        smoke = "theorem trivial_witness : True := trivial\n"
        self.assertEqual(scan67(smoke), [])
        self.assertEqual(
            scan67(smoke, include_unannotated_vacuity=True), [(R7, audit.RULE_TRIVIAL_CONCLUSION, 1)]
        )
        # Named contradictory hypotheses are always flagged; anonymous `→` premises only in
        # the full audit (annotated theorems or `--all-theorems`).
        self.assertEqual(
            scan67("theorem v (n : Nat) (h : 5 < 3) : n = n := rfl\n"),
            [(R7, audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS, 1)],
        )
        arrow = "theorem a : False → True := fun h => False.elim h\n"
        self.assertEqual(scan67(arrow), [])
        self.assertIn(
            (R7, audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS, 1),
            scan67(arrow, include_unannotated_vacuity=True),
        )
        # Annotated theorems get every check by default.
        self.assertEqual(
            scan67(_META + "theorem t (n : Nat) : n = n := rfl\n"),
            [(R7, audit.RULE_TRIVIAL_CONCLUSION, 4)],
        )
        helper = "/-- Kind: helper\nWitness: universal\nAssumes: S0 -/\ntheorem t (n : Nat) : n = n := rfl\n"
        self.assertEqual(scan67(helper), [])
        negative = "/-- Kind: safety\nWitness: negative\nAssumes: S0 -/\ntheorem t : ¬ False := fun h => h\n"
        self.assertEqual(scan67(negative), [])
        # `Proof/` claim theorems (`verified`, `prove_*`) get every check by default.
        claim = "theorem verified : True := trivial\n"
        self.assertEqual(scan67(claim, file_path="proofs/Proof/Demo/Foo.lean"), [(R7, audit.RULE_TRIVIAL_CONCLUSION, 1)])
        self.assertEqual(scan67(claim, file_path="theory/Demo/Foo.lean"), [])
        self.assertEqual(scan67("theorem helper_lemma : True := trivial\n", file_path="proofs/Proof/Foo.lean"), [])

    def test_scan_rust_text_rule6_and_fast_path_soundness(self) -> None:
        item = "/// anneal:documented_intent kept for FFI parity\npub fn ffi_magic() -> u32 { 7 }\n"
        self.assertEqual([(f.rule, f.subrule) for f in proof_health.scan_rust_text(item)], [(R6, "unpinned_waiver")])
        self.assertEqual(proof_health.scan_rust_text(pin_rust_snippet(item.split("\n")[0], "pub fn ffi_magic() -> u32 { 7 }")), [])
        escaped = '#[doc = "anneal\\x3adocumented_intent hidden"]\npub fn g() {}\n'
        self.assertEqual([f.subrule for f in proof_health.scan_rust_text(escaped)], ["unpinned_waiver"])
        computed = '#[doc = include_str!("README.md")]\npub fn f() {}\n'
        self.assertEqual([f.subrule for f in proof_health.scan_rust_text(computed)], ["invalid_waiver_syntax"])
        self.assertEqual(proof_health.scan_rust_text("pub fn plain() {}\n"), [])
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "lib.rs"
            p.write_text(item, encoding="utf-8")
            self.assertEqual([f.rule for f in proof_health.scan_file(p)], [R6])

    def test_post_edit_deltas_for_rule6_and_rule7_on_lean_and_rust(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cache = Path(tmp) / "cache.json"
            lean = Path(tmp) / "Demo.lean"
            before = "theorem ok (n : Nat) : n + 0 = n := Nat.add_zero n\n"
            after = before + "/-- anneal:documented_intent kept -/\ndef magic : Nat := 7\n"
            after += "theorem vac (n : Nat) (h : 0 = 1) : n = n := rfl\n"
            lean.write_text(after, encoding="utf-8")
            res = proof_health.evaluate_post_edit_proof_health(
                lean, None, after_text=after, before_text=before, cache_path=cache, scan_siblings=False
            )
            self.assertEqual(res["deltas"][R6], 1)
            self.assertEqual(res["deltas"][R7], 1)
            self.assertIn(R6, res["feedback"])
            self.assertIn(R7, res["feedback"])
            self.assertEqual({f.subrule for f in res["new_findings"]}, {"unpinned_waiver", "syntactic_contradiction_hypothesis"})

            rs = Path(tmp) / "lib.rs"
            rs_before = "pub fn f() {}\n"
            rs_after = "/// anneal:documented_intent kept\npub fn f() {}\n"
            rs.write_text(rs_after, encoding="utf-8")
            res_rs = proof_health.evaluate_post_edit_proof_health(
                rs, None, after_text=rs_after, before_text=rs_before, cache_path=cache
            )
            self.assertEqual(res_rs["deltas"][R6], 1)
            self.assertEqual([f.subrule for f in res_rs["new_findings"]], ["unpinned_waiver"])

    def test_cli_compute_pins_all_theorems_and_directory_scan(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "pkg" / ".hidden").mkdir(parents=True)
            (root / "pkg" / "target").mkdir()
            (root / "pkg" / "A.lean").write_text("theorem smoke : True := trivial\n", encoding="utf-8")
            item = "/// anneal:documented_intent kept for FFI parity"
            (root / "pkg" / "lib.rs").write_text(pin_rust_snippet(item, "pub fn f() {}"), encoding="utf-8")
            (root / "pkg" / ".hidden" / "B.lean").write_text("theorem v (h : 0 = 1) : True := trivial\n")
            (root / "pkg" / "target" / "gen.rs").write_text("/// anneal:documented_intent x\npub fn g() {}\n")

            def run(*argv: str) -> tuple[int, dict]:
                buf = io.StringIO()
                with patch("sys.stdout", buf):
                    rc = proof_health.main(list(argv))
                return rc, json.loads(buf.getvalue())

            rc, payload = run("--json", str(root / "pkg"))
            self.assertEqual((rc, payload["ok"], payload["files_scanned"]), (0, True, 2))
            rc, payload = run("--json", "--all-theorems", str(root / "pkg"))
            self.assertEqual((rc, payload["finding_count"]), (1, 1))
            self.assertEqual(payload["findings"][0]["subrule"], audit.RULE_TRIVIAL_CONCLUSION)
            self.assertEqual(payload["counts"][R7], 1)
            rc, pins = run("--compute-pins", "--json", str(root / "pkg" / "A.lean"))
            self.assertEqual(rc, 0)
            text = (root / "pkg" / "A.lean").read_text(encoding="utf-8")
            self.assertEqual(pins, {str(root / "pkg" / "A.lean"): proof_health.compute_lean_decl_pins(text)})
            buf = io.StringIO()
            with patch("sys.stdout", buf):
                self.assertEqual(proof_health.main([str(root / "pkg" / "A.lean"), "--all-theorems"]), 1)
            self.assertIn(f"[{R7}/{audit.RULE_TRIVIAL_CONCLUSION}]", buf.getvalue())
            result = subprocess.run(
                [sys.executable, "-B", str(SERVER_DIR / "proof_health.py"), "--json", str(root / "pkg")],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(json.loads(result.stdout)["ok"])

    def test_scan_result_cache_tracks_content_and_siblings(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            a, b = Path(tmp) / "A.lean", Path(tmp) / "B.lean"
            a.write_text("private theorem dup_name : 1 + 1 = 2 := rfl\n", encoding="utf-8")
            b.write_text("private theorem dup_name : 1 + 1 = 2 := rfl\n", encoding="utf-8")
            first = proof_health.scan_lean_file(a)
            self.assertTrue(any(f.rule == R5 for f in first))
            self.assertEqual(proof_health.scan_lean_file(a), first)  # memo hit
            self.assertTrue(proof_health._SCAN_RESULT_CACHE)
            # Same-size sibling rewrite inside the racy mtime window must invalidate the memo.
            b.write_text("private theorem dup_nam2 : 1 + 1 = 3 := rfl\n", encoding="utf-8")
            self.assertFalse(any(f.rule == R5 for f in proof_health.scan_lean_file(a)))
            # Content edits of the scanned file are separate memo keys.
            a.write_text("private theorem other : 2 + 2 = 4 := rfl\n", encoding="utf-8")
            self.assertEqual(proof_health.scan_lean_file(a), [])
            proof_health.clear_in_process_caches()
            self.assertFalse(proof_health._SCAN_RESULT_CACHE)
            self.assertFalse(proof_health._THM_AUDIT_CACHE)

    def test_scan_memo_never_confuses_same_length_texts(self) -> None:
        # The memo is looked up by length / head / tail and confirmed by full text equality:
        # two texts differing only in the middle (same length) keep their own results.
        head = "theorem h0 : True := trivial\n" * 20
        tail = "theorem t0 : True := trivial\n" * 20
        bad = head + "theorem mid (n : Nat) (h : 0 = 1) : n = n := rfl\n" + tail
        good = head + "theorem mid (n : Nat) (h : 0 = 0) : n = n := rfl\n" + tail
        self.assertEqual(len(bad), len(good))
        self.assertEqual([f.rule for f in proof_health.scan_lean_text(bad, scan_siblings=False)], [R7])
        self.assertEqual(proof_health.scan_lean_text(good, scan_siblings=False), [])
        self.assertEqual([f.rule for f in proof_health.scan_lean_text(bad, scan_siblings=False)], [R7])

    def test_dogfood_bytecodec_and_adt_and_control_warm_under_5ms(self) -> None:
        for path, anchor in (
            (EPISODE1_BYTECODEC, "theorem scalarValidRange_isExactWidth (sz : Nat)"),
            (EPISODE1_ADT_AND_CONTROL, "theorem evalConst_size_eq_forces_zero_pad_and_intoBytes"),
        ):
            self.assertEqual(proof_health.scan_lean_file(path), [], path.name)
            elapsed_ms = best_of_ms(lambda: proof_health.scan_lean_file(path, scan_siblings=True))
            self.assertLess(elapsed_ms, 5.0, f"{path.name} warm scan took {elapsed_ms:.2f} ms")

            text = path.read_text(encoding="utf-8")
            self.assertIn(anchor, text)
            self.assertEqual(audit.scan_lean_text(text, file_path=path), [], path.name)
            counter = iter(range(10**6))

            def incremental_audit() -> None:
                k = next(counter)
                audit.scan_lean_text(
                    text.replace(anchor, f"{anchor} (hInc{k} : {k} ≤ {k} + 1)", 1),
                    file_path=path,
                )

            inc_audit_ms = best_of_ms(incremental_audit, budget_ms=5.0)
            self.assertLess(
                inc_audit_ms,
                5.0,
                f"{path.name} incremental 1-theorem audit_lean_text took {inc_audit_ms:.2f} ms",
            )

            def incremental_full_scan() -> None:
                k = next(counter)
                proof_health.scan_lean_text(
                    text.replace(anchor, f"{anchor} (hScan{k} : {k} ≤ {k} + 1)", 1),
                    file_path=path,
                    scan_siblings=True,
                )

            inc_scan_ms = best_of_ms(incremental_full_scan, budget_ms=5.0)
            self.assertLess(
                inc_scan_ms,
                5.0,
                f"{path.name} incremental 1-theorem scan_lean_text took {inc_scan_ms:.2f} ms",
            )

            # Verify that a real vacuity or waiver-drift mutation inside the incremental window
            # is still caught identically to a cold full scan.
            bad_edit = text.replace(anchor, f"{anchor} (hBad : 0 = 1)", 1)
            inc_bad = proof_health.scan_lean_text(bad_edit, file_path=path, scan_siblings=True)
            proof_health.clear_in_process_caches()
            cold_bad = proof_health.scan_lean_text(bad_edit, file_path=path, scan_siblings=True)
            self.assertEqual(inc_bad, cold_bad, path.name)
            self.assertTrue(
                any(f.subrule == audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS for f in inc_bad),
                path.name,
            )

    def test_multiline_and_inline_block_comment_before_decl_preserves_pin_span(self) -> None:
        # 1. Multi-line `/- ... -/` block comment ending on the same line as an indented `def`
        # must preserve `\n` in `code_only` and compute the true line indentation (`2`), keeping
        # `where\n  def helper` inside the pinned span.
        indented_draft = (
            "namespace BlockIndent\n"
            "  /-- anneal:documented_intent test\n"
            "  PIN_TAG\n"
            "  -/\n"
            "  /- multi-line comment with a very long first line\n"
            "  -/ def pinnedIndented : Nat :=\n"
            "    helper\n"
            "    where\n"
            "      def helper : Nat := 1\n"
            "end BlockIndent\n"
        )
        tag1 = audit.compute_lean_decl_pins(indented_draft.replace("  PIN_TAG\n", ""))["pinnedIndented"]
        pinned1 = indented_draft.replace("PIN_TAG", tag1)
        self.assertEqual(audit.scan_lean_text(pinned1, check_3axis=False), [])
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned1.replace(":= 1", ":= 999"), check_3axis=False)),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

        # 2. Same-line `/- inline comment -/ def pinnedTopLevel` at column 0 must keep `where\n  def helper`
        # inside the pinned span, while a subsequent `/- comment -/ def nextCmd` at column 0 must end the span.
        top_draft = (
            "/-- anneal:documented_intent test\n"
            "PIN_TOP\n"
            "-/\n"
            "/- inline comment -/ def pinnedTopLevel : Nat :=\n"
            "  helper\n"
            "where\n"
            "  def helper : Nat := 1\n"
            "/- next inline -/ def nextCmd : Nat := 2\n"
        )
        tag2 = audit.compute_lean_decl_pins(top_draft.replace("PIN_TOP\n", ""))["pinnedTopLevel"]
        pinned2 = top_draft.replace("PIN_TOP", tag2)
        self.assertEqual(audit.scan_lean_text(pinned2, check_3axis=False), [])
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned2.replace("helper : Nat := 1", "helper : Nat := 999"), check_3axis=False)),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )
        self.assertEqual(
            audit.scan_lean_text(pinned2.replace("nextCmd : Nat := 2", "nextCmd : Nat := 999"), check_3axis=False),
            [],
        )

    def test_shared_auditor_section_byte_identical_and_check_trusted_stdlib_only(self) -> None:
        import ast

        ph_text = (SERVER_DIR / "proof_health.py").read_text(encoding="utf-8")
        ct_text = CHECK_TRUSTED_PATH.read_text(encoding="utf-8")
        self.assertEqual(_shared_section(ph_text), _shared_section(ct_text))
        allowed = {
            "__future__", "argparse", "bisect", "hashlib", "json", "os", "pathlib", "re", "shutil",
            "stat", "subprocess", "sys", "tempfile", "time", "tomllib", "typing",
            # `--self-test` only: the fixture harness in `tests/trusted-boundary/`.
            "test_boundary",
        }
        imported = set()
        for node in ast.walk(ast.parse(ct_text)):
            if isinstance(node, ast.Import):
                imported.update(alias.name.split(".")[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        self.assertLessEqual(imported, allowed, imported - allowed)
        self.assertNotIn("importlib", imported)  # no dynamic loading of untrusted helpers

    def test_check_trusted_auditor_agrees_with_proof_health(self) -> None:
        ct = _load_check_trusted()
        lean_corpus = [
            pin_lean_decl(_PINNED_DOC, "def pinnedMagic : Nat := 7\n"),
            "/-- anneal:documented_intent kept -/\ndef m : Nat := 7\n",
            _META + "theorem t (n : Nat) (h : 0 = 1) : n = n := rfl\n",
            "theorem smoke : True := trivial\n",
            EPISODE1_BYTECODEC.read_text(encoding="utf-8"),
        ]
        for text in lean_corpus:
            self.assertEqual(ct.compute_lean_decl_pins(text), proof_health.compute_lean_decl_pins(text))
            for scope in ("all", "annotated", "annotated-only"):
                self.assertEqual(
                    [(f.rule, f.line) for f in ct.audit_lean_text(text, vacuity_scope=scope)],
                    [(f.rule, f.line) for f in proof_health.audit_lean_text(text, vacuity_scope=scope)],
                )
        rust = "/// anneal:documented_intent kept\npub fn f() {}\n"
        self.assertEqual(ct.compute_rust_item_pins(rust), proof_health.compute_rust_item_pins(rust))
        self.assertEqual(
            [(f.rule, f.line) for f in ct.audit_rust_text(rust)],
            [(f.rule, f.line) for f in proof_health.audit_rust_text(rust)],
        )

    def test_repo_lean_files_default_scope_has_no_rule6_or_rule7_findings(self) -> None:
        try:
            listed = subprocess.run(
                ["git", "-C", str(REPO_ROOT), "ls-files", "*.lean"], capture_output=True, text=True, check=True
            ).stdout.split("\n")
        except (OSError, subprocess.CalledProcessError):
            self.skipTest("git ls-files unavailable")
        hits = []
        for rel in filter(None, listed):
            path = REPO_ROOT / rel
            if not path.is_file():
                continue
            text = path.read_bytes().decode("utf-8", errors="replace")
            hits.extend(
                (rel, f.line, f.subrule)
                for f in proof_health._lean_waiver_and_vacuity_findings(text, file_path=path)
            )
        self.assertEqual(hits, [])


class TestB1IncrementalAndSpanSoundness(unittest.TestCase):
    """`[adv ep2-B1]`: incremental window splicing must equal a cold full scan, and a body line
    indented deeper than its declaration must never end a pinned span."""

    _SNIPPETS = [
        '"', "/-", "-/", "--", "/--", "'", "«", "»", "\n", "theorem ", " (h : 0 = 1)", " (h : False)",
        "\n/-- anneal:documented_intent x -/\ndef w : Nat := 0\n",
        "\n/-- anneal:documented_intent kept\npin:sha256:0123456789ab\n-/\ndef wp : Nat := 1\n",
        "private theorem dup : True := trivial\n", "simp [wpMirExecSym]",
        "set_option trace.profiler.threshold 1\n", "/-- Kind: safety\nWitness: universal\nAssumes: S0 -/\n",
        "where\n  aux : Nat := 1\n", "@[simp] ", "  ", 'r#"', '"#', 's!"{', '}"',
        "/-! anneal:documented_intent m -/\n", " := by\n  rfl\n",
        # `[adv ep2-A2]` boundary classes: modifiers / attributes between a docstring and its
        # theorem, metadata separated by blank lines, and quotes inside comments.
        "noncomputable\n", "@[simp]\n", "private ", "open Foo in\n", '/-- " -/', '-- " quote\n',
        "\n\n\n\n\n", "/-- Kind: safety\nWitness: universal\nAssumes: S0 -/\n\n\n\n",
        "@[aesop safe\n  [constructors]]\n", '/- " -/', "where\n/- c -/  def helper : Nat := 1\n",
    ]

    @staticmethod
    def _corpus(rnd) -> str:
        parts = []
        for i in range(170):
            kind = rnd.randrange(9)
            doc = "/-- " + "long docstring words " * rnd.randint(1, 6) + "-/\n" if rnd.random() < 0.7 else ""
            if kind == 0:
                parts.append(doc + f"theorem t{i} (n : Nat) : n + 0 = n := Nat.add_zero n\n\n")
            elif kind == 1:
                parts.append(doc + f"theorem v{i} (n : Nat) (h : 0 = 1) : n = n := rfl\n\n")
            elif kind == 2:
                parts.append(f"/-- Kind: safety\nWitness: universal\nAssumes: S0 -/\ntheorem m{i} (n : Nat) : n = n := rfl\n\n")
            elif kind == 3:
                parts.append(doc + f"def d{i} : Nat :=\n  {i}\n\n")
            elif kind == 4:
                parts.append(doc + f"theorem s{i} : True := by\n  simp [foo{i}]\n\n")
            elif kind == 5:
                parts.append(f"/- plain comment {i} -/\ntheorem c{i} (x : Nat) (hx : x < x) : True := trivial\n\n")
            elif kind == 6:
                parts.append(doc + f"noncomputable\ntheorem nc{i} (n : Nat) (h : 2 = 3) : n = n := rfl\n\n")
            elif kind == 7:
                parts.append(
                    f"/-- anneal:documented_intent kept {i}\npin:sha256:0123456789ab\n-/\n@[simp]\n"
                    f"theorem pw{i} : True := trivial\n\n"
                )
            else:
                parts.append(
                    "/-- Kind: safety\nWitness: universal\nAssumes: S0 -/\n\n\n\n" + " " * 70
                    + f"\ntheorem far{i} (n : Nat) : n = n := rfl\n\n"
                )
        text = "".join(parts)
        return text if len(text) >= 32768 else text + text

    @staticmethod
    def _key(findings):
        return [(f.rule, getattr(f, "subrule", ""), f.line, f.symbol, f.message) for f in findings]

    def _incremental_vs_cold(self, text: str) -> tuple[list, list, list, list]:
        inc = self._key(proof_health.scan_lean_text(text, file_path="F.lean", scan_siblings=False))
        inc_a = self._key(proof_health.audit_lean_text(text, file_path="G.lean"))
        saved = (dict(proof_health._LAST_LEAN_SCAN), dict(proof_health._LAST_LEAN_AUDIT))
        proof_health.clear_in_process_caches()
        cold = self._key(proof_health.scan_lean_text(text, file_path="F.lean", scan_siblings=False))
        cold_a = self._key(proof_health.audit_lean_text(text, file_path="G.lean"))
        proof_health._LAST_LEAN_SCAN.update(saved[0])
        proof_health._LAST_LEAN_AUDIT.update(saved[1])
        return inc, cold, inc_a, cold_a

    def test_unterminated_string_in_window_falls_back_to_full_scan(self) -> None:
        doc = "/-- " + "This docstring is long so a 64-byte lookahead sees only comment bytes. " * 2 + "-/\n"
        parts = [doc + f"theorem t{i} (n : Nat) : n + 0 = n := Nat.add_zero n\n\n" for i in range(160)]
        parts += [doc + f"theorem tail{i} (n : Nat) (h : 0 = 1) : n = n := rfl\n\n" for i in range(5)]
        old_text = "".join(parts)
        anchor = "theorem t80 (n : Nat) : n + 0 = n := Nat.add_zero n"
        # The opened string swallows the rest of the file (no later `"`): every tail theorem
        # becomes string contents, so a cold scan reports nothing after the edit.
        new_text = old_text.replace(anchor, anchor.replace(":= Nat.add_zero", ':= "Nat.add_zero'), 1)
        proof_health.clear_in_process_caches()
        self.assertEqual(len(proof_health.scan_lean_text(old_text, file_path="F.lean", scan_siblings=False)), 5)
        self.assertEqual(len(proof_health.audit_lean_text(old_text, file_path="G.lean")), 10)
        inc, cold, inc_a, cold_a = self._incremental_vs_cold(new_text)
        self.assertEqual(cold, [])
        self.assertEqual(inc, cold)
        self.assertEqual(inc_a, cold_a)

    def test_3axis_metadata_on_scoped_local_and_in_prefixed_theorems(self) -> None:
        for mod_or_prefix in (
            "scoped ",
            "local ",
            "set_option maxHeartbeats 200000 in\n",
            "open Nat in\n@[simp] ",
            "variable (m : Nat) in\n",
        ):
            src = (
                "/- Kind: safety\nWitness: universal\nAssumes: S0\nSubject: n -/\n"
                f"{mod_or_prefix}theorem bypassed (n : Nat) : n = n := rfl\n"
            )
            for scope in ("annotated", "annotated-only", "all"):
                res = proof_health.audit_lean_text(src, vacuity_scope=scope)
                self.assertEqual(
                    [(f.rule, f.tier) for f in res],
                    [(audit.RULE_TRIVIAL_CONCLUSION, "S0")],
                    (mod_or_prefix, scope),
                )

    def test_waiver_docstring_before_in_prefix_and_single_line_in_prefix(self) -> None:
        for tpl, old, new in (
            (
                "/-- anneal:allow_compile_time_guard\nPIN\n-/\n"
                "set_option maxHeartbeats 400000 in\n"
                "theorem guarded_thm : True := trivial\n",
                "400000 in",
                "100000 in",
            ),
            (
                "/-- anneal:allow_compile_time_guard\nPIN\n-/\n"
                "set_option maxHeartbeats 400000 in theorem guarded_thm : True := trivial\n",
                "400000 in",
                "100000 in",
            ),
            (
                "open Foo in\n"
                "/-- anneal:allow_compile_time_guard\nPIN\n-/\n"
                "set_option maxHeartbeats 400000 in\n"
                "theorem guarded_thm : True := trivial\n",
                "open Foo in",
                "open Bar in",
            ),
        ):
            pin = proof_health.compute_lean_decl_pins(tpl.replace("PIN\n", ""))["guarded_thm"]
            pinned = tpl.replace("PIN", pin)
            self.assertEqual(proof_health.audit_lean_text(pinned, check_3axis=False), [], tpl)
            self.assertEqual(
                _rules(proof_health.audit_lean_text(pinned.replace(old, new, 1), check_3axis=False)),
                [audit.RULE_DRIFTED_WAIVER_PIN],
                tpl,
            )

    def test_comments_separated_by_long_whitespace_or_in_prefix_never_overwrite_metadata_or_waivers(self) -> None:
        # 1. >64 spaces between `Kind: safety` and `Kind: helper` must flag conflicting `Kind:`.
        src_conflict = (
            "/- Kind: safety\nWitness: universal\nAssumes: S0\nSubject: n -/\n"
            + (" " * 80)
            + "\n/- Kind: helper -/\n"
            + "theorem bypass_conflict (n : Nat) : n = n := rfl\n"
        )
        rules_c = _rules(proof_health.audit_lean_text(src_conflict, vacuity_scope="annotated"))
        self.assertIn(audit.RULE_TIER_ASSUMPTION_MISMATCH, rules_c)

        # 2. `set_option ... in` between two 3-axis comments on the same theorem must also preserve both.
        src_in_conflict = (
            "/- Kind: safety\nWitness: universal\nAssumes: S0\nSubject: n -/\n"
            "set_option maxHeartbeats 200000 in\n"
            "/- Kind: helper -/\n"
            "theorem bypass_in_conflict (n : Nat) : n = n := rfl\n"
        )
        rules_in = _rules(proof_health.audit_lean_text(src_in_conflict, vacuity_scope="annotated"))
        self.assertIn(audit.RULE_TIER_ASSUMPTION_MISMATCH, rules_in)

        # 3. >64 spaces between a `/-- anneal:... -/` docstring and a trailing `-- note` comment
        # must not overwrite `anns_by_decl` in `compute_lean_decl_pins`.
        waiver_draft = (
            "/-- anneal:documented_intent kept\nPIN\n-/\n"
            + (" " * 80)
            + "\n-- trailing note\n"
            + "def long_ws_waiver : Nat := 1\n"
        )
        pin_w = proof_health.compute_lean_decl_pins(waiver_draft.replace("PIN\n", ""))["long_ws_waiver"]
        waiver_pinned = waiver_draft.replace("PIN", pin_w)
        self.assertEqual(proof_health.audit_lean_text(waiver_pinned, check_3axis=False), [])
        self.assertEqual(
            _rules(proof_health.audit_lean_text(waiver_pinned.replace(":= 1", ":= 2"), check_3axis=False)),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

    def test_lean_in_prefix_start_does_not_swallow_preceding_decl_ending_with_let_in(self) -> None:
        draft = (
            "def prev (x : Nat) : Nat :=\n"
            "  let y := x + 1 in\n\n"
            "/-- anneal:documented_intent kept\nPIN\n-/\n"
            "def nextDecl : Nat := 7\n"
        )
        pin = proof_health.compute_lean_decl_pins(draft.replace("PIN\n", ""))["nextDecl"]
        pinned = draft.replace("PIN", pin)
        self.assertEqual(proof_health.audit_lean_text(pinned, check_3axis=False), [])
        # Editing `prev` must NOT drift `nextDecl`'s pin:
        self.assertEqual(
            proof_health.audit_lean_text(pinned.replace("x + 1", "x + 99"), check_3axis=False), []
        )

    def test_rust_outer_doc_groups_with_spaced_or_semicolon_attributes_and_non_attribute_code(self) -> None:
        # 1. Spaced `# [repr(C)]` and attributes containing `;` / `{}` in string literals between
        # outer doc lines belong to the same doc group and item span.
        rust_draft = (
            "/// anneal:pinned_compiler_coupled C ABI\n"
            "# [repr(C)]\n"
            '#[deprecated(note = "old; use {new}[0]")]\n'
            "/// PIN\n"
            "pub struct Packet { pub a: u16 }\n"
        )
        r_pin = proof_health.compute_rust_item_pins(rust_draft.replace("/// PIN\n", ""))["Packet"]
        rust_pinned = rust_draft.replace("PIN", r_pin)
        self.assertEqual(proof_health.audit_rust_text(rust_pinned), [])
        self.assertEqual(
            _rules(proof_health.audit_rust_text(rust_pinned.replace("# [repr(C)]", "# [repr(transparent)]"))),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

        # 2. Non-attribute code (`my_macro!(unpinned_item)`) bracketed by `#[...]` and `#[...]`
        # must NOT merge two separate items' doc comments into one group.
        macro_between = (
            '/// anneal:trusted reason = "waiver on macro"\n'
            "#[cfg(all())] my_macro!(unpinned_item) #[repr(C)]\n"
            "/// pin:sha256:0123456789ab\n"
            "pub struct SecondItem(pub u32);\n"
        )
        self.assertIn(
            audit.RULE_UNPINNED_WAIVER,
            _rules(proof_health.audit_rust_text(macro_between)),
        )

    def test_randomized_incremental_edits_match_cold_full_scans(self) -> None:
        import random

        rnd = random.Random(20261114)
        windows = []
        original = proof_health._find_incremental_lean_window

        def counting(*args, **kwargs):
            result = original(*args, **kwargs)
            windows.append(result is not None)
            return result

        mismatches = []
        with patch.object(proof_health, "_find_incremental_lean_window", counting):
            for trial in range(24):
                text = self._corpus(random.Random(rnd.randrange(10**6)))
                proof_health.clear_in_process_caches()
                proof_health.scan_lean_text(text, file_path="F.lean", scan_siblings=False)
                proof_health.audit_lean_text(text, file_path="G.lean")
                for step in range(5):
                    pos = rnd.randrange(len(text))
                    if rnd.random() < 0.25:
                        text = text[:pos] + text[pos + rnd.randint(1, 30):]
                    else:
                        text = text[:pos] + rnd.choice(self._SNIPPETS) + text[pos:]
                    inc, cold, inc_a, cold_a = self._incremental_vs_cold(text)
                    if inc != cold or inc_a != cold_a:
                        mismatches.append((trial, step, pos))
        self.assertEqual(mismatches, [])
        self.assertGreaterEqual(sum(windows), 10, "too few incremental windows exercised")

    def test_command_in_prefixes_are_bound_by_waiver_pins(self) -> None:
        # `cmd in decl` is one Lean command: prefixes above a pinned declaration's docstring
        # (including multi-line and chained ones) are part of the pin pre-image, so editing or
        # adding one drifts the pin, while edits to neighbouring declarations do not.
        body = "/-- anneal:documented_intent kept\nPIN\n-/\ntheorem t : True := trivial\n"
        for prefix, old, new in (
            ("open Foo in\n", "open Foo in", "open Bar in"),
            ("set_option debug.skipKernelTC false in\n", "false in", "true in"),
            ("attribute [local simp] foo in\n", "foo in", "bar in"),
            ("variable (n : Nat) in\n", "(n : Nat) in", "(n : Int) in"),
            ("open Foo in\nset_option pp.all true in\n", "open Foo in", "open Bar in"),
            ("set_option maxHeartbeats\n  400000 in\n", "400000 in", "1 in"),
        ):
            draft = "def before : Nat := 0\n\n" + prefix + body + "\ndef after : Nat := 1\n"
            pinned = draft.replace("PIN", audit.compute_lean_decl_pins(draft.replace("PIN\n", ""))["t"])
            self.assertEqual(audit.scan_lean_text(pinned, check_3axis=False), [], prefix)
            self.assertEqual(
                _rules(audit.scan_lean_text(pinned.replace(old, new, 1), check_3axis=False)),
                [audit.RULE_DRIFTED_WAIVER_PIN],
                prefix,
            )
            neighbours = pinned.replace("before : Nat := 0", "before : Nat := 5").replace("after : Nat := 1", "after : Nat := 7")
            self.assertEqual(audit.scan_lean_text(neighbours, check_3axis=False), [], prefix)
        plain = body.replace("PIN", audit.compute_lean_decl_pins(body.replace("PIN\n", ""))["t"])
        self.assertEqual(audit.scan_lean_text(plain, check_3axis=False), [])
        self.assertEqual(
            _rules(audit.scan_lean_text("set_option debug.skipKernelTC true in\n" + plain, check_3axis=False)),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )
        ct = _load_check_trusted()
        prefixed = "open Foo in\nset_option pp.all true in\n" + plain
        self.assertEqual(ct.compute_lean_decl_pins(prefixed), proof_health.compute_lean_decl_pins(prefixed))

    def test_check_trusted_never_splices_incremental_findings(self) -> None:
        ct = _load_check_trusted()
        self.assertIs(ct.INCREMENTAL_SPLICING, False)
        self.assertIs(proof_health.INCREMENTAL_SPLICING, True)
        import random

        text = self._corpus(random.Random(5))
        edited = text.replace(" := Nat.add_zero n", ' := "Nat.add_zero n', 1)
        first = [(f.rule, f.line, f.symbol) for f in ct.audit_lean_text(text, file_path="G.lean")]
        second = [(f.rule, f.line, f.symbol) for f in ct.audit_lean_text(edited, file_path="G.lean")]
        self.assertFalse(ct._LAST_LEAN_AUDIT)
        proof_health.clear_in_process_caches()
        self.assertEqual(first, [(f.rule, f.line, f.symbol) for f in proof_health.audit_lean_text(text, file_path="G.lean")])
        proof_health.clear_in_process_caches()
        self.assertEqual(
            second, [(f.rule, f.line, f.symbol) for f in proof_health.audit_lean_text(edited, file_path="G.lean")]
        )

    def test_body_line_after_column0_comment_tail_never_ends_pinned_span(self) -> None:
        # `/- comment` opened at column 0 closes at the start of an indented `where` member: the
        # member must stay inside `pinned`'s span (A1 measured its indent from the opener: 0).
        draft = (
            "/-- anneal:documented_intent test\nPIN\n-/\n"
            "def pinned : Nat :=\n  helper\nwhere\n/- comment\n-/  def helper : Nat := 1\n"
        )
        pinned = draft.replace("PIN", audit.compute_lean_decl_pins(draft.replace("PIN\n", ""))["pinned"])
        self.assertEqual(audit.scan_lean_text(pinned, check_3axis=False), [])
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned.replace(":= 1", ":= 999"), check_3axis=False)),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )
        # The declaration's own indent is the smallest plausible column: its line starts at
        # column 0 even though the comment it closes was opened at column 6.
        draft2 = (
            "/-- anneal:documented_intent test\nPIN\n-/\n"
            "      /- comment\n-/ def pinned2 : Nat :=\n  helper\nwhere\n  def helper : Nat := 1\n"
        )
        pinned2 = draft2.replace("PIN", audit.compute_lean_decl_pins(draft2.replace("PIN\n", ""))["pinned2"])
        self.assertEqual(audit.scan_lean_text(pinned2, check_3axis=False), [])
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned2.replace(":= 1", ":= 999"), check_3axis=False)),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )
        # Same-line `/- comment -/` at column 0 before an indented `where` auxiliary `def helper`
        # must also keep `def helper` inside `pinned`'s span.
        draft3 = (
            "/-- anneal:documented_intent test\nPIN\n-/\n"
            "def pinned3 : Nat :=\n  helper\nwhere\n/- single-line comment at col 0 -/  def helper : Nat := 1\n"
        )
        pinned3 = draft3.replace("PIN", audit.compute_lean_decl_pins(draft3.replace("PIN\n", ""))["pinned3"])
        self.assertEqual(audit.scan_lean_text(pinned3, check_3axis=False), [])
        self.assertEqual(
            _rules(audit.scan_lean_text(pinned3.replace(":= 1", ":= 999"), check_3axis=False)),
            [audit.RULE_DRIFTED_WAIVER_PIN],
        )

    def test_incremental_window_preserves_waivers_and_metadata_across_modifiers_and_blank_lines(self) -> None:
        pad = "".join(f"theorem pad{i} (n : Nat) : n + 0 = n := Nat.add_zero n\n\n" for i in range(500))
        binders = " ".join(f"(x{k} : Nat)" for k in range(15))

        # 1. Editing the body of a waiver-pinned `noncomputable\ntheorem` or multi-line
        # `@[aesop safe\n  [constructors]]\ntheorem` must not drop `RULE_DRIFTED_WAIVER_PIN`.
        for prefix in ("noncomputable\n", "@[aesop safe\n  [constructors]]\n"):
            draft_decl = (
                "/-- anneal:documented_intent pinned theorem\nPIN_HERE\n-/\n"
                + prefix
                + f"theorem target_thm (n : Nat) {binders} : n + 0 = n := Nat.add_zero n\n\n"
            )
            pin_tag = proof_health.compute_lean_decl_pins(draft_decl.replace("PIN_HERE\n", ""))["target_thm"]
            old_text = pad + draft_decl.replace("PIN_HERE", pin_tag) + pad
            proof_health.clear_in_process_caches()
            self.assertEqual(proof_health.scan_lean_text(old_text, file_path="F.lean", scan_siblings=False), [])
            self.assertEqual(proof_health.audit_lean_text(old_text, file_path="G.lean"), [])
            new_text = old_text.replace(":= Nat.add_zero n\n\ntheorem pad0", ":= by omega\n\ntheorem pad0", 1)
            inc, cold, inc_a, cold_a = self._incremental_vs_cold(new_text)
            self.assertTrue(any(r == R6 and s == audit.RULE_DRIFTED_WAIVER_PIN for r, s, *_ in cold))
            self.assertEqual(inc, cold, prefix)
            self.assertEqual(inc_a, cold_a, prefix)

        # 2. Editing or inserting a 3-axis docstring above `noncomputable\ntheorem` or across
        # >64 whitespace bytes before a plain column-0 `theorem` must not drop `RULE_TRIVIAL_CONCLUSION`.
        for mid_block in (
            "/-- Plain doc.\n-/\nnoncomputable\ntheorem target_thm (n : Nat) : n = n := rfl\n\n",
            "/-- Plain doc.\n-/\n" + (" \n" * 40) + "theorem target_thm (n : Nat) : n = n := rfl\n\n",
        ):
            old_text = pad + mid_block + pad
            proof_health.clear_in_process_caches()
            self.assertEqual(proof_health.scan_lean_text(old_text, file_path="F.lean", scan_siblings=False), [])
            self.assertEqual(
                proof_health.audit_lean_text(old_text, file_path="G.lean", vacuity_scope="annotated"), []
            )
            new_text = old_text.replace(
                "/-- Plain doc.\n-/",
                "/-- Kind: safety\nWitness: universal\nAssumes: S0\nSubject: n -/",
                1,
            )
            inc_s = self._key(proof_health.scan_lean_text(new_text, file_path="F.lean", scan_siblings=False))
            inc_au = self._key(
                proof_health.audit_lean_text(new_text, file_path="G.lean", vacuity_scope="annotated")
            )
            proof_health.clear_in_process_caches()
            cold_s = self._key(proof_health.scan_lean_text(new_text, file_path="F.lean", scan_siblings=False))
            cold_au = self._key(
                proof_health.audit_lean_text(new_text, file_path="G.lean", vacuity_scope="annotated")
            )
            self.assertTrue(any(s == audit.RULE_TRIVIAL_CONCLUSION for _, s, *_ in cold_s))
            self.assertEqual(inc_s, cold_s)
            self.assertEqual(inc_au, cold_au)

    def test_unterminated_string_closing_in_outer_ring_comment_falls_back(self) -> None:
        # When an edit opens an unclosed string literal that swallows `cut_hi_new` and closes
        # at a `"` inside a comment between `cut_hi_new` and `safe_hi_new`, the lexer is back in
        # the neutral state at `safe_hi_new`, so checking only the end sentinel would miss that
        # `cut_hi_new` was swallowed into the string literal.
        pad = "".join(f"theorem pad{i} (n : Nat) : n + 0 = n := Nat.add_zero n\n\n" for i in range(400))
        mid = (
            "theorem mid0 (n : Nat) : n + 0 = n := Nat.add_zero n\n\n"
            "theorem mid1 (n : Nat) : n + 0 = n := Nat.add_zero n\n\n"
            'theorem mid2 (n : Nat) (h : 0 = 1) : n = n := rfl -- one " quote here!\n\n'
            "theorem mid3 (n : Nat) : n + 0 = n := Nat.add_zero n\n\n"
        )
        old_text = pad + "theorem target_edit (n : Nat) : n + 0 = n := Nat.add_zero n\n\n" + mid + pad
        proof_health.clear_in_process_caches()
        self.assertEqual(len(proof_health.scan_lean_text(old_text, file_path="F.lean", scan_siblings=False)), 1)
        self.assertEqual(len(proof_health.audit_lean_text(old_text, file_path="G.lean")), 2)
        new_text = old_text.replace(":= Nat.add_zero n\n\ntheorem mid0", ':= "at.add_zero n\n\ntheorem mid0', 1)
        inc, cold, inc_a, cold_a = self._incremental_vs_cold(new_text)
        self.assertEqual(cold, [])
        self.assertEqual(inc, cold)
        self.assertEqual(inc_a, cold_a)


class TestB3PinAndScopeProperties(unittest.TestCase):
    """`[adv ep2-B3]` seeded property tests: for random docstring / `cmd in` prefix / attribute /
    modifier / comment arrangements, `compute_*_pins` and the audit agree (a freshly pinned
    waiver is clean, a body edit drifts, neighbour edits do not, `check_trusted.py` computes the
    same pins), and the vacuity scopes are monotone (`annotated-only` ⊆ `annotated` ⊆ `all`)."""

    _LEAN_PREFIXES = ["set_option maxHeartbeats 400000 in\n", "open Foo in\n", "variable (k : Nat) in\n",
                      "set_option maxHeartbeats\n  400000 in\n", "attribute [local simp] foo in\n"]
    _LEAN_PLAIN = ["/- plain note -/\n", "-- line note\n", "/- far -/\n\n\n\n" + " " * 70 + "\n"]
    _LEAN_ATTRS = ["@[simp]\n", "@[aesop safe [constructors]]\n", "@[simp] ", ""]
    _LEAN_MODS = ["private ", "noncomputable ", "protected ", ""]
    _LEAN_KINDS = [("theorem", ": True := trivial"), ("def", ": Nat := 7"),
                   ("theorem", "(n : Nat) : n + 0 = n := by\n  simp")]

    def test_lean_waiver_pins_consistent_across_random_arrangements(self) -> None:
        import random

        rnd = random.Random(1114)
        ct = _load_check_trusted()
        failures = []
        for it in range(120):
            name = f"target{it}"
            pre = "".join(rnd.choice(self._LEAN_PREFIXES) for _ in range(rnd.randint(0, 2)))
            plain = rnd.choice(self._LEAN_PLAIN) if rnd.random() < 0.3 else ""
            meta = "Kind: helper\nWitness: universal\nAssumes: S3\n" if rnd.random() < 0.5 else ""
            directive = rnd.choice(["anneal:documented_intent kept", "anneal:pinned_compiler_coupled rustc 1.90",
                                    'anneal:trusted reason = "audited"'])
            doc = f"/--\nWaived thing.\n{meta}{directive}\nPIN\n-/\n"
            post = rnd.choice(self._LEAN_PREFIXES) if rnd.random() < 0.3 else ""
            kw, rest = rnd.choice(self._LEAN_KINDS)
            decl = f"{kw} {name} {rest}\n"
            block = pre + plain + doc + post + rnd.choice(self._LEAN_ATTRS) + rnd.choice(self._LEAN_MODS) + decl
            text = "def before : Nat := 0\n\n" + block + "\ndef after : Nat := 1\n"
            draft = text.replace("PIN\n", "")
            pins = proof_health.compute_lean_decl_pins(draft)
            if name not in pins or ct.compute_lean_decl_pins(draft) != pins:
                failures.append((it, "pins", block))
                continue
            pinned = text.replace("PIN", pins[name])
            edited = pinned.replace(
                decl, decl.replace("trivial", "True.intro").replace(":= 7", ":= 8").replace("simp", "omega"), 1
            )
            neighbours = pinned.replace("before : Nat := 0", "before : Nat := 5").replace(
                "after : Nat := 1", "after : Nat := 9"
            )
            got = (
                _rules(audit.scan_lean_text(pinned, check_3axis=False)),
                _rules(audit.scan_lean_text(edited, check_3axis=False)),
                _rules(audit.scan_lean_text(neighbours, check_3axis=False)),
            )
            if got != ([], [audit.RULE_DRIFTED_WAIVER_PIN], []):
                failures.append((it, got, block))
        self.assertEqual(failures, [])

    def test_rust_waiver_pins_consistent_across_random_arrangements(self) -> None:
        import random

        attrs = ["#[repr(C)]\n", "#[derive(Clone, Copy)]\n", '#[deprecated(note = "use foo[0]; {x}")]\n',
                 "# [inline]\n", "#[cfg(all())]\n", '#[doc = "plain prose"]\n', "#[allow(dead_code)] ", ""]
        items = [
            "pub fn {n}() -> u32 {{ 7 }}",
            "pub fn {n}<T: Copy>(x: T) -> T where T: PartialOrd<T> {{ if 1 << 2 <= 4 {{ x }} else {{ x }} }}",
            "pub struct {n} {{ pub a: u8, pub b: u32 }}",
            "pub enum {n} {{ A = 1, B = 2 }}",
            "pub const {n}: u32 = 7;",
            "pub trait {n} {{ fn f(&self) -> u8; }}",
            "pub type {n} = [u8; 4];",
        ]
        rnd = random.Random(1115)
        ct = _load_check_trusted()
        failures = []
        for it in range(120):
            name = f"target_{it}"
            directive = rnd.choice(["anneal:documented_intent kept for ABI parity", "anneal:allow_compile_time_guard",
                                    'anneal:trusted reason = "audited by hand"'])
            doc = rnd.choice(["/// Waived item.\n", '#[doc = " Waived item."]\n', ""]) + "/// " + directive + "\nPIN"
            item = rnd.choice(items).format(n=name) + "\n"
            block = (
                "".join(rnd.choice(attrs) for _ in range(rnd.randint(0, 2)))
                + doc
                + "".join(rnd.choice(attrs) for _ in range(rnd.randint(0, 2)))
                + item
            )
            text = "pub fn before() -> u8 { 0 }\n\n" + block + "\npub fn after() -> u8 { 1 }\n"
            draft = text.replace("PIN", "")
            pins = proof_health.compute_rust_item_pins(draft)
            if name not in pins or ct.compute_rust_item_pins(draft) != pins:
                failures.append((it, "pins", block))
                continue
            pinned = text.replace("PIN", "/// " + pins[name] + "\n")
            edited = pinned.replace(item, item.replace("7", "8").replace("u8", "u16").replace("4", "5").replace("A = 1", "A = 3"), 1)
            neighbours = pinned.replace("{ 0 }", "{ 5 }").replace("{ 1 }", "{ 9 }")
            got = (
                _rules(audit.scan_rust_text(pinned)),
                _rules(audit.scan_rust_text(edited)),
                _rules(audit.scan_rust_text(neighbours)),
            )
            expected = ([], [audit.RULE_DRIFTED_WAIVER_PIN], [])
            if "#[repr(C)]" in block:
                got += (_rules(audit.scan_rust_text(pinned.replace("#[repr(C)]", "#[repr(packed)]", 1))),)
                expected += ([audit.RULE_DRIFTED_WAIVER_PIN],)
            if got != expected:
                failures.append((it, got, block))
        self.assertEqual(failures, [])

    def test_vacuity_scopes_are_monotone_on_random_files(self) -> None:
        import random

        rnd = random.Random(1116)
        snippets = TestB1IncrementalAndSpanSoundness._SNIPPETS
        failures = []
        for it in range(30):
            text = TestB1IncrementalAndSpanSoundness._corpus(random.Random(rnd.randrange(10**6)))
            for _ in range(rnd.randint(0, 8)):
                pos = rnd.randrange(len(text))
                text = text[:pos] + rnd.choice(snippets) + text[pos:]
            proof_health.clear_in_process_caches()

            def keyed(scope: str) -> set:
                return {
                    (f.rule, f.line, f.symbol, f.message)
                    for f in proof_health.audit_lean_text(text, file_path="X.lean", vacuity_scope=scope)
                }

            only, annotated, everything = keyed("annotated-only"), keyed("annotated"), keyed("all")
            if not (only <= annotated <= everything):
                failures.append(it)
        self.assertEqual(failures, [])


class TestA4MultiDocstringInPrefixesAndOperatorTriviality(unittest.TestCase):
    """[adv ep2-A4] Multi-docstring `<command> in` / `@[...]` grouping, indented `<command> in`
    prefix pin alignment, standalone `open Foo` before `let ... in` rejection, and parenthesized /
    operator-bearing (`==`, `:=`, `≤`) trivial conclusion and negated reflexive hypothesis checks."""

    def test_multiple_docstrings_separated_by_in_prefix_or_attributes_and_indented_in_prefix(self) -> None:
        ct = _load_check_trusted()
        for label, src in (
            (
                "in-between-docstrings",
                "/-- anneal:documented_intent first waiver -/\n"
                "set_option maxHeartbeats 200000 in\n"
                "/-- anneal:allow_compile_time_guard\nPIN\n-/\n"
                "theorem t : True := trivial\n",
            ),
            (
                "attr-between-docstrings",
                "/-- anneal:documented_intent first waiver -/\n"
                "@[simp]\n"
                "/-- anneal:allow_compile_time_guard\nPIN\n-/\n"
                "theorem t : True := trivial\n",
            ),
            (
                "indented-in-after-comment",
                "-- comment before set_option\n"
                "  set_option maxHeartbeats 200000 in\n"
                "/-- anneal:allow_compile_time_guard\nPIN\n-/\n"
                "theorem t : True := trivial\n",
            ),
        ):
            draft = src.replace("PIN\n", "")
            pins = proof_health.compute_lean_decl_pins(draft)
            self.assertEqual(ct.compute_lean_decl_pins(draft), pins, label)
            pinned = src.replace("PIN", pins["t"])
            self.assertEqual(proof_health.audit_lean_text(pinned, check_3axis=False), [], label)
            self.assertEqual(ct.audit_lean_text(pinned, check_3axis=False), [], label)
            drifted = pinned.replace("trivial", "True.intro")
            self.assertIn(
                proof_health.RULE_DRIFTED_WAIVER_PIN,
                _rules(proof_health.audit_lean_text(drifted, check_3axis=False)),
                label,
            )

        # Standalone `open Foo` (without `in`) before a theorem containing `let x := 1 in` must NOT
        # be mistaken for an `open ... in` prefix.
        dangling_open = (
            "/-- anneal:allow_compile_time_guard -/\n"
            "open Foo\n"
            "theorem t : let x := 1 in x = 1 := rfl\n"
        )
        self.assertEqual(
            _rules(proof_health.audit_lean_text(dangling_open, check_3axis=False)),
            [proof_health.RULE_DANGLING_WAIVER],
        )

    def test_parenthesized_conjunct_disjunct_and_operator_bearing_reflexive_triviality(self) -> None:
        for conc in (
            "(x == y) = (x == y)",
            "({ a := x } : S) = ({ a := x } : S)",
            "(x ≤ y) = (x ≤ y)",
            "(True ∧ x = x) ∧ y = y",
            "(P ∨ True) ∨ Q",
            "(x = x ∨ P) ∧ (y = y)",
        ):
            src = (
                "/-- Kind: safety\nWitness: universal\nAssumes: S0 -/\n"
                f"theorem t (x y : Nat) (P Q : Prop) : {conc} := by sorry\n"
            )
            self.assertIn(
                proof_health.RULE_TRIVIAL_CONCLUSION,
                _rules(proof_health.audit_lean_text(src, vacuity_scope="all")),
                conc,
            )

        for hyp in (
            "¬ ((x == y) = (x == y))",
            "¬ (({ a := x } : S) = ({ a := x } : S))",
            "¬ ((x ≤ y) = (x ≤ y))",
        ):
            src = f"theorem t (x y : Nat) (h : {hyp}) : x = y := by contradiction\n"
            self.assertIn(
                proof_health.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                _rules(proof_health.audit_lean_text(src, vacuity_scope="annotated")),
                hyp,
            )



class TestEpisode2SharedLeanLexer(unittest.TestCase):
    """Unit, cold-import hygiene, and seeded property tests (`0xA44EA1`) for `lean_lexer.py`."""

    def test_lean_lexer_stdlib_hygiene_and_isolated_import(self) -> None:
        # Run in a fresh `python3 -B` subprocess with `cwd=/tmp` and without `SERVER_DIR` on
        # `sys.path`: `lean_lexer` must not pull in `dataclasses`, `typing`, `ast`, `inspect`,
        # or `re` at import time, and `proof_health` loaded via `spec_from_file_location` must
        # resolve its sibling `lean_lexer` cleanly.
        lexer_path = SERVER_DIR / "lean_lexer.py"
        ph_path = SERVER_DIR / "proof_health.py"
        code = (
            "import importlib.util, sys\n"
            f"spec_ll = importlib.util.spec_from_file_location('lean_lexer_iso', {str(lexer_path)!r})\n"
            "mod_ll = importlib.util.module_from_spec(spec_ll)\n"
            "spec_ll.loader.exec_module(mod_ll)\n"
            "forbidden = {'dataclasses', 'typing', 'ast', 'inspect', 're'}\n"
            "leaked = sorted(forbidden.intersection(sys.modules))\n"
            "assert not leaked, f'lean_lexer imported forbidden modules: {leaked}'\n"
            "assert sys.dont_write_bytecode is True\n"
            f"spec_ph = importlib.util.spec_from_file_location('proof_health_iso', {str(ph_path)!r})\n"
            "mod_ph = importlib.util.module_from_spec(spec_ph)\n"
            "spec_ph.loader.exec_module(mod_ph)\n"
            "assert mod_ph.lean_lexer.__file__ == str(" + repr(str(lexer_path)) + ")\n"
            "assert mod_ph.strip_lean_comments_and_strings('a -- b\\nc') == 'a     \\nc'\n"
        )
        proc = subprocess.run(
            [sys.executable, "-B", "-c", code],
            cwd=tempfile.gettempdir(),
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr or proc.stdout)

    def test_ident_and_line_primitives(self) -> None:
        import lean_lexer

        for ch in ("a", "Z", "_", "α", "ω", "ℕ", "ℤ", "𝒜", "é"):
            self.assertTrue(lean_lexer.is_ident_start(ch), repr(ch))
            self.assertTrue(lean_lexer.is_ident_char(ch), repr(ch))
        for ch in ("0", "9", "'", "!", "?", "₀", "₁", "₉", "ₐ", "ᵢ", "ⱼ"):
            self.assertFalse(lean_lexer.is_ident_start(ch), repr(ch))
            self.assertTrue(lean_lexer.is_ident_char(ch), repr(ch))
        for bad in ("", "ab", "_x", "λ", "Π", "Σ", ".", "«", "»", "⊢", " ", "\n"):
            self.assertFalse(lean_lexer.is_ident_start(bad), repr(bad))
        for bad in ("", "ab", ".", "«", "»", "⊢", " ", "\n"):
            self.assertFalse(lean_lexer.is_ident_char(bad), repr(bad))

        for seg in ("", "abc", "ab\ncd\nef", "αβ\n⊢«x»\n"):
            blanked = lean_lexer.blank_preserving_newlines(seg)
            self.assertEqual(len(blanked), len(seg))
            for a, b in zip(seg, blanked):
                self.assertEqual(b, "\n" if a == "\n" else " ")

        sample = "l1\nl22\n\nl444\nl5"
        nl_offsets = [i for i, c in enumerate(sample) if c == "\n"]
        lc = lean_lexer.LineCounter(sample)
        for off in [0, 2, 3, 6, 7, 8, 12, 13, len(sample), 8, 7, 1, 0, 13, 3]:
            expected = sample.count("\n", 0, off) + 1
            self.assertEqual(lc(off), expected, off)
            self.assertEqual(lean_lexer.offset_to_line(sample, off), expected, off)
            self.assertEqual(lean_lexer.offset_to_line(nl_offsets, off), expected, off)

    def test_scanner_modes_doc_spans_and_unclosed_delimiters(self) -> None:
        import lean_lexer

        src = (
            "/-! Module header\nwith two lines -/\n"
            "/--/\n"
            "/-- Theorem doc\n  /- nested /- deep -/ block -/\n-/\n"
            'def s1 := "a\\"b\\\\" -- trailing -- comment\n'
            'def s2 := r#"raw "quote" -- not comment"#\n'
            'def s3 := obj.r"\\"field proj normal string"\n'
            "def cs := ('\"', '\\\"', '\\\\', '\\'', '«', '»', '\\n', '\\x22', '\\u0022')\n"
            "def pr := (f x'\"str\", f '\\''\"str\", «id--with/-quotes\"»)\n"
        )
        res = lean_lexer.scan_lean_source(src)
        self.assertEqual(res.unclosed_block_comment_pos, -1)
        self.assertEqual(res.unclosed_string_pos, -1)
        self.assertEqual(len(res.stripped), len(src))
        self.assertEqual(
            res.stripped,
            lean_lexer.strip_comments_and_strings_preserving_offsets(src),
        )
        self.assertEqual(res.stripped, proof_health.strip_lean_comments_and_strings(src))
        self.assertEqual(len(res.doc_comments), 2)
        self.assertEqual(res.doc_comments[0].kind, lean_lexer.MODULE_DOC_COMMENT)
        self.assertEqual(res.doc_comments[0].line_no, 1)
        self.assertTrue(src[res.doc_comments[0].start_pos : res.doc_comments[0].end_pos].startswith("/-!"))
        self.assertEqual(res.doc_comments[1].kind, lean_lexer.DOC_COMMENT)
        self.assertEqual(res.doc_comments[1].line_no, 4)
        self.assertIn("«id--with/-quotes\"»", res.stripped)
        with self.assertRaises(AttributeError):
            res.stripped = ""  # type: ignore[misc]

        # `retain_quotes=True` keeps opening/closing string delimiters (`"..."`, `r#"..."#`)
        # while blanking string interiors and comments.
        rq = lean_lexer.strip_comments_and_strings_preserving_offsets(src, retain_quotes=True)
        self.assertEqual(len(rq), len(src))
        self.assertIn('def s1 := "      "', rq)
        self.assertIn('def s2 := r#"                          "#', rq)
        self.assertNotIn("Theorem doc", rq)
        self.assertNotIn("trailing", rq)

        # `keep_strings=True` blanks only comments, keeping all string and char literals verbatim.
        ks = lean_lexer.strip_comments_and_strings_preserving_offsets(src, keep_strings=True)
        self.assertEqual(len(ks), len(src))
        self.assertIn('"a\\"b\\\\"', ks)
        self.assertIn('r#"raw "quote" -- not comment"#', ks)
        self.assertNotIn("trailing -- comment", ks)

        # Unclosed block comments and strings record exact opening offsets and preserve newlines.
        unclosed_blk = "def x := 1\n/- outer /- inner -/\ndef y := 2\n"
        rb = lean_lexer.scan_lean_source(unclosed_blk)
        self.assertEqual(rb.unclosed_block_comment_pos, unclosed_blk.index("/- outer"))
        self.assertEqual(rb.unclosed_string_pos, -1)
        self.assertEqual(len(rb.stripped), len(unclosed_blk))
        self.assertNotIn("def y", rb.stripped)

        unclosed_str = 'def x := 1\ndef s := "multi\nline\\"\n'
        rs = lean_lexer.scan_lean_source(unclosed_str, retain_quotes=True)
        self.assertEqual(rs.unclosed_string_pos, unclosed_str.index('"multi'))
        self.assertEqual(rs.unclosed_block_comment_pos, -1)
        self.assertEqual(len(rs.stripped), len(unclosed_str))
        self.assertEqual([i for i, c in enumerate(rs.stripped) if c == "\n"], [i for i, c in enumerate(unclosed_str) if c == "\n"])
        self.assertEqual(rs.stripped[rs.unclosed_string_pos], '"')

        unclosed_raw = 'def s := r##"unterminated "#" raw\n'
        rr = lean_lexer.scan_lean_source(unclosed_raw)
        self.assertEqual(rr.unclosed_string_pos, unclosed_raw.index('"unterminated'))

    def test_balanced_attribute_scanner_edge_cases(self) -> None:
        import lean_lexer

        src = (
            "-- @[ignored_in_comment]\n"
            'def strAttr := "@[ignored_in_string]"\n'
            "def «@[ignored_in_guillemet]» := 0\n"
            "@[simp, aesop safe [constructors, (apply «a]b»)], custom ']' «x»' ']' {k := \"v]\"}]\n"
            "theorem t1 : True := trivial\n"
            "@[unclosed_before_next\n"
            "@[inline, reducible] def f : Nat := 1\n"
            "@[mismatched (a] @[recover] def g : Nat := 2\n"
        )
        spans = lean_lexer.scan_balanced_attributes(src)
        self.assertEqual(
            [(sp.line_no, sp.content) for sp in spans],
            [
                (4, 'simp, aesop safe [constructors, (apply «a]b»)], custom \']\' «x»\' \']\' {k := "v]"}'),
                (7, "inline, reducible"),
                (8, "recover"),
            ],
        )
        stripped = lean_lexer.strip_comments_and_strings_preserving_offsets(src)
        self.assertIsNone(lean_lexer.match_balanced_attribute(stripped, -5))
        self.assertIsNone(
            lean_lexer.match_balanced_attribute(stripped, src.index("@[ignored_in_guillemet]"))
        )

    def test_namespace_tracker_scopes_inline_in_and_violations(self) -> None:
        import lean_lexer

        src = (
            "namespace A.B\n"
            "  def inAB : Nat := 1\n"
            "  section Sec1\n"
            "    def q := `(command| namespace Quoted def qx := 0 end Quoted)\n"
            "    theorem tac (h : Range) : True := by\n"
            "      let _ := (h.end, «end», Mir.Demo.«end»)\n"
            "      trivial\n"
            "    namespace Inline.Sub in\n"
            "    set_option maxHeartbeats 200000 in\n"
            "    @[simp] theorem inlineThm : True := by\n"
            "      trivial\n"
            "    def afterInline : Nat := 2\n"
            "    namespace MutNs in\n"
            "    mutual\n"
            "      def mf : Nat := mg\n"
            "      def mg : Nat := 0\n"
            "    end\n"
            "    def afterMut : Nat := 3\n"
            "  end Sec1\n"
            "end A.B\n"
            "namespace One; def sameLineIn := 1; end One; def sameLineOut := 2\n"
            "namespace Two def noSemiIn := 1 end Two def noSemiOut := 2\n"
        )
        tr = lean_lexer.NamespaceTracker.from_source(src)
        self.assertEqual(tr.violations, ())
        self.assertEqual(tr.namespace_at(0), ())
        self.assertEqual(tr.namespace_at(src.index("def inAB")), ("A", "B"))
        self.assertEqual(tr.namespace_at(src.index("let _ :=")), ("A", "B"))
        self.assertEqual(
            tr.scopes_at(src.index("let _ :=")),
            (("namespace", "A"), ("namespace", "B"), ("section", "Sec1")),
        )
        self.assertEqual(
            tr.namespace_at(src.index("theorem inlineThm")),
            ("A", "B", "Inline", "Sub"),
        )
        self.assertEqual(tr.namespace_at(src.index("def afterInline")), ("A", "B"))
        self.assertEqual(tr.namespace_at(src.index("def mf")), ("A", "B", "MutNs"))
        self.assertEqual(tr.namespace_at(src.index("def afterMut")), ("A", "B"))
        self.assertEqual(tr.namespace_at(src.index("def sameLineIn")), ("One",))
        self.assertEqual(tr.namespace_at(src.index("def sameLineOut")), ())
        self.assertEqual(tr.namespace_at(src.index("def noSemiIn")), ("Two",))
        self.assertEqual(tr.namespace_at(src.index("def noSemiOut")), ())

        # Mismatch & structural violation reporting
        bad = (
            "end Orphan\n"
            "namespace\n"
            "namespace Foo\n"
            "  end\n"
            "namespace Bar\n"
            "  end Wrong\n"
            "section S\n"
            "  end S.Extra\n"
            "mutual\n"
            "  def u : Nat := 1\n"
        )
        bad_tr = lean_lexer.track_namespaces(bad)
        self.assertEqual(len(bad_tr.violations), 6, bad_tr.violations)
        self.assertTrue(any("no open scope" in v for v in bad_tr.violations))
        self.assertTrue(any("without a name" in v for v in bad_tr.violations))
        self.assertTrue(any("missing the name" in v for v in bad_tr.violations))
        self.assertTrue(any("does not match" in v for v in bad_tr.violations))
        self.assertTrue(any("closes 2 scopes" in v for v in bad_tr.violations))
        self.assertTrue(any("`mutual` block is never closed" in v for v in bad_tr.violations))

    def test_seeded_property_lexer_attributes_and_namespaces(self) -> None:
        import random
        import lean_lexer

        rng = random.Random(0xA44EA1)

        # Part 1: 600 adversarial delimiter soups checking exact length, newline indices,
        # blanking discipline, and 3-way lexer parity (`lean_lexer` vs `proof_health` vs
        # shared auditor `_scan_lean_comments_and_strings`).
        vocab = [
            "--", "/-", "-/", "/--", "/-!", "/--/", '"', '\\"', "\\\\", "'", "'\"'", "'\\\"'",
            "'\\''", "'«'", "'»'", "«", "»", "«a--b»", "«end»", 'r"', 'r#"', '"#', 'r##"',
            '"##', ".r\"", "x'\"", "#[", "@[", "]", "(", ")", "{", "}", "\n", " ", "\t",
            "a", "r", "x'", "α", "₁", "ⱼ", "⊢",
        ]
        for _ in range(600):
            raw = "".join(rng.choice(vocab) for _ in range(rng.randint(0, 55)))
            nl_idx = [i for i, ch in enumerate(raw) if ch == "\n"]
            st = lean_lexer.strip_comments_and_strings_preserving_offsets(raw)
            scan_res = lean_lexer.scan_lean_source(raw)
            self.assertEqual(st, scan_res.stripped)
            self.assertEqual(st, proof_health.strip_lean_comments_and_strings(raw))
            self.assertEqual(st, proof_health._scan_lean_comments_and_strings(raw)[0])
            for mode_out in (
                st,
                lean_lexer.strip_comments_and_strings_preserving_offsets(raw, keep_strings=True),
                lean_lexer.strip_comments_and_strings_preserving_offsets(raw, retain_quotes=True),
            ):
                self.assertEqual(len(mode_out), len(raw))
                self.assertEqual([i for i, ch in enumerate(mode_out) if ch == "\n"], nl_idx)
                for r_ch, o_ch in zip(raw, mode_out):
                    if o_ch != r_ch:
                        self.assertEqual(o_ch, " ")
                        self.assertNotEqual(r_ch, "\n")

        # Part 2: 200 structured attribute + namespace documents with ground-truth scopes
        # and planted balanced `@[...]` spans surrounded by decoy comments/strings/guillemets.
        ns_atoms = ["Alpha", "Beta", "«Gam--ma»", "Delta_1"]
        attr_atoms = [
            "simp",
            'aesop safe [constructors, (apply «x]y»)]',
            'custom "str ] @[fake]"',
            "tag ']' «p»' ']'",
            "cfg { a := [1, (2, 3)] }",
        ]
        decoys = [
            "-- @[decoy] namespace Bad end\n",
            "/- @[decoy]\n  /- nested end -/ namespace Bad -/\n",
            'def strDecoy := "@[decoy] namespace Bad end"\n',
            'def rawDecoy := r#"@[decoy] " end "#\n',
            "def guiDecoy (h : T) := (h.end, «end», «@[decoy]»)\n",
        ]
        for _ in range(200):
            pieces: list[str] = []
            cursor = 0
            expected_attrs: list[tuple[int, int, str]] = []
            open_stack: list[tuple[str, str]] = []
            probes: list[tuple[int, tuple[str, ...]]] = []

            def emit(chunk: str) -> None:
                nonlocal cursor
                pieces.append(chunk)
                cursor += len(chunk)

            def cur_ns() -> tuple[str, ...]:
                return tuple(nm for k, nm in open_stack if k == "namespace")

            for _step in range(rng.randint(8, 20)):
                choice = rng.randrange(6)
                if choice == 0:
                    emit(rng.choice(decoys))
                    probes.append((cursor - 2, cur_ns()))
                elif choice == 1:
                    k_parts = rng.randint(1, 2)
                    parts = [rng.choice(ns_atoms) for _ in range(k_parts)]
                    dotted = ".".join(parts)
                    emit(f"namespace {dotted}\n")
                    for p_nm in parts:
                        open_stack.append(("namespace", p_nm))
                    probes.append((cursor - 1, cur_ns()))
                elif choice == 2:
                    sec_nm = rng.choice(["", "SecA", "«Sec-B»"])
                    emit(f"section {sec_nm}\n" if sec_nm else "section\n")
                    open_stack.append(("section", sec_nm))
                    probes.append((cursor - 1, cur_ns()))
                elif choice == 3:
                    emit("mutual\n  def m1 : Nat := 0\nend\n")
                    probes.append((cursor - 6, cur_ns()))
                elif choice == 4 and open_stack:
                    # Pop 1 or 2 named scopes when possible, or 1 anonymous section.
                    top_kind, top_nm = open_stack[-1]
                    if not top_nm:
                        open_stack.pop()
                        emit("end\n")
                    else:
                        pop_n = (
                            2
                            if len(open_stack) >= 2
                            and open_stack[-2][1]
                            and rng.random() < 0.4
                            else 1
                        )
                        popped = [open_stack.pop()[1] for _ in range(pop_n)]
                        popped.reverse()
                        emit(f"end {'.'.join(popped)}\n")
                    probes.append((cursor - 1, cur_ns()))
                else:
                    body = ", ".join(rng.sample(attr_atoms, k=rng.randint(1, 2)))
                    start_off = cursor
                    emit(f"@[{body}]\n")
                    end_off = cursor - 1
                    expected_attrs.append((start_off, end_off, body))
                    probe_off = cursor + 4
                    emit("theorem probe_thm : True := trivial\n")
                    probes.append((probe_off, cur_ns()))

            doc = "".join(pieces)
            st = lean_lexer.strip_comments_and_strings_preserving_offsets(doc)
            got_attrs = [(a.start_pos, a.end_pos, a.content) for a in lean_lexer.scan_balanced_attributes(doc, stripped=st)]
            self.assertEqual(got_attrs, expected_attrs)
            tr = lean_lexer.NamespaceTracker.from_source(doc, stripped=st)
            self.assertEqual(tr.violations, ())
            for off, want_ns in probes:
                self.assertEqual(tr.namespace_at(off), want_ns)


class TestEpisode2ProjectionAndRewriteOrderHazards(unittest.TestCase):
    """Unit, incremental cache/splicing, CLI `--advisories`, and `< 5.0 ms` benchmark tests
    for `scan_projection_and_rewrite_order_hazards`."""

    def test_backward_compatibility_of_all_rules_and_defaults(self) -> None:
        self.assertEqual(len(proof_health.ALL_RULES), 7)
        self.assertEqual(
            proof_health.ADVISORY_RULES,
            (
                proof_health.RULE_SIMP_DEEP_PROJECTION_CHAIN,
                proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET,
            ),
        )
        self.assertTrue(set(proof_health.ALL_RULES).isdisjoint(proof_health.ADVISORY_RULES))
        # `AdtAndControl.lean` contains legacy `try rw [...] at hEval ⊢` lines: default
        # `scan_lean_file` MUST remain `[]`, while `include_advisories=True` surfaces them.
        self.assertEqual(proof_health.scan_lean_file(EPISODE1_ADT_AND_CONTROL), [])
        adv = proof_health.scan_lean_file(EPISODE1_ADT_AND_CONTROL, include_advisories=True)
        self.assertEqual(
            [f.rule for f in adv],
            [
                proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET,
                proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET,
            ],
        )
        self.assertEqual(adv[1].line, adv[0].line + 1)
        adt_lines = EPISODE1_ADT_AND_CONTROL.read_text(encoding="utf-8").splitlines()
        for finding in adv:
            src_line = adt_lines[finding.line - 1]
            self.assertIn("try rw", src_line)
            self.assertIn("⊢", src_line)
        # Subsequent default scan must still return `[]` (no cache cross-talk).
        self.assertEqual(proof_health.scan_lean_file(EPISODE1_ADT_AND_CONTROL), [])

    def test_simp_deep_projection_chain_positive_and_negative_cases(self) -> None:
        R_PROJ = proof_health.RULE_SIMP_DEEP_PROJECTION_CHAIN
        S_ARG = proof_health.SUBRULE_PROJECTION_IN_SIMP_ARGS
        S_STMT = proof_health.SUBRULE_SIMP_AFTER_PROJECTION_STATEMENT

        positives = (
            "theorem p1 : P := by\n"
            "  simp [foo, (advanceStmt s l m).memory.locals, bar]\n"
            "  simp only [\n"
            "    h (Mir.advanceStmt s l).frame.stmtIdx\n"
            "  ] at h ⊢\n"
            "  simpa [foo] using bar ((@advanceStmt s l m)).memory.allocs.len\n"
            "  simp_all (disch := exact (advanceStmt s l).frame.locals_wf) [baz]\n"
            "  change (advanceStmt s l m).memory.locals = l; simp\n"
            "  show (advanceStmt s l m).frame.blockIdx = b\n"
            "  simp only [foo]\n"
            "  have h1 : (advanceStmt s l m).memory.locals = l := by simp [advanceStmt]\n"
            "  suffices h2 : Q (advanceStmt s l).frame.locals from by simpa using h2\n"
            "  change (advanceStmt s l m).memory.callStack = cs\n"
            "  dsimp only [unrelatedDef]\n"
            "  simp\n"
        )
        got = [
            (f.line, f.rule, f.subrule, f.symbol)
            for f in proof_health.scan_projection_and_rewrite_order_hazards(positives)
        ]
        self.assertEqual(
            got,
            [
                (2, R_PROJ, S_ARG, "(advanceStmt ...).memory.locals"),
                (4, R_PROJ, S_ARG, "(Mir.advanceStmt ...).frame.stmtIdx"),
                (6, R_PROJ, S_ARG, "(advanceStmt ...).memory.allocs.len"),
                (7, R_PROJ, S_ARG, "(advanceStmt ...).frame.locals_wf"),
                (8, R_PROJ, S_STMT, "(advanceStmt ...).memory.locals"),
                (10, R_PROJ, S_STMT, "(advanceStmt ...).frame.blockIdx"),
                (11, R_PROJ, S_STMT, "(advanceStmt ...).memory.locals"),
                (12, R_PROJ, S_STMT, "(advanceStmt ...).frame.locals"),
                (15, R_PROJ, S_STMT, "(advanceStmt ...).memory.callStack"),
            ],
        )
        for f in proof_health.scan_projection_and_rewrite_order_hazards(positives):
            self.assertIn("dsimp only [advanceStmt", f.suggestion)
            self.assertIn("leanprover/lean4#16532", f.message)

        negatives = (
            "-- simp [(advanceStmt s l m).memory.locals]\n"
            "/- change (advanceStmt s l m).memory.locals = l; simp -/\n"
            'def msg := "simp [(advanceStmt s l m).memory.locals]"\n'
            "def «simp [(advanceStmt s l).memory.locals]» : Nat := 0\n"
            "@[simp] theorem attr_not_tactic : (advanceStmt s l m).memory.locals = l := rfl\n"
            "theorem clean : P := by\n"
            "  dsimp only [advanceStmt, (advanceStmt s l m).memory.locals]\n"
            "  simp [(advanceStmt s l m).memory]\n"
            "  simp [(advanceStmt' s l m).memory.locals]\n"
            "  simp [(wrap (advanceStmt s l m)).memory.locals]\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  dsimp only [other, advanceStmt]\n"
            "  simp\n"
            "  have h : (advanceStmt s l m).memory.locals = l := by\n"
            "    exact rfl\n"
            "  simp [h]\n"
            "  have hProofOnly : Nat := foo (advanceStmt s l m).memory.locals\n"
            "  simp\n"
        )
        self.assertEqual(proof_health.scan_projection_and_rewrite_order_hazards(negatives), [])

    def test_try_rw_hyp_before_target_positive_and_negative_cases(self) -> None:
        R_TRY = proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET

        positives = (
            "theorem p : P := by\n"
            "  try rw [h1, h2] at hEval ⊢\n"
            "  try erw [show x = y by\n"
            "             simp at h0\n"
            "             exact h0] at _hg h2 ⊢\n"
            "  try rewrite [«a]b», show c = ']' from rfl] at «h» |-\n"
            "  try rwa (config := { occs := .pos [1] }) [h1] at\n"
            "    hEval ⊢\n"
            "  try (simp; rw [h1] at hA ⊢)\n"
            "  try simp <;> erw [h1] at hB ⊢\n"
            "  try all_goals rw [h1] at hC ⊢\n"
            "  try\n"
            "    simp\n"
            "    rw [h1] at hD ⊢\n"
        )
        got = [
            (f.line, f.rule, f.symbol)
            for f in proof_health.scan_projection_and_rewrite_order_hazards(positives)
        ]
        self.assertEqual(
            got,
            [
                (2, R_TRY, "try rw [...] at hEval ⊢"),
                (5, R_TRY, "try erw [...] at _hg h2 ⊢"),
                (6, R_TRY, "try rewrite [...] at «h» |-"),
                (7, R_TRY, "try rwa [...] at hEval ⊢"),
                (9, R_TRY, "try rw [...] at hA ⊢"),
                (10, R_TRY, "try erw [...] at hB ⊢"),
                (11, R_TRY, "try rw [...] at hC ⊢"),
                (14, R_TRY, "try rw [...] at hD ⊢"),
            ],
        )
        first = proof_health.scan_projection_and_rewrite_order_hazards(positives)[0]
        self.assertIn("at ⊢ hEval", first.suggestion)

        negatives = (
            "-- try rw [h] at hEval ⊢\n"
            'def s := "try erw [h] at hEval ⊢"\n'
            "def «try rw [h] at hEval ⊢» : Nat := 0\n"
            "theorem clean : P := by\n"
            "  try rw [h] at ⊢ hEval\n"
            "  try erw [h] at |- _hg h2\n"
            "  rw [h] at hEval ⊢\n"
            "  erw [h] at hEval ⊢\n"
            "  try rw [h] at hEval\n"
            "  try rw [h]\n"
            "  try rw [h] at *\n"
            "  retry rw [h] at hEval ⊢\n"
            "  try? rw [h] at hEval ⊢\n"
            "  try simp [h]\n"
            "  rw [h] at hEval ⊢\n"
            "  try\n"
            "  rw [h] at hEval ⊢\n"
        )
        self.assertEqual(proof_health.scan_projection_and_rewrite_order_hazards(negatives), [])

    def test_cli_advisories_text_and_json_modes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            lean_file = Path(tmp) / "Adv.lean"
            lean_file.write_text(
                "theorem t (h hEval : 1 = 1) : 1 = 1 := by\n"
                "  try rw [h] at hEval ⊢\n"
                "  exact h\n",
                encoding="utf-8",
            )
            # Without `--advisories`, clean exit 0 and 0 findings.
            buf = io.StringIO()
            with patch("sys.stdout", buf):
                rc = proof_health.main(["--json", "--no-siblings", str(lean_file)])
            self.assertEqual(rc, 0)
            rep0 = json.loads(buf.getvalue())
            self.assertTrue(rep0["ok"])
            self.assertEqual(rep0["finding_count"], 0)
            self.assertNotIn("advisory_count", rep0)

            # With `--advisories --json`, advisory is surfaced while `ok` and exit code stay 0.
            buf = io.StringIO()
            with patch("sys.stdout", buf):
                rc = proof_health.main(["--json", "--advisories", "--no-siblings", str(lean_file)])
            self.assertEqual(rc, 0)
            rep1 = json.loads(buf.getvalue())
            self.assertTrue(rep1["ok"])
            self.assertEqual(rep1["finding_count"], 1)
            self.assertEqual(rep1["advisory_count"], 1)
            self.assertEqual(rep1["counts"][proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET], 1)
            self.assertTrue(rep1["findings"][0]["advisory"])

            # Plain-text `--advisories` marks findings with `[advisory:...]`.
            buf = io.StringIO()
            with patch("sys.stdout", buf):
                rc = proof_health.main(["--advisories", "--no-siblings", str(lean_file)])
            self.assertEqual(rc, 0)
            self.assertIn(f"[advisory:{proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET}]", buf.getvalue())

            # When a blocking rule (e.g. R4) also fires, exit status is 1 and `ok` is False.
            lean_file.write_text(
                "set_option trace.profiler.threshold 10\n"
                "theorem t (h hEval : 1 = 1) : 1 = 1 := by\n"
                "  try rw [h] at hEval ⊢\n"
                "  exact h\n",
                encoding="utf-8",
            )
            buf = io.StringIO()
            with patch("sys.stdout", buf):
                rc = proof_health.main(["--json", "--advisories", "--no-siblings", str(lean_file)])
            self.assertEqual(rc, 1)
            rep2 = json.loads(buf.getvalue())
            self.assertFalse(rep2["ok"])
            self.assertEqual(rep2["finding_count"], 2)
            self.assertEqual(rep2["advisory_count"], 1)

    def test_incremental_splicing_and_sub_5ms_benchmarks(self) -> None:
        import random
        import lean_lexer

        # 1. Seeded incremental splicing parity with `include_advisories=True` vs `False`.
        base_theorems = [
            f"theorem thm_{i} (s : State) (h hEval : 1 = 1) : 1 = 1 := by\n"
            + (
                "  try rw [h] at hEval ⊢\n"
                if i in (2, 18)
                else "  have _ := s\n"
            )
            + "  exact h\n\n"
            for i in range(24)
        ]
        pad = "-- padding line for >= 32 KiB incremental splicing threshold\n" * 600
        base_doc = pad + "".join(base_theorems)
        self.assertGreaterEqual(len(base_doc), 32768)

        clear_in_process_caches()
        self.assertEqual(proof_health.scan_lean_text(base_doc, scan_siblings=False), [])
        base_adv = proof_health.scan_lean_text(
            base_doc, scan_siblings=False, include_advisories=True
        )
        self.assertEqual(len(base_adv), 2)

        rng = random.Random(0xE92AD7)
        edits = [
            "  simp [(advanceStmt s l m).memory.locals]\n",
            "  change (advanceStmt s l m).frame.stmtIdx = 0\n  simp\n",
            "  try erw [h] at hEval ⊢\n",
            "  dsimp only [advanceStmt]\n",
            "  -- multi-line\n  -- comment shift\n",
        ]
        cur_doc = base_doc
        for step in range(20):
            target_idx = rng.randint(4, 15)
            marker = f"theorem thm_{target_idx} "
            pos = cur_doc.index(marker)
            nl = cur_doc.index("\n", pos) + 1
            injected = rng.choice(edits)
            next_doc = cur_doc[:nl] + injected + cur_doc[nl:]

            inc_adv = proof_health.scan_lean_text(
                next_doc, scan_siblings=False, include_advisories=True
            )
            inc_def = proof_health.scan_lean_text(
                next_doc, scan_siblings=False, include_advisories=False
            )
            drop_scan_memo()
            cold_adv = proof_health.scan_lean_text(
                next_doc, scan_siblings=False, include_advisories=True
            )
            cold_def = proof_health.scan_lean_text(
                next_doc, scan_siblings=False, include_advisories=False
            )
            self.assertEqual(inc_adv, cold_adv, f"step {step}")
            self.assertEqual(inc_def, cold_def, f"step {step}")
            self.assertEqual(inc_def, [], f"step {step}")
            cur_doc = next_doc

        # 2. `< 5.0 ms` CPU latency benchmarks on `lean_lexer`, hazard scanner, and
        # incremental `scan_lean_text(..., include_advisories=True)` on `ByteCodec.lean`.
        bc_text = EPISODE1_BYTECODEC.read_text(encoding="utf-8")
        bc_stripped = lean_lexer.strip_comments_and_strings_preserving_offsets(bc_text)
        lex_ms = best_of_ms(
            lambda: lean_lexer.strip_comments_and_strings_preserving_offsets(bc_text),
            budget_ms=5.0,
        )
        self.assertLess(lex_ms, 5.0, f"ByteCodec lexing took {lex_ms:.2f} ms")

        scan_src_ms = best_of_ms(lambda: lean_lexer.scan_lean_source(bc_text), budget_ms=5.0)
        self.assertLess(scan_src_ms, 5.0, f"ByteCodec scan_lean_source took {scan_src_ms:.2f} ms")

        ns_ms = best_of_ms(
            lambda: lean_lexer.NamespaceTracker.from_source(bc_text, stripped=bc_stripped),
            budget_ms=5.0,
        )
        self.assertLess(ns_ms, 5.0, f"ByteCodec NamespaceTracker took {ns_ms:.2f} ms")

        haz_ms = best_of_ms(
            lambda: proof_health.scan_projection_and_rewrite_order_hazards(
                bc_text, stripped=bc_stripped
            ),
            budget_ms=5.0,
        )
        self.assertLess(haz_ms, 5.0, f"ByteCodec hazard scan took {haz_ms:.2f} ms")

        anchor = "theorem scalarValidRange_isExactWidth (sz : Nat)"
        proof_health.scan_lean_text(
            bc_text, file_path=EPISODE1_BYTECODEC, scan_siblings=True, include_advisories=True
        )
        seq = iter(range(10**6))

        def inc_with_advisories() -> None:
            k = next(seq)
            proof_health.scan_lean_text(
                bc_text.replace(anchor, f"{anchor} (hAdv{k} : {k} ≤ {k} + 1)", 1),
                file_path=EPISODE1_BYTECODEC,
                scan_siblings=True,
                include_advisories=True,
            )

        inc_ms = best_of_ms(inc_with_advisories, budget_ms=5.0)
        self.assertLess(
            inc_ms,
            5.0,
            f"ByteCodec incremental scan with advisories took {inc_ms:.2f} ms",
        )

    def test_shared_auditor_section_remains_byte_identical(self) -> None:
        ph_text = (SERVER_DIR / "proof_health.py").read_text(encoding="utf-8")
        ct_text = CHECK_TRUSTED_PATH.read_text(encoding="utf-8")
        self.assertEqual(_shared_section(ph_text), _shared_section(ct_text))

    def test_b1_lexer_attribute_namespace_and_advisory_regressions(self) -> None:
        import lean_lexer

        # 1. Negative / out-of-bounds offsets must clamp cleanly in `LineCounter` & `offset_to_line`.
        sample = "a\nb\nc"
        nl_offsets = [1, 3]
        lc = lean_lexer.LineCounter(sample)
        self.assertEqual(lean_lexer.offset_to_line(sample, -1), 1)
        self.assertEqual(lean_lexer.offset_to_line(nl_offsets, -1), 1)
        self.assertEqual(lc(-5), 1)
        self.assertEqual(lc(0), 1)
        self.assertEqual(lc(4), 3)
        self.assertEqual(lc(999), 3)
        self.assertEqual(lc(2), 2)

        # 2. Unclosed `«` followed by a distant `»` must stay linear (not scan to EOF per `«`).
        unclosed_stress = ("def x := «unclosed\n" * 1000) + "»\n"
        self.assertEqual(
            lean_lexer.strip_comments_and_strings_preserving_offsets(unclosed_stress),
            unclosed_stress,
        )
        stress_ms = best_of_ms(
            lambda: lean_lexer.strip_comments_and_strings_preserving_offsets(unclosed_stress),
            budget_ms=5.0,
        )
        self.assertLess(stress_ms, 5.0, f"Unclosed guillemet scan took {stress_ms:.2f} ms")

        # 3. Balanced attributes: reject as-patterns `xs@[a, b]`, allow them nested inside `@[...]`,
        # and track `⟨...⟩` bracket matching.
        attr_src = (
            "def f := fun xs@[a, b] => xs\n"
            "@[my_attr (fun xs@[a, b] => xs)]\n"
            "theorem t1 : True := trivial\n"
            "@[bad ⟨a, b]\n"
            "@[ok ⟨a, b⟩] def g : Nat := 0\n"
        )
        self.assertEqual(
            [(a.line_no, a.content) for a in lean_lexer.scan_balanced_attributes(attr_src)],
            [(2, "my_attr (fun xs@[a, b] => xs)"), (5, "ok ⟨a, b⟩")],
        )

        # 4. NamespaceTracker: multi-line brackets, `{...}` and nested syntax quotations,
        # non-command `end` / `section` tokens, `namespace ... in` with `:= by ...; ...` /
        # `:= by open ... in ...` / default-arg `:=`, and rejecting binder `λ` as scope name.
        ns_multiline = (
            "namespace Foo\n"
            "def f (\n"
            "  section : Nat\n"
            ") : Nat := section\n"
            "def q1 := `{\n"
            "  namespace Bar\n"
            "  def x := 1\n"
            "  end Bar\n"
            "}\n"
            "def q2 := `(command|\n"
            "  def inner := `[tactic| exact 1]\n"
            "  namespace Fake\n"
            "  end Fake\n"
            ")\n"
            "structure Span where\n"
            "  start : Nat\n"
            "  end : Nat\n"
            "def mkSpan (s e : Nat) : Span :=\n"
            "  { start := s,\n"
            "    end := e }\n"
            "theorem tac (h : Nat) : Nat := by\n"
            "  let end := h\n"
            "  exact end\n"
            "def stillInFoo : Nat := 0\n"
            "end Foo\n"
            "section λ\n"
            "  def inAnonSec : Nat := 1\n"
            "end\n"
        )
        tr = lean_lexer.track_namespaces(ns_multiline)
        self.assertEqual(tr.violations, ())
        self.assertEqual(tr.namespace_at(ns_multiline.index("def stillInFoo")), ("Foo",))
        self.assertEqual(tr.namespace_at(ns_multiline.index("def inAnonSec")), ())

        ns_in_cases = (
            "namespace A in theorem t1 : True := by simp; trivial\n"
            "def out1 := 0\n"
            "namespace B in theorem t2 : True := by open Classical in trivial\n"
            "def out2 := 0\n"
            "namespace C in def f (x : Nat := 0) (y : Nat := by open Nat; exact 1) : Nat := x\n"
            "def out3 := 0\n"
        )
        tr_in = lean_lexer.track_namespaces(ns_in_cases)
        self.assertEqual(tr_in.violations, ())
        self.assertEqual(tr_in.namespace_at(ns_in_cases.index("trivial")), ("A",))
        self.assertEqual(tr_in.namespace_at(ns_in_cases.index("def out1")), ())
        self.assertEqual(
            tr_in.namespace_at(ns_in_cases.index("trivial", ns_in_cases.index("t2"))),
            ("B",),
        )
        self.assertEqual(tr_in.namespace_at(ns_in_cases.index("def out2")), ())
        self.assertEqual(tr_in.namespace_at(ns_in_cases.index(":= x")), ("C",))
        self.assertEqual(tr_in.namespace_at(ns_in_cases.index("def out3")), ())

        # 5. Advisory hazard regressions: `simpa ... at h using ...`, exact `dsimp only` unfold
        # matching (rejecting `advanceStmt_*`, `-advanceStmt`, `← advanceStmt`, and wrong-target
        # `dsimp only [advanceStmt] at hOther`), nested `show` inside `change`, trailing comments /
        # spaces / CRLF in `try rw ... at ...`, `try` blocks with parenthesised first step, and
        # no false positives on indented tactics (`push_neg at ⊢`) or term-position `try`.
        R_PROJ = proof_health.RULE_SIMP_DEEP_PROJECTION_CHAIN
        S_ARG = proof_health.SUBRULE_PROJECTION_IN_SIMP_ARGS
        S_STMT = proof_health.SUBRULE_SIMP_AFTER_PROJECTION_STATEMENT
        R_TRY = proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET

        adv_pos = (
            "theorem p : P := by\n"
            "  simpa [foo] at h using bar (advanceStmt s l m).memory.locals\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  dsimp only [advanceStmt_locals_eq]\n"
            "  simp\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  dsimp only [-advanceStmt, ← advanceStmt]\n"
            "  simp\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  dsimp only [advanceStmt] at hOther\n"
            "  simp\n"
            "  change (show (advanceStmt s l m).memory.locals = l from h)\n"
            "  simp\n"
            "  try rw [h1] at hEval -- comment before turnstile\n"
            "    ⊢\n"
            "  try rw [h1] at \n"
            "    hEval ⊢\n"
            "  try\n"
            "    (simp [h1])\n"
            "    rw [h2] at hEval ⊢\n"
            "  try (simp [h1]) <;> rw [h2] at hEval ⊢\n"
        )
        got_pos = [
            (f.line, f.rule, f.subrule, f.symbol)
            for f in proof_health.scan_projection_and_rewrite_order_hazards(adv_pos)
        ]
        self.assertEqual(
            got_pos,
            [
                (2, R_PROJ, S_ARG, "(advanceStmt ...).memory.locals"),
                (5, R_PROJ, S_STMT, "(advanceStmt ...).memory.locals"),
                (8, R_PROJ, S_STMT, "(advanceStmt ...).memory.locals"),
                (11, R_PROJ, S_STMT, "(advanceStmt ...).memory.locals"),
                (13, R_PROJ, S_STMT, "(advanceStmt ...).memory.locals"),
                (14, R_TRY, "", "try rw [...] at hEval ⊢"),
                (16, R_TRY, "", "try rw [...] at hEval ⊢"),
                (20, R_TRY, "", "try rw [...] at hEval ⊢"),
                (21, R_TRY, "", "try rw [...] at hEval ⊢"),
            ],
        )

        # CRLF multi-line `at` clause
        crlf_src = "theorem p : P := by\r\n  try rw [h1] at hEval\r\n    ⊢\r\n"
        self.assertEqual(
            [(f.line, f.rule, f.symbol) for f in proof_health.scan_projection_and_rewrite_order_hazards(crlf_src)],
            [(2, R_TRY, "try rw [...] at hEval ⊢")],
        )

        # Negative regressions: goal-collapsing `dsimp only [advanceStmt] at h ⊢`, `change ... at h`
        # followed by `dsimp only [advanceStmt] at h`, indented tactic with `at ⊢` after `try rw`,
        # and term-position `try`.
        adv_neg = (
            "theorem clean (try : Nat → Nat) : P := by\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  dsimp only [Mir.advanceStmt] at hOther ⊢\n"
            "  simp\n"
            "  change (advanceStmt s l m).memory.locals = l at h\n"
            "  dsimp only [advanceStmt] at h\n"
            "  simp\n"
            "  try rw [h1] at hEval\n"
            "    push_neg at ⊢\n"
            "  try rw [h1] at hEval\n"
            "    custom_user_tactic at ⊢\n"
            "  have _ := try (by\n"
            "    rw [h] at hEval ⊢\n"
            "    exact 0)\n"
        )
        self.assertEqual(proof_health.scan_projection_and_rewrite_order_hazards(adv_neg), [])

        # 6. Symmetric memo derivation: scanning with `include_advisories=True` first and then
        # `include_advisories=False` must reuse cached results without re-scanning.
        sym_src = "theorem t (h hEval : 1 = 1) : 1 = 1 := by\n  try rw [h] at hEval ⊢\n  exact h\n"
        clear_in_process_caches()
        with patch.object(
            proof_health, "_scan_lean_text_uncached", wraps=proof_health._scan_lean_text_uncached
        ) as spy:
            adv_first = proof_health.scan_lean_text(
                sym_src, scan_siblings=False, include_advisories=True
            )
            def_second = proof_health.scan_lean_text(
                sym_src, scan_siblings=False, include_advisories=False
            )
            self.assertEqual(len(adv_first), 1)
            self.assertEqual(def_second, [])
            self.assertEqual(spy.call_count, 1)

    def test_a1_namespace_quotation_target_dataflow_and_try_regressions(self) -> None:
        import lean_lexer

        # 1. Single-line zero-arg tactics/clauses (`by simp end A`, `by intros end B`,
        # `structure Empty where end C`) must close their namespaces cleanly.
        same_line_closers = (
            "namespace A theorem t1 : True := by simp end A\n"
            "def outA := 0\n"
            "namespace B theorem t2 : True → True := by intros; assumption end B\n"
            "namespace B2 theorem t3 : True := by intros end B2\n"
            "def outB := 0\n"
            "namespace C structure Empty where end C\n"
            "def outC := 0\n"
        )
        tr_sc = lean_lexer.track_namespaces(same_line_closers)
        self.assertEqual(tr_sc.violations, ())
        for marker in ("def outA", "def outB", "def outC"):
            self.assertEqual(tr_sc.namespace_at(same_line_closers.index(marker)), (), marker)

        # 2. Unclosed syntax quotation earlier in the file must not disable scanning later
        # multi-line syntax quotations, and 1,000 unclosed `` `( `` stays linear (< 5 ms).
        unclosed_quot_then_valid = (
            "def broken := `(foo\n"
            "def q := `(command|\n"
            "def firstCmd := 0\n"
            "namespace Fake\n"
            "def insideFake := 1\n"
            "end Fake\n"
            ")\n"
            "def afterQuot := 2\n"
        )
        tr_uq = lean_lexer.track_namespaces(unclosed_quot_then_valid)
        self.assertEqual(tr_uq.violations, ())
        self.assertEqual(tr_uq.namespace_at(unclosed_quot_then_valid.index("def insideFake")), ())
        self.assertEqual(tr_uq.namespace_at(unclosed_quot_then_valid.index("def afterQuot")), ())

        quot_stress = ("def u := `(unclosed\n" * 600) + "namespace Real\ndef ok := 1\nend Real\n"
        quot_ms = best_of_ms(lambda: lean_lexer.track_namespaces(quot_stress), budget_ms=5.0)
        self.assertLess(quot_ms, 5.0, f"Unclosed quotation scan took {quot_ms:.2f} ms")

        # 3. `namespace ... in` with char literals `'('`, `do ...; ...`, and `⟨by ...; ..., ...⟩`.
        ns_in_edge = (
            "namespace A in def openParen : Char := '(' def outsideParen : Nat := 2\n"
            "namespace B in def m : Id Nat := do let x := 1; pure x\n"
            "def outsideDo := 0\n"
            "namespace C in theorem conj : True ∧ True := ⟨by simp; trivial, trivial⟩\n"
            "def outsideConj := 0\n"
        )
        tr_in2 = lean_lexer.track_namespaces(ns_in_edge)
        self.assertEqual(tr_in2.violations, ())
        self.assertEqual(tr_in2.namespace_at(ns_in_edge.index("openParen")), ("A",))
        self.assertEqual(tr_in2.namespace_at(ns_in_edge.index("def outsideParen")), ())
        self.assertEqual(tr_in2.namespace_at(ns_in_edge.index("pure x")), ("B",))
        self.assertEqual(tr_in2.namespace_at(ns_in_edge.index("def outsideDo")), ())
        self.assertEqual(tr_in2.namespace_at(ns_in_edge.rindex("trivial")), ("C",))
        self.assertEqual(tr_in2.namespace_at(ns_in_edge.index("def outsideConj")), ())

        # 4. Advisory target-location dataflow, `{ simp }` / ASCII bullets (`-`, `+`, `*`),
        # guillemet `dsimp only` decoy, `rw +opt` / `-opt`, and `first | try ... | rw ...`.
        R_PROJ = proof_health.RULE_SIMP_DEEP_PROJECTION_CHAIN
        S_STMT = proof_health.SUBRULE_SIMP_AFTER_PROJECTION_STATEMENT
        R_TRY = proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET

        a1_pos = (
            "theorem p : P := by\n"
            "  change (advanceStmt s l m).memory.locals = l at h1\n"
            "  dsimp only [advanceStmt]\n"
            "  simp at h1\n"
            "  have h2 : (advanceStmt s l m).memory.locals = l := h0\n"
            "  dsimp only [advanceStmt]\n"
            "  simp at h2\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  simp only [foo] at hOther\n"
            "  simp\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  dsimp only [«a, advanceStmt: b»]\n"
            "  simp\n"
            "  suffices (advanceStmt s l m).memory.locals = l by\n"
            "    { simp [advanceStmt] }\n"
            "  have h3 : (advanceStmt s l m).frame.stmtIdx = 0 := by\n"
            "    - simp [advanceStmt]\n"
            "  - try rw [h] at hEval ⊢\n"
            "  + try erw +occs [h] at hEval ⊢\n"
            "  * try rewrite -zeta [h] at hEval |-\n"
        )
        self.assertEqual(
            [(f.line, f.rule, f.subrule) for f in proof_health.scan_projection_and_rewrite_order_hazards(a1_pos)],
            [
                (4, R_PROJ, S_STMT),
                (7, R_PROJ, S_STMT),
                (10, R_PROJ, S_STMT),
                (13, R_PROJ, S_STMT),
                (15, R_PROJ, S_STMT),
                (17, R_PROJ, S_STMT),
                (18, R_TRY, ""),
                (19, R_TRY, ""),
                (20, R_TRY, ""),
            ],
        )

        a1_neg = (
            "theorem clean : P := by\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  simp only [foo] at hOther\n"
            "  have h1 : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simp only [foo]\n"
            "  first | try simp | rw [h] at hEval ⊢\n"
            "  (try simp [h]); rw [h] at hEval ⊢\n"
        )
        self.assertEqual(proof_health.scan_projection_and_rewrite_order_hazards(a1_neg), [])

    def test_b2_quotation_perf_namespace_in_and_advisory_regressions(self) -> None:
        import lean_lexer

        # 1. A single syntax quotation in a ~500 KiB file must not trigger a full-file
        # bracket regex scan (< 5.0 ms CPU budget).
        bc_with_q = "def _q := `(term| 1)\n" + EPISODE1_BYTECODEC.read_text(encoding="utf-8")
        bc_with_q_st = lean_lexer.strip_comments_and_strings_preserving_offsets(bc_with_q)
        q_ms = best_of_ms(
            lambda: lean_lexer.NamespaceTracker.from_source(bc_with_q, stripped=bc_with_q_st),
            budget_ms=5.0,
        )
        self.assertLess(q_ms, 5.0, f"ByteCodec + 1 quotation NamespaceTracker took {q_ms:.2f} ms")

        # 2. `NamespaceTracker`: primed identifiers containing keywords (`x'end`), indented
        # target commands under `namespace ... in`, col-0 commands inside syntax quotations
        # under `namespace ... in`, and guillemets containing `` `( ``.
        ns_b2 = (
            "namespace A in def f : Nat := 1 + x'end\n"
            "def outA := 0\n"
            "namespace B in\n"
            "  def inB : Nat := 1\n"
            "  def outB : Nat := 2\n"
            "namespace C in\n"
            "def q := `(command|\n"
            "def innerQuot := 1\n"
            ")\n"
            "def outC := 2\n"
            "def «fake`(open» := 0\n"
            "namespace D\n"
            "  def inD := 1\n"
            "end D\n"
        )
        tr = lean_lexer.track_namespaces(ns_b2)
        self.assertEqual(tr.violations, ())
        self.assertEqual(tr.namespace_at(ns_b2.index("x'end") + 2), ("A",))
        self.assertEqual(tr.namespace_at(ns_b2.index("def outA")), ())
        self.assertEqual(tr.namespace_at(ns_b2.index("def inB")), ("B",))
        self.assertEqual(tr.namespace_at(ns_b2.index("def outB")), ())
        self.assertEqual(tr.namespace_at(ns_b2.index(")\n")), ("C",))
        self.assertEqual(tr.namespace_at(ns_b2.index("def outC")), ())
        self.assertEqual(tr.namespace_at(ns_b2.index("def inD")), ("D",))

        # 3. Advisory regressions: `|` inside `try` (`cases` / `first` / `||` / `|>` / `rcases`
        # / `<|>`), `·` / `{` bullets before `dsimp only` -> `simp`, `simpa [my_using_lemma]`,
        # `have h (x : Nat) : ...`, `simp [-h]` erasure, and `suffices` target tracking.
        R_PROJ = proof_health.RULE_SIMP_DEEP_PROJECTION_CHAIN
        S_STMT = proof_health.SUBRULE_SIMP_AFTER_PROJECTION_STATEMENT
        R_TRY = proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET

        b2_pos = (
            "theorem p : P := by\n"
            "  try\n"
            "    cases h with\n"
            "    | inl h1 => rw [h1] at hEval ⊢\n"
            "    | inr h2 => rw [h2] at hEval ⊢\n"
            "  try\n"
            "    first\n"
            "    | simp\n"
            "    | rw [h] at hEval ⊢\n"
            "  try have h0 : b1 || b2 = true := rfl; rw [h0] at hEval ⊢\n"
            "  try have h0 := x |> f; rw [h0] at hEval ⊢\n"
            "  try rcases h with h1 | h2; rw [h1] at hEval ⊢\n"
            "  try exact h1 <|> rw [h] at hEval ⊢\n"
            "  first | try rw [h] at hEval |- | exact h2\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  · dsimp only [unrelatedDef]\n"
            "    simp\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  { dsimp only [unrelatedDef]\n"
            "    simp }\n"
            "  have : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simpa [my_using_lemma]\n"
            "  have h (x : Nat) : (advanceStmt s l m).memory.locals = l := h0 x\n"
            "  dsimp only [advanceStmt]\n"
            "  simp at h\n"
            "  suffices h : (advanceStmt s l m).memory.locals = l by\n"
            "    dsimp only [advanceStmt]\n"
            "    simp only [foo] at h\n"
            "  suffices h : (advanceStmt s l m).memory.locals = l from h0 h\n"
            "  dsimp only [advanceStmt] at hOther\n"
            "  simp\n"
        )
        self.assertEqual(
            [(f.line, f.rule, f.subrule) for f in proof_health.scan_projection_and_rewrite_order_hazards(b2_pos)],
            [
                (4, R_TRY, ""),
                (5, R_TRY, ""),
                (9, R_TRY, ""),
                (10, R_TRY, ""),
                (11, R_TRY, ""),
                (12, R_TRY, ""),
                (13, R_TRY, ""),
                (14, R_TRY, ""),
                (17, R_PROJ, S_STMT),
                (20, R_PROJ, S_STMT),
                (22, R_PROJ, S_STMT),
                (25, R_PROJ, S_STMT),
                (28, R_PROJ, S_STMT),
                (31, R_PROJ, S_STMT),
            ],
        )

        b2_neg = (
            "theorem clean : P := by\n"
            "  have h (x : Nat) : (advanceStmt s l m).memory.locals = l := h0 x\n"
            "  simp only [foo]\n"
            "  have h2 : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simp [-h2]\n"
            "  have «h3» : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simp [-«h3»]\n"
            "  suffices h4 : (advanceStmt s l m).memory.locals = l by\n"
            "    simp only [foo] at hOther\n"
            "  first | try simp | rw [h] at hEval ⊢\n"
        )
        self.assertEqual(proof_health.scan_projection_and_rewrite_order_hazards(b2_neg), [])

    def test_a2_suffices_first_arm_proj_arg_and_inline_comment_regressions(self) -> None:
        import lean_lexer

        # 1. Balanced attributes with syntax quotations (`@[my_attr `(command| @[simp] ...)]`
        # vs top-level quoted `@[simp]` vs unclosed `@[broken`).
        attr_quot_src = (
            "@[my_attr `(command| @[simp] def x := 1)]\n"
            "def realDecl : Nat := 0\n"
            "def quotedOnly := `(command| @[simp] def y := 2)\n"
            "@[broken\n"
            "@[simp] def afterBroken : Nat := 3\n"
        )
        self.assertEqual(
            [(a.line_no, a.content) for a in lean_lexer.scan_balanced_attributes(attr_quot_src)],
            [(1, "my_attr `(command| @[simp] def x := 1)"), (5, "simp")],
        )

        # 2. `NamespaceTracker`: inline `/- ... -/` block comments around `namespace ... in`
        # and col-0 `section` / `end` tokens inside multi-line bracket expressions.
        ns_a2 = (
            "namespace A in\n"
            "/- comment -/ theorem inA : True := by\n"
            "  open Classical in\n"
            "  trivial\n"
            "def outA := 2\n"
            "/- comment -/ namespace A2 in\n"
            "theorem inA2 : True := by\n"
            "  open Classical in\n"
            "  trivial\n"
            "def outA2 := 2\n"
            "namespace B in\n"
            "  def inB : Nat := 1\n"
            "  /- comment -/ def outB : Nat := 2\n"
            "namespace Foo\n"
            "def xs : List Nat := [\n"
            "1,\n"
            "section,\n"
            "end\n"
            "]\n"
            "def stillInFoo := 0\n"
            "end Foo\n"
        )
        tr_a2 = lean_lexer.track_namespaces(ns_a2)
        self.assertEqual(tr_a2.violations, ())
        t1 = ns_a2.index("trivial")
        self.assertEqual(tr_a2.namespace_at(t1), ("A",))
        self.assertEqual(tr_a2.namespace_at(ns_a2.index("def outA")), ())
        t2 = ns_a2.index("trivial", t1 + 1)
        self.assertEqual(tr_a2.namespace_at(t2), ("A2",))
        self.assertEqual(tr_a2.namespace_at(ns_a2.index("def outA2")), ())
        self.assertEqual(tr_a2.namespace_at(ns_a2.index("def inB")), ("B",))
        self.assertEqual(tr_a2.namespace_at(ns_a2.index("def outB")), ())
        self.assertEqual(tr_a2.namespace_at(ns_a2.index("def stillInFoo")), ("Foo",))

        # 3. Advisory regressions: `suffices h : <chain> by` canonical `dsimp at h; simp [h]`
        # fix and post-`by` sibling goal, `first | simp; try ... | rw ...` arms, and
        # `_call_mentions_ident` projections (`h.symm`, `h.1`, `«h».symm`) vs qualified
        # (`Foo.h`, `Foo.«h»`) / config (`-zeta`, `zeta := false`) names.
        R_PROJ = proof_health.RULE_SIMP_DEEP_PROJECTION_CHAIN
        S_STMT = proof_health.SUBRULE_SIMP_AFTER_PROJECTION_STATEMENT
        R_TRY = proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET

        a2_pos = (
            "theorem p : P := by\n"
            "  have h1 : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simp [h1.symm]\n"
            "  have h2 : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simpa using h2.1\n"
            "  have «h3» : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simp [«h3».symm]\n"
            "  suffices h4 : (advanceStmt s l m).memory.locals = l by\n"
            "    exact h0 h4\n"
            "  simp\n"
            "  cases hc with | inl c1 => try cases hd with | inl a => rw [a] at hEval ⊢ | inr b => exact h0\n"
            "  rcases hc with c1 | c2; try cases hd with | inl a => rw [a] at hEval ⊢ | inr b => exact h0\n"
        )
        self.assertEqual(
            [
                (f.line, f.rule, f.subrule)
                for f in proof_health.scan_projection_and_rewrite_order_hazards(a2_pos)
            ],
            [
                (3, R_PROJ, S_STMT),
                (5, R_PROJ, S_STMT),
                (7, R_PROJ, S_STMT),
                (10, R_PROJ, S_STMT),
                (11, R_TRY, ""),
                (12, R_TRY, ""),
            ],
        )

        a2_neg = (
            "theorem clean : P := by\n"
            "  suffices h1 : (advanceStmt s l m).memory.locals = l by\n"
            "    dsimp only [advanceStmt] at h1\n"
            "    simp [h1]\n"
            "  dsimp only [advanceStmt]\n"
            "  simp\n"
            "  suffices h2 : (advanceStmt s l m).memory.locals = l by\n"
            "    simp only [foo]\n"
            "    exact h0 h2\n"
            "  dsimp only [advanceStmt]\n"
            "  simp\n"
            "  have h3 : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simp [Foo.h3]\n"
            "  have «h4» : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simp [Foo.«h4»]\n"
            "  have zeta : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simp -zeta +zeta (config := { zeta := false }) [foo]\n"
            "  first | simp; try exact h0 | rw [h] at hEval ⊢\n"
            "  first | focus try simp | rw [h] at hEval ⊢\n"
            "  (first | simp; try exact h0 | rw [h] at hEval ⊢)\n"
            "  first\n"
            "  | simp; try exact h0 | rw [h] at hEval ⊢\n"
        )
        self.assertEqual(proof_health.scan_projection_and_rewrite_order_hazards(a2_neg), [])

    def test_b3_nested_comment_indent_guillemet_dsimp_and_first_regressions(self) -> None:
        import lean_lexer

        # 1. `_inside_guillemets`: primed identifier immediately before `«' ... »` is a
        # real guillemet identifier, not a `'«'` char literal.
        primed_gui = "def f := x'«' @[simp] »\n"
        self.assertEqual(lean_lexer.scan_balanced_attributes(primed_gui), [])
        ns_primed_gui = "namespace Real\ndef f := x'«' end Real »\ndef g := 1\nend Real\n"
        tr_pg = lean_lexer.track_namespaces(ns_primed_gui)
        self.assertEqual(tr_pg.violations, ())
        self.assertEqual(tr_pg.namespace_at(ns_primed_gui.index("def g")), ("Real",))

        # 2. `_true_line_indent`: nested multi-line block comments and mid-line `namespace ... in`
        # after an earlier col-0 comment must not miscompute indentation.
        ns_nested_c = (
            "/- header -/\n"
            "namespace Outer\n"
            "  def x := 1; namespace A in def inA := 1\n"
            "  def outA := 2\n"
            "end Outer\n"
            "namespace B in\n"
            "  def inB : Nat := 1\n"
            "/- outer col 0\n"
            "    /- nested col 4 -/\n"
            "-/ def outB : Nat := 2\n"
            "namespace C in\n"
            "  def inC : Nat := 1\n"
            "/- outer col 0\n"
            "    /- nested col 4 -/\n"
            "    -/ def outC : Nat := 2\n"
        )
        tr_nc = lean_lexer.track_namespaces(ns_nested_c)
        self.assertEqual(tr_nc.violations, ())
        self.assertEqual(tr_nc.namespace_at(ns_nested_c.index("def outA")), ("Outer",))
        self.assertEqual(tr_nc.namespace_at(ns_nested_c.index("def outB")), ())
        self.assertEqual(tr_nc.namespace_at(ns_nested_c.index("def outC")), ())

        # 3. `_may_have_unclosed_bracket`: stray closer before opener in same declaration must
        # still suppress col-0 `section` inside the subsequent balanced multi-line `(...)`.
        ns_stray = (
            "namespace Foo\n"
            "def ok :=\n"
            "  let bad := 1)\n"
            "  (1,\n"
            "section S\n"
            ")\n"
            "def stillInFoo := 0\n"
            "end Foo\n"
        )
        tr_stray = lean_lexer.track_namespaces(ns_stray)
        self.assertEqual(tr_stray.violations, ())
        self.assertEqual(tr_stray.namespace_at(ns_stray.index("def stillInFoo")), ("Foo",))

        # 4. Advisory regressions: multi-line `cases` / `first` inside `first | try ...`,
        # hypothesis named `only` in `simp [only]` / nested `simpa ... using (by simpa [only] ...)`,
        # non-`only` `dsimp` / `dsimp [unrelatedDef]` / `dsimp [-advanceStmt]` not collapsing
        # plain `def advanceStmt`, and braced `suffices ... by { ... }; simp` / same-col `{ ... }`.
        R_PROJ = proof_health.RULE_SIMP_DEEP_PROJECTION_CHAIN
        S_STMT = proof_health.SUBRULE_SIMP_AFTER_PROJECTION_STATEMENT
        R_TRY = proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET

        b3_pos = (
            "theorem p : P := by\n"
            "  first\n"
            "  | try\n"
            "      cases h with\n"
            "      | inl a => rw [a] at hEval ⊢\n"
            "      | inr b => exact b\n"
            "  | exact h0\n"
            "  first\n"
            "  | try cases h with\n"
            "      | inl a => rw [a] at hEval ⊢\n"
            "  | exact h0\n"
            "  first\n"
            "  | try\n"
            "      first\n"
            "      | simp\n"
            "      | rw [h] at hEval ⊢\n"
            "  | exact h0\n"
            "  have only : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simp [only]\n"
            "  have only : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simpa only [foo] using (by simpa [only] using h1)\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  dsimp\n"
            "  simp\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  dsimp [unrelatedDef]\n"
            "  simp\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  dsimp [-advanceStmt]\n"
            "  simp\n"
            "  suffices h1 : (advanceStmt s l m).memory.locals = l by { exact h0 h1 }; simp\n"
            "  suffices h2 : (advanceStmt s l m).memory.locals = l by\n"
            "  { exact h0 h2 }\n"
            "  simp\n"
        )
        self.assertEqual(
            [
                (f.line, f.rule, f.subrule)
                for f in proof_health.scan_projection_and_rewrite_order_hazards(b3_pos)
            ],
            [
                (5, R_TRY, ""),
                (10, R_TRY, ""),
                (16, R_TRY, ""),
                (19, R_PROJ, S_STMT),
                (21, R_PROJ, S_STMT),
                (24, R_PROJ, S_STMT),
                (27, R_PROJ, S_STMT),
                (30, R_PROJ, S_STMT),
                (31, R_PROJ, S_STMT),
                (34, R_PROJ, S_STMT),
            ],
        )

        b3_neg = (
            "theorem clean : P := by\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  dsimp [advanceStmt]\n"
            "  simp\n"
            "  have only : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simp only [foo]\n"
            "  first\n"
            "  | try simp\n"
            "  | rw [h] at hEval ⊢\n"
            "  suffices h : (advanceStmt s l m).memory.locals = l by { exact h0 h }\n"
            "  dsimp only [advanceStmt]\n"
            "  simp\n"
        )
        self.assertEqual(proof_health.scan_projection_and_rewrite_order_hazards(b3_neg), [])

    def test_a3_forward_comment_indent_in_scope_blocks_and_advisory_regressions(self) -> None:
        import lean_lexer

        # 1. `_true_line_indent`: overlapping `/-/` inside nested block comments, `-- fake -/`
        # line comments before `/-`, chained `/- c1 -/ /- c2\n  -/`, and trailing multi-line
        # comments on indented lines.
        ns_comments = (
            "namespace B1 in\n"
            "  def inB1 : Nat := 1\n"
            "/- outer col 0\n"
            "    /- nested /-/ still outer\n"
            "    -/ def outB1 : Nat := 2\n"
            "namespace B2 in\n"
            "  def inB2 : Nat := 1\n"
            "-- fake -/ before block comment\n"
            "/- outer col 0\n"
            "    -/ def outB2 : Nat := 2\n"
            "namespace B3 in\n"
            "  def inB3 : Nat := 1\n"
            "/- c1 -/ /- c2\n"
            "    -/ def outB3 : Nat := 2\n"
            "namespace B4 in\n"
            "  def inB4 : Nat := 1 /- trailing\n"
            "     comment -/ def outB4 : Nat := 2\n"
        )
        tr_c = lean_lexer.track_namespaces(ns_comments)
        self.assertEqual(tr_c.violations, ())
        for idx in ("1", "2", "3", "4"):
            self.assertEqual(tr_c.namespace_at(ns_comments.index(f"def inB{idx}")), (f"B{idx}",))
            self.assertEqual(tr_c.namespace_at(ns_comments.index(f"def outB{idx}")), ())

        # 2. Exact stack prefilter for stray closer + open bracket + closed inner pair, and
        # `namespace A in` governing `namespace B ... end B` and `section S ... end S` blocks.
        ns_blk = (
            "namespace Foo\n"
            "def ok (x : Nat) :=\n"
            "  let bad := 1)\n"
            "  (1, (0),\n"
            "section S\n"
            ")\n"
            "def stillInFoo := 0\n"
            "end Foo\n"
            "namespace A in\n"
            "namespace B.C\n"
            "def inABC : Nat := 1\n"
            "end B.C\n"
            "def afterABC : Nat := 2\n"
            "namespace D in\n"
            "section Sec\n"
            "def inDSec : Nat := 3\n"
            "end Sec\n"
            "def afterDSec : Nat := 4\n"
        )
        tr_b = lean_lexer.track_namespaces(ns_blk)
        self.assertEqual(tr_b.violations, ())
        self.assertEqual(tr_b.namespace_at(ns_blk.index("def stillInFoo")), ("Foo",))
        self.assertEqual(tr_b.namespace_at(ns_blk.index("def inABC")), ("A", "B", "C"))
        self.assertEqual(tr_b.namespace_at(ns_blk.index("def afterABC")), ())
        self.assertEqual(tr_b.namespace_at(ns_blk.index("def inDSec")), ("D",))
        self.assertEqual(tr_b.namespace_at(ns_blk.index("def afterDSec")), ())

        # 3. Advisory regressions: multi-line `try` after combinators (`all_goals`, `by`,
        # `| inl _ =>`), binder/declaration `try` decoys (`have try := ...`, `(try : Nat)`,
        # `theorem try`), whitespace-separated `simp !` / `simpa !` / `dsimp !`, mid-line
        # `; change <chain>\n  simp`, and parenthesized `suffices` continuations.
        R_PROJ = proof_health.RULE_SIMP_DEEP_PROJECTION_CHAIN
        S_ARG = proof_health.SUBRULE_PROJECTION_IN_SIMP_ARGS
        S_STMT = proof_health.SUBRULE_SIMP_AFTER_PROJECTION_STATEMENT
        R_TRY = proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET

        a3_pos = (
            "theorem p : P := by\n"
            "  all_goals try\n"
            "    rw [h] at hEval ⊢\n"
            "  cases hc with\n"
            "  | inl _ => try\n"
            "    erw [h] at hEval ⊢\n"
            "  | inr _ => exact h0\n"
            "  simp ! [(advanceStmt s l m).memory.locals]\n"
            "  simpa ? [foo] using (advanceStmt s l m).frame.stmtIdx\n"
            "  intro h0; change (advanceStmt s l m).memory.locals = l\n"
            "  simp\n"
            "  suffices h1 : (advanceStmt s l m).memory.locals = l by (exact h0 h1); simp\n"
            "  (suffices h2 : (advanceStmt s l m).memory.locals = l by exact h0 h2); simp\n"
        )
        self.assertEqual(
            [
                (f.line, f.rule, f.subrule)
                for f in proof_health.scan_projection_and_rewrite_order_hazards(a3_pos)
            ],
            [
                (3, R_TRY, ""),
                (6, R_TRY, ""),
                (8, R_PROJ, S_ARG),
                (9, R_PROJ, S_ARG),
                (11, R_PROJ, S_STMT),
                (12, R_PROJ, S_STMT),
                (13, R_PROJ, S_STMT),
            ],
        )

        a3_neg = (
            "theorem try (h hEval : 1 = 1) : 1 = 1 := by\n"
            "  rw [h] at hEval ⊢\n"
            "theorem clean (try : Nat) : P := by\n"
            "  have try := by rw [h] at hEval ⊢\n"
            "  intro try; rw [h] at hEval ⊢\n"
            "  change (advanceStmt s l m).memory.locals = l\n"
            "  dsimp ! [advanceStmt]\n"
            "  simp\n"
            "  have hProofOnly : Nat := show (advanceStmt s l m).memory.locals = l from rfl\n"
            "  simp\n"
        )
        self.assertEqual(proof_health.scan_projection_and_rewrite_order_hazards(a3_neg), [])

    def test_b4_tail_perf_namespace_in_marks_try_siblings_and_seq_regressions(self) -> None:
        import lean_lexer

        # 1. `NamespaceTracker` hot-path latency: the tail unmatched-closer gate and col-0 block
        # reuse keep `ByteCodec.lean` (< 5.0 ms) and repeated `namespace ... export ... end`
        # blocks linear instead of rescanning balanced 8 KiB windows per scope keyword.
        bc_text = EPISODE1_BYTECODEC.read_text(encoding="utf-8")
        bc_st = lean_lexer.strip_comments_and_strings_preserving_offsets(bc_text)
        lean_lexer.NamespaceTracker.from_source(bc_text, stripped=bc_st)  # warm regex cache
        bc_ms = best_of_ms(
            lambda: lean_lexer.NamespaceTracker.from_source(bc_text, stripped=bc_st),
            budget_ms=5.0,
        )
        self.assertLess(bc_ms, 5.0, f"ByteCodec NamespaceTracker took {bc_ms:.2f} ms")

        export_blocks = "".join(
            f"namespace N{i}\nexport Foo.N{i} (a b c)\nend N{i}\n" for i in range(80)
        )
        eb_st = lean_lexer.strip_comments_and_strings_preserving_offsets(export_blocks)
        eb_ms = best_of_ms(
            lambda: lean_lexer.NamespaceTracker.from_source(export_blocks, stripped=eb_st),
            budget_ms=5.0,
        )
        self.assertLess(eb_ms, 5.0, f"80 export-block NamespaceTracker took {eb_ms:.2f} ms")

        # 2. `NamespaceTracker` correctness: partial `end` on multi-component `namespace A.B in`,
        # non-`in` `namespace`/`section` containing body `in` tokens, and >8 chained block comments.
        ns_partial = (
            "namespace Outer\n"
            "namespace A.B in\n"
            "namespace C\n"
            "  def x := 1\n"
            "end B.C\n"
            "def after := 2\n"
            "end Outer\n"
        )
        tr_p = lean_lexer.track_namespaces(ns_partial)
        self.assertEqual(tr_p.violations, ())
        self.assertEqual(tr_p.namespace_at(ns_partial.index("def after")), ("Outer",))

        ns_body_in = (
            "namespace A in\n"
            "namespace B\n"
            "  custom_cmd x in y\n"
            "  def inAB := 1\n"
            "end B\n"
            "def afterAB := 2\n"
            "namespace C in\n"
            "section S\n"
            "  custom_cmd x in y\n"
            "  def inCS := 1\n"
            "end S\n"
            "def afterCS := 2\n"
        )
        tr_bi = lean_lexer.track_namespaces(ns_body_in)
        self.assertEqual(tr_bi.violations, ())
        self.assertEqual(tr_bi.namespace_at(ns_body_in.index("def inAB")), ("A", "B"))
        self.assertEqual(tr_bi.namespace_at(ns_body_in.index("def afterAB")), ())
        self.assertEqual(tr_bi.namespace_at(ns_body_in.index("def inCS")), ("C",))
        self.assertEqual(tr_bi.namespace_at(ns_body_in.index("def afterCS")), ())

        ns_chain10 = (
            "namespace Deep in\n"
            "def inDeep := by\n"
            "    /- c0\n"
            + "    -/ /- c\n" * 10
            + "    -/ open Nat in\n"
            "    exact 1\n"
            "def outDeep := 2\n"
        )
        tr_c10 = lean_lexer.track_namespaces(ns_chain10)
        self.assertEqual(tr_c10.violations, ())
        self.assertEqual(tr_c10.namespace_at(ns_chain10.index("exact 1")), ("Deep",))
        self.assertEqual(tr_c10.namespace_at(ns_chain10.index("def outDeep")), ())

        # 3. Advisory regressions: exact `args_start` after whitespace-separated `?`/`!`,
        # `simpa ? !`, aligned siblings outside `try`, bullet-prefixed `; change` / `; try`,
        # `have h0 := 1; change`, `| pat => tac; change`, and parenthesised statements.
        R_PROJ = proof_health.RULE_SIMP_DEEP_PROJECTION_CHAIN
        S_ARG = proof_health.SUBRULE_PROJECTION_IN_SIMP_ARGS
        S_STMT = proof_health.SUBRULE_SIMP_AFTER_PROJECTION_STATEMENT
        R_TRY = proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET

        b4_pos = (
            "theorem p : P := by\n"
            "  have h1 : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simpa ? ! using h1\n"
            "  simpa ? ! [foo] using (advanceStmt s l m).memory.locals\n"
            "  have h2 : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simpa ? ! [foo] at hOther using h2\n"
            "  have h0 := 1; change (advanceStmt s l m).memory.locals = l\n"
            "  simp\n"
            "  · intro h0; change (advanceStmt s l m).memory.locals = l\n"
            "    simp\n"
            "  - intro h0; have h3 : (advanceStmt s l m).memory.locals = l := h4\n"
            "    simp [h3]\n"
            "  cases hc with\n"
            "  | inl _ => intro h0; change (advanceStmt s l m).memory.locals = l\n"
            "             simp\n"
            "  (suffices h5 : (advanceStmt s l m).memory.locals = l by exact h0 h5)\n"
            "  simp\n"
            "  (change (advanceStmt s l m).memory.locals = l)\n"
            "  simp\n"
            "  all_goals try rw [h]\n"
            "    at hEval ⊢\n"
            "  have h6 : P := by try\n"
            "    rw [h] at hEval ⊢\n"
        )
        self.assertEqual(
            [
                (f.line, f.rule, f.subrule)
                for f in proof_health.scan_projection_and_rewrite_order_hazards(b4_pos)
            ],
            [
                (3, R_PROJ, S_STMT),
                (4, R_PROJ, S_ARG),
                (6, R_PROJ, S_STMT),
                (8, R_PROJ, S_STMT),
                (10, R_PROJ, S_STMT),
                (12, R_PROJ, S_STMT),
                (15, R_PROJ, S_STMT),
                (17, R_PROJ, S_STMT),
                (19, R_PROJ, S_STMT),
                (21, R_TRY, ""),
                (23, R_TRY, ""),
            ],
        )

        b4_neg = (
            "theorem clean : P := by\n"
            "  have zeta : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simp !-zeta [foo]\n"
            "  have zeta2 : (advanceStmt s l m).memory.locals = l := h0\n"
            "  simpa !-zeta2 [foo] using h1\n"
            "  cases hc with\n"
            "  | inl _ => try trivial\n"
            "             rw [h] at hEval ⊢\n"
            "             exact h0\n"
            "  | inr _ => try\n"
            "               trivial\n"
            "             rw [h] at hEval ⊢\n"
            "  have h1 : P := by try trivial\n"
            "                    rw [h] at hEval ⊢\n"
            "  all_goals try trivial\n"
            "            rw [h] at hEval ⊢\n"
            "  · simp; try trivial\n"
            "    rw [h] at hEval ⊢\n"
            "  have h2 : True := by trivial; change (advanceStmt s l m).memory.locals = l\n"
            "  simp\n"
            "  have hProof : Nat := (show (advanceStmt s l m).memory.locals = l from rfl)\n"
            "  simp\n"
            "  have _ : P := (by suffices h3 : (advanceStmt s l m).memory.locals = l by exact h0 h3); simp\n"
            "  cases hc with\n"
            "  | inl _ => intro h0; change (advanceStmt s l m).memory.locals = l\n"
            "  | inr _ => simp\n"
        )
        self.assertEqual(proof_health.scan_projection_and_rewrite_order_hazards(b4_neg), [])

    def test_a4_reserved_decl_bounds_guillemet_arrows_term_parens_and_combinator_continuations(
        self,
    ) -> None:
        import lean_lexer

        # 1. Non-reserved core-Lean identifiers (`alias`, `lemma`, `run_cmd`, `add_decl_doc`,
        # `register_option`) at col 0 inside multi-line bracket expressions must not truncate
        # `_enclosing_col0_block` before a col-0 `end` / `section`, and `meta` modifier is
        # skipped like `private` / `unsafe`.
        ns_a4 = (
            "namespace Foo\n"
            "meta def checkWords (alias lemma run_cmd : Nat) : List Nat := [\n"
            "alias,\n"
            "lemma,\n"
            "run_cmd,\n"
            "end\n"
            "]\n"
            "def stillInFoo := 0\n"
            "end Foo\n"
            "namespace M in\n"
            "meta def inM : Nat := 1\n"
            "def outM : Nat := 2\n"
        )
        tr_a4 = lean_lexer.track_namespaces(ns_a4)
        self.assertEqual(tr_a4.violations, ())
        self.assertEqual(tr_a4.namespace_at(ns_a4.index("def stillInFoo")), ("Foo",))
        self.assertEqual(tr_a4.namespace_at(ns_a4.index("inM")), ("M",))
        self.assertEqual(tr_a4.namespace_at(ns_a4.index("def outM")), ())

        # 2. Advisory regressions: guillemets/char literals/lambda arrows in `_statement_seq_col`
        # (`intro «a=>b»; change`, `| inl «(» => intro h0; change`, `| inl _ => · intro h0; change`,
        # `have f := fun x => x; change`), multi-line term-continuation `(show ...)` under `:=`
        # not falsely flagged, `first | ...` after `rcases ... | ...` / `cases ... =>` / `fun =>`,
        # and `<;>` / `<|>` multi-line continuations after combinator-prefixed `try`.
        R_PROJ = proof_health.RULE_SIMP_DEEP_PROJECTION_CHAIN
        S_STMT = proof_health.SUBRULE_SIMP_AFTER_PROJECTION_STATEMENT
        R_TRY = proof_health.RULE_TRY_RW_HYP_BEFORE_TARGET

        a4_pos = (
            "theorem p : P := by\n"
            "  intro «a=>b»; change (advanceStmt s l m).memory.locals = l\n"
            "  simp\n"
            "  cases hc with\n"
            "  | inl «(» => intro h0; change (advanceStmt s l m).memory.locals = l\n"
            "               simp\n"
            "  | inr _ => · intro h0; change (advanceStmt s l m).memory.locals = l\n"
            "               simp\n"
            "  have f := fun x => x; change (advanceStmt s l m).memory.locals = l\n"
            "  simp\n"
            "  all_goals try simp <;>\n"
            "    rw [h] at hEval ⊢\n"
            "  cases hc with\n"
            "  | inl _ => try exact h1 <|>\n"
            "    erw [h] at hEval ⊢\n"
            "  | inr _ => exact h0\n"
        )
        self.assertEqual(
            [
                (f.line, f.rule, f.subrule)
                for f in proof_health.scan_projection_and_rewrite_order_hazards(a4_pos)
            ],
            [
                (3, R_PROJ, S_STMT),
                (6, R_PROJ, S_STMT),
                (8, R_PROJ, S_STMT),
                (10, R_PROJ, S_STMT),
                (12, R_TRY, ""),
                (15, R_TRY, ""),
            ],
        )

        a4_neg = (
            "theorem clean : P := by\n"
            "  have hProof : Prop :=\n"
            "    (show (advanceStmt s l m).memory.locals = l from h0); simp\n"
            "  rcases hc with c1 | c2; first | try simp | rw [h] at hEval ⊢\n"
            "  cases hc with | inl c1 => first | try simp | rw [h] at hEval ⊢ | inr _ => exact h0\n"
            "  first | exact «a=>b»; try simp | rw [h] at hEval ⊢\n"
            "  first | have f := fun x => x; try simp | rw [h] at hEval ⊢\n"
        )
        self.assertEqual(proof_health.scan_projection_and_rewrite_order_hazards(a4_neg), [])

    def test_nested_standalone_attr_open_rejected_in_match_balanced_attribute(self) -> None:
        # Unquoted, non-as-pattern nested `@[` inside `@[...]` is malformed and must return `None`,
        # whereas `@[` inside syntax quotations `` `(@[...]) `` and identifier as-patterns `x@[y]`
        # remains balanced.
        lx = proof_health.lean_lexer
        self.assertIsNone(lx.match_balanced_attribute("@[a @[b] ]", 0))
        self.assertEqual(
            [(s.start_pos, s.end_pos, s.content) for s in lx.scan_balanced_attributes("@[a @[b] ]\ndef f := 1\n")],
            [(4, 8, "b")],
        )
        quoted = "@[foo `(@[bar])]"
        self.assertEqual(lx.match_balanced_attribute(quoted, 0), len(quoted))
        as_pat = "@[foo x@[y]]"
        self.assertEqual(lx.match_balanced_attribute(as_pat, 0), len(as_pat))


class TestNegationPrecedenceAndFalseElimExemption(unittest.TestCase):
    """Regression and adversarial tests for:
    1. Lean 4 precedence of prefix `¬` vs looser connectives (`→`, `->`, `↔`, `<->`, `∨`, `\\/`, `∧`, `/\\`)
       and top-level `≠` inside implications (fixing `dite` false positives without weakening
       `¬ (P → α)` / `P → α` detection).
    2. Narrow single-premise `False`-elimination (`noConfusion`) exemption (fixing `boolFalseNeTrue`
       / `boolTrueNeFalse` without weakening non-`False` or multi-premise vacuity detection).
    3. Exact `proof_health.audit_lean_text` vs `check_trusted.audit_lean_text` parity.
    """

    def setUp(self) -> None:
        proof_health.clear_in_process_caches()

    def test_looser_than_not_delimiters_and_binders(self) -> None:
        # `[adv B1]`: A0 tested `_has_top_level_arrow`, a helper nothing called; this is the
        # precedence scan the auditor actually runs.
        fn = proof_health._has_top_level_looser_than_not
        for yes in (
            "¬ P → α",
            "¬ P -> α",
            "¬ (P) → α",
            "¬ f ⟨a, b⟩ → c",
            "¬ (∀ x, P x) → Q",
            "¬ P → ∀ x, Q x",
            "¬ a = b → c",
            "¬ P ↔ Q",
            "¬ P <-> Q",
            "¬ P ∨ Q",
            "¬ P \\/ Q",
            "¬ P ∧ Q",
            "¬ P /\\ Q",
        ):
            self.assertTrue(fn(yes), yes)
        for no in (
            "¬ (P → α)",
            "¬ (P -> α)",
            "¬ f [P → α]",
            "¬ { x : Nat // x → y }",
            "¬ ⟨a → b, c⟩",
            "¬ «a → b»",
            "¬ ∀ x, P x → Q x",
            "¬ ∃ x, P x → Q x",
            "¬ f = fun x => x ∧ y",
            "¬ True",
            "x <- y",
            "f x => y",
        ):
            self.assertFalse(fn(no), no)

    def test_negation_precedence_dite_and_implication_false_positives_fixed(self) -> None:
        clean_cases = [
            (
                "dite_unicode_true",
                "private theorem dite_prop_true {α : Type} {P : Prop} {inst : Decidable P}\n"
                "    {t : P → α} {e : ¬ P → α} (h : P) : (@dite α P inst t e) = t h := by sorry\n",
            ),
            (
                "dite_unicode_false",
                "private theorem dite_prop_false {α : Type} {P : Prop} {inst : Decidable P}\n"
                "    {t : P → α} {e : ¬ P → α} (h : ¬ P) : (@dite α P inst t e) = e h := by sorry\n",
            ),
            (
                "dite_ascii_arrow",
                "theorem dite_ascii {α : Type} {P : Prop} {t : P -> α} {e : ¬ P -> α} (h : P) : t h = t h := rfl\n",
            ),
            (
                "dite_no_space_not",
                "theorem dite_nospace {α : Type} {P : Prop} {t : P → α} {e : ¬P → α} (h : P) : P := h\n",
            ),
            (
                "dite_eq_neq_arrows",
                "theorem dite_eq {α : Type} {a b : Nat} {t : a = b → α} {e : a ≠ b → α} (h : a = b) : t h = t h := rfl\n",
            ),
            (
                "not_true_arrow_fn",
                "theorem not_true_fn {α : Type} (f : ¬ True → α) (g : ¬ (x = x) → α) : x = y := by sorry\n",
            ),
            (
                "not_true_ascii_arrow_fn",
                "theorem not_true_ascii {α : Type} (f : ¬ True -> α) (g : ¬ x = x -> α) : x = y := by sorry\n",
            ),
            (
                "not_or_satisfiable",
                "theorem not_or_sat (P Q : Prop) (h1 : ¬ P ∨ Q) (h2 : P ∨ Q) : Q := by sorry\n",
            ),
            (
                "not_true_or_satisfiable",
                "theorem not_true_or_sat (P : Prop) (h : ¬ True ∨ P) : P := by sorry\n",
            ),
            (
                "double_neg_arrow_branches",
                "theorem dbl_neg_arrow {α : Type} {P : Prop} (t : ¬ P → α) (e : ¬ ¬ P → α) : x = y := by sorry\n",
            ),
            (
                "conj_antecedent_arrow",
                "theorem conj_ant {α : Type} {P : Prop} (f : false = true ∧ P → α) : x = y := by sorry\n",
            ),
            (
                "disjoint_ctor_arrow",
                "theorem ctor_ant {α : Type} (x : Nat) (xs : List Nat) (f : none = some x → α) (g : [] = x :: xs → α) : x = 0 := by sorry\n",
            ),
        ]
        for label, src in clean_cases:
            self.assertNotIn(
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                _rules(audit.scan_lean_text(src)),
                label,
            )
            self.assertEqual(scan67(src), [], label)

    def test_parenthesized_negated_implication_and_quantified_contradictions_still_flagged(self) -> None:
        bad_cases = [
            ("paren_not_imp", "theorem bad (P : Prop) (α : Type) (h1 : ¬ (P → α)) (h2 : P → α) : x = 1 := by sorry\n"),
            ("paren_not_imp_nospace", "theorem bad (P : Prop) (α : Type) (h1 : ¬(P → α)) (h2 : P → α) : x = 1 := by sorry\n"),
            ("paren_not_imp_ascii", "theorem bad (P : Prop) (α : Type) (h1 : ¬ (P -> α)) (h2 : P -> α) : x = 1 := by sorry\n"),
            ("paren_not_or", "theorem bad (P Q : Prop) (h1 : ¬ (P ∨ Q)) (h2 : P ∨ Q) : x = 1 := by sorry\n"),
            ("paren_not_and", "theorem bad (P Q : Prop) (h1 : ¬ (P ∧ Q)) (h2 : P ∧ Q) : x = 1 := by sorry\n"),
            ("paren_not_neg_imp", "theorem bad (P : Prop) (α : Type) (h1 : ¬ (¬ P → α)) (h2 : ¬ P → α) : x = 1 := by sorry\n"),
            ("not_forall_imp", "theorem bad (P Q : Nat → Prop) (h1 : ¬ ∀ x, P x → Q x) (h2 : ∀ x, P x → Q x) : 0 = 1 := by sorry\n"),
            ("double_neg_pair", "theorem bad (P : Prop) (h1 : ¬ P) (h2 : ¬ ¬ P) : 0 = 1 := by sorry\n"),
            ("not_true_direct", "theorem bad (h : ¬ True) : 0 = 1 := by sorry\n"),
            ("not_refl_eq_direct", "theorem bad (x : Nat) (h : ¬ (x = x)) : 0 = 1 := by sorry\n"),
            ("not_refl_arrow_eq", "theorem bad (P : Prop) (α : Type) (h : ¬ ((P → α) = (P → α))) : 0 = 1 := by sorry\n"),
        ]
        for label, src in bad_cases:
            self.assertIn(
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                _rules(audit.scan_lean_text(src)),
                label,
            )
            self.assertIn(
                (R7, audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS, 1),
                scan67(src),
                label,
            )

    def test_single_premise_false_elim_exemptions_and_strict_rejections(self) -> None:
        # Legitimate single-premise `False`-elimination (`noConfusion` / refutation) lemmas -> clean.
        exempt_cases = [
            ("bool_false_ne_true", "private theorem boolFalseNeTrue (h : false = true) : False := Bool.noConfusion h\n"),
            ("bool_true_ne_false", "private theorem boolTrueNeFalse (h : true = false) : False := Bool.noConfusion h\n"),
            ("bool_qual", "theorem boolQual (h : Bool.false = Bool.true) : False := Bool.noConfusion h\n"),
            ("with_data_binder", "theorem withBool {a : Bool} (h : false = true) : False := Bool.noConfusion h\n"),
            ("nat_lt_zero", "theorem natLtZero (n : Nat) (h : n < 0) : False := Nat.not_lt_zero n h\n"),
            ("opt_none_some", "theorem optNe {α : Type u} (x : α) (h : none = some x) : False := by nomatch h\n"),
            ("list_nil_cons", "theorem listNe {α : Type} (x : α) (xs : List α) (h : [] = x :: xs) : False := by nomatch h\n"),
            ("safe_decidable_inst", "theorem withDec {P : Prop} [Decidable P] (h : false = true) : False := Bool.noConfusion h\n"),
            ("safe_decidable_named", "theorem withDecN {a b : Nat} [d : Decidable (a = b)] (h : false = true) : False := Bool.noConfusion h\n"),
            ("forall_anon_all_scope", "theorem forallLtZero : ∀ n : Nat, n < 0 → False := fun _ h => Nat.not_lt_zero _ h\n"),
        ]
        for label, src in exempt_cases:
            self.assertEqual(audit.scan_lean_text(src), [], label)
            self.assertEqual(scan67(src), [], label)

        # Non-`False` conclusion, multi-premise, conjunctive, or unsafe/untyped binder -> MUST still flag!
        must_flag_cases = [
            ("non_false_eq", "theorem bad (h : false = true) : 1 = 2 := Bool.noConfusion h\n"),
            ("non_false_true", "theorem bad (h : false = true) : True := trivial\n"),
            ("non_false_not_true", "theorem bad (h : false = true) : ¬ True := Bool.noConfusion h\n"),
            ("non_false_and", "theorem bad (h : false = true) : False ∧ False := Bool.noConfusion h\n"),
            ("multi_premise_eq", "theorem bad2 (h : false = true) (x : Nat) (hx : x = 0) : False := Bool.noConfusion h\n"),
            ("conjunctive_hyp", "theorem bad_conj (x : Nat) (h : false = true ∧ x = 0) : False := Bool.noConfusion h.1\n"),
            ("conjunctive_ascii", "theorem bad_conj_ascii (x : Nat) (h : false = true /\\ x = 0) : False := Bool.noConfusion h.1\n"),
            ("conjunctive_nested", "theorem bad_conj_nest (x y : Nat) (h : (false = true ∧ x = 0) ∧ y = 1) : False := Bool.noConfusion h.1.1\n"),
            ("contradictory_pair_false", "theorem bad_pair (P : Prop) (h1 : P) (h2 : ¬ P) : False := h2 h1\n"),
            ("two_names_one_binder", "theorem bad_dup (h1 h2 : false = true) : False := Bool.noConfusion h1\n"),
            ("predicate_binder", "theorem bad_pred (x : Nat) (hx : IsGood x) (h : false = true) : False := Bool.noConfusion h\n"),
            ("prop_var_premise", "theorem bad_prop (P : Prop) (hp : P) (h : false = true) : False := Bool.noConfusion h\n"),
            ("shadowed_prop_then_type", "theorem bad_shadow (P : Prop) (hp : P) (P : Type) (h : false = true) : False := Bool.noConfusion h\n"),
            ("shadowed_type_then_prop", "theorem bad_shadow2 (α : Type) (α : Prop) (hp : α) (h : false = true) : False := Bool.noConfusion h\n"),
            ("sort_u_binder", "theorem bad_sort {α : Sort u} (x : α) (h : false = true) : False := Bool.noConfusion h\n"),
            ("empty_binder", "theorem bad_empty (x : Empty) (h : false = true) : False := Empty.elim x\n"),
            ("fin0_binder", "theorem bad_fin0 (x : Fin 0) (h : false = true) : False := Bool.noConfusion h\n"),
            ("subtype_binder", "theorem bad_sub (s : { x : Nat // x < 0 }) (h : false = true) : False := Bool.noConfusion h\n"),
            ("anon_prop_arrow", "theorem bad_anon (P : Prop) (h : false = true) : P → False := fun _ => Bool.noConfusion h\n"),
            ("anon_nat_arrow", "theorem bad_anon_nat (h : false = true) : Nat → False := fun _ => Bool.noConfusion h\n"),
            ("fact_inst", "theorem bad_fact (P : Prop) [Fact P] (h : false = true) : False := Bool.noConfusion h\n"),
            ("fact_named_inst", "theorem bad_fact_n (P : Prop) [hf : Fact P] (h : false = true) : False := Bool.noConfusion h\n"),
            ("untyped_paren", "theorem bad_untyped (hp) (h : false = true) : False := Bool.noConfusion h\n"),
            ("untyped_brace", "theorem bad_untyped_b {hp} (h : false = true) : False := Bool.noConfusion h\n"),
            ("bare_binder", "theorem bad_bare hp (h : false = true) : False := Bool.noConfusion h\n"),
            ("forall_untyped", "theorem bad_fa (h : false = true) : ∀ hp, False := fun _ => Bool.noConfusion h\n"),
            ("decidable_prod_empty", "theorem bad_dec_prod (d : Decidable (0 = 1) × Empty) (h : false = true) : False := Bool.noConfusion h\n"),
            ("two_contradictions", "theorem bad_two (h1 : false = true) (h2 : true = false) : False := Bool.noConfusion h1\n"),
        ]
        for label, src in must_flag_cases:
            self.assertIn(
                audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                _rules(audit.scan_lean_text(src)),
                f"all-scope failed to flag {label}",
            )
            self.assertIn(
                (R7, audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS, 1),
                scan67(src),
                f"default-scope failed to flag {label}",
            )

    def test_check_trusted_parity_on_precedence_and_false_elim_cases(self) -> None:
        ct = _load_check_trusted()
        samples = [
            "private theorem dite_prop_true {α : Type} {P : Prop} {inst : Decidable P} {t : P → α} {e : ¬ P → α} (h : P) : (@dite α P inst t e) = t h := by sorry\n",
            "theorem bad_paren (P : Prop) (α : Type) (h1 : ¬ (P → α)) (h2 : P → α) : x = 1 := by sorry\n",
            "private theorem boolFalseNeTrue (h : false = true) : False := Bool.noConfusion h\n",
            "theorem bad_nonfalse (h : false = true) : 1 = 2 := Bool.noConfusion h\n",
            "theorem bad_multi (h : false = true) (x : Nat) (hx : x = 0) : False := Bool.noConfusion h\n",
            "theorem bad_conj (x : Nat) (h : false = true ∧ x = 0) : False := Bool.noConfusion h.1\n",
            "theorem bad_pair (P : Prop) (h1 : P) (h2 : ¬ P) : False := h2 h1\n",
            "theorem bad_anon (P : Prop) (h : false = true) : P → False := fun _ => Bool.noConfusion h\n",
            "theorem bad_fact (P : Prop) [Fact P] (h : false = true) : False := Bool.noConfusion h\n",
        ]
        for src in samples:
            for scope in ("all", "annotated", "annotated-only"):
                self.assertEqual(
                    [(f.rule, f.line) for f in ct.audit_lean_text(src, vacuity_scope=scope)],
                    [(f.rule, f.line) for f in proof_health.audit_lean_text(src, vacuity_scope=scope)],
                    (scope, src),
                )


class TestNegationPrecedenceB1AdversarialHardening(unittest.TestCase):
    """`[adv B1]` regressions for what `[adv A0]`'s two false-positive fixes let through.

    Every `VACUOUS` header was reported at base `da6917c5` and went quiet at A0: a genuinely
    unsatisfiable or multi-premise hypothesis slipping past the new precedence scan or the new
    `: False` exemption. `VACUOUS_OTHER` headers are the same hazards in spellings base never
    read (or that A0 happened to keep). Every `CLEAN` header must stay quiet.
    """

    VACUOUS = {
        # The exemption reads `Nat` / `Bool` / `False` by spelling; a binder can rebind them.
        "rebound_nat_is_a_prop_premise": "theorem bad (Nat : Prop) (hn : Nat) (h : false = true) : False := by sorry\n",
        "rebound_bool_is_a_prop_premise": "theorem bad (Bool : Prop) (hb : Bool) (h : false = true) : False := by sorry\n",
        "rebound_unit_is_a_prop_premise": "theorem bad (Unit : Prop) (hu : Unit) (h : false = true) : False := by sorry\n",
        "rebound_false_conclusion": "theorem bad (False : Prop) (h : false = true) : False := by sorry\n",
        "forall_rebound_false_conclusion": "theorem bad (h : false = true) : ∀ (False : Prop), False := by sorry\n",
        # A relation whose left operand starts like a data type is a proposition, not a binder.
        "membership_of_container_type": "theorem bad (S : List Type) (hm : List Nat ∈ S) (h : false = true) : False := by sorry\n",
        "non_membership_of_container_type": "theorem bad (S : List Type) (hm : Option Nat ∉ S) (h : false = true) : False := by sorry\n",
        "membership_of_typeclass": "theorem bad (S : List Type) (hm : Decidable True ∈ S) (h : false = true) : False := by sorry\n",
        "heq_of_typeclasses": "theorem bad (α β : Type) (hm : BEq α ≍ BEq β) (h : false = true) : False := by sorry\n",
        "anonymous_instance_relation": "theorem bad (S : List Type) [Decidable True ∈ S] (h : false = true) : False := by sorry\n",
        # One binder, two propositions: the premise must be a single atomic relation.
        "bool_and_second_premise": "theorem bad (s : Nat) (h : none = some s && badState s) : False := by sorry\n",
        "pprod_second_premise": "theorem bad (s : Nat) (h : none = some s ×' Bad s) : False := by sorry\n",
        "pipe_second_premise": "theorem bad (s : Nat) (h : none = some s |> Bad) : False := by sorry\n",
        # The statement continues past a line-leading `|`, so the conclusion is not `False`.
        "conclusion_continues_with_bool_or": "theorem bad (h : false = true) : False\n  || (fun x => x) true = true := by sorry\n",
        "conclusion_continues_with_pipe": "theorem bad (h : false = true) : False\n  |> (fun p => p ∨ True) := by sorry\n",
        # Quantified hypotheses: a contradictory conjunct of the body is still a contradiction.
        "exists_body_conjunct": "theorem bad (P : Nat → Prop) (h : ∃ y, P y ∧ False) : x = 1 := by sorry\n",
        "exists_pair_with_outer_hypothesis": "theorem bad (P : Prop) (Q : Nat → Prop) (h1 : P) (h2 : ∃ y, Q y ∧ ¬ P) : x = 1 := by sorry\n",
        "forall_body_conjunct": "theorem bad (R : Nat → Prop) (h : ∀ s, R s ∧ False) : x = 1 := by sorry\n",
        "conjunct_then_exists_body": "theorem bad (P : Prop) (Q : Nat → Prop) (h : P ∧ ∃ y, Q y ∧ 0 = 1) : x = 1 := by sorry\n",
        "exists_body_outer_nat_bound": "theorem bad (n : Nat) (Q : Nat → Prop) (h : ∃ y, Q y ∧ n < 0) : x = 1 := by sorry\n",
        "nested_exists_body": "theorem bad (h : ∃ a, ∃ b : Nat, a < b ∧ b < b) : x = 1 := by sorry\n",
        "exists_body_operator_operands": "theorem bad (b : Bool) (Q : Nat → Prop) (h : ∃ y, Q y ∧ !b ≠ !b) : x = 1 := by sorry\n",
        # A character literal is not a connective.
        "char_literal_arrow_operand": "theorem bad (h : none = some '→') : x = 1 := by sorry\n",
        "char_literal_pair": "theorem bad (c : Char) (h1 : c = '→') (h2 : ¬ c = '→') : x = 1 := by sorry\n",
    }
    VACUOUS_OTHER = {
        "exists_proof_binder_premise": "theorem bad (h : ∃ _ : Bad, false = true) : False := by sorry\n",
        "exists_binder_predicate_premise": "theorem bad (s : List Nat) (h : ∃ x ∈ s, x < x) : False := by sorry\n",
        "exists_first_conjunct": "theorem bad (P : Nat → Prop) (h : ∃ y, False ∧ P y) : x = 1 := by sorry\n",
        "exists_whole_body": "theorem bad (h : ∃ y : Nat, y ≠ y) : x = 1 := by sorry\n",
        "exists_over_rebound_type_variable": "theorem bad {α : Type} (α : Prop) (h : ∃ x : α, false = true) : False := by sorry\n",
        "char_literal_conj_operands": "theorem bad (h : '∧' ≠ '∧') : x = 1 := by sorry\n",
        "arrow_false_pair": "theorem bad (P : Prop) (h1 : P) (h2 : P → False) : x = 1 := by sorry\n",
        "ascii_arrow_false_pair": "theorem bad (P : Prop) (h1 : P) (h2 : P -> False) : x = 1 := by sorry\n",
        "arrow_false_of_implication_pair": "theorem bad (P : Prop) (α : Type) (h1 : P → α) (h2 : (P → α) → False) : x = 1 := by sorry\n",
        "arrow_false_of_negation_pair": "theorem bad (P : Prop) (h1 : ¬ P) (h2 : ¬ P → False) : x = 1 := by sorry\n",
        "arrow_false_of_reflexive_equality": "theorem bad (h : x = x → False) : y = 1 := by sorry\n",
        "arrow_false_of_true": "theorem bad (h : True → False) : y = 1 := by sorry\n",
    }
    CLEAN = {
        # Honest single-premise refutations, including the shapes the new checks must still read.
        "primed_names": "theorem ok (x' : Nat) (h : x' < x') : False := by sorry\n",
        "nat_projection_bound": "theorem ok (xs : List Nat) (h : xs.length < 0) : False := by sorry\n",
        "sum_constructors": "theorem ok (a b : Nat) (h : Sum.inl a = Sum.inr b) : False := by sorry\n",
        "char_literal_irreflexive": "theorem ok (h : 'a' ≠ 'a') : False := by sorry\n",
        "arrow_false_of_true": "theorem ok (h : True → False) : False := by sorry\n",
        "arrow_false_of_reflexive_equality": "theorem ok (x : Nat) (h : x = x → False) : False := by sorry\n",
        "exists_over_data": "theorem ok (h : ∃ x : Nat, x < x) : False := by sorry\n",
        "exists_over_type_variable": "theorem ok {α : Type} (h : ∃ x : α, x ≠ x) : False := by sorry\n",
        "forall_over_data": "theorem ok (h : ∀ x : Nat, x ≠ x) : False := by sorry\n",
        "inhabited_data_binders": (
            "theorem ok (xs : List (Fin 0)) (o : Option Empty) (b : BitVec 8) (p : Nat × Bool)\n"
            "    (e : Except String Nat) (h : false = true) : False := by sorry\n"
        ),
        "type_variable_and_instances": (
            "theorem ok {α : Type u} [DecidableEq α] [inst : BEq α] (x : α) (h : none = some x) : False := by sorry\n"
        ),
        # Quantifiers that rebind a name, restrict their domain, or sit under a looser connective.
        "exists_rebinds_nat_name": "theorem ok (n : Nat) (h : ∃ n : Int, n < 0 ∧ n = -1) : x = 1 := by sorry\n",
        "exists_rebinds_pair_name": "theorem ok (y : Nat) (Q : Nat → Prop) (h1 : y = 0) (h2 : ∃ y, Q y ∧ ¬ y = 0) : x = 1 := by sorry\n",
        "forall_proof_binder": "theorem ok (P : Prop) (h : ∀ hp : P, x = 2 ∧ False) : x = 1 := by sorry\n",
        "forall_binder_predicate": "theorem ok (n : Nat) (h : ∀ i < n, x = 2 ∧ False) : x = 1 := by sorry\n",
        "forall_possibly_empty_domain": "theorem ok {α : Type} (h : ∀ a : α, a ≠ a) : x = 1 := by sorry\n",
        "negated_exists": "theorem ok (P : Nat → Prop) (h : ¬ ∃ y, P y ∧ False) : x = 1 := by sorry\n",
        "exists_body_implication": "theorem ok (P : Nat → Prop) (Q : Prop) (h : ∃ y, P y ∧ False → Q) : x = 1 := by sorry\n",
        # An arrow into `False` denies exactly its whole antecedent.
        "by_contra": "theorem by_contra {p : Prop} (h : ¬ p → False) : p := by sorry\n",
        "curried_arrow_false": "theorem ok (P Q : Prop) (hp : P) (h : P → Q → False) : x = 1 := by sorry\n",
        "iff_governs_arrow_false": "theorem ok (P Q : Prop) (hp : P) (h : Q ↔ P → False) : x = 1 := by sorry\n",
        "restricted_forall_arrow_false": "theorem ok (P : Prop) (Q : Nat → Prop) (hp : P) (h : ∀ hq : Q 0, P → False) : x = 1 := by sorry\n",
        "linear_arith_shape": "theorem ok (a b : Int) (h : Int.add b (Int.ofNat 1) ≤ a → False) : a ≤ b := by sorry\n",
        # Character literals and primes.
        "char_literal_operands": "theorem ok (c : Char) (h1 : c ≠ '→') (h2 : c = '∧') : x = 1 := by sorry\n",
        "primed_inequality": "theorem ok (x' y' : Nat) (h : x' ≠ y') (h2 : y' < x') : x = 1 := by sorry\n",
    }

    def setUp(self) -> None:
        proof_health.clear_in_process_caches()

    def test_vacuous_headers_are_reported_in_both_scopes(self) -> None:
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        for label, src in {**self.VACUOUS, **self.VACUOUS_OTHER}.items():
            self.assertIn(rule, _rules(audit.scan_lean_text(src)), f"all-scope missed {label}")
            self.assertIn((R7, rule, 1), scan67(src), f"default-scope missed {label}")

    def test_clean_headers_stay_quiet_in_both_scopes(self) -> None:
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        for label, src in self.CLEAN.items():
            self.assertNotIn(rule, _rules(audit.scan_lean_text(src)), f"all-scope flagged {label}")
            self.assertEqual(scan67(src), [], f"default-scope flagged {label}")

    def test_equation_arm_refutation_keeps_its_base_verdicts(self) -> None:
        # A statement cut at a real equation arm cannot be exempted (the cut is ambiguous), so
        # the anonymous premise is reported exactly as at base: by the full audit only.
        src = "theorem boolNe : false = true → False\n  | h => Bool.noConfusion h\n"
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        self.assertIn(rule, _rules(audit.scan_lean_text(src)))
        self.assertEqual(scan67(src), [])
        parsed = proof_health._split_lean_theorem_header(src, len("theorem boolNe"))
        self.assertEqual(parsed, ([("", "false = true")], "False", ["stmt-cut"]))

    def test_cache_never_serves_an_exemption_to_a_different_header(self) -> None:
        # The exemption depends on every binder and on the conclusion; all of it is in the
        # `_THM_AUDIT_CACHE` key (the header slice), under one theorem name, in one process.
        ct = _load_check_trusted()
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        exempt = "theorem t (h : false = true) : False := Bool.noConfusion h\n"
        variants = [
            "theorem t {hp} (h : false = true) : False := Bool.noConfusion h\n",
            "theorem t hp (h : false = true) : False := Bool.noConfusion h\n",
            "theorem t (P : Prop) [Fact P] (h : false = true) : False := Bool.noConfusion h\n",
            "theorem t (P : Prop) (hp : P) (h : false = true) : False := Bool.noConfusion h\n",
            "theorem t (h : false = true) : False ∨ True := Bool.noConfusion h\n",
            "theorem t (h : false = true) : False\n  || (fun x => x) true = true := Bool.noConfusion h\n",
        ]
        for mod in (proof_health, ct):
            for scope in ("all", "annotated"):
                for variant in variants:
                    for src, flagged in ((exempt, False), (variant, True), (exempt, False), (variant, True)):
                        found = rule in [f.rule for f in mod.audit_lean_text(src, vacuity_scope=scope)]
                        self.assertEqual(found, flagged, (mod.__name__, scope, src))
        # The parse the exemption reads is a function of the keyed slice alone.
        header = "theorem t {hp} [Fact P] (h : false = true) : False := x\n"
        alone = proof_health._split_lean_theorem_header(header, len("theorem t"))
        embedded = proof_health._split_lean_theorem_header(
            "  " + header + "theorem u (q : Q) : False := y\n", 2 + len("theorem t"), 2 + len(header)
        )
        self.assertEqual(alone, embedded)
        self.assertEqual(alone, ([("h", "false = true")], "False", ["untyped:hp", "[Fact P]"]))

    def test_arrow_false_antecedent(self) -> None:
        fn = proof_health._arrow_false_antecedent
        for expr, want in (
            ("P → False", "P"),
            ("P -> False", "P"),
            ("(P → α) → False", "P → α"),
            ("¬ p → False", "¬ p"),
            ("A ∧ B → False", "A ∧ B"),
            ("A ∨ B → False", "A ∨ B"),
            ("A → B → False", None),
            ("A ↔ B → False", None),
            ("∀ x, P x → False", None),
            ("fun x => x → False", None),
            ("P → False ∨ Q", None),
            ("P → isFalse", None),
            ("f (P → False)", None),
            ("False", None),
        ):
            self.assertEqual(fn(expr), want, expr)

    def test_non_prop_binder_type_is_a_strict_whitelist(self) -> None:
        fn = proof_health._is_non_prop_binder_type
        tv = frozenset({"α"})
        for ok in (
            "Nat", "Prop", "Type", "Type u", "α", "Nat × Bool", "List (Fin 0)", "Option Empty",
            "Array α", "BitVec 8", "BitVec (n + 1)", "Except String Nat", "Sum Nat α",
            "Decidable (a = b)", "DecidableEq α", "BEq α",
        ):
            self.assertTrue(fn(ok, tv), ok)
        for bad in (
            "Empty", "Fin 0", "P", "β", "Sort u", "List", "PLift P", "Nat × Empty", "Sum Nat Empty",
            "List Nat ∈ S", "Option Nat ∉ S", "Decidable P ∈ S", "BEq α ≍ BEq β", "List Nat → Prop",
            "List Nat × Empty", "Option Nat ⊕ Empty", "{ x : Nat // x < 0 }", "a = b", "Nat = Nat",
            "List Nat |>.Nonempty", "Option fun x => x", "Decidable", "",
        ):
            self.assertFalse(fn(bad, tv), bad)

    def test_simple_refutation_premise_is_a_strict_whitelist(self) -> None:
        fn = proof_health._is_simple_refutation_premise
        for ok in (
            "False", "false = true", "x' < x'", "[] = x :: xs", "none = some x", "¬ (x = x)",
            "¬ True", "xs.length < 0", "a + 1 < 0", ".inl a = .inr b", "True → False",
            "x = x → False", "'u61' ≠ 'u61'", "(f x).1 ≠ (f x).1",
        ):
            self.assertTrue(fn(ok), ok)
        for bad in (
            "none = some s && bad s", "none = some s ×' Bad s", "none = some s |> Bad",
            "none = some fun y => A ∧ B", "a < b < c", "P", "¬ ¬ True", "x = y ∧ False",
            "none = some x ∨ P", "n < 0 → P", "{ x // p } = s", "x ∈ s",
        ):
            self.assertFalse(fn(bad), bad)

    def test_quantifier_binder_helpers(self) -> None:
        plain = proof_health._plain_quantifier_binders
        for ok in ("y", "x y", "y : Nat", "(x : Nat) (b : Bool)", "x (y : Nat)", "{P : Prop}", "(x)"):
            self.assertTrue(plain(ok), ok)
        for bad in ("hp : P", "i < n", "x ∈ s", "a : α", "(i : Fin n)", "[inst : Foo]", "! x", ""):
            self.assertFalse(plain(bad), bad)
        # A type variable's domain may be empty: plain only for callers that pass it in scope.
        self.assertTrue(plain("a : α", frozenset({"α"})))
        self.assertTrue(plain("(a : α) (n : Nat)", frozenset({"α"})))
        self.assertFalse(plain("a : β", frozenset({"α"})))
        bound = proof_health._quantifier_bound_names
        self.assertEqual(bound("x y : T n"), frozenset({"x", "y"}))
        self.assertEqual(bound("(x : Nat) {y : Fin x}"), frozenset({"x", "y"}))
        self.assertEqual(bound("⟨a, b⟩"), frozenset({"a", "b"}))
        self.assertEqual(bound("x ∈ s"), frozenset({"x", "s"}))
        split = proof_health._split_quantifier_prefix
        self.assertEqual(split("∃ ⟨a, b⟩, a < b"), ("∃", " ⟨a, b⟩", " a < b"))
        self.assertEqual(split("forall x, P x"), ("∀", " x", " P x"))
        self.assertIsNone(split("existsUnique x"))
        self.assertIsNone(split("∀ x"))

    def test_check_trusted_agrees_on_every_b1_header(self) -> None:
        ct = _load_check_trusted()
        for label, src in {**self.VACUOUS, **self.VACUOUS_OTHER, **self.CLEAN}.items():
            for scope in ("all", "annotated", "annotated-only"):
                self.assertEqual(
                    [(f.rule, f.line, f.message) for f in ct.audit_lean_text(src, vacuity_scope=scope)],
                    [(f.rule, f.line, f.message) for f in proof_health.audit_lean_text(src, vacuity_scope=scope)],
                    (scope, label),
                )


class TestNegationPrecedenceA1AdversarialFixes(unittest.TestCase):
    """`[adv A1]` regressions for bugs found in `[adv B1]` and earlier vacuity auditor passes:

    1. Negated hypothesis fall-through (`¬ x :: xs = []`) and non-top-level `List` constructor
       checks (`(x :: xs).tail = []`, `[[], xs][0] = []`) plus depth-0 `<`/`>`/`=` splitting.
    2. Telescope-ordered `nat_vars` shadowing (`(n : Nat) (n : Int) (h : n < 0)`, later `∀ (n : Nat)`)
       and quantifier-typed `Nat` contradictions (`∃ n : Nat, n < 0`, `∀ n : Nat, n < 0`).
    3. Quantifier domain inhabitation & shadowing (`(Nat : Prop) (h : ∀ n : Nat, False)`,
       untyped `∀` over arbitrary `α` / `P : Prop` / `Fin n` / rebound `R` / non-head `Apply R s`,
       `∃ (α : Type), ∀ (x : α), False`), telescope shadowing inside `∃` refutations
       (`∃ (Nat : Prop) (hn : Nat), false = true`, `{α : Type} (h : ∃ (α : Prop) (hp : α), ...)`),
       untyped `∃` binders in `: False` refutations (`∃ hp, (hp : P) ≠ (hp : P)`), same-scope
       contradictory conjuncts inside quantifiers (`∃ x : Nat, P x ∧ ¬ P x`), and distinct
       nested quantifier scopes staying clean.
    4. Header parsing with bracket/arrow char literals (`'('`, `')'`, `'→'`), unnamed instances
       carrying nested colons (`[Decidable (∃ x : Nat, x = n)]`, `[Decidable (c = ':')]`),
       containers with parenthesised product/expression args (`List (Nat × Bool)`,
       `BitVec (n + 1)`), `→` looser connectives (`↔`, `<|`, `$`) and ASCII `exists`,
       parenthesised `→ (False)` negations, unary `!` / BitVec `#` simple refutation terms,
       and symmetric/unspaced `=`/`≠` pairs.
    """

    VACUOUS_BOTH_SCOPES = {
        "char_lparen_irrefl": "theorem bad (h : '(' ≠ '(') : x = 1 := by sorry\n",
        "char_rparen_irrefl": "theorem bad (h : ')' ≠ ')') : x = 1 := by sorry\n",
        "exists_typed_nat_lt_0": "theorem bad (h : ∃ n : Nat, n < 0) : x = 1 := by sorry\n",
        "forall_typed_nat_lt_0": "theorem bad (h : ∀ n : Nat, n < 0) : x = 1 := by sorry\n",
        "forall_multi_typed_nat_lt_0": "theorem bad (h : ∀ (x : Nat) (y : Int), x < 0) : x = 1 := by sorry\n",
        "some_nested_eq_none": "theorem bad (a b : Nat) (h : some (a = b) = none) : x = 1 := by sorry\n",
        "nested_lt_irrefl": "theorem bad (f : Prop → Nat) (a b : Nat) (h : f (a < b) < f (a < b)) : x = 1 := by sorry\n",
        "nested_fun_gt_irrefl": "theorem bad (a : Nat) (h : (fun x => x) a > (fun x => x) a) : x = 1 := by sorry\n",
        "paren_bool_eq": "theorem bad (h : (false) = (true)) : x = 1 := by sorry\n",
        "exists_shadow_nat_refutation": "theorem bad (h : ∃ (Nat : Prop) (hn : Nat), false = true) : False := by sorry\n",
        "exists_nested_shadow_nat_refutation": "theorem bad (h : ∃ (Nat : Prop), ∃ (hn : Nat), false = true) : False := by sorry\n",
        "exists_shadow_typevar_refutation": "theorem bad {α : Type} (h : ∃ (α : Prop) (hp : α), false = true) : False := by sorry\n",
        "exists_nested_shadow_typevar_refutation": "theorem bad {α : Type} (h : ∃ (α : Prop), ∃ (hp : α), false = true) : False := by sorry\n",
        "exists_untyped_proof_binder_refutation": "theorem bad (P : Prop) (h : ∃ hp, (hp : P) ≠ (hp : P)) : False := by sorry\n",
        "exists_untyped_global_f_refutation": "theorem bad (h : ∃ hp, f hp ≠ f hp) : False := by sorry\n",
        "exists_untyped_paren_refutation": "theorem bad (h : ∃ (hp), false = true) : False := by sorry\n",
        "exists_same_scope_pair": "theorem bad (P : Nat → Prop) (h : ∃ x : Nat, P x ∧ ¬ P x) : x = 1 := by sorry\n",
        "exists_same_scope_eq_neq": "theorem bad (h : ∃ x : Nat, x = 0 ∧ x ≠ 0) : x = 1 := by sorry\n",
        "exists_same_scope_symm_eq_neq": "theorem bad (h : ∃ x : Nat, x = 0 ∧ 0 ≠ x) : x = 1 := by sorry\n",
        "exists_same_scope_arrow_false": "theorem bad (P : Nat → Prop) (h : ∃ x : Nat, P x ∧ (P x → False)) : x = 1 := by sorry\n",
        "forall_same_scope_pair": "theorem bad (P : Nat → Prop) (h : ∀ x : Nat, P x ∧ ¬ P x) : x = 1 := by sorry\n",
        "arrow_paren_false_pair": "theorem bad (P : Prop) (h1 : P) (h2 : P → (False)) : x = 1 := by sorry\n",
        "arrow_paren_false_true": "theorem bad (h : True → (False)) : x = 1 := by sorry\n",
        "symm_eq_neq_pair": "theorem bad (a b : Nat) (h1 : a = b) (h2 : b ≠ a) : x = 1 := by sorry\n",
        "nospace_eq_neq_pair": "theorem bad (a b : Nat) (h1 : a=b) (h2 : a ≠ b) : x = 1 := by sorry\n",
        "list_nonempty_bracket_char_lit": "theorem bad (h : [']'] = []) : x = 1 := by sorry\n",
        "forall_two_arg_inhabited": "theorem bad (R : Nat → Bool → Prop) (h : ∀ a b, R a b ∧ False) : x = 1 := by sorry\n",
    }

    VACUOUS_ALL_SCOPE_ONLY = {
        "char_arrow_anon_premise": "theorem bad : '→' ≠ '→' → x = 1 := by sorry\n",
        "char_lparen_anon_premise": "theorem bad : '(' ≠ '(' → x = 1 := by sorry\n",
    }

    CLEAN = {
        "shadowed_nat_to_int": "theorem ok (n : Nat) (n : Int) (h : n < 0) : n ≠ 0 := by omega\n",
        "later_nat_binder_after_lt0": "theorem ok (h : n < 0) : ∀ (n : Nat), n = n := by intro; rfl\n",
        "shadowed_nat_type_for_lt0": "theorem ok (Nat : Prop) (n : Nat) (h : n < 0) : True := trivial\n",
        "not_cons_eq_nil": "theorem ok (x : Nat) (xs : List Nat) (h : ¬ x :: xs = []) : True := trivial\n",
        "cons_eq_nil_arrow_false": "theorem ok (x : Nat) (xs : List Nat) (h : x :: xs = [] → False) : True := trivial\n",
        "cons_tail_eq_nil": "theorem ok (x : Nat) (xs : List Nat) (h : (x :: xs).tail = []) : xs = [] := rfl\n",
        "list_index_eq_nil": "theorem ok (xs : List (List Nat)) (h : [[], xs][0] = []) : True := trivial\n",
        "rebound_nat_forall": "theorem ok (Nat : Prop) (h : ∀ n : Nat, False) : ¬ Nat := h\n",
        "rebound_nat_fn_domain_forall": "theorem ok (Nat : Prop) (R : Nat → Prop) (h : ∀ s, R s ∧ False) : ¬ Nat := by sorry\n",
        "forall_untyped_empty_alpha": "theorem ok {α : Type} (R : α → Prop) (h : ∀ a, R a ∧ False) : α → False := fun a => (h a).2\n",
        "forall_untyped_prop_domain": "theorem ok (P : Prop) (R : P → Prop) (h : ∀ hp, R hp ∧ False) : ¬ P := fun hp => (h hp).2\n",
        "forall_untyped_fin_domain": "theorem ok (n : Nat) (R : Fin n → Prop) (h : ∀ i, R i ∧ False) : n = 0 := by sorry\n",
        "forall_untyped_mixed_domain": "theorem ok {α : Type} (R : Nat → α → Prop) (h : ∀ a b, R a b ∧ False) : α → False := by sorry\n",
        "forall_untyped_non_head_arg": "theorem ok (R : Nat → Prop) (h : ∀ s, Apply R s ∧ False) : True := trivial\n",
        "forall_untyped_inner_rebound_fn": "theorem ok (R : Nat → Prop) (h : ∀ s, (∀ R : Empty → Prop, R s) ∧ False) : True := trivial\n",
        "forall_multi_typed_int_lt_0": "theorem ok (h : ∀ (x : Nat) (y : Int), y < 0) : x = 1 := by sorry\n",
        "exists_empty_type_forall": "theorem ok (h : ∃ (α : Type), ∀ (x : α), False) : x = 1 := by sorry\n",
        "exists_distinct_nested_scopes": "theorem ok (P : Nat → Nat → Prop) (h : ∃ x : Nat, (∃ y : Nat, P x y) ∧ (∃ y : Nat, ¬ P x y)) : x = 1 := by sorry\n",
        "exists_two_hyps_distinct_witnesses": "theorem ok (P : Nat → Prop) (h1 : ∃ x : Nat, P x) (h2 : ∃ x : Nat, ¬ P x) : x = 1 := by sorry\n",
        "exists_bitvec_paren_arg_refutation": "theorem ok (n : Nat) (h : ∃ b : BitVec (n + 1), b ≠ b) : False := by sorry\n",
        "exists_list_prod_arg_refutation": "theorem ok (h : ∃ xs : List (Nat × Bool), xs ≠ xs) : False := by sorry\n",
        "exists_new_typevar_refutation": "theorem ok (h : ∃ (α : Type) (x : α), x ≠ x) : False := by sorry\n",
        "option_prod_binder_refutation": "theorem ok (o : Option (Nat × Bool)) (h : false = true) : False := by sorry\n",
        "unnamed_decidable_exists_refutation": "theorem ok (n : Nat) [Decidable (∃ x : Nat, x = n)] (h : false = true) : False := by sorry\n",
        "unnamed_decidable_char_colon": "theorem ok (c : Char) [Decidable (c = ':')] (h : false = true) : False := by sorry\n",
        "unnamed_decidable_char_rparen": "theorem ok (c : Char) [Decidable (c = ')')] (h : false = true) : False := by sorry\n",
        "bool_bang_refutation": "theorem ok (b : Bool) (h : !b ≠ !b) : False := by sorry\n",
        "bitvec_lit_refutation": "theorem ok (h : 0#8 ≠ 0#8) : False := by sorry\n",
        "pipe_left_arrow_false": "theorem ok (f : Prop → Prop) (P : Prop) (h1 : f <| P) (h2 : f <| P → False) : x = 1 := by sorry\n",
        "dollar_arrow_false": "theorem ok (f : Prop → Prop) (P : Prop) (h1 : f $ P) (h2 : f $ P → False) : x = 1 := by sorry\n",
        "arrow_false_iff_true": "theorem ok : false = true → False ↔ True := by simp\n",
        "false_to_false_iff_true": "theorem ok : False → False ↔ True := by simp\n",
        "ascii_exists_arrow": "theorem ok (P : Prop) : exists x : Nat, False → P := by sorry\n",
        "exists_nat_lt_0_refutation": "theorem ok (h : ∃ n : Nat, n < 0) : False := by sorry\n",
        "forall_nat_lt_0_refutation": "theorem ok (h : ∀ n : Nat, n < 0) : False := by sorry\n",
    }

    def setUp(self) -> None:
        proof_health.clear_in_process_caches()

    def test_a1_vacuous_headers_flagged_in_both_scopes(self) -> None:
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        for label, src in self.VACUOUS_BOTH_SCOPES.items():
            self.assertIn(rule, _rules(audit.scan_lean_text(src)), f"all-scope missed {label}")
            self.assertIn((R7, rule, 1), scan67(src), f"default-scope missed {label}")

    def test_a1_vacuous_anonymous_headers_flagged_in_all_scope(self) -> None:
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        for label, src in self.VACUOUS_ALL_SCOPE_ONLY.items():
            self.assertIn(rule, _rules(audit.scan_lean_text(src)), f"all-scope missed {label}")
            self.assertEqual(scan67(src), [], f"default-scope unexpectedly flagged anon {label}")

    def test_a1_clean_headers_stay_quiet_in_both_scopes(self) -> None:
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        for label, src in self.CLEAN.items():
            self.assertNotIn(rule, _rules(audit.scan_lean_text(src)), f"all-scope flagged {label}")
            self.assertEqual(scan67(src), [], f"default-scope flagged {label}")

    def test_a1_helper_invariants(self) -> None:
        self.assertEqual(proof_health._arrow_false_antecedent("P → (False)"), "P")
        self.assertIsNone(proof_health._arrow_false_antecedent("f <| P → False"))
        self.assertIsNone(proof_health._arrow_false_antecedent("f $ P → False"))
        self.assertTrue(proof_health._has_top_level_looser_than_not("f <| P"))
        self.assertTrue(proof_health._has_top_level_looser_than_not("f $ P"))
        self.assertTrue(proof_health._is_non_prop_binder_type("List (Nat × Bool)", frozenset()))
        self.assertFalse(
            proof_health._is_non_prop_binder_type("Nat", frozenset(), shadowed=frozenset({"Nat"}))
        )
        self.assertTrue(proof_health._plain_quantifier_binders("x : List (Fin 0)"))
        self.assertTrue(proof_health._plain_quantifier_binders("b : BitVec (n + 1)"))
        self.assertFalse(proof_health._plain_quantifier_binders("(Nat : Prop) (hn : Nat)"))
        self.assertFalse(
            proof_health._plain_quantifier_binders("(α : Prop) (hp : α)", frozenset({"α"}))
        )
        self.assertFalse(proof_health._plain_quantifier_binders("hp", allow_untyped=False))
        self.assertTrue(proof_health._is_simple_refutation_premise("!b ≠ !b"))
        self.assertTrue(proof_health._is_simple_refutation_premise("0#8 ≠ 0#8"))

    def test_check_trusted_agrees_on_every_a1_header(self) -> None:
        ct = _load_check_trusted()
        all_cases = {**self.VACUOUS_BOTH_SCOPES, **self.VACUOUS_ALL_SCOPE_ONLY, **self.CLEAN}
        for label, src in all_cases.items():
            for scope in ("all", "annotated", "annotated-only"):
                self.assertEqual(
                    [(f.rule, f.line, f.message) for f in ct.audit_lean_text(src, vacuity_scope=scope)],
                    [(f.rule, f.line, f.message) for f in proof_health.audit_lean_text(src, vacuity_scope=scope)],
                    (scope, label),
                )


class TestNegationPrecedenceB2AdversarialFixes(unittest.TestCase):
    """`[adv B2]` regressions for bugs found in `[adv A1]` and earlier vacuity auditor passes:

    1. Binder-governed atoms read as one relation: `∀ x ∈ s, x :: xs = []`, `∀ x : α, xs.length < 0`,
       `∀ hp : P, ...` and `if c then True else ...` hold vacuously (empty domain / other branch)
       but were split at the `=` / `<` inside the binder body and flagged.
    2. `Nat`-valued operand detection: the `.length` / `.toNat` suffix and `sumSizes ` prefix tests
       ran on the whole operand and operators were split at any depth, so `f xs.length`,
       `x - y.toNat`, `sumSizes xs - z`, `-↑xs.length` and `g (a.size + b.size)` (all possibly
       negative) were flagged as `< 0` contradictions.
    3. Header binders the parser dropped: dependent-arrow premises (`(h : False) → P`,
       `(n : Nat) → n < 0 → P`) and strict-implicit binders (`⦃x : Nat⦄`, whose inner `:` was
       read as the statement colon) hid contradictory hypotheses from every scope.
    4. Relations never read: numeric `3 ≥ 5` and negated reflexive `¬ x ≤ x` / `¬ x ≥ x`.
    """

    VACUOUS_BOTH_SCOPES = {
        "dep_arrow_false": "theorem bad : (h : False) → x = 1 := by sorry\n",
        "dep_arrow_nat_lt_0": "theorem bad : (n : Nat) → (h : n < 0) → x = 1 := by sorry\n",
        "dep_arrow_ascii_pair": "theorem bad (P : Prop) : (h1 : P) -> (h2 : ¬ P) -> x = 1 := by sorry\n",
        "strict_implicit_nat_lt_0": "theorem bad ⦃x : Nat⦄ (h : x < 0) : x = 1 := by sorry\n",
        "strict_implicit_then_false": "theorem bad ⦃x : Nat⦄ (h : False) : x = 1 := by sorry\n",
        "strict_implicit_false": "theorem bad ⦃h : False⦄ : x = 1 := by sorry\n",
        "forall_strict_implicit_nat_lt_0": "theorem bad : ∀ ⦃n : Nat⦄ (h : n < 0), x = 1 := by sorry\n",
        "numeric_ge": "theorem bad (h : 3 ≥ 5) : x = 1 := by sorry\n",
        "not_le_refl": "theorem bad (x : Nat) (h : ¬ x ≤ x) : x = 1 := by sorry\n",
        "not_ge_refl_paren": "theorem bad (x : Nat) (h : ¬ (x ≥ x)) : x = 1 := by sorry\n",
        "len_lt_0": "theorem bad (xs : List Nat) (h : xs.length < 0) : x = 1 := by sorry\n",
        "paren_proj_len_lt_0": "theorem bad (xs : List Nat) (h : (xs.map f).length < 0) : x = 1 := by sorry\n",
        "nat_sub_lt_0": "theorem bad (a b : Nat) (h : a - b < 0) : x = 1 := by sorry\n",
        "nat_paren_arith_lt_0": "theorem bad (a b : Nat) (h : (a + b) * 2 < 0) : x = 1 := by sorry\n",
        "toNat_sub_gt": "theorem bad (a b : Int) (h : 0 > a.toNat - b.toNat) : x = 1 := by sorry\n",
        "prefix_fn_lt_0": "theorem bad (h : sumSizes xs < 0) : x = 1 := by sorry\n",
        "exists_mem_false": "theorem bad (h : ∃ x ∈ s, False) : x = 1 := by sorry\n",
        "exists_cons_nil": "theorem bad (xs : List Nat) (h : ∃ x : Nat, x :: xs = []) : x = 1 := by sorry\n",
        "forall_nat_cons_nil": "theorem bad (xs : List Nat) (h : ∀ x : Nat, x :: xs = []) : x = 1 := by sorry\n",
    }

    CLEAN = {
        "forall_empty_domain_len": "theorem ok {α : Type} (xs : List Nat) (h : ∀ x : α, xs.length < 0) : α → False := by sorry\n",
        "forall_mem_len": "theorem ok (s xs : List Nat) (h : ∀ i ∈ s, xs.length < 0) : s = [] := by sorry\n",
        "forall_empty_domain_cons_nil": "theorem ok {α : Type} (xs : List α) (h : ∀ x : α, x :: xs = []) : α → False := by sorry\n",
        "forall_mem_cons_nil": "theorem ok (s xs : List Nat) (h : ∀ x ∈ s, x :: xs = []) : s = [] := by sorry\n",
        "forall_proof_binder_len": "theorem ok (P : Prop) (xs : List Nat) (h : ∀ hp : P, xs.length < 0) : ¬ P := by sorry\n",
        "if_else_cons_nil": "theorem ok (c : Prop) [Decidable c] (x : Nat) (xs : List Nat) (h : if c then True else x :: xs = []) : c := by sorry\n",
        "if_else_len_lt_0": "theorem ok (c : Prop) [Decidable c] (xs : List Nat) (h : if c then True else xs.length < 0) : c := by sorry\n",
        "fn_of_suffix_arg_lt_0": "theorem ok (f : Nat → Int) (xs : List Nat) (h : f xs.length < 0) : f xs.length ≠ 0 := by omega\n",
        "fn_of_suffix_arg_gt": "theorem ok (f : Nat → Int) (xs : List Nat) (h : 0 > f xs.length) : f xs.length ≠ 0 := by omega\n",
        "int_minus_toNat": "theorem ok (x y : Int) (h : x - y.toNat < 0) : x < y.toNat := by omega\n",
        "prefix_fn_minus_int": "theorem ok (z : Int) (h : sumSizes xs - z < 0) : 0 < z := by sorry\n",
        "neg_cast_len": "theorem ok (xs : List Nat) (h : -↑xs.length < 0) : xs ≠ [] := by sorry\n",
        "fn_of_paren_arith": "theorem ok (g : Nat → Int) (a b : Array Nat) (h : g (a.size + b.size) < 0) : True := trivial\n",
        "int_times_nat": "theorem ok (n : Nat) (z : Int) (h : n * z < 0) : z < 0 := by sorry\n",
        "dep_arrow_data": "theorem ok : (n : Nat) → (h : n = 0) → n + 0 = 0 := by sorry\n",
        "dep_arrow_int_lt_0": "theorem ok : (n : Int) → (h : n < 0) → n ≠ 0 := by sorry\n",
        "subtype_premise": "theorem ok : {x : Nat // x < 0} → False := by sorry\n",
        "strict_implicit_data": "theorem ok ⦃x : Nat⦄ (h : x = 0) : x + 0 = 0 := by simp [h]\n",
        "strict_implicit_int_lt_0": "theorem ok ⦃x : Int⦄ (h : x < 0) : x ≠ 0 := by omega\n",
        "hoare_triple_hyp": "theorem ok (h : ⦃P⦄ t ⦃Q⦄) : ⦃P⦄ ITree.tau t ⦃Q⦄ := by sorry\n",
        "forall_strict_implicit_inj": "theorem ok (hInj : ∀ ⦃x y : α⦄, m.toValue x = m.toValue y → x = y) : inj m := by sorry\n",
        "numeric_ge_true": "theorem ok (h : 5 ≥ 3) : x = 1 := by sorry\n",
        "nat_ge_zero": "theorem ok (n : Nat) (h : n ≥ 0) : x = 1 := by sorry\n",
        "not_le_distinct": "theorem ok (x y : Nat) (h : ¬ x ≤ y) : y < x := by omega\n",
        "not_le_refl_refutation": "theorem ok (x : Nat) (h : ¬ x ≤ x) : False := by sorry\n",
        "dep_arrow_refutation": "theorem ok : (h : false = true) → False := by sorry\n",
    }

    def setUp(self) -> None:
        proof_health.clear_in_process_caches()

    def test_b2_vacuous_headers_flagged_in_both_scopes(self) -> None:
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        for label, src in self.VACUOUS_BOTH_SCOPES.items():
            self.assertIn(rule, _rules(audit.scan_lean_text(src)), f"all-scope missed {label}")
            self.assertIn((R7, rule, 1), scan67(src), f"default-scope missed {label}")

    def test_b2_clean_headers_stay_quiet_in_both_scopes(self) -> None:
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        for label, src in self.CLEAN.items():
            self.assertNotIn(rule, _rules(audit.scan_lean_text(src)), f"all-scope flagged {label}")
            self.assertEqual(scan67(src), [], f"default-scope flagged {label}")

    def test_b2_helper_invariants(self) -> None:
        nat = proof_health._is_nat_like_operand
        none: frozenset[str] = frozenset()
        for yes, nv in (
            ("xs.length", none),
            ("(xs.map f).length", none),
            ("a.toNat - b.toNat", none),
            ("sumSizes xs", none),
            ("(a + b) * 2", frozenset({"a", "b"})),
            ("2 ^ n - 1", frozenset({"n"})),
            ("↑xs.length", none),
        ):
            self.assertTrue(nat(yes, nv), yes)
        for no, nv in (
            ("f xs.length", none),
            ("x - y.toNat", none),
            ("sumSizes xs - z", none),
            ("-↑xs.length", none),
            ("-n", frozenset({"n"})),
            ("g (a.size + b.size)", none),
            ("n * z", frozenset({"n"})),
            ("(n : Int) + 1", frozenset({"n"})),
            ("", none),
        ):
            self.assertFalse(nat(no, nv), no)

        binder = proof_health._has_top_level_prefix_binder
        for yes in (
            "∀ x ∈ s, x :: xs = []",
            "forall x, x = 0",
            "if c then True else n < 0",
            "x = fun y => y",
            "n < 0 ∧ ∃ y, P y",
        ):
            self.assertTrue(binder(yes), yes)
        for no in (
            "f (fun x => x) = 0",
            "¬ (∀ x, P x)",
            "List.exists p xs = true",
            "«if» < 0",
            "notify x < 0",
            "n < 0 ∧ m = 1",
        ):
            self.assertFalse(binder(no), no)

        prem = proof_health._arrow_premise_binder
        self.assertEqual(prem("(h : False)"), ("h", "False"))
        self.assertEqual(prem("(a b : Nat)"), ("a b", "Nat"))
        self.assertEqual(prem("(a = b)"), ("", "(a = b)"))
        self.assertEqual(prem("(x := 1)"), ("", "(x := 1)"))
        self.assertEqual(prem("{x : Nat // x < 5}"), ("", "{x : Nat // x < 5}"))
        self.assertEqual(prem("(x : Nat) × Fin x"), ("", "(x : Nat) × Fin x"))
        self.assertEqual(prem("(f x : Nat)"), ("f x", "Nat"))
        self.assertEqual(prem("((a, b) : Nat × Nat)"), ("", "((a, b) : Nat × Nat)"))

        hyps, conc, extra = proof_health._split_lean_theorem_header(
            " ⦃x : Nat⦄ ⦃y⦄ (h : x < 0) : x = 1 := by sorry", 0
        )
        self.assertEqual(hyps, [("x", "Nat"), ("h", "x < 0")])
        self.assertEqual(conc, "x = 1")
        self.assertEqual(extra, ["untyped:y"])
        hyps, conc, _ = proof_health._split_lean_theorem_header(
            " : (n : Nat) → n < 0 → ∀ ⦃m : Nat⦄, m = n := by sorry", 0
        )
        self.assertEqual(hyps, [("n", "Nat"), ("", "n < 0"), ("m", "Nat")])
        self.assertEqual(conc, "m = n")
        self.assertIsNone(proof_health._split_lean_theorem_header(" ⦃x : Nat (h : False) : P", 0))

    def test_check_trusted_agrees_on_every_b2_header(self) -> None:
        ct = _load_check_trusted()
        all_cases = {**self.VACUOUS_BOTH_SCOPES, **self.CLEAN}
        for label, src in all_cases.items():
            for scope in ("all", "annotated", "annotated-only"):
                self.assertEqual(
                    [(f.rule, f.line, f.message) for f in ct.audit_lean_text(src, vacuity_scope=scope)],
                    [(f.rule, f.line, f.message) for f in proof_health.audit_lean_text(src, vacuity_scope=scope)],
                    (scope, label),
                )


class TestNegationPrecedenceA2AdversarialFixes(unittest.TestCase):
    r"""`[adv A2]` regressions for bugs found in `[adv B2]` and earlier vacuity auditor passes:

    1. Exponential ReDoS in `_BARE_BINDER_NAMES_RE` (`(?:[^\W\d][\w'!?]*\s*)+`): a single ~25-char
       non-matching identifier (e.g. `∀ very_long_variable_name < n, ...`) took seconds / hours.
    2. Strict-implicit `⦃...⦄` and bracket parity: nested `⦃...⦄` and `'⦄'` char literals inside
       strict-implicit binders, `theorem name⦃...⦄` without space, `∀ ⦃x : Nat⦄, ...` inside
       hypotheses, `_quantifier_bound_names` dropping binders after `⦃...⦄`, Hoare triples
       `⦃P ∧ False ∧ Q⦄` / `⦃P ∨ True ∨ Q⦄` and `⟨P, Q ∨ True ∨ R⟩` split at inner `∧` / `∨` / `→`.
    3. Dependent-arrow binders & negations: `{h : False} → P`, `⦃h : False⦄ → P`, `[h : False] → P`,
       `{n : Nat} → (h : n < 0) → P`, `(hp : P) → False` / `(ht : True) → False` denials.
    4. Header parser guards: fast-path `→` split through `if`/`match`/`let`/`fun`, `where` prefix
       identifiers (`whereFoo`, `where_x`), and `:=` inside guillemets (`«a := b»`).
    5. Coerced `Nat` subtraction (`↑a.length - ↑b.length < 0`, `↑a.length - 1 < 0`,
       `Nat.cast a - Nat.cast b < 0`), high-precedence infix operators (`>>=`, `|>.`, `*>`, `>>>`,
       `&&&`) on `Nat` / `Option` / `List` / `Sum` / `Except` operands, `↑xs.length < 0 : False`
       refutation exemption, `Option.none = Option.some x`, and string-blanked `Except.error "msg"`.
    6. Prefix-binder guard in `_record_pos_neg_atom` (`∀ x ∈ s, a = b` paired with `∀ x ∈ s, a ≠ b`),
       `Float` `¬ x ≤ x` NaN reflexivity exemption, `Fin` shadowing in quantifiers, projection &
       inner-rebinding guards in `_untyped_binders_inhabited_by_calls`, ancestor-descendant
       quantifier contradiction pairs (respecting rebinding), and char-literal / guillemet
       handling in conclusion triviality checks.
    """

    VACUOUS_BOTH_SCOPES = {
        "nested_strict_implicit_false": "theorem bad ⦃h : ∀ ⦃y : Nat⦄, False⦄ : x = 1 := by sorry\n",
        "strict_implicit_char_close_and_false": "theorem bad ⦃h : c = '⦄' ∧ False⦄ : x = 1 := by sorry\n",
        "forall_strict_implicit_nat_lt0_hyp": "theorem bad (h : ∀ ⦃x : Nat⦄, x < 0) : x = 1 := by sorry\n",
        "forall_strict_implicit_false_hyp": "theorem bad (h : ∀ ⦃x : Nat⦄, False) : x = 1 := by sorry\n",
        "dep_arrow_implicit_false": "theorem bad : {h : False} → x = 1 := by sorry\n",
        "dep_arrow_strict_implicit_false": "theorem bad : ⦃h : False⦄ → x = 1 := by sorry\n",
        "dep_arrow_inst_false": "theorem bad : [h : False] → x = 1 := by sorry\n",
        "dep_arrow_implicit_nat_lt0": "theorem bad : {n : Nat} → (h : n < 0) → x = 1 := by sorry\n",
        "dep_arrow_strict_implicit_nat_lt0": "theorem bad : ⦃n : Nat⦄ → (h : n < 0) → x = 1 := by sorry\n",
        "named_arrow_false_neg_pair": "theorem bad (P : Prop) (h1 : P) (h2 : (hp : P) → False) : x = 1 := by sorry\n",
        "named_arrow_true_false": "theorem bad (h : (ht : True) → False) : x = 1 := by sorry\n",
        "thm_name_no_space_strict_imp": "theorem bad⦃x : Nat⦄ (h : False) : x = 1 := by sorry\n",
        "where_prefix_ident_with_lambda": "theorem bad : (fun x => x) = id → whereFoo = 0 → (h : False) → x = 1 := by sorry\n",
        "bare_where_prefix_binder": "theorem bad where_x (h : False) : x = 1 := by sorry\n",
        "hoare_eq_refl_neg": "theorem bad (h : ¬ (⦃a = b⦄ = ⦃a = b⦄)) : x = 1 := by sorry\n",
        "nested_quant_ancestor_contradiction": "theorem bad (P : Nat → Prop) (h : ∃ x : Nat, P x ∧ ∃ y : Nat, ¬ P x) : x = 1 := by sorry\n",
        "nested_quant_forall_ancestor_contradiction": "theorem bad (P : Nat → Prop) (h : ∀ x : Nat, P x ∧ ∃ y : Nat, ¬ P x) : x = 1 := by sorry\n",
        "except_string_blanked_clash": 'theorem bad (h : Except.ok 1 = Except.error "boom") : x = 1 := by sorry\n',
        "option_qualified_clash": "theorem bad (h : Option.none = Option.some x) : y = 1 := by sorry\n",
        "float_shadowed_by_nat_in_quant": "theorem bad (x : Float) (h : ∀ x : Nat, ¬ x ≤ x) : y = 1 := by sorry\n",
        "coerced_nat_plus_one_lt0": "theorem bad (xs : List Nat) (h : ↑xs.length + 1 < 0) : y = 1 := by sorry\n",
        "cons_append_nil": "theorem bad (x : Nat) (xs ys : List Nat) (h : x :: xs ++ ys = []) : x = 0 := by sorry\n",
    }

    TRIVIAL_CONCLUSION_ALL_SCOPE = {
        "char_lit_arrow_or_true": "theorem bad (c : Char) : c = '→' ∨ True := by sorry\n",
        "char_lit_lparen_or_true": "theorem bad (c : Char) : c = '(' ∨ True := by sorry\n",
        "guillemet_if_or_true": "theorem bad : «if» = 0 ∨ True := by sorry\n",
        "guillemet_assign_in_stmt": "theorem bad : «a := b» = «a := b» := by sorry\n",
        "forall_strict_implicit_comma_true": "theorem bad : ∀ ⦃h : ∀ a, P a⦄, True := by sorry\n",
    }

    CLEAN = {
        "coerced_sub_len_lt_0": "theorem ok (a b : List Nat) (h : ↑a.length - ↑b.length < 0) : a.length < b.length := by sorry\n",
        "coerced_sub_1_lt_0": "theorem ok (a : List Nat) (h : ↑a.length - 1 < 0) : a = [] := by sorry\n",
        "one_minus_coerced_len_lt_0": "theorem ok (a : List Nat) (h : 1 - ↑a.length < 0) : a.length ≥ 2 := by sorry\n",
        "nat_cast_sub_lt_0": "theorem ok (a b : Nat) (h : Nat.cast a - Nat.cast b < 0) : a < b := by sorry\n",
        "sumSizes_pipe_dot_lt_0": "theorem ok (h : sumSizes xs |>.toInt < 0) : xs ≠ [] := by sorry\n",
        "nat_prefix_pipe_dot_lt_0": "theorem ok (n : Nat) (h : Nat.succ n |>.toInt < 0) : n ≠ 0 := by sorry\n",
        "sumSizes_band_lt_0": "theorem ok (y : Int64) (h : sumSizes xs &&& y < 0) : y < 0 := by sorry\n",
        "shift_suffix_lt_0": "theorem ok (x : Int64) (xs : List Nat) (h : x>>>xs.length < 0) : x < 0 := by sorry\n",
        "some_bind_none": "theorem ok (x : Nat) (f : Nat → Option Nat) (h : some x >>= f = none) : f x = none := by sorry\n",
        "some_pipe_dot_none": "theorem ok (x : Nat) (f : Nat → Option Nat) (h : some x |>.bind f = none) : f x = none := by sorry\n",
        "some_seqr_none": "theorem ok (x : Nat) (y : Option Nat) (h : some x *> y = none) : y = none := by sorry\n",
        "except_bind_err": "theorem ok (x : Nat) (e : String) (f : Nat → Except String Nat) (h : Except.ok x >>= f = Except.error e) : f x = Except.error e := by sorry\n",
        "sum_pipe_dot_swap": "theorem ok (x y : Nat) (h : Sum.inl x |>.swap = Sum.inr y) : x = y := by sorry\n",
        "cons_pipe_dot_nil": "theorem ok (x : Nat) (xs : List Nat) (h : x :: xs |>.tail = []) : xs = [] := by sorry\n",
        "cons_bind_nil": "theorem ok (x : Nat) (xs : List Nat) (f : Nat → List Nat) (h : x :: xs >>= f = []) : f x = [] := by sorry\n",
        "forall_mem_eq_neq_pair": "theorem ok (s : List Nat) (a b : Nat) (h1 : ∀ x ∈ s, a = b) (h2 : ∀ x ∈ s, a ≠ b) : s = [] := by sorry\n",
        "forall_prop_eq_neq_pair": "theorem ok (P : Prop) (a b : Nat) (h1 : ∀ hp : P, a = b) (h2 : ∀ hp : P, a ≠ b) : ¬ P := by sorry\n",
        "if_else_eq_neq_pair": "theorem ok (c : Prop) [Decidable c] (a b : Nat) (h1 : if c then True else a = b) (h2 : if c then True else a ≠ b) : c := by sorry\n",
        "hoare_conj_false": "theorem ok (h : ⦃P ∧ False ∧ Q⦄ t ⦃R⦄) : R = R → P := by sorry\n",
        "hoare_disj_true_conc": "theorem ok : ⦃P ∨ True ∨ Q⦄ t ⦃R⦄ := by sorry\n",
        "angle_disj_true_conc": "theorem ok (x : Prop × Prop) (P Q R : Prop) : ⟨P, Q ∨ True ∨ R⟩ = x := by sorry\n",
        "if_arrow_true_fastpath": "theorem ok (c : Prop) [Decidable c] (P : Prop) : if c then P else P → True := by sorry\n",
        "if_arrow_taut_fastpath": "theorem ok (c : Prop) [Decidable c] (P Q : Prop) (h : P) : if c then Q else Q → P := by sorry\n",
        "fin_shadowed_in_quant": "theorem ok (Fin : Nat → Type) (h : ∃ x : Fin 1, x < 0) : x = 1 := by sorry\n",
        "untyped_call_proj_fin0": "theorem ok (R : Nat → Prop) (P : Fin 0 → Prop) (h : ∀ s, P s ∧ R s.val ∧ False) : ∀ s : Fin 0, P s := by sorry\n",
        "untyped_call_inner_rebind_exists": "theorem ok {α : Type} (P : α → Prop) (R : Nat → Prop) (h : ∀ s, P s ∧ (∃ s : Nat, R s) ∧ False) : α → False := by sorry\n",
        "untyped_call_inner_rebind_arrow": "theorem ok {α : Type} (P : α → Prop) (R : Nat → Prop) (h : ∀ s, P s ∧ ((s : Nat) → R s) ∧ False) : α → False := by sorry\n",
        "coerced_len_false_elim": "theorem ok (xs : List Nat) (h : ↑xs.length < 0) : False := by omega\n",
        "float_not_le_refl": "theorem ok (x : Float) (h : ¬ x ≤ x) : x.isNaN = true := by sorry\n",
        "float_not_ge_refl_quant": "theorem ok (h : ∃ x : Float, ¬ x ≥ x) : P := by sorry\n",
        "float_nan_not_le_refl": "theorem ok (h : ¬ Float.nan ≤ Float.nan) : P := by sorry\n",
        "strict_imp_exists_shadow": "theorem ok (h1 : ∃ ⦃x : Nat⦄ (y : Nat), y = 1) (h2 : ∃ ⦃x : Nat⦄ (y : Nat), y ≠ 1) : P := by sorry\n",
        "nested_quant_rebind_shadow": "theorem ok (P : Nat → Prop) (h : ∃ x : Nat, P x ∧ ∃ x : Nat, ¬ P x) : Q := by sorry\n",
        "set_builder_premise": "theorem ok : {x : Nat | x < 0} → False := by sorry\n",
        "dep_arrow_named_true_false_refutation": "theorem ok : (h : (ht : True) → False) → False := fun h => h trivial\n",
    }

    def setUp(self) -> None:
        proof_health.clear_in_process_caches()

    def test_a2_vacuous_headers_flagged_in_both_scopes(self) -> None:
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        for label, src in self.VACUOUS_BOTH_SCOPES.items():
            self.assertIn(rule, _rules(audit.scan_lean_text(src)), f"all-scope missed {label}")
            self.assertIn((R7, rule, 1), scan67(src), f"default-scope missed {label}")

    def test_a2_trivial_conclusions_flagged_in_all_scope(self) -> None:
        rule = audit.RULE_TRIVIAL_CONCLUSION
        for label, src in self.TRIVIAL_CONCLUSION_ALL_SCOPE.items():
            self.assertIn(rule, _rules(audit.scan_lean_text(src)), f"all-scope missed {label}")

    def test_a2_clean_headers_stay_quiet_in_both_scopes(self) -> None:
        for label, src in self.CLEAN.items():
            self.assertEqual(audit.scan_lean_text(src), [], f"all-scope flagged {label}")
            self.assertEqual(scan67(src), [], f"default-scope flagged {label}")

    def test_a2_bare_binder_regex_linear_no_redos(self) -> None:
        long_ident = "very_long_lean_identifier_name_" * 4
        t0 = time.perf_counter()
        self.assertIsNone(proof_health._BARE_BINDER_NAMES_RE.fullmatch(long_ident + " < 0"))
        src = f"theorem ok (h : ∀ {long_ident} < n, P {long_ident}) : Q := by sorry\n"
        self.assertEqual(audit.scan_lean_text(src), [])
        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        self.assertLess(elapsed_ms, 50.0, f"ReDoS regression: took {elapsed_ms:.2f}ms")

    def test_a2_helper_invariants(self) -> None:
        prem = proof_health._arrow_premise_binder
        self.assertEqual(prem("{h : False}"), ("h", "False"))
        self.assertEqual(prem("⦃h : False⦄"), ("h", "False"))
        self.assertEqual(prem("[h : False]"), ("h", "False"))
        self.assertEqual(prem("{x : Nat | x < 5}"), ("", "{x : Nat | x < 5}"))
        self.assertEqual(prem("{x : {y : Nat // y < 5}}"), ("x", "{y : Nat // y < 5}"))
        self.assertEqual(prem("{h : a || b = true}"), ("h", "a || b = true"))
        self.assertEqual(prem("⦃P⦄ t ⦃Q⦄"), ("", "⦃P⦄ t ⦃Q⦄"))

        nat = proof_health._is_nat_like_operand
        none: frozenset[str] = frozenset()
        for yes, nv in (
            ("↑xs.length + 1", none),
            ("↑n", frozenset({"n"})),
            ("↑(a - b)", frozenset({"a", "b"})),
            ("Nat.cast a", frozenset({"a"})),
            ("arr[i].length", none),
        ):
            self.assertTrue(nat(yes, nv), yes)
        for no, nv in (
            ("↑a.length - ↑b.length", none),
            ("↑a.length - 1", none),
            ("1 - ↑a.length", none),
            ("Nat.cast a - Nat.cast b", frozenset({"a", "b"})),
            ("a - b + ↑c", frozenset({"a", "b", "c"})),
            ("sumSizes xs |>.toInt", none),
            ("Nat.succ n |>.toInt", frozenset({"n"})),
            ("x>>>xs.length", none),
            ("(f)(xs).length", none),
            ("↑x", none),
        ):
            self.assertFalse(nat(no, nv), no)

        self.assertEqual(proof_health._arrow_false_antecedent("(hp : P) → False"), "P")
        self.assertEqual(proof_health._arrow_false_antecedent("{ht : True} → False"), "True")
        self.assertIsNone(proof_health._split_lean_theorem_header(" ⦃x : ⦃y : Nat⦄", 0))

    def test_check_trusted_agrees_on_every_a2_header(self) -> None:
        ct = _load_check_trusted()
        all_cases = {**self.VACUOUS_BOTH_SCOPES, **self.TRIVIAL_CONCLUSION_ALL_SCOPE, **self.CLEAN}
        for label, src in all_cases.items():
            for scope in ("all", "annotated", "annotated-only"):
                self.assertEqual(
                    [(f.rule, f.line, f.message) for f in ct.audit_lean_text(src, vacuity_scope=scope)],
                    [(f.rule, f.line, f.message) for f in proof_health.audit_lean_text(src, vacuity_scope=scope)],
                    (scope, label),
                )


class TestNegationPrecedenceB3AdversarialFixes(unittest.TestCase):
    r"""`[adv B3]` regressions for bugs found in `[adv A2]` and earlier vacuity auditor passes:

    1. Cold-scan throughput (`test_sub_5ms_runtime_benchmark` failed by 0.05 us/line after A2):
       the C-level fast paths added here (`_SIMPLE_BINDER_MATCH`, `'`-first `_CHAR_LITERAL_RE`,
       keyword-free `_NOKW` scanners behind `_has_binder_keyword`, `_split_single_depth0_op`) must
       return exactly what the scans they shortcut return.
    2. `let ` substring in the statement / proof split: an identifier ending in `let`
       (`droplet = droplet := rfl`, `isOutlet x`, a field `s.let`) was read as a `let x := v`
       binding, so the proof was swallowed into the statement and no conclusion check could fire.
    3. `theorem t : A ∧ B where left := ..`: the statement ran through the depth-0 `where` to the
       first field's `:=` (`A ∧ B where left`), hiding trivial and tautological conclusions.
    4. `Float` NaN exemption keyed on the substring `Float`: naming a `Nat` binder `numFloats`
       hid `¬ numFloats ≤ numFloats`.
    5. `_untyped_binders_inhabited_by_calls` trusted any direct call: in `∀ s, E s ∧ R s ∧ False`
       with `E : Fin 0 → Prop` the first use fixes `s : Fin 0`, so the hypothesis holds vacuously.
    6. `int()` on source numerals: a literal longer than `sys.get_int_max_str_digits()` (4300
       digits) raised `ValueError` out of `audit_lean_text` (`(h : 99...9 = 1)`) and out of the
       `anneal:` directive lexer, aborting the scan of the whole file.
    """

    VACUOUS_BOTH_SCOPES = {
        "nat_named_numFloats_not_le": "theorem bad (numFloats : Nat) (h : ¬ numFloats ≤ numFloats) : x = 1 := by sorry\n",
        "nat_named_FloatCount_not_ge": "theorem bad (FloatCount : Nat) (h : ¬ FloatCount ≥ FloatCount) : x = 1 := by sorry\n",
        "nat_binder_lenFloat_not_le": "theorem bad (lenFloat : Nat) (h : ¬ lenFloat ≤ lenFloat) : x = 1 := by sorry\n",
        "float_binder_other_operand": "theorem bad (x : Float) (n : Nat) (h : ¬ n ≤ n) : y = 1 := by sorry\n",
        "where_instance_false_hyp": "theorem bad (h : False) : P ∧ Q where\n  left := h.elim\n  right := h.elim\n",
        "where_instance_dep_arrow_false": "theorem bad : (h : False) → P ∧ Q where\n  left := h.elim\n  right := h.elim\n",
        "let_suffix_ident_false_hyp": "theorem bad (droplet : Nat) (h : False) : droplet = 1 := by sorry\n",
        "untyped_first_use_inhabited": "theorem bad (E : Fin 0 → Prop) (R : Nat → Prop) (h : ∀ s, R s ∧ E s ∧ False) : x = 1 := by sorry\n",
        "untyped_two_names_in_order": "theorem bad (R : Nat → Bool → Prop) (h : ∀ s t, R s t ∧ False) : x = 1 := by sorry\n",
    }

    TRIVIAL_CONCLUSION_ALL_SCOPE = {
        "let_suffix_ident_refl": "theorem bad (droplet : Nat) : droplet = droplet := rfl\n",
        "let_suffix_app_refl": "theorem bad (x : Nat) : isOutlet x = isOutlet x := rfl\n",
        "let_field_refl": "theorem bad (s : S) : s.let = s.let := rfl\n",
        "let_suffix_true": "theorem bad (outlet : Nat) : True := trivial\n",
        "where_instance_true_and_true": "theorem bad : True ∧ True where\n  left := trivial\n  right := trivial\n",
        "where_instance_iff_refl": "theorem bad (p : Prop) : p ↔ p where\n  mp := id\n  mpr := id\n",
        "where_same_line_refl_and": "theorem bad (a : Nat) : a = a ∧ True where left := rfl; right := trivial\n",
    }

    TAUTOLOGY_ALL_SCOPE = {
        "let_suffix_taut": "theorem bad (droplet P : Prop) (h : droplet ∧ P) : droplet ∧ P := h\n",
        "where_instance_taut": "theorem bad (A B : Prop) (h : A ∧ B) : A ∧ B where\n  left := h.1\n  right := h.2\n",
    }

    CLEAN = {
        "float_binder_not_le": "theorem ok (x : Float) (h : ¬ x ≤ x) : x.isNaN = true := by sorry\n",
        "float_toFloat_not_le": "theorem ok (n : Nat) (h : ¬ n.toFloat ≤ n.toFloat) : P n := by sorry\n",
        "float_namespace_nan_not_ge": "theorem ok (h : ¬ Float.nan ≥ Float.nan) : P := by sorry\n",
        "float_accessor_app_not_le": "theorem ok (v : Vec) (h : ¬ asFloat v ≤ asFloat v) : P v := by sorry\n",
        "float_ascription_not_le": "theorem ok (h : ¬ (0.0 / 0.0 : Float) ≤ (0.0 / 0.0 : Float)) : P := by sorry\n",
        "untyped_first_use_empty_binder_dom": "theorem ok (E : Fin 0 → Prop) (R : Nat → Prop) (h : ∀ s, E s ∧ R s ∧ False) : P := by sorry\n",
        "untyped_first_use_global_fn": "theorem ok (R : Nat → Prop) (h : ∀ s, Fin.elim0 s ∧ R s ∧ False) : P := by sorry\n",
        "untyped_first_use_typevar_dom": "theorem ok (α : Type) (E : α → Prop) (R : Nat → Prop) (h : ∀ s, E s ∧ R s ∧ False) : P := by sorry\n",
        "untyped_first_use_ascription": "theorem ok (R : Nat → Prop) (h : ∀ s, (s : Fin 0) = s ∧ R s ∧ False) : P := by sorry\n",
        "untyped_first_use_projection": "theorem ok (R : Nat → Prop) (h : ∀ s, s.isLt ∧ R s ∧ False) : P := by sorry\n",
        "real_let_binding_in_statement": "theorem ok : let x := 5\n  x + 0 = 5 := by simp\n",
        "real_let_semicolon_in_statement": "theorem ok (n : Nat) : let m := n + 1; n < m := by simp\n",
        "where_after_proof_body": "theorem ok (n : Nat) : n + 0 = n := by\n  exact aux n\nwhere\n  aux (m : Nat) : m + 0 = m := rfl\n",
        "where_instance_nontrivial": "theorem ok (p q : Prop) (hp : p) (hq : q) : p ∧ q where\n  left := hp\n  right := hq\n",
        "where_prefix_ident": "theorem ok (whereabouts n : Nat) (h : whereabouts = n) : n = whereabouts := h.symm\n",
        "guillemet_where_name": "theorem ok («where» n : Nat) (h : «where» = n) : n = «where» := h.symm\n",
    }

    def setUp(self) -> None:
        proof_health.clear_in_process_caches()

    def test_b3_vacuous_headers_flagged_in_both_scopes(self) -> None:
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        for label, src in self.VACUOUS_BOTH_SCOPES.items():
            self.assertIn(rule, _rules(audit.scan_lean_text(src)), f"all-scope missed {label}")
            self.assertIn((R7, rule, 1), scan67(src), f"default-scope missed {label}")

    def test_b3_trivial_and_tautological_conclusions_flagged_in_all_scope(self) -> None:
        for label, src in self.TRIVIAL_CONCLUSION_ALL_SCOPE.items():
            self.assertIn(
                audit.RULE_TRIVIAL_CONCLUSION, _rules(audit.scan_lean_text(src)), f"missed {label}"
            )
        for label, src in self.TAUTOLOGY_ALL_SCOPE.items():
            self.assertIn(
                audit.RULE_TAUTOLOGICAL_IMPLICATION, _rules(audit.scan_lean_text(src)), f"missed {label}"
            )

    def test_b3_clean_headers_stay_quiet_in_both_scopes(self) -> None:
        for label, src in self.CLEAN.items():
            self.assertEqual(audit.scan_lean_text(src), [], f"all-scope flagged {label}")
            self.assertEqual(scan67(src), [], f"default-scope flagged {label}")

    def test_b3_statement_ends_at_where_and_ignores_let_suffixes(self) -> None:
        split = proof_health._split_lean_theorem_header
        self.assertEqual(
            split(" : True ∧ True where\n  left := trivial\n  right := trivial\n", 0),
            ([], "True ∧ True", []),
        )
        self.assertEqual(
            split(" (h : A) : B ∧ (C where_x) where\n  left := f (x := 1)\n", 0),
            ([("h", "A")], "B ∧ (C where_x)", []),
        )
        self.assertEqual(split(" (droplet : Nat) : droplet = droplet := rfl\n", 0)[1], "droplet = droplet")
        self.assertEqual(split(" : isOutlet x = y := by simp [h := 1]\n", 0)[1], "isOutlet x = y")
        self.assertEqual(split(" : s.let = t := rfl\n", 0)[1], "s.let = t")
        self.assertEqual(split(" : let' = t := rfl\n", 0)[1], "let' = t")
        # A real `let` binding still keeps its own `:=` inside the statement.
        self.assertEqual(split(" : let x := 5\n  x + 0 = 5 := by simp\n", 0)[1], "let x := 5\n  x + 0 = 5")
        self.assertEqual(split(" : droplet = (let y := 1; y) := rfl\n", 0)[1], "droplet = (let y := 1; y)")

    def test_b3_helper_invariants(self) -> None:
        may_float = proof_health._operand_may_be_float
        none: frozenset[str] = frozenset()
        for yes, fv in (
            ("x", frozenset({"x"})),
            ("x + 1", frozenset({"x"})),
            ("Float.nan", none),
            ("n.toFloat", none),
            ("asFloat v", none),
            ("x.toFloat32", none),
            ("0.0 / 0.0 : Float", none),
        ):
            self.assertTrue(may_float(yes, fv), yes)
        for no, fv in (
            ("numFloats", none),
            ("FloatCount", none),
            ("lenFloat", none),
            ("n", frozenset({"x"})),
            ("xs.length", none),
            ("isFloatLike n", none),
        ):
            self.assertFalse(may_float(no, fv), no)

        first = proof_health._first_standalone_use
        self.assertEqual(first("R s ∧ E s", "s"), 2)
        self.assertEqual(first("xs.s ∧ s' ∧ ss ∧ R s", "s"), 19)
        self.assertEqual(first("s.val < 1 ∧ R s", "s"), 0)
        self.assertEqual(first("R t", "s"), -1)

        inhab = proof_health._untyped_binders_inhabited_by_calls
        doms = {"R": (True,), "E": (False,)}
        self.assertTrue(inhab({"s"}, "R s ∧ E s ∧ False", doms, frozenset({"s"})))
        self.assertFalse(inhab({"s"}, "E s ∧ R s ∧ False", doms, frozenset({"s"})))
        self.assertFalse(inhab({"s"}, "g s ∧ R s ∧ False", doms, frozenset({"s"})))
        self.assertFalse(inhab({"s", "t"}, "R s ∧ E t ∧ R t ∧ False", doms, frozenset({"s", "t"})))

    def test_b3_fast_paths_agree_with_the_scans_they_shortcut(self) -> None:
        import re

        ph = proof_health
        texts = [
            "decodeScalar sz bs = some (v, rest) → rest.length < bs.length → (∀ x, ok x = true) → enc v ++ rest = bs",
            "bs.length = n + List.length (encode x) → ∃ y, decode bs = some y",
            "(∀ i < n, f i = g i) → if c then a else b",
            "x' = y'' → c = 'a' → f «weird := name» → ⟨a, b⟩ = p → show P by simp",
            "shift_left has_bytes fun_ext letters matched iff exists! forall? by' x.by h.if _fun funx 1by ∀by",
            "c = '(' ∧ d = ')' ∧ e = '\\'' ∧ f = '→' ∨ g = h' ↔ k'' = 'x'",
            "f <| g $ h <|> k |> m ↔ a <-> b -> c ∧ d ∨ e /\\ f \\/ g",
            "by", "(by simp)", "a.fun b", "fun", "if", "'match", "show.", "have\n", "λfun", "let", "outlet let'",
            "exists", "forall", "?by", "!if c", "x.let", "match x with | _ => y", "",
        ]
        kw_alt = re.compile(ph._BINDER_KEYWORD_ALT)
        old_char_lit = re.compile(r"(?<![\w'.!?])'(?:\\[^\n]{1,8}?|[^\\'\n])'")
        old_kw = r"(?<![\w'.!?])(?:forall|exists|fun|if|match|let|have|show|by)(?![\w'!?])"
        old_scanners = (
            (
                ph._ARROW_SCAN_RE,
                ph._ARROW_SCAN_NOKW_RE,
                r"«[^»]*»|(?<![\w'.!?])'(?:\\[^\n]{1,8}?|[^\\'\n])'|[(){}\[\]⟨⟩⦃⦄]|↔|<->|<\|>|<\||\$|→|->|∀|∃|λ|" + old_kw,
            ),
            (
                ph._TOP_LEVEL_LOOSER_THAN_NOT_RE,
                ph._TOP_LEVEL_LOOSER_THAN_NOT_NOKW_RE,
                r"«[^»]*»|[()\[\]{}⟨⟩⦃⦄]|↔|<->|<\|>|<\||\$|→|->|∨|\\/|∧|/\\|∀|∃|λ|" + old_kw,
            ),
            (
                ph._CONJ_TOP_BOUND_RE,
                ph._CONJ_TOP_BOUND_NOKW_RE,
                r"«[^»]*»|[()\[\]{}⟨⟩⦃⦄]|↔|<->|→|->|<\|>|<\||\|>|\$|∨|\\/|∀|∃|λ|" + old_kw,
            ),
            (
                ph._TOP_BOUND_RE,
                ph._TOP_BOUND_NOKW_RE,
                r"«[^»]*»|(?<![\w'.!?])'(?:\\[^\n]{1,8}?|[^\\'\n])'|[()\[\]{}⟨⟩⦃⦄]|"
                r"↔|→|->|<\|>|<\||\|>|\$|∨|∃|∀|λ|"
                r"(?<![\w'.!?])(?:fun|forall|exists|if|match|let|have|show|by)(?![\w'!?])",
            ),
        )

        def tokens(pat: "re.Pattern[str]", text: str) -> list[tuple[int, str]]:
            return [(m.start(), m.group(0)) for m in pat.finditer(text)]

        for text in texts:
            has_kw = kw_alt.search(text) is not None
            self.assertEqual(ph._has_binder_keyword(text), has_kw, text)
            self.assertEqual(
                ph._has_prefix_binder_hint(text), has_kw or any(c in text for c in "∀∃λ"), text
            )
            self.assertEqual(
                [m.span() for m in ph._CHAR_LITERAL_RE.finditer(text)],
                [m.span() for m in old_char_lit.finditer(text)],
                text,
            )
            for q in range(len(text)):
                self.assertEqual(
                    ph._CHAR_LITERAL_RE.match(text, q) is None, old_char_lit.match(text, q) is None, (text, q)
                )
            for full, nokw, old_src in old_scanners:
                self.assertEqual(tokens(full, text), tokens(re.compile(old_src), text), text)
                if not has_kw:
                    self.assertEqual(tokens(nokw, text), tokens(full, text), text)

        exprs = [
            "a = b", "f (g x) (h (k y)) = z", "f (g (h (k x))) = z", "a ) ( = b", "(a = b", "a] = [b",
            "«x = y» = z", "f «a(b» = c", "a == b", "a != b", "x := 1", "a <= b", "a >= b", "a = b = c",
            "(a = b) = c", "a = (b = c)", "f ⟨a, b⟩ {c} [d] ⦃e⦄ = g", "xs.length < 0", "a << b", "a <| b",
            "a <- b", "a <$> b", "a <*> b", "f (x < y) < z", "a < b < c", "0 > n", "a -> b", "a >= b",
            "a >> b", "a => b", "a |> f", "a *> b", "a $> b", "f (a > b) > c", "a ≤ b", "f (a ≤ b) ≤ c",
            "a ≤ b ≤ c", "", "=", "<", ">", "≤", "= a", "a =", "(((a))) = (b)", "a = b)", "a\n  = b",
        ]
        for e in exprs:
            self.assertEqual(ph._split_top_level_eq(e), ph._split_top_level_pat(e, ph._STANDALONE_EQ_SPLIT_RE), e)
            for op, not_before, not_after, pat in (
                ("=", "=!<>:", "=", ph._STANDALONE_EQ_SPLIT_RE),
                ("<", "<", "<=|-$*", ph._LT_TOP_SPLIT_RE),
                ("≤", "", "", ph._LE_TOP_SPLIT_RE),
                (">", "->=|*$", ">=", ph._GT_TOP_SPLIT_RE),
            ):
                fast = ph._split_single_depth0_op(e, op, not_before, not_after)
                if fast is not None:
                    self.assertEqual(fast, ph._split_top_level_pat(e, pat), (op, e))

        headers = [
            " (x : Nat) {y : Int} [inst : Foo α] (h : x = 1) : P x := by simp",
            " (x y : Nat)(h : f (g x) = y) {z : Fin (n + 1)} : P := by simp",
            " {f (a : Nat) : T} (x := 5) (h : c = ')') [Foo] (g : (a : Nat) → T) bare : P := rfl",
            " ( : T) (x : ) (a b\n  : List Nat)\n  (h :\n    a = b)\n  : P := rfl",
            " (x] : Nat) {y) : Nat} [z} : Nat] (w ⦃ : Nat) (h' : P) (k : c = 'a') : Q := rfl",
            " (x : A ∧ {y // p y}) {z : B → [C]} [w : D (E)] ⦃v : F⦄ (u :: U) (t :=: T) : Q := rfl",
            " (x : Nat",
        ]
        never = {key: (lambda *args: None) for key in ph._SIMPLE_BINDER_MATCH}
        for header in headers:
            fast_parse = ph._split_lean_theorem_header(header, 0)
            with patch.dict(ph._SIMPLE_BINDER_MATCH, never):
                self.assertEqual(ph._split_lean_theorem_header(header, 0), fast_parse, header)

    def test_b3_long_numerals_are_compared_not_crashed_on(self) -> None:
        # `int()` raises past 4300 digits: one long literal used to abort the whole file's scan.
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        big = "9" * 5000
        for label, hyp in (
            ("eq", f"{big} = 1"),
            ("eq_leading_zeros", f"{'0' * 5000}1 = 2"),
            ("lt", f"{big} < 1"),
            ("lt_equal", f"{big} < {big}0".replace(f"{big}0", big)),
            ("le", f"{big}0 ≤ {big}"),
            ("ge", f"1 ≥ {big}"),
            ("gt", f"1 > {big}"),
        ):
            src = f"theorem bad (h : {hyp}) : x = 1 := by sorry\n"
            self.assertIn(rule, _rules(audit.scan_lean_text(src)), f"all-scope missed {label}")
            self.assertIn((R7, rule, 1), scan67(src), f"default-scope missed {label}")
        for label, hyp in (
            ("eq_same_value", f"{'0' * 5000}7 = 7"),
            ("lt_true", f"1 < {big}"),
            ("le_true", f"{big} ≤ {big}0"),
            ("ge_true", f"{big}0 ≥ {big}"),
            ("gt_true", f"{big} > 1"),
        ):
            src = f"theorem ok (h : {hyp}) : P := by sorry\n"
            self.assertEqual(audit.scan_lean_text(src), [], f"flagged {label}")
        key = proof_health._num_lit_key
        self.assertEqual(key("0007"), key("7"))
        self.assertEqual(key("000"), key("0"))
        self.assertLess(key("9"), key("10"))
        self.assertLess(key("٣"), key("12"))  # `\d` admits non-ASCII decimal digits, as `int()` does
        self.assertEqual(key("٣٤"), key("34"))
        # The `anneal:` directive lexer rejects an out-of-range integer instead of raising.
        toks, err = proof_health._lex_spec_tokens(f"width == {big}")
        self.assertEqual(toks, [])
        self.assertIn("too large", err)
        toks, err = proof_health._lex_spec_tokens(f"width == {'0' * 5000}42")
        self.assertEqual(err, "")
        self.assertEqual(toks[-1], ("Int", 42))
        self.assertIn("too large", proof_health._lex_spec_tokens("width == 340282366920938463463374607431768211456")[1])
        self.assertEqual(
            proof_health._lex_spec_tokens("width == 340282366920938463463374607431768211455")[0][-1],
            ("Int", (1 << 128) - 1),
        )

    def test_b3_fast_path_regexes_stay_linear(self) -> None:
        n = 40000
        hostile = (
            "(" * n + " = x",
            "(a" * n + " = x",
            ")(" * n + " = x",
            "(a (b" * (n // 2) + ")" + " < 0",
            "x" * n + " = " + "(" * n,
        )
        t0 = time.process_time()
        for expr in hostile:
            proof_health._split_top_level_eq(expr)
            proof_health._split_single_depth0_op(expr, "<", "<", "<=|-$*")
            proof_health._has_binder_keyword("by" * n + expr)
            self.assertIsNone(proof_health._SIMPLE_BINDER_MATCH["("]("(" + "a b " * n, 0))
            self.assertEqual(audit.scan_lean_text(f"theorem ok (h : {expr}) : P := by sorry\n"), [])
        elapsed = time.process_time() - t0
        self.assertLess(elapsed, 3.0, f"fast-path regex blow-up: {elapsed:.2f}s")

    def test_check_trusted_agrees_on_every_b3_header(self) -> None:
        ct = _load_check_trusted()
        all_cases = {
            **self.VACUOUS_BOTH_SCOPES,
            **self.TRIVIAL_CONCLUSION_ALL_SCOPE,
            **self.TAUTOLOGY_ALL_SCOPE,
            **self.CLEAN,
        }
        for label, src in all_cases.items():
            for scope in ("all", "annotated", "annotated-only"):
                self.assertEqual(
                    [(f.rule, f.line, f.message) for f in ct.audit_lean_text(src, vacuity_scope=scope)],
                    [(f.rule, f.line, f.message) for f in proof_health.audit_lean_text(src, vacuity_scope=scope)],
                    (scope, label),
                )


class TestNegationPrecedenceA3AdversarialFixes(unittest.TestCase):
    r"""`[adv A3]` regressions for bugs found in `[adv B3]` and earlier vacuity auditor passes:

    1. Depth-0 `let` vs proof `:=`: closed `let x := 1 in ...`, parenthesised `(let x := 1 in x)`,
       `do` `let x ← f`, and whitespace variants (`let\tx`, `let\n  x`) were mishandled by the
       `rfind("let ")` heuristic, swallowing `:= rfl` / `:= h` into the statement.
    2. `where` before pattern-matching `\n  | ... =>` field arms: `_PIPE_ARM_RE` cut at `|` before
       checking for an earlier depth-0 `where`, leaving `A ∧ B where\n  left` and emitting a bogus
       `stmt-cut`.
    3. `Float` / `Float32` non-reflexivity symmetry & `_operand_may_be_float` precision:
       - `Float32` binders were missed by `_float_vars_before` and `_hyp_atoms`;
       - `tok != e` in `_operand_may_be_float` exempted `Nat` variables ending in `Float` inside
         compound operands (`lenFloat + 1`, `f lenFloat`);
       - Reflexive `x ≤ x` conclusions over `Float`/`Float32` (and `n.toFloat`) were falsely flagged
         as `RULE_TRIVIAL_CONCLUSION` even though `NaN ≤ NaN` is false.
    4. Implicit/instance parameter shift & multi-arg alignment in `_untyped_binders_inhabited_by_calls`:
       - `_quantifier_context_before` counted `{α : Type}` / `⦃α : Type⦄` / `[DecidableEq Nat]`
         domains as explicit positional slots, shifting an inhabited domain onto an empty `Fin 0`
         argument (`R x s` with `R : {α : Type} → Nat → Fin 0 → Prop`);
       - `@R` and named arguments `(a := 0)` similarly broke positional alignment;
       - Numeral (`R 0 s`) and projection/subscript (`R xs.length s`, `R arr[0] s`) leading args
         aborted the arg loop instead of advancing to the next positional slot;
       - `_first_standalone_use` matched inside guillemet identifiers `«s»`.
    5. Default-value / `autoParam` header binders `(x : T := v)` (also used in `ByteCodec.lean`):
       trailing depth-0 `:= default` leaked into `b_type`, breaking `Nat`/`Float`/`False` detection
       and `: False` refutation exemptions while nested `{ a := 1 }` and `let` stayed intact.
    6. Dependent-arrow inhabited domains in hypotheses: `(h : (x : Nat) → False)` /
       `(h : (x : Nat) → x < 0)` / `(h : (x : Nat) → P x ∧ ¬ P x)` were missed while `∀ x : Nat, ...`
       was caught.
    """

    VACUOUS_BOTH_SCOPES = {
        "lenFloat_plus_1_not_le": "theorem bad (lenFloat : Nat) (h : ¬ lenFloat + 1 ≤ lenFloat + 1) : x = 1 := by sorry\n",
        "app_lenFloat_not_le": "theorem bad (lenFloat : Nat) (h : ¬ f lenFloat ≤ f lenFloat) : x = 1 := by sorry\n",
        "nat_lenFloat_call_not_le": "theorem bad (lenFloat : Nat) (h : ¬ lenFloat 0 ≤ lenFloat 0) : x = 1 := by sorry\n",
        "float32_other_nat_not_le": "theorem bad (x : Float32) (n : Nat) (h : ¬ n ≤ n) : y = 1 := by sorry\n",
        "forall_float32_false": "theorem bad (h : ∀ x : Float32, False) : x = 1 := by sorry\n",
        "untyped_two_arg_numeral": "theorem bad (R : Nat → Nat → Prop) (h : ∀ s, R 0 s ∧ False) : x = 1 := by sorry\n",
        "untyped_two_arg_proj": "theorem bad (xs : List Nat) (R : Nat → Nat → Prop) (h : ∀ s, R xs.length s ∧ False) : x = 1 := by sorry\n",
        "untyped_two_arg_index": "theorem bad (arr : Array Nat) (R : Nat → Nat → Prop) (h : ∀ s, R arr[0] s ∧ False) : x = 1 := by sorry\n",
        "untyped_guillemet_before_use": "theorem bad (R : Nat → Prop) («s» : Nat) (h : ∀ s, «s» = 0 ∧ R s ∧ False) : x = 1 := by sorry\n",
        "optparam_nat_lt_zero": "theorem bad (n : Nat := 0) (h : n < 0) : x = 1 := by sorry\n",
        "autoparam_false_hyp": "theorem bad (h : False := by sorry) : x = 1 := by sorry\n",
        "autoparam_zero_eq_one": "theorem bad (h : 0 = 1 := by sorry) : x = 1 := by sorry\n",
        "forall_optparam_nat_lt_zero": "theorem bad : ∀ (n : Nat := 0) (h : n < 0), x = 1 := by sorry\n",
        "dep_arrow_nat_false": "theorem bad (h : (x : Nat) → False) : x = 1 := by sorry\n",
        "dep_arrow_nat_lt_zero": "theorem bad (h : (x : Nat) → x < 0) : x = 1 := by sorry\n",
        "dep_arrow_scoped_pos_neg": "theorem bad (P : Nat → Prop) (h : (x : Nat) → P x ∧ ¬ P x) : y = 1 := by sorry\n",
    }

    TRIVIAL_CONCLUSION_ALL_SCOPE = {
        "let_in_paren_refl": "theorem bad : (let x := 1 in x) = (let x := 1 in x) := rfl\n",
        "let_tab_paren_refl": "theorem bad : (let\tx := 1; x) = (let\tx := 1; x) := rfl\n",
        "where_pipe_field_trivial": "theorem bad : (∀ n : Nat, True) ∧ True where\n  left\n  | 0 => trivial\n  | _ + 1 => trivial\n  right := trivial\n",
        "where_all_pipe_fields_trivial": "theorem bad : (∀ n : Nat, True) ∧ (∀ m : Nat, True) where\n  left\n  | _ => trivial\n  right\n  | _ => trivial\n",
        "float_other_nat_le_conc": "theorem bad (x : Float) (n : Nat) : n ≤ n := Nat.le_refl n\n",
        "float_rebound_nat_forall_le_conc": "theorem bad (x : Float) : ∀ x : Nat, x ≤ x := fun _ => Nat.le_refl _\n",
        "lenFloat_plus_1_le_conc": "theorem bad (lenFloat : Nat) : lenFloat + 1 ≤ lenFloat + 1 := Nat.le_refl _\n",
    }

    TAUTOLOGY_ALL_SCOPE = {
        "let_in_paren_taut": "theorem bad (h : (let x := 1 in x) = 1) : (let x := 1 in x) = 1 := h\n",
        "where_pipe_field_taut": "theorem bad (h : (Nat → Prop) ∧ True) : (Nat → Prop) ∧ True where\n  left\n  | n => h.1 n\n  right := h.2\n",
    }

    CLEAN = {
        "float32_binder_not_le": "theorem ok (x : Float32) (h : ¬ x ≤ x) : x.isNaN = true := by sorry\n",
        "exists_float32_not_le": "theorem ok (h : ∃ x : Float32, ¬ x ≤ x) : P := by sorry\n",
        "dep_arrow_float_not_le": "theorem ok (h : (x : Float) → ¬ x ≤ x) : P := by sorry\n",
        "float_le_refl_conc": "theorem ok (x : Float) (h : ¬ x.isNaN) : x ≤ x := by sorry\n",
        "float32_le_refl_conc": "theorem ok (x : Float32) (h : ¬ x.isNaN) : x ≤ x := by sorry\n",
        "toFloat_le_refl_conc": "theorem ok (n : Nat) : n.toFloat ≤ n.toFloat := by sorry\n",
        "float_le_conc_conj": "theorem ok (x : Float) (h : ¬ x.isNaN) : x ≤ x ∧ True := by sorry\n",
        "float_le_conc_disj": "theorem ok (x : Float) (h : ¬ x.isNaN) : x ≤ x ∨ P := by sorry\n",
        "forall_float_le_conc": "theorem ok : ∀ x : Float, x ≤ x := by sorry\n",
        "forall_float32_le_conc": "theorem ok : ∀ x : Float32, x ≤ x := by sorry\n",
        "implicit_domain_shift_guarded": "theorem ok (x : Nat) (R : {α : Type} → Nat → Fin 0 → Prop) (h : ∀ s, R x s ∧ False) : P := by sorry\n",
        "instance_domain_shift_guarded": "theorem ok (x : Nat) (R : [DecidableEq Nat] → Nat → Fin 0 → Prop) (h : ∀ s, R x s ∧ False) : P := by sorry\n",
        "strict_implicit_shift_guarded": "theorem ok (x : Nat) (R : ⦃α : Type⦄ → Nat → Fin 0 → Prop) (h : ∀ s, R x s ∧ False) : P := by sorry\n",
        "explicit_at_call_guarded": "theorem ok (x : Nat) (R : Nat → Fin 0 → Prop) (h : ∀ s, @R x s ∧ False) : P := by sorry\n",
        "named_arg_call_guarded": "theorem ok (R : Nat → Fin 0 → Prop) (h : ∀ s, R (a := 0) s ∧ False) : P := by sorry\n",
        "optparam_float_not_le": "theorem ok (x : Float := Float.nan) (h : ¬ x ≤ x) : P := by sorry\n",
        "optparam_false_elim": "theorem ok (n : Nat := 0) (h : false = true) : False := by cases h\n",
        "struct_lit_in_binder_intact": "theorem ok (h : ({ a := 1 } : Foo).P) : Q := by sorry\n",
        "let_in_binder_intact": "theorem ok (h : let x := 1; x = 2) : Q := by sorry\n",
        "dep_arrow_empty_false": "theorem ok (h : (x : Empty) → False) : P := by sorry\n",
        "dep_arrow_shadowed_nat_false": "theorem ok (Nat : Prop) (h : (x : Nat) → False) : P := by sorry\n",
        "dep_arrow_iff_not_descended": "theorem ok (P : Prop) (h : (x : Nat) → False ↔ P) : Q := by sorry\n",
        "dep_arrow_nat_false_refutation": "theorem ok (h : (x : Nat) → False) : False := h 0\n",
        "where_pipe_nontrivial": "theorem ok (p q : Prop) (hp : p) (hq : q) : (Nat → p) ∧ q where\n  left\n  | _ => hp\n  right := hq\n",
        "let_multiline_and_opt_param": "theorem ok : let\n  x := 5\n  x + 0 = 5 := by simp\n",
        "let_fn_with_default_arg": "theorem ok : let f (x := 1) := 2\n  f = 2 := by simp\n",
    }

    def setUp(self) -> None:
        proof_health.clear_in_process_caches()

    def test_a3_vacuous_headers_flagged_in_both_scopes(self) -> None:
        rule = audit.RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS
        for label, src in self.VACUOUS_BOTH_SCOPES.items():
            self.assertIn(rule, _rules(audit.scan_lean_text(src)), f"all-scope missed {label}")
            self.assertIn((R7, rule, 1), scan67(src), f"default-scope missed {label}")

    def test_a3_trivial_and_tautological_conclusions_flagged_in_all_scope(self) -> None:
        for label, src in self.TRIVIAL_CONCLUSION_ALL_SCOPE.items():
            self.assertIn(
                audit.RULE_TRIVIAL_CONCLUSION, _rules(audit.scan_lean_text(src)), f"missed {label}"
            )
        for label, src in self.TAUTOLOGY_ALL_SCOPE.items():
            self.assertIn(
                audit.RULE_TAUTOLOGICAL_IMPLICATION, _rules(audit.scan_lean_text(src)), f"missed {label}"
            )

    def test_a3_clean_headers_stay_quiet_in_both_scopes(self) -> None:
        for label, src in self.CLEAN.items():
            self.assertEqual(audit.scan_lean_text(src), [], f"all-scope flagged {label}")
            self.assertEqual(scan67(src), [], f"default-scope flagged {label}")

    def test_a3_header_split_let_where_and_binder_defaults(self) -> None:
        split = proof_health._split_lean_theorem_header
        self.assertEqual(
            split(" : let x := 1 in x = x := rfl\n", 0),
            ([], "let x := 1 in x = x", []),
        )
        self.assertEqual(
            split(" : (let x := 1 in x) = (let x := 1 in x) := rfl\n", 0),
            ([], "(let x := 1 in x) = (let x := 1 in x)", []),
        )
        self.assertEqual(
            split(" : let\tx := 1; x = x := rfl\n", 0),
            ([], "let\tx := 1; x = x", []),
        )
        self.assertEqual(
            split(" : let\n  x := 5\n  x + 0 = 5 := by simp\n", 0),
            ([], "let\n  x := 5\n  x + 0 = 5", []),
        )
        self.assertEqual(
            split(" : let f (x := 1) := 2\n  f = 2 := by simp\n", 0),
            ([], "let f (x := 1) := 2\n  f = 2", []),
        )
        self.assertEqual(
            split(" : do let x ← f; pure x = pure x := rfl\n", 0),
            ([], "do let x ← f; pure x = pure x", []),
        )
        self.assertEqual(
            split(" : (∀ n : Nat, True) ∧ True where\n  left\n  | 0 => trivial\n  right := trivial\n", 0),
            ([], "(∀ n : Nat, True) ∧ True", []),
        )
        self.assertEqual(
            split(" (n : Nat := 0) (h : m.ok = true := by rfl) : P n := by simp\n", 0),
            ([("n", "Nat"), ("h", "m.ok = true")], "P n", []),
        )
        self.assertEqual(
            split(" (h : ({ a := 1 } : Foo).P) : Q := by simp\n", 0),
            ([("h", "({ a := 1 } : Foo).P")], "Q", []),
        )
        self.assertEqual(
            split(" (h : let x := 1; x = 2) : Q := by simp\n", 0),
            ([("h", "let x := 1; x = 2")], "Q", []),
        )

    def test_a3_helper_invariants(self) -> None:
        may_float = proof_health._operand_may_be_float
        none: frozenset[str] = frozenset()
        for yes, fv in (
            ("x", frozenset({"x"})),
            ("Float32.nan", none),
            ("n.toFloat", none),
            ("x.toFloat32", none),
            ("asFloat v", none),
            ("asFloat (x + 1)", none),
            ("1.0 + asFloat v", none),
        ):
            self.assertTrue(may_float(yes, fv), yes)
        for no, fv, nv in (
            ("lenFloat", none, none),
            ("lenFloat + 1", none, none),
            ("f lenFloat", none, none),
            ("lenFloat 0", none, frozenset({"lenFloat"})),
        ):
            self.assertFalse(may_float(no, fv, nv), no)
        self.assertEqual(proof_health._strip_binder_default("Nat := 0"), "Nat")
        self.assertEqual(proof_health._strip_binder_default("({ a := 1 } : S).P"), "({ a := 1 } : S).P")
        self.assertEqual(proof_health._strip_binder_default("let x := 1; x = 2"), "let x := 1; x = 2")
        self.assertEqual(proof_health._first_standalone_use("«s» = 0 ∧ R s", "s"), 12)
        self.assertEqual(
            proof_health._split_dep_arrow_prefix("(x : Nat) → False"),
            ("x", "Nat", " False"),
        )
        self.assertIsNone(proof_health._split_dep_arrow_prefix("{x : Nat // x < 0} → False"))
        self.assertIsNone(proof_health._split_dep_arrow_prefix("(x : Nat) → False ↔ P"))

    def test_check_trusted_agrees_on_every_a3_header(self) -> None:
        ct = _load_check_trusted()
        all_cases = {
            **self.VACUOUS_BOTH_SCOPES,
            **self.TRIVIAL_CONCLUSION_ALL_SCOPE,
            **self.TAUTOLOGY_ALL_SCOPE,
            **self.CLEAN,
        }
        for label, src in all_cases.items():
            for scope in ("all", "annotated", "annotated-only"):
                self.assertEqual(
                    [(f.rule, f.line, f.message) for f in ct.audit_lean_text(src, vacuity_scope=scope)],
                    [(f.rule, f.line, f.message) for f in proof_health.audit_lean_text(src, vacuity_scope=scope)],
                    (scope, label),
                )


if __name__ == "__main__":
    unittest.main()
