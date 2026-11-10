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
from unittest import mock

SERVER_DIR = Path(__file__).resolve().parent
HOOK_PATH = SERVER_DIR.parent / "hooks" / "post_tool_use.py"
REPO_ROOT = SERVER_DIR.parent.parent.parent

if str(SERVER_DIR) not in sys.path:
    sys.path.insert(0, str(SERVER_DIR))

import proof_health  # noqa: E402


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
        findings = proof_health.scan_lean_text(src, scan_siblings=False)
        rules = [(f.rule, f.line, f.symbol) for f in findings]
        self.assertEqual(
            rules,
            [
                (proof_health.RULE_DSIMP_FORBIDDEN_SYM, 2, "wpMirExecSym"),
                (proof_health.RULE_DSIMP_FORBIDDEN_SYM, 5, "Trusted.Sequence.length"),
                (proof_health.RULE_DSIMP_FORBIDDEN_SYM, 7, "Sequence.length"),
                (proof_health.RULE_DSIMP_FORBIDDEN_SYM, 8, "wpMirExecSym"),
            ],
        )

    def test_rule1_negatives(self) -> None:
        src = (
            "theorem ok1 (bs : List Nat) (h : Trusted.Sequence.length bs = 4) : True := by\n"
            "  have h2 := wpMirExecSym\n"
            "  rw [wpMirExecSym_helper]\n"
            "  simp [Trusted.Sequence.length] at h ⊢\n"
            "  trivial\n"
        )
        self.assertEqual(proof_health.scan_lean_text(src, scan_siblings=False), [])

    def test_rule2_dsimp_mir_body_unfold(self) -> None:
        src = (
            "def itemBB0 := Mir.Crate.Item.body[0]!\n"
            "theorem bad2 : True := by\n"
            "  dsimp only [Mir.Crate.Item.body]\n"
            "  simp [foo, Mir.Mod.Sub.fn.body]\n"
            "  unfold Mir.Crate.Item.body\n"
        )
        findings = proof_health.scan_lean_text(src, scan_siblings=False)
        rules = [(f.rule, f.line, f.symbol) for f in findings]
        self.assertEqual(
            rules,
            [
                (proof_health.RULE_DSIMP_MIR_BODY_UNFOLD, 3, "Mir.Crate.Item.body"),
                (proof_health.RULE_DSIMP_MIR_BODY_UNFOLD, 4, "Mir.Mod.Sub.fn.body"),
                (proof_health.RULE_DSIMP_MIR_BODY_UNFOLD, 5, "Mir.Crate.Item.body"),
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
        )
        findings = proof_health.scan_lean_text(src, scan_siblings=False)
        rules = [(f.rule, f.line, f.symbol) for f in findings]
        self.assertEqual(
            rules,
            [
                (proof_health.RULE_RAW_BITWISE_UNFOLD, 5, "bitwiseAndBits"),
                (proof_health.RULE_RAW_BITWISE_UNFOLD, 6, "bitwiseOrBits"),
                (proof_health.RULE_RAW_BITWISE_UNFOLD, 7, "bitwiseAndBits"),
            ],
        )

    def test_rule4_low_profiler_threshold(self) -> None:
        src = (
            "set_option trace.profiler.threshold 100\n"
            "set_option trace.profiler.threshold 50\n"
            "set_option trace.profiler.threshold 49\n"
            "set_option trace.profiler.threshold 1\n"
            "set_option trace.profiler.threshold 0\n"
        )
        findings = proof_health.scan_lean_text(src, scan_siblings=False)
        rules = [(f.rule, f.line, f.symbol) for f in findings]
        self.assertEqual(
            rules,
            [
                (proof_health.RULE_LOW_PROFILER_THRESHOLD, 3, "trace.profiler.threshold=49"),
                (proof_health.RULE_LOW_PROFILER_THRESHOLD, 4, "trace.profiler.threshold=1"),
                (proof_health.RULE_LOW_PROFILER_THRESHOLD, 5, "trace.profiler.threshold=0"),
            ],
        )

    def test_rule5_duplicate_private_lemma_intra_and_sibling(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            sibling = tmp_dir / "Sibling.lean"
            sibling.write_text(
                "private theorem shared_helper (x : Nat) : x + 0 = x := Nat.add_zero x\n"
                "private lemma sig_match (a : Nat) (b : Bool) : a = a := rfl\n",
                encoding="utf-8",
            )
            target = tmp_dir / "Target.lean"
            target_src = (
                "private theorem local_dup (n : Nat) : n = n := rfl\n"
                "private lemma local_dup (n : Nat) : n = n := rfl\n"
                "private theorem alpha_one (u : Nat) : u + 1 = 1 + u := by omega\n"
                "private theorem alpha_two (v : Nat) : v + 1 = 1 + v := by omega\n"
                "private theorem shared_helper (z : Nat) : z = z := rfl\n"
                "private theorem sibling_sig_copy (x : Nat) (y : Bool) : x = x := rfl\n"
            )
            target.write_text(target_src, encoding="utf-8")
            findings = proof_health.scan_lean_file(target, scan_siblings=True)
            dup_lines = [(f.line, f.symbol) for f in findings if f.rule == proof_health.RULE_DUPLICATE_PRIVATE_LEMMA]
            self.assertEqual(
                dup_lines,
                [
                    (2, "local_dup"),
                    (4, "alpha_two"),
                    (5, "shared_helper"),
                    (6, "sibling_sig_copy"),
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
            payload_v1 = {
                "toolCall": {
                    "args": {
                        "Path": str(lean_file),
                        "Target": "  trivial\n",
                        "Replacement": "  dsimp only [foo]\n  trivial\n",
                    }
                }
            }
            fb1 = proof_health.check_post_edit_proof_health(
                lean_file, payload_v1, cache_path=cache_file
            )
            self.assertEqual(fb1, "")

            # 2. Introduce `dsimp [wpMirExecSym]` via Jetski `Target`/`Replacement` -> warning (+1)
            bad_v2 = "theorem t : True := by\n  dsimp only [foo, wpMirExecSym]\n  trivial\n"
            lean_file.write_text(bad_v2, encoding="utf-8")
            payload_v2 = {
                "toolCall": {
                    "args": {
                        "Path": str(lean_file),
                        "Target": "  dsimp only [foo]\n",
                        "Replacement": "  dsimp only [foo, wpMirExecSym]\n",
                    }
                }
            }
            fb2 = proof_health.check_post_edit_proof_health(
                lean_file, payload_v2, cache_path=cache_file
            )
            self.assertIn("[Anneal Proof Health]", fb2)
            self.assertIn("dsimp_forbidden_sym (+1", fb2)
            self.assertIn("L2", fb2)

            # 3. Unrelated edit while `wpMirExecSym` remains -> delta is 0 -> suppressed ("")
            same_v3 = (
                "-- comment added\n"
                "theorem t : True := by\n  dsimp only [foo, wpMirExecSym]\n  trivial\n"
            )
            lean_file.write_text(same_v3, encoding="utf-8")
            payload_v3 = {
                "tool_input": {
                    "file_path": str(lean_file),
                    "old_string": "theorem t : True := by\n",
                    "new_string": "-- comment added\ntheorem t : True := by\n",
                }
            }
            fb3 = proof_health.check_post_edit_proof_health(
                lean_file, payload_v3, cache_path=cache_file
            )
            self.assertEqual(fb3, "")

            # 4. Fix the anti-pattern via Claude `MultiEdit` -> delta is -1 -> suppressed ("")
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
            fb4 = proof_health.check_post_edit_proof_health(
                lean_file, payload_v4, cache_path=cache_file
            )
            self.assertEqual(fb4, "")

            # 5. `write_file` payload (no Target/old_string) uses persisted cache to detect new issue
            bad_v5 = (
                "set_option trace.profiler.threshold 10\n"
                "theorem t : True := by\n  dsimp only [foo]\n  trivial\n"
            )
            lean_file.write_text(bad_v5, encoding="utf-8")
            payload_v5 = {"toolCall": {"args": {"Path": str(lean_file), "Content": bad_v5}}}
            fb5 = proof_health.check_post_edit_proof_health(
                lean_file, payload_v5, cache_path=cache_file
            )
            self.assertIn("low_profiler_threshold (+1", fb5)


class TestPerformanceAndDogfood(unittest.TestCase):
    def test_synthetic_5000_line_file_under_5ms(self) -> None:
        block = (
            "/-- Docstring mentioning dsimp [wpMirExecSym] and Mir.Foo.body -/\n"
            "theorem synthetic_lemma_{i} (a b : Nat) (h : a = b) : a + 0 = b := by\n"
            "  -- single line comment bitwiseAndBits\n"
            "  dsimp only [Nat.add_zero]\n"
            "  exact h\n"
        )
        lines = [block.format(i=i) for i in range(1050)]
        text = "".join(lines)
        self.assertGreaterEqual(text.count("\n"), 5000)

        # Warm-up run and measure best-of-3 to filter OS scheduler preemption jitter
        proof_health.scan_lean_text(text, scan_siblings=False)
        timings_ms: list[float] = []
        findings = []
        for _ in range(3):
            t0 = time.perf_counter()
            findings = proof_health.scan_lean_text(text, scan_siblings=False)
            timings_ms.append((time.perf_counter() - t0) * 1000.0)
        elapsed_ms = min(timings_ms)
        self.assertEqual(findings, [])
        self.assertLess(
            elapsed_ms,
            5.0,
            f"Expected < 5.0 ms on 5,250-line synthetic file, took {elapsed_ms:.2f} ms",
        )

    def test_dogfood_episode1_files_under_5ms_and_zero_findings(self) -> None:
        bit_validity = REPO_ROOT / "theory" / "Anneal" / "BitValidity.lean"
        mir_cast = REPO_ROOT / "theory" / "Anneal" / "Mir" / "Cast.lean"
        for path in (bit_validity, mir_cast):
            self.assertTrue(path.is_file(), f"Missing {path}")
            # Warm-up sibling cache and measure best-of-3
            proof_health.scan_lean_file(path, scan_siblings=True)
            timings_ms: list[float] = []
            findings = []
            for _ in range(3):
                t0 = time.perf_counter()
                findings = proof_health.scan_lean_file(path, scan_siblings=True)
                timings_ms.append((time.perf_counter() - t0) * 1000.0)
            elapsed_ms = min(timings_ms)
            self.assertEqual(
                findings,
                [],
                f"Expected 0 findings on {path.name}, got: {findings}",
            )
            self.assertLess(
                elapsed_ms,
                5.0,
                f"Expected < 5.0 ms on {path.name}, took {elapsed_ms:.2f} ms",
            )


class TestTranscriptLatencyTelemetry(unittest.TestCase):
    def test_compute_unbatched_tool_latencies_events_and_jsonl(self) -> None:
        events = [
            # Standalone unbatched fast LSP calls: 10 ms, 20 ms, 30 ms -> mean=20.0, median=20.0
            {"tool": "lean_goal", "duration_ms": 10.0, "batch_id": "turn_1"},
            {"tool": "lean_hover", "duration_ms": 20.0, "batch_id": "turn_2"},
            {"tool": "lean_goal", "duration_ms": 30.0, "batch_id": "turn_3"},
            # Parallel batch with a long-running `run_command` (4500 ms >= 1000 ms):
            # both calls must be classified as `batched_with_long_call` and excluded from unbatched
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

        # Also test reading from a `.jsonl` transcript file with Jetski `tool_calls` steps
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
            jsonl_path.write_text(
                "\n".join(json.dumps(s) for s in steps) + "\n", encoding="utf-8"
            )
            jstats = proof_health.compute_unbatched_tool_latencies(jsonl_path)
            self.assertEqual(jstats["unbatched_count"], 1)
            self.assertEqual(jstats["batched_with_long_call_count"], 2)
            self.assertAlmostEqual(jstats["unbatched_mean_ms"], 25.0, places=3)


class TestPostToolUseHookIntegration(unittest.TestCase):
    def test_hook_subprocess_offline_and_opt_out(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            cache_file = tmp_dir / "hook-cache.json"
            lean_file = tmp_dir / "OfflineProof.lean"
            lean_file.write_text(
                "theorem t : True := by\n  dsimp [wpMirExecSym]\n  trivial\n",
                encoding="utf-8",
            )
            payload = {
                "result": "Edited OfflineProof.lean",
                "toolCall": {
                    "args": {
                        "Path": str(lean_file),
                        "Target": "  trivial\n",
                        "Replacement": "  dsimp [wpMirExecSym]\n  trivial\n",
                    }
                },
            }
            env = dict(os.environ)
            env.pop("ANNEAL_DISABLE_LSP_HOOK", None)
            env["ANNEAL_PROOF_HEALTH_CACHE"] = str(cache_file)

            proc = subprocess.run(
                [sys.executable, "-B", str(HOOK_PATH)],
                input=json.dumps(payload),
                text=True,
                capture_output=True,
                env=env,
                check=True,
            )
            out = json.loads(proc.stdout.strip())
            self.assertIn("overwriteResult", out)
            self.assertIn("[Anneal Proof Health]", out["overwriteResult"])
            self.assertIn(
                "dsimp_forbidden_sym",
                out["hookSpecificOutput"]["additionalContext"],
            )

            # Second run with unchanged file -> delta is 0 -> `{}`
            proc2 = subprocess.run(
                [sys.executable, "-B", str(HOOK_PATH)],
                input=json.dumps({"toolCall": {"args": {"Path": str(lean_file)}}}),
                text=True,
                capture_output=True,
                env=env,
                check=True,
            )
            self.assertEqual(json.loads(proc2.stdout.strip()), {})

            # Opt-out via ANNEAL_DISABLE_LSP_HOOK=1 -> `{}`
            env["ANNEAL_DISABLE_LSP_HOOK"] = "1"
            proc3 = subprocess.run(
                [sys.executable, "-B", str(HOOK_PATH)],
                input=json.dumps(payload),
                text=True,
                capture_output=True,
                env=env,
                check=True,
            )
            self.assertEqual(json.loads(proc3.stdout.strip()), {})

    def test_hook_subprocess_mocked_combined_lsp_and_proof_health(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            cache_file = tmp_dir / "combined-cache.json"
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
            env = dict(os.environ)
            env.pop("ANNEAL_DISABLE_LSP_HOOK", None)
            env["ANNEAL_PROOF_HEALTH_CACHE"] = str(cache_file)

            runner_code = (
                "import runpy, sys, types\n"
                "m = types.ModuleType('anneal_lsp_daemon')\n"
                "m.resolve_lake_root = lambda p: '/fake/lake'\n"
                "m.daemon_rpc = lambda *a, **k: {'ok': True, 'result': {'feedback': '[Lean LSP] L2: unsolved goals'}}\n"
                "sys.modules['anneal_lsp_daemon'] = m\n"
                f"runpy.run_path({str(HOOK_PATH)!r}, run_name='__main__')\n"
            )
            proc = subprocess.run(
                [sys.executable, "-B", "-c", runner_code],
                input=json.dumps(payload),
                text=True,
                capture_output=True,
                env=env,
                check=True,
            )
            out = json.loads(proc.stdout.strip())
            self.assertIn("[Lean LSP] L2: unsolved goals", out["overwriteResult"])
            self.assertIn("[Anneal Proof Health]", out["overwriteResult"])
            self.assertIn(
                "[Lean LSP] L2: unsolved goals",
                out["hookSpecificOutput"]["additionalContext"],
            )
            self.assertIn(
                "low_profiler_threshold",
                out["hookSpecificOutput"]["additionalContext"],
            )


if __name__ == "__main__":
    unittest.main()
