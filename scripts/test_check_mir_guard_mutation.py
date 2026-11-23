#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Offline unit tests for `scripts/check_mir_guard_mutation.py`.

Exercises all static catalog invariants against the live `V2026_06_01`
`MirSemantics` sources, mutation/span/classification anti-false-kill logic,
`anneal-lean-run` wrapping and `.lake/build/lib/lean` cache freshness checks,
end-to-end synthetic CLI execution with a deterministic fast POSIX-shell fake
`lean` binary (< 2s offline), and guaranteed `TemporaryDirectory` cleanup +
zero-`mkdtemp` AST hygiene.
"""

from __future__ import annotations

import ast
import dataclasses
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest
from unittest import mock

sys.dont_write_bytecode = True

SCRIPTS_DIR = Path(__file__).resolve().parent
ANNEAL_ROOT = SCRIPTS_DIR.parent
SCRIPT = SCRIPTS_DIR / "check_mir_guard_mutation.py"
TEST_SCRIPT = Path(__file__).resolve()

if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

import check_mir_guard_mutation as gmut  # noqa: E402


MIR_SEMANTICS_FILES: tuple[Path, ...] = (
    ANNEAL_ROOT / "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean",
    ANNEAL_ROOT / "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean",
    ANNEAL_ROOT / "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean",
    ANNEAL_ROOT / "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean",
)


def _write_fake_lean_sh(bin_path: Path, body_sh: str) -> None:
    """Create a fast executable POSIX-shell fake `lean` binary (~1ms/call).

    Pre-parses `-o <out>` into `$OUT` and the trailing source path into `$SRC`
    (with `$BASENAME`), and sets `$IS_MUTANT=1` when `LEAN_PATH` points into a
    per-mutant temp dir rather than `anneal-gmut-base-`.
    """
    script = (
        "#!/bin/sh\n"
        "set -eu\n"
        'OUT=""\n'
        'SRC=""\n'
        'while [ "$#" -gt 0 ]; do\n'
        '  if [ "$1" = "-o" ]; then\n'
        '    OUT="$2"\n'
        "    shift 2\n"
        '  elif [ "$1" = "-R" ]; then\n'
        "    shift 2\n"
        "  else\n"
        '    SRC="$1"\n'
        "    shift\n"
        "  fi\n"
        "done\n"
        'BASENAME="${SRC##*/}"\n'
        'IS_MUTANT=0\n'
        'case "${LEAN_PATH:-}" in\n'
        "  *anneal-gmut-base-*) IS_MUTANT=0 ;;\n"
        "  *anneal-gmut-*) IS_MUTANT=1 ;;\n"
        "esac\n"
        f"{body_sh}\n"
    )
    bin_path.write_text(script, encoding="utf-8")
    bin_path.chmod(bin_path.stat().st_mode | stat.S_IXUSR)


def _snapshot_mir_hashes() -> dict[str, str]:
    return {
        str(p): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in MIR_SEMANTICS_FILES
    }


def _list_gmut_temp_dirs(base_tmp: Path | None = None) -> set[str]:
    root = base_tmp if base_tmp is not None else Path(tempfile.gettempdir())
    if not root.is_dir():
        return set()
    return {p.name for p in root.iterdir() if p.name.startswith("anneal-gmut-")}


class GuardMutationUnitTests(unittest.TestCase):
    def test_live_catalog_static_invariants_and_cli_list(self) -> None:
        errors = gmut.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertEqual(errors, [], f"catalog invariant errors: {errors}")

        # Coverage requirements: >= 10 guards (>= 8 hard floor), all 4 files,
        # and >= 3 --quick guards spanning Scalars, Statements, Terminators.
        self.assertGreaterEqual(len(gmut.MIR_SEMANTICS_GUARDS), 10)
        covered_files = {g.target_file for g in gmut.MIR_SEMANTICS_GUARDS}
        for rel in (
            "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean",
            "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean",
            "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean",
            "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean",
        ):
            self.assertIn(rel, covered_files)

        quick_guards = gmut.select_guards(quick=True)
        self.assertGreaterEqual(len(quick_guards), 3)
        quick_files = {g.target_file for g in quick_guards}
        self.assertIn(
            "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean",
            quick_files,
        )
        self.assertIn(
            "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean",
            quick_files,
        )
        self.assertIn(
            "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean",
            quick_files,
        )

        # CLI --list (text mode)
        res = subprocess.run(
            [sys.executable, "-B", str(SCRIPT), "--list"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertIn(
            f"Total cataloged guards: {len(gmut.MIR_SEMANTICS_GUARDS)}",
            res.stdout,
        )

        # CLI --list --json
        res_json = subprocess.run(
            [sys.executable, "-B", str(SCRIPT), "--list", "--json"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(res_json.returncode, 0, res_json.stderr)
        parsed = json.loads(res_json.stdout)
        self.assertEqual(parsed["total"], len(gmut.MIR_SEMANTICS_GUARDS))
        self.assertEqual(len(parsed["guards"]), len(gmut.MIR_SEMANTICS_GUARDS))

        # CLI --list --quick
        res_quick = subprocess.run(
            [sys.executable, "-B", str(SCRIPT), "--list", "--quick"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(res_quick.returncode, 0, res_quick.stderr)
        self.assertIn(
            f"Total cataloged guards: {len(quick_guards)}", res_quick.stdout
        )

        # Repeatable --guard selection works and preserves catalog order.
        multi = gmut.select_guards(guard_filters=["shift_oob", "div_by_zero"])
        self.assertEqual([g.guard_id for g in multi], ["div_by_zero", "shift_oob"])

        # Unknown --guard fails closed.
        res_bad = subprocess.run(
            [
                sys.executable,
                "-B",
                str(SCRIPT),
                "--list",
                "--guard",
                "nonexistent_guard_id_xyz",
            ],
            capture_output=True,
            text=True,
        )
        self.assertNotEqual(res_bad.returncode, 0)
        self.assertIn("no cataloged guard matched", res_bad.stderr)

        # Conflicting CLI mode flags fail closed.
        for bad_flags in (
            ["--quick", "--all"],
            ["--quick", "--guard", "div_by_zero"],
            ["--all", "--guard", "div_by_zero"],
        ):
            res_conflict = subprocess.run(
                [sys.executable, "-B", str(SCRIPT), *bad_flags],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(res_conflict.returncode, 0, bad_flags)

    def test_apply_single_guard_mutation_requires_exact_unique_match(self) -> None:
        src = "alpha\nbeta\ngamma\n"
        mutated = gmut.apply_single_guard_mutation(
            src, "beta", "BETA", guard_id="g1"
        )
        self.assertEqual(mutated, "alpha\nBETA\ngamma\n")

        with self.assertRaisesRegex(ValueError, "found 0 occurrences"):
            gmut.apply_single_guard_mutation(
                src, "missing", "x", guard_id="g0"
            )
        with self.assertRaisesRegex(ValueError, "found 2 occurrences"):
            gmut.apply_single_guard_mutation(
                "dup\ndup\n", "dup", "x", guard_id="g2"
            )
        with self.assertRaisesRegex(ValueError, "must differ"):
            gmut.apply_single_guard_mutation(
                src, "beta", "beta", guard_id="g_same"
            )

    def test_find_theorem_line_span(self) -> None:
        fixture = textwrap.dedent(
            """\
            namespace Test

            def helper : Nat := 1

            theorem first_thm : True :=
              trivial

            private def helper2 : Nat := 2

            theorem second_thm :
                True := by
              trivial

            end Test
            """
        )
        # Spans cover the header and its indented continuation lines only;
        # trailing blank lines are excluded.
        self.assertEqual(
            gmut.find_theorem_line_span(fixture, "first_thm"),
            (5, 6),
        )
        self.assertEqual(
            gmut.find_theorem_line_span(fixture, "second_thm"),
            (10, 12),
        )
        with self.assertRaisesRegex(ValueError, "not found"):
            gmut.find_theorem_line_span(fixture, "missing_thm")

    def test_classify_refutation_failure_anti_false_kill_matrix(self) -> None:
        # 1. Surviving mutant (rc=0) -> SURVIVED.
        status, _ = gmut.classify_refutation_failure(
            0, "", "Refute_div_by_zero.lean", (7, 10)
        )
        self.assertEqual(status, "SURVIVED")

        # 2. Genuine proof failure inside theorem span -> KILLED.
        good_err = (
            "/tmp/fixtures/Refute_div_by_zero.lean:9:2: error: Type mismatch\n"
            "  rfl\nhas type\n  ?m.1 = ?m.1\n"
        )
        status, _ = gmut.classify_refutation_failure(
            1, good_err, "Refute_div_by_zero.lean", (7, 10)
        )
        self.assertEqual(status, "KILLED")

        # 3. Error outside target theorem span -> ERROR.
        wrong_line_err = (
            "/tmp/fixtures/Refute_div_by_zero.lean:3:0: error: Type mismatch\n"
            "  rfl\nhas type\n  False\n"
        )
        status, _ = gmut.classify_refutation_failure(
            1, wrong_line_err, "Refute_div_by_zero.lean", (7, 10)
        )
        self.assertEqual(status, "ERROR")

        # 4. Mixed error lines (one outside + one inside span) -> ERROR.
        mixed_err = (
            "/tmp/fixtures/Refute_div_by_zero.lean:4:0: error: Type mismatch\n"
            "/tmp/fixtures/Refute_div_by_zero.lean:9:2: error: Type mismatch\n"
        )
        status, _ = gmut.classify_refutation_failure(
            1, mixed_err, "Refute_div_by_zero.lean", (7, 10)
        )
        self.assertEqual(status, "ERROR")

        # 5. Filename suffix spoofing must NOT match `Refute_div_by_zero.lean`.
        spoofed_err = (
            "/tmp/fixtures/OtherRefute_div_by_zero.lean:9:2: error: Type mismatch\n"
            "  rfl\n"
        )
        status, _ = gmut.classify_refutation_failure(
            1, spoofed_err, "Refute_div_by_zero.lean", (7, 10)
        )
        self.assertEqual(status, "ERROR")

        # 6. Missing proof-failure marker -> ERROR.
        unrecognized_err = (
            "/tmp/fixtures/Refute_div_by_zero.lean:9:2: error: bizarre glitch\n"
        )
        status, _ = gmut.classify_refutation_failure(
            1, unrecognized_err, "Refute_div_by_zero.lean", (7, 10)
        )
        self.assertEqual(status, "ERROR")

        # 7. Every NON_KILL_ERROR_MARKERS blocks a kill even with Type mismatch.
        for marker in gmut.NON_KILL_ERROR_MARKERS:
            bad_out = (
                "/tmp/fixtures/Refute_div_by_zero.lean:9:2: error: Type mismatch\n"
                f"{marker}\n"
            )
            status, detail = gmut.classify_refutation_failure(
                1, bad_out, "Refute_div_by_zero.lean", (7, 10)
            )
            self.assertEqual(status, "ERROR", f"marker={marker!r} detail={detail}")

        # 8. Signal / OOM / timeout / usage exit codes -> ERROR.
        for bad_rc in (-9, 2, 124, 137):
            status, _ = gmut.classify_refutation_failure(
                bad_rc, good_err, "Refute_div_by_zero.lean", (7, 10)
            )
            self.assertEqual(status, "ERROR", f"rc={bad_rc}")

    def test_build_lean_command_uses_anneal_lean_run_without_concurrency(self) -> None:
        wrapper = Path("/usr/local/bin/anneal-lean-run")
        lean_bin = Path("/home/user/.elan/bin/lean")
        cmd_wrapped = gmut._build_lean_command(
            lean_bin, ["-o", "out.olean", "in.lean"], lean_run_wrapper=wrapper
        )
        self.assertEqual(
            cmd_wrapped,
            [
                "/usr/local/bin/anneal-lean-run",
                "--mode",
                "file",
                "--",
                "/home/user/.elan/bin/lean",
                "-o",
                "out.olean",
                "in.lean",
            ],
        )
        self.assertNotIn("--concurrency", cmd_wrapped)
        self.assertNotIn("-W", cmd_wrapped)

        cmd_direct = gmut._build_lean_command(
            lean_bin, ["-o", "out.olean", "in.lean"], lean_run_wrapper=None
        )
        self.assertEqual(
            cmd_direct,
            ["/home/user/.elan/bin/lean", "-o", "out.olean", "in.lean"],
        )

    def test_can_reuse_lake_oleans_freshness_and_transitive_staleness(self) -> None:
        modules = (
            *gmut.BASE_TRUSTED_MODULES,
            "Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-cache-test-") as tmp:
            root = Path(tmp)
            self.assertFalse(gmut._can_reuse_lake_oleans(root, modules))

            for mod in modules:
                src = root / "trusted/lean" / f"{mod}.lean"
                src.parent.mkdir(parents=True, exist_ok=True)
                src.write_text("-- dummy\n", encoding="utf-8")
                os.utime(src, (1000.0, 1000.0))

                olean = root / ".lake/build/lib/lean" / f"{mod}.olean"
                olean.parent.mkdir(parents=True, exist_ok=True)
                olean.write_bytes(b"olean")
                os.utime(olean, (2000.0, 2000.0))

            self.assertTrue(gmut._can_reuse_lake_oleans(root, modules))

            # Direct source newer than `.olean` -> False.
            scalars_src = (
                root
                / "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean"
            )
            os.utime(scalars_src, (3000.0, 3000.0))
            self.assertFalse(gmut._can_reuse_lake_oleans(root, modules))
            os.utime(scalars_src, (1000.0, 1000.0))
            self.assertTrue(gmut._can_reuse_lake_oleans(root, modules))

            # Transitive upstream dependency (`State.lean`) newer than `Scalars.olean` -> False.
            state_src = (
                root
                / "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/State.lean"
            )
            state_olean = (
                root
                / ".lake/build/lib/lean/Trusted/Rustc/V2026_06_01/MirSemantics/State.olean"
            )
            os.utime(state_src, (2500.0, 2500.0))
            os.utime(state_olean, (2600.0, 2600.0))
            self.assertFalse(gmut._can_reuse_lake_oleans(root, modules))

    def test_run_lean_timeout_returns_124_error(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-timeout-") as tmp:
            slow_lean = Path(tmp) / "slow_lean"
            _write_fake_lean_sh(slow_lean, "sleep 5")
            res = gmut._run_lean(
                slow_lean,
                ["dummy.lean"],
                anneal_root=ANNEAL_ROOT,
                lean_path=[],
                timeout_sec=1,
                lean_run_wrapper=None,
            )
            self.assertEqual(res.returncode, 124)
            self.assertIn("timed out", res.stderr)
            status, _ = gmut.classify_refutation_failure(
                res.returncode, res.stderr, "Refute_div_by_zero.lean", (7, 10)
            )
            self.assertEqual(status, "ERROR")

    def _run_synthetic_cli(
        self,
        fake_lean_sh: str,
        extra_args: list[str],
        *,
        emit_json_out: bool = True,
    ) -> tuple[
        int,
        str,
        str,
        dict[str, object] | None,
        dict[str, str],
        dict[str, str],
    ]:
        """Run `check_mir_guard_mutation.py` from `/tmp` with a fake `lean`."""
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            tmp_path = Path(tmp)
            fake_lean = tmp_path / "fake_lean"
            _write_fake_lean_sh(fake_lean, fake_lean_sh)
            json_out = tmp_path / "report.json"

            before_hashes = _snapshot_mir_hashes()
            cmd = [
                sys.executable,
                "-B",
                str(SCRIPT),
                "--anneal-root",
                str(ANNEAL_ROOT),
                "--lean",
                str(fake_lean),
                "--no-lake-cache",
                "--jobs",
                "2",
                *extra_args,
            ]
            if emit_json_out:
                cmd.extend(["--json-out", str(json_out)])

            # Deliberately invoke from `/tmp` to verify `_run_lean` always
            # overrides `cwd=str(anneal_root)` for `elan` toolchain selection.
            res = subprocess.run(
                cmd,
                cwd=str(tmp_path),
                capture_output=True,
                text=True,
            )
            after_hashes = _snapshot_mir_hashes()
            parsed = (
                json.loads(json_out.read_text(encoding="utf-8"))
                if emit_json_out and json_out.is_file()
                else None
            )
            return (
                res.returncode,
                res.stdout,
                res.stderr,
                parsed,
                before_hashes,
                after_hashes,
            )

    def test_synthetic_clean_kill_json_and_untouched_tree(self) -> None:
        guard = gmut.select_guards(guard_filters=["div_by_zero"])[0]
        span = gmut.find_theorem_line_span(guard.refute_source, guard.theorem_name)
        expected_cwd = str(ANNEAL_ROOT.resolve())
        fake_sh = textwrap.dedent(
            f"""\
            if [ "$(pwd -P)" != "{expected_cwd}" ]; then
              echo "wrong cwd: $(pwd -P)" >&2
              exit 2
            fi
            if [ -n "$OUT" ]; then
              mkdir -p "$(dirname "$OUT")"
              printf 'fake-olean' > "$OUT"
            fi
            if [ "$IS_MUTANT" = "1" ]; then
              case "$BASENAME" in
                Places.lean|Statements.lean|Terminators.lean)
                  echo "unexpected downstream rebuild: $BASENAME" >&2
                  exit 2
                  ;;
                Refute_div_by_zero.lean)
                  printf '%s:{span[0]}:2: error: Type mismatch\\n  rfl\\n' "$SRC"
                  exit 1
                  ;;
              esac
            fi
            exit 0
            """
        )
        rc, out, err, report_file, before, after = self._run_synthetic_cli(
            fake_sh,
            ["--guard", "div_by_zero", "--json"],
            emit_json_out=True,
        )
        self.assertEqual(rc, 0, out + err)
        self.assertEqual(before, after)
        report_stdout = json.loads(out)
        self.assertEqual(report_stdout, report_file)
        assert report_file is not None
        self.assertEqual(report_file["mode"], "guard")
        self.assertEqual(report_file["total"], 1)
        self.assertEqual(report_file["killed"], 1)
        self.assertEqual(report_file["survived"], 0)
        self.assertEqual(report_file["errors"], 0)
        self.assertEqual(report_file["kill_rate_pct"], 100.0)

    def test_synthetic_quick_and_all_suites_kill_all_guards(self) -> None:
        case_arms: list[str] = []
        for g in gmut.MIR_SEMANTICS_GUARDS:
            line_no = gmut.find_theorem_line_span(
                g.refute_source, g.theorem_name
            )[0]
            case_arms.append(
                f'    {g.refute_module}.lean)\n'
                f'      printf \'%s:{line_no}:2: error: Type mismatch\\n  rfl\\n\' "$SRC"\n'
                f"      exit 1\n"
                f"      ;;"
            )
        fake_sh = (
            'if [ -n "$OUT" ]; then\n'
            '  mkdir -p "$(dirname "$OUT")"\n'
            "  printf 'fake-olean' > \"$OUT\"\n"
            "fi\n"
            'if [ "$IS_MUTANT" = "1" ]; then\n'
            '  case "$BASENAME" in\n'
            + "\n".join(case_arms)
            + "\n  esac\nfi\nexit 0\n"
        )

        # --quick
        quick_guards = gmut.select_guards(quick=True)
        rc, out, err, report_q, before, after = self._run_synthetic_cli(
            fake_sh, ["--quick", "--json"]
        )
        self.assertEqual(rc, 0, out + err)
        self.assertEqual(before, after)
        assert report_q is not None
        self.assertEqual(report_q["mode"], "quick")
        self.assertEqual(report_q["total"], len(quick_guards))
        self.assertEqual(report_q["killed"], len(quick_guards))
        self.assertEqual(report_q["survived"], 0)
        self.assertEqual(report_q["errors"], 0)

        # --all
        rc_all, out_all, err_all, report_all, before2, after2 = (
            self._run_synthetic_cli(fake_sh, ["--all", "--json"])
        )
        self.assertEqual(rc_all, 0, out_all + err_all)
        self.assertEqual(before2, after2)
        assert report_all is not None
        self.assertEqual(report_all["mode"], "all")
        self.assertEqual(report_all["total"], len(gmut.MIR_SEMANTICS_GUARDS))
        self.assertEqual(report_all["killed"], len(gmut.MIR_SEMANTICS_GUARDS))
        self.assertEqual(report_all["survived"], 0)
        self.assertEqual(report_all["errors"], 0)

    def test_synthetic_fails_closed_on_surviving_mutant(self) -> None:
        survive_sh = textwrap.dedent(
            """\
            if [ -n "$OUT" ]; then
              mkdir -p "$(dirname "$OUT")"
              printf 'fake-olean' > "$OUT"
            fi
            exit 0
            """
        )
        rc, out, err, report, before, after = self._run_synthetic_cli(
            survive_sh, ["--guard", "div_by_zero"]
        )
        self.assertEqual(rc, 1, out + err)
        self.assertEqual(before, after)
        assert report is not None
        self.assertEqual(report["survived"], 1)
        self.assertEqual(report["killed"], 0)
        self.assertEqual(report["errors"], 0)

    def test_synthetic_fails_closed_on_mutated_tcb_compile_error(self) -> None:
        broken_tcb_sh = textwrap.dedent(
            """\
            if [ "$IS_MUTANT" = "1" ] && [ "$BASENAME" = "Scalars.lean" ]; then
              echo "syntax error in mutated Scalars.lean" >&2
              exit 1
            fi
            if [ -n "$OUT" ]; then
              mkdir -p "$(dirname "$OUT")"
              printf 'fake-olean' > "$OUT"
            fi
            exit 0
            """
        )
        rc, out, err, report, before, after = self._run_synthetic_cli(
            broken_tcb_sh, ["--guard", "div_by_zero"]
        )
        self.assertEqual(rc, 1, out + err)
        self.assertEqual(before, after)
        assert report is not None
        self.assertEqual(report["errors"], 1)
        self.assertEqual(report["killed"], 0)
        self.assertEqual(report["survived"], 0)

    def test_synthetic_fails_closed_on_mutated_positive_sanity_failure(self) -> None:
        broken_sanity_sh = textwrap.dedent(
            """\
            if [ "$IS_MUTANT" = "1" ] && [ "$BASENAME" = "PositiveSanity_div_by_zero.lean" ]; then
              printf '%s:7:2: error: Type mismatch\\n' "$SRC" >&2
              exit 1
            fi
            if [ -n "$OUT" ]; then
              mkdir -p "$(dirname "$OUT")"
              printf 'fake-olean' > "$OUT"
            fi
            exit 0
            """
        )
        rc, out, err, report, before, after = self._run_synthetic_cli(
            broken_sanity_sh, ["--guard", "div_by_zero"]
        )
        self.assertEqual(rc, 1, out + err)
        self.assertEqual(before, after)
        assert report is not None
        self.assertEqual(report["errors"], 1)
        self.assertEqual(report["killed"], 0)

        # Even rc=0 with `declaration uses 'sorry'` on sanity must be ERROR.
        sorry_sanity_sh = textwrap.dedent(
            """\
            if [ -n "$OUT" ]; then
              mkdir -p "$(dirname "$OUT")"
              printf 'fake-olean' > "$OUT"
            fi
            if [ "$IS_MUTANT" = "1" ] && [ "$BASENAME" = "PositiveSanity_div_by_zero.lean" ]; then
              echo "warning: declaration uses 'sorry'" >&2
            fi
            exit 0
            """
        )
        rc2, out2, err2, report2, _, _ = self._run_synthetic_cli(
            sorry_sanity_sh, ["--guard", "div_by_zero"]
        )
        self.assertEqual(rc2, 1, out2 + err2)
        assert report2 is not None
        self.assertEqual(report2["errors"], 1)
        self.assertEqual(report2["killed"], 0)

    def test_synthetic_fails_closed_on_baseline_sorry_warning(self) -> None:
        baseline_sorry_sh = textwrap.dedent(
            """\
            if [ -n "$OUT" ]; then
              mkdir -p "$(dirname "$OUT")"
              printf 'fake-olean' > "$OUT"
            fi
            if [ "$BASENAME" = "Refute_div_by_zero.lean" ]; then
              echo "warning: declaration uses 'sorry'" >&2
            fi
            exit 0
            """
        )
        rc, out, err, report, _, _ = self._run_synthetic_cli(
            baseline_sorry_sh, ["--guard", "div_by_zero"]
        )
        self.assertEqual(rc, 1, out + err)
        self.assertIn("baseline refute fixture", err)
        # A fatal run still writes `--json-out`, so a stale green report from
        # an earlier run can never be mistaken for this one.
        assert report is not None
        self.assertIn("baseline refute fixture", report["fatal_error"])
        self.assertEqual(report["killed"], 0)
        self.assertEqual(report["total"], 0)
        self.assertEqual(report["errors"], 1)

    def test_temporary_directory_cleanup_on_exception_and_no_mkdtemp_calls(self) -> None:
        # 1. Verify neither script invokes bare `tempfile.mkdtemp()` (AST check).
        for script_path in (SCRIPT, TEST_SCRIPT):
            tree = ast.parse(
                script_path.read_text(encoding="utf-8"), filename=str(script_path)
            )
            for node in ast.walk(tree):
                if isinstance(node, ast.Call):
                    func = node.func
                    if isinstance(func, ast.Attribute) and func.attr == "mkdtemp":
                        self.fail(
                            f"forbidden mkdtemp() call found in {script_path}:{node.lineno}"
                        )
                    if isinstance(func, ast.Name) and func.id == "mkdtemp":
                        self.fail(
                            f"forbidden mkdtemp() call found in {script_path}:{node.lineno}"
                        )

        # 2. Inject an exception mid-run inside an isolated TMPDIR and confirm
        # zero `anneal-gmut-*` temporary directories leak after unwind.
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-leakcheck-") as isolated_tmp:
            isolated_tmp_path = Path(isolated_tmp)
            fake_lean = isolated_tmp_path / "fake_lean"
            _write_fake_lean_sh(fake_lean, "exit 0")

            call_count = 0

            def _exploding_compile(*args: object, **kwargs: object) -> subprocess.CompletedProcess[str]:
                nonlocal call_count
                call_count += 1
                if call_count >= 2:
                    raise RuntimeError("injected mid-run compilation crash")
                out_dir = args[3]
                mod = args[2]
                assert isinstance(out_dir, Path) and isinstance(mod, str)
                olean = out_dir / f"{mod}.olean"
                olean.parent.mkdir(parents=True, exist_ok=True)
                olean.write_bytes(b"fake")
                return subprocess.CompletedProcess(
                    args=["fake"], returncode=0, stdout="", stderr=""
                )

            with (
                mock.patch.dict(os.environ, {"TMPDIR": str(isolated_tmp_path)}),
                mock.patch.object(tempfile, "tempdir", str(isolated_tmp_path)),
                mock.patch.object(gmut, "_compile_module", side_effect=_exploding_compile),
            ):
                with self.assertRaisesRegex(
                    RuntimeError, "injected mid-run compilation crash"
                ):
                    gmut.run_guard_mutation_suite(
                        anneal_root=ANNEAL_ROOT,
                        lean_bin=fake_lean,
                        guard_filters=["div_by_zero"],
                        jobs=1,
                        reuse_lake_cache=False,
                    )

            leaked = _list_gmut_temp_dirs(isolated_tmp_path)
            self.assertEqual(leaked, set(), f"leaked temp dirs after exception: {leaked}")

        # 3. Also verify exception inside `_check_one_mir_guard` itself cleans up
        # the per-mutant `TemporaryDirectory`.
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-mutantleak-") as isolated_tmp:
            isolated_tmp_path = Path(isolated_tmp)
            base_olean_dir = isolated_tmp_path / "base_olean"
            base_olean_dir.mkdir()
            fake_lean = isolated_tmp_path / "fake_lean"
            _write_fake_lean_sh(fake_lean, "exit 0")
            guard = gmut.select_guards(guard_filters=["div_by_zero"])[0]
            baseline_mods = gmut._baseline_modules_for_guards([guard])
            for mod in baseline_mods:
                p = base_olean_dir / f"{mod}.olean"
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes(b"base")

            with (
                mock.patch.dict(os.environ, {"TMPDIR": str(isolated_tmp_path)}),
                mock.patch.object(tempfile, "tempdir", str(isolated_tmp_path)),
                mock.patch.object(
                    gmut,
                    "_compile_module",
                    side_effect=RuntimeError("mutant crash"),
                ),
            ):
                with self.assertRaisesRegex(RuntimeError, "mutant crash"):
                    gmut._check_one_mir_guard(
                        guard,
                        anneal_root=ANNEAL_ROOT,
                        lean_bin=fake_lean,
                        base_olean_dir=base_olean_dir,
                        baseline_modules=baseline_mods,
                        timeout_sec=30,
                        lean_run_wrapper=None,
                    )

            leaked_mut = _list_gmut_temp_dirs(isolated_tmp_path)
            self.assertEqual(
                leaked_mut, set(), f"leaked mutant temp dirs: {leaked_mut}"
            )


# ----------------------------------------------------------------------
# Round B1 adversarial regression tests
# ----------------------------------------------------------------------

ALL_TCB_MODULES: tuple[str, ...] = (
    *gmut.BASE_TRUSTED_MODULES,
    *gmut.SEMANTICS_MODULES,
)

# Fake `lean` that kills every refutation on a mutant and, like the real
# compiler, writes its `-o` output IN PLACE (shell `>` truncates the existing
# inode), which is exactly what would corrupt a hardlinked `.olean`.
KILL_ALL_FAKE_SH = textwrap.dedent(
    """\
    if [ ! -f "$SRC" ]; then
      echo "source not found from $(pwd): $SRC" >&2
      exit 2
    fi
    if [ -n "$OUT" ]; then
      mkdir -p "$(dirname "$OUT")"
      printf 'fake-olean:%s' "$BASENAME" > "$OUT"
    fi
    if [ "$IS_MUTANT" = "1" ]; then
      case "$BASENAME" in
        Refute_*)
          LINE="$(grep -n '^theorem ' "$SRC" | head -n 1 | cut -d: -f1)"
          printf '%s:%s:2: error: Type mismatch\\n  rfl\\n' "$SRC" "$LINE"
          exit 1
          ;;
      esac
    fi
    exit 0
    """
)


def _run_cli(
    args: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    full_env = os.environ.copy()
    if env:
        full_env.update(env)
    return subprocess.run(
        [sys.executable, "-B", str(SCRIPT), *args],
        cwd=str(cwd) if cwd is not None else None,
        env=full_env,
        capture_output=True,
        text=True,
    )


def _make_tcb_copy_root(tmp: Path) -> Path:
    """Copy the live TCB sources into an isolated fake repository root."""
    root = tmp / "root"
    for mod in ALL_TCB_MODULES:
        dst = root / "trusted/lean" / f"{mod}.lean"
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ANNEAL_ROOT / "trusted/lean" / f"{mod}.lean", dst)
    shutil.copyfile(ANNEAL_ROOT / "lean-toolchain", root / "lean-toolchain")
    return root


def _write_lake_build(
    root: Path,
    modules: tuple[str, ...],
    *,
    traces: bool = True,
    base_time: int = 2_000_000_000,
) -> None:
    """Write a fake `.lake/build/lib/lean` tree shaped like Lake's own output.

    Traces record the source path of ANOTHER checkout, as they do when a
    `.lake` directory is hardlinked into a fresh `git worktree`.
    """
    lib = root / ".lake/build/lib/lean"
    version = gmut._read_lean_toolchain_version(root)
    olean_hashes: dict[str, str] = {}
    for idx, mod in enumerate(modules):
        stamp = base_time + idx * 10
        olean = lib / f"{mod}.olean"
        olean.parent.mkdir(parents=True, exist_ok=True)
        olean.write_bytes(f"olean:{mod}".encode())
        os.utime(olean, (stamp, stamp))
        if not traces:
            continue
        olean_hash = gmut.lake_hash_of_bytes(olean.read_bytes())
        olean_hashes[mod] = olean_hash
        hash_path = lib / f"{mod}.olean.hash"
        hash_path.write_text(olean_hash, encoding="utf-8")
        os.utime(hash_path, (stamp + 1, stamp + 1))
        src_bytes = (root / "trusted/lean" / f"{mod}.lean").read_bytes()
        imports = gmut._extract_trusted_imports(src_bytes.decode("utf-8"))
        imports_node: object = [
            [
                f"{imp.replace('/', '.')}:importAllArts",
                gmut.lake_import_arts_hash(olean_hashes[imp]),
            ]
            for imp in imports
        ] or "00000000000006bb"
        trace = {
            "synthetic": False,
            "schemaVersion": "2025-09-10",
            "outputs": {"o": [f"{olean_hash}.olean"], "m": False},
            "log": [],
            "inputs": [
                ["deps", [["imports", imports_node]]],
                [f"Lean {version}, commit 0123456789abcdef", "0" * 16],
                [
                    f"/elsewhere/other-worktree/trusted/lean/{mod}.lean",
                    gmut.lake_hash_of_text(src_bytes),
                ],
                ["options", "00000000000006bb"],
            ],
            "depHash": "0" * 16,
        }
        trace_path = lib / f"{mod}.trace"
        trace_path.write_text(json.dumps(trace), encoding="utf-8")
        os.utime(trace_path, (stamp + 2, stamp + 2))


def _make_tiny_lake_root(tmp: Path) -> tuple[Path, tuple[str, ...]]:
    """Three-module fake repo (`A`; `B` imports `A`; `C` imports `A`, `B`)."""
    root = tmp / "tiny"
    sources = {
        "Trusted/A": "def a : Nat := 1\n",
        "Trusted/B": "import Trusted.A\ndef b : Nat := a\n",
        "Trusted/C": "import Trusted.A\nimport Trusted.B\ndef c : Nat := b\n",
    }
    for mod, text in sources.items():
        src = root / "trusted/lean" / f"{mod}.lean"
        src.parent.mkdir(parents=True, exist_ok=True)
        src.write_text(text, encoding="utf-8")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n", encoding="utf-8")
    modules = tuple(sources)
    _write_lake_build(root, modules)
    return root, modules


def _replace_guard(guard_id: str, **changes: object) -> tuple[gmut.MirSemanticsGuard, ...]:
    return tuple(
        dataclasses.replace(g, **changes) if g.guard_id == guard_id else g
        for g in gmut.MIR_SEMANTICS_GUARDS
    )


class GuardMutationB1AdversarialTests(unittest.TestCase):
    FIXTURE = "Refute_div_by_zero.lean"
    SPAN = (7, 9)

    def _classify(self, rc: int, out: str) -> str:
        return gmut.classify_refutation_failure(rc, out, self.FIXTURE, self.SPAN)[0]

    # -- sorry detection ------------------------------------------------

    def test_sorry_warning_detected_in_every_quoting_style(self) -> None:
        # Lean v4.34.1 (the pinned toolchain) prints backticks, not quotes.
        for text in (
            "X.lean:3:8: warning: declaration uses `sorry`",
            "X.lean:3:8: warning: declaration uses 'sorry'",
            "warning: declaration uses `sorryAx`",
        ):
            self.assertTrue(gmut._has_sorry_warning(text), text)
        self.assertFalse(gmut._has_sorry_warning("X.lean:3:8: warning: unused variable"))
        self.assertFalse(gmut._has_sorry_warning(""))

    def test_synthetic_backtick_sorry_on_mutant_sanity_is_error(self) -> None:
        fake_sh = textwrap.dedent(
            """\
            if [ -n "$OUT" ]; then
              mkdir -p "$(dirname "$OUT")"
              printf 'fake-olean' > "$OUT"
            fi
            if [ "$IS_MUTANT" = "1" ] && [ "$BASENAME" = "PositiveSanity_div_by_zero.lean" ]; then
              printf '%s:7:8: warning: declaration uses `sorry`\\n' "$SRC"
            fi
            exit 0
            """
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            fake = Path(tmp) / "fake_lean"
            _write_fake_lean_sh(fake, fake_sh)
            res = _run_cli(
                ["--lean", str(fake), "--no-lake-cache", "--guard", "div_by_zero", "--json"]
            )
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        report = json.loads(res.stdout)
        self.assertEqual(report["errors"], 1)
        self.assertEqual(report["killed"], 0)
        self.assertIn("positive sanity", report["results"][0]["detail"])

    # -- refutation classification -------------------------------------

    def test_classify_named_error_outside_span_is_not_missed(self) -> None:
        # Lean 4.34 prints named errors as `error(lean.<name>):`.
        out = (
            "/t/Refute_div_by_zero.lean:3:0: error(lean.someNamedError): helper broke\n"
            "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\n  rfl\n"
        )
        self.assertEqual(self._classify(1, out), "ERROR")
        inside = "/t/Refute_div_by_zero.lean:9:2: error(lean.x): Type mismatch\n  rfl\n"
        self.assertEqual(self._classify(1, inside), "KILLED")

    def test_classify_foreign_and_unlocated_errors_are_never_kills(self) -> None:
        kill = "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\n  rfl\n"
        self.assertEqual(self._classify(1, kill), "KILLED")
        for extra in (
            "/t/Helper.lean:9:2: error: Type mismatch\n",
            "/t/OtherRefute_div_by_zero.lean:9:2: error: Type mismatch\n",
            "error: toolchain 'leanprover/lean4:v9.9.9' is not installed\n",
            "lean: error: could not load something\n",
            "[anneal-lean-run] error: scope setup failed\n",
        ):
            self.assertEqual(self._classify(1, extra + kill), "ERROR", extra)
            self.assertEqual(self._classify(1, kill + extra), "ERROR", extra)

    def test_classify_requires_marker_inside_target_theorem_diagnostic(self) -> None:
        # The marker text appears only in a warning and in wrapper chatter; the
        # error inside the theorem is something else entirely.
        out = (
            "/t/Refute_div_by_zero.lean:2:0: warning: Type mismatch rfl has type\n"
            "wrapper says: rfl unsolved goals\n"
            "/t/Refute_div_by_zero.lean:9:2: error: bizarre glitch\n"
        )
        self.assertEqual(self._classify(1, out), "ERROR")

    def test_classify_path_styles_ranges_and_signals(self) -> None:
        windows = "C:\\tmp\\fix\\Refute_div_by_zero.lean:9:2: error: Type mismatch\n  rfl\n"
        self.assertEqual(self._classify(1, windows), "KILLED")
        bare = "Refute_div_by_zero.lean:8:4-9:5: error: Type mismatch\n  rfl\n"
        self.assertEqual(self._classify(1, bare), "KILLED")
        two = (
            "/t/Refute_div_by_zero.lean:7:8: error: type mismatch\n  x\n"
            "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\n  rfl\nhas type\n"
        )
        status, detail = gmut.classify_refutation_failure(1, two, self.FIXTURE, self.SPAN)
        self.assertEqual(status, "KILLED")
        self.assertIn("[7, 9]", detail)
        for rc in (-9, -11, -15, 2, 124, 127, 134, 137, 139):
            self.assertEqual(self._classify(rc, windows), "ERROR", rc)
        for marker in ("(deterministic) timeout", "Stack overflow", "out of memory"):
            self.assertEqual(self._classify(1, windows + marker + "\n"), "ERROR", marker)

    # -- theorem span ---------------------------------------------------

    def test_theorem_span_ends_at_any_top_level_text(self) -> None:
        for trailer in (
            "example : False := by decide",
            "instance : Inhabited Nat := ⟨0⟩",
            "#eval 1",
            "-- trailing comment",
            "abbrev Z := Nat",
            "@[simp] theorem other : True := trivial",
        ):
            fixture = f"theorem target :\n    True :=\n  trivial\n\n{trailer}\n  more\n"
            self.assertEqual(
                gmut.find_theorem_line_span(fixture, "target"), (1, 3), trailer
            )
        # Prefix names must not match, and duplicates are rejected.
        primed = "theorem target' : True :=\n  trivial\n\ntheorem target : True :=\n  trivial\n"
        self.assertEqual(gmut.find_theorem_line_span(primed, "target"), (4, 5))
        dotted = "theorem target.aux : True :=\n  trivial\n"
        with self.assertRaisesRegex(ValueError, "not found"):
            gmut.find_theorem_line_span(dotted, "target")
        dup = "theorem t : True :=\n  trivial\ntheorem t : True :=\n  trivial\n"
        with self.assertRaisesRegex(ValueError, "declared 2 times"):
            gmut.find_theorem_line_span(dup, "t")

    # -- static catalog shape ------------------------------------------

    def test_fixture_shape_rejects_smuggled_proofs(self) -> None:
        good = "import Trusted.A\ntheorem t :\n    1 = 1 :=\n  rfl\n"
        self.assertEqual(gmut._fixture_shape_errors("refute", good, "t"), [])
        for bad_tail in (
            "example : True := trivial\n",
            "theorem u : True := trivial\n",
            "theorem v : 1 = 2 := sorryAx _ false\n",
            "def x : Nat := by admit\n",
            "axiom boom : False\n",
            "set_option maxRecDepth 2\n",
            "#eval 1\n",
            "def y : Bool := by native_decide\n",
            "instance : Inhabited Nat := ⟨0⟩\n",
        ):
            self.assertNotEqual(
                gmut._fixture_shape_errors("refute", good + bad_tail, "t"), [], bad_tail
            )
        # A theorem whose proof is outside its span is rejected.
        split = "theorem t :\n    1 = 1\n:= rfl\n"
        self.assertTrue(
            any("does not contain its proof" in e
                for e in gmut._fixture_shape_errors("refute", split, "t"))
        )

    def test_catalog_rejects_stale_imports_and_bad_rebuild_order(self) -> None:
        places = "Trusted/Rustc/V2026_06_01/MirSemantics/Places"
        scalars = "Trusted/Rustc/V2026_06_01/MirSemantics/Scalars"
        guard = gmut.select_guards(guard_filters=["div_by_zero"])[0]
        stale_import = (
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Places\n" + guard.refute_source
        )
        with mock.patch.object(
            gmut, "MIR_SEMANTICS_GUARDS", _replace_guard("div_by_zero", refute_source=stale_import)
        ):
            errors = gmut.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertTrue(any("stale" in e and "div_by_zero (refute)" in e for e in errors), errors)

        # Rebuilding the downstream module makes the same import legitimate.
        with mock.patch.object(
            gmut,
            "MIR_SEMANTICS_GUARDS",
            _replace_guard(
                "div_by_zero",
                refute_source=stale_import,
                rebuild_modules=(
                    scalars,
                    "Trusted/Rustc/V2026_06_01/MirSemantics/Bytes",
                    places,
                ),
            ),
        ):
            self.assertEqual(gmut.validate_catalog_invariants(ANNEAL_ROOT), [])

        # Skipping `Bytes` (which `Places` imports) leaves a stale dependency.
        with mock.patch.object(
            gmut,
            "MIR_SEMANTICS_GUARDS",
            _replace_guard("div_by_zero", rebuild_modules=(scalars, places)),
        ):
            errors = gmut.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertTrue(any("stale un-rebuilt" in e for e in errors), errors)

        with mock.patch.object(
            gmut,
            "MIR_SEMANTICS_GUARDS",
            _replace_guard("div_by_zero", replacement=guard.replacement + " sorry"),
        ):
            errors = gmut.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertTrue(any("forbidden token in replacement" in e for e in errors), errors)

        # Stale downstream `.olean`s are never seeded into a mutant overlay.
        self.assertEqual(
            gmut._stale_modules_for_guard(guard),
            set(gmut.SEMANTICS_MODULES) - {scalars},
        )
        term_guard = gmut.select_guards(guard_filters=["tb_drop_protector_conflict"])[0]
        self.assertEqual(gmut._stale_modules_for_guard(term_guard), set())

    # -- Lake cache content validation ---------------------------------

    def test_lake_hash_matches_lake_recorded_values(self) -> None:
        # Ground truth from a real Lake v4.34.1 `.trace`: the toolchain input
        # `Lean 4.34.1, commit 5045d005...` is recorded with this hash of the
        # commit string.
        self.assertEqual(
            gmut.lake_hash_of_text(b"5045d0056413266e57c625dcd7c365b10e377c52"),
            "e9f3658beb070375",
        )
        self.assertEqual(f"{gmut._LAKE_HASH_NIL:016x}", "00000000000006bb")
        # Regression pins for the tail and empty paths, taken from the
        # implementation after it reproduced real Lake source and `.olean`
        # hashes of arbitrary lengths.
        self.assertEqual(gmut.lake_hash_of_bytes(b""), "21c42906adea99f5")
        self.assertEqual(gmut.lake_hash_of_bytes(b"abc"), "4ee8255398c6e574")
        self.assertEqual(gmut.lake_hash_of_bytes(b"hello world!"), "7a8b5d63b72a5af2")
        # Lake normalizes CRLF in source text only.
        self.assertEqual(gmut.lake_hash_of_text(b"a\r\nb"), gmut.lake_hash_of_bytes(b"a\nb"))
        self.assertNotEqual(gmut.lake_hash_of_bytes(b"a\r\nb"), gmut.lake_hash_of_bytes(b"a\nb"))

    def test_lake_reuse_is_decided_by_content_not_mtime(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-lake-test-") as tmp:
            root, mods = _make_tiny_lake_root(Path(tmp))
            lib = root / ".lake/build/lib/lean"
            src_b = root / "trusted/lean/Trusted/B.lean"

            # Fresh `git worktree`: every source is NEWER than its `.olean`,
            # yet the build provably matches the sources, so it is reused.
            for mod in mods:
                os.utime(root / "trusted/lean" / f"{mod}.lean", (3e9, 3e9))
            self.assertFalse(gmut._legacy_mtime_fresh(root, mods))
            self.assertEqual(
                gmut._lake_olean_reuse_decision(root, mods), (True, "lake-trace-verified")
            )
            self.assertEqual(
                gmut._lake_olean_reuse_decision(root, mods, verify_olean_bytes=True),
                (True, "lake-trace-verified"),
            )
            self.assertTrue(gmut._can_reuse_lake_oleans(root, mods))

            # Source content diverged while its mtime looks OLDER than the
            # `.olean` (the case an mtime check wrongly accepts).
            original_b = src_b.read_bytes()
            src_b.write_bytes(original_b + b"-- edited\n")
            os.utime(src_b, (1000, 1000))
            ok, why = gmut._lake_olean_reuse_decision(root, mods)
            self.assertFalse(ok)
            self.assertIn("Trusted/B: source text differs", why)
            src_b.write_bytes(original_b)
            self.assertTrue(gmut._lake_olean_reuse_decision(root, mods)[0])

            # A changed import list is caught through the source hash too.
            src_b.write_bytes(b"def b : Nat := 2\n")
            self.assertFalse(gmut._lake_olean_reuse_decision(root, mods)[0])
            src_b.write_bytes(original_b)

    def test_lake_reuse_rejects_tampered_or_inconsistent_builds(self) -> None:
        def fresh(tmp: str) -> tuple[Path, tuple[str, ...], Path]:
            root, mods = _make_tiny_lake_root(Path(tmp))
            return root, mods, root / ".lake/build/lib/lean"

        # `.olean` rewritten after Lake hashed it (newer than its `.hash`).
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-lake-test-") as tmp:
            root, mods, lib = fresh(tmp)
            olean_a = lib / "Trusted/A.olean"
            olean_a.write_bytes(b"clobbered through a hardlink")
            os.utime(olean_a, (2_500_000_000, 2_500_000_000))
            ok, why = gmut._lake_olean_reuse_decision(root, mods)
            self.assertFalse(ok)
            self.assertIn("bytes do not match", why)
            # Same clobber with an OLD mtime needs the explicit byte check.
            os.utime(olean_a, (1000, 1000))
            self.assertTrue(gmut._lake_olean_reuse_decision(root, mods)[0])
            ok, why = gmut._lake_olean_reuse_decision(root, mods, verify_olean_bytes=True)
            self.assertFalse(ok)
            self.assertIn("bytes do not match", why)

        # `A` was rebuilt (self-consistently) but its importers were not.
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-lake-test-") as tmp:
            root, mods, lib = fresh(tmp)
            new_bytes = b"olean:Trusted/A rebuilt"
            new_hash = gmut.lake_hash_of_bytes(new_bytes)
            (lib / "Trusted/A.olean").write_bytes(new_bytes)
            os.utime(lib / "Trusted/A.olean", (2_000_000_000, 2_000_000_000))
            (lib / "Trusted/A.olean.hash").write_text(new_hash, encoding="utf-8")
            trace_a = json.loads((lib / "Trusted/A.trace").read_text(encoding="utf-8"))
            trace_a["outputs"]["o"] = [f"{new_hash}.olean"]
            (lib / "Trusted/A.trace").write_text(json.dumps(trace_a), encoding="utf-8")
            os.utime(lib / "Trusted/A.trace", (2_000_000_002, 2_000_000_002))
            ok, why = gmut._lake_olean_reuse_decision(root, mods)
            self.assertFalse(ok)
            self.assertIn("built against a different Trusted/A.olean", why)

        # Importer recorded before its import was last rebuilt.
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-lake-test-") as tmp:
            root, mods, lib = fresh(tmp)
            os.utime(lib / "Trusted/A.trace", (2_900_000_000, 2_900_000_000))
            ok, why = gmut._lake_olean_reuse_decision(root, mods)
            self.assertFalse(ok)
            self.assertIn("predates the rebuild of its import Trusted/A", why)

        # Structural problems all fail closed.
        def mutate_trace(lib: Path, mod: str, fn: object) -> None:
            path = lib / f"{mod}.trace"
            stat_before = path.stat()
            trace = json.loads(path.read_text(encoding="utf-8"))
            fn(trace)  # type: ignore[operator]
            path.write_text(json.dumps(trace), encoding="utf-8")
            os.utime(path, ns=(stat_before.st_atime_ns, stat_before.st_mtime_ns))

        cases = {
            "unsupported Lake trace schema": lambda t: t.update(schemaVersion="1999-01-01"),
            "different Lean toolchain": lambda t: t["inputs"].__setitem__(
                1, ["Lean 4.0.0, commit 0", "0" * 16]
            ),
            "unrecognized `.olean` outputs": lambda t: t["outputs"].update(
                o=["a.olean", "a.olean.server", "a.olean.private"]
            ),
            "`.olean.hash` disagrees": lambda t: t["outputs"].update(o=["0" * 16 + ".olean"]),
            "imports differ from source imports": lambda t: t["inputs"].__setitem__(
                0, ["deps", [["imports", "00000000000006bb"]]]
            ),
            "unrecognized imports record": lambda t: t["inputs"].__setitem__(0, ["deps", []]),
            "source text differs": lambda t: t["inputs"].__setitem__(
                2, ["/x/trusted/lean/Trusted/C.lean", "0" * 16]
            ),
        }
        for expected, fn in cases.items():
            with tempfile.TemporaryDirectory(prefix="anneal-gmut-lake-test-") as tmp:
                root, mods, lib = fresh(tmp)
                mutate_trace(lib, "Trusted/C", fn)
                ok, why = gmut._lake_olean_reuse_decision(root, mods)
                self.assertFalse(ok, expected)
                self.assertIn(expected, why)

        with tempfile.TemporaryDirectory(prefix="anneal-gmut-lake-test-") as tmp:
            root, mods, lib = fresh(tmp)
            (lib / "Trusted/C.trace").write_text("{not json", encoding="utf-8")
            self.assertIn("unreadable", gmut._lake_olean_reuse_decision(root, mods)[1])
            (lib / "Trusted/C.trace").unlink()
            self.assertEqual(
                gmut._lake_olean_reuse_decision(root, mods),
                (False, "Lake traces present for only some modules"),
            )
            (root / "lean-toolchain").unlink()
            (lib / "Trusted/C.olean").unlink()
            self.assertEqual(
                gmut._lake_olean_reuse_decision(root, mods),
                (False, "Trusted/C: missing .olean"),
            )

    # -- hardlink write-through ----------------------------------------

    def test_link_and_compile_never_write_through_hardlinks(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-link-test-") as tmp:
            tmp_path = Path(tmp)
            shared = tmp_path / "lake/M.olean"
            shared.parent.mkdir()
            shared.write_bytes(b"lake-bytes")
            other = tmp_path / "other.olean"
            other.write_bytes(b"other-bytes")

            # Re-linking over a destination that aliases `shared`.
            dst = tmp_path / "overlay/M.olean"
            gmut._link_or_copy(shared, dst)
            self.assertTrue(os.path.samefile(shared, dst))
            gmut._link_or_copy(other, dst)
            self.assertEqual(shared.read_bytes(), b"lake-bytes")
            self.assertEqual(dst.read_bytes(), b"other-bytes")

            # Copy fallback (cross-device) over an aliasing destination.
            gmut._link_or_copy(shared, dst)
            with mock.patch.object(gmut.os, "link", side_effect=OSError("EXDEV")):
                gmut._link_or_copy(other, dst)
            self.assertEqual(shared.read_bytes(), b"lake-bytes")
            self.assertEqual(dst.read_bytes(), b"other-bytes")
            self.assertFalse(os.path.samefile(shared, dst))

            # Compiling over a hardlinked `.olean` with an in-place writer.
            fake = tmp_path / "fake_lean"
            _write_fake_lean_sh(fake, 'printf "mutant-bytes" > "$OUT"\nexit 0')
            src_root = tmp_path / "src"
            src_root.mkdir()
            (src_root / "M.lean").write_text("-- m\n", encoding="utf-8")
            out_dir = tmp_path / "overlay"
            gmut._link_or_copy(shared, out_dir / "M.olean")
            self.assertTrue(os.path.samefile(shared, out_dir / "M.olean"))
            res = gmut._compile_module(
                fake,
                src_root,
                "M",
                out_dir,
                anneal_root=ANNEAL_ROOT,
                lean_path=[out_dir],
                timeout_sec=30,
                lean_run_wrapper=None,
            )
            self.assertEqual(res.returncode, 0, res.stderr)
            self.assertEqual((out_dir / "M.olean").read_bytes(), b"mutant-bytes")
            self.assertEqual(shared.read_bytes(), b"lake-bytes")
            self.assertFalse(os.path.samefile(shared, out_dir / "M.olean"))

    def test_synthetic_lake_reuse_leaves_lake_artifacts_untouched(self) -> None:
        # A `Scalars` mutant must not see the baseline `.olean`s of modules
        # that depend on `Scalars` (they were compiled against the unmutated
        # `Scalars`), while a `Terminators` mutant needs all of its upstream.
        fake_sh = (
            textwrap.dedent(
                """\
                SEM="$LEAN_PATH/Trusted/Rustc/V2026_06_01/MirSemantics"
                case "$LEAN_PATH" in
                  *anneal-gmut-div_by_zero-*)
                    for stale in Bytes Places Statements Terminators; do
                      if [ -e "$SEM/$stale.olean" ]; then
                        echo "stale $stale.olean visible to Scalars mutant" >&2
                        exit 3
                      fi
                    done
                    [ -e "$SEM/State.olean" ] || { echo "missing State.olean" >&2; exit 3; }
                    ;;
                  *anneal-gmut-tb_drop_protector_conflict-*)
                    for needed in State Scalars Bytes Places Statements; do
                      if [ ! -e "$SEM/$needed.olean" ]; then
                        echo "missing $needed.olean for Terminators mutant" >&2
                        exit 3
                      fi
                    done
                    ;;
                esac
                """
            )
            + KILL_ALL_FAKE_SH
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            tmp_path = Path(tmp)
            root = _make_tcb_copy_root(tmp_path)
            _write_lake_build(root, ALL_TCB_MODULES)
            lib = root / ".lake/build/lib/lean"
            before = {
                mod: (lib / f"{mod}.olean").read_bytes() for mod in ALL_TCB_MODULES
            }
            fake = tmp_path / "fake_lean"
            _write_fake_lean_sh(fake, fake_sh)
            res = _run_cli(
                [
                    "--anneal-root", str(root), "--lean", str(fake),
                    "--guard", "div_by_zero", "--guard", "tb_drop_protector_conflict",
                    "--json",
                ]
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            report = json.loads(res.stdout)
            self.assertTrue(report["used_lake_cache"])
            self.assertEqual(report["lake_cache_detail"], "lake-trace-verified")
            self.assertEqual(report["killed"], 2)
            for mod in ALL_TCB_MODULES:
                olean = lib / f"{mod}.olean"
                self.assertEqual(olean.read_bytes(), before[mod], mod)
                self.assertEqual(olean.stat().st_nlink, 1, mod)

            # A build of DIFFERENT sources is rejected and rebuilt cold even
            # though every `.olean` is newer than every source.
            scalars = root / "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean"
            scalars.write_bytes(scalars.read_bytes() + b"\n-- diverged\n")
            os.utime(scalars, (1000, 1000))
            res2 = _run_cli(
                ["--anneal-root", str(root), "--lean", str(fake), "--guard", "div_by_zero", "--json"]
            )
            self.assertEqual(res2.returncode, 0, res2.stdout + res2.stderr)
            report2 = json.loads(res2.stdout)
            self.assertFalse(report2["used_lake_cache"])
            self.assertIn("source text differs", report2["lake_cache_detail"])
            for mod in ALL_TCB_MODULES:
                self.assertEqual((lib / f"{mod}.olean").read_bytes(), before[mod], mod)

    def test_run_fails_if_lake_artifacts_change_during_run(self) -> None:
        fake_sh = (
            'if [ "$IS_MUTANT" = "1" ] && [ "$BASENAME" = "Scalars.lean" ]; then\n'
            '  printf "x" >> "$GMUT_TEST_CLOBBER"\n'
            "fi\n" + KILL_ALL_FAKE_SH
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            tmp_path = Path(tmp)
            root = _make_tcb_copy_root(tmp_path)
            _write_lake_build(root, ALL_TCB_MODULES)
            fake = tmp_path / "fake_lean"
            _write_fake_lean_sh(fake, fake_sh)
            json_out = tmp_path / "report.json"
            json_out.write_text('{"killed": 99, "total": 99}', encoding="utf-8")
            res = _run_cli(
                [
                    "--anneal-root", str(root), "--lean", str(fake),
                    "--guard", "div_by_zero", "--json", "--json-out", str(json_out),
                ],
                env={
                    "GMUT_TEST_CLOBBER": str(
                        root / ".lake/build/lib/lean/Trusted/Sequence.olean"
                    )
                },
            )
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("changed during the run", res.stderr)
            # `--json` stdout stays pure JSON, and the stale green report file
            # from an earlier run is replaced by the fatal report.
            report = json.loads(res.stdout)
            self.assertIn("changed during the run", report["fatal_error"])
            self.assertEqual(report["killed"], 0)
            self.assertEqual(json.loads(json_out.read_text(encoding="utf-8")), report)

    # -- subprocess and worker isolation -------------------------------

    def test_run_lean_spawn_failure_and_group_kill_on_timeout(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-timeout-") as tmp:
            tmp_path = Path(tmp)
            missing = gmut._run_lean(
                tmp_path / "no_such_lean",
                ["x.lean"],
                anneal_root=ANNEAL_ROOT,
                lean_path=[],
                timeout_sec=5,
                lean_run_wrapper=None,
            )
            self.assertEqual(missing.returncode, 127)
            self.assertIn("failed to execute", missing.stderr)
            self.assertEqual(
                gmut.classify_refutation_failure(
                    missing.returncode, missing.stderr, self.FIXTURE, self.SPAN
                )[0],
                "ERROR",
            )

            # A wrapper whose child outlives it: the child must die too.
            pid_file = tmp_path / "child.pid"
            wrapper_like = tmp_path / "slow_lean"
            _write_fake_lean_sh(
                wrapper_like, 'sleep 60 &\necho "$!" > "$GMUT_TEST_PIDFILE"\nwait'
            )
            with mock.patch.dict(os.environ, {"GMUT_TEST_PIDFILE": str(pid_file)}):
                t0 = time.monotonic()
                res = gmut._run_lean(
                    wrapper_like,
                    ["x.lean"],
                    anneal_root=ANNEAL_ROOT,
                    lean_path=[],
                    timeout_sec=1,
                    lean_run_wrapper=None,
                )
            self.assertEqual(res.returncode, 124)
            self.assertLess(time.monotonic() - t0, 20)
            child_pid = int(pid_file.read_text(encoding="utf-8").strip())
            deadline = time.monotonic() + 5
            alive = True
            while alive and time.monotonic() < deadline:
                try:
                    state = Path(f"/proc/{child_pid}/stat").read_text().rsplit(")", 1)[1].split()[0]
                    alive = state != "Z"
                except (OSError, IndexError):
                    alive = False
                if alive:
                    time.sleep(0.05)
            self.assertFalse(alive, f"grandchild {child_pid} survived the timeout")
            self.assertEqual(gmut._LIVE_PROCS, set())

    def test_timeout_in_one_guard_does_not_abort_the_others(self) -> None:
        fake_sh = (
            'if [ "$IS_MUTANT" = "1" ] && [ "$BASENAME" = "Refute_div_by_zero.lean" ]; then\n'
            "  sleep 60\n"
            "fi\n" + KILL_ALL_FAKE_SH
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            fake = Path(tmp) / "fake_lean"
            _write_fake_lean_sh(fake, fake_sh)
            res = _run_cli(
                [
                    "--lean", str(fake), "--no-lake-cache", "--jobs", "2",
                    "--timeout-sec", "1", "--json",
                    "--guard", "div_by_zero", "--guard", "rem_by_zero",
                ]
            )
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        report = json.loads(res.stdout)
        by_id = {r["guard_id"]: r for r in report["results"]}
        self.assertEqual(by_id["div_by_zero"]["status"], "ERROR")
        self.assertIn("exit code 124", by_id["div_by_zero"]["detail"])
        self.assertEqual(by_id["rem_by_zero"]["status"], "KILLED")
        self.assertEqual((report["killed"], report["errors"], report["survived"]), (1, 1, 0))

    def test_baseline_failure_aborts_in_flight_lean_promptly(self) -> None:
        # One baseline fixture fails at once while another is still compiling.
        # The run must stop the in-flight Lean instead of waiting it out.
        fake_sh = (
            'if [ "$IS_MUTANT" = "0" ]; then\n'
            '  case "$BASENAME" in\n'
            "    Refute_div_by_zero.lean) echo boom >&2; exit 1 ;;\n"
            "    PositiveSanity_rem_by_zero.lean) sleep 60 ;;\n"
            "  esac\n"
            "fi\n" + KILL_ALL_FAKE_SH
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            fake = Path(tmp) / "fake_lean"
            _write_fake_lean_sh(fake, fake_sh)
            t0 = time.monotonic()
            res = _run_cli(
                [
                    "--lean", str(fake), "--no-lake-cache", "--jobs", "2",
                    "--timeout-sec", "120", "--json",
                    "--guard", "div_by_zero", "--guard", "rem_by_zero",
                ]
            )
            elapsed = time.monotonic() - t0
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        self.assertLess(elapsed, 30, "in-flight baseline compile was not aborted")
        self.assertIn("baseline", json.loads(res.stdout)["fatal_error"])
        self.assertFalse(gmut._ABORT.is_set())

    def test_unexpected_worker_exception_becomes_per_guard_error(self) -> None:
        def fake_compile(*args: object, **kwargs: object) -> subprocess.CompletedProcess[str]:
            out_dir, mod = args[3], args[2]
            assert isinstance(out_dir, Path) and isinstance(mod, str)
            (out_dir / f"{mod}.olean").parent.mkdir(parents=True, exist_ok=True)
            (out_dir / f"{mod}.olean").write_bytes(b"fake")
            return subprocess.CompletedProcess(args=["fake"], returncode=0, stdout="", stderr="")

        def fake_check(guard: gmut.MirSemanticsGuard, **kwargs: object) -> gmut.GuardResult:
            if guard.guard_id == "div_by_zero":
                raise OSError("No space left on device")
            return gmut.GuardResult(
                guard.guard_id, guard.target_file, guard.target_module,
                guard.quick, "KILLED", 0.0, "ok",
            )

        with (
            mock.patch.object(gmut, "_compile_module", side_effect=fake_compile),
            mock.patch.object(gmut, "_check_one_mir_guard", side_effect=fake_check),
        ):
            report = gmut.run_guard_mutation_suite(
                anneal_root=ANNEAL_ROOT,
                lean_bin=Path("/nonexistent/lean"),
                guard_filters=["div_by_zero", "rem_by_zero"],
                jobs=2,
                reuse_lake_cache=False,
            )
        by_id = {r["guard_id"]: r for r in report["results"]}  # type: ignore[union-attr]
        self.assertEqual(by_id["div_by_zero"]["status"], "ERROR")
        self.assertIn("internal error: OSError", by_id["div_by_zero"]["detail"])
        self.assertEqual(by_id["rem_by_zero"]["status"], "KILLED")
        self.assertEqual((report["killed"], report["errors"]), (1, 1))

    def test_mutated_module_without_olean_or_aliasing_baseline_is_error(self) -> None:
        guard = gmut.select_guards(guard_filters=["div_by_zero"])[0]
        baseline_mods = gmut._baseline_modules_for_guards([guard])
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            base = Path(tmp) / "base"
            for mod in baseline_mods:
                (base / f"{mod}.olean").parent.mkdir(parents=True, exist_ok=True)
                (base / f"{mod}.olean").write_bytes(b"base")

            def run(compile_impl: object) -> gmut.GuardResult:
                with mock.patch.object(gmut, "_compile_module", side_effect=compile_impl):
                    return gmut._check_one_mir_guard(
                        guard,
                        anneal_root=ANNEAL_ROOT,
                        lean_bin=Path("/nonexistent/lean"),
                        base_olean_dir=base,
                        baseline_modules=baseline_mods,
                        timeout_sec=30,
                        lean_run_wrapper=None,
                    )

            ok = subprocess.CompletedProcess(args=["fake"], returncode=0, stdout="", stderr="")
            no_olean = run(lambda *a, **k: ok)
            self.assertEqual(no_olean.status, "ERROR")
            self.assertIn("produced no .olean", no_olean.detail)

            def alias_baseline(*args: object, **kwargs: object) -> object:
                out_dir, mod = args[3], args[2]
                assert isinstance(out_dir, Path) and isinstance(mod, str)
                os.link(base / f"{mod}.olean", out_dir / f"{mod}.olean")
                return ok

            aliased = run(alias_baseline)
            self.assertEqual(aliased.status, "ERROR")
            self.assertIn("shares an inode", aliased.detail)
            self.assertEqual(
                (base / f"{guard.target_module}.olean").read_bytes(), b"base"
            )

    # -- CLI ------------------------------------------------------------

    def test_cli_relative_lean_and_anneal_root_paths(self) -> None:
        # Lean runs with `cwd=<anneal_root>`, so relative paths must be made
        # absolute before the directory changes.
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            tmp_path = Path(tmp)
            _write_fake_lean_sh(tmp_path / "fake_lean", KILL_ALL_FAKE_SH)
            res = _run_cli(
                [
                    "--anneal-root", os.path.relpath(ANNEAL_ROOT, tmp_path),
                    "--lean", "./fake_lean", "--no-lake-cache",
                    "--guard", "div_by_zero", "--json",
                ],
                cwd=tmp_path,
            )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        report = json.loads(res.stdout)
        self.assertEqual((report["killed"], report["total"]), (1, 1))
        self.assertTrue(os.path.isabs(report["lean_bin"]))

    def test_cli_argument_validation_and_json_stdout_purity(self) -> None:
        for bad in (
            ["--jobs", "0"],
            ["--jobs", "-3"],
            ["--timeout-sec", "0"],
            ["--list", "--json-out", "x.json"],
            ["--use-lean-run", "--no-lean-run"],
        ):
            res = _run_cli(bad)
            self.assertEqual(res.returncode, 2, bad)
            self.assertEqual(res.stdout, "", bad)

        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            tmp_path = Path(tmp)
            fake = tmp_path / "fake_lean"
            _write_fake_lean_sh(fake, KILL_ALL_FAKE_SH)

            # Unknown guard and missing Lean are fatal, with pure-JSON stdout.
            for args, needle in (
                (["--lean", str(fake), "--guard", "no_such_guard_xyz"], "no cataloged guard matched"),
                (["--lean", str(tmp_path / "missing_lean")], "Lean binary not found"),
                (["--lean", str(fake), "--guard", " "], "must be non-empty"),
            ):
                res = _run_cli([*args, "--no-lake-cache", "--json"])
                self.assertEqual(res.returncode, 1, args)
                self.assertIn(needle, res.stderr)
                report = json.loads(res.stdout)
                self.assertIn(needle, report["fatal_error"])
                self.assertEqual((report["total"], report["killed"], report["errors"]), (0, 0, 1))

            # Several `--guard` flags (exact, substring, duplicate) union in
            # catalog order; stdout is exactly one JSON document.
            res = _run_cli(
                [
                    "--lean", str(fake), "--no-lake-cache", "--json",
                    "--guard", "shift_oob", "--guard", "signed_", "--guard", "shift_oob",
                ]
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            report = json.loads(res.stdout)
            self.assertEqual(
                [r["guard_id"] for r in report["results"]],
                ["signed_div_overflow", "signed_rem_overflow", "shift_oob"],
            )
            self.assertEqual(report["lake_cache_detail"], "disabled by --no-lake-cache")

            # Human mode prints the summary banner; JSON mode never does.
            human = _run_cli(
                ["--lean", str(fake), "--no-lake-cache", "--guard", "div_by_zero"]
            )
            self.assertEqual(human.returncode, 0, human.stdout + human.stderr)
            self.assertIn("MIR guard-mutation summary (guard, cold-build): 1/1 killed", human.stdout)
            self.assertNotIn("MIR guard-mutation summary", res.stdout)


if __name__ == "__main__":
    unittest.main()
