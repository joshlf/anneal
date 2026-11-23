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
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import textwrap
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
        self.assertEqual(
            gmut.find_theorem_line_span(fixture, "first_thm"),
            (5, 7),
        )
        self.assertEqual(
            gmut.find_theorem_line_span(fixture, "second_thm"),
            (10, 13),
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
        self.assertIsNone(report)
        self.assertIn("baseline refute fixture", err)

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


if __name__ == "__main__":
    unittest.main()
