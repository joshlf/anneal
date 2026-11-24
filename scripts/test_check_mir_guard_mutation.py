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
import random
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import textwrap
import threading
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


def _write_fake_lean_sh(
    bin_path: Path,
    body_sh: str,
    *,
    version_str: str | None = None,
) -> None:
    """Create a fast executable POSIX-shell fake `lean` binary (~1ms/call).

    Pre-parses `-o <out>` into `$OUT` and the trailing source path into `$SRC`
    (with `$BASENAME`), and sets `$IS_MUTANT=1` when `LEAN_PATH` points into a
    per-mutant temp dir rather than `anneal-gmut-base-`.
    """
    version_block = ""
    if version_str is not None:
        safe_ver = version_str.replace("'", "'\\''")
        version_block = (
            'if [ "${1:-}" = "--version" ]; then\n'
            f"  printf '%s\\n' '{safe_ver}'\n"
            "  exit 0\n"
            "fi\n"
        )
    script = (
        "#!/bin/sh\n"
        "set -eu\n"
        f"{version_block}"
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
            self.assertFalse(gmut._lake_olean_reuse_decision(root, modules)[0])

            for mod in modules:
                src = root / "trusted/lean" / f"{mod}.lean"
                src.parent.mkdir(parents=True, exist_ok=True)
                src.write_text("-- dummy\n", encoding="utf-8")
                os.utime(src, (1000.0, 1000.0))

                olean = root / ".lake/build/lib/lean" / f"{mod}.olean"
                olean.parent.mkdir(parents=True, exist_ok=True)
                olean.write_bytes(b"olean")
                os.utime(olean, (2000.0, 2000.0))

            self.assertTrue(gmut._lake_olean_reuse_decision(root, modules)[0])

            # Direct source newer than `.olean` -> False.
            scalars_src = (
                root
                / "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean"
            )
            os.utime(scalars_src, (3000.0, 3000.0))
            self.assertFalse(gmut._lake_olean_reuse_decision(root, modules)[0])
            os.utime(scalars_src, (1000.0, 1000.0))
            self.assertTrue(gmut._lake_olean_reuse_decision(root, modules)[0])

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
            self.assertFalse(gmut._lake_olean_reuse_decision(root, modules)[0])

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


TEST_LEAN_V434_GITHASH = "5045d0056413266e57c625dcd7c365b10e377c52"
TEST_LEAN_V434_VERSION = (
    "Lean (version 4.34.1, x86_64-unknown-linux-gnu, "
    f"commit {TEST_LEAN_V434_GITHASH}, Release)"
)
TINY_LAKEFILE_TOML = (
    'name = "Anneal"\n'
    'defaultTargets = ["Trusted"]\n'
    "\n"
    "[[lean_lib]]\n"
    'name = "Trusted"\n'
    'srcDir = "trusted/lean"\n'
)


def _make_tcb_copy_root(tmp: Path) -> Path:
    """Copy the live TCB sources into an isolated fake repository root."""
    root = tmp / "root"
    for mod in ALL_TCB_MODULES:
        dst = root / "trusted/lean" / f"{mod}.lean"
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ANNEAL_ROOT / "trusted/lean" / f"{mod}.lean", dst)
    shutil.copyfile(ANNEAL_ROOT / "lean-toolchain", root / "lean-toolchain")
    shutil.copyfile(ANNEAL_ROOT / "lakefile.toml", root / "lakefile.toml")
    return root


def _write_lake_build(
    root: Path,
    modules: tuple[str, ...],
    *,
    traces: bool = True,
    base_time: int = 2_000_000_000,
    synthetic: bool = False,
    synthetic_modules: set[str] | None = None,
    lean_githash: str = TEST_LEAN_V434_GITHASH,
    pkg_name: str = "Anneal",
    olean_bytes: dict[str, bytes] | None = None,
) -> None:
    """Write a fake `.lake/build/lib/lean` tree shaped like Lake's own output.

    Traces record the source path of ANOTHER checkout, as they do when a
    `.lake` directory is hardlinked into a fresh `git worktree`. When
    `synthetic=True` (or a module is listed in `synthetic_modules`), writes a
    `$LAKE_CACHE_DIR`-style `"synthetic": true` trace with `"inputs": []` and
    the exact Lake v4.34 `"depHash"`.
    """
    lib = root / ".lake/build/lib/lean"
    version = gmut._read_lean_toolchain_version(root)
    olean_hashes: dict[str, str] = {}
    all_arts_hashes: dict[str, int] = {}
    legacy_trans_hashes: dict[str, int] = {}
    for idx, mod in enumerate(modules):
        stamp = base_time + idx * 10
        olean = lib / f"{mod}.olean"
        olean.parent.mkdir(parents=True, exist_ok=True)
        olean.write_bytes((olean_bytes or {}).get(mod, f"olean:{mod}".encode()))
        os.utime(olean, (stamp, stamp))
        if not traces:
            continue
        olean_hash = gmut.lake_hash_of_bytes(olean.read_bytes())
        olean_hashes[mod] = olean_hash
        all_arts_hashes[mod] = gmut._lean_mix_hash(
            gmut._LAKE_HASH_NIL, int(olean_hash, 16)
        )
        hash_path = lib / f"{mod}.olean.hash"
        hash_path.write_text(olean_hash, encoding="utf-8")
        os.utime(hash_path, (stamp + 1, stamp + 1))
        src_bytes = (root / "trusted/lean" / f"{mod}.lean").read_bytes()
        imports = gmut._extract_trusted_imports(src_bytes.decode("utf-8"))
        dep_hash, mod_legacy_trans = gmut.lake_module_dep_hash(
            module=mod,
            src_bytes=src_bytes,
            direct_imports=imports,
            all_arts_hashes=all_arts_hashes,
            legacy_trans_hashes=legacy_trans_hashes,
            lean_githash=lean_githash,
            pkg_name=pkg_name,
        )
        legacy_trans_hashes[mod] = mod_legacy_trans
        is_syn = synthetic or (
            synthetic_modules is not None and mod in synthetic_modules
        )
        if is_syn:
            trace: dict[str, object] = {
                "synthetic": True,
                "schemaVersion": "2025-09-10",
                "outputs": {"o": [f"{olean_hash}.olean"], "m": False},
                "log": [],
                "inputs": [],
                "depHash": dep_hash,
            }
        else:
            # Lake records two entries per import, in source order.
            imports_node: object = [
                entry
                for imp in imports
                for entry in (
                    [
                        f"{imp.replace('/', '.')} transitive imports (legacy)",
                        f"{legacy_trans_hashes[imp]:016x}",
                    ],
                    [
                        f"{imp.replace('/', '.')}:importAllArts",
                        gmut.lake_import_arts_hash(olean_hashes[imp]),
                    ],
                )
            ] or "00000000000006bb"
            trace = {
                "synthetic": False,
                "schemaVersion": "2025-09-10",
                "outputs": {"o": [f"{olean_hash}.olean"], "m": False},
                "log": [],
                "inputs": [
                    ["deps", [["imports", imports_node]]],
                    [f"Lean {version}, commit {lean_githash}", "0" * 16],
                    [
                        f"/elsewhere/other-worktree/trusted/lean/{mod}.lean",
                        gmut.lake_hash_of_text(src_bytes),
                    ],
                    ["options", "00000000000006bb"],
                    ["Module.leanArgs: #[]", "00000000000006bb"],
                ],
                "depHash": dep_hash,
            }
        trace_path = lib / f"{mod}.trace"
        trace_path.write_text(json.dumps(trace), encoding="utf-8")
        os.utime(trace_path, (stamp + 2, stamp + 2))


def _make_tiny_lake_root(
    tmp: Path,
    *,
    synthetic: bool = False,
    synthetic_modules: set[str] | None = None,
) -> tuple[Path, tuple[str, ...]]:
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
    (root / "lakefile.toml").write_text(TINY_LAKEFILE_TOML, encoding="utf-8")
    modules = tuple(sources)
    _write_lake_build(
        root,
        modules,
        synthetic=synthetic,
        synthetic_modules=synthetic_modules,
    )
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
        # Lean 4.34 reports a failing `:= rfl` theorem twice: the `@[defeq]`
        # check at the declaration and the `Type mismatch` at `rfl`.
        two = (
            "/t/Refute_div_by_zero.lean:7:0: error: Not a definitional equality: "
            "the left-hand side\n  f x\n"
            "is not definitionally equal to the right-hand side\n  y\n"
            "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\n  rfl\nhas type\n"
        )
        status, detail = gmut.classify_refutation_failure(1, two, self.FIXTURE, self.SPAN)
        self.assertEqual(status, "KILLED")
        self.assertIn("[7, 9]", detail)
        # A second error about a term of the STATEMENT is not a refuted proof.
        broken_statement = (
            "/t/Refute_div_by_zero.lean:7:8: error: type mismatch\n  x\n"
            "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\n  rfl\nhas type\n"
        )
        self.assertEqual(self._classify(1, broken_statement), "ERROR")
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
            self.assertTrue(gmut._lake_olean_reuse_decision(root, mods)[0])

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
            # Same clobber with an OLD mtime: still caught, because every
            # reused `.olean` is re-hashed by default. Only the explicit
            # mtime-trust mode misses it.
            os.utime(olean_a, (1000, 1000))
            ok, why = gmut._lake_olean_reuse_decision(root, mods)
            self.assertFalse(ok)
            self.assertIn("bytes do not match", why)
            self.assertTrue(
                gmut._lake_olean_reuse_decision(root, mods, verify_olean_bytes=False)[0]
            )

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

        # Record mtimes play no part: a consistent build whose records were
        # copied in an arbitrary order (`cp -r`) is still reusable.
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-lake-test-") as tmp:
            root, mods, lib = fresh(tmp)
            os.utime(lib / "Trusted/A.trace", (2_900_000_000, 2_900_000_000))
            self.assertEqual(
                gmut._lake_olean_reuse_decision(root, mods), (True, "lake-trace-verified")
            )

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


class GuardMutationA1AdversarialTests(unittest.TestCase):
    FIXTURE = "Refute_div_by_zero.lean"
    SPAN = (7, 9)

    def _classify(self, rc: int, out: str) -> str:
        return gmut.classify_refutation_failure(rc, out, self.FIXTURE, self.SPAN)[0]

    # -- Lake v4.34 `"synthetic": true` (`$LAKE_CACHE_DIR`) traces ------

    def test_lake_module_dep_hash_matches_real_v434_sequence_trace(self) -> None:
        # Ground truth from a real Lake v4.34.1 `$LAKE_CACHE_DIR` restore on the
        # 128-vCPU host: `.lake/build/lib/lean/Trusted/Sequence.trace` records
        # `"synthetic": true`, `"inputs": []`, `"depHash": "c6d95c0a123d5a26"`.
        seq_bytes = (ANNEAL_ROOT / "trusted/lean/Trusted/Sequence.lean").read_bytes()
        pkg_name, err = gmut._read_lakefile_trusted_pkg_name(ANNEAL_ROOT)
        self.assertEqual((pkg_name, err), ("Anneal", ""))
        dep_hash, legacy_trans = gmut.lake_module_dep_hash(
            module="Trusted/Sequence",
            src_bytes=seq_bytes,
            direct_imports=[],
            all_arts_hashes={},
            legacy_trans_hashes={},
            lean_githash=TEST_LEAN_V434_GITHASH,
            pkg_name="Anneal",
        )
        self.assertEqual(legacy_trans, gmut._LAKE_HASH_NIL)
        self.assertEqual(dep_hash, "c6d95c0a123d5a26")

    def test_synthetic_lake_trace_verification_and_mixed_trees(self) -> None:
        # Pure synthetic tree: accepted even when sources are newer than
        # `.olean`s AND `.trace` mtimes are reversed (parallel cache restore).
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-syn-test-") as tmp:
            root, mods = _make_tiny_lake_root(Path(tmp), synthetic=True)
            lib = root / ".lake/build/lib/lean"
            for mod in mods:
                os.utime(root / "trusted/lean" / f"{mod}.lean", (3e9, 3e9))
            os.utime(lib / "Trusted/A.trace", (2_900_000_000, 2_900_000_000))
            os.utime(lib / "Trusted/B.trace", (2_500_000_000, 2_500_000_000))
            os.utime(lib / "Trusted/C.trace", (2_100_000_000, 2_100_000_000))
            self.assertEqual(
                gmut._lake_olean_reuse_decision(
                    root, mods, lean_githash=TEST_LEAN_V434_GITHASH
                ),
                (True, "lake-trace-verified (synthetic)"),
            )
            self.assertEqual(
                gmut._lake_olean_reuse_decision(
                    root,
                    mods,
                    verify_olean_bytes=True,
                    lean_githash=TEST_LEAN_V434_GITHASH,
                ),
                (True, "lake-trace-verified (synthetic)"),
            )

            # Without lean_githash or lean_bin, synthetic traces fail closed.
            ok, why = gmut._lake_olean_reuse_decision(root, mods)
            self.assertFalse(ok)
            self.assertIn("requires active Lean githash", why)

            # Wrong githash fails closed.
            ok, why = gmut._lake_olean_reuse_decision(
                root, mods, lean_githash="0" * 40
            )
            self.assertFalse(ok)
            self.assertIn("depHash mismatch", why)

            # Edited source with OLD mtime breaks `depHash`.
            src_c = root / "trusted/lean/Trusted/C.lean"
            orig_c = src_c.read_bytes()
            src_c.write_bytes(orig_c + b"-- stale\n")
            os.utime(src_c, (1000, 1000))
            ok, why = gmut._lake_olean_reuse_decision(
                root, mods, lean_githash=TEST_LEAN_V434_GITHASH
            )
            self.assertFalse(ok)
            self.assertIn("Trusted/C: synthetic Lake trace depHash mismatch", why)
            src_c.write_bytes(orig_c)

            # Transitive rebuild of `A` (updating `A`'s `.olean`, `.hash`, and
            # `A.trace` self-consistently, but leaving `B` and `C` untouched)
            # breaks `B`'s `depHash`!
            new_a_bytes = b"olean:Trusted/A rebuilt"
            new_a_hash = gmut.lake_hash_of_bytes(new_a_bytes)
            (lib / "Trusted/A.olean").write_bytes(new_a_bytes)
            (lib / "Trusted/A.olean.hash").write_text(new_a_hash, encoding="utf-8")
            trace_a = json.loads((lib / "Trusted/A.trace").read_text(encoding="utf-8"))
            trace_a["outputs"]["o"] = [f"{new_a_hash}.olean"]
            (lib / "Trusted/A.trace").write_text(json.dumps(trace_a), encoding="utf-8")
            ok, why = gmut._lake_olean_reuse_decision(
                root, mods, lean_githash=TEST_LEAN_V434_GITHASH
            )
            self.assertFalse(ok)
            self.assertIn("Trusted/B: synthetic Lake trace depHash mismatch", why)

        # Mixed trees: non-synthetic A + synthetic B + non-synthetic C, AND
        # synthetic A + non-synthetic B + synthetic C both verify cleanly.
        for syn_set in ({"Trusted/B"}, {"Trusted/A", "Trusted/C"}):
            with tempfile.TemporaryDirectory(prefix="anneal-gmut-mix-test-") as tmp:
                root, mods = _make_tiny_lake_root(
                    Path(tmp), synthetic_modules=syn_set
                )
                self.assertEqual(
                    gmut._lake_olean_reuse_decision(
                        root, mods, lean_githash=TEST_LEAN_V434_GITHASH
                    ),
                    (True, "lake-trace-verified (synthetic)"),
                    syn_set,
                )

        # Fail-closed checks for lakefile.toml, outputs.m, non-bool synthetic,
        # `module` headers, and non-Trusted imports.
        lakefile_bad_cases = (
            ("missing lakefile.toml", lambda r: (r / "lakefile.toml").unlink(), "cannot read lakefile.toml"),
            ("lakefile.lean present", lambda r: (r / "lakefile.lean").write_text("-- lean\n", encoding="utf-8"), "lakefile.lean is unsupported"),
            ("root leanOptions", lambda r: (r / "lakefile.toml").write_text(TINY_LAKEFILE_TOML.replace('name = "Anneal"\n', 'name = "Anneal"\n[leanOptions]\nautoImplicit = false\n'), encoding="utf-8"), "unsupported root key"),
            ("Trusted moreLeanArgs", lambda r: (r / "lakefile.toml").write_text(TINY_LAKEFILE_TOML + 'moreLeanArgs = ["-DautoImplicit=false"]\n', encoding="utf-8"), "Trusted` lean_lib sets unsupported key"),
            ("wrong srcDir", lambda r: (r / "lakefile.toml").write_text(TINY_LAKEFILE_TOML.replace("trusted/lean", "other/lean"), encoding="utf-8"), "srcDir"),
        )
        for label, mutator, expected_msg in lakefile_bad_cases:
            with tempfile.TemporaryDirectory(prefix="anneal-gmut-syn-bad-") as tmp:
                root, mods = _make_tiny_lake_root(Path(tmp), synthetic=True)
                mutator(root)
                ok, why = gmut._lake_olean_reuse_decision(
                    root, mods, lean_githash=TEST_LEAN_V434_GITHASH
                )
                self.assertFalse(ok, label)
                self.assertIn(expected_msg, why, label)

        # `outputs.m == true`, non-bool `synthetic`, `module` header, and
        # non-Trusted imports all fail closed.
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-syn-bad2-") as tmp:
            root, mods = _make_tiny_lake_root(Path(tmp), synthetic=True)
            lib = root / ".lake/build/lib/lean"
            tr_path = lib / "Trusted/A.trace"
            orig_tr = json.loads(tr_path.read_text(encoding="utf-8"))

            bad_m = {**orig_tr, "outputs": {**orig_tr["outputs"], "m": True}}
            tr_path.write_text(json.dumps(bad_m), encoding="utf-8")
            ok, why = gmut._lake_olean_reuse_decision(
                root, mods, lean_githash=TEST_LEAN_V434_GITHASH
            )
            self.assertFalse(ok)
            self.assertIn("module-system", why)

            bad_syn = {**orig_tr, "synthetic": "yes"}
            tr_path.write_text(json.dumps(bad_syn), encoding="utf-8")
            ok, why = gmut._lake_olean_reuse_decision(
                root, mods, lean_githash=TEST_LEAN_V434_GITHASH
            )
            self.assertFalse(ok)
            self.assertIn("unrecognized `synthetic`", why)

            tr_path.write_text(json.dumps(orig_tr), encoding="utf-8")
            (root / "trusted/lean/Trusted/A.lean").write_text(
                "module\ndef a : Nat := 1\n", encoding="utf-8"
            )
            ok, why = gmut._lake_olean_reuse_decision(
                root, mods, lean_githash=TEST_LEAN_V434_GITHASH
            )
            self.assertFalse(ok)
            self.assertIn("`module` files are unsupported", why)

            (root / "trusted/lean/Trusted/A.lean").write_text(
                "import Lean\ndef a : Nat := 1\n", encoding="utf-8"
            )
            ok, why = gmut._lake_olean_reuse_decision(
                root, mods, lean_githash=TEST_LEAN_V434_GITHASH
            )
            self.assertFalse(ok)
            self.assertIn("non-Trusted import", why)

    def test_synthetic_lake_trace_cli_end_to_end_reuses_cache(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-syn-cli-") as tmp:
            tmp_path = Path(tmp)
            root = _make_tcb_copy_root(tmp_path)
            _write_lake_build(root, ALL_TCB_MODULES, synthetic=True)
            lib = root / ".lake/build/lib/lean"
            before = {
                mod: (lib / f"{mod}.olean").read_bytes() for mod in ALL_TCB_MODULES
            }
            fake = tmp_path / "fake_lean"
            _write_fake_lean_sh(
                fake, KILL_ALL_FAKE_SH, version_str=TEST_LEAN_V434_VERSION
            )
            res = _run_cli(
                [
                    "--anneal-root", str(root), "--lean", str(fake),
                    "--guard", "div_by_zero", "--json",
                ]
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            report = json.loads(res.stdout)
            self.assertTrue(report["used_lake_cache"])
            self.assertEqual(
                report["lake_cache_detail"], "lake-trace-verified (synthetic)"
            )
            self.assertEqual(report["killed"], 1)
            for mod in ALL_TCB_MODULES:
                olean = lib / f"{mod}.olean"
                self.assertEqual(olean.read_bytes(), before[mod], mod)
                self.assertEqual(olean.stat().st_nlink, 1, mod)

            # A Lean binary whose `--version` disagrees with `lean-toolchain`
            # fails closed and falls back to a cold build.
            wrong_fake = tmp_path / "wrong_lean"
            _write_fake_lean_sh(
                wrong_fake,
                KILL_ALL_FAKE_SH,
                version_str=(
                    "Lean (version 4.33.0, x86_64-unknown-linux-gnu, "
                    f"commit {TEST_LEAN_V434_GITHASH}, Release)"
                ),
            )
            res2 = _run_cli(
                [
                    "--anneal-root", str(root), "--lean", str(wrong_fake),
                    "--guard", "div_by_zero", "--json",
                ]
            )
            self.assertEqual(res2.returncode, 0, res2.stdout + res2.stderr)
            report2 = json.loads(res2.stdout)
            self.assertFalse(report2["used_lake_cache"])
            self.assertIn("active Lean binary is 4.33.0, expected 4.34.1", report2["lake_cache_detail"])

    # -- refutation classification & sorry boundary ---------------------

    def test_classify_indented_error_body_vs_unlocated_errors(self) -> None:
        # Indented continuation lines inside a located fixture error may
        # contain `error:` prose without turning a genuine kill into ERROR.
        kill_with_indented = (
            "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\n"
            "  rfl\n"
            "  note: type error: expected .ub\n"
            "has type\n"
            "  ?m.1 = ?m.1\n"
        )
        self.assertEqual(self._classify(1, kill_with_indented), "KILLED")

        # Indented error BEFORE any diagnostic header is still unlocated -> ERROR.
        self.assertEqual(
            self._classify(1, "  error: wrapper boom\n" + kill_with_indented),
            "ERROR",
        )
        # Column-0 unlocated error AFTER the fixture diagnostic -> ERROR.
        self.assertEqual(
            self._classify(1, kill_with_indented + "error: post-elaboration failure\n"),
            "ERROR",
        )
        # Indented error inside a FOREIGN file's diagnostic -> ERROR.
        foreign_warn = "/t/Other.lean:1:0: warning: w\n  error: leaked\n"
        self.assertEqual(
            self._classify(1, foreign_warn + kill_with_indented),
            "ERROR",
        )

    def test_sorry_warning_word_boundary(self) -> None:
        self.assertFalse(
            gmut._has_sorry_warning("X.lean:3:8: warning: unused variable `sorry_helper`")
        )
        self.assertFalse(
            gmut._has_sorry_warning("/tmp/sorry_dir/X.lean:1:0: warning: unused variable")
        )
        for text in (
            "X.lean:3:8: warning: declaration uses `sorry`",
            "X.lean:3:8: warning: declaration uses 'sorry'",
            "X.lean:3:8: warning: declaration uses sorry",
            "X.lean:3:8: warning: declaration uses `sorryAx`",
        ):
            self.assertTrue(gmut._has_sorry_warning(text), text)

    # -- header parsing & comment-aware fixture validation --------------

    def test_lean_header_parser_and_comment_aware_fixture_validation(self) -> None:
        src = textwrap.dedent(
            """\
            -- import Trusted.CommentedLine
            /- nested /- import Trusted.NestedComment -/
               import Trusted.BlockComment -/
            prelude
            public meta import all Trusted.A -- trailing comment
            import Trusted.B
            namespace Foo
            -- After namespace, import is not a header directive:
            import Trusted.NotHeader
            """
        )
        self.assertEqual(
            gmut._parse_lean_header(src),
            (False, ["Trusted/A", "Trusted/B"]),
        )
        self.assertEqual(
            gmut._parse_lean_header("module\nimport Trusted.A\nimport «Lean»\n"),
            (True, ["Trusted/A", "«Lean»"]),
        )

        # Comments mentioning `theorem`/`example` and string literals with `--`
        # do not cause false positives, while `macro_rules`, `elab_rules`,
        # unclosed `/-`, and raw `sorry` in comments are rejected.
        ok_fixture = textwrap.dedent(
            """\
            import Trusted.A
            -- theorem note: example helper
            def msg : String := "-- not a comment /- neither"
            /- theorem fake : True := trivial -/
            theorem t :
                1 = 1 :=
              rfl
            """
        )
        self.assertEqual(gmut._fixture_shape_errors("refute", ok_fixture, "t"), [])
        self.assertEqual(gmut.find_theorem_line_span(ok_fixture, "t"), (5, 7))
        for bad_tail in (
            "macro_rules | `(foo) => `(1)\n",
            "elab_rules : term | `(foo) => pure default\n",
            "/- unclosed comment\n",
            "-- " + "TO" + "DO: remove sorry\n",
        ):
            self.assertNotEqual(
                gmut._fixture_shape_errors("refute", ok_fixture + bad_tail, "t"),
                [],
                bad_tail,
            )

        # Non-Trusted imports (including guillemet-escaped) and `module`
        # headers in fixtures are rejected by `validate_catalog_invariants`.
        guard = gmut.select_guards(guard_filters=["div_by_zero"])[0]
        for prefix, needle in (
            ("import Lean\n", "non-Trusted module"),
            ("import «Lean»\n", "non-Trusted module"),
            ("module\n", "must not use a `module` header"),
        ):
            with mock.patch.object(
                gmut,
                "MIR_SEMANTICS_GUARDS",
                _replace_guard("div_by_zero", refute_source=prefix + guard.refute_source),
            ):
                errors = gmut.validate_catalog_invariants(ANNEAL_ROOT)
            self.assertTrue(any(needle in e for e in errors), (prefix, errors))

    # -- atomic `_ABORT` / `_LIVE_PROCS` spawn race ---------------------

    def test_run_lean_abort_during_popen_kills_child_immediately(self) -> None:
        # Simulate `_abort_pending` firing in the exact window between
        # `subprocess.Popen(...)` returning and `_run_lean` acquiring
        # `_LIVE_PROCS_LOCK`. The child must be killed immediately (rc=130).
        real_popen = gmut.subprocess.Popen
        spawned_pids: list[int] = []

        def racing_popen(*args: object, **kwargs: object) -> subprocess.Popen[str]:
            proc = real_popen(*args, **kwargs)
            spawned_pids.append(proc.pid)
            gmut._ABORT.set()
            return proc

        gmut._ABORT.clear()
        try:
            with tempfile.TemporaryDirectory(prefix="anneal-gmut-race-") as tmp:
                slow = Path(tmp) / "slow_lean"
                _write_fake_lean_sh(slow, "sleep 60")
                t0 = time.monotonic()
                with mock.patch.object(gmut.subprocess, "Popen", side_effect=racing_popen):
                    res = gmut._run_lean(
                        slow,
                        ["x.lean"],
                        anneal_root=ANNEAL_ROOT,
                        lean_path=[],
                        timeout_sec=30,
                        lean_run_wrapper=None,
                    )
                elapsed = time.monotonic() - t0
            self.assertEqual(res.returncode, 130)
            self.assertIn("aborted while Lean was starting", res.stderr)
            self.assertLess(elapsed, 5.0)
            self.assertEqual(len(spawned_pids), 1)
            self.assertEqual(gmut._LIVE_PROCS, set())
        finally:
            gmut._ABORT.clear()

    # -- expanded 14-guard catalog & strengthened return sanity ---------

    def test_new_guards_and_strengthened_return_sanity(self) -> None:
        self.assertGreaterEqual(len(gmut.MIR_SEMANTICS_GUARDS), 14)
        by_id = {g.guard_id: g for g in gmut.MIR_SEMANTICS_GUARDS}
        self.assertIn("shr_oob", by_id)
        self.assertIn("storage_uninit_read", by_id)
        ret_guard = by_id["tb_return_frame_dealloc_protector_conflict"]
        self.assertIn("activeProtectors := 1 :: .nil", ret_guard.sanity_source)
        self.assertIn("targetLocal := 1", ret_guard.sanity_source)


# ----------------------------------------------------------------------
# Round B2 adversarial regression tests
# ----------------------------------------------------------------------


class GuardMutationB2AdversarialTests(unittest.TestCase):
    FIXTURE = "Refute_div_by_zero.lean"
    SPAN = (7, 9)
    KILL = "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\n  rfl\n"

    def _classify(self, rc: int, out: str, stderr: str | None = None) -> str:
        return gmut.classify_refutation_failure(
            rc, out, self.FIXTURE, self.SPAN, stderr_output=stderr
        )[0]

    # -- comment scanner vs strings it cannot lex -----------------------

    def test_scanner_refuses_sources_it_cannot_lex_exactly(self) -> None:
        theorem = "theorem t :\n    1 = 1 :=\n  rfl\n"
        hidden = 'axiom cheat : False\ndef b : String := "-/"\n'
        # In each case Lean sees a complete string and then compiles the
        # `axiom`; the scanner instead believes a block comment started.
        smuggles = {
            "interpolation": 'def a : String := s!"{"/-"}"\n',
            "interpolation ": 'def a : Nat := dbg_trace "{"/-"}"; 0\n',
            "backslash inside a string": 'def a : String := r"\\"\ndef c : String := "/-"\n',
            "raw string literal": 'def a : String := r#"x"/-"#\n',
        }
        for needle, opener in smuggles.items():
            src = "import Trusted.A\n" + opener + hidden + theorem
            code, _ = gmut._strip_lean_comments(src)
            self.assertNotIn("axiom", code, opener)  # the scanner IS fooled
            errors = gmut._fixture_shape_errors("sanity", src, "t")
            self.assertTrue(
                any("unsupported lexical construct" in e and needle.strip() in e for e in errors),
                (opener, errors),
            )

        # Constructs that are refused even though they smuggle nothing here.
        for needle, line in (
            ("character literal", "def c : Char := 'x'\n"),
            ("character literal", "def c : Char := '\\x41'\n"),
            ("guillemet-quoted identifier", "def «odd name» : Nat := 0\n"),
            ("backslash outside a string literal", "def d : Nat := 1 \\ 2\n"),
            ("unterminated string literal", 'def e : String := "abc\n'),
        ):
            src = "import Trusted.A\n" + line + theorem
            errors = gmut._fixture_shape_errors("sanity", src, "t")
            self.assertTrue(
                any("unsupported lexical construct" in e and needle in e for e in errors),
                (line, errors),
            )

        # Plain strings (even ones containing comment delimiters) and
        # identifier primes are lexed exactly and stay accepted.
        fine = (
            "import Trusted.A\n"
            'def msg : String := "-- not a comment /- neither -/"\n'
            "def x' : Nat := 1\n" + theorem
        )
        code, unclosed, hazards = gmut._scan_lean_source(fine)
        self.assertEqual((unclosed, hazards), (False, []))
        self.assertIn("-- not a comment", code)
        self.assertEqual(gmut._fixture_shape_errors("sanity", fine, "t"), [])
        # Hazards carry 1-based line numbers.
        self.assertEqual(
            gmut._scan_lean_source("def a := 1\ndef c := 'x'\n")[2],
            ["line 2: character literal"],
        )

    # -- fixture shape --------------------------------------------------

    def test_fixture_must_be_one_binderless_rfl_theorem(self) -> None:
        head = "import Trusted.A\ndef helper : Nat := 1\n"
        good = head + "theorem t :\n    helper = 1 :=\n  rfl\n"
        reserved = {"evalOperand", "emptyMemory"}
        self.assertEqual(
            gmut._fixture_shape_errors("sanity", good, "t", reserved_names=reserved), []
        )
        bad = {
            # A hypothesis makes the statement vacuous.
            "theorem header must be exactly": head + "theorem t (h : False) :\n    1 = 2 :=\n  rfl\n",
            "theorem header must be exactly ": head + "private theorem t :\n    1 = 1 :=\n  rfl\n",
            "must be proved by": head + "theorem t :\n    1 = 1 :=\n  by decide\n",
            "must be proved by ": head + "theorem t :\n    1 = 1 := rfl\n",
            "must be proved by  ": head + "theorem t :\n    False → 1 = 2 :=\n  fun h => h.elim\n",
            "unsupported top-level command 'section'": "section\n" + good,
            "forbidden token 'variable'": head + "variable (h : 1 = 2)\n" + "theorem t :\n    1 = 2 :=\n  rfl\n",
            "forbidden token 'abbrev'": head + "  abbrev Z := Nat\n" + "theorem t :\n    1 = 1 :=\n  rfl\n",
            "forbidden token 'infix'": head + '  infix:50 " ≈ " => Eq\n' + "theorem t :\n    1 = 1 :=\n  rfl\n",
            "forbidden token 'local'": head + "  local instance : Inhabited Nat := ⟨0⟩\n" + "theorem t :\n    1 = 1 :=\n  rfl\n",
            # A local definition would win over the opened trusted one.
            "`def evalOperand` in sanity_source shadows a trusted declaration": (
                "import Trusted.A\ndef evalOperand : Nat := 1\n"
                "theorem t :\n    evalOperand = 1 :=\n  rfl\n"
            ),
            "`def emptyMemory` in sanity_source shadows": (
                "import Trusted.A\ndef helper : Nat :=\n  1\n  def emptyMemory : Nat := 2\n"
                "theorem t :\n    1 = 1 :=\n  rfl\n"
            ),
            "must be a simple identifier": (
                "import Trusted.A\ndef Foo.bar : Nat := 1\ntheorem t :\n    1 = 1 :=\n  rfl\n"
            ),
            # An import the header parser cannot read is not silently dropped.
            "header parser recognized 1": (
                "import Trusted.A\nimport Ünï.B\ntheorem t :\n    1 = 1 :=\n  rfl\n"
            ),
        }
        for needle, src in bad.items():
            errors = gmut._fixture_shape_errors("sanity", src, "t", reserved_names=reserved)
            self.assertTrue(any(needle.strip() in e for e in errors), (needle, errors))

        # The live catalog reserves the real trusted names.
        guard = gmut.select_guards(guard_filters=["div_by_zero"])[0]
        shadowing = guard.sanity_source.replace(
            "theorem sanity_div_by_zero",
            "def evalScalarBinOp : Nat := 0\n\ntheorem sanity_div_by_zero",
        )
        with mock.patch.object(
            gmut, "MIR_SEMANTICS_GUARDS", _replace_guard("div_by_zero", sanity_source=shadowing)
        ):
            errors = gmut.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertTrue(
            any("`def evalScalarBinOp`" in e and "shadows a trusted declaration" in e for e in errors),
            errors,
        )
        scalars = (
            ANNEAL_ROOT / "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean"
        ).read_text(encoding="utf-8")
        names = gmut._trusted_declaration_names(scalars)
        for expected in ("evalScalarBinOp", "evalSignedDiv", "evalUnaryNot", "scalarModulus"):
            self.assertIn(expected, names)

    # -- refutation classification: stdout vs stderr -------------------

    def test_classify_keeps_stdout_and_stderr_apart(self) -> None:
        self.assertEqual(self._classify(1, self.KILL, ""), "KILLED")
        self.assertEqual(self._classify(1, self.KILL, "note: build finished\n"), "KILLED")
        # Diagnostics that Lean prints on stderr still count.
        self.assertEqual(self._classify(1, "", self.KILL), "KILLED")
        self.assertEqual(
            self._classify(1, "", self.KILL + "  note: type error: expected .ub\n"), "KILLED"
        )

        # An indented error on stderr is NOT a continuation of the stdout
        # diagnostic, whether or not stdout ended with a newline.
        for stdout in (self.KILL, self.KILL.rstrip("\n")):
            for stderr in (
                "  error: wrapper scope setup failed\n",
                "\terror: toolchain missing\n",
                "  lean: error: something\n",
            ):
                self.assertEqual(self._classify(1, stdout, stderr), "ERROR", (stdout, stderr))
        # Indented prose mentioning `error:` is accepted as a diagnostic body
        # ONLY in the same stream, while an indented LEADING `error:` is
        # rejected even in one stream (closing B2's residual risk #3).
        self.assertEqual(
            self._classify(1, self.KILL, "  note: type error: expected .ub\n"),
            "ERROR",
        )
        self.assertEqual(
            self._classify(1, self.KILL + "  note: type error: expected .ub\n"),
            "KILLED",
        )
        self.assertEqual(
            self._classify(1, self.KILL + "  error: wrapper scope setup failed\n"),
            "ERROR",
        )

        # stderr cannot complete a stdout error into a `Type mismatch` on `rfl`.
        cut = "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\n"
        self.assertEqual(self._classify(1, cut, "  rfl\nhas type\n"), "ERROR")
        self.assertEqual(self._classify(1, cut + "  rfl\nhas type\n"), "KILLED")
        # Marker words elsewhere in another error's text are not a kill, in
        # either stream.
        odd = "/t/Refute_div_by_zero.lean:9:2: error: bizarre glitch\n"
        self.assertEqual(self._classify(1, odd, "rfl has type Type mismatch\n"), "ERROR")
        self.assertEqual(self._classify(1, odd + "rfl has type Type mismatch\n"), "ERROR")
        # Non-kill markers and foreign errors on stderr still block a kill.
        self.assertEqual(self._classify(1, self.KILL, "PANIC at Foo\n"), "ERROR")
        self.assertEqual(
            self._classify(1, self.KILL, "/t/Other.lean:1:0: error: boom\n"), "ERROR"
        )

    def test_synthetic_indented_stderr_error_is_not_a_kill(self) -> None:
        fake_sh = (
            'if [ "$IS_MUTANT" = "1" ] && [ "$BASENAME" = "Refute_div_by_zero.lean" ]; then\n'
            "  printf '  error: wrapper scope setup failed\\n' >&2\n"
            "fi\n" + KILL_ALL_FAKE_SH
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            fake = Path(tmp) / "fake_lean"
            _write_fake_lean_sh(fake, fake_sh)
            res = _run_cli(
                [
                    "--lean", str(fake), "--no-lake-cache", "--json",
                    "--guard", "div_by_zero", "--guard", "rem_by_zero",
                ]
            )
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        by_id = {r["guard_id"]: r for r in json.loads(res.stdout)["results"]}
        self.assertEqual(by_id["div_by_zero"]["status"], "ERROR")
        self.assertIn("wrapper scope setup failed", by_id["div_by_zero"]["detail"])
        self.assertEqual(by_id["rem_by_zero"]["status"], "KILLED")

    # -- Lake reuse -----------------------------------------------------

    def test_lake_reuse_pins_transitive_imports_by_content(self) -> None:
        # `A`; `B` imports `A`; `D` imports ONLY `B`.
        sources = {
            "Trusted/A": "def a : Nat := 1\n",
            "Trusted/B": "import Trusted.A\ndef b : Nat := a\n",
            "Trusted/D": "import Trusted.B\ndef d : Nat := b\n",
        }
        mods = tuple(sources)

        def build(tmp: Path, name: str, olean_bytes: dict[str, bytes] | None = None) -> Path:
            root = tmp / name
            for mod, text in sources.items():
                src = root / "trusted/lean" / f"{mod}.lean"
                src.parent.mkdir(parents=True, exist_ok=True)
                src.write_text(text, encoding="utf-8")
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n", encoding="utf-8")
            (root / "lakefile.toml").write_text(TINY_LAKEFILE_TOML, encoding="utf-8")
            _write_lake_build(root, mods, olean_bytes=olean_bytes)
            return root

        with tempfile.TemporaryDirectory(prefix="anneal-gmut-lake-test-") as tmp:
            tmp_path = Path(tmp)
            root = build(tmp_path, "current")
            self.assertEqual(
                gmut._lake_olean_reuse_decision(root, mods), (True, "lake-trace-verified")
            )
            # `A` is rebuilt with different output and `B` is re-recorded
            # against it. `B.olean` happens to be byte-identical, and `D` is
            # NOT rebuilt. Every file keeps a plausible mtime (records of
            # importers are newer than records of their imports).
            rebuilt = build(tmp_path, "rebuilt", {"Trusted/A": b"olean:Trusted/A v2"})
            lib, new_lib = (r / ".lake/build/lib/lean" for r in (root, rebuilt))
            for rel in ("Trusted/A.olean", "Trusted/A.olean.hash", "Trusted/A.trace", "Trusted/B.trace"):
                shutil.copy2(new_lib / rel, lib / rel)
            self.assertEqual(
                (lib / "Trusted/B.olean").read_bytes(), (new_lib / "Trusted/B.olean").read_bytes()
            )
            self.assertLess(
                (lib / "Trusted/B.trace").stat().st_mtime_ns,
                (lib / "Trusted/D.trace").stat().st_mtime_ns,
            )
            self.assertEqual(
                gmut._lake_olean_reuse_decision(root, mods),
                (False, "Trusted/D: built against different transitive imports of Trusted/B"),
            )
            # `A` and `B` on their own are a consistent build.
            self.assertTrue(gmut._lake_olean_reuse_decision(root, mods[:2])[0])

        # A build made with non-default options or arguments is not reused,
        # because mutants are compiled by plain `lean`.
        for mutate in (
            lambda t: t["inputs"].__setitem__(3, ["options", "1" * 16]),
            lambda t: t["inputs"].__setitem__(4, ["Module.leanArgs: #[-DautoImplicit=true]", "2" * 16]),
            lambda t: t["inputs"].pop(4),
        ):
            with tempfile.TemporaryDirectory(prefix="anneal-gmut-lake-test-") as tmp:
                root = build(Path(tmp), "opts")
                trace_path = root / ".lake/build/lib/lean/Trusted/B.trace"
                trace = json.loads(trace_path.read_text(encoding="utf-8"))
                mutate(trace)
                trace_path.write_text(json.dumps(trace), encoding="utf-8")
                self.assertEqual(
                    gmut._lake_olean_reuse_decision(root, mods),
                    (False, "Trusted/B: built with non-default Lean options or arguments"),
                )

    def test_replaced_olean_with_intact_hash_and_trace_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            tmp_path = Path(tmp)
            root = _make_tcb_copy_root(tmp_path)
            _write_lake_build(root, ALL_TCB_MODULES)
            fake = tmp_path / "fake_lean"
            _write_fake_lean_sh(fake, KILL_ALL_FAKE_SH)
            base = ["--anneal-root", str(root), "--lean", str(fake), "--guard", "div_by_zero", "--json"]

            res = _run_cli(base)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertTrue(json.loads(res.stdout)["used_lake_cache"])

            # Swap in a different `.olean` that is OLDER than its `.hash`
            # file (a rename, `cp -p`, or a bad artifact restored from the
            # Lake cache). `.olean.hash` and `.trace` are untouched.
            state = root / ".lake/build/lib/lean/Trusted/Rustc/V2026_06_01/MirSemantics/State.olean"
            state.write_bytes(b"some other olean")
            os.utime(state, (1000, 1000))

            res = _run_cli(base)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            report = json.loads(res.stdout)
            self.assertFalse(report["used_lake_cache"])
            self.assertIn("State: `.olean` bytes do not match", report["lake_cache_detail"])

            # The explicit opt-out restores the mtime-only trust rule.
            res = _run_cli([*base, "--trust-lake-olean-hash-files"])
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertTrue(json.loads(res.stdout)["used_lake_cache"])

            # Re-hashing is the only default: there is no flag to ask for it,
            # and flags cannot be abbreviated.
            for bad_flag in ("--verify-lake-olean-bytes", "--trust-lake"):
                res = _run_cli([*base, bad_flag])
                self.assertEqual(res.returncode, 2, bad_flag)

    def test_bulk_murmur_matches_the_block_by_block_hash(self) -> None:
        rng = random.Random(20261123)
        sizes = [0, 1, 7, 8, 9, 63, 64, 4095, 4096, 4097, 4103, 8192, 12345]
        # Force several bulk chunks, including a short final chunk and a
        # chunk boundary that falls exactly on the end of the data.
        with (
            mock.patch.object(gmut, "_MURMUR_BULK_MIN_BLOCKS", 1),
            mock.patch.object(gmut, "_MURMUR_BULK_BLOCKS", 7),
        ):
            for size in [*sizes, 7 * 8, 7 * 8 * 3, 7 * 8 * 3 + 5]:
                data = rng.randbytes(size)
                for seed in (11, 0, 2**64 - 1):
                    self.assertEqual(
                        gmut._lean_murmur_hash64a(data, seed),
                        gmut._lean_murmur_hash64a_simple(data, seed),
                        (size, seed),
                    )
        # Default thresholds: one byte either side of where the bulk path
        # starts, and data spanning more than one default chunk.
        edge = gmut._MURMUR_BULK_MIN_BLOCKS * 8
        chunk = gmut._MURMUR_BULK_BLOCKS * 8
        for size in (edge - 1, edge, edge + 1, chunk + 13, 2 * chunk):
            data = rng.randbytes(size)
            self.assertEqual(
                gmut._lean_murmur_hash64a(data), gmut._lean_murmur_hash64a_simple(data), size
            )
        # Worst case for lane arithmetic: every block is all ones.
        ones = b"\xff" * (edge + 24)
        self.assertEqual(
            gmut._lean_murmur_hash64a(ones), gmut._lean_murmur_hash64a_simple(ones)
        )
        # The Lake-recorded ground truth still holds through the public API.
        self.assertEqual(
            gmut.lake_hash_of_text(b"5045d0056413266e57c625dcd7c365b10e377c52"),
            "e9f3658beb070375",
        )

    def test_lakefile_must_be_default_for_any_lake_reuse(self) -> None:
        # Lake does not record weak arguments in its traces at all, so the
        # lakefile itself must be the modelled default, synthetic trace or not.
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-lake-test-") as tmp:
            root, mods = _make_tiny_lake_root(Path(tmp))
            self.assertEqual(
                gmut._lake_olean_reuse_decision(root, mods), (True, "lake-trace-verified")
            )
            (root / "lakefile.toml").write_text(
                TINY_LAKEFILE_TOML + 'weakLeanArgs = ["-DautoImplicit=true"]\n', encoding="utf-8"
            )
            ok, why = gmut._lake_olean_reuse_decision(root, mods)
            self.assertFalse(ok)
            self.assertIn("unsupported key(s)", why)
            self.assertIn("weakLeanArgs", why)

            (root / "lakefile.toml").write_text(TINY_LAKEFILE_TOML, encoding="utf-8")
            with mock.patch.object(gmut, "tomllib", None):
                ok, why = gmut._lake_olean_reuse_decision(root, mods)
            self.assertFalse(ok)
            self.assertIn("tomllib", why)

            (root / "lakefile.toml").unlink()
            ok, why = gmut._lake_olean_reuse_decision(root, mods)
            self.assertFalse(ok)
            self.assertIn("cannot read lakefile.toml", why)

    # -- header parser completeness -------------------------------------

    def test_header_parser_reports_imports_it_cannot_read(self) -> None:
        self.assertEqual(
            gmut._parse_lean_header_ex("import Trusted.A\nimport Trusted.B\ndef x := 1\n"),
            (False, ["Trusted/A", "Trusted/B"], True),
        )
        self.assertEqual(
            gmut._parse_lean_header_ex(
                "import Trusted.A -- note\n/- c -/ import Trusted.B/- c -/\nnamespace X\n"
            ),
            (False, ["Trusted/A", "Trusted/B"], True),
        )
        # Lean accepts every one of these headers in full; the parser cannot
        # read one name and would silently drop the imports after it.
        for src in (
            "import Trusted.A\nimport Ünï.B\nimport Trusted.C\n",
            "import Trusted.Ünï\nimport Trusted.C\n",
            "import Trusted.A\npublic import all Ünï\nimport Trusted.C\n",
            "import Trusted.A?\nimport Trusted.C\n",
        ):
            _, imports, complete = gmut._parse_lean_header_ex(src)
            self.assertFalse(complete, src)
            self.assertNotIn("Trusted/C", imports, src)

        # Nothing that relies on a trusted file's import list accepts it.
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            root = _make_tcb_copy_root(Path(tmp))
            _write_lake_build(root, ALL_TCB_MODULES)
            self.assertEqual(gmut.validate_catalog_invariants(root), [])
            self.assertTrue(gmut._lake_olean_reuse_decision(root, ALL_TCB_MODULES)[0])
            seq = root / "trusted/lean/Trusted/Sequence.lean"
            seq.write_text(
                "import Ünï.Hidden\n" + seq.read_text(encoding="utf-8"), encoding="utf-8"
            )
            errors = gmut.validate_catalog_invariants(root)
            self.assertTrue(
                any("cannot parse every import of trusted module Trusted/Sequence" in e for e in errors),
                errors,
            )
            self.assertEqual(
                gmut._lake_olean_reuse_decision(root, ALL_TCB_MODULES),
                (False, "Trusted/Sequence: cannot parse every import of the source"),
            )

    # -- catalog boundary tightness ------------------------------------

    def test_shift_guards_are_refuted_exactly_at_the_boundary(self) -> None:
        by_id = {g.guard_id: g for g in gmut.MIR_SEMANTICS_GUARDS}
        operands = re.compile(r"Unchecked ⟨(\d+), (\d+)⟩ ⟨(\d+), (\d+)⟩")

        def shift_and_bits(source: str) -> tuple[int, int]:
            match = operands.search(source)
            assert match is not None, source
            return (int(match.group(3)), 8 * int(match.group(2)))

        for full, edge in (("shift_oob", "shl_oob_off_by_one"), ("shr_oob", "shr_oob_off_by_one")):
            # The boundary mutant weakens `numBits <= b` to `numBits < b`.
            self.assertEqual(by_id[edge].anchor, by_id[full].anchor)
            self.assertIn("Nat.ble numBits b", by_id[edge].anchor)
            self.assertEqual(
                by_id[edge].replacement,
                by_id[edge].anchor.replace("Nat.ble numBits b", "Nat.blt numBits b"),
            )
            for guard_id in (full, edge):
                shift, bits = shift_and_bits(by_id[guard_id].refute_source)
                # `b == numBits`: the smallest UB shift. `b > numBits` would
                # let the `<` mutant survive.
                self.assertEqual(shift, bits, guard_id)
                shift, bits = shift_and_bits(by_id[guard_id].sanity_source)
                self.assertLess(shift, bits, guard_id)
            # The boundary mutant's sanity sits on the last defined shift.
            shift, bits = shift_and_bits(by_id[edge].sanity_source)
            self.assertEqual(shift, bits - 1, edge)


class GuardMutationA2AdversarialTests(unittest.TestCase):
    FIXTURE = "Refute_div_by_zero.lean"
    SPAN = (7, 9)

    # -- vacuous & swapped fixture statement checks --------------------

    def test_vacuous_and_swapped_fixture_statements_are_rejected(self) -> None:
        guard = gmut.select_guards(guard_filters=["div_by_zero"])[0]
        semantics_fns = {"evalScalarBinOp"}

        # Syntactically reflexive `X = X := rfl` is rejected.
        refl_src = guard.sanity_source.replace(
            ".ok (.scalar ⟨7, 1⟩) .nil emptyMemory",
            "evalScalarBinOp .div ⟨42, 1⟩ ⟨6, 1⟩ .nil emptyMemory false",
        )
        errs = gmut._fixture_statement_errors(
            "sanity", refl_src, guard.sanity_theorem_name, semantics_fn_names=semantics_fns
        )
        self.assertTrue(any("syntactically reflexive" in e for e in errs), errs)

        # Arithmetic-only `1 + 1 = 2 := rfl` with no semantics call on LHS is rejected.
        no_tcb = (
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "theorem sanity_div_by_zero :\n"
            "    1 + 1 = 2 :=\n"
            "  rfl\n"
        )
        errs = gmut._fixture_statement_errors(
            "sanity", no_tcb, "sanity_div_by_zero", semantics_fn_names=semantics_fns
        )
        self.assertTrue(any("LHS must apply a trusted MirSemantics function" in e for e in errs), errs)

        # `let` / `fun` inside theorem statement is rejected.
        let_src = (
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "theorem sanity_div_by_zero :\n"
            "    let x := evalScalarBinOp .div ⟨42, 1⟩ ⟨6, 1⟩ .nil emptyMemory false\n"
            "    x = x :=\n"
            "  rfl\n"
        )
        errs = gmut._fixture_statement_errors(
            "sanity", let_src, "sanity_div_by_zero", semantics_fn_names=semantics_fns
        )
        self.assertTrue(any("must not contain `let`, `fun` or `λ`" in e for e in errs), errs)

        # Swapped outcomes: refute NOT asserting UB, or sanity asserting UB.
        swapped_refute = guard.sanity_source.replace(
            guard.sanity_theorem_name, guard.theorem_name
        )
        swapped_sanity = guard.refute_source.replace(
            guard.theorem_name, guard.sanity_theorem_name
        )
        with mock.patch.object(
            gmut,
            "MIR_SEMANTICS_GUARDS",
            _replace_guard("div_by_zero", refute_source=swapped_refute),
        ):
            cat_errs = gmut.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertTrue(any("RHS must assert UB" in e for e in cat_errs), cat_errs)

        with mock.patch.object(
            gmut,
            "MIR_SEMANTICS_GUARDS",
            _replace_guard("div_by_zero", sanity_source=swapped_sanity),
        ):
            cat_errs = gmut.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertTrue(any("must not mention `ub`" in e for e in cat_errs), cat_errs)

    # -- constructor & core-name shadowing -----------------------------

    def test_constructor_and_core_shadowing_rejected(self) -> None:
        guard = gmut.select_guards(guard_filters=["div_by_zero"])[0]
        for shadowed in ("ub", "fail", "rfl", "Trusted", "Nat"):
            bad = guard.sanity_source.replace(
                "theorem sanity_div_by_zero",
                f"def {shadowed} : Nat := 0\n\ntheorem sanity_div_by_zero",
            )
            with mock.patch.object(
                gmut,
                "MIR_SEMANTICS_GUARDS",
                _replace_guard("div_by_zero", sanity_source=bad),
            ):
                errors = gmut.validate_catalog_invariants(ANNEAL_ROOT)
            self.assertTrue(
                any(f"def {shadowed}" in e and "shadows" in e for e in errors),
                (shadowed, errors),
            )

    # -- same-stream indented error & CR/LF classifier hardening -------

    def test_classify_rejects_same_stream_indented_leading_error_and_handles_cr(self) -> None:
        kill = "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\n  rfl\n"
        # Same-stream indented prose mentioning `error:` stays KILLED.
        self.assertEqual(
            gmut.classify_refutation_failure(
                1,
                kill + "  note: type error: expected .ub\n",
                self.FIXTURE,
                self.SPAN,
                stderr_output="",
            )[0],
            "KILLED",
        )
        # Same-stream indented LEADING `  error:` / `  error(...):` is ERROR.
        for bad_indented in (
            "  error: unlocated failure on same stream\n",
            "\terror(lean.foo): nested unlocated failure\n",
        ):
            self.assertEqual(
                gmut.classify_refutation_failure(
                    1,
                    kill + bad_indented,
                    self.FIXTURE,
                    self.SPAN,
                    stderr_output="",
                )[0],
                "ERROR",
                bad_indented,
            )
        # CRLF and bare CR do not desync `stream_break` or diagnostic headers.
        crlf_kill = "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\r\n  rfl\r\n"
        self.assertEqual(
            gmut.classify_refutation_failure(
                1, crlf_kill, self.FIXTURE, self.SPAN, stderr_output=""
            )[0],
            "KILLED",
        )
        # Bare `\r` before a foreign error is normalized so it cannot slip past.
        self.assertEqual(
            gmut.classify_refutation_failure(
                1,
                kill,
                self.FIXTURE,
                self.SPAN,
                stderr_output="progress\r/t/Other.lean:1:0: error: boom\n",
            )[0],
            "ERROR",
        )

    # -- unclosed header comment & duplicate/non-Trusted Lake traces ---

    def test_unclosed_header_comment_and_duplicate_or_extra_trace_entries(self) -> None:
        self.assertEqual(
            gmut._parse_lean_header_ex("/- unclosed header\nimport Trusted.A\n"),
            (False, [], False),
        )

        # Duplicate options / leanArgs / non-Trusted imports / conflicting
        # duplicate imports inside `synthetic: false` traces all fail closed.
        def check_mutated_c(fn: object, expected_substr: str) -> None:
            with tempfile.TemporaryDirectory(prefix="anneal-gmut-a2-trace-") as tmp:
                root, mods = _make_tiny_lake_root(Path(tmp))
                tr_path = root / ".lake/build/lib/lean/Trusted/C.trace"
                trace = json.loads(tr_path.read_text(encoding="utf-8"))
                fn(trace)  # type: ignore[operator]
                tr_path.write_text(json.dumps(trace), encoding="utf-8")
                ok, why = gmut._lake_olean_reuse_decision(root, mods)
                self.assertFalse(ok, expected_substr)
                self.assertIn(expected_substr, why)

        # Duplicate `options` where non-default precedes nil (would fool `dict()`).
        check_mutated_c(
            lambda t: t["inputs"].insert(0, ["options", "deadbeefdeadbeef"]),
            "non-default Lean options or arguments",
        )
        # Duplicate `Module.leanArgs:` with non-empty args alongside `#[]`.
        check_mutated_c(
            lambda t: t["inputs"].insert(0, ['Module.leanArgs: #["-Dfoo=1"]', "deadbeefdeadbeef"]),
            "non-default Lean options or arguments",
        )
        # Extra non-Trusted entry smuggled inside `imports_node`.
        check_mutated_c(
            lambda t: t["inputs"][0][1][0][1].append(["Anneal.Sneaky:importAllArts", "0" * 16]),
            "unrecognized imports record",
        )
        # Conflicting duplicate import entry inside `imports_node`.
        check_mutated_c(
            lambda t: t["inputs"][0][1][0][1].insert(0, ["Trusted.A:importAllArts", "0" * 16]),
            "conflicting duplicate import record",
        )

    # -- mutated TCB sorry rejection & new Statements.lean guards ------

    def test_mutated_tcb_sorry_warning_is_error_and_new_statements_guards(self) -> None:
        fake_sh = textwrap.dedent(
            """\
            if [ -n "$OUT" ]; then
              mkdir -p "$(dirname "$OUT")"
              printf 'fake-olean' > "$OUT"
            fi
            if [ "$IS_MUTANT" = "1" ] && [ "$BASENAME" = "Scalars.lean" ]; then
              printf '%s:10:0: warning: declaration uses `sorry`\\n' "$SRC"
            fi
            exit 0
            """
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-a2-sorry-") as tmp:
            fake = Path(tmp) / "fake_lean"
            _write_fake_lean_sh(fake, fake_sh)
            res = _run_cli(
                ["--lean", str(fake), "--no-lake-cache", "--guard", "div_by_zero", "--json"]
            )
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        report = json.loads(res.stdout)
        self.assertEqual((report["killed"], report["errors"]), (0, 1))
        self.assertIn("mutated semantics module", report["results"][0]["detail"])

        # Catalog now covers 18 guards including both new Statements.lean guards.
        self.assertGreaterEqual(len(gmut.MIR_SEMANTICS_GUARDS), 18)
        by_id = {g.guard_id: g for g in gmut.MIR_SEMANTICS_GUARDS}
        self.assertIn("intrinsic_assume_invalid_bool", by_id)
        self.assertIn("copy_nonoverlapping_place_overlap", by_id)
        # `intrinsic_assume_invalid_bool` weakens `== 1` to `!= 0` and tests bit pattern 2.
        self.assertIn("Bool.not (Nat.beq sc.bits 0)", by_id["intrinsic_assume_invalid_bool"].replacement)
        self.assertIn("⟨2, 1⟩", by_id["intrinsic_assume_invalid_bool"].refute_source)
        # `copy_nonoverlapping_place_overlap` keeps same-tag check intact and uses distinct tags 1 & 2.
        self.assertIn("Nat.beq srcPtr.tag dstPtr.tag", by_id["copy_nonoverlapping_place_overlap"].replacement)
        self.assertIn("tag := 1, targetLocal := 0", by_id["copy_nonoverlapping_place_overlap"].refute_source)
        self.assertIn("tag := 2, targetLocal := 0", by_id["copy_nonoverlapping_place_overlap"].refute_source)


class GuardMutationB3AdversarialTests(unittest.TestCase):
    """Round 3: statement shape, classifier bodies, CLI selectors, interrupts."""

    FIXTURE = "Refute_div_by_zero.lean"
    SPAN = (7, 9)
    HEADER = "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"

    def _stmt_errors(self, kind: str, body: str, helpers: str = "") -> list[str]:
        src = f"{self.HEADER}{helpers}theorem t :\n{body} :=\n  rfl\n"
        return gmut._fixture_statement_errors(
            kind, src, "t", semantics_fn_names={"evalStmt", "evalOperand"}
        )

    # -- the statement must evaluate the semantics, on the LHS only ----

    def test_statement_evaluates_semantics_on_lhs_and_compares_with_data(self) -> None:
        # Valid shapes: multi-line, nested structure instances, `=` inside a
        # string, brackets or a compound operator.
        self.assertEqual(
            self._stmt_errors("refute", "    evalStmt s stmt = MirStepNode.fail .ub"), []
        )
        self.assertEqual(
            self._stmt_errors(
                "sanity",
                '    evalStmt\n      { frame := f, memory := m }\n'
                '      { kind := .nop, span := "a = b" } =\n'
                "      MirStepNode.step { frame := g (x == y), memory := m }",
            ),
            [],
        )

        # Helper-alias reflexivity: the RHS is the evaluation under another
        # name, so `rfl` would prove it on every mutant.
        alias = self._stmt_errors(
            "sanity",
            "    evalStmt s stmt = expected",
            helpers="def expected : MirStepNode :=\n  evalStmt s stmt\n\n",
        )
        self.assertTrue(any("outside the theorem LHS" in e for e in alias), alias)
        # ... also through `open ... renaming`, or inline on the RHS.
        renamed = self._stmt_errors(
            "sanity",
            "    evalStmt s stmt = run s stmt",
            helpers="open Trusted.Rustc.V2026_06_01.MirSemantics renaming evalStmt → run\n",
        )
        self.assertTrue(any("outside the theorem LHS" in e for e in renamed), renamed)
        inline = self._stmt_errors("sanity", "    evalStmt s stmt = id (evalStmt s stmt)")
        self.assertTrue(any("outside the theorem LHS" in e for e in inline), inline)

        # The LHS head must be a semantics function, not merely mention one or
        # a trusted type (`MirStepNode`), and must be written unqualified.
        for lhs in (
            "Prod.fst (MirStepNode.fail .ub, evalStmt s stmt)",
            "id (MirStepNode.fail .ub)",
            "(evalStmt s stmt)",
            "MirSemantics.evalStmt s stmt",
            "evalStmt.helper s stmt",
            "helperValue",
        ):
            errs = self._stmt_errors("refute", f"    {lhs} = MirStepNode.fail .ub")
            self.assertTrue(
                any("LHS must apply a trusted MirSemantics function" in e for e in errs),
                (lhs, errs),
            )

        # Not a single unparenthesized top-level equality.
        for body in (
            "    Eq (evalStmt s stmt) (MirStepNode.fail .ub)",
            "    evalStmt s stmt ≠ MirStepNode.unsupported",
            "    True",
            "    (evalStmt s stmt = MirStepNode.fail .ub)",
            "    evalStmt s stmt = MirStepNode.fail .ub ∨ 1 = 1",
            "    evalStmt s stmt == MirStepNode.fail .ub",
        ):
            errs = self._stmt_errors("refute", body)
            self.assertTrue(any("exactly one top-level `=`" in e for e in errs), (body, errs))
        self.assertTrue(
            any("empty LHS or RHS" in e for e in self._stmt_errors("refute", "    = .ub"))
        )
        errs = self._stmt_errors("sanity", "    evalStmt ((λ x => x) s) stmt = MirStepNode.step s")
        self.assertTrue(any("`let`, `fun` or `λ`" in e for e in errs), errs)

        # A statement that cannot be extracted is an error, never a pass.
        one_line = f"{self.HEADER}theorem t : evalStmt s stmt = .ub := rfl\n"
        for src, name in ((one_line, "t"), (one_line, "missing")):
            errs = gmut._fixture_statement_errors(
                "refute", src, name, semantics_fn_names={"evalStmt"}
            )
            self.assertEqual(len(errs), 1, errs)
            self.assertIn("cannot extract the statement", errs[0])

    def test_sanity_cannot_assert_ub_in_any_spelling(self) -> None:
        for rhs in (".ub", "(.ub)", "MirStepNode.fail (.ub)", ".fail .ub", "MirStepNode.fail MirError.ub"):
            errs = self._stmt_errors("sanity", f"    evalStmt s stmt = {rhs}")
            self.assertTrue(any("must not mention `ub`" in e for e in errs), (rhs, errs))
        # ... nor through a data helper.
        errs = self._stmt_errors(
            "sanity",
            "    evalStmt s stmt = expected",
            helpers="def expected : MirStepNode :=\n  MirStepNode.fail .ub\n\n",
        )
        self.assertTrue(any("must not mention `ub`" in e for e in errs), errs)
        # A refutation accepts only the literal UB spellings.
        for rhs in ("(.ub)", "expected", "MirStepNode.unsupported"):
            errs = self._stmt_errors("refute", f"    evalStmt s stmt = {rhs}")
            self.assertTrue(any("RHS must assert UB" in e for e in errs), (rhs, errs))
        # Identifiers that merely contain `ub` are not UB.
        self.assertEqual(
            self._stmt_errors("sanity", "    evalStmt s stmt = MirStepNode.step subState"), []
        )

    def test_live_catalog_rejects_alias_sanity_and_passes_as_is(self) -> None:
        self.assertEqual(gmut.validate_catalog_invariants(ANNEAL_ROOT), [])
        guard = gmut.select_guards(guard_filters=["div_by_zero"])[0]
        call = "evalScalarBinOp .div ⟨42, 1⟩ ⟨6, 1⟩ .nil emptyMemory false"
        self.assertIn(call, guard.sanity_source)
        alias_src = guard.sanity_source.replace(
            "theorem sanity_div_by_zero",
            f"def expected :=\n  {call}\n\ntheorem sanity_div_by_zero",
        ).replace(".ok (.scalar ⟨7, 1⟩) .nil emptyMemory", "expected")
        with mock.patch.object(
            gmut,
            "MIR_SEMANTICS_GUARDS",
            _replace_guard("div_by_zero", sanity_source=alias_src),
        ):
            errors = gmut.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertTrue(
            any("['evalScalarBinOp'] outside the theorem LHS" in e for e in errors), errors
        )

    # -- classifier: `error:` text inside a pretty-printed goal --------

    def test_classify_error_text_inside_goal_terms_is_still_a_kill(self) -> None:
        head = "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\n  rfl\nhas type\n"
        for body_line in (
            '  evalStmt s { kind := .nop, span := "error: boom" } = MirStepNode.fail .ub\n',
            '  "error: boom"\n',
            '    span := "lexer error: unexpected character" }\n',
            "  error : Nat\n",
            "  errorCode: 3\n",
        ):
            self.assertEqual(
                gmut.classify_refutation_failure(
                    1, head + body_line, self.FIXTURE, self.SPAN, stderr_output=""
                )[0],
                "KILLED",
                body_line,
            )
        # A bare `error:` that opens a line is an unlocated error wherever it
        # sits, indented or not. Lean never prints a goal line like this (a
        # string is quoted, a binder is `error : T`), so this fails closed.
        for body_line in ("  error: boom\n", "error: boom\n", "lean: error: boom\n"):
            self.assertEqual(
                gmut.classify_refutation_failure(
                    1, head + body_line, self.FIXTURE, self.SPAN, stderr_output=""
                )[0],
                "ERROR",
                body_line,
            )

    # -- CLI: selectors, report schema, fail-closed sink, interrupts ---

    def test_guard_selectors_accept_comma_lists_and_fail_closed(self) -> None:
        ids = [
            g.guard_id
            for g in gmut.select_guards(guard_filters=["shift_oob, signed_", "shift_oob"])
        ]
        self.assertEqual(ids, ["signed_div_overflow", "signed_rem_overflow", "shift_oob"])
        for bad, needle in (
            (["div_by_zero,"], "must be non-empty"),
            ([",,"], "must be non-empty"),
            (["div_by_zero,no_such_guard"], "no cataloged guard matched --guard 'no_such_guard'"),
        ):
            with self.assertRaisesRegex(ValueError, re.escape(needle)):
                gmut.select_guards(guard_filters=bad)
        # All three `assume` guards mutate the same line in different ways.
        assume = gmut.select_guards(guard_filters=["intrinsic_assume"])
        self.assertEqual(len(assume), 3)
        self.assertEqual(len({g.anchor for g in assume}), 1)
        self.assertEqual(len({g.replacement for g in assume}), 3)
        size_guard = next(g for g in assume if g.guard_id == "intrinsic_assume_non_bool_size")
        self.assertNotIn("sc.sizeBytes", size_guard.replacement)
        self.assertIn("match Nat.beq sc.bits 1 with", size_guard.replacement)
        # Bit pattern 1 in a 4-byte scalar: only the size check makes it UB.
        self.assertIn(".init (.scalar ⟨1, 4⟩)", size_guard.refute_source)

        # Likewise the two place-overlap guards of `evalCopySingleDirect`: one
        # drops the same-local check, the other keeps it for whole locals only.
        place, subplace = gmut.select_guards(
            guard_filters=["copy_nonoverlapping_place_overlap,copy_nonoverlapping_subplace_overlap"]
        )
        self.assertEqual(place.anchor, subplace.anchor)
        self.assertNotEqual(place.replacement, subplace.replacement)
        self.assertNotIn("projectionsOverlap", subplace.replacement)
        self.assertIn("        | .nil, .nil => true\n        | _, _ => false\n", subplace.replacement)
        # Source borrows field 0 of local 0, destination borrows all of it.
        self.assertIn("targetProjection := fieldZero :: .nil", subplace.refute_source)
        self.assertIn("tag := 2, targetLocal := 0, targetProjection := .nil", subplace.refute_source)
        self.assertEqual(len(gmut.MIR_SEMANTICS_GUARDS), 20)

    def test_report_schema_is_the_same_for_finished_and_fatal_runs(self) -> None:
        fatal_keys = set(gmut._fatal_report("all", "boom"))
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            fake = Path(tmp) / "fake_lean"
            _write_fake_lean_sh(fake, KILL_ALL_FAKE_SH)
            base = ["--lean", str(fake), "--no-lake-cache", "--json"]
            green = _run_cli([*base, "--guard", "div_by_zero,rem_by_zero"])
            fatal = _run_cli([*base, "--guard", "no_such_guard_xyz"])
            survivor_fake = Path(tmp) / "fake_lean_survivor"
            _write_fake_lean_sh(
                survivor_fake,
                'if [ -n "$OUT" ]; then mkdir -p "$(dirname "$OUT")"; printf x > "$OUT"; fi\nexit 0',
            )
            red = _run_cli(
                ["--lean", str(survivor_fake), "--no-lake-cache", "--json", "--guard", "div_by_zero"]
            )
        green_report = json.loads(green.stdout)
        fatal_report = json.loads(fatal.stdout)
        red_report = json.loads(red.stdout)
        self.assertEqual(set(green_report), fatal_keys)
        self.assertEqual(set(fatal_report), fatal_keys)
        self.assertEqual(
            (green.returncode, green_report["ok"], green_report["fatal_error"], green_report["total"]),
            (0, True, None, 2),
        )
        self.assertEqual((fatal.returncode, fatal_report["ok"]), (1, False))
        self.assertIn("no cataloged guard matched", fatal_report["fatal_error"])
        self.assertEqual(
            (red.returncode, red_report["ok"], red_report["fatal_error"], red_report["survived"]),
            (1, False, None, 1),
        )

    def test_json_out_holds_a_failing_report_until_the_run_reports(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            fake = Path(tmp) / "fake_lean"
            _write_fake_lean_sh(fake, KILL_ALL_FAKE_SH)
            out = Path(tmp) / "report.json"
            argv = [
                "--lean", str(fake), "--no-lake-cache",
                "--guard", "div_by_zero", "--json-out", str(out),
            ]
            # A stale green report from an earlier run ...
            out.write_text(json.dumps({"ok": True, "killed": 1, "total": 1}), encoding="utf-8")
            # ... must not survive a run that dies without reporting.
            with mock.patch.object(
                gmut, "run_guard_mutation_suite", side_effect=KeyError("boom")
            ):
                with self.assertRaises(KeyError):
                    gmut.main(argv)
            report = json.loads(out.read_text(encoding="utf-8"))
            self.assertEqual((report["ok"], report["errors"]), (False, 1))
            self.assertEqual(report["fatal_error"], "run did not complete")

            # An unwritable sink is fatal before any Lean runs.
            res = _run_cli(
                [*argv[:-1], str(Path(tmp) / "fake_lean" / "report.json"), "--json"]
            )
            self.assertEqual(res.returncode, 1)
            self.assertEqual(res.stderr.count("cannot write"), 1, res.stderr)
            self.assertIn("cannot write", json.loads(res.stdout)["fatal_error"])

    def test_sigterm_and_sigint_kill_lean_and_remove_temp_dirs(self) -> None:
        fake_sh = (
            'if [ -n "$OUT" ]; then mkdir -p "$(dirname "$OUT")"; printf x > "$OUT"; fi\n'
            'if [ "$IS_MUTANT" = "1" ]; then\n'
            '  echo "$$" > "$GMUT_TEST_PIDFILE"\n'
            "  sleep 60\n"
            "fi\n"
            "exit 0"
        )
        for sig in (signal.SIGTERM, signal.SIGINT):
            with tempfile.TemporaryDirectory(prefix="b3-interrupt-") as tmp:
                tmp_path = Path(tmp)
                fake = tmp_path / "fake_lean"
                _write_fake_lean_sh(fake, fake_sh)
                tmp_root = tmp_path / "tmp"
                tmp_root.mkdir()
                pidfile = tmp_path / "lean.pid"
                out = tmp_path / "report.json"
                out.write_text(json.dumps({"ok": True}), encoding="utf-8")
                env = os.environ.copy()
                env.update({"TMPDIR": str(tmp_root), "GMUT_TEST_PIDFILE": str(pidfile)})
                proc = subprocess.Popen(
                    [
                        sys.executable, "-B", str(SCRIPT),
                        "--lean", str(fake), "--no-lake-cache",
                        "--guard", "div_by_zero", "--json-out", str(out),
                    ],
                    env=env,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                )
                try:
                    deadline = time.monotonic() + 30
                    while not (pidfile.is_file() and pidfile.read_text().strip()):
                        self.assertIsNone(proc.poll(), "CLI exited before the mutant compile")
                        self.assertLess(time.monotonic(), deadline, "fake Lean never started")
                        time.sleep(0.01)
                    lean_pid = int(pidfile.read_text().strip())
                    self.assertTrue(_list_gmut_temp_dirs(tmp_root))
                    proc.send_signal(sig)
                    _, stderr = proc.communicate(timeout=30)
                finally:
                    if proc.poll() is None:
                        proc.kill()
                        proc.communicate()
                self.assertEqual(proc.returncode, gmut.EXIT_INTERRUPTED, stderr)
                self.assertIn(f"interrupted by {sig.name}", stderr)
                self.assertNotIn("Traceback", stderr)
                report = json.loads(out.read_text(encoding="utf-8"))
                self.assertFalse(report["ok"])
                self.assertEqual(report["fatal_error"], f"interrupted by {sig.name}")
                # Nothing leaked: no temp dir, and the sleeping Lean is gone.
                self.assertEqual(_list_gmut_temp_dirs(tmp_root), set())
                deadline = time.monotonic() + 10
                while True:
                    try:
                        os.kill(lean_pid, 0)
                    except ProcessLookupError:
                        break
                    self.assertLess(time.monotonic(), deadline, "Lean survived the interrupt")
                    time.sleep(0.01)

    def test_termination_signals_are_only_taken_over_when_default(self) -> None:
        for sig in (signal.SIGTERM, signal.SIGHUP):
            before = signal.getsignal(sig)
            try:
                # `nohup` / an embedding program: an ignored signal stays ignored.
                signal.signal(sig, signal.SIG_IGN)
                with gmut._termination_signals_as_interrupt():
                    self.assertIs(signal.getsignal(sig), signal.SIG_IGN)
                self.assertIs(signal.getsignal(sig), signal.SIG_IGN)
                # A default action is replaced for the duration only.
                signal.signal(sig, signal.SIG_DFL)
                with self.assertRaisesRegex(KeyboardInterrupt, sig.name):
                    with gmut._termination_signals_as_interrupt():
                        os.kill(os.getpid(), sig)
                        time.sleep(5)  # the handler interrupts this sleep
                self.assertIs(signal.getsignal(sig), signal.SIG_DFL)
            finally:
                signal.signal(sig, before)


class GuardMutationA3AdversarialTests(unittest.TestCase):
    """Round 3 A3 audit: subplace sanity, target-module/LHS/rfl tightening, signals."""

    FIXTURE = "Refute_div_by_zero.lean"
    SPAN = (7, 9)
    HEADER = "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"

    def _stmt_errors(
        self,
        kind: str,
        body: str,
        helpers: str = "",
        *,
        semantics_fn_names: set[str] | None = None,
        target_fn_names: set[str] | None = None,
    ) -> list[str]:
        src = f"{self.HEADER}{helpers}theorem t :\n{body} :=\n  rfl\n"
        return gmut._fixture_statement_errors(
            kind,
            src,
            "t",
            semantics_fn_names=semantics_fn_names or {"evalStmt", "evalOperand"},
            target_fn_names=target_fn_names,
        )

    # -- same-local disjoint sub-field sanity for subplace overlap -----

    def test_subplace_overlap_sanity_exercises_same_local_disjoint_fields(self) -> None:
        guard = gmut.select_guards(
            guard_filters=["copy_nonoverlapping_subplace_overlap"]
        )[0]
        # Both source and destination borrows target local 0 with distinct
        # field projections (.field 0 vs .field 1), so the positive sanity
        # proof genuinely traverses the `targetLocal == targetLocal ->
        # projectionsOverlap` branch on both unmodified and mutated TCBs.
        self.assertIn(".field 0 { kind := .uint .u32, layoutIdx := 0 }", guard.sanity_source)
        self.assertIn(".field 1 { kind := .uint .u32, layoutIdx := 0 }", guard.sanity_source)
        self.assertIn(
            "tag := 1, targetLocal := 0, targetProjection := fieldZero :: .nil",
            guard.sanity_source,
        )
        self.assertIn(
            "tag := 2, targetLocal := 0, targetProjection := fieldOne :: .nil",
            guard.sanity_source,
        )
        # Local 0 is a 2-field aggregate whose field 1 receives field 0's value,
        # and whole-local `invalidateConflictingBorrows` disables tag 1.
        self.assertIn(
            ".init (.aggregate 0 (.scalar ⟨42, 4⟩ :: .scalar ⟨99, 4⟩ :: .nil))",
            guard.sanity_source,
        )
        self.assertIn(
            ".init (.aggregate 0 (.scalar ⟨42, 4⟩ :: .scalar ⟨42, 4⟩ :: .nil))",
            guard.sanity_source,
        )
        self.assertIn("{ fieldZeroBorrow with perm := .disabled }", guard.sanity_source)
        self.assertEqual(gmut.validate_catalog_invariants(ANNEAL_ROOT), [])

    # -- _trusted_function_names & cross-module / LHS hardening --------

    def test_trusted_function_names_ignores_comments_dotted_and_nullary_data(self) -> None:
        sample = textwrap.dedent(
            """\
            -- def fakeLineComment (x : Nat) : Nat := x
            /-!
            Doc quote with stray " character:
            def fakeBlockComment (x : Nat) : Nat := x
            /- nested comment
            def fakeNested (x : Nat) : Nat := x
            -/
            -/
            def emptyLayoutTable : LayoutTable :=
              { entries := .nil }
            abbrev F32Bits : Type := BitVec 32
            def defaultCodecFuel : Nat := 16
            def FloatPtrWidth.bits : FloatPtrWidth → Nat
              | .bits32 => 32
            def realFn (x : Nat) : Nat := x
            def realArrow : Nat → Nat
              | n => n
            abbrev realAlias := realFn
            """
        )
        names = gmut._trusted_function_names(sample)
        self.assertEqual(names, {"realFn", "realArrow", "realAlias"})

        # Live Scalars.lean: `bits` (from `FloatPtrWidth.bits`) and
        # `emptyLayoutTable` are NOT in `semantics_fn_names`, so record syntax
        # `{ bits := 42, sizeBytes := 4 }` in a helper `def` is accepted.
        scalars_text = (
            ANNEAL_ROOT
            / "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean"
        ).read_text(encoding="utf-8")
        scalars_fns = gmut._trusted_function_names(scalars_text)
        self.assertIn("evalScalarBinOp", scalars_fns)
        self.assertIn("evalUnaryNot", scalars_fns)
        self.assertNotIn("bits", scalars_fns)
        self.assertNotIn("emptyLayoutTable", scalars_fns)
        self.assertNotIn("F32Bits", scalars_fns)

        guard = gmut.select_guards(guard_filters=["div_by_zero"])[0]
        record_helper = guard.sanity_source.replace(
            "theorem sanity_div_by_zero :",
            "def fortyTwo : ScalarInt :=\n  { bits := 42, sizeBytes := 1 }\n\ntheorem sanity_div_by_zero :",
        ).replace("⟨42, 1⟩", "fortyTwo")
        with mock.patch.object(
            gmut,
            "MIR_SEMANTICS_GUARDS",
            _replace_guard("div_by_zero", sanity_source=record_helper),
        ):
            self.assertEqual(gmut.validate_catalog_invariants(ANNEAL_ROOT), [])

    def test_cross_module_sanity_bypass_is_rejected(self) -> None:
        # A Terminators.lean guard whose sanity theorem calls `evalScalarBinOp`
        # (from unmutated Scalars.lean) would pass on every broken Terminators
        # mutant; target-module scoping must reject it statically.
        div_guard = gmut.select_guards(guard_filters=["div_by_zero"])[0]
        term_guard = gmut.select_guards(
            guard_filters=["tb_drop_protector_conflict"]
        )[0]
        cross_sanity = div_guard.sanity_source.replace(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars",
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators",
        ).replace(div_guard.sanity_theorem_name, term_guard.sanity_theorem_name)
        with mock.patch.object(
            gmut,
            "MIR_SEMANTICS_GUARDS",
            _replace_guard("tb_drop_protector_conflict", sanity_source=cross_sanity),
        ):
            errors = gmut.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertTrue(
            any("LHS must apply a trusted MirSemantics function from the mutated module" in e for e in errors),
            errors,
        )

    def test_lhs_pipelines_operators_nested_calls_and_control_syntax_rejected(self) -> None:
        # Pipelines, comparisons, cons, or arithmetic at depth 0 of LHS could
        # discard or self-compare the semantics result (`rfl` proves `0 = 0`).
        for bad_lhs in (
            "evalStmt s stmt |> Function.const _ 0",
            "evalStmt s stmt |>.isOk",
            "evalStmt s stmt == evalStmt s stmt",
            "evalStmt s stmt :: .nil",
            "evalStmt s stmt $ x",
            "evalStmt s stmt + 0",
        ):
            errs = self._stmt_errors("sanity", f"    {bad_lhs} = expected")
            self.assertTrue(
                any("without top-level operator(s)" in e for e in errs),
                (bad_lhs, errs),
            )

        # Helper discard via pipeline is also blocked even when `fun` lives in a helper.
        errs = self._stmt_errors(
            "sanity",
            "    evalStmt s stmt |> discard = 0",
            helpers="def discard : MirStepNode → Nat := fun _ => 0\n\n",
        )
        self.assertTrue(any("without top-level operator(s)" in e for e in errs), errs)

        # Bare 0-ary LHS (no arguments applied), qualified paths, and
        # double-parenthesized applications all fail closed.
        for bad_lhs in (
            "evalStmt",
            "((evalStmt s stmt))",
            "Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt s stmt",
        ):
            errs = self._stmt_errors("refute", f"    {bad_lhs} = MirStepNode.fail .ub")
            self.assertTrue(
                any("LHS must apply a trusted MirSemantics function" in e for e in errs),
                (bad_lhs, errs),
            )

        # Nested second MirSemantics function inside LHS arguments is rejected.
        errs = self._stmt_errors(
            "sanity", "    evalStmt (evalOperand xs op) stmt = MirStepNode.step s"
        )
        self.assertTrue(
            any("LHS arguments must not invoke additional MirSemantics" in e for e in errs),
            errs,
        )

        # `match`, `if`, and Lean 4 center-dot `·` anonymous lambda are blocked,
        # while the same text inside a string literal is harmless data.
        for bad_body in (
            "    evalStmt (if true then s else s) stmt = MirStepNode.step s",
            "    evalStmt (match s with | x => x) stmt = MirStepNode.step s",
            "    evalStmt ((·) s) stmt = MirStepNode.step s",
        ):
            errs = self._stmt_errors("sanity", bad_body)
            self.assertTrue(any("`match`, `if` or `·`" in e for e in errs), (bad_body, errs))

        self.assertEqual(
            self._stmt_errors(
                "sanity",
                '    evalStmt s { kind := .nop, span := "if let a |> b == c ·" } = MirStepNode.step s',
            ),
            [],
        )

    # -- tightened `:= rfl` proof-failure classification ---------------

    def test_classify_rejects_statement_elaboration_errors_and_partial_kills(self) -> None:
        # Broken statement elaboration errors (arity, field, typeclass, argument
        # type mismatch) are NON_KILL_ERROR_MARKERS and never count as kills —
        # including `Application type mismatch`, which contains `type mismatch`.
        for broken in (
            "/t/Refute_div_by_zero.lean:8:4: error: Application type mismatch\n  x\nhas type\n  Nat\n",
            "/t/Refute_div_by_zero.lean:8:4: error: Function expected at\n  f\n",
            "/t/Refute_div_by_zero.lean:8:4: error: invalid field 'foo', the environment does not contain 'Bar.foo'\n",
            "/t/Refute_div_by_zero.lean:8:4: error: 'foo' is not a valid field\n",
            "/t/Refute_div_by_zero.lean:8:4: error: failed to synthesize\n  Inhabited Foo\n",
        ):
            status, detail = gmut.classify_refutation_failure(
                1, broken, self.FIXTURE, self.SPAN, stderr_output=""
            )
            self.assertEqual(status, "ERROR", (broken, detail))

        # Arbitrary errors mentioning `rfl`, `has type`, or `unsolved goals`
        # without `Type mismatch` / `type mismatch` are NOT `:= rfl` kills.
        for non_rfl in (
            "/t/Refute_div_by_zero.lean:9:2: error: unsolved goals\n  ⊢ False\n",
            "/t/Refute_div_by_zero.lean:9:2: error: failed near rfl\n",
            "/t/Refute_div_by_zero.lean:9:2: error: term has type Nat\n",
        ):
            status, detail = gmut.classify_refutation_failure(
                1, non_rfl, self.FIXTURE, self.SPAN, stderr_output=""
            )
            self.assertEqual(status, "ERROR", (non_rfl, detail))

        # Exact two-diagnostic Lean 4.34.1 `:= rfl` refutation failure
        # (`Not a definitional equality` + `Type mismatch`) classifies as KILLED,
        # while adding any NON_KILL_ERROR_MARKERS turns it into ERROR.
        lean434_pair = (
            "/t/Refute_div_by_zero.lean:7:0: error: Not a definitional equality: the left-hand side\n"
            "  evalScalarBinOp Trusted.Rustc.V2026_06_01.MirAst.BinOp.div { bits := 5, sizeBytes := 4 } { bits := 1, sizeBytes := 4 }\n"
            "    []\n"
            "is not definitionally equal to the right-hand side\n"
            "  RvalueEvalResult.ub\n"
            "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\n"
            "  rfl\n"
            "has type\n"
            "  ?m.14 = ?m.14\n"
            "but is expected to have type\n"
            "  evalScalarBinOp .div ⟨7, 1⟩ ⟨0, 1⟩ .nil emptyMemory false = .ub\n"
        )
        status, detail = gmut.classify_refutation_failure(
            1, lean434_pair, self.FIXTURE, self.SPAN, stderr_output=""
        )
        self.assertEqual(status, "KILLED", detail)
        self.assertIn("[7, 9]", detail)
        for marker in gmut.NON_KILL_ERROR_MARKERS:
            bad_pair = lean434_pair + f"  {marker}\n"
            status_bad, detail_bad = gmut.classify_refutation_failure(
                1, bad_pair, self.FIXTURE, self.SPAN, stderr_output=""
            )
            self.assertEqual(status_bad, "ERROR", (marker, detail_bad))

        # Every error diagnostic inside the theorem span must be a recognized
        # `:= rfl` proof failure: a bizarre glitch alongside a Type mismatch is
        # ERROR, not KILLED.
        mixed = (
            "/t/Refute_div_by_zero.lean:8:4: error: bizarre glitch\n"
            "/t/Refute_div_by_zero.lean:9:2: error: Type mismatch\n  rfl\n"
        )
        status, _ = gmut.classify_refutation_failure(
            1, mixed, self.FIXTURE, self.SPAN, stderr_output=""
        )
        self.assertEqual(status, "ERROR")

    # -- signal handling in non-main threads & partial-install restore --

    def test_termination_signals_non_main_thread_and_partial_install_restore(self) -> None:
        # Entering `_termination_signals_as_interrupt` from a worker thread
        # must not raise `ValueError: signal only works in main thread`.
        worker_errors: list[BaseException] = []
        entered = False

        def _worker() -> None:
            nonlocal entered
            try:
                with gmut._termination_signals_as_interrupt():
                    entered = True
            except BaseException as exc:  # noqa: BLE001
                worker_errors.append(exc)

        t = threading.Thread(target=_worker)
        t.start()
        t.join(timeout=5)
        self.assertFalse(t.is_alive())
        self.assertTrue(entered)
        self.assertEqual(worker_errors, [])

        # If SIGTERM is installed and installing SIGHUP is interrupted (or
        # raises), SIGTERM must still be restored to SIG_DFL.
        before_term = signal.getsignal(signal.SIGTERM)
        before_hup = signal.getsignal(signal.SIGHUP)
        real_signal = signal.signal
        try:
            real_signal(signal.SIGTERM, signal.SIG_DFL)
            real_signal(signal.SIGHUP, signal.SIG_DFL)

            def _flaky_signal(signum: int, handler: object) -> object:
                if signum == signal.SIGHUP and handler is not signal.SIG_DFL:
                    raise KeyboardInterrupt("SIGTERM")
                return real_signal(signum, handler)  # type: ignore[arg-type]

            with mock.patch.object(signal, "signal", side_effect=_flaky_signal):
                with self.assertRaisesRegex(KeyboardInterrupt, "SIGTERM"):
                    with gmut._termination_signals_as_interrupt():
                        self.fail("body should not run when install is interrupted")
            self.assertIs(signal.getsignal(signal.SIGTERM), signal.SIG_DFL)
        finally:
            real_signal(signal.SIGTERM, before_term)
            real_signal(signal.SIGHUP, before_hup)

    def test_final_json_out_write_error_still_emits_fatal_json_to_stdout(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-a3-json-") as tmp:
            fake = Path(tmp) / "fake_lean"
            _write_fake_lean_sh(fake, KILL_ALL_FAKE_SH)
            out = Path(tmp) / "report.json"
            writes = 0
            real_write = gmut._write_json_out

            def _fail_second_write(path: Path, report: dict[str, object]) -> None:
                nonlocal writes
                writes += 1
                if writes >= 2:
                    raise OSError("disk full")
                real_write(path, report)

            with (
                mock.patch.object(gmut, "_write_json_out", side_effect=_fail_second_write),
                mock.patch("sys.stdout", new_callable=lambda: __import__("io").StringIO()) as buf_out,
                mock.patch("sys.stderr", new_callable=lambda: __import__("io").StringIO()) as buf_err,
            ):
                rc = gmut.main(
                    [
                        "--lean", str(fake),
                        "--no-lake-cache",
                        "--guard", "div_by_zero",
                        "--json",
                        "--json-out", str(out),
                    ]
                )
            self.assertEqual(rc, 1)
            self.assertIn("disk full", buf_err.getvalue())
            emitted = json.loads(buf_out.getvalue())
            self.assertFalse(emitted["ok"])
            self.assertIn("disk full", emitted["fatal_error"])
            # Pre-written fail-closed sentinel remains on disk.
            on_disk = json.loads(out.read_text(encoding="utf-8"))
            self.assertFalse(on_disk["ok"])


class GuardMutationB4AdversarialTests(unittest.TestCase):
    """Round 4 B4 audit: only a `Type mismatch` on the `rfl` proof is a kill."""

    FIXTURE = "Refute_div_by_zero.lean"
    SPAN = (7, 9)
    PATH = "/t/Refute_div_by_zero.lean"
    RFL = f"{PATH}:9:2: error: Type mismatch\n  rfl\nhas type\n  ?m.14 = ?m.14\nbut is expected to have type\n  f x = y\n"
    DEFEQ = (
        f"{PATH}:7:0: error: Not a definitional equality: the left-hand side\n"
        "  f x\n"
        "is not definitionally equal to the right-hand side\n"
        "  y\n"
    )

    def _classify(self, out: str) -> tuple[str, str]:
        return gmut.classify_refutation_failure(
            1, out, self.FIXTURE, self.SPAN, stderr_output=""
        )

    def test_statement_type_mismatch_is_not_a_kill(self) -> None:
        # What Lean prints for `theorem t : (1 : Nat) = Bool := rfl`: the
        # STATEMENT fails to elaborate, on a line inside the theorem span, and
        # `rfl` is never reached. A mutant that breaks a refutation's statement
        # this way must not pass for a refuted proof.
        statement = (
            f"{self.PATH}:8:15: error: Type mismatch\n  Bool\nhas type\n  Type\n"
            "but is expected to have type\n  Nat\n"
        )
        status, detail = self._classify(statement)
        self.assertEqual(status, "ERROR", detail)
        self.assertIn("unrecognized non-proof diagnostic", detail)
        # ... not even next to a genuine `rfl` mismatch or its companion.
        for extra in (self.RFL, self.DEFEQ, self.DEFEQ + self.RFL):
            self.assertEqual(self._classify(statement + extra)[0], "ERROR", extra)
            self.assertEqual(self._classify(extra + statement)[0], "ERROR", extra)

        # Every other `Type mismatch` Lean can print is about something else
        # than the `rfl` proof term.
        for text in (
            "type mismatch\n  x\nhas type\n  Nat\n",
            "Type mismatch\n  rfl.symm\nhas type\n",
            "Type mismatch\n  rfl x\nhas type\n",
            "Type mismatch\n  @rfl Nat 1\nhas type\n",
            "Type mismatch\n  rflect\nhas type\n",
            "Type mismatch\n  Eq.refl ?a\nhas type\n",
            "Type mismatch\nrfl\nhas type\n",
            "Type mismatch rfl has type\n",
            "Type mismatch\n",
            "Type mismatch: target is\n  rfl\n",
            "Type mismatch in pattern: Pattern\n  rfl\n",
            "Type mismatch. The `do` element has monadic result type\n  rfl\n",
            "bizarre glitch\n  Type mismatch\n  rfl\nhas type\n",
            "rfl\n  Type mismatch\n",
        ):
            out = f"{self.PATH}:9:2: error: {text}"
            self.assertEqual(self._classify(out)[0], "ERROR", text)
            self.assertEqual(self._classify(self.RFL + out)[0], "ERROR", text)

    def test_rfl_type_mismatch_is_the_kill_and_defeq_only_accompanies_it(self) -> None:
        # The proof itself was rejected: alone, or with Lean 4.34's `@[defeq]`
        # companion in either order.
        for out in (self.RFL, self.DEFEQ + self.RFL, self.RFL + self.DEFEQ):
            status, detail = self._classify(out)
            self.assertEqual(status, "KILLED", (out, detail))
        self.assertIn("[7, 9]", self._classify(self.DEFEQ + self.RFL)[1])
        # Older toolchains spell the heading in lower case and add sorts.
        legacy = f"{self.PATH}:9:2: error: type mismatch\n  rfl\nhas type\n  f x = f x : Prop\n"
        self.assertEqual(self._classify(legacy)[0], "KILLED")
        named = f"{self.PATH}:9:2: error(lean.typeMismatch): Type mismatch\n  rfl\nhas type\n"
        self.assertEqual(self._classify(named)[0], "KILLED")

        # `Not a definitional equality` comes from validating the `@[defeq]`
        # attribute of a `:= rfl` theorem. It looks at the statement only and
        # is printed for a theorem whose `rfl` Lean ACCEPTED as well, so alone
        # it is an exit status 1 without a rejected proof.
        status, detail = self._classify(self.DEFEQ)
        self.assertEqual(status, "ERROR")
        self.assertIn("no `Type mismatch` on the `rfl` proof", detail)
        self.assertEqual(self._classify(self.DEFEQ + self.DEFEQ)[0], "ERROR")

        # Only the exact left-hand/right-hand side form is the companion.
        for text in (
            "Not a definitional equality: the conclusion should be an equality, but is\n  True\n",
            "Not a definitional equality: the left-hand side\n  f x\n",
            "Not a definitional equality\n",
            "not a definitional equality: the left-hand side\n  f x\n"
            "is not definitionally equal to the right-hand side\n  y\n",
            "f x is not definitionally equal to the right-hand side\n  y\n",
        ):
            out = f"{self.PATH}:7:0: error: {text}"
            self.assertEqual(self._classify(out + self.RFL)[0], "ERROR", text)

        # Each recognized diagnostic opens with one of the documented headings.
        self.assertEqual(gmut._rfl_failure_kind(" Type mismatch\n  rfl\n"), "rfl")
        self.assertEqual(gmut._rfl_failure_kind(self.DEFEQ.split("error:")[1]), "defeq")
        self.assertIsNone(gmut._rfl_failure_kind(" Type mismatch\n  Bool\n"))
        for text in (self.RFL, self.DEFEQ):
            self.assertTrue(
                text.split("error: ")[1].startswith(gmut.EXPECTED_PROOF_FAILURE_MARKERS)
            )

    def test_proof_is_the_only_rfl_of_a_fixture(self) -> None:
        # The classifier recognizes the proof by the term Lean names, so no
        # other `rfl` may sit in the statement or in a helper.
        head = "import Trusted.A\n"
        theorem = "theorem t :\n    f 1 = 2 :=\n  rfl\n"
        self.assertEqual(gmut._fixture_shape_errors("refute", head + theorem, "t"), [])
        for src in (
            head + "theorem t :\n    f ⟨1, rfl⟩ = 2 :=\n  rfl\n",
            head + "theorem t :\n    f (h := _root_.rfl) = 2 :=\n  rfl\n",
            head + "def h : 1 = 1 :=\n  rfl\n" + theorem,
            head + "def h : 1 = 1 := Eq.rfl\n" + theorem,
        ):
            errors = gmut._fixture_shape_errors("refute", src, "t")
            self.assertTrue(
                any("exactly one `rfl` (the theorem's proof), found 2" in e for e in errors),
                (src, errors),
            )
        # `rfl` as text in a string or a comment, or inside a longer name, is
        # not the term.
        harmless = (
            head
            + 'def msg : String := "rfl"\n'
            + "def rfl' : Nat := 1\n"
            + "def my_rfl : Nat := 2 -- rfl\n"
            + theorem
        )
        self.assertEqual(gmut._fixture_shape_errors("refute", harmless, "t"), [])

        # The live catalog obeys it, and rejects a guard that does not.
        guard = gmut.select_guards(guard_filters=["div_by_zero"])[0]
        self.assertEqual(guard.refute_source.count("rfl"), 1)
        smuggled = guard.refute_source.replace(
            "theorem refute_div_by_zero :",
            "def same : 1 = 1 :=\n  rfl\n\ntheorem refute_div_by_zero :",
        )
        self.assertNotEqual(smuggled, guard.refute_source)
        with mock.patch.object(
            gmut, "MIR_SEMANTICS_GUARDS", _replace_guard("div_by_zero", refute_source=smuggled)
        ):
            errors = gmut.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertTrue(
            any("div_by_zero" in e and "exactly one `rfl`" in e for e in errors), errors
        )

    def test_synthetic_statement_type_mismatch_on_mutant_is_error(self) -> None:
        # End to end: the mutant makes the refutation's statement ill-typed.
        # Lean exits 1 with a `Type mismatch` inside the theorem, on a
        # statement line, and the gate must report ERROR, not a kill.
        body = textwrap.dedent(
            """\
            if [ -n "$OUT" ]; then
              mkdir -p "$(dirname "$OUT")"
              printf 'fake-olean:%s' "$BASENAME" > "$OUT"
            fi
            if [ "$IS_MUTANT" = "1" ]; then
              case "$BASENAME" in
                Refute_*)
                  LINE="$(grep -n '^theorem ' "$SRC" | head -n 1 | cut -d: -f1)"
                  printf '%s:%s:4: error: Type mismatch\\n  RvalueEvalResult.ub\\nhas type\\n  RvalueEvalResult\\nbut is expected to have type\\n  Nat\\n' "$SRC" "$((LINE + 1))"
                  exit 1
                  ;;
              esac
            fi
            exit 0
            """
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-b4-stmt-") as tmp:
            fake = Path(tmp) / "fake_lean"
            _write_fake_lean_sh(fake, body)
            proc = _run_cli(
                ["--lean", str(fake), "--no-lake-cache", "--guard", "div_by_zero", "--json"]
            )
            self.assertEqual(proc.returncode, 1, proc.stderr)
            report = json.loads(proc.stdout)
            self.assertEqual(
                (report["killed"], report["survived"], report["errors"]), (0, 0, 1)
            )
            self.assertIn("unrecognized non-proof diagnostic", report["results"][0]["detail"])

    def test_signal_arriving_as_soon_as_its_handler_is_installed_is_restored(self) -> None:
        # SIGHUP is delivered the instant its handler is in place, before the
        # context manager could do anything else: both signals must still go
        # back to their default action.
        before_term = signal.getsignal(signal.SIGTERM)
        before_hup = signal.getsignal(signal.SIGHUP)
        real_signal = signal.signal
        try:
            real_signal(signal.SIGTERM, signal.SIG_DFL)
            real_signal(signal.SIGHUP, signal.SIG_DFL)

            def _install_then_deliver(signum: int, handler: object) -> object:
                previous = real_signal(signum, handler)  # type: ignore[arg-type]
                if signum == signal.SIGHUP and callable(handler):
                    handler(signum, None)
                return previous

            with mock.patch.object(signal, "signal", side_effect=_install_then_deliver):
                with self.assertRaisesRegex(KeyboardInterrupt, "SIGHUP"):
                    with gmut._termination_signals_as_interrupt():
                        self.fail("body must not run when a signal interrupts setup")
            self.assertIs(signal.getsignal(signal.SIGTERM), signal.SIG_DFL)
            self.assertIs(signal.getsignal(signal.SIGHUP), signal.SIG_DFL)
        finally:
            real_signal(signal.SIGTERM, before_term)
            real_signal(signal.SIGHUP, before_hup)

    def test_module_docstring_matches_the_cli_and_the_catalog(self) -> None:
        doc = gmut.__doc__ or ""
        # Every command-line flag is documented.
        flags: set[str] = set()
        for node in ast.walk(ast.parse(SCRIPT.read_text(encoding="utf-8"))):
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "add_argument"
            ):
                flags.update(
                    arg.value
                    for arg in node.args
                    if isinstance(arg, ast.Constant)
                    and isinstance(arg.value, str)
                    and arg.value.startswith("--")
                )
        self.assertGreaterEqual(len(flags), 13, flags)
        for flag in sorted(flags):
            self.assertRegex(doc, rf"(?m)^  {re.escape(flag)}(?:\s|$)", flag)

        # The catalog summary is the live catalog.
        guards = gmut.MIR_SEMANTICS_GUARDS
        per_file = {
            name: sum(1 for g in guards if g.target_file.endswith(f"/{name}.lean"))
            for name in ("Scalars", "Places", "Statements", "Terminators")
        }
        self.assertEqual(sum(per_file.values()), len(guards))
        summary = " ".join(doc.split())
        self.assertIn(
            f"`MIR_SEMANTICS_GUARDS` holds {len(guards)} guards: "
            f"{per_file['Scalars']} in `Scalars.lean`, "
            f"{per_file['Places']} in `Places.lean`, "
            f"{per_file['Statements']} in `Statements.lean` and "
            f"{per_file['Terminators']} in `Terminators.lean`.",
            summary,
        )
        quick = [g for g in guards if g.quick]
        self.assertIn(f"Run the {len(quick)}-guard smoke subset", summary)
        self.assertEqual(
            sorted(Path(g.target_file).stem for g in quick),
            ["Scalars", "Statements", "Terminators"],
        )
        # "Each fixture imports only its guard's target module".
        for g in guards:
            self.assertEqual(g.effective_rebuild_modules, (g.target_module,), g.guard_id)


class GuardMutationA4ConvergenceTests(unittest.TestCase):
    """Round 4 A4 convergence ratchets for B4's `rfl` classifier and token checks."""

    FIXTURE = "Refute_div_by_zero.lean"
    SPAN = (7, 9)
    PATH = "/t/Refute_div_by_zero.lean"

    def test_rfl_type_mismatch_named_codes_crlf_indentation_and_stream_isolation(
        self,
    ) -> None:
        # Named error codes + Windows CRLF + varying horizontal indentation on
        # `rfl` (2 spaces, 4 spaces, tab, trailing whitespace) all count as KILLED,
        # alone or paired with a named `@[defeq]` companion.
        named_defeq_crlf = (
            f"{self.PATH}:7:0: error(lean.defeq): Not a definitional equality: "
            "the left-hand side\r\n"
            "  evalScalarBinOp .div ⟨7, 1⟩ ⟨0, 1⟩ .nil emptyMemory false\r\n"
            "is not definitionally equal to the right-hand side\r\n"
            "  .ub\r\n"
        )
        for indent in ("  ", "    ", "\t"):
            named_rfl_crlf = (
                f"{self.PATH}:9:2: error(lean.typeMismatch): Type mismatch \r\n"
                f"{indent}rfl  \r\n"
                "has type\r\n"
                "  ?m.14 = ?m.14\r\n"
                "but is expected to have type\r\n"
                "  f x = .ub\r\n"
            )
            for out in (named_rfl_crlf, named_defeq_crlf + named_rfl_crlf):
                status, detail = gmut.classify_refutation_failure(
                    1, out, self.FIXTURE, self.SPAN, stderr_output=""
                )
                self.assertEqual(status, "KILLED", (indent, detail))

        # Named error code on a statement-level mismatch or a lone named defeq
        # diagnostic must remain ERROR.
        named_stmt = (
            f"{self.PATH}:8:4: error(lean.typeMismatch): Type mismatch\r\n"
            "  Bool\r\nhas type\r\n  Type\r\n"
        )
        valid_rfl = f"{self.PATH}:9:2: error(lean.typeMismatch): Type mismatch\n  rfl\n"
        for bad in (named_stmt, named_stmt + valid_rfl, named_defeq_crlf):
            status, detail = gmut.classify_refutation_failure(
                1, bad, self.FIXTURE, self.SPAN, stderr_output=""
            )
            self.assertEqual(status, "ERROR", (bad, detail))

        # A `Not a definitional equality` diagnostic truncated on stdout cannot
        # borrow its second line from stderr, even when a valid `rfl` mismatch
        # also appears on stderr.
        stdout_half = (
            f"{self.PATH}:7:0: error: Not a definitional equality: the left-hand side\n"
            "  f x\n"
        )
        stderr_rest = (
            "is not definitionally equal to the right-hand side\n  .ub\n" + valid_rfl
        )
        status, detail = gmut.classify_refutation_failure(
            1, stdout_half, self.FIXTURE, self.SPAN, stderr_output=stderr_rest
        )
        self.assertEqual(status, "ERROR", detail)

    def test_single_rfl_token_check_handles_block_comments_strings_and_smuggling(
        self,
    ) -> None:
        head = "import Trusted.A\n"
        theorem = "theorem t :\n    f 1 = 2 :=\n  rfl\n"

        # `rfl` inside block comments, nested block comments, comments holding
        # stray quotes, or a string literal inside the theorem statement must
        # not trip the single-`rfl` token check.
        harmless = (
            head
            + "/- rfl -/\n"
            + "/- outer /- rfl -/ \"rfl -/\n"
            + "-- \"rfl\n"
            + 'def tag : String := "-- rfl /- rfl"\n'
            + 'theorem t :\n    f "rfl" = 2 :=\n  rfl\n'
        )
        self.assertEqual(gmut._fixture_shape_errors("refute", harmless, "t"), [])

        # Strings containing `--` or `/-` must NOT mask a real `rfl` that
        # follows on the next line, and `rfl!`/`rfl?` or zero `rfl`s fail closed.
        for bad, expected_count in (
            (
                head + 'def s : String := "-- rfl"\ndef h : 1 = 1 := rfl\n' + theorem,
                2,
            ),
            (
                head + 'def s : String := "/- rfl"\ndef h : 1 = 1 := rfl\n' + theorem,
                2,
            ),
            (
                head + "theorem t :\n    f rfl! = 2 :=\n  rfl\n",
                2,
            ),
            (
                head + "theorem t :\n    f rfl? = 2 :=\n  rfl\n",
                2,
            ),
            (
                head + "theorem t :\n    f 1 = 2 :=\n  Eq.refl _\n",
                0,
            ),
        ):
            errors = gmut._fixture_shape_errors("refute", bad, "t")
            self.assertTrue(
                any(
                    f"exactly one `rfl` (the theorem's proof), found {expected_count}"
                    in e
                    for e in errors
                ),
                (bad, errors),
            )

    def test_end_to_end_named_type_mismatch_and_lone_defeq_cli_verdicts(self) -> None:
        named_kill_sh = textwrap.dedent(
            """\
            if [ -n "$OUT" ]; then
              mkdir -p "$(dirname "$OUT")"
              printf 'fake-olean:%s' "$BASENAME" > "$OUT"
            fi
            if [ "$IS_MUTANT" = "1" ]; then
              case "$BASENAME" in
                Refute_*)
                  LINE="$(grep -n '^theorem ' "$SRC" | head -n 1 | cut -d: -f1)"
                  printf '%s:%s:0: error(lean.defeq): Not a definitional equality: the left-hand side\\r\\n  lhs\\r\\nis not definitionally equal to the right-hand side\\r\\n  .ub\\r\\n' "$SRC" "$LINE"
                  printf '%s:%s:2: error(lean.typeMismatch): Type mismatch\\r\\n  rfl\\r\\nhas type\\r\\n  ?m = ?m\\r\\n' "$SRC" "$((LINE + 2))"
                  exit 1
                  ;;
              esac
            fi
            exit 0
            """
        )
        lone_defeq_sh = textwrap.dedent(
            """\
            if [ -n "$OUT" ]; then
              mkdir -p "$(dirname "$OUT")"
              printf 'fake-olean:%s' "$BASENAME" > "$OUT"
            fi
            if [ "$IS_MUTANT" = "1" ]; then
              case "$BASENAME" in
                Refute_*)
                  LINE="$(grep -n '^theorem ' "$SRC" | head -n 1 | cut -d: -f1)"
                  printf '%s:%s:0: error: Not a definitional equality: the left-hand side\\n  lhs\\nis not definitionally equal to the right-hand side\\n  .ub\\n' "$SRC" "$LINE"
                  exit 1
                  ;;
              esac
            fi
            exit 0
            """
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-a4-e2e-") as tmp:
            tmp_path = Path(tmp)
            fake_kill = tmp_path / "fake_lean_kill"
            fake_defeq = tmp_path / "fake_lean_defeq"
            json_out = tmp_path / "report.json"
            _write_fake_lean_sh(fake_kill, named_kill_sh)
            _write_fake_lean_sh(fake_defeq, lone_defeq_sh)

            kill_proc = _run_cli(
                [
                    "--lean", str(fake_kill),
                    "--no-lake-cache",
                    "--guard", "div_by_zero",
                    "--json",
                    "--json-out", str(json_out),
                ]
            )
            self.assertEqual(kill_proc.returncode, 0, kill_proc.stderr)
            kill_report = json.loads(kill_proc.stdout)
            self.assertEqual(
                (
                    kill_report["ok"],
                    kill_report["killed"],
                    kill_report["survived"],
                    kill_report["errors"],
                ),
                (True, 1, 0, 0),
            )
            self.assertEqual(
                json.loads(json_out.read_text(encoding="utf-8")), kill_report
            )

            defeq_proc = _run_cli(
                [
                    "--lean", str(fake_defeq),
                    "--no-lake-cache",
                    "--guard", "div_by_zero",
                    "--json",
                    "--json-out", str(json_out),
                ]
            )
            self.assertEqual(defeq_proc.returncode, 1, defeq_proc.stderr)
            defeq_report = json.loads(defeq_proc.stdout)
            self.assertEqual(
                (
                    defeq_report["ok"],
                    defeq_report["killed"],
                    defeq_report["survived"],
                    defeq_report["errors"],
                ),
                (False, 0, 0, 1),
            )
            self.assertIn(
                "no `Type mismatch` on the `rfl` proof",
                defeq_report["results"][0]["detail"],
            )
            self.assertEqual(
                json.loads(json_out.read_text(encoding="utf-8")), defeq_report
            )


class GuardMutationTaxonomyAndWildcardTests(unittest.TestCase):
    """Episode 2: property-taxonomy unification and the `error_branch_wildcard` probe."""

    RUST_REL = "crates/cargo-anneal/src/property_registry.rs"
    LEAN_REL = "theory/Anneal/SpecBoundaryGuards.lean"

    EXPECTED_GUARD_CLASSES: dict[str, str] = {
        "div_by_zero": "div_rem_ub",
        "rem_by_zero": "div_rem_ub",
        "signed_div_overflow": "div_rem_ub",
        "signed_rem_overflow": "div_rem_ub",
        "shift_oob": "shift_bounds",
        "shr_oob": "shift_bounds",
        "shl_oob_off_by_one": "shift_bounds",
        "shr_oob_off_by_one": "shift_bounds",
        "bool_valid_range": "discriminant_validity",
        "storage_dead_read": "uninit_read",
        "storage_uninit_read": "uninit_read",
        "unaligned_deref": "pointer_deref",
        "intrinsic_assume_false": "discriminant_validity",
        "intrinsic_assume_invalid_bool": "discriminant_validity",
        "intrinsic_assume_non_bool_size": "discriminant_validity",
        "copy_nonoverlapping_overlap": "memory_copy_overlap",
        "copy_nonoverlapping_place_overlap": "memory_copy_overlap",
        "copy_nonoverlapping_subplace_overlap": "memory_copy_overlap",
        "tb_drop_protector_conflict": "pointer_deref",
        "tb_return_frame_dealloc_protector_conflict": "pointer_deref",
    }

    def _stage(self, root: Path, rel: str, old: str | None = None, new: str = "") -> None:
        """Copy a live taxonomy source into `root`, replacing `old` exactly once."""
        text = (ANNEAL_ROOT / rel).read_text(encoding="utf-8")
        if old is not None:
            self.assertEqual(text.count(old), 1, old)
            text = text.replace(old, new)
        dst = root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(text, encoding="utf-8")

    # -- canonical taxonomy and live parity ----------------------------

    def test_canonical_taxonomy_is_the_live_rust_and_lean_taxonomy(self) -> None:
        self.assertEqual(
            gmut.CANONICAL_PROPERTY_CLASSES,
            (
                "arithmetic_overflow",
                "shift_bounds",
                "div_rem_ub",
                "pointer_deref",
                "slice_array_bounds",
                "discriminant_validity",
                "call_contract",
                "loop_termination",
                "switch_exhaustiveness",
                "memory_copy_overlap",
                "uninit_read",
                "unsupported_fallback",
            ),
        )
        self.assertEqual(
            gmut.CANONICAL_SPEC_BOUNDARY_GUARDS,
            ("entry_point_requires", "fixed_width_ghost_length", "error_branch_wildcard"),
        )
        canonical = gmut.canonical_property_taxonomy()
        rust = gmut.extract_rust_property_taxonomy(ANNEAL_ROOT)
        self.assertEqual(rust, canonical)
        self.assertEqual(
            [e["id"] for e in rust["property_classes"]], list(gmut.CANONICAL_PROPERTY_CLASSES)
        )
        self.assertEqual(
            [e["id"] for e in rust["spec_boundary_guards"]],
            list(gmut.CANONICAL_SPEC_BOUNDARY_GUARDS),
        )
        lean = gmut.extract_lean_property_taxonomy(ANNEAL_ROOT)
        for section, keys in (
            ("property_classes", ("rank", "id", "variant", "is_waivable")),
            ("spec_boundary_guards", ("rank", "id", "canonical_name", "vacuity_class")),
        ):
            self.assertEqual(
                lean[section], [{k: e[k] for k in keys} for e in canonical[section]], section
            )
        self.assertEqual(gmut.validate_property_taxonomy(ANNEAL_ROOT), [])
        self.assertEqual(
            gmut.validate_property_taxonomy(ANNEAL_ROOT, require_rust_taxonomy=True), []
        )
        # The returned taxonomy is a private copy: mutating it cannot poison the cache.
        rust["property_classes"][0]["id"] = "poisoned"
        self.assertEqual(gmut.extract_rust_property_taxonomy(ANNEAL_ROOT), canonical)

    def test_taxonomy_manifest_json_has_the_exact_rust_layout(self) -> None:
        manifest = gmut.render_property_taxonomy_manifest()
        self.assertEqual(
            manifest, gmut.render_property_taxonomy_manifest(gmut.extract_rust_property_taxonomy(ANNEAL_ROOT))
        )
        parsed = json.loads(manifest)
        self.assertEqual(parsed, gmut.canonical_property_taxonomy())
        self.assertEqual(list(parsed), ["schema_version", "property_classes", "spec_boundary_guards"])
        lines = manifest.split("\n")
        self.assertEqual(lines[:3], ["{", '  "schema_version": 1,', '  "property_classes": ['])
        self.assertEqual(
            lines[3],
            '    {"rank": 0, "id": "arithmetic_overflow", "variant": "ArithmeticOverflow", '
            '"is_waivable": true, "strict_disposition": "discharged", '
            '"partial_disposition": "discharged", '
            '"description": "signed/unsigned arithmetic and float-to-int conversion overflow"},',
        )
        self.assertEqual(
            lines[14],
            '    {"rank": 11, "id": "unsupported_fallback", "variant": "UnsupportedFallback", '
            '"is_waivable": false, "strict_disposition": "unsupported_fail_closed", '
            '"partial_disposition": "unsupported_fail_closed", '
            '"description": "fail-closed fallback for unsupported or unscannable MIR constructs"}',
        )
        self.assertEqual(lines[15:17], ["  ],", '  "spec_boundary_guards": ['])
        self.assertEqual(
            lines[19],
            '    {"rank": 2, "id": "error_branch_wildcard", "canonical_name": "ErrorBranchWildcard", '
            '"vacuity_class": "SurvivedAllMutants", "description": "postcondition arm accepts '
            'every error payload, ub, or unsupported outcome"}',
        )
        self.assertEqual(lines[20:], ["  ]", "}", ""])
        by_id = {e["id"]: e for e in parsed["property_classes"]}
        self.assertEqual(by_id["loop_termination"]["partial_disposition"], "explicitly_waived")
        self.assertEqual(by_id["loop_termination"]["strict_disposition"], "discharged")
        # A registry export adds `disposition` between the partial disposition
        # and the description, and strings are escaped the way Rust escapes them.
        annotated = gmut.canonical_property_taxonomy()
        annotated["property_classes"][0]["disposition"] = "unemitted_gap"
        annotated["spec_boundary_guards"][0]["description"] = 'a "b"\\c\n\x01é'
        text = gmut.render_property_taxonomy_manifest(annotated)
        self.assertIn('"partial_disposition": "discharged", "disposition": "unemitted_gap", "description"', text)
        self.assertIn('"description": "a \\"b\\"\\\\c\\n\\u0001é"}', text)
        self.assertEqual(json.loads(text), annotated)

        res = _run_cli(["--taxonomy-json"])
        self.assertEqual((res.returncode, res.stdout, res.stderr), (0, manifest, ""))
        for bad in (["--taxonomy-json", "--list"], ["--taxonomy-json", "--quick"],
                    ["--taxonomy-json", "--json-out", "x.json"]):
            self.assertEqual(_run_cli(bad).returncode, 2, bad)

    def test_taxonomy_drift_against_the_rust_registry_fails_closed(self) -> None:
        cases: tuple[tuple[str, str, str, str], ...] = (
            (
                "reordered ALL",
                "        PropertyClass::ShiftBounds,\n        PropertyClass::DivRemUb,\n",
                "        PropertyClass::DivRemUb,\n        PropertyClass::ShiftBounds,\n",
                "`PropertyClass::ALL` is not the enum declaration order",
            ),
            (
                "renamed slug",
                'Self::DivRemUb => "div_rem_ub",',
                'Self::DivRemUb => "div_rem",',
                "property_registry.rs property_classes[2].id is 'div_rem', expected 'div_rem_ub'",
            ),
            (
                "slug kept only in a comment",
                'Self::DivRemUb => "div_rem_ub",',
                '/* Self::DivRemUb => "div_rem_ub", */ Self::DivRemUb => "div_rem", // "div_rem_ub"',
                "property_classes[2].id is 'div_rem'",
            ),
            (
                "thirteenth variant",
                "    UnsupportedFallback,\n}\n",
                "    UnsupportedFallback,\n    Extra,\n}\n",
                "malformed taxonomy source",
            ),
            (
                "reranked class",
                "            Self::ShiftBounds => 1,\n            Self::DivRemUb => 2,\n",
                "            Self::ShiftBounds => 2,\n            Self::DivRemUb => 1,\n",
                "`PropertyClass::rank` is not the declaration order",
            ),
            (
                "waivability",
                "!matches!(self, Self::UnsupportedFallback)",
                "!matches!(self, Self::UnsupportedFallback | Self::LoopTermination)",
                "property_classes[7].is_waivable is False, expected True",
            ),
            (
                "partial-correctness waiver moved",
                "reg.entries[PropertyClass::LoopTermination.rank()].disposition",
                "reg.entries[PropertyClass::CallContract.rank()].disposition",
                "property_classes[6].partial_disposition is 'explicitly_waived', expected 'discharged'",
            ),
            (
                "description",
                '"bit-shift distance within target integer bit width"',
                '"bit-shift distance"',
                "property_classes[1].description is 'bit-shift distance'",
            ),
            (
                "spec-boundary guard slug",
                'Self::ErrorBranchWildcard => "error_branch_wildcard",',
                'Self::ErrorBranchWildcard => "error_wildcard",',
                "spec_boundary_guards[2].id is 'error_wildcard', expected 'error_branch_wildcard'",
            ),
            (
                "spec-boundary vacuity class",
                'Self::EntryPointRequires => "DeadPrecondition",',
                'Self::EntryPointRequires => "SpecViolation",',
                "spec_boundary_guards[0].vacuity_class is 'SpecViolation'",
            ),
            (
                "schema version",
                "pub const PROPERTY_TAXONOMY_SCHEMA_VERSION: u32 = 1;",
                "pub const PROPERTY_TAXONOMY_SCHEMA_VERSION: u32 = 2;",
                "schema_version is 2, expected 1",
            ),
            (
                "unterminated comment",
                "pub enum PropertyClass {",
                "/* pub enum PropertyClass {",
                "malformed taxonomy source: unterminated block comment",
            ),
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            for idx, (label, old, new, needle) in enumerate(cases):
                root = Path(tmp) / f"case{idx}"
                self._stage(root, self.RUST_REL, old, new)
                errors = gmut.validate_property_taxonomy(root)
                self.assertTrue(any(needle in e for e in errors), (label, errors))
                # The extractor either refuses the source or reports the drifted value.
                try:
                    extracted = gmut.extract_rust_property_taxonomy(root)
                except ValueError:
                    continue
                self.assertNotEqual(extracted, gmut.canonical_property_taxonomy(), label)

            # The pristine sources validate in an isolated root, and the catalog
            # gate reports the drift of a staged registry.
            clean = Path(tmp) / "clean"
            self._stage(clean, self.RUST_REL)
            self._stage(clean, self.LEAN_REL)
            self.assertEqual(gmut.validate_property_taxonomy(clean), [])
            tcb = _make_tcb_copy_root(Path(tmp) / "tcb")
            self.assertEqual(gmut.validate_catalog_invariants(tcb), [])
            # No registry under an isolated test root: skipped unless required.
            self.assertEqual(gmut.validate_property_taxonomy(tcb), [])
            required = gmut.validate_catalog_invariants(tcb, require_rust_taxonomy=True)
            self.assertEqual(len(required), 1, required)
            self.assertIn(f"property taxonomy: cannot read {self.RUST_REL}", required[0])
            self._stage(tcb, self.RUST_REL, 'Self::UninitRead => "uninit_read",', 'Self::UninitRead => "uninit",')
            drifted = gmut.validate_catalog_invariants(tcb)
            self.assertEqual(len(drifted), 1, drifted)
            self.assertIn("property_classes[10].id is 'uninit', expected 'uninit_read'", drifted[0])
            # A registry that is present but unreadable is an error, not "absent".
            dangling = Path(tmp) / "dangling"
            (dangling / self.RUST_REL).parent.mkdir(parents=True)
            os.symlink("/nonexistent/property_registry.rs", dangling / self.RUST_REL)
            self.assertTrue(
                any("cannot read" in e for e in gmut.validate_property_taxonomy(dangling))
            )

        # The live checkout must have both sources: deleting one cannot pass.
        with mock.patch.object(gmut, "_RUST_TAXONOMY_REL", "crates/cargo-anneal/src/gone.rs"):
            self.assertTrue(any("cannot read" in e for e in gmut.validate_property_taxonomy(ANNEAL_ROOT)))
        with mock.patch.object(gmut, "_LEAN_TAXONOMY_REL", "theory/Anneal/Gone.lean"):
            self.assertTrue(any("cannot read" in e for e in gmut.validate_property_taxonomy(ANNEAL_ROOT)))
        # Drift in the Python constants themselves is caught against the live sources.
        with mock.patch.object(
            gmut, "_PROPERTY_CLASS_ROWS",
            (("arith_overflow",) + gmut._PROPERTY_CLASS_ROWS[0][1:], *gmut._PROPERTY_CLASS_ROWS[1:]),
        ):
            errors = gmut.validate_property_taxonomy(ANNEAL_ROOT)
            self.assertTrue(any("CANONICAL_PROPERTY_CLASSES is not" in e for e in errors), errors)
            self.assertTrue(any("property_registry.rs property_classes[0].id" in e for e in errors), errors)
            self.assertTrue(any("SpecBoundaryGuards.lean property_classes[0].id" in e for e in errors), errors)

    def test_taxonomy_drift_against_the_lean_theory_fails_closed(self) -> None:
        cases: tuple[tuple[str, str, str, str], ...] = (
            (
                "class slug",
                '  | .pointerDereference => "pointer_deref"\n',
                '  | .pointerDereference => "pointer_dereference"\n',
                "SpecBoundaryGuards.lean property_classes[3].id is 'pointer_dereference'",
            ),
            (
                "guard slug",
                '  | .errorBranchWildcard => "error_branch_wildcard"\n',
                '  | .errorBranchWildcard => "error_wildcard"\n',
                "SpecBoundaryGuards.lean spec_boundary_guards[2].id is 'error_wildcard'",
            ),
            (
                "guard vacuity class",
                "  | .errorBranchWildcard => .survivedAllMutants\n",
                "  | .errorBranchWildcard => .specViolation\n",
                "spec_boundary_guards[2].vacuity_class is 'SpecViolation'",
            ),
            (
                "class order",
                "  [.arithmeticOverflow, .shiftBounds, .divRemUb,",
                "  [.shiftBounds, .arithmeticOverflow, .divRemUb,",
                "`PropertyClassTag.all` is not the constructor declaration order",
            ),
            (
                "waivability",
                "  | .unsupportedFallback => false\n  | _ => true\n",
                "  | .unsupportedFallback => false\n  | .loopTermination => false\n  | _ => true\n",
                "property_classes[7].is_waivable is False",
            ),
            (
                "unterminated comment",
                "inductive PropertyClassTag : Type where",
                "/- inductive PropertyClassTag : Type where",
                "malformed taxonomy source",
            ),
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            for idx, (label, old, new, needle) in enumerate(cases):
                root = Path(tmp) / f"case{idx}"
                self._stage(root, self.LEAN_REL, old, new)
                errors = gmut.validate_property_taxonomy(root)
                self.assertTrue(any(needle in e for e in errors), (label, errors))

    # -- guard tagging --------------------------------------------------

    def test_every_cataloged_guard_names_its_canonical_property_class(self) -> None:
        self.assertEqual(
            {g.guard_id: g.property_class for g in gmut.MIR_SEMANTICS_GUARDS},
            self.EXPECTED_GUARD_CLASSES,
        )
        self.assertEqual(tuple(gmut.PROPERTY_CLASS_DISPOSITIONS), gmut.CANONICAL_PROPERTY_CLASSES)
        guarded = {g.property_class for g in gmut.MIR_SEMANTICS_GUARDS}
        for class_id, disposition in gmut.PROPERTY_CLASS_DISPOSITIONS.items():
            self.assertIn(disposition.coverage, gmut.PROPERTY_CLASS_COVERAGE_KINDS, class_id)
            self.assertTrue(disposition.rationale.strip(), class_id)
            self.assertEqual(
                disposition.coverage == "single_step_ub_guarded", class_id in guarded, class_id
            )
        self.assertEqual(gmut.PROPERTY_CLASS_DISPOSITIONS["loop_termination"].coverage, "coinductive_non_ub")
        self.assertEqual(
            gmut.PROPERTY_CLASS_DISPOSITIONS["unsupported_fallback"].coverage, "fail_closed_non_ub"
        )
        self.assertEqual(gmut._guard_property_class_errors(), [])

        # A synthetic guard may still be built without `property_class` ...
        first = gmut.MIR_SEMANTICS_GUARDS[0]
        synthetic = gmut.MirSemanticsGuard(
            "synthetic", first.target_file, first.target_module, "d", "a", "b",
            "sanity_x", "s", "refute_x", "r",
        )
        self.assertEqual(synthetic.property_class, gmut.PROPERTY_CLASS_UNSPECIFIED)
        self.assertEqual(
            gmut.GuardResult("g", "f", "m", False, "KILLED", 0.0, "ok").property_class, ""
        )
        # ... but the catalog gate rejects a missing, unknown or mis-dispositioned class.
        for label, catalog, needle in (
            ("missing", _replace_guard("div_by_zero", property_class=""),
             "div_by_zero: missing explicit property_class"),
            ("unknown", _replace_guard("div_by_zero", property_class="DivRemUb"),
             "div_by_zero: unknown property_class 'DivRemUb'"),
            ("coinductive", _replace_guard("div_by_zero", property_class="loop_termination"),
             "PROPERTY_CLASS_DISPOSITIONS['loop_termination'] is 'coinductive_non_ub' but the "
             "catalog tags 1 guard(s)"),
            ("uncataloged", _replace_guard("div_by_zero", property_class="arithmetic_overflow"),
             "PROPERTY_CLASS_DISPOSITIONS['arithmetic_overflow'] is 'single_step_ub_uncataloged'"),
            ("emptied class",
             tuple(dataclasses.replace(g, property_class="shift_bounds")
                   if g.property_class == "uninit_read" else g for g in gmut.MIR_SEMANTICS_GUARDS),
             "PROPERTY_CLASS_DISPOSITIONS['uninit_read'] is 'single_step_ub_guarded' but the "
             "catalog tags 0 guard(s)"),
        ):
            with mock.patch.object(gmut, "MIR_SEMANTICS_GUARDS", catalog):
                errors = gmut.validate_catalog_invariants(ANNEAL_ROOT)
            self.assertTrue(any(needle in e for e in errors), (label, errors))
        with mock.patch.dict(gmut.PROPERTY_CLASS_DISPOSITIONS, clear=False) as patched:
            del patched["uninit_read"]
            self.assertTrue(
                any("must list exactly the 12 canonical" in e for e in gmut._guard_property_class_errors())
            )

    def test_property_class_is_reported_per_guard_result_and_class(self) -> None:
        listed = json.loads(_run_cli(["--list", "--json"]).stdout)
        self.assertEqual(
            {g["guard_id"]: g["property_class"] for g in listed["guards"]}, self.EXPECTED_GUARD_CLASSES
        )
        self.assertEqual(listed["property_classes"], list(gmut.CANONICAL_PROPERTY_CLASSES))
        self.assertEqual(listed["spec_boundary_guards"], list(gmut.CANONICAL_SPEC_BOUNDARY_GUARDS))
        summary = listed["property_class_summary"]
        self.assertEqual([row["property_class"] for row in summary], list(gmut.CANONICAL_PROPERTY_CLASSES))
        self.assertEqual([row["rank"] for row in summary], list(range(12)))
        self.assertEqual(sum(row["selected"] for row in summary), 20)
        self.assertEqual(
            {row["property_class"]: row["cataloged"] for row in summary if row["cataloged"]},
            {"shift_bounds": 4, "div_rem_ub": 4, "pointer_deref": 3, "discriminant_validity": 4,
             "memory_copy_overlap": 3, "uninit_read": 2},
        )
        text = _run_cli(["--list"]).stdout
        self.assertIn("Property classes with selected guards: shift_bounds=4, div_rem_ub=4", text)
        self.assertTrue(text.rstrip().endswith("Total cataloged guards: 20"))

        fatal = gmut._fatal_report("all", "boom")
        self.assertEqual(len(fatal["property_class_summary"]), 12)
        self.assertTrue(all(row["selected"] == 0 for row in fatal["property_class_summary"]))

        def fake_compile(*args: object, **kwargs: object) -> subprocess.CompletedProcess[str]:
            out_dir, mod = args[3], args[2]
            assert isinstance(out_dir, Path) and isinstance(mod, str)
            (out_dir / f"{mod}.olean").parent.mkdir(parents=True, exist_ok=True)
            (out_dir / f"{mod}.olean").write_bytes(b"fake")
            return subprocess.CompletedProcess(args=["fake"], returncode=0, stdout="", stderr="")

        def fake_check(guard: gmut.MirSemanticsGuard, **kwargs: object) -> gmut.GuardResult:
            # Built positionally, without a class: the suite stamps the catalog's.
            status = "SURVIVED" if guard.guard_id == "shift_oob" else "KILLED"
            return gmut.GuardResult(
                guard.guard_id, guard.target_file, guard.target_module, guard.quick, status, 0.0, "x"
            )

        with (
            mock.patch.object(gmut, "_compile_module", side_effect=fake_compile),
            mock.patch.object(gmut, "_check_one_mir_guard", side_effect=fake_check),
        ):
            report = gmut.run_guard_mutation_suite(
                anneal_root=ANNEAL_ROOT,
                lean_bin=Path("/nonexistent/lean"),
                guard_filters=["div_by_zero", "rem_by_zero", "shift_oob"],
                jobs=2,
                reuse_lake_cache=False,
            )
        self.assertEqual(set(report), set(fatal))
        self.assertEqual(
            {r["guard_id"]: r["property_class"] for r in report["results"]},
            {"div_by_zero": "div_rem_ub", "rem_by_zero": "div_rem_ub", "shift_oob": "shift_bounds"},
        )
        rows = {row["property_class"]: row for row in report["property_class_summary"]}
        self.assertEqual(
            (rows["div_rem_ub"]["selected"], rows["div_rem_ub"]["killed"], rows["div_rem_ub"]["cataloged"]),
            (2, 2, 4),
        )
        self.assertEqual(
            (rows["shift_bounds"]["killed"], rows["shift_bounds"]["survived"], rows["shift_bounds"]["guard_ids"]),
            (0, 1, ["shift_oob"]),
        )
        self.assertEqual(rows["loop_termination"]["coverage"], "coinductive_non_ub")
        self.assertFalse(report["ok"])

    # -- error-branch wildcard probe -------------------------------------

    def _patterns(self, source: str, language: str = "auto") -> list[str]:
        findings = gmut.detect_postcondition_error_wildcards(source, language=language)
        for finding in findings:
            self.assertEqual(finding.guard_id, "error_branch_wildcard")
            self.assertIn(finding.pattern, gmut.ERROR_WILDCARD_PATTERNS)
        return [finding.pattern for finding in findings]

    def test_wildcard_detector_flags_every_vacuous_error_arm_shape(self) -> None:
        cases: tuple[tuple[str, str], ...] = (
            ("| Err _ => True", "err_arm_true"),
            ("| .err _ => True", "err_arm_true"),
            ("| .error _ => True", "err_arm_true"),
            ("| .err e => True", "err_arm_true"),
            ("| .err (_ : String) => True", "err_arm_true"),
            ("| Except.error _ => True", "err_arm_true"),
            ("| .ub => True", "ub_arm_true"),
            ("| .unsupported => True", "unsupported_arm_true"),
            ("| MirStepNode.fail .ub => True", "ub_arm_true"),
            ("| .fail .unsupported => True", "unsupported_arm_true"),
            ("| .fail _ => True", "ub_arm_true"),
            ("| .ub | .unsupported => True", "ub_arm_true"),
            ("| .unsupported | .ub => True", "unsupported_arm_true"),
            ("| .ub => (True)", "ub_arm_true"),
            ("| .ub => ((True))", "ub_arm_true"),
            ("| .err _ => trivial", "err_arm_true"),
            ("| .err _ => by trivial", "err_arm_true"),
            ("| .err _ => ¬False", "err_arm_true"),
            ("| .err _ => Not False", "err_arm_true"),
            ("| .err _ => True ∧ True", "err_arm_true"),
            ("| .err _ => True ∨ x = 3", "err_arm_true"),
            ("| .err _ => x = x", "err_arm_true"),
            ("| .err _ =>\n      True", "err_arm_true"),
            ("match out with .err _ => True", "err_arm_true"),
            ("fun x out => match out with | .ok v => v = x + 1 | .ub => True", "ub_arm_true"),
            (
                "def post (x : Nat) : Except String Nat → Prop\n  | .ok v => v = x + 1\n"
                "  | .error _ => True\n\ntheorem next : True := trivial",
                "err_arm_true",
            ),
            ("| .ok v => v = 1 | _ => True", "catch_all_arm_true"),
            ("Err(_) => true", "err_arm_true"),
            ("Err(..) => true", "err_arm_true"),
            ("Err(e) => true", "err_arm_true"),
            ("Err(_) => (true)", "err_arm_true"),
            ("Err(_) => ((true))", "err_arm_true"),
            ("Err(_) => { true }", "err_arm_true"),
            ("Err(_) => { return true; }", "err_arm_true"),
            ("Err(_) => true,", "err_arm_true"),
            ("Err(_) if true => true", "err_arm_true"),
            ("Err(_) => true || x == 3", "err_arm_true"),
            ("Err(_) => !false", "err_arm_true"),
            ("Err(_) => true && true", "err_arm_true"),
            ("Err(_) => true as bool", "err_arm_true"),
            ("Err(_) => 1 == 1", "err_arm_true"),
            ("Ok(0) | Err(_) => true", "err_arm_true"),
            ("Some(Ok(_) | Err(_)) => true", "err_arm_true"),
            ("(Err(_), _) => true", "err_arm_true"),
            ("Err(E::A | _) => true", "err_arm_true"),
            ("Err(()) => true", "err_arm_true"),
            ("Result::Err(_) => true", "err_arm_true"),
            ("match out { Ok(v) => *v == x + 1, Err(_) => true }", "err_arm_true"),
            ("|out: &Result<u32, E>| match out {\n    Ok(v) => *v == x + 1,\n    Err(_) => true,\n}",
             "err_arm_true"),
            ("SemanticOutcome::Ub => true", "ub_arm_true"),
            ("SemanticOutcome::Unsupported => true", "unsupported_arm_true"),
            ("matches!(out, Ok(_) | Err(_))", "matches_any_err"),
            ("matches!(out, Ok(v) | _)", "matches_any_err"),
            ("match out { Ok(v) => *v == 1, _ => true }", "catch_all_arm_true"),
        )
        for source, expected in cases:
            self.assertEqual(self._patterns(source), [expected], source)
        lean = gmut.detect_postcondition_error_wildcards(
            "match out with\n  | .ok v => v = spec x\n  | .err _ => True\n  | .ub => False\n"
        )
        self.assertEqual(
            [(f.pattern, f.language, f.line, f.column) for f in lean], [("err_arm_true", "lean", 3, 12)]
        )
        self.assertIn(". err _ => True", lean[0].arm)

    def test_wildcard_detector_ignores_guarded_arms_comments_and_literals(self) -> None:
        for source in (
            "| .ub => False",
            "| Err e => e = .overflow",
            "| .err .overflow => True",
            "| .ok v => v = 1",
            "| .err _ => x = y",
            "| .err _ => True ∧ x = 3",
            "| .err _ => ¬True",
            "| .ok v => v = 1\n| .ub => False\n| .unsupported => False",
            "-- | .ub => True\n| .ub => False",
            "/- | .ub => True /- nested | .err _ => True -/ -/\n| .ub => False",
            'def doc := "| .ub => True"\n',
            "fun x => True",
            "def isWaivable : T → Bool\n  | .unsupportedFallback => false\n  | _ => true\n",
            "| .none => True",
            "Err(E::Overflow) => true",
            "Err(Unsupported) => true",
            "Err(E::A | E::B) => true",
            "Err(0) => true",
            "Err(_) => false",
            "Err(_) => x == y",
            "Err(_) if cond => true",
            "Err(e) => *e == E::Overflow",
            "match out { Ok(v) => *v == x + 1, Err(E::Overflow) => x == u32::MAX }",
            "// Err(_) => true\nErr(_) => false",
            "/* Err(_) => true /* nested */ */ Err(_) => false",
            'let s = "Err(_) => true"; let r = r#"Err(_) => "true"#;',
            "let c = '\"'; let d = b'\\''; fn f<'a>(x: &'a str) -> bool { x == \"Err(_) => true\" }",
            "!matches!(out, Err(_))",
            "match n { 0 => true, _ => true }",
        ):
            self.assertEqual(self._patterns(source), [], source)
        # Explicit languages: a Rust arm is not a Lean arm and vice versa.
        self.assertEqual(self._patterns("-- note\n| .ub => True", language="lean"), ["ub_arm_true"])
        self.assertEqual(self._patterns("// Err(_) => true", language="rust"), [])
        with self.assertRaises(ValueError):
            gmut.detect_postcondition_error_wildcards("x", language="ocaml")

    def test_wildcard_detector_fails_closed_on_unlexable_sources(self) -> None:
        for source, language in (
            ("/- unclosed\n| .ub => True", "lean"),
            ('def s := "unterminated\n| .ub => False', "lean"),
            ('| .ub => s!"{x}"', "lean"),
            ("match out with (| .ub => False", "lean"),
            ("/* unclosed\nErr(_) => true", "rust"),
            ('let s = "unterminated;\nErr(_) => false', "rust"),
            ('let s = r#"unterminated";\nErr(_) => false', "rust"),
            ("match out { Ok(v) => true, Err(_) => false", "rust"),
            ("match out { Ok(v) => true) }", "rust"),
            ("/- unclosed | .ub => True", "auto"),
        ):
            self.assertIn("unclosed_literal_or_comment", self._patterns(source, language), source)
            report = gmut.verify_postcondition_kills_error_mutants(source, language=language)
            self.assertFalse(report["ok"], source)
            self.assertGreater(report["errors"], 0, source)

    def test_wildcard_probe_kills_guarded_arms_and_survives_injected_wildcards(self) -> None:
        self.assertEqual(gmut.error_wildcard_probe_self_check(), [])
        guarded_lean = (
            "def post (x : Nat) : Outcome Nat → Prop\n"
            "  | .ok v => v = x + 1\n"
            "  | .err e => e = .overflow\n"
            "  | .ub => False\n"
            "  | .unsupported => False\n"
        )
        report = gmut.verify_postcondition_kills_error_mutants(guarded_lean)
        self.assertEqual(
            (report["ok"], report["guard_id"], report["killed"], report["survived"], report["errors"]),
            (True, "error_branch_wildcard", 3, 0, 0),
        )
        self.assertEqual(report["findings"], [])
        self.assertEqual({r["status"] for r in report["results"]}, {"KILLED"})

        # Injecting each vacuous arm lets exactly that mutant survive.
        for old, new, mutant, pattern in (
            ("| .ub => False", "| .ub => True", "ub", "ub_arm_true"),
            ("| .err e => e = .overflow", "| Err _ => True", "err", "err_arm_true"),
            ("| .unsupported => False", "| .unsupported => True", "unsupported", "unsupported_arm_true"),
        ):
            mutated = guarded_lean.replace(old, new)
            self.assertNotEqual(mutated, guarded_lean)
            probe = gmut.probe_postcondition_error_wildcard_mutant(mutated, mutant)
            self.assertEqual(
                (probe["status"], probe["guard_id"], probe["pattern"], probe["language"]),
                ("SURVIVED", "error_branch_wildcard", pattern, "lean"),
                mutated,
            )
            self.assertIn(new.lstrip("| ").split(" =>")[0].split()[0].lstrip("."), probe["detail"])
            report = gmut.verify_postcondition_kills_error_mutants(mutated)
            self.assertEqual((report["ok"], report["survived"], report["killed"]), (False, 1, 2))
            self.assertEqual([f["pattern"] for f in report["findings"]], [pattern])
            self.assertEqual(report["findings"][0]["guard_id"], "error_branch_wildcard")
            # The other mutants are still killed.
            for other in gmut.ERROR_MUTANT_KINDS:
                if other != mutant:
                    self.assertEqual(
                        gmut.probe_postcondition_error_wildcard_mutant(mutated, other)["status"], "KILLED"
                    )

        guarded_rust = "match out { Ok(v) => *v == x + 1, Err(e) => *e == E::Overflow }"
        self.assertEqual(
            gmut.probe_postcondition_error_wildcard_mutant(guarded_rust, "err", language="rust")["status"],
            "KILLED",
        )
        report = gmut.verify_postcondition_kills_error_mutants(guarded_rust)
        self.assertEqual((report["ok"], report["killed"], report["unmatched"]), (True, 1, 2))
        # `ub` is not an outcome of a Rust `Result`: demanding its kill fails.
        self.assertFalse(
            gmut.verify_postcondition_kills_error_mutants(guarded_rust, mutants=("err", "ub"))["ok"]
        )
        for vacuous in (
            "match out { Ok(v) => *v == x + 1, Err(_) => true }",
            "match out { Ok(v) => *v == x + 1, Err(..) => true }",
            "match out { Ok(v) => *v == x + 1, _ => true }",
            "matches!(out, Ok(_) | Err(_))",
        ):
            probe = gmut.probe_postcondition_error_wildcard_mutant(vacuous, "err")
            self.assertEqual((probe["status"], probe["guard_id"]), ("SURVIVED", "error_branch_wildcard"), vacuous)
            self.assertFalse(gmut.verify_postcondition_kills_error_mutants(vacuous)["ok"], vacuous)

        # First covering arm wins; a payload-specific arm alone does not cover.
        self.assertEqual(
            gmut.probe_postcondition_error_wildcard_mutant(
                "| .ok v => v = 1\n| .err .overflow => True\n| .err _ => False\n", "err"
            )["status"],
            "KILLED",
        )
        self.assertEqual(
            gmut.probe_postcondition_error_wildcard_mutant(
                "| .ok v => v = 1\n| .err .overflow => False\n| .err _ => True\n", "err"
            )["status"],
            "SURVIVED",
        )
        # A postcondition that inspects no error outcome kills nothing: not ok.
        for blind in ("fun out => True", "| .ok v => v = 1", "match out { Ok(v) => *v == 1 }"):
            report = gmut.verify_postcondition_kills_error_mutants(blind)
            self.assertEqual((report["ok"], report["killed"]), (False, 0), blind)
        with self.assertRaises(ValueError):
            gmut.probe_postcondition_error_wildcard_mutant("| .ub => True", "panic")
        # A broken probe is reported by the self-check, not trusted.
        with mock.patch.object(gmut, "_const_truth", return_value=None):
            self.assertNotEqual(gmut.error_wildcard_probe_self_check(), [])

    def test_check_spec_wildcards_cli_exit_codes(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            root = Path(tmp)
            clean_lean = root / "Clean.lean"
            clean_lean.write_text(
                "-- | .ub => True is rejected\ndef post : Outcome Nat → Prop\n"
                "  | .ok v => v = 1\n  | .ub => False\n",
                encoding="utf-8",
            )
            clean_rs = root / "clean.rs"
            clean_rs.write_text(
                "// Err(_) => true\nfn post(out: &Result<u32, E>) -> bool {\n"
                "    match out { Ok(v) => *v == 1, Err(e) => *e == E::Overflow }\n}\n",
                encoding="utf-8",
            )
            bad_lean = root / "Bad.lean"
            bad_lean.write_text(
                "def post : Outcome Nat → Prop\n  | .ok v => v = 1\n  | .ub => True\n", encoding="utf-8"
            )
            bad_rs = root / "bad.rs"
            bad_rs.write_text(
                "fn post(out: &Result<u32, E>) -> bool {\n    match out { Ok(v) => *v == 1, Err(_) => true }\n}\n",
                encoding="utf-8",
            )
            binary = root / "binary.lean"
            binary.write_bytes(b"\xff\xfe| .ub => True")

            ok = _run_cli(["--check-spec-wildcards", str(clean_lean), str(clean_rs)])
            self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)
            self.assertIn("2 file(s) scanned, 0 finding(s), 0 error(s)", ok.stdout)

            bad = _run_cli(["--check-spec-wildcards", str(clean_lean), str(bad_lean), str(bad_rs), "--json"])
            self.assertEqual(bad.returncode, 1)
            report = json.loads(bad.stdout)
            self.assertEqual(
                (report["ok"], report["guard_id"], report["checked"], report["errors"]),
                (False, "error_branch_wildcard", 3, []),
            )
            self.assertEqual(
                [(Path(f["path"]).name, f["pattern"], f["language"], f["line"]) for f in report["findings"]],
                [("Bad.lean", "ub_arm_true", "lean", 3), ("bad.rs", "err_arm_true", "rust", 2)],
            )
            text = _run_cli(["--check-spec-wildcards", str(bad_lean)])
            self.assertEqual(text.returncode, 1)
            self.assertIn(f"{bad_lean}:3:9: error_branch_wildcard [ub_arm_true]", text.stdout)

            for unreadable in (root / "missing.lean", root, binary):
                res = _run_cli(["--check-spec-wildcards", str(clean_lean), str(unreadable)])
                self.assertEqual(res.returncode, 1, unreadable)
                self.assertIn("cannot read", res.stderr, unreadable)

            # `--json-out` is fail-closed: a stale pass is replaced even when the
            # scan fails, and an unwritable sink fails the run.
            out = root / "out" / "report.json"
            self.assertEqual(
                _run_cli(["--check-spec-wildcards", str(clean_lean), "--json-out", str(out)]).returncode, 0
            )
            self.assertTrue(json.loads(out.read_text(encoding="utf-8"))["ok"])
            self.assertEqual(
                _run_cli(["--check-spec-wildcards", str(bad_lean), "--json-out", str(out)]).returncode, 1
            )
            failed = json.loads(out.read_text(encoding="utf-8"))
            self.assertEqual((failed["ok"], len(failed["findings"])), (False, 1))
            pending = gmut.check_spec_wildcard_paths(())
            self.assertEqual((pending["ok"], pending["checked"]), (False, 0))
            self.assertEqual(set(pending), set(failed))
            blocked = _run_cli(
                ["--check-spec-wildcards", str(clean_lean), "--json-out", str(clean_rs / "x.json")]
            )
            self.assertEqual(blocked.returncode, 1)
            self.assertIn("cannot write", blocked.stderr)

            for usage in (
                ["--check-spec-wildcards"],
                ["--check-spec-wildcards", str(clean_lean), "--list"],
                ["--check-spec-wildcards", str(clean_lean), "--quick"],
                ["--check-spec-wildcards", str(clean_lean), "--guard", "div_by_zero"],
            ):
                self.assertEqual(_run_cli(usage).returncode, 2, usage)
            # A probe that cannot tell a wildcard from a guard refuses to pass.
            with mock.patch.object(gmut, "_const_truth", return_value=None):
                broken = gmut.check_spec_wildcard_paths([clean_lean])
            self.assertFalse(broken["ok"])
            self.assertTrue(broken["errors"])

        # The live Lean theory states the wildcard arms it proves vacuous; the
        # frozen taxonomy sources themselves must stay scannable.
        live = gmut.check_spec_wildcard_paths([ANNEAL_ROOT / self.LEAN_REL])
        self.assertEqual((live["checked"], live["errors"]), (1, []))
        self.assertTrue(all(f["guard_id"] == "error_branch_wildcard" for f in live["findings"]))


class GuardMutationEp2B1AdversarialTests(unittest.TestCase):
    """Pass B1 adversarial regressions for taxonomy parsing and the wildcard probe."""

    RUST_REL = "crates/cargo-anneal/src/property_registry.rs"
    LEAN_REL = "theory/Anneal/SpecBoundaryGuards.lean"

    def _stage(self, root: Path, rel: str, old: str | None = None, new: str = "") -> None:
        text = (ANNEAL_ROOT / rel).read_text(encoding="utf-8")
        if old is not None:
            self.assertEqual(text.count(old), 1, old)
            text = text.replace(old, new)
        dst = root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(text, encoding="utf-8")

    def _patterns(self, source: str, language: str = "auto") -> list[str]:
        return [f.pattern for f in gmut.detect_postcondition_error_wildcards(source, language=language)]

    def test_rust_block_arm_without_comma_and_struct_slice_at_patterns(self) -> None:
        # Rust block-bodied error arm followed by another arm without comma (`rustfmt` default).
        no_comma = (
            "match out {\n"
            "    Err(_) => {\n"
            "        true\n"
            "    }\n"
            "    Ok(v) => *v == x + 1,\n"
            "}"
        )
        self.assertEqual(self._patterns(no_comma, "rust"), ["err_arm_true"])
        self.assertEqual(
            gmut.probe_postcondition_error_wildcard_mutant(no_comma, "err", language="rust")["status"],
            "SURVIVED",
        )
        for source, expected in (
            ("match w { W { r: Err(_) } => true }", "err_arm_true"),
            ("match out { Ok(v) => *v == 1, Err { .. } => true }", "err_arm_true"),
            ("match out { Ok(v) => *v == 1, Outcome::Err { msg: _ } => true }", "err_arm_true"),
            ("match out { Ok(v) => *v == 1, e @ (Err(_)) => true }", "err_arm_true"),
            ("match out { Ok(v) => *v == 1, &(Err(_)) => true }", "err_arm_true"),
            ("match out { Ok(v) => *v == 1, Err(e @ _) => true }", "err_arm_true"),
            ("match out { Ok(v) => *v == 1, e @ _ => true }", "catch_all_arm_true"),
            ("match out { Ok(v) => *v == 1, (0 | _) => true }", "catch_all_arm_true"),
            ("match arr { [_, Err(_)] => true, _ => false }", "err_arm_true"),
            ("match out { Ok(v) => *v == 1, Err(_) => { return true; false } }", "err_arm_true"),
            ("match out { Ok(v) => *v == 1, Err(_) => if true { true } else { false } }", "err_arm_true"),
            ("match out { Ok(v) => *v == 1, Err(_) => !cond == !cond }", "err_arm_true"),
            ("match out { Ok(v) => *v == 1, Outcome::Fail(_) => true }", "ub_arm_true"),
            ('let _ = cr#"Err(_) => true"#; match out { Ok(v) => *v == 1, Err(_) => true }', "err_arm_true"),
        ):
            self.assertEqual(self._patterns(source, "rust"), [expected], source)

        # Early-return guard inside a Rust block must NOT be misclassified as constant truth.
        guarded_block = (
            "match out {\n"
            "    Ok(v) => *v == x + 1,\n"
            "    Err(e) => { if *e != E::Overflow { return false; }; true },\n"
            "}"
        )
        self.assertEqual(self._patterns(guarded_block, "rust"), [])
        self.assertEqual(
            gmut.probe_postcondition_error_wildcard_mutant(guarded_block, "err", language="rust")["status"],
            "KILLED",
        )
        # C raw string hiding a fake arm must NOT trigger a finding.
        self.assertEqual(
            self._patterns('let s = cr#"Err(_) => true"#; match out { Err(_) => false }', "rust"),
            [],
        )

    def test_lean_records_angle_tuples_let_quantifiers_dedent_and_multi_match_scopes(self) -> None:
        for source, expected in (
            ("| ⟨_, .ub⟩ => True", "ub_arm_true"),
            ("| { val := .err _ } => True", "err_arm_true"),
            ("| .ub => Bool.true", "ub_arm_true"),
            ("| .ub => ∀ _ : Nat, True", "ub_arm_true"),
            ("| .ub => forall x, x = x", "ub_arm_true"),
            ("| .ub => (x) = x", "ub_arm_true"),
            ("| .ub => if true then True else False", "ub_arm_true"),
            ("| .ub => by exact True.intro", "ub_arm_true"),
            ("| .ub => by constructor", "ub_arm_true"),
            ("| .ub => let _ := 0; True", "ub_arm_true"),
            ("match out with\n| .ok v => v = 1\n| .ub =>\nTrue\n", "ub_arm_true"),
            ("-- note //\nmatch out with .ub => trivial", "ub_arm_true"),
            ("-- let ok\nmatch out with Err _ => trivial", "err_arm_true"),
        ):
            self.assertEqual(self._patterns(source), [expected], source)

        # Unclosed Lean guillemet fails closed.
        self.assertEqual(self._patterns("def «unclosed := match out with | .ub => False", "lean"), ["unclosed_literal_or_comment"])

        # Lean `¬ x = x` is `¬ (x = x)` = False, not True.
        self.assertEqual(self._patterns("| .ub => ¬ x = x", "lean"), [])

        # Two sequential `match` expressions in one Lean `def` must not mask each other!
        two_matches = (
            "def post (other out : Outcome Nat) : Prop :=\n"
            "  let helper := match other with\n"
            "    | .ub => False\n"
            "    | _ => True\n"
            "  match out with\n"
            "  | .ok v => v = 1\n"
            "  | .ub => True\n"
        )
        self.assertEqual(
            gmut.probe_postcondition_error_wildcard_mutant(two_matches, "ub", language="lean")["status"],
            "SURVIVED",
        )
        self.assertFalse(gmut.verify_postcondition_kills_error_mutants(two_matches, language="lean")["ok"])

        # Separate `match` on a non-outcome must not inherit `ok_groups` from an earlier `match out`.
        separate_ok = (
            "def post (x : Nat) (out : Outcome Nat) : Prop :=\n"
            "  let a := match out with\n"
            "    | .ok v => v = 1\n"
            "    | .ub => False\n"
            "  match x with\n"
            "  | 0 => True\n"
            "  | _ => True\n"
        )
        self.assertEqual(self._patterns(separate_ok, "lean"), [])

    def test_taxonomy_parser_blocks_extra_statements_extra_lean_ctors_and_empty_root(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-b1-") as tmp:
            # Sneaky extra waiver call in `for_partial_correctness` without `PropertyDisposition::`.
            r1 = Path(tmp) / "sneaky_partial"
            self._stage(
                r1,
                self.RUST_REL,
                "        reg\n    }\n\n    /// Select the canonical",
                "        reg.waive(PropertyClass::DivRemUb);\n        reg\n    }\n\n    /// Select the canonical",
            )
            errs = gmut.validate_property_taxonomy(r1)
            self.assertTrue(any("for_partial_correctness" in e for e in errs), errs)

            # Extra Lean constructor with parameters after the 12 nullary constructors.
            r2 = Path(tmp) / "extra_lean_ctor"
            self._stage(
                r2,
                self.LEAN_REL,
                "  | unsupportedFallback\n  deriving DecidableEq",
                "  | unsupportedFallback\n  | extra (n : Nat)\n  deriving DecidableEq",
            )
            errs2 = gmut.validate_property_taxonomy(r2)
            self.assertTrue(any("constructor this parser cannot read" in e for e in errs2), errs2)

            # `--taxonomy-json` pointed at an empty directory must fail closed (not print manifest).
            empty = Path(tmp) / "empty"
            empty.mkdir()
            res = _run_cli(["--taxonomy-json", "--anneal-root", str(empty)])
            self.assertEqual(res.returncode, 1)
            self.assertEqual(res.stdout, "")
            self.assertIn("cannot read", res.stderr)

            # `--check-spec-wildcards` rejects FIFO without blocking and emits consistent JSON on sink error.
            fifo = Path(tmp) / "pipe.lean"
            os.mkfifo(fifo)
            res_fifo = _run_cli(["--check-spec-wildcards", str(fifo), "--json"])
            self.assertEqual(res_fifo.returncode, 1)
            self.assertFalse(json.loads(res_fifo.stdout)["ok"])

            clean = Path(tmp) / "clean.lean"
            clean.write_text("| .ub => False\n", encoding="utf-8")
            blocked = _run_cli(
                ["--check-spec-wildcards", str(clean), "--json", "--json-out", str(clean / "x.json")]
            )
            self.assertEqual(blocked.returncode, 1)
            blocked_json = json.loads(blocked.stdout)
            self.assertFalse(blocked_json["ok"])
            self.assertIsNotNone(blocked_json["fatal_error"])


class GuardMutationEp2A1AdversarialTests(unittest.TestCase):
    """Pass A1 adversarial regressions for taxonomy parsing, Lean/Rust lexing, and the wildcard probe."""

    RUST_REL = "crates/cargo-anneal/src/property_registry.rs"
    LEAN_REL = "theory/Anneal/SpecBoundaryGuards.lean"

    def _stage(self, root: Path, rel: str, old: str | None = None, new: str = "") -> None:
        text = (ANNEAL_ROOT / rel).read_text(encoding="utf-8")
        if old is not None:
            self.assertEqual(text.count(old), 1, old)
            text = text.replace(old, new)
        dst = root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(text, encoding="utf-8")

    def _patterns(self, source: str, language: str = "auto") -> list[str]:
        return [f.pattern for f in gmut.detect_postcondition_error_wildcards(source, language=language)]

    def test_lean_raw_strings_cannot_smuggle_vacuous_arms_inside_fake_block_comments(self) -> None:
        # In Lean 4, `#"a"/-"#` is a single raw string literal; a scanner that only knew
        # `r#"..."#` opened a fake `/-` comment across `| .ub => True`!
        smuggled = (
            'def openRaw := #"a"/-"#\n'
            "def post : Outcome Nat → Prop\n"
            "  | .ok v => v = 1\n"
            "  | .ub => True\n"
            'def closeRaw := #"a"-/"#\n'
        )
        self.assertEqual(self._patterns(smuggled, "lean"), ["ub_arm_true"])
        self.assertEqual(
            gmut.probe_postcondition_error_wildcard_mutant(smuggled, "ub", language="lean")["status"],
            "SURVIVED",
        )
        # Conversely, a vacuous arm inside a Lean `#"..."#` raw string is literal text, not code.
        in_raw = 'def doc := #"| .ub => True"#\ndef post : Outcome Nat → Prop\n  | .ub => False\n'
        self.assertEqual(self._patterns(in_raw, "lean"), [])
        # Unclosed Lean `#"` raw string and `s!#"{x}"#` interpolated raw string fail closed.
        for hazard in ('def s := #"unterminated\n| .ub => False', '| .ub => s!#"{x}"#'):
            self.assertEqual(self._patterns(hazard, "lean"), ["unclosed_literal_or_comment"])

    def test_lean_sequential_let_matches_and_pattern_matching_lambdas_never_collide(self) -> None:
        # Arms aligned with `let` (`arm_col == 3 < match_col == 19`) previously popped `lean_matches`
        # on the first arm and collapsed every `let ... := match` onto `match_id = -1`!
        two_let_matches = (
            "def post (other out : Outcome Nat) : Prop :=\n"
            "  let helper := match other with\n"
            "  | .ub => False\n"
            "  | _ => True\n"
            "  let actual := match out with\n"
            "  | .ok v => v = 1\n"
            "  | .ub => True\n"
            "  helper ∧ actual\n"
        )
        self.assertEqual(
            gmut.probe_postcondition_error_wildcard_mutant(two_let_matches, "ub", language="lean")["status"],
            "SURVIVED",
        )
        self.assertFalse(gmut.verify_postcondition_kills_error_mutants(two_let_matches, language="lean")["ok"])

        # Separate `let ... := match` on a `Nat` must not inherit `ok_groups` from an earlier `let` match.
        clean_two_let_matches = (
            "def post (x : Nat) (out : Outcome Nat) : Prop :=\n"
            "  let a := match out with\n"
            "  | .ok v => v = 1\n"
            "  | .ub => False\n"
            "  let b := match x with\n"
            "  | 0 => True\n"
            "  | _ => True\n"
            "  a ∧ b\n"
        )
        self.assertEqual(self._patterns(clean_two_let_matches, "lean"), [])

        # Sequential pattern-matching `fun | ...` expressions also get distinct match groups.
        two_funs = (
            "def post (other out : Outcome Nat) : Prop :=\n"
            "  let f := fun\n"
            "  | .ub => False\n"
            "  | _ => True\n"
            "  let g := fun\n"
            "  | .ok v => v = 1\n"
            "  | .ub => True\n"
            "  f other ∧ g out\n"
        )
        self.assertEqual(
            gmut.probe_postcondition_error_wildcard_mutant(two_funs, "ub", language="lean")["status"],
            "SURVIVED",
        )

    def test_expression_precedence_let_propagation_tautologies_and_pure_reflexivity(self) -> None:
        # Vacuous shapes that previously slipped past `_const_truth` / `_alt_head`.
        for source, lang, expected in (
            ("Result::<u32, E>::Err(_) => true", "rust", "err_arm_true"),
            ("<Result<u32, E>>::Err(_) => true", "rust", "err_arm_true"),
            ("Err([..]) => true", "rust", "err_arm_true"),
            ("Err(_) if if true { true } else { false } => true", "rust", "err_arm_true"),
            ("Err(_) => { let ok = true; ok }", "rust", "err_arm_true"),
            ("Err(_) => |_| true", "rust", "err_arm_true"),
            ("Err(e) => *e == 0 || *e != 0", "rust", "err_arm_true"),
            ("Err(_) => cond || !cond", "rust", "err_arm_true"),
            ("| .«ub» => «True»", "lean", "ub_arm_true"),
            ("| «Err» «e» => True", "lean", "err_arm_true"),
            ("| .ub =>\n  let _ := f 1 2\n  True", "lean", "ub_arm_true"),
            ("| .ub => let ok := True; ok", "lean", "ub_arm_true"),
            ("| .ub => have h : Prop := True; h", "lean", "ub_arm_true"),
            ("| .ub => fun _ => True", "lean", "ub_arm_true"),
            ("| .err e => e = 0 → e = 0", "lean", "err_arm_true"),
            ("| .ub => p ∨ ¬p", "lean", "ub_arm_true"),
        ):
            self.assertEqual(self._patterns(source, lang), [expected], source)

        # Sound constrained arms that must NOT false-fire:
        # 1. Lean `if c then False else False ∨ True` extends across `∨` (only True when `¬c`)!
        # 2. Rust `let _ = assert!(...);` / `let x = check(e)?;` have side effects / early exits!
        # 3. `f64::NAN == f64::NAN` and `iter.next() == iter.next()` are NOT reflexive tautologies!
        for guarded, lang in (
            ("| .err e => if e != .allowed then False else False ∨ True", "lean"),
            ("| .err e => if e = .allowed then False else False → False", "lean"),
            ("| .err e =>\n  let ok := e = .overflow\n  ok", "lean"),
            ("Err(e) => { let _ = assert!(*e == E::Overflow); true }", "rust"),
            ("Err(e) => { let _ = check(e)?; true }", "rust"),
            ("Err(e) => { let true = (*e == E::Overflow) else { panic!() }; true }", "rust"),
            ("Err(_) => f64::NAN == f64::NAN", "rust"),
            ("Err(_) => iter.next() == iter.next()", "rust"),
            ("Err(_) => cond && !cond", "rust"),
        ):
            self.assertEqual(self._patterns(guarded, lang), [], guarded)

        # `auto` language detection must not let Lean list-cons `::` + a quote in a Lean comment
        # trigger a bogus Rust `unclosed_literal_or_comment` error!
        clean_lean_cons = (
            '/- note with single " quote inside Lean comment -/\n'
            "def post (xs : List Nat) : Outcome Nat → Prop\n"
            "  | .ok v => xs = v :: []\n"
            "  | .ub => False\n"
        )
        self.assertEqual(self._patterns(clean_lean_cons, "auto"), [])

        # `@[simp]` and `#check` terminate a column-0 Lean arm body cleanly.
        at_and_hash = "def post : Outcome Nat → Prop\n| .ok v => v = 1\n| .ub => True\n@[simp]\ntheorem t : True := trivial\n"
        self.assertEqual(self._patterns(at_and_hash, "lean"), ["ub_arm_true"])

    def test_lean_all_list_continuation_and_require_lean_taxonomy_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-a1-") as tmp:
            r1 = Path(tmp) / "all_append"
            self._stage(
                r1,
                self.LEAN_REL,
                "  [.entryPointPrecondition, .fixedWidthGhostLength, .errorBranchWildcard]\n",
                "  [.entryPointPrecondition, .fixedWidthGhostLength, .errorBranchWildcard] ++ [.entryPointPrecondition]\n",
            )
            errs = gmut.validate_property_taxonomy(r1)
            self.assertTrue(any("SpecBoundaryGuardClass.all" in e for e in errs), errs)

            tcb = _make_tcb_copy_root(Path(tmp) / "tcb")
            lean_req = gmut.validate_catalog_invariants(tcb, require_lean_taxonomy=True)
            self.assertEqual(len(lean_req), 1, lean_req)
            self.assertIn(f"cannot read {self.LEAN_REL}", lean_req[0])


class GuardMutationEp2B2AdversarialTests(unittest.TestCase):
    """Round 2 adversarial regression tests for Shard A scanner/probe/lexing gaps."""

    def _patterns(self, source: str, language: str = "auto") -> list[str]:
        return [f.pattern for f in gmut.detect_postcondition_error_wildcards(source, language=language)]

    def test_rust_block_like_arms_without_commas_nested_ifs_matches_and_closures(self) -> None:
        # Block-like Rust arms without trailing commas (standard `rustfmt` output) must NOT swallow
        # the following `Ok(v)` arm or drop `ok_groups`.
        for source, expected in (
            (
                "match out {\n"
                "    Err(_) => if c { true } else { true }\n"
                "    Ok(v) => *v == 1,\n"
                "}\n",
                ["err_arm_true"],
            ),
            (
                "match out {\n"
                "    Err(_) => if c1 || c2 { true } else if c3 && c4 { true } else { true }\n"
                "    Ok(v) => *v == 1,\n"
                "}\n",
                ["err_arm_true"],
            ),
            (
                "match out {\n"
                "    Err(_) => match x { _ => true }\n"
                "    Ok(v) => *v == 1,\n"
                "}\n",
                ["err_arm_true"],
            ),
            (
                "match out {\n"
                "    Err(_) => match x {\n"
                "        A => { true }\n"
                "        B => { true }\n"
                "    }\n"
                "    | Ok(v) => *v == 1,\n"
                "}\n",
                ["err_arm_true"],
            ),
            (
                "match out {\n"
                "    Ok(v) => if c { *v == 1 } else { *v == 2 }\n"
                "    _ => true,\n"
                "}\n",
                ["catch_all_arm_true"],
            ),
            ("Err(_) => move |_| true", ["err_arm_true"]),
            ("Err(_) => move || true", ["err_arm_true"]),
            ("Err(_) => |_| -> bool { true }", ["err_arm_true"]),
            ("Err(_) => move |_: &E| -> bool { !false }", ["err_arm_true"]),
            ("Err(_) => unsafe { true }", ["err_arm_true"]),
            ("Err(e) => !(e == E::Overflow) || e == E::Overflow", ["err_arm_true"]),
            ("Err(_) => { let ok = !false; ok }", ["err_arm_true"]),
            ("Err(_) => { let _ = !x; true }", ["err_arm_true"]),
            ("Err(_) => { let mut ok = false; ok = !false; ok }", ["err_arm_true"]),
        ):
            self.assertEqual(self._patterns(source, "rust"), expected, source)
            self.assertEqual(
                gmut.probe_postcondition_error_wildcard_mutant(source, "err", language="rust")["status"],
                "SURVIVED",
                source,
            )

        # Sound constrained arms must NOT trigger false positives:
        # 1. Mutable reassignment of `ok` to a real error predicate.
        # 2. Compound assignment (`&=`) or helper assertion call inside a block.
        # 3. `!x && y || x && y` (evaluates to `y`, NOT `true`!).
        # 4. `if let Foo { a } = e { *a == 1 } else { false }` (brace inside `if let` pattern).
        # 5. `match x` whose arms disagree (`true` vs `false`).
        for guarded in (
            "Err(e) => { let mut ok = true; ok = *e == E::Overflow; ok }",
            "Err(e) => { let mut ok = true; ok &= *e == E::Overflow; ok }",
            "Err(e) => { assert_overflow(e); true }",
            "Err(e) => !x && y || x && y",
            "Err(e) => !a == b || a == b",
            "Err(e) => if let Foo { a } = e { *a == 1 } else { false }",
            "Err(e) => match e { E::Overflow => true, _ => false }",
            "Err(e) => if c1 || c2 { *e == E::Overflow } else if c3 { true } else { false }",
        ):
            self.assertEqual(self._patterns(guarded, "rust"), [], guarded)
            self.assertEqual(
                gmut.probe_postcondition_error_wildcard_mutant(guarded, "err", language="rust")["status"],
                "KILLED",
                guarded,
            )

    def test_lean_nested_if_pattern_lambdas_nested_match_let_shadowing_and_precedence(self) -> None:
        for source, expected in (
            ("| .ub => if c1 then True else if c2 then True else True", ["ub_arm_true"]),
            ("| .ub => if c1 then if c2 then True else True else True", ["ub_arm_true"]),
            ("| .ub => fun | _ => True", ["ub_arm_true"]),
            (
                "def post : Outcome Nat → Prop\n"
                "  | .err _ => fun | _ => True\n"
                "  | .ok v => v = 1\n",
                ["err_arm_true"],
            ),
            (
                "def post (x : Bool) : Outcome Nat → Prop\n"
                "  | .ok v => v = 1\n"
                "  | .err _ =>\n"
                "    match x with\n"
                "    | true => True\n"
                "    | false => True\n",
                ["err_arm_true"],
            ),
            ("| .err e => ¬(e = .overflow) ∨ e = .overflow", ["err_arm_true"]),
            ("| .ub =>\n  let p := True\n  let p := p\n  p", ["ub_arm_true"]),
        ):
            self.assertEqual(self._patterns(source, "lean"), expected, source)

        # Sound Lean arms must NOT trigger false positives:
        # 1. `let p := True` shadowed by `let p := (e = .overflow)` or `fun p => p`.
        # 2. `¬p ∧ q ∨ p ∧ q` (evaluates to `q`, NOT `True`!).
        # 3. Variable named `or` / `and` (`| .err or => or = .overflow`).
        # 4. Non-catch-all single-arm `fun | 0 => True` or `fun | _ => False` or disagreeing `match`.
        for guarded in (
            "| .err e =>\n  let p := True\n  let p := (e = .overflow)\n  p",
            "| .err e =>\n  let p := True\n  fun p => p",
            "| .err e =>\n  let p := True\n  let p := !p\n  p",
            "| .err e => ¬p ∧ q ∨ p ∧ q",
            "| .err or => or = .overflow",
            "| .err and => and = .overflow",
            "| .ub => fun | 0 => True",
            "| .ub => fun | _ => False",
            "def post (x : Bool) : Outcome Nat → Prop\n  | .ok v => v = 1\n  | .err _ =>\n    match x with\n    | true => True\n    | false => False\n",
            "def post : Outcome Nat → Prop\n  | .ok v => fun | _ => True\n  | .ub => False\n",
        ):
            self.assertEqual(self._patterns(guarded, "lean"), [], guarded)

    def test_empty_lean_guillemets_and_cross_language_unclosed_comments_fail_closed(self) -> None:
        # Empty / whitespace-only guillemets fail closed (matching Episode 1's `SpecBoundaryGuards.lean`).
        for bad_guil in ("| .ub => «»", "| .ub => «   »"):
            self.assertEqual(self._patterns(bad_guil, "lean"), ["unclosed_literal_or_comment"], bad_guil)
        # Under `language="auto"`, an unclosed block comment of one language with keywords of the other
        # must NOT silently drop the failing language!
        for cross_hazard in (
            "/* unclosed Rust comment (fun stuff)\nErr(_) => false",
            "/- unclosed Lean comment (fn demo; Err(e))\n| .ub => False",
            "fn demo() { let _ = «unclosed; }\nErr(_) => false",
        ):
            self.assertEqual(
                self._patterns(cross_hazard, "auto"),
                ["unclosed_literal_or_comment"],
                cross_hazard,
            )


class GuardMutationEp2A2AdversarialTests(unittest.TestCase):
    """Pass A2 adversarial regression tests for Shard A layout/shadowing/raw-ident/arm-boundary edges."""

    def _patterns(self, source: str, language: str = "auto") -> list[str]:
        return [f.pattern for f in gmut.detect_postcondition_error_wildcards(source, language=language)]

    def test_lean_inline_ok_match_and_nested_layout_matches_without_false_positives_or_bypasses(self) -> None:
        # Inner `match x with` starting on the `| .ok v =>` line with indented `| _ => True`
        # belongs to the `.ok` arm's inner match, NOT the outer `Outcome` match!
        guarded_ok_match = (
            "def post (x : Nat) : Outcome Nat → Prop\n"
            "  | .ok v => match x with\n"
            "    | 0 => v = 1\n"
            "    | _ => True\n"
            "  | .ub => False\n"
            "  | .err e => e = .overflow\n"
            "  | .unsupported => False\n"
        )
        self.assertEqual(self._patterns(guarded_ok_match, "lean"), [])
        self.assertEqual(
            gmut.verify_postcondition_kills_error_mutants(guarded_ok_match, language="lean")["ok"],
            True,
        )

        # Nested layout `match` inside the first arm of an outer `match` followed by another outer arm:
        # vacuous when all outer+inner arms are `True`, sound when a trailing outer arm constrains `e`.
        vacuous_nested = (
            "def post (x y : Bool) : Outcome Nat → Prop\n"
            "  | .ok v => v = 1\n"
            "  | .err _ =>\n"
            "    match x with\n"
            "    | true =>\n"
            "      match y with\n"
            "      | true => True\n"
            "      | false => True\n"
            "    | false => True\n"
        )
        self.assertEqual(self._patterns(vacuous_nested, "lean"), ["err_arm_true"])
        self.assertEqual(
            gmut.probe_postcondition_error_wildcard_mutant(vacuous_nested, "err", language="lean")["status"],
            "SURVIVED",
        )

        sound_nested = (
            "def post (t : Tag) (y : Bool) : Outcome Nat → Prop\n"
            "  | .ok v => v = 1\n"
            "  | .err e =>\n"
            "    match t with\n"
            "    | .a => True\n"
            "    | .b =>\n"
            "      match y with\n"
            "      | true => True\n"
            "      | false => True\n"
            "    | .c => e = .overflow\n"
        )
        self.assertEqual(self._patterns(sound_nested, "lean"), [])

    def test_pattern_binder_shadowing_in_match_if_let_and_quantifier_binder_types(self) -> None:
        # Outer constant `let` shadowed by `match` or `if let` pattern binders must NOT fold to True!
        for sound_rust in (
            "Err(e) => { let ok = true; match e { E::Check(ok) => ok, _ => true } }",
            "Err(e) => { let ok = true; if let E::Check(ok) = e { ok } else { true } }",
            "Err(e) => { let mut ok = true; { ok = *e == E::Overflow; }; ok }",
            "Err(e) => { let mut ok = true; if *e != E::Overflow { ok = false; } ok }",
            "Err(e) => match e { x if *x == E::A => true, y if *y == E::B => true }",
        ):
            self.assertEqual(self._patterns(sound_rust, "rust"), [], sound_rust)
            self.assertEqual(
                gmut.probe_postcondition_error_wildcard_mutant(sound_rust, "err", language="rust")["status"],
                "KILLED",
                sound_rust,
            )

        for sound_lean in (
            "| .err e =>\n  let ok := True\n  if let .check ok := e then ok else True",
            "| .err e =>\n  let x := True\n  match e with\n  | .code x => x\n  | .other => True",
            "| .err e => ∀ (_ : Unit), ∃ (h : e = .overflow), True",
        ):
            self.assertEqual(self._patterns(sound_lean, "lean"), [], sound_lean)

        # Conversely, non-shadowing `if let` else-branch, binder-type free variable, and un-shadowed arms fold!
        self.assertEqual(
            self._patterns("Err(_) => { let ok = true; if let E::Check(ok) = x { true } else { ok } }", "rust"),
            ["err_arm_true"],
        )
        self.assertEqual(
            self._patterns("| .err _ =>\n  let ok := True\n  if let .check ok := x then True else ok", "lean"),
            ["err_arm_true"],
        )
        self.assertEqual(
            self._patterns("| .ub =>\n  let p := True\n  ∀ (h : P p), p", "lean"),
            ["ub_arm_true"],
        )

    def test_rust_raw_identifiers_reference_arm_boundaries_and_semicolonless_blocks(self) -> None:
        for vacuous_rust, expected in (
            ("Err(r#e) => true", ["err_arm_true"]),
            ("r#Err(r#true) => true", ["err_arm_true"]),
            ("Err([xs @ ..]) => true", ["err_arm_true"]),
            ("Err(_) => { if cond {} true }", ["err_arm_true"]),
            ("Err(_) => { { let _ = 1; } true }", ["err_arm_true"]),
            ("Err(_) => if unsafe { cond } { true } else { true }", ["err_arm_true"]),
            ("Err(_) => match { x } { _ => true }", ["err_arm_true"]),
            (
                "match out_ref {\n"
                "    &Err(_) => { true }\n"
                "    &Ok(v) => v == 1,\n"
                "}\n",
                ["err_arm_true"],
            ),
            (
                "match out_ref {\n"
                "    &Ok(v) => { v == 1 }\n"
                "    r#true => true,\n"
                "}\n",
                ["catch_all_arm_true"],
            ),
        ):
            self.assertEqual(self._patterns(vacuous_rust, "rust"), expected, vacuous_rust)

        # `r#true` in expression position is an identifier variable, NOT the boolean literal `true`!
        self.assertEqual(self._patterns("Err(r#true) => r#true", "rust"), [])
        self.assertEqual(self._patterns("Err(e) => if *e != E::Overflow { return false; } else { true }", "rust"), [])
        self.assertEqual(self._patterns("Err(e) => { if *e != E::Overflow { return false; } true }", "rust"), [])


class GuardMutationEp2B3AdversarialTests(unittest.TestCase):
    """Round 3 adversarial regression tests closing A2's Shard A bypasses and false positives."""

    LEAN_REL = "theory/Anneal/SpecBoundaryGuards.lean"

    def _patterns(self, source: str, language: str = "auto") -> list[str]:
        return [f.pattern for f in gmut.detect_postcondition_error_wildcards(source, language=language)]

    def test_lean_inline_err_match_and_let_rhs_aligned_match_no_longer_bypass(self) -> None:
        # 1. `match x with` starting on the `| .err _ =>` line with indented arms below
        # previously popped `(` before the first arm because `line_first_col` saw col(match)!
        inline_err_match = (
            "def post (x : Bool) : Outcome Nat → Prop\n"
            "  | .ok v => v = 1\n"
            "  | .err _ => match x with\n"
            "    | true => True\n"
            "    | false => True\n"
        )
        self.assertEqual(self._patterns(inline_err_match, "lean"), ["err_arm_true"])
        self.assertEqual(
            gmut.probe_postcondition_error_wildcard_mutant(inline_err_match, "err", language="lean")["status"],
            "SURVIVED",
        )
        # Nested inline `match y with` inside inline `match x with` followed by trailing outer arm.
        inline_nested_match = (
            "def post (x y : Bool) : Outcome Nat → Prop\n"
            "  | .ok v => v = 1\n"
            "  | .err _ => match x with\n"
            "    | true => match y with\n"
            "      | true => True\n"
            "      | false => True\n"
            "    | false => True\n"
        )
        self.assertEqual(self._patterns(inline_nested_match, "lean"), ["err_arm_true"])

        # 2. `let p := match x with` with arms aligned at `let`'s column followed by `p`
        # previously failed to close `match` before `p` and never inserted `;`!
        let_aligned_match = (
            "def post (x : Bool) : Outcome Nat → Prop\n"
            "  | .ok v => v = 1\n"
            "  | .err _ =>\n"
            "    let p := match x with\n"
            "    | true => True\n"
            "    | false => True\n"
            "    p\n"
        )
        self.assertEqual(self._patterns(let_aligned_match, "lean"), ["err_arm_true"])

        # Sound counterpart with constraining arm stays clean.
        sound_inline = (
            "def post (x : Bool) : Outcome Nat → Prop\n"
            "  | .ok v => v = 1\n"
            "  | .err e => match x with\n"
            "    | true => e = .overflow\n"
            "    | false => False\n"
        )
        self.assertEqual(self._patterns(sound_inline, "lean"), [])

    def test_rust_block_or_expr_raw_keyword_shadowing_if_let_scrutinee_and_side_effect_conditions(self) -> None:
        # 1. `{ false } || { true }` without trailing comma before `Ok(v) =>` must NOT split after `{ false }`!
        block_or_arm = (
            "match out {\n"
            "    Err(_) => { false } || { true }\n"
            "    Ok(v) => *v == 1,\n"
            "}\n"
        )
        self.assertEqual(self._patterns(block_or_arm, "rust"), ["err_arm_true"])
        self.assertEqual(
            gmut.probe_postcondition_error_wildcard_mutant(block_or_arm, "err", language="rust")["status"],
            "SURVIVED",
        )

        # 2. `let r#true = false; true` must NOT overwrite literal `true`, and `let r#false = true; false`
        # must NOT overwrite literal `false`; `let r#true = true; r#true` still folds!
        for vacuous in (
            "Err(_) => { let r#true = false; true }",
            "Err(_) => { let r#true = true; r#true }",
            "Err(_) => { if let Foo { a } = x {} true }",
            "Err(_) => { let ok = true; if let E::Check(ok) = e && c { true } else { ok } }",
        ):
            self.assertEqual(self._patterns(vacuous, "rust"), ["err_arm_true"], vacuous)

        # 3. Sound arms that must NOT false-fire:
        # - `let r#false = true; false`
        # - `if let` with block scrutinee (`unsafe { e }` / `{ e }`) or `&&` let-chain shadowing `ok`
        # - `if` condition with `assert!`, `?`, or `return false`
        for sound in (
            "Err(e) => { let r#false = true; false }",
            "Err(e) => { let ok = true; if let E::Check(ok) = unsafe { e } { ok } else { true } }",
            "Err(e) => { let ok = true; if let E::Check(ok) = { e } { ok } else { true } }",
            "Err(e) => { let ok = true; if let E::Check(ok) = e && ok { true } else { false } }",
            "Err(e) => if { assert!(*e == E::Overflow); true } { true } else { true }",
            "Err(e) => if { if *e != E::Overflow { return false; } true } { true } else { true }",
            "Err(e) => if check(e)? { true } else { true }",
        ):
            self.assertEqual(self._patterns(sound, "rust"), [], sound)

    def test_lean_col0_all_continuation_and_uppercase_spec_extension(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-b3-") as tmp:
            root = Path(tmp) / "repo"
            src = (ANNEAL_ROOT / self.LEAN_REL).read_text(encoding="utf-8")
            old = "  [.entryPointPrecondition, .fixedWidthGhostLength, .errorBranchWildcard]\n"
            new = old + "++ [.entryPointPrecondition]\n"
            self.assertEqual(src.count(old), 1)
            dst = root / self.LEAN_REL
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text(src.replace(old, new), encoding="utf-8")
            errs = gmut.validate_property_taxonomy(root)
            self.assertTrue(any("SpecBoundaryGuardClass.all" in e for e in errs), errs)

            upper = Path(tmp) / "SPEC.RS"
            upper.write_text("match out { Ok(v) => *v == 1, Err(_) => true }\n", encoding="utf-8")
            report = gmut.check_spec_wildcard_paths([upper])
            self.assertFalse(report["ok"])
            self.assertEqual(report["findings"][0]["language"], "rust")  # type: ignore[index]


if __name__ == "__main__":
    unittest.main()
