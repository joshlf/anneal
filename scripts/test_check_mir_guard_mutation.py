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
            "-- TODO: remove sorry\n",
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

        # stderr cannot supply the proof-failure marker for a stdout error.
        odd = "/t/Refute_div_by_zero.lean:9:2: error: bizarre glitch\n"
        self.assertEqual(self._classify(1, odd, "rfl has type Type mismatch\n"), "ERROR")
        self.assertEqual(self._classify(1, odd + "rfl has type Type mismatch\n"), "KILLED")
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

            res = _run_cli([*base, "--trust-lake-olean-hash-files", "--verify-lake-olean-bytes"])
            self.assertEqual(res.returncode, 2)

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
        trusted = {"evalScalarBinOp", "emptyMemory"}

        # Syntactically reflexive `X = X := rfl` is rejected.
        refl_src = guard.sanity_source.replace(
            ".ok (.scalar ⟨7, 1⟩) .nil emptyMemory",
            "evalScalarBinOp .div ⟨42, 1⟩ ⟨6, 1⟩ .nil emptyMemory false",
        )
        errs = gmut._fixture_statement_errors(
            "sanity", refl_src, guard.sanity_theorem_name, trusted_decl_names=trusted
        )
        self.assertTrue(any("syntactically reflexive" in e for e in errs), errs)

        # Arithmetic-only `1 + 1 = 2 := rfl` with no trusted call on LHS is rejected.
        no_tcb = (
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "theorem sanity_div_by_zero :\n"
            "    1 + 1 = 2 :=\n"
            "  rfl\n"
        )
        errs = gmut._fixture_statement_errors(
            "sanity", no_tcb, "sanity_div_by_zero", trusted_decl_names=trusted
        )
        self.assertTrue(any("does not reference any trusted declaration" in e for e in errs), errs)

        # `let` / `fun` inside theorem statement is rejected.
        let_src = (
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "theorem sanity_div_by_zero :\n"
            "    let x := evalScalarBinOp .div ⟨42, 1⟩ ⟨6, 1⟩ .nil emptyMemory false\n"
            "    x = x :=\n"
            "  rfl\n"
        )
        errs = gmut._fixture_statement_errors(
            "sanity", let_src, "sanity_div_by_zero", trusted_decl_names=trusted
        )
        self.assertTrue(any("must not contain `let` or `fun`" in e for e in errs), errs)

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
        self.assertTrue(any("RHS must not assert UB" in e for e in cat_errs), cat_errs)

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


if __name__ == "__main__":
    unittest.main()
