#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and adversarial tamper tests for `scripts/receipt_claim_guard.py`.

Every negative test states the exact violation code the guard must fail
closed with. All files live in `tempfile.TemporaryDirectory()` trees.
"""

from __future__ import annotations

import ast
import contextlib
import io
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

sys.dont_write_bytecode = True

SCRIPTS_DIR = Path(__file__).resolve().parent
SCRIPT = SCRIPTS_DIR / "receipt_claim_guard.py"

if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

import receipt_claim_guard as rcg  # noqa: E402

SHA = "c81271f6d1b8df7f17be327c296687e8dccc9104"
BASE_SHA = "7ce766e036d404b5afce2078d7adaf0f6370da68"
OTHER_SHA = "121d78538a0f0c1d2e3f4a5b6c7d8e9f00112233"
STANDARD_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def bundle(**overrides: dict[str, object]) -> dict[str, object]:
    """A passing three-step canonical bundle; `overrides` update steps by id."""
    steps: list[dict[str, object]] = [
        {
            "step_id": "unit_tests",
            "command": "python3 -B -m unittest scripts/test_check_mir_guard_mutation.py -v",
            "returncode": 0,
            "ok": True,
            "passed_count": 42,
            "failed_count": 0,
        },
        {
            "step_id": "spec_boundary_guards",
            "command": "anneal-lean-run --mode build -- lake build Anneal.SpecBoundaryGuards",
            "returncode": 0,
            "theorem_count": 34,
            "sorry_count": 0,
            "axioms": list(STANDARD_AXIOMS),
        },
        {
            "step_id": "cargo_test",
            "command": "cargo test --manifest-path crates/anneal-spec/Cargo.toml --locked",
            "exit_code": 0,
            "passed_count": 118,
            "failed_count": 0,
        },
    ]
    for step in steps:
        step.update(overrides.get(step["step_id"], {}))  # type: ignore[arg-type]
    return {"schema": rcg.RECEIPT_SCHEMA, "commit_sha": SHA, "steps": steps}


def guard_mutation(killed: int = 20, survived: int = 0, fatal: str | None = None) -> dict[str, object]:
    """A `check_mir_guard_mutation.py --json` report."""
    if fatal is not None:
        return {"ok": False, "fatal_error": fatal, "mode": "all", "total": 0, "killed": 0,
                "survived": 0, "errors": 1, "kill_rate_pct": 0.0, "results": []}
    results = [{"guard_id": f"g{i}", "status": "KILLED"} for i in range(killed)]
    results += [{"guard_id": f"s{i}", "status": "SURVIVED"} for i in range(survived)]
    total = killed + survived
    return {"ok": survived == 0 and total > 0, "fatal_error": None, "mode": "all", "total": total,
            "killed": killed, "survived": survived, "errors": 0,
            "kill_rate_pct": round(100.0 * killed / total, 2) if total else 0.0, "results": results}


CHECK_TRUSTED = {
    "graph": {}, "declarations": [], "kernelDeclarations": 512, "compilerOnlyNames": 0,
    "reachableDeclarations": 512, "axioms": list(STANDARD_AXIOMS), "replay": True,
    "downstream": {"downstreamModules": 3, "replayedDeclarations": 77, "claimTheoremsChecked": 9,
                   "localTestAxioms": 0},
    "sourceSha256": "ab" * 32, "toolchain": "4.34.1",
}

NIGHTLY = {
    "schema_version": 1,
    "unstable_commit_sha": SHA,
    "pillar_2_correctness_and_correspondence": {
        "overall_status": "PASS",
        "steps": [
            {"name": "mir_guard_mutation_quick", "category": "tcb", "status": "PASS", "exit_code": 0,
             "command": "python3 -B scripts/check_mir_guard_mutation.py --quick"},
            {"name": "trusted audit", "category": "tcb", "status": "PASS", "exit_code": 0,
             "command": "python3 -B trusted/audit/check_trusted.py --fast"},
        ],
    },
}

GATE2 = f"""# Gate-2 report: ep2

- Commit SHA: `{SHA}` (Base: `{BASE_SHA[:12]}`)
- `unit_tests`: rc=0, 42 passed, 0 failed
- `lake build Anneal.SpecBoundaryGuards`: rc=0, 34 theorems, 0 sorry, standard axioms only
- `cargo test --manifest-path crates/anneal-spec/Cargo.toml --locked`: exit code 0, 118 passed, 0 failed

## guard_mutation

20/20 killed, 0 survived, kill rate 100%. Status: PASS

| Step | Result |
| --- | --- |
| `check_trusted` | PASS, 9 theorems, axioms: propext, Classical.choice, Quot.sound |
| `mir_guard_mutation_quick` | PASS (exit code 0) |

```
$ python3 -B trusted/audit/check_trusted.py --fast
rc=0
```

Previously: 3 failed (fixed in this pass).

All gates pass.
"""


class GuardHarness(unittest.TestCase):
    """Runs the guard in-process against files in one temporary directory."""

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory(prefix="anneal-rcg-unit-")
        self.addCleanup(tmp.cleanup)
        self.tmp = Path(tmp.name)

    def write(self, name: str, content: object) -> Path:
        path = self.tmp / name
        if isinstance(content, bytes):
            path.write_bytes(content)
        else:
            path.write_text(content if isinstance(content, str) else json.dumps(content), encoding="utf-8")
        return path

    def run_main(self, argv: list[str]) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            try:
                rc = rcg.main(argv)
            except SystemExit as exc:
                rc = exc.code if isinstance(exc.code, int) else 1
        return rc, out.getvalue(), err.getvalue()

    def guard(
        self,
        claims: str,
        receipts: list[object] | None = None,
        *extra: str,
    ) -> tuple[int, dict[str, object]]:
        """Run with `--json`; a receipt is JSON content, raw text, or `(id, content)`."""
        argv = ["--claims", str(self.write("claims.md", claims)), "--json", *extra]
        for idx, receipt in enumerate([bundle()] if receipts is None else receipts):
            forced, content = receipt if isinstance(receipt, tuple) else (None, receipt)
            path = content if isinstance(content, Path) else self.write(f"receipt{idx}.json", content)
            argv += ["--receipt", f"{forced}={path}" if forced else str(path)]
        rc, out, _ = self.run_main(argv)
        return rc, json.loads(out)

    def codes(self, claims: str, receipts: list[object] | None = None, *extra: str) -> list[str]:
        rc, report = self.guard(claims, receipts, *extra)
        codes = sorted({v["code"] for v in report["violations"]})
        self.assertEqual(rc, 1 if codes else 0, report["violations"])
        self.assertEqual(report["ok"], not codes)
        return codes


class PositiveTests(GuardHarness):
    def test_realistic_gate2_report_passes_against_every_receipt_format(self) -> None:
        receipts: list[object] = [bundle(), guard_mutation(), CHECK_TRUSTED, NIGHTLY]
        rc, report = self.guard(GATE2, receipts, "--expected-sha", SHA,
                                "--require-step", "unit_tests", "--require-step", "guard_mutation")
        self.assertEqual((rc, report["ok"], report["violations"]), (0, True, []))
        self.assertEqual(report["schema"], rcg.REPORT_SCHEMA)
        self.assertEqual(report["claims_ignored_lines"], 1)
        self.assertEqual(
            [(r["step_id"], r["kind"]) for r in report["receipts"]],
            [("unit_tests", "canonical"), ("spec_boundary_guards", "canonical"), ("cargo_test", "canonical"),
             ("guard_mutation", "guard_mutation"), ("check_trusted", "check_trusted"),
             ("mir_guard_mutation_quick", "nightly"), ("trusted audit", "nightly")],
        )
        attributed = {(c["line"], c["kind"], c["metric"], str(c["value"])): c["step"] for c in report["claims"]}
        self.assertEqual(attributed[(3, "commit_sha", "head", SHA)], None)
        self.assertEqual(attributed[(3, "commit_sha", "base", BASE_SHA[:12])], None)
        self.assertEqual(attributed[(4, "count", "passed", "42")], "unit_tests")
        self.assertEqual(attributed[(5, "count", "theorems", "34")], "spec_boundary_guards")
        self.assertEqual(attributed[(5, "axioms", "standard_only", "None")], "spec_boundary_guards")
        self.assertEqual(attributed[(6, "exit_status", "rc", "0")], "cargo_test")
        self.assertEqual(attributed[(10, "count", "killed", "20")], "guard_mutation")
        self.assertEqual(attributed[(10, "kill_rate", "kill_rate", "100.0")], "guard_mutation")
        self.assertEqual(attributed[(14, "count", "theorems", "9")], "check_trusted")
        self.assertEqual(attributed[(15, "exit_status", "rc", "0")], "mir_guard_mutation_quick")
        self.assertEqual(attributed[(19, "exit_status", "rc", "0")], "trusted audit")
        self.assertEqual(attributed[(24, "exit_status", "all", "pass")], None)
        self.assertEqual(report["claims_checked"], len(report["claims"]))
        self.assertEqual(report["claims_checked"], 24)

        # Text mode, and the same verdict twice over: the output is deterministic.
        argv = ["--claims", str(self.tmp / "claims.md")]
        for idx in range(4):
            argv += ["--receipt", str(self.tmp / f"receipt{idx}.json")]
        rc, out, _ = self.run_main(argv)
        self.assertEqual(rc, 0)
        self.assertEqual(out, f"receipt-claim-guard: PASS (0 violation(s), {report['claims_checked']} claim(s), 7 receipt step(s))\n")
        first = self.run_main([*argv, "--json"])
        self.assertEqual(first, self.run_main([*argv, "--json"]))

    def test_verification_takes_well_under_50ms_of_cpu(self) -> None:
        paths = [self.write(f"r{i}.json", r) for i, r in enumerate([bundle(), guard_mutation(), CHECK_TRUSTED, NIGHTLY])]
        argv = ["--claims", str(self.write("claims.md", GATE2 * 4)), "--json", "--max-elapsed-ms", "50"]
        for path in paths:
            argv += ["--receipt", str(path)]
        self.run_main(argv)  # warm the regex caches the way a second CLI run would not need
        best = float("inf")
        for _ in range(5):
            started = time.process_time()
            rc, out, _ = self.run_main(argv)
            best = min(best, (time.process_time() - started) * 1000.0)
            self.assertEqual(rc, 0, out)
        self.assertLess(best, 50.0)
        # A cold process, interpreter start included, still verifies in the budget.
        cold = subprocess.run([sys.executable, "-B", str(SCRIPT), *argv], capture_output=True, text=True)
        self.assertEqual(cold.returncode, 0, cold.stdout + cold.stderr)
        self.assertTrue(json.loads(cold.stdout)["ok"])
        rc, report = self.guard(GATE2, [bundle(), guard_mutation(), CHECK_TRUSTED, NIGHTLY], "--max-elapsed-ms", "0.000001")
        self.assertEqual((rc, [v["code"] for v in report["violations"]]), (1, ["ELAPSED_BUDGET_EXCEEDED"]))

    def test_script_is_an_executable_stdlib_only_cli(self) -> None:
        source = SCRIPT.read_text(encoding="utf-8")
        self.assertTrue(source.startswith("#!/usr/bin/env python3\n#\n# Copyright 2026 The Fuchsia Authors\n"))
        self.assertEqual(stat.S_IMODE(SCRIPT.stat().st_mode) & 0o111, 0o111)
        self.assertIn("sys.dont_write_bytecode = True", source)
        tree = ast.parse(source)
        imported = {
            (node.module if isinstance(node, ast.ImportFrom) else alias.name).split(".")[0]
            for node in ast.walk(tree)
            if isinstance(node, (ast.Import, ast.ImportFrom))
            for alias in node.names
        }
        self.assertLessEqual(imported, set(sys.stdlib_module_names))
        self.assertFalse(imported & {"socket", "urllib", "http", "subprocess", "ssl"})
        # Every flag is documented on its own line of the module docstring.
        flags = {
            arg.value
            for node in ast.walk(tree)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "add_argument"
            for arg in node.args
            if isinstance(arg, ast.Constant) and isinstance(arg.value, str) and arg.value.startswith("--")
        }
        self.assertEqual(len(flags), 12, flags)
        for flag in sorted(flags):
            self.assertRegex(rcg.__doc__ or "", rf"(?m)^  {re.escape(flag)}(?:\s|$)", flag)
        self.assertEqual(rcg.ALLOWED_KERNEL_AXIOMS, frozenset(STANDARD_AXIOMS))
        self.assertEqual(sorted(rcg.VIOLATION_CODES), list(rcg.VIOLATION_CODES))

    def test_claims_are_read_from_stdin_and_attributed_by_context(self) -> None:
        receipt = self.write("bundle.json", bundle())
        for claims_arg in ([], ["--claims", "-"]):
            res = subprocess.run(
                [sys.executable, "-B", str(SCRIPT), "--receipt-bundle", str(receipt), "--json", *claims_arg],
                input="`cargo_test`: rc=0, 118 passed\n", capture_output=True, text=True,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertEqual(json.loads(res.stdout)["claims_checked"], 2)
        # Heading, paragraph, table-cell and fenced-command context.
        claims = (
            "## cargo_test\n\n118 passed.\n\n## Other\n\n`unit_tests` ran:\n42 passed\n\n"
            "| `unit_tests` | 42 passed | `cargo_test` | 118 passed |\n\n"
            "```\n$ anneal-lean-run --mode build -- lake build Anneal.SpecBoundaryGuards\n34 theorems\n```\n"
        )
        rc, report = self.guard(claims)
        self.assertEqual((rc, report["violations"]), (0, []))
        self.assertEqual(
            [(c["line"], c["value"], c["step"]) for c in report["claims"]],
            [(3, 118, "cargo_test"), (8, 42, "unit_tests"), (10, 42, "unit_tests"),
             (10, 118, "cargo_test"), (14, 34, "spec_boundary_guards")],
        )
        # A claim that names no step speaks for every receipt that reports the metric.
        self.assertEqual(self.codes("160 passed and 0 failed overall, rc=0."), [])
        self.assertEqual(self.codes("42 passed."), ["COUNT_MISMATCH"])
        self.assertEqual(self.codes("161 passed."), ["INFLATED_COUNT"])


class CommitShaTamperTests(GuardHarness):
    def test_stale_mismatched_ambiguous_and_conflicting_shas(self) -> None:
        ok = "\n`unit_tests`: rc=0\n"
        self.assertEqual(self.codes(f"Commit SHA: {SHA}{ok}"), [])
        self.assertEqual(self.codes(f"HEAD: `{SHA[:7]}`{ok}"), [])
        self.assertEqual(self.codes(f"Verified at commit {SHA[:12]}.{ok}"), [])
        self.assertEqual(self.codes(f"Base SHA: {BASE_SHA}\nHead SHA: {SHA}{ok}"), [])
        self.assertEqual(self.codes(f"Parent commit `{OTHER_SHA}`; commit `{SHA}`{ok}"), [])
        for prose, code in (
            (f"Commit SHA: {OTHER_SHA}", "COMMIT_SHA_MISMATCH"),  # stale
            (f"Commit SHA: {SHA[:8]}0", "COMMIT_SHA_MISMATCH"),  # prefix mismatch
            (f"HEAD is at `{OTHER_SHA[:9]}`", "COMMIT_SHA_MISMATCH"),
            (f"commit {OTHER_SHA[:12]}", "COMMIT_SHA_MISMATCH"),
            (f"Commit SHA: {SHA[:4]}", "AMBIGUOUS_COMMIT_SHA"),
            (f"commit `{SHA[:6]}`", "AMBIGUOUS_COMMIT_SHA"),
            ("Commit SHA: unknown", "INVALID_COMMIT_SHA"),
            (f"Commit SHA: {'0' * 40}", "INVALID_COMMIT_SHA"),
            (f"Commit SHA: {SHA.upper()}", "INVALID_COMMIT_SHA"),
            (f"Commit SHA: {SHA}ab", "INVALID_COMMIT_SHA"),
            (f"Commit SHA: g{SHA[1:]}", "INVALID_COMMIT_SHA"),
        ):
            self.assertEqual(self.codes(prose + ok), [code], prose)
        # Two different head commits contradict each other unless one is `Base`.
        self.assertEqual(
            self.codes(f"Commit SHA: {SHA}\nTarget commit: {OTHER_SHA}{ok}"),
            ["COMMIT_SHA_MISMATCH", "CONFLICTING_COMMIT_SHA"],
        )
        # Prose words after a label are not SHAs.
        self.assertEqual(self.codes(f"Commit: added tests; HEAD is clean; base branch main.{ok}"), [])

    def test_receipt_commits_must_agree_with_each_other_and_the_expected_sha(self) -> None:
        ok = "`unit_tests`: rc=0\n"
        self.assertEqual(self.codes(ok, None, "--expected-sha", SHA[:10]), [])
        self.assertEqual(self.codes(ok, None, "--expected-sha", OTHER_SHA), ["STALE_RECEIPT"])
        self.assertEqual(
            self.codes(f"Commit SHA: {SHA}\n{ok}", None, "--expected-sha", OTHER_SHA),
            ["COMMIT_SHA_MISMATCH", "STALE_RECEIPT"],
        )
        nightly = json.loads(json.dumps(NIGHTLY))
        nightly["unstable_commit_sha"] = OTHER_SHA
        self.assertEqual(self.codes(ok, [bundle(), nightly]), ["CONFLICTING_RECEIPT_SHA"])
        # No receipt names a commit: a SHA claim has nothing behind it.
        self.assertEqual(self.codes(f"Commit SHA: {SHA}\nStatus: PASS", [guard_mutation()]), ["UNBACKED_CLAIM"])
        self.assertEqual(self.codes(f"Commit SHA: {SHA}\nStatus: PASS", [guard_mutation()], "--expected-sha", SHA), [])


class CountAndStatusTamperTests(GuardHarness):
    def test_inflated_and_mismatched_counts(self) -> None:
        for prose, code in (
            ("`unit_tests`: 43 passed", "INFLATED_COUNT"),
            ("`unit_tests`: 41 passed", "COUNT_MISMATCH"),
            ("`unit_tests`: 1,042 passed", "INFLATED_COUNT"),
            ("`unit_tests`: passed=420", "INFLATED_COUNT"),
            ("`unit_tests`: 43/43 passed", "INFLATED_COUNT"),
            ("`unit_tests`: 42/50 tests passed", "INFLATED_COUNT"),
            ("`spec_boundary_guards`: 35 theorems", "THEOREM_COUNT_MISMATCH"),
            ("`spec_boundary_guards`: 33 kernel-checked theorems", "THEOREM_COUNT_MISMATCH"),
            ("`spec_boundary_guards`: theorem_count=340", "THEOREM_COUNT_MISMATCH"),
            ("`unit_tests`: ~42 passed", "MALFORMED_CLAIM"),
            ("`unit_tests`: >40 passed", "MALFORMED_CLAIM"),
            ("`unit_tests`: 4.2 passed", "MALFORMED_CLAIM"),
            ("`unit_tests`: 42 theorems", "UNBACKED_CLAIM"),
            ("`cargo_test`: 0 sorry", "UNBACKED_CLAIM"),
        ):
            self.assertEqual(self.codes(prose), [code], prose)
        # Fullwidth digits and zero-width characters cannot hide an inflation.
        self.assertEqual(self.codes("`unit_tests`: ４３ passed"), ["INFLATED_COUNT"])
        self.assertEqual(self.codes("`unit_tests`: 4\u200b3 passed"), ["INFLATED_COUNT"])
        self.assertEqual(self.codes("`unit_tests`: 43 pas\u200bsed, rc\uff1d0"), ["INFLATED_COUNT"])
        self.assertEqual(self.codes("`unit_tests`: rc=0 \u202e43 passed"), ["INFLATED_COUNT", "MALFORMED_CLAIMS"])
        for prose, receipt, code in (
            ("21/21 killed", guard_mutation(), "INFLATED_COUNT"),
            ("20/20 killed", guard_mutation(19, 1), "INFLATED_COUNT"),
            ("19/21 killed", guard_mutation(19, 1), "INFLATED_COUNT"),
            ("0 survived", guard_mutation(19, 1), "COUNT_MISMATCH"),
            ("no survivors", guard_mutation(19, 1), "COUNT_MISMATCH"),
            ("kill rate 100%", guard_mutation(19, 1), "INFLATED_COUNT"),
            ("100% kill rate", guard_mutation(19, 1), "INFLATED_COUNT"),
            ("kill rate: 90%", guard_mutation(19, 1), "COUNT_MISMATCH"),
            ("kill rate ~100%", guard_mutation(), "MALFORMED_CLAIM"),
        ):
            self.assertEqual(self.codes(prose, [receipt]), [code], prose)
        self.assertEqual(self.codes("19/20 killed, 1 survived, kill rate 95%", [guard_mutation(19, 1)]), [])

    def test_suppressed_failures_behind_pass_prose(self) -> None:
        failing: tuple[tuple[str, list[object]], ...] = (
            ("rc=1", [bundle(unit_tests={"returncode": 1, "ok": False})]),
            ("failed_count=1", [bundle(unit_tests={"failed_count": 1, "ok": None, "returncode": None,
                                                   "exit_code": None} | {"ok": False})]),
            ("failed count, rc 0", [bundle(cargo_test={"failed_count": 1})]),
            ("survived=1", [guard_mutation(19, 1)]),
            ("fatal_error", [guard_mutation(fatal="baseline refute fixture failed")]),
            ("ok=false", [bundle(spec_boundary_guards={"returncode": None, "ok": False})]),
        )
        for label, receipts in failing:
            for prose in ("rc=0", "exit code 0", "Status: PASS", "ok=true", "PASS", "All checks passed.", "✅"):
                self.assertEqual(self.codes(prose, receipts), ["SUPPRESSED_FAILURE"], (label, prose))
        # The step is named and failed.
        self.assertEqual(
            self.codes("`unit_tests`: rc=0", [bundle(unit_tests={"returncode": 1, "ok": False})]),
            ["SUPPRESSED_FAILURE"],
        )
        # An honest report of the failure passes; a wrong code or a false "FAIL" does not.
        red = [bundle(unit_tests={"returncode": 1, "ok": False, "failed_count": 3, "passed_count": 39})]
        self.assertEqual(self.codes("`unit_tests`: rc=1, 39 passed, 3 failed. Status: FAIL", red), [])
        self.assertEqual(self.codes("`unit_tests`: rc=2", red), ["EXIT_CODE_MISMATCH"])
        self.assertEqual(self.codes("`unit_tests`: 0 failed", red), ["COUNT_MISMATCH"])
        self.assertEqual(self.codes("`unit_tests`: no failures", red), ["COUNT_MISMATCH"])
        self.assertEqual(self.codes("`cargo_test`: rc=1"), ["EXIT_CODE_MISMATCH"])
        self.assertEqual(self.codes("`cargo_test`: FAILED"), ["EXIT_CODE_MISMATCH"])
        self.assertEqual(self.codes("`cargo_test`: rc=zero, 118 passed"), ["MALFORMED_CLAIM"])
        nightly = json.loads(json.dumps(NIGHTLY))
        nightly["pillar_2_correctness_and_correspondence"]["overall_status"] = "FAIL"
        nightly["pillar_2_correctness_and_correspondence"]["steps"][1].update(status="TIMEOUT", exit_code=124)
        self.assertEqual(self.codes("`trusted audit`: PASS", [nightly]), ["SUPPRESSED_FAILURE"])
        self.assertEqual(self.codes("`trusted audit`: exit code 124; `mir_guard_mutation_quick`: PASS", [nightly]), [])

    def test_claims_about_steps_or_commands_without_a_receipt(self) -> None:
        for prose, code in (
            ("`cargo test --workspace`: rc=0, 900 passed", "UNBACKED_CLAIM"),
            ("`./ci/check_todo.sh scripts/x.py`: rc=0", "UNBACKED_CLAIM"),
            ("```\n$ lake build Everything\nrc=0\n```", "UNBACKED_CLAIM"),
            ("step=fuzz_campaign rc=0", "MISSING_STEP_RECEIPT"),
            ("Step: `nightly_soak` PASS", "MISSING_STEP_RECEIPT"),
            ("## step: ghost\n\n12 passed", "MISSING_STEP_RECEIPT"),
        ):
            self.assertEqual(self.codes(prose), [code], prose)
        ok = "`unit_tests`: rc=0"
        self.assertEqual(self.codes(ok, None, "--require-step", "check_trusted"), ["MISSING_STEP_RECEIPT"])
        self.assertEqual(
            self.codes("`unit_tests`: rc=1", [bundle(unit_tests={"returncode": 1, "ok": False})],
                       "--require-step", "unit_tests"),
            ["REQUIRED_STEP_FAILED"],
        )
        self.assertEqual(self.codes(ok, None, "--require-step", "unit_tests", "--require-step", "cargo_test"), [])

    def test_vague_or_empty_prose_fails_closed(self) -> None:
        for prose in (
            "",
            "Everything looks great. The proofs are solid and the tests were thorough.\n",
            "# Handoff\n\nImplemented the guard. Ran the usual checks; nothing surprising.\n",
            "Previously: 42 passed, rc=0\n",
            "<!-- claim-guard: ignore-begin -->\n42 passed\n<!-- claim-guard: ignore-end -->\n",
            "~~`unit_tests`: rc=0, 42 passed~~\n",
            "<!-- `unit_tests`: rc=0 -->\n",
        ):
            self.assertEqual(self.codes(prose), ["NO_CLAIMS_EXTRACTED"], prose)
            self.assertEqual(self.codes(prose, None, "--allow-empty-claims"), [], prose)
            self.assertEqual(self.codes(prose, None, "--require-nonempty-claims"), ["NO_CLAIMS_EXTRACTED"], prose)
        # Ignored text is skipped, not trusted, and an unclosed ignore block is an error.
        self.assertEqual(self.codes("Historical: `unit_tests`: 999 passed\n`unit_tests`: 42 passed"), [])
        self.assertEqual(
            self.codes("`unit_tests`: 42 passed\n<!-- claim-guard: ignore-begin -->\n`unit_tests`: rc=1\n"),
            ["MALFORMED_CLAIMS"],
        )
        # A marker in the middle of a line does not make the line historical.
        self.assertEqual(self.codes("`unit_tests`: 43 passed (not historical: current)"), ["INFLATED_COUNT"])


class SorryAndAxiomTamperTests(GuardHarness):
    def test_sorry_hidden_behind_zero_sorry_prose(self) -> None:
        for prose in ("0 sorry", "0 `sorry`", "sorry_count=0", "no sorry", "zero sorries", "sorry-free"):
            self.assertEqual(self.codes(f"`spec_boundary_guards`: {prose}"), [], prose)
            self.assertEqual(
                self.codes(f"`spec_boundary_guards`: {prose}", [bundle(spec_boundary_guards={"sorry_count": 2})]),
                ["SORRY_VIOLATION"], prose,
            )
            self.assertEqual(self.codes(prose, [bundle(spec_boundary_guards={"sorry_count": 1})]),
                             ["SORRY_VIOLATION"], prose)
        with_sorry_ax = [bundle(spec_boundary_guards={"axioms": [*STANDARD_AXIOMS, "sorryAx"]})]
        self.assertEqual(self.codes("`spec_boundary_guards`: 0 sorry", with_sorry_ax),
                         ["SORRY_VIOLATION", "UNAUTHORIZED_AXIOM"])
        self.assertEqual(self.codes("`spec_boundary_guards`: 0 sorry", with_sorry_ax,
                                    "--allow-conditional-axiom", "Lean.ofReduceBool"),
                         ["SORRY_VIOLATION", "UNAUTHORIZED_AXIOM"])
        # `check_trusted` reports no `sorry` count; its axiom list still decides.
        self.assertEqual(self.codes("`check_trusted`: 0 sorry", [CHECK_TRUSTED]), [])
        self.assertEqual(
            self.codes("`check_trusted`: 0 sorry", [{**CHECK_TRUSTED, "axioms": ["sorryAx"]}]),
            ["SORRY_VIOLATION", "UNAUTHORIZED_AXIOM"],
        )
        self.assertEqual(self.codes("`spec_boundary_guards`: 2 sorry",
                                    [bundle(spec_boundary_guards={"sorry_count": 2})]), [])
        self.assertEqual(self.codes("`spec_boundary_guards`: 1 sorry"), ["SORRY_VIOLATION"])

    def test_unauthorized_axioms_and_omitted_axiom_claims(self) -> None:
        ok = "`spec_boundary_guards`: rc=0"
        for axiom in ("Lean.ofReduceBool", "Lean.trustCompiler", "myAxiom", "sorryAx"):
            receipts = [bundle(spec_boundary_guards={"axioms": [*STANDARD_AXIOMS, axiom]})]
            # The receipt alone fails, whatever the prose says.
            self.assertEqual(self.codes(ok, receipts), ["UNAUTHORIZED_AXIOM"], axiom)
            self.assertEqual(
                self.codes(f"{ok}, standard axioms only", receipts),
                ["AXIOM_SET_MISMATCH", "UNAUTHORIZED_AXIOM"], axiom,
            )
            self.assertEqual(
                self.codes(f"{ok}; axioms: propext, Classical.choice, Quot.sound", receipts),
                ["AXIOM_SET_MISMATCH", "UNAUTHORIZED_AXIOM"], axiom,
            )
        conditional = [bundle(spec_boundary_guards={"axioms": [*STANDARD_AXIOMS, "Lean.ofReduceBool"]})]
        allow = ("--allow-conditional-axiom", "Lean.ofReduceBool")
        self.assertEqual(self.codes(ok, conditional, *allow), [])
        self.assertEqual(
            self.codes(f"{ok}; axioms: propext, Classical.choice, Quot.sound, `Lean.ofReduceBool`", conditional, *allow), []
        )
        # Authorized, but the prose still may not call the set standard or omit it.
        for prose in ("standard axioms only", "only the standard axioms", "no non-standard axioms",
                      "Axioms: standard only", "axioms: propext, Classical.choice", "no axioms", "axiom-free"):
            self.assertEqual(self.codes(f"{ok}; {prose}", conditional, *allow), ["AXIOM_SET_MISMATCH"], prose)
        self.assertEqual(self.codes(f"{ok}; axioms: propext, Quot.sound"), ["AXIOM_SET_MISMATCH"])
        self.assertEqual(self.codes(f"{ok}; axioms: propext, Classical.choice, Quot.sound"), [])
        self.assertEqual(self.codes(f"{ok}; axioms: ???"), ["MALFORMED_CLAIM"])
        self.assertEqual(self.codes("`cargo_test`: standard axioms only"), ["UNBACKED_CLAIM"])
        self.assertEqual(self.codes("standard axioms only", [CHECK_TRUSTED, bundle()]), [])


class ReceiptFormatTests(GuardHarness):
    def test_malformed_missing_and_non_finite_receipts(self) -> None:
        ok = "`unit_tests`: rc=0"
        raw = json.dumps(bundle())
        cases: tuple[tuple[str, object, str], ...] = (
            ("truncated", raw[:-2], "MALFORMED_RECEIPT"),
            ("empty", "", "MALFORMED_RECEIPT"),
            ("array", "[]", "MALFORMED_RECEIPT"),
            ("NaN", raw.replace('"passed_count": 42', '"passed_count": NaN'), "MALFORMED_RECEIPT"),
            ("Infinity", raw.replace('"returncode": 0', '"returncode": Infinity', 1), "MALFORMED_RECEIPT"),
            ("-Infinity", raw.replace('"failed_count": 0', '"failed_count": -Infinity', 1), "MALFORMED_RECEIPT"),
            ("overflowing float", raw.replace('"passed_count": 42', '"passed_count": 1e999'), "MALFORMED_RECEIPT"),
            ("float count", raw.replace('"passed_count": 42', '"passed_count": 42.0'), "MALFORMED_RECEIPT"),
            ("string count", raw.replace('"passed_count": 42', '"passed_count": "42"'), "MALFORMED_RECEIPT"),
            ("negative count", raw.replace('"failed_count": 0', '"failed_count": -1', 1), "MALFORMED_RECEIPT"),
            ("bool exit code", raw.replace('"returncode": 0', '"returncode": false', 1), "MALFORMED_RECEIPT"),
            ("bool count", raw.replace('"passed_count": 42', '"passed_count": true'), "MALFORMED_RECEIPT"),
            ("int ok", raw.replace('"ok": true', '"ok": 1'), "MALFORMED_RECEIPT"),
            ("duplicate key", raw.replace('"returncode": 0', '"returncode": 1, "returncode": 0', 1), "MALFORMED_RECEIPT"),
            ("unknown key", raw.replace('"failed_count": 0', '"failed_cnt": 1', 1), "MALFORMED_RECEIPT"),
            ("unknown schema", raw.replace(rcg.RECEIPT_SCHEMA, "anneal.verification_receipt.v2"), "MALFORMED_RECEIPT"),
            ("no exit status", {"schema": rcg.RECEIPT_SCHEMA, "step_id": "x", "passed_count": 1}, "MALFORMED_RECEIPT"),
            ("bad commit", {**bundle(), "commit_sha": "unknown"}, "MALFORMED_RECEIPT"),
            ("empty steps", {**bundle(), "steps": []}, "MALFORMED_RECEIPT"),
            ("unrecognized", {"hello": "world"}, "MALFORMED_RECEIPT"),
            ("invalid utf-8", b'{"schema": "\xff"}', "MALFORMED_RECEIPT"),
            ("ok contradicts rc", bundle(unit_tests={"returncode": 1}), "INCONSISTENT_RECEIPT"),
            ("ok contradicts failures", bundle(unit_tests={"failed_count": 2}), "INCONSISTENT_RECEIPT"),
            ("rc contradicts exit_code", bundle(unit_tests={"exit_code": 1}), "INCONSISTENT_RECEIPT"),
            ("guard counts", {**guard_mutation(), "killed": 21}, "INCONSISTENT_RECEIPT"),
            ("guard ok", {**guard_mutation(19, 1), "ok": True}, "INCONSISTENT_RECEIPT"),
            ("guard results", {**guard_mutation(), "results": []}, "INCONSISTENT_RECEIPT"),
            ("nightly status", {"name": "s", "status": "PASS", "exit_code": 1}, "INCONSISTENT_RECEIPT"),
        )
        for label, content, code in cases:
            codes = self.codes(ok, [content])
            self.assertIn(code, codes, label)
            # Nothing is trusted from an unusable receipt.
            self.assertTrue(set(codes) <= {code, "UNBACKED_CLAIM", "MISSING_STEP_RECEIPT"}, (label, codes))
        self.assertIn("MISSING_RECEIPT", self.codes(ok, [self.tmp / "absent.json"]))
        self.assertIn("MALFORMED_RECEIPT", self.codes(ok, [self.tmp]))
        # One bad receipt fails the run even when the claims are fully backed elsewhere.
        self.assertEqual(self.codes(ok, [bundle(), self.tmp / "absent.json"]), ["MISSING_RECEIPT"])
        self.assertEqual(self.codes(ok, [bundle(), bundle()]), ["DUPLICATE_STEP_RECEIPT"])

    def test_symlinks_fifos_and_bundle_typing(self) -> None:
        ok = "`unit_tests`: rc=0"
        real = self.write("real.json", bundle())
        link = self.tmp / "link.json"
        os.symlink(real, link)
        self.assertEqual(self.codes(ok, [link]), [])
        self.assertIn("MALFORMED_RECEIPT", self.codes(ok, [link], "--no-symlinks"))
        claims_link = self.tmp / "claims-link.md"
        os.symlink(self.write("target.md", ok), claims_link)
        rc, out, _ = self.run_main(["--claims", str(claims_link), "--receipt", str(real), "--no-symlinks", "--json"])
        self.assertEqual((rc, [v["code"] for v in json.loads(out)["violations"]]), (1, ["UNREADABLE_CLAIMS"]))
        fifo = self.tmp / "fifo.json"
        os.mkfifo(fifo)
        self.assertIn("MALFORMED_RECEIPT", self.codes(ok, [fifo]))  # returns at once, never blocks
        rc, out, _ = self.run_main(["--claims", str(self.tmp / "nope.md"), "--receipt", str(real), "--json"])
        self.assertEqual((rc, [v["code"] for v in json.loads(out)["violations"]]), (1, ["UNREADABLE_CLAIMS"]))
        # `--receipt-bundle` takes only the canonical schema; `ID=` names single-step receipts.
        gm = self.write("gm.json", guard_mutation())
        rc, out, _ = self.run_main(["--claims", str(self.tmp / "target.md"), "--receipt-bundle", str(gm), "--json"])
        self.assertEqual(rc, 1)
        self.assertIn("MALFORMED_RECEIPT", [v["code"] for v in json.loads(out)["violations"]])
        self.assertEqual(self.codes("`mutants`: 20/20 killed, rc=0", [("mutants", guard_mutation())]), [])
        self.assertEqual(self.codes("`trusted`: PASS, 9 theorems", [("trusted", CHECK_TRUSTED)]), [])
        self.assertIn("MALFORMED_RECEIPT", self.codes(ok, [("renamed", bundle())]))
        single = {"schema": rcg.RECEIPT_SCHEMA, "step_id": "lake", "returncode": 0, "theorem_count": 3}
        self.assertEqual(self.codes("`lake`: rc=0, 3 theorems", [single]), [])
        self.assertEqual(self.codes("`build`: rc=0, 3 theorems", [("build", single)]), [])

    def test_check_trusted_and_nightly_adapters(self) -> None:
        stdout_receipt = rcg._CHECK_TRUSTED_STDOUT_PREFIX + json.dumps(
            {"trusted": {"modules": 14, "waivers": 0}, "rustcCapture": {"files": 9}, "downstream": {"files": 4}}
        ) + "\n"
        self.assertEqual(self.codes("`check_trusted`: rc=0, PASS", [stdout_receipt]), [])
        self.assertIn("MALFORMED_RECEIPT", self.codes("`check_trusted`: rc=0", [stdout_receipt.replace("14", "NaN")]))
        self.assertEqual(self.codes("`check_trusted`: 9 theorems, standard axioms only, rc=0", [CHECK_TRUSTED]), [])
        self.assertEqual(self.codes("`check_trusted`: 10 theorems", [CHECK_TRUSTED]), ["THEOREM_COUNT_MISMATCH"])
        self.assertEqual(self.codes("`check_trusted`: PASS", [{**CHECK_TRUSTED, "replay": False}]), ["SUPPRESSED_FAILURE"])
        self.assertIn("MALFORMED_RECEIPT", self.codes("`check_trusted`: PASS", [{**CHECK_TRUSTED, "axioms": "propext"}]))
        self.assertIn("MALFORMED_RECEIPT", self.codes("`check_trusted`: PASS", [{**CHECK_TRUSTED, "sourceSha256": "zz"}]))
        self.assertEqual(self.codes(f"Commit SHA: {SHA}\n`mir_guard_mutation_quick`: PASS", [NIGHTLY]), [])
        self.assertEqual(self.codes(f"Commit SHA: {OTHER_SHA}\n`trusted audit`: PASS", [NIGHTLY]), ["COMMIT_SHA_MISMATCH"])
        self.assertEqual(self.codes("`s`: exit code 3", [{"name": "s", "status": "FAIL", "exit_code": 3}]), [])


class CommandLineTests(GuardHarness):
    def test_usage_errors_exit_2(self) -> None:
        claims = str(self.write("claims.md", "`unit_tests`: rc=0"))
        receipt = str(self.write("bundle.json", bundle()))
        for argv in (
            ["--claims", claims],
            ["--claims", claims, "--receipt", receipt, "--expected-sha", "abc"],
            ["--claims", claims, "--receipt", receipt, "--expected-sha", SHA.upper()],
            ["--claims", claims, "--receipt", receipt, "--expected-sha", "0" * 40],
            ["--claims", claims, "--receipt", receipt, "--allow-conditional-axiom", "sorryAx"],
            ["--claims", claims, "--receipt", receipt, "--allow-conditional-axiom", "not an axiom"],
            ["--claims", claims, "--receipt", receipt, "--max-elapsed-ms", "0"],
            ["--claims", claims, "--receipt", receipt, "--max-elapsed-ms", "nan"],
            ["--claims", claims, "--receipt", "id="],
            ["--claims", claims, "--receipt", receipt, "--require-step", " "],
            ["--claims", claims, "--receipt", receipt, "--allow-empty-claims", "--require-nonempty-claims"],
            ["--claims", claims, "--receipt", receipt, "--allow-empty"],
            ["--claims", claims, "--receipt", receipt, "--bogus"],
        ):
            self.assertEqual(self.run_main(argv)[0], 2, argv)
        cli = subprocess.run([sys.executable, "-B", str(SCRIPT), "--claims", claims], capture_output=True, text=True)
        self.assertEqual(cli.returncode, 2)
        executable = subprocess.run([str(SCRIPT), "--claims", claims, "--receipt", receipt], capture_output=True, text=True)
        self.assertEqual((executable.returncode, executable.stdout.startswith("receipt-claim-guard: PASS")), (0, True))

    def test_json_out_is_written_fail_closed_before_anything_is_read(self) -> None:
        claims = str(self.write("claims.md", "`unit_tests`: rc=0, 42 passed"))
        receipt = str(self.write("bundle.json", bundle()))
        out = self.tmp / "nested" / "report.json"
        base = ["--claims", claims, "--receipt", receipt, "--json-out", str(out)]
        self.assertEqual(self.run_main(base)[0], 0)
        green = json.loads(out.read_text(encoding="utf-8"))
        self.assertEqual((green["ok"], green["fatal_error"], green["claims_checked"]), (True, None, 2))

        # The sink holds a failing report while the run is in flight ...
        seen: list[dict[str, object]] = []

        def crash(*args: object, **kwargs: object) -> dict[str, object]:
            seen.append(json.loads(out.read_text(encoding="utf-8")))
            raise KeyboardInterrupt

        with mock.patch.object(rcg, "run_guard", side_effect=crash), self.assertRaises(KeyboardInterrupt):
            self.run_main(base)
        self.assertEqual((seen[0]["ok"], seen[0]["fatal_error"]), (False, "run did not complete"))
        stale = json.loads(out.read_text(encoding="utf-8"))
        self.assertEqual((stale["ok"], stale["fatal_error"]), (False, "run did not complete"))
        self.assertEqual(set(stale), set(green))

        # ... a red run replaces a green file ...
        self.write("claims.md", "`unit_tests`: rc=0, 43 passed")
        rc, stdout, _ = self.run_main([*base, "--json"])
        red = json.loads(out.read_text(encoding="utf-8"))
        self.assertEqual((rc, red["ok"], [v["code"] for v in red["violations"]]), (1, False, ["INFLATED_COUNT"]))
        self.assertEqual(json.loads(stdout), red)

        # ... and a sink that cannot be written fails the run that would have passed.
        self.write("claims.md", "`unit_tests`: rc=0, 42 passed")
        rc, stdout, stderr = self.run_main(["--claims", claims, "--receipt", receipt,
                                            "--json-out", str(Path(receipt) / "x.json"), "--json"])
        self.assertEqual((rc, json.loads(stdout)["ok"]), (1, False))
        self.assertIn("cannot write", stderr)

    def test_strict_json_and_violation_text(self) -> None:
        for text in ("NaN", "[Infinity]", '{"a": -Infinity}', '{"a": 1e999}', '{"a": 1, "a": 2}', "[" * 100000):
            with self.assertRaises(ValueError, msg=text[:20]):
                rcg.parse_strict_json(text)
        self.assertEqual(rcg.parse_strict_json('{"a": [1, 2.5, true, null]}'), {"a": [1, 2.5, True, None]})
        self.write("claims.md", "`unit_tests`: rc=0, 43 passed")
        rc, out, _ = self.run_main(["--claims", str(self.tmp / "claims.md"), "--receipt", str(self.write("b.json", bundle()))])
        self.assertEqual(rc, 1)
        self.assertEqual(
            out,
            "VIOLATION INFLATED_COUNT [line 1] [step unit_tests]: `43 passed` but step `unit_tests` reports 42\n"
            "receipt-claim-guard: FAIL (1 violation(s), 2 claim(s), 3 receipt step(s))\n",
        )
        for violation_code in ("INFLATED_COUNT", "SUPPRESSED_FAILURE", "NO_CLAIMS_EXTRACTED", "UNBACKED_CLAIM"):
            self.assertIn(violation_code, rcg.VIOLATION_CODES)


class Ep2B1AdversarialTests(GuardHarness):
    """Pass B1 adversarial bypass regressions for `receipt_claim_guard.py`."""

    def test_base_sha_only_cannot_bypass_nonempty_claims(self) -> None:
        self.assertEqual(
            self.codes(f"Base SHA: `{BASE_SHA}`\nEverything looks clean!\n"),
            ["NO_CLAIMS_EXTRACTED"],
        )
        # Even against a failing receipt, Base-only prose fails closed.
        red = [bundle(unit_tests={"returncode": 1, "ok": False})]
        self.assertEqual(self.codes(f"Base SHA: `{BASE_SHA}`\n", red), ["NO_CLAIMS_EXTRACTED"])
        self.assertEqual(
            self.codes(f"Base SHA: `{BASE_SHA}`\n", None, "--allow-empty-claims"),
            [],
        )

    def test_inline_ignore_markers_and_unclosed_html_comments_cannot_swallow_claims(self) -> None:
        # Claims before ignore-begin or after ignore-end on the same line are still audited!
        self.assertEqual(
            self.codes("`unit_tests`: 999 passed <!-- claim-guard: ignore-begin -->\n<!-- claim-guard: ignore-end -->\n"),
            ["INFLATED_COUNT"],
        )
        self.assertEqual(
            self.codes("<!-- claim-guard: ignore-begin --><!-- claim-guard: ignore-end --> `unit_tests`: 999 passed\n"),
            ["INFLATED_COUNT"],
        )
        self.assertEqual(
            self.codes("<!-- claim-guard: ignore-begin -->\n999 passed\n<!-- claim-guard: ignore-end --> `unit_tests`: 999 passed\n"),
            ["INFLATED_COUNT"],
        )
        # Legitimate inline ignore hides only the span between markers.
        self.assertEqual(
            self.codes("`unit_tests`: 42 passed <!-- claim-guard: ignore-begin -->(was 999 passed)<!-- claim-guard: ignore-end -->\n"),
            [],
        )
        # Stray ignore-end, nested ignore-begin, and unclosed HTML comments fail closed.
        self.assertEqual(
            self.codes("`unit_tests`: 42 passed\n<!-- claim-guard: ignore-end -->\n"),
            ["MALFORMED_CLAIMS"],
        )
        self.assertEqual(
            self.codes("`unit_tests`: 42 passed\n<!-- claim-guard: ignore-begin -->\n<!-- claim-guard: ignore-begin -->\n<!-- claim-guard: ignore-end -->\n"),
            ["MALFORMED_CLAIMS"],
        )
        self.assertEqual(
            self.codes("`unit_tests`: 42 passed\n<!-- unclosed comment hiding `unit_tests`: 999 passed\n"),
            ["MALFORMED_CLAIMS"],
        )

    def test_step_binding_does_not_leak_across_bullets_tables_clauses_or_fences(self) -> None:
        # Bullet list: fabricated step must not inherit previous bullet's `unit_tests` context.
        self.assertEqual(
            self.codes("- `unit_tests`: rc=0, 42 passed\n- `fabricated_fuzz`: rc=0, 42 passed\n"),
            ["MISSING_STEP_RECEIPT"],
        )
        # Under a heading naming `unit_tests`, an explicit fabricated bullet still fails!
        self.assertEqual(
            self.codes("## unit_tests\n\n- `unit_tests`: rc=0, 42 passed\n- `miri_suite`: rc=0, 42 passed\n"),
            ["MISSING_STEP_RECEIPT"],
        )
        # Markdown tables: fabricated row or column must not inherit an earlier step.
        self.assertEqual(
            self.codes(
                "| Step | Result |\n| --- | --- |\n"
                "| `unit_tests` | rc=0, 42 passed |\n"
                "| `fabricated_step` | rc=0, 42 passed |\n"
            ),
            ["MISSING_STEP_RECEIPT"],
        )
        self.assertEqual(
            self.codes("| `unit_tests` | 42 passed | `fabricated_step` | 42 passed |\n"),
            ["MISSING_STEP_RECEIPT"],
        )
        self.assertEqual(
            self.codes("| unit_tests | 42 passed |\n| fabricated_step | 42 passed |\n"),
            ["MISSING_STEP_RECEIPT"],
        )
        # Semicolon clause isolation: step B's count must not bind to step A's ref.
        self.assertEqual(
            self.codes("rc=0 for `unit_tests`; 42 passed for `cargo_test`\n"),
            ["COUNT_MISMATCH"],
        )
        # Bare command inside a fenced code block (no `$ `) under a heading must not inherit heading.
        self.assertEqual(
            self.codes("## unit_tests\n\n```\ncargo test --workspace\nrc=0\n```\n"),
            ["UNBACKED_CLAIM"],
        )
        # Heading with unknown backticked step id fails closed instead of going unscoped.
        self.assertEqual(
            self.codes("## `ghost_gate`\n\nrc=0\n"),
            ["MISSING_STEP_RECEIPT"],
        )
        # Shell-chained wrapper prefix cannot spoof a real receipt's command.
        self.assertEqual(
            self.codes("`evil_cmd && foo -- cargo test --manifest-path crates/anneal-spec/Cargo.toml --locked`: rc=0\n"),
            ["UNBACKED_CLAIM"],
        )

    def test_negated_prose_bold_markdown_fractions_and_axiom_edge_cases(self) -> None:
        red = [bundle(unit_tests={"returncode": 1, "ok": False, "failed_count": 3, "passed_count": 39})]
        # Negated "all pass" is NOT a positive pass claim: honest on failing run, mismatch on green run.
        self.assertEqual(self.codes("All checks did not pass.", red), [])
        self.assertEqual(self.codes("All tests failed to pass.", red), [])
        self.assertEqual(self.codes("Not all checks passed.", red), [])
        self.assertEqual(self.codes("All checks did not pass."), ["EXIT_CODE_MISMATCH"])
        self.assertEqual(self.codes("`unit_tests`: NOT PASS", red), [])
        self.assertEqual(self.codes("`unit_tests`: NOT PASS"), ["EXIT_CODE_MISMATCH"])
        # Double-negation hiding a failure ("NOT FAILED") is caught as SUPPRESSED_FAILURE.
        self.assertEqual(self.codes("`unit_tests`: NOT FAILED", red), ["SUPPRESSED_FAILURE"])

        # Fraction variants that previously slipped past `_FRACTION_RE` and `_NUM`.
        self.assertEqual(self.codes("`unit_tests`: 99/99 tests passing"), ["INFLATED_COUNT"])
        self.assertEqual(self.codes("`unit_tests`: 42 of 42 tests passed"), [])
        self.assertEqual(self.codes("`unit_tests`: 0/42 failed", red), ["COUNT_MISMATCH"])
        self.assertEqual(self.codes("`spec_boundary_guards`: 99/99 theorems"), ["THEOREM_COUNT_MISMATCH"])
        self.assertEqual(self.codes("`spec_boundary_guards`: 35/34 theorems"), ["MALFORMED_CLAIM"])
        self.assertEqual(self.codes("0/20 survived", [guard_mutation(19, 1)]), ["COUNT_MISMATCH"])

        # Zero-word & kv-count variants.
        self.assertEqual(self.codes("`unit_tests`: zero failed tests", red), ["COUNT_MISMATCH"])
        self.assertEqual(self.codes("`unit_tests`: no failing tests", red), ["COUNT_MISMATCH"])
        self.assertEqual(self.codes("`unit_tests`: no tests failed", red), ["COUNT_MISMATCH"])
        self.assertEqual(self.codes("no mutants survived", [guard_mutation(19, 1)]), ["COUNT_MISMATCH"])
        self.assertEqual(self.codes("100% of mutants killed", [guard_mutation(19, 1)]), ["INFLATED_COUNT"])
        self.assertEqual(
            self.codes(
                "`spec_boundary_guards`: no sorryAx",
                [bundle(spec_boundary_guards={"axioms": [*STANDARD_AXIOMS, "sorryAx"]})],
            ),
            ["SORRY_VIOLATION", "UNAUTHORIZED_AXIOM"],
        )

        # Markdown bold labels and underscore SHA keys must still be verified.
        self.assertEqual(self.codes(f"**Commit SHA**: `{OTHER_SHA}`\n`unit_tests`: rc=0\n"), ["COMMIT_SHA_MISMATCH"])
        self.assertEqual(self.codes(f"**Commit SHA:** `{OTHER_SHA}`\n`unit_tests`: rc=0\n"), ["COMMIT_SHA_MISMATCH"])
        self.assertEqual(self.codes(f"commit_sha: {OTHER_SHA}\n`unit_tests`: rc=0\n"), ["COMMIT_SHA_MISMATCH"])
        self.assertEqual(self.codes(f"**HEAD**: `{SHA}`\n`unit_tests`: **42** passed, **Status**: PASS\n"), [])
        self.assertEqual(self.codes("`unit_tests`: **43** passed\n"), ["INFLATED_COUNT"])

        # `axioms: standard axioms only`, `axioms = []`, sentence stops, multiple axiom clauses, bogus unauthorized axiom.
        self.assertEqual(self.codes("`spec_boundary_guards`: axioms: standard axioms only"), [])
        self.assertEqual(
            self.codes("`spec_boundary_guards`: axioms = []", [bundle(spec_boundary_guards={"axioms": []})]),
            [],
        )
        self.assertEqual(
            self.codes("`spec_boundary_guards`: axioms: propext, Classical.choice, Quot.sound. Next line is prose."),
            [],
        )
        self.assertEqual(
            self.codes("`spec_boundary_guards`: axioms: propext, Classical.choice, Quot.sound; `check_trusted`: axioms: propext",
                       [bundle(), CHECK_TRUSTED]),
            ["AXIOM_SET_MISMATCH"],
        )
        self.assertEqual(
            self.codes("`spec_boundary_guards`: axioms: propext, Classical.choice, Quot.sound, sorryAx"),
            ["AXIOM_SET_MISMATCH"],
        )

    def test_kill_rate_boundary_rounding_and_unbacked_rc_fail_closed(self) -> None:
        # 19999/20000 rounds to 100.00% at 2 decimals, yet 1 mutant survived: 100% MUST fail!
        almost = {
            "schema": rcg.RECEIPT_SCHEMA,
            "step_id": "big_mut",
            "returncode": 1,
            "ok": False,
            "killed": 19999,
            "survived": 1,
            "errors": 0,
            "total": 20000,
        }
        self.assertEqual(self.codes("`big_mut`: kill rate 100%", [almost]), ["INFLATED_COUNT"])
        self.assertEqual(self.codes("`big_mut`: kill rate 99.995%", [almost]), [])
        # A step with ok=False and no returncode cannot back an arbitrary `rc=999`.
        no_rc = [bundle(spec_boundary_guards={"returncode": None, "ok": False})]
        self.assertEqual(self.codes("`spec_boundary_guards`: rc=999", no_rc), ["UNBACKED_CLAIM"])

    def test_hardened_receipt_adapters_and_json_out_symlinks(self) -> None:
        ok = "`check_trusted`: rc=0"
        # `check_trusted` must never ignore explicit failure markers or malformed downstream.
        for bad_ct, code in (
            ({**CHECK_TRUSTED, "ok": False}, "SUPPRESSED_FAILURE"),
            ({**CHECK_TRUSTED, "returncode": 1}, "SUPPRESSED_FAILURE"),
            ({**CHECK_TRUSTED, "fatal_error": "boom"}, "SUPPRESSED_FAILURE"),
            ({**CHECK_TRUSTED, "status": "FAIL"}, "SUPPRESSED_FAILURE"),
            ({**CHECK_TRUSTED, "downstream": "not-a-dict"}, "MALFORMED_RECEIPT"),
            ({**CHECK_TRUSTED, "claimTheoremsChecked": 99}, "INCONSISTENT_RECEIPT"),
            ({**CHECK_TRUSTED, "ok": True, "replay": False}, "INCONSISTENT_RECEIPT"),
            (rcg._CHECK_TRUSTED_STDOUT_PREFIX + "{}\n", "MALFORMED_RECEIPT"),
        ):
            codes = self.codes(ok, [bad_ct])
            self.assertIn(code, codes, bad_ct)
        # Canonical step validation: nested `schema`, `killed > total`, empty `fatal_error`, bad `duration_sec`.
        for bad_canon, code in (
            (bundle(unit_tests={"schema": "bogus"}), "MALFORMED_RECEIPT"),
            (bundle(unit_tests={"killed": 25, "survived": 0, "errors": 0, "total": 20}), "INCONSISTENT_RECEIPT"),
            (bundle(unit_tests={"fatal_error": ""}), "MALFORMED_RECEIPT"),
            (bundle(unit_tests={"duration_sec": True}), "MALFORMED_RECEIPT"),
            (bundle(unit_tests={"artifacts": 123}), "MALFORMED_RECEIPT"),
            ({**guard_mutation(19, 1), "kill_rate_pct": 100.0}, "INCONSISTENT_RECEIPT"),
            ({**guard_mutation(), "fatal_error": ""}, "MALFORMED_RECEIPT"),
        ):
            codes = self.codes("`unit_tests`: rc=0", [bad_canon])
            self.assertIn(code, codes, bad_canon)
        # Nightly dashboard: invalid SHA or contradictory overall_status/counts fail closed.
        bad_nightly_sha = json.loads(json.dumps(NIGHTLY))
        bad_nightly_sha["unstable_commit_sha"] = "unknown"
        self.assertIn("MALFORMED_RECEIPT", self.codes("`trusted audit`: PASS", [bad_nightly_sha]))
        bad_nightly_overall = json.loads(json.dumps(NIGHTLY))
        bad_nightly_overall["pillar_2_correctness_and_correspondence"]["steps"][1].update(
            status="FAIL", exit_code=1
        )
        self.assertIn("INCONSISTENT_RECEIPT", self.codes("`trusted audit`: FAIL", [bad_nightly_overall]))
        bad_nightly_counts = json.loads(json.dumps(NIGHTLY))
        bad_nightly_counts["pillar_2_correctness_and_correspondence"]["steps_total"] = 99
        self.assertIn("INCONSISTENT_RECEIPT", self.codes("`trusted audit`: PASS", [bad_nightly_counts]))

        # `--json-out` under `--no-symlinks` refuses a symlink sink and records fatal_error.
        claims = str(self.write("c.md", "`unit_tests`: rc=0"))
        receipt = str(self.write("r.json", bundle()))
        target = self.write("target.json", "{}")
        link_out = self.tmp / "out-link.json"
        os.symlink(target, link_out)
        rc, stdout, _ = self.run_main(
            ["--claims", claims, "--receipt", receipt, "--no-symlinks", "--json-out", str(link_out), "--json"]
        )
        parsed = json.loads(stdout)
        self.assertEqual((rc, parsed["ok"]), (1, False))
        self.assertIsNotNone(parsed["fatal_error"])
        self.assertEqual(target.read_text(encoding="utf-8"), "{}")


if __name__ == "__main__":
    unittest.main()
