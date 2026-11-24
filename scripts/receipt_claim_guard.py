#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Deterministic prose-vs-receipt claim verifier for Anneal handoffs.

Why this check exists
---------------------

A `HANDOFF.md`, Gate-2 report or PR description states what was verified: the
commit, each command's exit status, test and mutant counts, theorem and `sorry`
counts, and the kernel axioms. Nothing ties that prose to what actually ran. A
report can name a stale commit, round a failure up to a pass, or describe a
command that was never executed, and it still reads well.

This is the "Epistemic Guard" of arXiv:2611.27095: every verification claim in
the prose is checked against machine-generated JSON receipts, with no model in
the loop. It is stdlib-only, makes no network call, and verifies a realistic
multi-receipt handoff in well under 50 ms. It fails closed: a claim the
receipts contradict, a claim no receipt backs, a receipt it cannot read, and a
document that makes no checkable claim at all are all violations.

Receipts (`--receipt [STEP_ID=]PATH`, `--receipt-bundle PATH`)
---------------------------------------------------------------

* `anneal.verification_receipt.v1`: a JSON object with
  `"schema": "anneal.verification_receipt.v1"`, an optional `commit_sha`, and
  either a `steps` array (a bundle) or the step fields themselves. A step has
  `step_id`, optional `command`, `returncode` / `exit_code`, `ok`,
  `passed_count`, `failed_count`, `theorem_count`, `sorry_count`, `killed`,
  `survived`, `errors`, `total`, `axioms`, `fatal_error` and `artifacts`.
  Unknown keys are rejected, so a misspelled `failed_count` cannot hide.
* `check_mir_guard_mutation.py --json` reports (`ok`, `fatal_error`, `total`,
  `killed`, `survived`, `errors`, `results`); default step id `guard_mutation`.
* `check_trusted.py` reports (`axioms`, `kernelDeclarations`, `replay`,
  `downstream.claimTheoremsChecked`, `sourceSha256`), the `--audit-vacuity`
  summary object (`trusted`, `rustcCapture`, `downstream`), and its stdout line
  `PASS: waiver pins and annotated-claim vacuity; {...}`; default step id
  `check_trusted`.
* `run_nightly_verification_suite.py` dashboards
  (`unstable_commit_sha` / `git_sha` / `commit_sha` and
  `pillar_2_correctness_and_correspondence.steps` with `name`, `status`,
  `exit_code`, `command`) and single step objects.

A receipt must be a UTF-8 regular file of strict JSON: `NaN`, `Infinity`,
duplicate keys, booleans where integers belong, and negative counts are
rejected, as is a receipt that contradicts itself (`ok: true` with a non-zero
exit code, `killed + survived + errors != total`).

Claims (`--claims PATH`, default stdin)
---------------------------------------

Claims are read from Markdown: prose, bullets, tables, and fenced blocks.

* Commit: `Commit SHA: <hex>`, `HEAD: <hex>`, ``commit `<hex>` ``. 7 to 40
  lowercase hex characters. `Base` / `Parent` / `Previous` labels name another
  commit and are not compared with the receipts.
* Exit status: `rc=0`, `exit code 0`, `status: PASS`, `ok=true`, `PASS`.
* Counts: `42 passed`, `0 failed`, `20/20 killed`, `0 survived`, `34 theorems`,
  `0 sorry`, `kill rate 100%`, and `key=value` forms (`passed=42`).
* Axioms: `standard axioms only`, `axioms: propext, Classical.choice`.

A claim belongs to the step named on its line (a step id, a receipt's command
in backticks, or `step=<id>`), else to the step named earlier in its paragraph
or by its heading. A claim that names no step speaks for every receipt: `rc=0`
then requires every step to have passed, and a count must equal the sum over
the receipts that report it.

Only explicitly marked prose is skipped: a line starting with `Historical:`,
`Previously:`, `Superseded:` or `Obsolete:`, `~~struck-through~~` text, HTML
comments, and the lines between `<!-- claim-guard: ignore-begin -->` and
`<!-- claim-guard: ignore-end -->`.

Command line
------------

  --claims PATH       Markdown to audit (default, or `-`: stdin).
  --receipt [STEP_ID=]PATH
                      A receipt file. Repeatable. `STEP_ID=` names the step of
                      a single-step receipt.
  --receipt-bundle PATH
                      An `anneal.verification_receipt.v1` bundle. Repeatable.
  --expected-sha SHA  The commit every SHA claim and receipt must name.
  --require-step STEP_ID
                      A step that must have a passing receipt. Repeatable.
  --allow-conditional-axiom NAME
                      Authorize one more kernel axiom. Repeatable. `sorryAx`
                      can never be authorized.
  --require-nonempty-claims
                      Fail when no claim is extracted. This is the default.
  --allow-empty-claims
                      Accept a document that makes no checkable claim.
  --no-symlinks       Reject a receipt or claims path that is a symlink.
  --json              Print the JSON report on stdout, and nothing else.
  --json-out PATH     Write the JSON report to PATH. The file is overwritten
                      with a failing report before anything is read, so it can
                      never show a stale pass.
  --max-elapsed-ms MS Fail when verification itself takes longer than MS.

Exit status: `0` every claim is backed and nothing is violated; `1` a
violation, or a receipt or claims file that cannot be used; `2` bad command
line.
"""

from __future__ import annotations

import argparse
from collections.abc import Sequence
from dataclasses import asdict, dataclass, field
import json
import os
from pathlib import Path
import re
import stat
import sys
import time
import unicodedata

sys.dont_write_bytecode = True

RECEIPT_SCHEMA = "anneal.verification_receipt.v1"
REPORT_SCHEMA = "anneal.receipt_claim_guard.v1"

# The three axioms of Lean 4's standard foundation.
ALLOWED_KERNEL_AXIOMS: frozenset[str] = frozenset({"propext", "Classical.choice", "Quot.sound"})
# Never authorizable, even through `--allow-conditional-axiom`.
NEVER_ALLOWED_AXIOMS: frozenset[str] = frozenset({"sorryAx"})

MAX_INPUT_BYTES = 16 * 1024 * 1024

VIOLATION_CODES: tuple[str, ...] = (
    "AMBIGUOUS_COMMIT_SHA",
    "AXIOM_SET_MISMATCH",
    "COMMIT_SHA_MISMATCH",
    "CONFLICTING_COMMIT_SHA",
    "CONFLICTING_RECEIPT_SHA",
    "COUNT_MISMATCH",
    "DUPLICATE_STEP_RECEIPT",
    "ELAPSED_BUDGET_EXCEEDED",
    "EXIT_CODE_MISMATCH",
    "INCONSISTENT_RECEIPT",
    "INFLATED_COUNT",
    "INVALID_COMMIT_SHA",
    "MALFORMED_CLAIM",
    "MALFORMED_CLAIMS",
    "MALFORMED_RECEIPT",
    "MISSING_RECEIPT",
    "MISSING_STEP_RECEIPT",
    "NO_CLAIMS_EXTRACTED",
    "REQUIRED_STEP_FAILED",
    "SORRY_VIOLATION",
    "STALE_RECEIPT",
    "SUPPRESSED_FAILURE",
    "THEOREM_COUNT_MISMATCH",
    "UNAUTHORIZED_AXIOM",
    "UNBACKED_CLAIM",
    "UNREADABLE_CLAIMS",
)

_STEP_ID_ARG_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.:-]*")
_SHA_RE = re.compile(r"[0-9a-f]{7,40}")
_AXIOM_NAME_RE = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")
_CHECK_TRUSTED_STDOUT_PREFIX = "PASS: waiver pins and annotated-claim vacuity; "

# Count metrics a step may report, by canonical receipt key.
_CANONICAL_COUNT_KEYS: dict[str, str] = {
    "passed_count": "passed",
    "failed_count": "failed",
    "theorem_count": "theorems",
    "sorry_count": "sorry",
    "killed": "killed",
    "survived": "survived",
    "errors": "errors",
    "total": "total",
}
_CANONICAL_STEP_KEYS: frozenset[str] = frozenset(
    {"step_id", "command", "returncode", "exit_code", "ok", "axioms", "artifacts",
     "fatal_error", "commit_sha", "duration_sec", *_CANONICAL_COUNT_KEYS}
)
_CANONICAL_TOP_KEYS: frozenset[str] = frozenset(
    {"schema", "commit_sha", "steps", "generated_at_utc", "generator", "artifacts", "metadata"}
)
# A larger claim than the receipt is an inflation; any other difference is a mismatch.
_GOOD_METRICS: frozenset[str] = frozenset({"passed", "killed", "total", "tests"})


class InputError(Exception):
    """A receipt or claims file that cannot be used; becomes a violation."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(message)
        self.code = code
        self.message = message


@dataclass
class Step:
    """One verification step, normalized from any supported receipt format."""

    step_id: str
    kind: str
    source: str
    command: str | None = None
    returncode: int | None = None
    ok: bool | None = None
    status: str | None = None
    fatal_error: str | None = None
    counts: dict[str, int] = field(default_factory=dict)
    axioms: tuple[str, ...] | None = None

    def has_exit_evidence(self) -> bool:
        return (
            self.returncode is not None
            or self.ok is not None
            or self.status is not None
            or self.fatal_error is not None
        )

    def failure(self) -> str | None:
        """Why the step did not pass, or `None` when nothing says it failed."""
        if self.fatal_error is not None:
            return f"fatal_error={self.fatal_error!r}"
        if self.returncode not in (None, 0):
            return f"rc={self.returncode}"
        if self.ok is False:
            return "ok=false"
        if self.status is not None and self.status != "PASS":
            return f"status={self.status}"
        for key in ("failed", "survived", "errors"):
            if self.counts.get(key, 0) > 0:
                return f"{key}={self.counts[key]}"
        return None


@dataclass(frozen=True)
class Claim:
    """One checkable statement extracted from the prose."""

    kind: str  # commit_sha | exit_status | count | kill_rate | axioms
    metric: str
    value: object
    line: int
    text: str
    step: str | None  # resolved step id; `None` speaks for every receipt
    missing: str = ""  # a named step or command that no receipt backs


@dataclass(frozen=True)
class Violation:
    code: str
    line: int
    step_id: str | None
    message: str


# ---------------------------------------------------------------------------
# Strict input reading
# ---------------------------------------------------------------------------


def read_regular_utf8(path: Path, *, no_symlinks: bool, missing_code: str, bad_code: str) -> str:
    """Read a UTF-8 regular file, never blocking on a FIFO or device."""
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_CLOEXEC", 0)
    if no_symlinks:
        flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        if no_symlinks and os.path.islink(path):
            raise InputError(bad_code, f"{path}: is a symlink (--no-symlinks)")
        fd = os.open(path, flags)
    except OSError as exc:
        code = missing_code if isinstance(exc, FileNotFoundError) else bad_code
        raise InputError(code, f"{path}: cannot open: {exc.strerror or exc}") from exc
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode):
            raise InputError(bad_code, f"{path}: not a regular file")
        if info.st_size > MAX_INPUT_BYTES:
            raise InputError(bad_code, f"{path}: larger than {MAX_INPUT_BYTES} bytes")
        with os.fdopen(fd, "rb") as handle:
            fd = -1
            data = handle.read(MAX_INPUT_BYTES + 1)
    except OSError as exc:
        raise InputError(bad_code, f"{path}: cannot read: {exc.strerror or exc}") from exc
    finally:
        if fd >= 0:
            os.close(fd)
    if len(data) > MAX_INPUT_BYTES:
        raise InputError(bad_code, f"{path}: larger than {MAX_INPUT_BYTES} bytes")
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise InputError(bad_code, f"{path}: not valid UTF-8: {exc.reason}") from exc


def _reject_constant(name: str) -> object:
    raise ValueError(f"non-finite JSON constant {name}")


def _strict_float(text: str) -> float:
    value = float(text)
    if value != value or value in (float("inf"), float("-inf")):
        raise ValueError(f"non-finite JSON number {text}")
    return value


def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    obj: dict[str, object] = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError(f"duplicate JSON key {key!r}")
        obj[key] = value
    return obj


def parse_strict_json(text: str) -> object:
    """`json.loads` without `NaN` / `Infinity`, overflowing floats or duplicate keys."""
    try:
        return json.loads(
            text,
            parse_constant=_reject_constant,
            parse_float=_strict_float,
            object_pairs_hook=_unique_object,
        )
    except RecursionError as exc:
        raise ValueError("JSON nested too deeply") from exc


# ---------------------------------------------------------------------------
# Receipts
# ---------------------------------------------------------------------------


def _bad(source: str, message: str, code: str = "MALFORMED_RECEIPT") -> InputError:
    return InputError(code, f"{source}: {message}")


def _opt_int(obj: dict[str, object], key: str, source: str, *, minimum: int | None = 0) -> int | None:
    value = obj.get(key)
    if value is None:
        return None
    # `bool` is an `int` in Python; `true` is not a count or an exit code.
    if type(value) is not int or (minimum is not None and value < minimum):
        kind = "an integer" if minimum is None else "a non-negative integer"
        raise _bad(source, f"`{key}` must be {kind}, got {value!r}")
    return value


def _opt_bool(obj: dict[str, object], key: str, source: str) -> bool | None:
    value = obj.get(key)
    if value is not None and type(value) is not bool:
        raise _bad(source, f"`{key}` must be a boolean, got {value!r}")
    return value  # type: ignore[return-value]


def _opt_str(obj: dict[str, object], key: str, source: str) -> str | None:
    value = obj.get(key)
    if value is not None and not isinstance(value, str):
        raise _bad(source, f"`{key}` must be a string, got {value!r}")
    return value  # type: ignore[return-value]


def _axioms(value: object, source: str) -> tuple[str, ...] | None:
    if value is None:
        return None
    if not isinstance(value, list) or not all(
        isinstance(name, str) and _AXIOM_NAME_RE.fullmatch(name) for name in value
    ):
        raise _bad(source, "`axioms` must be a list of axiom names")
    return tuple(value)


def _receipt_sha(value: object, source: str, key: str) -> str | None:
    if value is None:
        return None
    if not isinstance(value, str) or not _SHA_RE.fullmatch(value) or set(value) == {"0"}:
        raise _bad(source, f"`{key}` must be 7 to 40 lowercase hex characters, got {value!r}")
    return value


def _canonical_step(obj: object, source: str) -> tuple[Step, str | None]:
    if not isinstance(obj, dict):
        raise _bad(source, "a step must be a JSON object")
    unknown = sorted(set(obj) - _CANONICAL_STEP_KEYS - {"schema"})
    if unknown:
        raise _bad(source, f"unknown step key(s) {unknown}")
    step_id = obj.get("step_id")
    if not isinstance(step_id, str) or not step_id.strip() or step_id != step_id.strip() or "\n" in step_id:
        raise _bad(source, f"`step_id` must be a non-empty single-line string, got {step_id!r}")
    where = f"{source} step {step_id!r}"
    returncode = _opt_int(obj, "returncode", where, minimum=None)
    exit_code = _opt_int(obj, "exit_code", where, minimum=None)
    if returncode is not None and exit_code is not None and returncode != exit_code:
        raise _bad(where, "`returncode` and `exit_code` disagree", "INCONSISTENT_RECEIPT")
    step = Step(
        step_id=step_id,
        kind="canonical",
        source=source,
        command=_opt_str(obj, "command", where),
        returncode=returncode if returncode is not None else exit_code,
        ok=_opt_bool(obj, "ok", where),
        fatal_error=_opt_str(obj, "fatal_error", where),
        axioms=_axioms(obj.get("axioms"), where),
    )
    for key, metric in _CANONICAL_COUNT_KEYS.items():
        value = _opt_int(obj, key, where)
        if value is not None:
            step.counts[metric] = value
    if step.returncode is None and step.ok is None:
        raise _bad(where, "a step needs `returncode`, `exit_code` or `ok`")
    failure = Step(**{**step.__dict__, "ok": None}).failure()
    if step.ok is True and failure is not None:
        raise _bad(where, f"`ok` is true but {failure}", "INCONSISTENT_RECEIPT")
    if step.ok is False and step.returncode == 0:
        raise _bad(where, "`ok` is false but the exit code is 0", "INCONSISTENT_RECEIPT")
    return step, _receipt_sha(obj.get("commit_sha"), where, "commit_sha")


def _guard_mutation_step(obj: dict[str, object], step_id: str, source: str) -> Step:
    ok = _opt_bool(obj, "ok", source)
    fatal = _opt_str(obj, "fatal_error", source)
    counts = {key: _opt_int(obj, key, source) for key in ("total", "killed", "survived", "errors")}
    results = obj.get("results")
    if ok is None or None in counts.values() or not isinstance(results, list):
        raise _bad(source, "guard-mutation report needs `ok`, the four counts and `results`")
    tally = {"KILLED": 0, "SURVIVED": 0, "ERROR": 0}
    for entry in results:
        status = entry.get("status") if isinstance(entry, dict) else None
        if status not in tally:
            raise _bad(source, f"guard-mutation result with unknown status {status!r}")
        tally[status] += 1
    total, killed, survived, errors = (counts[k] for k in ("total", "killed", "survived", "errors"))
    if fatal is None and (
        killed + survived + errors != total  # type: ignore[operator]
        or (tally["KILLED"], tally["SURVIVED"], tally["ERROR"]) != (killed, survived, errors)
    ):
        raise _bad(source, "guard-mutation counts contradict `results`", "INCONSISTENT_RECEIPT")
    expected_ok = fatal is None and total > 0 and killed == total and not survived and not errors  # type: ignore[operator]
    if ok != expected_ok:
        raise _bad(source, f"`ok` is {ok} but the counts say {expected_ok}", "INCONSISTENT_RECEIPT")
    return Step(
        step_id=step_id,
        kind="guard_mutation",
        source=source,
        returncode=0 if ok else 1,
        ok=ok,
        fatal_error=fatal,
        counts={k: v for k, v in counts.items() if v is not None},
    )


def _check_trusted_step(obj: dict[str, object], step_id: str, source: str) -> Step:
    step = Step(step_id=step_id, kind="check_trusted", source=source)
    step.axioms = _axioms(obj.get("axioms"), source)
    downstream = obj.get("downstream")
    theorems = None
    for holder in (obj, downstream if isinstance(downstream, dict) else {}):
        value = _opt_int(holder, "claimTheoremsChecked", source)
        theorems = value if value is not None else theorems
    if theorems is not None:
        step.counts["theorems"] = theorems
    for key, metric in (("kernelDeclarations", "kernel_declarations"),
                        ("replayedDeclarations", "replayed_declarations")):
        value = _opt_int(obj, key, source)
        if value is None and isinstance(downstream, dict):
            value = _opt_int(downstream, key, source)
        if value is not None:
            step.counts[metric] = value
    digest = obj.get("sourceSha256")
    if digest is not None and not (isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest)):
        raise _bad(source, "`sourceSha256` must be 64 lowercase hex characters")
    replay = _opt_bool(obj, "replay", source)
    # The audit only writes a report (or prints its summary) after it passed;
    # a recorded `replay: false` says the kernel replay did not hold.
    step.ok = True if replay is None else replay
    step.returncode = 0 if step.ok else 1
    return step


def _nightly_step(obj: object, source: str) -> Step:
    if not isinstance(obj, dict):
        raise _bad(source, "a nightly step must be a JSON object")
    name = obj.get("name")
    status = obj.get("status")
    if not isinstance(name, str) or not name.strip() or "\n" in name or not isinstance(status, str):
        raise _bad(source, "a nightly step needs a `name` and a `status` string")
    where = f"{source} step {name!r}"
    exit_code = _opt_int(obj, "exit_code", where, minimum=None)
    if exit_code is None:
        raise _bad(where, "a nightly step needs an integer `exit_code`")
    if (status == "PASS") != (exit_code == 0):
        raise _bad(where, f"status {status!r} contradicts exit code {exit_code}", "INCONSISTENT_RECEIPT")
    return Step(
        step_id=name.strip(),
        kind="nightly",
        source=source,
        command=_opt_str(obj, "command", where),
        returncode=exit_code,
        ok=status == "PASS",
        status=status,
    )


def load_receipt(
    path: Path, forced_id: str | None = None, *, no_symlinks: bool = False, bundle_only: bool = False
) -> tuple[list[Step], list[str]]:
    """Normalize one receipt file into steps and the commit SHAs it names."""
    source = str(path)
    text = read_regular_utf8(
        path, no_symlinks=no_symlinks, missing_code="MISSING_RECEIPT", bad_code="MALFORMED_RECEIPT"
    )
    stdout_form = text.strip().startswith(_CHECK_TRUSTED_STDOUT_PREFIX)
    if stdout_form:
        text = text.strip()[len(_CHECK_TRUSTED_STDOUT_PREFIX):]
    try:
        obj = parse_strict_json(text)
    except ValueError as exc:
        raise _bad(source, f"malformed JSON: {exc}") from exc
    if not isinstance(obj, dict):
        raise _bad(source, "a receipt must be a JSON object")
    steps: list[Step] = []
    shas: list[str] = []

    def single(default_id: str) -> str:
        return forced_id or default_id

    if "schema" in obj and not stdout_form:
        if obj["schema"] != RECEIPT_SCHEMA:
            raise _bad(source, f"unknown receipt schema {obj['schema']!r}")
        top_sha = _receipt_sha(obj.get("commit_sha"), source, "commit_sha")
        if "steps" in obj:
            unknown = sorted(set(obj) - _CANONICAL_TOP_KEYS)
            if unknown:
                raise _bad(source, f"unknown bundle key(s) {unknown}")
            if not isinstance(obj["steps"], list) or not obj["steps"]:
                raise _bad(source, "`steps` must be a non-empty array")
            if forced_id is not None:
                raise _bad(source, "a STEP_ID= prefix cannot name a multi-step bundle")
            for entry in obj["steps"]:
                step, sha = _canonical_step(entry, source)
                steps.append(step)
                shas += [sha] if sha else []
        else:
            step, _ = _canonical_step(obj, source)
            step.step_id = single(step.step_id)
            steps.append(step)
        shas += [top_sha] if top_sha else []
    elif bundle_only:
        raise _bad(source, f"--receipt-bundle needs a {RECEIPT_SCHEMA} receipt")
    elif not stdout_form and {"ok", "fatal_error", "total", "killed", "survived", "errors", "results"} <= set(obj):
        steps.append(_guard_mutation_step(obj, single("guard_mutation"), source))
    elif not stdout_form and isinstance(obj.get("pillar_2_correctness_and_correspondence"), dict):
        entries = obj["pillar_2_correctness_and_correspondence"].get("steps")  # type: ignore[union-attr]
        if not isinstance(entries, list) or not entries:
            raise _bad(source, "nightly dashboard has no `steps`")
        if forced_id is not None:
            raise _bad(source, "a STEP_ID= prefix cannot name a multi-step dashboard")
        steps += [_nightly_step(entry, source) for entry in entries]
        for key in ("unstable_commit_sha", "git_sha", "commit_sha"):
            value = obj.get(key)
            if isinstance(value, str) and _SHA_RE.fullmatch(value) and set(value) != {"0"}:
                shas.append(value)
                break
    elif not stdout_form and {"name", "status", "exit_code"} <= set(obj):
        step = _nightly_step(obj, source)
        step.step_id = single(step.step_id)
        steps.append(step)
    elif stdout_form or set(obj) & {"kernelDeclarations", "claimTheoremsChecked", "replayedDeclarations",
                                    "sourceSha256", "rustcCapture"}:
        steps.append(_check_trusted_step(obj, single("check_trusted"), source))
    else:
        raise _bad(source, "unrecognized receipt format")
    return steps, shas


# ---------------------------------------------------------------------------
# Claim extraction
# ---------------------------------------------------------------------------

_NUM = r"(?<![\w.,/=])([~≈<>≥≤+\-]?)([0-9]+(?:[,._][0-9]+)*)"
_COUNT_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("passed", re.compile(_NUM + r"\s+(?:(?:unit\s+|doc\s+)?tests?\s+|checks?\s+)?(?:passed|passing|pass)\b", re.I)),
    ("failed", re.compile(_NUM + r"\s+(?:(?:unit\s+|doc\s+)?tests?\s+)?(?:failed|failing|failures?)\b", re.I)),
    ("survived", re.compile(_NUM + r"\s+(?:mutants?\s+|guards?\s+)?(?:survived|surviving|survivors?)\b", re.I)),
    ("killed", re.compile(_NUM + r"\s+(?:mutants?\s+|guards?\s+)?killed\b", re.I)),
    ("errors", re.compile(_NUM + r"\s+errors?\b", re.I)),
    (
        "theorems",
        re.compile(
            _NUM + r"\s+(?:(?:new|proved|proven|kernel-checked|checked|verified|Lean|total|"
            r"public|universal)\s+){0,2}theorems?\b",
            re.I,
        ),
    ),
    ("sorry", re.compile(_NUM + r"\s+`?sorr(?:y|ies)\b`?", re.I)),
)
_KV_COUNT_RE = re.compile(
    r"(?i)(?<![\w-])(passed|failed|killed|survived|errors|theorems?|sorry|total)(?:_count)?"
    r"\s*[=:]\s*`?([~≈<>≥≤+\-]?)([0-9]+(?:[,._][0-9]+)*)"
)
_FRACTION_RE = re.compile(
    _NUM + r"\s*/\s*([0-9]+(?:[,._][0-9]+)*)\s+(?:mutants?\s+|guards?\s+|tests?\s+)?(killed|passed)\b", re.I
)
_KILL_RATE_RES: tuple[re.Pattern[str], ...] = (
    re.compile(r"(?i)(?<![\w.,/])([~≈<>≥≤+\-]?)([0-9]+(?:[,._][0-9]+)*)\s*%\s+(?:kill[ -]rate|killed|mutation\s+score)\b"),
    re.compile(r"(?i)\bkill[ _-]rate(?:_pct)?\s*(?:[=:]|of|is)?\s*`?([~≈<>≥≤+\-]?)([0-9]+(?:[,._][0-9]+)*)\s*%?"),
)
_ZERO_WORD_RES: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("failed", re.compile(r"(?i)\b(?:no|zero)\s+(?:test\s+)?failures?\b")),
    ("survived", re.compile(r"(?i)\b(?:no|zero)\s+surviv(?:ors?|ing(?:\s+mutants?)?)\b")),
    ("sorry", re.compile(r"(?i)\b(?:no|zero|without)\s+`?sorr(?:y|ies)\b`?|\bsorry-free\b")),
)
_RC_ASSIGN_RE = re.compile(
    r"(?i)(?<![\w-])(?:rc|exit[ _-]?code|exit[ _-]?status|return[ _]?code)\s*[=:]\s*`?([^\s`,;)|*]+)"
)
_RC_PROSE_RE = re.compile(
    r"(?i)(?<![\w-])(?:exit(?:ed)?(?:\s+with)?(?:\s+code|\s+status)?|rc|return\s+code)\s+"
    r"(?:is\s+|was\s+|of\s+)?`?(-?[0-9]+)\b"
)
_STATUS_RE = re.compile(r"(?i)(?<![\w-])(?:status|result|verdict|outcome)\s*[=:]\s*[`*_]*([A-Za-z]+)")
_OK_RE = re.compile(r"(?i)(?<![\w-])ok\s*[=:]\s*`?(true|false)\b")
_VERDICT_TOKEN_RE = re.compile(r"(?<![\w/-])(PASS(?:ED)?|FAIL(?:ED)?|✅|❌)(?![\w/-])")
_ALL_PASS_RE = re.compile(
    r"(?i)\ball\s+(?:[\w-]+\s+){0,3}(?:pass(?:ed|es)?|green|succeed(?:ed)?)\b"
)
_PASS_WORDS: frozenset[str] = frozenset({"PASS", "PASSED", "PASSING", "OK", "SUCCESS", "GREEN", "✅"})
_FAIL_WORDS: frozenset[str] = frozenset(
    {"FAIL", "FAILED", "FAILING", "FAILURE", "ERROR", "RED", "TIMEOUT", "❌"}
)
_SHA_CLAIM_RE = re.compile(
    r"(?i)(?<![\w/-])(?P<label>(?:(?:base|parent|previous|prior|old|head|target|tip|final|new|current)"
    r"\s+)*(?:commit(?:\s+(?:sha|hash|id))?|sha|revision|head|base|parent|target))(?![\w-])"
    r"(?:\s+(?:is|was|at|of)){0,2}\s*(?P<sep>[:=])?\s*(?P<tick>`?)(?P<value>[0-9A-Za-z/_.?-]+)"
)
_BASE_ROLE_RE = re.compile(r"(?i)\b(?:base|parent|previous|prior|old)\b")
_SHA_PLACEHOLDERS: frozenset[str] = frozenset({"unknown", "none", "n/a", "na", "tbd", "null", "dirty", "?"})
_STANDARD_AXIOMS_RE = re.compile(
    r"(?i)\b(?:only\s+)?(?:the\s+)?(?:three\s+)?standard\s+(?:kernel\s+|Lean\s+)?axioms?(?:\s+only)?\b"
    r"|\b(?:no|zero)\s+(?:non-?standard|extra|additional|unauthorized|custom)\s+axioms?\b"
)
_NO_AXIOMS_RE = re.compile(r"(?i)\b(?:no|zero)\s+axioms?\b|\baxiom-free\b")
_AXIOM_LIST_RE = re.compile(r"(?i)(?<![\w-])axioms?(?:\s+used|\s+set|\s+closure)?\s*[=:]\s*(.+)$")
_EXPLICIT_STEP_RE = re.compile(r"(?i)(?<![\w-])step(?:[ _-]?id)?\s*[=:]\s*`?([A-Za-z0-9][\w.:/-]*)")
_CODE_SPAN_RE = re.compile(r"`([^`\n]+)`")
_COMMAND_HEAD_RE = re.compile(
    r"(?:\./|(?:python3?|cargo|lake|lean|anneal-lean-run|bash|sh|git|pytest|make|rg)\b)"
)
_FENCE_RE = re.compile(r"^\s{0,3}(```|~~~)")
_HISTORICAL_RE = re.compile(
    r"(?i)^(?:[-*+>\s]|[0-9]+[.)])*[\[(*_]*(?:historical|previously|superseded|obsolete)[\])*_]*\s*[:\-–]"
)
_STRIKE_RE = re.compile(r"~~.*?~~")
_HTML_COMMENT_RE = re.compile(r"<!--.*?-->")
_IGNORE_BEGIN = "<!-- claim-guard: ignore-begin -->"
_IGNORE_END = "<!-- claim-guard: ignore-end -->"
_INVISIBLE_RE = re.compile("[\u200b-\u200f\u2060-\u2064\ufeff\u00ad]")
_CONTROL_RE = re.compile("[\x00-\x08\x0b\x0c\x0e-\x1f\x7f\u202a-\u202e\u2066-\u2069]")


def _parse_count(prefix: str, token: str) -> int | None:
    """An exact non-negative integer (`42`, `1,234`), or `None` when it is anything else."""
    token = token.rstrip(".,;:")
    if prefix:
        return None
    if re.fullmatch(r"[0-9]+", token):
        return int(token)
    if re.fullmatch(r"[0-9]{1,3}(?:,[0-9]{3})+", token):
        return int(token.replace(",", ""))
    return None


class _KnownSteps:
    """Step ids and commands of the loaded receipts, for attributing claims."""

    def __init__(self, steps: Sequence[Step]) -> None:
        self.ids = {step.step_id for step in steps}
        self.id_res = [
            (step_id, re.compile(r"(?<![\w./-])" + re.escape(step_id) + r"(?![\w/-])"))
            for step_id in sorted(self.ids, key=lambda s: (-len(s), s))
        ]
        self.commands: dict[str, set[str]] = {}
        for step in steps:
            if step.command:
                self.commands.setdefault(" ".join(step.command.split()), set()).add(step.step_id)

    def by_command(self, span: str) -> str | None:
        """The one step whose command is `span`, allowing a `wrapper -- ` prefix on either."""
        hits: set[str] = set()
        for command, step_ids in self.commands.items():
            if span == command or command.endswith(" -- " + span) or span.endswith(" -- " + command):
                hits |= step_ids
        return next(iter(hits)) if len(hits) == 1 else None


def _line_refs(line: str, known: _KnownSteps, in_fence: bool) -> list[tuple[int, str | None, str, bool]]:
    """`(position, step id or None, name, explicit)` for every step the line names."""
    refs: list[tuple[int, str | None, str, bool]] = []
    taken: list[tuple[int, int]] = []

    def add(m_start: int, m_end: int, step_id: str | None, name: str, explicit: bool) -> None:
        refs.append((m_start, step_id, name, explicit))
        taken.append((m_start, m_end))

    for m in _EXPLICIT_STEP_RE.finditer(line):
        name = m.group(1).rstrip(".,;:")
        add(m.start(), m.end(), name if name in known.ids else None, name, True)
    if in_fence:
        stripped = line.strip()
        shell = stripped.startswith("$ ")
        candidate = " ".join((stripped[2:] if shell else stripped).split())
        step_id = known.by_command(candidate)
        if step_id is not None or shell:
            add(0, len(line), step_id, candidate, False)
    for m in _CODE_SPAN_RE.finditer(line):
        span = " ".join(m.group(1).split())
        step_id = span if span in known.ids else known.by_command(span)
        if step_id is not None or _COMMAND_HEAD_RE.match(span):
            add(m.start(), m.end(), step_id, span, False)
    for step_id, pattern in known.id_res:
        for m in pattern.finditer(line):
            if not any(lo < m.end() and m.start() < hi for lo, hi in taken):
                add(m.start(), m.end(), step_id, step_id, False)
    refs.sort(key=lambda ref: ref[0])
    return refs


def _classify_sha(value: str, explicit: bool) -> tuple[str, str]:
    """`("valid", sha)`, `("ignore", "")`, or a violation code with its reason."""
    token = value.strip("`'\"").rstrip(".,;:)")
    if _SHA_RE.fullmatch(token):
        if set(token) == {"0"}:
            return "INVALID_COMMIT_SHA", f"`{token}` is the all-zero SHA"
        if not explicit and not any(ch.isdigit() for ch in token):
            return "ignore", ""
        return "valid", token
    has_digit = any(ch.isdigit() for ch in token)
    if explicit and token.lower() in _SHA_PLACEHOLDERS:
        return "INVALID_COMMIT_SHA", f"`{token}` is a placeholder, not a commit SHA"
    # An English word made of hex letters (`added`, `dead`) is prose unless it
    # carries a digit or sits in backticks.
    if re.fullmatch(r"[0-9a-fA-F]+", token) and (has_digit or value.startswith("`")):
        if len(token) < 7:
            if explicit and (len(token) >= 4 or value.startswith("`")):
                return "AMBIGUOUS_COMMIT_SHA", f"`{token}` is shorter than 7 hex characters"
            return "ignore", ""
        reason = "longer than 40 characters" if len(token) > 40 else "not lowercase hex"
        return "INVALID_COMMIT_SHA", f"`{token}` is {reason}"
    if explicit and has_digit and len(token) >= 7 and re.fullmatch(r"[0-9A-Za-z]+", token):
        return "INVALID_COMMIT_SHA", f"`{token}` is not hexadecimal"
    return "ignore", ""


def _axiom_names(rest: str) -> frozenset[str] | None:
    """Axiom names of an `axioms: ...` list; `None` when the list cannot be read."""
    names: set[str] = set()
    for raw in re.split(r"[,\s+]+|\band\b", rest.strip()):
        token = raw.strip("`'\"[](){}*_").rstrip(".;:")
        if not token:
            continue
        if token.lower() in ("none", "no", "empty", "∅") and not names:
            return frozenset()
        if not _AXIOM_NAME_RE.fullmatch(token):
            break
        names.add(token)
    return frozenset(names) if names else None


def _line_claims(
    line: str, lineno: int, violations: list[Violation]
) -> list[tuple[int, str, str, object, str]]:
    """`(position, kind, metric, value, text)` claims of one line, each span used once."""
    found: list[tuple[int, str, str, object, str]] = []
    work = [line]

    def take(m: re.Match[str]) -> None:
        work[0] = work[0][: m.start()] + " " * (m.end() - m.start()) + work[0][m.end():]

    def count(m: re.Match[str], prefix: str, token: str) -> int | None:
        value = _parse_count(prefix, token)
        if value is None:
            violations.append(
                Violation("MALFORMED_CLAIM", lineno, None,
                          f"`{m.group(0).strip()}` is not an exact non-negative integer claim")
            )
        return value

    for m in list(_SHA_CLAIM_RE.finditer(work[0])):
        explicit = bool(m.group("sep")) or bool(m.group("tick"))
        verdict, detail = _classify_sha(m.group("tick") + m.group("value"), explicit)
        if verdict == "ignore":
            continue
        take(m)
        if verdict == "valid":
            role = "base" if _BASE_ROLE_RE.search(m.group("label")) else "head"
            found.append((m.start(), "commit_sha", role, detail, m.group(0).strip()))
        else:
            violations.append(Violation(verdict, lineno, None, f"commit SHA claim: {detail}"))
    for m in list(_FRACTION_RE.finditer(work[0])):
        take(m)
        part, whole = count(m, m.group(1), m.group(2)), count(m, "", m.group(3))
        if part is not None and whole is not None:
            metric = m.group(4).lower()
            found.append((m.start(), "count", metric, part, m.group(0).strip()))
            found.append((m.start(), "count", "total" if metric == "killed" else "tests", whole,
                          m.group(0).strip()))
    for pattern in _KILL_RATE_RES:
        for m in list(pattern.finditer(work[0])):
            take(m)
            token = m.group(2).rstrip(".,;:")
            if m.group(1) or not re.fullmatch(r"[0-9]+(?:\.[0-9]+)?", token):
                violations.append(Violation("MALFORMED_CLAIM", lineno, None,
                                            f"`{m.group(0).strip()}` is not an exact kill rate"))
            else:
                found.append((m.start(), "kill_rate", "kill_rate", float(token), m.group(0).strip()))
    for m in list(_KV_COUNT_RE.finditer(work[0])):
        take(m)
        value = count(m, m.group(2), m.group(3))
        if value is not None:
            metric = m.group(1).lower()
            found.append((m.start(), "count", "theorems" if metric.startswith("theorem") else metric,
                          value, m.group(0).strip()))
    for metric, pattern in _COUNT_PATTERNS:
        for m in list(pattern.finditer(work[0])):
            take(m)
            value = count(m, m.group(1), m.group(2))
            if value is not None:
                found.append((m.start(), "count", metric, value, m.group(0).strip()))
    for metric, pattern in _ZERO_WORD_RES:
        for m in list(pattern.finditer(work[0])):
            take(m)
            found.append((m.start(), "count", metric, 0, m.group(0).strip()))
    for m in list(_RC_ASSIGN_RE.finditer(work[0])):
        take(m)
        token = m.group(1).rstrip(".:")
        if re.fullmatch(r"-?[0-9]+", token):
            found.append((m.start(), "exit_status", "rc", int(token), m.group(0).strip()))
        else:
            violations.append(Violation("MALFORMED_CLAIM", lineno, None,
                                        f"`{m.group(0).strip()}` is not an integer exit code"))
    for m in list(_RC_PROSE_RE.finditer(work[0])):
        take(m)
        found.append((m.start(), "exit_status", "rc", int(m.group(1)), m.group(0).strip()))
    for pattern in (_STATUS_RE, _OK_RE, _VERDICT_TOKEN_RE):
        for m in list(pattern.finditer(work[0])):
            word = m.group(1).upper()
            verdict = (
                "pass" if word in _PASS_WORDS or word == "TRUE"
                else "fail" if word in _FAIL_WORDS or word == "FALSE" else ""
            )
            if verdict:
                take(m)
                found.append((m.start(), "exit_status", "status", verdict, m.group(0).strip()))
    for m in list(_ALL_PASS_RE.finditer(work[0])):
        take(m)
        found.append((m.start(), "exit_status", "all", "pass", m.group(0).strip()))
    for m in list(_STANDARD_AXIOMS_RE.finditer(work[0])):
        take(m)
        found.append((m.start(), "axioms", "standard_only", None, m.group(0).strip()))
    for m in list(_NO_AXIOMS_RE.finditer(work[0])):
        take(m)
        found.append((m.start(), "axioms", "set", frozenset(), m.group(0).strip()))
    m_list = _AXIOM_LIST_RE.search(work[0])
    if m_list is not None:
        names = _axiom_names(m_list.group(1))
        words = {name.lower() for name in names or ()}
        if names is None:
            violations.append(Violation("MALFORMED_CLAIM", lineno, None,
                                        f"`{m_list.group(0).strip()}` lists no readable axiom name"))
        elif "standard" in words and words <= {"standard", "only", "the", "three", "lean", "kernel"}:
            found.append((m_list.start(), "axioms", "standard_only", None, m_list.group(0).strip()))
        else:
            found.append((m_list.start(), "axioms", "set", names, m_list.group(0).strip()))
    found.sort(key=lambda claim: claim[0])
    return found


def extract_claims(text: str, steps: Sequence[Step]) -> tuple[list[Claim], list[Violation], int]:
    """Claims of a Markdown document, the violations found while reading it, and the
    number of explicitly ignored lines."""
    violations: list[Violation] = []
    claims: list[Claim] = []
    ignored = 0
    text = unicodedata.normalize("NFKC", text)
    if _CONTROL_RE.search(text):
        violations.append(
            Violation("MALFORMED_CLAIMS", 0, None,
                      "the document contains control or bidirectional-override characters")
        )
        text = _CONTROL_RE.sub(" ", text)
    text = _INVISIBLE_RE.sub("", text)
    known = _KnownSteps(steps)
    in_fence = in_ignore = in_comment = False
    ignore_line = 0
    heading_ctx: tuple[str | None, str, bool] | None = None
    para_ctx: tuple[str | None, str, bool] | None = None
    for lineno, line in enumerate(text.split("\n"), 1):
        if in_ignore:
            ignored += 1
            if _IGNORE_END in line:
                in_ignore = False
            continue
        if _IGNORE_BEGIN in line:
            in_ignore, ignore_line = True, lineno
            ignored += 1
            if _IGNORE_END in line.split(_IGNORE_BEGIN, 1)[1]:
                in_ignore = False
            continue
        if in_comment:
            if "-->" not in line:
                continue
            line = line.split("-->", 1)[1]
            in_comment = False
        line = _HTML_COMMENT_RE.sub(" ", line)
        if "<!--" in line:
            line = line.split("<!--", 1)[0]
            in_comment = True
        if _FENCE_RE.match(line):
            in_fence = not in_fence
            para_ctx = None
            continue
        line = _STRIKE_RE.sub(" ", line)
        if not line.strip():
            if not in_fence:
                para_ctx = None
            continue
        if _HISTORICAL_RE.match(line):
            ignored += 1
            continue
        refs = _line_refs(line, known, in_fence)
        for pos, kind, metric, value, snippet in _line_claims(line, lineno, violations):
            if kind == "commit_sha" or metric == "all":
                # A commit names the whole run, and "all ... pass" every step.
                claims.append(Claim(kind, metric, value, lineno, snippet, None))
                continue
            before = [ref for ref in refs if ref[0] <= pos]
            ref = (before[-1] if before else refs[0]) if refs else (para_ctx or heading_ctx)
            ref3 = ref[-3:] if ref else None
            if ref3 is None:
                claims.append(Claim(kind, metric, value, lineno, snippet, None))
            elif ref3[0] is None:
                missing = ("step:" if ref3[2] else "command:") + ref3[1]
                claims.append(Claim(kind, metric, value, lineno, snippet, None, missing))
            else:
                claims.append(Claim(kind, metric, value, lineno, snippet, ref3[0]))
        distinct = sorted({ref[1:] for ref in refs}, key=repr)
        is_heading = not in_fence and line.lstrip().startswith("#")
        if is_heading:
            heading_ctx = distinct[0] if len(distinct) == 1 else None
            para_ctx = None
        elif distinct:
            para_ctx = distinct[0] if len(distinct) == 1 else None
    if in_ignore:
        violations.append(
            Violation("MALFORMED_CLAIMS", ignore_line, None,
                      "`claim-guard: ignore-begin` is never closed")
        )
    return claims, violations, ignored


# ---------------------------------------------------------------------------
# Verification
# ---------------------------------------------------------------------------


def _sha_compatible(a: str, b: str) -> bool:
    return a.startswith(b) or b.startswith(a)


def _count_code(metric: str, claimed: int, actual: int) -> str:
    if metric == "theorems":
        return "THEOREM_COUNT_MISMATCH"
    if metric == "sorry":
        return "SORRY_VIOLATION"
    if metric in _GOOD_METRICS and claimed > actual:
        return "INFLATED_COUNT"
    return "COUNT_MISMATCH"


def _metric_value(step: Step, metric: str) -> int | None:
    if metric == "tests":
        if "passed" in step.counts and "failed" in step.counts:
            return step.counts["passed"] + step.counts["failed"]
        return None
    return step.counts.get(metric)


def verify_claims(
    claims: Sequence[Claim],
    steps: Sequence[Step],
    receipt_shas: Sequence[str],
    *,
    expected_sha: str | None = None,
    require_steps: Sequence[str] = (),
    conditional_axioms: Sequence[str] = (),
) -> list[Violation]:
    """Every way the claims and the receipts disagree."""
    out: list[Violation] = []
    by_id = {step.step_id: step for step in steps}

    def add(code: str, claim: Claim | None, message: str, step_id: str | None = None) -> None:
        out.append(Violation(code, claim.line if claim else 0, step_id or (claim.step if claim else None), message))

    # Receipts on their own: axioms, freshness, required steps.
    authorized = (ALLOWED_KERNEL_AXIOMS | set(conditional_axioms)) - NEVER_ALLOWED_AXIOMS
    for step in steps:
        for axiom in step.axioms or ():
            if axiom not in authorized:
                add("UNAUTHORIZED_AXIOM", None,
                    f"step `{step.step_id}` depends on the unauthorized axiom `{axiom}`", step.step_id)
    distinct_shas = sorted(set(receipt_shas))
    for i, sha in enumerate(distinct_shas):
        if any(not _sha_compatible(sha, other) for other in distinct_shas[i + 1:]):
            add("CONFLICTING_RECEIPT_SHA", None, f"receipts name different commits ({', '.join(distinct_shas)})")
            break
    if expected_sha is not None:
        for sha in distinct_shas:
            if not _sha_compatible(sha, expected_sha):
                add("STALE_RECEIPT", None, f"a receipt was produced at `{sha}`, not at the expected `{expected_sha}`")
    for step_id in require_steps:
        step = by_id.get(step_id)
        if step is None:
            add("MISSING_STEP_RECEIPT", None, f"required step `{step_id}` has no receipt", step_id)
        elif step.failure() is not None or not step.has_exit_evidence():
            add("REQUIRED_STEP_FAILED", None,
                f"required step `{step_id}` did not pass ({step.failure() or 'no exit status'})", step_id)

    # Commit SHA claims.
    evidence = distinct_shas + ([expected_sha] if expected_sha else [])
    heads = [claim for claim in claims if claim.kind == "commit_sha" and claim.metric == "head"]
    for i, claim in enumerate(heads):
        sha = str(claim.value)
        if any(not _sha_compatible(sha, str(other.value)) for other in heads[:i]):
            add("CONFLICTING_COMMIT_SHA", claim,
                f"`{sha}` contradicts an earlier head commit claim; label other commits `Base`")
        if not evidence:
            add("UNBACKED_CLAIM", claim, f"commit `{sha}` is claimed but no receipt names a commit")
        for known_sha in evidence:
            if not _sha_compatible(sha, known_sha):
                add("COMMIT_SHA_MISMATCH", claim, f"claimed commit `{sha}` is not the receipt commit `{known_sha}`")

    for claim in claims:
        if claim.kind == "commit_sha":
            continue
        if claim.missing:
            kind, _, name = claim.missing.partition(":")
            code = "MISSING_STEP_RECEIPT" if kind == "step" else "UNBACKED_CLAIM"
            add(code, claim, f"`{claim.text}` refers to {kind} `{name}`, which no receipt backs")
            continue
        targets = [by_id[claim.step]] if claim.step is not None else list(steps)
        scope = f"step `{claim.step}`" if claim.step is not None else "the receipts"

        if claim.kind == "exit_status":
            with_exit = [step for step in targets if step.has_exit_evidence()]
            if not with_exit:
                add("UNBACKED_CLAIM", claim, f"`{claim.text}`: {scope} record no exit status")
                continue
            claims_pass = claim.value == "pass" or claim.value == 0
            failing = [step for step in with_exit if step.failure() is not None]
            if claims_pass:
                for step in failing:
                    add("SUPPRESSED_FAILURE", claim,
                        f"`{claim.text}` but step `{step.step_id}` failed ({step.failure()})", step.step_id)
            elif claim.metric == "rc":
                codes = {step.returncode for step in with_exit if step.returncode is not None}
                if claim.value not in codes and not (not codes and failing):
                    add("EXIT_CODE_MISMATCH", claim,
                        f"`{claim.text}` but {scope} record exit code(s) {sorted(codes)}")
            elif not failing:
                add("EXIT_CODE_MISMATCH", claim, f"`{claim.text}` but {scope} passed")

        elif claim.kind == "count":
            metric, claimed = claim.metric, int(claim.value)  # type: ignore[call-overload]
            reporting = [step for step in targets if _metric_value(step, metric) is not None]
            if metric == "sorry":
                with_axioms = [step for step in targets if step.axioms is not None]
                if claimed == 0:
                    for step in with_axioms:
                        if "sorryAx" in (step.axioms or ()):
                            add("SORRY_VIOLATION", claim,
                                f"`{claim.text}` but step `{step.step_id}` depends on `sorryAx`", step.step_id)
                if not reporting and with_axioms and claimed == 0:
                    continue
            if not reporting:
                add("UNBACKED_CLAIM", claim, f"`{claim.text}`: {scope} report no `{metric}` count")
                continue
            actual = sum(_metric_value(step, metric) or 0 for step in reporting)
            if claimed != actual:
                basis = (
                    f"step `{reporting[0].step_id}` reports {actual}" if len(reporting) == 1
                    else f"the {len(reporting)} receipts that report it sum to {actual}; name the step"
                )
                add(_count_code(metric, claimed, actual), claim, f"`{claim.text}` but {basis}")

        elif claim.kind == "kill_rate":
            rated = [step for step in targets if step.counts.get("total") and "killed" in step.counts]
            if not rated:
                add("UNBACKED_CLAIM", claim, f"`{claim.text}`: {scope} report no kill counts")
                continue
            killed = sum(step.counts["killed"] for step in rated)
            total = sum(step.counts["total"] for step in rated)
            actual_rate = round(100.0 * killed / total, 2)
            if abs(float(claim.value) - actual_rate) > 0.005:  # type: ignore[arg-type]
                code = "INFLATED_COUNT" if float(claim.value) > actual_rate else "COUNT_MISMATCH"  # type: ignore[arg-type]
                add(code, claim, f"`{claim.text}` but the receipts give {killed}/{total} = {actual_rate}%")

        elif claim.kind == "axioms":
            with_axioms = [step for step in targets if step.axioms is not None]
            if not with_axioms:
                add("UNBACKED_CLAIM", claim, f"`{claim.text}`: {scope} report no axiom list")
                continue
            allowed = ALLOWED_KERNEL_AXIOMS if claim.metric == "standard_only" else claim.value
            for step in with_axioms:
                extra = sorted(set(step.axioms or ()) - set(allowed))  # type: ignore[arg-type]
                if extra:
                    add("AXIOM_SET_MISMATCH", claim,
                        f"`{claim.text}` omits axiom(s) {', '.join(extra)} of step `{step.step_id}`", step.step_id)
    return out


# ---------------------------------------------------------------------------
# Report and command line
# ---------------------------------------------------------------------------


def _empty_report(fatal_error: str | None) -> dict[str, object]:
    return {
        "schema": REPORT_SCHEMA,
        "ok": False,
        "fatal_error": fatal_error,
        "claims_checked": 0,
        "claims_ignored_lines": 0,
        "receipts": [],
        "claims": [],
        "violations": [],
    }


def run_guard(
    claims_text: str | None,
    receipt_specs: Sequence[tuple[Path, str | None, bool]],
    *,
    claims_error: InputError | None = None,
    expected_sha: str | None = None,
    require_steps: Sequence[str] = (),
    conditional_axioms: Sequence[str] = (),
    require_nonempty_claims: bool = True,
    no_symlinks: bool = False,
) -> dict[str, object]:
    """Load the receipts, extract the claims and return the deterministic report."""
    violations: list[Violation] = []
    steps: list[Step] = []
    shas: list[str] = []
    for path, forced_id, bundle_only in receipt_specs:
        try:
            loaded, loaded_shas = load_receipt(path, forced_id, no_symlinks=no_symlinks, bundle_only=bundle_only)
        except InputError as exc:
            violations.append(Violation(exc.code, 0, forced_id, exc.message))
            continue
        for step in loaded:
            if any(step.step_id == other.step_id for other in steps):
                violations.append(Violation("DUPLICATE_STEP_RECEIPT", 0, step.step_id,
                                            f"{step.source}: step `{step.step_id}` already has a receipt"))
            else:
                steps.append(step)
        shas += loaded_shas
    claims: list[Claim] = []
    ignored = 0
    if claims_error is not None:
        violations.append(Violation(claims_error.code, 0, None, claims_error.message))
    else:
        claims, claim_violations, ignored = extract_claims(claims_text or "", steps)
        violations += claim_violations
        # A document whose only claims are unreadable already fails for that.
        if not claims and not claim_violations and require_nonempty_claims:
            violations.append(Violation("NO_CLAIMS_EXTRACTED", 0, None,
                                        "the document makes no checkable verification claim"))
    violations += verify_claims(
        claims, steps, shas,
        expected_sha=expected_sha, require_steps=require_steps, conditional_axioms=conditional_axioms,
    )
    violations = sorted(set(violations), key=lambda v: (v.line, v.code, v.step_id or "", v.message))
    report = _empty_report(None)
    report.update(
        ok=not violations,
        claims_checked=len(claims),
        claims_ignored_lines=ignored,
        receipts=[{"step_id": s.step_id, "kind": s.kind, "source": s.source} for s in steps],
        claims=[
            {
                "kind": c.kind,
                "metric": c.metric,
                "value": sorted(c.value) if isinstance(c.value, frozenset) else c.value,
                "line": c.line,
                "step": c.step,
                "text": c.text,
            }
            for c in claims
        ],
        violations=[asdict(v) for v in violations],
    )
    return report


def format_report(report: dict[str, object]) -> str:
    lines = [
        f"VIOLATION {v['code']}"
        + (f" [line {v['line']}]" if v["line"] else "")
        + (f" [step {v['step_id']}]" if v["step_id"] else "")
        + f": {v['message']}"
        for v in report["violations"]  # type: ignore[union-attr]
    ]
    lines.append(
        f"receipt-claim-guard: {'PASS' if report['ok'] else 'FAIL'} "
        f"({len(report['violations'])} violation(s), "  # type: ignore[arg-type]
        f"{report['claims_checked']} claim(s), "
        f"{len(report['receipts'])} receipt step(s))"  # type: ignore[arg-type]
    )
    return "\n".join(lines)


def _write_json_out(path: Path, report: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check the verification claims of a handoff against JSON receipts.",
        allow_abbrev=False,
    )
    parser.add_argument("--claims", default=None, help="Markdown to audit (default or `-`: stdin).")
    parser.add_argument("--receipt", action="append", default=[], metavar="[STEP_ID=]PATH",
                        help="A receipt file (repeatable).")
    parser.add_argument("--receipt-bundle", action="append", default=[], type=Path, metavar="PATH",
                        help=f"A {RECEIPT_SCHEMA} bundle (repeatable).")
    parser.add_argument("--expected-sha", default=None, help="The commit every claim and receipt must name.")
    parser.add_argument("--require-step", action="append", default=[], metavar="STEP_ID",
                        help="A step that must have a passing receipt (repeatable).")
    parser.add_argument("--allow-conditional-axiom", action="append", default=[], metavar="NAME",
                        help="Authorize one more kernel axiom (repeatable).")
    empties = parser.add_mutually_exclusive_group()
    empties.add_argument("--require-nonempty-claims", dest="require_nonempty", action="store_true",
                         default=True, help="Fail when no claim is extracted (default).")
    empties.add_argument("--allow-empty-claims", dest="require_nonempty", action="store_false",
                         help="Accept a document that makes no checkable claim.")
    parser.add_argument("--no-symlinks", action="store_true", help="Reject symlinked input paths.")
    parser.add_argument("--json", dest="emit_json", action="store_true",
                        help="Print the JSON report on stdout, and nothing else.")
    parser.add_argument("--json-out", type=Path, default=None, help="Write the JSON report to this path.")
    parser.add_argument("--max-elapsed-ms", type=float, default=None,
                        help="Fail when verification takes longer than this many milliseconds.")
    args = parser.parse_args(list(argv) if argv is not None else None)

    specs: list[tuple[Path, str | None, bool]] = []
    for raw in args.receipt:
        head, sep, tail = raw.partition("=")
        if sep and _STEP_ID_ARG_RE.fullmatch(head):
            if not tail:
                parser.error(f"--receipt {raw!r}: missing PATH after STEP_ID=")
            specs.append((Path(tail), head, False))
        elif not raw:
            parser.error("--receipt needs a PATH")
        else:
            specs.append((Path(raw), None, False))
    specs += [(path, None, True) for path in args.receipt_bundle]
    if not specs:
        parser.error("at least one --receipt or --receipt-bundle is required")
    if args.expected_sha is not None and (
        not _SHA_RE.fullmatch(args.expected_sha) or set(args.expected_sha) == {"0"}
    ):
        parser.error("--expected-sha must be 7 to 40 lowercase hex characters")
    for name in args.allow_conditional_axiom:
        if not _AXIOM_NAME_RE.fullmatch(name) or name in NEVER_ALLOWED_AXIOMS:
            parser.error(f"--allow-conditional-axiom {name!r} cannot be authorized")
    if any(not step_id.strip() for step_id in args.require_step):
        parser.error("--require-step needs a non-empty STEP_ID")
    if args.max_elapsed_ms is not None and not (0 < args.max_elapsed_ms < float("inf")):
        parser.error("--max-elapsed-ms must be a positive finite number")

    def write_out(report: dict[str, object]) -> bool:
        if args.json_out is None:
            return True
        try:
            _write_json_out(args.json_out, report)
            return True
        except OSError as exc:
            print(f"ERROR: cannot write {args.json_out}: {exc}", file=sys.stderr)
            return False

    # Fail-closed sink: a report left by an earlier green run must not outlive
    # a run that dies before it reports.
    sink_ok = write_out(_empty_report("run did not complete"))

    started = time.perf_counter()
    claims_text: str | None = None
    claims_error: InputError | None = None
    try:
        if args.claims is None or args.claims == "-":
            data = sys.stdin.buffer.read(MAX_INPUT_BYTES + 1)
            if len(data) > MAX_INPUT_BYTES:
                raise InputError("UNREADABLE_CLAIMS", f"stdin: larger than {MAX_INPUT_BYTES} bytes")
            try:
                claims_text = data.decode("utf-8")
            except UnicodeDecodeError as exc:
                raise InputError("UNREADABLE_CLAIMS", f"stdin: not valid UTF-8: {exc.reason}") from exc
        else:
            claims_text = read_regular_utf8(
                Path(args.claims), no_symlinks=args.no_symlinks,
                missing_code="UNREADABLE_CLAIMS", bad_code="UNREADABLE_CLAIMS",
            )
    except InputError as exc:
        claims_error = exc
    report = run_guard(
        claims_text,
        specs,
        claims_error=claims_error,
        expected_sha=args.expected_sha,
        require_steps=args.require_step,
        conditional_axioms=args.allow_conditional_axiom,
        require_nonempty_claims=args.require_nonempty,
        no_symlinks=args.no_symlinks,
    )
    elapsed_ms = (time.perf_counter() - started) * 1000.0
    if args.max_elapsed_ms is not None and elapsed_ms > args.max_elapsed_ms:
        report["violations"].append(  # type: ignore[union-attr]
            asdict(Violation("ELAPSED_BUDGET_EXCEEDED", 0, None,
                             f"verification exceeded --max-elapsed-ms={args.max_elapsed_ms:g}"))
        )
        report["ok"] = False
    if not sink_ok or not write_out(report):
        report["ok"] = False
    if args.emit_json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(format_report(report))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
