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
import tempfile
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


def _ensure_no_symlink_components(path: Path) -> None:
    """Raise `OSError` if `path` or any directory traversed to reach it is a symlink."""
    def check_parts(abs_parts: tuple[str, ...]) -> None:
        cur = Path(abs_parts[0])
        for part in abs_parts[1:]:
            if part in ("", "."):
                continue
            cur = cur / part
            if os.path.islink(cur):
                raise OSError(f"{cur}: is a symlink (--no-symlinks)")

    if path.is_absolute():
        check_parts(path.parts)
        return
    check_parts(Path(os.getcwd()).parts + path.parts)
    pwd = os.environ.get("PWD")
    if pwd and os.path.isabs(pwd):
        try:
            same = os.path.samefile(pwd, ".")
        except OSError:
            same = False
        if same:
            check_parts(Path(pwd).parts + path.parts)


def read_regular_utf8(path: Path, *, no_symlinks: bool, missing_code: str, bad_code: str) -> str:
    """Read a UTF-8 regular file, never blocking on a FIFO or device."""
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_CLOEXEC", 0)
    if no_symlinks:
        flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        if no_symlinks:
            _ensure_no_symlink_components(path)
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


def _opt_str(obj: dict[str, object], key: str, source: str, *, allow_empty: bool = True) -> str | None:
    value = obj.get(key)
    if value is not None and (not isinstance(value, str) or (not allow_empty and not value.strip())):
        kind = "a string" if allow_empty else "a non-empty string"
        raise _bad(source, f"`{key}` must be {kind}, got {value!r}")
    return value  # type: ignore[return-value]


def _opt_nonneg_num(obj: dict[str, object], key: str, source: str) -> float | None:
    value = obj.get(key)
    if value is None:
        return None
    if type(value) not in (int, float) or value < 0 or value != value or value == float("inf"):
        raise _bad(source, f"`{key}` must be a non-negative finite number, got {value!r}")
    return float(value)


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


def _validate_canonical_top_metadata(obj: dict[str, object], source: str) -> None:
    _opt_str(obj, "generated_at_utc", source, allow_empty=False)
    _opt_str(obj, "generator", source, allow_empty=False)
    artifacts = obj.get("artifacts")
    if artifacts is not None and not isinstance(artifacts, (list, dict)):
        raise _bad(source, f"`artifacts` must be a list or object, got {artifacts!r}")
    metadata = obj.get("metadata")
    if metadata is not None and not isinstance(metadata, dict):
        raise _bad(source, f"`metadata` must be a JSON object, got {metadata!r}")


def _canonical_step(obj: object, source: str, *, allow_schema: bool = False) -> tuple[Step, str | None]:
    if not isinstance(obj, dict):
        raise _bad(source, "a step must be a JSON object")
    extra_top = {"schema", "generated_at_utc", "generator", "metadata"} if allow_schema else set()
    allowed_keys = _CANONICAL_STEP_KEYS | extra_top
    unknown = sorted(set(obj) - allowed_keys)
    if unknown:
        raise _bad(source, f"unknown step key(s) {unknown}")
    if allow_schema:
        _validate_canonical_top_metadata(obj, source)
    step_id = obj.get("step_id")
    if (
        not isinstance(step_id, str)
        or not step_id.strip()
        or step_id != step_id.strip()
        or "\n" in step_id
        or "\r" in step_id
    ):
        raise _bad(source, f"`step_id` must be a non-empty single-line string, got {step_id!r}")
    where = f"{source} step {step_id!r}"
    returncode = _opt_int(obj, "returncode", where, minimum=None)
    exit_code = _opt_int(obj, "exit_code", where, minimum=None)
    if returncode is not None and exit_code is not None and returncode != exit_code:
        raise _bad(where, "`returncode` and `exit_code` disagree", "INCONSISTENT_RECEIPT")
    _opt_nonneg_num(obj, "duration_sec", where)
    artifacts = obj.get("artifacts")
    if artifacts is not None and not isinstance(artifacts, (list, dict)):
        raise _bad(where, f"`artifacts` must be a list or object, got {artifacts!r}")
    step = Step(
        step_id=step_id,
        kind="canonical",
        source=source,
        command=_opt_str(obj, "command", where),
        returncode=returncode if returncode is not None else exit_code,
        ok=_opt_bool(obj, "ok", where),
        fatal_error=_opt_str(obj, "fatal_error", where, allow_empty=False),
        axioms=_axioms(obj.get("axioms"), where),
    )
    for key, metric in _CANONICAL_COUNT_KEYS.items():
        value = _opt_int(obj, key, where)
        if value is not None:
            step.counts[metric] = value
    if "total" in step.counts:
        total = step.counts["total"]
        parts = [step.counts[k] for k in ("killed", "survived", "errors") if k in step.counts]
        if parts and sum(parts) > total:
            raise _bad(where, "guard-mutation counts exceed `total`", "INCONSISTENT_RECEIPT")
        if (
            step.fatal_error is None
            and all(k in step.counts for k in ("killed", "survived", "errors"))
            and sum(parts) != total
        ):
            raise _bad(where, "`killed + survived + errors` disagrees with `total`", "INCONSISTENT_RECEIPT")
    if step.returncode is None and step.ok is None:
        raise _bad(where, "a step needs `returncode`, `exit_code` or `ok`")
    failure = Step(**{**step.__dict__, "ok": None}).failure()
    if step.ok is True and failure is not None:
        raise _bad(where, f"`ok` is true but {failure}", "INCONSISTENT_RECEIPT")
    if step.ok is False and step.returncode == 0:
        raise _bad(where, "`ok` is false but the exit code is 0", "INCONSISTENT_RECEIPT")
    return step, _receipt_sha(obj.get("commit_sha"), where, "commit_sha")


def _guard_mutation_step(obj: dict[str, object], step_id: str, source: str) -> tuple[Step, str | None]:
    ok = _opt_bool(obj, "ok", source)
    fatal = _opt_str(obj, "fatal_error", source, allow_empty=False)
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
    kill_rate = _opt_nonneg_num(obj, "kill_rate_pct", source)
    if kill_rate is not None:
        if kill_rate > 100.0:
            raise _bad(source, f"`kill_rate_pct` exceeds 100: {kill_rate}", "INCONSISTENT_RECEIPT")
        if fatal is None and total:
            expected_rate = round(100.0 * killed / total, 2)  # type: ignore[operator]
            if abs(kill_rate - expected_rate) > 0.01 or (kill_rate >= 100.0 and killed < total):  # type: ignore[operator]
                raise _bad(
                    source,
                    f"`kill_rate_pct` ({kill_rate}) contradicts {killed}/{total}",
                    "INCONSISTENT_RECEIPT",
                )
    expected_ok = fatal is None and total > 0 and killed == total and not survived and not errors  # type: ignore[operator]
    if ok != expected_ok:
        raise _bad(source, f"`ok` is {ok} but the counts say {expected_ok}", "INCONSISTENT_RECEIPT")
    step = Step(
        step_id=step_id,
        kind="guard_mutation",
        source=source,
        returncode=0 if ok else 1,
        ok=ok,
        fatal_error=fatal,
        counts={k: v for k, v in counts.items() if v is not None},
    )
    return step, _receipt_sha(obj.get("commit_sha"), source, "commit_sha")


def _check_trusted_step(
    obj: dict[str, object], step_id: str, source: str, *, stdout_form: bool = False
) -> tuple[Step, str | None]:
    if stdout_form or "rustcCapture" in obj or "trusted" in obj:
        for section in ("trusted", "rustcCapture", "downstream"):
            if not isinstance(obj.get(section), dict):
                raise _bad(source, f"`check_trusted --audit-vacuity` summary missing `{section}` object")
    step = Step(step_id=step_id, kind="check_trusted", source=source)
    step.axioms = _axioms(obj.get("axioms"), source)
    downstream = obj.get("downstream")
    if downstream is not None and not isinstance(downstream, dict):
        raise _bad(source, "`downstream` must be a JSON object")
    down_dict = downstream if isinstance(downstream, dict) else {}
    trusted_dict = obj["trusted"] if isinstance(obj.get("trusted"), dict) else {}
    rustc_dict = obj["rustcCapture"] if isinstance(obj.get("rustcCapture"), dict) else {}

    def unique_int(key: str) -> int | None:
        top_val = _opt_int(obj, key, source)
        sub_val = _opt_int(down_dict, key, source)
        if top_val is not None and sub_val is not None and top_val != sub_val:
            raise _bad(source, f"`{key}` disagrees between top-level and `downstream`", "INCONSISTENT_RECEIPT")
        return top_val if top_val is not None else sub_val

    theorems = unique_int("claimTheoremsChecked")
    if theorems is not None:
        step.counts["theorems"] = theorems
    for key, metric in (("kernelDeclarations", "kernel_declarations"),
                        ("replayedDeclarations", "replayed_declarations")):
        value = unique_int(key)
        if value is not None:
            step.counts[metric] = value
    for top_key in ("compilerOnlyNames", "reachableDeclarations"):
        _opt_int(obj, top_key, source)
    if "graph" in obj and obj["graph"] is not None and not isinstance(obj["graph"], dict):
        raise _bad(source, "`graph` must be a JSON object")
    if "declarations" in obj and obj["declarations"] is not None and not isinstance(obj["declarations"], list):
        raise _bad(source, "`declarations` must be a JSON list")
    for down_key in ("downstreamModules", "localTestAxioms", "files", "leanFiles", "rustFiles"):
        _opt_int(down_dict, down_key, source)
    for tr_key in ("modules", "waivers", "files", "leanFiles", "rustFiles"):
        _opt_int(trusted_dict, tr_key, source)  # type: ignore[arg-type]
    for rc_key in ("files", "crates", "leanFiles", "rustFiles"):
        _opt_int(rustc_dict, rc_key, source)  # type: ignore[arg-type]
    digest = obj.get("sourceSha256")
    if digest is not None and not (isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest)):
        raise _bad(source, "`sourceSha256` must be 64 lowercase hex characters")
    replay = _opt_bool(obj, "replay", source)
    explicit_ok = _opt_bool(obj, "ok", source)
    returncode = _opt_int(obj, "returncode", source, minimum=None)
    exit_code = _opt_int(obj, "exit_code", source, minimum=None)
    if returncode is not None and exit_code is not None and returncode != exit_code:
        raise _bad(source, "`returncode` and `exit_code` disagree", "INCONSISTENT_RECEIPT")
    effective_rc = returncode if returncode is not None else exit_code
    status = _opt_str(obj, "status", source, allow_empty=False)
    fatal = _opt_str(obj, "fatal_error", source, allow_empty=False)
    failed = (
        replay is False
        or explicit_ok is False
        or fatal is not None
        or effective_rc not in (None, 0)
        or status not in (None, "PASS")
    )
    if explicit_ok is True and failed:
        raise _bad(source, "`ok` is true but the check_trusted receipt records a failure", "INCONSISTENT_RECEIPT")
    if (explicit_ok is False or replay is False) and effective_rc == 0:
        raise _bad(source, "check_trusted failure contradicts exit code 0", "INCONSISTENT_RECEIPT")
    if status == "PASS" and failed:
        raise _bad(source, "`status` is PASS but the check_trusted receipt records a failure", "INCONSISTENT_RECEIPT")
    step.fatal_error = fatal
    step.status = status
    # The audit only writes a report (or prints its summary) after it passed;
    # any explicit failure signal (`replay: false`, `ok: false`, non-zero rc,
    # `fatal_error`, non-PASS `status`) marks it failed.
    step.ok = not failed
    step.returncode = effective_rc if effective_rc is not None else (0 if step.ok else 1)
    return step, _receipt_sha(obj.get("commit_sha"), source, "commit_sha")


def _nightly_step(obj: object, source: str) -> tuple[Step, list[str]]:
    if not isinstance(obj, dict):
        raise _bad(source, "a nightly step must be a JSON object")
    name = obj.get("name")
    status = obj.get("status")
    if (
        not isinstance(name, str)
        or not name.strip()
        or name != name.strip()
        or "\n" in name
        or "\r" in name
        or not isinstance(status, str)
        or not status.strip()
    ):
        raise _bad(source, "a nightly step needs a non-empty `name` and `status` string")
    where = f"{source} step {name!r}"
    exit_code = _opt_int(obj, "exit_code", where, minimum=None)
    if exit_code is None:
        raise _bad(where, "a nightly step needs an integer `exit_code`")
    if (status == "PASS") != (exit_code == 0):
        raise _bad(where, f"status {status!r} contradicts exit code {exit_code}", "INCONSISTENT_RECEIPT")
    step = Step(
        step_id=name,
        kind="nightly",
        source=source,
        command=_opt_str(obj, "command", where),
        returncode=exit_code,
        ok=status == "PASS",
        status=status,
    )
    step_shas: list[str] = []
    for sha_key in ("commit_sha", "git_sha", "unstable_commit_sha"):
        if sha_key in obj:
            sha = _receipt_sha(obj.get(sha_key), where, sha_key)
            if sha is not None:
                step_shas.append(sha)
    return step, step_shas


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
            _validate_canonical_top_metadata(obj, source)
            if not isinstance(obj["steps"], list) or not obj["steps"]:
                raise _bad(source, "`steps` must be a non-empty array")
            if forced_id is not None:
                raise _bad(source, "a STEP_ID= prefix cannot name a multi-step bundle")
            for entry in obj["steps"]:
                step, sha = _canonical_step(entry, source, allow_schema=False)
                steps.append(step)
                shas += [sha] if sha else []
        else:
            step, _ = _canonical_step(obj, source, allow_schema=True)
            step.step_id = single(step.step_id)
            steps.append(step)
        shas += [top_sha] if top_sha else []
    elif bundle_only:
        raise _bad(source, f"--receipt-bundle needs a {RECEIPT_SCHEMA} receipt")
    elif not stdout_form and {"ok", "fatal_error", "total", "killed", "survived", "errors", "results"} <= set(obj):
        step, sha = _guard_mutation_step(obj, single("guard_mutation"), source)
        steps.append(step)
        shas += [sha] if sha else []
    elif not stdout_form and isinstance(obj.get("pillar_2_correctness_and_correspondence"), dict):
        p2: dict[str, object] = obj["pillar_2_correctness_and_correspondence"]  # type: ignore[assignment]
        entries = p2.get("steps")
        if not isinstance(entries, list) or not entries:
            raise _bad(source, "nightly dashboard has no `steps`")
        if forced_id is not None:
            raise _bad(source, "a STEP_ID= prefix cannot name a multi-step dashboard")
        loaded_steps: list[Step] = []
        for entry in entries:
            step, entry_shas = _nightly_step(entry, source)
            loaded_steps.append(step)
            shas += entry_shas
        steps_total = _opt_int(p2, "steps_total", source)
        steps_passed = _opt_int(p2, "steps_passed", source)
        steps_failed = _opt_int(p2, "steps_failed", source)
        actual_passed = sum(1 for s in loaded_steps if s.status == "PASS")
        actual_failed = len(loaded_steps) - actual_passed
        if steps_total is not None and steps_total != len(loaded_steps):
            raise _bad(source, f"`steps_total` ({steps_total}) contradicts {len(loaded_steps)} steps", "INCONSISTENT_RECEIPT")
        if steps_passed is not None and steps_passed != actual_passed:
            raise _bad(source, f"`steps_passed` ({steps_passed}) contradicts {actual_passed} passing steps", "INCONSISTENT_RECEIPT")
        if steps_failed is not None and steps_failed != actual_failed:
            raise _bad(source, f"`steps_failed` ({steps_failed}) contradicts {actual_failed} failing steps", "INCONSISTENT_RECEIPT")
        overall = _opt_str(p2, "overall_status", source, allow_empty=False)
        top_overall = _opt_str(obj, "overall_status", source, allow_empty=False)
        if (overall == "PASS" or top_overall == "PASS") and actual_failed > 0:
            raise _bad(source, "`overall_status` is PASS but a nightly step failed", "INCONSISTENT_RECEIPT")
        if (
            (overall is not None and overall != "PASS")
            or (top_overall is not None and top_overall != "PASS")
        ) and actual_failed == 0:
            raise _bad(
                source,
                "`overall_status` is not PASS despite all listed nightly steps passing",
                "INCONSISTENT_RECEIPT",
            )
        steps += loaded_steps
        for key in ("unstable_commit_sha", "git_sha", "commit_sha"):
            if key in obj:
                sha = _receipt_sha(obj.get(key), source, key)
                if sha is not None:
                    shas.append(sha)
    elif not stdout_form and {"name", "status", "exit_code"} <= set(obj):
        step, entry_shas = _nightly_step(obj, source)
        step.step_id = single(step.step_id)
        steps.append(step)
        shas += entry_shas
    elif stdout_form or set(obj) & {"kernelDeclarations", "claimTheoremsChecked", "replayedDeclarations",
                                    "sourceSha256", "rustcCapture"}:
        step, sha = _check_trusted_step(obj, single("check_trusted"), source, stdout_form=stdout_form)
        steps.append(step)
        shas += [sha] if sha else []
    else:
        raise _bad(source, "unrecognized receipt format")
    return steps, shas


# ---------------------------------------------------------------------------
# Claim extraction
# ---------------------------------------------------------------------------

_NUM = r"(?<![\w.,/=])[`*_]*((?:>=|<=|!=|==|[~≈<>≥≤≠+\-])[`*_]*\s*)?[`*_]*([0-9]+(?:[,._][0-9]+)*[+~]?)[`*_]*"
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
    r"(?i)(?<![\w-])[*_]*(passed|failed|failure|killed|survived|survivor|errors?|theorems?|sorry|total)"
    r"(?:_count)?[*_]*\s*(?:==|[=:])\s*[`*_]*((?:>=|<=|!=|[~≈<>≥≤≠+\-])[`*_]*\s*)?[`*_]*([0-9]+(?:[,._][0-9]+)*[+~]?)"
)
_KV_METRIC_ALIASES: dict[str, str] = {
    "failure": "failed",
    "survivor": "survived",
    "error": "errors",
    "theorem": "theorems",
}
_FRACTION_RE = re.compile(
    _NUM
    + r"\s*(?:/|\bof\b)\s*[`*_]*([0-9]+(?:[,._][0-9]+)*[+~]?)[`*_]*\s+"
    + r"(?:(?:unit\s+|doc\s+|new\s+|proved\s+|proven\s+|kernel-checked\s+|checked\s+|verified\s+|Lean\s+|total\s+)?"
    + r"(?:mutants?|guards?|tests?|checks?)\s+)?"
    + r"(killed|passed|passing|pass|failed|failing|failures?|survived|surviving|survivors?|theorems?)\b",
    re.I,
)
_KILL_RATE_RES: tuple[re.Pattern[str], ...] = (
    re.compile(
        r"(?i)(?<![\w.,/=])[`*_]*((?:>=|<=|!=|==|[~≈<>≥≤≠+\-])[`*_]*\s*)?[`*_]*([0-9]+(?:[,._][0-9]+)*[+~]?)[`*_]*\s*%([+~]?)\s+"
        r"(?:of\s+)?(?:(?:mutants?|guards?)\s+)?(?:kill[ -]rate|killed|mutation\s+score)\b"
    ),
    re.compile(
        r"(?i)\b[*_]*kill[ _-]rate(?:_pct)?[*_]*\s*(?:==|[=:]|of|is)?\s*[`*_]*((?:>=|<=|!=|[~≈<>≥≤≠+\-])[`*_]*\s*)?[`*_]*([0-9]+(?:[,._][0-9]+)*[+~]?)[`*_]*\s*(?:%([+~]?))?"
    ),
)
_ZERO_WORD_RES: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "failed",
        re.compile(
            r"(?i)\b(?:no|zero)\s+(?:(?:unit\s+|doc\s+)?tests?\s+)?"
            r"(?:failures?|failed(?:\s+tests?)?|failing(?:\s+tests?)?)\b"
            r"|\b(?:no|zero)\s+(?:unit\s+|doc\s+)?tests?\s+failed\b"
        ),
    ),
    (
        "survived",
        re.compile(
            r"(?i)\b(?:no|zero)\s+(?:(?:mutants?|guards?)\s+)?"
            r"surviv(?:ors?|ed|ing(?:\s+(?:mutants?|guards?))?)\b"
        ),
    ),
    ("sorry", re.compile(r"(?i)\b(?:no|zero|without)\s+`?(?:sorr(?:y|ies)|sorryAx)\b`?|\bsorry-free\b")),
    ("errors", re.compile(r"(?i)\b(?:no|zero|without)\s+errors?\b")),
)
_BAD_KV_RE = re.compile(
    r"(?i)(?<![\w-])[*_]*(?:"
    r"(?:(?:passed|failed|failure|killed|survived|survivor|errors?|theorems?|sorry|total)_count|kill[ _-]rate_pct)"
    r"[*_]*\s*(?:==|[=:])\s*[`*_]*([^\s`,;)|*]+)"
    r"|(?:passed|failed|failure|killed|survived|survivor|errors?|theorems?|sorry|total|kill[ _-]rate)"
    r"[*_]*\s*(?:==|=(?!=))\s*[`*_]*([^\s`,;)|*]+)"
    r"|(?:passed|failed|failure|killed|survived|survivor|errors?|theorems?|sorry|total|kill[ _-]rate)"
    r"[*_]*\s*:\s*[`*_]*(?:unknown|tbd|n/a|na|nan|inf(?:inity)?|null|"
    r"(?:approx\.?|approximately|roughly|around|about|over|under|above|below|"
    r"at\s+(?:least|most)|(?:more|less|fewer|greater)\s+than)\s+[0-9]+|"
    r"[~≈<>≥≤≠+\-][0-9]+|(?:>=|<=|!=)\s*[0-9]+|[0-9]+\.[0-9]+)\b"
    r"|(?:passed|failed|failure|killed|survived|survivor|errors?|theorems?|sorry|total|kill[ _-]rate)(?:_count|_pct)?"
    r"[*_]*\s*(?:>=|<=|!=|≠|>|<|≥|≤|≈)\s*[`*_]*[^\s`,;)|*]+"
    r"|(?:passed|failed|failure|killed|survived|survivor|errors?|theorems?|sorry|total|kill[ _-]rate)(?:_count|_pct)?"
    r"[*_]*\s*~(?!~)\s*[`*_]*[0-9][^\s`,;)|*]*"
    r"|ok[*_]*\s*(?:==|!=|≠|=(?!=))\s*[`*_]*(?!(?:true|false)\b)[^\s`,;)|*]+"
    r"|ok[*_]*\s*:\s*[`*_]*(?:unknown|tbd|n/a|na|nan|null|none|pending|skipped)\b"
    r"|(?:status|result|verdict|outcome)[*_]*\s*(?:==|!=|≠|[=:])\s*[`*_]*(?:unknown|tbd|n/a|na|null|none|pending|skipped)\b)"
)
_RC_NEQ_RE = re.compile(
    r"(?i)(?<![\w-])[*_]*(?:rc|exit[ _-]?code|exit[ _-]?status|return[ _]?code)[*_]*\s*(?:!=|≠)\s*[`*_]*([^\s`,;)|*]+)"
)
_RC_ASSIGN_RE = re.compile(
    r"(?i)(?<![\w-])[*_]*(?:rc|exit[ _-]?code|exit[ _-]?status|return[ _]?code)[*_]*\s*(?:==|[=:])\s*[`*_]*([^\s`,;)|*]+)"
)
_RC_PROSE_RE = re.compile(
    r"(?i)(?<![\w-])(?:exit(?:ed)?(?:\s+with)?(?:\s+code|\s+status)?|rc|return\s+code)\s+"
    r"(?:is\s+|was\s+|of\s+)?`?(-?[0-9]+)\b"
)
_STATUS_RE = re.compile(
    r"(?i)(?<![\w-])[*_]*(?:status|result|verdict|outcome)[*_]*\s*(==|!=|≠|[=:])\s*[`*_]*([A-Za-z]+)"
)
_OK_RE = re.compile(r"(?i)(?<![\w-])[*_]*ok[*_]*\s*(==|!=|≠|[=:])\s*[`*_]*(true|false)\b")
_VERDICT_TOKEN_RE = re.compile(r"(?<![\w/.-])(PASS(?:ED)?|FAIL(?:ED)?|OK|✅|❌)(?![\w/-]|\.\w|\()")
_SCOPED_VERDICT_RE = re.compile(
    r"(?i)(?:(?<=\|)|(?<=:))\s*[`*_]*\b(?P<neg>(?:not|never|did\s+not|didn't|does\s+not|doesn't|failed\s+to)\s+)?"
    r"(?P<word>pass(?:ed|ing)?|green|ok|succeed(?:ed)|success|fail(?:ed|ing|ure)?|red|error|timeout)\b[`*_]*\s*"
    r"(?=\||[.;,()]|$)"
)
_ALL_PASS_RE = re.compile(
    r"(?i)\ball\s+(?:[\w'-]+\s+){0,3}(?:pass(?:ed|es)?|green|succeed(?:ed)?)\b"
)
_NEGATION_WORDS: frozenset[str] = frozenset({
    "not", "never", "no", "without", "neither", "nor", "fail", "failed", "failing",
    "cannot", "can't", "cant", "didn't", "didnt", "doesn't", "doesnt",
    "don't", "dont", "won't", "wont", "unable", "unverified", "non",
})
_PRECEDING_NEG_RE = re.compile(
    r"(?i)(?:\b(?:not|never|no|non|didn't|did\s+not|does\s+not|doesn't|failed\s+to|cannot|can't)\s*[-]?)$"
)
_APPROX_OR_INEQ_PREFIX_RE = re.compile(
    r"(?i)(?:\b(?:approx\.?|approximately|roughly|around|about|nearly|almost|"
    r"over|under|above|below|up\s+to|at\s+least|at\s+most|"
    r"more\s+than|less\s+than|fewer\s+than|greater\s+than)\s+)$"
)
_COMPARATIVE_PREFIX_RE = re.compile(
    r"(?i)(?:\b(?:vs\.?|versus|after|before|replacing|unlike|than|from|instead\s+of|"
    r"compared\s+(?:to|with|against)|against|see|mirrors|like|same\s+as|matching)\s+)$"
)
_PASS_WORDS: frozenset[str] = frozenset(
    {"PASS", "PASSED", "PASSING", "OK", "SUCCESS", "SUCCEEDED", "GREEN", "✅"}
)
_FAIL_WORDS: frozenset[str] = frozenset(
    {"FAIL", "FAILED", "FAILING", "FAILURE", "ERROR", "RED", "TIMEOUT", "❌"}
)
_SHA_CLAIM_RE = re.compile(
    r"(?i)(?<![\w/-])[`*_]*(?P<label>(?:(?:base|parent|previous|prior|old|head|target|tip|final|new|current|git)"
    r"[\s_-]+)*(?:commit(?:[\s_-]+(?:sha(?:-?1)?|hash|id))?|sha(?:-?1)?|revision|head|base|parent|target))[`*_]*(?![\w-])"
    r"(?:\s+(?:is|was|at|of)){0,2}[`*_]*\s*(?P<sep>[:=|@]|->|→)?[*_]*\s*(?P<paren>\()?\s*[*_]*(?P<tick>[`'\"]?)(?P<value>[0-9A-Za-z/_.?<>-]+)"
)
_EXPLICIT_SHA_LABEL_RE = re.compile(r"(?i)\b(?:sha(?:-?1)?|hash|revision|commit[\s_-]+id)\b")
_STRICT_SHA_LABEL_RE = re.compile(
    r"(?i)\b(?:sha(?:-?1)?|(?:commit|git|head|base)[\s_-]+hash|commit[\s_-]+id|revision)\b"
)
_TABLE_NON_SHA_HEADERS: frozenset[str] = frozenset({
    "status", "result", "verdict", "outcome", "step", "steps", "notes", "note",
    "details", "detail", "check", "checks", "value", "description", "summary",
})
_TABLE_HEADER_CELL0_WORDS: frozenset[str] = frozenset({
    "step", "steps", "check", "checks", "gate", "gates", "target", "command",
    "commands", "test", "tests", "item", "name",
})
_BASE_ROLE_RE = re.compile(r"(?i)(?:^|[\s_-])(?:base|parent|previous|prior|old)(?:$|[\s_-])")
_SHA_PLACEHOLDERS: frozenset[str] = frozenset({
    "unknown", "none", "n/a", "na", "tbd", "null", "dirty", "pending", "uncommitted", "wip", "?", "??", "???",
})
_AXIOM_PREFIX_OPT = r"(?:[*_]*axioms?(?:\s+used|\s+set|\s+closure)?[*_]*\s*[=:]\s*)?"
_STANDARD_AXIOMS_RE = re.compile(
    r"(?i)" + _AXIOM_PREFIX_OPT
    + r"(?:\b(?:only\s+)?(?:the\s+)?(?:three\s+)?standard\s+(?:kernel\s+|Lean\s+)?axioms?(?:\s+only)?\b"
    r"|\b(?:no|zero)\s+(?:non-?standard|extra|additional|unauthorized|custom)\s+axioms?\b)"
)
_NO_AXIOMS_RE = re.compile(
    r"(?i)" + _AXIOM_PREFIX_OPT + r"(?:\b(?:no|zero)\s+axioms?\b|\baxiom-free\b)"
)
_AXIOM_LIST_RE = re.compile(
    r"(?i)(?<![\w-])[*_]*axioms?(?:\s+used|\s+set|\s+closure)?[*_]*\s*[=:]\s*([^;|\n]+)"
)
_EXPLICIT_STEP_RE = re.compile(r"(?i)(?<![\w-])[*_]*step(?:[ _-]?id)?[*_]*\s*[=:]\s*[`*_]*([A-Za-z0-9][\w.:/-]*)")
_LEADING_LABEL_RE = re.compile(
    r"^\s*(?:[-*+]|\d+[.)])?\s*(?:`([^`\n]+)`|\*\*([^*\n`]+)\*\*|([A-Za-z0-9][A-Za-z0-9_.-]*))(?:\s*\([^)\n]*\))?\s*:"
)
_LABEL_ATOM_SRC = r"(?:`[^`\n]+`|\*\*[^*\n`]+\*\*|[A-Za-z0-9][A-Za-z0-9_.-]*)"
_COMPOUND_LEADING_LABELS_RE = re.compile(
    r"^\s*(?:[-*+]|\d+[.)])?\s*(?P<head>"
    + _LABEL_ATOM_SRC
    + r"(?:\s*(?:,|&|\+|/|\band\b)\s*"
    + _LABEL_ATOM_SRC
    + r")+)(?:\s*\([^)\n]*\))?\s*:"
)
_TABLE_CELL_SINGLE_LABEL_RE = re.compile(
    r"^\s*(?:`([^`\n]+)`|\*\*([^*\n`]+)\*\*|([A-Za-z0-9.~/][A-Za-z0-9_./~-]*))(?:\s*\([^)\n]*\))?\s*$"
)
_TABLE_CELL_COMPOUND_LABELS_RE = re.compile(
    r"^\s*(?P<head>"
    + _LABEL_ATOM_SRC
    + r"(?:\s*(?:,|&|\+|/|\band\b)\s*"
    + _LABEL_ATOM_SRC
    + r")+)(?:\s*\([^)\n]*\))?\s*$"
)
_LABEL_ITEM_RE = re.compile(r"`([^`\n]+)`|\*\*([^*\n`]+)\*\*|([A-Za-z0-9][A-Za-z0-9_.-]*)")
_HEADING_PREFIX_RE = re.compile(r"^\s*#{1,6}\s+")
_HEADING_SINGLE_LABEL_RE = re.compile(
    r"(?i)^(?:`([^`\n]+)`|\*\*([^*\n`]+)\*\*|([A-Za-z0-9][A-Za-z0-9.-]*_[A-Za-z0-9_.-]*))"
    r"(?:\s+(?:verification|results?|summary|report|audit|checks?|gates?|status|output|receipts?))*"
    r"(?:\s*\([^)\n]*\))?\s*$"
)
_HEADING_CODE_STEP_RE = re.compile(r"^\s*#{1,6}\s+`([^`\n]+)`\s*$")
_HEADING_BARE_STEP_RE = re.compile(r"^\s*#{1,6}\s+(?:\*\*)?([A-Za-z0-9][A-Za-z0-9.-]*_[A-Za-z0-9_.-]*)(?:\*\*)?\s*$")
_LIST_ITEM_RE = re.compile(r"^\s*(?:[-*+]|\d+[.)])\s+")
_COMMAND_HEAD_RE = re.compile(
    r"(?:~?/|(?:\.{1,2}/)+|(?:python3?|cargo|lake|lean|anneal-lean-run|bash|sh|git|pytest|make|rg|"
    r"env|timeout|time|nice|nohup|rustup|elan)\b)"
)
_ANNEAL_WRAPPER_RE = re.compile(
    r"(?:[\w./~-]+/)?anneal-lean-run(?:\s+--[A-Za-z0-9_-]+(?:=[^\s;&|`$<>]+|\s+[A-Za-z0-9_./:-]+)?)*"
)
_NON_STEP_LABELS: frozenset[str] = frozenset({
    "commit", "commit sha", "commit_sha", "git sha", "git_sha", "sha", "sha1", "sha-1", "revision",
    "head", "head sha", "head_sha", "base", "base sha", "base_sha", "parent",
    "previous", "prior", "old", "target", "tip", "status", "result", "verdict",
    "outcome", "axioms", "axioms used", "axioms set", "axioms closure", "axiom",
    "summary", "note", "notes", "receipt", "receipts", "overall", "total",
    "kill rate", "kill_rate", "passed", "failed", "killed", "survived", "errors",
    "theorems", "sorry", "rc", "exit code", "exit_code", "ok", "step", "step_id",
    "verification", "gate", "gates", "checks", "tests", "all", "command", "commands",
    "historical", "previously", "superseded", "obsolete",
})
_FENCE_OPEN_RE = re.compile(r"^\s{0,3}(`{3,}|~{3,})(.*)$")
_HISTORICAL_RE = re.compile(
    r"(?i)^(?:[-*+>\s]|[0-9]+[.)])*[\[(*_]*(?:historical|previously|superseded|obsolete)[\])*_]*\s*[:\-–]"
)
_IGNORE_BEGIN = "<!-- claim-guard: ignore-begin -->"
_IGNORE_END = "<!-- claim-guard: ignore-end -->"
_INVISIBLE_RE = re.compile("[\u200b-\u200f\u2060-\u2064\u206a-\u206f\ufeff\u00ad\u034f\u061c\u180e\U000e0000-\U000e007f]")
_LINE_SEP_CONTROL_RE = re.compile("[\u0085\u2028\u2029]")
_CONTROL_RE = re.compile("[\x00-\x08\x0b\x0c\x0e-\x1f\x7f\u0085\u2028\u2029\u202a-\u202e\u2066-\u2069]")
_HAS_DIGIT_RE = re.compile(r"[0-9]")
_HAS_KV_OP_RE = re.compile(r"[=:<>≤≥≠~≈]")
_HAS_SHA_WORD_RE = re.compile(r"(?i)commit|sha|revision|head|base|parent|target")
_BQ_ONE_RE = re.compile(r"^\s{0,3}>\s?")
_INEQ_GT_TAIL_RE = re.compile(r"^\s*(?:=|[~≈]|[+\-]?\s*[*_`]*[0-9])")
_NUM_LIST_LINE_RE = re.compile(r"^\s*[0-9]+[.)]\s+")
_TABLE_SEP_CELL_RE = re.compile(r"[-:\s]+")


def _strip_blockquote_prefix(line: str, max_depth: int | None = None) -> tuple[str, int]:
    """Strip CommonMark `>` blockquote prefixes unless `>` starts a numeric inequality."""
    cur = line
    depth = 0
    while max_depth is None or depth < max_depth:
        m = _BQ_ONE_RE.match(cur)
        if m is None:
            break
        rem = cur[m.end() :]
        if max_depth is None and _INEQ_GT_TAIL_RE.match(rem) and not _NUM_LIST_LINE_RE.match(rem):
            break
        cur = rem
        depth += 1
    return cur, depth


def _inline_code_spans(line: str) -> list[tuple[int, int, str]]:
    """CommonMark matched inline code spans `(open_idx, close_end, inner)` on `line`."""
    spans: list[tuple[int, int, str]] = []
    n = len(line)
    i = 0
    while i < n:
        if line[i] != "`":
            i += 1
            continue
        run_end = i
        while run_end < n and line[run_end] == "`":
            run_end += 1
        tick_len = run_end - i
        j = run_end
        closed_at = -1
        while j < n:
            if line[j] != "`":
                j += 1
                continue
            k = j
            while k < n and line[k] == "`":
                k += 1
            if k - j == tick_len:
                closed_at = j
                break
            j = k
        if closed_at != -1:
            inner = line[run_end:closed_at]
            if len(inner) >= 2 and inner[0] == " " and inner[-1] == " " and inner.strip(" "):
                inner = inner[1:-1]
            spans.append((i, closed_at + tick_len, inner))
            i = closed_at + tick_len
        else:
            i = run_end
    return spans


def _in_spans(idx: int, spans: Sequence[tuple[int, int, str]]) -> bool:
    return any(lo <= idx < hi for lo, hi, _ in spans)


def _strip_strikethrough_outside_code(line: str) -> str:
    """Replace matched `~~...~~` spans (strictly 2 tildes, per GFM) outside code spans with spaces."""
    if "~~" not in line:
        return line
    code_spans = _inline_code_spans(line)
    chars = list(line)
    n = len(line)
    i = 0
    open_at = -1
    while i < n:
        if line[i] == "~" and not _in_spans(i, code_spans):
            j = i
            while j < n and line[j] == "~":
                j += 1
            if j - i == 2:
                if open_at == -1:
                    open_at = i
                else:
                    for pos in range(open_at, j):
                        chars[pos] = " "
                    open_at = -1
            i = j
            continue
        i += 1
    return "".join(chars)


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
        """The one step whose command is `span`, allowing an `anneal-lean-run ... -- ` wrapper."""
        hits: set[str] = set()
        for command, step_ids in self.commands.items():
            if span == command:
                hits |= step_ids
            elif command.endswith(" -- " + span):
                prefix = command[: -len(" -- " + span)]
                if _ANNEAL_WRAPPER_RE.fullmatch(prefix):
                    hits |= step_ids
            elif span.endswith(" -- " + command):
                prefix = span[: -len(" -- " + command)]
                if _ANNEAL_WRAPPER_RE.fullmatch(prefix):
                    hits |= step_ids
        return next(iter(hits)) if len(hits) == 1 else None


def _is_candidate_unknown_step_label(label: str) -> bool:
    """Whether `label` looks like an unrecognized step or script name rather than metadata."""
    norm = " ".join(label.strip().split())
    if not norm or norm.lower() in _NON_STEP_LABELS:
        return False
    if any(ch in norm for ch in ("=", ":", "%", "|", ";")):
        return False
    if _SHA_RE.fullmatch(norm) or norm.isdigit():
        return False
    return bool(re.fullmatch(r"[A-Za-z0-9.~/][A-Za-z0-9_./~+@ -]*", norm))


def _table_cell_spans(line: str) -> list[tuple[int, int]]:
    """`(lo, hi)` character spans of Markdown table cells, ignoring `|` inside inline code."""
    code_spans = _inline_code_spans(line)
    pipes = [idx for idx, ch in enumerate(line) if ch == "|" and not _in_spans(idx, code_spans)]
    if len(pipes) < 2:
        return []
    return [(pipes[i] + 1, pipes[i + 1]) for i in range(len(pipes) - 1)]


def _clause_spans(line: str) -> list[tuple[int, int]]:
    """`(lo, hi)` spans split on `;` outside inline code spans."""
    code_spans = _inline_code_spans(line)
    spans: list[tuple[int, int]] = []
    start = 0
    for idx, ch in enumerate(line):
        if ch == ";" and not _in_spans(idx, code_spans):
            spans.append((start, idx))
            start = idx + 1
    spans.append((start, len(line)))
    return spans


def _line_refs(
    line: str, known: _KnownSteps, in_fence: bool
) -> list[tuple[int, str | None, str, bool, bool]]:
    """`(position, step id or None, name, explicit, secondary)` for every step the line names."""
    refs: list[tuple[int, str | None, str, bool, bool]] = []
    taken: list[tuple[int, int]] = []

    def overlaps(lo: int, hi: int) -> bool:
        return any(a < hi and lo < b for a, b in taken)

    def add(
        m_start: int, m_end: int, step_id: str | None, name: str, explicit: bool, secondary: bool = False
    ) -> None:
        refs.append((m_start, step_id, name, explicit, secondary))
        taken.append((m_start, m_end))

    for m in _EXPLICIT_STEP_RE.finditer(line):
        name = m.group(1).rstrip(".,;:*_")
        add(m.start(), m.end(), name if name in known.ids else None, name, True)
    if in_fence:
        stripped = line.strip()
        shell = stripped.startswith("$ ")
        candidate = " ".join((stripped[2:] if shell else stripped).split())
        step_id = known.by_command(candidate)
        if step_id is not None or shell or _COMMAND_HEAD_RE.match(candidate):
            add(0, len(line), step_id, candidate, False)
    is_table = not in_fence and line.lstrip().startswith("|")
    table_cells = _table_cell_spans(line) if is_table else []
    m_lead = _LEADING_LABEL_RE.match(line) if not in_fence and not is_table else None
    lead_paren_span: tuple[int, int] | None = None

    def add_lead_item(
        grp: int, raw_text: str, span_lo: int, span_hi: int, *, allow_slash_bare: bool = False
    ) -> bool:
        if overlaps(span_lo, span_hi):
            return False
        lead_label = " ".join(raw_text.split())
        if lead_label in known.ids:
            add(span_lo, span_hi, lead_label, lead_label, True)
            return True
        cmd_step = known.by_command(lead_label) if grp == 1 else None
        if cmd_step is not None:
            add(span_lo, span_hi, cmd_step, lead_label, False)
            return True
        if is_table and lead_label.upper() in (_PASS_WORDS | _FAIL_WORDS):
            return False
        if grp in (1, 2):
            if _is_candidate_unknown_step_label(lead_label):
                is_step_id = "/" not in lead_label and not _COMMAND_HEAD_RE.match(lead_label)
                add(span_lo, span_hi, None, lead_label, is_step_id)
                return True
            if grp == 1 and lead_label and lead_label.lower() not in _NON_STEP_LABELS and " " in lead_label:
                add(span_lo, span_hi, None, lead_label, False)
                return True
        elif grp == 3 and (
            "_" in lead_label or "-" in lead_label or (allow_slash_bare and "/" in lead_label)
        ) and _is_candidate_unknown_step_label(lead_label):
            is_step_id = "/" not in lead_label and not _COMMAND_HEAD_RE.match(lead_label)
            add(span_lo, span_hi, None, lead_label, is_step_id)
            return True
        return False

    if m_lead is not None:
        grp = 1 if m_lead.group(1) is not None else (2 if m_lead.group(2) is not None else 3)
        lead_added = add_lead_item(grp, m_lead.group(grp), m_lead.start(grp), m_lead.end(grp))
        if lead_added and m_lead.end() > m_lead.end(grp):
            lead_paren_span = (m_lead.end(grp), m_lead.end())
    elif not in_fence and not is_table:
        m_hpre = _HEADING_PREFIX_RE.match(line)
        if m_hpre is not None:
            h_lo = m_hpre.end()
            h_body = line[h_lo:]
            m_hsingle = _HEADING_SINGLE_LABEL_RE.match(h_body)
            if m_hsingle is not None:
                grp = 1 if m_hsingle.group(1) is not None else (2 if m_hsingle.group(2) is not None else 3)
                h_added = add_lead_item(
                    grp,
                    m_hsingle.group(grp),
                    h_lo + m_hsingle.start(grp),
                    h_lo + m_hsingle.end(grp),
                    allow_slash_bare=True,
                )
                if h_added and m_hsingle.end() > m_hsingle.end(grp):
                    lead_paren_span = (h_lo + m_hsingle.end(grp), h_lo + m_hsingle.end())
            else:
                m_hcomp = _TABLE_CELL_COMPOUND_LABELS_RE.match(h_body)
                if m_hcomp is not None:
                    base_off = h_lo + m_hcomp.start("head")
                    h_comp_added = False
                    for m_item in _LABEL_ITEM_RE.finditer(m_hcomp.group("head")):
                        igrp = 1 if m_item.group(1) is not None else (2 if m_item.group(2) is not None else 3)
                        tok_text = m_item.group(igrp)
                        if igrp == 3 and tok_text.lower() == "and":
                            continue
                        if add_lead_item(
                            igrp,
                            tok_text,
                            base_off + m_item.start(igrp),
                            base_off + m_item.end(igrp),
                            allow_slash_bare=True,
                        ):
                            h_comp_added = True
                    if h_comp_added and m_hcomp.end() > m_hcomp.end("head"):
                        lead_paren_span = (h_lo + m_hcomp.end("head"), h_lo + m_hcomp.end())
        else:
            m_comp = _COMPOUND_LEADING_LABELS_RE.match(line)
            if m_comp is not None:
                base_off = m_comp.start("head")
                comp_added = False
                for m_item in _LABEL_ITEM_RE.finditer(m_comp.group("head")):
                    igrp = 1 if m_item.group(1) is not None else (2 if m_item.group(2) is not None else 3)
                    tok_text = m_item.group(igrp)
                    if igrp == 3 and tok_text.lower() == "and":
                        continue
                    if add_lead_item(igrp, tok_text, base_off + m_item.start(igrp), base_off + m_item.end(igrp)):
                        comp_added = True
                if comp_added and m_comp.end() > m_comp.end("head"):
                    lead_paren_span = (m_comp.end("head"), m_comp.end())
    elif is_table and table_cells:
        c0_lo, c0_hi = table_cells[0]
        cell0 = line[c0_lo:c0_hi]
        if cell0.strip() and not re.fullmatch(r"[-:\s]+", cell0.strip()):
            m_c0 = _TABLE_CELL_SINGLE_LABEL_RE.match(cell0)
            if m_c0 is not None:
                grp = 1 if m_c0.group(1) is not None else (2 if m_c0.group(2) is not None else 3)
                c0_added = add_lead_item(
                    grp,
                    m_c0.group(grp),
                    c0_lo + m_c0.start(grp),
                    c0_lo + m_c0.end(grp),
                    allow_slash_bare=True,
                )
                if c0_added and m_c0.end() > m_c0.end(grp):
                    lead_paren_span = (c0_lo + m_c0.end(grp), c0_lo + m_c0.end())
            else:
                m_c0_comp = _TABLE_CELL_COMPOUND_LABELS_RE.match(cell0)
                if m_c0_comp is not None:
                    base_off = c0_lo + m_c0_comp.start("head")
                    c0_comp_added = False
                    for m_item in _LABEL_ITEM_RE.finditer(m_c0_comp.group("head")):
                        igrp = 1 if m_item.group(1) is not None else (2 if m_item.group(2) is not None else 3)
                        tok_text = m_item.group(igrp)
                        if igrp == 3 and tok_text.lower() == "and":
                            continue
                        if add_lead_item(
                            igrp,
                            tok_text,
                            base_off + m_item.start(igrp),
                            base_off + m_item.end(igrp),
                            allow_slash_bare=True,
                        ):
                            c0_comp_added = True
                    if c0_comp_added and m_c0_comp.end() > m_c0_comp.end("head"):
                        lead_paren_span = (c0_lo + m_c0_comp.end("head"), c0_lo + m_c0_comp.end())

    def is_secondary(lo: int, hi: int) -> bool:
        if lead_paren_span is not None and lead_paren_span[0] <= lo and hi <= lead_paren_span[1]:
            return True
        after_ref = line[hi:].lstrip(" \t*_")
        if after_ref.startswith(":"):
            return False
        if _COMPARATIVE_PREFIX_RE.search(line[:lo]):
            return True
        if is_table:
            for idx, (clo, chi) in enumerate(table_cells):
                if idx > 0 and clo <= lo and hi <= chi:
                    before_in_cell = line[clo:lo].strip()
                    if before_in_cell and not before_in_cell.endswith((",", ";", ":")):
                        return True
        return False

    if not in_fence:
        for lo, hi, raw_inner in _inline_code_spans(line):
            if overlaps(lo, hi):
                continue
            span = " ".join(raw_inner.split())
            step_id = span if span in known.ids else known.by_command(span)
            is_cmd = _COMMAND_HEAD_RE.match(span) is not None or " -- " in span
            if step_id is not None or is_cmd:
                sec = False if (step_id is None and is_cmd) else is_secondary(lo, hi)
                add(lo, hi, step_id, span, False, secondary=sec)
    for step_id, pattern in known.id_res:
        for m in pattern.finditer(line):
            if not overlaps(m.start(), m.end()):
                add(m.start(), m.end(), step_id, step_id, False, secondary=is_secondary(m.start(), m.end()))
    if not in_fence:
        m_head = _HEADING_CODE_STEP_RE.match(line)
        if m_head is not None and not overlaps(m_head.start(1), m_head.end(1)):
            label = " ".join(m_head.group(1).split())
            if _is_candidate_unknown_step_label(label):
                is_step_id = "/" not in label and not _COMMAND_HEAD_RE.match(label)
                add(m_head.start(1), m_head.end(1), None, label, is_step_id)
        m_bare_head = _HEADING_BARE_STEP_RE.match(line)
        if m_bare_head is not None and not overlaps(m_bare_head.start(1), m_bare_head.end(1)):
            label = m_bare_head.group(1)
            if _is_candidate_unknown_step_label(label):
                add(m_bare_head.start(1), m_bare_head.end(1), None, label, True)
        if is_table:
            for idx, (lo, hi) in enumerate(table_cells):
                if overlaps(lo, hi):
                    continue
                cell = line[lo:hi].strip()
                if not cell or re.fullmatch(r"[-:\s]+", cell):
                    continue
                m_cell = re.fullmatch(r"(?:\*\*)?`([^`\n]+)`(?:\*\*)?", cell)
                if m_cell is not None:
                    label = " ".join(m_cell.group(1).split())
                    if _is_candidate_unknown_step_label(label) and label.upper() not in (_PASS_WORDS | _FAIL_WORDS):
                        is_step_id = "/" not in label and not _COMMAND_HEAD_RE.match(label)
                        add(lo, hi, None, label, is_step_id)
                elif idx == 0 and re.fullmatch(r"(?:\*\*)?([A-Za-z0-9.~/][A-Za-z0-9_./~-]*)(?:\*\*)?", cell):
                    plain = cell.strip("*")
                    if (
                        ("_" in plain or "-" in plain or "/" in plain)
                        and _is_candidate_unknown_step_label(plain)
                        and plain.upper() not in (_PASS_WORDS | _FAIL_WORDS)
                    ):
                        is_step_id = "/" not in plain and not _COMMAND_HEAD_RE.match(plain)
                        add(lo, hi, None, plain, is_step_id)
    refs.sort(key=lambda ref: ref[0])
    return refs


def _classify_sha(value: str, explicit: bool, *, strict_label: bool = False) -> tuple[str, str]:
    """`("valid", sha)`, `("ignore", "")`, or a violation code with its reason."""
    quoted = value[:1] in ("`", '"', "'")
    token = value.strip("`'\"*_").rstrip(".,;:)")
    if _SHA_RE.fullmatch(token):
        if set(token) == {"0"}:
            return "INVALID_COMMIT_SHA", f"`{token}` is the all-zero SHA"
        if not explicit and not strict_label and not any(ch.isdigit() for ch in token):
            return "ignore", ""
        return "valid", token
    has_digit = any(ch.isdigit() for ch in token)
    if (explicit or strict_label) and (
        token.lower() in _SHA_PLACEHOLDERS
        or re.fullmatch(r"\?+", token)
        or (token.startswith("<") and token.endswith(">") and len(token) > 2)
    ):
        return "INVALID_COMMIT_SHA", f"`{token}` is a placeholder, not a commit SHA"
    # An English word made of hex letters (`added`, `dead`) is prose unless it
    # carries a digit, sits in backticks/quotes, sits under a strict SHA label,
    # or is an explicit 7+ char hex token.
    if re.fullmatch(r"[0-9a-fA-F]+", token) and (
        has_digit or quoted or strict_label or (explicit and len(token) >= 7)
    ):
        if len(token) < 7:
            if strict_label or (explicit and (len(token) >= 4 or quoted)):
                return "AMBIGUOUS_COMMIT_SHA", f"`{token}` is shorter than 7 hex characters"
            return "ignore", ""
        reason = "longer than 40 characters" if len(token) > 40 else "not lowercase hex"
        return "INVALID_COMMIT_SHA", f"`{token}` is {reason}"
    if strict_label and token:
        return "INVALID_COMMIT_SHA", f"`{token}` is not hexadecimal"
    if explicit and has_digit and len(token) >= 7 and re.fullmatch(r"[0-9A-Za-z]+", token):
        return "INVALID_COMMIT_SHA", f"`{token}` is not hexadecimal"
    return "ignore", ""


def _axiom_names(rest: str) -> frozenset[str] | None:
    """Axiom names of an `axioms: ...` list; `None` when the list cannot be read."""
    trimmed = rest.strip()
    if trimmed in ("[]", "{}", "()", "∅"):
        return frozenset()
    names: set[str] = set()
    expect_more = True
    done = False
    chunks = trimmed.split()
    for c_idx, chunk in enumerate(chunks):
        if done:
            break
        if chunk.startswith("(") and names and not expect_more:
            # Parenthetical note after a complete list (`axioms: propext, Quot.sound (standard)`),
            # accepted only when balanced `(...)` reaches the end with no trailing items or axiom names.
            tail = " ".join(chunks[c_idx:])
            if (
                tail.endswith((")", ")."))
                and "," not in tail
                and tail.count("(") == 1
                and tail.count(")") == 1
            ):
                inner_note = tail.rstrip(".")[1:-1]
                if not any(
                    tok.strip("`'\"*_") in NEVER_ALLOWED_AXIOMS or "." in tok.strip("`'\"*_")
                    for tok in inner_note.split()
                ):
                    break
            return None
        parts = chunk.split(",")
        for p_idx, raw in enumerate(parts):
            has_comma = p_idx < len(parts) - 1
            if not raw:
                if has_comma:
                    if not names:
                        return None
                    expect_more = True
                continue
            had_sentence_stop = raw.rstrip("`'\"[](){}*_").endswith((".", ";", ":"))
            token = raw.strip("`'\"[](){}*_").rstrip(".;:")
            if not token:
                if has_comma:
                    expect_more = True
                if had_sentence_stop and names:
                    done = True
                    break
                continue
            if token.lower() in ("and", "+") and not has_comma and not had_sentence_stop:
                if not names:
                    return None
                expect_more = True
                continue
            if token.lower() in ("none", "no", "empty", "∅") and not names and not has_comma:
                return frozenset()
            if not _AXIOM_NAME_RE.fullmatch(token):
                if expect_more:
                    return None
                done = True
                break
            names.add(token)
            expect_more = has_comma
            if had_sentence_stop:
                if has_comma:
                    return None
                done = True
                break
    if expect_more:
        return None
    return frozenset(names) if names else None


def _preceded_by_negation(line: str, pos: int) -> bool:
    return bool(_PRECEDING_NEG_RE.search(line[:pos]))


def _preceded_by_approx_or_ineq(line: str, pos: int) -> bool:
    return bool(_APPROX_OR_INEQ_PREFIX_RE.search(line[:pos]))


def _line_claims(
    line: str, lineno: int, violations: list[Violation], *, has_step_context: bool = False
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

    low = line.lower()
    has_digit = _HAS_DIGIT_RE.search(line) is not None
    has_kv_op = _HAS_KV_OP_RE.search(line) is not None
    has_eq_or_colon = "=" in line or ":" in line

    if _HAS_SHA_WORD_RE.search(line) is not None:
        for m in list(_SHA_CLAIM_RE.finditer(work[0])):
            sep = m.group("sep")
            raw_val = m.group("value")
            clean_val = raw_val.strip("`'\"*_").rstrip(".,;:)")
            if sep == "|":
                is_sep_or_hdr = bool(_TABLE_SEP_CELL_RE.fullmatch(clean_val)) or clean_val.lower() in _TABLE_NON_SHA_HEADERS
                has_sha_word = bool(_EXPLICIT_SHA_LABEL_RE.search(m.group("label")))
                strict_label = not is_sep_or_hdr and bool(_STRICT_SHA_LABEL_RE.search(m.group("label")))
                explicit = not is_sep_or_hdr and (
                    bool(m.group("tick"))
                    or any(ch.isdigit() for ch in clean_val)
                    or clean_val.lower() in _SHA_PLACEHOLDERS
                    or has_sha_word
                )
            else:
                explicit = bool(sep) or bool(m.group("paren")) or bool(m.group("tick"))
                strict_label = explicit and bool(
                    _STRICT_SHA_LABEL_RE.search(m.group("label"))
                )
            verdict, detail = _classify_sha(
                m.group("tick") + raw_val, explicit, strict_label=strict_label
            )
            if verdict == "ignore":
                continue
            take(m)
            if verdict == "valid":
                role = "base" if _BASE_ROLE_RE.search(m.group("label")) else "head"
                found.append((m.start(), "commit_sha", role, detail, m.group(0).strip()))
            else:
                violations.append(Violation(verdict, lineno, None, f"commit SHA claim: {detail}"))
    if has_digit:
        for m in list(_FRACTION_RE.finditer(work[0])):
            inexact_prefix = _preceded_by_approx_or_ineq(line, m.start()) or _preceded_by_negation(line, m.start())
            take(m)
            if inexact_prefix:
                violations.append(
                    Violation("MALFORMED_CLAIM", lineno, None,
                              f"`{m.group(0).strip()}` is negated or approximate, not an exact count")
                )
                continue
            part, whole = count(m, m.group(1) or "", m.group(2)), count(m, "", m.group(3))
            if part is not None and whole is not None:
                raw_metric = m.group(4).lower()
                snippet = m.group(0).strip()
                if whole == 0:
                    violations.append(
                        Violation("MALFORMED_CLAIM", lineno, None,
                                  f"`{snippet}` has a zero denominator")
                    )
                elif part > whole:
                    violations.append(
                        Violation("MALFORMED_CLAIM", lineno, None,
                                  f"`{snippet}` numerator exceeds denominator")
                    )
                elif raw_metric.startswith("pass"):
                    found.append((m.start(), "count", "passed", part, snippet))
                    found.append((m.start(), "count", "tests", whole, snippet))
                elif raw_metric == "killed":
                    found.append((m.start(), "count", "killed", part, snippet))
                    found.append((m.start(), "count", "total", whole, snippet))
                elif raw_metric.startswith("fail"):
                    found.append((m.start(), "count", "failed", part, snippet))
                    found.append((m.start(), "count", "tests", whole, snippet))
                elif raw_metric.startswith("surviv"):
                    found.append((m.start(), "count", "survived", part, snippet))
                    found.append((m.start(), "count", "total", whole, snippet))
                elif raw_metric.startswith("theorem"):
                    found.append((m.start(), "count", "theorems", part, snippet))
        if "kill" in low or "mutation" in low:
            for pattern in _KILL_RATE_RES:
                for m in list(pattern.finditer(work[0])):
                    inexact_prefix = _preceded_by_approx_or_ineq(line, m.start()) or _preceded_by_negation(line, m.start())
                    take(m)
                    token = m.group(2).rstrip(".,;:")
                    trailing_approx = bool(m.group(3))
                    if inexact_prefix or m.group(1) or trailing_approx or not re.fullmatch(r"[0-9]+(?:\.[0-9]+)?", token):
                        violations.append(Violation("MALFORMED_CLAIM", lineno, None,
                                                    f"`{m.group(0).strip()}` is not an exact kill rate"))
                    else:
                        found.append((m.start(), "kill_rate", "kill_rate", float(token), m.group(0).strip()))
        if has_eq_or_colon:
            for m in list(_KV_COUNT_RE.finditer(work[0])):
                inexact_prefix = _preceded_by_negation(line, m.start())
                take(m)
                if inexact_prefix:
                    violations.append(
                        Violation("MALFORMED_CLAIM", lineno, None,
                                  f"`{m.group(0).strip()}` is negated, not an exact count")
                    )
                    continue
                value = count(m, m.group(2) or "", m.group(3))
                if value is not None:
                    raw_metric = m.group(1).lower()
                    metric = _KV_METRIC_ALIASES.get(raw_metric, raw_metric)
                    found.append((m.start(), "count", metric, value, m.group(0).strip()))
    if has_kv_op:
        for m in list(_BAD_KV_RE.finditer(work[0])):
            take(m)
            violations.append(
                Violation("MALFORMED_CLAIM", lineno, None,
                          f"`{m.group(0).strip()}` is not an exact numeric verification claim")
            )
    if has_digit:
        for metric, pattern in _COUNT_PATTERNS:
            for m in list(pattern.finditer(work[0])):
                inexact_prefix = _preceded_by_approx_or_ineq(line, m.start()) or _preceded_by_negation(line, m.start())
                take(m)
                if inexact_prefix:
                    violations.append(
                        Violation("MALFORMED_CLAIM", lineno, None,
                                  f"`{m.group(0).strip()}` is negated or approximate, not an exact count")
                    )
                    continue
                value = count(m, m.group(1) or "", m.group(2))
                if value is not None:
                    found.append((m.start(), "count", metric, value, m.group(0).strip()))
    if "no" in low or "zero" in low or "without" in low or "sorry" in low:
        for metric, pattern in _ZERO_WORD_RES:
            for m in list(pattern.finditer(work[0])):
                neg = _preceded_by_negation(line, m.start())
                take(m)
                found.append((m.start(), "nonzero" if neg else "count", metric, 1 if neg else 0, m.group(0).strip()))
    if "!=" in line or "≠" in line:
        for m in list(_RC_NEQ_RE.finditer(work[0])):
            neg = _preceded_by_negation(line, m.start())
            take(m)
            token = m.group(1).rstrip(".:")
            if re.fullmatch(r"-?[0-9]+", token):
                val = int(token)
                if neg:
                    found.append((m.start(), "exit_status", "rc", val, m.group(0).strip()))
                elif val == 0:
                    found.append((m.start(), "exit_status", "status", "fail", m.group(0).strip()))
                else:
                    found.append((m.start(), "exit_status", "rc_neq", val, m.group(0).strip()))
            else:
                violations.append(Violation("MALFORMED_CLAIM", lineno, None,
                                            f"`{m.group(0).strip()}` is not an integer exit code"))
    if has_eq_or_colon:
        for m in list(_RC_ASSIGN_RE.finditer(work[0])):
            neg = _preceded_by_negation(line, m.start())
            take(m)
            token = m.group(1).rstrip(".:")
            if re.fullmatch(r"-?[0-9]+", token):
                val = int(token)
                if neg:
                    if val == 0:
                        found.append((m.start(), "exit_status", "status", "fail", m.group(0).strip()))
                    else:
                        found.append((m.start(), "exit_status", "rc_neq", val, m.group(0).strip()))
                else:
                    found.append((m.start(), "exit_status", "rc", val, m.group(0).strip()))
            else:
                violations.append(Violation("MALFORMED_CLAIM", lineno, None,
                                            f"`{m.group(0).strip()}` is not an integer exit code"))
    if has_digit:
        for m in list(_RC_PROSE_RE.finditer(work[0])):
            neg = _preceded_by_negation(line, m.start())
            take(m)
            val = int(m.group(1))
            if neg:
                if val == 0:
                    found.append((m.start(), "exit_status", "status", "fail", m.group(0).strip()))
                else:
                    found.append((m.start(), "exit_status", "rc_neq", val, m.group(0).strip()))
            else:
                found.append((m.start(), "exit_status", "rc", val, m.group(0).strip()))
    verdict_patterns: tuple[re.Pattern[str], ...] = (
        (_STATUS_RE, _OK_RE, _VERDICT_TOKEN_RE)
        if (has_eq_or_colon or "≠" in line)
        else (_VERDICT_TOKEN_RE,)
    )
    for pattern in verdict_patterns:
        for m in list(pattern.finditer(work[0])):
            if pattern is _VERDICT_TOKEN_RE:
                op_neq = False
                word = m.group(1).upper()
            else:
                op_neq = m.group(1) in ("!=", "≠")
                word = m.group(2).upper()
            verdict = (
                "pass" if word in _PASS_WORDS or word == "TRUE"
                else "fail" if word in _FAIL_WORDS or word == "FALSE" else ""
            )
            if verdict:
                if op_neq:
                    verdict = "fail" if verdict == "pass" else "pass"
                if _preceded_by_negation(line, m.start()):
                    verdict = "fail" if verdict == "pass" else "pass"
                take(m)
                found.append((m.start(), "exit_status", "status", verdict, m.group(0).strip()))
    if "all" in low:
        for m in list(_ALL_PASS_RE.finditer(work[0])):
            take(m)
            words = [w.lower() for w in re.findall(r"[A-Za-z']+", m.group(0))]
            negated = _preceded_by_negation(line, m.start()) or any(w in _NEGATION_WORDS for w in words[:-1])
            if negated:
                found.append((m.start(), "exit_status", "status", "fail", m.group(0).strip()))
            else:
                found.append((m.start(), "exit_status", "all", "pass", m.group(0).strip()))
    if has_step_context and (":" in line or "|" in line):
        for m in list(_SCOPED_VERDICT_RE.finditer(work[0])):
            word = m.group("word").upper()
            verdict = "pass" if word in _PASS_WORDS else "fail" if word in _FAIL_WORDS else ""
            if verdict:
                if m.group("neg") or _preceded_by_negation(line, m.start()):
                    verdict = "fail" if verdict == "pass" else "pass"
                take(m)
                found.append((m.start(), "exit_status", "status", verdict, m.group(0).strip()))
    if "axiom" in low:
        for m in list(_STANDARD_AXIOMS_RE.finditer(work[0])):
            neg = _preceded_by_negation(line, m.start())
            take(m)
            found.append((m.start(), "axioms", "non_standard" if neg else "standard_only", None, m.group(0).strip()))
        for m in list(_NO_AXIOMS_RE.finditer(work[0])):
            neg = _preceded_by_negation(line, m.start())
            take(m)
            found.append((m.start(), "axioms", "non_empty" if neg else "set", frozenset(), m.group(0).strip()))
        for m_list in list(_AXIOM_LIST_RE.finditer(work[0])):
            g_start, g_end = m_list.start(1), m_list.end(1)
            # Drop only comma-separated items that were already extracted in full as
            # earlier claims (`0 sorry`, `rc=0`), while preserving every unblanked
            # trailing item (`sorryAx`, `???`, or a genuine dangling comma).
            kept_segs: list[str] = []
            seg_pos = g_start
            for orig_seg in line[g_start:g_end].split(","):
                seg_end = seg_pos + len(orig_seg)
                work_seg = work[0][seg_pos:seg_end]
                seg_pos = seg_end + 1
                if orig_seg.strip() and not work_seg.strip():
                    continue
                if work_seg != orig_seg and work_seg.strip().lower() in ("with", "and", "plus"):
                    continue
                kept_segs.append(work_seg)
            raw_rest = ",".join(kept_segs)
            take(m_list)
            names = _axiom_names(raw_rest)
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


def _find_outside_code_spans(
    line: str, needle: str, pos: int, code_spans: Sequence[tuple[int, int, str]]
) -> int:
    """First index of `needle` at or after `pos` that does not start inside an inline code span."""
    cur = pos
    while True:
        idx = line.find(needle, cur)
        if idx == -1 or not _in_spans(idx, code_spans):
            return idx
        cur = idx + 1


def _strip_ignore_and_comments_line(
    line: str,
    lineno: int,
    in_ignore: bool,
    ignore_line: int,
    in_comment: bool,
    comment_line: int,
    violations: list[Violation],
) -> tuple[str, bool, int, bool, int, bool]:
    """Strip inline ignore blocks and HTML comments outside inline code spans on one line.

    Returns `(kept_text, in_ignore, ignore_line, in_comment, comment_line, was_ignored)`.
    Text outside `ignore-begin`..`ignore-end` on the same line is preserved.
    """
    out: list[str] = []
    pos = 0
    had_ignored = False
    while pos < len(line):
        if in_ignore:
            had_ignored = True
            end_at = line.find(_IGNORE_END, pos)
            begin_at = line.find(_IGNORE_BEGIN, pos)
            if begin_at != -1 and (end_at == -1 or begin_at < end_at):
                violations.append(
                    Violation("MALFORMED_CLAIMS", lineno, None,
                              "nested `claim-guard: ignore-begin` inside an open ignore block")
                )
            if end_at == -1:
                pos = len(line)
                break
            in_ignore = False
            pos = end_at + len(_IGNORE_END)
            out.append(" ")
        elif in_comment:
            close_at = line.find("-->", pos)
            if close_at == -1:
                pos = len(line)
                break
            in_comment = False
            pos = close_at + 3
            out.append(" ")
        else:
            code_spans = _inline_code_spans(line[pos:])
            shifted = [(pos + lo, pos + hi, inner) for lo, hi, inner in code_spans]
            begin_at = _find_outside_code_spans(line, _IGNORE_BEGIN, pos, shifted)
            end_at = _find_outside_code_spans(line, _IGNORE_END, pos, shifted)
            comm_at = _find_outside_code_spans(line, "<!--", pos, shifted)
            candidates = [idx for idx in (begin_at, end_at, comm_at) if idx != -1]
            if not candidates:
                out.append(line[pos:])
                break
            nxt = min(candidates)
            out.append(line[pos:nxt])
            if nxt == begin_at:
                in_ignore, ignore_line = True, lineno
                had_ignored = True
                pos = nxt + len(_IGNORE_BEGIN)
            elif nxt == end_at:
                violations.append(
                    Violation("MALFORMED_CLAIMS", lineno, None,
                              "unmatched `claim-guard: ignore-end` without an open ignore block")
                )
                pos = nxt + len(_IGNORE_END)
            else:
                in_comment, comment_line = True, lineno
                pos = nxt + 4
    kept = "".join(out)
    return kept, in_ignore, ignore_line, in_comment, comment_line, had_ignored and not kept.strip()


def _select_refs_for_pos(
    refs: Sequence[tuple[int, str | None, str, bool, bool]],
    claim_positions: Sequence[int],
    pos: int,
) -> list[tuple[str | None, str, bool]]:
    """Step reference(s) governing `pos` within a clause or line.

    Consecutive references with no intervening claim between them (`A and B: PASS`
    or `| A | B | PASS |`) form a compound subject and are all checked, deduplicated
    by target identity so `| step_id | step_command | PASS |` emits one claim.
    """
    non_secondary = [r for r in refs if not r[4]]
    pool = non_secondary if non_secondary else list(refs)
    before = [r for r in pool if r[0] <= pos]
    if before:
        group = [before[-1]]
        for k in range(len(before) - 2, -1, -1):
            lo_pos, hi_pos = before[k][0], before[k + 1][0]
            if any(lo_pos < c_pos < hi_pos for c_pos in claim_positions):
                break
            group.append(before[k])
        group.reverse()
    else:
        group = [pool[0]]
        for k in range(len(pool) - 1):
            lo_pos, hi_pos = pool[k][0], pool[k + 1][0]
            if any(lo_pos < c_pos < hi_pos for c_pos in claim_positions):
                break
            group.append(pool[k + 1])
    out: list[tuple[str | None, str, bool]] = []
    seen_keys: set[object] = set()
    for r in group:
        key: object = ("id", r[1]) if r[1] is not None else ("missing", r[3], r[2])
        if key not in seen_keys:
            seen_keys.add(key)
            out.append(r[1:4])
    return out


def extract_claims(text: str, steps: Sequence[Step]) -> tuple[list[Claim], list[Violation], int]:
    """Claims of a Markdown document, the violations found while reading it, and the
    number of explicitly ignored lines."""
    violations: list[Violation] = []
    claims: list[Claim] = []
    ignored = 0
    text = unicodedata.normalize("NFKC", text)
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    if _CONTROL_RE.search(text):
        violations.append(
            Violation("MALFORMED_CLAIMS", 0, None,
                      "the document contains control or bidirectional-override characters")
        )
        text = _LINE_SEP_CONTROL_RE.sub("\n", text)
        text = _CONTROL_RE.sub(" ", text)
    text = _INVISIBLE_RE.sub("", text)
    known = _KnownSteps(steps)
    fence_state: tuple[str, int, int, int] | None = None  # (char, length, open_lineno, bq_depth)
    in_ignore = in_comment = False
    ignore_line = comment_line = 0
    heading_ctx: list[tuple[str | None, str, bool]] = []
    para_ctx: list[tuple[str | None, str, bool]] = []

    def _audit_line(
        target: str,
        lineno: int,
        in_fence_mode: bool,
        fallback_ctx: Sequence[tuple[str | None, str, bool]],
    ) -> list[tuple[int, str | None, str, bool, bool]]:
        refs = _line_refs(target, known, in_fence_mode)
        clauses = _clause_spans(target) if not in_fence_mode else [(0, len(target))]
        is_table_hdr = False
        if not in_fence_mode and not refs and target.lstrip().startswith("|"):
            t_cells = _table_cell_spans(target)
            if t_cells:
                c0_plain = target[t_cells[0][0] : t_cells[0][1]].strip(" \t`*_").lower()
                is_table_hdr = c0_plain in _TABLE_HEADER_CELL0_WORDS
        raw_claims = _line_claims(
            target,
            lineno,
            violations,
            has_step_context=bool(refs or (fallback_ctx and not is_table_hdr)),
        )
        scoped_positions = [
            c_pos for c_pos, c_kind, c_metric, _v, _s in raw_claims
            if c_kind != "commit_sha" and c_metric != "all"
        ]
        for pos, kind, metric, value, snippet in raw_claims:
            if kind == "commit_sha" or metric == "all":
                # A commit names the whole run, and "all ... pass" every step.
                claims.append(Claim(kind, metric, value, lineno, snippet, None))
                continue
            seg_bounds = next(((lo, hi) for lo, hi in clauses if lo <= pos < hi), (0, len(target)))
            seg_lo, seg_hi = seg_bounds
            seg_refs = [r for r in refs if seg_lo <= r[0] < seg_hi]
            seg_claim_pos = [cp for cp in scoped_positions if seg_lo <= cp < seg_hi]
            if seg_refs:
                chosen_list = _select_refs_for_pos(seg_refs, seg_claim_pos, pos)
            elif refs:
                chosen_list = _select_refs_for_pos(refs, scoped_positions, pos)
            elif fallback_ctx:
                chosen_list = list(fallback_ctx)
            else:
                chosen_list = []
            if not chosen_list:
                claims.append(Claim(kind, metric, value, lineno, snippet, None))
            else:
                for ref3 in chosen_list:
                    if ref3[0] is None:
                        missing = ("step:" if ref3[2] else "command:") + ref3[1]
                        claims.append(Claim(kind, metric, value, lineno, snippet, None, missing))
                    else:
                        claims.append(Claim(kind, metric, value, lineno, snippet, ref3[0]))
        return refs

    for lineno, line in enumerate(text.split("\n"), 1):
        if fence_state is not None:
            f_ch, f_len, f_line, f_bq = fence_state
            if f_bq > 0:
                unq, got_bq = _strip_blockquote_prefix(line, max_depth=f_bq)
                if got_bq < f_bq:
                    violations.append(
                        Violation("MALFORMED_CLAIMS", f_line, None,
                                  "fenced code block is never closed")
                    )
                    fence_state = None
                    para_ctx = []
                else:
                    line = unq
        if fence_state is not None:
            f_ch, f_len, _f_line, _f_bq = fence_state
            if _IGNORE_BEGIN in line or _IGNORE_END in line:
                violations.append(
                    Violation("MALFORMED_CLAIMS", lineno, None,
                              "claim-guard ignore directive is not permitted inside a fenced code block")
                )
            if re.match(rf"^\s{{0,3}}{re.escape(f_ch)}{{{f_len},}}\s*$", line):
                fence_state = None
                para_ctx = []
                continue
        else:
            line, in_ignore, ignore_line, in_comment, comment_line, was_ignored = (
                _strip_ignore_and_comments_line(
                    line, lineno, in_ignore, ignore_line, in_comment, comment_line, violations
                )
            )
            if was_ignored:
                ignored += 1
                continue
            line, bq_depth = _strip_blockquote_prefix(line)
            m_fence = _FENCE_OPEN_RE.match(line)
            if m_fence is not None:
                f_ch, f_len, info = m_fence.group(1)[0], len(m_fence.group(1)), m_fence.group(2)
                is_inline_tilde = f_ch == "~" and bool(re.search(rf"{re.escape(f_ch)}{{{f_len},}}\s*$", info))
                if not (f_ch == "`" and "`" in info) and not is_inline_tilde:
                    fence_state = (f_ch, f_len, lineno, bq_depth)
                    para_ctx = []
                    info_s = info.strip()
                    if info_s and info_s.upper() in (_PASS_WORDS | _FAIL_WORDS):
                        _audit_line(f": {info_s}", lineno, False, heading_ctx)
                    elif info_s and not re.fullmatch(r"[A-Za-z0-9_+#.-]+", info_s):
                        _audit_line(_strip_strikethrough_outside_code(info), lineno, False, heading_ctx)
                    continue
            line = _strip_strikethrough_outside_code(line)
        in_fence = fence_state is not None
        if not line.strip():
            if not in_fence:
                para_ctx = []
            continue
        if not in_fence and _HISTORICAL_RE.match(line):
            ignored += 1
            continue
        is_table_row = not in_fence and line.lstrip().startswith("|")
        is_list_item = not in_fence and bool(_LIST_ITEM_RE.match(line))
        if is_table_row or is_list_item:
            para_ctx = []
        refs = _audit_line(line, lineno, in_fence, para_ctx or heading_ctx)
        non_sec = [r for r in refs if not r[4]]
        ctx_pool = non_sec if non_sec else refs
        distinct = sorted({r[1:4] for r in ctx_pool}, key=repr)
        is_heading = not in_fence and line.lstrip().startswith("#")
        if is_heading:
            heading_ctx = distinct
            para_ctx = []
        elif is_table_row:
            para_ctx = []
        elif distinct:
            para_ctx = distinct if len(distinct) == 1 else []
    if fence_state is not None:
        violations.append(
            Violation("MALFORMED_CLAIMS", fence_state[2], None,
                      "fenced code block is never closed")
        )
    if in_ignore:
        violations.append(
            Violation("MALFORMED_CLAIMS", ignore_line, None,
                      "`claim-guard: ignore-begin` is never closed")
        )
    if in_comment:
        violations.append(
            Violation("MALFORMED_CLAIMS", comment_line, None,
                      "HTML comment `<!--` is never closed")
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
        if "total" in step.counts and "passed" in step.counts:
            return step.counts["total"]
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

    # Track which failing steps are explicitly acknowledged as failing by another claim.
    acknowledged_fail_steps: set[str] = set()
    any_unscoped_fail_ack = False
    for c in claims:
        if c.kind == "exit_status" and not c.missing:
            if (c.metric == "status" and c.value == "fail") or (c.metric == "rc" and c.value != 0):
                if c.step is None:
                    any_unscoped_fail_ack = True
                else:
                    acknowledged_fail_steps.add(c.step)

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
                if not codes:
                    add("UNBACKED_CLAIM", claim,
                        f"`{claim.text}`: {scope} record no integer exit code")
                elif claim.value not in codes:
                    add("EXIT_CODE_MISMATCH", claim,
                        f"`{claim.text}` but {scope} record exit code(s) {sorted(codes)}")
            elif claim.metric == "rc_neq":
                codes = {step.returncode for step in with_exit if step.returncode is not None}
                if not codes:
                    add("UNBACKED_CLAIM", claim,
                        f"`{claim.text}`: {scope} record no integer exit code")
                elif claim.value in codes:
                    add("EXIT_CODE_MISMATCH", claim,
                        f"`{claim.text}` but {scope} exited with {claim.value}")
                elif failing:
                    unscoped_covers = claim.step is None and len(steps) == 1 and any_unscoped_fail_ack
                    for step in failing:
                        if step.step_id not in acknowledged_fail_steps and not unscoped_covers:
                            add("SUPPRESSED_FAILURE", claim,
                                f"`{claim.text}` suppresses failure of step `{step.step_id}` ({step.failure()})",
                                step.step_id)
            elif not failing:
                add("EXIT_CODE_MISMATCH", claim, f"`{claim.text}` but {scope} passed")

        elif claim.kind == "nonzero":
            metric = claim.metric
            reporting = [step for step in targets if _metric_value(step, metric) is not None]
            if metric == "sorry" and not reporting:
                with_axioms = [step for step in targets if step.axioms is not None]
                if with_axioms:
                    if not any("sorryAx" in (step.axioms or ()) for step in with_axioms):
                        add("SORRY_VIOLATION", claim, f"`{claim.text}` but {scope} have no `sorryAx`")
                    continue
            if not reporting:
                add("UNBACKED_CLAIM", claim, f"`{claim.text}`: {scope} report no `{metric}` count")
                continue
            actual = sum(_metric_value(step, metric) or 0 for step in reporting)
            if actual == 0:
                add(_count_code(metric, 1, 0), claim, f"`{claim.text}` but {scope} report 0 `{metric}`")

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
            elif claimed == 0 and metric in ("failed", "survived", "errors"):
                # Claiming `0 failed`, `0 survived`, or `0 errors` must not mask a crashed,
                # fatally aborted, or uncounted failing step.
                for step in targets:
                    fail_reason = step.failure()
                    if fail_reason is None:
                        continue
                    if metric == "failed" and (_metric_value(step, "failed") or 0) == 0:
                        if step.counts.get("survived", 0) == 0:
                            add("SUPPRESSED_FAILURE", claim,
                                f"`{claim.text}` but step `{step.step_id}` failed ({fail_reason})", step.step_id)
                    elif metric == "survived" and step.counts.get("survived", 0) == 0:
                        if step.counts.get("failed", 0) == 0:
                            add("SUPPRESSED_FAILURE", claim,
                                f"`{claim.text}` but step `{step.step_id}` failed ({fail_reason})", step.step_id)
                    elif metric == "errors" and step.counts.get("errors", 0) == 0:
                        if step.counts.get("failed", 0) == 0 and step.counts.get("survived", 0) == 0:
                            add("SUPPRESSED_FAILURE", claim,
                                f"`{claim.text}` but step `{step.step_id}` failed ({fail_reason})", step.step_id)

        elif claim.kind == "kill_rate":
            rated = [step for step in targets if step.counts.get("total") and "killed" in step.counts]
            if not rated:
                add("UNBACKED_CLAIM", claim, f"`{claim.text}`: {scope} report no kill counts")
                continue
            killed = sum(step.counts["killed"] for step in rated)
            total = sum(step.counts["total"] for step in rated)
            claimed_rate = float(claim.value)  # type: ignore[arg-type]
            exact_rate = 100.0 * killed / total
            actual_rate = round(exact_rate, 2)
            # Never round a non-100% kill rate up to 100%, or a non-0% rate down to 0%.
            boundary_lie = (claimed_rate >= 100.0 and killed < total) or (claimed_rate <= 0.0 and killed > 0)
            if boundary_lie or claimed_rate > 100.0 or (
                abs(claimed_rate - exact_rate) > 0.005 and abs(claimed_rate - actual_rate) > 0.005
            ):
                code = "INFLATED_COUNT" if claimed_rate > exact_rate else "COUNT_MISMATCH"
                add(code, claim, f"`{claim.text}` but the receipts give {killed}/{total} = {exact_rate:.4g}%")

        elif claim.kind == "axioms":
            with_axioms = [step for step in targets if step.axioms is not None]
            if not with_axioms:
                add("UNBACKED_CLAIM", claim, f"`{claim.text}`: {scope} report no axiom list")
                continue
            if claim.metric == "non_standard":
                if all(set(step.axioms or ()) <= ALLOWED_KERNEL_AXIOMS for step in with_axioms):
                    add("AXIOM_SET_MISMATCH", claim,
                        f"`{claim.text}` but {scope} use only standard kernel axioms")
                continue
            if claim.metric == "non_empty":
                if all(not (step.axioms or ()) for step in with_axioms):
                    add("AXIOM_SET_MISMATCH", claim, f"`{claim.text}` but {scope} use 0 axioms")
                continue
            allowed = ALLOWED_KERNEL_AXIOMS if claim.metric == "standard_only" else set(claim.value)  # type: ignore[arg-type]
            for step in with_axioms:
                step_axioms = set(step.axioms or ())
                extra = sorted(step_axioms - allowed)
                if extra:
                    add("AXIOM_SET_MISMATCH", claim,
                        f"`{claim.text}` omits axiom(s) {', '.join(extra)} of step `{step.step_id}`", step.step_id)
                if claim.metric == "set":
                    bogus = sorted((allowed - authorized) - step_axioms)
                    if bogus:
                        add("AXIOM_SET_MISMATCH", claim,
                            f"`{claim.text}` lists unauthorized axiom(s) {', '.join(bogus)} absent from step `{step.step_id}`",
                            step.step_id)
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
        # A `Base` SHA is informational context, not a verified claim; a document
        # with only `Base` SHAs and vague prose must still fail closed.
        verifiable = [c for c in claims if not (c.kind == "commit_sha" and c.metric == "base")]
        # A document whose only claims are unreadable already fails for that.
        if not verifiable and not claim_violations and require_nonempty_claims:
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


def _write_json_out(path: Path, report: dict[str, object], *, no_symlinks: bool = False) -> None:
    if no_symlinks:
        _ensure_no_symlink_components(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    fd, tmp_name = tempfile.mkstemp(prefix=".rcg-", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            fd = -1
            handle.write(payload)
        os.replace(tmp_name, path)
    except BaseException:
        if fd >= 0:
            os.close(fd)
        try:
            os.unlink(tmp_name)
        except OSError:
            pass
        raise


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
        if sep and not head:
            parser.error(f"--receipt {raw!r}: empty STEP_ID before '='")
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
    if any(
        not step_id.strip() or step_id != step_id.strip() or "\n" in step_id or "\r" in step_id
        for step_id in args.require_step
    ):
        parser.error("--require-step needs a clean single-line non-empty STEP_ID")
    if args.max_elapsed_ms is not None and not (0 < args.max_elapsed_ms < float("inf")):
        parser.error("--max-elapsed-ms must be a positive finite number")

    sink_error: list[str] = []

    def write_out(report: dict[str, object]) -> bool:
        if args.json_out is None:
            return True
        try:
            _write_json_out(args.json_out, report, no_symlinks=args.no_symlinks)
            return True
        except OSError as exc:
            msg = f"cannot write {args.json_out}: {exc}"
            sink_error.append(msg)
            print(f"ERROR: {msg}", file=sys.stderr)
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
        if report["fatal_error"] is None and sink_error:
            report["fatal_error"] = sink_error[-1]
    if args.emit_json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(format_report(report))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
