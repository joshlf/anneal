#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Single-guard mutation testing gate for Anneal's `V2026_06_01` MIR semantics.

Why this check exists
---------------------

Positive verification proofs and positive canary suites cannot catch an
accidental deletion or weakening of an undefined-behavior (UB) guard in
`trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/`. If a refactor drops a
division-by-zero check, weakens pointer alignment validation, removes an
`assume(false)` or `copy_nonoverlapping` overlap guard, or drops a Tree Borrows
active-protector conflict check, every positive proof still succeeds while UB
programs silently become provable.

This script closes that blind spot (ported from `google/zerocopy#4119` to
`Trusted.Rustc.V2026_06_01.MirSemantics`) by performing single-guard mutation
testing inside isolated `tempfile.TemporaryDirectory` workspaces without ever
modifying the repository working tree:

1. Against the unmodified TCB `.olean`s (reusing up-to-date
   `.lake/build/lib/lean` artifacts via hardlinks when available, or compiling
   in topological order on cold checkouts), every selected guard's positive
   sanity theorem AND negative refutation theorem must compile cleanly (`rc=0`,
   zero `sorry` warnings).
2. For each cataloged guard, the runner weakens ONLY that guard inside a fresh
   `with tempfile.TemporaryDirectory():` overlay, recompiles ONLY the mutated
   target module (plus any declared downstream modules), confirms that the
   mutated TCB module AND the guard's positive sanity theorem still compile
   cleanly with zero `sorry`s (preventing syntax/type/crash errors from
   masquerading as mutant kills), and verifies that the guard's dedicated
   negative refutation theorem fails with a genuine proof/type mismatch error
   localized strictly inside the target theorem's line span.
3. The gate exits `0` if and only if 100% of selected guards are genuinely
   killed with `0` survivors and `0` errors.

Anti-false-kill and isolation invariants
----------------------------------------

* A mutant only counts as `KILLED` when Lean exits `1` and every error
  diagnostic is located inside the guard's refutation theorem in the generated
  fixture, with a proof/type-mismatch marker inside one of those diagnostics.
  Errors in other files, errors without a source position, crash/timeout/parse
  markers, and signal exit codes are `ERROR`, never a kill.
* `.lake/build/lib/lean` `.olean`s are reused only when they are proven to
  correspond to the current sources: Lake's own `.trace` records are checked by
  content — both standard traces (source text hash, `.olean` hash, toolchain,
  and every imported `.olean` hash) and `"synthetic": true` `$LAKE_CACHE_DIR`
  traces (by reproducing Lake v4.34's exact cryptographic `depHash` over
  source, toolchain commit, package/module identity, and transitive import
  traces in pure Python). Every reused `.olean` is re-hashed by default, so an
  artifact that was swapped or corrupted while its `.olean.hash` and `.trace`
  stayed intact is rejected. File mtimes are consulted only for build trees
  that have no Lake traces at all, where a source newer than its `.olean`
  forces a cold build.
* Fixtures are checked statically before Lean runs: one `rfl` theorem with no
  binders, helper `def`s that shadow no trusted declaration, an allowlist of
  top-level commands, and no construct the comment scanner cannot lex exactly
  (interpolated or raw strings, character literals, backslashes). The theorem
  must read `<MirSemantics function> <args> = <expected data>`: no other part
  of the fixture may name a MirSemantics function, a refutation must expect
  UB literally, and a positive sanity fixture must not mention `ub` at all.
* `.olean`s are shared by hardlink, so no Lean invocation may ever write
  through one: destinations are unlinked before every link and every compile,
  stale downstream modules are never seeded into a mutant overlay, and the
  reused Lake artifacts are re-checked after the run.

Exit status and JSON report
---------------------------

`0`: every selected guard was killed. `1`: a survivor, an error, or a fatal
failure before any result. `2`: bad command line. `130`: interrupted by
SIGINT, SIGTERM or SIGHUP, after killing every Lean process group and removing
every temporary directory.

`--json` and `--json-out` carry the same keys whether the run finished or
failed fatally; `ok` is the verdict and `fatal_error` is `null` unless the run
produced no results. A `--json-out` file is overwritten with a failing report
before the run starts, so it can never show a stale pass.

How to add a new guard
----------------------

1. Add a `MirSemanticsGuard` entry to `MIR_SEMANTICS_GUARDS` below whose
   `anchor` uniquely matches the UB guard in `Scalars.lean`, `Places.lean`,
   `Statements.lean`, or `Terminators.lean`, and whose `replacement` weakens
   only that guard without breaking the module or any internal theorem inside
   it.
2. Provide self-contained `sanity_source` (positive behavior that must keep
   passing on the mutant) and `refute_source` (concrete UB refutation theorem
   that passes on unmodified TCB and fails with a proof error on the mutant).
3. Run:
     python3 -B scripts/check_mir_guard_mutation.py --list
     python3 -B -m unittest scripts/test_check_mir_guard_mutation.py
     anneal-lean-run --mode build -- python3 -B scripts/check_mir_guard_mutation.py --all --json
"""

from __future__ import annotations

import argparse
import array
from collections import Counter
from collections.abc import Iterator, Sequence
from concurrent.futures import Future, ThreadPoolExecutor, as_completed
import contextlib
from dataclasses import asdict, dataclass
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time

try:  # Python >= 3.11
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - older interpreters
    tomllib = None  # type: ignore[assignment]

sys.dont_write_bytecode = True


# Base trusted Lean modules in strict topological import order. None of the
# cataloged guards mutate these files, so every mutant reuses their precompiled
# `.olean` artifacts via hardlinks into its isolated `mut_olean_dir`.
BASE_TRUSTED_MODULES: tuple[str, ...] = (
    "Trusted/Sequence",
    "Trusted/CoInd",
    "Trusted/Effect",
    "Trusted/Refinement",
    "Trusted/ITree",
    "Trusted/Rustc/V2026_06_01/Layout",
    "Trusted/Rustc/V2026_06_01/MirAst/Types",
    "Trusted/Rustc/V2026_06_01/MirAst/Places",
    "Trusted/Rustc/V2026_06_01/MirAst/Rvalues",
    "Trusted/Rustc/V2026_06_01/MirAst/Statements",
    "Trusted/Rustc/V2026_06_01/MirAst/Terminators",
    "Trusted/Rustc/V2026_06_01/MirAst/Body",
    "Trusted/Rustc/V2026_06_01/MirSemantics/State",
)

# Operational semantics modules in strict topological import order.
SEMANTICS_MODULES: tuple[str, ...] = (
    "Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
    "Trusted/Rustc/V2026_06_01/MirSemantics/Bytes",
    "Trusted/Rustc/V2026_06_01/MirSemantics/Places",
    "Trusted/Rustc/V2026_06_01/MirSemantics/Statements",
    "Trusted/Rustc/V2026_06_01/MirSemantics/Terminators",
)

# Transitive upstream semantics dependencies within `SEMANTICS_MODULES` (in
# topological order) for each semantics module. Every semantics module also
# depends on `BASE_TRUSTED_MODULES`.
SEMANTICS_UPSTREAM: dict[str, tuple[str, ...]] = {
    "Trusted/Rustc/V2026_06_01/MirSemantics/Scalars": (),
    "Trusted/Rustc/V2026_06_01/MirSemantics/Bytes": (
        "Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
    ),
    "Trusted/Rustc/V2026_06_01/MirSemantics/Places": (
        "Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        "Trusted/Rustc/V2026_06_01/MirSemantics/Bytes",
    ),
    "Trusted/Rustc/V2026_06_01/MirSemantics/Statements": (
        "Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        "Trusted/Rustc/V2026_06_01/MirSemantics/Bytes",
        "Trusted/Rustc/V2026_06_01/MirSemantics/Places",
    ),
    "Trusted/Rustc/V2026_06_01/MirSemantics/Terminators": (
        "Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        "Trusted/Rustc/V2026_06_01/MirSemantics/Bytes",
        "Trusted/Rustc/V2026_06_01/MirSemantics/Places",
        "Trusted/Rustc/V2026_06_01/MirSemantics/Statements",
    ),
}

# Minimal direct rebuild closure for guards whose generated sanity & refutation
# fixtures import `guard.target_module` directly (avoiding unnecessary rebuilds
# of heavy downstream files such as `Places.lean` when mutating `Scalars.lean`).
SEMANTICS_DOWNSTREAM_DIRECT: dict[str, tuple[str, ...]] = {
    "Trusted/Rustc/V2026_06_01/MirSemantics/Scalars": (
        "Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
    ),
    "Trusted/Rustc/V2026_06_01/MirSemantics/Places": (
        "Trusted/Rustc/V2026_06_01/MirSemantics/Places",
    ),
    "Trusted/Rustc/V2026_06_01/MirSemantics/Statements": (
        "Trusted/Rustc/V2026_06_01/MirSemantics/Statements",
    ),
    "Trusted/Rustc/V2026_06_01/MirSemantics/Terminators": (
        "Trusted/Rustc/V2026_06_01/MirSemantics/Terminators",
    ),
}

# Required four operational semantics modules that the catalog must cover.
REQUIRED_COVERAGE_MODULES: tuple[str, ...] = (
    "Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
    "Trusted/Rustc/V2026_06_01/MirSemantics/Places",
    "Trusted/Rustc/V2026_06_01/MirSemantics/Statements",
    "Trusted/Rustc/V2026_06_01/MirSemantics/Terminators",
)

# Lean 4 compiled module artifact suffixes (covering both traditional `.olean`
# and split module-system companion files if emitted).
OLEAN_SUFFIXES: tuple[str, ...] = (
    ".olean",
    ".olean.server",
    ".olean.private",
)

# Error substrings indicating compiler crash, syntax error, missing import,
# toolchain mismatch, or resource exhaustion rather than a genuine proof
# refutation failure. Any refutation failure containing one of these markers is
# classified as `ERROR` rather than `KILLED`.
NON_KILL_ERROR_MARKERS: tuple[str, ...] = (
    "unknown identifier",
    "unknown constant",
    "unknown module",
    "expected token",
    "unexpected token",
    "maximum recursion depth",
    "deterministic timeout",
    "heartbeats",
    "PANIC",
    "internal exception",
    "invalid import",
    "incompatible header",
    "(deterministic) timeout",
    "stack overflow",
    "Stack overflow",
    "out of memory",
    "uncaught exception",
    "unknown namespace",
    "unknown package",
    "object file",
)

# Diagnostic substrings emitted by Lean 4 when a refutation theorem fails to
# type-check because the mutated semantics no longer produces UB.
EXPECTED_PROOF_FAILURE_MARKERS: tuple[str, ...] = (
    "Type mismatch",
    "type mismatch",
    "has type",
    "rfl",
    "unsolved goals",
    "Function expected",
    "Application type mismatch",
    "failed to synthesize",
    "invalid field",
    "is not a valid",
)

# Lean 4 warns when a proof uses `sorry`. The pinned toolchain (v4.34.1) prints
# "declaration uses `sorry`" with backticks, older ones used single quotes, and
# `#print axioms` names `sorryAx`. One pattern matches every spelling.
SORRY_OUTPUT_RE = re.compile(r"\bsorry(?:Ax)?\b")

# Tokens forbidden inside generated sanity and refutation Lean fixtures (and in
# guard replacements). They either make a proof vacuous (`sorry`, `sorryAx`,
# `admit`, `axiom`, `opaque`, `native_decide`, `implemented_by`, `extern`,
# `unsafe`, `partial`), smuggle a second proof obligation into the fixture
# (`example`, `lemma`, `instance`), or change how the fixture elaborates
# (`set_option`, `attribute`, `macro`, `macro_rules`, `syntax`, `elab`,
# `elab_rules`, `notation`, `infix*`, `prefix`, `postfix`, `local`, `scoped`,
# `declare_syntax_cat`, `run_cmd`, `initialize`, `#`-commands), bring hidden
# hypotheses or names into scope (`variable`, `universe`, `export`), or declare
# anything other than a plain helper `def` (`abbrev`, `structure`,
# `inductive`, `class`, `deriving`, `mutual`).
FORBIDDEN_FIXTURE_TOKEN_RE = re.compile(
    r"\bsorry\w*|#[A-Za-z_]\w*|"
    r"\b(?:admit|axiom|opaque|native_decide|implemented_by|extern|unsafe|"
    r"partial|example|lemma|instance|set_option|attribute|macro|macro_rules|"
    r"syntax|elab|elab_rules|notation|run_cmd|initialize|variable|universe|"
    r"local|scoped|infix|infixl|infixr|prefix|postfix|declare_syntax_cat|"
    r"export|abbrev|structure|inductive|class|deriving|mutual)\b"
)

# The only words that may start a column-0 line of a generated fixture.
FIXTURE_TOP_LEVEL_WORDS: frozenset[str] = frozenset(
    {"import", "namespace", "end", "open", "def", "theorem"}
)

# Lake build trace schema versions whose layout `_verify_lake_traces` knows.
LAKE_TRACE_SCHEMA_VERSIONS: tuple[str, ...] = ("2025-09-10",)

# Valid guard_id pattern (also used as Lean module filename suffix).
GUARD_ID_RE = re.compile(r"^[a-z][a-z0-9_]*$")


@dataclass(frozen=True)
class MirSemanticsGuard:
    """Single-guard mutation entry targeting `V2026_06_01/MirSemantics/`."""

    guard_id: str
    target_file: str
    target_module: str
    description: str
    anchor: str
    replacement: str
    sanity_theorem_name: str
    sanity_source: str
    theorem_name: str
    refute_source: str
    quick: bool = False
    rebuild_modules: tuple[str, ...] = ()

    @property
    def effective_rebuild_modules(self) -> tuple[str, ...]:
        if self.rebuild_modules:
            return self.rebuild_modules
        return SEMANTICS_DOWNSTREAM_DIRECT[self.target_module]

    @property
    def sanity_module(self) -> str:
        return f"PositiveSanity_{self.guard_id}"

    @property
    def refute_module(self) -> str:
        return f"Refute_{self.guard_id}"


@dataclass(frozen=True)
class GuardResult:
    """Outcome of executing one single-guard mutation check."""

    guard_id: str
    target_file: str
    target_module: str
    quick: bool
    status: str  # KILLED | SURVIVED | ERROR
    duration_sec: float
    detail: str


MIR_SEMANTICS_GUARDS: tuple[MirSemanticsGuard, ...] = (
    # ------------------------------------------------------------------
    # Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean (7 UB guards + 2 boundary mutants)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="div_by_zero",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        description="evalScalarBinOp .div rejects divisor == 0 as UB",
        anchor=(
            "        | .div =>\n"
            "          match Nat.beq b 0 with\n"
            "          | true => .ub\n"
            "          | false =>\n"
            "            match isSigned with"
        ),
        replacement=(
            "        | .div =>\n"
            "          match false with\n"
            "          | true => .ub\n"
            "          | false =>\n"
            "            match isSigned with"
        ),
        sanity_theorem_name="sanity_div_by_zero",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem sanity_div_by_zero :\n"
            "    evalScalarBinOp .div ⟨42, 1⟩ ⟨6, 1⟩ .nil emptyMemory false =\n"
            "      .ok (.scalar ⟨7, 1⟩) .nil emptyMemory :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_div_by_zero",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem refute_div_by_zero :\n"
            "    evalScalarBinOp .div ⟨7, 1⟩ ⟨0, 1⟩ .nil emptyMemory false = .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        quick=True,
    ),
    MirSemanticsGuard(
        guard_id="rem_by_zero",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        description="evalScalarBinOp .rem rejects divisor == 0 as UB",
        anchor=(
            "        | .rem =>\n"
            "          match Nat.beq b 0 with\n"
            "          | true => .ub\n"
            "          | false =>\n"
            "            match isSigned with"
        ),
        replacement=(
            "        | .rem =>\n"
            "          match false with\n"
            "          | true => .ub\n"
            "          | false =>\n"
            "            match isSigned with"
        ),
        sanity_theorem_name="sanity_rem_by_zero",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem sanity_rem_by_zero :\n"
            "    evalScalarBinOp .rem ⟨23, 1⟩ ⟨5, 1⟩ .nil emptyMemory false =\n"
            "      .ok (.scalar ⟨3, 1⟩) .nil emptyMemory :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_rem_by_zero",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem refute_rem_by_zero :\n"
            "    evalScalarBinOp .rem ⟨7, 1⟩ ⟨0, 1⟩ .nil emptyMemory false = .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    MirSemanticsGuard(
        guard_id="signed_div_overflow",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        description="evalSignedDiv rejects signed MIN / -1 overflow as UB",
        anchor=(
            "  match Bool.and (Nat.beq ca minSigned) (Nat.beq cb minusOne) with\n"
            "  | true => .ub\n"
            "  | false =>\n"
            "    let negA := isSignedNegative ca sz\n"
            "    let negB := isSignedNegative cb sz\n"
            "    let magA := match negA with | false => ca | true => Nat.sub modulus ca\n"
            "    let magB := match negB with | false => cb | true => Nat.sub modulus cb\n"
            "    let magQ := Nat.div magA magB"
        ),
        replacement=(
            "  match false with\n"
            "  | true => .ub\n"
            "  | false =>\n"
            "    let negA := isSignedNegative ca sz\n"
            "    let negB := isSignedNegative cb sz\n"
            "    let magA := match negA with | false => ca | true => Nat.sub modulus ca\n"
            "    let magB := match negB with | false => cb | true => Nat.sub modulus cb\n"
            "    let magQ := Nat.div magA magB"
        ),
        sanity_theorem_name="sanity_signed_div_overflow",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem sanity_signed_div_overflow :\n"
            "    evalScalarBinOp .div ⟨246, 1⟩ ⟨2, 1⟩ .nil emptyMemory true =\n"
            "      .ok (.scalar ⟨251, 1⟩) .nil emptyMemory :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_signed_div_overflow",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem refute_signed_div_overflow :\n"
            "    evalScalarBinOp .div ⟨128, 1⟩ ⟨255, 1⟩ .nil emptyMemory true = .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    MirSemanticsGuard(
        guard_id="signed_rem_overflow",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        description="evalSignedRem rejects signed MIN % -1 overflow as UB",
        anchor=(
            "  match Bool.and (Nat.beq ca minSigned) (Nat.beq cb minusOne) with\n"
            "  | true => .ub\n"
            "  | false =>\n"
            "    let negA := isSignedNegative ca sz\n"
            "    let negB := isSignedNegative cb sz\n"
            "    let magA := match negA with | false => ca | true => Nat.sub modulus ca\n"
            "    let magB := match negB with | false => cb | true => Nat.sub modulus cb\n"
            "    let magR := Nat.mod magA magB"
        ),
        replacement=(
            "  match false with\n"
            "  | true => .ub\n"
            "  | false =>\n"
            "    let negA := isSignedNegative ca sz\n"
            "    let negB := isSignedNegative cb sz\n"
            "    let magA := match negA with | false => ca | true => Nat.sub modulus ca\n"
            "    let magB := match negB with | false => cb | true => Nat.sub modulus cb\n"
            "    let magR := Nat.mod magA magB"
        ),
        sanity_theorem_name="sanity_signed_rem_overflow",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem sanity_signed_rem_overflow :\n"
            "    evalScalarBinOp .rem ⟨246, 1⟩ ⟨3, 1⟩ .nil emptyMemory true =\n"
            "      .ok (.scalar ⟨255, 1⟩) .nil emptyMemory :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_signed_rem_overflow",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem refute_signed_rem_overflow :\n"
            "    evalScalarBinOp .rem ⟨128, 1⟩ ⟨255, 1⟩ .nil emptyMemory true = .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    MirSemanticsGuard(
        guard_id="shift_oob",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        description="evalScalarBinOp .shlUnchecked rejects shift distance >= bit width as UB",
        anchor=(
            "    | .shlUnchecked =>\n"
            "      match Nat.beq rhs.sizeBytes 0 with\n"
            "      | true => .unsupported\n"
            "      | false =>\n"
            "        match Nat.ble numBits b with\n"
            "        | true => .ub\n"
            "        | false => .ok (.scalar ⟨shiftLeftBits a b modulus, sz⟩) locals mem"
        ),
        replacement=(
            "    | .shlUnchecked =>\n"
            "      match Nat.beq rhs.sizeBytes 0 with\n"
            "      | true => .unsupported\n"
            "      | false =>\n"
            "        match false with\n"
            "        | true => .ub\n"
            "        | false => .ok (.scalar ⟨shiftLeftBits a b modulus, sz⟩) locals mem"
        ),
        sanity_theorem_name="sanity_shift_oob",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem sanity_shift_oob :\n"
            "    evalScalarBinOp .shlUnchecked ⟨1, 1⟩ ⟨3, 1⟩ .nil emptyMemory false =\n"
            "      .ok (.scalar ⟨8, 1⟩) .nil emptyMemory :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_shift_oob",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem refute_shift_oob :\n"
            "    evalScalarBinOp .shlUnchecked ⟨1, 1⟩ ⟨8, 1⟩ .nil emptyMemory false = .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    MirSemanticsGuard(
        guard_id="shr_oob",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        description="evalScalarBinOp .shrUnchecked rejects shift distance >= bit width as UB",
        anchor=(
            "    | .shrUnchecked =>\n"
            "      match Nat.beq rhs.sizeBytes 0 with\n"
            "      | true => .unsupported\n"
            "      | false =>\n"
            "        match Nat.ble numBits b with\n"
            "        | true => .ub\n"
            "        | false =>\n"
            "          let shifted :="
        ),
        replacement=(
            "    | .shrUnchecked =>\n"
            "      match Nat.beq rhs.sizeBytes 0 with\n"
            "      | true => .unsupported\n"
            "      | false =>\n"
            "        match false with\n"
            "        | true => .ub\n"
            "        | false =>\n"
            "          let shifted :="
        ),
        sanity_theorem_name="sanity_shr_oob",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem sanity_shr_oob :\n"
            "    evalScalarBinOp .shrUnchecked ⟨16, 1⟩ ⟨2, 1⟩ .nil emptyMemory false =\n"
            "      .ok (.scalar ⟨4, 1⟩) .nil emptyMemory :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_shr_oob",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem refute_shr_oob :\n"
            "    evalScalarBinOp .shrUnchecked ⟨16, 1⟩ ⟨8, 1⟩ .nil emptyMemory false = .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    # Off-by-one boundary mutants (`numBits <= b` weakened to `numBits < b`).
    # Only a refutation input with `b == numBits` kills these, so they pin
    # the shift guards' refutation inputs to the exact boundary.
    MirSemanticsGuard(
        guard_id="shl_oob_off_by_one",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        description="evalScalarBinOp .shlUnchecked rejects shift distance == bit width (off-by-one boundary)",
        anchor=(
            "    | .shlUnchecked =>\n"
            "      match Nat.beq rhs.sizeBytes 0 with\n"
            "      | true => .unsupported\n"
            "      | false =>\n"
            "        match Nat.ble numBits b with\n"
            "        | true => .ub\n"
            "        | false => .ok (.scalar ⟨shiftLeftBits a b modulus, sz⟩) locals mem"
        ),
        replacement=(
            "    | .shlUnchecked =>\n"
            "      match Nat.beq rhs.sizeBytes 0 with\n"
            "      | true => .unsupported\n"
            "      | false =>\n"
            "        match Nat.blt numBits b with\n"
            "        | true => .ub\n"
            "        | false => .ok (.scalar ⟨shiftLeftBits a b modulus, sz⟩) locals mem"
        ),
        sanity_theorem_name="sanity_shl_oob_off_by_one",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem sanity_shl_oob_off_by_one :\n"
            "    evalScalarBinOp .shlUnchecked ⟨1, 1⟩ ⟨7, 1⟩ .nil emptyMemory false =\n"
            "      .ok (.scalar ⟨128, 1⟩) .nil emptyMemory :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_shl_oob_off_by_one",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem refute_shl_oob_off_by_one :\n"
            "    evalScalarBinOp .shlUnchecked ⟨1, 1⟩ ⟨8, 1⟩ .nil emptyMemory false = .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    MirSemanticsGuard(
        guard_id="shr_oob_off_by_one",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        description="evalScalarBinOp .shrUnchecked rejects shift distance == bit width (off-by-one boundary)",
        anchor=(
            "    | .shrUnchecked =>\n"
            "      match Nat.beq rhs.sizeBytes 0 with\n"
            "      | true => .unsupported\n"
            "      | false =>\n"
            "        match Nat.ble numBits b with\n"
            "        | true => .ub\n"
            "        | false =>\n"
            "          let shifted :="
        ),
        replacement=(
            "    | .shrUnchecked =>\n"
            "      match Nat.beq rhs.sizeBytes 0 with\n"
            "      | true => .unsupported\n"
            "      | false =>\n"
            "        match Nat.blt numBits b with\n"
            "        | true => .ub\n"
            "        | false =>\n"
            "          let shifted :="
        ),
        sanity_theorem_name="sanity_shr_oob_off_by_one",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem sanity_shr_oob_off_by_one :\n"
            "    evalScalarBinOp .shrUnchecked ⟨128, 1⟩ ⟨7, 1⟩ .nil emptyMemory false =\n"
            "      .ok (.scalar ⟨1, 1⟩) .nil emptyMemory :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_shr_oob_off_by_one",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem refute_shr_oob_off_by_one :\n"
            "    evalScalarBinOp .shrUnchecked ⟨16, 1⟩ ⟨8, 1⟩ .nil emptyMemory false = .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    MirSemanticsGuard(
        guard_id="bool_valid_range",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Scalars",
        description="evalUnaryNot on .bool rejects invalid bit patterns outside {0, 1} as UB",
        anchor=(
            "    match ty.kind with\n"
            "    | .bool =>\n"
            "      match Nat.beq sc.sizeBytes 1 with\n"
            "      | false => .ub\n"
            "      | true =>\n"
            "        match Nat.beq sc.bits 0 with\n"
            "        | true => .ok (.scalar ⟨1, 1⟩) locals mem\n"
            "        | false =>\n"
            "          match Nat.beq sc.bits 1 with\n"
            "          | true => .ok (.scalar ⟨0, 1⟩) locals mem\n"
            "          | false => .ub"
        ),
        replacement=(
            "    match ty.kind with\n"
            "    | .bool =>\n"
            "      match Nat.beq sc.sizeBytes 1 with\n"
            "      | false => .ub\n"
            "      | true =>\n"
            "        match Nat.beq sc.bits 0 with\n"
            "        | true => .ok (.scalar ⟨1, 1⟩) locals mem\n"
            "        | false =>\n"
            "          match Nat.beq sc.bits 1 with\n"
            "          | true => .ok (.scalar ⟨0, 1⟩) locals mem\n"
            "          | false => .ok (.scalar ⟨0, 1⟩) locals mem"
        ),
        sanity_theorem_name="sanity_bool_valid_range",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem sanity_bool_valid_range :\n"
            "    evalUnaryNot ⟨1, 1⟩ (.some { kind := .bool, layoutIdx := 0 }) .nil emptyMemory =\n"
            "      .ok (.scalar ⟨0, 1⟩) .nil emptyMemory :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_bool_valid_range",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem refute_bool_valid_range :\n"
            "    evalUnaryNot ⟨2, 1⟩ (.some { kind := .bool, layoutIdx := 0 }) .nil emptyMemory = .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    # ------------------------------------------------------------------
    # Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean (3 UB guards)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="storage_dead_read",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Places",
        description="evalOperand .copy of a LocalSlot.dead local faults UB",
        anchor=(
            "    | .nil =>\n"
            "      match get? locals p.local_ with\n"
            "      | .some (.init rootVal) =>\n"
            "        match readProjectedValue locals rootVal .nil with\n"
            "        | .ok fieldVal => .ok fieldVal locals\n"
            "        | .ub => .ub\n"
            "        | .unsupported => .unsupported\n"
            "      | .some .uninit => .ub\n"
            "      | .some .dead => .ub\n"
            "      | .none => .ub"
        ),
        replacement=(
            "    | .nil =>\n"
            "      match get? locals p.local_ with\n"
            "      | .some (.init rootVal) =>\n"
            "        match readProjectedValue locals rootVal .nil with\n"
            "        | .ok fieldVal => .ok fieldVal locals\n"
            "        | .ub => .ub\n"
            "        | .unsupported => .unsupported\n"
            "      | .some .uninit => .ub\n"
            "      | .some .dead => .ok .unit locals\n"
            "      | .none => .ub"
        ),
        sanity_theorem_name="sanity_storage_dead_read",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Places\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem sanity_storage_dead_read :\n"
            "    evalOperand\n"
            "      (.init (.scalar ⟨42, 4⟩) :: .nil)\n"
            "      (.copy { local_ := 0, projection := .nil }) =\n"
            "      .ok (.scalar ⟨42, 4⟩) (.init (.scalar ⟨42, 4⟩) :: .nil) :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_storage_dead_read",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Places\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem refute_storage_dead_read :\n"
            "    evalOperand\n"
            "      (.dead :: .nil)\n"
            "      (.copy { local_ := 0, projection := .nil }) = .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    MirSemanticsGuard(
        guard_id="storage_uninit_read",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Places",
        description="evalOperand .copy of a LocalSlot.uninit local faults UB",
        anchor=(
            "    | .nil =>\n"
            "      match get? locals p.local_ with\n"
            "      | .some (.init rootVal) =>\n"
            "        match readProjectedValue locals rootVal .nil with\n"
            "        | .ok fieldVal => .ok fieldVal locals\n"
            "        | .ub => .ub\n"
            "        | .unsupported => .unsupported\n"
            "      | .some .uninit => .ub\n"
            "      | .some .dead => .ub\n"
            "      | .none => .ub"
        ),
        replacement=(
            "    | .nil =>\n"
            "      match get? locals p.local_ with\n"
            "      | .some (.init rootVal) =>\n"
            "        match readProjectedValue locals rootVal .nil with\n"
            "        | .ok fieldVal => .ok fieldVal locals\n"
            "        | .ub => .ub\n"
            "        | .unsupported => .unsupported\n"
            "      | .some .uninit => .ok .unit locals\n"
            "      | .some .dead => .ub\n"
            "      | .none => .ub"
        ),
        sanity_theorem_name="sanity_storage_uninit_read",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Places\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem sanity_storage_uninit_read :\n"
            "    evalOperand\n"
            "      (.init (.scalar ⟨99, 4⟩) :: .nil)\n"
            "      (.copy { local_ := 0, projection := .nil }) =\n"
            "      .ok (.scalar ⟨99, 4⟩) (.init (.scalar ⟨99, 4⟩) :: .nil) :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_storage_uninit_read",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Places\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "theorem refute_storage_uninit_read :\n"
            "    evalOperand\n"
            "      (.uninit :: .nil)\n"
            "      (.copy { local_ := 0, projection := .nil }) = .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    MirSemanticsGuard(
        guard_id="unaligned_deref",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Places",
        description="checkDerefAlign rejects misaligned non-zero pointer dereference as UB",
        anchor=(
            "def checkDerefAlign\n"
            "    (localDecls : List LocalDecl)\n"
            "    (layouts : LayoutTable)\n"
            "    (tyOpt : Option Ty)\n"
            "    (offsetBytes : Nat) :\n"
            "    Bool :=\n"
            "  match Nat.beq offsetBytes 0 with\n"
            "  | true => true\n"
            "  | false =>\n"
            "    match tyOpt with\n"
            "    | .none => true\n"
            "    | .some ty =>\n"
            "      let align := tyByteAlign localDecls layouts ty\n"
            "      match Nat.ble align 1 with\n"
            "      | true => true\n"
            "      | false =>\n"
            "        let (_, rem) := divModBytesAux offsetBytes offsetBytes align 0\n"
            "        Nat.beq rem 0"
        ),
        replacement=(
            "def checkDerefAlign\n"
            "    (localDecls : List LocalDecl)\n"
            "    (layouts : LayoutTable)\n"
            "    (tyOpt : Option Ty)\n"
            "    (offsetBytes : Nat) :\n"
            "    Bool :=\n"
            "  match Nat.beq offsetBytes 0 with\n"
            "  | true => true\n"
            "  | false =>\n"
            "    match tyOpt with\n"
            "    | .none => true\n"
            "    | .some ty =>\n"
            "      let align := tyByteAlign localDecls layouts ty\n"
            "      match Nat.ble align 1 with\n"
            "      | true => true\n"
            "      | false =>\n"
            "        let (_, _rem) := divModBytesAux offsetBytes offsetBytes align 0\n"
            "        true"
        ),
        sanity_theorem_name="sanity_unaligned_deref",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Places\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def alignedLocals : List LocalSlot :=\n"
            "  .init (.ptr ⟨1, 2⟩ 8) :: .init (.scalar ⟨0, 4⟩) :: .nil\n"
            "\n"
            "def ptrBorrow : List BorrowEntry :=\n"
            "  { tag := 1, targetLocal := 1, targetProjection := .nil, perm := .frozen } :: .nil\n"
            "\n"
            "def u16PtrDecls : List LocalDecl :=\n"
            "  { mutability := .not\n"
            "    ty := { kind := .rawPtr .not (.uint .u16), layoutIdx := 0 }\n"
            "    debugName := .none } :: .nil\n"
            "\n"
            "theorem sanity_unaligned_deref :\n"
            "    evalOperand\n"
            "      alignedLocals\n"
            "      (.copy { local_ := 0, projection := .deref :: .nil })\n"
            "      ptrBorrow\n"
            "      .nil\n"
            "      emptyLayoutTable\n"
            "      .nil\n"
            "      u16PtrDecls\n"
            "      .nil =\n"
            "      .ok (.scalar ⟨0, 2⟩) alignedLocals :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_unaligned_deref",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Places\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def misalignedLocals : List LocalSlot :=\n"
            "  .init (.ptr ⟨1, 1⟩ 8) :: .init (.scalar ⟨0, 4⟩) :: .nil\n"
            "\n"
            "def ptrBorrow : List BorrowEntry :=\n"
            "  { tag := 1, targetLocal := 1, targetProjection := .nil, perm := .frozen } :: .nil\n"
            "\n"
            "def u16PtrDecls : List LocalDecl :=\n"
            "  { mutability := .not\n"
            "    ty := { kind := .rawPtr .not (.uint .u16), layoutIdx := 0 }\n"
            "    debugName := .none } :: .nil\n"
            "\n"
            "theorem refute_unaligned_deref :\n"
            "    evalOperand\n"
            "      misalignedLocals\n"
            "      (.copy { local_ := 0, projection := .deref :: .nil })\n"
            "      ptrBorrow\n"
            "      .nil\n"
            "      emptyLayoutTable\n"
            "      .nil\n"
            "      u16PtrDecls\n"
            "      .nil = .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    # ------------------------------------------------------------------
    # Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean (6 UB guards)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="intrinsic_assume_false",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Statements",
        description="evalStmt .intrinsic (.assume op) rejects false operand as UB",
        anchor=(
            "  | .intrinsic (.assume op) =>\n"
            "    match\n"
            "      evalOperand\n"
            "        s.frame.locals\n"
            "        op\n"
            "        s.memory.borrows\n"
            "        s.memory.globals\n"
            "        layouts\n"
            "        s.memory.callerLocals\n"
            "        localDecls\n"
            "        s.memory.callStack\n"
            "    with\n"
            "    | .ok (.scalar sc) locals' =>\n"
            "      match Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with\n"
            "      | true => MirStepNode.step (advanceStmt s locals')\n"
            "      | false => MirStepNode.fail .ub"
        ),
        replacement=(
            "  | .intrinsic (.assume op) =>\n"
            "    match\n"
            "      evalOperand\n"
            "        s.frame.locals\n"
            "        op\n"
            "        s.memory.borrows\n"
            "        s.memory.globals\n"
            "        layouts\n"
            "        s.memory.callerLocals\n"
            "        localDecls\n"
            "        s.memory.callStack\n"
            "    with\n"
            "    | .ok (.scalar _sc) locals' =>\n"
            "      match true with\n"
            "      | true => MirStepNode.step (advanceStmt s locals')\n"
            "      | false => MirStepNode.fail .ub"
        ),
        sanity_theorem_name="sanity_intrinsic_assume_false",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def trueState : MachineState :=\n"
            "  { frame := { blockIdx := 0, stmtIdx := 0, locals := .init (.scalar ⟨1, 1⟩) :: .nil }\n"
            "    memory := emptyMemory }\n"
            "\n"
            "def assumeStmt : Statement :=\n"
            "  { kind := .intrinsic (.assume (.copy { local_ := 0, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem sanity_intrinsic_assume_false :\n"
            "    evalStmt trueState assumeStmt =\n"
            "      MirStepNode.step\n"
            "        { frame := { blockIdx := 0, stmtIdx := 1, locals := .init (.scalar ⟨1, 1⟩) :: .nil }\n"
            "          memory := emptyMemory } :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_intrinsic_assume_false",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def falseState : MachineState :=\n"
            "  { frame := { blockIdx := 0, stmtIdx := 0, locals := .init (.scalar ⟨0, 1⟩) :: .nil }\n"
            "    memory := emptyMemory }\n"
            "\n"
            "def assumeStmt : Statement :=\n"
            "  { kind := .intrinsic (.assume (.copy { local_ := 0, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem refute_intrinsic_assume_false :\n"
            "    evalStmt falseState assumeStmt = MirStepNode.fail .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        quick=True,
    ),
    MirSemanticsGuard(
        guard_id="intrinsic_assume_invalid_bool",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Statements",
        description="evalStmt .intrinsic (.assume op) rejects invalid non-bool bit pattern (2) as UB",
        anchor=(
            "  | .intrinsic (.assume op) =>\n"
            "    match\n"
            "      evalOperand\n"
            "        s.frame.locals\n"
            "        op\n"
            "        s.memory.borrows\n"
            "        s.memory.globals\n"
            "        layouts\n"
            "        s.memory.callerLocals\n"
            "        localDecls\n"
            "        s.memory.callStack\n"
            "    with\n"
            "    | .ok (.scalar sc) locals' =>\n"
            "      match Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with\n"
            "      | true => MirStepNode.step (advanceStmt s locals')\n"
            "      | false => MirStepNode.fail .ub"
        ),
        replacement=(
            "  | .intrinsic (.assume op) =>\n"
            "    match\n"
            "      evalOperand\n"
            "        s.frame.locals\n"
            "        op\n"
            "        s.memory.borrows\n"
            "        s.memory.globals\n"
            "        layouts\n"
            "        s.memory.callerLocals\n"
            "        localDecls\n"
            "        s.memory.callStack\n"
            "    with\n"
            "    | .ok (.scalar sc) locals' =>\n"
            "      match Bool.and (Nat.beq sc.sizeBytes 1) (Bool.not (Nat.beq sc.bits 0)) with\n"
            "      | true => MirStepNode.step (advanceStmt s locals')\n"
            "      | false => MirStepNode.fail .ub"
        ),
        sanity_theorem_name="sanity_intrinsic_assume_invalid_bool",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def trueState : MachineState :=\n"
            "  { frame := { blockIdx := 0, stmtIdx := 0, locals := .init (.scalar ⟨1, 1⟩) :: .nil }\n"
            "    memory := emptyMemory }\n"
            "\n"
            "def assumeStmt : Statement :=\n"
            "  { kind := .intrinsic (.assume (.copy { local_ := 0, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem sanity_intrinsic_assume_invalid_bool :\n"
            "    evalStmt trueState assumeStmt =\n"
            "      MirStepNode.step\n"
            "        { frame := { blockIdx := 0, stmtIdx := 1, locals := .init (.scalar ⟨1, 1⟩) :: .nil }\n"
            "          memory := emptyMemory } :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_intrinsic_assume_invalid_bool",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def invalidBoolState : MachineState :=\n"
            "  { frame := { blockIdx := 0, stmtIdx := 0, locals := .init (.scalar ⟨2, 1⟩) :: .nil }\n"
            "    memory := emptyMemory }\n"
            "\n"
            "def assumeStmt : Statement :=\n"
            "  { kind := .intrinsic (.assume (.copy { local_ := 0, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem refute_intrinsic_assume_invalid_bool :\n"
            "    evalStmt invalidBoolState assumeStmt = MirStepNode.fail .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    MirSemanticsGuard(
        guard_id="intrinsic_assume_non_bool_size",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Statements",
        description="evalStmt .intrinsic (.assume op) rejects a scalar that is not 1 byte wide as UB",
        anchor=(
            "  | .intrinsic (.assume op) =>\n"
            "    match\n"
            "      evalOperand\n"
            "        s.frame.locals\n"
            "        op\n"
            "        s.memory.borrows\n"
            "        s.memory.globals\n"
            "        layouts\n"
            "        s.memory.callerLocals\n"
            "        localDecls\n"
            "        s.memory.callStack\n"
            "    with\n"
            "    | .ok (.scalar sc) locals' =>\n"
            "      match Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with\n"
            "      | true => MirStepNode.step (advanceStmt s locals')\n"
            "      | false => MirStepNode.fail .ub"
        ),
        replacement=(
            "  | .intrinsic (.assume op) =>\n"
            "    match\n"
            "      evalOperand\n"
            "        s.frame.locals\n"
            "        op\n"
            "        s.memory.borrows\n"
            "        s.memory.globals\n"
            "        layouts\n"
            "        s.memory.callerLocals\n"
            "        localDecls\n"
            "        s.memory.callStack\n"
            "    with\n"
            "    | .ok (.scalar sc) locals' =>\n"
            "      match Nat.beq sc.bits 1 with\n"
            "      | true => MirStepNode.step (advanceStmt s locals')\n"
            "      | false => MirStepNode.fail .ub"
        ),
        sanity_theorem_name="sanity_intrinsic_assume_non_bool_size",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def trueState : MachineState :=\n"
            "  { frame := { blockIdx := 0, stmtIdx := 0, locals := .init (.scalar ⟨1, 1⟩) :: .nil }\n"
            "    memory := emptyMemory }\n"
            "\n"
            "def assumeStmt : Statement :=\n"
            "  { kind := .intrinsic (.assume (.copy { local_ := 0, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem sanity_intrinsic_assume_non_bool_size :\n"
            "    evalStmt trueState assumeStmt =\n"
            "      MirStepNode.step\n"
            "        { frame := { blockIdx := 0, stmtIdx := 1, locals := .init (.scalar ⟨1, 1⟩) :: .nil }\n"
            "          memory := emptyMemory } :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_intrinsic_assume_non_bool_size",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def wideOneState : MachineState :=\n"
            "  { frame := { blockIdx := 0, stmtIdx := 0, locals := .init (.scalar ⟨1, 4⟩) :: .nil }\n"
            "    memory := emptyMemory }\n"
            "\n"
            "def assumeStmt : Statement :=\n"
            "  { kind := .intrinsic (.assume (.copy { local_ := 0, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem refute_intrinsic_assume_non_bool_size :\n"
            "    evalStmt wideOneState assumeStmt = MirStepNode.fail .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    MirSemanticsGuard(
        guard_id="copy_nonoverlapping_overlap",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Statements",
        description="evalCopySingleDirect rejects overlapping copy_nonoverlapping ranges as UB",
        anchor=(
            "  let overlaps :=\n"
            "    match Nat.beq srcPtr.tag dstPtr.tag with\n"
            "    | true => true\n"
            "    | false =>\n"
            "      match\n"
            "        Nat.beq srcEntry.targetLocal dstEntry.targetLocal\n"
            "      with\n"
            "      | false => false\n"
            "      | true =>\n"
            "        projectionsOverlap\n"
            "          srcEntry.targetProjection\n"
            "          dstEntry.targetProjection\n"
            "  match overlaps with\n"
            "  | true => MirStepNode.fail .ub\n"
            "  | false =>\n"
            "    let srcRootSlot : Option LocalSlot :="
        ),
        replacement=(
            "  let _overlaps :=\n"
            "    match Nat.beq srcPtr.tag dstPtr.tag with\n"
            "    | true => true\n"
            "    | false =>\n"
            "      match\n"
            "        Nat.beq srcEntry.targetLocal dstEntry.targetLocal\n"
            "      with\n"
            "      | false => false\n"
            "      | true =>\n"
            "        projectionsOverlap\n"
            "          srcEntry.targetProjection\n"
            "          dstEntry.targetProjection\n"
            "  match false with\n"
            "  | true => MirStepNode.fail .ub\n"
            "  | false =>\n"
            "    let srcRootSlot : Option LocalSlot :="
        ),
        sanity_theorem_name="sanity_copy_nonoverlapping_overlap",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def srcBorrow : BorrowEntry :=\n"
            "  { tag := 1, targetLocal := 0, targetProjection := .nil, perm := .unique }\n"
            "\n"
            "def dstBorrow : BorrowEntry :=\n"
            "  { tag := 2, targetLocal := 1, targetProjection := .nil, perm := .unique }\n"
            "\n"
            "def disjointMem : Memory :=\n"
            "  { emptyMemory with borrows := srcBorrow :: dstBorrow :: .nil }\n"
            "\n"
            "def disjointInitLocals : List LocalSlot :=\n"
            "  .init (.scalar ⟨42, 4⟩) ::\n"
            "  .init (.scalar ⟨99, 4⟩) ::\n"
            "  .init (.ptr ⟨1, 0⟩ 8) ::\n"
            "  .init (.ptr ⟨2, 0⟩ 8) ::\n"
            "  .init (.scalar ⟨1, 8⟩) :: .nil\n"
            "\n"
            "def disjointAfterLocals : List LocalSlot :=\n"
            "  .init (.scalar ⟨42, 4⟩) ::\n"
            "  .init (.scalar ⟨42, 4⟩) ::\n"
            "  .init (.ptr ⟨1, 0⟩ 8) ::\n"
            "  .init (.ptr ⟨2, 0⟩ 8) ::\n"
            "  .init (.scalar ⟨1, 8⟩) :: .nil\n"
            "\n"
            "def disjointCopyStmt : Statement :=\n"
            "  { kind := .intrinsic\n"
            "      (.copyNonOverlapping\n"
            "        (.copy { local_ := 2, projection := .nil })\n"
            "        (.copy { local_ := 3, projection := .nil })\n"
            "        (.copy { local_ := 4, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem sanity_copy_nonoverlapping_overlap :\n"
            "    evalStmt\n"
            "      { frame := { blockIdx := 0, stmtIdx := 0, locals := disjointInitLocals }\n"
            "        memory := disjointMem }\n"
            "      disjointCopyStmt =\n"
            "      MirStepNode.step\n"
            "        { frame := { blockIdx := 0, stmtIdx := 1, locals := disjointAfterLocals }\n"
            "          memory := disjointMem } :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_copy_nonoverlapping_overlap",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def overlapBorrow : BorrowEntry :=\n"
            "  { tag := 1, targetLocal := 0, targetProjection := .nil, perm := .unique }\n"
            "\n"
            "def overlapState : MachineState :=\n"
            "  { frame :=\n"
            "      { blockIdx := 0\n"
            "        stmtIdx := 0\n"
            "        locals :=\n"
            "          .init (.scalar ⟨42, 4⟩) ::\n"
            "          .init (.ptr ⟨1, 0⟩ 8) ::\n"
            "          .init (.scalar ⟨1, 8⟩) :: .nil }\n"
            "    memory := { emptyMemory with borrows := overlapBorrow :: .nil } }\n"
            "\n"
            "def overlapCopyStmt : Statement :=\n"
            "  { kind := .intrinsic\n"
            "      (.copyNonOverlapping\n"
            "        (.copy { local_ := 1, projection := .nil })\n"
            "        (.copy { local_ := 1, projection := .nil })\n"
            "        (.copy { local_ := 2, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem refute_copy_nonoverlapping_overlap :\n"
            "    evalStmt overlapState overlapCopyStmt = MirStepNode.fail .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    MirSemanticsGuard(
        guard_id="copy_nonoverlapping_place_overlap",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Statements",
        description="evalCopySingleDirect rejects distinct-tag pointers targeting overlapping places as UB",
        anchor=(
            "  let overlaps :=\n"
            "    match Nat.beq srcPtr.tag dstPtr.tag with\n"
            "    | true => true\n"
            "    | false =>\n"
            "      match\n"
            "        Nat.beq srcEntry.targetLocal dstEntry.targetLocal\n"
            "      with\n"
            "      | false => false\n"
            "      | true =>\n"
            "        projectionsOverlap\n"
            "          srcEntry.targetProjection\n"
            "          dstEntry.targetProjection\n"
            "  match overlaps with\n"
            "  | true => MirStepNode.fail .ub\n"
            "  | false =>\n"
            "    let srcRootSlot : Option LocalSlot :="
        ),
        replacement=(
            "  let overlaps :=\n"
            "    match Nat.beq srcPtr.tag dstPtr.tag with\n"
            "    | true => true\n"
            "    | false => false\n"
            "  match overlaps with\n"
            "  | true => MirStepNode.fail .ub\n"
            "  | false =>\n"
            "    let srcRootSlot : Option LocalSlot :="
        ),
        sanity_theorem_name="sanity_copy_nonoverlapping_place_overlap",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def srcBorrow : BorrowEntry :=\n"
            "  { tag := 1, targetLocal := 0, targetProjection := .nil, perm := .unique }\n"
            "\n"
            "def dstBorrow : BorrowEntry :=\n"
            "  { tag := 2, targetLocal := 1, targetProjection := .nil, perm := .unique }\n"
            "\n"
            "def disjointMem : Memory :=\n"
            "  { emptyMemory with borrows := srcBorrow :: dstBorrow :: .nil }\n"
            "\n"
            "def disjointInitLocals : List LocalSlot :=\n"
            "  .init (.scalar ⟨42, 4⟩) ::\n"
            "  .init (.scalar ⟨99, 4⟩) ::\n"
            "  .init (.ptr ⟨1, 0⟩ 8) ::\n"
            "  .init (.ptr ⟨2, 0⟩ 8) ::\n"
            "  .init (.scalar ⟨1, 8⟩) :: .nil\n"
            "\n"
            "def disjointAfterLocals : List LocalSlot :=\n"
            "  .init (.scalar ⟨42, 4⟩) ::\n"
            "  .init (.scalar ⟨42, 4⟩) ::\n"
            "  .init (.ptr ⟨1, 0⟩ 8) ::\n"
            "  .init (.ptr ⟨2, 0⟩ 8) ::\n"
            "  .init (.scalar ⟨1, 8⟩) :: .nil\n"
            "\n"
            "def disjointCopyStmt : Statement :=\n"
            "  { kind := .intrinsic\n"
            "      (.copyNonOverlapping\n"
            "        (.copy { local_ := 2, projection := .nil })\n"
            "        (.copy { local_ := 3, projection := .nil })\n"
            "        (.copy { local_ := 4, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem sanity_copy_nonoverlapping_place_overlap :\n"
            "    evalStmt\n"
            "      { frame := { blockIdx := 0, stmtIdx := 0, locals := disjointInitLocals }\n"
            "        memory := disjointMem }\n"
            "      disjointCopyStmt =\n"
            "      MirStepNode.step\n"
            "        { frame := { blockIdx := 0, stmtIdx := 1, locals := disjointAfterLocals }\n"
            "          memory := disjointMem } :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_copy_nonoverlapping_place_overlap",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def aliasSrcBorrow : BorrowEntry :=\n"
            "  { tag := 1, targetLocal := 0, targetProjection := .nil, perm := .unique }\n"
            "\n"
            "def aliasDstBorrow : BorrowEntry :=\n"
            "  { tag := 2, targetLocal := 0, targetProjection := .nil, perm := .unique }\n"
            "\n"
            "def aliasState : MachineState :=\n"
            "  { frame :=\n"
            "      { blockIdx := 0\n"
            "        stmtIdx := 0\n"
            "        locals :=\n"
            "          .init (.scalar ⟨42, 4⟩) ::\n"
            "          .init (.ptr ⟨1, 0⟩ 8) ::\n"
            "          .init (.ptr ⟨2, 0⟩ 8) ::\n"
            "          .init (.scalar ⟨1, 8⟩) :: .nil }\n"
            "    memory := { emptyMemory with borrows := aliasSrcBorrow :: aliasDstBorrow :: .nil } }\n"
            "\n"
            "def aliasCopyStmt : Statement :=\n"
            "  { kind := .intrinsic\n"
            "      (.copyNonOverlapping\n"
            "        (.copy { local_ := 1, projection := .nil })\n"
            "        (.copy { local_ := 2, projection := .nil })\n"
            "        (.copy { local_ := 3, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem refute_copy_nonoverlapping_place_overlap :\n"
            "    evalStmt aliasState aliasCopyStmt = MirStepNode.fail .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    MirSemanticsGuard(
        guard_id="copy_nonoverlapping_subplace_overlap",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Statements",
        description="evalCopySingleDirect rejects a sub-place (field of a local vs the whole local) overlap as UB",
        anchor=(
            "  let overlaps :=\n"
            "    match Nat.beq srcPtr.tag dstPtr.tag with\n"
            "    | true => true\n"
            "    | false =>\n"
            "      match\n"
            "        Nat.beq srcEntry.targetLocal dstEntry.targetLocal\n"
            "      with\n"
            "      | false => false\n"
            "      | true =>\n"
            "        projectionsOverlap\n"
            "          srcEntry.targetProjection\n"
            "          dstEntry.targetProjection\n"
            "  match overlaps with\n"
            "  | true => MirStepNode.fail .ub\n"
            "  | false =>\n"
            "    let srcRootSlot : Option LocalSlot :="
        ),
        replacement=(
            "  let overlaps :=\n"
            "    match Nat.beq srcPtr.tag dstPtr.tag with\n"
            "    | true => true\n"
            "    | false =>\n"
            "      match\n"
            "        Nat.beq srcEntry.targetLocal dstEntry.targetLocal\n"
            "      with\n"
            "      | false => false\n"
            "      | true =>\n"
            "        match srcEntry.targetProjection, dstEntry.targetProjection with\n"
            "        | .nil, .nil => true\n"
            "        | _, _ => false\n"
            "  match overlaps with\n"
            "  | true => MirStepNode.fail .ub\n"
            "  | false =>\n"
            "    let srcRootSlot : Option LocalSlot :="
        ),
        sanity_theorem_name="sanity_copy_nonoverlapping_subplace_overlap",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def srcBorrow : BorrowEntry :=\n"
            "  { tag := 1, targetLocal := 0, targetProjection := .nil, perm := .unique }\n"
            "\n"
            "def dstBorrow : BorrowEntry :=\n"
            "  { tag := 2, targetLocal := 1, targetProjection := .nil, perm := .unique }\n"
            "\n"
            "def disjointMem : Memory :=\n"
            "  { emptyMemory with borrows := srcBorrow :: dstBorrow :: .nil }\n"
            "\n"
            "def disjointInitLocals : List LocalSlot :=\n"
            "  .init (.scalar ⟨42, 4⟩) ::\n"
            "  .init (.scalar ⟨99, 4⟩) ::\n"
            "  .init (.ptr ⟨1, 0⟩ 8) ::\n"
            "  .init (.ptr ⟨2, 0⟩ 8) ::\n"
            "  .init (.scalar ⟨1, 8⟩) :: .nil\n"
            "\n"
            "def disjointAfterLocals : List LocalSlot :=\n"
            "  .init (.scalar ⟨42, 4⟩) ::\n"
            "  .init (.scalar ⟨42, 4⟩) ::\n"
            "  .init (.ptr ⟨1, 0⟩ 8) ::\n"
            "  .init (.ptr ⟨2, 0⟩ 8) ::\n"
            "  .init (.scalar ⟨1, 8⟩) :: .nil\n"
            "\n"
            "def disjointCopyStmt : Statement :=\n"
            "  { kind := .intrinsic\n"
            "      (.copyNonOverlapping\n"
            "        (.copy { local_ := 2, projection := .nil })\n"
            "        (.copy { local_ := 3, projection := .nil })\n"
            "        (.copy { local_ := 4, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem sanity_copy_nonoverlapping_subplace_overlap :\n"
            "    evalStmt\n"
            "      { frame := { blockIdx := 0, stmtIdx := 0, locals := disjointInitLocals }\n"
            "        memory := disjointMem }\n"
            "      disjointCopyStmt =\n"
            "      MirStepNode.step\n"
            "        { frame := { blockIdx := 0, stmtIdx := 1, locals := disjointAfterLocals }\n"
            "          memory := disjointMem } :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_copy_nonoverlapping_subplace_overlap",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Statements\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def fieldZero : ProjectionElem :=\n"
            "  .field 0 { kind := .uint .u32, layoutIdx := 0 }\n"
            "\n"
            "def fieldSrcBorrow : BorrowEntry :=\n"
            "  { tag := 1, targetLocal := 0, targetProjection := fieldZero :: .nil, perm := .unique }\n"
            "\n"
            "def wholeDstBorrow : BorrowEntry :=\n"
            "  { tag := 2, targetLocal := 0, targetProjection := .nil, perm := .unique }\n"
            "\n"
            "def subplaceState : MachineState :=\n"
            "  { frame :=\n"
            "      { blockIdx := 0\n"
            "        stmtIdx := 0\n"
            "        locals :=\n"
            "          .init (.scalar ⟨42, 4⟩) ::\n"
            "          .init (.ptr ⟨1, 0⟩ 8) ::\n"
            "          .init (.ptr ⟨2, 0⟩ 8) ::\n"
            "          .init (.scalar ⟨1, 8⟩) :: .nil }\n"
            "    memory := { emptyMemory with borrows := fieldSrcBorrow :: wholeDstBorrow :: .nil } }\n"
            "\n"
            "def subplaceCopyStmt : Statement :=\n"
            "  { kind := .intrinsic\n"
            "      (.copyNonOverlapping\n"
            "        (.copy { local_ := 1, projection := .nil })\n"
            "        (.copy { local_ := 2, projection := .nil })\n"
            "        (.copy { local_ := 3, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem refute_copy_nonoverlapping_subplace_overlap :\n"
            "    evalStmt subplaceState subplaceCopyStmt = MirStepNode.fail .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
    # ------------------------------------------------------------------
    # Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean (2 UB guards)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="tb_drop_protector_conflict",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Terminators",
        description="evalTerminator .drop rejects dropping a local with an active protector conflict as UB",
        anchor=(
            "          | protHead :: protTail =>\n"
            "            match\n"
            "              hasProtectedWriteConflict\n"
            "                s.memory.borrows\n"
            "                (protHead :: protTail)\n"
            "                place.local_\n"
            "                .none\n"
            "                .nil\n"
            "                0\n"
            "                0\n"
            "                depth\n"
            "            with\n"
            "            | true => MirStepNode.fail .ub\n"
            "            | false =>\n"
            "              let borrows' :=\n"
            "                invalidateConflictingBorrows s.memory.borrows place.local_ .none depth"
        ),
        replacement=(
            "          | _protHead :: _protTail =>\n"
            "            match false with\n"
            "            | true => MirStepNode.fail .ub\n"
            "            | false =>\n"
            "              let borrows' :=\n"
            "                invalidateConflictingBorrows s.memory.borrows place.local_ .none depth"
        ),
        sanity_theorem_name="sanity_tb_drop_protector_conflict",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def otherLocalBorrow : BorrowEntry :=\n"
            "  { tag := 1\n"
            "    targetLocal := 1\n"
            "    targetProjection := .nil\n"
            "    perm := .unique\n"
            "    protector := .some 1 }\n"
            "\n"
            "def protectedOtherMem : Memory :=\n"
            "  { emptyMemory with\n"
            "    borrows := otherLocalBorrow :: .nil\n"
            "    activeProtectors := 1 :: .nil }\n"
            "\n"
            "def dropZeroTerm : Terminator :=\n"
            "  { kind := .drop { local_ := 0, projection := .nil } 1 .continue_\n"
            "    span := \"\" }\n"
            "\n"
            "theorem sanity_tb_drop_protector_conflict :\n"
            "    evalTerminator\n"
            "      { frame :=\n"
            "          { blockIdx := 0\n"
            "            stmtIdx := 0\n"
            "            locals := .init (.scalar ⟨1, 4⟩) :: .init (.scalar ⟨2, 4⟩) :: .nil }\n"
            "        memory := protectedOtherMem }\n"
            "      dropZeroTerm =\n"
            "      MirStepNode.step\n"
            "        { frame :=\n"
            "            { blockIdx := 1\n"
            "              stmtIdx := 0\n"
            "              locals := .uninit :: .init (.scalar ⟨2, 4⟩) :: .nil }\n"
            "          memory := protectedOtherMem } :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_tb_drop_protector_conflict",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def protectedLocalZeroBorrow : BorrowEntry :=\n"
            "  { tag := 1\n"
            "    targetLocal := 0\n"
            "    targetProjection := .nil\n"
            "    perm := .unique\n"
            "    protector := .some 1 }\n"
            "\n"
            "def dropZeroState : MachineState :=\n"
            "  { frame :=\n"
            "      { blockIdx := 0\n"
            "        stmtIdx := 0\n"
            "        locals := .init (.scalar ⟨1, 4⟩) :: .nil }\n"
            "    memory :=\n"
            "      { emptyMemory with\n"
            "        borrows := protectedLocalZeroBorrow :: .nil\n"
            "        activeProtectors := 1 :: .nil } }\n"
            "\n"
            "def dropZeroTerm : Terminator :=\n"
            "  { kind := .drop { local_ := 0, projection := .nil } 1 .continue_\n"
            "    span := \"\" }\n"
            "\n"
            "theorem refute_tb_drop_protector_conflict :\n"
            "    evalTerminator dropZeroState dropZeroTerm = MirStepNode.fail .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        quick=True,
    ),
    MirSemanticsGuard(
        guard_id="tb_return_frame_dealloc_protector_conflict",
        target_file="trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean",
        target_module="Trusted/Rustc/V2026_06_01/MirSemantics/Terminators",
        description="evalTerminator .return_ rejects frame deallocation under an active protector as UB",
        anchor=(
            "  | .return_ =>\n"
            "    match get? s.frame.locals 0 with\n"
            "    | .some (.init retVal) =>\n"
            "      let depth := length s.memory.callStack\n"
            "      let nLocals := length s.frame.locals\n"
            "      match\n"
            "        hasFrameDeallocProtectorConflict\n"
            "          s.memory.borrows\n"
            "          s.memory.activeProtectors\n"
            "          depth\n"
            "          nLocals\n"
            "      with\n"
            "      | true => MirStepNode.fail .ub\n"
            "      | false =>"
        ),
        replacement=(
            "  | .return_ =>\n"
            "    match get? s.frame.locals 0 with\n"
            "    | .some (.init retVal) =>\n"
            "      let depth := length s.memory.callStack\n"
            "      let nLocals := length s.frame.locals\n"
            "      match false with\n"
            "      | true => MirStepNode.fail .ub\n"
            "      | false =>"
        ),
        sanity_theorem_name="sanity_tb_return_frame_dealloc_protector_conflict",
        sanity_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def callerProtectedBorrow : BorrowEntry :=\n"
            "  { tag := 1\n"
            "    targetLocal := 1\n"
            "    targetProjection := .nil\n"
            "    perm := .unique\n"
            "    protector := .some 1 }\n"
            "\n"
            "def retCleanMemory : Memory :=\n"
            "  { emptyMemory with\n"
            "    borrows := callerProtectedBorrow :: .nil\n"
            "    activeProtectors := 1 :: .nil }\n"
            "\n"
            "def retCleanState : MachineState :=\n"
            "  { frame :=\n"
            "      { blockIdx := 0\n"
            "        stmtIdx := 0\n"
            "        locals := .init (.scalar ⟨7, 4⟩) :: .nil }\n"
            "    memory := retCleanMemory }\n"
            "\n"
            "def retTerm : Terminator :=\n"
            "  { kind := .return_, span := \"\" }\n"
            "\n"
            "theorem sanity_tb_return_frame_dealloc_protector_conflict :\n"
            "    evalTerminator retCleanState retTerm =\n"
            "      MirStepNode.retNormal (.scalar ⟨7, 4⟩) retCleanMemory :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
        theorem_name="refute_tb_return_frame_dealloc_protector_conflict",
        refute_source=(
            "import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators\n"
            "\n"
            "namespace GuardMutation\n"
            "open Trusted.Effect\n"
            "open Trusted.Rustc.V2026_06_01.MirAst\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "\n"
            "def protectedRetBorrow : BorrowEntry :=\n"
            "  { tag := 1\n"
            "    targetLocal := 0\n"
            "    targetProjection := .nil\n"
            "    perm := .unique\n"
            "    protector := .some 1 }\n"
            "\n"
            "def retProtectedState : MachineState :=\n"
            "  { frame :=\n"
            "      { blockIdx := 0\n"
            "        stmtIdx := 0\n"
            "        locals := .init (.scalar ⟨7, 4⟩) :: .nil }\n"
            "    memory :=\n"
            "      { emptyMemory with\n"
            "        borrows := protectedRetBorrow :: .nil\n"
            "        activeProtectors := 1 :: .nil } }\n"
            "\n"
            "def retTerm : Terminator :=\n"
            "  { kind := .return_, span := \"\" }\n"
            "\n"
            "theorem refute_tb_return_frame_dealloc_protector_conflict :\n"
            "    evalTerminator retProtectedState retTerm = MirStepNode.fail .ub :=\n"
            "  rfl\n"
            "\n"
            "end GuardMutation\n"
        ),
    ),
)


def apply_single_guard_mutation(
    source_text: str,
    anchor: str,
    replacement: str,
    *,
    guard_id: str,
) -> str:
    """Replace `anchor` with `replacement`, requiring exactly one occurrence.

    Requiring a unique match ensures that refactoring a guarded expression in
    the TCB fails loudly rather than silently skipping the mutation or editing
    the wrong branch.
    """
    occurrences = source_text.count(anchor)
    if occurrences != 1:
        raise ValueError(
            f"guard {guard_id!r}: expected anchor to match exactly once, "
            f"found {occurrences} occurrences"
        )
    if anchor == replacement:
        raise ValueError(
            f"guard {guard_id!r}: replacement must differ from anchor"
        )
    return source_text.replace(anchor, replacement, 1)


def _scan_lean_source(lean_source: str) -> tuple[str, bool, list[str]]:
    """Separate Lean code from comments and report what cannot be lexed exactly.

    Returns `(code, has_unclosed_block_comment, hazards)`. `code` is
    `lean_source` with `--` and nested `/- ... -/` comments replaced by spaces;
    newlines are preserved, so 1-based line numbers still match.

    The scanner understands plain `"..."` string literals, simple character
    literals and identifier primes (`mem'`). It cannot know everything Lean
    knows. Whether a string is interpolated is decided by the parser that
    consumes it (`s!"{"/-"}"`, `dbg_trace "{...}"; e`), and raw strings
    (`r"\"`, `r#"a"b"#`) quote differently. Inside any of those the scanner
    and Lean disagree about where the string ends, so a real declaration can
    sit "inside a comment" for the scanner while Lean compiles it.

    `hazards` names every such construct with its 1-based line: a string
    literal containing `{` or a backslash, a `#"` raw string, an unterminated
    string, a character literal, a guillemet identifier, or a stray backslash.
    A source with no hazards is lexed exactly; callers that depend on `code`
    must refuse a source that has any.
    """
    out: list[str] = []
    hazards: list[str] = []
    n = len(lean_source)
    i = 0
    block_depth = 0

    def hazard(what: str, pos: int) -> None:
        hazards.append(f"line {lean_source.count(chr(10), 0, pos) + 1}: {what}")

    while i < n:
        ch = lean_source[i]
        if block_depth > 0:
            if lean_source[i : i + 2] == "/-":
                block_depth += 1
                out.append("  ")
                i += 2
            elif lean_source[i : i + 2] == "-/":
                block_depth -= 1
                out.append("  ")
                i += 2
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
            continue

        if ch == '"':
            start = i
            if i > 0 and lean_source[i - 1] == "#":
                hazard("raw string literal", start)
            out.append(ch)
            i += 1
            closed = False
            while i < n:
                c = lean_source[i]
                out.append(c)
                i += 1
                if c == "\\":
                    hazard("backslash inside a string literal", start)
                    if i < n:
                        out.append(lean_source[i])
                        i += 1
                elif c == "{":
                    hazard("`{` inside a string literal (possible interpolation)", start)
                elif c == '"':
                    closed = True
                    break
            if not closed:
                hazard("unterminated string literal", start)
            continue

        if ch == "'" and not (i > 0 and (lean_source[i - 1].isalnum() or lean_source[i - 1] in "_'")):
            hazard("character literal", i)
            if i + 2 < n and lean_source[i + 1] != "\\" and lean_source[i + 1] != "\n" and lean_source[i + 2] == "'":
                out.append(lean_source[i : i + 3])
                i += 3
                continue
            if i + 3 < n and lean_source[i + 1] == "\\" and lean_source[i + 3] == "'":
                out.append(lean_source[i : i + 4])
                i += 4
                continue

        if ch == "«":
            hazard("guillemet-quoted identifier", i)
            out.append(ch)
            i += 1
            while i < n:
                c = lean_source[i]
                out.append(c)
                i += 1
                if c == "»":
                    break
            continue

        if lean_source[i : i + 2] == "--":
            while i < n and lean_source[i] != "\n":
                out.append(" ")
                i += 1
            continue

        if lean_source[i : i + 2] == "/-":
            block_depth = 1
            out.append("  ")
            i += 2
            continue

        if ch == "\\":
            hazard("backslash outside a string literal", i)
        out.append(ch)
        i += 1

    return ("".join(out), block_depth > 0, hazards)


def _strip_lean_comments(lean_source: str) -> tuple[str, bool]:
    """Replace Lean `--` and nested `/- ... -/` comments with spaces.

    Returns `(stripped_text, has_unclosed_block_comment)`. The result is exact
    only for sources with no `_scan_lean_source` hazards.
    """
    code, unclosed, _ = _scan_lean_source(lean_source)
    return (code, unclosed)


def find_theorem_line_span(
    fixture_text: str,
    theorem_name: str,
) -> tuple[int, int]:
    """Return the inclusive 1-based `(start, end)` line span of `theorem_name`.

    Used to confirm that a Lean proof failure on a mutated semantics actually
    originated inside the guard's dedicated refutation theorem rather than in
    an unrelated declaration, helper definition, or file header.

    The span starts at the column-0 `theorem <name>` header (ignoring comments)
    and covers only the indented continuation lines that follow it. ANY later
    text at column 0 (`example`, `instance`, `#eval`, a comment, `end`, ...)
    ends the span, and trailing blank lines are excluded, so a failure in
    whatever follows the theorem can never be attributed to it.
    """
    lines = fixture_text.splitlines()
    code_only, _ = _strip_lean_comments(fixture_text)
    code_lines = code_only.splitlines()
    target_re = re.compile(
        rf"^(?:(?:private|protected)\s+)?theorem\s+{re.escape(theorem_name)}"
        r"(?![\w'.!?])"
    )
    starts = [idx for idx, line in enumerate(code_lines, start=1) if target_re.match(line)]
    if not starts:
        raise ValueError(
            f"theorem {theorem_name!r} not found in fixture source"
        )
    if len(starts) > 1:
        raise ValueError(
            f"theorem {theorem_name!r} declared {len(starts)} times in fixture source"
        )
    start = starts[0]
    end = start
    for idx in range(start + 1, len(lines) + 1):
        line = lines[idx - 1]
        if not line.strip():
            continue
        if line[0] not in " \t":
            break
        end = idx
    return (start, end)


# `<path>:<line>:<col>[-<line>:<col>]: <severity>[(<name>)]:` diagnostic header,
# as printed by `Lean.mkErrorStringWithPos`. Lean 4.34 prints named errors as
# `error(lean.someName):`, which must count as errors too.
_DIAG_HEADER_RE = re.compile(
    r"^(?P<path>.+?):(?P<line>\d+):(?P<col>\d+)(?:-\d+:\d+)?:\s*"
    r"(?P<sev>error|warning|info|information)(?:\([^)\n]*\))?:",
    re.MULTILINE,
)

# Any line announcing an error, with or without a source position
# (`error: toolchain ... is not installed`, `lean: error: ...`).
_ERROR_TOKEN_RE = re.compile(r"(?:^|[\s:])error(?:\([^)\n]*\))?:")

# An indented line whose FIRST non-whitespace token is `error:` or `error(...):`.
# Lean 4 diagnostic continuation bodies indent terms, types, goals, and notes
# (`  note: type error: ...`), never a bare leading `  error: ...`; rejecting
# these closes the loophole of an indented unlocated error on the same stream
# right after a located fixture diagnostic.
_INDENTED_LEADING_ERROR_RE = re.compile(r"^[ \t]+error(?:\([^)\n]*\))?:")


def _split_lf_lines_keepends(text: str) -> list[str]:
    """Split `text` strictly on `\\n` (preserving `\\n`), matching `re.MULTILINE` `^`."""
    if not text:
        return []
    parts = text.split("\n")
    lines = [f"{part}\n" for part in parts[:-1]]
    if parts[-1]:
        lines.append(parts[-1])
    return lines


def classify_refutation_failure(
    returncode: int,
    combined_output: str,
    fixture_filename: str,
    theorem_span: tuple[int, int],
    *,
    stderr_output: str | None = None,
) -> tuple[str, str]:
    """Classify Lean output on a mutated refutation fixture.

    `combined_output` is Lean's output. When `stderr_output` is given,
    `combined_output` is stdout only and the two streams are kept apart: a
    diagnostic printed on stdout never extends into stderr, so stderr text can
    neither supply a proof-failure marker nor hide an indented error line
    behind a stdout diagnostic.

    Returns `(status, detail)` where `status` is:
    - `SURVIVED`: Lean accepted (`rc == 0`) the negative refutation even after
      the guard was disabled.
    - `KILLED`: Lean rejected (`rc == 1`), every error diagnostic is located in
      `fixture_filename` inside the target theorem's line span, at least one of
      those diagnostics carries a proof/type-mismatch marker, and the output
      has no crash/parse/timeout marker.
    - `ERROR`: anything else (never counted as a kill): unexpected exit status
      (signals, OOM, timeout), crash/parse/timeout marker, an error diagnostic
      in another file or without a source position, an error outside the
      target theorem span, or no proof-failure marker inside the target
      theorem's own diagnostics.
    """
    if returncode == 0:
        return ("SURVIVED", "refutation theorem still compiled on mutant")
    if returncode != 1:
        return (
            "ERROR",
            f"unexpected Lean exit code {returncode} (expected 1 on proof failure)",
        )
    # Normalize CR/CRLF to LF before joining streams so `re.MULTILINE` `^` and
    # line iteration never desync on `\r` or Unicode line separators.
    combined_output = combined_output.replace("\r\n", "\n").replace("\r", "\n")
    # Offset at which stderr starts (always at the start of a line).
    stream_break: int | None = None
    if stderr_output is not None:
        stderr_norm = stderr_output.replace("\r\n", "\n").replace("\r", "\n")
        if combined_output and not combined_output.endswith("\n"):
            combined_output += "\n"
        stream_break = len(combined_output)
        combined_output += stderr_norm
    for marker in NON_KILL_ERROR_MARKERS:
        if marker in combined_output:
            return (
                "ERROR",
                f"non-proof failure marker {marker!r} in Lean output",
            )

    # Split the output into diagnostics: each header owns the text up to the
    # next header.
    headers = list(_DIAG_HEADER_RE.finditer(combined_output))
    header_by_start = {m.start(): m for m in headers}

    def _is_fixture(match: re.Match[str]) -> bool:
        return re.split(r"[/\\]", match.group("path"))[-1] == fixture_filename

    # Every located error diagnostic header must point into `fixture_filename`.
    for match in headers:
        if match.group("sev") == "error" and not _is_fixture(match):
            return (
                "ERROR",
                "error diagnostic not located in "
                f"{fixture_filename}: {match.group(0)!r}",
            )

    # Every line announcing an error must be a located error header in the
    # fixture itself, EXCEPT indented continuation lines inside the body of a
    # diagnostic already located in `fixture_filename` whose first non-space
    # token is NOT `error:` / `error(...):` (e.g., `  note: type error: ...`).
    # Errors in other files and unlocated errors (including indented leading
    # `  error: ...` on the same stream or on stderr) are never kills.
    pos = 0
    active_header: re.Match[str] | None = None
    for raw_line in _split_lf_lines_keepends(combined_output):
        if pos == stream_break:
            # A stdout diagnostic does not continue on stderr.
            active_header = None
        match = header_by_start.get(pos)
        if match is not None:
            active_header = match
        in_fixture_body = (
            match is None
            and active_header is not None
            and _is_fixture(active_header)
            and raw_line[:1].isspace()
            and _INDENTED_LEADING_ERROR_RE.match(raw_line) is None
        )
        if not in_fixture_body and _ERROR_TOKEN_RE.search(raw_line):
            if match is None or match.group("sev") != "error" or not _is_fixture(match):
                return (
                    "ERROR",
                    "error diagnostic not located in "
                    f"{fixture_filename}: {raw_line.strip()[:200]!r}",
                )
        pos += len(raw_line)

    error_diags: list[tuple[int, str]] = []
    for idx, match in enumerate(headers):
        if match.group("sev") != "error":
            continue
        body_end = (
            headers[idx + 1].start() if idx + 1 < len(headers) else len(combined_output)
        )
        if stream_break is not None and match.start() < stream_break:
            body_end = min(body_end, stream_break)
        error_diags.append(
            (int(match.group("line")), combined_output[match.end() : body_end])
        )

    start, end = theorem_span
    error_lines = [ln for ln, _ in error_diags]
    outside = [ln for ln in error_lines if not (start <= ln <= end)]
    if outside:
        return (
            "ERROR",
            f"error diagnostic outside target theorem lines {start}-{end} "
            f"(outside lines: {outside}, all error lines: {error_lines})",
        )
    if not error_diags:
        return (
            "ERROR",
            f"no error diagnostic in target theorem lines {start}-{end} "
            f"(saw error lines: {error_lines})",
        )
    if not any(
        marker in body
        for _, body in error_diags
        for marker in EXPECTED_PROOF_FAILURE_MARKERS
    ):
        return (
            "ERROR",
            "Lean failed without a recognized proof/type mismatch diagnostic "
            f"inside target theorem lines {start}-{end}",
        )
    return (
        "KILLED",
        f"proof failed inside target theorem at line(s) {error_lines}",
    )


_LEAN_HEADER_MOD_RE = re.compile(
    r"(?:[A-Za-z_][A-Za-z0-9_']*|«[^»\n]+»)"
    r"(?:\.(?:[A-Za-z_][A-Za-z0-9_']*|«[^»\n]+»))*"
)


def _parse_lean_header_ex(lean_source: str) -> tuple[bool, list[str], bool]:
    """Parse a Lean 4 module header (`module`, `prelude`, `import` directives).

    Returns `(is_module, imports, complete)`. `complete` is False when an
    `import` was seen whose module name this parser could not read in full
    (for example a non-ASCII name): Lean would go on to process that import and
    every one after it, so `imports` is then an INCOMPLETE list and must not
    be used to decide what a file depends on.

    Scans only the header (stopping at the first non-header token while
    skipping whitespace, `--` line comments, and nested `/- ... -/` block
    comments), so `import` text inside comments, docstrings, or the file body
    is never mistaken for a real import. Returns `(is_module, imports)` with
    module names converted to slash paths in exact header order.
    """
    n = len(lean_source)
    i = 0
    unclosed_header_comment = False

    def skip_ws_and_comments() -> None:
        nonlocal i, unclosed_header_comment
        while i < n:
            ch = lean_source[i]
            if ch.isspace():
                i += 1
            elif lean_source[i : i + 2] == "--":
                nl = lean_source.find("\n", i + 2)
                i = n if nl == -1 else nl + 1
            elif lean_source[i : i + 2] == "/-":
                depth = 1
                i += 2
                while i < n and depth > 0:
                    if lean_source[i : i + 2] == "/-":
                        depth += 1
                        i += 2
                    elif lean_source[i : i + 2] == "-/":
                        depth -= 1
                        i += 2
                    else:
                        i += 1
                if depth > 0:
                    unclosed_header_comment = True
            else:
                break

    def read_word() -> tuple[str, int] | None:
        skip_ws_and_comments()
        if i >= n:
            return None
        match = _LEAN_HEADER_MOD_RE.match(lean_source, i)
        if match is None:
            return None
        return (match.group(0), match.end())

    is_module = False
    imports: list[str] = []
    complete = True

    tok = read_word()
    if tok is not None and tok[0] == "module":
        is_module = True
        i = tok[1]
        tok = read_word()
    if tok is not None and tok[0] == "prelude":
        i = tok[1]

    while True:
        saved = i
        tok = read_word()
        if tok is None:
            break
        word, end = tok
        if word in ("public", "private"):
            i = end
            tok = read_word()
            if tok is None:
                i = saved
                break
            word, end = tok
        if word == "meta":
            i = end
            tok = read_word()
            if tok is None:
                i = saved
                break
            word, end = tok
        if word != "import":
            i = saved
            break
        i = end
        tok = read_word()
        if tok is None:
            complete = False
            break
        word, end = tok
        if word == "all":
            i = end
            tok = read_word()
            if tok is None:
                complete = False
                break
            word, end = tok
        imports.append(word.replace(".", "/"))
        i = end
        # The name must end here; `Trusted.Ünï` would otherwise be read as
        # the module `Trusted` followed by unparsed text.
        if i < n and not (
            lean_source[i].isspace() or lean_source[i : i + 2] in ("--", "/-")
        ):
            complete = False
            break

    return (is_module, imports, complete and not unclosed_header_comment)


def _parse_lean_header(lean_source: str) -> tuple[bool, list[str]]:
    """Return `(is_module, imports)` from `_parse_lean_header_ex`."""
    is_module, imports, _ = _parse_lean_header_ex(lean_source)
    return (is_module, imports)


def _extract_trusted_imports(lean_source: str) -> list[str]:
    """Return `Trusted/...` module paths imported by `lean_source` in header order."""
    _, all_imports = _parse_lean_header(lean_source)
    return [mod for mod in all_imports if mod.startswith("Trusted/")]


def _has_sorry_warning(combined_output: str) -> bool:
    """Return True if Lean output mentions `sorry` or `sorryAx` in any quoting style."""
    return bool(SORRY_OUTPUT_RE.search(combined_output))


# Names a fixture declares (`def helper ...`), wherever the keyword appears.
_FIXTURE_DECL_NAME_RE = re.compile(r"\bdef\s+([^\s:({\[]+)")
_LEAN_SIMPLE_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

# Declarations in a trusted source file, matched on raw text (a name that only
# appears in a comment is reserved too, which errs on the safe side).
_TRUSTED_DECL_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)[ \t]+)*"
    r"(def|theorem|abbrev|structure|inductive|class|opaque|axiom)[ \t]+"
    r"([^\s:({\[]+)",
    re.MULTILINE,
)

# Declaration keywords that introduce something a fixture could CALL to
# evaluate the semantics (as opposed to a type or a proof).
_TRUSTED_FUNCTION_KINDS: frozenset[str] = frozenset({"def", "abbrev", "opaque"})


# Lean prelude primitives and trusted root namespace components that a fixture
# helper `def` must never shadow.
_LEAN_CORE_RESERVED_NAMES: frozenset[str] = frozenset(
    {
        "Trusted",
        "Rustc",
        "V2026_06_01",
        "MirAst",
        "MirSemantics",
        "Effect",
        "Sequence",
        "Layout",
        "Nat",
        "Bool",
        "Option",
        "List",
        "String",
        "Unit",
        "Eq",
        "rfl",
        "true",
        "false",
        "some",
        "none",
        "nil",
        "cons",
    }
)

_TRUSTED_INDUCTIVE_START_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    r"(?:(?:private|protected)[ \t]+)?inductive\b"
)
_TRUSTED_CTOR_LINE_RE = re.compile(r"^[ \t]*\|[ \t]+([A-Za-z_][A-Za-z0-9_']*)")


def _trusted_declaration_names(lean_source: str) -> set[str]:
    """Return the last name component of every declaration in a trusted file."""
    return {name.split(".")[-1] for _, name in _TRUSTED_DECL_RE.findall(lean_source)}


def _trusted_function_names(lean_source: str) -> set[str]:
    """Return the last name component of every function a trusted file defines."""
    return {
        name.split(".")[-1]
        for kind, name in _TRUSTED_DECL_RE.findall(lean_source)
        if kind in _TRUSTED_FUNCTION_KINDS
    }


def _trusted_constructor_names(lean_source: str) -> set[str]:
    """Return inductive constructor names declared in a trusted file."""
    ctors: set[str] = set()
    in_inductive = False
    for line in lean_source.splitlines():
        if _TRUSTED_INDUCTIVE_START_RE.match(line):
            in_inductive = True
            continue
        if not in_inductive:
            continue
        if line and not line[0].isspace():
            in_inductive = False
            continue
        match = _TRUSTED_CTOR_LINE_RE.match(line)
        if match and "=>" not in line:
            ctors.add(match.group(1))
    return ctors


def _split_top_level_equality(stmt: str) -> list[int]:
    """Return character indices of top-level standalone `=` operators in `stmt`.

    Ignores `=` inside string literals or nested `(...)`, `[...]`, `{...}`,
    `⟨...⟩`, as well as compound operators (`:=`, `==`, `!=`, `<=`, `>=`, `=>`).
    """
    positions: list[int] = []
    depth = 0
    i = 0
    n = len(stmt)
    while i < n:
        ch = stmt[i]
        if ch == '"':
            i += 1
            while i < n:
                if stmt[i] == "\\" and i + 1 < n:
                    i += 2
                elif stmt[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            continue
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩" and depth > 0:
            depth -= 1
        elif (
            ch == "="
            and depth == 0
            and stmt[max(i - 1, 0) : i] not in (":", "<", ">", "!", "=")
            and stmt[i + 1 : i + 2] not in ("=", ">")
        ):
            positions.append(i)
        i += 1
    return positions


# Term-level binders that could name the whole evaluation and then state
# something trivial about that name (`let x := evalStmt s t; x = x`).
_STATEMENT_BINDER_RE = re.compile(r"(?<![\w'])(?:let|fun|λ)(?![\w'])")
_STATEMENT_HEAD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?=\s|$)")
_UB_IDENT_RE = re.compile(r"(?<![\w'])ub(?![\w'])")

# The only right-hand sides a refutation theorem may assert.
REFUTE_UB_RHS: tuple[str, ...] = (".ub", "MirStepNode.fail .ub")


def _fixture_statement_errors(
    kind: str,
    src_text: str,
    theorem_name: str,
    *,
    semantics_fn_names: frozenset[str] | set[str],
) -> list[str]:
    """Reject a fixture theorem that does not test the trusted semantics.

    `_fixture_shape_errors` pins the proof to `rfl`; this pins the statement
    to `<semantics function> <args> = <expected data>`:

    - exactly one top-level `=`, written without enclosing parentheses, with
      no `let`/`fun`/`λ` and with textually different sides;
    - the LHS is an application whose head is a function defined in one of
      `SEMANTICS_MODULES` (`semantics_fn_names`), written unqualified;
    - no such function is named anywhere else in the fixture. Helper `def`s
      and the RHS are therefore plain data, so the RHS cannot be an alias of
      the very evaluation it is compared with (`def expected := evalStmt s t`
      and then `evalStmt s t = expected`), which `rfl` proves on every mutant;
    - a refutation's RHS is literally UB (`REFUTE_UB_RHS`), and a positive
      sanity fixture never mentions `ub`, neither inline nor through a helper.

    A vacuous REFUTATION at least fails the gate at run time, because its
    mutant survives. A vacuous SANITY theorem does not: it passes on every
    mutant and silently disables the check that a mutation left non-UB
    behavior intact. These checks are what protects that half of the gate.
    """
    code_only, _, _ = _scan_lean_source(src_text)
    span_lines: list[str] = []
    try:
        start, end = find_theorem_line_span(src_text, theorem_name)
    except ValueError:
        pass
    else:
        span_lines = [
            ln for ln in code_only.splitlines()[start - 1 : end] if ln.strip()
        ]
    if (
        len(span_lines) < 3
        or span_lines[0].rstrip() != f"theorem {theorem_name} :"
        or not span_lines[-2].rstrip().endswith(":=")
    ):
        return [f"({kind}): cannot extract the statement of theorem {theorem_name!r}"]
    stmt = "\n".join(span_lines[1:-1]).rstrip()[: -len(":=")].strip()

    errors: list[str] = []
    if _STATEMENT_BINDER_RE.search(stmt):
        errors.append(
            f"({kind}): theorem {theorem_name!r} statement must not contain "
            "`let`, `fun` or `λ`"
        )
    eq_positions = _split_top_level_equality(stmt)
    if len(eq_positions) != 1:
        errors.append(
            f"({kind}): theorem {theorem_name!r} statement must have exactly one "
            f"top-level `=`, found {len(eq_positions)}"
        )
        return errors
    lhs = stmt[: eq_positions[0]].strip()
    rhs = " ".join(stmt[eq_positions[0] + 1 :].split())
    if not lhs or not rhs:
        errors.append(
            f"({kind}): theorem {theorem_name!r} has empty LHS or RHS around `=`"
        )
        return errors
    if " ".join(lhs.split()) == rhs:
        errors.append(
            f"({kind}): theorem {theorem_name!r} is syntactically reflexive (`lhs = lhs`)"
        )

    head = _STATEMENT_HEAD_RE.match(lhs)
    if head is None or head.group(0) not in semantics_fn_names:
        errors.append(
            f"({kind}): theorem {theorem_name!r} LHS must apply a trusted "
            f"MirSemantics function, got {lhs.split()[0]!r}"
        )
    outside_lhs = Counter(_LEAN_SIMPLE_IDENT_RE.findall(code_only)) - Counter(
        _LEAN_SIMPLE_IDENT_RE.findall(lhs)
    )
    leaked = sorted(name for name in outside_lhs if name in semantics_fn_names)
    if leaked:
        errors.append(
            f"({kind}): {kind}_source names trusted MirSemantics function(s) "
            f"{leaked} outside the theorem LHS (helper `def`s and the expected "
            "value must be plain data)"
        )

    if kind == "refute":
        if rhs not in REFUTE_UB_RHS:
            errors.append(
                f"({kind}): refutation theorem {theorem_name!r} RHS must assert UB "
                f"(one of {REFUTE_UB_RHS!r}), got {rhs!r}"
            )
    elif _UB_IDENT_RE.search(code_only):
        errors.append(
            f"({kind}): positive sanity fixture must not mention `ub` "
            f"(theorem {theorem_name!r} must assert a non-UB outcome)"
        )
    return errors


def _fixture_shape_errors(
    kind: str,
    src_text: str,
    theorem_name: str,
    *,
    reserved_names: frozenset[str] | set[str] = frozenset(),
) -> list[str]:
    """Return static shape errors for one generated fixture source.

    A fixture is `import`s, `namespace`/`open`/`end`, helper `def`s, and ONE
    theorem of the exact form

        theorem <name> :
            <statement> :=
          rfl

    `rfl` only proves definitional equalities, so with no binders, no second
    proof obligation, and no helper that shadows a trusted declaration
    (`reserved_names`), the theorem can only hold by evaluating the trusted
    semantics. Anything else is rejected before Lean ever runs, including
    every construct `_scan_lean_source` cannot lex exactly.
    """
    errors: list[str] = []
    code_only, unclosed_comment, hazards = _scan_lean_source(src_text)
    if unclosed_comment:
        errors.append(f"unclosed block comment in {kind}_source")
    for hazard in hazards:
        errors.append(
            f"unsupported lexical construct in {kind}_source ({hazard})"
        )
    raw_sorry = re.search(r"\bsorry\w*", src_text)
    if raw_sorry:
        errors.append(
            f"forbidden token {raw_sorry.group(0)!r} in {kind}_source"
        )
    else:
        forbidden = FORBIDDEN_FIXTURE_TOKEN_RE.search(code_only)
        if forbidden:
            errors.append(
                f"forbidden token {forbidden.group(0)!r} in {kind}_source"
            )
    theorem_count = len(re.findall(r"\btheorem\b", code_only))
    if theorem_count != 1:
        errors.append(
            f"{kind}_source must declare exactly one theorem, found {theorem_count}"
        )

    # Every `import` Lean sees must be one the header parser recognized;
    # otherwise the stale-import check ran on an incomplete import list.
    import_tokens = len(re.findall(r"\bimport\b", code_only))
    _, header_imports, header_complete = _parse_lean_header_ex(src_text)
    parsed_imports = len(header_imports)
    if import_tokens != parsed_imports or not header_complete:
        errors.append(
            f"{kind}_source has {import_tokens} `import` token(s) but the "
            f"header parser recognized {parsed_imports}"
        )

    code_lines = code_only.splitlines()
    for line_no, line in enumerate(code_lines, start=1):
        if line and line[0] not in " \t":
            word = line.split(maxsplit=1)[0]
            if word not in FIXTURE_TOP_LEVEL_WORDS:
                errors.append(
                    f"unsupported top-level command {word!r} at line {line_no} "
                    f"of {kind}_source"
                )

    for helper in _FIXTURE_DECL_NAME_RE.findall(code_only):
        if not _LEAN_SIMPLE_IDENT_RE.fullmatch(helper):
            errors.append(
                f"helper `def {helper}` in {kind}_source must be a simple identifier"
            )
        elif helper in reserved_names:
            errors.append(
                f"helper `def {helper}` in {kind}_source shadows a trusted declaration"
            )

    try:
        start, end = find_theorem_line_span(src_text, theorem_name)
    except ValueError as exc:
        errors.append(f"({kind}): {exc}")
        return errors
    span_lines = [ln for ln in code_lines[start - 1 : end] if ln.strip()]
    span_text = "\n".join(span_lines)
    if ":=" not in span_text:
        errors.append(
            f"({kind}): theorem {theorem_name!r} line span {start}-{end} "
            "does not contain its proof (`:=`)"
        )
    if span_lines[0].rstrip() != f"theorem {theorem_name} :":
        errors.append(
            f"({kind}): theorem header must be exactly `theorem {theorem_name} :` "
            "(no binders, hypotheses or modifiers)"
        )
    if (
        len(span_lines) < 3
        or span_lines[-1].strip() != "rfl"
        or not span_lines[-2].rstrip().endswith(":=")
    ):
        errors.append(
            f"({kind}): theorem {theorem_name!r} must be proved by `:=` followed "
            "by `rfl` on its own line"
        )
    return errors


def validate_catalog_invariants(anneal_root: Path) -> list[str]:
    """Validate static catalog and topological invariants without invoking Lean.

    Returns a list of error strings (empty when all invariants hold).
    """
    errors: list[str] = []
    seen_ids: set[str] = set()
    covered_modules: set[str] = set()
    quick_count = 0

    if len(MIR_SEMANTICS_GUARDS) < 8:
        errors.append(
            f"catalog must define at least 8 guards, found {len(MIR_SEMANTICS_GUARDS)}"
        )

    all_known_modules = set(BASE_TRUSTED_MODULES) | set(SEMANTICS_MODULES)
    trusted_lean_dir = anneal_root / "trusted/lean"

    # Verify BASE_TRUSTED_MODULES + SEMANTICS_MODULES exist and are topologically ordered.
    seen_mods: set[str] = set()
    # Names a fixture helper must not reuse: inside `namespace GuardMutation`
    # a local `def evalOperand` or `def ub` or `def rfl` would win over the
    # `open`ed trusted/core declaration, detaching the theorem from the TCB.
    trusted_decl_names: set[str] = set()
    trusted_ctor_names: set[str] = set()
    # Functions of the mutable semantics modules: the only things a fixture
    # theorem may evaluate, and only on its LHS.
    semantics_fn_names: set[str] = set()
    for mod in (*BASE_TRUSTED_MODULES, *SEMANTICS_MODULES):
        mod_path = trusted_lean_dir / f"{mod}.lean"
        if not mod_path.is_file():
            errors.append(f"missing trusted Lean module: {mod_path}")
            continue
        mod_text = mod_path.read_text(encoding="utf-8")
        trusted_decl_names |= _trusted_declaration_names(mod_text)
        trusted_ctor_names |= _trusted_constructor_names(mod_text)
        if mod in SEMANTICS_MODULES:
            semantics_fn_names |= _trusted_function_names(mod_text)
        if not _parse_lean_header_ex(mod_text)[2]:
            errors.append(f"cannot parse every import of trusted module {mod}")
        mod_imports = _extract_trusted_imports(mod_text)
        for imp in mod_imports:
            if imp not in seen_mods:
                errors.append(
                    f"topological/missing import in {mod}: {imp!r} not compiled before {mod!r}"
                )
        # `SEMANTICS_UPSTREAM` decides which `.olean`s are stale for a mutant,
        # so it must cover every semantics module the live source imports.
        if mod in SEMANTICS_UPSTREAM:
            declared_upstream = set(SEMANTICS_UPSTREAM[mod])
            for imp in mod_imports:
                if imp in SEMANTICS_MODULES and imp not in declared_upstream:
                    errors.append(
                        f"SEMANTICS_UPSTREAM[{mod!r}] is missing live import {imp!r}"
                    )
        seen_mods.add(mod)
    reserved_names = trusted_decl_names | trusted_ctor_names | _LEAN_CORE_RESERVED_NAMES

    for guard in MIR_SEMANTICS_GUARDS:
        if not GUARD_ID_RE.match(guard.guard_id):
            errors.append(
                f"invalid guard_id {guard.guard_id!r} (must match {GUARD_ID_RE.pattern})"
            )
        if guard.guard_id in seen_ids:
            errors.append(f"duplicate guard_id: {guard.guard_id}")
        seen_ids.add(guard.guard_id)

        if guard.quick:
            quick_count += 1

        if guard.target_module not in SEMANTICS_DOWNSTREAM_DIRECT:
            errors.append(
                f"{guard.guard_id}: unknown target_module {guard.target_module!r}"
            )
            continue
        covered_modules.add(guard.target_module)

        expected_rel_file = f"trusted/lean/{guard.target_module}.lean"
        if guard.target_file != expected_rel_file:
            errors.append(
                f"{guard.guard_id}: target_file {guard.target_file!r} does not match "
                f"target_module ({expected_rel_file!r})"
            )

        rebuild_mods = guard.effective_rebuild_modules
        if not rebuild_mods or rebuild_mods[0] != guard.target_module:
            errors.append(
                f"{guard.guard_id}: effective_rebuild_modules must start with target_module"
            )
        for mod in rebuild_mods:
            if mod not in SEMANTICS_MODULES:
                errors.append(
                    f"{guard.guard_id}: unknown rebuild module {mod!r}"
                )
        known_rebuild = [m for m in rebuild_mods if m in SEMANTICS_MODULES]
        if len(set(known_rebuild)) != len(known_rebuild) or known_rebuild != [
            m for m in SEMANTICS_MODULES if m in known_rebuild
        ]:
            errors.append(
                f"{guard.guard_id}: rebuild modules must be unique and in "
                "topological order"
            )
        # A rebuilt module must never import a module that depends on the
        # mutated target but is not itself rebuilt (its `.olean` is stale).
        for mod in known_rebuild:
            for dep in SEMANTICS_UPSTREAM.get(mod, ()):
                if (
                    guard.target_module in SEMANTICS_UPSTREAM.get(dep, ())
                    and dep not in known_rebuild
                ):
                    errors.append(
                        f"{guard.guard_id}: rebuild module {mod!r} depends on "
                        f"stale un-rebuilt module {dep!r}"
                    )

        if FORBIDDEN_FIXTURE_TOKEN_RE.search(guard.replacement):
            errors.append(
                f"{guard.guard_id}: forbidden token in replacement"
            )

        target_path = anneal_root / guard.target_file
        if not target_path.is_file():
            errors.append(f"{guard.guard_id}: missing target_file {target_path}")
        else:
            text = target_path.read_text(encoding="utf-8")
            try:
                apply_single_guard_mutation(
                    text,
                    guard.anchor,
                    guard.replacement,
                    guard_id=guard.guard_id,
                )
            except ValueError as exc:
                errors.append(str(exc))

        if guard.sanity_theorem_name == guard.theorem_name:
            errors.append(
                f"{guard.guard_id}: sanity and refutation theorems must have "
                "distinct names"
            )
        if guard.sanity_source == guard.refute_source:
            errors.append(
                f"{guard.guard_id}: sanity and refutation fixtures are identical"
            )

        for kind, src_text, thm_name in (
            ("sanity", guard.sanity_source, guard.sanity_theorem_name),
            ("refute", guard.refute_source, guard.theorem_name),
        ):
            for shape_error in _fixture_shape_errors(
                kind, src_text, thm_name, reserved_names=reserved_names
            ):
                errors.append(f"{guard.guard_id}: {shape_error}")
            for stmt_error in _fixture_statement_errors(
                kind, src_text, thm_name, semantics_fn_names=semantics_fn_names
            ):
                errors.append(f"{guard.guard_id}: {stmt_error}")

            is_module, all_imports = _parse_lean_header(src_text)
            if is_module:
                errors.append(
                    f"{guard.guard_id} ({kind}): fixture must not use a `module` header"
                )
            non_trusted = [imp for imp in all_imports if not imp.startswith("Trusted/")]
            if non_trusted:
                errors.append(
                    f"{guard.guard_id} ({kind}): fixture imports non-Trusted module(s) "
                    f"{non_trusted!r}"
                )
            imports = [imp for imp in all_imports if imp.startswith("Trusted/")]
            if not imports:
                errors.append(
                    f"{guard.guard_id} ({kind}): fixture imports no Trusted.* module"
                )
            for imp in imports:
                if imp not in all_known_modules:
                    errors.append(
                        f"{guard.guard_id} ({kind}): fixture imports unknown module {imp!r}"
                    )
                elif (
                    imp not in rebuild_mods
                    and guard.target_module in SEMANTICS_UPSTREAM.get(imp, ())
                ):
                    errors.append(
                        f"{guard.guard_id} ({kind}): fixture imports {imp!r}, which "
                        "depends on the mutated module but is not rebuilt (stale)"
                    )
            if not any(imp in rebuild_mods for imp in imports):
                errors.append(
                    f"{guard.guard_id} ({kind}): fixture must import target/rebuilt module "
                    f"from {rebuild_mods!r}, got {imports!r}"
                )

    for req_mod in REQUIRED_COVERAGE_MODULES:
        if req_mod not in covered_modules:
            errors.append(f"catalog missing required coverage of {req_mod}")

    if quick_count < 3:
        errors.append(
            f"--quick subset must contain at least 3 guards, found {quick_count}"
        )

    return errors


def select_guards(
    *,
    quick: bool = False,
    guard_filters: Sequence[str] | None = None,
) -> list[MirSemanticsGuard]:
    """Select cataloged guards according to `--quick`, `--guard`, or `--all`."""
    if quick and guard_filters:
        raise ValueError("--quick and --guard cannot be combined")
    if quick:
        return [g for g in MIR_SEMANTICS_GUARDS if g.quick]
    if guard_filters:
        selected_ids: set[str] = set()
        # Each `--guard` value is one selector or a comma-separated list. Every
        # selector must match: an exact guard_id wins over a substring match.
        for raw_pattern in guard_filters:
            for part in raw_pattern.split(","):
                pattern = part.strip()
                if not pattern:
                    raise ValueError(
                        f"--guard filter must be non-empty, got {raw_pattern!r}"
                    )
                exact = [g for g in MIR_SEMANTICS_GUARDS if g.guard_id == pattern]
                matched = (
                    exact
                    if exact
                    else [g for g in MIR_SEMANTICS_GUARDS if pattern in g.guard_id]
                )
                if not matched:
                    raise ValueError(
                        f"no cataloged guard matched --guard {pattern!r}"
                    )
                selected_ids.update(g.guard_id for g in matched)
        return [g for g in MIR_SEMANTICS_GUARDS if g.guard_id in selected_ids]
    return list(MIR_SEMANTICS_GUARDS)


def _baseline_modules_for_guards(
    guards: Sequence[MirSemanticsGuard],
) -> tuple[str, ...]:
    """Return minimal topological list of TCB modules required by `guards`."""
    needed_sem: set[str] = set()
    for guard in guards:
        for mod in guard.effective_rebuild_modules:
            needed_sem.add(mod)
            needed_sem.update(SEMANTICS_UPSTREAM.get(mod, ()))
    ordered_sem = tuple(m for m in SEMANTICS_MODULES if m in needed_sem)
    return (*BASE_TRUSTED_MODULES, *ordered_sem)


def _stale_modules_for_guard(guard: MirSemanticsGuard) -> set[str]:
    """Semantics modules whose baseline `.olean` is stale for `guard`'s mutant.

    These depend on the mutated target but are not rebuilt, so they were
    compiled against the UNMUTATED target. They are never seeded into the
    mutant overlay: an accidental import then fails loudly instead of silently
    mixing mutated and unmutated semantics.
    """
    rebuilt = set(guard.effective_rebuild_modules)
    return {
        mod
        for mod in SEMANTICS_MODULES
        if guard.target_module in SEMANTICS_UPSTREAM.get(mod, ())
        and mod not in rebuilt
    }


def _resolve_lean_run_wrapper(anneal_root: Path) -> Path | None:
    """Locate `anneal-lean-run` on PATH, `~/.local/bin`, or `<repo>/scripts`."""
    candidates: list[Path] = []
    on_path = shutil.which("anneal-lean-run")
    if on_path:
        candidates.append(Path(on_path))
    candidates.append(Path.home() / ".local/bin/anneal-lean-run")
    candidates.append(anneal_root / "scripts/anneal-lean-run")
    for cand in candidates:
        if cand.is_file() and os.access(cand, os.X_OK):
            return Path(os.path.abspath(cand))
    return None


def _build_lean_command(
    lean_bin: Path,
    args: Sequence[str],
    *,
    lean_run_wrapper: Path | None,
) -> list[str]:
    """Build Lean argv, optionally wrapped via `anneal-lean-run --mode file --`."""
    if lean_run_wrapper is not None:
        return [str(lean_run_wrapper), "--mode", "file", "--", str(lean_bin), *args]
    return [str(lean_bin), *args]


# ----------------------------------------------------------------------
# `.lake/build/lib/lean` reuse: content validation against Lake's traces
# ----------------------------------------------------------------------

_MASK64 = (1 << 64) - 1
_MURMUR_M = 0xC6A4A7935BD1E995
_LAKE_HASH_NIL = 1723  # `Lake.Hash.nil`
_LAKE_HASH_NIL_HEX = f"{_LAKE_HASH_NIL:016x}"
_LAKE_OLEAN_OUTPUT_RE = re.compile(r"([0-9a-f]{16})\.olean")
_LAKE_IMPORT_ARTS_SUFFIX = ":importAllArts"
_LAKE_IMPORT_LEGACY_SUFFIX = " transitive imports (legacy)"
_LAKE_DEFAULT_LEAN_ARGS_CAPTION = "Module.leanArgs: #[]"
_LEAN_VERSION_RE = re.compile(r"\bversion\s+(\d+\.\d+\.\d+(?:-[\w.]+)?)\b")
_LEAN_COMMIT_RE = re.compile(r"\bcommit\s+([0-9a-f]{40})\b")
_LEAN_GITHASH_RE = re.compile(r"^[0-9a-f]{40}$")
_LAKE_TOML_ALLOWED_ROOT_KEYS: frozenset[str] = frozenset({
    "name",
    "defaultTargets",
    "lean_lib",
    "lean_exe",
    "testDriver",
    "lintDriver",
    "version",
    "description",
    "keywords",
    "homepage",
    "license",
    "readmeFile",
})
_LAKE_TOML_ALLOWED_TRUSTED_LIB_KEYS: frozenset[str] = frozenset({
    "name",
    "srcDir",
    "roots",
    "globs",
})


def _lean_murmur_hash64a_simple(data: bytes, seed: int = 11) -> int:
    """Lean runtime `hash_str` (MurmurHash64A), written out block by block."""
    m = _MURMUR_M
    mask = _MASK64
    n = len(data)
    h = (seed ^ (n * m)) & mask
    n_block_bytes = (n // 8) * 8
    if n_block_bytes:
        words = array.array("Q")
        if words.itemsize != 8:
            raise RuntimeError("platform lacks an 8-byte unsigned array type")
        words.frombytes(memoryview(data)[:n_block_bytes])
        if sys.byteorder != "little":
            words.byteswap()
        for k in words:
            k = (k * m) & mask
            k ^= k >> 47
            k = (k * m) & mask
            h = ((h ^ k) * m) & mask
    tail = data[n_block_bytes:]
    if tail:
        h ^= int.from_bytes(tail, "little")
        h = (h * m) & mask
    h ^= h >> 47
    h = (h * m) & mask
    h ^= h >> 47
    return h


# Inputs of at least this many 8-byte blocks take the bulk path below, in
# chunks of `_MURMUR_BULK_BLOCKS` blocks.
_MURMUR_BULK_MIN_BLOCKS = 512
_MURMUR_BULK_BLOCKS = 1 << 15
_MURMUR_LANE = b"\xff" * 8 + b"\x00" * 8


def _murmur_mix_blocks(chunk: memoryview) -> array.array[int]:
    """Return MurmurHash64A's mixed value of every whole 8-byte block in `chunk`.

    Each little-endian block `k` becomes `k *= m; k ^= k >> 47; k *= m`
    (mod 2^64). Blocks are independent at this stage, so they are laid out in
    128-bit lanes of one big integer and transformed together at C speed: a
    64-bit value times a 64-bit constant cannot overflow its lane, and a right
    shift by 47 only moves a neighbouring lane's bits into the upper half of a
    lane, which the lane mask clears. Only the final chaining of blocks into
    the running hash has to stay a Python loop.
    """
    count = len(chunk) // 8
    lanes = bytearray(count * 16)
    for j in range(8):
        lanes[j::16] = chunk[j::8]
    lane_mask = int.from_bytes(_MURMUR_LANE * count, "little")
    big = int.from_bytes(lanes, "little")
    big = (big * _MURMUR_M) & lane_mask
    big ^= (big >> 47) & lane_mask
    big = (big * _MURMUR_M) & lane_mask
    mixed = big.to_bytes(count * 16, "little")
    packed = bytearray(count * 8)
    for j in range(8):
        packed[j::8] = mixed[j::16]
    words = array.array("Q")
    if words.itemsize != 8:
        raise RuntimeError("platform lacks an 8-byte unsigned array type")
    words.frombytes(packed)
    if sys.byteorder != "little":
        words.byteswap()
    return words


def _lean_murmur_hash64a(data: bytes, seed: int = 11) -> int:
    """Lean runtime `hash_str` (MurmurHash64A), i.e. `String.hash`/`ByteArray.hash`.

    Identical to `_lean_murmur_hash64a_simple`; large inputs (`.olean` files)
    mix their blocks in bulk, which roughly halves the time to re-hash every
    reused `.olean`.
    """
    n = len(data)
    n_block_bytes = (n // 8) * 8
    if n_block_bytes < _MURMUR_BULK_MIN_BLOCKS * 8:
        return _lean_murmur_hash64a_simple(data, seed)
    m = _MURMUR_M
    mask = _MASK64
    h = (seed ^ (n * m)) & mask
    view = memoryview(data)
    step = _MURMUR_BULK_BLOCKS * 8
    for start in range(0, n_block_bytes, step):
        for k in _murmur_mix_blocks(view[start : min(start + step, n_block_bytes)]):
            h = ((h ^ k) * m) & mask
    tail = data[n_block_bytes:]
    if tail:
        h ^= int.from_bytes(tail, "little")
        h = (h * m) & mask
    h ^= h >> 47
    h = (h * m) & mask
    h ^= h >> 47
    return h


def _lean_mix_hash(h: int, k: int) -> int:
    """Lean runtime `lean_uint64_mix_hash` (`mixHash`)."""
    m = _MURMUR_M
    k = (k * m) & _MASK64
    k ^= k >> 47
    k ^= m
    h ^= k
    return (h * m) & _MASK64


def lake_hash_of_bytes(data: bytes) -> str:
    """`Lake.Hash.ofByteArray` as 16 lowercase hex digits (`.olean.hash` format)."""
    return f"{_lean_mix_hash(_LAKE_HASH_NIL, _lean_murmur_hash64a(data)):016x}"


def lake_hash_of_text(data: bytes) -> str:
    """`Lake.Hash.ofText` (CRLF-normalized source text hash) as 16 hex digits."""
    return lake_hash_of_bytes(data.replace(b"\r\n", b"\n"))


def lake_import_arts_hash(olean_hash_hex: str) -> str:
    """Hash Lake records for importing a non-`module` file with this `.olean`."""
    return f"{_lean_mix_hash(_LAKE_HASH_NIL, int(olean_hash_hex, 16)):016x}"


def _lean_name_hash(parts: Sequence[str]) -> int:
    """Lean `Lean.Name.hash` for a string-component name (`Trusted.Sequence`)."""
    h = _LAKE_HASH_NIL
    for part in parts:
        h = _lean_mix_hash(h, _lean_murmur_hash64a(part.encode("utf-8")))
    return h


def _lake_extra_dep_default_hash() -> int:
    """Default `LeanLib.extraDep` hash (`Job.nil` mixed with root `Package.extraDep`)."""
    return _lean_mix_hash(_LAKE_HASH_NIL, _LAKE_HASH_NIL)


def _lake_nil_libs_trace_hash() -> int:
    """Default `libs` trace hash (4 empty dynlib/plugin jobs mixed into `nil`)."""
    h = _LAKE_HASH_NIL
    for _ in range(4):
        h = _lean_mix_hash(h, _LAKE_HASH_NIL)
    return h


def lake_legacy_trans_hash(
    direct_imports: Sequence[str],
    all_arts_hashes: dict[str, int],
    legacy_trans_hashes: dict[str, int],
) -> int:
    """Compute Lake's `ModuleImportInfo.legacyTransTrace.hash` for a non-`module` file."""
    h = _LAKE_HASH_NIL
    for dep in direct_imports:
        h = _lean_mix_hash(_lean_mix_hash(h, legacy_trans_hashes[dep]), all_arts_hashes[dep])
    return h


def lake_module_dep_hash(
    *,
    module: str,
    src_bytes: bytes,
    direct_imports: Sequence[str],
    all_arts_hashes: dict[str, int],
    legacy_trans_hashes: dict[str, int],
    lean_githash: str,
    pkg_name: str,
) -> tuple[str, int]:
    """Reproduce Lake v4.34's `depHash` for a default-configured non-`module` file.

    Returns `(dep_hash_hex, legacy_trans_hash)` where `dep_hash_hex` is the
    16-char lowercase hex string written to `<Mod>.trace`'s `"depHash"` field
    (including `"synthetic": true` traces restored from `$LAKE_CACHE_DIR`).
    """
    legacy_trans = lake_legacy_trans_hash(
        direct_imports, all_arts_hashes, legacy_trans_hashes
    )
    dep_trace = _lean_mix_hash(
        _lean_mix_hash(_LAKE_HASH_NIL, _lake_extra_dep_default_hash()),
        legacy_trans,
    )
    lib_trace = _lake_nil_libs_trace_hash()
    lean_trace = _lean_mix_hash(
        _LAKE_HASH_NIL, _lean_murmur_hash64a(lean_githash.encode("utf-8"))
    )
    src_hash = int(lake_hash_of_text(src_bytes), 16)
    is_module_false = _lean_mix_hash(_LAKE_HASH_NIL, 13)  # `Hashable Bool`: false => 13
    mod_name_trace = _lean_mix_hash(
        _LAKE_HASH_NIL, _lean_name_hash(module.split("/"))
    )
    pkg_id_trace = _lean_mix_hash(
        _LAKE_HASH_NIL,
        _lean_mix_hash(_lean_murmur_hash64a(pkg_name.encode("utf-8")), 13),
    )

    h = _LAKE_HASH_NIL
    h = _lean_mix_hash(h, dep_trace)
    h = _lean_mix_hash(h, lib_trace)
    h = _lean_mix_hash(h, lean_trace)
    h = _lean_mix_hash(h, src_hash)
    h = _lean_mix_hash(h, _LAKE_HASH_NIL)  # empty `leanOptions`
    h = _lean_mix_hash(h, is_module_false)
    h = _lean_mix_hash(h, mod_name_trace)
    h = _lean_mix_hash(h, pkg_id_trace)
    h = _lean_mix_hash(h, _LAKE_HASH_NIL)  # empty `Module.leanArgs`
    return (f"{h:016x}", legacy_trans)


def _read_lakefile_trusted_pkg_name(anneal_root: Path) -> tuple[str | None, str]:
    """Read package `name` from `lakefile.toml` if `Trusted` uses default build opts.

    Fails closed if `lakefile.lean` exists, `lakefile.toml` is missing/invalid,
    or either the root package or `[[lean_lib]] name = "Trusted"` declares any
    unmodeled hash-affecting option (e.g., `leanOptions`, `moreLeanArgs`,
    `needs`, `extraDepTargets`, `precompileModules`, `platformIndependent`).
    """
    if (anneal_root / "lakefile.lean").exists():
        return (None, "lakefile.lean is unsupported for Lake trace verification")
    toml_path = anneal_root / "lakefile.toml"
    if tomllib is None:
        return (None, "cannot read lakefile.toml (needs Python >= 3.11 `tomllib`)")
    try:
        data = tomllib.loads(toml_path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return (None, f"cannot read lakefile.toml ({exc})")
    if not isinstance(data, dict):
        return (None, "invalid lakefile.toml root table")
    extra_root = sorted(set(data) - _LAKE_TOML_ALLOWED_ROOT_KEYS)
    if extra_root:
        return (
            None,
            "lakefile.toml sets unsupported root key(s) for synthetic trace "
            f"verification: {', '.join(extra_root)}",
        )
    pkg_name = data.get("name")
    if not isinstance(pkg_name, str) or not pkg_name:
        return (None, "lakefile.toml missing package `name`")
    lean_libs = data.get("lean_lib")
    if not isinstance(lean_libs, list):
        return (None, "lakefile.toml missing `[[lean_lib]]` table")
    trusted_libs = [
        lib for lib in lean_libs if isinstance(lib, dict) and lib.get("name") == "Trusted"
    ]
    if len(trusted_libs) != 1:
        return (
            None,
            f"lakefile.toml must declare exactly one `Trusted` lean_lib, found {len(trusted_libs)}",
        )
    tlib = trusted_libs[0]
    extra_lib = sorted(set(tlib) - _LAKE_TOML_ALLOWED_TRUSTED_LIB_KEYS)
    if extra_lib:
        return (
            None,
            "lakefile.toml `Trusted` lean_lib sets unsupported key(s) for "
            f"synthetic trace verification: {', '.join(extra_lib)}",
        )
    src_dir = tlib.get("srcDir", ".")
    if not isinstance(src_dir, str) or Path(src_dir).as_posix().rstrip("/") != "trusted/lean":
        return (
            None,
            f"lakefile.toml `Trusted` srcDir {src_dir!r} != 'trusted/lean'",
        )
    return (pkg_name, "")


def _query_lean_toolchain_githash(
    lean_bin: Path,
    anneal_root: Path,
    expected_version: str,
) -> tuple[str | None, str]:
    """Query `lean_bin --version` to verify `expected_version` and get its git commit."""
    try:
        res = subprocess.run(
            [str(lean_bin), "--version"],
            cwd=str(anneal_root),
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=10,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return (None, f"failed to query Lean version ({exc})")
    if res.returncode != 0:
        return (None, f"Lean --version failed (rc={res.returncode})")
    combined = f"{res.stdout}\n{res.stderr}"
    ver_match = _LEAN_VERSION_RE.search(combined)
    commit_match = _LEAN_COMMIT_RE.search(combined)
    if ver_match is None or commit_match is None:
        return (None, "cannot parse Lean version/commit from `lean --version`")
    actual_version = ver_match.group(1)
    if actual_version != expected_version:
        return (
            None,
            f"active Lean binary is {actual_version}, expected {expected_version}",
        )
    return (commit_match.group(1), "")


def _read_lean_toolchain_version(anneal_root: Path) -> str | None:
    """Return `X.Y.Z[-suffix]` from `<anneal_root>/lean-toolchain`, if parseable."""
    try:
        text = (anneal_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    except OSError:
        return None
    match = re.search(r"v?(\d+\.\d+\.\d+(?:-[\w.]+)?)$", text)
    return match.group(1) if match else None


def _trace_pairs(node: object) -> list[tuple[str, object]]:
    """Return the `[caption, value]` pairs of a Lake trace `inputs` list."""
    if not isinstance(node, list):
        return []
    return [
        (entry[0], entry[1])
        for entry in node
        if isinstance(entry, list) and len(entry) == 2 and isinstance(entry[0], str)
    ]


def _verify_lake_traces(
    anneal_root: Path,
    modules: Sequence[str],
    *,
    verify_olean_bytes: bool = True,
    lean_bin: Path | None = None,
    lean_githash: str | None = None,
) -> tuple[bool, str]:
    """Prove by content that Lake's `.olean`s for `modules` match the sources.

    Supports both standard Lake traces (`"synthetic": false`) and Lake cache
    restore traces (`"synthetic": true`, written when Lake restores artifacts
    from `$LAKE_CACHE_DIR` with `"inputs": []` and a full `"depHash"`):

    * For `"synthetic": false` modules, `<Mod>.trace` must record (a) the hash
      of the CURRENT source text, (b) the hash stored in `<Mod>.olean.hash`,
      (c) the pinned toolchain version, (d) default Lean options and
      arguments, and (e) for every `Trusted.*` import, both the hash of that
      import's CURRENT `.olean` and Lake's hash over that import's CURRENT
      transitive imports. (e) pins the whole import closure by content, so a
      module that was not rebuilt after a change deeper in its import chain is
      rejected whatever the file mtimes say.
    * For `"synthetic": true` modules, `depHash` is reproduced from scratch
      using Lake v4.34's exact hash formula over `lakefile.toml`'s package
      identity, the verified Lean binary commit matching `lean-toolchain`, the
      CURRENT source text hash, and the transitive import traces of all
      imported modules (all verified in topological order).

    `modules` must be in topological import order. The `.olean` bytes are
    re-hashed against the recorded hash unless `verify_olean_bytes` is False,
    in which case they are re-hashed only when the `.olean` is newer than its
    `.olean.hash` file (the rule Lake itself uses to trust a `.hash` file).
    That weaker rule cannot see an `.olean` that was replaced by an OLDER file
    (a rename, `cp -p`, or a corrupted artifact restored from
    `$LAKE_CACHE_DIR`). Any unreadable, missing, or unrecognized record fails
    closed.
    """
    lake_lib_dir = anneal_root / ".lake/build/lib/lean"
    trusted_lean_dir = anneal_root / "trusted/lean"
    toolchain_version = _read_lean_toolchain_version(anneal_root)
    if toolchain_version is None:
        return (False, "cannot determine pinned Lean version from lean-toolchain")

    # Mutants are compiled by plain `lean`, so a baseline built by Lake is only
    # comparable when the lakefile adds nothing (options, arguments, weak
    # arguments that Lake does not even record in its traces).
    pkg_name, pkg_err = _read_lakefile_trusted_pkg_name(anneal_root)
    if pkg_name is None:
        return (False, pkg_err)

    olean_hashes: dict[str, str] = {}
    all_arts_hashes: dict[str, int] = {}
    legacy_trans_hashes: dict[str, int] = {}
    saw_synthetic = False
    effective_githash: str | None = None

    for mod in modules:
        olean = lake_lib_dir / f"{mod}.olean"
        hash_path = lake_lib_dir / f"{mod}.olean.hash"
        trace_path = lake_lib_dir / f"{mod}.trace"
        try:
            trace = json.loads(trace_path.read_text(encoding="utf-8"))
            hash_file_text = hash_path.read_text(encoding="utf-8").strip()
            src_bytes = (trusted_lean_dir / f"{mod}.lean").read_bytes()
            olean_stat = olean.stat()
            hash_stat = hash_path.stat()
        except (OSError, ValueError) as exc:
            return (False, f"{mod}: unreadable Lake build record ({exc})")
        if (
            not isinstance(trace, dict)
            or trace.get("schemaVersion") not in LAKE_TRACE_SCHEMA_VERSIONS
        ):
            return (False, f"{mod}: unsupported Lake trace schema")

        outputs = trace.get("outputs")
        if isinstance(outputs, dict) and outputs.get("m") is True:
            return (False, f"{mod}: module-system Lake artifacts are not supported")
        olean_outputs = outputs.get("o") if isinstance(outputs, dict) else None
        if isinstance(olean_outputs, str):
            olean_outputs = [olean_outputs]
        if not (
            isinstance(olean_outputs, list)
            and len(olean_outputs) == 1
            and isinstance(olean_outputs[0], str)
        ):
            return (False, f"{mod}: unrecognized `.olean` outputs in Lake trace")
        output_match = _LAKE_OLEAN_OUTPUT_RE.fullmatch(olean_outputs[0])
        if output_match is None:
            return (False, f"{mod}: unrecognized `.olean` outputs in Lake trace")
        olean_hash = output_match.group(1)
        if hash_file_text != olean_hash:
            return (False, f"{mod}: `.olean.hash` disagrees with Lake trace")
        if verify_olean_bytes or hash_stat.st_mtime_ns < olean_stat.st_mtime_ns:
            try:
                actual_olean_hash = lake_hash_of_bytes(olean.read_bytes())
            except OSError as exc:
                return (False, f"{mod}: unreadable `.olean` ({exc})")
            if actual_olean_hash != olean_hash:
                return (False, f"{mod}: `.olean` bytes do not match Lake trace")

        synthetic = trace.get("synthetic")
        if not isinstance(synthetic, bool):
            return (False, f"{mod}: unrecognized `synthetic` flag in Lake trace")

        src_text = src_bytes.decode("utf-8", errors="replace")
        is_module, all_imports, header_complete = _parse_lean_header_ex(src_text)
        if not header_complete:
            return (False, f"{mod}: cannot parse every import of the source")
        trusted_imports = [imp for imp in all_imports if imp.startswith("Trusted/")]
        olean_hashes[mod] = olean_hash
        all_arts_hashes[mod] = _lean_mix_hash(_LAKE_HASH_NIL, int(olean_hash, 16))

        if synthetic:
            saw_synthetic = True
            if is_module:
                return (
                    False,
                    f"{mod}: `module` files are unsupported for synthetic Lake trace verification",
                )
            non_trusted = [imp for imp in all_imports if not imp.startswith("Trusted/")]
            if non_trusted:
                return (
                    False,
                    f"{mod}: non-Trusted import(s) {non_trusted!r} unsupported for synthetic Lake trace",
                )
            if effective_githash is None:
                if lean_githash is not None:
                    if not _LEAN_GITHASH_RE.fullmatch(lean_githash):
                        return (
                            False,
                            f"{mod}: invalid lean_githash {lean_githash!r} for synthetic Lake trace",
                        )
                    effective_githash = lean_githash
                elif lean_bin is not None:
                    effective_githash, git_err = _query_lean_toolchain_githash(
                        lean_bin, anneal_root, toolchain_version
                    )
                    if effective_githash is None:
                        return (False, f"{mod}: {git_err}")
                else:
                    return (
                        False,
                        f"{mod}: synthetic Lake trace requires active Lean githash to verify depHash",
                    )
            for dep in trusted_imports:
                if dep not in legacy_trans_hashes or dep not in all_arts_hashes:
                    return (
                        False,
                        f"{mod}: imports {dep}, which was not verified for synthetic Lake trace",
                    )
            expected_dep_hash, mod_legacy_trans = lake_module_dep_hash(
                module=mod,
                src_bytes=src_bytes,
                direct_imports=trusted_imports,
                all_arts_hashes=all_arts_hashes,
                legacy_trans_hashes=legacy_trans_hashes,
                lean_githash=effective_githash,
                pkg_name=pkg_name,
            )
            recorded_dep_hash = trace.get("depHash")
            if not isinstance(recorded_dep_hash, str) or recorded_dep_hash != expected_dep_hash:
                return (
                    False,
                    f"{mod}: synthetic Lake trace depHash mismatch "
                    f"(expected {expected_dep_hash}, got {recorded_dep_hash!r})",
                )
            legacy_trans_hashes[mod] = mod_legacy_trans
            continue

        if is_module:
            return (False, f"{mod}: `module` files are unsupported for Lake trace verification")
        if len(trusted_imports) != len(all_imports):
            return (False, f"{mod}: non-Trusted imports are unsupported for Lake trace verification")
        inputs = _trace_pairs(trace.get("inputs"))
        src_suffix = f"/trusted/lean/{mod}.lean"
        src_hashes = [
            value
            for caption, value in inputs
            if caption.replace("\\", "/").endswith(src_suffix)
        ]
        if len(src_hashes) != 1 or src_hashes[0] != lake_hash_of_text(src_bytes):
            return (False, f"{mod}: source text differs from the Lake-built source")
        toolchains = [caption for caption, _ in inputs if caption.startswith("Lean ")]
        if len(toolchains) != 1 or not toolchains[0].startswith(
            f"Lean {toolchain_version},"
        ):
            return (False, f"{mod}: built by a different Lean toolchain")
        # Mutants are compiled by plain `lean` with no extra options, so the
        # baseline must have been built that way too. Avoid `dict(inputs)` so
        # duplicate entries cannot overwrite earlier non-default values.
        options_vals = [value for caption, value in inputs if caption == "options"]
        lean_args_entries = [
            (caption, value)
            for caption, value in inputs
            if caption.startswith("Module.leanArgs:")
        ]
        if options_vals != [_LAKE_HASH_NIL_HEX] or lean_args_entries != [
            (_LAKE_DEFAULT_LEAN_ARGS_CAPTION, _LAKE_HASH_NIL_HEX)
        ]:
            return (False, f"{mod}: built with non-default Lean options or arguments")

        deps_vals = [value for caption, value in inputs if caption == "deps"]
        if len(deps_vals) != 1:
            return (False, f"{mod}: unrecognized imports record in Lake trace")
        imports_vals = [
            value
            for caption, value in _trace_pairs(deps_vals[0])
            if caption == "imports"
        ]
        if len(imports_vals) != 1:
            return (False, f"{mod}: unrecognized imports record in Lake trace")
        imports_node = imports_vals[0]
        import_arts: dict[str, str] = {}
        import_legacy: dict[str, str] = {}
        if isinstance(imports_node, list):
            for entry in imports_node:
                if not (
                    isinstance(entry, list)
                    and len(entry) == 2
                    and isinstance(entry[0], str)
                    and isinstance(entry[1], str)
                ):
                    return (
                        False,
                        f"{mod}: unrecognized imports record in Lake trace",
                    )
                caption, value = entry
                matched_sink: dict[str, str] | None = None
                dep = ""
                for suffix, sink in (
                    (_LAKE_IMPORT_ARTS_SUFFIX, import_arts),
                    (_LAKE_IMPORT_LEGACY_SUFFIX, import_legacy),
                ):
                    if caption.endswith(suffix):
                        dep = caption[: -len(suffix)].replace(".", "/")
                        matched_sink = sink
                        break
                if matched_sink is None or not dep.startswith("Trusted/"):
                    return (
                        False,
                        f"{mod}: unrecognized imports record in Lake trace ({caption!r})",
                    )
                if dep in matched_sink and matched_sink[dep] != value:
                    return (
                        False,
                        f"{mod}: conflicting duplicate import record for {dep} in Lake trace",
                    )
                matched_sink[dep] = value
        elif imports_node != _LAKE_HASH_NIL_HEX:
            return (False, f"{mod}: unrecognized imports record in Lake trace")
        if set(import_arts) != set(trusted_imports) or set(import_legacy) != set(
            trusted_imports
        ):
            return (False, f"{mod}: Lake trace imports differ from source imports")

        for dep in trusted_imports:
            if dep not in olean_hashes or dep not in legacy_trans_hashes:
                return (False, f"{mod}: imports {dep}, which was not verified")
            if import_arts[dep] != lake_import_arts_hash(olean_hashes[dep]):
                return (False, f"{mod}: built against a different {dep}.olean")
            # The direct import's `.olean` hash does not pin that import's own
            # imports; Lake's transitive-import hash for it does.
            if import_legacy[dep] != f"{legacy_trans_hashes[dep]:016x}":
                return (
                    False,
                    f"{mod}: built against different transitive imports of {dep}",
                )
        legacy_trans_hashes[mod] = lake_legacy_trans_hash(
            trusted_imports, all_arts_hashes, legacy_trans_hashes
        )

    if saw_synthetic:
        return (True, "lake-trace-verified (synthetic)")
    return (True, "lake-trace-verified")


def _legacy_mtime_fresh(
    anneal_root: Path,
    modules: Sequence[str],
) -> bool:
    """mtime freshness for build trees WITHOUT Lake traces.

    Requires `olean.mtime >= src.mtime` for the module and for every upstream
    module. This is conservative in one direction only (a touched source forces
    a cold build); it cannot notice an `.olean` built from different content
    with a newer mtime, which is why Lake-traced trees never use it.
    """
    lake_lib_dir = anneal_root / ".lake/build/lib/lean"
    trusted_lean_dir = anneal_root / "trusted/lean"

    src_mtimes: dict[str, float] = {}
    for mod in modules:
        try:
            src_mtimes[mod] = (trusted_lean_dir / f"{mod}.lean").stat().st_mtime
        except OSError:
            return False

    base_max_mtime = max(
        (src_mtimes[m] for m in BASE_TRUSTED_MODULES if m in src_mtimes),
        default=0.0,
    )

    for idx, mod in enumerate(modules):
        try:
            olean_mtime = (lake_lib_dir / f"{mod}.olean").stat().st_mtime
        except OSError:
            return False
        if mod in SEMANTICS_UPSTREAM:
            dep_mtimes = [base_max_mtime, src_mtimes[mod]]
            for dep in SEMANTICS_UPSTREAM[mod]:
                if dep in src_mtimes:
                    dep_mtimes.append(src_mtimes[dep])
            req_mtime = max(dep_mtimes)
        else:
            req_mtime = max(src_mtimes[m] for m in modules[: idx + 1])
        if olean_mtime < req_mtime:
            return False
    return True


def _lake_olean_reuse_decision(
    anneal_root: Path,
    modules: Sequence[str],
    *,
    verify_olean_bytes: bool = True,
    lean_bin: Path | None = None,
    lean_githash: str | None = None,
) -> tuple[bool, str]:
    """Decide whether `.lake/build/lib/lean` `.olean`s may seed the baseline.

    Returns `(reusable, reason)`. Lake-traced trees are validated by content
    (`_verify_lake_traces`) and mtimes play no part, so a fresh `git worktree`
    with new source mtimes still reuses a matching build, and a build of
    different sources is rejected even when its `.olean`s are newer. Trees with
    no Lake traces at all fall back to `_legacy_mtime_fresh`. A tree with
    traces for only some modules is rejected.
    """
    lake_lib_dir = anneal_root / ".lake/build/lib/lean"
    trusted_lean_dir = anneal_root / "trusted/lean"
    if not lake_lib_dir.is_dir():
        return (False, "no .lake/build/lib/lean")
    for mod in modules:
        if not (trusted_lean_dir / f"{mod}.lean").is_file():
            return (False, f"{mod}: missing source")
        if not (lake_lib_dir / f"{mod}.olean").is_file():
            return (False, f"{mod}: missing .olean")

    traced = [(lake_lib_dir / f"{mod}.trace").is_file() for mod in modules]
    if not any(traced):
        if _legacy_mtime_fresh(anneal_root, modules):
            return (True, "legacy-mtime")
        return (False, "no Lake traces and a source is newer than its .olean")
    if not all(traced):
        return (False, "Lake traces present for only some modules")
    return _verify_lake_traces(
        anneal_root,
        modules,
        verify_olean_bytes=verify_olean_bytes,
        lean_bin=lean_bin,
        lean_githash=lean_githash,
    )


def _olean_fingerprints(
    olean_dir: Path,
    modules: Sequence[str],
) -> dict[str, tuple[int, int, int]]:
    """Return `(inode, size, mtime_ns)` for every compiled artifact of `modules`."""
    prints: dict[str, tuple[int, int, int]] = {}
    for mod in modules:
        for suffix in OLEAN_SUFFIXES:
            art = olean_dir / f"{mod}{suffix}"
            try:
                st = art.stat()
            except OSError:
                continue
            prints[f"{mod}{suffix}"] = (st.st_ino, st.st_size, st.st_mtime_ns)
    return prints


def _link_or_copy(src: Path, dst: Path) -> None:
    """Hardlink (or copy) `src` to `dst` without ever writing through `dst`.

    An existing `dst` may itself be a hardlink into `.lake/build` or the
    baseline tree, so it is unlinked first: both `os.link` and the copy
    fallback then create a new directory entry instead of truncating a shared
    inode in place.
    """
    dst.parent.mkdir(parents=True, exist_ok=True)
    real_src = os.path.realpath(src)
    try:
        dst.unlink()
    except FileNotFoundError:
        pass
    try:
        os.link(real_src, dst)
    except OSError:
        shutil.copy2(real_src, dst)


def _seed_olean_tree(
    src_olean_dir: Path,
    dst_olean_dir: Path,
    modules: Sequence[str],
    *,
    skip_modules: set[str] | None = None,
) -> None:
    """Hardlink (or copy) `.olean` and companion artifacts for `modules`."""
    skipped = skip_modules or set()
    for mod in modules:
        if mod in skipped:
            continue
        for suffix in OLEAN_SUFFIXES:
            src_art = src_olean_dir / f"{mod}{suffix}"
            if src_art.is_file():
                dst_art = dst_olean_dir / f"{mod}{suffix}"
                _link_or_copy(src_art, dst_art)


# Live Lean process groups, so an interrupt can stop them. Lean runs in its
# own session (see `_run_lean`) and therefore does not receive the terminal's
# Ctrl-C by itself.
_LIVE_PROCS: set[subprocess.Popen[str]] = set()
_LIVE_PROCS_LOCK = threading.Lock()

# Set while a run is being torn down, so workers that are between two Lean
# invocations do not start another one.
_ABORT = threading.Event()


def _kill_process_group(proc: subprocess.Popen[str]) -> None:
    """SIGKILL `proc`'s whole process group (wrapper AND the Lean it spawned)."""
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError, OSError):
        pass
    try:
        proc.kill()
    except OSError:
        pass


def _abort_pending(futures: Sequence[Future[object]]) -> None:
    """Stop a failing or interrupted run promptly.

    Called BEFORE the worker pool is joined: unstarted work is cancelled, and
    `_ABORT.set()` plus the `_LIVE_PROCS` snapshot execute atomically under
    `_LIVE_PROCS_LOCK` so any concurrent `_run_lean` returning from `Popen`
    observes `_ABORT` under the same lock and kills its own process group
    immediately instead of slipping past teardown.
    """
    for fut in futures:
        fut.cancel()
    with _LIVE_PROCS_LOCK:
        _ABORT.set()
        procs = list(_LIVE_PROCS)
    for proc in procs:
        _kill_process_group(proc)


def _run_lean(
    lean_bin: Path,
    args: Sequence[str],
    *,
    anneal_root: Path,
    lean_path: Sequence[Path],
    timeout_sec: int,
    lean_run_wrapper: Path | None,
) -> subprocess.CompletedProcess[str]:
    """Execute Lean in `cwd=anneal_root` with explicit `LEAN_PATH`.

    Never raises for a failed, missing, or hung Lean: a spawn failure returns
    `rc=127` and a timeout returns `rc=124`, so callers classify them as
    errors. Lean runs in its own process group; on timeout the WHOLE group is
    killed, because killing only an `anneal-lean-run` wrapper would leave the
    real `lean` running and still writing into a temporary directory that is
    about to be deleted.
    """
    cmd = _build_lean_command(lean_bin, args, lean_run_wrapper=lean_run_wrapper)
    if _ABORT.is_set():
        return subprocess.CompletedProcess(
            args=cmd, returncode=130, stdout="", stderr="run aborted before Lean started"
        )
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in lean_path)
    try:
        proc = subprocess.Popen(
            cmd,
            cwd=str(anneal_root),
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            start_new_session=True,
        )
    except OSError as exc:
        return subprocess.CompletedProcess(
            args=cmd,
            returncode=127,
            stdout="",
            stderr=f"failed to execute Lean command {cmd[0]!r}: {exc}",
        )
    aborted_during_spawn = False
    with _LIVE_PROCS_LOCK:
        if _ABORT.is_set():
            aborted_during_spawn = True
        else:
            _LIVE_PROCS.add(proc)
    if aborted_during_spawn:
        _kill_process_group(proc)
        try:
            with proc:
                proc.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            pass
        return subprocess.CompletedProcess(
            args=cmd,
            returncode=130,
            stdout="",
            stderr="run aborted while Lean was starting",
        )
    try:
        with proc:
            try:
                out, err = proc.communicate(timeout=timeout_sec)
            except subprocess.TimeoutExpired:
                _kill_process_group(proc)
                try:
                    out, err = proc.communicate(timeout=10)
                except subprocess.TimeoutExpired:
                    out, err = "", ""
                return subprocess.CompletedProcess(
                    args=cmd,
                    returncode=124,
                    stdout=out or "",
                    stderr=(
                        f"{err or ''}\nLean invocation timed out after "
                        f"{timeout_sec}s"
                    ).strip(),
                )
            except BaseException:
                _kill_process_group(proc)
                raise
            return subprocess.CompletedProcess(
                args=cmd,
                returncode=proc.returncode,
                stdout=out or "",
                stderr=err or "",
            )
    finally:
        with _LIVE_PROCS_LOCK:
            _LIVE_PROCS.discard(proc)


def _compile_module(
    lean_bin: Path,
    root_dir: Path,
    module: str,
    out_dir: Path,
    *,
    anneal_root: Path,
    lean_path: Sequence[Path],
    timeout_sec: int,
    lean_run_wrapper: Path | None,
) -> subprocess.CompletedProcess[str]:
    """Compile `<root_dir>/<module>.lean` to `<out_dir>/<module>.olean`.

    Any existing output artifact is unlinked first. `.olean`s in `out_dir` may
    be hardlinks into the baseline tree or `.lake/build`, and Lean writes its
    output in place, so compiling over one would rewrite the shared inode.
    """
    src = root_dir / f"{module}.lean"
    olean = out_dir / f"{module}.olean"
    olean.parent.mkdir(parents=True, exist_ok=True)
    for suffix in OLEAN_SUFFIXES:
        try:
            (out_dir / f"{module}{suffix}").unlink()
        except FileNotFoundError:
            pass
    return _run_lean(
        lean_bin,
        ["-R", str(root_dir), "-o", str(olean), str(src)],
        anneal_root=anneal_root,
        lean_path=lean_path,
        timeout_sec=timeout_sec,
        lean_run_wrapper=lean_run_wrapper,
    )


def _verify_one_baseline_guard(
    guard: MirSemanticsGuard,
    *,
    anneal_root: Path,
    lean_bin: Path,
    base_olean_dir: Path,
    fixture_src_dir: Path,
    fixture_olean_dir: Path,
    timeout_sec: int,
    lean_run_wrapper: Path | None,
) -> None:
    """Confirm sanity and refutation fixtures compile with 0 errors and 0 sorrys."""
    for kind, mod_name, src_text in (
        ("sanity", guard.sanity_module, guard.sanity_source),
        ("refute", guard.refute_module, guard.refute_source),
    ):
        src_path = fixture_src_dir / f"{mod_name}.lean"
        src_path.write_text(src_text, encoding="utf-8")
        res = _compile_module(
            lean_bin,
            fixture_src_dir,
            mod_name,
            fixture_olean_dir,
            anneal_root=anneal_root,
            lean_path=[base_olean_dir],
            timeout_sec=timeout_sec,
            lean_run_wrapper=lean_run_wrapper,
        )
        combined = (res.stdout + "\n" + res.stderr).strip()
        if res.returncode != 0 or _has_sorry_warning(combined):
            raise RuntimeError(
                f"baseline {kind} fixture {mod_name} failed on unmodified TCB "
                f"(rc={res.returncode}):\n{combined}"
            )


def _check_one_mir_guard(
    guard: MirSemanticsGuard,
    *,
    anneal_root: Path,
    lean_bin: Path,
    base_olean_dir: Path,
    baseline_modules: Sequence[str],
    timeout_sec: int,
    lean_run_wrapper: Path | None,
) -> GuardResult:
    """Mutate a single guard in an isolated TemporaryDirectory and classify kill."""
    t0 = time.monotonic()

    def _result(status: str, detail: str) -> GuardResult:
        return GuardResult(
            guard_id=guard.guard_id,
            target_file=guard.target_file,
            target_module=guard.target_module,
            quick=guard.quick,
            status=status,
            duration_sec=round(time.monotonic() - t0, 3),
            detail=detail,
        )

    trusted_lean_dir = anneal_root / "trusted/lean"
    src_path = anneal_root / guard.target_file
    original_text = src_path.read_text(encoding="utf-8")
    try:
        mutated_text = apply_single_guard_mutation(
            original_text,
            guard.anchor,
            guard.replacement,
            guard_id=guard.guard_id,
        )
    except ValueError as exc:
        return _result("ERROR", str(exc))

    theorem_span = find_theorem_line_span(guard.refute_source, guard.theorem_name)
    rebuild_mods = guard.effective_rebuild_modules

    with tempfile.TemporaryDirectory(
        prefix=f"anneal-gmut-{guard.guard_id}-"
    ) as tmp:
        tmp_path = Path(tmp)
        mut_src_root = tmp_path / "trusted_lean"
        mut_olean_dir = tmp_path / "olean"
        fixture_src_dir = tmp_path / "fixtures"
        fixture_olean_dir = tmp_path / "fixture_olean"
        mut_olean_dir.mkdir()
        fixture_src_dir.mkdir()
        fixture_olean_dir.mkdir()

        # Write ONLY the mutated TCB source into the isolated temp overlay.
        mut_target_path = mut_src_root / f"{guard.target_module}.lean"
        mut_target_path.parent.mkdir(parents=True, exist_ok=True)
        mut_target_path.write_text(mutated_text, encoding="utf-8")

        # Hardlink every still-valid TCB `.olean` from `base_olean_dir` into
        # `mut_olean_dir` so Lean 4 sees a complete `Trusted.*` root namespace
        # in a single `LEAN_PATH` directory. Modules that will be recompiled
        # here, and modules left stale by the mutation, are NOT seeded.
        _seed_olean_tree(
            base_olean_dir,
            mut_olean_dir,
            baseline_modules,
            skip_modules=set(rebuild_mods) | _stale_modules_for_guard(guard),
        )

        lean_path = [mut_olean_dir]

        # 1. Recompile the mutated TCB module (and any declared downstream).
        for idx, mod in enumerate(rebuild_mods):
            root_for_mod = mut_src_root if idx == 0 else trusted_lean_dir
            res = _compile_module(
                lean_bin,
                root_for_mod,
                mod,
                mut_olean_dir,
                anneal_root=anneal_root,
                lean_path=lean_path,
                timeout_sec=timeout_sec,
                lean_run_wrapper=lean_run_wrapper,
            )
            mod_combined = (res.stdout + "\n" + res.stderr).strip()
            if res.returncode != 0 or _has_sorry_warning(mod_combined):
                return _result(
                    "ERROR",
                    f"mutated semantics module {mod} failed to compile cleanly "
                    f"(rc={res.returncode}): "
                    f"{mod_combined[:300]}",
                )
            mut_olean = mut_olean_dir / f"{mod}.olean"
            base_olean = base_olean_dir / f"{mod}.olean"
            if not mut_olean.is_file():
                return _result(
                    "ERROR",
                    f"mutated semantics module {mod} compiled (rc=0) but "
                    "produced no .olean",
                )
            if base_olean.exists() and os.path.samefile(mut_olean, base_olean):
                return _result(
                    "ERROR",
                    f"mutated {mod}.olean shares an inode with the baseline "
                    ".olean (hardlink write-through)",
                )

        # 2. Positive sanity theorem MUST still compile cleanly with 0 sorrys.
        sanity_path = fixture_src_dir / f"{guard.sanity_module}.lean"
        sanity_path.write_text(guard.sanity_source, encoding="utf-8")
        sanity_res = _compile_module(
            lean_bin,
            fixture_src_dir,
            guard.sanity_module,
            fixture_olean_dir,
            anneal_root=anneal_root,
            lean_path=lean_path,
            timeout_sec=timeout_sec,
            lean_run_wrapper=lean_run_wrapper,
        )
        sanity_combined = (sanity_res.stdout + "\n" + sanity_res.stderr).strip()
        if sanity_res.returncode != 0 or _has_sorry_warning(sanity_combined):
            return _result(
                "ERROR",
                f"positive sanity {guard.sanity_module} broke on mutant "
                f"(rc={sanity_res.returncode}): {sanity_combined[:300]}",
            )

        # 3. Negative refutation theorem MUST fail with a localized proof error.
        refute_path = fixture_src_dir / f"{guard.refute_module}.lean"
        refute_path.write_text(guard.refute_source, encoding="utf-8")
        refute_res = _compile_module(
            lean_bin,
            fixture_src_dir,
            guard.refute_module,
            fixture_olean_dir,
            anneal_root=anneal_root,
            lean_path=lean_path,
            timeout_sec=timeout_sec,
            lean_run_wrapper=lean_run_wrapper,
        )
        status, detail = classify_refutation_failure(
            refute_res.returncode,
            refute_res.stdout,
            f"{guard.refute_module}.lean",
            theorem_span,
            stderr_output=refute_res.stderr,
        )
        return _result(status, detail)


def _check_one_mir_guard_safe(
    guard: MirSemanticsGuard,
    **kwargs: object,
) -> GuardResult:
    """Run `_check_one_mir_guard`, turning an unexpected exception into `ERROR`.

    One guard's I/O failure must not abort the worker pool and discard every
    other guard's result.
    """
    t0 = time.monotonic()
    try:
        return _check_one_mir_guard(guard, **kwargs)  # type: ignore[arg-type]
    except Exception as exc:  # noqa: BLE001 - reported as a per-guard ERROR
        return GuardResult(
            guard_id=guard.guard_id,
            target_file=guard.target_file,
            target_module=guard.target_module,
            quick=guard.quick,
            status="ERROR",
            duration_sec=round(time.monotonic() - t0, 3),
            detail=f"internal error: {type(exc).__name__}: {exc}",
        )


def run_guard_mutation_suite(
    *,
    anneal_root: Path,
    lean_bin: Path,
    quick: bool = False,
    guard_filters: Sequence[str] | None = None,
    jobs: int = 4,
    timeout_sec: int = 120,
    lean_run_wrapper: Path | None = None,
    reuse_lake_cache: bool = True,
    verify_lake_olean_bytes: bool = True,
) -> dict[str, object]:
    """Run baseline verification and all selected single-guard mutations."""
    _ABORT.clear()
    try:
        return _run_guard_mutation_suite(
            anneal_root=anneal_root,
            lean_bin=lean_bin,
            quick=quick,
            guard_filters=guard_filters,
            jobs=jobs,
            timeout_sec=timeout_sec,
            lean_run_wrapper=lean_run_wrapper,
            reuse_lake_cache=reuse_lake_cache,
            verify_lake_olean_bytes=verify_lake_olean_bytes,
        )
    finally:
        _ABORT.clear()


def _run_guard_mutation_suite(
    *,
    anneal_root: Path,
    lean_bin: Path,
    quick: bool,
    guard_filters: Sequence[str] | None,
    jobs: int,
    timeout_sec: int,
    lean_run_wrapper: Path | None,
    reuse_lake_cache: bool,
    verify_lake_olean_bytes: bool,
) -> dict[str, object]:
    t_start = time.monotonic()
    catalog_errors = validate_catalog_invariants(anneal_root)
    if catalog_errors:
        raise RuntimeError(
            "guard catalog validation failed:\n  - "
            + "\n  - ".join(catalog_errors)
        )

    selected_guards = select_guards(quick=quick, guard_filters=guard_filters)
    if not selected_guards:
        raise RuntimeError("no guards selected")

    mode_label = "quick" if quick else ("guard" if guard_filters else "all")
    baseline_modules = _baseline_modules_for_guards(selected_guards)
    trusted_lean_dir = anneal_root / "trusted/lean"
    lake_lib_dir = anneal_root / ".lake/build/lib/lean"
    worker_count = max(1, min(jobs, len(selected_guards)))
    used_lake_cache = False
    lake_cache_detail = "disabled by --no-lake-cache"
    lake_prints: dict[str, tuple[int, int, int]] = {}
    baseline_sec = 0.0
    results: list[GuardResult] = []

    with tempfile.TemporaryDirectory(prefix="anneal-gmut-base-") as base_tmp:
        base_path = Path(base_tmp)
        base_olean_dir = base_path / "olean"
        fixture_src_dir = base_path / "fixtures"
        fixture_olean_dir = base_path / "fixture_olean"
        base_olean_dir.mkdir()
        fixture_src_dir.mkdir()
        fixture_olean_dir.mkdir()

        t_base = time.monotonic()
        if reuse_lake_cache:
            used_lake_cache, lake_cache_detail = _lake_olean_reuse_decision(
                anneal_root,
                baseline_modules,
                verify_olean_bytes=verify_lake_olean_bytes,
                lean_bin=lean_bin,
            )
        if used_lake_cache:
            lake_prints = _olean_fingerprints(lake_lib_dir, baseline_modules)
            _seed_olean_tree(lake_lib_dir, base_olean_dir, baseline_modules)
        else:
            for mod in baseline_modules:
                res = _compile_module(
                    lean_bin,
                    trusted_lean_dir,
                    mod,
                    base_olean_dir,
                    anneal_root=anneal_root,
                    lean_path=[base_olean_dir],
                    timeout_sec=timeout_sec,
                    lean_run_wrapper=lean_run_wrapper,
                )
                if res.returncode != 0:
                    raise RuntimeError(
                        f"baseline trusted module {mod} failed to compile "
                        f"(rc={res.returncode}):\n{res.stdout}\n{res.stderr}"
                    )

        # Verify every selected guard's positive sanity AND negative refutation
        # compile cleanly on unmodified TCB `.olean`s with zero `sorry`s.
        with ThreadPoolExecutor(max_workers=worker_count) as pool:
            base_futs = [
                pool.submit(
                    _verify_one_baseline_guard,
                    guard,
                    anneal_root=anneal_root,
                    lean_bin=lean_bin,
                    base_olean_dir=base_olean_dir,
                    fixture_src_dir=fixture_src_dir,
                    fixture_olean_dir=fixture_olean_dir,
                    timeout_sec=timeout_sec,
                    lean_run_wrapper=lean_run_wrapper,
                )
                for guard in selected_guards
            ]
            try:
                for fut in as_completed(base_futs):
                    fut.result()
            except BaseException:
                _abort_pending(base_futs)
                raise

        baseline_sec = time.monotonic() - t_base

        # Run single-guard mutations in parallel inside isolated temp dirs.
        with ThreadPoolExecutor(max_workers=worker_count) as pool:
            future_map = {
                pool.submit(
                    _check_one_mir_guard_safe,
                    guard,
                    anneal_root=anneal_root,
                    lean_bin=lean_bin,
                    base_olean_dir=base_olean_dir,
                    baseline_modules=baseline_modules,
                    timeout_sec=timeout_sec,
                    lean_run_wrapper=lean_run_wrapper,
                ): guard
                for guard in selected_guards
            }
            by_id: dict[str, GuardResult] = {}
            try:
                for fut in as_completed(future_map):
                    res = fut.result()
                    by_id[res.guard_id] = res
            except BaseException:
                _abort_pending(list(future_map))
                raise
        results.extend(by_id[g.guard_id] for g in selected_guards)

        # The reused Lake artifacts are shared by hardlink. Prove that nothing
        # in this run wrote through one.
        if used_lake_cache and _olean_fingerprints(
            lake_lib_dir, baseline_modules
        ) != lake_prints:
            raise RuntimeError(
                ".lake/build/lib/lean artifacts changed during the run "
                "(hardlink write-through or concurrent build); results discarded"
            )

    total = len(results)
    killed = sum(1 for r in results if r.status == "KILLED")
    survived = sum(1 for r in results if r.status == "SURVIVED")
    errors = sum(1 for r in results if r.status == "ERROR")
    return {
        "ok": total > 0 and killed == total and survived == 0 and errors == 0,
        "fatal_error": None,
        "mode": mode_label,
        "used_lake_cache": used_lake_cache,
        "lake_cache_detail": lake_cache_detail,
        "lean_bin": str(lean_bin),
        "lean_run_wrapper": str(lean_run_wrapper) if lean_run_wrapper else None,
        "total": total,
        "killed": killed,
        "survived": survived,
        "errors": errors,
        "kill_rate_pct": round((100.0 * killed / total), 2) if total else 0.0,
        "baseline_sec": round(baseline_sec, 3),
        "total_sec": round(time.monotonic() - t_start, 3),
        "results": [asdict(r) for r in results],
    }


def _default_anneal_root() -> Path:
    return Path(__file__).resolve().parent.parent


def _resolve_lean_binary(explicit: Path | None) -> Path:
    """Resolve the Lean executable to an ABSOLUTE path.

    Lean always runs with `cwd=<anneal_root>`, so a relative path would stop
    resolving. The path is made absolute without following symlinks:
    `~/.elan/bin/lean` is a symlink to the `elan` proxy, which picks the tool
    from the name it was invoked as.
    """
    if explicit is not None:
        if not explicit.is_file():
            raise SystemExit(f"Lean binary not found: {explicit}")
        return Path(os.path.abspath(explicit))
    env_lean = os.environ.get("ANNEAL_LEAN")
    if env_lean:
        cand = Path(env_lean)
        if cand.is_file():
            return Path(os.path.abspath(cand))
    found = shutil.which("lean")
    if found:
        return Path(os.path.abspath(found))
    elan_lean = Path.home() / ".elan/bin/lean"
    if elan_lean.is_file():
        return elan_lean
    raise SystemExit(
        "Lean binary not found; pass --lean <path>, set ANNEAL_LEAN, or install elan"
    )


def _format_summary(report: dict[str, object]) -> str:
    lines: list[str] = []
    for entry in report["results"]:  # type: ignore[index]
        tag = "quick" if entry["quick"] else "full "
        lines.append(
            f"[{entry['status']:8s}] ({tag}) "
            f"{entry['guard_id']:42s} {entry['duration_sec']:5.2f}s  "
            f"{entry['detail']}"
        )
    cache_note = "lake-cache" if report["used_lake_cache"] else "cold-build"
    lines.append(f"Baseline .olean source: {cache_note} ({report['lake_cache_detail']})")
    lines.append(
        f"MIR guard-mutation summary ({report['mode']}, {cache_note}): "
        f"{report['killed']}/{report['total']} killed "
        f"({report['kill_rate_pct']:.1f}%), {report['survived']} survived, "
        f"{report['errors']} errors "
        f"(baseline {report['baseline_sec']:.2f}s, total {report['total_sec']:.2f}s)"
    )
    return "\n".join(lines)


def _fatal_report(mode_label: str, message: str) -> dict[str, object]:
    """Report for a run that failed before producing per-guard results.

    Carries exactly the keys of a finished run's report, so a consumer never
    has to special-case a missing key: `ok` is the verdict either way.
    """
    return {
        "ok": False,
        "fatal_error": message,
        "mode": mode_label,
        "used_lake_cache": False,
        "lake_cache_detail": "",
        "lean_bin": None,
        "lean_run_wrapper": None,
        "total": 0,
        "killed": 0,
        "survived": 0,
        "errors": 1,
        "kill_rate_pct": 0.0,
        "baseline_sec": 0.0,
        "total_sec": 0.0,
        "results": [],
    }


# Exit status of a run cut short by SIGINT, SIGTERM or SIGHUP.
EXIT_INTERRUPTED = 130


@contextlib.contextmanager
def _termination_signals_as_interrupt() -> Iterator[None]:
    """Deliver SIGTERM and SIGHUP as `KeyboardInterrupt`, exactly like SIGINT.

    Python's default action for both kills the interpreter on the spot. No
    `finally` or `with` exit runs, so every `anneal-gmut-*` directory leaks,
    and each Lean child keeps compiling: it runs in its own session, where a
    signal sent to this process's group (CI cancel, `timeout`) cannot reach it.

    Only a signal still at its default action is taken over, so `nohup` (which
    ignores SIGHUP) and an embedding program's own handlers keep working.
    """

    def _raise(signum: int, _frame: object) -> None:
        raise KeyboardInterrupt(signal.Signals(signum).name)

    taken_over: list[int] = []
    try:
        for name in ("SIGTERM", "SIGHUP"):
            signum = getattr(signal, name, None)
            if signum is not None and signal.getsignal(signum) is signal.SIG_DFL:
                signal.signal(signum, _raise)
                taken_over.append(signum)
    except ValueError:
        # Not the main thread: signal handling belongs to the embedding program.
        pass
    try:
        yield
    finally:
        for signum in taken_over:
            signal.signal(signum, signal.SIG_DFL)


def _write_json_out(path: Path, report: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Single-guard mutation testing gate for Anneal's "
            "Trusted.Rustc.V2026_06_01.MirSemantics."
        ),
        # A gate's flags must be spelled out: no silent `--tr` -> `--trust-...`.
        allow_abbrev=False,
    )
    mode_group = parser.add_mutually_exclusive_group()
    mode_group.add_argument(
        "--quick",
        action="store_true",
        help="Run the fast 3-guard smoke subset (Scalars, Statements, Terminators).",
    )
    mode_group.add_argument(
        "--all",
        action="store_true",
        help="Run the full catalog of all guards across all 4 MirSemantics files (default).",
    )
    parser.add_argument(
        "--guard",
        dest="guards",
        action="append",
        default=None,
        help=(
            "Run only guard(s) matching this exact guard_id or substring "
            "(repeatable; each value may be a comma-separated list)."
        ),
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="Validate static catalog invariants, list cataloged guards, and exit.",
    )
    parser.add_argument(
        "--json",
        dest="emit_json",
        action="store_true",
        help="Emit the structured JSON report to stdout (and nothing else).",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help="Write the structured JSON report to this file path.",
    )
    parser.add_argument(
        "--anneal-root",
        type=Path,
        default=_default_anneal_root(),
        help="Path to the Anneal repository root (default: script parent).",
    )
    parser.add_argument(
        "--lean",
        type=Path,
        default=None,
        help="Path to the `lean` executable (default: ANNEAL_LEAN, PATH, or ~/.elan/bin/lean).",
    )
    wrapper_group = parser.add_mutually_exclusive_group()
    wrapper_group.add_argument(
        "--use-lean-run",
        dest="use_lean_run",
        action="store_true",
        default=None,
        help="Force wrapping Lean invocations through `anneal-lean-run --mode file --`.",
    )
    wrapper_group.add_argument(
        "--no-lean-run",
        dest="use_lean_run",
        action="store_false",
        help="Invoke `lean` directly without `anneal-lean-run`.",
    )
    parser.add_argument(
        "--no-lake-cache",
        action="store_true",
        help="Do not reuse `.lake/build/lib/lean` `.olean`s for baseline seeding.",
    )
    parser.add_argument(
        "--trust-lake-olean-hash-files",
        action="store_true",
        help=(
            "Faster, weaker: trust an `.olean.hash` file that is at least as new "
            "as its `.olean` instead of re-hashing every reused `.olean` (the "
            "default). Does not notice an `.olean` replaced by an older file."
        ),
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=min(4, os.cpu_count() or 1),
        help="Maximum parallel worker threads (default: min(4, CPU count)).",
    )
    parser.add_argument(
        "--timeout-sec",
        type=int,
        default=120,
        help="Per-Lean-invocation timeout in seconds (default: 120).",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    if args.jobs < 1:
        parser.error("--jobs must be >= 1")
    if args.timeout_sec < 1:
        parser.error("--timeout-sec must be >= 1")
    if args.guards and (args.quick or args.all):
        parser.error("--guard cannot be combined with --quick or --all")
    if args.list and args.json_out is not None:
        parser.error("--json-out cannot be combined with --list")

    # Lean always runs with `cwd=<anneal_root>`; relative paths must not shift.
    anneal_root = Path(os.path.abspath(args.anneal_root))
    mode_label = "quick" if args.quick else ("guard" if args.guards else "all")

    if args.list:
        errors = validate_catalog_invariants(anneal_root)
        if errors:
            for err in errors:
                print(f"ERROR: {err}", file=sys.stderr)
            return 1
        try:
            selected = select_guards(quick=args.quick, guard_filters=args.guards)
        except ValueError as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
            return 1
        if args.emit_json:
            payload = {
                "total": len(selected),
                "guards": [
                    {
                        "guard_id": g.guard_id,
                        "target_file": g.target_file,
                        "target_module": g.target_module,
                        "quick": g.quick,
                        "description": g.description,
                        "theorem_name": g.theorem_name,
                        "sanity_theorem_name": g.sanity_theorem_name,
                    }
                    for g in selected
                ],
            }
            print(json.dumps(payload, indent=2))
        else:
            for g in selected:
                tag = "quick" if g.quick else "full "
                print(f"{tag}  {g.guard_id:42s} {g.target_file}")
            print(f"Total cataloged guards: {len(selected)}")
        return 0

    def _fail(message: str, exit_code: int = 1) -> int:
        """Report a fatal error on stderr AND in every requested JSON sink."""
        print(f"ERROR: {message}", file=sys.stderr)
        report = _fatal_report(mode_label, message)
        if args.json_out is not None:
            try:
                _write_json_out(args.json_out, report)
            except OSError as exc:
                print(f"ERROR: cannot write {args.json_out}: {exc}", file=sys.stderr)
        if args.emit_json:
            print(json.dumps(report, indent=2))
        return exit_code

    # Fail-closed sink: a `--json-out` file left by an earlier green run must
    # not outlive a run that never reports, however it dies (crash, OOM kill,
    # SIGKILL). It holds a failing report until the real one replaces it.
    if args.json_out is not None:
        try:
            _write_json_out(
                args.json_out, _fatal_report(mode_label, "run did not complete")
            )
        except OSError as exc:
            unwritable, args.json_out = args.json_out, None
            return _fail(f"cannot write {unwritable}: {exc}")

    try:
        lean_bin = _resolve_lean_binary(args.lean)
    except SystemExit as exc:
        return _fail(str(exc))

    # Wrap auto-resolved real `lean` calls through `anneal-lean-run --mode file --`
    # when available; invoke explicit custom `--lean` directly unless
    # `--use-lean-run` is explicitly requested.
    lean_run_wrapper: Path | None = None
    if args.use_lean_run is True:
        lean_run_wrapper = _resolve_lean_run_wrapper(anneal_root)
        if lean_run_wrapper is None:
            return _fail("--use-lean-run specified, but anneal-lean-run was not found")
    elif args.use_lean_run is None and args.lean is None:
        lean_run_wrapper = _resolve_lean_run_wrapper(anneal_root)

    try:
        with _termination_signals_as_interrupt():
            report = run_guard_mutation_suite(
                anneal_root=anneal_root,
                lean_bin=lean_bin,
                quick=args.quick,
                guard_filters=args.guards,
                jobs=args.jobs,
                timeout_sec=args.timeout_sec,
                lean_run_wrapper=lean_run_wrapper,
                reuse_lake_cache=not args.no_lake_cache,
                verify_lake_olean_bytes=not args.trust_lake_olean_hash_files,
            )
    except KeyboardInterrupt as exc:
        # The suite has already killed every Lean process group and removed
        # its temporary directories on the way out.
        signal_name = exc.args[0] if exc.args else "SIGINT"
        return _fail(f"interrupted by {signal_name}", EXIT_INTERRUPTED)
    except (RuntimeError, ValueError, OSError) as exc:
        return _fail(str(exc))

    if args.json_out is not None:
        try:
            _write_json_out(args.json_out, report)
        except OSError as exc:
            print(f"ERROR: cannot write {args.json_out}: {exc}", file=sys.stderr)
            return 1

    if args.emit_json:
        print(json.dumps(report, indent=2))
    else:
        print(_format_summary(report))

    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
