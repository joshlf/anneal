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
from collections.abc import Sequence
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

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

# Warning substrings emitted by Lean 4 when a proof uses `sorry`.
SORRY_OUTPUT_MARKERS: tuple[str, ...] = (
    "uses 'sorry'",
    "declaration uses 'sorry'",
)

# Tokens forbidden inside generated sanity and refutation Lean fixtures.
FORBIDDEN_FIXTURE_TOKEN_RE = re.compile(r"\b(?:sorry|admit|axiom)\b")

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
    # Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean (5 UB guards)
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
    # Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean (2 UB guards)
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
    # Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean (2 UB guards)
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
            "def retCleanState : MachineState :=\n"
            "  { frame :=\n"
            "      { blockIdx := 0\n"
            "        stmtIdx := 0\n"
            "        locals := .init (.scalar ⟨7, 4⟩) :: .nil }\n"
            "    memory := emptyMemory }\n"
            "\n"
            "def retTerm : Terminator :=\n"
            "  { kind := .return_, span := \"\" }\n"
            "\n"
            "theorem sanity_tb_return_frame_dealloc_protector_conflict :\n"
            "    evalTerminator retCleanState retTerm =\n"
            "      MirStepNode.retNormal (.scalar ⟨7, 4⟩) emptyMemory :=\n"
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


def find_theorem_line_span(
    fixture_text: str,
    theorem_name: str,
) -> tuple[int, int]:
    """Return the inclusive 1-based `(start, end)` line span of `theorem_name`.

    Used to confirm that a Lean proof failure on a mutated semantics actually
    originated inside the guard's dedicated refutation theorem rather than in
    an unrelated declaration, helper definition, or file header.
    """
    lines = fixture_text.splitlines()
    decl_re = re.compile(
        r"^(?:(?:private|protected)\s+)?(?:theorem|lemma|def|noncomputable\s+def|end)\b"
    )
    target_re = re.compile(
        rf"^(?:(?:private|protected)\s+)?theorem\s+{re.escape(theorem_name)}\b"
    )
    start: int | None = None
    for idx, line in enumerate(lines, start=1):
        if start is None:
            if target_re.match(line):
                start = idx
        elif decl_re.match(line):
            return (start, idx - 1)
    if start is None:
        raise ValueError(
            f"theorem {theorem_name!r} not found in fixture source"
        )
    return (start, len(lines))


def classify_refutation_failure(
    returncode: int,
    combined_output: str,
    fixture_filename: str,
    theorem_span: tuple[int, int],
) -> tuple[str, str]:
    """Classify Lean output on a mutated refutation fixture.

    Returns `(status, detail)` where `status` is:
    - `SURVIVED`: Lean accepted (`rc == 0`) the negative refutation even after
      the guard was disabled.
    - `KILLED`: Lean rejected (`rc == 1`) with a genuine proof/type failure
      localized strictly inside the target theorem's line span and with no
      crash/parse/timeout markers.
    - `ERROR`: Unexpected exit status, crash/parse/timeout marker, missing
      proof-failure marker, or any error diagnostic outside the target theorem
      span (never counted as a kill).
    """
    if returncode == 0:
        return ("SURVIVED", "refutation theorem still compiled on mutant")
    if returncode != 1:
        return (
            "ERROR",
            f"unexpected Lean exit code {returncode} (expected 1 on proof failure)",
        )
    for marker in NON_KILL_ERROR_MARKERS:
        if marker in combined_output:
            return (
                "ERROR",
                f"non-proof failure marker {marker!r} in Lean output",
            )
    if not any(m in combined_output for m in EXPECTED_PROOF_FAILURE_MARKERS):
        return (
            "ERROR",
            "Lean failed without a recognized proof/type mismatch diagnostic",
        )

    # Extract `<path>/<fixture_filename>:<line>:<col>: error:` diagnostics and
    # require at least one error inside `theorem_span` and zero outside it.
    diag_re = re.compile(
        rf"(?:^|[/\\]){re.escape(fixture_filename)}:(\d+):\d+:\s*error:",
        re.MULTILINE,
    )
    error_lines = [int(m.group(1)) for m in diag_re.finditer(combined_output)]
    start, end = theorem_span
    outside = [ln for ln in error_lines if not (start <= ln <= end)]
    if outside:
        return (
            "ERROR",
            f"error diagnostic outside target theorem lines {start}-{end} "
            f"(outside lines: {outside}, all error lines: {error_lines})",
        )
    matching = [ln for ln in error_lines if start <= ln <= end]
    if not matching:
        return (
            "ERROR",
            f"no error diagnostic in target theorem lines {start}-{end} "
            f"(saw error lines: {error_lines})",
        )
    return (
        "KILLED",
        f"proof failed inside target theorem at line(s) {matching}",
    )


def _extract_trusted_imports(lean_source: str) -> list[str]:
    """Return `Trusted/...` module paths imported by `lean_source`."""
    imports: list[str] = []
    for line in lean_source.splitlines():
        stripped = line.strip()
        if stripped.startswith("import "):
            mod = stripped[len("import ") :].strip().replace(".", "/")
            if mod.startswith("Trusted/"):
                imports.append(mod)
    return imports


def _has_sorry_warning(combined_output: str) -> bool:
    return any(marker in combined_output for marker in SORRY_OUTPUT_MARKERS)


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
    for mod in (*BASE_TRUSTED_MODULES, *SEMANTICS_MODULES):
        mod_path = trusted_lean_dir / f"{mod}.lean"
        if not mod_path.is_file():
            errors.append(f"missing trusted Lean module: {mod_path}")
            continue
        for imp in _extract_trusted_imports(mod_path.read_text(encoding="utf-8")):
            if imp not in seen_mods:
                errors.append(
                    f"topological/missing import in {mod}: {imp!r} not compiled before {mod!r}"
                )
        seen_mods.add(mod)

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
        else:
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

        for kind, src_text, thm_name in (
            ("sanity", guard.sanity_source, guard.sanity_theorem_name),
            ("refute", guard.refute_source, guard.theorem_name),
        ):
            if FORBIDDEN_FIXTURE_TOKEN_RE.search(src_text):
                errors.append(
                    f"{guard.guard_id}: forbidden sorry/admit/axiom token in {kind}_source"
                )
            try:
                find_theorem_line_span(src_text, thm_name)
            except ValueError as exc:
                errors.append(f"{guard.guard_id} ({kind}): {exc}")

            imports = _extract_trusted_imports(src_text)
            if not imports:
                errors.append(
                    f"{guard.guard_id} ({kind}): fixture imports no Trusted.* module"
                )
            for imp in imports:
                if imp not in all_known_modules:
                    errors.append(
                        f"{guard.guard_id} ({kind}): fixture imports unknown module {imp!r}"
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
        for raw_pattern in guard_filters:
            pattern = raw_pattern.strip()
            if not pattern:
                raise ValueError("--guard filter must be non-empty")
            exact = [g for g in MIR_SEMANTICS_GUARDS if g.guard_id == pattern]
            matched = (
                exact
                if exact
                else [g for g in MIR_SEMANTICS_GUARDS if pattern in g.guard_id]
            )
            if not matched:
                raise ValueError(
                    f"no cataloged guard matched --guard {raw_pattern!r}"
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
            return cand
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


def _can_reuse_lake_oleans(
    anneal_root: Path,
    modules: Sequence[str],
) -> bool:
    """Return True if `.lake/build/lib/lean` has up-to-date `.olean`s for `modules`.

    Verifies both direct freshness (`olean.mtime >= src.mtime`) and transitive
    upstream freshness (every earlier module in `BASE_TRUSTED_MODULES` and
    `SEMANTICS_UPSTREAM` has `src.mtime <= olean.mtime`).
    """
    lake_lib_dir = anneal_root / ".lake/build/lib/lean"
    trusted_lean_dir = anneal_root / "trusted/lean"
    if not lake_lib_dir.is_dir():
        return False

    src_mtimes: dict[str, float] = {}
    for mod in modules:
        src = trusted_lean_dir / f"{mod}.lean"
        if not src.is_file():
            return False
        try:
            src_mtimes[mod] = src.stat().st_mtime
        except OSError:
            return False

    base_max_mtime = max(
        (src_mtimes[m] for m in BASE_TRUSTED_MODULES if m in src_mtimes),
        default=0.0,
    )

    for idx, mod in enumerate(modules):
        olean = lake_lib_dir / f"{mod}.olean"
        if not olean.is_file():
            return False
        try:
            olean_mtime = olean.stat().st_mtime
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


def _link_or_copy(src: Path, dst: Path) -> None:
    dst.parent.mkdir(parents=True, exist_ok=True)
    try:
        os.link(src, dst)
    except OSError:
        shutil.copy2(src, dst)


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


def _run_lean(
    lean_bin: Path,
    args: Sequence[str],
    *,
    anneal_root: Path,
    lean_path: Sequence[Path],
    timeout_sec: int,
    lean_run_wrapper: Path | None,
) -> subprocess.CompletedProcess[str]:
    """Execute Lean in `cwd=anneal_root` with explicit `LEAN_PATH`."""
    cmd = _build_lean_command(lean_bin, args, lean_run_wrapper=lean_run_wrapper)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in lean_path)
    try:
        return subprocess.run(
            cmd,
            cwd=str(anneal_root),
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired as exc:
        out = exc.stdout if isinstance(exc.stdout, str) else (
            exc.stdout.decode("utf-8", errors="replace") if exc.stdout else ""
        )
        err = exc.stderr if isinstance(exc.stderr, str) else (
            exc.stderr.decode("utf-8", errors="replace") if exc.stderr else ""
        )
        return subprocess.CompletedProcess(
            args=cmd,
            returncode=124,
            stdout=out,
            stderr=f"{err}\nLean invocation timed out after {timeout_sec}s".strip(),
        )


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
    src = root_dir / f"{module}.lean"
    olean = out_dir / f"{module}.olean"
    olean.parent.mkdir(parents=True, exist_ok=True)
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
        return GuardResult(
            guard_id=guard.guard_id,
            target_file=guard.target_file,
            target_module=guard.target_module,
            quick=guard.quick,
            status="ERROR",
            duration_sec=round(time.monotonic() - t0, 3),
            detail=str(exc),
        )

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

        # Hardlink every unmodified TCB `.olean` from `base_olean_dir` into
        # `mut_olean_dir` so Lean 4 sees a complete `Trusted.*` root namespace
        # in a single `LEAN_PATH` directory.
        _seed_olean_tree(
            base_olean_dir,
            mut_olean_dir,
            baseline_modules,
            skip_modules=set(rebuild_mods),
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
            if res.returncode != 0:
                return GuardResult(
                    guard_id=guard.guard_id,
                    target_file=guard.target_file,
                    target_module=guard.target_module,
                    quick=guard.quick,
                    status="ERROR",
                    duration_sec=round(time.monotonic() - t0, 3),
                    detail=(
                        f"mutated semantics module {mod} failed to compile "
                        f"(rc={res.returncode}): "
                        f"{(res.stdout + res.stderr).strip()[:300]}"
                    ),
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
            return GuardResult(
                guard_id=guard.guard_id,
                target_file=guard.target_file,
                target_module=guard.target_module,
                quick=guard.quick,
                status="ERROR",
                duration_sec=round(time.monotonic() - t0, 3),
                detail=(
                    f"positive sanity {guard.sanity_module} broke on mutant "
                    f"(rc={sanity_res.returncode}): {sanity_combined[:300]}"
                ),
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
        combined = (refute_res.stdout + "\n" + refute_res.stderr).strip()
        status, detail = classify_refutation_failure(
            refute_res.returncode,
            combined,
            f"{guard.refute_module}.lean",
            theorem_span,
        )
        return GuardResult(
            guard_id=guard.guard_id,
            target_file=guard.target_file,
            target_module=guard.target_module,
            quick=guard.quick,
            status=status,
            duration_sec=round(time.monotonic() - t0, 3),
            detail=detail,
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
) -> dict[str, object]:
    """Run baseline verification and all selected single-guard mutations."""
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
    worker_count = max(1, min(jobs, len(selected_guards)))
    used_lake_cache = False
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
        if reuse_lake_cache and _can_reuse_lake_oleans(
            anneal_root, baseline_modules
        ):
            _seed_olean_tree(
                anneal_root / ".lake/build/lib/lean",
                base_olean_dir,
                baseline_modules,
            )
            used_lake_cache = True
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
            for fut in as_completed(base_futs):
                fut.result()

        baseline_sec = time.monotonic() - t_base

        # Run single-guard mutations in parallel inside isolated temp dirs.
        with ThreadPoolExecutor(max_workers=worker_count) as pool:
            future_map = {
                pool.submit(
                    _check_one_mir_guard,
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
            for fut in as_completed(future_map):
                res = fut.result()
                by_id[res.guard_id] = res
        results.extend(by_id[g.guard_id] for g in selected_guards)

    total = len(results)
    killed = sum(1 for r in results if r.status == "KILLED")
    survived = sum(1 for r in results if r.status == "SURVIVED")
    errors = sum(1 for r in results if r.status == "ERROR")
    return {
        "mode": mode_label,
        "used_lake_cache": used_lake_cache,
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
    if explicit is not None:
        if not explicit.is_file():
            raise SystemExit(f"Lean binary not found: {explicit}")
        return explicit
    env_lean = os.environ.get("ANNEAL_LEAN")
    if env_lean:
        cand = Path(env_lean)
        if cand.is_file():
            return cand
    found = shutil.which("lean")
    if found:
        return Path(found)
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
    lines.append(
        f"MIR guard-mutation summary ({report['mode']}, {cache_note}): "
        f"{report['killed']}/{report['total']} killed "
        f"({report['kill_rate_pct']:.1f}%), {report['survived']} survived, "
        f"{report['errors']} errors "
        f"(baseline {report['baseline_sec']:.2f}s, total {report['total_sec']:.2f}s)"
    )
    return "\n".join(lines)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Single-guard mutation testing gate for Anneal's "
            "Trusted.Rustc.V2026_06_01.MirSemantics."
        )
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
        help="Run only guard(s) matching this exact guard_id or substring (repeatable).",
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
        help="Emit the structured JSON report to stdout.",
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

    if args.list:
        errors = validate_catalog_invariants(args.anneal_root)
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

    lean_bin = _resolve_lean_binary(args.lean)

    # Wrap auto-resolved real `lean` calls through `anneal-lean-run --mode file --`
    # when available; invoke explicit custom `--lean` directly unless
    # `--use-lean-run` is explicitly requested.
    lean_run_wrapper: Path | None = None
    if args.use_lean_run is True:
        lean_run_wrapper = _resolve_lean_run_wrapper(args.anneal_root)
        if lean_run_wrapper is None:
            print(
                "ERROR: --use-lean-run specified, but anneal-lean-run was not found",
                file=sys.stderr,
            )
            return 1
    elif args.use_lean_run is None and args.lean is None:
        lean_run_wrapper = _resolve_lean_run_wrapper(args.anneal_root)

    try:
        report = run_guard_mutation_suite(
            anneal_root=args.anneal_root,
            lean_bin=lean_bin,
            quick=args.quick,
            guard_filters=args.guards,
            jobs=args.jobs,
            timeout_sec=args.timeout_sec,
            lean_run_wrapper=lean_run_wrapper,
            reuse_lake_cache=not args.no_lake_cache,
        )
    except (RuntimeError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8"
        )

    if args.emit_json:
        print(json.dumps(report, indent=2))
    else:
        print(_format_summary(report))

    if (
        report["total"] == 0
        or report["survived"] != 0
        or report["errors"] != 0
        or report["killed"] != report["total"]
    ):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
