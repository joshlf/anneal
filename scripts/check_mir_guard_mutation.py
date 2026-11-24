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

* A mutant only counts as `KILLED` when Lean exits `1`, every error diagnostic
  is located inside the guard's refutation theorem in the generated fixture,
  at least one of them is a `Type mismatch` whose mismatched term is the `rfl`
  proof itself, every other one is the `Not a definitional equality` companion
  Lean 4.34 prints for a `:= rfl` theorem, and the output has no
  crash/parse/timeout/elaboration-breakage marker. A `Type mismatch` about any
  other term (a statement that stopped elaborating on the mutant), a lone
  `Not a definitional equality` (Lean prints it even for a theorem whose `rfl`
  it accepted), errors in other files, errors without a source position,
  crash/timeout/parse or statement-elaboration markers
  (`Application type mismatch`, `Function expected`, `invalid field`,
  `failed to synthesize`), and signal exit codes are `ERROR`, never a kill.
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
  binders (its proof is the fixture's only `rfl`), helper `def`s that shadow
  no trusted declaration, an allowlist of top-level commands, and no construct
  the comment scanner cannot lex exactly (interpolated or raw strings,
  character literals, backslashes). The theorem must read
  `<MirSemantics function> <args> = <expected data>`, where the function is
  defined in a module the guard's mutant rebuilds: no other part of the
  fixture may name a MirSemantics function, a refutation must expect UB
  literally, and a positive sanity fixture must not mention `ub` at all.
* `.olean`s are shared by hardlink, so no Lean invocation may ever write
  through one: destinations are unlinked before every link and every compile,
  stale downstream modules are never seeded into a mutant overlay, and the
  reused Lake artifacts are re-checked after the run.

Catalog and command line
------------------------

`MIR_SEMANTICS_GUARDS` holds 20 guards: 9 in `Scalars.lean`, 3 in
`Places.lean`, 6 in `Statements.lean` and 2 in `Terminators.lean`. Each
fixture imports only its guard's target module, so a mutant recompiles that
one module and nothing downstream of it.

  --quick             Run the 3-guard smoke subset (one guard each in
                      `Scalars.lean`, `Statements.lean`, `Terminators.lean`).
  --all               Run the whole catalog. This is the default.
  --guard SELECTOR    Run the guards whose id equals SELECTOR or, failing
                      that, contains it. Repeatable, and each value may be a
                      comma-separated list. A selector that matches no guard
                      fails the run.
  --list              Validate every static catalog invariant against the live
                      sources, print the selected guards, and run no Lean.
  --json              Print the JSON report on stdout, and nothing else.
  --json-out PATH     Write the JSON report to PATH.
  --anneal-root PATH  Repository root (default: this script's parent).
  --lean PATH         The `lean` to run (default: `ANNEAL_LEAN`, `PATH`, or
                      `~/.elan/bin/lean`).
  --use-lean-run      Wrap every Lean call in `anneal-lean-run --mode file --`.
  --no-lean-run       Never wrap. With neither flag, only a `lean` that was
                      resolved by default (no `--lean`) is wrapped, when
                      `anneal-lean-run` is installed.
  --no-lake-cache     Compile the baseline `.olean`s from source instead of
                      reusing `.lake/build/lib/lean`.
  --trust-lake-olean-hash-files
                      Faster, weaker: do not re-hash each reused `.olean`.
  --jobs N            Worker threads (default: `min(4, CPU count)`).
  --timeout-sec SEC   Timeout of each Lean invocation (default: 120).
  --taxonomy-json     Print the canonical `PropertyTaxonomyManifest` JSON (the
                      12 property classes and 3 spec-boundary guards) after
                      checking it against `property_registry.rs` and
                      `SpecBoundaryGuards.lean`. Runs no Lean.
  --check-spec-wildcards PATH [PATH ...]
                      Scan Lean (`.lean`) or Rust (`.rs`) specification sources
                      for postcondition arms that accept every error outcome
                      (`| .ub => True`, `Err(_) => true`). Exit `0` when clean,
                      `1` on a finding or an unreadable path. Runs no Lean.

Property taxonomy and the spec-boundary wildcard probe
------------------------------------------------------

Every guard names the canonical `PropertyClass` of the UB check it mutates
(`property_class`, one of the 12 `CANONICAL_PROPERTY_CLASSES`), and
`PROPERTY_CLASS_DISPOSITIONS` accounts for all 12 classes: the ones the
catalog guards, the ones whose single-step checks have no cataloged mutant
yet, and the two that are not single-step UB at all (`loop_termination`,
`unsupported_fallback`). `--list` and every run compare these identifiers and
the 3 `CANONICAL_SPEC_BOUNDARY_GUARDS` with the live
`crates/cargo-anneal/src/property_registry.rs` and
`theory/Anneal/SpecBoundaryGuards.lean`, so the two taxonomies cannot drift
apart silently. Reports carry `property_class` per result and a
`property_class_summary` row per class.

`detect_postcondition_error_wildcards` and
`verify_postcondition_kills_error_mutants` are the `error_branch_wildcard`
(`awsm2`) probe: a postcondition whose error, `ub` or `unsupported` arm folds
to constant truth lets the error mutant survive, while a guarded arm kills
it. The probe lexes comments and literals of both languages and fails closed
on anything it cannot delimit.

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
import stat
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
# toolchain mismatch, resource exhaustion, or broken statement elaboration
# (arity/field/typeclass/argument type errors) rather than a genuine `:= rfl`
# proof refutation failure. Any refutation failure containing one of these
# markers is classified as `ERROR` rather than `KILLED`.
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
    "Function expected",
    "Application type mismatch",
    "failed to synthesize",
    "invalid field",
    "is not a valid",
)

# Headings of the only two error diagnostics Lean 4.34 prints when a
# `theorem ... := rfl` refutation no longer holds on a mutant. Every error
# inside the refutation theorem must OPEN with one of them, and must then have
# the exact shape `_rfl_failure_kind` recognizes:
#
# * `Type mismatch` whose mismatched term, printed alone on the next line, is
#   `rfl` itself (`Lean.Elab.Term.throwTypeMismatchError`). This is the
#   elaborator rejecting the proof, and the only evidence of a kill. A
#   `Type mismatch` about any other term, such as the `Bool` of
#   `theorem t : (1 : Nat) = Bool := rfl`, is a STATEMENT that no longer
#   elaborates on the mutant, not a refuted proof.
# * `Not a definitional equality: the left-hand side ... is not definitionally
#   equal to the right-hand side ...`, from the `@[defeq]` validation Lean
#   applies to every theorem whose body is syntactically `:= rfl`
#   (`Lean.validateDefEqAttr`). It inspects only the statement and is reported
#   even when the `rfl` proof itself was ACCEPTED, so it may accompany the
#   `rfl` mismatch but never replaces it.
#
# Broken statement/arity/field/typeclass diagnostics belong in
# `NON_KILL_ERROR_MARKERS`, not here.
EXPECTED_PROOF_FAILURE_MARKERS: tuple[str, ...] = (
    "Type mismatch",
    "type mismatch",
    "Not a definitional equality",
)
_RFL_TYPE_MISMATCH_RE = re.compile(r"[Tt]ype mismatch[ \t]*\n[ \t]+rfl[ \t]*(?:\n|\Z)")
_NOT_DEFEQ_RE = re.compile(
    r"Not a definitional equality: the left-hand side[ \t]*\n"
    r"(?:.*\n)*?is not definitionally equal to the right-hand side[ \t]*(?:\n|\Z)"
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
    # Canonical `PropertyClass` identifier of the UB check this guard mutates.
    # The default exists only so a synthetic guard can be built positionally;
    # `validate_catalog_invariants` requires an explicit canonical class on
    # every `MIR_SEMANTICS_GUARDS` entry.
    property_class: str = ""

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
    # Stamped from the catalog by `run_guard_mutation_suite`.
    property_class: str = ""


MIR_SEMANTICS_GUARDS: tuple[MirSemanticsGuard, ...] = (
    # ------------------------------------------------------------------
    # Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean (7 UB guards + 2 boundary mutants)
    # ------------------------------------------------------------------
    MirSemanticsGuard(
        guard_id="div_by_zero",
        property_class="div_rem_ub",
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
        property_class="div_rem_ub",
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
        property_class="div_rem_ub",
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
        property_class="div_rem_ub",
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
        property_class="shift_bounds",
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
        property_class="shift_bounds",
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
        property_class="shift_bounds",
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
        property_class="shift_bounds",
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
        property_class="discriminant_validity",
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
        property_class="uninit_read",
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
        property_class="uninit_read",
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
        property_class="pointer_deref",
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
        property_class="discriminant_validity",
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
        property_class="discriminant_validity",
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
        property_class="discriminant_validity",
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
        property_class="memory_copy_overlap",
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
        property_class="memory_copy_overlap",
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
        property_class="memory_copy_overlap",
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
            "def fieldZero : ProjectionElem :=\n"
            "  .field 0 { kind := .uint .u32, layoutIdx := 0 }\n"
            "\n"
            "def fieldOne : ProjectionElem :=\n"
            "  .field 1 { kind := .uint .u32, layoutIdx := 0 }\n"
            "\n"
            "def fieldZeroBorrow : BorrowEntry :=\n"
            "  { tag := 1, targetLocal := 0, targetProjection := fieldZero :: .nil, perm := .unique }\n"
            "\n"
            "def fieldOneBorrow : BorrowEntry :=\n"
            "  { tag := 2, targetLocal := 0, targetProjection := fieldOne :: .nil, perm := .unique }\n"
            "\n"
            "def fieldZeroDisabledBorrow : BorrowEntry :=\n"
            "  { fieldZeroBorrow with perm := .disabled }\n"
            "\n"
            "def subplaceInitMem : Memory :=\n"
            "  { emptyMemory with borrows := fieldZeroBorrow :: fieldOneBorrow :: .nil }\n"
            "\n"
            "def subplaceAfterMem : Memory :=\n"
            "  { emptyMemory with borrows := fieldZeroDisabledBorrow :: fieldOneBorrow :: .nil }\n"
            "\n"
            "def subplaceInitLocals : List LocalSlot :=\n"
            "  .init (.aggregate 0 (.scalar ⟨42, 4⟩ :: .scalar ⟨99, 4⟩ :: .nil)) ::\n"
            "  .init (.ptr ⟨1, 0⟩ 8) ::\n"
            "  .init (.ptr ⟨2, 0⟩ 8) ::\n"
            "  .init (.scalar ⟨1, 8⟩) :: .nil\n"
            "\n"
            "def subplaceAfterLocals : List LocalSlot :=\n"
            "  .init (.aggregate 0 (.scalar ⟨42, 4⟩ :: .scalar ⟨42, 4⟩ :: .nil)) ::\n"
            "  .init (.ptr ⟨1, 0⟩ 8) ::\n"
            "  .init (.ptr ⟨2, 0⟩ 8) ::\n"
            "  .init (.scalar ⟨1, 8⟩) :: .nil\n"
            "\n"
            "def subplaceDisjointCopyStmt : Statement :=\n"
            "  { kind := .intrinsic\n"
            "      (.copyNonOverlapping\n"
            "        (.copy { local_ := 1, projection := .nil })\n"
            "        (.copy { local_ := 2, projection := .nil })\n"
            "        (.copy { local_ := 3, projection := .nil }))\n"
            "    span := \"\" }\n"
            "\n"
            "theorem sanity_copy_nonoverlapping_subplace_overlap :\n"
            "    evalStmt\n"
            "      { frame := { blockIdx := 0, stmtIdx := 0, locals := subplaceInitLocals }\n"
            "        memory := subplaceInitMem }\n"
            "      subplaceDisjointCopyStmt =\n"
            "      MirStepNode.step\n"
            "        { frame := { blockIdx := 0, stmtIdx := 1, locals := subplaceAfterLocals }\n"
            "          memory := subplaceAfterMem } :=\n"
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
        property_class="pointer_deref",
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
        property_class="pointer_deref",
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


def _rfl_failure_kind(diag_text: str) -> str | None:
    """Classify the text of one error diagnostic of a `:= rfl` theorem.

    `diag_text` is everything after the `error:` header. Returns `"rfl"` for a
    `Type mismatch` on the `rfl` proof term, `"defeq"` for the
    `Not a definitional equality` companion, and `None` for anything else
    (see `EXPECTED_PROOF_FAILURE_MARKERS`).
    """
    text = diag_text.lstrip(" \t")
    if not text.startswith(EXPECTED_PROOF_FAILURE_MARKERS):
        return None
    if _RFL_TYPE_MISMATCH_RE.match(text):
        return "rfl"
    if _NOT_DEFEQ_RE.match(text):
        return "defeq"
    return None


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
      them is a `Type mismatch` on the `rfl` proof term itself, every other one
      is the `Not a definitional equality` companion Lean prints for a
      `:= rfl` theorem, and the output has no
      crash/parse/timeout/elaboration-breakage marker.
    - `ERROR`: anything else (never counted as a kill): unexpected exit status
      (signals, OOM, timeout), crash/parse/timeout/elaboration-breakage marker,
      an error diagnostic in another file or without a source position, an
      error outside the target theorem span, a `Type mismatch` about any term
      other than `rfl` (the statement stopped elaborating), any other
      diagnostic inside the target theorem, or a
      `Not a definitional equality` with no `Type mismatch` on `rfl` (Lean
      prints it for a theorem whose `rfl` proof it accepted, too).
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
    kinds = [_rfl_failure_kind(body) for _, body in error_diags]
    if None in kinds:
        return (
            "ERROR",
            "Lean failed with an unrecognized non-proof diagnostic (neither a "
            "`Type mismatch` on `rfl` nor its `Not a definitional equality` "
            f"companion) inside target theorem lines {start}-{end}",
        )
    if "rfl" not in kinds:
        return (
            "ERROR",
            "Lean reported no `Type mismatch` on the `rfl` proof inside target "
            f"theorem lines {start}-{end}; `Not a definitional equality` alone "
            "does not show that the proof was rejected",
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


# Fast O(N) comment stripper for large trusted TCB sources (such as the 848 KB
# `Places.lean`), preserving newline counts and nested `/- ... -/` block
# comments without letting stray `"` characters inside block comments hide `-/`
# closers. Used by `_trusted_function_names` so comment-only text is never
# allowlisted as a callable `MirSemantics` function.
_FAST_CODE_EDGE_RE = re.compile(r'/-|--[^\n]*|"(?:\\.|[^"\\])*"')
_FAST_BLOCK_EDGE_RE = re.compile(r"/-|-/")


def _strip_lean_comments_fast(lean_source: str) -> str:
    """Strip `--` and nested `/- ... -/` comments from `lean_source` in O(N)."""
    out: list[str] = []
    n = len(lean_source)
    pos = 0
    while pos < n:
        match = _FAST_CODE_EDGE_RE.search(lean_source, pos)
        if match is None:
            out.append(lean_source[pos:])
            break
        out.append(lean_source[pos : match.start()])
        tok = match.group(0)
        if tok == "/-":
            depth = 1
            cur = match.end()
            while cur < n and depth > 0:
                edge = _FAST_BLOCK_EDGE_RE.search(lean_source, cur)
                if edge is None:
                    nl = lean_source.count("\n", cur, n)
                    if nl:
                        out.append("\n" * nl)
                    cur = n
                    break
                nl = lean_source.count("\n", cur, edge.start())
                if nl:
                    out.append("\n" * nl)
                depth += 1 if edge.group(0) == "/-" else -1
                cur = edge.end()
            pos = cur
        elif tok.startswith("--"):
            pos = match.end()
        else:
            out.append(tok)
            pos = match.end()
    return "".join(out)


def _trusted_declaration_names(lean_source: str) -> set[str]:
    """Return the last name component of every declaration in a trusted file."""
    return {name.split(".")[-1] for _, name in _TRUSTED_DECL_RE.findall(lean_source)}


def _trusted_function_names(lean_source: str) -> set[str]:
    """Return unqualified callable function names defined in a trusted file.

    Comments are stripped first so a `def` inside doc prose is never
    allowlisted. Two kinds of definition are left out, so that fixtures can
    write them as plain data and none of them can head a theorem LHS:

    - Dotted, type-scoped definitions (`FloatPtrWidth.bits`). A LHS head is an
      unqualified name, and their last components collide with structure
      fields a fixture spells out (`{ bits := 42, sizeBytes := 4 }`). Every
      one in today's semantics modules is a small accessor on an enum or a
      byte. They stay reachable from a helper through `open` or dot notation,
      so a dotted EVALUATOR added to a semantics module must be reserved here.
    - Nullary constants and type aliases without an arrow in their signature
      (`emptyLayoutTable : LayoutTable`, `defaultCodecFuel : Nat`,
      `F32Bits : Type`).
    """
    code = _strip_lean_comments_fast(lean_source)
    names: set[str] = set()
    for match in _TRUSTED_DECL_RE.finditer(code):
        kind, name = match.group(1), match.group(2)
        if kind not in _TRUSTED_FUNCTION_KINDS or "." in name:
            continue
        tail = code[match.end() : match.end() + 400]
        stop = len(tail)
        for sep in (":=", "\n  |", "\n|", " where"):
            idx = tail.find(sep)
            if idx != -1 and idx < stop:
                stop = idx
        header_sig = tail[:stop].strip()
        if (
            header_sig.startswith(":")
            and "→" not in header_sig
            and "->" not in header_sig
            and "∀" not in header_sig
        ):
            continue
        names.add(name)
    return names


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


# Term-level binders and control/lambda syntax that could name or discard the
# semantics evaluation (`let x := evalStmt s t; x = x`, `evalStmt s t |> (·)`).
_STATEMENT_BINDER_RE = re.compile(r"(?<![\w'])(?:let|fun|λ)(?![\w'])")
_STATEMENT_CONTROL_RE = re.compile(r"(?<![\w'])(?:match|if)(?![\w'])|·")
_STATEMENT_HEAD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?=\s|$)")
_UB_IDENT_RE = re.compile(r"(?<![\w'])ub(?![\w'])")

# Top-level operators forbidden at bracket depth 0 of a theorem LHS. A valid
# LHS is a single direct application `<semantics_fn> <arg1> <arg2> ...`;
# pipelines (`|>`, `<|`, `$`), boolean/comparison operators (`==`, `!=`, `&&`,
# `||`), cons (`::`), or arithmetic at depth 0 could discard or self-compare
# the semantics result (`evalStmt s stmt |> Function.const _ 0 = 0`).
_LHS_TOP_LEVEL_OPS_2: tuple[str, ...] = (
    "|>",
    "<|",
    "==",
    "!=",
    "&&",
    "||",
    "++",
    "::",
    "<=",
    ">=",
    ":=",
    "=>",
)
_LHS_TOP_LEVEL_OPS_1: frozenset[str] = frozenset("$ ; ≠ ∧ ∨ ≤ ≥ + - * / % < > ,".split())

# The only right-hand sides a refutation theorem may assert.
REFUTE_UB_RHS: tuple[str, ...] = (".ub", "MirStepNode.fail .ub")


def _blank_lean_string_literals(text: str) -> str:
    """Replace contents of double-quoted string literals with spaces."""
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == '"':
            out.append('"')
            i += 1
            while i < n:
                c = text[i]
                if c == "\\" and i + 1 < n:
                    out.append("  ")
                    i += 2
                elif c == '"':
                    out.append('"')
                    i += 1
                    break
                else:
                    out.append("\n" if c == "\n" else " ")
                    i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def _find_top_level_lhs_operators(lhs: str) -> list[str]:
    """Return any top-level (depth-0, non-string) operators found in `lhs`."""
    found: list[str] = []
    depth = 0
    i = 0
    n = len(lhs)
    while i < n:
        ch = lhs[i]
        if ch == '"':
            i += 1
            while i < n:
                if lhs[i] == "\\" and i + 1 < n:
                    i += 2
                elif lhs[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            continue
        if ch in "([{⟨":
            depth += 1
            i += 1
            continue
        if ch in ")]}⟩" and depth > 0:
            depth -= 1
            i += 1
            continue
        if depth == 0:
            two = lhs[i : i + 2]
            if two in _LHS_TOP_LEVEL_OPS_2:
                found.append(two)
                i += 2
                continue
            if ch in _LHS_TOP_LEVEL_OPS_1:
                found.append(ch)
                i += 1
                continue
        i += 1
    return found


def _fixture_statement_errors(
    kind: str,
    src_text: str,
    theorem_name: str,
    *,
    semantics_fn_names: frozenset[str] | set[str],
    target_fn_names: frozenset[str] | set[str] | None = None,
) -> list[str]:
    """Reject a fixture theorem that does not test the trusted semantics.

    `_fixture_shape_errors` pins the proof to `rfl`; this pins the statement
    to `<target semantics function> <arg1> ... = <expected data>`:

    - exactly one top-level `=`, written without enclosing parentheses, with
      no `let`/`fun`/`λ`/`match`/`if`/`·` and with textually different sides;
    - the LHS is a direct application (at least one argument, no depth-0
      pipeline/infix/comparison/cons operators) whose head is a function
      defined in the guard's rebuilt/mutated module(s) (`target_fn_names`,
      defaulting to `semantics_fn_names`), written unqualified;
    - no `MirSemantics` function (`semantics_fn_names`) is named anywhere else
      in the fixture — neither in LHS arguments, nor in helper `def`s, nor on
      the RHS. Helper `def`s and the RHS are therefore plain data, so the RHS
      cannot alias the evaluation (`def expected := evalStmt s t`) and the LHS
      cannot self-compare or discard it (`evalStmt s t |> Function.const _ 0`);
    - a refutation's RHS is literally UB (`REFUTE_UB_RHS`), and a positive
      sanity fixture never mentions `ub`, neither inline nor through a helper.

    A vacuous REFUTATION at least fails the gate at run time, because its
    mutant survives. A vacuous SANITY theorem does not: it passes on every
    mutant and silently disables the check that a mutation left non-UB
    behavior intact. These checks are what protects that half of the gate.
    """
    effective_target_fns = (
        semantics_fn_names if target_fn_names is None else target_fn_names
    )
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
    stmt_no_strings = _blank_lean_string_literals(stmt)

    errors: list[str] = []
    if _STATEMENT_BINDER_RE.search(stmt_no_strings):
        errors.append(
            f"({kind}): theorem {theorem_name!r} statement must not contain "
            "`let`, `fun` or `λ`"
        )
    if _STATEMENT_CONTROL_RE.search(stmt_no_strings):
        errors.append(
            f"({kind}): theorem {theorem_name!r} statement must not contain "
            "`match`, `if` or `·`"
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
    if (
        head is None
        or head.group(0) not in effective_target_fns
        or not lhs[head.end() :].strip()
    ):
        errors.append(
            f"({kind}): theorem {theorem_name!r} LHS must apply a trusted "
            f"MirSemantics function from the mutated module, got {lhs.split()[0]!r}"
        )
    else:
        top_ops = _find_top_level_lhs_operators(lhs)
        if top_ops:
            errors.append(
                f"({kind}): theorem {theorem_name!r} LHS must be a direct function "
                f"application without top-level operator(s) {top_ops!r}"
            )
        lhs_args_no_strings = _blank_lean_string_literals(lhs[head.end() :])
        nested_in_lhs = sorted(
            {
                name
                for name in _LEAN_SIMPLE_IDENT_RE.findall(lhs_args_no_strings)
                if name in semantics_fn_names
            }
        )
        if nested_in_lhs:
            errors.append(
                f"({kind}): theorem {theorem_name!r} LHS arguments must not invoke "
                f"additional MirSemantics function(s) {nested_in_lhs}"
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
    # `classify_refutation_failure` tells a refuted proof from a statement that
    # stopped elaborating by the term Lean's `Type mismatch` names (`rfl`), so
    # the proof must be the fixture's ONLY `rfl`: none in the statement, none
    # in a helper `def`.
    rfl_count = len(
        re.findall(r"(?<![\w'])rfl(?![\w'])", _blank_lean_string_literals(code_only))
    )
    if rfl_count != 1:
        errors.append(
            f"{kind}_source must contain exactly one `rfl` (the theorem's proof), "
            f"found {rfl_count}"
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


# ---------------------------------------------------------------------------
# Canonical property taxonomy shared with `PropertyRegistry` (Rust) and
# `Anneal.SpecBoundaryGuards` (Lean)
# ---------------------------------------------------------------------------

# `PROPERTY_TAXONOMY_SCHEMA_VERSION` of `property_registry.rs`.
PROPERTY_TAXONOMY_SCHEMA_VERSION = 1

# The 12 `PropertyClass` wire identifiers in canonical rank order `0..11`.
CANONICAL_PROPERTY_CLASSES: tuple[str, ...] = (
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
)

# The 3 `SpecBoundaryGuardId` wire identifiers in canonical rank order `0..2`.
CANONICAL_SPEC_BOUNDARY_GUARDS: tuple[str, ...] = (
    "entry_point_requires",
    "fixed_width_ghost_length",
    "error_branch_wildcard",
)

# `(id, Rust variant, description)` of every property class, in rank order.
_PROPERTY_CLASS_ROWS: tuple[tuple[str, str, str], ...] = (
    (
        "arithmetic_overflow",
        "ArithmeticOverflow",
        "signed/unsigned arithmetic and float-to-int conversion overflow",
    ),
    ("shift_bounds", "ShiftBounds", "bit-shift distance within target integer bit width"),
    (
        "div_rem_ub",
        "DivRemUb",
        "non-zero divisor and non-overflowing signed MIN / -1 division",
    ),
    (
        "pointer_deref",
        "PointerDereference",
        "pointer alignment, provenance, Tree Borrows permissions, and live dereference",
    ),
    (
        "slice_array_bounds",
        "SliceArrayBounds",
        "array, slice, subslice, and runtime assert index bounds",
    ),
    (
        "discriminant_validity",
        "DiscriminantValidity",
        "union/enum discriminant, scalar niche validity, assume, and unreachability",
    ),
    (
        "call_contract",
        "CallContract",
        "call argument ABI compatibility, callee preconditions, and unwind contracts",
    ),
    (
        "loop_termination",
        "LoopTermination",
        "CFG cycle back-edge and recursive-call termination / decreasing variant",
    ),
    (
        "switch_exhaustiveness",
        "SwitchExhaustiveness",
        "SwitchInt branch / otherwise exhaustiveness and in-bounds CFG targets",
    ),
    (
        "memory_copy_overlap",
        "MemoryCopyOverlap",
        "copy_nonoverlapping disjointness, byte-count validity, and copy/set bounds",
    ),
    ("uninit_read", "UninitRead", "initialized local slot and memory byte reads"),
    (
        "unsupported_fallback",
        "UnsupportedFallback",
        "fail-closed fallback for unsupported or unscannable MIR constructs",
    ),
)

# `(id, canonical_name, vacuity_class, description)` of every spec-boundary
# guard, in rank order.
_SPEC_BOUNDARY_GUARD_ROWS: tuple[tuple[str, str, str, str], ...] = (
    (
        "entry_point_requires",
        "EntryPointPrecondition",
        "DeadPrecondition",
        "binary entry point (main, #![no_main] _start, #[entry]) carries a non-trivial "
        "requires that no verified caller discharges",
    ),
    (
        "fixed_width_ghost_length",
        "FixedWidthGhostLength",
        "SpecViolation",
        "ghost collection length or cardinality typed at a fixed machine width wraps at "
        "2^64 instead of using Nat or Int",
    ),
    (
        "error_branch_wildcard",
        "ErrorBranchWildcard",
        "SurvivedAllMutants",
        "postcondition arm accepts every error payload, ub, or unsupported outcome",
    ),
)

# `PropertyClass::is_waivable` is false for exactly these classes, and
# `PropertyRegistry::for_partial_correctness` waives exactly these.
_NON_WAIVABLE_PROPERTY_CLASSES: frozenset[str] = frozenset({"unsupported_fallback"})
_PARTIAL_WAIVED_PROPERTY_CLASSES: frozenset[str] = frozenset({"loop_termination"})

# `MirSemanticsGuard.property_class` of a guard that names no class. Only a
# synthetic guard built by a unit test may carry it: `validate_catalog_invariants`
# rejects it on every `MIR_SEMANTICS_GUARDS` entry.
PROPERTY_CLASS_UNSPECIFIED = ""

# How the single-guard mutation catalog relates to one property class.
PROPERTY_CLASS_COVERAGE_KINDS: tuple[str, ...] = (
    # At least one cataloged guard mutates a single-step UB check of the class.
    "single_step_ub_guarded",
    # `MirSemantics` has single-step UB checks of the class, none cataloged yet.
    "single_step_ub_uncataloged",
    # The class is a property of whole executions; no single step faults.
    "coinductive_non_ub",
    # The class is the fail-closed `.unsupported` outcome, which is not UB.
    "fail_closed_non_ub",
)


@dataclass(frozen=True)
class PropertyClassDisposition:
    """Guard-mutation coverage of one canonical property class."""

    coverage: str
    rationale: str


# One entry per canonical property class, in rank order. A class is
# `single_step_ub_guarded` exactly when `MIR_SEMANTICS_GUARDS` tags a guard with
# it, so adding the first guard of a class forces this table to be updated.
PROPERTY_CLASS_DISPOSITIONS: dict[str, PropertyClassDisposition] = {
    "arithmetic_overflow": PropertyClassDisposition(
        "single_step_ub_uncataloged",
        "the `addUnchecked` / `subUnchecked` / `mulUnchecked` overflow checks of "
        "`Scalars.lean` have no cataloged mutant",
    ),
    "shift_bounds": PropertyClassDisposition(
        "single_step_ub_guarded",
        "`shlUnchecked` / `shrUnchecked` distance checks of `evalScalarBinOp`",
    ),
    "div_rem_ub": PropertyClassDisposition(
        "single_step_ub_guarded",
        "zero-divisor and signed `MIN / -1`, `MIN % -1` checks of `Scalars.lean`",
    ),
    "pointer_deref": PropertyClassDisposition(
        "single_step_ub_guarded",
        "`checkDerefAlign` and the Tree Borrows active-protector conflict checks",
    ),
    "slice_array_bounds": PropertyClassDisposition(
        "single_step_ub_uncataloged",
        "the `.index` / `.constantIndex` / `.subslice` bounds checks of `Places.lean` "
        "have no cataloged mutant",
    ),
    "discriminant_validity": PropertyClassDisposition(
        "single_step_ub_guarded",
        "`bool` bit-pattern validity and the `assume` intrinsic operand checks",
    ),
    "call_contract": PropertyClassDisposition(
        "single_step_ub_uncataloged",
        "the call ABI and callee-contract checks of `Terminators.lean` have no "
        "cataloged mutant",
    ),
    "loop_termination": PropertyClassDisposition(
        "coinductive_non_ub",
        "divergence is a property of an infinite execution, not a single-step `.ub` "
        "result, so no `rfl` refutation theorem can state it",
    ),
    "switch_exhaustiveness": PropertyClassDisposition(
        "single_step_ub_uncataloged",
        "the `SwitchInt` target and basic-block index checks of `Terminators.lean` "
        "have no cataloged mutant",
    ),
    "memory_copy_overlap": PropertyClassDisposition(
        "single_step_ub_guarded",
        "`copy_nonoverlapping` range, place and sub-place overlap checks",
    ),
    "uninit_read": PropertyClassDisposition(
        "single_step_ub_guarded",
        "reads of `LocalSlot.dead` and `LocalSlot.uninit` locals",
    ),
    "unsupported_fallback": PropertyClassDisposition(
        "fail_closed_non_ub",
        "an unsupported construct evaluates to `.unsupported`, not `.ub`, and a "
        "refutation fixture must expect UB literally",
    ),
}

_RUST_TAXONOMY_REL = "crates/cargo-anneal/src/property_registry.rs"
_LEAN_TAXONOMY_REL = "theory/Anneal/SpecBoundaryGuards.lean"


def canonical_property_taxonomy() -> dict[str, object]:
    """The `PropertyTaxonomyManifest` this script is written against."""
    classes: list[dict[str, object]] = []
    for rank, (class_id, variant, description) in enumerate(_PROPERTY_CLASS_ROWS):
        waivable = class_id not in _NON_WAIVABLE_PROPERTY_CLASSES
        strict = "discharged" if waivable else "unsupported_fail_closed"
        classes.append(
            {
                "rank": rank,
                "id": class_id,
                "variant": variant,
                "is_waivable": waivable,
                "strict_disposition": strict,
                "partial_disposition": (
                    "explicitly_waived"
                    if class_id in _PARTIAL_WAIVED_PROPERTY_CLASSES
                    else strict
                ),
                "description": description,
            }
        )
    guards: list[dict[str, object]] = [
        {
            "rank": rank,
            "id": guard_id,
            "canonical_name": canonical_name,
            "vacuity_class": vacuity_class,
            "description": description,
        }
        for rank, (guard_id, canonical_name, vacuity_class, description) in enumerate(
            _SPEC_BOUNDARY_GUARD_ROWS
        )
    ]
    return {
        "schema_version": PROPERTY_TAXONOMY_SCHEMA_VERSION,
        "property_classes": classes,
        "spec_boundary_guards": guards,
    }


def _taxonomy_json_string(value: str) -> str:
    """JSON string literal, escaped exactly like `push_json_string` in Rust."""
    out = ['"']
    for ch in value:
        if ch == '"':
            out.append('\\"')
        elif ch == "\\":
            out.append("\\\\")
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\r":
            out.append("\\r")
        elif ch == "\t":
            out.append("\\t")
        elif ord(ch) < 0x20:
            out.append(f"\\u{ord(ch):04x}")
        else:
            out.append(ch)
    out.append('"')
    return "".join(out)


def render_property_taxonomy_manifest(taxonomy: dict[str, object] | None = None) -> str:
    """Render the manifest byte for byte like `PropertyTaxonomyManifest::to_json`.

    Fixed key order, two-space indentation, one entry per line, and a trailing
    newline. A per-class `disposition` is emitted only when the entry has one.
    """
    tax = canonical_property_taxonomy() if taxonomy is None else taxonomy
    quote = _taxonomy_json_string

    def rows(entries: Sequence[dict[str, object]], keys: Sequence[str]) -> list[str]:
        rendered: list[str] = []
        for entry in entries:
            fields: list[str] = []
            for key in keys:
                value = entry.get(key)
                if key == "disposition" and value is None:
                    continue
                if isinstance(value, bool):
                    text = "true" if value else "false"
                elif isinstance(value, int):
                    text = str(value)
                else:
                    text = quote(str(value))
                fields.append(f'"{key}": {text}')
            rendered.append("    {" + ", ".join(fields) + "}")
        return [row + "," for row in rendered[:-1]] + rendered[-1:]

    lines = ["{", f'  "schema_version": {tax["schema_version"]},', '  "property_classes": [']
    lines += rows(
        tax["property_classes"],  # type: ignore[arg-type]
        (
            "rank",
            "id",
            "variant",
            "is_waivable",
            "strict_disposition",
            "partial_disposition",
            "disposition",
            "description",
        ),
    )
    lines += ["  ],", '  "spec_boundary_guards": [']
    lines += rows(
        tax["spec_boundary_guards"],  # type: ignore[arg-type]
        ("rank", "id", "canonical_name", "vacuity_class", "description"),
    )
    lines += ["  ]", "}"]
    return "\n".join(lines) + "\n"


class SourceLexError(ValueError):
    """Source text whose comments or literals cannot be delimited exactly."""


# Everything that can hide code from a scanner, per language: comments, string
# literals (plain and raw) and character literals. A lifetime (`'a`) or an
# identifier prime (`x'`) is not a character literal and never matches.
_RUST_LEX_RE = re.compile(
    r"//[^\n]*|/\*"
    r"|(?<![A-Za-z0-9_])(?:b|c)?r#*\"|(?<![A-Za-z0-9_])(?:b|c)?\""
    r"|(?<![A-Za-z0-9_'])b?'(?:\\(?:x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f_]{1,8}\}|[^\nxu])|[^\\'\n])'"
)
_LEAN_LEX_RE = re.compile(
    r"--[^\n]*|/-|«[^»\n]*»|«"
    r"|#+\"|(?<![\w'!?.])r#*\"|\""
    r"|(?<![\w'])'(?:\\(?:x[0-9A-Fa-f]{2}|u[0-9A-Fa-f]{4}|[^\nxu])|[^\\'\n])'"
)
_DQ_STRING_TAIL_RE = re.compile(r'(?:[^"\\]|\\.)*"', re.S)
_BLOCK_COMMENT_EDGE_RE: dict[str, re.Pattern[str]] = {
    "rust": re.compile(r"/\*|\*/"),
    "lean": re.compile(r"/-|-/"),
}
_NOT_NEWLINE_RE = re.compile(r"[^\n]")


def _line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _strip_source_comments(text: str, language: str, *, blank_literals: bool = False) -> str:
    """Blank the comments of Lean or Rust `text`, keeping every offset.

    Line comments and nested block comments become spaces (newlines survive,
    so offsets and line numbers still match `text`). With `blank_literals`, a
    string literal keeps only its outer quotes and a character literal becomes
    `0`, so no literal content can be mistaken for code.

    Raises `SourceLexError` for an unterminated comment or string, and for a
    Lean interpolated string with a `{` hole, whose end only Lean's parser can
    find.
    """
    lex_re = _RUST_LEX_RE if language == "rust" else _LEAN_LEX_RE
    edge_re = _BLOCK_COMMENT_EDGE_RE["rust" if language == "rust" else "lean"]
    out: list[str] = []
    pos = 0
    while True:
        m = lex_re.search(text, pos)
        if m is None:
            out.append(text[pos:])
            break
        start = m.start()
        out.append(text[pos:start])
        tok = m.group(0)
        if tok in ("/*", "/-"):
            depth, end = 1, m.end()
            while depth:
                edge = edge_re.search(text, end)
                if edge is None:
                    raise SourceLexError(
                        f"unterminated block comment opened at line {_line_of(text, start)}"
                    )
                depth += 1 if edge.group(0) == tok else -1
                end = edge.end()
            out.append(_NOT_NEWLINE_RE.sub(" ", text[start:end]))
        elif tok.startswith(("//", "--")):
            end = m.end()
            out.append(" " * (end - start))
        elif tok[0] == "«":
            if len(tok) == 1 or tok[-1] != "»":
                raise SourceLexError(
                    f"unterminated guillemet identifier opened at line {_line_of(text, start)}"
                )
            if not tok[1:-1].strip():
                raise SourceLexError(
                    f"empty guillemet identifier at line {_line_of(text, start)}"
                )
            end = m.end()
            out.append(tok)
        elif tok[-1] == '"':
            if "r" in tok or tok[0] == "#":
                closer = '"' + "#" * tok.count("#")
                close_at = text.find(closer, m.end())
                if close_at < 0:
                    raise SourceLexError(
                        f"unterminated raw string opened at line {_line_of(text, start)}"
                    )
                end = close_at + len(closer)
            else:
                tail = _DQ_STRING_TAIL_RE.match(text, m.end())
                if tail is None:
                    raise SourceLexError(
                        f"unterminated string literal opened at line {_line_of(text, start)}"
                    )
                end = tail.end()
            literal = text[start:end]
            if language != "rust" and start > 0 and text[start - 1] == "!" and "{" in literal:
                raise SourceLexError(
                        f"interpolated string with a hole at line {_line_of(text, start)}"
                    )
            if blank_literals:
                out.append('"' + _NOT_NEWLINE_RE.sub(" ", literal[1:-1]) + '"')
            else:
                out.append(literal)
        else:
            end = m.end()
            out.append("0" + " " * (end - start - 1) if blank_literals else tok)
        pos = end
    return "".join(out)


_BRACE_RE = re.compile(r"[{}]")
_RUST_VARIANT_RE = re.compile(r"[A-Z][A-Za-z0-9]*")
_RUST_SIMPLE_ESCAPES: dict[str, str] = {
    "n": "\n",
    "r": "\r",
    "t": "\t",
    "0": "\0",
    "\\": "\\",
    '"': '"',
    "'": "'",
}


def _keyword_matches(pattern: str, text: str) -> list[re.Match[str]]:
    """Matches of `pattern` (which starts with a keyword) at a word start.

    The pattern carries no leading `\\b`, so the regex engine can search for
    its literal prefix; the word boundary is checked here instead.
    """
    return [
        m
        for m in re.compile(pattern).finditer(text)
        if m.start() == 0 or not (text[m.start() - 1].isalnum() or text[m.start() - 1] == "_")
    ]


def _one_match(pattern: str, text: str, what: str) -> re.Match[str]:
    found = _keyword_matches(pattern, text)
    if len(found) != 1:
        raise ValueError(f"expected exactly one {what}, found {len(found)}")
    return found[0]


def _brace_block(code: str, open_idx: int, what: str) -> tuple[int, int]:
    """`(start, end)` of the body of the `{ ... }` block opening at `open_idx`."""
    depth = 0
    for edge in _BRACE_RE.finditer(code, open_idx):
        depth += 1 if edge.group(0) == "{" else -1
        if depth == 0:
            return (open_idx + 1, edge.start())
    raise ValueError(f"unbalanced braces in {what}")


def _decode_rust_string_literal(literal: str) -> str:
    """Value of a plain Rust `"..."` literal (escapes and `\\`-newline joins)."""
    if len(literal) < 2 or literal[0] != '"' or literal[-1] != '"':
        raise ValueError(f"not a plain string literal: {literal[:40]!r}")
    body = literal[1:-1]
    out: list[str] = []
    i = 0
    while i < len(body):
        ch = body[i]
        if ch != "\\":
            out.append(ch)
            i += 1
            continue
        nxt = body[i + 1 : i + 2]
        if nxt == "\n":
            i += 2
            while i < len(body) and body[i] in " \t\r\n":
                i += 1
        elif nxt in _RUST_SIMPLE_ESCAPES:
            out.append(_RUST_SIMPLE_ESCAPES[nxt])
            i += 2
        elif nxt == "x":
            out.append(chr(int(body[i + 2 : i + 4], 16)))
            i += 4
        elif nxt == "u" and body[i + 2 : i + 3] == "{":
            close_at = body.index("}", i)
            out.append(chr(int(body[i + 3 : close_at].replace("_", ""), 16)))
            i = close_at + 1
        else:
            raise ValueError(f"unsupported escape in string literal {literal[:40]!r}")
    return "".join(out)


class _RustTaxonomySource:
    """Comment-stripped view of `property_registry.rs` for taxonomy extraction.

    `code` has comments and literal contents blanked and is offset-aligned
    with `text`, so structure is found in `code` and literal values are read
    from `text`: a slug inside a comment or a string is never taken for code.
    """

    _ARM_RE = re.compile(
        r"\s*Self::([A-Za-z0-9_]+)\s*(?:\{\s*\.\.\s*\})?\s*=>\s*"
        r"(\{\s*)?(\"[^\"]*\"|[0-9]+)\s*(\}\s*)?,?\s*"
    )

    def __init__(self, text: str) -> None:
        self.text = text
        self.code = _strip_source_comments(text, "rust", blank_literals=True)
        if len(self.code) != len(text):  # pragma: no cover - lexer invariant
            raise ValueError("comment stripping changed the source length")
        self._impl_spans: dict[str, list[tuple[int, int]]] = {}

    def impl_spans(self, type_name: str) -> list[tuple[int, int]]:
        spans = self._impl_spans.get(type_name)
        if spans is None:
            spans = [
                _brace_block(self.code, m.end() - 1, f"`impl {type_name}`")
                for m in _keyword_matches(rf"impl\s+{type_name}\s*\{{", self.code)
            ]
            self._impl_spans[type_name] = spans
        if not spans:
            raise ValueError(f"no `impl {type_name}` block")
        return spans

    def _one_in_impl_with_span(self, type_name: str, pattern: str, what: str) -> tuple[re.Match[str], int]:
        compiled = re.compile(pattern)
        hits = [
            (m, hi)
            for lo, hi in self.impl_spans(type_name)
            for m in compiled.finditer(self.code, lo, hi)
        ]
        if len(hits) != 1:
            raise ValueError(f"expected exactly one `{type_name}::{what}`, found {len(hits)}")
        return hits[0]

    def _one_in_impl(self, type_name: str, pattern: str, what: str) -> re.Match[str]:
        return self._one_in_impl_with_span(type_name, pattern, what)[0]

    def enum_variants(self, name: str) -> list[str]:
        head = _one_match(rf"enum\s+{name}\s*\{{", self.code, f"`enum {name}`")
        lo, hi = _brace_block(self.code, head.end() - 1, f"`enum {name}`")
        variants = [part.strip() for part in self.code[lo:hi].split(",")]
        if variants and not variants[-1]:
            variants.pop()
        for variant in variants:
            if not _RUST_VARIANT_RE.fullmatch(variant):
                raise ValueError(f"`enum {name}` has an unsupported variant {variant!r}")
        if len(set(variants)) != len(variants):
            raise ValueError(f"`enum {name}` repeats a variant")
        return variants

    def const_all(self, type_name: str) -> list[str]:
        m = self._one_in_impl(
            type_name, r"\bconst\s+ALL\s*:\s*\[[^\]]*\]\s*=\s*\[([^\]]*)\]\s*;", "ALL"
        )
        items = [part.strip() for part in m.group(1).split(",")]
        if items and not items[-1]:
            items.pop()
        out: list[str] = []
        for item in items:
            for prefix in (f"{type_name}::", "Self::"):
                if item.startswith(prefix):
                    out.append(item[len(prefix) :])
                    break
            else:
                raise ValueError(f"`{type_name}::ALL` has an unsupported entry {item!r}")
        return out

    def const_count(self, type_name: str) -> int:
        m = self._one_in_impl(
            type_name, r"\bconst\s+COUNT\s*:\s*usize\s*=\s*([0-9]+)\s*;", "COUNT"
        )
        return int(m.group(1))

    def fn_body(self, type_name: str, fn_name: str) -> tuple[int, int]:
        m, impl_hi = self._one_in_impl_with_span(type_name, rf"\bfn\s+{fn_name}\s*\(", fn_name)
        open_idx = self.code.find("{", m.end(), impl_hi)
        if open_idx < 0 or ";" in self.code[m.end() : open_idx]:
            raise ValueError(f"`{type_name}::{fn_name}` has no body")
        return _brace_block(self.code, open_idx, f"`{type_name}::{fn_name}`")

    def match_arms(self, type_name: str, fn_name: str) -> dict[str, object]:
        """`{variant: value}` of a body that is one `match self { ... }`."""
        what = f"`{type_name}::{fn_name}`"
        lo, hi = self.fn_body(type_name, fn_name)
        head = re.compile(r"\s*match\s+\*?self\s*\{").match(self.code, lo, hi)
        if head is None:
            raise ValueError(f"{what} is not a single `match self`")
        arm_lo, arm_hi = _brace_block(self.code, head.end() - 1, what)
        if self.code[arm_hi + 1 : hi].strip():
            raise ValueError(f"{what} has code after its `match self`")
        arms: dict[str, object] = {}
        pos = arm_lo
        while self.code[pos:arm_hi].strip():
            m = self._ARM_RE.match(self.code, pos, arm_hi)
            if m is None or bool(m.group(2)) != bool(m.group(4)):
                raise ValueError(f"{what} has an arm this parser cannot read")
            variant = m.group(1)
            if variant in arms:
                raise ValueError(f"{what} repeats the arm `Self::{variant}`")
            raw = self.text[m.start(3) : m.end(3)]
            arms[variant] = int(raw) if raw.isdigit() else _decode_rust_string_literal(raw)
            pos = m.end()
        return arms

    def non_matching_variants(self, type_name: str, fn_name: str) -> list[str]:
        """Variants `V` of a body that is exactly `!matches!(self, Self::V | ...)`."""
        lo, hi = self.fn_body(type_name, fn_name)
        m = re.fullmatch(
            r"\s*!\s*matches!\s*\(\s*self\s*,\s*(Self::\w+(?:\s*\|\s*Self::\w+)*)\s*\)\s*",
            self.code[lo:hi],
        )
        if m is None:
            raise ValueError(f"`{type_name}::{fn_name}` is not `!matches!(self, ...)`")
        return [part.strip()[len("Self::") :] for part in m.group(1).split("|")]

    def body_text(self, type_name: str, fn_name: str) -> str:
        lo, hi = self.fn_body(type_name, fn_name)
        return self.code[lo:hi]


def _parse_rust_property_taxonomy(text: str) -> dict[str, object]:
    src = _RustTaxonomySource(text)
    schema_version = int(
        _one_match(
            r"const\s+PROPERTY_TAXONOMY_SCHEMA_VERSION\s*:\s*u32\s*=\s*([0-9]+)\s*;",
            src.code,
            "`PROPERTY_TAXONOMY_SCHEMA_VERSION`",
        ).group(1)
    )

    def table(type_name: str, fns: Sequence[str]) -> tuple[list[str], dict[str, dict[str, object]]]:
        variants = src.enum_variants(type_name)
        if src.const_all(type_name) != variants:
            raise ValueError(f"`{type_name}::ALL` is not the enum declaration order")
        if src.const_count(type_name) != len(variants):
            raise ValueError(f"`{type_name}::COUNT` is not the number of variants")
        columns: dict[str, dict[str, object]] = {}
        for fn_name in fns:
            arms = src.match_arms(type_name, fn_name)
            if list(arms) != variants:
                raise ValueError(
                    f"`{type_name}::{fn_name}` arms are not the variants in declaration order"
                )
            columns[fn_name] = arms
        if [columns["rank"][v] for v in variants] != list(range(len(variants))):
            raise ValueError(f"`{type_name}::rank` is not the declaration order `0..`")
        return variants, columns

    variants, cols = table("PropertyClass", ("rank", "as_str", "description", "variant_name"))
    for variant in variants:
        if cols["variant_name"][variant] != variant:
            raise ValueError(f"`PropertyClass::variant_name` of `{variant}` is not its name")
    non_waivable = src.non_matching_variants("PropertyClass", "is_waivable")
    if any(variant not in variants for variant in non_waivable):
        raise ValueError("`PropertyClass::is_waivable` names an unknown variant")
    tags = src.match_arms("PropertyDisposition", "tag")

    strict_body = src.body_text("PropertyRegistry", "strict")
    strict_match = re.fullmatch(
        r"\s*Self\s*\{\s*entries\s*:\s*PropertyClass::ALL\s*\.\s*map\s*\(\s*\|\s*class\s*\|\s*"
        r"PropertyEntry\s*\{\s*class\s*,\s*disposition\s*:\s*"
        r"if\s+class\s*==\s*PropertyClass::(\w+)\s*\{\s*PropertyDisposition::(\w+)\s*\}"
        r"\s*else\s*\{\s*PropertyDisposition::(\w+)\s*\}\s*,\s*"
        r"description\s*:\s*class\s*\.\s*description\s*\(\s*\)\s*,?\s*\}\s*\)\s*,?\s*\}\s*",
        strict_body,
    )
    if strict_match is None or strict_match.group(1) not in variants:
        raise ValueError("`PropertyRegistry::strict` has dispositions this parser cannot read")
    strict = {
        v: tags[strict_match.group(2) if v == strict_match.group(1) else strict_match.group(3)]
        for v in variants
    }
    partial_body = src.body_text("PropertyRegistry", "for_partial_correctness")
    init = re.match(r"\s*let\s+mut\s+reg\s*=\s*Self::strict\s*\(\s*\)\s*;", partial_body)
    if init is None:
        raise ValueError(
            "`PropertyRegistry::for_partial_correctness` does not start with `let mut reg = Self::strict();`"
        )
    overrides: list[tuple[str, str]] = []
    pos = init.end()
    override_re = re.compile(
        r"\s*reg\s*\.\s*entries\s*\[\s*PropertyClass::(\w+)\s*\.\s*rank\s*\(\s*\)\s*\]\s*\.\s*"
        r"disposition\s*=\s*PropertyDisposition::(\w+)\s*"
    )
    while True:
        om = override_re.match(partial_body, pos)
        if om is None:
            break
        pos = om.end()
        if pos < len(partial_body) and partial_body[pos] == "{":
            _, close_idx = _brace_block(partial_body, pos, "`for_partial_correctness`")
            pos = close_idx + 1
        semi = re.match(r"\s*;", partial_body[pos:])
        if semi is None:
            raise ValueError(
                "`PropertyRegistry::for_partial_correctness` has a disposition statement this "
                "parser cannot read"
            )
        pos += semi.end()
        overrides.append((om.group(1), om.group(2)))
    if re.fullmatch(r"\s*reg\s*", partial_body[pos:]) is None:
        raise ValueError(
            "`PropertyRegistry::for_partial_correctness` has statements this parser cannot read"
        )
    partial = dict(strict)
    for variant, disposition in overrides:
        if variant not in partial:
            raise ValueError("`for_partial_correctness` overrides an unknown variant")
        partial[variant] = tags[disposition]

    classes = [
        {
            "rank": rank,
            "id": cols["as_str"][variant],
            "variant": variant,
            "is_waivable": variant not in non_waivable,
            "strict_disposition": strict[variant],
            "partial_disposition": partial[variant],
            "description": cols["description"][variant],
        }
        for rank, variant in enumerate(variants)
    ]
    guard_variants, guard_cols = table(
        "SpecBoundaryGuardId",
        ("rank", "as_str", "canonical_name", "vacuity_class", "description"),
    )
    guards = [
        {
            "rank": rank,
            "id": guard_cols["as_str"][variant],
            "canonical_name": guard_cols["canonical_name"][variant],
            "vacuity_class": guard_cols["vacuity_class"][variant],
            "description": guard_cols["description"][variant],
        }
        for rank, variant in enumerate(guard_variants)
    ]
    return {
        "schema_version": schema_version,
        "property_classes": classes,
        "spec_boundary_guards": guards,
    }


def _parse_lean_property_taxonomy(text: str) -> dict[str, object]:
    code = _strip_source_comments(text, "lean", blank_literals=True)
    if len(code) != len(text):  # pragma: no cover - lexer invariant
        raise ValueError("comment stripping changed the source length")
    ident = r"[A-Za-z_][A-Za-z0-9_']*"

    def _next_nonblank_starts_bar(buf: str, pos: int) -> bool:
        m_next = re.search(r"(?m)^[ \t]*(\S)", buf[pos:])
        return m_next is not None and m_next.group(1) == "|"

    def ctors(name: str) -> list[str]:
        m = _one_match(
            rf"(?m)^inductive[ \t]+{name}\b[^\n]*\bwhere[ \t]*\n"
            rf"((?:[ \t]*(?:\|[ \t]*{ident})?[ \t]*\n)+)",
            code,
            f"`inductive {name}`",
        )
        if _next_nonblank_starts_bar(code, m.end()):
            raise ValueError(f"`inductive {name}` has a constructor this parser cannot read")
        found = re.findall(rf"\|[ \t]*({ident})", m.group(1))
        if not found or len(set(found)) != len(found):
            raise ValueError(f"`inductive {name}` has no or repeated constructors")
        return found

    def namespace_span(name: str) -> tuple[int, int]:
        start = _one_match(rf"(?m)^namespace[ \t]+{name}[ \t]*$", code, f"`namespace {name}`")
        stop = re.compile(rf"(?m)^end[ \t]+{name}[ \t]*$").search(code, start.end())
        if stop is None:
            raise ValueError(f"`namespace {name}` is never closed")
        return start.end(), stop.start()

    def arms(ns_span: tuple[int, int], def_name: str, where: str) -> list[tuple[str, str]]:
        ns_lo, ns_hi = ns_span
        body = code[ns_lo:ns_hi]
        m = _one_match(
            rf"(?m)^def[ \t]+{def_name}[ \t]*:[^\n]*\n((?:[ \t]*(?:\|[^\n]*)?\n)+)",
            body,
            f"`{where}.{def_name}`",
        )
        if _next_nonblank_starts_bar(body, m.end()):
            raise ValueError(f"`{where}.{def_name}` has an arm this parser cannot read")
        out: list[tuple[str, str]] = []
        offset = ns_lo + m.start(1)
        for raw_line in m.group(1).splitlines(keepends=True):
            line = raw_line.rstrip("\n")
            if line.strip():
                arm = re.fullmatch(rf"[ \t]*\|[ \t]*(\.{ident}|_)[ \t]*=>[ \t]*(\S.*?)[ \t]*", line)
                if arm is None:
                    raise ValueError(f"`{where}.{def_name}` has an arm this parser cannot read")
                val_raw = text[offset + arm.start(2) : offset + arm.end(2)]
                out.append((arm.group(1).lstrip("."), val_raw))
            offset += len(raw_line)
        if not out or len({pattern for pattern, _ in out}) != len(out):
            raise ValueError(f"`{where}.{def_name}` has no or repeated arms")
        return out

    def column(ns_span: tuple[int, int], def_name: str, where: str, names: list[str]) -> dict[str, str]:
        found = arms(ns_span, def_name, where)
        if [pattern for pattern, _ in found] != names:
            raise ValueError(
                f"`{where}.{def_name}` arms are not the constructors in declaration order"
            )
        return dict(found)

    def all_list(ns_span: tuple[int, int], where: str) -> list[str]:
        body = code[ns_span[0] : ns_span[1]]
        m = _one_match(
            r"(?m)^def[ \t]+all[ \t]*:[^\n]*:=\s*\[([^\]]*)\][ \t]*$", body, f"`{where}.all`"
        )
        m_cont = re.search(r"(?m)^([ \t]*)\S", body[m.end() :])
        if m_cont is not None and m_cont.group(1):
            raise ValueError(f"`{where}.all` has a trailing continuation")
        out: list[str] = []
        for raw_item in m.group(1).split(","):
            item = raw_item.strip()
            if not re.fullmatch(rf"\.{ident}", item):
                raise ValueError(f"`{where}.all` has an unsupported entry {item!r}")
            out.append(item[1:])
        return out

    def string(value: str, where: str) -> str:
        if not re.fullmatch(r'"[^"\\]*"', value):
            raise ValueError(f"{where} is not a plain string literal: {value!r}")
        return value[1:-1]

    def ranks(ns_span: tuple[int, int], where: str, names: list[str]) -> None:
        col = column(ns_span, "rank", where, names)
        if [col[name] for name in names] != [str(i) for i in range(len(names))]:
            raise ValueError(f"`{where}.rank` is not the declaration order `0..`")

    cls = "PropertyClassTag"
    cls_ctors = ctors(cls)
    cls_ns = namespace_span(cls)
    if all_list(cls_ns, cls) != cls_ctors:
        raise ValueError(f"`{cls}.all` is not the constructor declaration order")
    ranks(cls_ns, cls, cls_ctors)
    as_str = column(cls_ns, "asStr", cls, cls_ctors)
    variant = column(cls_ns, "variantName", cls, cls_ctors)
    waivable = arms(cls_ns, "isWaivable", cls)
    if (
        not waivable
        or waivable[-1] != ("_", "true")
        or any(value != "false" or name not in cls_ctors for name, value in waivable[:-1])
    ):
        raise ValueError(f"`{cls}.isWaivable` is not `false` arms followed by `| _ => true`")
    non_waivable = {name for name, _ in waivable[:-1]}
    classes = [
        {
            "rank": rank,
            "id": string(as_str[name], f"`{cls}.asStr`"),
            "variant": string(variant[name], f"`{cls}.variantName`"),
            "is_waivable": name not in non_waivable,
        }
        for rank, name in enumerate(cls_ctors)
    ]
    for entry, name in zip(classes, cls_ctors):
        if entry["variant"] != name[:1].upper() + name[1:]:
            raise ValueError(f"`{cls}.variantName` of `{name}` is not its Rust variant name")

    guard = "SpecBoundaryGuardClass"
    guard_ctors = ctors(guard)
    guard_ns = namespace_span(guard)
    if all_list(guard_ns, guard) != guard_ctors:
        raise ValueError(f"`{guard}.all` is not the constructor declaration order")
    ranks(guard_ns, guard, guard_ctors)
    guard_id = column(guard_ns, "guardId", guard, guard_ctors)
    canonical_name = column(guard_ns, "canonicalName", guard, guard_ctors)
    vacuity = column(guard_ns, "toVacuityClass", guard, guard_ctors)
    guards: list[dict[str, object]] = []
    for rank, name in enumerate(guard_ctors):
        vac = vacuity[name]
        if not re.fullmatch(rf"\.{ident}", vac):
            raise ValueError(f"`{guard}.toVacuityClass` of `{name}` is not a constructor")
        guards.append(
            {
                "rank": rank,
                "id": string(guard_id[name], f"`{guard}.guardId`"),
                "canonical_name": string(canonical_name[name], f"`{guard}.canonicalName`"),
                "vacuity_class": vac[1:2].upper() + vac[2:],
            }
        )
    return {"property_classes": classes, "spec_boundary_guards": guards}


# Parsed taxonomies by source text: the catalog is validated many times per
# process against the same two files.
_TAXONOMY_PARSE_CACHE: dict[tuple[str, str], dict[str, object] | str] = {}


def _extract_taxonomy(anneal_root: Path, rel: str, kind: str) -> dict[str, object]:
    path = Path(anneal_root) / rel
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise ValueError(f"cannot read {rel}: {exc}") from exc
    key = (kind, text)
    cached = _TAXONOMY_PARSE_CACHE.get(key)
    if cached is None:
        parser = _parse_rust_property_taxonomy if kind == "rust" else _parse_lean_property_taxonomy
        try:
            cached = parser(text)
        except (ValueError, KeyError, IndexError) as exc:
            cached = f"{rel}: malformed taxonomy source: {exc}"
        if len(_TAXONOMY_PARSE_CACHE) >= 8:
            _TAXONOMY_PARSE_CACHE.clear()
        _TAXONOMY_PARSE_CACHE[key] = cached
    if isinstance(cached, str):
        raise ValueError(cached)
    return {
        key_: [dict(entry) for entry in value] if isinstance(value, list) else value
        for key_, value in cached.items()
    }


def extract_rust_property_taxonomy(anneal_root: Path) -> dict[str, object]:
    """Read the taxonomy manifest out of the live `property_registry.rs`.

    Parses the comment-stripped source directly: `PropertyClass` and
    `SpecBoundaryGuardId` declaration order, `ALL`, `COUNT`, `rank`, `as_str`,
    `variant_name`, `description`, `is_waivable`, the strict and
    partial-correctness dispositions, and the manifest schema version. The
    result has the shape of `canonical_property_taxonomy()`.

    Raises `ValueError` when the file is missing, unreadable, or not shaped
    the way this parser can prove it reads completely.
    """
    return _extract_taxonomy(anneal_root, _RUST_TAXONOMY_REL, "rust")


def extract_lean_property_taxonomy(anneal_root: Path) -> dict[str, object]:
    """Read `PropertyClassTag` and `SpecBoundaryGuardClass` out of the Lean theory.

    The result has the rank, identifier, variant / canonical name, waivability
    and vacuity-class fields of `canonical_property_taxonomy()`; Lean carries
    no descriptions or dispositions.
    """
    return _extract_taxonomy(anneal_root, _LEAN_TAXONOMY_REL, "lean")


_TAXONOMY_REQUIRED_KEYS: dict[str, dict[str, tuple[str, ...]]] = {
    "property_registry.rs": {
        "property_classes": (
            "rank", "id", "variant", "is_waivable",
            "strict_disposition", "partial_disposition", "description",
        ),
        "spec_boundary_guards": (
            "rank", "id", "canonical_name", "vacuity_class", "description",
        ),
    },
    "SpecBoundaryGuards.lean": {
        "property_classes": ("rank", "id", "variant", "is_waivable"),
        "spec_boundary_guards": ("rank", "id", "canonical_name", "vacuity_class"),
    },
}


def _taxonomy_drift_errors(
    source: str, found: dict[str, object], expected: dict[str, object]
) -> list[str]:
    errors: list[str] = []
    if source == "property_registry.rs" and "schema_version" not in found:
        errors.append(f"property taxonomy drift: {source} is missing schema_version")
    elif "schema_version" in found and found["schema_version"] != expected["schema_version"]:
        errors.append(
            f"property taxonomy drift: {source} schema_version is "
            f"{found['schema_version']!r}, expected {expected['schema_version']!r}"
        )
    req_sections = _TAXONOMY_REQUIRED_KEYS.get(source, {})
    for section in ("property_classes", "spec_boundary_guards"):
        found_rows: list[dict[str, object]] = found[section]  # type: ignore[assignment]
        expected_rows: list[dict[str, object]] = expected[section]  # type: ignore[assignment]
        if len(found_rows) != len(expected_rows):
            errors.append(
                f"property taxonomy drift: {source} has {len(found_rows)} {section}, "
                f"expected {len(expected_rows)}"
            )
        req_keys = req_sections.get(section, ())
        for found_row, expected_row in zip(found_rows, expected_rows):
            keys_to_check = list(dict.fromkeys((*req_keys, *found_row.keys())))
            for key in keys_to_check:
                if key not in found_row:
                    errors.append(
                        f"property taxonomy drift: {source} {section}[{expected_row['rank']}] "
                        f"is missing key {key!r}"
                    )
                    continue
                value = found_row[key]
                want = expected_row.get(key)
                if key not in expected_row or value != want or type(value) is not type(want):
                    errors.append(
                        f"property taxonomy drift: {source} {section}[{expected_row['rank']}]"
                        f".{key} is {value!r}, expected {want!r}"
                    )
    return errors


def validate_property_taxonomy(
    anneal_root: Path,
    *,
    require_rust_taxonomy: bool | None = None,
    require_lean_taxonomy: bool | None = None,
) -> list[str]:
    """Check this script's taxonomy against the live Rust and Lean sources.

    `property_registry.rs` is checked whenever it exists under `anneal_root`,
    and its absence is an error when `require_rust_taxonomy` is true. With the
    default `None` it is required exactly when `anneal_root` is the checkout
    this script lives in, so an isolated test root that stages only
    `trusted/lean` still validates. `SpecBoundaryGuards.lean` follows the same
    rule (overrideable via `require_lean_taxonomy`).
    """
    errors: list[str] = []
    canonical = canonical_property_taxonomy()
    if (
        tuple(row[0] for row in _PROPERTY_CLASS_ROWS) != CANONICAL_PROPERTY_CLASSES
        or len(set(CANONICAL_PROPERTY_CLASSES)) != 12
    ):
        errors.append("CANONICAL_PROPERTY_CLASSES is not the 12 distinct manifest class ids")
    if (
        tuple(row[0] for row in _SPEC_BOUNDARY_GUARD_ROWS) != CANONICAL_SPEC_BOUNDARY_GUARDS
        or len(set(CANONICAL_SPEC_BOUNDARY_GUARDS)) != 3
    ):
        errors.append("CANONICAL_SPEC_BOUNDARY_GUARDS is not the 3 distinct manifest guard ids")

    root = Path(anneal_root)
    try:
        own_checkout = root.resolve() == _default_anneal_root()
    except OSError:
        own_checkout = False
    rust_required = own_checkout if require_rust_taxonomy is None else require_rust_taxonomy
    lean_required = own_checkout if require_lean_taxonomy is None else require_lean_taxonomy
    for rel, required, extract, source in (
        (_RUST_TAXONOMY_REL, rust_required, extract_rust_property_taxonomy, "property_registry.rs"),
        (_LEAN_TAXONOMY_REL, lean_required, extract_lean_property_taxonomy, "SpecBoundaryGuards.lean"),
    ):
        if not required and not os.path.lexists(root / rel):
            continue
        try:
            found = extract(root)
        except ValueError as exc:
            errors.append(f"property taxonomy: {exc}")
            continue
        errors.extend(_taxonomy_drift_errors(source, found, canonical))
    return errors


def _guard_property_class_errors() -> list[str]:
    """Every cataloged guard names a canonical class its disposition allows."""
    errors: list[str] = []
    if tuple(PROPERTY_CLASS_DISPOSITIONS) != CANONICAL_PROPERTY_CLASSES:
        errors.append(
            "PROPERTY_CLASS_DISPOSITIONS must list exactly the 12 canonical property "
            "classes in rank order"
        )
    guarded: Counter[str] = Counter()
    for guard in MIR_SEMANTICS_GUARDS:
        if guard.property_class == PROPERTY_CLASS_UNSPECIFIED:
            errors.append(f"{guard.guard_id}: missing explicit property_class")
        elif guard.property_class not in CANONICAL_PROPERTY_CLASSES:
            errors.append(
                f"{guard.guard_id}: unknown property_class {guard.property_class!r} "
                f"(expected one of {', '.join(CANONICAL_PROPERTY_CLASSES)})"
            )
        else:
            guarded[guard.property_class] += 1
    for class_id in CANONICAL_PROPERTY_CLASSES:
        disposition = PROPERTY_CLASS_DISPOSITIONS.get(class_id)
        if disposition is None:
            continue
        if disposition.coverage not in PROPERTY_CLASS_COVERAGE_KINDS:
            errors.append(
                f"PROPERTY_CLASS_DISPOSITIONS[{class_id!r}]: unknown coverage "
                f"{disposition.coverage!r}"
            )
        elif not disposition.rationale.strip():
            errors.append(f"PROPERTY_CLASS_DISPOSITIONS[{class_id!r}]: empty rationale")
        elif (disposition.coverage == "single_step_ub_guarded") != (guarded[class_id] > 0):
            errors.append(
                f"PROPERTY_CLASS_DISPOSITIONS[{class_id!r}] is {disposition.coverage!r} "
                f"but the catalog tags {guarded[class_id]} guard(s) with the class"
            )
    return errors


def property_class_summary(
    guards: Sequence[MirSemanticsGuard], results: Sequence[GuardResult] = ()
) -> list[dict[str, object]]:
    """One row per canonical property class, in rank order.

    `cataloged` counts the class's guards in `MIR_SEMANTICS_GUARDS`; `selected`,
    `guard_ids` and the `killed` / `survived` / `errors` tallies cover `guards`
    and their `results`.
    """
    status_by_id = {result.guard_id: result.status for result in results}
    rows: list[dict[str, object]] = []
    for rank, class_id in enumerate(CANONICAL_PROPERTY_CLASSES):
        selected = [g.guard_id for g in guards if g.property_class == class_id]
        statuses = [status_by_id.get(guard_id) for guard_id in selected]
        disposition = PROPERTY_CLASS_DISPOSITIONS.get(class_id)
        rows.append(
            {
                "rank": rank,
                "property_class": class_id,
                "coverage": disposition.coverage if disposition else None,
                "cataloged": sum(
                    1 for g in MIR_SEMANTICS_GUARDS if g.property_class == class_id
                ),
                "selected": len(selected),
                "killed": statuses.count("KILLED"),
                "survived": statuses.count("SURVIVED"),
                "errors": statuses.count("ERROR"),
                "guard_ids": selected,
            }
        )
    return rows


# ---------------------------------------------------------------------------
# Postcondition error-branch wildcard probe (`error_branch_wildcard`, `awsm2`)
# ---------------------------------------------------------------------------
#
# A postcondition arm such as `| .ub => True` or `Err(_) => true` accepts every
# error escape, so a kernel-checked proof of it says nothing about the error
# path. The scanner below is the stdlib-only counterpart of
# `anneal_spec::spec_check::scan_error_branch_wildcard` and reports under the
# same guard id and pattern wire identifiers.

SPEC_WILDCARD_GUARD_ID = "error_branch_wildcard"

# `ErrorWildcardPattern::as_str` of `anneal-spec`.
ERROR_WILDCARD_PATTERNS: tuple[str, ...] = (
    "err_arm_true",
    "ub_arm_true",
    "unsupported_arm_true",
    "matches_any_err",
    "catch_all_arm_true",
    "unclosed_literal_or_comment",
)

# The error outcomes a postcondition must reject: an `Err` / `.error` result
# with an arbitrary payload, undefined behavior, and an unsupported construct.
ERROR_MUTANT_KINDS: tuple[str, ...] = ("err", "ub", "unsupported")

_WILDCARD_WIRE_ID: dict[str, str] = {
    "err": "err_arm_true",
    "ub": "ub_arm_true",
    "unsupported": "unsupported_arm_true",
}


@dataclass(frozen=True)
class ErrorWildcardFinding:
    """One vacuous error-branch arm (or a source that cannot be scanned)."""

    guard_id: str
    pattern: str
    language: str
    line: int
    column: int
    arm: str


_SPEC_TOKEN_RE = re.compile(
    r'"[^"]*"|«[^»\n]*»|r#[^\W\d][\w]*|[^\W\d][\w\']*|\d[\w.]*'
    r"|==>|=>|::|\.\.=|\.\.|->|:=|==|!=|<=|>=|&&|\|\||/\\|\\/|<->|\S"
)
_SPEC_WORD_RE = re.compile(r"[^\W\d][\w']*")
_SPEC_OPENERS: dict[str, str] = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
_SPEC_CLOSERS: frozenset[str] = frozenset(_SPEC_OPENERS.values())
_LEAN_ARM_BOUNDARY_WORDS: frozenset[str] = frozenset(
    "with fun match def theorem lemma abbrev instance example where then else do by in "
    "at have show from let if return structure inductive namespace open end".split()
)
_LEAN_DECL_WORDS: frozenset[str] = frozenset(
    "def theorem lemma abbrev instance example structure inductive class namespace "
    "section end open variable universe import private protected noncomputable "
    "opaque axiom syntax macro elab notation local scoped unsafe partial mutual "
    "export attribute set_option".split()
)
_RUST_ARM_BOUNDARY_WORDS: frozenset[str] = frozenset({"match", "return", "else", "let"})
# Boundaries after which the first `|`-separated piece really is a pattern.
_CLEAN_ARM_STARTS: frozenset[str] = frozenset({"", "with", "fun", ",", "}", *_SPEC_OPENERS})
_TRUE_ATOMS: frozenset[str] = frozenset({"true", "True", "trivial", "⊤"})
_FALSE_ATOMS: frozenset[str] = frozenset({"false", "False", "⊥"})
_SPECIFIC_LOWER_PATTERNS: frozenset[str] = frozenset(
    {"true", "false", "none", "some", "nil", "zero", "unit"}
)
_PATTERN_PREFIX_WORDS: frozenset[str] = frozenset({"&", "&&", "ref", "mut", "box"})
_MAX_SPEC_DEPTH = 24


def _spec_tokens(code: str) -> list[tuple[str, int, int, bool]]:
    """`(text, line, column, first_on_line)` tokens of comment-free `code`."""
    toks: list[tuple[str, int, int, bool]] = []
    line, line_start, scan, prev_line = 1, 0, 0, 0
    for m in _SPEC_TOKEN_RE.finditer(code):
        start = m.start()
        newlines = code.count("\n", scan, start)
        if newlines:
            line += newlines
            line_start = code.rfind("\n", scan, start) + 1
        scan = start
        toks.append((m.group(0), line, start - line_start + 1, line != prev_line))
        prev_line = line
    return toks


def _match_delimiters(toks: Sequence[tuple[str, int, int, bool]]) -> dict[int, int]:
    partner: dict[int, int] = {}
    stack: list[int] = []
    for idx, tok in enumerate(toks):
        text = tok[0]
        if text in _SPEC_OPENERS:
            stack.append(idx)
        elif text in _SPEC_CLOSERS:
            if not stack or _SPEC_OPENERS[toks[stack[-1]][0]] != text:
                raise SourceLexError(f"unbalanced `{text}` at line {tok[1]}")
            open_idx = stack.pop()
            partner[open_idx] = idx
            partner[idx] = open_idx
    if stack:
        raise SourceLexError(f"unclosed `{toks[stack[-1]][0]}` at line {toks[stack[-1]][1]}")
    return partner


def _split_top(texts: Sequence[str], seps: frozenset[str] | set[str]) -> list[list[str]]:
    """Split a balanced token run on `seps` outside every bracket."""
    parts: list[list[str]] = [[]]
    depth = 0
    for text in texts:
        if text in _SPEC_OPENERS:
            depth += 1
        elif text in _SPEC_CLOSERS:
            depth -= 1
        elif depth == 0 and text in seps:
            parts.append([])
            continue
        parts[-1].append(text)
    return parts


def _wrapped(texts: Sequence[str]) -> bool:
    """Whether `texts` is one bracket group: its first token closes at its last."""
    if len(texts) < 2 or texts[0] not in _SPEC_OPENERS or texts[-1] != _SPEC_OPENERS[texts[0]]:
        return False
    depth = 0
    for idx, text in enumerate(texts):
        if text in _SPEC_OPENERS:
            depth += 1
        elif text in _SPEC_CLOSERS:
            depth -= 1
            if depth == 0:
                return idx == len(texts) - 1
    return False


def _strip_parens(texts: Sequence[str]) -> list[str]:
    out = list(texts)
    while out and out[0] == "(" and _wrapped(out):
        out = out[1:-1]
    return out


def _int_literal(texts: Sequence[str]) -> int | None:
    if len(texts) == 1 and texts[0].isascii() and texts[0].isdigit():
        return int(texts[0])
    return None


_RUST_EXPR_CONT_OPS: frozenset[str] = frozenset(
    {".", "&&", "||", "==", "!=", "<", "<=", ">", ">=", "as", "?", "+", "-", "*", "/", "%", "&", "|", "^"}
)
_RUST_BLOCK_CTRL_WORDS: frozenset[str] = frozenset(
    {"if", "match", "while", "for", "loop", "break", "continue", "return", "panic", "assert",
     "assert_eq", "assert_ne", "debug_assert", "unreachable"}
)
_RUST_NON_STRUCT_BEFORE_BRACE: frozenset[str] = frozenset(
    {"match", "else", "loop", "unsafe", "async", "try", "move", "do"}
)


def _split_first_top(texts: Sequence[str], seps: frozenset[str] | set[str]) -> tuple[list[str], list[str]] | None:
    """Split `texts` at the first top-level token in `seps`, or `None` if absent."""
    depth = 0
    for idx, text in enumerate(texts):
        if text in _SPEC_OPENERS:
            depth += 1
        elif text in _SPEC_CLOSERS:
            depth -= 1
        elif depth == 0 and text in seps:
            return list(texts[:idx]), list(texts[idx + 1 :])
    return None


_COMPLEMENT_LOW_PREC_OPS: frozenset[str] = frozenset(
    {"&&", "∧", "/\\", "||", "∨", "\\/", "→", "->", "==>", "↔", "<->"}
)
_COMPLEMENT_CMP_OPS: frozenset[str] = frozenset(
    {"==", "=", "!=", "≠", "<=", "≤", ">=", "≥", "<", ">"}
)
_CLOSURE_BAR_PRECEDERS: frozenset[str] = frozenset(
    {"", "(", "{", "[", ",", ";", "=", ":=", "=>", "move", "return", "&&", "||", "!"}
)


def _has_macro_invocation(toks: Sequence[str]) -> bool:
    return any(
        tok == "!" and idx > 0 and _is_spec_word(toks[idx - 1])
        for idx, tok in enumerate(toks)
    )


def _has_call_expr(toks: Sequence[str]) -> bool:
    return any(
        tok == "(" and idx > 0 and (_is_spec_word(toks[idx - 1]) or toks[idx - 1] in (")", "]", ">"))
        for idx, tok in enumerate(toks)
    )


def _rust_brace_ends_arm(toks: Sequence[str], close_idx: int) -> bool:
    """Whether closing `}` at `close_idx` terminates a Rust `match` arm body."""
    n = len(toks)
    if close_idx + 1 >= n:
        return True
    after = toks[close_idx + 1]
    if after in (",", ";") or after in _SPEC_CLOSERS:
        return True
    if after in ("else", "=", "{"):
        return False
    if after in _RUST_EXPR_CONT_OPS:
        bdepth = 0
        probe = close_idx + 1
        while probe < n:
            pt = toks[probe]
            if pt in _SPEC_OPENERS:
                bdepth += 1
            elif pt in _SPEC_CLOSERS:
                if bdepth == 0:
                    return False
                bdepth -= 1
            elif bdepth == 0:
                if pt == "=>":
                    return True
                if pt in (",", ";"):
                    return False
            probe += 1
        return False
    return True


_NON_BINDER_PATTERN_WORDS: frozenset[str] = frozenset(
    {"mut", "ref", "box", "_", "true", "false", "True", "False", "none", "some", "nil", "zero", "unit"}
)


def _pattern_binder_names(pat_toks: Sequence[str]) -> set[str]:
    """Variable names bound by a Rust or Lean pattern slice."""
    names: set[str] = set()
    n = len(pat_toks)
    in_type = False
    bdepth = 0
    for idx, tok in enumerate(pat_toks):
        prev = pat_toks[idx - 1] if idx > 0 else ""
        nxt = pat_toks[idx + 1] if idx + 1 < n else ""
        if tok in _SPEC_OPENERS:
            bdepth += 1
            in_type = False
            continue
        if tok in _SPEC_CLOSERS:
            bdepth = max(0, bdepth - 1)
            in_type = False
            continue
        if tok in (",", "|"):
            in_type = False
            continue
        if tok == ":" and prev != ":" and nxt != ":":
            if bdepth == 0:
                in_type = True
            continue
        if in_type or not _is_spec_word(tok):
            continue
        if prev in (".", "::") or nxt in ("::", ".", "{", ":="):
            continue
        if nxt == ":" and idx + 2 < n:
            # Struct field label (`{ field: pat }`), not the bound variable.
            continue
        if tok.startswith("r#") and len(tok) > 2:
            plain = tok[2:]
            if plain != "_" and not plain[0].isupper():
                names.add(plain)
            continue
        plain = _unquote_ident(tok)
        if plain in _NON_BINDER_PATTERN_WORDS:
            continue
        if plain[0] == "_" or not plain[0].isupper():
            names.add(plain)
    return names


def _subst_lean_match_arms(arms_toks: Sequence[str], scope: dict[str, str], depth: int) -> list[str]:
    """Substitute `scope` across Lean `| <pat> => <body>` arms while respecting pattern binders."""
    if not arms_toks or depth > _MAX_SPEC_DEPTH:
        return list(arms_toks)
    segments: list[list[str]] = [[]]
    has_bar: list[bool] = [False]
    bdepth = 0
    for tok in arms_toks:
        if tok in _SPEC_OPENERS:
            bdepth += 1
        elif tok in _SPEC_CLOSERS:
            bdepth -= 1
        elif bdepth == 0 and tok == "|":
            segments.append([])
            has_bar.append(True)
            continue
        segments[-1].append(tok)
    out: list[str] = []
    pending_pats: list[tuple[bool, list[str]]] = []
    for bar, seg in zip(has_bar, segments):
        if not seg and not bar:
            continue
        arrow = _split_first_top(seg, {"=>"})
        if arrow is None:
            pending_pats.append((bar, seg))
            continue
        pat, body = arrow
        pats = [*pending_pats, (bar, pat)]
        pending_pats = []
        binders: set[str] = set()
        for _, p_toks in pats:
            binders |= _pattern_binder_names(p_toks)
        arm_scope = {k: v for k, v in scope.items() if k not in binders}
        for p_bar, p_toks in pats:
            if p_bar:
                out.append("|")
            out.extend(p_toks)
        out.append("=>")
        out.extend(_subst_ident_map(body, arm_scope, depth + 1))
    for p_bar, p_toks in pending_pats:
        if p_bar:
            out.append("|")
        out.extend(p_toks)
    return out


def _subst_rust_match_inner(inner: Sequence[str], scope: dict[str, str], depth: int) -> list[str]:
    """Substitute `scope` across a Rust `match` `{ ... }` arm list while respecting pattern binders."""
    if not inner or depth > _MAX_SPEC_DEPTH:
        return list(inner)
    raw_arms: list[list[str]] = []
    cur: list[str] = []
    bdepth = 0
    saw_arrow = False
    n = len(inner)
    for idx, tok in enumerate(inner):
        if tok in _SPEC_OPENERS:
            bdepth += 1
            cur.append(tok)
            continue
        if tok in _SPEC_CLOSERS:
            bdepth -= 1
            cur.append(tok)
            if bdepth == 0 and tok == "}" and saw_arrow and _rust_brace_ends_arm(inner, idx):
                raw_arms.append(cur)
                cur = []
                saw_arrow = False
            continue
        if bdepth == 0 and tok == ",":
            if cur:
                raw_arms.append(cur)
                cur = []
                saw_arrow = False
            continue
        if bdepth == 0 and tok == "=>":
            saw_arrow = True
        cur.append(tok)
    if cur:
        raw_arms.append(cur)
    out: list[str] = []
    for arm_idx, arm in enumerate(raw_arms):
        if arm_idx > 0:
            out.append(",")
        arrow = _split_first_top(arm, {"=>"})
        if arrow is None:
            out.extend(_subst_ident_map(arm, scope, depth + 1))
            continue
        pat_part, body = arrow
        guard_split = _split_first_top(pat_part, {"if"})
        pat_toks = pat_part if guard_split is None else guard_split[0]
        binders = _pattern_binder_names(pat_toks)
        arm_scope = {k: v for k, v in scope.items() if k not in binders}
        out.extend(pat_toks)
        if guard_split is not None:
            out.append("if")
            out.extend(_subst_ident_map(guard_split[1], arm_scope, depth + 1))
        out.append("=>")
        out.extend(_subst_ident_map(body, arm_scope, depth + 1))
    return out


def _subst_ident_map(toks: Sequence[str], bindings: dict[str, str], depth: int = 0) -> list[str]:
    """Substitute known constant identifiers outside member and shadowing binder positions."""
    if not bindings or depth > _MAX_SPEC_DEPTH:
        return list(toks)
    out: list[str] = []
    scopes: list[dict[str, str]] = [dict(bindings)]
    # Pending `(scope_depth, shadowed_names)` from `let`/`have` headers waiting for `;`/`in`.
    pending_lets: list[tuple[int, set[str]]] = []
    # Pending `[scope_depth, shadowed_names, saved_scope, stage, if_nesting]` for `if let`.
    pending_if_lets: list[list[object]] = []
    skip_until = -1
    n = len(toks)
    idx = 0
    while idx < n:
        tok = toks[idx]
        prev = toks[idx - 1] if idx > 0 else ""
        sdepth = len(scopes) - 1
        if idx < skip_until:
            if tok in _SPEC_OPENERS:
                scopes.append(dict(scopes[-1]))
            elif tok in _SPEC_CLOSERS and len(scopes) > 1:
                scopes.pop()
            out.append(tok)
            idx += 1
            continue
        if tok in _SPEC_OPENERS:
            new_scope = dict(scopes[-1])
            if tok == "{":
                for p_idx in range(len(pending_if_lets) - 1, -1, -1):
                    entry = pending_if_lets[p_idx]
                    if entry[0] == sdepth and entry[3] == 0:
                        for name in entry[1]:  # type: ignore[attr-defined]
                            new_scope.pop(name, None)
                        pending_if_lets.pop(p_idx)
                        break
            scopes.append(new_scope)
            out.append(tok)
            idx += 1
            continue
        if tok in _SPEC_CLOSERS:
            if len(scopes) > 1:
                pending_lets = [p for p in pending_lets if p[0] < sdepth]
                pending_if_lets = [p for p in pending_if_lets if int(p[0]) < sdepth]  # type: ignore[arg-type]
                scopes.pop()
            out.append(tok)
            idx += 1
            continue
        if tok == "if":
            for entry in pending_if_lets:
                if entry[0] == sdepth and entry[3] == 1:
                    entry[4] = int(entry[4]) + 1  # type: ignore[arg-type]
        elif tok == "then":
            for entry in reversed(pending_if_lets):
                if entry[0] == sdepth and entry[3] == 0:
                    entry[3] = 1
                    for name in entry[1]:  # type: ignore[attr-defined]
                        scopes[-1].pop(name, None)
                    break
        elif tok == "else":
            for p_idx in range(len(pending_if_lets) - 1, -1, -1):
                entry = pending_if_lets[p_idx]
                if entry[0] == sdepth and entry[3] == 1:
                    if int(entry[4]) > 0:  # type: ignore[arg-type]
                        entry[4] = int(entry[4]) - 1  # type: ignore[arg-type]
                    else:
                        scopes[-1] = dict(entry[2])  # type: ignore[arg-type]
                        pending_if_lets.pop(p_idx)
                    break
        if tok in (";", "in"):
            remaining_pending: list[tuple[int, set[str]]] = []
            for p_depth, p_names in pending_lets:
                if p_depth == sdepth:
                    for name in p_names:
                        scopes[-1].pop(name, None)
                else:
                    remaining_pending.append((p_depth, p_names))
            pending_lets = remaining_pending
            out.append(tok)
            idx += 1
            continue
        if tok == "match":
            # Find extent of current bracket scope so inner/outer `match` blocks stay bounded.
            end_scope = idx + 1
            bdepth = 0
            open_brace = -1
            with_at = -1
            while end_scope < n:
                st = toks[end_scope]
                if st in _SPEC_OPENERS:
                    if bdepth == 0 and st == "{" and open_brace == -1 and with_at == -1:
                        open_brace = end_scope
                    bdepth += 1
                elif st in _SPEC_CLOSERS:
                    if bdepth == 0:
                        break
                    bdepth -= 1
                    if bdepth == 0 and open_brace != -1:
                        if toks[end_scope + 1 : end_scope + 2] == ["{"]:
                            open_brace = -1
                        else:
                            close_brace = end_scope
                            out.append("match")
                            out.extend(_subst_ident_map(toks[idx + 1 : open_brace], scopes[-1], depth + 1))
                            out.append("{")
                            out.extend(_subst_rust_match_inner(toks[open_brace + 1 : close_brace], scopes[-1], depth + 1))
                            out.append("}")
                            idx = close_brace + 1
                            open_brace = -2
                            break
                elif bdepth == 0 and st == "with" and open_brace == -1 and with_at == -1:
                    with_at = end_scope
                end_scope += 1
            if open_brace == -2:
                continue
            if with_at != -1:
                out.append("match")
                out.extend(_subst_ident_map(toks[idx + 1 : with_at], scopes[-1], depth + 1))
                out.append("with")
                out.extend(_subst_lean_match_arms(toks[with_at + 1 : end_scope], scopes[-1], depth + 1))
                idx = end_scope
                continue
        if (tok == "fun" or tok.startswith("λ")) and toks[idx + 1 : idx + 2] == ["|"]:
            end_scope = idx + 1
            bdepth = 0
            while end_scope < n:
                st = toks[end_scope]
                if st in _SPEC_OPENERS:
                    bdepth += 1
                elif st in _SPEC_CLOSERS:
                    if bdepth == 0:
                        break
                    bdepth -= 1
                end_scope += 1
            out.append(tok)
            out.extend(_subst_lean_match_arms(toks[idx + 1 : end_scope], scopes[-1], depth + 1))
            idx = end_scope
            continue
        if tok in ("let", "have"):
            bdepth = 0
            scan = idx + 1
            while scan < n:
                st = toks[scan]
                if st in _SPEC_OPENERS:
                    bdepth += 1
                elif st in _SPEC_CLOSERS:
                    if bdepth == 0:
                        break
                    bdepth -= 1
                elif bdepth == 0 and st in (":=", "=", ";", "in"):
                    break
                scan += 1
            header_names = _pattern_binder_names(toks[idx + 1 : scan])
            if prev in ("if", "while"):
                if header_names:
                    pending_if_lets.append([sdepth, header_names, dict(scopes[-1]), 0, 0])
            elif header_names:
                pending_lets.append((sdepth, header_names))
            skip_until = scan
            out.append(tok)
            idx += 1
            continue
        if tok == "fun" or tok.startswith("λ") or tok in ("∀", "forall"):
            stop_tok = "," if tok in ("∀", "forall") else "=>"
            bdepth = 0
            scan = idx + 1
            binder_names: set[str] = set()
            binder_positions: set[int] = set()
            in_top_type = False
            in_group_type = False
            if tok.startswith("λ") and len(tok) > 1:
                binder_names.add(tok[1:])
            while scan < n:
                st = toks[scan]
                if st in _SPEC_OPENERS:
                    if bdepth == 0:
                        in_group_type = False
                    bdepth += 1
                elif st in _SPEC_CLOSERS:
                    if bdepth == 0:
                        break
                    bdepth -= 1
                    if bdepth == 0:
                        in_group_type = False
                elif bdepth == 0 and st == stop_tok:
                    break
                elif bdepth == 0 and st == ":":
                    in_top_type = True
                elif bdepth == 1 and st == ":":
                    in_group_type = True
                elif _is_spec_word(st) and (
                    (bdepth == 0 and not in_top_type) or (bdepth == 1 and not in_group_type)
                ):
                    u = _ident_key(st)
                    binder_positions.add(scan)
                    if u in scopes[-1]:
                        binder_names.add(u)
                scan += 1
            if scan < n and toks[scan] == stop_tok:
                out.append(tok)
                hdr_idx = idx + 1
                while hdr_idx <= scan:
                    ht = toks[hdr_idx]
                    hprev = toks[hdr_idx - 1] if hdr_idx > 0 else ""
                    hkey = _ident_key(ht)
                    if hdr_idx not in binder_positions and hprev not in (".", "::") and hkey in scopes[-1]:
                        out.append(scopes[-1][hkey])
                    else:
                        out.append(ht)
                    hdr_idx += 1
                for name in binder_names:
                    scopes[-1].pop(name, None)
                idx = scan + 1
                continue
        if tok == "|" and prev in _CLOSURE_BAR_PRECEDERS:
            bdepth = 0
            scan = idx + 1
            binder_names = set()
            binder_positions = set()
            in_param_type = False
            while scan < n:
                st = toks[scan]
                if st in _SPEC_OPENERS:
                    bdepth += 1
                elif st in _SPEC_CLOSERS:
                    if bdepth == 0:
                        break
                    bdepth -= 1
                elif bdepth == 0 and st == "|":
                    break
                elif bdepth == 0 and st in (";", "=>"):
                    scan = n
                    break
                elif bdepth == 0 and st == ",":
                    in_param_type = False
                elif bdepth == 0 and st == ":":
                    in_param_type = True
                elif not in_param_type and _is_spec_word(st):
                    u = _ident_key(st)
                    binder_positions.add(scan)
                    if u in scopes[-1]:
                        binder_names.add(u)
                scan += 1
            if scan < n and toks[scan] == "|":
                out.append(tok)
                hdr_idx = idx + 1
                while hdr_idx <= scan:
                    ht = toks[hdr_idx]
                    hprev = toks[hdr_idx - 1] if hdr_idx > 0 else ""
                    hkey = _ident_key(ht)
                    if hdr_idx not in binder_positions and hprev not in (".", "::") and hkey in scopes[-1]:
                        out.append(scopes[-1][hkey])
                    else:
                        out.append(ht)
                    hdr_idx += 1
                for name in binder_names:
                    scopes[-1].pop(name, None)
                idx = scan + 1
                continue
        key = _ident_key(tok)
        if prev not in (".", "::") and key in scopes[-1]:
            out.append(scopes[-1][key])
        else:
            out.append(tok)
        idx += 1
    return out


def _is_pure_reflexive_operand(toks: Sequence[str]) -> bool:
    """Whether `toks` is a side-effect-free non-NaN operand safe for `e == e` folding."""
    stripped = _strip_parens(toks)
    if not stripped:
        return True  # unit `()`
    for idx, tok in enumerate(stripped):
        u = _unquote_ident(tok)
        if u.upper() in ("NAN", "INFINITY", "INF"):
            return False
        if tok in ("{", "}", "?", "/", "%"):
            return False
        if tok == "!" and idx > 0 and _is_spec_word(stripped[idx - 1]):
            # Macro invocation (`foo!(...)`): may panic or have side effects.
            return False
        if tok == "(" and idx > 0 and (_is_spec_word(stripped[idx - 1]) or stripped[idx - 1] in (")", "]", ">")):
            # Function or method call (`f(x)`, `iter.next()`): may have side effects.
            return False
    return True


def _complement_signature(part: Sequence[str], depth: int = 0) -> tuple[str, object] | None:
    """Canonical polarity signature of a pure proposition/boolean disjunct or conjunct."""
    if depth > _MAX_SPEC_DEPTH:
        return None
    toks = _strip_parens(part)
    if not toks:
        return None
    if toks[0] in ("!", "¬", "Not", "not") and len(toks) > 1:
        rest = toks[1:]
        # Only treat leading negation as applying to the full expression when
        # no looser-binding top-level connective sits in `rest` (e.g. `!x && y`
        # or `¬p ∧ q` is `(!x) && y`, not `!(x && y)`).
        looser_ops = _COMPLEMENT_LOW_PREC_OPS | (
            _COMPLEMENT_CMP_OPS if toks[0] in ("!", "not") else frozenset()
        )
        if len(_split_top(rest, looser_ops)) == 1:
            inner = _strip_parens(rest)
            if inner:
                sub = _complement_signature(inner, depth + 1)
                if sub is not None:
                    sub_kind, sub_payload = sub
                    flip = {"pos": "neg", "neg": "pos", "eq": "neq", "neq": "eq"}[sub_kind]
                    return (flip, sub_payload)
            return None
    if len(_split_top(toks, _COMPLEMENT_LOW_PREC_OPS)) == 1:
        for eq_ops, polarity in ((("==", "="), "eq"), (("!=", "≠"), "neq")):
            for op in eq_ops:
                sides = _split_top(toks, {op})
                if len(sides) == 2 and sides[0] and sides[1]:
                    lhs, rhs = _strip_parens(sides[0]), _strip_parens(sides[1])
                    if _is_pure_reflexive_operand(lhs) and _is_pure_reflexive_operand(rhs):
                        pair = tuple(sorted((tuple(lhs), tuple(rhs))))
                        return (polarity, pair)
    if _is_pure_reflexive_operand(toks):
        return ("pos", tuple(toks))
    return None


def _has_complementary_pair(parts: Sequence[Sequence[str]]) -> bool:
    seen: set[tuple[str, object]] = set()
    for part in parts:
        sig = _complement_signature(part)
        if sig is None:
            continue
        kind, payload = sig
        opposite = {"pos": "neg", "neg": "pos", "eq": "neq", "neq": "eq"}[kind]
        if (opposite, payload) in seen:
            return True
        seen.add(sig)
    return False


_RUST_BLOCK_ABORT_WORDS: frozenset[str] = frozenset(
    {"while", "for", "loop", "break", "continue", "return", "panic", "assert",
     "assert_eq", "assert_ne", "debug_assert", "unreachable"}
)


def _split_rust_block_statements(toks: Sequence[str]) -> list[list[str]]:
    """Split a Rust `{ ... }` body into top-level `;`- and block-terminated statements."""
    statements: list[list[str]] = []
    cur: list[str] = []
    bdepth = 0
    n = len(toks)
    for idx, tok in enumerate(toks):
        if tok in _SPEC_OPENERS:
            bdepth += 1
            cur.append(tok)
            continue
        if tok in _SPEC_CLOSERS:
            bdepth -= 1
            cur.append(tok)
            if (
                bdepth == 0
                and tok == "}"
                and cur[0] in ("{", "unsafe", "if", "match")
                and idx + 1 < n
                and toks[idx + 1] != ";"
                and _rust_brace_ends_arm(toks, idx)
            ):
                statements.append(cur)
                cur = []
            continue
        if bdepth == 0 and tok == ";":
            if cur:
                statements.append(cur)
                cur = []
            continue
        cur.append(tok)
    if cur:
        statements.append(cur)
    return statements


def _has_non_let_assignment(toks: Sequence[str]) -> bool:
    """Whether `toks` contains any `=` outside an inner `let` header."""
    in_let_header = False
    for tok in toks:
        if tok in (";", "{", "}"):
            in_let_header = False
        elif tok == "let":
            in_let_header = True
        elif tok == "=":
            if not in_let_header:
                return True
            in_let_header = False
    return False


def _eval_rust_block_statements(toks: Sequence[str], depth: int) -> bool | None:
    """Fold a Rust `{ ... }` block body without ignoring earlier control flow."""
    statements = _split_rust_block_statements(toks)
    if not statements:
        return None
    bindings: dict[str, str] = {}
    for stmt in statements[:-1]:
        if stmt[0] == "return":
            return _const_truth(_subst_ident_map(stmt[1:], bindings), depth + 1)
        if (
            any(word in _RUST_BLOCK_ABORT_WORDS for word in stmt)
            or "?" in stmt
            or _has_macro_invocation(stmt)
            or _has_call_expr(stmt)
        ):
            return None
        if stmt[0] == "let":
            eq_split = _split_first_top(stmt[1:], {"="})
            if eq_split is None:
                continue
            lhs, rhs = eq_split
            if _has_non_let_assignment(rhs):
                return None
            if lhs[:1] == ["mut"]:
                lhs = lhs[1:]
            lhs = _split_top(lhs, {":"})[0]
            lhs = _strip_parens(lhs)
            if len(lhs) != 1 or not (lhs[0] == "_" or _is_spec_word(lhs[0])):
                # Refutable destructuring (`let Ok(x) = ...` / `let true = ...`).
                return None
            binder = _ident_key(lhs[0])
            rhs_val = _const_truth(_subst_ident_map(rhs, bindings), depth + 1)
            if binder != "_":
                if rhs_val is True:
                    bindings[binder] = "true"
                elif rhs_val is False:
                    bindings[binder] = "false"
                else:
                    bindings.pop(binder, None)
            continue
        eq_split = _split_first_top(stmt, {"="})
        if eq_split is not None and stmt[0] not in ("{", "if", "match", "unsafe"):
            lhs, rhs = eq_split
            lhs_s = _strip_parens(lhs)
            if len(lhs_s) != 1 or not _is_spec_word(lhs_s[0]) or _has_non_let_assignment(rhs):
                # Compound assignment (`&=`, `|=`), inner mutation, or field/deref mutation: abort.
                return None
            target = _ident_key(lhs_s[0])
            rhs_val = _const_truth(_subst_ident_map(rhs, bindings), depth + 1)
            if rhs_val is True:
                bindings[target] = "true"
            elif rhs_val is False:
                bindings[target] = "false"
            else:
                bindings.pop(target, None)
            continue
        if _has_non_let_assignment(stmt):
            return None
    return _const_truth(_subst_ident_map(statements[-1], bindings), depth + 1)


def _strip_lean_let_prefix(toks: Sequence[str], depth: int) -> list[str] | None:
    """Strip or constant-propagate one `let`/`have` `<binder> ... := <rhs> (; | in) <body>` prefix."""
    if not toks or toks[0] not in ("let", "have"):
        return None
    split_pair = _split_first_top(toks, {";", "in"})
    if split_pair is None or not split_pair[0] or not split_pair[1]:
        return None
    header, rest = split_pair
    eq_split = _split_first_top(header[1:], {":="})
    if eq_split is None or not eq_split[1]:
        return None
    binder_lhs, rhs = eq_split
    binder_lhs = _strip_parens(_split_top(binder_lhs, {":"})[0])
    if len(binder_lhs) != 1:
        return None
    binder = _ident_key(binder_lhs[0])
    if binder == "_":
        return rest
    if not _is_spec_word(binder_lhs[0]):
        return None
    rhs_val = _const_truth(rhs, depth + 1)
    if rhs_val is True:
        return _subst_ident_map(rest, {binder: "True"})
    if rhs_val is False:
        return _subst_ident_map(rest, {binder: "False"})
    if all(_ident_key(tok) != binder for tok in rest):
        return rest
    return None


def _split_lean_if(toks: Sequence[str]) -> tuple[list[str], list[str], list[str]] | None:
    """Split Lean `if <cond> then <t> else <f>` matching nested `if`/`else` pairs."""
    if not toks or toks[0] != "if":
        return None
    bdepth = 0
    if_depth = 0
    then_idx: int | None = None
    else_idx: int | None = None
    for idx in range(1, len(toks)):
        tok = toks[idx]
        if tok in _SPEC_OPENERS:
            bdepth += 1
        elif tok in _SPEC_CLOSERS:
            bdepth -= 1
        elif bdepth == 0:
            if tok == "if":
                if_depth += 1
            elif tok == "then":
                if if_depth == 0 and then_idx is None:
                    then_idx = idx
            elif tok == "else":
                if if_depth == 0:
                    if then_idx is None:
                        return None
                    else_idx = idx
                    break
                if_depth -= 1
    if then_idx is None or else_idx is None:
        return None
    cond = list(toks[1:then_idx])
    t_branch = list(toks[then_idx + 1 : else_idx])
    f_branch = list(toks[else_idx + 1 :])
    if not cond or not t_branch or not f_branch:
        return None
    return cond, t_branch, f_branch


def _split_rust_if(toks: Sequence[str]) -> tuple[list[str], list[str], list[str]] | None:
    """Split a complete Rust `if <cond> { ... } else ({ ... } | if ...)` expression."""
    if not toks or toks[0] != "if" or toks[-1] != "}":
        return None
    else_split = _split_first_top(toks[1:], {"else"})
    if else_split is None or not else_split[0] or not else_split[1]:
        return None
    head, f_branch = else_split
    if head[-1] != "}":
        return None
    if not (
        (f_branch[0] == "{" and _wrapped(f_branch))
        or (f_branch[0] == "if" and _split_rust_if(f_branch) is not None)
    ):
        return None
    depth = 0
    open_idx = -1
    for idx, tok in enumerate(head):
        if tok in _SPEC_OPENERS:
            if depth == 0 and tok == "{":
                open_idx = idx
            depth += 1
        elif tok in _SPEC_CLOSERS:
            depth -= 1
            if depth == 0 and idx == len(head) - 1 and open_idx >= 0:
                return list(head[:open_idx]), list(head[open_idx:]), list(f_branch)
    return None


def _eval_lean_match_arms(arms_toks: Sequence[str], depth: int) -> bool | None:
    """Fold Lean `| <pat> => <body> ...` arms when every arm returns the same constant."""
    if not arms_toks:
        return None
    # Split on top-level `|`; layout-delimited nested `match`/`fun |` blocks are
    # parenthesized by `_normalize_lean_layout_lets`, and single-line inline ones
    # stay guarded by `nested_match`.
    segments: list[list[str]] = [[]]
    bdepth = 0
    saw_arrow = False
    nested_match = False
    for idx, tok in enumerate(arms_toks):
        if tok in _SPEC_OPENERS:
            bdepth += 1
        elif tok in _SPEC_CLOSERS:
            bdepth -= 1
        elif bdepth == 0:
            if tok == "|" and not nested_match:
                segments.append([])
                saw_arrow = False
                continue
            if tok == "=>" and not saw_arrow:
                saw_arrow = True
            elif saw_arrow and (
                tok == "match"
                or ((tok == "fun" or tok.startswith("λ")) and list(arms_toks[idx + 1 : idx + 2]) == ["|"])
            ):
                nested_match = True
        segments[-1].append(tok)
    parsed: list[tuple[list[list[str]], bool | None]] = []
    pending_pats: list[list[str]] = []
    for seg in segments:
        if not seg:
            continue
        arrow = _split_first_top(seg, {"=>"})
        if arrow is None:
            pending_pats.append(seg)
            continue
        pat, body = arrow
        if not pat or not body:
            return None
        pats = [*pending_pats, pat]
        pending_pats = []
        parsed.append((pats, _const_truth(body, depth + 1)))
    if pending_pats or not parsed:
        return None
    if len(parsed) == 1:
        pats, val = parsed[0]
        if not any(_alt_is_catch_all(p) for p in pats):
            return None
        return val
    vals = [val for _, val in parsed]
    if all(v is True for v in vals):
        return True
    if all(v is False for v in vals):
        return False
    return None


def _eval_rust_match(toks: Sequence[str], depth: int) -> bool | None:
    """Fold a Rust `match <scrutinee> { ... }` when every arm returns the same constant."""
    if not toks or toks[0] != "match" or toks[-1] != "}":
        return None
    bdepth = 0
    open_idx = -1
    for idx, tok in enumerate(toks):
        if tok in _SPEC_OPENERS:
            if bdepth == 0 and tok == "{":
                open_idx = idx
            bdepth += 1
        elif tok in _SPEC_CLOSERS:
            bdepth -= 1
            if bdepth == 0 and idx == len(toks) - 1 and open_idx > 1:
                break
            if bdepth == 0 and open_idx >= 0 and tok == "}":
                nxt_tok = toks[idx + 1] if idx + 1 < len(toks) else ""
                if nxt_tok != "{" and nxt_tok not in _RUST_EXPR_CONT_OPS:
                    return None
                open_idx = -1
    if open_idx <= 1:
        return None
    scrutinee = toks[1:open_idx]
    if (
        any(word in _RUST_BLOCK_ABORT_WORDS for word in scrutinee)
        or "?" in scrutinee
        or "/" in scrutinee
        or "%" in scrutinee
        or _has_macro_invocation(scrutinee)
        or _has_call_expr(scrutinee)
        or _has_non_let_assignment(scrutinee)
    ):
        return None
    inner = toks[open_idx + 1 : -1]
    if not inner:
        return None
    raw_arms: list[list[str]] = []
    cur: list[str] = []
    bdepth = 0
    saw_arrow = False
    idx = 0
    n = len(inner)
    while idx < n:
        tok = inner[idx]
        if tok in _SPEC_OPENERS:
            bdepth += 1
            cur.append(tok)
            idx += 1
            continue
        if tok in _SPEC_CLOSERS:
            bdepth -= 1
            cur.append(tok)
            if bdepth == 0 and tok == "}" and saw_arrow and _rust_brace_ends_arm(inner, idx):
                raw_arms.append(cur)
                cur = []
                saw_arrow = False
            idx += 1
            continue
        if bdepth == 0 and tok == ",":
            if cur:
                raw_arms.append(cur)
                cur = []
                saw_arrow = False
            idx += 1
            continue
        if bdepth == 0 and tok == "=>":
            saw_arrow = True
        cur.append(tok)
        idx += 1
    if cur:
        raw_arms.append(cur)
    if not raw_arms:
        return None
    parsed: list[tuple[list[list[str]], bool, bool | None]] = []
    for arm in raw_arms:
        arrow = _split_first_top(arm, {"=>"})
        if arrow is None or not arrow[0] or not arrow[1]:
            return None
        pat_part, body = arrow
        guard_split = _split_first_top(pat_part, {"if"})
        if guard_split is not None:
            pat_toks, guard_toks = guard_split
            if not pat_toks or not guard_toks:
                return None
            if not _is_pure_reflexive_operand(guard_toks):
                return None
            guard_always_true = _const_truth(guard_toks, depth + 1) is True
        else:
            pat_toks = pat_part
            guard_always_true = True
        alts = [alt for alt in _split_top(pat_toks, {"|"}) if alt]
        if not alts:
            return None
        parsed.append((alts, guard_always_true, _const_truth(body, depth + 1)))
    if len(parsed) == 1:
        alts, guard_always_true, val = parsed[0]
        if not guard_always_true or not any(_alt_is_catch_all(a) for a in alts):
            return None
        return val
    # An exhaustive Rust `match` always contains at least one unguarded (or
    # unconditionally-true guarded) arm; guarded-only partial snippets cannot fold.
    if not any(guard_always_true for _, guard_always_true, _ in parsed):
        return None
    vals = [val for _, _, val in parsed]
    if all(v is True for v in vals):
        return True
    if all(v is False for v in vals):
        return False
    return None


def _strip_closure_return_type(body: Sequence[str]) -> list[str]:
    """Strip an optional Rust closure `-> <Type>` prefix before its `{ ... }` body."""
    if not body or body[0] != "->":
        return list(body)
    if body[-1] != "}":
        return list(body)
    bdepth = 0
    open_idx = -1
    for idx in range(1, len(body)):
        tok = body[idx]
        if tok in _SPEC_OPENERS:
            if bdepth == 0 and tok == "{":
                open_idx = idx
            bdepth += 1
        elif tok in _SPEC_CLOSERS:
            bdepth -= 1
            if bdepth == 0 and idx == len(body) - 1 and open_idx > 1:
                return list(body[open_idx:])
    return list(body)


def _const_truth(texts: Sequence[str], depth: int = 0) -> bool | None:
    """Constant truth value of a boolean / `Prop` expression, or `None`.

    Three-valued folding over `true` / `false` atoms, negation, conjunction,
    disjunction, implication, `iff`, universal quantification and constant
    lambdas/closures, pure reflexive and literal comparisons, casts,
    `Prop` / `Bool` ascriptions, `if` / `match` with constant conditions or
    agreeing branches, Rust blocks, `let` / `have` bindings, and `by trivial`.
    Anything else is `None`: the arm depends on its inputs.
    """
    if depth > _MAX_SPEC_DEPTH:
        return None
    toks = list(texts)
    changed = True
    while changed and toks:
        changed = False
        while toks and toks[-1] in (";", ","):
            toks.pop()
            changed = True
        if len(toks) >= 2 and toks[0] == "(" and _wrapped(toks):
            toks = toks[1:-1]
            changed = True
        elif len(toks) >= 3 and toks[0] == "unsafe" and toks[1] == "{" and _wrapped(toks[1:]):
            toks = toks[1:]
            changed = True
        elif len(toks) >= 2 and toks[0] == "{" and _wrapped(toks):
            return _eval_rust_block_statements(toks[1:-1], depth + 1)
        if toks and toks[0] == "return":
            toks = toks[1:]
            changed = True
        stripped_let = _strip_lean_let_prefix(toks, depth + 1)
        if stripped_let is not None:
            toks = stripped_let
            changed = True
    if not toks:
        return None
    if toks[0] == "by":
        return True if toks[1:] in (
            ["trivial"], ["exact", "trivial"], ["exact", "True", ".", "intro"], ["constructor"]
        ) else None
    if toks[0] in ("∀", "forall"):
        comma_split = _split_first_top(toks[1:], {","})
        if comma_split is not None and comma_split[1]:
            body_val = _const_truth(comma_split[1], depth + 1)
            return True if body_val is True else None
        return None
    if toks[0] == "fun" or toks[0].startswith("λ"):
        if toks[1:2] == ["|"]:
            return _eval_lean_match_arms(toks[1:], depth + 1)
        arrow_split = _split_first_top(toks[1:], {"=>"})
        if arrow_split is not None and arrow_split[1]:
            body_val = _const_truth(arrow_split[1], depth + 1)
            return body_val if body_val is not None else None
        return None
    if toks[0] == "match":
        rust_match = _eval_rust_match(toks, depth + 1)
        if rust_match is not None:
            return rust_match
        with_split = _split_first_top(toks[1:], {"with"})
        if (
            with_split is not None
            and with_split[0]
            and with_split[1]
            and _is_pure_reflexive_operand(with_split[0])
        ):
            return _eval_lean_match_arms(with_split[1], depth + 1)
        return None
    closure_toks = toks[1:] if toks[0] == "move" and toks[1:2] in (["||"], ["|"]) else toks
    if closure_toks[0] == "||" and len(closure_toks) > 1:
        body_val = _const_truth(_strip_closure_return_type(closure_toks[1:]), depth + 1)
        return body_val if body_val is not None else None
    if closure_toks[0] == "|":
        bar_split = _split_first_top(closure_toks[1:], {"|"})
        if bar_split is not None and bar_split[1]:
            body_val = _const_truth(_strip_closure_return_type(bar_split[1]), depth + 1)
            return body_val if body_val is not None else None
        return None
    # Lean `if c then t else f` and complete Rust `if c { t } else { f }` extend
    # over their conditions (which may contain `||`/`&&`), so fold them before
    # splitting on binary connectives.
    if toks[0] == "if":
        if_parts = _split_lean_if(toks) or _split_rust_if(toks)
        if if_parts is not None:
            cond_toks, t_branch, f_branch = if_parts
            cond_val = _const_truth(cond_toks, depth + 1)
            if cond_val is True:
                return _const_truth(t_branch, depth + 1)
            if cond_val is False:
                return _const_truth(f_branch, depth + 1)
            first = _const_truth(t_branch, depth + 1)
            return first if first is not None and first == _const_truth(f_branch, depth + 1) else None

    parts = _split_top(toks, {"→", "->", "==>"})
    if len(parts) > 1:
        norm_hyps = [_strip_parens(p) for p in parts[:-1] if p]
        norm_conc = _strip_parens(parts[-1])
        if norm_conc and _is_pure_reflexive_operand(norm_conc) and norm_conc in norm_hyps:
            return True
        values = [_const_truth(part, depth + 1) for part in parts]
        if values[-1] is True or any(value is False for value in values[:-1]):
            return True
        if values[-1] is False and all(value is True for value in values[:-1]):
            return False
        return None
    parts = _split_top(toks, {"↔", "<->"})
    if len(parts) == 2:
        if (
            parts[0]
            and _strip_parens(parts[0]) == _strip_parens(parts[1])
            and _is_pure_reflexive_operand(parts[0])
        ):
            return True
        left, right = (_const_truth(part, depth + 1) for part in parts)
        return None if left is None or right is None else left == right
    if len(parts) > 2:
        return None
    parts = _split_top(toks, {"||", "∨", "\\/"})
    if len(parts) > 1:
        if _has_complementary_pair(parts):
            return True
        values = [_const_truth(part, depth + 1) for part in parts]
        if any(value is True for value in values):
            return True
        return False if all(value is False for value in values) else None
    parts = _split_top(toks, {"&&", "∧", "/\\"})
    if len(parts) > 1:
        if _has_complementary_pair(parts):
            return False
        values = [_const_truth(part, depth + 1) for part in parts]
        if any(value is False for value in values):
            return False
        return True if all(value is True for value in values) else None
    # Lean `¬` / `Not` bind looser than `=` (`¬ x = x` means `¬ (x = x)`), while
    # Rust `!` binds tighter than `==` / `!=` (`!c == !c` means `(!c) == (!c)`).
    if toks[0] in ("¬", "Not"):
        value = _const_truth(toks[1:], depth + 1)
        return None if value is None else not value

    for op in ("==", "=", "≠", "!=", "<=", "≤", ">=", "≥", "<", ">"):
        parts = _split_top(toks, {op})
        if len(parts) != 2 or not parts[0] or not parts[1]:
            continue
        lhs, rhs = parts
        same = (
            _strip_parens(lhs) == _strip_parens(rhs)
            and _is_pure_reflexive_operand(lhs)
        )
        lv, rv = _const_truth(lhs, depth + 1), _const_truth(rhs, depth + 1)
        ln, rn = _int_literal(_strip_parens(lhs)), _int_literal(_strip_parens(rhs))
        if op in ("==", "="):
            if same:
                return True
            if lv is not None and rv is not None:
                return lv == rv
            return ln == rn if ln is not None and rn is not None else None
        if op in ("≠", "!="):
            if same:
                return False
            if lv is not None and rv is not None:
                return lv != rv
            return ln != rn if ln is not None and rn is not None else None
        if ln is not None and rn is not None:
            return {"<=": ln <= rn, "≤": ln <= rn, ">=": ln >= rn, "≥": ln >= rn,
                    "<": ln < rn, ">": ln > rn}[op]
        if same:
            return op in ("<=", "≤", ">=", "≥")
        return None

    if toks[0] in ("!", "not"):
        value = _const_truth(toks[1:], depth + 1)
        return None if value is None else not value

    for sep, types in (("as", (["bool"],)), (":", (["Prop"], ["Bool"], ["bool"]))):
        parts = _split_top(toks, {sep})
        if len(parts) == 2 and parts[0] and parts[1] in types:
            return _const_truth(parts[0], depth + 1)
    if toks[0] == "decide" and len(toks) > 1:
        return _const_truth(toks[1:], depth + 1)
    if len(toks) == 1:
        atom = _unquote_ident(toks[0])
        return True if atom in _TRUE_ATOMS else False if atom in _FALSE_ATOMS else None
    if [_unquote_ident(t) for t in toks] in (["True", ".", "intro"], ["Bool", ".", "true"]):
        return True
    if [_unquote_ident(t) for t in toks] == ["Bool", ".", "false"]:
        return False
    return None


def _unquote_ident(text: str) -> str:
    return text[1:-1] if len(text) >= 3 and text[0] == "«" and text[-1] == "»" else text


def _ident_key(text: str) -> str:
    """Canonical identifier name, stripping Lean `«...»` or Rust `r#`."""
    if text.startswith("r#") and len(text) > 2:
        return text[2:]
    return _unquote_ident(text)


def _is_spec_word(text: str) -> bool:
    if len(text) >= 3 and text[0] == "«" and text[-1] == "»":
        return bool(text[1:-1].strip())
    if text.startswith("r#") and len(text) > 2:
        return _SPEC_WORD_RE.fullmatch(text[2:]) is not None
    return _SPEC_WORD_RE.fullmatch(text) is not None


def _is_wildcard_payload_word(word: str) -> bool:
    """A payload word that binds or ignores instead of constraining (`_`, `e`)."""
    if not _is_spec_word(word):
        return False
    if word.startswith("r#") and len(word) > 2:
        plain = word[2:]
        return plain[0] == "_" or not plain[0].isupper()
    plain = _unquote_ident(word)
    if plain in ("true", "false"):
        return False
    return plain[0] == "_" or not plain[0].isupper()


def _is_catch_all_word(word: str) -> bool:
    """A lone pattern word that matches every value (`_`, `other`)."""
    if not _is_spec_word(word):
        return False
    if word.startswith("r#") and len(word) > 2:
        plain = word[2:]
        return plain[0] == "_" or plain[0].islower()
    plain = _unquote_ident(word)
    if plain in _SPECIFIC_LOWER_PATTERNS:
        return False
    return plain[0] == "_" or plain[0].islower()


def _strip_pattern_wrappers(texts: Sequence[str]) -> list[str]:
    """Repeatedly strip outer `(...)`, `&`/`ref`/`mut`/`box`, and `ident @`."""
    toks = list(texts)
    changed = True
    while changed and toks:
        changed = False
        if toks[0] == "(" and _wrapped(toks):
            toks = toks[1:-1]
            changed = True
        elif toks[0] in _PATTERN_PREFIX_WORDS:
            toks = toks[1:]
            changed = True
        elif len(toks) >= 2 and _is_spec_word(toks[0]) and toks[1] == "@":
            toks = toks[2:]
            changed = True
    return toks


def _struct_field_patterns(inner: Sequence[str]) -> list[list[str]]:
    """Field value patterns inside `{ a: pat, b := pat, .. }`."""
    fields: list[list[str]] = []
    for part in _split_top(inner, {","}):
        if not part or part == [".."]:
            continue
        for sep in (":=", ":"):
            kv = _split_top(part, {sep})
            if len(kv) == 2 and kv[1]:
                fields.append(kv[1])
                break
        else:
            fields.append(part)
    return fields


def _payload_is_wildcard(payload: Sequence[str], depth: int = 0) -> bool:
    """Whether an error payload pattern accepts every payload value."""
    if depth > _MAX_SPEC_DEPTH:
        return False
    toks = _strip_pattern_wrappers(payload)
    parts = _split_top(toks, {"|"})
    if len(parts) > 1:
        return any(_payload_is_wildcard(part, depth + 1) for part in parts)
    parts = _split_top(toks, {","})
    if len(parts) > 1:
        return all(_payload_is_wildcard(part, depth + 1) for part in parts if part)
    toks = _split_top(toks, {":"})[0]
    toks = _strip_pattern_wrappers(toks)
    idx = 0
    while idx < len(toks):
        text = toks[idx]
        if text in _SPEC_OPENERS:
            close = idx
            nesting = 0
            while close < len(toks):
                if toks[close] in _SPEC_OPENERS:
                    nesting += 1
                elif toks[close] in _SPEC_CLOSERS:
                    nesting -= 1
                    if nesting == 0:
                        break
                close += 1
            inner = toks[idx + 1 : close]
            if text in ("(", "⟨"):
                if not _payload_is_wildcard(inner, depth + 1):
                    return False
            elif text == "{":
                field_pats = _struct_field_patterns(inner)
                if not all(_payload_is_wildcard(fp, depth + 1) for fp in field_pats):
                    return False
            elif text == "[":
                if _strip_pattern_wrappers(inner) != [".."]:
                    return False
            else:
                return False
            idx = close + 1
            continue
        if text == "@" and idx > 0:
            # Handle inline `e @ _` or `ref e @ _` inside a multi-token Lean/Rust payload.
            idx += 1
            continue
        if text != ".." and text not in _PATTERN_PREFIX_WORDS and not _is_wildcard_payload_word(text):
            return False
        idx += 1
    return True


def _skip_angle_args(toks: Sequence[str], start: int) -> int | None:
    """Index right after balanced `< ... >` generic arguments starting at `start`."""
    if start >= len(toks) or toks[start] != "<":
        return None
    depth = 0
    for idx in range(start, len(toks)):
        tok = toks[idx]
        if tok == "<":
            depth += 1
        elif tok == ">":
            depth -= 1
            if depth == 0:
                return idx + 1
    return None


def _strip_pattern_generics(toks: Sequence[str]) -> list[str]:
    """Strip Rust `::< ... >` turbofishes and leading `< ... >::` from a pattern token list."""
    out: list[str] = []
    idx = 0
    n = len(toks)
    if idx < n and toks[idx] == "<":
        after = _skip_angle_args(toks, idx)
        if after is not None and toks[after : after + 1] == ["::"]:
            idx = after + 1
    while idx < n:
        if toks[idx : idx + 2] == ["::", "<"]:
            after = _skip_angle_args(toks, idx + 1)
            if after is not None:
                idx = after
                continue
        out.append(toks[idx])
        idx += 1
    return out


def _alt_head(alt: Sequence[str]) -> tuple[str | None, bool, list[str]]:
    """`(constructor, after_dot, payload)` of one pattern alternative."""
    toks = _strip_pattern_generics(_strip_pattern_wrappers(alt))
    idx = 0
    after_dot = False
    if idx < len(toks) and toks[idx] == ".":
        after_dot = True
        idx += 1
    head: str | None = None
    while idx < len(toks) and _is_spec_word(toks[idx]):
        head = _ident_key(toks[idx])
        idx += 1
        if idx + 1 < len(toks) and toks[idx] in ("::", ".") and _is_spec_word(toks[idx + 1]):
            after_dot = toks[idx] == "."
            idx += 1
            continue
        break
    return head, after_dot, toks[idx:]


def _error_ctor(word: str, after_dot: bool) -> str | None:
    """`ErrorCtor::of`: capitalized names stand alone, lowercase ones need a dot."""
    word = _ident_key(word)
    if word == "Err":
        return "err"
    if word in ("Ub", "UB"):
        return "ub"
    if word == "Unsupported":
        return "unsupported"
    if word == "Fail":
        return "fail"
    if after_dot:
        return {"err": "err", "error": "err", "ub": "ub", "unsupported": "unsupported",
                "fail": "fail"}.get(word)
    return None


def _alt_error_matches(alt: Sequence[str], depth: int = 0) -> list[tuple[str, bool]]:
    """`(error kind, accepts every payload)` for each error pattern inside `alt`."""
    if depth > _MAX_SPEC_DEPTH:
        return []
    toks = _strip_pattern_generics(_strip_pattern_wrappers(alt))
    if not toks:
        return []
    for seps in ({"|"}, {","}):
        parts = _split_top(toks, seps)
        if len(parts) > 1:
            return [hit for part in parts for hit in _alt_error_matches(part, depth + 1)]
    if toks[0] == "{" and _wrapped(toks):
        return [
            hit
            for fp in _struct_field_patterns(toks[1:-1])
            for hit in _alt_error_matches(fp, depth + 1)
        ]
    if toks[0] in ("⟨", "[") and _wrapped(toks):
        return _alt_error_matches(toks[1:-1], depth + 1)
    head, after_dot, payload = _alt_head(toks)
    if head is None:
        return []
    ctor = _error_ctor(head, after_dot)
    if ctor is None:
        hits: list[tuple[str, bool]] = []
        idx = 0
        while idx < len(payload):
            if payload[idx] in _SPEC_OPENERS:
                close, nesting = idx, 0
                while close < len(payload):
                    if payload[close] in _SPEC_OPENERS:
                        nesting += 1
                    elif payload[close] in _SPEC_CLOSERS:
                        nesting -= 1
                        if nesting == 0:
                            break
                    close += 1
                sub = payload[idx + 1 : close]
                if payload[idx] == "{":
                    for fp in _struct_field_patterns(sub):
                        hits += _alt_error_matches(fp, depth + 1)
                else:
                    hits += _alt_error_matches(sub, depth + 1)
                idx = close + 1
            else:
                idx += 1
        if not hits and payload[:1] == ["."]:
            hits = _alt_error_matches(payload, depth + 1)
        return hits
    if ctor == "fail":
        inner = _alt_error_matches(payload, depth + 1)
        if inner:
            return [hit for hit in inner if hit[0] in ("ub", "unsupported")]
        if _payload_is_wildcard(payload):
            return [("ub", True), ("unsupported", True)]
        return []
    return [(ctor, _payload_is_wildcard(payload))]


def _alt_is_ok_ctor(alt: Sequence[str]) -> bool:
    head, after_dot, _ = _alt_head(alt)
    return head == "Ok" or (head == "ok" and after_dot)


def _alt_is_catch_all(alt: Sequence[str], depth: int = 0) -> bool:
    if depth > _MAX_SPEC_DEPTH:
        return False
    toks = _strip_pattern_wrappers(alt)
    if not toks:
        return False
    if toks[0] == "⟨" and _wrapped(toks):
        toks = toks[1:-1]
    parts = _split_top(toks, {"|"})
    if len(parts) > 1:
        return any(_alt_is_catch_all(part, depth + 1) for part in parts)
    parts = _split_top(toks, {","})
    if len(parts) > 1:
        return all(_alt_is_catch_all(part, depth + 1) for part in parts)
    toks = _strip_pattern_wrappers(toks)
    toks = _split_top(toks, {":"})[0]
    toks = _strip_pattern_wrappers(toks)
    return len(toks) == 1 and _is_catch_all_word(toks[0])


def _normalize_lean_layout_lets(
    body_toks: Sequence[tuple[str, int, int, bool]],
) -> list[str]:
    """Insert `;` for layout `let`/`have` and `(` `)` around layout `match`/`fun |` blocks."""
    out: list[str] = []
    line_first_col: dict[int, int] = {}
    for _t, ln, col, _first in body_toks:
        line_first_col.setdefault(ln, col)
    # LIFO stack of layout blocks:
    # - `{"kind": "let", "depth": d, "col": c, "ready": 0|1}`
    # - `{"kind": "match", "depth": d, "min_col": m, "arm_col": -1|c, "saw_with": 0|1, "if_count": k}`
    layout: list[dict[str, int | str]] = []
    depth = 0
    n = len(body_toks)
    for idx, (text, ln, col, first_on_line) in enumerate(body_toks):
        if first_on_line:
            closed_let = False
            while layout and layout[-1]["depth"] == depth:
                top = layout[-1]
                if top["kind"] == "match":
                    arm_c = int(top["arm_col"])
                    thresh = arm_c if arm_c != -1 else int(top["min_col"])
                    if col < thresh:
                        layout.pop()
                        out.append(")")
                        continue
                    break
                if int(top["ready"]) and col <= int(top["col"]):
                    layout.pop()
                    closed_let = True
                    continue
                break
            if closed_let and out and out[-1] not in (";", "in"):
                out.append(";")
        if text in _SPEC_OPENERS:
            depth += 1
            out.append(text)
            continue
        if text in _SPEC_CLOSERS:
            while layout and int(layout[-1]["depth"]) >= depth:
                popped = layout.pop()
                if popped["kind"] == "match":
                    out.append(")")
            depth -= 1
            out.append(text)
            continue
        if text in (";", "in"):
            while layout and layout[-1]["depth"] == depth:
                top = layout[-1]
                if top["kind"] == "match":
                    layout.pop()
                    out.append(")")
                    continue
                if int(top["ready"]):
                    layout.pop()
                    if text == "in":
                        break
                    continue
                break
            out.append(text)
            continue
        if text == "if":
            for entry in reversed(layout):
                if entry["depth"] == depth and entry["kind"] == "match":
                    entry["if_count"] = int(entry["if_count"]) + 1
                    break
        elif text == "else":
            while layout and layout[-1]["depth"] == depth and layout[-1]["kind"] == "match":
                top = layout[-1]
                if int(top["if_count"]) > 0:
                    top["if_count"] = int(top["if_count"]) - 1
                    break
                layout.pop()
                out.append(")")
        is_match_head = text == "match" or (
            (text == "fun" or text.startswith("λ"))
            and idx + 1 < n
            and body_toks[idx + 1][0] == "|"
        )
        if is_match_head:
            after_arrow = any(
                body_toks[p][0] == "=>" and body_toks[p][1] == ln
                for p in range(idx - 1, -1, -1)
                if body_toks[p][1] == ln
            )
            min_col = line_first_col[ln] + (1 if after_arrow else 0)
            out.append("(")
            layout.append(
                {
                    "kind": "match",
                    "depth": depth,
                    "min_col": min_col,
                    "arm_col": -1,
                    "saw_with": 0 if text == "match" else 1,
                    "if_count": 0,
                }
            )
            out.append(text)
            continue
        if text == "with":
            for entry in reversed(layout):
                if entry["depth"] == depth and entry["kind"] == "match" and not int(entry["saw_with"]):
                    entry["saw_with"] = 1
                    break
        elif text == "|":
            for entry in reversed(layout):
                if entry["depth"] == depth and entry["kind"] == "match":
                    if int(entry["saw_with"]) and int(entry["arm_col"]) == -1:
                        entry["arm_col"] = col
                    break
        elif text in ("let", "have") and (not out or out[-1] != "if"):
            layout.append({"kind": "let", "depth": depth, "col": col, "ready": 0})
        elif text == ":=":
            for entry in reversed(layout):
                if entry["depth"] == depth and entry["kind"] == "let" and not int(entry["ready"]):
                    entry["ready"] = 1
                    break
        out.append(text)
    while layout:
        popped = layout.pop()
        if popped["kind"] == "match":
            out.append(")")
    return out


def _has_rust_if_guard_before_brace(
    texts: Sequence[str], partner: dict[int, int], open_idx: int
) -> bool:
    """Whether `{` at `open_idx` sits inside a Rust match-arm `if` guard rather than a prior arm body."""
    g = open_idx - 1
    found_guard_if = False
    while g >= 0:
        gt = texts[g]
        if gt in _SPEC_CLOSERS:
            g = partner[g] - 1
            continue
        if gt in _SPEC_OPENERS or gt in ("=>", ";", ",", ":="):
            break
        if gt == "if":
            prev_gt = texts[g - 1] if g > 0 else ""
            if prev_gt in ("=>", "return", "=", "let", ";", "{"):
                return False
            if prev_gt != "else":
                found_guard_if = True
        g -= 1
    return found_guard_if


def _collect_spec_arms(text: str, lang: str) -> list[dict[str, object]]:
    """Every match arm and `matches!` of `text`, with its folded body truth.

    Raises `SourceLexError` when comments, literals or brackets cannot be
    delimited.
    """
    code = _strip_source_comments(text, lang, blank_literals=True)
    toks = _spec_tokens(code)
    partner = _match_delimiters(toks)
    lean = lang == "lean"
    texts = [tok[0] for tok in toks]
    count = len(texts)
    line_col: dict[int, int] = {}
    for tok in toks:
        line_col.setdefault(tok[1], tok[2])
    enclosing = [-1] * count
    stack = [-1]
    for idx, text_ in enumerate(texts):
        if text_ in _SPEC_CLOSERS:
            stack.pop()
        enclosing[idx] = stack[-1]
        if text_ in _SPEC_OPENERS:
            stack.append(idx)

    def snippet(lo: int, hi: int) -> str:
        return " ".join(texts[lo:hi])[:200]

    arms: list[dict[str, object]] = []
    decl_by_enclosing: dict[int, int] = {}
    # Per delimiter scope, stack of `[head_col, match_token_idx, first_arm_col, min_arm_col]`
    # so sequential and nested Lean `match ... with` and `fun | ...` expressions
    # never collide even when `match` sits after `=>` with indented arms below.
    lean_matches: dict[int, list[list[int]]] = {}
    for i, text_ in enumerate(texts):
        enc = enclosing[i]
        if lean and toks[i][3] and (
            text_ in _LEAN_DECL_WORDS
            or text_.startswith("#")
            or (text_ == "@" and texts[i + 1 : i + 2] == ["["])
        ):
            decl_by_enclosing[enc] = i
            lean_matches[enc] = []
        is_lean_match_head = lean and (
            text_ == "match"
            or ((text_ == "fun" or text_.startswith("λ")) and texts[i + 1 : i + 2] == ["|"])
        )
        if is_lean_match_head:
            cur_line = toks[i][1]
            after_arrow_on_line = any(
                texts[p] == "=>" and enclosing[p] == enc and toks[p][1] == cur_line
                for p in range(i - 1, -1, -1)
                if toks[p][1] == cur_line
            )
            head_col = toks[i][2] if after_arrow_on_line else line_col[cur_line]
            min_arm_col = line_col[cur_line] + (1 if after_arrow_on_line else 0)
            m_stack = lean_matches.setdefault(enc, [])
            while m_stack:
                top_head_col, top_idx, top_arm_col, _top_min = m_stack[-1]
                if top_arm_col != -1 and head_col <= top_arm_col:
                    m_stack.pop()
                elif top_arm_col == -1 and top_head_col >= head_col and toks[i][1] > toks[top_idx][1]:
                    m_stack.pop()
                else:
                    break
            m_stack.append([head_col, i, -1, min_arm_col])
        if text_ == "matches" and texts[i + 1 : i + 3] == ["!", "("]:
            close = partner[i + 2]
            first_comma = _split_first_top(texts[i + 3 : close], {","})
            if first_comma is None or not first_comma[1]:
                continue
            rhs_pat = list(first_comma[1])
            while rhs_pat and rhs_pat[-1] == ",":
                rhs_pat.pop()
            if not rhs_pat:
                continue
            negations = 0
            while i - 1 - negations >= 0 and texts[i - 1 - negations] == "!":
                negations += 1
            guard_split = _split_first_top(rhs_pat, {"if"})
            pat_tokens = rhs_pat if guard_split is None else guard_split[0]
            guard_ok = negations % 2 == 0 and (
                guard_split is None or _const_truth(guard_split[1]) is True
            )
            group = (lang, enc, decl_by_enclosing.get(enc, -1) if lean else -1, -1)
            arms.append(
                {
                    "macro": True,
                    "group": group,
                    "line": toks[i][1],
                    "column": toks[i][2],
                    "alts": [alt for alt in _split_top(pat_tokens, {"|"}) if alt],
                    "guard_ok": guard_ok,
                    "body_truth": None,
                    "text": snippet(i, close + 1),
                }
            )
            continue
        if text_ != "=>":
            continue

        # Pattern: scan left to the token that ends the previous construct.
        j = i - 1
        boundary = ""
        while j >= 0:
            prev = texts[j]
            if not lean and prev == ">" and texts[j + 1 : j + 2] == ["::"]:
                angle_depth = 1
                b = j - 1
                while b >= 0 and angle_depth > 0:
                    bt = texts[b]
                    if bt in ("=>", ";", "{", "}", "if"):
                        break
                    if bt == ">":
                        angle_depth += 1
                    elif bt == "<":
                        angle_depth -= 1
                    b -= 1
                if angle_depth == 0:
                    j = b
                    continue
            if prev in _SPEC_CLOSERS:
                if prev == "}" and not lean:
                    open_idx = partner[j]
                    before_brace = texts[open_idx - 1] if open_idx > 0 else ""
                    after_brace = texts[j + 1] if j + 1 < count else ""
                    has_block_syntax = any(t in ("=>", ";") for t in texts[open_idx + 1 : j])
                    is_struct_pat = (
                        (_is_spec_word(before_brace) or before_brace == ">")
                        and before_brace not in _RUST_NON_STRUCT_BEFORE_BRACE
                        and not has_block_syntax
                    )
                    if (
                        j == i - 1
                        or after_brace == "else"
                        or (is_struct_pat and after_brace in ("|", "if"))
                        or (
                            (after_brace in _RUST_EXPR_CONT_OPS or after_brace == "{")
                            and _has_rust_if_guard_before_brace(texts, partner, open_idx)
                        )
                    ):
                        j = open_idx - 1
                        continue
                    boundary = prev
                    break
                j = partner[j] - 1
                continue
            if prev in _SPEC_OPENERS or prev in ("=>", ";", ":=") or (prev == "," and not lean):
                boundary = prev
                break
            if lean and (prev in _LEAN_ARM_BOUNDARY_WORDS or prev.startswith("λ")):
                boundary = "fun" if prev.startswith("λ") else prev
                break
            if not lean and prev in _RUST_ARM_BOUNDARY_WORDS:
                if prev == "else" and texts[j + 1 : j + 2] == ["{"]:
                    j -= 1
                    continue
                boundary = prev
                break
            j -= 1
        pat_lo = j + 1
        if pat_lo >= i:
            continue
        if lean and boundary == "fun" and texts[pat_lo] != "|":
            continue  # `fun x => ...` binds a variable; it is not a match arm.
        pattern = texts[pat_lo:i]
        guard_ok = True
        if not lean:
            guard_split = _split_first_top(pattern, {"if"})
            if guard_split is not None:
                pattern = guard_split[0]
                guard_ok = _const_truth(guard_split[1]) is True
        segments = _split_top(pattern, {"|"})
        if boundary not in _CLEAN_ARM_STARTS:
            # What precedes the first `|` is the tail of the previous arm body.
            segments = segments[1:]
        alts = [segment for segment in segments if segment]
        if not alts:
            continue
        alt_tokens = sum(len(alt) for alt in alts) + len(alts) - 1
        alt_lo = min(max(pat_lo, pat_lo + len(pattern) - alt_tokens), i - 1)
        alt_line = toks[alt_lo][1]
        after_arrow_on_alt_line = any(
            texts[p] == "=>" and enclosing[p] == enc
            for p in range(alt_lo - 1, -1, -1)
            if toks[p][1] == alt_line
        )
        if after_arrow_on_alt_line:
            bar_col = toks[alt_lo - 1][2] if alt_lo > 0 and texts[alt_lo - 1] == "|" and toks[alt_lo - 1][1] == alt_line else toks[alt_lo][2]
            arm_col = bar_col
        else:
            arm_col = line_col[alt_line]
        match_id = -1
        if lean:
            m_stack = lean_matches.get(enc, [])
            while m_stack:
                _top_head, _top_idx, top_arm_col, top_min_arm_col = m_stack[-1]
                if top_arm_col != -1 and arm_col < top_arm_col:
                    m_stack.pop()
                elif top_arm_col == -1 and arm_col < top_min_arm_col:
                    m_stack.pop()
                else:
                    break
            if m_stack:
                if m_stack[-1][2] == -1:
                    m_stack[-1][2] = arm_col
                match_id = m_stack[-1][1]
        group = (lang, enc, decl_by_enclosing.get(enc, -1) if lean else -1, match_id)

        # Body: scan right to the token that ends this arm.
        k = i + 1
        in_lean_nested_match = False
        while k < count:
            nxt = texts[k]
            if nxt in _SPEC_OPENERS:
                close_idx = partner[k]
                if not lean and nxt == "{" and _rust_brace_ends_arm(texts, close_idx):
                    k = close_idx + 1
                    break
                k = close_idx + 1
                continue
            if nxt in _SPEC_CLOSERS or (nxt in (";", ",") and not lean):
                break
            if lean:
                if (
                    nxt == "match"
                    or ((nxt == "fun" or nxt.startswith("λ")) and texts[k + 1 : k + 2] == ["|"])
                ):
                    in_lean_nested_match = True
                if (
                    (nxt == "|" and (not in_lean_nested_match or (toks[k][3] and toks[k][2] <= arm_col)))
                    or (
                        toks[k][3]
                        and (
                            nxt in _LEAN_DECL_WORDS
                            or nxt.startswith("#")
                            or (nxt == "@" and texts[k + 1 : k + 2] == ["["])
                            or (k > i + 1 and toks[k][2] <= arm_col)
                        )
                    )
                ):
                    break
            k += 1
        body_slice = _normalize_lean_layout_lets(toks[i + 1 : k]) if lean else texts[i + 1 : k]
        arms.append(
            {
                "macro": False,
                "group": group,
                "line": toks[i][1],
                "column": toks[i][2],
                "alts": alts,
                "guard_ok": guard_ok,
                "body_truth": _const_truth(body_slice),
                "text": snippet(alt_lo, k),
            }
        )
    return arms


_LEAN_HINT_RE = re.compile(
    r":=|=>\s*\(*\s*(?:True|False|trivial)\b|\bmatch\b[^\n]*\bwith\b|\bwith\s*$"
    r"|\|\s*\.(?:[A-Za-z_]|«)|\b(?:theorem|Prop|fun)\b|/-|[∀→∧∨¬«»]",
    re.M,
)
_RUST_HINT_RE = re.compile(
    r"=>\s*[({]*\s*(?:true|false)\b|\bfn\b|\b(?:Err|Ok)\s*[(<{]|(?:\w|>)::\s*[A-Za-z_<]"
    r"|;\s*$|//|/\*|\bmatches!|\blet\s+(?:mut\s+)?[A-Za-z_][\w:<> ,()]*=(?!=)",
    re.M,
)


def _spec_languages(text: str, language: str) -> tuple[str, ...]:
    """Languages to scan `text` as: the named one, or what `auto` cannot exclude."""
    if language in ("lean", "rust"):
        return (language,)
    if language != "auto":
        raise ValueError(f"unknown language {language!r} (expected auto, lean or rust)")
    lean_stripped: str | None = None
    rust_stripped: str | None = None
    try:
        lean_stripped = _strip_source_comments(text, "lean", blank_literals=True)
    except SourceLexError:
        pass
    try:
        rust_stripped = _strip_source_comments(text, "rust", blank_literals=True)
    except SourceLexError:
        pass
    if lean_stripped is not None and rust_stripped is None:
        if (
            "/*" not in lean_stripped
            and (_LEAN_HINT_RE.search(lean_stripped) is not None or _RUST_HINT_RE.search(text) is None)
        ):
            return ("lean",)
    elif rust_stripped is not None and lean_stripped is None:
        if (
            "/-" not in rust_stripped
            and "«" not in rust_stripped
            and (_RUST_HINT_RE.search(rust_stripped) is not None or _LEAN_HINT_RE.search(text) is None)
        ):
            return ("rust",)
    lean_probe = lean_stripped if lean_stripped is not None else text
    rust_probe = rust_stripped if rust_stripped is not None else text
    lean = _LEAN_HINT_RE.search(lean_probe) is not None
    rust = _RUST_HINT_RE.search(rust_probe) is not None
    if lean != rust:
        return ("lean",) if lean else ("rust",)
    return ("lean", "rust")


def _arm_wildcard_pattern(arm: dict[str, object], ok_groups: set[object]) -> str | None:
    alts: list[list[str]] = arm["alts"]  # type: ignore[assignment]
    if not arm["guard_ok"]:
        return None
    if arm["macro"]:
        for alt in alts:
            if any(wild for _, wild in _alt_error_matches(alt)) or _alt_is_catch_all(alt):
                return "matches_any_err"
        return None
    if arm["body_truth"] is not True:
        return None
    for alt in alts:
        for kind, wild in _alt_error_matches(alt):
            if wild:
                return _WILDCARD_WIRE_ID[kind]
    if arm["group"] in ok_groups and any(_alt_is_catch_all(alt) for alt in alts):
        return "catch_all_arm_true"
    return None


def _ok_groups(arms: Sequence[dict[str, object]]) -> set[object]:
    return {
        arm["group"]
        for arm in arms
        if not arm["macro"]
        and any(_alt_is_ok_ctor(alt) for alt in arm["alts"])  # type: ignore[union-attr]
    }


def detect_postcondition_error_wildcards(
    source_text: str, *, language: str = "auto"
) -> list[ErrorWildcardFinding]:
    """Find postcondition arms that accept every error, `ub` or `unsupported` outcome.

    `language` is `"lean"`, `"rust"` or `"auto"`; `auto` scans the text as
    every language its syntax does not exclude. Comments and string literals
    are never scanned. Reported shapes (all under guard `error_branch_wildcard`):

    * `err_arm_true`: `| Err _ => True`, `| .err _ => True`, `| .error _ => True`,
      `Err(_) => true`, `Err(..) => true`, `Err(e) => true`;
    * `ub_arm_true`: `| .ub => True`, `| MirStepNode.fail .ub => True`,
      `| .fail _ => True`, `Ub => true`;
    * `unsupported_arm_true`: `| .unsupported => True`, `Unsupported => true`;
    * `matches_any_err`: `matches!(out, Ok(_) | Err(_))`;
    * `catch_all_arm_true`: `_ => true` beside an `Ok` arm of the same match;
    * `unclosed_literal_or_comment`: an unterminated comment, string or
      bracket. The scanner cannot tell code from text there and fails closed.

    An arm counts when any of its `|` alternatives is such a pattern and its
    body folds to a constant truth (`True`, `(true)`, `trivial`, `!false`,
    `True ∧ True`, `true || x == 3`, `x == x`, `{ return true; }`).
    """
    findings: list[ErrorWildcardFinding] = []
    seen: set[tuple[int, int, str]] = set()
    for lang in _spec_languages(source_text, language):
        try:
            arms = _collect_spec_arms(source_text, lang)
        except SourceLexError as exc:
            findings.append(
                ErrorWildcardFinding(
                    SPEC_WILDCARD_GUARD_ID, "unclosed_literal_or_comment", lang, 1, 1, str(exc)
                )
            )
            continue
        ok_groups = _ok_groups(arms)
        for arm in arms:
            pattern = _arm_wildcard_pattern(arm, ok_groups)
            key = (arm["line"], arm["column"], pattern or "")
            if pattern is None or key in seen:
                continue
            seen.add(key)  # type: ignore[arg-type]
            findings.append(
                ErrorWildcardFinding(
                    SPEC_WILDCARD_GUARD_ID,
                    pattern,
                    lang,
                    arm["line"],  # type: ignore[arg-type]
                    arm["column"],  # type: ignore[arg-type]
                    arm["text"],  # type: ignore[arg-type]
                )
            )
    return findings


def _probe_arms(arms: Sequence[dict[str, object]], mutant: str, lang: str) -> dict[str, object]:
    """Run the `mutant` outcome through the arms of one scanned source."""
    base: dict[str, object] = {
        "guard_id": SPEC_WILDCARD_GUARD_ID,
        "mutant": mutant,
        "language": lang,
        "pattern": None,
        "line": None,
    }
    outcome_groups = {
        arm["group"]
        for arm in arms
        if not arm["macro"]
        and any(
            _alt_is_ok_ctor(alt) or _alt_error_matches(alt)
            for alt in arm["alts"]  # type: ignore[union-attr]
        )
    }
    decided: dict[object, dict[str, object]] = {}
    constrained_line: int | None = None
    for arm in arms:
        alts: list[list[str]] = arm["alts"]  # type: ignore[assignment]
        hits = [hit for alt in alts for hit in _alt_error_matches(alt) if hit[0] == mutant]
        catch_all = any(_alt_is_catch_all(alt) for alt in alts)
        if arm["macro"]:
            if arm["guard_ok"] and (catch_all or any(wild for _, wild in hits)):
                return {
                    **base,
                    "status": "SURVIVED",
                    "pattern": "matches_any_err",
                    "line": arm["line"],
                    "detail": f"`matches!` at line {arm['line']} accepts every `{mutant}` outcome",
                }
            continue
        group = arm["group"]
        if group in decided:
            continue
        catch_all = catch_all and group in outcome_groups
        covers = catch_all or any(wild for _, wild in hits)
        if covers and arm["guard_ok"]:
            if arm["body_truth"] is True:
                return {
                    **base,
                    "status": "SURVIVED",
                    "pattern": _WILDCARD_WIRE_ID[mutant] if hits else "catch_all_arm_true",
                    "line": arm["line"],
                    "detail": (
                        f"arm at line {arm['line']} accepts every `{mutant}` outcome: "
                        f"{arm['text']}"
                    ),
                }
            decided[group] = {
                **base,
                "status": "KILLED",
                "line": arm["line"],
                "detail": (
                    f"arm at line {arm['line']} rejects or constrains the `{mutant}` "
                    f"outcome: {arm['text']}"
                ),
            }
        elif (covers or hits) and constrained_line is None:
            constrained_line = arm["line"]  # type: ignore[assignment]
    if decided:
        return next(iter(decided.values()))
    if constrained_line is not None:
        return {
            **base,
            "status": "KILLED",
            "line": constrained_line,
            "detail": (
                f"only payload-specific or guarded arms match the `{mutant}` outcome "
                f"(first at line {constrained_line})"
            ),
        }
    return {
        **base,
        "status": "UNMATCHED",
        "detail": f"no arm matches the `{mutant}` outcome",
    }


_PROBE_SEVERITY: dict[str, int] = {"SURVIVED": 3, "ERROR": 2, "KILLED": 1, "UNMATCHED": 0}


def probe_postcondition_error_wildcard_mutant(
    postcondition_source: str, mutant: str = "err", *, language: str = "auto"
) -> dict[str, object]:
    """Decide whether a postcondition kills one error mutant, without running Lean.

    The mutant is an implementation that ends in the `mutant` outcome (`"err"`:
    an error with an arbitrary payload, `"ub"`, or `"unsupported"`). In every
    match of the postcondition, the first arm that covers the whole outcome
    decides: a body that folds to constant truth lets the mutant `SURVIVE`
    (the `error_branch_wildcard` violation); any other body `KILLS` it.

    Returns `guard_id`, `mutant`, `status` (`KILLED`, `SURVIVED`, `UNMATCHED`
    when no arm mentions the outcome, `ERROR` when the source cannot be
    scanned), `pattern`, `language`, `line` and `detail`.
    """
    if mutant not in ERROR_MUTANT_KINDS:
        raise ValueError(f"unknown error mutant {mutant!r} (expected one of {ERROR_MUTANT_KINDS})")
    best: dict[str, object] | None = None
    for lang in _spec_languages(postcondition_source, language):
        try:
            result = _probe_arms(_collect_spec_arms(postcondition_source, lang), mutant, lang)
        except SourceLexError as exc:
            result = {
                "guard_id": SPEC_WILDCARD_GUARD_ID,
                "mutant": mutant,
                "language": lang,
                "pattern": "unclosed_literal_or_comment",
                "line": None,
                "status": "ERROR",
                "detail": str(exc),
            }
        if best is None or _PROBE_SEVERITY[str(result["status"])] > _PROBE_SEVERITY[str(best["status"])]:
            best = result
    assert best is not None
    return best


def verify_postcondition_kills_error_mutants(
    postcondition_source: str,
    *,
    language: str = "auto",
    mutants: Sequence[str] | None = None,
) -> dict[str, object]:
    """Self-contained mutant-kill check of one postcondition's error branches.

    Probes every error mutant (`ERROR_MUTANT_KINDS`, or exactly `mutants`) and
    runs the static wildcard scan. `ok` holds only when no mutant survives,
    nothing fails to scan, the scan reports no wildcard arm, and at least one
    mutant is killed. With explicit `mutants`, every one of them must be
    killed. A postcondition that inspects no error outcome kills nothing and
    is rejected.
    """
    selected = tuple(ERROR_MUTANT_KINDS if mutants is None else mutants)
    results = [
        probe_postcondition_error_wildcard_mutant(postcondition_source, mutant, language=language)
        for mutant in selected
    ]
    findings = detect_postcondition_error_wildcards(postcondition_source, language=language)
    tally = Counter(str(result["status"]) for result in results)
    ok = (
        not findings
        and tally["SURVIVED"] == 0
        and tally["ERROR"] == 0
        and tally["KILLED"] > 0
        and (mutants is None or tally["KILLED"] == len(selected))
    )
    return {
        "ok": ok,
        "guard_id": SPEC_WILDCARD_GUARD_ID,
        "killed": tally["KILLED"],
        "survived": tally["SURVIVED"],
        "unmatched": tally["UNMATCHED"],
        "errors": tally["ERROR"],
        "results": results,
        "findings": [asdict(finding) for finding in findings],
    }


# `(language, postcondition, mutant, expected status)`: a guarded postcondition
# kills its error mutant, and the same postcondition with the vacuous arm
# injected lets it survive. `--check-spec-wildcards` refuses to report a clean
# scan unless the probe still tells every pair apart.
_ERROR_WILDCARD_SELF_CHECK: tuple[tuple[str, str, str, str], ...] = (
    ("lean", "match out with\n  | .ok v => v = spec x\n  | .ub => False\n", "ub", "KILLED"),
    ("lean", "match out with\n  | .ok v => v = spec x\n  | .ub => True\n", "ub", "SURVIVED"),
    ("lean", "| .ok v => v = 1\n| Err e => e = .overflow\n", "err", "KILLED"),
    ("lean", "| .ok v => v = 1\n| Err _ => True\n", "err", "SURVIVED"),
    ("lean", "| .ok v => v = 1\n| .unsupported => False\n", "unsupported", "KILLED"),
    ("lean", "| .ok v => v = 1\n| .unsupported => True\n", "unsupported", "SURVIVED"),
    ("rust", "match out { Ok(v) => *v == x + 1, Err(e) => *e == E::Overflow }", "err", "KILLED"),
    ("rust", "match out { Ok(v) => *v == x + 1, Err(_) => true }", "err", "SURVIVED"),
)


def error_wildcard_probe_self_check() -> list[str]:
    """Errors of the probe's built-in kill / survive demonstrations (empty when sound)."""
    errors: list[str] = []
    for lang, source, mutant, expected in _ERROR_WILDCARD_SELF_CHECK:
        status = probe_postcondition_error_wildcard_mutant(source, mutant, language=lang)["status"]
        flagged = bool(detect_postcondition_error_wildcards(source, language=lang))
        if status != expected or flagged != (expected == "SURVIVED"):
            errors.append(
                f"wildcard probe self-check: {lang} {mutant} mutant of {source!r} is "
                f"{status} (flagged={flagged}), expected {expected}"
            )
    return errors


# Largest specification source `--check-spec-wildcards` reads.
_MAX_SPEC_SOURCE_BYTES = 8 * 1024 * 1024


def _read_regular_spec_utf8(path: Path) -> str:
    """Read a UTF-8 regular file bounded by `_MAX_SPEC_SOURCE_BYTES`, never blocking on a FIFO."""
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_CLOEXEC", 0)
    fd = os.open(path, flags)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode):
            raise OSError("not a regular file")
        if info.st_size > _MAX_SPEC_SOURCE_BYTES:
            raise OSError(f"larger than {_MAX_SPEC_SOURCE_BYTES} bytes")
        with os.fdopen(fd, "rb") as handle:
            fd = -1
            data = handle.read(_MAX_SPEC_SOURCE_BYTES + 1)
    finally:
        if fd >= 0:
            os.close(fd)
    if len(data) > _MAX_SPEC_SOURCE_BYTES:
        raise OSError(f"larger than {_MAX_SPEC_SOURCE_BYTES} bytes")
    return data.decode("utf-8")


def _empty_spec_wildcard_report(fatal_error: str | None = None) -> dict[str, object]:
    return {
        "ok": False,
        "fatal_error": fatal_error,
        "mode": "check-spec-wildcards",
        "guard_id": SPEC_WILDCARD_GUARD_ID,
        "checked": 0,
        "findings": [],
        "errors": [],
    }


def check_spec_wildcard_paths(paths: Sequence[Path]) -> dict[str, object]:
    """Scan specification files for error-branch wildcard arms.

    `.lean` files are scanned as Lean, `.rs` files as Rust, anything else as
    `auto`. `ok` holds only when every path was read as a UTF-8 regular file
    and scanned with no finding, and the probe's self-check passes.
    """
    findings: list[dict[str, object]] = []
    errors: list[dict[str, object]] = [
        {"path": None, "error": message} for message in error_wildcard_probe_self_check()
    ]
    checked = 0
    for path in paths:
        try:
            text = _read_regular_spec_utf8(path)
        except (OSError, UnicodeDecodeError) as exc:
            errors.append({"path": str(path), "error": f"cannot read: {exc}"})
            continue
        language = {".lean": "lean", ".rs": "rust"}.get(path.suffix, "auto")
        checked += 1
        findings.extend(
            {"path": str(path), **asdict(finding)}
            for finding in detect_postcondition_error_wildcards(text, language=language)
        )
    return {
        "ok": not findings and not errors and checked == len(paths) and checked > 0,
        "fatal_error": None,
        "mode": "check-spec-wildcards",
        "guard_id": SPEC_WILDCARD_GUARD_ID,
        "checked": checked,
        "findings": findings,
        "errors": errors,
    }


def validate_catalog_invariants(
    anneal_root: Path,
    *,
    require_rust_taxonomy: bool | None = None,
    require_lean_taxonomy: bool | None = None,
) -> list[str]:
    """Validate static catalog and topological invariants without invoking Lean.

    Returns a list of error strings (empty when all invariants hold).

    Besides the fixture and topology checks, the catalog must agree with the
    canonical property taxonomy: every guard names one of the 12
    `PropertyClass` identifiers, `PROPERTY_CLASS_DISPOSITIONS` accounts for all
    12, and the identifiers match the live `property_registry.rs` and
    `SpecBoundaryGuards.lean` (see `validate_property_taxonomy` for when a
    missing source file is an error and what `require_rust_taxonomy` does).
    """
    errors: list[str] = []
    errors.extend(
        validate_property_taxonomy(
            anneal_root,
            require_rust_taxonomy=require_rust_taxonomy,
            require_lean_taxonomy=require_lean_taxonomy,
        )
    )
    errors.extend(_guard_property_class_errors())
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
    # theorem may evaluate, and only as the LHS head of a guard whose rebuild
    # closure includes the defining module.
    semantics_fns_by_module: dict[str, set[str]] = {}
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
            mod_fns = _trusted_function_names(mod_text)
            semantics_fns_by_module[mod] = mod_fns
            semantics_fn_names |= mod_fns
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

        target_fn_names: set[str] = set()
        for mod in rebuild_mods:
            target_fn_names |= semantics_fns_by_module.get(mod, set())

        for kind, src_text, thm_name in (
            ("sanity", guard.sanity_source, guard.sanity_theorem_name),
            ("refute", guard.refute_source, guard.theorem_name),
        ):
            for shape_error in _fixture_shape_errors(
                kind, src_text, thm_name, reserved_names=reserved_names
            ):
                errors.append(f"{guard.guard_id}: {shape_error}")
            for stmt_error in _fixture_statement_errors(
                kind,
                src_text,
                thm_name,
                semantics_fn_names=semantics_fn_names,
                target_fn_names=target_fn_names,
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
    try:
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
    except BaseException:
        _kill_process_group(proc)
        if proc.poll() is None:
            try:
                with proc:
                    proc.communicate(timeout=5)
            except BaseException:
                pass
        raise
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
        # A result carries the class of its cataloged guard, whoever built it.
        results.extend(
            GuardResult(**{**asdict(by_id[g.guard_id]), "property_class": g.property_class})
            for g in selected_guards
        )

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
        "property_class_summary": property_class_summary(selected_guards, results),
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
        "property_class_summary": property_class_summary(()),
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
        try:
            for name in ("SIGTERM", "SIGHUP"):
                signum = getattr(signal, name, None)
                if signum is not None and signal.getsignal(signum) is signal.SIG_DFL:
                    # Recorded BEFORE it is installed: the signal may arrive
                    # (and `_raise` may fire) the instant the handler is in
                    # place, and it must still be restored on the way out.
                    taken_over.append(signum)
                    signal.signal(signum, _raise)
        except ValueError:
            # Not the main thread: signal handling belongs to the embedding program.
            pass
        yield
    finally:
        for signum in taken_over:
            try:
                signal.signal(signum, signal.SIG_DFL)
            except ValueError:
                pass


def _write_json_out(path: Path, report: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


def _run_spec_wildcard_check(
    paths: Sequence[Path], *, emit_json: bool, json_out: Path | None
) -> int:
    """`--check-spec-wildcards`: exit `0` when clean, `1` on a finding or bad path."""
    if json_out is not None:
        # Same fail-closed sink as a guard run: a stale pass never survives.
        pending = _empty_spec_wildcard_report("run did not complete")
        try:
            _write_json_out(json_out, pending)
        except OSError as exc:
            msg = f"cannot write {json_out}: {exc}"
            print(f"ERROR: {msg}", file=sys.stderr)
            if emit_json:
                print(json.dumps(_empty_spec_wildcard_report(msg), indent=2))
            return 1
    report = check_spec_wildcard_paths(paths)
    exit_code = 0 if report["ok"] else 1
    if json_out is not None:
        try:
            _write_json_out(json_out, report)
        except OSError as exc:
            msg = f"cannot write {json_out}: {exc}"
            print(f"ERROR: {msg}", file=sys.stderr)
            report["ok"] = False
            report["fatal_error"] = msg
            exit_code = 1
    if emit_json:
        print(json.dumps(report, indent=2))
        return exit_code
    for finding in report["findings"]:  # type: ignore[union-attr]
        print(
            f"{finding['path']}:{finding['line']}:{finding['column']}: "
            f"{finding['guard_id']} [{finding['pattern']}] {finding['arm']}"
        )
    for error in report["errors"]:  # type: ignore[union-attr]
        where = f"{error['path']}: " if error["path"] else ""
        print(f"ERROR: {where}{error['error']}", file=sys.stderr)
    print(
        f"Spec wildcard check: {report['checked']} file(s) scanned, "
        f"{len(report['findings'])} finding(s), "  # type: ignore[arg-type]
        f"{len(report['errors'])} error(s)"  # type: ignore[arg-type]
    )
    return exit_code


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
    parser.add_argument(
        "--taxonomy-json",
        action="store_true",
        help=(
            "Print the canonical PropertyTaxonomyManifest JSON after checking it "
            "against property_registry.rs and SpecBoundaryGuards.lean, and exit."
        ),
    )
    parser.add_argument(
        "--check-spec-wildcards",
        nargs="+",
        type=Path,
        default=None,
        metavar="PATH",
        help=(
            "Scan Lean or Rust specification sources for vacuous error-branch "
            "postcondition arms and exit 0 when clean, 1 otherwise."
        ),
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
    run_selection = args.list or args.quick or args.all or bool(args.guards)
    if args.taxonomy_json and (
        run_selection or args.json_out is not None or args.check_spec_wildcards is not None
    ):
        parser.error(
            "--taxonomy-json cannot be combined with --list, --quick, --all, --guard, "
            "--json-out or --check-spec-wildcards"
        )
    if args.check_spec_wildcards is not None and run_selection:
        parser.error(
            "--check-spec-wildcards cannot be combined with --list, --quick, --all or --guard"
        )

    # Lean always runs with `cwd=<anneal_root>`; relative paths must not shift.
    anneal_root = Path(os.path.abspath(args.anneal_root))
    mode_label = "quick" if args.quick else ("guard" if args.guards else "all")

    if args.taxonomy_json:
        taxonomy_errors = validate_property_taxonomy(
            anneal_root, require_rust_taxonomy=True, require_lean_taxonomy=True
        )
        if taxonomy_errors:
            for err in taxonomy_errors:
                print(f"ERROR: {err}", file=sys.stderr)
            return 1
        sys.stdout.write(render_property_taxonomy_manifest())
        return 0

    if args.check_spec_wildcards is not None:
        return _run_spec_wildcard_check(
            args.check_spec_wildcards, emit_json=args.emit_json, json_out=args.json_out
        )

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
                        "property_class": g.property_class,
                        "target_file": g.target_file,
                        "target_module": g.target_module,
                        "quick": g.quick,
                        "description": g.description,
                        "theorem_name": g.theorem_name,
                        "sanity_theorem_name": g.sanity_theorem_name,
                    }
                    for g in selected
                ],
                "property_classes": list(CANONICAL_PROPERTY_CLASSES),
                "spec_boundary_guards": list(CANONICAL_SPEC_BOUNDARY_GUARDS),
                "property_class_summary": property_class_summary(selected),
            }
            print(json.dumps(payload, indent=2))
        else:
            for g in selected:
                tag = "quick" if g.quick else "full "
                print(f"{tag}  {g.guard_id:42s} {g.target_file}")
            summary_rows = property_class_summary(selected)
            print(
                "Property classes with selected guards: "
                + ", ".join(
                    f"{row['property_class']}={row['selected']}"
                    for row in summary_rows
                    if row["selected"]
                )
            )
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
            unwritable, args.json_out = args.json_out, None
            return _fail(f"cannot write {unwritable}: {exc}")

    if args.emit_json:
        print(json.dumps(report, indent=2))
    else:
        print(_format_summary(report))

    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
