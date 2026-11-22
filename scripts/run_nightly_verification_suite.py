#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Anneal Nightly Verification Suite, Correspondence Tracker & 10,000-Foot Completeness Census.

Executes repository verification suites (wrapped in `anneal-lean-run` for Lean/Lake
invocations), harvests `MiniRustSpec`, `Correspondence`, and `LeanMiriSpec`
correspondence scorecards, computes Stage A (syntactic authority denominators)
and Stage B (empirical real-world Rust corpus verifiability blended with
sub-function partial coverage and marginal-unlock blocker rankings), and writes
dashboard-ready JSON (`LATEST_DASHBOARD_STATE.json`, `completeness_history.jsonl`,
`correspondence_ratchet.json`) and human-readable Markdown (`LATEST_SUITE_REPORT.md`)
reports.

Profiles (`--profile`):
  census-only  Fast (seconds) static/ledger completeness & correspondence census plus
               lightweight offline lints (`correspondence_gaps.toml` / `minirust.lock.toml` /
               `check_semantic_sources.py`). Zero heavy Cargo/Lake builds.
  quick        Runs `census-only` plus a pre-flight `lake build Trusted Anneal MiniRust`,
               `check_trusted.py --fast`, Python test suites
               (`ci/`, `scripts/`, `tools/anneal-lsp/`), `anneal-minirust-gen --check`,
               `cargo anneal correspondence-bugs lint`, `minirust-sync verify-lock`,
               and `cargo test --workspace --lib --bins --locked`.
  nightly      Runs `quick` plus `check_trusted.py --self-test`, a `lake build +<Module>`
               of every workspace module imported by the standalone `tests/mir/*` Lean
               suites, those suites, `lake build Correspondence`, `lake build MiniRustSpec`,
               `lake --dir examples build LeanMiriSpec`, domain crate integration tests,
               `cargo-anneal` end-to-end suites, and real-world Fuchsia/Fxfs example
               crate verifications.

Step environment: every step runs with `LAKE_ARTIFACT_CACHE=true` and
`LAKE_RESTORE_ARTIFACTS=true`, and `lake_build_lean_miri_spec` with `LEAN_NUM_THREADS=1`
when its effective RAM ceiling is below 10 GiB. Before their first step, `quick` and
`nightly` remove stale Lean build artifacts from `.lake/build/lib/lean/` and
`examples/.lake/build/lib/lean/` (`clean_stale_oleans`) and report them on stderr.

Exit codes:
  0  All executed suite steps passed and zero active test/build regressions occurred.
  1  Internal script or configuration error.
  2  One or more executed verification/test steps failed (regression detected), or the
     flip-direction witness polarity audit (`--flip-baseline-root` /
     `--flip-baseline-ref`) found a violation.
"""

from __future__ import annotations

import argparse
from collections.abc import Mapping
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import struct
import subprocess
import sys
import tempfile
import time
import tomllib
from typing import Any


EXIT_SUCCESS = 0
EXIT_INTERNAL_ERROR = 1
EXIT_SUITE_REGRESSION = 2

SCHEMA_VERSION = 1
DEFAULT_BLEND_ALPHA = 0.5


def _atomic_write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = path.parent / f".tmp_{os.getpid()}_{path.name}"
    try:
        tmp_path.write_text(content, encoding="utf-8")
        os.replace(tmp_path, path)
    except BaseException:
        try:
            tmp_path.unlink(missing_ok=True)
        except OSError:
            pass
        raise


def _git_head_sha(repo_root: Path, ref: str = "HEAD") -> str:
    try:
        proc = subprocess.run(
            ["git", "-C", str(repo_root), "rev-parse", ref],
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
        if proc.returncode == 0:
            return proc.stdout.strip()
    except OSError:
        pass
    return "unknown"


# ---------------------------------------------------------------------------
# Stage A: Syntactic & Authority Completeness Denominators
# ---------------------------------------------------------------------------

# One entry per constructor of the corresponding `inductive` in `file`, using the exact Lean
# constructor names: `scripts/audit_mir_coverage_matrix.py --check` requires exact set equality with
# the parsed `Trusted.Rustc.V2026_06_01.MirAst` inductives (94 constructors). rustc variants that
# `trusted/rustc-capture` lowers onto an existing constructor are not separate entries (like
# `FakeRead` -> `.placeMention`, `AggregateKind::CoroutineClosure` -> `.closure`).
MIR_AST_CATEGORIES: list[dict[str, Any]] = [
    {
        "category": "StatementKind",
        "file": "trusted/lean/Trusted/Rustc/V2026_06_01/MirAst/Statements.lean",
        "variants": [
            ("assign", "proved_corresponding"),
            ("setDiscriminant", "proved_corresponding"),
            ("deinit", "proved_corresponding"),
            ("storageLive", "proved_corresponding"),
            ("storageDead", "proved_corresponding"),
            ("retag", "proved_corresponding"),
            ("placeMention", "proved_corresponding"),
            ("intrinsic", "proved_corresponding"),
            ("nop", "proved_corresponding"),
            ("coverage", "supported_and_tested"),
            # Trusted / MiniRust / LeanMiri correspondence: tests/mir/MirUntestedVariantCorrespondenceTests.lean
            ("constEvalCounter", "proved_corresponding"),
            ("backwardIncompatibleDropHint", "unsupported_fail_closed"),
        ],
    },
    {
        "category": "NonDivergingIntrinsic",
        "file": "trusted/lean/Trusted/Rustc/V2026_06_01/MirAst/Statements.lean",
        "variants": [
            ("assume", "proved_corresponding"),
            ("copyNonOverlapping", "proved_corresponding"),
        ],
    },
    {
        "category": "TerminatorKind",
        "file": "trusted/lean/Trusted/Rustc/V2026_06_01/MirAst/Terminators.lean",
        "variants": [
            ("goto", "proved_corresponding"),
            ("switchInt", "proved_corresponding"),
            ("return_", "proved_corresponding"),
            ("unreachable", "proved_corresponding"),
            ("assert", "proved_corresponding"),
            ("call", "proved_corresponding"),
            ("drop", "supported_and_tested"),
            # Trusted / MiniRust / LeanMiri correspondence: tests/mir/MirUntestedVariantCorrespondenceTests.lean
            ("tailCall", "proved_corresponding"),
            ("unwindResume", "unsupported_fail_closed"),
            ("unwindTerminate", "unsupported_fail_closed"),
            ("inlineAsm", "unsupported_fail_closed"),
        ],
    },
    {
        "category": "ProjectionElem",
        "file": "trusted/lean/Trusted/Rustc/V2026_06_01/MirAst/Places.lean",
        "variants": [
            ("deref", "proved_corresponding"),
            ("field", "proved_corresponding"),
            ("index", "proved_corresponding"),
            ("constantIndex", "proved_corresponding"),
            ("subslice", "proved_corresponding"),
            ("downcast", "proved_corresponding"),
            # Phase boundary, not a gap: rustc's validator rejects OpaqueCast at MirPhase::Runtime (after PostAnalysisNormalize) and both vendored Miri paths throw "OpaqueCast after borrowck" (Projection.lean `.invariant` / PlaceDynamic.lean `.invalidProgram`), while Trusted treats it as a value-transparent retype.
            ("opaqueCast", "supported_and_tested"),
            ("unwrapUnsafeBinder", "unsupported_fail_closed"),
        ],
    },
    {
        "category": "Rvalue",
        "file": "trusted/lean/Trusted/Rustc/V2026_06_01/MirAst/Rvalues.lean",
        "variants": [
            ("use", "proved_corresponding"),
            ("repeat", "proved_corresponding"),
            ("ref", "proved_corresponding"),
            ("rawPtr", "proved_corresponding"),
            ("len", "proved_corresponding"),
            ("cast", "proved_corresponding"),
            ("binaryOp", "proved_corresponding"),
            ("unaryOp", "proved_corresponding"),
            ("discriminant", "proved_corresponding"),
            ("aggregate", "proved_corresponding"),
            ("copyForDeref", "proved_corresponding"),
            # Ground semantics in Trusted (`evalNullaryOp`, `evalShallowInitBox`,
            # `evalWrapUnsafeBinder` in `MirSemantics/Places.lean`), with two-sided
            # equalities and ground round-trip witnesses in Anneal.Mir.PlaceAndRvalue
            # and Anneal.Mir.AdtAndControl.
            ("nullaryOp", "supported_and_tested"),
            ("shallowInitBox", "supported_and_tested"),
            ("wrapUnsafeBinder", "supported_and_tested"),
            ("threadLocalRef", "unsupported_fail_closed"),
        ],
    },
    {
        "category": "BinOp",
        "file": "trusted/lean/Trusted/Rustc/V2026_06_01/MirAst/Rvalues.lean",
        "variants": [
            ("add", "proved_corresponding"),
            ("addUnchecked", "proved_corresponding"),
            ("addWithOverflow", "proved_corresponding"),
            ("sub", "proved_corresponding"),
            ("subUnchecked", "proved_corresponding"),
            ("subWithOverflow", "proved_corresponding"),
            ("mul", "proved_corresponding"),
            ("mulUnchecked", "proved_corresponding"),
            ("mulWithOverflow", "proved_corresponding"),
            ("div", "proved_corresponding"),
            ("rem", "proved_corresponding"),
            ("bitXor", "proved_corresponding"),
            ("bitAnd", "proved_corresponding"),
            ("bitOr", "proved_corresponding"),
            ("shl", "proved_corresponding"),
            ("shlUnchecked", "proved_corresponding"),
            ("shr", "proved_corresponding"),
            ("shrUnchecked", "proved_corresponding"),
            ("eq", "proved_corresponding"),
            ("lt", "proved_corresponding"),
            ("le", "proved_corresponding"),
            ("ne", "proved_corresponding"),
            ("ge", "proved_corresponding"),
            ("gt", "proved_corresponding"),
            ("cmp", "proved_corresponding"),
            ("offset", "proved_corresponding"),
        ],
    },
    {
        "category": "UnOp",
        "file": "trusted/lean/Trusted/Rustc/V2026_06_01/MirAst/Rvalues.lean",
        "variants": [
            ("not", "proved_corresponding"),
            ("neg", "proved_corresponding"),
            ("ptrMetadata", "proved_corresponding"),
        ],
    },
    {
        "category": "CastKind",
        "file": "trusted/lean/Trusted/Rustc/V2026_06_01/MirAst/Rvalues.lean",
        "variants": [
            ("intToInt", "proved_corresponding"),
            ("ptrToPtr", "proved_corresponding"),
            ("transmute", "proved_corresponding"),
            ("pointerExposeProvenance", "proved_corresponding"),
            ("pointerWithExposedProvenance", "proved_corresponding"),
            ("pointerCoercion", "supported_and_tested"),
            ("subtype", "supported_and_tested"),
            # Float casts: evidence is the kernel-checked IEEE-754 reference-model
            # agreement in `theory/Anneal/Mir/IeeeFloatCast.lean` (ties-to-even,
            # saturating float->int, NaN quietization, subnormal single rounding) plus
            # `tests/mir/CastStage1Tests.lean`; there is not yet a MiniRustSpec /
            # LeanMiriSpec step-simulation theorem for `FloatToInt`/`IntToFloat`/
            # `FloatToFloat` (LeanMiriSpec only translates the cast kinds).
            ("floatToInt", "proved_corresponding"),
            ("intToFloat", "proved_corresponding"),
            ("floatToFloat", "proved_corresponding"),
            ("fnPtrToPtr", "unsupported_fail_closed"),
        ],
    },
    {
        "category": "AggregateKind",
        "file": "trusted/lean/Trusted/Rustc/V2026_06_01/MirAst/Rvalues.lean",
        "variants": [
            ("array", "proved_corresponding"),
            ("tuple", "proved_corresponding"),
            ("adt", "proved_corresponding"),
            ("rawPtr", "supported_and_tested"),
            # Also covers rustc's `AggregateKind::CoroutineClosure`, which `mir_lower.rs` lowers to `.closure`.
            ("closure", "unsupported_fail_closed"),
            ("coroutine", "unsupported_fail_closed"),
        ],
    },
]


def compute_stage_a_syntactic_completeness(repo_root: Path) -> dict[str, Any]:
    """Compute Stage A syntactic construct and authority completeness metrics."""
    # 1. Anneal MIR AST surface
    totals = {
        "proved_corresponding": 0,
        "supported_and_tested": 0,
        "supported_untested": 0,
        "unsupported_fail_closed": 0,
    }
    by_category: dict[str, dict[str, Any]] = {}
    unsupported_variants: list[str] = []
    untested_variants: list[str] = []

    for cat_entry in MIR_AST_CATEGORIES:
        cat_name = cat_entry["category"]
        cat_counts = {
            "total": len(cat_entry["variants"]),
            "proved_corresponding": 0,
            "supported_and_tested": 0,
            "supported_untested": 0,
            "unsupported_fail_closed": 0,
        }
        for v_name, status in cat_entry["variants"]:
            cat_counts[status] += 1
            totals[status] += 1
            if status == "unsupported_fail_closed":
                unsupported_variants.append(f"{cat_name}.{v_name}")
            elif status == "supported_untested":
                untested_variants.append(f"{cat_name}.{v_name}")
        by_category[cat_name] = cat_counts

    total_variants = sum(totals.values())
    supported_total = (
        totals["proved_corresponding"]
        + totals["supported_and_tested"]
        + totals["supported_untested"]
    )

    # Check Stage-1 lowered `LIntrinsicOp` count in `theory/Anneal/Mir/AdtAndControl.lean`
    adt_path = repo_root / "theory/Anneal/Mir/AdtAndControl.lean"
    lintrinsic_variants = 0
    if adt_path.is_file():
        adt_text = adt_path.read_text(encoding="utf-8", errors="replace")
        m = re.search(
            r"inductive\s+LIntrinsicOp\b(.*?)(?:deriving|\nend\b|\n/--|\ndef\s)",
            adt_text,
            re.DOTALL,
        )
        if m:
            lintrinsic_variants = len(re.findall(r"^\s*\|\s*[a-zA-Z0-9_]+", m.group(1), re.MULTILINE))

    # 2. MiniRust authority completeness
    mr_cov_path = repo_root / "minirust/coverage.json"
    mr_cov: dict[str, Any] = {}
    if mr_cov_path.is_file():
        try:
            mr_cov = json.loads(mr_cov_path.read_text(encoding="utf-8"))
        except ValueError:
            mr_cov = {}

    ast_structural = mr_cov.get("ast_nodes", {}).get("structural", 0)
    ast_opaque = mr_cov.get("ast_nodes", {}).get("opaque", 0)
    ast_total = ast_structural + ast_opaque
    ast_pct = round((100.0 * ast_structural / ast_total), 4) if ast_total > 0 else 0.0
    shallow_translated = mr_cov.get("shallow_types", {}).get("translated", 0)
    shallow_candidates = mr_cov.get("shallow_types", {}).get("candidates", 0)

    anchors_path = repo_root / "minirust/lean/MiniRustSpec/Anchors.lean"
    anchored_items = 0
    if anchors_path.is_file():
        anchors_text = anchors_path.read_text(encoding="utf-8", errors="replace")
        anchored_items = len(re.findall(r'tokenSha256\s*:=\s*"[0-9a-f]{64}"', anchors_text))

    interp_path = repo_root / "minirust/lean/MiniRustSpec/Interp.lean"
    interp_unsupported_branches = 0
    if interp_path.is_file():
        interp_text = interp_path.read_text(encoding="utf-8", errors="replace")
        interp_unsupported_branches = len(re.findall(r"\.unsupported\b", interp_text))

    mr_audit_path = repo_root / "minirust/lean/MiniRustSpec/Audit.lean"
    mr_audited_decls = 0
    if mr_audit_path.is_file():
        mr_audit_text = mr_audit_path.read_text(encoding="utf-8", errors="replace")
        for block in re.findall(
            r"#(?:assert_standard_axioms|check_theorem_deps(?:\s+\"[^\"]+\")?)\s+((?:[A-Za-z0-9_.'`]+\s*)+)",
            mr_audit_text,
        ):
            tokens = [
                t
                for t in block.split()
                if t and not t.startswith("#") and t not in ("open", "in", "end", "namespace")
            ]
            mr_audited_decls += len(tokens)

    # 3. lean-miri authority completeness
    lm_pin_path = repo_root / "lean-miri/UPSTREAM_PIN.json"
    lm_pin: dict[str, Any] = {}
    if lm_pin_path.is_file():
        try:
            lm_pin = json.loads(lm_pin_path.read_text(encoding="utf-8"))
        except ValueError:
            lm_pin = {}

    vendored_miri_files = lm_pin.get("vendor_tree", {}).get("file_count", 0)
    lm_corr_dir = repo_root / "lean-miri/lean/LeanMiriSpec/Correspondence"
    sim_milestones: list[str] = []
    if lm_corr_dir.is_dir():
        for p in sorted(lm_corr_dir.glob("SimLM*.lean")):
            m = re.match(r"SimLM(\d+)_(\d+)\.lean$", p.name)
            if m:
                sim_milestones.append(f"LM-{m.group(1)}.{m.group(2)}")
        if (lm_corr_dir / "Simulation.lean").is_file():
            sim_milestones.insert(0, "LM-1.1")

    lm_audit_path = repo_root / "lean-miri/lean/LeanMiriSpec/Audit.lean"
    lm_example_pins = 0
    lm_audited_decls = 0
    if lm_audit_path.is_file():
        lm_audit_text = lm_audit_path.read_text(encoding="utf-8", errors="replace")
        lm_example_pins = len(re.findall(r"^\s*example\b", lm_audit_text, re.MULTILINE))
        for block in re.findall(
            r"#assert_standard_axioms\s+((?:[A-Za-z0-9_.'`]+\s*)+)",
            lm_audit_text,
        ):
            tokens = [
                t
                for t in block.split()
                if t and not t.startswith("#") and t not in ("open", "in", "end", "namespace", "--")
            ]
            lm_audited_decls += len(tokens)

    # Partition vendored Miri files by subsystem
    miri_vendor_dir = repo_root / "lean-miri/vendor/Miri"
    miri_subsystems: dict[str, dict[str, Any]] = {
        "ABI_and_MIR_Syntax": {"files": 0, "status": "modeled_and_translated"},
        "Memory_and_TreeBorrows": {"files": 0, "status": "proved_corresponding"},
        "Interpreter_Core": {"files": 0, "status": "proved_corresponding_with_hooks"},
        "Input_and_Startup_World": {"files": 0, "status": "harness_instantiated"},
        "Concurrency_and_WeakMemory": {"files": 0, "status": "out_of_scope_single_thread"},
        "OS_Foreign_and_Float_Shims": {"files": 0, "status": "out_of_scope_no_std_core"},
    }
    if miri_vendor_dir.is_dir():
        for p in miri_vendor_dir.rglob("*.lean"):
            rel = p.relative_to(miri_vendor_dir).as_posix()
            if rel.startswith(("ABI", "MIR", "DataStructures")):
                miri_subsystems["ABI_and_MIR_Syntax"]["files"] += 1
            elif rel.startswith(("Memory", "TreeBorrows")):
                miri_subsystems["Memory_and_TreeBorrows"]["files"] += 1
            elif rel.startswith("Concurrency"):
                miri_subsystems["Concurrency_and_WeakMemory"]["files"] += 1
            elif rel.startswith("Input"):
                miri_subsystems["Input_and_Startup_World"]["files"] += 1
            elif any(
                k in rel
                for k in (
                    "Unix",
                    "Windows",
                    "MacOs",
                    "Linux",
                    "Android",
                    "FreeBsd",
                    "NetBsd",
                    "Solarish",
                    "Socket",
                    "Epoll",
                    "EventFd",
                    "Pthread",
                    "Chrono",
                    "Math/Float",
                    "Native/",
                )
            ):
                miri_subsystems["OS_Foreign_and_Float_Shims"]["files"] += 1
            else:
                miri_subsystems["Interpreter_Core"]["files"] += 1

    return {
        "anneal_mir_ast": {
            "total_variants": total_variants,
            "supported_total": supported_total,
            "supported_pct": round(100.0 * supported_total / total_variants, 2)
            if total_variants
            else 0.0,
            "proved_corresponding": totals["proved_corresponding"],
            "proved_corresponding_pct": round(
                100.0 * totals["proved_corresponding"] / total_variants, 2
            )
            if total_variants
            else 0.0,
            "supported_and_tested": totals["supported_and_tested"],
            "supported_untested": totals["supported_untested"],
            "unsupported_fail_closed": totals["unsupported_fail_closed"],
            "unsupported_variants": unsupported_variants,
            "untested_variants": untested_variants,
            "stage1_lowered_lintrinsic_op_variants": lintrinsic_variants,
            "by_category": by_category,
        },
        "minirust_authority": {
            "upstream_commit": mr_cov.get("upstream_commit", "unknown"),
            "spec_files": mr_cov.get("spec_files", 0),
            "rust_blocks": mr_cov.get("rust_blocks", 0),
            "spec_items_total": sum(mr_cov.get("items_by_kind", {}).values()),
            "spec_fns_total": mr_cov.get("functions_and_methods", 0),
            "ast_nodes_structural": ast_structural,
            "ast_nodes_opaque": ast_opaque,
            "ast_nodes_structural_pct": ast_pct,
            "shallow_types_translated": shallow_translated,
            "shallow_types_candidates": shallow_candidates,
            "shallow_types_pct": round(100.0 * shallow_translated / shallow_candidates, 2)
            if shallow_candidates
            else 0.0,
            "interp_anchored_items": anchored_items,
            "interp_anchored_pct_of_items": round(
                100.0 * anchored_items / max(1, sum(mr_cov.get("items_by_kind", {}).values())),
                2,
            ),
            "interp_unsupported_branches": interp_unsupported_branches,
            "audited_declarations": mr_audited_decls,
            "lintrinsic_ops_classified": {
                "total": lintrinsic_variants,
                "covered": lintrinsic_variants,
            },
        },
        "lean_miri_authority": {
            "upstream_commit": lm_pin.get("commit", "unknown"),
            "vendored_miri_files": vendored_miri_files,
            "milestones_merged": sim_milestones,
            "audited_declarations": lm_audited_decls,
            "statement_pin_examples": lm_example_pins,
            "subsystems": miri_subsystems,
        },
    }


# ---------------------------------------------------------------------------
# Stage B: Empirical Real-World Rust Corpus Completeness & Blended Coverage
# ---------------------------------------------------------------------------

# Construct patterns scanned on Rust function bodies to identify unsupported/blocker
# features across the 4 layers (`trusted_mir`, `anneal_proof_lifters`,
# `minirust_correspondence`, `lean_miri_correspondence`).
#
# Slice wide pointers vs. unsized DSTs (formerly one `wide_ptr_or_unsized_dst` blocker):
# Episode 1 lifted `[T]` wide pointers (data pointer + element-count metadata) into the proof
# lifters (`theory/Anneal/SepLogicLenses.lean`, section `SliceWidePtrLenses`: `WidePtrVal`,
# `SliceTypedAt`, `ActiveTypedSliceBorrow`, `ActiveTypedSliceMutBorrow`, `SliceTypedAt.splitAt`).
# Raw slice construction (`slice::from_raw_parts(_mut)`, `ptr::slice_from_raw_parts(_mut)`,
# `NonNull::slice_from_raw_parts`) therefore no longer blocks `anneal_proof_lifters`, but its
# MiniRust / LeanMiri correspondence is unproved, so it keeps blocking those two layers (as
# `slice_from_raw_parts` did before; `slice::from_raw_parts`, the same construction behind a
# reference, is now recognized too). Plain slice operations (`.len()`, `split_at(_mut)`,
# indexing, `PtrMetadata` of a `&[T]`) never matched a blocker and still do not. Generic
# unsized DSTs stay unlifted: `?Sized`
# bounds, `size_of_val(_raw)` / `align_of_val(_raw)` / `Layout::for_value(_raw)`, `Pointee` /
# `DynMetadata` / `ptr::metadata` / zerocopy's `PointerMetadata`, and the generic
# `ptr::from_raw_parts(_mut)` / `NonNull::from_raw_parts` / `<*const T>::from_raw_parts`
# constructors (anchored on `ptr::` / `NonNull::` / `>::`, so `slice::from_raw_parts` and
# `slice_from_raw_parts` never match them). `dyn Trait` keeps its own `dyn_trait_dispatch` blocker.
LIFTED_SLICE_WIDE_PTR_BLOCKER = "slice_wide_ptr_lifted"
UNSIZED_DST_BLOCKER = "unsized_dst_or_ptr_metadata"
# Blocker patterns only scan body statements, but `T: ?Sized` bounds sit in signatures and
# `impl` / `trait` headers. So that the split never newly reports a function verifiable on
# `anneal_proof_lifters` while it is generic over an unsized type, a function whose body hits a
# key blocker below is also checked for the mapped guard blocker in its signature context (own
# signature plus enclosing `impl` / `trait` headers, e.g. `fn f<T: ?Sized>` or
# `impl<T: ?Sized> Ptr<T>`); a match is attributed to its entry statement. Other functions keep
# body-only scanning (unchanged accounting).
SIGNATURE_GUARDED_BLOCKERS: dict[str, str] = {LIFTED_SLICE_WIDE_PTR_BLOCKER: UNSIZED_DST_BLOCKER}

RUST_CONSTRUCT_BLOCKERS: list[tuple[str, re.Pattern[str], set[str]]] = [
    (
        "float_arith_or_cast",
        re.compile(r"\b(?:f32|f64)\b"),
        {"trusted_mir", "anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},
    ),
    (
        "inline_asm",
        re.compile(r"\b(?:asm|global_asm)\s*!"),
        {"trusted_mir", "anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},
    ),
    (
        "async_or_coroutine",
        re.compile(r"\b(?:async\s+fn|async\s+move)\b|\.await\b"),
        {"trusted_mir", "anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},
    ),
    (
        "thread_local_or_atomic",
        re.compile(
            r"\bthread_local\s*!|\b(?:Atomic(?:Bool|U8|U16|U32|U64|Usize|I8|I16|I32|I64|Isize|Ptr)|Ordering::(?:Relaxed|Acquire|Release|AcqRel|SeqCst))\b"
        ),
        {"trusted_mir", "anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},
    ),
    (
        "dyn_trait_dispatch",
        re.compile(r"\bdyn\s+[A-Z][A-Za-z0-9_]*"),
        {"trusted_mir", "anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},
    ),
    (
        "closure_capture_or_higher_order",
        re.compile(r"\b(?:FnOnce|FnMut|impl\s+Fn)\b"),
        {"trusted_mir", "anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},
    ),
    (
        "simd_intrinsics",
        re.compile(r"\b(?:core::arch|std::arch|simd_[a-zA-Z0-9_]+)\b"),
        {"trusted_mir", "anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},
    ),
    (
        "formatting_or_io_machinery",
        re.compile(
            r"\b(?:core::fmt::Formatter|fmt::Formatter|fmt::Debug|fmt::Display|std::io)\b|\b(?:write|writeln|println|eprintln|format)\s*!"
        ),
        {"anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},
    ),
    (
        LIFTED_SLICE_WIDE_PTR_BLOCKER,
        re.compile(r"\b(?:slice::from_raw_parts(?:_mut)?|slice_from_raw_parts(?:_mut)?)\b"),
        {"minirust_correspondence", "lean_miri_correspondence"},
    ),
    (
        UNSIZED_DST_BLOCKER,
        re.compile(
            r"\?\s*Sized\b"
            r"|\b(?:size|align)_of_val(?:_raw)?\b"
            r"|\bLayout::for_value(?:_raw)?\b"
            r"|\b(?:Pointee|DynMetadata|PointerMetadata)\b"
            r"|\bptr::metadata\b"
            r"|(?:\b(?:ptr|NonNull)|>)::from_raw_parts(?:_mut)?\b"
            r"|(?:(?:\b(?:ptr|NonNull)|>)::|\.)to_raw_parts\b"
        ),
        {"anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},
    ),
    (
        "union_or_maybe_uninit_projection",
        re.compile(r"\b(?:MaybeUninit|ManuallyDrop)\b"),
        {"minirust_correspondence"},
    ),
    (
        "cross_frame_mut_ref_or_ptr_call",
        re.compile(r"&mut\s+[a-zA-Z0-9_]+\s*[,)]|\.(?:as_mut_ptr|as_ptr|cast|add|sub|offset|wrapping_offset|wrapping_add|wrapping_sub)\s*\("),
        {"minirust_correspondence"},
    ),
    (
        "unaligned_or_volatile_ptr_intrinsics",
        re.compile(r"\b(?:read_unaligned|write_unaligned|read_volatile|write_volatile|copy_nonoverlapping|write_bytes)\b"),
        {"anneal_proof_lifters", "minirust_correspondence"},
    ),
    (
        "panic_or_unreachable_unwind_path",
        re.compile(r"\b(?:panic|unreachable|assert|assert_eq|debug_assert|debug_assert_eq)\s*!"),
        {"minirust_correspondence", "lean_miri_correspondence"},
    ),
]


_RUST_IMPL_OR_TRAIT_HEADER_RE = re.compile(
    r"(?m)^[ \t]*(?:pub(?:\([^)\n]*\))?[ \t]+)?(?:default[ \t]+)?(?:unsafe[ \t]+)?(?:auto[ \t]+)?(?:impl|trait)\b"
)


def _rust_block_header_spans(cleaned: str) -> list[tuple[int, int, str]]:
    """`(body_open, body_close, header)` for every `impl` / `trait` item block in `cleaned`
    (`header` runs from the item keyword up to, excluding, the block's opening `{`)."""
    spans: list[tuple[int, int, str]] = []
    n = len(cleaned)
    for m in _RUST_IMPL_OR_TRAIT_HEADER_RE.finditer(cleaned):
        idx = m.end()
        depth = 0
        open_idx = -1
        while idx < n:
            ch = cleaned[idx]
            if ch in "([":
                depth += 1
            elif ch in ")]":
                depth = max(0, depth - 1)
            elif ch == ";" and depth == 0:
                break
            elif ch == "{" and depth == 0:
                open_idx = idx
                break
            idx += 1
        if open_idx == -1:
            continue
        brace = 0
        close_idx = open_idx
        while close_idx < n:
            ch = cleaned[close_idx]
            if ch == "{":
                brace += 1
            elif ch == "}":
                brace -= 1
                if brace == 0:
                    break
            close_idx += 1
        spans.append((open_idx, close_idx, cleaned[m.start() : open_idx]))
    return spans


def _strip_rust_comments_and_strings(rs_text: str) -> str:
    """Return `rs_text` with `//` line comments and nested `/* ... */` block comments blanked to
    spaces, and string literal interiors (`"..."` and `r#*"..."#*`) blanked to spaces (outer quotes
    and newlines preserved) so comments and string literals never inject unbalanced braces, fake
    `fn` / `impl` headers, or false blocker matches."""
    out: list[str] = []
    i = 0
    n = len(rs_text)
    raw_str_re = re.compile(r'(?<![\w\'"])[bc]?r(#*)"')
    char_re = re.compile(r"'(?:\\(?:x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f]{1,6}\}|.)|[^\\'\n])'")
    while i < n:
        if rs_text.startswith("//", i):
            end = rs_text.find("\n", i + 2)
            end = n if end == -1 else end
            out.append(" " * (end - i))
            i = end
        elif rs_text.startswith("/*", i):
            depth = 1
            k = i + 2
            while k < n and depth > 0:
                if rs_text.startswith("/*", k):
                    depth += 1
                    k += 2
                elif rs_text.startswith("*/", k):
                    depth -= 1
                    k += 2
                else:
                    k += 1
            out.append(re.sub(r"[^\n]", " ", rs_text[i:k]))
            i = k
        elif rs_text[i] == "'":
            prev = rs_text[i - 1] if i > 0 else ""
            # A byte char literal `b'"'` is preceded by `b` (itself not part of an identifier).
            byte_prefix = prev == "b" and (i < 2 or not (rs_text[i - 2].isalnum() or rs_text[i - 2] == "_"))
            cm = char_re.match(rs_text, i) if (not (prev.isalnum() or prev == "_") or byte_prefix) else None
            if cm:
                out.append("'" + " " * (cm.end() - i - 2) + "'")
                i = cm.end()
            else:
                out.append("'")
                i += 1
        elif (rm := raw_str_re.match(rs_text, i)) is not None:
            close = '"' + rm.group(1)
            end = rs_text.find(close, rm.end())
            if end == -1:
                out.append(rs_text[i:rm.end()] + re.sub(r"[^\n]", " ", rs_text[rm.end():]))
                i = n
            else:
                out.append(rs_text[i:rm.end()] + re.sub(r"[^\n]", " ", rs_text[rm.end():end]) + close)
                i = end + len(close)
        elif rs_text[i] == '"':
            k = i + 1
            while k < n and rs_text[k] != '"':
                k += 2 if rs_text[k] == "\\" else 1
            if k >= n:
                out.append('"' + re.sub(r"[^\n]", " ", rs_text[i + 1 :]))
                i = n
            else:
                out.append('"' + re.sub(r"[^\n]", " ", rs_text[i + 1 : k]) + '"')
                i = k + 1
        else:
            out.append(rs_text[i])
            i += 1
    return "".join(out)


def _extract_rust_fn_units(rs_text: str) -> list[tuple[str, list[str], str]]:
    """Extract `(fn_name, statements, signature_context)` from a Rust source file using brace
    balancing. `signature_context` is the function's own signature (generics, parameters,
    return type, `where` clause) preceded by the headers of its enclosing `impl` / `trait`
    blocks, so signature-level constructs such as `T: ?Sized` bounds are visible."""
    cleaned = _strip_rust_comments_and_strings(rs_text)
    block_spans = _rust_block_header_spans(cleaned)

    fn_Header_re = re.compile(
        r"(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?(?:unsafe\s+)?(?:extern\s+(?:\"[^\"]+\"\s+)?)?fn\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*[<(]"
    )
    results: list[tuple[str, list[str], str]] = []
    pos = 0
    n = len(cleaned)
    while pos < n:
        m = fn_Header_re.search(cleaned, pos)
        if not m:
            break
        fn_name = m.group(1)
        # Find opening `{` or `;` (trait method declaration without body)
        idx = m.end() - 1
        paren_depth = 0
        angle_depth = 0
        bracket_depth = 0
        body_start = -1
        while idx < n:
            ch = cleaned[idx]
            if ch == "(":
                paren_depth += 1
            elif ch == ")":
                paren_depth = max(0, paren_depth - 1)
            elif ch == "[":
                bracket_depth += 1
            elif ch == "]":
                bracket_depth = max(0, bracket_depth - 1)
            elif ch == "<":
                angle_depth += 1
            elif ch == ">" and (idx == 0 or cleaned[idx - 1] != "-"):
                angle_depth = max(0, angle_depth - 1)
            elif ch == ";" and paren_depth == 0 and angle_depth == 0 and bracket_depth == 0:
                pos = idx + 1
                break
            elif ch == "{" and paren_depth == 0 and bracket_depth == 0:
                body_start = idx
                break
            idx += 1
        else:
            break

        if body_start == -1:
            continue

        # Balance `{ ... }`
        depth = 0
        end_idx = body_start
        while end_idx < n:
            ch = cleaned[end_idx]
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    break
            end_idx += 1

        body_str = cleaned[body_start + 1 : end_idx]
        raw_stmts = [
            s.strip()
            for s in re.split(r"[;\n]+", body_str)
            if s.strip() and s.strip() not in ("{", "}")
        ]
        if not raw_stmts:
            raw_stmts = ["return ()"]
        enclosing = [hdr for open_i, close_i, hdr in block_spans if open_i < m.start() < close_i]
        signature_context = "\n".join([*enclosing, cleaned[m.start() : body_start]])
        results.append((fn_name, raw_stmts, signature_context))
        pos = end_idx + 1

    return results


def _extract_rust_functions(rs_text: str) -> list[tuple[str, list[str]]]:
    """Extract `(fn_name, statements)` from a Rust source file using brace balancing."""
    return [(fn_name, stmts) for fn_name, stmts, _sig in _extract_rust_fn_units(rs_text)]


def analyze_corpus_completeness(
    corpus_name: str,
    rs_files: list[Path],
    alpha: float = DEFAULT_BLEND_ALPHA,
) -> dict[str, Any]:
    """Compute whole-function verifiability, partial statement/prefix coverage,
    blended completeness score, and marginal-unlock blocker rankings for a corpus.
    """
    layers = (
        "trusted_mir",
        "anneal_proof_lifters",
        "minirust_correspondence",
        "lean_miri_correspondence",
    )
    layer_stats: dict[str, dict[str, float]] = {
        layer: {
            "full_fns": 0,
            "partial_fns": 0,
            "uncovered_fns": 0,
            "full_stmts": 0,
            "supported_stmts_in_blocked_fns": 0,
            "total_stmts_in_blocked_fns": 0,
            "prefix_stmts_in_blocked_fns": 0,
        }
        for layer in layers
    }

    # Track blockers for `trusted_mir` and `anneal_proof_lifters`
    blocker_stats: dict[str, dict[str, int]] = {}
    total_fns = 0
    total_stmts = 0

    for rs_path in sorted(rs_files):
        try:
            text = rs_path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for _fn_name, stmts, signature_context in _extract_rust_fn_units(text):
            total_fns += 1
            w = len(stmts)
            total_stmts += w

            # For each statement, determine which blockers fire
            stmt_blockers: list[list[tuple[str, set[str]]]] = []
            fn_blockers_by_layer: dict[str, set[str]] = {layer: set() for layer in layers}
            for s in stmts:
                hit_list: list[tuple[str, set[str]]] = []
                for b_name, pattern, affected_layers in RUST_CONSTRUCT_BLOCKERS:
                    if pattern.search(s):
                        hit_list.append((b_name, affected_layers))
                        for layer in affected_layers:
                            fn_blockers_by_layer[layer].add(b_name)
                stmt_blockers.append(hit_list)

            # `SIGNATURE_GUARDED_BLOCKERS`: a body hit on a guarded blocker also checks its guard
            # blocker against the signature context, attributing a match to the entry statement.
            body_hit_names = {b_name for s_hits in stmt_blockers for b_name, _aff in s_hits}
            for guarded, guard in SIGNATURE_GUARDED_BLOCKERS.items():
                if guarded not in body_hit_names or not stmt_blockers:
                    continue
                if any(b_name == guard for b_name, _aff in stmt_blockers[0]):
                    continue
                for b_name, pattern, affected_layers in RUST_CONSTRUCT_BLOCKERS:
                    if b_name == guard and pattern.search(signature_context):
                        stmt_blockers[0].append((b_name, affected_layers))
                        for layer in affected_layers:
                            fn_blockers_by_layer[layer].add(b_name)
                        break

            # Record blocker attribution for `anneal_proof_lifters` (our primary proof-lifting frontier)
            lifter_blockers = fn_blockers_by_layer["anneal_proof_lifters"]
            for b_name in lifter_blockers:
                entry = blocker_stats.setdefault(
                    b_name,
                    {
                        "blocked_fn_count": 0,
                        "sole_blocker_fn_count": 0,
                        "uncovered_stmt_count": 0,
                    },
                )
                entry["blocked_fn_count"] += 1
                if len(lifter_blockers) == 1:
                    entry["sole_blocker_fn_count"] += 1

            for s_hits in stmt_blockers:
                for b_name, affected_layers in s_hits:
                    if "anneal_proof_lifters" in affected_layers:
                        blocker_stats[b_name]["uncovered_stmt_count"] += 1

            for layer in layers:
                st = layer_stats[layer]
                if not fn_blockers_by_layer[layer]:
                    st["full_fns"] += 1
                    st["full_stmts"] += w
                else:
                    supp_count = 0
                    prefix_count = 0
                    prefix_open = True
                    for s_hits in stmt_blockers:
                        blocked_here = any(layer in aff for _, aff in s_hits)
                        if not blocked_here:
                            supp_count += 1
                            if prefix_open:
                                prefix_count += 1
                        else:
                            prefix_open = False
                    if supp_count > 0:
                        st["partial_fns"] += 1
                    else:
                        st["uncovered_fns"] += 1
                    st["supported_stmts_in_blocked_fns"] += supp_count
                    st["total_stmts_in_blocked_fns"] += w
                    st["prefix_stmts_in_blocked_fns"] += prefix_count

    rendered_layers: dict[str, dict[str, float]] = {}
    for layer in layers:
        st = layer_stats[layer]
        f_total = max(1, total_fns)
        s_total = max(1, total_stmts)
        blocked_s_total = st["total_stmts_in_blocked_fns"]

        v_fn_pct = 100.0 * st["full_fns"] / f_total
        p_fn_pct = 100.0 * st["partial_fns"] / f_total
        u_fn_pct = 100.0 * st["uncovered_fns"] / f_total
        v_stmt_pct = 100.0 * st["full_stmts"] / s_total

        within_blocked_stmt_pct = (
            100.0 * st["supported_stmts_in_blocked_fns"] / blocked_s_total
            if blocked_s_total > 0
            else 100.0
        )
        within_blocked_prefix_pct = (
            100.0 * st["prefix_stmts_in_blocked_fns"] / blocked_s_total
            if blocked_s_total > 0
            else 100.0
        )
        total_stmt_cov_pct = (
            100.0 * (st["full_stmts"] + st["supported_stmts_in_blocked_fns"]) / s_total
        )
        blended_pct = alpha * v_stmt_pct + (1.0 - alpha) * total_stmt_cov_pct

        rendered_layers[layer] = {
            "fully_verifiable_fns": int(st["full_fns"]),
            "partially_covered_fns": int(st["partial_fns"]),
            "uncovered_fns": int(st["uncovered_fns"]),
            "fully_verifiable_fn_pct": round(v_fn_pct, 2),
            "partially_covered_fn_pct": round(p_fn_pct, 2),
            "uncovered_fn_pct": round(u_fn_pct, 2),
            "fully_verifiable_stmt_pct": round(v_stmt_pct, 2),
            "within_blocked_fns_stmt_coverage_pct": round(within_blocked_stmt_pct, 2),
            "within_blocked_fns_cfg_prefix_pct": round(within_blocked_prefix_pct, 2),
            "total_stmt_coverage_pct": round(total_stmt_cov_pct, 2),
            "blended_completeness_score_pct": round(blended_pct, 2),
        }

    top_blockers = sorted(
        [
            {
                "construct": k,
                "blocked_fn_count": v["blocked_fn_count"],
                "sole_blocker_fn_count": v["sole_blocker_fn_count"],
                "marginal_delta_v_fn_pct": round(
                    100.0 * v["sole_blocker_fn_count"] / max(1, total_fns), 2
                ),
                "uncovered_stmt_count": v["uncovered_stmt_count"],
            }
            for k, v in blocker_stats.items()
        ],
        key=lambda x: (
            -x["sole_blocker_fn_count"],
            -x["blocked_fn_count"],
            -x["uncovered_stmt_count"],
            x["construct"],
        ),
    )

    return {
        "corpus_name": corpus_name,
        "rust_files_scanned": len(rs_files),
        "total_fns": total_fns,
        "total_stmt_units": total_stmts,
        "layers": rendered_layers,
        "top_marginal_unlock_blockers": top_blockers,
    }


def compute_stage_b_empirical_corpora(
    repo_root: Path,
    zerocopy_dir: Path | None = None,
    alpha: float = DEFAULT_BLEND_ALPHA,
) -> dict[str, Any]:
    """Run Stage B empirical completeness analysis across all benchmark corpora."""
    examples_rs = sorted((repo_root / "examples").glob("*/src/**/*.rs"))
    difftest_rs = sorted((repo_root / "tests/miri-diff/corpus/src").glob("**/*.rs")) + sorted(
        (repo_root / "tests/itree-diff/corpus/src").glob("**/*.rs")
    )

    corpora: dict[str, Any] = {
        "fuchsia_and_fxfs_examples": analyze_corpus_completeness(
            "fuchsia_and_fxfs_examples", examples_rs, alpha=alpha
        ),
        "difftest_seed_corpora": analyze_corpus_completeness(
            "difftest_seed_corpora", difftest_rs, alpha=alpha
        ),
    }

    zc_root = zerocopy_dir
    if zc_root is None:
        env_zc = os.environ.get("ANNEAL_ZEROCOPY_DIR", "").strip()
        if env_zc:
            zc_root = Path(env_zc).expanduser()
        else:
            candidate = repo_root.parent / "zerocopy"
            if candidate.exists():
                zc_root = candidate

    all_rs = list(examples_rs) + list(difftest_rs)
    if zc_root is not None and zc_root.exists():
        zc_src = zc_root / "zerocopy" / "src" if (zc_root / "zerocopy" / "src").is_dir() else zc_root / "src"
        if zc_src.is_dir():
            zc_rs = sorted(zc_src.rglob("*.rs"))
            corpora["zerocopy"] = analyze_corpus_completeness(
                "zerocopy", zc_rs, alpha=alpha
            )
            all_rs.extend(zc_rs)

    combined = analyze_corpus_completeness("combined_all_corpora", all_rs, alpha=alpha)
    return {
        "blend_alpha": alpha,
        "combined": combined,
        "corpora": corpora,
    }


# ---------------------------------------------------------------------------
# Pillar 3: Live Correspondence Divergence & Known-Bug Discovery
# ---------------------------------------------------------------------------
# Note: All actionable entries below remain permanently registered in
# `TRACKED_CORRESPONDENCE_DIVERGENCES` as switch-to-pass regression guards; once
# their `witness_symbol` divergence theorems are replaced by positive
# `*_simulation` theorems, `discover_correspondence_divergences` classifies them
# under `resolved_correspondence_divergences`. Resolution is fail-closed: an entry
# with a `resolution_symbol` only counts as resolved when the old witness is gone
# AND the named replacement theorem is live in `resolution_file` (default: `file`,
# in the namespace spelled by its `lean/` module path or by `resolution_namespace`);
# otherwise (e.g. the witness file was deleted, moved, or the witness was renamed
# without a replacement) it stays in `actionable_anneal_bugs` with
# `status == "resolution_missing"`.
# Known out-of-scope follow-ups (documented here rather than tracked as open
# Episode 2 bugs in `TRACKED_CORRESPONDENCE_DIVERGENCES`):
# - `DIV-MR-TB-DIRECT-LOCAL-ACCESS` — general Tree Borrows ancestor/child Read vs.
#   Write state transitions on direct local reads/writes beyond unprotected Freeze
#   Reserved root writes (`DIV-MR-TB-TWOPHASE-DIRECT-WRITE`) remain a future TB
#   correspondence milestone rather than a claim of full Tree Borrows completeness.
# - `step_binOp_offset_usize_wrap_divergence` (`SimLM3_1.lean`) — pre-existing
#   `BinOp.Offset` unsigned `usize` rhs >= 2^63 wrap-around on non-disabled pointers
#   (where `lean-miri` raises `"PointerArithOverflow"` UB while Anneal wraps).

# Episode 2 correspondence file closing `constEvalCounter` / `tailCall` / `opaqueCast`.
UNTESTED_VARIANT_TEST_FILE = "tests/mir/MirUntestedVariantCorrespondenceTests.lean"
# Its declarations live in this namespace (its path has no `lean/` source root), so its
# registry entries name it as `resolution_namespace`: a resolution theorem or statement pin
# in any other namespace of the file (e.g. a decoy `namespace Scratch`) does not count.
# Its resolution theorems are pinned in the file itself (`resolution_pin_file`), since no
# authority audit module imports it.
UNTESTED_VARIANT_NAMESPACE = "Anneal.MirUntestedVariantCorrespondenceTests"

TRACKED_CORRESPONDENCE_DIVERGENCES: list[dict[str, str]] = [
    {
        "id": "DIV-MR-CALL-TARGET-LOCAL",
        "authority": "MiniRustSpec",
        "category": "actionable_anneal_bug",
        "severity": "P0_soundness",
        "witness_symbol": "callerRefMutSilentWrongLocal_divergence",
        "resolution_symbol": "callerRefMutSilentWrongLocal_simulation",
        "file": "minirust/lean/MiniRustSpec/Correspondence/ProvenanceWitness.lean",
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Terminators",
        "switch_to_pass_criterion": "Rebind BorrowEntry.targetLocal across frames in Trusted.MirSemantics.Terminators.evalTerminator so callerRefMutSilentWrongLocal_divergence switches to 3-way agreement (42).",
        "summary": "Cross-frame Call saves caller locals on callStack without rebinding BorrowEntry.targetLocal, allowing callee local index collision to silently return wrong scalar (137 vs. 42) with MirNoUBTree.",
    },
    {
        "id": "DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL",
        "authority": "MiniRustSpec",
        "category": "actionable_anneal_bug",
        "severity": "P1_false_positive_ub",
        "witness_symbol": "callerBorrowAcrossScalarCall_divergence",
        "resolution_symbol": "callerBorrowAcrossScalarCall_simulation",
        "file": "minirust/lean/MiniRustSpec/Correspondence/ProvenanceWitness.lean",
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Statements",
        "switch_to_pass_criterion": "Scope invalidateConflictingBorrows to the active frame so callee root assignments do not disable caller borrows across scalar calls.",
        "summary": "Callee root local assignment runs invalidateConflictingBorrows on the shared borrows table, disabling the caller's borrow of its own local _1.",
    },
    {
        "id": "DIV-MR-TB-TWOPHASE-DIRECT-WRITE",
        "authority": "MiniRustSpec",
        "category": "actionable_anneal_bug",
        "severity": "P1_soundness",
        "witness_symbol": "twoPhaseDirectWriteTreeBorrowsGap",
        "resolution_symbol": "twoPhaseDirectWriteTreeBorrows_simulation",
        "file": "minirust/lean/MiniRustSpec/Correspondence/RefWitness.lean",
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Places",
        "switch_to_pass_criterion": "Update updateBorrowPerm on direct root write (writerTag = none) to disable unprotected Freeze Reserved borrows, switching twoPhaseDirectWriteTreeBorrowsGap to UB agreement with MachTB.",
        "summary": "Direct write (_1 = 99) to a local with an unprotected Freeze Reserved two-phase borrow leaves .reserved unchanged in Anneal while MachTB disables it.",
    },
    {
        "id": "DIV-MR-TB-FNENTRY-LOCAL-DEALLOC",
        "authority": "MiniRustSpec",
        "category": "actionable_anneal_bug",
        "severity": "P1_soundness",
        "witness_symbol": "retagFnEntryLocalDeallocUb",
        "resolution_symbol": "retagFnEntryLocalDealloc_simulation",
        "file": "minirust/lean/MiniRustSpec/Correspondence/RefWitness.lean",
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Terminators",
        "switch_to_pass_criterion": "Check active FnEntry protectors on callee-owned locals during Return frame teardown before releasing protectors, matching MachTB deallocAllM.",
        "summary": "Returning with a function-entry protector attached to a callee-owned local succeeds in Anneal while faulting at Terminator::Return on MachTB.",
    },
    {
        "id": "DIV-MR-TB-UNSAFECELL-PROTECTED-IM",
        "authority": "MiniRustSpec",
        "category": "actionable_anneal_bug",
        "severity": "P2_false_positive_ub",
        "witness_symbol": "unsafeCellProtectedInteriorMut",
        "resolution_symbol": "unsafeCellProtectedInteriorMut_simulation",
        "file": "minirust/lean/MiniRustSpec/Correspondence/TbWitness.lean",
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Places",
        "switch_to_pass_criterion": "Exempt !Freeze Cell/ReservedIM entries from hasProtectedWriteConflict so unsafeCellProtectedInteriorMut returns 77 across Anneal, Mach, and MachTB.",
        "summary": "Retag([fn entry]) on &UnsafeCell<u32> faults in Anneal's hasProtectedWriteConflict whereas MachTB uses PermissionProt::Cell (prevents_deallocation = false) and returns 77.",
    },
    {
        "id": "DIV-LM-RAW-OVERWRITE-CHAR-COPY",
        "authority": "LeanMiriSpec",
        "category": "actionable_anneal_bug",
        "severity": "P1_soundness",
        "witness_symbol": "step_raw_overwritten_direct_copy_invalid_char_divergence",
        "resolution_symbol": "step_raw_overwritten_direct_copy_invalid_char_simulation",
        "file": "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean",
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Places",
        "switch_to_pass_criterion": "Re-validate char Unicode scalar validity on direct Use(Copy) of raw-overwritten char locals (matching bool re-validation in step_raw_overwritten_direct_copy_invalid_bool_simulation).",
        "summary": "After a raw pointer write stores an invalid char surrogate (0xD800) into a char local, direct Use(Copy) does not re-validate char scalar validity.",
    },
    {
        "id": "DIV-LM-D6-OFFSET-DISABLED-TAG",
        "authority": "LeanMiriSpec",
        "category": "actionable_anneal_bug",
        "severity": "P2_false_positive_ub",
        "witness_symbol": "step_binOp_offset_disabled_divergence",
        "resolution_symbol": "step_binOp_offset_disabled_simulation",
        "file": "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean",
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Scalars",
        "switch_to_pass_criterion": "Align BinOp.Offset allocation bounds check with Miri ptrOffsetInbounds (which checks live allocation bounds independent of Tree Borrows .disabled permission).",
        "summary": "BinOp.Offset on a live allocation whose borrow tag is .disabled faults in Anneal whereas lean-miri ptrOffsetInbounds checks allocation bounds only on offset and defers Tree Borrows check to dereference.",
    },
    {
        "id": "DIV-LM-ENUM-SET-DISCR-UNINIT",
        "authority": "LeanMiriSpec",
        "category": "actionable_anneal_bug",
        "severity": "P2_precision",
        "witness_symbol": "step_setDiscriminant_uninit_divergence",
        "resolution_symbol": "step_setDiscriminant_uninit_simulation",
        "file": "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean",
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Statements",
        "switch_to_pass_criterion": "Initialize discriminant tag on SetDiscriminant when target enum slot is .uninit, matching Miri's writeDiscriminant.",
        "summary": "StatementKind.SetDiscriminant on an uninitialized enum local diverges from lean-miri's writeDiscriminant.",
    },
    {
        "id": "MODEL-LM-D12-SYNTHETIC-ADDR-STRIDE",
        "authority": "LeanMiriSpec",
        "category": "intentional_modeling_choice",
        "severity": "info",
        "witness_symbol": "step_rawPtr_cmp_ptr_ptr_exact",
        "file": "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean",
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Scalars",
        "switch_to_pass_criterion": "Intentional two-address-model characterization (64 KiB local page stride vs. 4 GiB allocId stride).",
        "summary": "Anneal assigns local i base address (1048576 + i) * 65536 vs. lean-miri allocId.value * 2^32; exact relation proved in step_rawPtr_cmp_ptr_ptr_exact.",
    },
    # Episode 2 (`tests/mir/MirUntestedVariantCorrespondenceTests.lean`): divergences found while
    # closing `tailCall` / `opaqueCast`, each witnessed by a kernel-audited manifest theorem.
    {
        "id": "DIV-LM-TAILCALL-NOUNWIND-UNWIND",
        "authority": "LeanMiriSpec",
        "category": "actionable_anneal_bug",
        "severity": "P2_soundness",
        "witness_symbol": "tailCall_leanMiri_nounwind_callee",
        "resolution_symbol": "tailCall_leanMiri_nounwind_callee_simulation",
        "resolution_namespace": UNTESTED_VARIANT_NAMESPACE,
        "resolution_pin_file": UNTESTED_VARIANT_TEST_FILE,
        "file": UNTESTED_VARIANT_TEST_FILE,
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Terminators",
        "switch_to_pass_criterion": "When the call-site or callee ABI cannot unwind, rewrite the inherited saved caller's returnUnwind to .unreachable in enterTailCalleeFrame (Miri initStackFrame, Call.lean:261-264), so tailCall_leanMiri_nounwind_callee's `↔ u = ur` collapses to unconditional shape agreement.",
        "summary": "A tail call into a non-unwinding (e.g. extern \"C\") callee keeps the tail-caller's inherited unwind action in Anneal, whereas Miri forces it to Unreachable: an UnwindResume out of the callee is UB in Miri for every inherited action but resumes the caller's cleanup block, aborts, or keeps unwinding in Anneal (two-sided verdict table: tailCall_leanMiri_unwind_verdicts).",
    },
    {
        "id": "DIV-TR-OPAQUECAST-ROOT-DISPATCH",
        "authority": "LeanMiriSpec",
        "category": "actionable_anneal_bug",
        "severity": "P3_latent_phase_boundary",
        "witness_symbol": "opaqueCast_trusted_root_dispatch_divergence",
        "resolution_symbol": "opaqueCast_trusted_root_dispatch_simulation",
        "resolution_namespace": UNTESTED_VARIANT_NAMESPACE,
        "resolution_pin_file": UNTESTED_VARIANT_TEST_FILE,
        "file": UNTESTED_VARIANT_TEST_FILE,
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Places",
        "switch_to_pass_criterion": "Strip leading/bare ProjectionElem.opaqueCast before the root-vs-projected dispatch in evalOperand (.move), writePlaceValue, evalStmt (.assign / .deinit / .setDiscriminant), and uninitFieldWriteShell?, so (_l as T) and (_l as T).f behave like their post-borrowck erasures _l and _l.f.",
        "summary": "A bare (_l as T) place takes Trusted's projected path while its erasure _l takes the root path, and uninitFieldWriteShell? returns none on a leading .opaqueCast: move keeps _l initialized, writes/assignments to an uninitialized _l (including (_l as T).f = v) and SetDiscriminant((_l as T), vIdx) on an uninitialized enum fault with UB, and Deinit((_l as T)) leaves _l as LocalSlot.init Value.uninit where Deinit(_l) stores LocalSlot.uninit. Latent: MirPhase::Runtime forbids OpaqueCast.",
    },
    {
        "id": "MODEL-LM-TAILCALL-MODULAR-ROOT",
        "authority": "LeanMiriSpec",
        "category": "intentional_modeling_choice",
        "severity": "info",
        "witness_symbol": "tailCall_leanMiri_root_stop_diverges",
        "file": UNTESTED_VARIANT_TEST_FILE,
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Terminators",
        "switch_to_pass_criterion": "Intentional modular-root model (Anneal's root frame is the modularly verified function with an external caller); nested and modular-root lockstep is proved in tailCall_leanMiri_shape_lockstep, and 1-frame modular-root UnwindResume (.panic vs Miri's topmost-frame UB) is characterized in tailCall_leanMiri_modular_root_unwind.",
        "summary": "At a whole-program root (ReturnContinuation.stop) Miri raises invalidProgram (rustc bug!(\"can't tailcall as root\")) and at a 1-frame stack UnwindResume is UB (\"unwinding past the topmost stack frame\"), whereas Anneal's modular root tail call steps into the callee and unwinds to .panic.",
    },
    {
        "id": "MODEL-LM-TAILCALL-DIRECT-ARITY-STEP",
        "authority": "LeanMiriSpec",
        "category": "intentional_modeling_choice",
        "severity": "info",
        "witness_symbol": "tailCall_witness_direct_arity_divergence",
        "file": UNTESTED_VARIANT_TEST_FILE,
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Terminators",
        "switch_to_pass_criterion": "Intentional: rustc's MIR type checker rules out ill-arity FnDef calls; both semantics report UB.",
        "summary": "An ill-arity direct tail call is UB at the call in Miri, while Anneal enters the callee and faults one step later when it reads the dead parameter (both UB, different steps).",
    },
    {
        "id": "DIV-TR-TAILCALL-DANGLING-CALLER-LOCAL",
        "authority": "LeanMiriSpec",
        "category": "actionable_anneal_bug",
        "severity": "P1_soundness",
        "witness_symbol": "tailCall_witness_dangling_caller_local_divergence",
        "resolution_symbol": "tailCall_witness_dangling_caller_local_simulation",
        "resolution_namespace": UNTESTED_VARIANT_NAMESPACE,
        "resolution_pin_file": UNTESTED_VARIANT_TEST_FILE,
        "file": UNTESTED_VARIANT_TEST_FILE,
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Terminators",
        "switch_to_pass_criterion": "Disable (or remove) every borrow entry targeting the replaced tail-caller frame in enterTailCalleeFrame, matching Miri's tail-call cleanup (CallMachine.cleanup deallocates the popped frame's memory-backed locals), so the witness's *p faults with .ub instead of returning 137.",
        "summary": "enterTailCalleeFrame discards the tail-caller's locals but keeps borrow entries whose un-namespaced targetLocal now names the callee's local: a raw pointer to the tail-caller's x = 42 passed to the callee silently reads the callee's same-index local (137) and returns normally, whereas Miri's tail-call cleanup deallocates x and the dereference is a use-after-free (UB). Resolved once evalTailCallTerminator tore the tail-caller frame down (disableFrameBorrows before enterTailCalleeFrame): *p now faults with UB (tailCall_witness_dangling_caller_local_simulation).",
    },
    {
        "id": "DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW",
        "authority": "LeanMiriSpec",
        "category": "actionable_anneal_bug",
        "severity": "P1_soundness",
        "witness_symbol": "tailCall_witness_root_caller_referent_divergence",
        "resolution_symbol": "tailCall_witness_root_caller_referent_simulation",
        "resolution_namespace": UNTESTED_VARIANT_NAMESPACE,
        "resolution_pin_file": UNTESTED_VARIANT_TEST_FILE,
        "file": UNTESTED_VARIANT_TEST_FILE,
        "anneal_component": "Trusted.Rustc.V2026_06_01.MirSemantics.Terminators",
        "switch_to_pass_criterion": "Keep caller-owned referents (Memory.callerLocals) addressable after a root tail call into a callee with more locals, e.g. by giving caller referents a frame identity distinct from the root frame's (targetFrameDepth, targetLocal) pairs, so the witness's *p reads the caller's 42 instead of the tail-callee's own _2.",
        "summary": "A modular-root tail call into a callee with more locals than the tail-caller makes the callee's own local shadow a caller-owned referent: a pointer argument into the caller (callerLocals slot 2 = 42, borrow at (0, 2)) is read through activeFrameSlot? as the callee's _2 = 137, whereas Miri reads the live caller allocation (42).",
    },
]


# Top-level starts of a stripped span: a nested block comment, a line comment, a string,
# a character literal, or a raw string literal (`r"..."`, `r#"..."#`, ...; an `r` that
# does not end an identifier).
_LEAN_STRIP_TOP_RE = re.compile(r"""/-|--|"|'|(?<![\w'!?»])r(?=#*")""")
_LEAN_STRIP_BLOCK_RE = re.compile(r"/-|-/")
_LEAN_STRIP_STRING_RE = re.compile(r'[\\"]')


def _blank_keep_newlines(text: str) -> str:
    """`text` with every character except `\\n` replaced by a space."""
    if "\n" not in text:
        return " " * len(text)
    return "\n".join(" " * len(part) for part in text.split("\n"))


def _strip_lean_comments_and_strings(src: str) -> str:
    """Strip Lean `--` line comments, nested `/- ... -/` block comments, and literals.

    Replaces stripped spans with spaces while preserving `\\n` so line-anchored
    declaration matching cannot be spoofed by commented-out theorems, docstrings,
    or string literals (and handles `'\"'` character literals cleanly). Copies the
    unstripped text between stripped spans in bulk.
    """
    out: list[str] = []
    n = len(src)
    i = 0
    while i < n:
        m = _LEAN_STRIP_TOP_RE.search(src, i)
        if m is None:
            out.append(src[i:])
            break
        start = m.start()
        out.append(src[i:start])
        tok = m.group(0)
        if tok == "/-":
            out.append("  ")
            depth = 1
            j = start + 2
            while depth > 0:
                bm = _LEAN_STRIP_BLOCK_RE.search(src, j)
                if bm is None:
                    out.append(_blank_keep_newlines(src[j:]))
                    j = n
                    break
                out.append(_blank_keep_newlines(src[j : bm.start()]))
                out.append("  ")
                depth += 1 if bm.group(0) == "/-" else -1
                j = bm.end()
            i = j
        elif tok == "--":
            nl = src.find("\n", start)
            end = n if nl < 0 else nl
            out.append(" " * (end - start))
            i = end
        elif tok == "r":
            # Lean 4 raw string literals (`r"..."`, `r#"..."#`, `r##"..."##`) do not
            # escape `\\"`.
            j = start + 1
            while src[j] == "#":
                j += 1
            closing = '"' + "#" * (j - start - 1)
            out.append(" " * (j - start + 1))
            close_at = src.find(closing, j + 1)
            if close_at < 0:
                out.append(_blank_keep_newlines(src[j + 1 :]))
                i = n
            else:
                out.append(_blank_keep_newlines(src[j + 1 : close_at]))
                out.append(" " * len(closing))
                i = close_at + len(closing)
        elif tok == '"':
            out.append(" ")
            j = start + 1
            while j < n:
                sm = _LEAN_STRIP_STRING_RE.search(src, j)
                if sm is None:
                    out.append(_blank_keep_newlines(src[j:]))
                    j = n
                    break
                out.append(_blank_keep_newlines(src[j : sm.start()]))
                j = sm.start()
                if src[j] == "\\":
                    out.append("  " if j + 1 < n and src[j + 1] != "\n" else " ")
                    j += 2
                else:
                    out.append(" ")
                    j += 1
                    break
            i = j
        # Lean character literals like `'"'` or `'\\''`, so `'"'` does not open a string.
        elif start + 2 < n and src[start + 1] != "\\" and src[start + 2] == "'":
            out.append("   ")
            i = start + 3
        elif start + 3 < n and src[start + 1] == "\\" and src[start + 3] == "'":
            out.append("    ")
            i = start + 4
        else:
            out.append("'")
            i = start + 1
    return "".join(out)


_LEAN_TOKEN_RE = re.compile(
    r"""
    @\[
    | :=
    | [(\[{⟨⦃)\]}⟩⦄:@.;,]
    | ``?(?:«[^»\n]*»|[^\W\d][\w'!?]*)(?:\.(?:«[^»\n]*»|[^\W\d][\w'!?]*))*
    | «[^»\n]+»
    | [\#?]?[A-Za-z_0-9][A-Za-z_0-9'!?]*
    """,
    re.VERBOSE,
)
# (A quoted name literal such as `` `theorem `` or ``` ``Foo.def ``` is one token, never a
# command keyword that could cut a declaration body short.)

_LEAN_OPEN_BRACKETS = {"@[", "(", "[", "{", "⟨", "⦃"}
_LEAN_CLOSE_BRACKETS = {")", "]", "}", "⟩", "⦄"}
_LEAN_DECL_MODIFIERS = {
    "private",
    "protected",
    "noncomputable",
    "nonrec",
    "partial",
    "unsafe",
    "scoped",
    "local",
}
_LEAN_FORBIDDEN_RES_MODS = {"private", "unsafe", "partial"}
_LEAN_WITNESS_DECL_KINDS = {
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "axiom",
    "opaque",
    "structure",
    "inductive",
    "class",
}
_LEAN_RES_DECL_KINDS = {"theorem", "lemma"}
_LEAN_IN_PREFIX_CMDS = {
    "open",
    "set_option",
    "include",
    "omit",
    "variable",
    "unseal",
    "seal",
    "attribute",
}
_LEAN_SCOPE_KEYWORDS = {"namespace", "section", "mutual", "end"}
_LEAN_OTHER_TOP_CMDS = {
    "import",
    "prelude",
    "universe",
    "universes",
    "export",
    "elab",
    "macro",
    "macro_rules",
    "syntax",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "instance",
    "deriving",
    "initialize",
    "builtin_initialize",
}
_LEAN_ALL_CMD_BOUNDARIES = (
    _LEAN_DECL_MODIFIERS
    | _LEAN_WITNESS_DECL_KINDS
    | _LEAN_IN_PREFIX_CMDS
    | _LEAN_SCOPE_KEYWORDS
    | _LEAN_OTHER_TOP_CMDS
    | {"example", "@["}
)
_LEAN_TRIVIAL_PIN_TYPES = {"_", "True", "Prop", "Bool", "Nat", "Unit", "PUnit"}
# Tokens that make a pin's type depend on its own RHS (so the pin locks nothing).
_LEAN_SELF_TYPED_PIN_TOKENS = {"type_of", "by", "_"}
_LEAN_FORBIDDEN_PIN_ARGS = {
    "by",
    "fun",
    "let",
    "have",
    "do",
    "match",
    "where",
    "with",
    "show",
    "suffices",
}

# ---------------------------------------------------------------------------
# Flip-direction witness polarity guard: statement analysis of resolution theorems
# and their audit pins.
#
# When a tracked divergence is fixed, its `*_divergence` witness must flip to a
# `*_simulation` theorem whose statement actually says something. The coarse
# declaration scanner above drops every operator, so the statements of resolution
# theorems and pins are re-tokenized here with logical connectives, arrows,
# binders, and `=` kept, and are rejected (fail closed) when they are vacuous
# (`True`, `¬False`, `x = x`, a closed statement naming no definition, or a
# trivially false antecedent such as `False → ...` or `(h : False)`, also under
# `∀` binders), hole-riddled (`_` as the whole statement, `?m` / `?_`
# metavariables, `sorry`), self-typed (`type_of%`, a tactic-synthesized `by ...`
# type), or proved with `sorry` / `admit`.
# ---------------------------------------------------------------------------

_LEAN_STMT_TOKEN_RE = re.compile(
    r"""
    @\[
    | :=|::
    | <->|<\||\|>\.?|\|\||&&
    | ->|=>|<=|>=|!=|\+\+
    | /\\|\\/
    | [→↔↦∧∨¬∀∃Π∏λ≠≤≥∈∉⊆▸]
    | [(\[{⟨⦃)\]}⟩⦄:@.;,|%=+\-*/<>^!$]
    | «[^»\n]+»
    | [\#?]?[^\W\d][\w'!?]*
    | \d\w*
    """,
    re.VERBOSE,
)
_LEAN_STMT_OPEN = frozenset({"(", "[", "{", "⟨", "⦃", "@["})
_LEAN_STMT_CLOSE = frozenset({")", "]", "}", "⟩", "⦄"})
_LEAN_STMT_ARROWS = frozenset({"→", "->"})
_LEAN_STMT_IFFS = frozenset({"↔", "<->"})
_LEAN_STMT_ANDS = frozenset({"∧", "/\\"})
_LEAN_STMT_ORS = frozenset({"∨", "\\/"})
_LEAN_STMT_NOTS = frozenset({"¬", "Not"})
_LEAN_STMT_FORALLS = frozenset({"∀", "Π", "∏"})
_LEAN_STMT_INFIX_OPS = frozenset(
    {
        "=",
        "≠",
        "<",
        ">",
        "≤",
        "≥",
        "<=",
        ">=",
        "!=",
        "+",
        "-",
        "*",
        "/",
        "%",
        "^",
        "++",
        "::",
        "∈",
        "∉",
        "⊆",
        "|>",
        "|>.",
        "<|",
        "$",
        "▸",
        "&&",
        "||",
    }
)
# Metaprogramming constant/application builders that turn a quoted hole literal
# (``mkConst ``sorryAx``) into an actual proof term inside `elab` / `macro` commands.
_LEAN_METAPROG_CONST_BUILDERS = frozenset(
    {"mkConst", "mkApp", "mkAppM", "mkAppN", "mkAppOptM", "evalConst", "evalConstCheck"}
)
# Tokens whose scope extends to the end of the enclosing expression.
_LEAN_STMT_SCOPE_TOKENS = frozenset(
    {"∀", "Π", "∏", "∃", "fun", "λ", "let", "have", "show", "match", "if", "do"}
)
# Options and environment hooks that add a declaration without kernel type checking
# (`set_option debug.skipKernelTC true`), so a metaprogram can admit an ill-typed proof.
# They are holes even as the field of a `.`-qualified name.
_LEAN_KERNEL_BYPASS_TOKENS = frozenset({"skipKernelTC", "addDeclWithoutChecking"})
# Proof terms, tactics, and compiler-reduction hooks that close a goal without a
# kernel-checked standard-axiom proof.
_LEAN_HOLE_PROOF_TOKENS = frozenset(
    {
        "sorry",
        "admit",
        "sorryAx",
        "native_decide",
        "ofReduceBool",
        "ofReduceNat",
        "mkSorry",
        *_LEAN_KERNEL_BYPASS_TOKENS,
    }
)
_LEAN_FILE_HOLE_TOKENS = frozenset({*_LEAN_HOLE_PROOF_TOKENS, "axiom", "implemented_by", "extern"})
# Tactics that search the environment for a closing lemma: a proof that runs one may use
# an earlier holey declaration of its module without naming it.
_LEAN_SEARCH_TACTICS = frozenset({"exact?", "apply?", "rw?", "library_search", "rw_search"})
# Identifiers that name no domain definition a correspondence statement could be about.
_LEAN_STMT_LOGICAL_IDENTS = frozenset(
    {
        "_root_",
        "True",
        "False",
        "Bool",
        "true",
        "false",
        "Not",
        "And",
        "Or",
        "Iff",
        "Eq",
        "Ne",
        "HEq",
        "Prop",
        "Type",
        "Sort",
        "Unit",
        "PUnit",
        "Empty",
        "PEmpty",
        "ULift",
        "PLift",
        "Fin",
        "Subsingleton",
        "Nat",
        "Int",
        "String",
        "Char",
        "UInt8",
        "UInt16",
        "UInt32",
        "UInt64",
        "USize",
        "ISize",
        "Float",
        "ByteArray",
        "BitVec",
        "Array",
        "List",
        "Option",
        "Prod",
        "Sum",
        "Sigma",
        "PSigma",
        "Subtype",
        "Decidable",
        "DecidableEq",
        "Inhabited",
        "Nonempty",
        "BEq",
        "Ord",
        "LT",
        "LE",
        "HAdd",
        "HSub",
        "HMul",
        "HDiv",
        "HMod",
        "HPow",
        "HAppend",
        "some",
        "none",
        "inl",
        "inr",
        "fst",
        "snd",
        "mk",
        "id",
        "fun",
        "let",
        "have",
        "show",
        "from",
        "by",
        "if",
        "then",
        "else",
        "match",
        "with",
        "do",
        "in",
        "at",
        "this",
        "trivial",
        "rfl",
        "decide",
        "nofun",
        "absurd",
        "nomatch",
    }
)
_LEAN_TRUTH_TRUE = "true"
_LEAN_TRUTH_FALSE = "false"
_LEAN_PIN_SEG_PAT = r"(?:«[^»\n]+»|(?!_\b)[^\W\d][\w'!?]*)"
_LEAN_PIN_RHS_RE = re.compile(
    rf"\s*@?\s*{_LEAN_PIN_SEG_PAT}(?:\s*\.\s*{_LEAN_PIN_SEG_PAT})*(?:\s+(?:_|{_LEAN_PIN_SEG_PAT}))*\s*"
)


def _unescape_lean_guillemet_ident(tok: str) -> str:
    """Normalize `«ident»` to `ident` when `ident` is an ordinary identifier token."""
    if tok.startswith("«") and tok.endswith("»"):
        inner = tok[1:-1]
        if inner and not inner[0].isdigit() and all(c.isalnum() or c in "_'!?" for c in inner):
            return inner
    return tok


def _collapse_lean_root_prefix(tokens: list[str]) -> list[str]:
    """Collapse top-level `_root_ . X` into `X` so `_root_.True` / `_root_.False` match
    unqualified logical constants."""
    out: list[str] = []
    i = 0
    n = len(tokens)
    while i < n:
        if (
            i + 2 < n
            and tokens[i] == "_root_"
            and tokens[i + 1] == "."
            and (not out or out[-1] != ".")
        ):
            i += 2
            continue
        out.append(tokens[i])
        i += 1
    return out


_LEAN_NAME_SEG_PAT = r"(?:«[^»\n]*»|[^\W\d][\w'!?]*)"
# A quoted name literal (`` `foo.bar `` or ``` ``foo ```) names a declaration without
# using it (`` a == ``sorryAx `` in an axiom audit is not a `sorry`), unlike a syntax
# quotation `` `(tactic| sorry) ``, which expands to its contents.
_LEAN_NAME_LITERAL_RE = re.compile(rf"``?({_LEAN_NAME_SEG_PAT}(?:\.{_LEAN_NAME_SEG_PAT})*)")


def _lean_stmt_tokens(text: str) -> list[str]:
    """Tokens of a comment/string-stripped Lean statement (operators included, simple
    guillemets unescaped, `_root_.` prefixes collapsed, and quoted name literals kept as
    opaque `` «`name» `` tokens)."""
    text = _LEAN_NAME_LITERAL_RE.sub(
        lambda m: "«`" + m.group(1).replace("«", "").replace("»", "") + "»", text
    )
    raw = [_unescape_lean_guillemet_ident(tok) for tok in _LEAN_STMT_TOKEN_RE.findall(text)]
    return _collapse_lean_root_prefix(raw)


def _lean_stmt_matching_close(tokens: list[str], start: int) -> int:
    """Index of the bracket closing `tokens[start]`, or `len(tokens)` if unbalanced."""
    depth = 0
    for j in range(start, len(tokens)):
        tok = tokens[j]
        if tok in _LEAN_STMT_OPEN:
            depth += 1
        elif tok in _LEAN_STMT_CLOSE:
            depth -= 1
            if depth == 0:
                return j
    return len(tokens)


def _lean_stmt_first_top(tokens: list[str], wanted: frozenset[str] | set[str], start: int = 0) -> int | None:
    """Index of the first depth-0 token of `tokens[start:]` in `wanted`."""
    depth = 0
    for j in range(start, len(tokens)):
        tok = tokens[j]
        if tok in _LEAN_STMT_OPEN:
            depth += 1
        elif tok in _LEAN_STMT_CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and tok in wanted:
            return j
    return None


def _lean_stmt_strip_outer(tokens: list[str], brackets: str = "(") -> list[str]:
    """Strip redundant outer bracket pairs (`(P)` -> `P`) whose opener is in `brackets`."""
    while (
        len(tokens) >= 2
        and tokens[0] in brackets
        and tokens[0] in _LEAN_STMT_OPEN
        and _lean_stmt_matching_close(tokens, 0) == len(tokens) - 1
    ):
        tokens = tokens[1:-1]
    return tokens


def _lean_stmt_split_top(tokens: list[str], seps: frozenset[str] | set[str]) -> list[list[str]]:
    """Split `tokens` at depth-0 separators; a scope token (`∀`, `fun`, `let`, ...)
    absorbs the rest of the expression into the current part."""
    parts: list[list[str]] = []
    cur: list[str] = []
    depth = 0
    for idx, tok in enumerate(tokens):
        if depth == 0 and tok in _LEAN_STMT_SCOPE_TOKENS:
            cur.extend(tokens[idx:])
            break
        if tok in _LEAN_STMT_OPEN:
            depth += 1
        elif tok in _LEAN_STMT_CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and tok in seps:
            parts.append(cur)
            cur = []
            continue
        cur.append(tok)
    parts.append(cur)
    return parts


def _lean_strip_binder_default(tokens: list[str]) -> list[str]:
    """Strip an auto-param / optional default `:= <default>` suffix from a binder type."""
    assign = _lean_stmt_first_top(tokens, {":="})
    return tokens[:assign] if assign is not None else tokens


def _lean_bracket_binder_types(tokens: list[str]) -> list[list[str]]:
    """Types of the depth-0 bracketed binder groups of `tokens`: `(x y : T)`,
    `{x : T}`, `⦃x : T⦄`, `{{x : T}}`, `[T]`, `[inst : T]`, and `(h : T := tac)`."""
    out: list[list[str]] = []
    i = 0
    while i < len(tokens):
        tok = tokens[i]
        if tok in ("(", "{", "⦃", "["):
            close = _lean_stmt_matching_close(tokens, i)
            inner = tokens[i + 1 : close]
            colon = _lean_stmt_first_top(inner, {":"})
            if colon is not None:
                out.append(_lean_strip_binder_default(inner[colon + 1 :]))
            elif inner and inner[0] in ("(", "{", "⦃", "["):
                out.extend(_lean_bracket_binder_types(inner))
            elif tok == "[":
                out.append(_lean_strip_binder_default(inner))
            i = close + 1
        else:
            i += 1
    return out


def _lean_quantifier_binder_types(binders: list[str]) -> list[list[str]]:
    """Types bound by the binder list of `∀ <binders>, ...` (bracketed groups, or an
    unbracketed `x y : T`)."""
    types = _lean_bracket_binder_types(binders)
    colon = _lean_stmt_first_top(binders, {":"})
    if colon is not None:
        types.append(_lean_strip_binder_default(binders[colon + 1 :]))
    return types


def _lean_binder_group_names(tokens: list[str]) -> list[str]:
    """Bound variable names introduced by bracketed binder groups `(x y : T)`, `{x : T}`, etc."""
    names: list[str] = []
    i = 0
    while i < len(tokens):
        tok = tokens[i]
        if tok in ("(", "{", "⦃", "["):
            close = _lean_stmt_matching_close(tokens, i)
            inner = tokens[i + 1 : close]
            colon = _lean_stmt_first_top(inner, {":"})
            if colon is not None:
                for bt in inner[:colon]:
                    if _is_lean_stmt_ident(bt) and bt != "_":
                        names.append(bt)
            elif inner and inner[0] in ("(", "{", "⦃", "["):
                names.extend(_lean_binder_group_names(inner))
            i = close + 1
        else:
            i += 1
    return names


def _lean_quantifier_binder_names(binders: list[str]) -> list[str]:
    """Bound variable names introduced by `∀ <binders>, ...` or `∃ <binders>, ...`."""
    names = _lean_binder_group_names(binders)
    colon = _lean_stmt_first_top(binders, {":"})
    prefix = binders[:colon] if colon is not None else binders
    i = 0
    while i < len(prefix):
        tok = prefix[i]
        if tok in _LEAN_STMT_OPEN:
            i = _lean_stmt_matching_close(prefix, i) + 1
            continue
        if _is_lean_stmt_ident(tok) and tok != "_":
            names.append(tok)
        i += 1
    return names


_LEAN_CANON_CONNECTIVES = {
    "->": "→",
    "<->": "↔",
    "/\\": "∧",
    "\\/": "∨",
    "<=": "≤",
    ">=": "≥",
    "Π": "∀",
    "∏": "∀",
    "λ": "fun",
}


def _lean_norm_expr_tokens(tokens: list[str]) -> list[str]:
    """Canonicalize outer parentheses, leading `id`, `Bool.true`/`Bool.false`, and
    ASCII/Unicode connectives for syntactic comparison."""
    toks = _lean_stmt_strip_outer(list(tokens))
    while len(toks) > 1 and toks[0] == "id":
        toks = _lean_stmt_strip_outer(toks[1:])
    out: list[str] = []
    i = 0
    n = len(toks)
    while i < n:
        if (
            i + 2 < n
            and toks[i] == "Bool"
            and toks[i + 1] == "."
            and toks[i + 2] in ("true", "false")
            and (not out or out[-1] != ".")
        ):
            out.append(toks[i + 2])
            i += 3
            continue
        out.append(_LEAN_CANON_CONNECTIVES.get(toks[i], toks[i]))
        i += 1
    return out


def _lean_top_app_args(tokens: list[str]) -> tuple[str, list[list[str]]] | None:
    """Parse a depth-0 prefix application `@?head arg1 arg2 ...` when no infix binary
    connective or relation occurs at depth 0."""
    toks = _lean_norm_expr_tokens(tokens)
    if not toks:
        return None
    explicit = False
    if toks[0] == "@":
        explicit = True
        toks = toks[1:]
    if not toks or not _is_lean_stmt_ident(toks[0]):
        return None
    if _lean_stmt_first_top(
        toks,
        _LEAN_STMT_IFFS
        | _LEAN_STMT_ARROWS
        | _LEAN_STMT_ORS
        | _LEAN_STMT_ANDS
        | _LEAN_STMT_INFIX_OPS
        | {":", ",", ":=", ";"},
    ) is not None:
        return None
    head = ("@" + toks[0]) if explicit else toks[0]
    i = 1
    n = len(toks)
    while i + 1 < n and toks[i] == "." and _is_lean_stmt_ident(toks[i + 1]):
        head = f"{head}.{toks[i + 1]}"
        i += 2
    args: list[list[str]] = []
    while i < n:
        tok = toks[i]
        if tok in _LEAN_STMT_OPEN:
            close = _lean_stmt_matching_close(toks, i)
            arg = list(toks[i : close + 1])
            i = close + 1
        else:
            arg = [tok]
            i += 1
        while i < n and toks[i] == ".":
            if i + 1 < n and toks[i + 1] in _LEAN_STMT_OPEN:
                close = _lean_stmt_matching_close(toks, i + 1)
                arg.extend(toks[i : close + 1])
                i = close + 1
            elif i + 1 < n:
                arg.extend(toks[i : i + 2])
                i += 2
            else:
                arg.append(toks[i])
                i += 1
        args.append(_lean_stmt_strip_outer(arg))
    return head, args


def _lean_eq_sides(tokens: list[str]) -> tuple[str, list[str], list[str]] | None:
    """Extract `("=", lhs, rhs)` or `("≠", lhs, rhs)` from infix `=`/`≠` or prefix `Eq`/`Ne`.

    `=` and `≠` bind tighter than `∧`, `∨`, `→`, and `↔`, and `¬a = b` is `¬(a = b)`, so
    `v = e ∧ Q`, `a = b → c`, and `¬a = b` are not equations (`None`)."""
    toks = _lean_norm_expr_tokens(tokens)
    if not toks or toks[0] in _LEAN_STMT_NOTS or toks[0] in _LEAN_STMT_SCOPE_TOKENS:
        return None
    if (
        _lean_stmt_first_top(
            toks,
            _LEAN_STMT_IFFS | _LEAN_STMT_ARROWS | _LEAN_STMT_ORS | _LEAN_STMT_ANDS | {","},
        )
        is not None
    ):
        return None
    for rel in ("=", "≠"):
        parts = _lean_stmt_split_top(toks, {rel})
        if len(parts) == 2 and parts[0] and parts[1]:
            return rel, _lean_norm_expr_tokens(parts[0]), _lean_norm_expr_tokens(parts[1])
    app = _lean_top_app_args(toks)
    if app is not None:
        head, args = app
        if (head == "Eq" and len(args) == 2) or (head == "@Eq" and len(args) == 3):
            return "=", _lean_norm_expr_tokens(args[-2]), _lean_norm_expr_tokens(args[-1])
        if (head == "Ne" and len(args) == 2) or (head == "@Ne" and len(args) == 3):
            return "≠", _lean_norm_expr_tokens(args[-2]), _lean_norm_expr_tokens(args[-1])
    return None


def _lean_decimal_literal(tokens: list[str]) -> int | None:
    """The value of a single ASCII decimal numeral token (`42`, `042`), else `None`."""
    if len(tokens) == 1 and tokens[0].isascii() and tokens[0].isdigit():
        return int(tokens[0])
    return None


def _lean_antecedent_type(tokens: list[str]) -> list[str]:
    """Underlying proposition/type of an implication antecedent (`(h : P)` -> `P`, else `tokens`)."""
    inner = _lean_stmt_strip_outer(tokens, "({⦃[")
    colon = _lean_stmt_first_top(inner, {":"})
    if colon is not None and inner is not tokens:
        return _lean_strip_binder_default(inner[colon + 1 :])
    return tokens


def _lean_antecedent_truth(tokens: list[str], depth: int) -> str | None:
    """Truth of an implication antecedent, which may be a Pi binder `(h : P)`."""
    return _lean_prop_truth(_lean_antecedent_type(tokens), depth + 1)


def _lean_negated_core(tokens: list[str]) -> tuple[bool, tuple[str, ...]]:
    """`(is_negated, core_tokens)` normalizing `¬P`, `Not P`, and `a ≠ b` against `P` and `a = b`."""
    toks = _lean_norm_expr_tokens(tokens)
    neg = False
    while toks and toks[0] in _LEAN_STMT_NOTS and len(toks) > 1:
        neg = not neg
        toks = _lean_norm_expr_tokens(toks[1:])
    eq_sides = _lean_eq_sides(toks)
    if eq_sides is not None:
        rel, lhs, rhs = eq_sides
        if rel == "≠":
            neg = not neg
        return neg, ("=", *lhs, "=", *rhs)
    return neg, tuple(toks)


def _lean_subst_ident(tokens: list[str], var: str, repl: list[str]) -> list[str]:
    """Substitute free (non-field) occurrences of `var` in `tokens` with `repl`,
    stopping along branches where a nested binder shadows `var`."""
    out: list[str] = []
    i = 0
    n = len(tokens)
    while i < n:
        tok = tokens[i]
        prev = tokens[i - 1] if i > 0 else ""
        if prev != "." and (tok == "∀" or tok in _LEAN_STMT_FORALLS or tok == "∃"):
            comma = _lean_stmt_first_top(tokens, {","}, start=i + 1)
            if comma is not None and var in _lean_quantifier_binder_names(tokens[i + 1 : comma]):
                out.extend(tokens[i:])
                return out
        if prev != "." and tok in ("fun", "λ"):
            arrow = _lean_stmt_first_top(tokens, {"=>", "↦"}, start=i + 1)
            if arrow is not None and var in _lean_quantifier_binder_names(tokens[i + 1 : arrow]):
                out.extend(tokens[i:])
                return out
        if prev != "." and tok in ("let", "have"):
            assign = _lean_stmt_first_top(tokens, {":="}, start=i + 1)
            if assign is not None:
                hdr = tokens[i + 1 : assign]
                hcol = _lean_stmt_first_top(hdr, {":"})
                lhs = hdr[:hcol] if hcol is not None else hdr
                if var in lhs:
                    out.extend(tokens[i : assign + 1])
                    # Substitute inside the RHS of `let var := <val>; <body>`, then stop on `<body>`.
                    nested = 0
                    depth = 0
                    sep = None
                    for k in range(assign + 1, n):
                        tk = tokens[k]
                        pk = tokens[k - 1] if k > 0 else ""
                        if tk in _LEAN_STMT_OPEN:
                            depth += 1
                        elif tk in _LEAN_STMT_CLOSE:
                            depth = max(0, depth - 1)
                        elif depth == 0 and pk != ".":
                            if tk in ("let", "have"):
                                nested += 1
                            elif tk in (";", "in"):
                                if nested > 0:
                                    nested -= 1
                                else:
                                    sep = k
                                    break
                    if sep is not None:
                        out.extend(_lean_subst_ident(tokens[assign + 1 : sep], var, repl))
                        out.extend(tokens[sep:])
                    else:
                        out.extend(_lean_subst_ident(tokens[assign + 1 :], var, repl))
                    return out
        if tok in ("(", "{", "⦃", "["):
            close = _lean_stmt_matching_close(tokens, i)
            inner = tokens[i + 1 : close]
            colon = _lean_stmt_first_top(inner, {":"})
            if colon is not None and close < n:
                bnames = [bt for bt in inner[:colon] if _is_lean_stmt_ident(bt) and bt != "_"]
                if var in bnames and close + 1 < n and tokens[close + 1] in _LEAN_STMT_ARROWS:
                    out.append(tok)
                    out.extend(inner[: colon + 1])
                    out.extend(_lean_subst_ident(inner[colon + 1 :], var, repl))
                    out.extend(tokens[close:])
                    return out
            out.append(tok)
            out.extend(_lean_subst_ident(inner, var, repl))
            if close < n:
                out.append(tokens[close])
            i = close + 1
            continue
        if prev != "." and tok == var:
            out.extend(repl)
        else:
            out.append(tok)
        i += 1
    return out


def _lean_peel_let_have_show(tokens: list[str]) -> list[str]:
    """Peel leading `show T from e`, `let x := v; body` (substituting pure single-ident
    bindings), and `have ... := v; body` wrappers so vacuity and closed-statement checks
    inspect the underlying proposition."""
    toks = _lean_norm_expr_tokens(tokens)
    for _ in range(32):
        if not toks:
            break
        head = toks[0]
        if head == "show":
            from_idx = _lean_stmt_first_top(toks, {"from"}, start=1)
            if from_idx is None or from_idx + 1 >= len(toks):
                break
            toks = _lean_norm_expr_tokens(toks[from_idx + 1 :])
            continue
        if head in ("let", "have"):
            assign = _lean_stmt_first_top(toks, {":="}, start=1)
            if assign is None:
                break
            nested = 0
            depth = 0
            sep: int | None = None
            for k in range(assign + 1, len(toks)):
                tk = toks[k]
                pk = toks[k - 1] if k > 0 else ""
                if tk in _LEAN_STMT_OPEN:
                    depth += 1
                elif tk in _LEAN_STMT_CLOSE:
                    depth = max(0, depth - 1)
                elif depth == 0 and pk != ".":
                    if tk in ("let", "have"):
                        nested += 1
                    elif tk in (";", "in"):
                        if nested > 0:
                            nested -= 1
                        else:
                            sep = k
                            break
            if sep is None or sep + 1 >= len(toks):
                break
            body = toks[sep + 1 :]
            if head == "let":
                hdr = toks[1:assign]
                hcol = _lean_stmt_first_top(hdr, {":"})
                lhs = hdr[:hcol] if hcol is not None else hdr
                val = toks[assign + 1 : sep]
                if (
                    len(lhs) == 1
                    and _is_lean_stmt_ident(lhs[0])
                    and lhs[0] != "_"
                    and len(val) <= 64
                    and _lean_stmt_first_top(val, {";", "in"}) is None
                ):
                    body = _lean_subst_ident(body, lhs[0], ["(", *val, ")"])
            toks = _lean_norm_expr_tokens(body)
            continue
        break
    return toks


def _lean_split_ite(tokens: list[str]) -> tuple[list[str], list[str], list[str]] | None:
    """Split a depth-0 `if <cond> then <t> else <e>` expression."""
    if not tokens or tokens[0] != "if":
        return None
    then_idx = _lean_stmt_first_top(tokens, {"then"}, start=1)
    if then_idx is None or then_idx == 1:
        return None
    nested = 0
    depth = 0
    else_idx: int | None = None
    for k in range(then_idx + 1, len(tokens)):
        tk = tokens[k]
        pk = tokens[k - 1] if k > 0 else ""
        if tk in _LEAN_STMT_OPEN:
            depth += 1
        elif tk in _LEAN_STMT_CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and pk != ".":
            if tk == "if":
                nested += 1
            elif tk == "else":
                if nested > 0:
                    nested -= 1
                else:
                    else_idx = k
                    break
    if else_idx is None or else_idx == then_idx + 1 or else_idx + 1 >= len(tokens):
        return None
    return tokens[1:then_idx], tokens[then_idx + 1 : else_idx], tokens[else_idx + 1 :]


def _lean_split_match_arms(tokens: list[str]) -> list[list[str]] | None:
    """Extract the arm RHS slices of a `| pat => rhs` alternative list at depth 0
    without stopping on `∀` / `∃` / `fun` / `let` / `if` inside an arm RHS."""
    if not tokens or tokens[0] != "|":
        return None
    arms: list[list[str]] = []
    cur: list[str] = []
    depth = 0
    for idx in range(1, len(tokens)):
        tok = tokens[idx]
        if tok in _LEAN_STMT_OPEN:
            depth += 1
        elif tok in _LEAN_STMT_CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and tok == "|":
            arms.append(cur)
            cur = []
            continue
        cur.append(tok)
    arms.append(cur)
    rhs_list: list[list[str]] = []
    for arm in arms:
        arrow = _lean_stmt_first_top(arm, {"=>", "↦"})
        if arrow is None or arrow + 1 >= len(arm):
            return None
        rhs_list.append(arm[arrow + 1 :])
    return rhs_list or None


def _lean_prop_truth(tokens: list[str], depth: int = 0) -> str | None:
    """`"true"` / `"false"` when the proposition `tokens` is syntactically trivially
    true / false (`True`, `¬False`, `x = x`, `0 = 1`, `P ∨ ¬P`, `P ∧ ¬P`, `False → P`,
    `∀ (h : False), P`, `∃ x, True`, `∃ x, e = x`, ...), else `None`."""
    if depth > 64:
        return None
    toks = _lean_peel_let_have_show(tokens)
    if not toks:
        return None
    head = toks[0]
    if head == "if":
        ite = _lean_split_ite(toks)
        if ite is None:
            return None
        cond_s, then_s, else_s = ite
        ct = _lean_prop_truth(cond_s, depth + 1)
        if ct == _LEAN_TRUTH_TRUE:
            return _lean_prop_truth(then_s, depth + 1)
        if ct == _LEAN_TRUTH_FALSE:
            return _lean_prop_truth(else_s, depth + 1)
        tt = _lean_prop_truth(then_s, depth + 1)
        et = _lean_prop_truth(else_s, depth + 1)
        if tt is not None and tt == et:
            return tt
        return None
    if head == "match":
        with_idx = _lean_stmt_first_top(toks, {"with"}, start=1)
        if with_idx is None or with_idx + 1 >= len(toks):
            return None
        arm_rhss = _lean_split_match_arms(toks[with_idx + 1 :])
        if not arm_rhss:
            return None
        arm_truths = {_lean_prop_truth(rhs, depth + 1) for rhs in arm_rhss}
        if len(arm_truths) == 1:
            return arm_truths.pop()
        return None
    if head == "∀" or head in _LEAN_STMT_FORALLS or head == "∃":
        comma = _lean_stmt_first_top(toks, {","}, start=1)
        if comma is None:
            return None
        binder_slice = toks[1:comma]
        binder_truths = [
            _lean_prop_truth(t, depth + 1) for t in _lean_quantifier_binder_types(binder_slice)
        ]
        body_slice = _lean_peel_let_have_show(toks[comma + 1 :])
        body = _lean_prop_truth(body_slice, depth + 1)
        if head == "∃":
            if _LEAN_TRUTH_FALSE in binder_truths or body == _LEAN_TRUTH_FALSE:
                return _LEAN_TRUTH_FALSE
            if body == _LEAN_TRUTH_TRUE:
                return _LEAN_TRUTH_TRUE
            bound_vars = set(_lean_quantifier_binder_names(binder_slice))
            eq_sides = _lean_eq_sides(body_slice)
            if bound_vars and eq_sides is not None and eq_sides[0] == "=":
                _, lhs, rhs = eq_sides
                if (len(lhs) == 1 and lhs[0] in bound_vars and lhs[0] not in rhs) or (
                    len(rhs) == 1 and rhs[0] in bound_vars and rhs[0] not in lhs
                ):
                    return _LEAN_TRUTH_TRUE
            return None
        if _LEAN_TRUTH_FALSE in binder_truths or body == _LEAN_TRUTH_TRUE:
            return _LEAN_TRUTH_TRUE
        return None
    if head in _LEAN_STMT_SCOPE_TOKENS:
        return None
    app = _lean_top_app_args(toks)
    parts = _lean_stmt_split_top(toks, _LEAN_STMT_IFFS)
    if len(parts) == 1 and app is not None and app[0] == "Iff" and len(app[1]) == 2:
        parts = app[1]
    if len(parts) > 1:
        if len(parts) != 2 or not parts[0] or not parts[1]:
            return None
        if _lean_norm_expr_tokens(parts[0]) == _lean_norm_expr_tokens(parts[1]):
            return _LEAN_TRUTH_TRUE
        lhs = _lean_prop_truth(parts[0], depth + 1)
        rhs = _lean_prop_truth(parts[1], depth + 1)
        if lhs is not None and rhs is not None:
            return _LEAN_TRUTH_TRUE if lhs == rhs else _LEAN_TRUTH_FALSE
        return None
    parts = _lean_stmt_split_top(toks, _LEAN_STMT_ARROWS)
    if len(parts) > 1:
        antecedents = [_lean_antecedent_truth(p, depth) for p in parts[:-1]]
        conclusion = _lean_prop_truth(parts[-1], depth + 1)
        if _LEAN_TRUTH_FALSE in antecedents or conclusion == _LEAN_TRUTH_TRUE:
            return _LEAN_TRUTH_TRUE
        if all(a == _LEAN_TRUTH_TRUE for a in antecedents) and conclusion == _LEAN_TRUTH_FALSE:
            return _LEAN_TRUTH_FALSE
        return None
    for seps, app_head, any_value, all_value in (
        (_LEAN_STMT_ORS, "Or", _LEAN_TRUTH_TRUE, _LEAN_TRUTH_FALSE),
        (_LEAN_STMT_ANDS, "And", _LEAN_TRUTH_FALSE, _LEAN_TRUTH_TRUE),
    ):
        parts = _lean_stmt_split_top(toks, seps)
        if len(parts) == 1 and app is not None and app[0] == app_head and len(app[1]) == 2:
            parts = app[1]
        if len(parts) > 1:
            truths = [_lean_prop_truth(p, depth + 1) for p in parts]
            if any_value in truths:
                return any_value
            if all(t == all_value for t in truths):
                return all_value
            cores = {_lean_negated_core(p) for p in parts if p}
            if any((not neg, core) in cores for neg, core in cores):
                return any_value
            return None
    if head in _LEAN_STMT_NOTS and len(toks) > 1:
        inner = _lean_prop_truth(toks[1:], depth + 1)
        return {_LEAN_TRUTH_TRUE: _LEAN_TRUTH_FALSE, _LEAN_TRUTH_FALSE: _LEAN_TRUTH_TRUE}.get(
            inner or ""
        )
    eq_sides = _lean_eq_sides(toks)
    if eq_sides is not None:
        rel, lhs_e, rhs_e = eq_sides
        lhs_lit, rhs_lit = _lean_decimal_literal(lhs_e), _lean_decimal_literal(rhs_e)
        if lhs_e == rhs_e or (lhs_lit is not None and lhs_lit == rhs_lit):
            return _LEAN_TRUTH_TRUE if rel == "=" else _LEAN_TRUTH_FALSE
        # Distinct bare literals differ (bare numerals default to `Nat`; `@Eq T a b`
        # may fix a type, such as `Fin 2`, in which they wrap around).
        both_int_lits = lhs_lit is not None and rhs_lit is not None and toks[0] != "@"
        both_bool_lits = (
            len(lhs_e) == 1
            and len(rhs_e) == 1
            and lhs_e[0] in ("true", "false")
            and rhs_e[0] in ("true", "false")
        )
        if both_int_lits or both_bool_lits:
            return _LEAN_TRUTH_FALSE if rel == "=" else _LEAN_TRUTH_TRUE
    if app is not None:
        a_head, a_args = app
        if a_head in ("ULift", "PLift") and len(a_args) == 1:
            return _lean_prop_truth(a_args[0], depth + 1)
        if a_head == "Fin" and a_args == [["0"]]:
            return _LEAN_TRUTH_FALSE
    if toks in (["True"], ["Unit"], ["PUnit"]):
        return _LEAN_TRUTH_TRUE
    if toks in (["False"], ["Empty"], ["PEmpty"]):
        return _LEAN_TRUTH_FALSE
    return None


def _lean_collect_hyp_cores(
    prop_list: list[list[str]], cores: set[tuple[bool, tuple[str, ...]]], depth: int = 0
) -> bool:
    """Add `prop_list` (splitting top-level conjunctions) to `cores`. Returns `True`
    immediately if any hypothesis is trivially false or contradicts another."""
    if depth > 64:
        return False
    for raw in prop_list:
        toks = _lean_peel_let_have_show(raw)
        if not toks:
            continue
        if _lean_prop_truth(toks, depth + 1) == _LEAN_TRUTH_FALSE:
            return True
        conj = _lean_stmt_split_top(toks, _LEAN_STMT_ANDS)
        app = _lean_top_app_args(toks) if len(conj) == 1 else None
        if len(conj) == 1 and app is not None and app[0] == "And" and len(app[1]) == 2:
            conj = app[1]
        if len(conj) > 1 and _lean_collect_hyp_cores(conj, cores, depth + 1):
            return True
        neg, core = _lean_negated_core(toks)
        if (not neg, core) in cores:
            return True
        cores.add((neg, core))
    return False


def _lean_stmt_tautological_under_hyps(
    tokens: list[str], hyp_cores: set[tuple[bool, tuple[str, ...]]], depth: int = 0
) -> bool:
    """True when `tokens` is trivially proved from `hyp_cores` (e.g. `(h : P) : P`,
    `P → P`, `P ∧ Q → P`, `(h : P) : P ∨ Q`, or contradictory hypotheses `P` and `¬P`).

    A `∀` or Pi binder shadows the outer hypotheses that mention the names it binds:
    `(h : P x) : ∀ x, P x` does not follow from `h`."""
    if depth > 64:
        return False
    toks = _lean_peel_let_have_show(tokens)
    if not toks:
        return False
    if _lean_prop_truth(toks, depth + 1) == _LEAN_TRUTH_TRUE:
        return True
    if _lean_negated_core(toks) in hyp_cores:
        return True
    if toks[0] == "if":
        ite = _lean_split_ite(toks)
        if ite is not None:
            cond_s, then_s, else_s = ite
            then_cores = set(hyp_cores)
            then_ok = _lean_collect_hyp_cores([cond_s], then_cores, depth + 1) or (
                _lean_stmt_tautological_under_hyps(then_s, then_cores, depth + 1)
            )
            else_cores = set(hyp_cores)
            else_ok = _lean_collect_hyp_cores([["¬", "(", *cond_s, ")"]], else_cores, depth + 1) or (
                _lean_stmt_tautological_under_hyps(else_s, else_cores, depth + 1)
            )
            if then_ok and else_ok:
                return True
    if toks[0] == "match":
        with_idx = _lean_stmt_first_top(toks, {"with"}, start=1)
        if with_idx is not None and with_idx + 1 < len(toks):
            arm_rhss = _lean_split_match_arms(toks[with_idx + 1 :])
            if arm_rhss and all(
                _lean_stmt_tautological_under_hyps(rhs, hyp_cores, depth + 1) for rhs in arm_rhss
            ):
                return True
    if toks[0] == "∀" or toks[0] in _LEAN_STMT_FORALLS:
        comma = _lean_stmt_first_top(toks, {","}, start=1)
        if comma is not None:
            binders = toks[1:comma]
            bound = set(_lean_quantifier_binder_names(binders))
            sub = {core for core in hyp_cores if not bound.intersection(core[1])}
            if _lean_collect_hyp_cores(_lean_quantifier_binder_types(binders), sub, depth + 1):
                return True
            return _lean_stmt_tautological_under_hyps(toks[comma + 1 :], sub, depth + 1)
    arrows = _lean_stmt_split_top(toks, _LEAN_STMT_ARROWS)
    if len(arrows) > 1:
        bound = {name for p in arrows[:-1] for name in _lean_binder_group_names(p)}
        sub = {core for core in hyp_cores if not bound.intersection(core[1])}
        ant_types = [_lean_antecedent_type(p) for p in arrows[:-1]]
        if _lean_collect_hyp_cores(ant_types, sub, depth + 1):
            return True
        return _lean_stmt_tautological_under_hyps(arrows[-1], sub, depth + 1)
    app = _lean_top_app_args(toks)
    disj = _lean_stmt_split_top(toks, _LEAN_STMT_ORS)
    if len(disj) == 1 and app is not None and app[0] == "Or" and len(app[1]) == 2:
        disj = app[1]
    if len(disj) > 1:
        return any(_lean_stmt_tautological_under_hyps(d, hyp_cores, depth + 1) for d in disj)
    conj = _lean_stmt_split_top(toks, _LEAN_STMT_ANDS)
    if len(conj) == 1 and app is not None and app[0] == "And" and len(app[1]) == 2:
        conj = app[1]
    if len(conj) > 1:
        return all(_lean_stmt_tautological_under_hyps(c, hyp_cores, depth + 1) for c in conj)
    return False


def _lean_prop_has_hole(tokens: list[str], depth: int = 0) -> bool:
    """True when a proposition or binder type leaves a wildcard `_` hole at type/equality
    level (`: _`, `: id _`, `(h : _)`, `: P ∧ _`, `: lhs = _`), without rejecting bound
    wildcard names `(_ : T)` or `match ... | _ => ...` arms."""
    if depth > 64:
        return False
    toks = _lean_norm_expr_tokens(tokens)
    if not toks:
        return False
    if toks == ["_"]:
        return True
    if toks[0] == "∀" or toks[0] in _LEAN_STMT_FORALLS or toks[0] == "∃":
        comma = _lean_stmt_first_top(toks, {","}, start=1)
        if comma is not None:
            return any(
                _lean_prop_has_hole(t, depth + 1)
                for t in _lean_quantifier_binder_types(toks[1:comma])
            ) or _lean_prop_has_hole(toks[comma + 1 :], depth + 1)
    for seps in (_LEAN_STMT_IFFS, _LEAN_STMT_ARROWS, _LEAN_STMT_ORS, _LEAN_STMT_ANDS):
        parts = _lean_stmt_split_top(toks, seps)
        if len(parts) > 1:
            if seps is _LEAN_STMT_ARROWS:
                parts = [_lean_antecedent_type(p) for p in parts[:-1]] + [parts[-1]]
            return any(_lean_prop_has_hole(p, depth + 1) for p in parts)
    if toks[0] in _LEAN_STMT_NOTS and len(toks) > 1:
        return _lean_prop_has_hole(toks[1:], depth + 1)
    eq_sides = _lean_eq_sides(toks)
    if eq_sides is not None:
        return eq_sides[1] == ["_"] or eq_sides[2] == ["_"]
    return False


def _lean_prop_has_tactic_type(tokens: list[str], depth: int = 0) -> bool:
    """True when a proposition or binder type is synthesized by `type_of%` or a head `by`
    tactic block (without rejecting dependent proof arguments like `arr[i]'(by omega)` or
    auto-param defaults `(h : P := by rintro ⟨⟩)`)."""
    if depth > 64:
        return False
    if "type_of" in tokens:
        return True
    toks = _lean_norm_expr_tokens(tokens)
    if not toks:
        return False
    if toks[0] == "by":
        return True
    if toks[0] == "∀" or toks[0] in _LEAN_STMT_FORALLS or toks[0] == "∃":
        comma = _lean_stmt_first_top(toks, {","}, start=1)
        if comma is not None:
            return any(
                _lean_prop_has_tactic_type(t, depth + 1)
                for t in _lean_quantifier_binder_types(toks[1:comma])
            ) or _lean_prop_has_tactic_type(toks[comma + 1 :], depth + 1)
    for seps in (_LEAN_STMT_IFFS, _LEAN_STMT_ARROWS, _LEAN_STMT_ORS, _LEAN_STMT_ANDS):
        parts = _lean_stmt_split_top(toks, seps)
        if len(parts) > 1:
            if seps is _LEAN_STMT_ARROWS:
                parts = [_lean_antecedent_type(p) for p in parts[:-1]] + [parts[-1]]
            return any(_lean_prop_has_tactic_type(p, depth + 1) for p in parts)
    if toks[0] in _LEAN_STMT_NOTS and len(toks) > 1:
        return _lean_prop_has_tactic_type(toks[1:], depth + 1)
    return False


def _is_lean_stmt_ident(tok: str) -> bool:
    if tok.startswith("«") and tok.endswith("»"):
        return not tok.startswith("«`")
    return bool(tok) and (tok[0].isalpha() or (tok[0] == "_" and len(tok) > 1))


# Tokens that end the explicit arguments of an application at bracket depth 0.
_LEAN_APP_ARG_STOPS = frozenset(
    _LEAN_STMT_ARROWS
    | _LEAN_STMT_IFFS
    | _LEAN_STMT_ANDS
    | _LEAN_STMT_ORS
    | _LEAN_STMT_SCOPE_TOKENS
    | _LEAN_STMT_INFIX_OPS
    | {",", ":", ":=", "|", "=>", "↦", ";", "then", "else", "with", "from"}
)
# Tokens after which a (sub)expression, and so an application head, starts.
_LEAN_EXPR_START_AFTER = frozenset(
    _LEAN_STMT_OPEN
    | _LEAN_STMT_ARROWS
    | _LEAN_STMT_IFFS
    | _LEAN_STMT_ANDS
    | _LEAN_STMT_ORS
    | _LEAN_STMT_NOTS
    | _LEAN_STMT_INFIX_OPS
    | {",", ":", ":=", "|", "=>", "↦", ";", "then", "else", "show", "from"}
)

_PropDefSpec = tuple[int, int, list[str]]


def _lean_read_stmt_qname(tokens: list[str], start: int) -> tuple[bool, str, int] | None:
    """Read `@?seg(.seg)*` at `tokens[start]`, returning `(has_at, last_seg, end_idx)`."""
    n = len(tokens)
    has_at = start < n and tokens[start] == "@"
    j = start + 1 if has_at else start
    if j >= n or not _is_lean_stmt_ident(tokens[j]):
        return None
    last = tokens[j]
    k = j + 1
    while k + 1 < n and tokens[k] == "." and _is_lean_stmt_ident(tokens[k + 1]):
        last = tokens[k + 1]
        k += 2
    if k < n and tokens[k] == ".":
        return None
    return has_at, last, k


def _lean_inline_prop_defs(tokens: list[str], defs: dict[str, _PropDefSpec]) -> list[str]:
    """Replace every application `@?Ns.Def arg*` (including bare `(Ns.Def) arg*`,
    `arg |> Ns.Def`, and 0-arg constants `A` inside prefix calls like `Or A P`), where
    `Def` reduces to a fixed proposition (`defs`: name -> `(explicit_arity, total_arity,
    replacement_tokens)`), by that proposition. Binders that shadow `Def` do not stop the
    replacement (fail closed)."""
    if not defs or not tokens:
        return tokens
    # Pass 1: unwrap bare `(@?Ns.Def)` parens and desugar `<atom> |> @?Ns.Def` pipes for
    # definitions in `defs`.
    pre: list[str] = []
    i = 0
    n = len(tokens)
    while i < n:
        if tokens[i] == "(":
            qn = _lean_read_stmt_qname(tokens, i + 1)
            if qn is not None and qn[1] in defs and qn[2] < n and tokens[qn[2]] == ")":
                pre.extend(tokens[i + 1 : qn[2]])
                i = qn[2] + 1
                continue
        if tokens[i] == "|>" and pre:
            qn = _lean_read_stmt_qname(tokens, i + 1)
            if qn is not None and qn[1] in defs and defs[qn[1]][1] >= 1:
                # Pop the preceding atomic argument (with any trailing `.field` chain) from `pre`.
                atom_end = len(pre)
                pos = atom_end - 1
                while pos >= 2 and pre[pos - 1] == ".":
                    if pre[pos] in _LEAN_STMT_CLOSE:
                        open_idx = pos - 1
                        bal = 0
                        for m in range(pos, -1, -1):
                            if pre[m] in _LEAN_STMT_CLOSE:
                                bal += 1
                            elif pre[m] in _LEAN_STMT_OPEN:
                                bal -= 1
                                if bal == 0:
                                    open_idx = m
                                    break
                        if open_idx >= 1 and pre[open_idx - 1] == ".":
                            pos = open_idx - 2
                            continue
                    pos -= 2
                if pos >= 0 and pre[pos] in _LEAN_STMT_CLOSE:
                    bal = 0
                    for m in range(pos, -1, -1):
                        if pre[m] in _LEAN_STMT_CLOSE:
                            bal += 1
                        elif pre[m] in _LEAN_STMT_OPEN:
                            bal -= 1
                            if bal == 0:
                                pos = m
                                break
                atom = pre[pos:atom_end]
                del pre[pos:atom_end]
                pre.extend(tokens[i + 1 : qn[2]])
                pre.extend(atom)
                i = qn[2]
                continue
        pre.append(tokens[i])
        i += 1

    # Pass 2: inline applications of `defs` up to their explicit (or `@`-total) arity.
    out: list[str] = []
    m = len(pre)
    i = 0
    while i < m:
        prev = pre[i - 1] if i > 0 else ""
        if prev != ".":
            qn = _lean_read_stmt_qname(pre, i)
            if qn is not None and qn[1] in defs:
                has_at, last, k = qn
                exp_arity, tot_arity, repl = defs[last]
                max_args = tot_arity if has_at else exp_arity
                if max_args == 0 or i == 0 or prev in _LEAN_EXPR_START_AFTER:
                    consumed = 0
                    while (
                        consumed < max_args
                        and k < m
                        and pre[k] not in _LEAN_STMT_CLOSE
                        and pre[k] not in _LEAN_APP_ARG_STOPS
                    ):
                        k = _lean_stmt_matching_close(pre, k) + 1 if pre[k] in _LEAN_STMT_OPEN else k + 1
                        while k < m and pre[k] == ".":
                            if k + 1 < m and pre[k + 1] in _LEAN_STMT_OPEN:
                                k = _lean_stmt_matching_close(pre, k + 1) + 1
                            elif k + 1 < m:
                                k += 2
                            else:
                                k += 1
                        consumed += 1
                    out.extend(repl)
                    i = min(k, m)
                    continue
        out.append(pre[i])
        i += 1
    return out


def _lean_header_binder_arities(tokens: list[str]) -> tuple[int, int]:
    """`(explicit_count, total_count)` of bracketed binder groups in `tokens`."""
    exp = 0
    tot = 0
    i = 0
    while i < len(tokens):
        tok = tokens[i]
        if tok in ("(", "{", "⦃", "["):
            close = _lean_stmt_matching_close(tokens, i)
            inner = tokens[i + 1 : close]
            colon = _lean_stmt_first_top(inner, {":"})
            if colon is not None:
                cnt = max(1, sum(1 for bt in inner[:colon] if _is_lean_stmt_ident(bt)))
                tot += cnt
                if tok == "(":
                    exp += cnt
            elif inner and inner[0] in ("(", "{", "⦃", "["):
                sub_e, sub_t = _lean_header_binder_arities(inner)
                exp += sub_e
                tot += sub_t
            elif tok == "[":
                tot += 1
            i = close + 1
        else:
            i += 1
    return exp, tot


def _lean_decl_arities_and_hyps(
    sig_tokens: list[str], body_tokens: list[str]
) -> tuple[int, int, bool, list[list[str]], set[str]]:
    """Return `(explicit_arity, total_arity, ends_in_prop, binder_hyp_types, bound_param_names)`
    for a `def` / `abbrev` / `structure` / `inductive` header."""
    colon = _lean_stmt_first_top(sig_tokens, {":"})
    hdr = sig_tokens[:colon] if colon is not None else sig_tokens
    exp, tot = _lean_header_binder_arities(hdr)
    hyp_types = list(_lean_bracket_binder_types(hdr))
    params = set(_lean_binder_group_names(hdr))
    ends_in_prop = False
    if colon is not None:
        ret = _lean_norm_expr_tokens(sig_tokens[colon + 1 :])
        while ret:
            if ret[0] == "∀" or ret[0] in _LEAN_STMT_FORALLS:
                comma = _lean_stmt_first_top(ret, {","}, start=1)
                if comma is None:
                    break
                bslice = ret[1:comma]
                b_exp, b_tot = _lean_header_binder_arities(bslice)
                bcol = _lean_stmt_first_top(bslice, {":"})
                if bcol is not None:
                    prefix = bslice[:bcol]
                    unbr = sum(
                        1
                        for idx, bt in enumerate(prefix)
                        if _is_lean_stmt_ident(bt) and (idx == 0 or prefix[idx - 1] not in ("(", "{", "⦃", "["))
                    )
                    unbr = max(1, unbr) if not b_tot else unbr
                    b_exp += unbr
                    b_tot += unbr
                elif not b_tot:
                    unbr = max(1, sum(1 for bt in bslice if _is_lean_stmt_ident(bt)))
                    b_exp += unbr
                    b_tot += unbr
                exp += b_exp
                tot += b_tot
                hyp_types.extend(_lean_quantifier_binder_types(bslice))
                params.update(_lean_quantifier_binder_names(bslice))
                ret = _lean_norm_expr_tokens(ret[comma + 1 :])
                continue
            arrows = _lean_stmt_split_top(ret, _LEAN_STMT_ARROWS)
            if len(arrows) > 1:
                for ant in arrows[:-1]:
                    stripped_ant = _lean_stmt_strip_outer(ant)
                    if stripped_ant and stripped_ant[0] in ("{", "⦃", "["):
                        _, a_tot = _lean_header_binder_arities(stripped_ant)
                        tot += max(1, a_tot)
                    else:
                        a_exp, a_tot = _lean_header_binder_arities(ant)
                        if a_tot and stripped_ant and stripped_ant[0] == "(":
                            exp += a_exp
                            tot += a_tot
                        else:
                            exp += 1
                            tot += 1
                    hyp_types.append(_lean_antecedent_type(ant))
                    params.update(_lean_binder_group_names(ant))
                ret = _lean_norm_expr_tokens(arrows[-1])
                continue
            break
        ret_core = _lean_stmt_strip_outer(ret)
        ends_in_prop = ret_core == ["Prop"]
    else:
        b = _lean_norm_expr_tokens(body_tokens)
        while b and b[0] == "fun" and not (len(b) > 1 and b[1] == "|"):
            arrow = _lean_stmt_first_top(b, {"=>", "↦"}, start=1)
            if arrow is None:
                break
            fslice = b[1:arrow]
            f_exp, f_tot = _lean_header_binder_arities(fslice)
            i = 0
            while i < len(fslice):
                if fslice[i] in _LEAN_STMT_OPEN:
                    i = _lean_stmt_matching_close(fslice, i) + 1
                    continue
                if fslice[i] == ":":
                    break
                if _is_lean_stmt_ident(fslice[i]):
                    f_exp += 1
                    f_tot += 1
                i += 1
            exp += max(1, f_exp) if not f_tot else f_exp
            tot += max(1, f_tot)
            params.update(t for t in fslice if _is_lean_stmt_ident(t) and t != "_")
            b = _lean_norm_expr_tokens(b[arrow + 1 :])
        if b and b[0] == "|":
            arrow = _lean_stmt_first_top(b, {"=>", "↦"}, start=1)
            if arrow is not None and arrow > 1:
                pats = _lean_stmt_split_top(b[1:arrow], {","})
                exp += len(pats)
                tot += len(pats)
    return exp, tot, ends_in_prop, hyp_types, params


def _lean_prop_def_body_truth(
    body_tokens: list[str],
    defs: dict[str, _PropDefSpec],
    *,
    allow_prop_tautology: bool = True,
    hyp_types: list[list[str]] | None = None,
) -> str | None:
    """Truth of a definition body that is trivially true / false for every argument:
    directly (`:= True`, `:= p = p`, `:= stepOk p → stepOk p`, `:= by exact True`,
    `:= by trivial`), under `fun x =>` binders, or across all arms of `match` / `|`."""
    toks = _lean_peel_let_have_show(_lean_inline_prop_defs(body_tokens, defs))
    hyps = list(hyp_types or [])
    for _ in range(64):
        if allow_prop_tautology and toks and toks[0] == "by":
            rest = _lean_norm_expr_tokens(toks[1:])
            if rest == ["trivial"]:
                return _LEAN_TRUTH_TRUE
            if len(rest) >= 2 and rest[0] in ("exact", "apply"):
                toks = _lean_peel_let_have_show(rest[1:])
                continue
        if toks and toks[0] == "match":
            with_idx = _lean_stmt_first_top(toks, {"with"}, start=1)
            if with_idx is None:
                return None
            toks = toks[with_idx + 1 :]
        elif len(toks) > 1 and toks[0] == "fun" and toks[1] == "|":
            toks = toks[1:]
        elif toks and toks[0] == "fun":
            arrow = _lean_stmt_first_top(toks, {"=>", "↦"}, start=1)
            if arrow is None:
                return None
            fslice = toks[1:arrow]
            hyps.extend(_lean_quantifier_binder_types(fslice))
            toks = _lean_peel_let_have_show(toks[arrow + 1 :])
            continue
        if toks and toks[0] == "|":
            arm_rhss = _lean_split_match_arms(toks)
            if not arm_rhss:
                return None
            truths = {
                _lean_prop_def_body_truth(
                    rhs,
                    {},
                    allow_prop_tautology=allow_prop_tautology,
                    hyp_types=hyps,
                )
                for rhs in arm_rhss
            }
            if len(truths) != 1:
                return None
            return truths.pop()
        direct = _lean_prop_truth(toks)
        if direct is not None:
            return direct
        if allow_prop_tautology:
            hyp_cores: set[tuple[bool, tuple[str, ...]]] = set()
            if _lean_collect_hyp_cores(hyps, hyp_cores) or _lean_stmt_tautological_under_hyps(
                toks, hyp_cores
            ):
                return _LEAN_TRUTH_TRUE
        return None
    return None


_LEAN_PROP_TYPED_BODY_MARKERS = frozenset(
    {
        "=",
        "≠",
        "<",
        ">",
        "≤",
        "≥",
        "∧",
        "∨",
        "→",
        "↔",
        "¬",
        "∀",
        "∃",
        "Eq",
        "Ne",
        "HEq",
        "And",
        "Or",
        "Iff",
        "Not",
        "True",
        "False",
    }
)


def _lean_prop_def_replacement(
    sig_tokens: list[str], body_tokens: list[str], defs: dict[str, _PropDefSpec]
) -> _PropDefSpec | None:
    """`(explicit_arity, total_arity, replacement_tokens)` for `_lean_inline_prop_defs`
    when `<sig> := <body>` reduces to `True` / `False` for every argument or is a
    `Prop`-valued definition whose body ignores all parameters (`0 < 1`), else `None`."""
    colon = _lean_stmt_first_top(sig_tokens, {":"})
    exp_arity, tot_arity, ends_in_prop, hyp_types, params = _lean_decl_arities_and_hyps(
        sig_tokens, body_tokens
    )
    allow_prop = colon is None or ends_in_prop
    truth = _lean_prop_def_body_truth(
        body_tokens, defs, allow_prop_tautology=allow_prop, hyp_types=hyp_types
    )
    if truth == _LEAN_TRUTH_FALSE:
        return (exp_arity, tot_arity, ["False"])
    if truth == _LEAN_TRUTH_TRUE and allow_prop:
        return (exp_arity, tot_arity, ["True"])
    body = _lean_peel_let_have_show(_lean_inline_prop_defs(body_tokens, defs))
    for _ in range(64):
        if allow_prop and len(body) >= 3 and body[0] == "by" and body[1] in ("exact", "apply"):
            body = _lean_peel_let_have_show(body[2:])
            continue
        if not body or body[0] != "fun":
            break
        arrow = _lean_stmt_first_top(body, {"=>", "↦"}, start=1)
        if arrow is None:
            return None
        params.update(t for t in body[1:arrow] if _is_lean_stmt_ident(t))
        body = _lean_peel_let_have_show(body[arrow + 1 :])
    if colon is not None:
        if not ends_in_prop:
            return None
    else:
        if not params or not any(t in _LEAN_PROP_TYPED_BODY_MARKERS for t in body):
            return None
    if (
        not body
        or body[0] in ("|", "match", "by", "fun")
        or "where" in body
        or any(t in params for t in body if _is_lean_stmt_ident(t))
    ):
        return None
    return (exp_arity, tot_arity, ["(", *body, ")"])


def _lean_structure_or_inductive_prop_def(
    kind: str,
    sig_tokens: list[str],
    body_tokens: list[str],
    defs: dict[str, _PropDefSpec],
) -> _PropDefSpec | None:
    """Detect vacuous `structure ... : Prop` (0 fields or all-`True` fields -> `True`) and
    uninhabited constructor-less `inductive ...` (0 `|` constructors -> `False`)."""
    exp_arity, tot_arity, ends_in_prop, _, _ = _lean_decl_arities_and_hyps(sig_tokens, [])
    rest = list(body_tokens)
    if rest and rest[0] == "where":
        rest = rest[1:]
    deriv = _lean_stmt_first_top(rest, {"deriving"})
    if deriv is not None:
        rest = rest[:deriv]
    if kind == "inductive":
        if "|" not in rest:
            return (exp_arity, tot_arity, ["False"])
        return None
    if kind == "structure" and ends_in_prop and "extends" not in sig_tokens:
        if ":" not in rest:
            return (exp_arity, tot_arity, ["True"])
        # Check if every `field : FieldType` in `structure ... : Prop where` is trivially `True`.
        inlined_rest = _lean_inline_prop_defs(rest, defs)
        depth = 0
        colons: list[int] = []
        for idx, tk in enumerate(inlined_rest):
            if tk in _LEAN_STMT_OPEN:
                depth += 1
            elif tk in _LEAN_STMT_CLOSE:
                depth = max(0, depth - 1)
            elif depth == 0 and tk == ":":
                colons.append(idx)
        if colons and len(colons) == 1:
            ftype = _lean_strip_binder_default(inlined_rest[colons[0] + 1 :])
            if _lean_prop_truth(ftype) == _LEAN_TRUTH_TRUE:
                return (exp_arity, tot_arity, ["True"])
    return None


def _lean_inner_bound_names(tokens: list[str]) -> set[str]:
    """Collect bound variable names introduced inside an expression (`∀`, `∃`, `fun`,
    `let`, `have`, and dependent Pi `(x : T) → ...`)."""
    names: set[str] = set()
    i = 0
    n = len(tokens)
    while i < n:
        tok = tokens[i]
        prev = tokens[i - 1] if i > 0 else ""
        if prev != "." and (tok == "∀" or tok in _LEAN_STMT_FORALLS or tok == "∃"):
            comma = _lean_stmt_first_top(tokens, {","}, start=i + 1)
            if comma is not None:
                names.update(_lean_quantifier_binder_names(tokens[i + 1 : comma]))
        elif prev != "." and tok in ("fun", "λ"):
            arrow = _lean_stmt_first_top(tokens, {"=>", "↦"}, start=i + 1)
            if arrow is not None:
                names.update(_lean_quantifier_binder_names(tokens[i + 1 : arrow]))
        elif prev != "." and tok in ("let", "have"):
            assign = _lean_stmt_first_top(tokens, {":="}, start=i + 1)
            if assign is not None:
                hdr = tokens[i + 1 : assign]
                hcol = _lean_stmt_first_top(hdr, {":"})
                lhs = hdr[:hcol] if hcol is not None else hdr
                names.update(bt for bt in lhs if _is_lean_stmt_ident(bt) and bt != "_")
        elif tok in ("(", "{", "⦃", "["):
            close = _lean_stmt_matching_close(tokens, i)
            inner = tokens[i + 1 : close]
            if close + 1 < n and tokens[close + 1] in _LEAN_STMT_ARROWS:
                colon = _lean_stmt_first_top(inner, {":"})
                if colon is not None:
                    names.update(bt for bt in inner[:colon] if _is_lean_stmt_ident(bt) and bt != "_")
            names.update(_lean_inner_bound_names(inner))
            i = close + 1
            continue
        i += 1
    return names


def _lean_prune_trivial_subprops(tokens: list[str], depth: int = 0) -> list[str]:
    """Remove syntactically trivially true / false sub-clauses (`(0 < 1) ∧ (x = x)` ->
    `0 < 1`, `(P ∧ False) ∨ (0 < 1)` -> `0 < 1`, `(x = x) → (0 < 1)` -> `0 < 1`) so
    domain identifiers inside vacuous padding cannot mask a closed trivial statement."""
    if depth > 64:
        return tokens
    toks = _lean_peel_let_have_show(tokens)
    if not toks or _lean_prop_truth(toks) is not None:
        return []
    app = _lean_top_app_args(toks)
    for seps, app_head in ((_LEAN_STMT_IFFS, "Iff"), (_LEAN_STMT_ORS, "Or"), (_LEAN_STMT_ANDS, "And")):
        parts = _lean_stmt_split_top(toks, seps)
        if len(parts) == 1 and app is not None and app[0] == app_head and len(app[1]) == 2:
            parts = app[1]
        if len(parts) > 1:
            out: list[str] = []
            for p in parts:
                out.extend(_lean_prune_trivial_subprops(p, depth + 1))
            return out
    arrows = _lean_stmt_split_top(toks, _LEAN_STMT_ARROWS)
    if len(arrows) > 1:
        out = []
        for ant in arrows[:-1]:
            if _lean_antecedent_truth(ant, depth) is None:
                out.extend(_lean_prune_trivial_subprops(_lean_antecedent_type(ant), depth + 1))
        out.extend(_lean_prune_trivial_subprops(arrows[-1], depth + 1))
        return out
    if toks[0] in _LEAN_STMT_NOTS and len(toks) > 1:
        return _lean_prune_trivial_subprops(toks[1:], depth + 1)
    return toks


def _lean_has_active_domain_ident(sig_tokens: list[str], var_tokens: list[str]) -> bool:
    """True when the non-vacuous statement of `sig_tokens` (or the types of binders whose
    bound variables participate in the conclusion) names at least one free domain
    identifier outside `_LEAN_STMT_LOGICAL_IDENTS`."""
    colon = _lean_stmt_first_top(sig_tokens, {":"})
    own_hdr = sig_tokens[:colon] if colon is not None else sig_tokens
    body = _lean_peel_let_have_show(sig_tokens[colon + 1 :] if colon is not None else [])
    tele: list[tuple[list[str], list[str]]] = [
        *_lean_bracket_binder_bindings(var_tokens),
        *_lean_bracket_binder_bindings(own_hdr),
    ]
    while body:
        if body[0] == "∀" or body[0] in _LEAN_STMT_FORALLS:
            comma = _lean_stmt_first_top(body, {","}, start=1)
            if comma is not None:
                tele.extend(_lean_quantifier_bindings(body[1:comma]))
                body = _lean_peel_let_have_show(body[comma + 1 :])
                continue
        arrows = _lean_stmt_split_top(body, _LEAN_STMT_ARROWS)
        if len(arrows) > 1:
            for ant in arrows[:-1]:
                inner = _lean_stmt_strip_outer(ant, "({⦃[")
                acol = _lean_stmt_first_top(inner, {":"})
                if acol is not None and inner is not ant:
                    bnames = [bt for bt in inner[:acol] if _is_lean_stmt_ident(bt) and bt != "_"]
                    tele.append((bnames, _lean_strip_binder_default(inner[acol + 1 :])))
                else:
                    tele.append(([], ant))
            body = _lean_peel_let_have_show(arrows[-1])
            continue
        break

    bound_names: set[str] = {bn for bnames, _ in tele for bn in bnames}
    bound_names.update(_lean_inner_bound_names(body))
    for _, bt in tele:
        bound_names.update(_lean_inner_bound_names(bt))

    concl_is_false = _lean_prop_truth(body) == _LEAN_TRUTH_FALSE
    active_tokens: list[str] = list(_lean_prune_trivial_subprops(body))
    if concl_is_false:
        for _, bt in tele:
            active_tokens.extend(_lean_prune_trivial_subprops(bt))

    used_binder_idxs: set[int] = set()
    changed = True
    while changed:
        changed = False
        active_set = {t for t in active_tokens if _is_lean_stmt_ident(t)}
        active_bound = active_set & bound_names
        for idx, (bnames, btype) in enumerate(tele):
            if idx in used_binder_idxs or not btype:
                continue
            pruned_bt = _lean_prune_trivial_subprops(btype)
            if not pruned_bt:
                continue
            bt_idents = {t for t in pruned_bt if _is_lean_stmt_ident(t)}
            if (set(bnames) & active_set) or bool(bt_idents & active_bound):
                used_binder_idxs.add(idx)
                active_tokens.extend(pruned_bt)
                changed = True

    return any(
        _is_lean_stmt_ident(tok) and tok not in _LEAN_STMT_LOGICAL_IDENTS and tok not in bound_names
        for tok in active_tokens
    )


def _lean_signature_problems(
    sig_tokens: list[str],
    body_tokens: list[str] | None = None,
    *,
    var_tokens: list[str] | None = None,
) -> list[str]:
    """Reasons why a declaration signature (`<binders> : <statement>`, as rich tokens
    after the declared name) and its proof body do not state and prove anything:
    `missing_statement`, `wildcard_statement` (`: _`, `: id _`, `(h : _)`, `: lhs = _`),
    `metavariable_hole` (`?m`, `?_` anywhere in the signature), `self_typed_statement`
    (`type_of%` or a `by` tactic block synthesizing a binder/statement type),
    `sorry_or_admit` (in the signature or the body), `vacuous_statement` (trivially true,
    tautological self-implication `(h : P) : P` / `P → P`, contradictory hypotheses, or a
    trivially false antecedent such as `(h : False)` or `False → ...`, also under `∀`
    binders), and `closed_trivial_statement` (names no free domain definition: `0 = 0`,
    `0 < 1`, `(p : CapturedMir) : 0 < 1`, `(n : Nat) : n + 0 = n`)."""
    problems: list[str] = []
    v_toks = list(var_tokens or [])
    full_sig = [*v_toks, *sig_tokens]
    colon = _lean_stmt_first_top(full_sig, {":"})
    binders = full_sig[:colon] if colon is not None else full_sig
    stmt = _lean_stmt_strip_outer(full_sig[colon + 1 :]) if colon is not None else []
    binder_types = _lean_bracket_binder_types(binders)
    if not stmt:
        problems.append("missing_statement")
    elif _lean_prop_has_hole(stmt) or any(_lean_prop_has_hole(bt) for bt in binder_types):
        problems.append("wildcard_statement")
    if any(tok.startswith("?") for tok in full_sig):
        problems.append("metavariable_hole")
    if (
        "type_of" in full_sig
        or _lean_prop_has_tactic_type(stmt)
        or any(_lean_prop_has_tactic_type(bt) for bt in binder_types)
    ):
        problems.append("self_typed_statement")
    if any(tok in _LEAN_HOLE_PROOF_TOKENS for tok in [*full_sig, *(body_tokens or [])]):
        problems.append("sorry_or_admit")
    if stmt and "wildcard_statement" not in problems:
        hyp_cores: set[tuple[bool, tuple[str, ...]]] = set()
        contradictory_binders = _lean_collect_hyp_cores(binder_types, hyp_cores)
        if contradictory_binders or _lean_stmt_tautological_under_hyps(stmt, hyp_cores):
            problems.append("vacuous_statement")
        if "vacuous_statement" in problems:
            if not any(
                _is_lean_stmt_ident(tok) and tok not in _LEAN_STMT_LOGICAL_IDENTS for tok in sig_tokens
            ):
                problems.append("closed_trivial_statement")
        elif not _lean_has_active_domain_ident(sig_tokens, v_toks):
            problems.append("closed_trivial_statement")
    return problems


def _split_lean_decl_text(text: str) -> tuple[list[str], list[str]]:
    """Split the text of a declaration after its name into rich signature tokens
    (binders and statement) and body tokens: the signature ends at the first depth-0
    `:=` (not a `let` / `have` binding inside the statement), `where`, or
    equation-compiler `|` (not a `match` / `fun` alternative)."""
    toks = _lean_stmt_tokens(text)
    depth = 0
    let_pending = 0
    alternatives_open = False
    for idx, tok in enumerate(toks):
        if tok in _LEAN_STMT_OPEN:
            depth += 1
            continue
        if tok in _LEAN_STMT_CLOSE:
            depth = max(0, depth - 1)
            continue
        if depth:
            continue
        if tok in ("let", "have"):
            let_pending += 1
        elif tok in ("match", "fun", "λ"):
            alternatives_open = True
        elif tok == ":=":
            if let_pending:
                let_pending -= 1
                continue
            return toks[:idx], toks[idx + 1 :]
        elif tok == "where" or (tok == "|" and not alternatives_open):
            return toks[:idx], toks[idx:]
    return toks, []


# Unconditional top-level declaration/command keywords that end a declaration body at
# bracket depth 0. Modifiers (`private`, `@[...]`, ...) only start a new top-level
# declaration when followed by one of these (inside `where`, `@[simp] aux := sorry` and
# `private aux := sorry` bind local helpers without a declaration keyword). Commands in
# `_LEAN_IN_PREFIX_CMDS` (`open`, `set_option`, `omit`, `attribute`, ...) end the body
# unless an `in` follows that scopes a tactic (`set_option ... in simp`) rather than the
# next top-level declaration (`set_option ... in theorem ...`).
_LEAN_UNCOND_DECL_BOUNDARIES = frozenset(
    _LEAN_WITNESS_DECL_KINDS
    | _LEAN_OTHER_TOP_CMDS
    | {
        "example",
        "namespace",
        "section",
        "end",
        "mutual",
    }
)
_LEAN_IN_SCOPED_CMDS = frozenset(_LEAN_IN_PREFIX_CMDS)


def _lean_decl_end_offset(tokens: list[str], spans: list[tuple[int, int]], start: int, default: int) -> int:
    """Source offset of the first depth-0 declaration boundary token at or after
    `tokens[start]` (or `default`)."""
    n = len(tokens)

    def is_uncond_boundary(j: int) -> bool:
        tok = tokens[j]
        return tok in _LEAN_UNCOND_DECL_BOUNDARIES or (tok.startswith("#") and len(tok) > 1)

    def is_standalone_in_cmd(j: int) -> bool:
        if tokens[j] not in _LEAN_IN_SCOPED_CMDS:
            return False
        d2 = 0
        for k in range(j + 1, n):
            t2 = tokens[k]
            if t2 in _LEAN_OPEN_BRACKETS:
                d2 += 1
            elif t2 in _LEAN_CLOSE_BRACKETS:
                d2 = max(0, d2 - 1)
            elif d2 == 0 and tokens[k - 1] != ".":
                if t2 == "in":
                    # `set_option ... in theorem ...` prefixes the next top-level
                    # declaration; `set_option ... in simp` scopes a tactic.
                    return is_modifier_prefix_of_top_decl(k + 1)
                if is_uncond_boundary(k) or t2 in _LEAN_IN_SCOPED_CMDS or t2 in _LEAN_DECL_MODIFIERS or t2 == "@[":
                    return True
        return True

    def is_modifier_prefix_of_top_decl(j: int) -> bool:
        k = j
        while k < n:
            tk = tokens[k]
            if tk == "@[":
                d_attr = 1
                k += 1
                while k < n and d_attr > 0:
                    if tokens[k] in _LEAN_OPEN_BRACKETS:
                        d_attr += 1
                    elif tokens[k] in _LEAN_CLOSE_BRACKETS:
                        d_attr -= 1
                    k += 1
                continue
            if tk in _LEAN_DECL_MODIFIERS and (k == 0 or tokens[k - 1] != "."):
                k += 1
                continue
            break
        return k < n and (is_uncond_boundary(k) or is_standalone_in_cmd(k))

    depth = 0
    for j in range(start, n):
        tok = tokens[j]
        prev = tokens[j - 1] if j > 0 else ""
        if tok in _LEAN_OPEN_BRACKETS and tok != "@[":
            depth += 1
            continue
        if tok in _LEAN_CLOSE_BRACKETS:
            if depth > 0:
                depth -= 1
            continue
        if depth or prev == ".":
            continue
        if is_uncond_boundary(j) or is_standalone_in_cmd(j):
            return spans[j][0]
        if (tok == "@[" or tok in _LEAN_DECL_MODIFIERS) and is_modifier_prefix_of_top_decl(j):
            return spans[j][0]
    return default


def _lean_module_parts(rel_file: str) -> list[str]:
    """Extract Lean module path components after `lean/` (e.g. `['LeanMiriSpec', 'Correspondence', 'SimLM2_3']`)."""
    parts = list(Path(rel_file).with_suffix("").parts)
    if "lean" in parts:
        idx = parts.index("lean")
        return parts[idx + 1 :]
    return parts


def _clean_lean_seg(tok: str) -> str:
    return tok[1:-1] if tok.startswith("«") and tok.endswith("»") else tok


def _is_lean_ident_tok(tok: str) -> bool:
    if tok.startswith("«") and tok.endswith("»"):
        return True
    if not tok or tok[0] in "@?:()[]{}⟨⟩⦃⦄.,;#0123456789":
        return False
    return True


def _is_lean_top_cmd_tok(tok: str, prev_tok: str) -> bool:
    if prev_tok == ".":
        return False
    return tok in _LEAN_ALL_CMD_BOUNDARIES or (tok.startswith("#") and len(tok) > 1)


def _read_lean_qname(tokens: list[str], idx: int) -> tuple[list[str], int]:
    """Read `seg (. seg)*` starting at `idx` (including `.1` field projections so `thm.1` does not match `thm`)."""
    n = len(tokens)
    if idx >= n or not (_is_lean_ident_tok(tokens[idx]) or tokens[idx].isdigit()):
        return [], idx
    segs = [_clean_lean_seg(tokens[idx])]
    idx += 1
    while (
        idx + 1 < n
        and tokens[idx] == "."
        and (_is_lean_ident_tok(tokens[idx + 1]) or tokens[idx + 1].isdigit())
    ):
        segs.append(_clean_lean_seg(tokens[idx + 1]))
        idx += 2
    return segs, idx


def _scan_lean_declarations_and_pins(
    stripped_src: str,
    *,
    external_holey_names: set[str] | frozenset[str] | None = None,
    external_ambient_hole: bool = False,
    external_prop_defs: dict[str, _PropDefSpec] | None = None,
    resolution_symbols: frozenset[str] | None = None,
    summary_only: bool = False,
) -> dict[str, Any]:
    """Tokenize comment/string-stripped Lean 4 source at bracket depth 0.

    Handles multi-line and same-line commands (`namespace Foo theorem bar ... end Foo`,
    `section private theorem ...`, `open Foo in private\\ntheorem ...`, `private @[simp,\\n ...]`,
    `mutual ... end`, `section #exit`, `#exit'` non-truncation) and extracts:
      - `witness_symbols`: every declared witness-eligible constant name;
      - `resolutions`: `symbol -> list[(effective_namespace_parts, has_forbidden_modifier,
        signature_problems)]` for `theorem` / `lemma` declarations (only of
        `resolution_symbols`, when given), where `signature_problems`
        (`_lean_signature_problems`) lists why the declaration states or proves nothing
        (empty for a meaningful, hole-free theorem). The statement is checked with every
        section `variable` binder in scope (any of them may be a hypothesis, by
        `include` or by mention) and with the definitions that reduce to a fixed
        proposition inlined (`_lean_prop_def_replacement`, `_lean_inline_prop_defs`:
        this module's and `external_prop_defs`), and `hole_dependency` is added when
        the declaration mentions a holey declaration (`holey_names`: a `sorry`, an
        `axiom`, ... of this module or `external_holey_names`), or follows a hole that
        proofs use unnamed (`ambient_hole`: an attributed holey declaration, a holey
        `instance` / `macro` / `notation`, `set_option debug.skipKernelTC`, or
        `external_ambient_hole`), or runs a lemma search such as `exact?` after any
        holey declaration;
      - `decl_statements`: `symbol -> list[(effective_namespace_parts, statement)]` for
        every witness-eligible declaration, `statement` being its signature after the
        name as space-joined rich tokens (`_lean_stmt_tokens`);
      - `pins`: `symbol -> list[(audit_active_namespace_parts, inline_qualifier_parts,
        type_tokens, example_sig_tokens, var_sig_tokens, rhs_arg_tokens, ambient_hole)]`
        for valid typed `example ... : <NonTrivialProp> := @?symbol <ident_args>*`
        statement pins, where `example_sig_tokens` / `var_sig_tokens` are the rich
        tokens (definitions inlined) of the `example`'s binders and type and of the
        `variable` binders in scope, `rhs_arg_tokens` the arguments applied to
        `symbol`, and `ambient_hole` whether an unnamed hole precedes the pin;
      - `holey_names`, `ambient_hole`, `prop_def_inline`: the module's outward summaries,
        which a module that imports it receives as `external_*`.

    With `summary_only` (an imported module), only the outward summaries are exact:
    `resolutions`, `decl_statements`, and `pins` are left empty, and a declaration
    whose text holds no hole token and names no holey declaration (a superset regex
    screen) is not tokenized unless it may define a proposition.
    """
    matches = list(_LEAN_TOKEN_RE.finditer(stripped_src))
    tokens = [m.group(0) for m in matches]
    spans = [m.span() for m in matches]
    n = len(tokens)
    depth = 0
    scope_stack: list[tuple[str, list[str]]] = []
    mutual_seq = 0
    mutual_hole_ids: set[str] = set()
    mutual_decl_names: dict[str, list[str]] = {}
    res_mutual_tags: list[tuple[str, int, str]] = []
    pending_mods: set[str] = set()
    witness_symbols: set[str] = set()
    resolutions: dict[str, list[tuple[list[str], bool, tuple[str, ...]]]] = {}
    decl_statements: dict[str, list[tuple[list[str], str]]] = {}
    pins: dict[
        str,
        list[
            tuple[
                list[str],
                list[str],
                tuple[str, ...],
                tuple[str, ...],
                tuple[str, ...],
                tuple[str, ...],
                bool,
            ]
        ],
    ] = {}
    variables: list[tuple[int, list[str]]] = []
    pending_in_vars: list[str] = []
    holey_names: set[str] = set(external_holey_names or ())
    ambient_hole = bool(external_ambient_hole)
    prop_def_inline: dict[str, _PropDefSpec] = dict(external_prop_defs or {})

    def active_var_tokens() -> list[str]:
        return [tok for _, var_toks in variables for tok in var_toks] + pending_in_vars

    i = 0
    while i < n:
        tok = tokens[i]
        prev = tokens[i - 1] if i > 0 else ""
        if tok in _LEAN_OPEN_BRACKETS:
            if tok == "@[" and depth == 0:
                # Recorded like a modifier: the declaration it decorates has an attribute.
                pending_mods.add("@[")
            depth += 1
            i += 1
            continue
        if tok in _LEAN_CLOSE_BRACKETS:
            if depth > 0:
                depth -= 1
            i += 1
            continue
        if depth > 0 or prev == ".":
            i += 1
            continue

        if tok == "#exit":
            break

        if tok in _LEAN_DECL_MODIFIERS:
            nxt = tokens[i + 1] if i + 1 < n else ""
            if tok in ("local", "scoped") and nxt in (_LEAN_IN_PREFIX_CMDS | _LEAN_OTHER_TOP_CMDS):
                i += 1
                continue
            pending_mods.add(tok)
            i += 1
            continue

        if tok == "variable":
            # `variable` takes bracketed binders only; it scopes the next command when an
            # `in` follows them, and the enclosing section otherwise.
            j = i + 1
            while j < n and tokens[j] in _LEAN_OPEN_BRACKETS and tokens[j] != "@[":
                d2 = 0
                while j < n:
                    if tokens[j] in _LEAN_OPEN_BRACKETS:
                        d2 += 1
                    elif tokens[j] in _LEAN_CLOSE_BRACKETS:
                        d2 -= 1
                        if d2 == 0:
                            break
                    j += 1
                j += 1
            var_toks = _lean_stmt_tokens(
                stripped_src[spans[i][1] : spans[j][0] if j < n else len(stripped_src)]
            )
            if j < n and tokens[j] == "in":
                pending_in_vars.extend(var_toks)
                i = j + 1
            else:
                variables.append((len(scope_stack), var_toks))
                pending_mods.clear()
                i = j
            continue

        if tok in _LEAN_IN_PREFIX_CMDS:
            j = i + 1
            d2 = 0
            cmd_next: int | None = None
            while j < n:
                t2 = tokens[j]
                p2 = tokens[j - 1] if j > 0 else ""
                if d2 == 0 and p2 != "." and t2 == "@[":
                    # An attribute starts the next declaration.
                    pending_mods.clear()
                    cmd_next = j
                    break
                if t2 in _LEAN_OPEN_BRACKETS:
                    d2 += 1
                elif t2 in _LEAN_CLOSE_BRACKETS:
                    if d2 > 0:
                        d2 -= 1
                elif d2 == 0 and p2 != ".":
                    if t2 == "in":
                        cmd_next = j + 1
                        break
                    if (
                        t2 == "#exit"
                        or t2 in (_LEAN_WITNESS_DECL_KINDS | _LEAN_SCOPE_KEYWORDS | {"example"})
                        or t2 in _LEAN_DECL_MODIFIERS
                    ):
                        pending_mods.clear()
                        cmd_next = j
                        break
                j += 1
            if tok == "attribute" and any(
                _clean_lean_seg(t2) in holey_names for t2 in tokens[i + 1 : j]
            ):
                # `attribute [simp] cheat` lets later proofs use the holey `cheat` unnamed.
                ambient_hole = True
            if any(t2 in _LEAN_KERNEL_BYPASS_TOKENS for t2 in tokens[i + 1 : j]):
                # `set_option debug.skipKernelTC true [in]`: later proofs go unchecked.
                ambient_hole = True
            if cmd_next is None:
                break
            i = cmd_next
            continue

        if tok == "namespace":
            pending_mods.clear()
            segs, i = _read_lean_qname(tokens, i + 1)
            if segs:
                scope_stack.append(("ns", segs))
            continue

        if tok == "section":
            pending_mods.clear()
            nxt = tokens[i + 1] if i + 1 < n else ""
            if _is_lean_ident_tok(nxt) and not _is_lean_top_cmd_tok(nxt, ""):
                scope_stack.append(("sec", [_clean_lean_seg(nxt)]))
                i += 2
            else:
                scope_stack.append(("sec", []))
                i += 1
            continue

        if tok == "mutual":
            pending_mods.clear()
            mutual_seq += 1
            scope_stack.append(("mutual", [str(mutual_seq)]))
            i += 1
            continue

        if tok == "end":
            pending_mods.clear()
            nxt = tokens[i + 1] if i + 1 < n else ""
            if _is_lean_ident_tok(nxt) and not _is_lean_top_cmd_tok(nxt, ""):
                end_parts, i = _read_lean_qname(tokens, i + 1)
                while scope_stack and end_parts:
                    kind, sp = scope_stack.pop()
                    if kind == "mutual":
                        continue
                    if sp and len(sp) <= len(end_parts) and end_parts[-len(sp) :] == sp:
                        end_parts = end_parts[: -len(sp)]
                    else:
                        break
            else:
                if scope_stack:
                    scope_stack.pop()
                i += 1
            # Section variables go out of scope with their section or namespace.
            variables = [(d, v) for d, v in variables if d <= len(scope_stack)]
            continue

        if tok in _LEAN_WITNESS_DECL_KINDS:
            mods = set(pending_mods)
            pending_mods.clear()
            var_toks = active_var_tokens()
            pending_in_vars = []
            segs, next_i = _read_lean_qname(tokens, i + 1)
            if segs and not segs[-1].isdigit():
                sym = segs[-1]
                witness_symbols.add(sym)
                active_ns = [s for kind, sp in scope_stack if kind == "ns" for s in sp]
                active_mut = [sp[0] for kind, sp in scope_stack if kind == "mutual" and sp]
                inline_ns = segs[:-1]
                eff_ns = inline_ns[1:] if (inline_ns and inline_ns[0] == "_root_") else (active_ns + inline_ns)
                decl_end = _lean_decl_end_offset(tokens, spans, next_i, len(stripped_src))
                decl_text = stripped_src[spans[next_i - 1][1] : decl_end]
                if (
                    summary_only
                    and tok not in ("def", "abbrev", "structure", "inductive", "axiom")
                    and _FAST_HOLE_SCREEN_RE.search(decl_text) is None
                    and not (
                        holey_names
                        and not holey_names.isdisjoint(_FAST_IDENT_EXTRACT_RE.findall(decl_text))
                    )
                ):
                    # No hole token and no holey name: nothing to record for an import.
                    sig_toks, body_toks = [], []
                else:
                    sig_toks, body_toks = _split_lean_decl_text(decl_text)
                if not summary_only:
                    decl_statements.setdefault(sym, []).append((eff_ns, " ".join(sig_toks)))
                direct_hole = tok == "axiom" or any(
                    t in _LEAN_HOLE_PROOF_TOKENS for t in [*sig_toks, *body_toks]
                )
                used_names = {t for t in [*sig_toks, *body_toks] if _is_lean_stmt_ident(t)} - {sym}
                uses_holey = bool(used_names & holey_names)
                if direct_hole or uses_holey:
                    holey_names.add(sym)
                for mid in active_mut:
                    mutual_decl_names.setdefault(mid, []).append(sym)
                    if direct_hole or uses_holey:
                        mutual_hole_ids.add(mid)
                    if mid in mutual_hole_ids:
                        # A `mutual` block stands or falls together.
                        holey_names.update(mutual_decl_names[mid])
                if tok in ("def", "abbrev") and body_toks:
                    replacement = _lean_prop_def_replacement(sig_toks, body_toks, prop_def_inline)
                    if replacement is not None:
                        prop_def_inline[sym] = replacement
                elif tok in ("structure", "inductive"):
                    replacement = _lean_structure_or_inductive_prop_def(
                        tok, sig_toks, body_toks, prop_def_inline
                    )
                    if replacement is not None:
                        prop_def_inline[sym] = replacement
                if (
                    tok in _LEAN_RES_DECL_KINDS
                    and not summary_only
                    and (resolution_symbols is None or sym in resolution_symbols)
                ):
                    problems = _lean_signature_problems(
                        _lean_inline_prop_defs(sig_toks, prop_def_inline),
                        body_toks,
                        var_tokens=_lean_inline_prop_defs(var_toks, prop_def_inline),
                    )
                    searches = any(t in _LEAN_SEARCH_TACTICS for t in body_toks)
                    if uses_holey or ambient_hole or (searches and holey_names - {sym}):
                        problems.append("hole_dependency")
                    entry_list = resolutions.setdefault(sym, [])
                    entry_idx = len(entry_list)
                    entry_list.append(
                        (
                            eff_ns,
                            bool(mods & _LEAN_FORBIDDEN_RES_MODS),
                            tuple(problems),
                        )
                    )
                    for mid in active_mut:
                        res_mutual_tags.append((sym, entry_idx, mid))
                if sym in holey_names and "@[" in mods:
                    # `@[simp]` / `@[instance]` let later proofs use the hole unnamed.
                    ambient_hole = True
            i = max(next_i, i + 1)
            continue

        if tok == "example":
            mods = set(pending_mods)
            pending_mods.clear()
            var_toks = active_var_tokens()
            pending_in_vars = []
            j = i + 1
            d2 = 0
            colon_idx: int | None = None
            assign_idx: int | None = None
            let_pending = 0
            while j < n:
                t2 = tokens[j]
                p2 = tokens[j - 1] if j > 0 else ""
                if t2 in _LEAN_OPEN_BRACKETS:
                    d2 += 1
                elif t2 in _LEAN_CLOSE_BRACKETS:
                    if d2 > 0:
                        d2 -= 1
                elif d2 == 0:
                    if assign_idx is not None and _is_lean_top_cmd_tok(t2, p2):
                        break
                    if t2 == ":" and colon_idx is None and assign_idx is None:
                        colon_idx = j
                    elif colon_idx is not None and assign_idx is None and p2 != "." and t2 in ("let", "have"):
                        let_pending += 1
                    elif t2 == ":=" and assign_idx is None:
                        if let_pending > 0:
                            let_pending -= 1
                        else:
                            assign_idx = j
                j += 1
            end_ex = j
            if (
                not (mods & _LEAN_FORBIDDEN_RES_MODS)
                and colon_idx is not None
                and assign_idx is not None
                and colon_idx < assign_idx
            ):
                type_toks = tokens[colon_idx + 1 : assign_idx]
                while len(type_toks) >= 2 and type_toks[0] == "(" and type_toks[-1] == ")":
                    bal = 0
                    ok_strip = True
                    for tt in type_toks[:-1]:
                        if tt == "(":
                            bal += 1
                        elif tt == ")":
                            bal -= 1
                            if bal == 0:
                                ok_strip = False
                                break
                    if ok_strip and bal == 1:
                        type_toks = type_toks[1:-1]
                    else:
                        break
                valid_type = len(type_toks) > 0 and not (
                    len(type_toks) == 1
                    and (
                        _clean_lean_seg(type_toks[0]) in _LEAN_TRIVIAL_PIN_TYPES
                        or type_toks[0].startswith("?")
                    )
                )
                rhs_toks = tokens[assign_idx + 1 : end_ex]
                rhs_end_offset = spans[end_ex][0] if end_ex < n else len(stripped_src)
                rhs_raw = stripped_src[spans[assign_idx][1] : rhs_end_offset]
                if (
                    not summary_only
                    and valid_type
                    and rhs_toks
                    and _LEAN_PIN_RHS_RE.fullmatch(rhs_raw) is not None
                ):
                    r_idx = 1 if rhs_toks[0] == "@" else 0
                    qsegs, r_next = _read_lean_qname(rhs_toks, r_idx)
                    if qsegs and not qsegs[-1].isdigit():
                        rem = rhs_toks[r_next:]
                        if all(
                            (_is_lean_ident_tok(rt) or rt == "_") and rt not in _LEAN_FORBIDDEN_PIN_ARGS
                            for rt in rem
                        ):
                            active_ns = [s for kind, sp in scope_stack if kind == "ns" for s in sp]
                            ex_inlined = _lean_inline_prop_defs(
                                _lean_stmt_tokens(stripped_src[spans[i][1] : spans[assign_idx][0]]),
                                prop_def_inline,
                            )
                            var_inlined = _lean_inline_prop_defs(var_toks, prop_def_inline)
                            pins.setdefault(qsegs[-1], []).append(
                                (
                                    active_ns,
                                    qsegs[:-1],
                                    tuple(type_toks),
                                    tuple(ex_inlined),
                                    tuple(var_inlined),
                                    tuple(rem),
                                    ambient_hole,
                                )
                            )
            i = end_ex
            continue

        if pending_mods:
            pending_mods.clear()
        if tok in _LEAN_OTHER_TOP_CMDS:
            # A `variable ... in` prefix scopes only the command it precedes.
            pending_in_vars = []
            cmd_end = _lean_decl_end_offset(tokens, spans, i + 1, len(stripped_src))
            cmd_toks = _lean_stmt_tokens(stripped_src[spans[i][1] : cmd_end])
            has_quoted_hole = any(
                t2.startswith("«`") and t2[2:-1].rsplit(".", 1)[-1] in _LEAN_HOLE_PROOF_TOKENS
                for t2 in cmd_toks
            )
            has_const_builder = any(t2 in _LEAN_METAPROG_CONST_BUILDERS for t2 in cmd_toks)
            if (
                any(t2 in _LEAN_HOLE_PROOF_TOKENS or t2 in holey_names for t2 in cmd_toks)
                or (has_quoted_hole and has_const_builder)
            ):
                ambient_hole = True
        i += 1

    for sym, entry_idx, mid in res_mutual_tags:
        if mid in mutual_hole_ids:
            eff_ns, has_forb, probs = resolutions[sym][entry_idx]
            if "sorry_or_admit" not in probs:
                resolutions[sym][entry_idx] = (eff_ns, has_forb, (*probs, "sorry_or_admit"))

    return {
        "witness_symbols": witness_symbols,
        "resolutions": resolutions,
        "decl_statements": decl_statements,
        "pins": pins,
        "holey_names": holey_names,
        "ambient_hole": ambient_hole,
        "prop_def_inline": prop_def_inline,
    }


def _has_lean_decl(
    stripped_src: str,
    symbol: str,
    *,
    resolution: bool,
    rel_file: str = "",
    scan: dict[str, Any] | None = None,
    module_parts: list[str] | None = None,
) -> bool:
    """Check whether `symbol` is declared in `stripped_src` under witness or resolution rules.

    `module_parts` overrides the namespace derived from `rel_file`'s path (a registry
    entry's explicit `resolution_namespace`, for files outside a `lean/` source root)."""
    parsed = scan if scan is not None else _scan_lean_declarations_and_pins(stripped_src)
    if not resolution:
        return symbol in parsed["witness_symbols"]
    return bool(_resolution_candidates(parsed, symbol, rel_file=rel_file, module_parts=module_parts))


def _resolution_candidates(
    parsed: dict[str, Any],
    symbol: str,
    *,
    rel_file: str = "",
    module_parts: list[str] | None = None,
) -> list[tuple[list[str], bool, tuple[str, ...]]]:
    """The `theorem` / `lemma` declarations of `symbol` that can count as its resolution:
    without a forbidden modifier (`private` / `unsafe` / `partial`) and declared in the
    module's namespace or one of its prefixes (`module_parts`, else derived from
    `rel_file`'s path)."""
    if module_parts is not None:
        mod_parts = module_parts
    else:
        mod_parts = _lean_module_parts(rel_file) if rel_file else []
    out: list[tuple[list[str], bool, tuple[str, ...]]] = []
    for eff_ns, has_forbidden, problems in parsed["resolutions"].get(symbol, []):
        if has_forbidden:
            continue
        if mod_parts and (len(eff_ns) > len(mod_parts) or eff_ns != mod_parts[: len(eff_ns)]):
            continue
        out.append((eff_ns, has_forbidden, problems))
    return out


def _resolution_decl_status(
    parsed: dict[str, Any],
    symbol: str,
    *,
    rel_file: str = "",
    module_parts: list[str] | None = None,
) -> tuple[str, list[str]]:
    """`("valid", [])`, `("invalid", problems)`, or `("missing", [])` for the resolution
    theorem `symbol` (`_resolution_candidates`). Fails closed: a single candidate whose
    statement or proof is vacuous or hole-riddled (`_lean_signature_problems`) makes the
    resolution `invalid`, even next to a meaningful one."""
    candidates = _resolution_candidates(parsed, symbol, rel_file=rel_file, module_parts=module_parts)
    if not candidates:
        return "missing", []
    problems = sorted({p for _, _, probs in candidates for p in probs})
    return ("invalid", problems) if problems else ("valid", [])


# Authority audit modules whose `example : <statement> := <theorem>` pins lock the
# exact statement of each resolution theorem (a pin fails the Lean build if the
# theorem is ever weakened, e.g. restated as `True`).
AUTHORITY_AUDIT_FILES: dict[str, str] = {
    "MiniRustSpec": "minirust/lean/MiniRustSpec/Audit.lean",
    "LeanMiriSpec": "lean-miri/lean/LeanMiriSpec/Audit.lean",
}


def _has_statement_pin(
    stripped_audit_src: str,
    symbol: str,
    *,
    rel_res_file: str = "",
    rel_pin_file: str = "",
    scan: dict[str, Any] | None = None,
    res_module_parts: list[str] | None = None,
    pin_module_parts: list[str] | None = None,
) -> bool:
    """True iff `stripped_audit_src` contains a non-trivial typed `example` statement pin
    whose RHS directly applies `symbol` (without field projections like `.1`, vacuous `: True`
    or wildcard `: _` types, or decoy inline/enclosing namespaces).

    `res_module_parts` / `pin_module_parts` override the namespaces derived from the
    resolution / pin file paths (a registry entry's explicit `resolution_namespace`)."""
    return _statement_pin_status(
        stripped_audit_src,
        symbol,
        rel_res_file=rel_res_file,
        rel_pin_file=rel_pin_file,
        scan=scan,
        res_module_parts=res_module_parts,
        pin_module_parts=pin_module_parts,
    )[0]


def _statement_pin_status(
    stripped_audit_src: str,
    symbol: str,
    *,
    rel_res_file: str = "",
    rel_pin_file: str = "",
    scan: dict[str, Any] | None = None,
    res_module_parts: list[str] | None = None,
    pin_module_parts: list[str] | None = None,
) -> tuple[bool, list[str]]:
    """`(pinned, rejected_pin_reasons)` for `_has_statement_pin`: the sorted reasons
    for which every candidate pin of `symbol` was rejected (empty when pinned or when
    no candidate pin exists)."""
    parsed = scan if scan is not None else _scan_lean_declarations_and_pins(stripped_audit_src)
    entries = parsed["pins"].get(symbol, [])
    if not entries:
        return False, []
    res_parts = (
        res_module_parts
        if res_module_parts is not None
        else (_lean_module_parts(rel_res_file) if rel_res_file else [])
    )
    pin_parts = (
        pin_module_parts
        if pin_module_parts is not None
        else (_lean_module_parts(rel_pin_file) if rel_pin_file else [])
    )
    has_res = bool(rel_res_file) or res_module_parts is not None
    has_pin = bool(rel_pin_file) or pin_module_parts is not None
    allowed_inline = {"_root_", *res_parts} if has_res else None
    allowed_audit_ns = {"StatementPins", *pin_parts, *res_parts} if (has_pin or has_res) else None
    sym_last = _clean_lean_seg(symbol.split(".")[-1])
    holey_names = parsed.get("holey_names", set())
    rejected: set[str] = set()
    for active_ns, inline_qual, type_toks, ex_sig_rich, var_sig_rich, rem_args, pin_ambient_hole in entries:
        ex_list = list(ex_sig_rich)
        var_list = list(var_sig_rich)
        sig_list = [*var_list, *ex_list]
        pin_colon = _lean_stmt_first_top(sig_list, {":"})
        pin_binders = sig_list[:pin_colon] if pin_colon is not None else sig_list
        pin_stmt = _lean_stmt_strip_outer(sig_list[pin_colon + 1 :]) if pin_colon is not None else []
        pin_binder_types = _lean_bracket_binder_types(pin_binders)
        if (
            any(_clean_lean_seg(st) == sym_last or st.startswith("?") for st in sig_list)
            or "type_of" in sig_list
            or _lean_prop_has_tactic_type(pin_stmt)
            or any(_lean_prop_has_tactic_type(bt) for bt in pin_binder_types)
            or _lean_prop_has_hole(pin_stmt)
            or any(_lean_prop_has_hole(bt) for bt in pin_binder_types)
        ):
            rejected.add("self_typed_or_hole_pin")
            continue
        if any(_clean_lean_seg(rt) in _LEAN_HOLE_PROOF_TOKENS for rt in rem_args):
            rejected.add("pin_sorry_or_admit")
            continue
        problems = _lean_signature_problems(ex_list, var_tokens=var_list)
        if problems:
            rejected.update(f"pin_{p}" for p in problems)
            continue
        used_pin_names = {t for t in sig_list if _is_lean_stmt_ident(t)} | {
            _clean_lean_seg(rt) for rt in rem_args if rt != "_"
        }
        if pin_ambient_hole or bool(used_pin_names & holey_names):
            rejected.add("pin_hole_dependency")
            continue
        pin_bound = set(_lean_binder_group_names(pin_binders))
        named_rem = [_clean_lean_seg(rt) for rt in rem_args if rt != "_"]
        if any(rn not in pin_bound for rn in named_rem) or len(named_rem) != len(set(named_rem)):
            rejected.add("pin_instantiates_or_duplicates_arg")
            continue
        if allowed_inline is not None and any(seg not in allowed_inline for seg in inline_qual):
            rejected.add("pin_decoy_qualifier")
            continue
        if allowed_audit_ns is not None and any(seg not in allowed_audit_ns for seg in active_ns):
            rejected.add("pin_decoy_namespace")
            continue
        return True, []
    return False, sorted(rejected)


_LEAN_IMPORT_ROOTS: tuple[str, ...] = ("lean-miri/lean", "minirust/lean", "theory", "trusted/lean", "")
_LEAN_IMPORT_HEADER_TOK_RE = re.compile(
    r"""
    (?:«[^»\n]+»|[^\W\d][\w'!?]*)(?:\.(?:«[^»\n]+»|[^\W\d][\w'!?]*))*
    | [^\s]
    """,
    re.VERBOSE,
)
_SIMPLE_GUILLEMET_UNESCAPE_RE = re.compile(r"«([^\W\d][\w'!?]*)»")
_FAST_HOLE_SCREEN_RE = re.compile(
    r"\b(?:sorry|admit|sorryAx|native_decide|ofReduceBool|ofReduceNat|mkSorry|"
    r"skipKernelTC|addDeclWithoutChecking|axiom|implemented_by|extern)\b"
)
_FAST_PROP_DECL_NAME_RE = re.compile(
    r"\b(def|abbrev|structure|inductive)\s+"
    r"((?:«[^»\n]+»|[^\W\d][\w'!?]*)(?:\.(?:«[^»\n]+»|[^\W\d][\w'!?]*))*)"
)
_FAST_TOP_DECL_BOUNDARY_RE = re.compile(
    r"(?:^|\n)\s*(?:@\[[^\]]*\]\s*|(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*"
    r"\b(?:theorem|lemma|def|abbrev|axiom|opaque|structure|inductive|class|instance|example|namespace|section|end|mutual)\b"
)
_FAST_PROP_OR_UNINHABITED_TYPE_RE = re.compile(
    r"\b(?:Prop|Type|Sort|False|Empty|PEmpty|Fin)\b"
)
_FAST_IDENT_EXTRACT_RE = re.compile(r"[^\W\d][\w'!?]*")
# Content-addressed per-file metadata cache: sha256 of the raw file bytes ->
# `(stripped_content_sha, stripped_src, header_imports, has_hole_screen_hit,
# cand_decl_idents, all_idents)`. (Keyed by content, not by path and mtime, so a file
# rewritten within one timestamp tick is never served stale.)
_LEAN_FILE_META_CACHE: dict[
    bytes,
    tuple[bytes, str, tuple[str, ...], bool, dict[str, frozenset[str]], frozenset[str]],
] = {}
# Content-addressed scan cache shared across calls and materialized baseline trees.
_LEAN_SCAN_BY_HASH_CACHE: dict[
    tuple[
        bytes,
        frozenset[str],
        bool,
        tuple[tuple[str, tuple[int, int, tuple[str, ...]]], ...],
        frozenset[str] | None,
        bool,
    ],
    dict[str, Any],
] = {}

def _scan_lean_cached(
    content_sha: bytes,
    stripped_src: str,
    *,
    external_holey_names: set[str] | frozenset[str] = frozenset(),
    external_ambient_hole: bool = False,
    external_prop_defs: dict[str, _PropDefSpec] | None = None,
    resolution_symbols: frozenset[str] | None = None,
    summary_only: bool = False,
) -> dict[str, Any]:
    """`_scan_lean_declarations_and_pins`, memoized by content and scan context."""
    holey_frozen = frozenset(external_holey_names)
    defs_dict = external_prop_defs or {}
    defs_sig = tuple(sorted((k, (v[0], v[1], tuple(v[2]))) for k, v in defs_dict.items()))
    key = (
        content_sha,
        holey_frozen,
        bool(external_ambient_hole),
        defs_sig,
        resolution_symbols,
        summary_only,
    )
    cached = _LEAN_SCAN_BY_HASH_CACHE.get(key)
    if cached is not None:
        return cached
    scanned = _scan_lean_declarations_and_pins(
        stripped_src,
        external_holey_names=holey_frozen,
        external_ambient_hole=external_ambient_hole,
        external_prop_defs=defs_dict,
        resolution_symbols=resolution_symbols,
        summary_only=summary_only,
    )
    if len(_LEAN_SCAN_BY_HASH_CACHE) > 2048:
        _LEAN_SCAN_BY_HASH_CACHE.clear()
    _LEAN_SCAN_BY_HASH_CACHE[key] = scanned
    return scanned


def _parse_header_imports_from_stripped(stripped_src: str) -> tuple[str, ...]:
    tokens = _LEAN_IMPORT_HEADER_TOK_RE.findall(stripped_src[:65536].lstrip("\ufeff"))
    mods: list[str] = []
    i = 0
    if tokens[i : i + 1] == ["module"]:
        i += 1
    if tokens[i : i + 1] == ["prelude"]:
        i += 1
    while i < len(tokens):
        j = i
        while j < len(tokens) and tokens[j] in ("public", "meta", "private"):
            j += 1
        if j >= len(tokens) or tokens[j] != "import":
            break
        j += 1
        if j < len(tokens) and tokens[j] in ("all", "runtime"):
            j += 1
        if j >= len(tokens):
            break
        mods.append(tokens[j].replace("«", "").replace("»", ""))
        i = j + 1
    return tuple(mods)


def _extract_cand_prop_decls(unesc: str) -> dict[str, frozenset[str]]:
    """Map candidate `def` / `abbrev` / `structure` / `inductive` short names that could
    reduce to a fixed proposition or uninhabited type to the identifiers in their slice."""
    boundaries = [m.start() for m in _FAST_TOP_DECL_BOUNDARY_RE.finditer(unesc)]
    out: dict[str, set[str]] = {}
    b_idx = 0
    n_b = len(boundaries)
    for m in _FAST_PROP_DECL_NAME_RE.finditer(unesc):
        kind = m.group(1)
        short = m.group(2).replace("«", "").replace("»", "").rsplit(".", 1)[-1]
        start = m.start()
        while b_idx < n_b and boundaries[b_idx] <= start + 1:
            b_idx += 1
        end = boundaries[b_idx] if b_idx < n_b else len(unesc)
        seg = unesc[start:end]
        if kind == "inductive":
            if "|" in seg.split("deriving", 1)[0]:
                continue
        elif kind == "structure":
            if "Prop" not in seg:
                continue
        else:
            hdr = seg.split(":=", 1)[0].split("where", 1)[0]
            if ":" in hdr and _FAST_PROP_OR_UNINHABITED_TYPE_RE.search(seg) is None:
                continue
        out.setdefault(short, set()).update(_FAST_IDENT_EXTRACT_RE.findall(seg))
    return {k: frozenset(v) for k, v in out.items()}


def _get_cached_lean_file_meta(
    path: Path,
) -> tuple[bytes, str, tuple[str, ...], bool, dict[str, frozenset[str]], frozenset[str]] | None:
    try:
        raw_bytes = path.read_bytes()
    except OSError:
        return None
    key = hashlib.sha256(raw_bytes).digest()
    cached = _LEAN_FILE_META_CACHE.get(key)
    if cached is not None:
        return cached
    raw = raw_bytes.decode("utf-8", errors="replace")
    stripped = _strip_lean_comments_and_strings(raw)
    content_sha = hashlib.sha256(stripped.encode("utf-8")).digest()
    unesc = _SIMPLE_GUILLEMET_UNESCAPE_RE.sub(r"\1", stripped) if "«" in stripped else stripped
    imports = _parse_header_imports_from_stripped(stripped)
    has_hole = _FAST_HOLE_SCREEN_RE.search(unesc) is not None
    cand_decls = _extract_cand_prop_decls(unesc)
    all_idents = frozenset(_FAST_IDENT_EXTRACT_RE.findall(unesc))
    entry = (content_sha, stripped, imports, has_hole, cand_decls, all_idents)
    if len(_LEAN_FILE_META_CACHE) > 2048:
        _LEAN_FILE_META_CACHE.clear()
    _LEAN_FILE_META_CACHE[key] = entry
    return entry


def _resolve_repo_lean_module(repo_root: Path, mod_name: str) -> str | None:
    rel_mod = Path(*mod_name.split(".")).with_suffix(".lean")
    for root in _LEAN_IMPORT_ROOTS:
        rel = (Path(root) / rel_mod) if root else rel_mod
        if (repo_root / rel).is_file():
            return rel.as_posix()
    return None


def _repo_lean_import_closure_toposort(
    repo_root: Path,
    start_rels: list[str],
    *,
    stop_rels: set[str] | None = None,
) -> list[str]:
    """Return transitive repo-local `.lean` dependencies of `start_rels` (excluding
    `start_rels` themselves) in topological dependency-first order."""
    visited: set[str] = set()
    order: list[str] = []
    start_set = set(start_rels)
    stops = stop_rels or set()

    def dfs(rel: str, is_root: bool = False) -> None:
        if not is_root:
            if rel in visited or rel in stops:
                return
            visited.add(rel)
        meta = _get_cached_lean_file_meta(repo_root / rel)
        if meta is None:
            return
        for mod in meta[2]:
            dep_rel = _resolve_repo_lean_module(repo_root, mod)
            if dep_rel is not None and dep_rel not in start_set:
                dfs(dep_rel, False)
        if not is_root:
            order.append(rel)

    for s_rel in start_rels:
        dfs(s_rel, True)
    return order


def _relevant_target_idents(stripped_src: str, target_symbols: set[str]) -> set[str]:
    """Extract identifiers used near `target_symbols` (and local `variable`/`def` headers)
    so huge shared files like `Audit.lean` only pull in definitions relevant to tracked
    theorems and pins."""
    unesc = _SIMPLE_GUILLEMET_UNESCAPE_RE.sub(r"\1", stripped_src) if "«" in stripped_src else stripped_src
    if len(unesc) <= 32768 or not target_symbols:
        return set(_FAST_IDENT_EXTRACT_RE.findall(unesc))
    out: set[str] = set()
    for sym in target_symbols:
        pos = 0
        while True:
            idx = unesc.find(sym, pos)
            if idx < 0:
                break
            window = unesc[max(0, idx - 8192) : min(len(unesc), idx + len(sym) + 512)]
            out.update(_FAST_IDENT_EXTRACT_RE.findall(window))
            pos = idx + max(1, len(sym))
    for m in re.finditer(r"\b(?:variable|def|abbrev|structure|inductive)\b", unesc):
        window = unesc[m.start() : min(len(unesc), m.end() + 512)]
        out.update(_FAST_IDENT_EXTRACT_RE.findall(window))
    return out


def discover_correspondence_divergences(
    repo_root: Path, *, include_statements: bool = False
) -> dict[str, Any]:
    """Check status of tracked correspondence divergences and `correspondence_gaps.toml`.

    Each actionable entry is `open` while its witness is declared, and otherwise
    `resolution_missing` (no resolution theorem in the expected namespace),
    `resolution_invalid` (the resolution theorem's statement or proof is vacuous or
    hole-riddled, see `_lean_signature_problems` and `_scan_lean_declarations_and_pins`;
    the reasons are in `resolution_problems`), `resolution_unpinned` (no non-vacuous
    statement pin; the rejected pins' reasons are in `resolution_pin_problems`), or
    `resolved`. Resolution and pin modules are scanned with what their repo-local
    imports export (`holey_names`, `ambient_hole`, `prop_def_inline`), so a vacuous
    definition or a hole in an imported helper module counts as well.

    With `include_statements`, every record also carries `witness_statements` and
    `resolution_statements`: the signatures (space-joined `_lean_stmt_tokens`) of the
    witness's declarations and of the resolution candidates, which the flip-direction
    audit (`audit_flip_direction_transitions`) compares across checkouts."""
    actionable_open: list[dict[str, Any]] = []
    actionable_resolved: list[dict[str, Any]] = []
    modeling_choices: list[dict[str, Any]] = []
    plain_scan_cache: dict[Path, tuple[str, dict[str, Any]]] = {}
    import_scan_cache: dict[Path, tuple[str, dict[str, Any]]] = {}
    # Only the tracked resolution theorems' statements are analyzed (the scans of
    # imported modules need just their exported summaries).
    tracked_res_syms = frozenset(
        str(it["resolution_symbol"])
        for it in TRACKED_CORRESPONDENCE_DIVERGENCES
        if it.get("resolution_symbol")
    )
    tracked_res_syms_by_file: dict[str, set[str]] = {}
    for it in TRACKED_CORRESPONDENCE_DIVERGENCES:
        rs = it.get("resolution_symbol")
        if rs:
            rf = it.get("resolution_file", it["file"])
            tracked_res_syms_by_file.setdefault(rf, set()).add(rs)
            pf = it.get("resolution_pin_file", AUTHORITY_AUDIT_FILES.get(it["authority"]))
            if pf:
                tracked_res_syms_by_file.setdefault(pf, set()).add(rs)

    def read_plain_scanned(path: Path) -> tuple[str, dict[str, Any]] | None:
        if path in plain_scan_cache:
            return plain_scan_cache[path]
        meta = _get_cached_lean_file_meta(path)
        if meta is None:
            return None
        content_sha, stripped, _, _, _, _ = meta
        scanned = _scan_lean_cached(content_sha, stripped, resolution_symbols=tracked_res_syms)
        plain_scan_cache[path] = (stripped, scanned)
        return stripped, scanned

    def read_import_aware_scanned(rel_file: str) -> tuple[str, dict[str, Any]] | None:
        path = repo_root / rel_file
        if path in import_scan_cache:
            return import_scan_cache[path]
        meta = _get_cached_lean_file_meta(path)
        if meta is None:
            return None
        content_sha, stripped, imports, _, _, _ = meta
        if not imports:
            res = read_plain_scanned(path)
            if res is not None:
                import_scan_cache[path] = res
            return res
        dep_rels = _repo_lean_import_closure_toposort(repo_root, [rel_file])
        if not dep_rels:
            res = read_plain_scanned(path)
            if res is not None:
                import_scan_cache[path] = res
            return res

        wanted_defs = _relevant_target_idents(
            stripped, tracked_res_syms_by_file.get(rel_file, set())
        )
        selected_deps: set[str] = set()
        for dep_rel in reversed(dep_rels):
            dmeta = _get_cached_lean_file_meta(repo_root / dep_rel)
            if dmeta is None:
                continue
            _, _, _, dep_has_hole, dep_cand_decls, _ = dmeta
            matched = set(dep_cand_decls.keys()) & wanted_defs
            if matched:
                selected_deps.add(dep_rel)
                for mname in matched:
                    wanted_defs.update(dep_cand_decls[mname])
            if dep_has_hole:
                selected_deps.add(dep_rel)

        ext_holey: set[str] = set()
        ext_ambient = False
        ext_defs: dict[str, _PropDefSpec] = {}
        for dep_rel in dep_rels:
            dpath = repo_root / dep_rel
            dmeta = _get_cached_lean_file_meta(dpath)
            if dmeta is None:
                continue
            dep_sha, dep_stripped, _, dep_has_hole, _, dep_all_idents = dmeta
            if (
                dep_rel not in selected_deps
                and not dep_has_hole
                and not (ext_holey and (dep_all_idents & ext_holey))
            ):
                continue
            dscanned = _scan_lean_cached(
                dep_sha,
                dep_stripped,
                external_holey_names=ext_holey,
                external_ambient_hole=ext_ambient,
                external_prop_defs=ext_defs,
                summary_only=True,
            )
            ext_holey.update(dscanned["holey_names"])
            ext_ambient = ext_ambient or dscanned["ambient_hole"]
            ext_defs.update(dscanned["prop_def_inline"])

        scanned = _scan_lean_cached(
            content_sha,
            stripped,
            external_holey_names=ext_holey,
            external_ambient_hole=ext_ambient,
            external_prop_defs=ext_defs,
            resolution_symbols=tracked_res_syms,
        )
        import_scan_cache[path] = (stripped, scanned)
        return stripped, scanned

    for item in TRACKED_CORRESPONDENCE_DIVERGENCES:
        fpath = repo_root / item["file"]
        symbol = item["witness_symbol"]
        scanned_f = read_plain_scanned(fpath)
        present = (
            _has_lean_decl(scanned_f[0], symbol, resolution=False, scan=scanned_f[1])
            if scanned_f is not None
            else False
        )

        resolution_symbol = item.get("resolution_symbol")
        resolution_present: bool | None = None
        resolution_valid: bool | None = None
        resolution_problems: list[str] = []
        resolution_statements: list[str] = []
        rel_r = item.get("resolution_file", item["file"])
        # Explicit namespace of the resolution theorem (and of its pin, when the pin lives
        # in the same file) for files outside a `lean/` source root, whose path does not
        # spell their namespace (`tests/mir/X.lean` declares `namespace Anneal.X`).
        res_ns = item.get("resolution_namespace")
        res_ns_parts = [seg for seg in res_ns.split(".") if seg] if res_ns else None
        if resolution_symbol:
            scanned_r = read_import_aware_scanned(rel_r)
            res_status = "missing"
            if scanned_r is not None:
                res_status, resolution_problems = _resolution_decl_status(
                    scanned_r[1], resolution_symbol, rel_file=rel_r, module_parts=res_ns_parts
                )
                candidate_ns = [
                    ns
                    for ns, _, _ in _resolution_candidates(
                        scanned_r[1], resolution_symbol, rel_file=rel_r, module_parts=res_ns_parts
                    )
                ]
                resolution_statements = sorted(
                    {
                        stmt
                        for ns, stmt in scanned_r[1]["decl_statements"].get(resolution_symbol, [])
                        if ns in candidate_ns
                    }
                )
            resolution_present = res_status != "missing"
            resolution_valid = res_status == "valid"

        resolution_pinned: bool | None = None
        pin_problems: list[str] = []
        if resolution_symbol and resolution_present:
            rel_pin = item.get("resolution_pin_file", AUTHORITY_AUDIT_FILES.get(item["authority"]))
            scanned_pin = read_import_aware_scanned(rel_pin) if rel_pin else None
            resolution_pinned = False
            if scanned_pin is not None:
                resolution_pinned, pin_problems = _statement_pin_status(
                    scanned_pin[0],
                    resolution_symbol,
                    rel_res_file=rel_r,
                    rel_pin_file=rel_pin or "",
                    scan=scanned_pin[1],
                    res_module_parts=res_ns_parts,
                    pin_module_parts=res_ns_parts if rel_pin == rel_r else None,
                )

        record = dict(item)
        record["live_in_source"] = present
        record["resolution_live_in_source"] = resolution_present
        record["resolution_valid"] = resolution_valid
        record["resolution_problems"] = resolution_problems
        record["resolution_statement_pinned"] = resolution_pinned
        record["resolution_pin_problems"] = pin_problems
        if include_statements:
            record["witness_statements"] = sorted(
                {stmt for _, stmt in scanned_f[1]["decl_statements"].get(symbol, [])}
                if scanned_f is not None
                else set()
            )
            record["resolution_statements"] = resolution_statements
        if item["category"] == "intentional_modeling_choice":
            record["status"] = "modeling_choice"
            modeling_choices.append(record)
        elif present:
            record["status"] = "open"
            actionable_open.append(record)
        elif resolution_symbol and not resolution_present:
            # Fail closed: the divergence witness vanished without its positive
            # replacement theorem (deleted/moved file or bare rename), so the
            # divergence is NOT proven resolved.
            record["status"] = "resolution_missing"
            actionable_open.append(record)
        elif resolution_symbol and not resolution_valid:
            # Fail closed: the replacement theorem states or proves nothing (vacuous,
            # hole-riddled, or `sorry`-proved), so the divergence is NOT proven resolved.
            record["status"] = "resolution_invalid"
            actionable_open.append(record)
        elif resolution_symbol and not resolution_pinned:
            # Fail closed: the replacement theorem exists but no non-vacuous audit
            # `example` pin locks its statement, so it could be weakened without notice.
            record["status"] = "resolution_unpinned"
            actionable_open.append(record)
        else:
            record["status"] = "resolved"
            actionable_resolved.append(record)

    # Also parse `theory/Correspondence/correspondence_gaps.toml`
    gaps_path = repo_root / "theory/Correspondence/correspondence_gaps.toml"
    open_toml_bugs: list[dict[str, Any]] = []
    closed_toml_bugs: list[str] = []
    epoch_deltas: list[str] = []
    if gaps_path.is_file():
        try:
            raw_toml = tomllib.loads(gaps_path.read_text(encoding="utf-8"))
            for g in raw_toml.get("gaps", []):
                gid = g.get("id", "unknown")
                kind = g.get("kind", "")
                status = g.get("status", "")
                if kind == "intentional_epoch_divergence":
                    epoch_deltas.append(gid)
                elif status == "open":
                    open_toml_bugs.append(g)
                else:
                    closed_toml_bugs.append(gid)
        except tomllib.TOMLDecodeError:
            pass

    # Also check `tests/miri-diff/manifest.toml` for any `[tests.known_anneal_bug]`
    miri_manifest_path = repo_root / "tests/miri-diff/manifest.toml"
    known_miri_bugs: list[str] = []
    if miri_manifest_path.is_file():
        try:
            mm = tomllib.loads(miri_manifest_path.read_text(encoding="utf-8"))
            for t in mm.get("tests", []):
                if "known_anneal_bug" in t:
                    known_miri_bugs.append(t.get("name", "unknown"))
        except tomllib.TOMLDecodeError:
            pass

    return {
        "actionable_anneal_bugs": actionable_open,
        "actionable_anneal_bugs_count": len(actionable_open),
        "resolved_correspondence_divergences": actionable_resolved,
        "intentional_modeling_choices": modeling_choices,
        "correspondence_gaps_toml": {
            "open_bugs": open_toml_bugs,
            "closed_bugs": closed_toml_bugs,
            "epoch_version_deltas": epoch_deltas,
        },
        "known_miri_diff_manifest_bugs": known_miri_bugs,
    }


def flip_direction_tracked_files() -> list[str]:
    """Every file that `discover_correspondence_divergences` reads for the tracked
    divergences: witness, resolution, and statement-pin modules."""
    files: set[str] = set()
    for item in TRACKED_CORRESPONDENCE_DIVERGENCES:
        files.add(item["file"])
        if item.get("resolution_symbol"):
            files.add(item.get("resolution_file", item["file"]))
            pin = item.get("resolution_pin_file", AUTHORITY_AUDIT_FILES.get(item["authority"]))
            if pin:
                files.add(pin)
    return sorted(files)


def materialize_flip_baseline_tree(repo_root: Path, ref: str, dest: Path) -> Path:
    """Write the tracked divergence files (`flip_direction_tracked_files`) and their
    transitive repo-local `.lean` imports as they are at git revision `ref` of
    `repo_root` under `dest`, and return `dest`. A file that does not exist at `ref` is
    left absent. Raises `ValueError` for an unknown revision."""
    probe = subprocess.run(
        ["git", "-C", str(repo_root), "rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}"],
        capture_output=True,
        text=True,
        check=False,
    )
    if probe.returncode != 0:
        raise ValueError(f"unknown flip-direction baseline revision {ref!r}")
    commit = probe.stdout.strip()
    ls_proc = subprocess.run(
        ["git", "-C", str(repo_root), "ls-tree", "-r", "-z", commit],
        capture_output=True,
        check=False,
    )
    blob_by_rel: dict[str, str] = {}
    if ls_proc.returncode == 0 and ls_proc.stdout:
        for rec in ls_proc.stdout.split(b"\x00"):
            if not rec or b"\t" not in rec:
                continue
            meta_b, path_b = rec.split(b"\t", 1)
            parts_b = meta_b.split()
            if len(parts_b) >= 3 and parts_b[1] == b"blob":
                blob_by_rel[path_b.decode("utf-8", errors="replace")] = parts_b[2].decode("ascii")

    def fetch_blobs(rels: list[str]) -> dict[str, bytes]:
        out_blobs: dict[str, bytes] = {}
        batch_rels = [r for r in rels if r in blob_by_rel]
        if batch_rels:
            stdin_payload = "".join(f"{blob_by_rel[r]}\n" for r in batch_rels).encode("ascii")
            cat_proc = subprocess.run(
                ["git", "-C", str(repo_root), "cat-file", "--batch"],
                input=stdin_payload,
                capture_output=True,
                check=False,
            )
            if cat_proc.returncode == 0:
                raw = cat_proc.stdout
                pos = 0
                ok = True
                for r in batch_rels:
                    nl = raw.find(b"\n", pos)
                    if nl < 0:
                        ok = False
                        break
                    hdr_parts = raw[pos:nl].split()
                    if len(hdr_parts) < 3 or hdr_parts[1] != b"blob":
                        ok = False
                        break
                    size = int(hdr_parts[2])
                    data_start = nl + 1
                    data_end = data_start + size
                    if data_end > len(raw):
                        ok = False
                        break
                    out_blobs[r] = raw[data_start:data_end]
                    pos = data_end + (1 if data_end < len(raw) and raw[data_end : data_end + 1] == b"\n" else 0)
                if ok:
                    return out_blobs
                out_blobs.clear()
        for r in rels:
            shown = subprocess.run(
                ["git", "-C", str(repo_root), "show", f"{commit}:./{r}"],
                capture_output=True,
                check=False,
            )
            if shown.returncode == 0:
                out_blobs[r] = shown.stdout
        return out_blobs

    def resolve_in_commit(mod_name: str) -> str | None:
        rel_mod = Path(*mod_name.split(".")).with_suffix(".lean")
        for root in _LEAN_IMPORT_ROOTS:
            cand = ((Path(root) / rel_mod) if root else rel_mod).as_posix()
            if cand in blob_by_rel:
                return cand
        return None

    written: set[str] = set()
    tracked_seeds = flip_direction_tracked_files()
    current_imports = _repo_lean_import_closure_toposort(repo_root, tracked_seeds)
    frontier = [
        r
        for r in [*tracked_seeds, *current_imports]
        if (not blob_by_rel or r in blob_by_rel)
    ]
    while frontier:
        pending = [r for r in dict.fromkeys(frontier) if r not in written]
        if not pending:
            break
        fetched = fetch_blobs(pending)
        next_frontier: list[str] = []
        for rel, data in fetched.items():
            written.add(rel)
            target = dest / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            if rel.endswith(".lean") and blob_by_rel:
                stripped = _strip_lean_comments_and_strings(
                    data[:65536].decode("utf-8", errors="replace")
                )
                for mod in _parse_header_imports_from_stripped(stripped):
                    dep_rel = resolve_in_commit(mod)
                    if dep_rel is not None and dep_rel not in written:
                        next_frontier.append(dep_rel)
        for rel in pending:
            written.add(rel)
        frontier = next_frontier
    return dest


def _lean_bracket_binder_bindings(tokens: list[str]) -> list[tuple[list[str], list[str]]]:
    """`[(bound_names, binder_type), ...]` for depth-0 bracketed binder groups."""
    out: list[tuple[list[str], list[str]]] = []
    i = 0
    while i < len(tokens):
        tok = tokens[i]
        if tok in ("(", "{", "⦃", "["):
            close = _lean_stmt_matching_close(tokens, i)
            inner = tokens[i + 1 : close]
            colon = _lean_stmt_first_top(inner, {":"})
            if colon is not None:
                bnames = [bt for bt in inner[:colon] if _is_lean_stmt_ident(bt) and bt != "_"]
                out.append((bnames, _lean_strip_binder_default(inner[colon + 1 :])))
            elif inner and inner[0] in ("(", "{", "⦃", "["):
                out.extend(_lean_bracket_binder_bindings(inner))
            elif tok == "[":
                out.append(([], _lean_strip_binder_default(inner)))
            i = close + 1
        else:
            i += 1
    return out


def _lean_quantifier_bindings(binders: list[str]) -> list[tuple[list[str], list[str]]]:
    """`[(bound_names, binder_type), ...]` for `∀ <binders>, ...`."""
    bindings = _lean_bracket_binder_bindings(binders)
    colon = _lean_stmt_first_top(binders, {":"})
    if colon is not None:
        bnames: list[str] = []
        i = 0
        prefix = binders[:colon]
        while i < len(prefix):
            if prefix[i] in _LEAN_STMT_OPEN:
                i = _lean_stmt_matching_close(prefix, i) + 1
                continue
            if _is_lean_stmt_ident(prefix[i]) and prefix[i] != "_":
                bnames.append(prefix[i])
            i += 1
        bindings.append((bnames, _lean_strip_binder_default(binders[colon + 1 :])))
    elif not bindings:
        bare = [bt for bt in binders if _is_lean_stmt_ident(bt) and bt != "_"]
        if bare:
            bindings.append((bare, []))
    return bindings


def _canonical_lean_signature(sig_str: str) -> str:
    """Alpha- and binder-canonicalized form of a declaration signature string so cosmetic
    rewrites (wrapping in parentheses/`id`, swapping `->` and `→`, folding `(x : T) : P`
    into `: ∀ {x : T}, P` or `: (x : T) → P`, alpha-renaming bound variables, or padding
    with `True ∧ ...`) cannot disguise an unflipped witness or pre-existing theorem."""
    toks = _lean_stmt_tokens(sig_str)
    colon = _lean_stmt_first_top(toks, {":"})
    header = toks[:colon] if colon is not None else []
    body = _lean_norm_expr_tokens(toks[colon + 1 :] if colon is not None else toks)
    telescope: list[tuple[list[str], list[str]]] = _lean_bracket_binder_bindings(header)
    while body:
        if body[0] == "∀" or body[0] in _LEAN_STMT_FORALLS:
            comma = _lean_stmt_first_top(body, {","}, start=1)
            if comma is not None:
                telescope.extend(_lean_quantifier_bindings(body[1:comma]))
                body = _lean_norm_expr_tokens(body[comma + 1 :])
                continue
        arrows = _lean_stmt_split_top(body, _LEAN_STMT_ARROWS)
        if len(arrows) > 1:
            for ant in arrows[:-1]:
                inner = _lean_stmt_strip_outer(ant, "({⦃[")
                acol = _lean_stmt_first_top(inner, {":"})
                if acol is not None and inner is not ant:
                    bnames = [bt for bt in inner[:acol] if _is_lean_stmt_ident(bt) and bt != "_"]
                    telescope.append((bnames, _lean_strip_binder_default(inner[acol + 1 :])))
                else:
                    telescope.append(([], ant))
            body = _lean_norm_expr_tokens(arrows[-1])
            continue
        break

    conj = _lean_stmt_split_top(body, _LEAN_STMT_ANDS)
    if len(conj) > 1:
        kept = [c for c in conj if _lean_prop_truth(c) != _LEAN_TRUTH_TRUE]
        if kept:
            merged: list[str] = []
            for idx, part in enumerate(kept):
                if idx > 0:
                    merged.append("∧")
                merged.extend(_lean_norm_expr_tokens(part))
            body = merged

    def subst_env(expr: list[str], env: dict[str, str]) -> list[str]:
        out: list[str] = []
        for idx, t in enumerate(expr):
            if (idx == 0 or expr[idx - 1] != ".") and t in env:
                out.append(env[t])
            else:
                out.append(t)
        return out

    env: dict[str, str] = {}
    next_id = 0
    norm_binders: list[str] = []
    for bnames, btype in telescope:
        norm_bt = _lean_norm_expr_tokens(btype) if btype else []
        if not bnames and norm_bt and _lean_prop_truth(norm_bt) == _LEAN_TRUTH_TRUE:
            continue
        sub_bt = subst_env(norm_bt, env) if norm_bt else ["_untyped_"]
        count = max(1, len(bnames))
        for _ in range(count):
            norm_binders.append(" ".join(sub_bt))
        for bn in bnames:
            env[bn] = f"$b{next_id}"
            next_id += 1
    norm_body = " ".join(subst_env(_lean_norm_expr_tokens(body), env))
    return " | ".join([*norm_binders, norm_body])


def _lean_file_hole_token_counts(path: Path) -> dict[str, int]:
    """Counts of the proof-hole and unsound-escape tokens of a Lean file (comments and
    strings stripped, guillemets unescaped): `sorry`, `admit`, `sorryAx`, `axiom`,
    `native_decide`, `ofReduceBool`, `ofReduceNat`, `mkSorry`, `implemented_by`, and
    `extern` (not after a `.`), the kernel-check bypasses `skipKernelTC` and
    `addDeclWithoutChecking` (also after a `.`), and each of them as the last component
    of a quoted name literal (``` ``sorryAx ```, `` `Lean.Meta.mkSorry ``), with which
    metaprogramming code (`mkConst ``sorryAx`) builds a hole term without spelling the
    token."""
    counts = {tok: 0 for tok in sorted(_LEAN_FILE_HOLE_TOKENS)}
    meta = _get_cached_lean_file_meta(path)
    if meta is None or not meta[3]:
        return counts
    toks = _lean_stmt_tokens(meta[1])
    for idx, tok in enumerate(toks):
        if tok.startswith("«`"):
            last = tok[2:-1].rsplit(".", 1)[-1]
            if last in counts:
                counts[last] += 1
        elif tok in counts and (idx == 0 or toks[idx - 1] != "." or tok in _LEAN_KERNEL_BYPASS_TOKENS):
            counts[tok] += 1
    return counts


def audit_flip_direction_transitions(baseline_root: Path, current_root: Path) -> dict[str, Any]:
    """Flip-direction witness polarity guard: compare every tracked actionable
    divergence between a baseline checkout tree and the current one.

    Every `* -> resolved` transition must, at once, remove the `*_divergence`
    witness, introduce a non-vacuous, hole-free `*_simulation` theorem in the expected
    namespace, and lock it with a non-vacuous statement pin. Beyond what the
    current tree's `resolved` status already requires, the transition is rejected when
    the simulation theorem's statement restates a baseline witness statement up to
    binder/connective/alpha canonicalization (`polarity_not_flipped`: the witness was
    renamed or cosmetically wrapped, not flipped), when an unchanged simulation theorem
    already held next to the live witness in the baseline (`resolution_predates_flip`:
    it held while the divergence was live, so it cannot show that the divergence is
    gone), or when its witness, resolution, pin, or imported helper module gained a
    proof hole anywhere (`proof_hole_introduced`: a `sorry` / `admit` / `sorryAx` /
    `native_decide` / `implemented_by` / `extern` / `debug.skipKernelTC` token, see
    `_lean_file_hole_token_counts`, or an `axiom`, including when an already-resolved
    theorem's statement is rewritten). Every transition from a non-`resolved` baseline
    state into a `resolution_*` state is an `incomplete_flip` (a move back to `open`
    restores a live witness and flips nothing), and every transition out of `resolved`
    is a `flip_regressed`. Returns `{"passed", "transitions", "violations", ...}`."""
    base = discover_correspondence_divergences(baseline_root, include_statements=True)
    cur = discover_correspondence_divergences(current_root, include_statements=True)

    def by_id(divs: dict[str, Any]) -> dict[str, dict[str, Any]]:
        return {
            r["id"]: r
            for r in divs["actionable_anneal_bugs"] + divs["resolved_correspondence_divergences"]
        }

    base_by_id, cur_by_id = by_id(base), by_id(cur)
    transitions: list[dict[str, Any]] = []
    violations: list[dict[str, Any]] = []
    all_tracked_mod_files = {
        r
        for it in TRACKED_CORRESPONDENCE_DIVERGENCES
        for r in (it["file"], it.get("resolution_file", it["file"]))
        if r
    }

    def violate(div_id: str, reason: str, detail: str) -> None:
        violations.append({"id": div_id, "reason": reason, "detail": detail})

    def check_added_holes(div_id: str, item: dict[str, Any], res_sym: str) -> bool:
        rel_wit = item["file"]
        rel_res = item.get("resolution_file", rel_wit)
        rel_pin = item.get("resolution_pin_file", AUTHORITY_AUDIT_FILES.get(item["authority"]))
        own_mods = [r for r in dict.fromkeys((rel_wit, rel_res)) if r]
        other_tracked = all_tracked_mod_files - set(own_mods)
        imported_by_own = _repo_lean_import_closure_toposort(current_root, own_mods)
        imported_by_pin = (
            _repo_lean_import_closure_toposort(
                current_root, [rel_pin], stop_rels=other_tracked
            )
            if rel_pin
            else []
        )
        candidate_rels = list(
            dict.fromkeys([*own_mods, *([rel_pin] if rel_pin else []), *imported_by_own, *imported_by_pin])
        )
        found_hole = False
        for rel in candidate_rels:
            before = _lean_file_hole_token_counts(baseline_root / rel)
            after = _lean_file_hole_token_counts(current_root / rel)
            added = {tok: after[tok] - before[tok] for tok in after if after[tok] > before[tok]}
            if added:
                violate(
                    div_id,
                    "proof_hole_introduced",
                    f"`{rel}` gained proof-hole tokens {added} while `{res_sym}` flipped",
                )
                found_hole = True
        return found_hole

    for item in TRACKED_CORRESPONDENCE_DIVERGENCES:
        div_id = item["id"]
        if div_id not in base_by_id or div_id not in cur_by_id:
            continue
        b, c = base_by_id[div_id], cur_by_id[div_id]
        res_sym = item.get("resolution_symbol", "<none>")
        if b["status"] == c["status"]:
            if b["status"] == "resolved":
                b_canon = {_canonical_lean_signature(s) for s in b["resolution_statements"]}
                c_canon = {_canonical_lean_signature(s) for s in c["resolution_statements"]}
                if c_canon != b_canon and check_added_holes(div_id, item, res_sym):
                    transitions.append({"id": div_id, "from": "resolved", "to": "resolved"})
            continue
        transitions.append({"id": div_id, "from": b["status"], "to": c["status"]})
        if c["status"] == "resolved":
            if c["live_in_source"]:
                violate(div_id, "witness_not_removed", f"`{item['witness_symbol']}` is still declared")
            if not (c["resolution_live_in_source"] and c["resolution_valid"]):
                violate(
                    div_id,
                    "resolution_not_introduced",
                    f"`{res_sym}` is missing or invalid: {c['resolution_problems']}",
                )
            if not c["resolution_statement_pinned"]:
                violate(div_id, "resolution_unpinned", f"no non-vacuous statement pin locks `{res_sym}`")
            base_wit_canon = {_canonical_lean_signature(s) for s in b["witness_statements"]}
            renamed = sorted(
                s
                for s in c["resolution_statements"]
                if s in set(b["witness_statements"]) or _canonical_lean_signature(s) in base_wit_canon
            )
            if renamed:
                violate(
                    div_id,
                    "polarity_not_flipped",
                    f"`{res_sym}` restates the baseline witness `{item['witness_symbol']}`: "
                    f"{renamed[0]}",
                )
            base_res_canon = {_canonical_lean_signature(s) for s in b["resolution_statements"]}
            cur_res_canon = {_canonical_lean_signature(s) for s in c["resolution_statements"]}
            if (
                b["live_in_source"]
                and b["resolution_valid"]
                and cur_res_canon
                and cur_res_canon <= base_res_canon
            ):
                violate(
                    div_id,
                    "resolution_predates_flip",
                    f"`{res_sym}` already held, unchanged, next to the live witness "
                    f"`{item['witness_symbol']}` in the baseline",
                )
            check_added_holes(div_id, item, res_sym)
        elif b["status"] == "resolved":
            violate(
                div_id,
                "flip_regressed",
                f"resolved in the baseline, `{c['status']}` now",
            )
        elif c["status"] != "open":
            # An incomplete flip: out of `open`, or between the `resolution_*` states.
            # (A move back to `open` restores a live witness: the divergence is tracked
            # as open again, which is no flip at all.)
            detail = f"the witness flipped from `{b['status']}` to `{c['status']}`"
            if c["resolution_problems"]:
                detail += f": {c['resolution_problems']}"
            elif c["resolution_pin_problems"]:
                detail += f": {c['resolution_pin_problems']}"
            violate(div_id, "incomplete_flip", detail)

    return {
        "baseline_root": str(baseline_root),
        "current_root": str(current_root),
        "baseline_actionable_count": base["actionable_anneal_bugs_count"],
        "current_actionable_count": cur["actionable_anneal_bugs_count"],
        "transitions": transitions,
        "violations": violations,
        "passed": not violations,
    }


# ---------------------------------------------------------------------------
# Pillar 2: Suite Runner (Categories 1–7)
# ---------------------------------------------------------------------------

WRAPPER_TIMEOUT_GRACE_SEC = 30
# `anneal-lean-run --mode build` first queues for a host build slot for up to
# `max(30, --timeout)` seconds (`acquire_build_slot`), and only then starts the
# command's own `--timeout` clock; its `file` mode never queues.
LEAN_RUN_SLOT_WAIT_FLOOR_SEC = 30
LEAN_RUN_DEFAULT_TIMEOUT_SEC = {"file": 180, "build": 900}
# SIGTERM -> SIGKILL escalation window for a timed-out step's process group, so
# `anneal-lean-run` can forward the signal and reap its own (separate-session) scope.
STEP_TERMINATE_GRACE_SEC = 10
STEP_PIPE_DRAIN_SEC = 5

# Hermetic Lake 4.34.1 artifact-cache restoration defaults: ensure cached `.olean`s
# are restored into `.lake/build/lib/lean/` and `examples/.lake/build/lib/lean/`
# rather than leaving stale `.olean` copies behind across commits.
LAKE_ARTIFACT_CACHE_ENV: dict[str, str] = {
    "LAKE_ARTIFACT_CACHE": "true",
    "LAKE_RESTORE_ARTIFACTS": "true",
}

# Hosts / cgroups with an effective RAM ceiling strictly below 10 GiB (10240 MiB)
# elaborate `LeanMiriSpec` (608-file `Miri` + `LeanMiriSpec` closure) single-threaded
# to avoid `exit 137` cgroup OOM kills.
LEAN_MIRI_SPEC_SINGLE_THREAD_RAM_THRESHOLD_MIB = 10240

# Sentinel distinguishing "caller omitted `effective_ram_mib`" from an explicit
# `None` (representing an unreadable `/proc` / cgroup probe).
_RAM_UNSET: object = object()

# Per-module files Lake keeps under `.lake/build/lib/lean/` (`<Mod>.<suffix>`): the
# primary artifacts loaded through `LEAN_PATH`, the module-system IR companions, the
# module archive, and Lake's `.trace` / `.hash` bookkeeping for each of them.
_LEAN_PRIMARY_ARTIFACT_SUFFIXES: frozenset[str] = frozenset(
    (".olean", ".olean.server", ".olean.private", ".ilean")
)
_LEAN_OLEAN_PART_SUFFIXES: frozenset[str] = frozenset((".olean", ".olean.server", ".olean.private"))
# The artifacts whose content hashes Lake mixes, in this order, into the
# `<Mod>:importAllArts` trace that an importer records for a module-system (`module`)
# dependency (`Module.computeExportInfo`); for a classic module it is the `.olean` alone.
_LEAN_IMPORT_ALL_ARTS_MODULE_PARTS: tuple[str, ...] = (
    ".olean",
    ".olean.server",
    ".olean.private",
    ".ir.sig",
    ".ir",
)
_LEAN_ARTIFACT_SUFFIXES: frozenset[str] = frozenset(
    (
        *_LEAN_PRIMARY_ARTIFACT_SUFFIXES,
        ".ir",
        ".ir.sig",
        ".ltar",
        ".trace",
        *(f"{sfx}.hash" for sfx in (*_LEAN_PRIMARY_ARTIFACT_SUFFIXES, ".ir", ".ir.sig", ".ltar")),
    )
)
_TRUSTED_LIB = "Trusted"
# Vendored upstream `Miri` modules (`lean-miri/vendor/Miri`) never import `Trusted`.
_TRUSTED_INDEPENDENT_LIBS: frozenset[str] = frozenset(("Miri",))
# Source roots tried (after the `lakefile.toml` `srcDir` of the module's library) when
# mapping `<Mod>.olean` back to `<Mod>.lean` in synthetic or partial trees.
_LEAN_SOURCE_FALLBACK_DIRS: tuple[str, ...] = (
    "trusted/lean",
    "theory",
    "minirust/lean",
    "lean-miri/lean",
    "lean-miri/vendor",
    "examples",
    "examples/refinement",
    "examples/step-result",
    "examples/pass",
    "examples/mir",
)

# Lake's 64-bit content hash (`Lake.Hash`): `MurmurHash64A` with seed 11 (`String.hash` /
# `ByteArray.hash`) mixed into `Hash.nil` (`Hash.ofHashable`), printed as 16 hex digits.
_LAKE_HASH_MASK = (1 << 64) - 1
_LAKE_HASH_MUL = 0xC6A4A7935BD1E995
_LAKE_HASH_SEED = 11
_LAKE_HASH_NIL = 1723
_LAKE_HASH_HEX_RE = re.compile(r"[0-9a-f]{16}")


_LEAN_RUN_VALUE_OPTS: frozenset[str] = frozenset(
    (
        "--concurrency",
        "-W",
        "--mode",
        "--memory-max-mb",
        "--timeout",
    )
)
_LEAN_RUN_BOOL_OPTS: frozenset[str] = frozenset(
    (
        "--probe",
        "--print-limits",
        "--json",
        "--no-slot-lock",
        "--nested-ok",
        "--exclusive",
        "--no-oom-retry",
        "--unsafe-ignore-cgroup",
        "--ensure-slice",
        "-h",
        "--help",
    )
)
_LEAN_RUN_LONG_OPTS: tuple[str, ...] = tuple(
    sorted(o for o in (_LEAN_RUN_VALUE_OPTS | _LEAN_RUN_BOOL_OPTS) if o.startswith("--"))
)


def _resolve_lean_run_opt(opt: str) -> str:
    """Resolve `argparse` long-option prefix abbreviations (e.g. `--time` -> `--timeout`)."""
    if opt in _LEAN_RUN_VALUE_OPTS or opt in _LEAN_RUN_BOOL_OPTS or not opt.startswith("--"):
        return opt
    matches = [cand for cand in _LEAN_RUN_LONG_OPTS if cand.startswith(opt)]
    return matches[0] if len(matches) == 1 else opt


def _is_lean_run_wrapped(cmd: list[str]) -> bool:
    return bool(cmd) and Path(cmd[0]).name == "anneal-lean-run"


def _parse_lean_run_wrapper(cmd: list[str]) -> tuple[str, int | None, bool, bool]:
    """`(mode, timeout_sec, slot_lock, saw_timeout_flag)` from the `anneal-lean-run`
    options preceding `--` or the first positional command token."""
    mode = "auto"
    timeout: int | None = None
    saw_timeout = False
    slot_lock = True
    i = 1
    n = len(cmd)
    while i < n:
        tok = cmd[i]
        if tok == "--":
            i += 1
            break
        if not tok.startswith("-") or tok == "-":
            break
        opt = tok
        val: str | None = None
        if "=" in tok and tok.startswith("-"):
            opt, val = tok.split("=", 1)
            opt = _resolve_lean_run_opt(opt)
        else:
            opt = _resolve_lean_run_opt(opt)
            if opt in _LEAN_RUN_VALUE_OPTS and i + 1 < n:
                val = cmd[i + 1]
                i += 1
        if opt == "--no-slot-lock":
            slot_lock = False
        elif opt == "--mode" and val is not None:
            mode = val
        elif opt == "--timeout" and val is not None:
            saw_timeout = True
            try:
                timeout = int(val)
            except ValueError:
                timeout = None
        i += 1
    inner = cmd[i:]
    if mode not in ("file", "build"):
        is_lean_file = (bool(inner) and Path(inner[0]).name == "lean") or (
            len(inner) >= 3
            and Path(inner[0]).name == "lake"
            and inner[1] == "env"
            and Path(inner[2]).name == "lean"
        )
        mode = "file" if is_lean_file and "--run" not in inner else "build"
    if timeout is not None and timeout <= 0:
        timeout = None
    return mode, timeout, slot_lock, saw_timeout


def _lean_run_wrapper_flags(cmd: list[str]) -> tuple[str, int | None, bool]:
    """`(mode, timeout_sec, slot_lock)` from the `anneal-lean-run` options preceding
    `--` or the first positional command token (an `auto` mode resolves like the
    wrapper: `lean` or `lake env lean` without `--run` is `file`)."""
    mode, timeout, slot_lock, _saw_timeout = _parse_lean_run_wrapper(cmd)
    return mode, timeout, slot_lock


def _outer_timeout_sec(
    cmd: list[str], timeout_sec: int, env: dict[str, str] | None = None
) -> int:
    """Outer Python deadline for a step: the step budget itself for direct commands,
    and for `anneal-lean-run` wrapped ones the wrapper's worst-case lifetime (build
    slot queueing + its own `--timeout` + termination) plus a grace margin, so the
    wrapper's structured exit-124 diagnostic always wins the race."""
    if not _is_lean_run_wrapped(cmd):
        return timeout_sec
    mode, inner_timeout, slot_lock, saw_timeout = _parse_lean_run_wrapper(cmd)
    if inner_timeout is None and not saw_timeout:
        env_map = os.environ if env is None else env
        raw_env_timeout = env_map.get("ANNEAL_LEAN_TIMEOUT_SEC", "").strip()
        if raw_env_timeout:
            try:
                parsed = int(raw_env_timeout)
                if parsed > 0:
                    inner_timeout = parsed
            except ValueError:
                pass
    inner = inner_timeout if inner_timeout is not None else LEAN_RUN_DEFAULT_TIMEOUT_SEC[mode]
    worst = inner
    if mode == "build" and slot_lock:
        worst += max(LEAN_RUN_SLOT_WAIT_FLOOR_SEC, inner)
    return max(timeout_sec, worst) + WRAPPER_TIMEOUT_GRACE_SEC


def _ensure_toolchain_path(env: dict[str, str]) -> None:
    """Ensure `~/.elan/bin`, `~/.cargo/bin`, and `~/.local/bin` are on `env["PATH"]`
    so cron/automation invocations with minimal `PATH` still locate `lake` and `cargo`."""
    raw_path = env.get("PATH", "")
    parts = [p for p in raw_path.split(os.pathsep) if p]
    try:
        home = Path.home()
    except (KeyError, RuntimeError):
        return
    prepend: list[str] = []
    for rel in (".elan/bin", ".cargo/bin", ".local/bin"):
        cand = str(home / rel)
        if cand not in parts and (home / rel).is_dir():
            prepend.append(cand)
    if prepend:
        env["PATH"] = os.pathsep.join([*prepend, *parts])


def _is_executable_file(path: Path) -> bool:
    try:
        return path.is_file() and os.access(path, os.X_OK)
    except OSError:
        return False


def _resolve_anneal_lean_run(
    repo_root: Path,
    env: Mapping[str, str] | None = None,
    home: Path | None = None,
) -> Path | None:
    """Resolve `anneal-lean-run` wrapper with strict precedence:
    1. `ANNEAL_LEAN_RUN` environment variable (executable regular file),
    2. Fleet-managed `anneal-lean-run` on `PATH` or `~/.local/bin/anneal-lean-run`
       (so cron environments with minimal `PATH` still prefer the fleet wrapper),
    3. Fallback to in-repo `repo_root / "scripts/anneal-lean-run"` (executable file).
    """
    env_map: Mapping[str, str] = os.environ if env is None else env

    # Steps run with `cwd=repo_root`, so a relative `ANNEAL_LEAN_RUN` or `PATH` hit is
    # anchored here, against the directory it was just found executable in.
    env_lean_run = env_map.get("ANNEAL_LEAN_RUN", "").strip()
    if env_lean_run:
        env_path = Path(env_lean_run)
        if _is_executable_file(env_path):
            return Path(os.path.abspath(env_path))

    raw_path = env_map.get("PATH", "")
    if raw_path:
        path_lean_run = shutil.which("anneal-lean-run", path=raw_path)
        if path_lean_run:
            found_path = Path(path_lean_run)
            if _is_executable_file(found_path):
                return Path(os.path.abspath(found_path))

    home_dir = home
    if home_dir is None:
        if env is None:
            try:
                home_dir = Path.home()
            except (KeyError, RuntimeError):
                home_dir = None
        else:
            raw_home = env_map.get("HOME", "").strip()
            home_dir = Path(raw_home) if raw_home else None
    if home_dir is not None:
        user_local = home_dir / ".local/bin/anneal-lean-run"
        if _is_executable_file(user_local):
            return user_local

    local_lean_run = repo_root / "scripts/anneal-lean-run"
    if _is_executable_file(local_lean_run):
        return local_lean_run
    return None


def _parse_cgroup_memory_limit_mib(path: Path, *, max_sentinel_bytes: int = 1 << 60) -> int | None:
    """Read a cgroup memory limit file (`memory.max`, `memory.high`, or
    `memory.limit_in_bytes`) returning the ceiling in MiB, or `None` if absent,
    unreadable, non-regular/symlink, `"max"`, or an unbounded kernel sentinel."""
    try:
        fd = os.open(os.fspath(path), os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except (OSError, ValueError):
        return None
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            return None
        raw = os.read(fd, 128).decode("utf-8", errors="replace").strip()
    except OSError:
        return None
    finally:
        os.close(fd)
    if not raw or raw == "max":
        return None
    try:
        val_bytes = int(raw)
    except ValueError:
        return None
    if val_bytes < 0 or val_bytes >= max_sentinel_bytes:
        return None
    return val_bytes // (1024 * 1024)


def _safe_cgroup_subpath(cgroup_root: Path, raw_rel: str) -> Path | None:
    """Join a `/proc/self/cgroup` relative path onto `cgroup_root` without
    allowing `..`, NUL bytes, or symlink traversal outside `cgroup_root`."""
    if "\x00" in raw_rel:
        return None
    rel = raw_rel.strip().lstrip("/")
    if not rel:
        return cgroup_root
    parts = [p for p in rel.split("/") if p and p != "."]
    if any(p == ".." for p in parts):
        return None
    cand = cgroup_root.joinpath(*parts)
    try:
        root_real = os.path.realpath(cgroup_root)
        # Walk down checking existing prefix components for symlink escapes.
        cur = cgroup_root
        for part in parts:
            cur = cur / part
            if cur.is_symlink():
                target_real = os.path.realpath(cur)
                if target_real != root_real and not target_real.startswith(root_real + os.sep):
                    return None
    except (OSError, ValueError):
        return None
    return cand


def _probe_effective_ram_ceiling_mib(
    *,
    proc_meminfo: Path = Path("/proc/meminfo"),
    proc_self_cgroup: Path = Path("/proc/self/cgroup"),
    cgroup_root: Path = Path("/sys/fs/cgroup"),
) -> int | None:
    """Probe the effective available RAM / cgroup memory ceiling in MiB.

    Takes the minimum finite MiB bound across:
    - Host `/proc/meminfo` `MemTotal` and `MemAvailable` (kB -> MiB),
    - Cgroup v2 `memory.max` and `memory.high` walked upward from the process's
      `0::` hierarchy to `cgroup_root` (ignoring `"max"` and unbounded sentinels),
    - Cgroup v1 `memory.limit_in_bytes` walked upward from any `:memory:`
      hierarchy under `cgroup_root / "memory"` (if present).

    Returns `None` only when no readable finite memory bound exists.
    """
    candidates_mib: list[int] = []

    try:
        meminfo_text = proc_meminfo.read_text(encoding="utf-8", errors="replace")
    except OSError:
        meminfo_text = ""
    for line in meminfo_text.splitlines():
        m = re.match(r"^(MemTotal|MemAvailable):\s+(\d+)\s+kB\b", line.strip())
        if m:
            candidates_mib.append(int(m.group(2)) // 1024)

    try:
        cg_text = proc_self_cgroup.read_text(encoding="utf-8", errors="replace")
    except OSError:
        cg_text = ""

    v2_rel: str | None = None
    v1_mem_rel: str | None = None
    for line in cg_text.splitlines():
        parts = line.split(":", 2)
        if len(parts) != 3:
            continue
        hier_id, controllers, rel_path = parts
        if hier_id == "0" and controllers == "":
            v2_rel = rel_path
        elif "memory" in controllers.split(","):
            v1_mem_rel = rel_path

    if v2_rel is not None and cgroup_root.is_dir():
        cur = _safe_cgroup_subpath(cgroup_root, v2_rel)
        while cur is not None:
            for cg_file in ("memory.max", "memory.high"):
                lim = _parse_cgroup_memory_limit_mib(cur / cg_file, max_sentinel_bytes=1 << 60)
                if lim is not None:
                    candidates_mib.append(lim)
            if cur == cgroup_root:
                break
            parent = cur.parent
            if parent == cur:
                break
            cur = parent

    v1_root = cgroup_root / "memory"
    if v1_mem_rel is not None and v1_root.is_dir():
        cur = _safe_cgroup_subpath(v1_root, v1_mem_rel)
        while cur is not None:
            lim = _parse_cgroup_memory_limit_mib(
                cur / "memory.limit_in_bytes", max_sentinel_bytes=1 << 50
            )
            if lim is not None:
                candidates_mib.append(lim)
            if cur == v1_root:
                break
            parent = cur.parent
            if parent == cur:
                break
            cur = parent

    return min(candidates_mib) if candidates_mib else None


def _probe_lean_run_memory_max_mib(
    cmd: list[str],
    *,
    env: Mapping[str, str] | None = None,
    cwd: Path | None = None,
    timeout_sec: float = 20.0,
) -> int | None:
    """`MemoryMax` (MiB) that the `anneal-lean-run` wrapper of `cmd` plans for the
    scope it runs the wrapped command in (`memory_max_mb` of `<wrapper> <its options>
    --probe --json`, which never runs the command), or `None` if `cmd` is not wrapped
    or the probe fails. The suite process is outside that scope, so its own cgroup
    hierarchy cannot show this cap."""
    if not _is_lean_run_wrapped(cmd):
        return None
    opts: list[str] = []
    i, n = 1, len(cmd)
    while i < n:
        tok = cmd[i]
        if tok == "--" or tok == "-" or not tok.startswith("-"):
            break
        opts.append(tok)
        if "=" not in tok and _resolve_lean_run_opt(tok) in _LEAN_RUN_VALUE_OPTS and i + 1 < n:
            opts.append(cmd[i + 1])
            i += 1
        i += 1
    try:
        out = subprocess.run(
            [cmd[0], *opts, "--probe", "--json"],
            cwd=None if cwd is None else str(cwd),
            env=None if env is None else dict(env),
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            errors="replace",
            timeout=timeout_sec,
            check=False,
        )
        limits = json.loads(out.stdout) if out.returncode == 0 else None
    except (OSError, subprocess.SubprocessError, ValueError):
        return None
    mem_max = limits.get("memory_max_mb") if isinstance(limits, dict) else None
    if isinstance(mem_max, int) and not isinstance(mem_max, bool) and mem_max > 0:
        return mem_max
    return None


def _build_step_env(
    step_name: str,
    *,
    base_env: Mapping[str, str] | None = None,
    env_overrides: Mapping[str, str] | None = None,
    effective_ram_mib: int | None | object = _RAM_UNSET,
    cmd: list[str] | None = None,
    cwd: Path | None = None,
) -> dict[str, str]:
    """Build an isolated subprocess environment for suite step `step_name`.

    - Always populates toolchain dirs on `PATH` without mutating `os.environ`.
    - Always sets `LAKE_ARTIFACT_CACHE=true` and `LAKE_RESTORE_ARTIFACTS=true`
      so Lake 4.34.1 restores cached `.olean`s into workspace build dirs.
    - For `lake_build_lean_miri_spec`, injects `LEAN_NUM_THREADS=1` whenever the
      effective RAM ceiling is `< 10240 MiB` (`< 10 GiB`), while preserving normal
      multi-threaded builds on `>= 10 GiB` hosts. Unless `effective_ram_mib` is given,
      the ceiling is the tightest of the host/cgroup probe and, for an
      `anneal-lean-run`-wrapped step `cmd`, the `MemoryMax` the wrapper plans for it.
    - Explicit `env_overrides` take final precedence.
    """
    env = dict(os.environ if base_env is None else base_env)
    _ensure_toolchain_path(env)
    env.update(LAKE_ARTIFACT_CACHE_ENV)
    if step_name == "lake_build_lean_miri_spec":
        if effective_ram_mib is _RAM_UNSET:
            ceilings = [
                mib
                for mib in (
                    _probe_effective_ram_ceiling_mib(),
                    _probe_lean_run_memory_max_mib(cmd, env=env, cwd=cwd) if cmd else None,
                )
                if mib is not None
            ]
            ram_mib: int | None | object = min(ceilings) if ceilings else None
        else:
            ram_mib = effective_ram_mib
        if (
            isinstance(ram_mib, int)
            and not isinstance(ram_mib, bool)
            and ram_mib < LEAN_MIRI_SPEC_SINGLE_THREAD_RAM_THRESHOLD_MIB
        ):
            env["LEAN_NUM_THREADS"] = "1"
    if env_overrides:
        env.update(env_overrides)
    return env


def _lake_mix_hash(a: int, b: int) -> int:
    """Lake's `mixHash a b` (`lean_uint64_mix_hash`)."""
    mask, mul = _LAKE_HASH_MASK, _LAKE_HASH_MUL
    k = (b * mul) & mask
    k ^= k >> 47
    k ^= mul
    return ((a ^ k) * mul) & mask


def _lake_bytes_hash_hex(data: bytes) -> str:
    """Lake's `Hash.ofByteArray data` (also `Hash.ofString` of UTF-8 `data`), as the
    16-digit lowercase hex Lake writes to `.trace` and `.hash` files."""
    mask, mul = _LAKE_HASH_MASK, _LAKE_HASH_MUL
    size = len(data)
    body = size & ~7
    h = (_LAKE_HASH_SEED ^ (size * mul)) & mask
    for (k,) in struct.iter_unpack("<Q", memoryview(data)[:body]):
        k = (k * mul) & mask
        k ^= k >> 47
        h = ((h ^ ((k * mul) & mask)) * mul) & mask
    if body != size:
        h = ((h ^ int.from_bytes(data[body:], "little")) * mul) & mask
    h ^= h >> 47
    h = (h * mul) & mask
    h ^= h >> 47
    return f"{_lake_mix_hash(_LAKE_HASH_NIL, h):016x}"


def _lake_text_hash_hex(data: bytes) -> str:
    """Lake's `Hash.ofText` (`computeTextFileHash`): the hash of `data` with `\\r\\n`
    normalized to `\\n`, which is how Lake hashes a module's `.lean` source."""
    return _lake_bytes_hash_hex(data.replace(b"\r\n", b"\n"))


def _lake_trace_recorded_hashes(
    trace_text: str, rel_mod: str
) -> tuple[str | None, dict[str, str]] | None:
    """`(source_text_hash, {olean_part_suffix: content_hash})` recorded by Lake in the
    `.trace` of module `rel_mod` (`Lib/Sub/Mod`), or `None` if the trace is malformed.

    A trace Lake wrote after building the module (`BuildMetadata.ofBuild`) must name
    exactly one `<...>/<rel_mod>.lean` input. The synthetic trace Lake writes when it
    fetches the module's artifacts from its cache (`BuildMetadata.ofFetch`:
    `"synthetic": true`, no `inputs`) records no source hash: `source_text_hash` is
    `None`. Either kind must name a well-formed `.olean` output."""
    try:
        doc = json.loads(trace_text)
    except ValueError:
        return None
    if not isinstance(doc, dict):
        return None
    inputs, outputs = doc.get("inputs"), doc.get("outputs")
    if not isinstance(inputs, list) or not isinstance(outputs, dict):
        return None
    src_hash: str | None = None
    if not (doc.get("synthetic") is True and not inputs):
        src_name = f"{rel_mod}.lean"
        src_hashes = [
            item[1]
            for item in inputs
            if isinstance(item, list)
            and len(item) == 2
            and isinstance(item[0], str)
            and (item[0] == src_name or item[0].replace("\\", "/").endswith("/" + src_name))
        ]
        if (
            len(src_hashes) != 1
            or not isinstance(src_hashes[0], str)
            or not _LAKE_HASH_HEX_RE.fullmatch(src_hashes[0])
        ):
            return None
        src_hash = src_hashes[0]
    descrs = outputs.get("o")
    if isinstance(descrs, str):
        descrs = [descrs]
    if not isinstance(descrs, list):
        return None
    olean_hashes: dict[str, str] = {}
    for descr in descrs:
        if not isinstance(descr, str):
            return None
        content_hash, _dot, ext = descr.partition(".")
        suffix = f".{ext}"
        if (
            not _LAKE_HASH_HEX_RE.fullmatch(content_hash)
            or suffix not in _LEAN_OLEAN_PART_SUFFIXES
            or suffix in olean_hashes
        ):
            return None
        olean_hashes[suffix] = content_hash
    if ".olean" not in olean_hashes:
        return None
    return src_hash, olean_hashes


def _private_regular_file_stat(path: str) -> os.stat_result | None:
    """`lstat` of `path` if it is a regular file with a single hard link, else `None`.
    Lake never links its `.trace` / `.hash` bookkeeping files, so a second link means
    another tree (a `cp -al`-seeded cache) can rewrite the file in place."""
    try:
        st = os.lstat(path)
    except OSError:
        return None
    return st if stat.S_ISREG(st.st_mode) and st.st_nlink == 1 else None


def _read_private_regular_file(path: str) -> tuple[bytes, int] | None:
    """`(content, st_mtime_ns)` of `path` if it is a regular file with a single hard link
    (see `_private_regular_file_stat`), else `None`. Never follows a symlink at `path`,
    never blocks on a FIFO there, handles POSIX short reads, and rejects files that grow
    or shrink while being read."""
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except OSError:
        return None
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
            return None
        expected = st.st_size
        chunks: list[bytes] = []
        total = 0
        # Read up to `expected + 1` bytes so both short reads and concurrent growth are caught.
        while total <= expected:
            chunk = os.read(fd, max(1, expected + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
        if total != expected:
            return None
        data = b"" if not chunks else (chunks[0] if len(chunks) == 1 else b"".join(chunks))
        return data, st.st_mtime_ns
    except OSError:
        return None
    finally:
        os.close(fd)


def _lake_records_prove_source_unchanged(
    rel_mod: str, arts: Mapping[str, str], src_path: str, src_mtime_ns: int
) -> bool:
    """Whether Lake's own bookkeeping shows that module `rel_mod`'s `.olean` parts were
    built from exactly the current content of `src_path` (last modified at
    `src_mtime_ns`), although the `.olean` is older than the source.

    Lake hard-links cached artifacts into `.lake/build/lib/lean/` (`LAKE_RESTORE_ARTIFACTS`),
    so a restored `.olean` keeps the mtime of whichever checkout first built it, and a
    source that `git` merely rewrote looks newer although nothing changed. Lake itself
    decides freshness by content hash, and so does this check. It accepts the module only
    on positive evidence, when all of the following hold:

    - the module's `.trace` is a private regular file naming its `.olean` parts with
      hashes `h_out`;
    - every `.olean` part on disk is one the trace names, and its private `.hash`
      sidecar (the hash Lake trusts for the file) is not older than it and equals `h_out`;
    - the trace ties those parts to this source: a build trace names the source with
      Lake's text hash of its current content; a cache-fetch trace names no input, but
      Lake computed the module's input hash from the source when it wrote the trace, so
      the trace must not be older than the source.
    """
    trace_path = arts.get(".trace")
    trace = None if trace_path is None else _read_private_regular_file(trace_path)
    if trace is None:
        return False
    trace_bytes, trace_mtime_ns = trace
    recorded = _lake_trace_recorded_hashes(trace_bytes.decode("utf-8", errors="replace"), rel_mod)
    if recorded is None:
        return False
    src_hash, olean_hashes = recorded
    if {sfx for sfx in arts if sfx in _LEAN_OLEAN_PART_SUFFIXES} != set(olean_hashes):
        return False
    for suffix, content_hash in olean_hashes.items():
        sidecar_path = arts.get(f"{suffix}.hash")
        sidecar = None if sidecar_path is None else _read_private_regular_file(sidecar_path)
        if sidecar is None:
            return False
        sidecar_bytes, sidecar_mtime_ns = sidecar
        try:
            if sidecar_mtime_ns < os.stat(arts[suffix]).st_mtime_ns:
                return False
        except OSError:
            return False
        if sidecar_bytes[:64].decode("ascii", errors="replace").strip() != content_hash:
            return False
    if src_hash is None:
        return trace_mtime_ns >= src_mtime_ns
    try:
        with open(src_path, "rb") as fh:
            return _lake_text_hash_hex(fh.read()) == src_hash
    except OSError:
        return False


def _lake_trace_import_art_hashes(trace: bytes) -> dict[str, str]:
    """Extract `{Dep/Sub/Mod: importAllArts_hex}` from a non-synthetic Lake build
    `.trace`, or `{}` for synthetic/fetch/malformed traces. A trace that never mentions
    `:importAllArts` (every cache-fetch trace, every import-free module) is not parsed."""
    if b':importAllArts"' not in trace:
        return {}
    try:
        doc = json.loads(trace)
    except (ValueError, RecursionError):
        return {}
    if not isinstance(doc, dict) or doc.get("synthetic") is True:
        return {}
    inputs = doc.get("inputs")
    if not isinstance(inputs, list):
        return {}
    dep_hashes: dict[str, str] = {}
    for item in inputs:
        if not (isinstance(item, list) and len(item) == 2 and item[0] == "deps" and isinstance(item[1], list)):
            continue
        for dep_entry in item[1]:
            if not (
                isinstance(dep_entry, list)
                and len(dep_entry) == 2
                and dep_entry[0] == "imports"
                and isinstance(dep_entry[1], list)
            ):
                continue
            for imp_entry in dep_entry[1]:
                if not (
                    isinstance(imp_entry, list)
                    and len(imp_entry) == 2
                    and isinstance(imp_entry[0], str)
                    and isinstance(imp_entry[1], str)
                    and imp_entry[0].endswith(":importAllArts")
                    and _LAKE_HASH_HEX_RE.fullmatch(imp_entry[1])
                ):
                    continue
                mod_name = imp_entry[0][: -len(":importAllArts")]
                if mod_name:
                    dep_hashes[mod_name.replace(".", "/")] = imp_entry[1]
    return dep_hashes


def _lean_import_all_arts_parts(arts: Mapping[str, str]) -> tuple[str, ...] | None:
    """Suffixes of the artifacts of a module whose content hashes Lake mixes, in this
    order, into its `importAllArts` trace: `(".olean",)` for a classic module, all of
    `_LEAN_IMPORT_ALL_ARTS_MODULE_PARTS` for a module-system one. `None` for any other
    set of files (a torn module, or a layout this Lake version does not produce)."""
    parts = tuple(sfx for sfx in _LEAN_IMPORT_ALL_ARTS_MODULE_PARTS if sfx in arts)
    return parts if parts in ((".olean",), _LEAN_IMPORT_ALL_ARTS_MODULE_PARTS) else None


def _lean_import_all_arts_recorded_ns(arts: Mapping[str, str]) -> int | None:
    """When Lake last (re)recorded a content hash that enters the module's
    `importAllArts` trace: the newest `st_mtime_ns` of the private `.hash` sidecars of
    `_lean_import_all_arts_parts`, or `None` if one is missing or not private."""
    parts = _lean_import_all_arts_parts(arts)
    if parts is None:
        return None
    newest: int | None = None
    for sfx in parts:
        sidecar_path = arts.get(f"{sfx}.hash")
        sidecar_st = None if sidecar_path is None else _private_regular_file_stat(sidecar_path)
        if sidecar_st is None:
            return None
        if newest is None or sidecar_st.st_mtime_ns > newest:
            newest = sidecar_st.st_mtime_ns
    return newest


def _lean_module_current_import_all_arts_hex(arts: Mapping[str, str]) -> str | None:
    """Lake's current `importAllArts` trace hash of a module (16 hex digits): `Hash.nil`
    mixed with the content hash of each of `_lean_import_all_arts_parts` in order, read
    from the private `.hash` sidecars Lake itself trusts (each not older than its
    artifact). `None` if the module's files do not let this be verified."""
    parts = _lean_import_all_arts_parts(arts)
    if parts is None:
        return None
    acc = _LAKE_HASH_NIL
    for sfx in parts:
        sidecar_path = arts.get(f"{sfx}.hash")
        sidecar = None if sidecar_path is None else _read_private_regular_file(sidecar_path)
        if sidecar is None:
            return None
        try:
            if sidecar[1] < os.stat(arts[sfx]).st_mtime_ns:
                return None
        except OSError:
            return None
        content_hash = sidecar[0][:64].decode("ascii", errors="replace").strip()
        if not _LAKE_HASH_HEX_RE.fullmatch(content_hash):
            return None
        acc = _lake_mix_hash(acc, int(content_hash, 16))
    return f"{acc:016x}"


def _lean_artifact_module_stem(path: Path) -> Path:
    """Strip the longest matching `_LEAN_ARTIFACT_SUFFIXES` suffix from `path`."""
    name = path.name
    for suffix in sorted(_LEAN_ARTIFACT_SUFFIXES, key=len, reverse=True):
        if name.endswith(suffix):
            return path.with_name(name[: -len(suffix)])
    return path


def _lake_lib_src_dirs(lake_root: Path, repo_root: Path) -> tuple[dict[str, list[str]], list[str]]:
    """Map top-level Lean module-name components to source directories from
    `lakefile.toml` (`lean_lib` names and `roots`), plus ordered fallback source roots
    for synthetic/partial trees."""
    by_lib: dict[str, list[str]] = {}

    def add(top: str, src_dir: str) -> None:
        dirs = by_lib.setdefault(top, [])
        if src_dir not in dirs:
            dirs.append(src_dir)

    try:
        cfg = tomllib.loads((lake_root / "lakefile.toml").read_text(encoding="utf-8"))
        libs = cfg.get("lean_lib", [])
        for lib in libs if isinstance(libs, list) else []:
            if not isinstance(lib, dict) or not lib.get("name"):
                continue
            src_dir = os.path.realpath(lake_root / str(lib.get("srcDir", ".")))
            add(str(lib["name"]), src_dir)
            roots = lib.get("roots")
            for root_mod in roots if isinstance(roots, list) else []:
                if isinstance(root_mod, str) and root_mod:
                    add(root_mod.split(".", 1)[0], src_dir)
    except (OSError, ValueError, TypeError, KeyError):
        by_lib = {}
    fallbacks = [os.path.realpath(repo_root / rel) for rel in _LEAN_SOURCE_FALLBACK_DIRS]
    return by_lib, fallbacks


def _find_lean_source_for_module(
    rel_mod: str,
    by_lib: Mapping[str, list[str]],
    fallbacks: list[str],
) -> tuple[str, int] | None:
    """`(path, st_mtime_ns)` of the `.lean` source of module `rel_mod` (`Lib/Sub/Mod`)."""
    rel_lean = f"{rel_mod}.lean"
    seen: set[str] = set()
    for base in (*by_lib.get(rel_mod.partition("/")[0], ()), *fallbacks):
        if base in seen:
            continue
        seen.add(base)
        cand = os.path.join(base, rel_lean)
        try:
            st = os.stat(cand)
        except OSError:
            continue
        if stat.S_ISREG(st.st_mode):
            return cand, st.st_mtime_ns
    return None


def _scan_lean_module_artifacts(lib_lean_dir: str) -> dict[str, dict[str, str]]:
    """`{Lib/Sub/Mod: {suffix: path}}` for every `_LEAN_ARTIFACT_SUFFIXES` file under
    `lib_lean_dir`, never descending into symlinked directories."""
    modules: dict[str, dict[str, str]] = {}
    stack = [(lib_lean_dir, "")]
    while stack:
        dir_path, prefix = stack.pop()
        try:
            with os.scandir(dir_path) as entries:
                for entry in entries:
                    name = entry.name
                    try:
                        if entry.is_dir(follow_symlinks=False):
                            stack.append((entry.path, f"{prefix}{name}/"))
                            continue
                    except OSError:
                        continue
                    stem, dot, ext = name.partition(".")
                    if stem and dot and (suffix := f".{ext}") in _LEAN_ARTIFACT_SUFFIXES:
                        modules.setdefault(prefix + stem, {})[suffix] = entry.path
        except OSError:
            continue
    return modules


def _lean_module_artifact_mtime_ns(arts: Mapping[str, str]) -> int | None:
    """Representative `st_mtime_ns` of a module's primary artifacts: its `.olean`, else
    the oldest other primary artifact; `None` if one is unreadable (a broken symlink)."""
    paths = (
        [arts[".olean"]]
        if ".olean" in arts
        else [arts[sfx] for sfx in _LEAN_PRIMARY_ARTIFACT_SUFFIXES if sfx in arts]
    )
    try:
        return min(os.stat(path).st_mtime_ns for path in paths)
    except OSError:
        return None


def clean_stale_oleans(repo_root: Path) -> list[Path]:
    """Pre-flight `.olean` freshness coherence guard across workspace Lake roots
    (`.` and `examples`).

    A module `<Mod>` of `<lake_root>/.lake/build/lib/lean/` is stale, and every one of
    its files there is removed (`.olean`, `.olean.server`, `.olean.private`, `.ilean`,
    `.ir`, `.ir.sig`, `.ltar` and their `.hash` / `.trace` companions, so Lake rebuilds
    it or restores it from its artifact cache), when either:

    1. a primary artifact is unreadable, or its `.lean` source (under `trusted/lean/`,
       `theory/`, `minirust/lean/`, `lean-miri/` or `examples/`) has `mtime > olean_mtime`
       and Lake's own records do not prove the source unchanged
       (`_lake_records_prove_source_unchanged`), or
    2. it can depend on `Trusted` (any library but vendored `Miri`) and some `Trusted`
       module of the same Lake root is stale by rule 1 or 3: every downstream `.olean` of
       that root is then stale against `Trusted`, or
    3. Lake built it (its private `.trace` is a build trace, which records the
       `<Dep>:importAllArts` hash of each direct import) and either a recorded import is
       itself stale, or that import's artifacts were re-recorded after the trace was
       written (a `.hash` sidecar of `_lean_import_all_arts_parts` is newer than the
       trace) with a different `importAllArts` hash: the import was rebuilt without the
       module, e.g. by a partial `lake build Trusted`.

    Rule 1's check of Lake's records is what keeps the guard a no-op on coherent trees
    whose mtimes are not: artifacts Lake restored by hard link, a cache seeded from another
    worktree, or sources `git` rewrote without changing. Rule 2 deliberately compares
    each `Trusted` `.olean` with its own source rather than with the newest
    `trusted/lean/**/*.lean` file: Lake rebuilds only the importers of an edited module,
    so every unrelated `Trusted` `.olean` legitimately stays older than that edit, and
    comparing against it would wipe the whole root on every run from then on. Rule 3
    covers what that leaves open, and asks for both a newer sidecar and a different hash
    so that neither alone removes anything: Lake rewrites sidecars without rebuilding,
    and a hash computed by a formula this Lake version no longer uses would otherwise
    disagree with every trace on every run. A module Lake restored from its cache has a
    synthetic trace that names no import, so rule 3 leaves it to Lake.

    Never follows directory symlinks or deletes anything outside
    `<lake_root>/.lake/build/lib/lean/`; when no source is newer than its `.olean`
    (or there are no `.olean`s) it only stats files and reads each module's `.trace`.
    """
    removed: list[str] = []
    for lake_root in (repo_root, repo_root / "examples"):
        lake_dir = lake_root / ".lake"
        lib_lean_dir = lake_dir / "build" / "lib" / "lean"
        if any(p.is_symlink() for p in (lake_dir, lake_dir / "build", lib_lean_dir.parent, lib_lean_dir)):
            continue
        if not lib_lean_dir.is_dir():
            continue
        lib_lean_real = os.path.realpath(lib_lean_dir)
        modules = _scan_lean_module_artifacts(os.fspath(lib_lean_dir))
        if not modules:
            continue
        by_lib, fallbacks = _lake_lib_src_dirs(lake_root, repo_root)

        tops: dict[str, str] = {}
        stale: set[str] = set()
        for rel_mod, arts in modules.items():
            if _LEAN_PRIMARY_ARTIFACT_SUFFIXES.isdisjoint(arts):
                continue
            tops[rel_mod] = rel_mod.partition("/")[0]
            art_ns = _lean_module_artifact_mtime_ns(arts)
            if art_ns is None:
                stale.add(rel_mod)
                continue
            src = _find_lean_source_for_module(rel_mod, by_lib, fallbacks)
            if (
                src is not None
                and src[1] > art_ns
                and not _lake_records_prove_source_unchanged(rel_mod, arts, src[0], src[1])
            ):
                stale.add(rel_mod)
        if any(tops[rel_mod] == _TRUSTED_LIB for rel_mod in stale):
            stale.update(
                rel_mod for rel_mod, top in tops.items() if top not in _TRUSTED_INDEPENDENT_LIBS
            )

        # Rule 3: Lake build-trace import-hash coherence (see the docstring).
        dep_edges: dict[str, tuple[int, dict[str, str]]] = {}
        for rel_mod, arts in modules.items():
            if rel_mod in stale or rel_mod not in tops:
                continue
            trace_path = arts.get(".trace")
            trace = None if trace_path is None else _read_private_regular_file(trace_path)
            if trace is None:
                continue
            imports = _lake_trace_import_art_hashes(trace[0])
            if imports:
                dep_edges[rel_mod] = (trace[1], imports)

        recorded_ns: dict[str, int | None] = {}
        current_hex: dict[str, str | None] = {}
        missing_local_dep: dict[str, bool] = {}
        for rel_mod, (trace_ns, imports) in dep_edges.items():
            for dep_mod, recorded_hex in imports.items():
                if dep_mod in stale:
                    stale.add(rel_mod)
                    break
                dep_arts = modules.get(dep_mod)
                if dep_arts is None or ".olean" not in dep_arts:
                    is_local = missing_local_dep.get(dep_mod)
                    if is_local is None:
                        dep_top = dep_mod.partition("/")[0]
                        if by_lib:
                            is_local = dep_top in by_lib
                        else:
                            is_local = (
                                dep_top not in ("Init", "Std", "Lean", "Lake")
                                and _find_lean_source_for_module(dep_mod, by_lib, fallbacks) is not None
                            )
                        missing_local_dep[dep_mod] = is_local
                    if is_local:
                        stale.add(rel_mod)
                        break
                    continue
                if dep_mod not in recorded_ns:
                    recorded_ns[dep_mod] = _lean_import_all_arts_recorded_ns(dep_arts)
                dep_ns = recorded_ns[dep_mod]
                if dep_ns is None or dep_ns <= trace_ns:
                    continue
                if dep_mod not in current_hex:
                    current_hex[dep_mod] = _lean_module_current_import_all_arts_hex(dep_arts)
                dep_hex = current_hex[dep_mod]
                if dep_hex is not None and dep_hex != recorded_hex:
                    stale.add(rel_mod)
                    break

        changed = True
        while changed:
            changed = False
            for rel_mod, (_trace_ns, imports) in dep_edges.items():
                if rel_mod not in stale and not stale.isdisjoint(imports):
                    stale.add(rel_mod)
                    changed = True
            if any(tops[rel_mod] == _TRUSTED_LIB for rel_mod in stale):
                before = len(stale)
                stale.update(
                    rel_mod for rel_mod, top in tops.items() if top not in _TRUSTED_INDEPENDENT_LIBS
                )
                changed = changed or len(stale) != before

        for rel_mod in sorted(stale):
            for art_path in sorted(modules[rel_mod].values()):
                parent_real = os.path.realpath(os.path.dirname(art_path))
                if parent_real != lib_lean_real and not parent_real.startswith(lib_lean_real + os.sep):
                    continue
                try:
                    os.unlink(art_path)
                except FileNotFoundError:
                    pass
                except OSError:
                    continue
                removed.append(art_path)

    return sorted(Path(p) for p in removed)


def _preflight_clean_stale_oleans(repo_root: Path) -> list[Path]:
    """Run `clean_stale_oleans` before the suite's Lake/Lean steps, reporting what it
    removed on stderr. The guard is best-effort: a failure in it is reported, and the
    steps still run (Lake then decides freshness on its own)."""
    try:
        removed = clean_stale_oleans(repo_root)
    except Exception as exc:  # noqa: BLE001 - never let the pre-flight abort the suite
        sys.stderr.write(f"[nightly-suite] stale .olean pre-flight failed ({type(exc).__name__}: {exc})\n")
        return []
    if removed:
        by_mod: dict[Path, list[Path]] = {}
        for p in removed:
            by_mod.setdefault(_lean_artifact_module_stem(p), []).append(p)
        reps = [
            next((p for p in paths if p.name.endswith(".olean")), sorted(paths)[0])
            for _mod, paths in sorted(by_mod.items())
        ]
        shown = ", ".join(os.path.relpath(p, repo_root) for p in reps[:5])
        more = f", ... (+{len(reps) - 5} more)" if len(reps) > 5 else ""
        sys.stderr.write(
            f"[nightly-suite] stale .olean pre-flight removed {len(removed)} artifact file(s) "
            f"of {len(reps)} module(s): {shown}{more}\n"
        )
    return removed


def _signal_process_group(pgid: int, sig: int) -> None:
    try:
        os.killpg(pgid, sig)
    except (ProcessLookupError, PermissionError):
        pass


def _process_group_alive(pgid: int) -> bool:
    try:
        os.killpg(pgid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def _terminate_step(proc: subprocess.Popen[str]) -> None:
    """Stop a step started with `start_new_session=True`: `SIGTERM` its whole process
    group (an `anneal-lean-run` wrapper forwards it to the separate-session group it
    created and reaps it), wait up to `STEP_TERMINATE_GRACE_SEC` for the entire group
    to exit, then `SIGKILL` any survivors. A bare `Popen.kill()` would `SIGKILL` only
    the direct child, orphaning the build (still holding RAM, while the wrapper's
    released build slot admits the next step)."""
    pgid = proc.pid
    deadline = time.monotonic() + STEP_TERMINATE_GRACE_SEC
    _signal_process_group(pgid, signal.SIGTERM)
    try:
        proc.wait(timeout=max(0.0, deadline - time.monotonic()))
    except subprocess.TimeoutExpired:
        pass
    while _process_group_alive(pgid) and time.monotonic() < deadline:
        time.sleep(0.02)
    if proc.poll() is None or _process_group_alive(pgid):
        _signal_process_group(pgid, signal.SIGKILL)
    if proc.poll() is None:
        try:
            proc.wait(timeout=STEP_TERMINATE_GRACE_SEC)
        except subprocess.TimeoutExpired:
            pass


def _as_text(data: str | bytes | None) -> str:
    if data is None:
        return ""
    if isinstance(data, bytes):
        return data.decode("utf-8", errors="replace")
    return data


def _run_step(
    name: str,
    category: str,
    cmd: list[str],
    cwd: Path,
    timeout_sec: int = 900,
    env_overrides: dict[str, str] | None = None,
) -> dict[str, Any]:
    t0 = time.monotonic()
    env = _build_step_env(name, env_overrides=env_overrides, cmd=cmd, cwd=cwd)
    outer_timeout = _outer_timeout_sec(cmd, timeout_sec, env=env)
    timed_out = False
    try:
        proc = subprocess.Popen(
            cmd,
            cwd=str(cwd),
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            errors="replace",
            start_new_session=True,
        )
    except OSError as exc:
        return {
            "name": name,
            "category": category,
            "status": "FAIL",
            "exit_code": 127,
            "duration_sec": round(time.monotonic() - t0, 2),
            "command": " ".join(cmd),
            "audit_tags": [],
            "failure_excerpt": f"Failed to launch {cmd[0] if cmd else '<empty>'}: {exc}",
        }
    try:
        try:
            out, err = proc.communicate(timeout=outer_timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            _terminate_step(proc)
            try:
                out, err = proc.communicate(timeout=STEP_PIPE_DRAIN_SEC)
            except subprocess.TimeoutExpired as drain_exc:
                # An escaped descendant still holds the pipes open: keep what was read.
                out, err = _as_text(drain_exc.output), _as_text(drain_exc.stderr)
                for stream in (proc.stdout, proc.stderr):
                    if stream is not None:
                        stream.close()
    except BaseException:
        # Ctrl-C / SystemExit: never leave the detached step group running.
        _terminate_step(proc)
        raise
    elapsed = round(time.monotonic() - t0, 2)
    out, err = _as_text(out), _as_text(err)
    combined_out = (out + "\n" + err).strip()
    if timed_out:
        tail_lines = "\n".join(combined_out.splitlines()[-39:])
        excerpt = (
            f"{tail_lines}\nTimed out after {elapsed}s (step budget {timeout_sec}s, "
            f"outer deadline {outer_timeout}s)"
        ).strip()
        return {
            "name": name,
            "category": category,
            "status": "TIMEOUT",
            "exit_code": 124,
            "duration_sec": elapsed,
            "command": " ".join(cmd),
            "audit_tags": [],
            "failure_excerpt": excerpt,
        }
    returncode = proc.returncode
    if returncode == 0:
        status = "PASS"
    elif returncode == 124:
        status = "TIMEOUT"
    else:
        status = "FAIL"
    tail_lines = "\n".join(combined_out.splitlines()[-40:]) if status != "PASS" else ""
    if status == "TIMEOUT" and not tail_lines:
        tail_lines = f"Timed out after {timeout_sec}s"
    # Extract any `[...-AUDIT]` lines when running `MiniRustSpec`
    audit_tags = [
        line.strip()
        for line in combined_out.splitlines()
        if any(
            tag in line
            for tag in (
                "[ANCHOR-AUDIT]",
                "[SIMULATION-AUDIT]",
                "[WITNESS-AUDIT]",
                "[POINTER-AUDIT]",
                "[REF-AUDIT]",
                "[TB-AUDIT]",
                "[PROV-AUDIT]",
                "[DEINIT-AUDIT]",
                "[IMPORT-ISOLATION]",
                "[ADT-AUDIT-COVERAGE]",
                "[ANNEAL-AXIOMS]",
            )
        )
    ]
    return {
        "name": name,
        "category": category,
        "status": status,
        "exit_code": returncode,
        "duration_sec": elapsed,
        "command": " ".join(cmd),
        "audit_tags": audit_tags,
        "failure_excerpt": tail_lines,
    }


# Standalone `nightly` Lean test files. `lake env lean` never builds imports, so each
# module they import needs an up-to-date `.olean` before they run; `Anneal.ByteCodec`,
# `Anneal.Mir.Cast` and `Anneal.Mir.AdtAndControl` are outside the
# `Trusted`/`Anneal`/`MiniRust` import closure, and so are the `Correspondence` /
# `MiniRustSpec` modules imported by `MirUntestedVariantCorrespondenceTests.lean`
# (`Anneal.SepLogicLenses`, `Anneal.MirLoops` and `Anneal.MirFuelFree` are inside it).
MIR_STANDALONE_LEAN_TESTS: tuple[tuple[str, str], ...] = (
    ("tests_mir_bit_validity_stage1", "tests/mir/BitValidityStage1Tests.lean"),
    ("tests_mir_byte_codec", "tests/mir/ByteCodecTests.lean"),
    ("tests_mir_cast_stage1", "tests/mir/CastStage1Tests.lean"),
    ("tests_mir_adt_and_control", "tests/mir/AdtAndControlTests.lean"),
    ("tests_mir_slice_wide_ptr_lens", "tests/mir/MirSliceWidePtrLensTests.lean"),
    ("tests_mir_untested_variant_correspondence", "tests/mir/MirUntestedVariantCorrespondenceTests.lean"),
)
CORE_THEORY_LIBS: tuple[str, ...] = ("Trusted", "Anneal", "MiniRust")
_LOCAL_LEAN_LIB_FALLBACK: tuple[str, ...] = (
    "Trusted",
    "Anneal",
    "MiniRust",
    "Correspondence",
    "MiniRustSpec",
)
# Used only if a test header is unreadable (the unit tests keep it in sync): the first-seen
# ordered union of the workspace-library imports of every `MIR_STANDALONE_LEAN_TESTS` header.
_MIR_TEST_MODULE_FALLBACK: tuple[str, ...] = (
    "Anneal.BitValidity",
    "Anneal.ByteCodec",
    "Anneal.Mir.Cast",
    "Anneal.Mir.AdtAndControl",
    "Anneal.SepLogicLenses",
    "Anneal.MirLoops",
    "Trusted",
    "Anneal.MirFuelFree",
    "Correspondence.V2026_06_01.L3_PlacesAndBasicMem",
    "Correspondence.V2026_06_01.L5_ControlAndCalls",
    "MiniRustSpec.Correspondence.Translate",
)
_LEAN_HEADER_TOKEN_RE = re.compile(r"(?:«[^»\n]*»|[^\s«])+")


def _strip_lean_comments(text: str) -> str:
    """`text` with `--` line comments and (nested) `/- ... -/` block comments blanked,
    while preserving `«...»` guillemet identifiers that contain `--` or `/-`."""
    out: list[str] = []
    i, n = 0, len(text)
    while i < n:
        if text[i] == "«":
            end_g = text.find("»", i + 1)
            if end_g != -1 and text.find("\n", i + 1, end_g) == -1:
                out.append(text[i : end_g + 1])
                i = end_g + 1
            else:
                out.append("«")
                i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
            out.append(" ")
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(" ")
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def _lean_header_imports(path: Path, max_chars: int = 16384) -> list[str] | None:
    """Module names imported by the header of Lean file `path` (`[module] [prelude]`
    followed by `[public] [meta] import [all] <Module>` commands), or `None` if the
    file cannot be read."""
    try:
        with path.open(encoding="utf-8", errors="replace") as fh:
            head = fh.read(max_chars).lstrip("\ufeff")
    except OSError:
        return None
    tokens = _LEAN_HEADER_TOKEN_RE.findall(_strip_lean_comments(head))
    mods: list[str] = []
    i = 0
    if tokens[i : i + 1] == ["module"]:
        i += 1
    if tokens[i : i + 1] == ["prelude"]:
        i += 1
    while i < len(tokens):
        j = i
        while j < len(tokens) and tokens[j] in ("public", "meta", "private"):
            j += 1
        if j >= len(tokens) or tokens[j] != "import":
            break
        j += 1
        if j < len(tokens) and tokens[j] in ("all", "runtime"):
            j += 1
        if j >= len(tokens):
            break
        mods.append(tokens[j].replace("«", "").replace("»", ""))
        i = j + 1
    return mods


def _local_lean_libs(repo_root: Path) -> tuple[str, ...]:
    try:
        cfg = tomllib.loads((repo_root / "lakefile.toml").read_text(encoding="utf-8"))
        names = tuple(
            str(lib["name"]) for lib in cfg.get("lean_lib", []) if isinstance(lib, dict) and lib.get("name")
        )
        return names or _LOCAL_LEAN_LIB_FALLBACK
    except (OSError, ValueError, TypeError, KeyError):
        return _LOCAL_LEAN_LIB_FALLBACK


def mir_test_prebuild_modules(repo_root: Path) -> list[str]:
    """Workspace modules imported by `MIR_STANDALONE_LEAN_TESTS`, in first-seen order;
    `lake build +<Module>` builds each with its transitive imports."""
    libs = set(_local_lean_libs(repo_root))
    mods: list[str] = []
    for _step, rel in MIR_STANDALONE_LEAN_TESTS:
        imports = _lean_header_imports(repo_root / rel)
        if imports is None:
            imports = list(_MIR_TEST_MODULE_FALLBACK)
        for mod in imports:
            if mod.split(".", 1)[0] in libs and mod not in mods:
                mods.append(mod)
    return mods or list(_MIR_TEST_MODULE_FALLBACK)


def build_suite_steps(repo_root: Path, profile: str) -> list[tuple[str, str, list[str], int]]:
    """Return ordered `(step_name, category, cmd, timeout_sec)` for `profile`.

    `quick` and `nightly` start with `lake_build_core_theory` (`Trusted`, `Anneal`,
    `MiniRust` `.olean`s) before any trusted-boundary or Lean step; `nightly` also
    builds every workspace module imported by the standalone `tests/mir` files
    (`lake_build_mir_test_modules`) right before running them. A step wrapped in
    `anneal-lean-run` receives its step budget as the wrapper's own `--timeout`, so
    the two can never drift apart (`_outer_timeout_sec` adds the wrapper's slot
    queueing and a grace margin on top).
    """
    resolved_lean_run = _resolve_anneal_lean_run(repo_root)
    lean_run = str(resolved_lean_run) if resolved_lean_run is not None else str(repo_root / "scripts/anneal-lean-run")
    has_lean_run = resolved_lean_run is not None
    steps: list[tuple[str, str, list[str], int]] = []

    def add(name: str, category: str, cmd: list[str], timeout_sec: int, wrap: str | None = None) -> None:
        if wrap is not None and has_lean_run:
            cmd = [
                lean_run,
                "--mode",
                wrap,
                "--concurrency",
                "1",
                "--timeout",
                str(timeout_sec),
                "--",
                *cmd,
            ]
        steps.append((name, category, cmd, timeout_sec))

    add(
        "lean_miri_semantic_source_lint",
        "cat2_correspondence_suites",
        [sys.executable, "-B", "lean-miri/vendor/tools/check_semantic_sources.py"],
        60,
    )
    add("ci_check_non_stable_version", "cat7_python_and_ci_tests", ["bash", "./ci/check_non_stable_version.sh"], 30)

    if profile in ("quick", "nightly"):
        # Cold `Trusted Anneal MiniRust` builds measure ~210 s on an 8-core host.
        add(
            "lake_build_core_theory",
            "cat1_trusted_boundary",
            ["lake", "build", *CORE_THEORY_LIBS],
            900,
            wrap="build",
        )
        add(
            "check_trusted_fast",
            "cat1_trusted_boundary",
            [sys.executable, "-B", "trusted/audit/check_trusted.py", "--fast"],
            600,
            wrap="build",
        )
        add(
            "ci_python_unit_tests",
            "cat7_python_and_ci_tests",
            [sys.executable, "-B", "-m", "unittest", "discover", "-s", "ci", "-p", "test_*.py"],
            120,
        )
        add(
            "scripts_python_unit_tests",
            "cat7_python_and_ci_tests",
            [sys.executable, "-B", "-m", "unittest", "discover", "-s", "scripts", "-p", "test_*.py"],
            180,
        )
        add(
            "anneal_lsp_python_unit_tests",
            "cat7_python_and_ci_tests",
            [
                sys.executable,
                "-B",
                "-m",
                "unittest",
                "discover",
                "-s",
                "tools/anneal-lsp/server",
                "-p",
                "test_*.py",
            ],
            120,
        )
        add(
            "minirust_gen_freshness_check",
            "cat2_correspondence_suites",
            ["cargo", "run", "-q", "-p", "anneal-minirust-gen", "--", "generate", "--check"],
            180,
        )
        add(
            "correspondence_bugs_lint",
            "cat2_correspondence_suites",
            [
                "cargo",
                "run",
                "-q",
                "-p",
                "cargo-anneal",
                "--",
                "correspondence-bugs",
                "lint",
                "--gaps-toml",
                "theory/Correspondence/correspondence_gaps.toml",
                "--matrix-toml",
                "theory/Correspondence/correspondence_matrix.toml",
                "--miri-manifest",
                "tests/miri-diff/manifest.toml",
            ],
            180,
        )
        add(
            "minirust_sync_verify_lock",
            "cat2_correspondence_suites",
            [
                "cargo",
                "run",
                "-q",
                "-p",
                "cargo-anneal",
                "--",
                "minirust-sync",
                "verify-lock",
                "--lock-toml",
                "theory/MiniRust/upstream-minirust.lock.toml",
            ],
            180,
        )
        add(
            "rust_workspace_unit_tests",
            "cat3_rust_unit_tests",
            ["cargo", "test", "--workspace", "--lib", "--bins", "--locked"],
            600,
            wrap="build",
        )

    if profile == "nightly":
        add(
            "check_trusted_self_test",
            "cat1_trusted_boundary",
            [sys.executable, "-B", "trusted/audit/check_trusted.py", "--self-test"],
            1500,
            wrap="build",
        )
        # Cold `+Anneal.BitValidity +Anneal.ByteCodec +Anneal.Mir.Cast` after the core
        # build measures ~96 s on an 8-core host; rebuilding `Anneal.Mir.AdtAndControl`
        # (28.8k lines, also imported by `MiniRustSpec` via `DeinitBridge`, so
        # `lake_build_minirust_spec` reuses it) adds ~200 s. The `Correspondence.V2026_06_01`
        # L3/L5 and `MiniRustSpec.Correspondence.Translate` imports of
        # `MirUntestedVariantCorrespondenceTests.lean` add 40 modules outside the core closure
        # (~96k lines: 34 `MiniRustSpec` modules, ~86k lines, mostly generated spec items plus
        # `Interp` and `Translate`; 6 `Correspondence` modules, ~9.8k lines), estimated
        # line-proportionally against the `lake_build_correspondence` / `lake_build_minirust_spec`
        # closures at another ~250-400 s cold (~700 s in total). Those `.olean`s are reused by both
        # later steps, so the budget rises to 1500 s to keep ~2x headroom without adding wall time.
        add(
            "lake_build_mir_test_modules",
            "cat1_trusted_boundary",
            ["lake", "build", *(f"+{mod}" for mod in mir_test_prebuild_modules(repo_root))],
            1500,
            wrap="build",
        )
        for step_name, rel in MIR_STANDALONE_LEAN_TESTS:
            add(step_name, "cat1_trusted_boundary", ["lake", "env", "lean", rel], 300, wrap="file")
        add(
            "lake_build_correspondence",
            "cat2_correspondence_suites",
            ["lake", "build", "Correspondence"],
            900,
            wrap="build",
        )
        add(
            "lake_build_minirust_spec",
            "cat2_correspondence_suites",
            ["lake", "build", "MiniRustSpec"],
            1200,
            wrap="build",
        )
        add(
            "lake_build_lean_miri_spec",
            "cat2_correspondence_suites",
            ["lake", "--dir", "examples", "build", "LeanMiriSpec"],
            1800,
            wrap="build",
        )
        add(
            "domain_integration_tests_anneal_mir",
            "cat4_rust_domain_integration_tests",
            ["cargo", "test", "-p", "anneal-mir", "--tests", "--locked"],
            300,
            wrap="build",
        )
        add(
            "domain_integration_tests_minirust_gen_and_specr",
            "cat4_rust_domain_integration_tests",
            [
                "cargo",
                "test",
                "-p",
                "anneal-minirust-gen",
                "-p",
                "anneal-specr-lean",
                "-p",
                "anneal-spec",
                "--tests",
                "--locked",
            ],
            300,
            wrap="build",
        )
        # Measures ~575 s warm on a 96-core host across `--lib`, `campaign_orchestrator`,
        # `itree_difftest_oracle`, and `miri_difftest_oracle` (after preserving
        # `anneal-trace` staging artifacts, narrowing ITree Lean imports to
        # `TraceCheck`, and serializing Miri sysroot setup). `itree_difftest_oracle`
        # alone is ~350 s and mostly serial (13 min CPU over 6 min wall: one staging
        # slot, one `lake env lean` worker), so extra cores barely help it; 1500 s
        # keeps ~2.5x headroom for slower hosts.
        add(
            "domain_integration_tests_anneal_difftest",
            "cat4_rust_domain_integration_tests",
            [
                "cargo",
                "test",
                "--manifest-path",
                "crates/anneal-difftest/Cargo.toml",
                "--lib",
                "--bins",
                "--tests",
                "--locked",
            ],
            1500,
            wrap="build",
        )
        add(
            "cargo_anneal_e2e_minirust_correspondence",
            "cat5_cargo_anneal_e2e_suites",
            [
                "cargo",
                "test",
                "-p",
                "cargo-anneal",
                "--test",
                "end_to_end_minirust_correspondence",
                "--locked",
            ],
            600,
            wrap="build",
        )
        add(
            "cargo_anneal_e2e_pipeline_and_adoption",
            "cat5_cargo_anneal_e2e_suites",
            [
                "cargo",
                "test",
                "-p",
                "cargo-anneal",
                "--test",
                "end_to_end_pipeline",
                "--test",
                "end_to_end_rust_only_adoption",
                "--test",
                "end_to_end_trace_observer",
                "--locked",
            ],
            900,
            wrap="build",
        )

    return steps


def render_markdown_report(dashboard: dict[str, Any]) -> str:
    """Render the human-readable `LATEST_SUITE_REPORT.md` from `dashboard`."""
    p1 = dashboard["pillar_1_completeness"]
    p2 = dashboard["pillar_2_correctness_and_correspondence"]
    p3 = dashboard["pillar_3_known_issues_and_regressions"]

    mir = p1["syntactic_authorities"]["anneal_mir_ast"]
    mr = p1["syntactic_authorities"]["minirust_authority"]
    lm = p1["syntactic_authorities"]["lean_miri_authority"]
    emp = p1["empirical_corpus_coverage"]
    comb = emp["combined"]

    lines = [
        f"# Anneal 10,000-Foot Completeness, Correspondence & Verification Suite Report (`{dashboard['profile']}` — `{dashboard['date_utc']}`)",
        "",
        f"- **Generated At**: `{dashboard['generated_at_utc']}`",
        f"- **`unstable` Commit**: `{dashboard['unstable_commit_sha']}`",
        f"- **Overall Suite Status**: **`{p2['overall_status']}`** (`{p2['steps_passed']}/{p2['steps_total']}` steps passed in `{p2['total_duration_sec']}s`)",
        f"- **Active Test/Build Regressions**: **`{len(p3['active_build_or_test_regressions'])}`**",
        f"- **Actionable Correspondence Divergences (Tier 1 Targets)**: **`{p3['correspondence_divergences']['actionable_anneal_bugs_count']}`**",
        "",
        "---",
        "",
        "## Pillar 1: 10,000-Foot Project Completeness",
        "",
        "### 1A. Syntactic & Semantic-Authority Completeness (`Anneal MIR`, `MiniRust`, `lean-miri`)",
        "",
        "| Authority / Surface | Total Denominator | Proved Corresponding | Supported & Tested | Supported (Untested Gap) | Unsupported (Fail-Closed) | Headline Coverage |",
        "| :--- | ---: | ---: | ---: | ---: | ---: | ---: |",
        (
            f"| **Anneal MIR (`Trusted.MirAst`)** | `{mir['total_variants']}` variants "
            f"(+`{mir['stage1_lowered_lintrinsic_op_variants']}` `LIntrinsicOp`) | "
            f"`{mir['proved_corresponding']}` (`{mir['proved_corresponding_pct']}%`) | "
            f"`{mir['supported_and_tested']}` | "
            f"`{mir['supported_untested']}` | "
            f"`{mir['unsupported_fail_closed']}` | "
            f"**`{mir['supported_pct']}%`** operational |"
        ),
        (
            f"| **MiniRust (`MiniRustSpec`)** | `{mr['spec_items_total']}` items / `{mr['spec_fns_total']}` fns "
            f"(`{mr['ast_nodes_structural']}` AST nodes) | "
            f"`{mr['audited_declarations']}` audited decls (`{mr['lintrinsic_ops_classified']['covered']}/{mr['lintrinsic_ops_classified']['total']}` `LIntrinsicOp`) | "
            f"`{mr['interp_anchored_items']}` anchored items (`{mr['interp_anchored_pct_of_items']}%`) | "
            f"`0` | `{mr['interp_unsupported_branches']}` `Stop.unsupported` branches | "
            f"**`{mr['ast_nodes_structural_pct']}%`** AST / **`{mr['shallow_types_pct']}%`** types |"
        ),
        (
            f"| **`lean-miri` (`LeanMiriSpec`)** | `{lm['vendored_miri_files']}` vendored `Miri.*` files | "
            f"`{lm['audited_declarations']}` audited decls / `{lm['statement_pin_examples']}` pins "
            f"(`{', '.join(lm['milestones_merged'])}`) | "
            f"`{lm['subsystems']['ABI_and_MIR_Syntax']['files'] + lm['subsystems']['Memory_and_TreeBorrows']['files'] + lm['subsystems']['Interpreter_Core']['files']}` core files | "
            f"`{lm['subsystems']['Input_and_Startup_World']['files']}` startup/world files | "
            f"`{lm['subsystems']['Concurrency_and_WeakMemory']['files'] + lm['subsystems']['OS_Foreign_and_Float_Shims']['files']}` (concurrency/OS/float) | "
            f"**`{len(lm['milestones_merged'])}`** milestones merged |"
        ),
        "",
        f"- **Untested Supported MIR Variants (`{len(mir['untested_variants'])}`)**: {', '.join(f'`{v}`' for v in mir['untested_variants']) or 'None'}",
        f"- **Unsupported `Trusted.MirSemantics` Variants (`{len(mir['unsupported_variants'])}`)**: {', '.join(f'`{v}`' for v in mir['unsupported_variants'])}",
        "",
        "### 1B. Empirical Real-World Rust Corpus Completeness & Blended Sub-Program Coverage",
        "",
        "| Corpus | Functions (`\\|F\\|`) | Stmt Units (`W`) | Layer | Fully Verifiable Fns (`V_fn`) | Partially Covered Fns (`P_fn`) | Within-Blocked Stmt Coverage (`C_blocked`) | Within-Blocked Entry-Prefix (`C_cfg`) | Total Stmt Coverage (`C_total`) | **Blended Score (`S_blend`)** |",
        "| :--- | ---: | ---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]

    for c_key, c_data in [("combined_all_corpora", comb), *emp["corpora"].items()]:
        for layer_name in (
            "trusted_mir",
            "anneal_proof_lifters",
            "minirust_correspondence",
            "lean_miri_correspondence",
        ):
            ldata = c_data["layers"][layer_name]
            lines.append(
                f"| `{c_key}` | `{c_data['total_fns']}` | `{c_data['total_stmt_units']}` | "
                f"`{layer_name}` | **`{ldata['fully_verifiable_fn_pct']}%`** (`{ldata['fully_verifiable_fns']}`) | "
                f"`{ldata['partially_covered_fn_pct']}%` (`{ldata['partially_covered_fns']}`) | "
                f"`{ldata['within_blocked_fns_stmt_coverage_pct']}%` | "
                f"`{ldata['within_blocked_fns_cfg_prefix_pct']}%` | "
                f"`{ldata['total_stmt_coverage_pct']}%` | "
                f"**`{ldata['blended_completeness_score_pct']}%`** |"
            )

    lines.extend(
        [
            "",
            "#### Top Marginal-Unlock Blockers Across All Scanned Corpora (`anneal_proof_lifters` Frontier)",
            "",
            "| Construct Blocker | Sole-Blocker Functions (`Delta V_fn`) | Marginal `+V_fn %` Unlock | Total Blocked Functions | Uncovered Stmt Units |",
            "| :--- | ---: | ---: | ---: | ---: |",
        ]
    )
    for b in comb["top_marginal_unlock_blockers"][:10]:
        lines.append(
            f"| `{b['construct']}` | **`{b['sole_blocker_fn_count']}`** | "
            f"**`+{b['marginal_delta_v_fn_pct']}%`** | `{b['blocked_fn_count']}` | `{b['uncovered_stmt_count']}` |"
        )

    lines.extend(
        [
            "",
            "---",
            "",
            "## Pillar 2: Correctness, Correspondence & Repository Test Suite Results",
            "",
            "| Step Name | Category | Status | Duration (`s`) | Notes / Audit Tags |",
            "| :--- | :--- | :--- | ---: | :--- |",
        ]
    )
    for step in p2["steps"]:
        tags_str = "; ".join(step.get("audit_tags", [])[:3])
        lines.append(
            f"| `{step['name']}` | `{step['category']}` | **`{step['status']}`** | `{step['duration_sec']}` | {tags_str} |"
        )

    lines.extend(
        [
            "",
            "---",
            "",
            "## Pillar 3: Known Issues, Active Regressions & Actionable Correspondence Divergences",
            "",
            "### 3A. Active Build or Test Suite Regressions",
            "",
        ]
    )
    if not p3["active_build_or_test_regressions"]:
        lines.append("None (`0` regressions).")
    else:
        for reg in p3["active_build_or_test_regressions"]:
            lines.extend(
                [
                    f"- **`{reg['name']}` (`{reg['category']}`, exit `{reg['exit_code']}`)**:",
                    "  ```text",
                    "  " + reg.get("failure_excerpt", "").replace("\n", "\n  "),
                    "  ```",
                ]
            )

    lines.extend(
        [
            "",
            "### 3B. Actionable Correspondence Divergences (Tier 1 `P0` Workstream Targets)",
            "",
            "| ID | Authority | Severity | Witness Theorem | Anneal Component | Switch-to-Pass Criterion |",
            "| :--- | :--- | :--- | :--- | :--- | :--- |",
        ]
    )
    for div in p3["correspondence_divergences"]["actionable_anneal_bugs"]:
        if div.get("status") == "resolution_missing":
            res_sym = div.get("resolution_symbol", "<missing>")
            res_file = div.get("resolution_file", div["file"])
            witness_cell = (
                f"`{div['witness_symbol']}` (`{div['file']}`) — "
                f"**missing resolution** `{res_sym}` (`{res_file}`)"
            )
        elif div.get("status") == "resolution_unpinned":
            res_sym = div.get("resolution_symbol", "<missing>")
            pin_file = div.get(
                "resolution_pin_file", AUTHORITY_AUDIT_FILES.get(div["authority"], "<audit>")
            )
            pin_problems = div.get("resolution_pin_problems") or []
            rejected = f"; rejected pins: {', '.join(pin_problems)}" if pin_problems else ""
            witness_cell = (
                f"`{div['witness_symbol']}` (`{div['file']}`) — "
                f"**unpinned resolution** `{res_sym}` (no `example ... := {res_sym}` in `{pin_file}`"
                f"{rejected})"
            )
        elif div.get("status") == "resolution_invalid":
            res_sym = div.get("resolution_symbol", "<missing>")
            res_file = div.get("resolution_file", div["file"])
            witness_cell = (
                f"`{div['witness_symbol']}` (`{div['file']}`) — "
                f"**invalid resolution** `{res_sym}` (`{res_file}`: "
                f"{', '.join(div.get('resolution_problems') or [])})"
            )
        else:
            witness_cell = f"`{div['witness_symbol']}` (`{div['file']}`)"
        lines.append(
            f"| `{div['id']}` | `{div['authority']}` | `{div['severity']}` | "
            f"{witness_cell} | `{div['anneal_component']}` | "
            f"{div['switch_to_pass_criterion']} |"
        )

    flip = p3.get("flip_direction_audit")
    if flip is not None:
        lines.extend(
            [
                "",
                "### 3C. Flip-Direction Witness Polarity Audit",
                "",
                f"- **Baseline**: `{flip['baseline_root']}` "
                f"(`{flip['baseline_actionable_count']}` actionable → "
                f"`{flip['current_actionable_count']}` now)",
                f"- **Status**: **`{'PASS' if flip['passed'] else 'FAIL'}`** "
                f"(`{len(flip['transitions'])}` transitions, `{len(flip['violations'])}` violations)",
                "",
            ]
        )
        for tr in flip["transitions"]:
            lines.append(f"- `{tr['id']}`: `{tr['from']}` → `{tr['to']}`")
        for v in flip["violations"]:
            lines.append(f"- **VIOLATION** `{v['id']}` (`{v['reason']}`): {v['detail']}")

    return "\n".join(lines) + "\n"


def run_suite_and_generate_dashboard(
    repo_root: Path,
    profile: str,
    state_dir: Path,
    difftest_dir: Path | None = None,
    zerocopy_dir: Path | None = None,
    flip_baseline_root: Path | None = None,
) -> tuple[int, dict[str, Any], str]:
    """Run the requested verification profile, compute all 3 pillars, and persist reports.

    With `flip_baseline_root` (a checkout of the baseline revision, or a tree written
    by `materialize_flip_baseline_tree`), the flip-direction witness polarity audit
    (`audit_flip_direction_transitions`) runs against it, and any violation fails the
    run with `EXIT_SUITE_REGRESSION`."""
    now = datetime.datetime.now(datetime.timezone.utc)
    now_iso = now.strftime("%Y-%m-%dT%H:%M:%SZ")
    date_str = now.strftime("%Y-%m-%d")

    stage_a = compute_stage_a_syntactic_completeness(repo_root)
    stage_b = compute_stage_b_empirical_corpora(repo_root, zerocopy_dir=zerocopy_dir)
    divergences = discover_correspondence_divergences(repo_root)
    flip_audit = (
        audit_flip_direction_transitions(flip_baseline_root, repo_root)
        if flip_baseline_root is not None
        else None
    )

    steps_spec = build_suite_steps(repo_root, profile)
    if any(s_name.startswith("lake_build_") for s_name, _, _, _ in steps_spec):
        _preflight_clean_stale_oleans(repo_root)
    step_results: list[dict[str, Any]] = []
    t0 = time.monotonic()
    for s_name, s_cat, s_cmd, s_timeout in steps_spec:
        res = _run_step(s_name, s_cat, s_cmd, cwd=repo_root, timeout_sec=s_timeout)
        step_results.append(res)
    total_dur = round(time.monotonic() - t0, 2)

    regressions = [s for s in step_results if s["status"] != "PASS"]
    overall_status = "PASS" if not regressions else "FAIL"

    # Optional ingestion of latest differential testing summary
    difftest_summary: dict[str, Any] = {}
    if difftest_dir is not None:
        latest_dt = difftest_dir / "reports/LATEST_CAMPAIGN_SUMMARY.json"
        if latest_dt.is_file():
            try:
                difftest_summary = json.loads(latest_dt.read_text(encoding="utf-8"))
            except ValueError:
                difftest_summary = {}

    dashboard: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "profile": profile,
        "generated_at_utc": now_iso,
        "date_utc": date_str,
        "unstable_commit_sha": _git_head_sha(repo_root, "HEAD"),
        "pillar_1_completeness": {
            "syntactic_authorities": stage_a,
            "empirical_corpus_coverage": stage_b,
        },
        "pillar_2_correctness_and_correspondence": {
            "overall_status": overall_status,
            "steps_total": len(step_results),
            "steps_passed": sum(1 for s in step_results if s["status"] == "PASS"),
            "steps_failed": len(regressions),
            "total_duration_sec": total_dur,
            "steps": step_results,
            "latest_differential_testing": {
                "overall_status": difftest_summary.get("overall_status", "unknown"),
                "unquarantined_count": len(difftest_summary.get("unquarantined_findings", [])),
                "quarantined_count": len(difftest_summary.get("quarantined_findings", [])),
            },
        },
        "pillar_3_known_issues_and_regressions": {
            "active_build_or_test_regressions": regressions,
            "correspondence_divergences": divergences,
            "unquarantined_difftest_findings": difftest_summary.get("unquarantined_findings", []),
            "flip_direction_audit": flip_audit,
        },
    }

    report_md = render_markdown_report(dashboard)

    # Write state and reports
    reports_dir = state_dir / "reports"
    st_sub = state_dir / "state"
    reports_dir.mkdir(parents=True, exist_ok=True)
    st_sub.mkdir(parents=True, exist_ok=True)

    _atomic_write_text(
        reports_dir / "LATEST_DASHBOARD_STATE.json",
        json.dumps(dashboard, indent=2, sort_keys=True) + "\n",
    )
    _atomic_write_text(
        reports_dir / f"{date_str}_{profile}_dashboard_state.json",
        json.dumps(dashboard, indent=2, sort_keys=True) + "\n",
    )
    _atomic_write_text(reports_dir / "LATEST_SUITE_REPORT.md", report_md)
    _atomic_write_text(reports_dir / f"{date_str}_{profile}_suite_report.md", report_md)

    # Update ratchet file
    ratchet_path = st_sub / "correspondence_ratchet.json"
    prev_ratchet: dict[str, Any] = {}
    if ratchet_path.is_file():
        try:
            prev_ratchet = json.loads(ratchet_path.read_text(encoding="utf-8"))
        except ValueError:
            prev_ratchet = {}

    comb_lifters = stage_b["combined"]["layers"]["anneal_proof_lifters"]
    new_ratchet = {
        "updated_at_utc": now_iso,
        "unstable_commit_sha": dashboard["unstable_commit_sha"],
        "high_water_minirust_audited_decls": max(
            prev_ratchet.get("high_water_minirust_audited_decls", 0),
            stage_a["minirust_authority"]["audited_declarations"],
        ),
        "high_water_lean_miri_audited_decls": max(
            prev_ratchet.get("high_water_lean_miri_audited_decls", 0),
            stage_a["lean_miri_authority"]["audited_declarations"],
        ),
        "high_water_blended_completeness_pct": max(
            prev_ratchet.get("high_water_blended_completeness_pct", 0.0),
            comb_lifters["blended_completeness_score_pct"],
        ),
        "low_water_actionable_divergences": min(
            prev_ratchet.get(
                "low_water_actionable_divergences",
                divergences["actionable_anneal_bugs_count"],
            ),
            divergences["actionable_anneal_bugs_count"],
        ),
        "latest_actionable_divergences": divergences["actionable_anneal_bugs_count"],
    }
    _atomic_write_text(ratchet_path, json.dumps(new_ratchet, indent=2, sort_keys=True) + "\n")

    # Append compact time-series entry to `completeness_history.jsonl`
    history_entry = {
        "timestamp_utc": now_iso,
        "profile": profile,
        "commit": dashboard["unstable_commit_sha"],
        "overall_status": overall_status,
        "mir_supported_pct": stage_a["anneal_mir_ast"]["supported_pct"],
        "minirust_audited_decls": stage_a["minirust_authority"]["audited_declarations"],
        "lean_miri_audited_decls": stage_a["lean_miri_authority"]["audited_declarations"],
        "combined_v_fn_pct": comb_lifters["fully_verifiable_fn_pct"],
        "combined_total_stmt_pct": comb_lifters["total_stmt_coverage_pct"],
        "combined_blended_pct": comb_lifters["blended_completeness_score_pct"],
        "actionable_divergences": divergences["actionable_anneal_bugs_count"],
        "regressions": len(regressions),
    }
    history_path = st_sub / "completeness_history.jsonl"
    with history_path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(history_entry, sort_keys=True) + "\n")

    exit_code = EXIT_SUCCESS if overall_status == "PASS" else EXIT_SUITE_REGRESSION
    if flip_audit is not None and not flip_audit["passed"]:
        exit_code = EXIT_SUITE_REGRESSION
    return exit_code, dashboard, report_md


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--profile",
        choices=("census-only", "quick", "nightly"),
        default="nightly",
        help="Verification and completeness execution profile.",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Path to the Anneal repository root.",
    )
    parser.add_argument(
        "--state-dir",
        type=Path,
        default=Path("/tmp/anneal-verification-suite"),
        help="Directory for writing state/ and reports/ outputs.",
    )
    parser.add_argument(
        "--difftest-dir",
        type=Path,
        default=None,
        help="Optional differential-testing state/reports directory to cross-link.",
    )
    parser.add_argument(
        "--zerocopy-dir",
        type=Path,
        default=None,
        help="Optional zerocopy checkout directory for Stage B empirical corpus scan.",
    )
    baseline = parser.add_mutually_exclusive_group()
    baseline.add_argument(
        "--flip-baseline-root",
        type=Path,
        default=None,
        help=(
            "Optional checkout of a baseline revision: audit every tracked divergence's "
            "transition from it (flip-direction witness polarity guard) and fail on violations."
        ),
    )
    baseline.add_argument(
        "--flip-baseline-ref",
        default=None,
        help=(
            "Like --flip-baseline-root, with the baseline's tracked divergence files read "
            "from this git revision of --repo-root."
        ),
    )
    args = parser.parse_args(argv)

    repo_root = args.repo_root.resolve()
    with tempfile.TemporaryDirectory(prefix="anneal-flip-baseline-") as tmp:
        flip_baseline_root: Path | None = None
        if args.flip_baseline_root is not None:
            flip_baseline_root = args.flip_baseline_root.resolve()
            if not flip_baseline_root.is_dir():
                sys.stderr.write(f"--flip-baseline-root {flip_baseline_root} is not a directory\n")
                return EXIT_INTERNAL_ERROR
        elif args.flip_baseline_ref is not None:
            try:
                flip_baseline_root = materialize_flip_baseline_tree(
                    repo_root, args.flip_baseline_ref, Path(tmp)
                )
            except ValueError as exc:
                sys.stderr.write(f"{exc}\n")
                return EXIT_INTERNAL_ERROR
        code, _dashboard, report_md = run_suite_and_generate_dashboard(
            repo_root=repo_root,
            profile=args.profile,
            state_dir=args.state_dir.resolve(),
            difftest_dir=args.difftest_dir.resolve() if args.difftest_dir else None,
            zerocopy_dir=args.zerocopy_dir.resolve() if args.zerocopy_dir else None,
            flip_baseline_root=flip_baseline_root,
        )
    sys.stdout.write(report_md)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
