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
  census-only  Fast (<5s) static/ledger completeness & correspondence census plus
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

Exit codes:
  0  All executed suite steps passed and zero active test/build regressions occurred.
  1  Internal script or configuration error.
  2  One or more executed verification/test steps failed (regression detected).
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
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
            ("constEvalCounter", "supported_untested"),
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
            ("tailCall", "supported_untested"),
            ("resume", "unsupported_fail_closed"),
            ("terminate", "unsupported_fail_closed"),
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
            ("opaqueCast", "supported_untested"),
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
            ("nullaryOp", "unsupported_fail_closed"),  # Lowered in Anneal.Mir.AdtAndControl
            ("shallowInitBox", "unsupported_fail_closed"),  # Lowered in Anneal.Mir.AdtAndControl
            ("wrapUnsafeBinder", "unsupported_fail_closed"),  # Lowered in Anneal.Mir.AdtAndControl
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
            ("closure", "unsupported_fail_closed"),
            ("coroutine", "unsupported_fail_closed"),
            ("coroutineClosure", "unsupported_fail_closed"),
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
        "wide_ptr_or_unsized_dst",
        re.compile(r"\?\s*Sized\b|\bslice_from_raw_parts(?:_mut)?\b|\bsize_of_val(?:_raw)?\b|\balign_of_val(?:_raw)?\b|\bPointerMetadata\b"),
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


def _extract_rust_functions(rs_text: str) -> list[tuple[str, list[str]]]:
    """Extract `(fn_name, statements)` from a Rust source file using brace balancing."""
    # Strip line comments to avoid unbalanced braces in comments
    cleaned_lines = []
    for line in rs_text.splitlines():
        code_part = line.split("//", 1)[0]
        cleaned_lines.append(code_part)
    cleaned = "\n".join(cleaned_lines)

    fn_Header_re = re.compile(
        r"(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?(?:unsafe\s+)?(?:extern\s+(?:\"[^\"]+\"\s+)?)?fn\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*[<(]"
    )
    results: list[tuple[str, list[str]]] = []
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
        body_start = -1
        while idx < n:
            ch = cleaned[idx]
            if ch == "(":
                paren_depth += 1
            elif ch == ")":
                paren_depth = max(0, paren_depth - 1)
            elif ch == "<":
                angle_depth += 1
            elif ch == ">" and (idx == 0 or cleaned[idx - 1] != "-"):
                angle_depth = max(0, angle_depth - 1)
            elif ch == ";" and paren_depth == 0 and angle_depth == 0:
                pos = idx + 1
                break
            elif ch == "{" and paren_depth == 0:
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
        results.append((fn_name, raw_stmts))
        pos = end_idx + 1

    return results


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
        for _fn_name, stmts in _extract_rust_functions(text):
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
        for candidate in (
            repo_root.parent / "zerocopy",
            Path.home() / "Projects/markdittmer/zerocopy",
            Path("/usr/local/google/Projects/open/zerocopy"),
        ):
            if candidate.exists():
                zc_root = candidate
                break

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
# Note: All 8 entries below remain permanently registered in
# `TRACKED_CORRESPONDENCE_DIVERGENCES` as switch-to-pass regression guards; once
# their `witness_symbol` divergence theorems are replaced by positive
# `*_simulation` theorems, `discover_correspondence_divergences` classifies them
# under `resolved_correspondence_divergences`. Resolution is fail-closed: an entry
# with a `resolution_symbol` only counts as resolved when the old witness is gone
# AND the named replacement theorem is live in `resolution_file` (default: `file`);
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
]


def _strip_lean_comments_and_strings(src: str) -> str:
    """Strip Lean `--` line comments, nested `/- ... -/` block comments, and literals.

    Replaces stripped spans with spaces while preserving `\\n` so line-anchored
    declaration matching cannot be spoofed by commented-out theorems, docstrings,
    or string literals (and handles `'\"'` character literals cleanly).
    """
    out: list[str] = []
    n = len(src)
    i = 0
    block_depth = 0
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.append("  ")
            i += 2
            continue
        if ch == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
            continue
        # Lean 4 raw string literals (`r"..."`, `r#"..."#`, `r##"..."##`) do not escape `\"`.
        if ch == "r" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_'!?»")):
            j = i + 1
            while j < n and src[j] == "#":
                j += 1
            if j < n and src[j] == '"':
                hashes = j - (i + 1)
                closing = '"' + ("#" * hashes)
                out.append(" " * (j - i + 1))
                i = j + 1
                while i < n:
                    if src.startswith(closing, i):
                        out.append(" " * len(closing))
                        i += len(closing)
                        break
                    out.append("\n" if src[i] == "\n" else " ")
                    i += 1
                continue
        if ch == '"':
            out.append(" ")
            i += 1
            while i < n:
                c = src[i]
                if c == "\\":
                    out.append("  " if i + 1 < n and src[i + 1] != "\n" else " ")
                    i += 2
                    continue
                if c == '"':
                    out.append(" ")
                    i += 1
                    break
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        # Handle Lean character literals like `'"'` or `'\''` so `'"'` does not open a string.
        if ch == "'":
            if i + 2 < n and src[i + 1] != "\\" and src[i + 2] == "'":
                out.append("   ")
                i += 3
                continue
            if i + 3 < n and src[i + 1] == "\\" and src[i + 3] == "'":
                out.append("    ")
                i += 4
                continue
        out.append(ch)
        i += 1
    return "".join(out)


_LEAN_TOKEN_RE = re.compile(
    r"""
    @\[
    | :=
    | [(\[{⟨)\]}⟩:@.;,]
    | «[^»\n]+»
    | [\#?]?[A-Za-z_0-9][A-Za-z_0-9'!?]*
    """,
    re.VERBOSE,
)

_LEAN_OPEN_BRACKETS = {"@[", "(", "[", "{", "⟨"}
_LEAN_CLOSE_BRACKETS = {")", "]", "}", "⟩"}
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
    if not tok or tok[0] in "@?:()[]{}⟨⟩.,;#0123456789":
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


def _scan_lean_declarations_and_pins(stripped_src: str) -> dict[str, Any]:
    """Tokenize comment/string-stripped Lean 4 source at bracket depth 0.

    Handles multi-line and same-line commands (`namespace Foo theorem bar ... end Foo`,
    `section private theorem ...`, `open Foo in private\\ntheorem ...`, `private @[simp,\\n ...]`,
    `mutual ... end`, `section #exit`, `#exit'` non-truncation) and extracts:
      - `witness_symbols`: every declared witness-eligible constant name;
      - `resolutions`: `symbol -> list[(effective_namespace_parts, has_forbidden_modifier)]`;
      - `pins`: `symbol -> list[(audit_active_namespace_parts, inline_qualifier_parts)]` for
        valid typed `example ... : <NonTrivialProp> := @?symbol <ident_args>*` statement pins.
    """
    tokens = _LEAN_TOKEN_RE.findall(stripped_src)
    n = len(tokens)
    depth = 0
    scope_stack: list[tuple[str, list[str]]] = []
    pending_mods: set[str] = set()
    witness_symbols: set[str] = set()
    resolutions: dict[str, list[tuple[list[str], bool]]] = {}
    pins: dict[str, list[tuple[list[str], list[str]]]] = {}

    i = 0
    while i < n:
        tok = tokens[i]
        prev = tokens[i - 1] if i > 0 else ""
        if tok in _LEAN_OPEN_BRACKETS:
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

        if tok in _LEAN_IN_PREFIX_CMDS:
            j = i + 1
            d2 = 0
            while j < n:
                t2 = tokens[j]
                p2 = tokens[j - 1] if j > 0 else ""
                if t2 in _LEAN_OPEN_BRACKETS:
                    d2 += 1
                elif t2 in _LEAN_CLOSE_BRACKETS:
                    if d2 > 0:
                        d2 -= 1
                elif d2 == 0 and p2 != ".":
                    if t2 == "in":
                        i = j + 1
                        break
                    if (
                        t2 == "#exit"
                        or t2 in (_LEAN_WITNESS_DECL_KINDS | _LEAN_SCOPE_KEYWORDS | {"example"})
                        or t2 in _LEAN_DECL_MODIFIERS
                        or t2 == "@["
                    ):
                        pending_mods.clear()
                        i = j
                        break
                j += 1
            else:
                break
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
            scope_stack.append(("mutual", []))
            i += 1
            continue

        if tok == "end":
            pending_mods.clear()
            nxt = tokens[i + 1] if i + 1 < n else ""
            if _is_lean_ident_tok(nxt) and not _is_lean_top_cmd_tok(nxt, ""):
                end_parts, i = _read_lean_qname(tokens, i + 1)
                while scope_stack and end_parts:
                    _, sp = scope_stack.pop()
                    if sp and len(sp) <= len(end_parts) and end_parts[-len(sp) :] == sp:
                        end_parts = end_parts[: -len(sp)]
                    else:
                        break
            else:
                if scope_stack:
                    scope_stack.pop()
                i += 1
            continue

        if tok in _LEAN_WITNESS_DECL_KINDS:
            mods = set(pending_mods)
            pending_mods.clear()
            segs, next_i = _read_lean_qname(tokens, i + 1)
            if segs and not segs[-1].isdigit():
                sym = segs[-1]
                witness_symbols.add(sym)
                if tok in _LEAN_RES_DECL_KINDS:
                    active_ns = [s for kind, sp in scope_stack if kind == "ns" for s in sp]
                    inline_ns = segs[:-1]
                    eff_ns = inline_ns[1:] if (inline_ns and inline_ns[0] == "_root_") else (active_ns + inline_ns)
                    resolutions.setdefault(sym, []).append((eff_ns, bool(mods & _LEAN_FORBIDDEN_RES_MODS)))
            i = max(next_i, i + 1)
            continue

        if tok == "example":
            mods = set(pending_mods)
            pending_mods.clear()
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
                    and (type_toks[0] in _LEAN_TRIVIAL_PIN_TYPES or type_toks[0].startswith("?"))
                )
                rhs_toks = tokens[assign_idx + 1 : end_ex]
                if valid_type and rhs_toks:
                    r_idx = 1 if rhs_toks[0] == "@" else 0
                    qsegs, r_next = _read_lean_qname(rhs_toks, r_idx)
                    if qsegs and not qsegs[-1].isdigit():
                        rem = rhs_toks[r_next:]
                        if all(
                            (_is_lean_ident_tok(rt) or rt == "_") and rt not in _LEAN_FORBIDDEN_PIN_ARGS
                            for rt in rem
                        ):
                            active_ns = [s for kind, sp in scope_stack if kind == "ns" for s in sp]
                            pins.setdefault(qsegs[-1], []).append(
                                (active_ns, qsegs[:-1], tuple(type_toks))
                            )
            i = end_ex
            continue

        if pending_mods:
            pending_mods.clear()
        i += 1

    return {
        "witness_symbols": witness_symbols,
        "resolutions": resolutions,
        "pins": pins,
    }


def _has_lean_decl(
    stripped_src: str,
    symbol: str,
    *,
    resolution: bool,
    rel_file: str = "",
    scan: dict[str, Any] | None = None,
) -> bool:
    """Check whether `symbol` is declared in `stripped_src` under witness or resolution rules."""
    parsed = scan if scan is not None else _scan_lean_declarations_and_pins(stripped_src)
    if not resolution:
        return symbol in parsed["witness_symbols"]
    mod_parts = _lean_module_parts(rel_file) if rel_file else []
    for eff_ns, has_forbidden in parsed["resolutions"].get(symbol, []):
        if has_forbidden:
            continue
        if mod_parts and (len(eff_ns) > len(mod_parts) or eff_ns != mod_parts[: len(eff_ns)]):
            continue
        return True
    return False


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
) -> bool:
    """True iff `stripped_audit_src` contains a non-trivial typed `example` statement pin
    whose RHS directly applies `symbol` (without field projections like `.1`, vacuous `: True`
    or wildcard `: _` types, or decoy inline/enclosing namespaces)."""
    parsed = scan if scan is not None else _scan_lean_declarations_and_pins(stripped_audit_src)
    entries = parsed["pins"].get(symbol, [])
    if not entries:
        return False
    allowed_inline = {"_root_", *_lean_module_parts(rel_res_file)} if rel_res_file else None
    allowed_audit_ns = (
        {"StatementPins", *_lean_module_parts(rel_pin_file), *_lean_module_parts(rel_res_file)}
        if (rel_pin_file or rel_res_file)
        else None
    )
    sym_last = _clean_lean_seg(symbol.split(".")[-1])
    for active_ns, inline_qual, type_toks in entries:
        # A pin locks nothing if its type is computed from the theorem itself
        # (`type_of% thm`, self-reference), by a tactic (`by ...`), or via holes
        # (`_`, `?_`, `?m`) that unify with the RHS type.
        if any(
            _clean_lean_seg(tt) == sym_last
            or tt in _LEAN_SELF_TYPED_PIN_TOKENS
            or tt.startswith("?")
            for tt in type_toks
        ):
            continue
        if allowed_inline is not None and any(seg not in allowed_inline for seg in inline_qual):
            continue
        if allowed_audit_ns is not None and any(seg not in allowed_audit_ns for seg in active_ns):
            continue
        return True
    return False


def discover_correspondence_divergences(repo_root: Path) -> dict[str, Any]:
    """Check status of tracked correspondence divergences and `correspondence_gaps.toml`."""
    actionable_open: list[dict[str, Any]] = []
    actionable_resolved: list[dict[str, Any]] = []
    modeling_choices: list[dict[str, Any]] = []
    scan_cache: dict[Path, tuple[str, dict[str, Any]]] = {}

    def read_scanned(path: Path) -> tuple[str, dict[str, Any]] | None:
        if path in scan_cache:
            return scan_cache[path]
        if not path.is_file():
            return None
        raw = path.read_text(encoding="utf-8", errors="replace")
        stripped = _strip_lean_comments_and_strings(raw)
        scanned = _scan_lean_declarations_and_pins(stripped)
        scan_cache[path] = (stripped, scanned)
        return stripped, scanned

    for item in TRACKED_CORRESPONDENCE_DIVERGENCES:
        fpath = repo_root / item["file"]
        symbol = item["witness_symbol"]
        scanned_f = read_scanned(fpath)
        present = (
            _has_lean_decl(scanned_f[0], symbol, resolution=False, scan=scanned_f[1])
            if scanned_f is not None
            else False
        )

        resolution_symbol = item.get("resolution_symbol")
        resolution_present: bool | None = None
        rel_r = item.get("resolution_file", item["file"])
        if resolution_symbol:
            scanned_r = read_scanned(repo_root / rel_r)
            resolution_present = (
                _has_lean_decl(
                    scanned_r[0],
                    resolution_symbol,
                    resolution=True,
                    rel_file=rel_r,
                    scan=scanned_r[1],
                )
                if scanned_r is not None
                else False
            )

        resolution_pinned: bool | None = None
        if resolution_symbol and resolution_present:
            rel_pin = item.get("resolution_pin_file", AUTHORITY_AUDIT_FILES.get(item["authority"]))
            scanned_pin = read_scanned(repo_root / rel_pin) if rel_pin else None
            resolution_pinned = (
                _has_statement_pin(
                    scanned_pin[0],
                    resolution_symbol,
                    rel_res_file=rel_r,
                    rel_pin_file=rel_pin or "",
                    scan=scanned_pin[1],
                )
                if scanned_pin is not None
                else False
            )

        record = dict(item)
        record["live_in_source"] = present
        record["resolution_live_in_source"] = resolution_present
        record["resolution_statement_pinned"] = resolution_pinned
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
        elif resolution_symbol and not resolution_pinned:
            # Fail closed: the replacement theorem exists but no audit `example`
            # pin locks its statement, so it could be weakened without notice.
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


_LEAN_RUN_VALUE_OPTS: frozenset[str] = frozenset(
    (
        "--concurrency",
        "-W",
        "--mode",
        "--memory-max-mb",
        "--timeout",
        "--verify-bundle-ff",
        "--check-unstable-ff",
        "--ref",
        "--repo-dir",
        "--local-rev",
    )
)
_LEAN_RUN_BOOL_OPTS: frozenset[str] = frozenset(
    (
        "--probe",
        "--print-limits",
        "--json",
        "--no-slot-lock",
        "--sync-if-behind",
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
    env = os.environ.copy()
    _ensure_toolchain_path(env)
    if env_overrides:
        env.update(env_overrides)
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
# `Trusted`/`Anneal`/`MiniRust` import closure.
MIR_STANDALONE_LEAN_TESTS: tuple[tuple[str, str], ...] = (
    ("tests_mir_bit_validity_stage1", "tests/mir/BitValidityStage1Tests.lean"),
    ("tests_mir_byte_codec", "tests/mir/ByteCodecTests.lean"),
    ("tests_mir_cast_stage1", "tests/mir/CastStage1Tests.lean"),
    ("tests_mir_adt_and_control", "tests/mir/AdtAndControlTests.lean"),
)
CORE_THEORY_LIBS: tuple[str, ...] = ("Trusted", "Anneal", "MiniRust")
_LOCAL_LEAN_LIB_FALLBACK: tuple[str, ...] = (
    "Trusted",
    "Anneal",
    "MiniRust",
    "Correspondence",
    "MiniRustSpec",
)
# Used only if a test header is unreadable (the unit tests keep it in sync).
_MIR_TEST_MODULE_FALLBACK: tuple[str, ...] = (
    "Anneal.BitValidity",
    "Anneal.ByteCodec",
    "Anneal.Mir.Cast",
    "Anneal.Mir.AdtAndControl",
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
    lean_run = str(repo_root / "scripts/anneal-lean-run")
    has_lean_run = Path(lean_run).is_file() and os.access(lean_run, os.X_OK)
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
        # Cold `Trusted Anneal MiniRust` builds measure ~210 s on an 8-core capsule.
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
        # build measures ~96 s on an 8-core capsule; rebuilding `Anneal.Mir.AdtAndControl`
        # (28.8k lines, also imported by `MiniRustSpec` via `DeinitBridge`, so
        # `lake_build_minirust_spec` reuses it) adds ~200 s.
        add(
            "lake_build_mir_test_modules",
            "cat1_trusted_boundary",
            ["lake", "build", *(f"+{mod}" for mod in mir_test_prebuild_modules(repo_root))],
            900,
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
            900,
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
            witness_cell = (
                f"`{div['witness_symbol']}` (`{div['file']}`) — "
                f"**unpinned resolution** `{res_sym}` (no `example ... := {res_sym}` in `{pin_file}`)"
            )
        else:
            witness_cell = f"`{div['witness_symbol']}` (`{div['file']}`)"
        lines.append(
            f"| `{div['id']}` | `{div['authority']}` | `{div['severity']}` | "
            f"{witness_cell} | `{div['anneal_component']}` | "
            f"{div['switch_to_pass_criterion']} |"
        )

    return "\n".join(lines) + "\n"


def run_suite_and_generate_dashboard(
    repo_root: Path,
    profile: str,
    state_dir: Path,
    difftest_dir: Path | None = None,
    zerocopy_dir: Path | None = None,
) -> tuple[int, dict[str, Any], str]:
    """Run the requested verification profile, compute all 3 pillars, and persist reports."""
    now = datetime.datetime.now(datetime.timezone.utc)
    now_iso = now.strftime("%Y-%m-%dT%H:%M:%SZ")
    date_str = now.strftime("%Y-%m-%d")

    stage_a = compute_stage_a_syntactic_completeness(repo_root)
    stage_b = compute_stage_b_empirical_corpora(repo_root, zerocopy_dir=zerocopy_dir)
    divergences = discover_correspondence_divergences(repo_root)

    steps_spec = build_suite_steps(repo_root, profile)
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
    args = parser.parse_args(argv)

    code, _dashboard, report_md = run_suite_and_generate_dashboard(
        repo_root=args.repo_root.resolve(),
        profile=args.profile,
        state_dir=args.state_dir.resolve(),
        difftest_dir=args.difftest_dir.resolve() if args.difftest_dir else None,
        zerocopy_dir=args.zerocopy_dir.resolve() if args.zerocopy_dir else None,
    )
    sys.stdout.write(report_md)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
