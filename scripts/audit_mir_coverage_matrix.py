#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Mechanical cross-check of Anneal's MIR coverage matrix.

Checks (each reported separately; `--check` exits 1 if any fails):

  a_mir_ast_constructors     `MIR_AST_CATEGORIES` (`scripts/run_nightly_verification_suite.py`)
                             equals, category by category, the constructors of the
                             `Trusted.Rustc.V2026_06_01.MirAst` inductives parsed from
                             `trusted/lean/.../MirAst/{Statements,Terminators,Places,Rvalues}.lean`
                             (no missing, phantom or duplicate entries; 94 in total), and every
                             rustc variant folded onto an existing constructor is backed by
                             its `trusted/rustc-capture` lowering arm.
  a_surface_totals           Stage-1 `LIntrinsicOp` count (cross-parsed), MiniRust / LeanMiri
                             Stage-A authority denominators, and the combined surface floor.
  b_untested_variants_zero   `supported_untested == 0` and `untested_variants == []`.
  c_variant_manifest         `tests/mir/MirUntestedVariantCorrespondenceTests.lean` carries
                             exactly one `-- @mir-variant-coverage` line per required variant,
                             naming `trusted` / `minirust` / `leanmiri` / `positive` /
                             `negative` theorems that are declared in code (not comments),
                             precede the trailing audit, reference the variant, and are named
                             in code by the trailing `run_cmd` audit (which names no other
                             theorem of the file), so the two manifests cannot drift.
  c_correspondence_test_hygiene / c_slice_lens_test_hygiene
                             No `sorry` / `admit` / `native_decide` / `axiom` / `unsafe` /
                             kernel-bypass tokens in code (comments and string literals
                             stripped), `sorryAx` / `ofReduceBool` only inside the trailing
                             `run_cmd` audit, which must exist (and, for the slice-lens suite,
                             keep its non-vacuity check).
  d_slice_lens_declarations  `SliceTypedAt` / `ActiveTypedSliceBorrow` /
                             `ActiveTypedSliceMutBorrow` definitions and the
                             `SliceTypedAt.splitAt` / `of_splitAt` / `DisjointSlice.adjacent`
                             lemmas exist.
  d_stage_b_blocker_separation
                             Behavioral probes through `analyze_corpus_completeness`: lifted
                             slice wide-pointer operations do not block `anneal_proof_lifters`,
                             unlifted unsized-DST constructs (and functions mixing both) do.
  e_vendored_source_anchors  Every `REQUIRED_SOURCE_ANCHORS` snippet is a line of its vendored
                             file, whose sha256 matches `lean-miri/UPSTREAM_PIN.json` /
                             `minirust/minirust.lock.toml`.
  e_source_anchor_quotes     The correspondence test quotes every required anchor (and only
                             valid ones) as `-- @source-anchor <relpath>#<snippet>`.

Exit codes: 0 report produced (with `--check`: every check passed); 1 with `--check`: at
least one check failed.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile
import tomllib
from types import ModuleType
from typing import Any, Callable, Iterable

SCHEMA_VERSION = 1
SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_REPO_ROOT = SCRIPT_DIR.parent
SUITE_RELPATH = "scripts/run_nightly_verification_suite.py"

# ---------------------------------------------------------------------------
# (a) `Trusted.MirAst` constructor census
# ---------------------------------------------------------------------------

MIR_AST_DIR = "trusted/lean/Trusted/Rustc/V2026_06_01/MirAst"
MIR_AST_FILES: tuple[str, ...] = tuple(
    f"{MIR_AST_DIR}/{name}.lean" for name in ("Statements", "Terminators", "Places", "Rvalues")
)
EXPECTED_CATEGORIES: tuple[str, ...] = (
    "StatementKind",
    "NonDivergingIntrinsic",
    "TerminatorKind",
    "ProjectionElem",
    "Rvalue",
    "BinOp",
    "UnOp",
    "CastKind",
    "AggregateKind",
)
KNOWN_STATUSES: tuple[str, ...] = (
    "proved_corresponding",
    "supported_and_tested",
    "supported_untested",
    "unsupported_fail_closed",
)
# 12 StatementKind + 2 NonDivergingIntrinsic + 11 TerminatorKind + 8 ProjectionElem + 15 Rvalue
# + 26 BinOp + 3 UnOp + 11 CastKind + 6 AggregateKind = 94 constructors. (The census used to
# claim 95 by also listing rustc's `AggregateKind::CoroutineClosure`, which has no constructor of
# its own: `mir_lower.rs` lowers it to `.closure`, see `RUSTC_VARIANTS_FOLDED_ONTO_CONSTRUCTORS`.)
EXPECTED_MIR_AST_TOTAL = 94
# rustc variants that `trusted/rustc-capture` lowers onto an existing constructor, so they are
# deliberately absent from both the inductive and the census. Each fold is checked against the
# lowering arm (consecutive stripped lines of `lowering_file`).
RUSTC_VARIANTS_FOLDED_ONTO_CONSTRUCTORS: tuple[dict[str, Any], ...] = (
    {
        "category": "AggregateKind",
        "rustc_variant": "CoroutineClosure",
        "folded_onto": "closure",
        "lowering_file": "trusted/rustc-capture/src/rustc_2026_06_01/mir_lower.rs",
        "lowering_lines": (
            "| AggregateKind::CoroutineClosure(def_id, _args) => {",
            "IrAggregateKind::Closure(canonical_def_path(self.tcx, *def_id))",
        ),
    },
)

LINTRINSIC_FILE = "theory/Anneal/Mir/AdtAndControl.lean"
# Combined syntactic surface = the Stage-A "Total Denominator" column of the nightly report:
#     94  Trusted.MirAst constructors        (`anneal_mir_ast.total_variants`, (a) above)
#   + 30  Stage-1 `LIntrinsicOp` constructors (`stage1_lowered_lintrinsic_op_variants`)
#   + 250 MiniRust spec items                 (`minirust_authority.spec_items_total`,
#                                              `minirust/coverage.json` items_by_kind)
#   + 608 vendored LeanMiri `Miri.*` files    (`lean_miri_authority.vendored_miri_files`)
#   = 982, comfortably above the >= 231 surface expected by the Episode 2 brief. The floor is
# the current value, so a silently collapsed denominator (e.g. a missing `coverage.json`)
# fails the audit; lower it only together with an intentional surface change.
COMBINED_SURFACE_FLOOR = 982
COMBINED_SURFACE_BRIEF_EXPECTATION = 231

# ---------------------------------------------------------------------------
# (c) correspondence test manifest & hygiene
# ---------------------------------------------------------------------------

UNTESTED_VARIANT_TEST = "tests/mir/MirUntestedVariantCorrespondenceTests.lean"
SLICE_LENS_TEST = "tests/mir/MirSliceWidePtrLensTests.lean"
REQUIRED_MANIFEST_VARIANTS: tuple[str, ...] = (
    "StatementKind.constEvalCounter",
    "TerminatorKind.tailCall",
    "ProjectionElem.opaqueCast",
)
MANIFEST_KEYS: tuple[str, ...] = ("trusted", "minirust", "leanmiri", "positive", "negative")
# A manifest theorem must reference its variant: directly (name or code) or through a
# declaration of the same file whose code does (transitively).
VARIANT_REFERENCE_RES: dict[str, re.Pattern[str]] = {
    "StatementKind.constEvalCounter": re.compile(r"const_?eval_?counter", re.IGNORECASE),
    "TerminatorKind.tailCall": re.compile(r"tail_?call", re.IGNORECASE),
    "ProjectionElem.opaqueCast": re.compile(r"opaque_?cast", re.IGNORECASE),
}
SLICE_LENS_NON_VACUITY_MESSAGE = "theorems not instantiated by any witness"
REQUIRED_AUDIT_MENTIONS: tuple[str, ...] = ("collectAxioms", "sorryAx", "Lean.ofReduceBool")

_NAME_BOUND_L = r"(?<![\w'!?])"
_NAME_BOUND_R = r"(?![\w'!?])"


def _word_re(word: str) -> re.Pattern[str]:
    return re.compile(_NAME_BOUND_L + re.escape(word) + _NAME_BOUND_R)


# Forbidden anywhere in code (comments and string literals stripped).
FORBIDDEN_CODE_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("sorry", _word_re("sorry")),
    ("admit", _word_re("admit")),
    ("native_decide", _word_re("native_decide")),
    ("decide +native", re.compile(r"\+\s*native" + _NAME_BOUND_R)),
    ("native := true", re.compile(_NAME_BOUND_L + r"native\s*:=\s*true" + _NAME_BOUND_R)),
    ("axiom declaration", _word_re("axiom")),
    ("unsafe", _word_re("unsafe")),
    ("implemented_by", _word_re("implemented_by")),
    ("@[extern]", re.compile(r"@\[\s*extern" + _NAME_BOUND_R)),
    ("debug.skipKernelTC", _word_re("skipKernelTC")),
    ("#exit", re.compile(r"(?m)^\s*#exit" + _NAME_BOUND_R)),
    ("admitGoal", _word_re("admitGoal")),
    ("mkSorry", re.compile(_NAME_BOUND_L + r"mk(?:Synthetic)?Sorry\w*")),
    ("axiomDecl", _word_re("axiomDecl")),
    ("addDeclWithoutChecking", _word_re("addDeclWithoutChecking")),
)
# Allowed only inside the trailing `run_cmd` audit, which names them to reject them.
AUDIT_ONLY_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("sorryAx", _word_re("sorryAx")),
    ("ofReduceBool", _word_re("ofReduceBool")),
    ("reduceBool", _word_re("reduceBool")),
    ("ofReduceNat", _word_re("ofReduceNat")),
    ("reduceNat", _word_re("reduceNat")),
    ("trustCompiler", _word_re("trustCompiler")),
)

# ---------------------------------------------------------------------------
# (d) Episode 1 slice lenses & Stage-B blocker separation
# ---------------------------------------------------------------------------

SEP_LOGIC_LENSES = "theory/Anneal/SepLogicLenses.lean"
LENS_THEORY_DIR = "theory/Anneal"
REQUIRED_LENS_DEFINITIONS: tuple[str, ...] = (
    "SliceTypedAt",
    "ActiveTypedSliceBorrow",
    "ActiveTypedSliceMutBorrow",
)
LENS_DEFINITION_KINDS: frozenset[str] = frozenset({"def", "structure", "abbrev"})
REQUIRED_LENS_LEMMAS: tuple[str, ...] = (
    "SliceTypedAt.splitAt",
    "SliceTypedAt.of_splitAt",
    "DisjointSlice.adjacent",
)
REQUIRED_DOGFOOD_PROOFS: tuple[str, ...] = (
    "examples/fxfs-storage-boundary/anneal/proofs/Proof/FxfsStorageBoundary/vmo_subslice_bounds_valid.lean",
    "examples/fxfs-storage-boundary/anneal/proofs/Proof/FxfsStorageBoundary/zerocopy_check_slice_len.lean",
    "examples/fxfs-storage-boundary/anneal/proofs/Proof/FxfsStorageBoundary/vmo_buffer_as_ref_unchecked.lean",
    "examples/fuchsia-usercopy/anneal/proofs/Proof/FuchsiaUsercopy/assume_initialized_until_split_len.lean",
    "examples/fuchsia-usercopy/anneal/proofs/Proof/FuchsiaUsercopy/fidl_chunk_padding_len.lean",
    "examples/fuchsia-usercopy/anneal/proofs/Proof/FuchsiaUsercopy/hermetic_copy_bytes_copied.lean",
    "examples/fuchsia-usercopy/anneal/proofs/Proof/FuchsiaUsercopy/usercopy_copyin_bracketed.lean",
)
DEFAULT_LIFTED_SLICE_BLOCKER = "slice_wide_ptr_lifted"
DEFAULT_UNSIZED_DST_BLOCKER = "unsized_dst_or_ptr_metadata"
LIFTERS_LAYER = "anneal_proof_lifters"



_VERIFIED_KINDS = (
    "StatefulVerificationResult",
    "ModularVerificationResult",
    "UbExceptionVerificationResult",
    "VerificationResult",
)


def _dogfood_crate_item(rel: str) -> tuple[str, str]:
    """`(Crate, item)` of `examples/<crate>/anneal/proofs/Proof/<Crate>/<item>.lean`."""
    parts = Path(rel).parts
    return parts[-2], Path(parts[-1]).stem


def _verified_signature_ok(header: str, crate: str, item: str) -> bool:
    """Whether the whitespace-normalized `theorem verified : ...` header (up to `:=`) is exactly
    `theorem verified : <Kind> Obligations.<crate>.<item>.<claim>`."""
    m = re.fullmatch(
        r"theorem verified : (" + "|".join(_VERIFIED_KINDS) + r") Obligations\."
        + re.escape(crate) + r"\." + re.escape(item) + r"\.[A-Za-z_][A-Za-z0-9_]*",
        header,
    )
    return m is not None

@dataclass(frozen=True)
class BlockerProbe:
    """A one-function Rust sample and whether it must block `anneal_proof_lifters`."""

    name: str
    source: str
    lifters_blocked: bool


STAGE_B_BLOCKER_PROBES: tuple[BlockerProbe, ...] = (
    BlockerProbe(
        "lifted_slice_raw_parts_and_split",
        """
pub fn probe(p: *mut u32, n: usize, k: usize) -> usize {
    let s = unsafe { core::slice::from_raw_parts(p, n) };
    let m = unsafe { core::slice::from_raw_parts_mut(p, n) };
    let w = core::ptr::slice_from_raw_parts(p, n);
    let wm = core::ptr::slice_from_raw_parts_mut(p, n);
    let nn = core::ptr::NonNull::slice_from_raw_parts(core::ptr::NonNull::dangling(), n);
    let (left, right) = m.split_at_mut(k);
    s.len() + left.len() + right.len()
}
""",
        False,
    ),
    BlockerProbe(
        "unsized_size_of_val",
        """
pub fn probe<T: ?Sized>(t: &T) -> usize {
    let n = core::mem::size_of_val(t);
    n + 1
}
""",
        True,
    ),
    BlockerProbe(
        "unsized_align_of_val_raw",
        """
pub fn probe(p: *const u8) -> usize {
    let a = unsafe { core::mem::align_of_val_raw(p) };
    a + 1
}
""",
        True,
    ),
    BlockerProbe(
        "generic_ptr_from_raw_parts",
        """
pub fn probe(p: *const u8, n: usize) -> usize {
    let w: *const [u8] = core::ptr::from_raw_parts(p, n);
    let x = 1;
    x
}
""",
        True,
    ),
    BlockerProbe(
        "dyn_metadata",
        """
pub fn probe(p: *const u8) -> usize {
    let meta = core::ptr::metadata(p);
    let x = 2;
    x
}
""",
        True,
    ),
    BlockerProbe(
        "lifted_slice_mixed_with_size_of_val",
        """
pub fn probe(p: *const u8, n: usize) -> usize {
    let s = unsafe { core::slice::from_raw_parts(p, n) };
    let bytes = core::mem::size_of_val(s);
    bytes
}
""",
        True,
    ),
    BlockerProbe(
        "lifted_slice_in_qsized_generic_fn",
        """
pub fn probe<T: ?Sized>(t: &T, p: *const u8, n: usize) -> *const [u8] {
    let w = core::ptr::slice_from_raw_parts(p, n);
    w
}
""",
        True,
    ),
    BlockerProbe(
        "lifted_slice_in_qsized_impl",
        """
pub struct W<T: ?Sized>(core::marker::PhantomData<T>);
impl<T: ?Sized> W<T> {
    pub fn probe(&self, p: *const u8, n: usize) -> *const [u8] {
        let w = core::ptr::slice_from_raw_parts_mut(p as *mut u8, n);
        w
    }
}
""",
        True,
    ),
    BlockerProbe(
        "unsized_ptr_to_raw_parts",
        """
pub fn probe(p: *const [u8]) -> (*const (), usize) {
    let parts = p.to_raw_parts();
    parts
}
""",
        True,
    ),
    BlockerProbe(
        "lifted_slice_with_comment_and_string_dst_tokens",
        """
/* impl<T: ?Sized> Ghost<T> { fn ghost() { core::mem::size_of_val(&0); } } */
pub fn probe(p: *const u8, n: usize) -> usize {
    let _msg = "http://example.com size_of_val T: ?Sized ptr::from_raw_parts";
    let _cstr = cr#"raw c string with " quote and size_of_val"#;
    let s = unsafe { core::slice::from_raw_parts(p, n) };
    s.len()
}
""",
        False,
    ),
    BlockerProbe(
        "unsized_qsized_returning_array",
        """
pub fn probe<T: ?Sized>(_t: &T, p: *const u8, n: usize) -> [usize; 2] {
    let _w = core::ptr::slice_from_raw_parts(p, n);
    [n, 0]
}
""",
        True,
    ),
)

# ---------------------------------------------------------------------------
# (e) vendored source anchors
# ---------------------------------------------------------------------------

LEAN_MIRI_PIN = "lean-miri/UPSTREAM_PIN.json"
LEAN_MIRI_VENDOR = "lean-miri/vendor/"
MINIRUST_LOCK = "minirust/minirust.lock.toml"
MINIRUST_VENDOR = "minirust/vendor/"
_MR = "minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src"
REQUIRED_SOURCE_ANCHORS: tuple[tuple[str, str], ...] = (
    (
        "lean-miri/vendor/Miri/Interpreter/Step.lean",
        "| .ConstEvalCounter => hooks.incrementConstEvalCounter choice state",
    ),
    ("lean-miri/vendor/Miri/Interpreter/Step.lean", "if oldIndex != newIndex then"),
    (
        "lean-miri/vendor/Miri/Interpreter/Step.lean",
        "let next := { currentLoc with statementIndex := currentLoc.statementIndex + 1 }",
    ),
    (
        "lean-miri/vendor/Miri/Interpreter/ExecutionMachine.lean",
        "incrementConstEvalCounter := fun _ state => (state,.ok ())",
    ),
    (
        "lean-miri/vendor/Miri/Interpreter/ExecutionMachine.lean",
        "tailCall := fun c terminator => MachineHooks.run "
        "(Call.evalTailCallTerminator calls c limits.callDispatch terminator)",
    ),
    (
        "lean-miri/vendor/Miri/Interpreter/Call.lean",
        "let args := evaluated.args.map fun arg => FnArg.Copy arg.copyFnArg",
    ),
    ("lean-miri/vendor/Miri/Interpreter/Call.lean", "let frame ← h.popRaw choice"),
    (
        "lean-miri/vendor/Miri/Interpreter/Call.lean",
        '| .stop _ => throw (.invalidProgram "cannot tailcall as root of stack")',
    ),
    (
        "lean-miri/vendor/Miri/Interpreter/Call.lean",
        "evaluated.withCallerLocation, frame.returnPlace, ret, unwind⟩",
    ),
    (
        "lean-miri/vendor/Miri/Interpreter/Call.lean",
        'require ((← h.frameIndex) == oldIndex) "evaluating this tail call pushed a new stack frame"',
    ),
    (
        "lean-miri/vendor/Miri/Interpreter/Call.lean",
        'throw (.undefinedBehavior "calling a function with more arguments than it expected")',
    ),
    ("lean-miri/vendor/Miri/Interpreter/Call.lean", 'throw (.undefinedBehavior "AbiMismatchReturn")'),
    (
        "lean-miri/vendor/Miri/Interpreter/Projection.lean",
        '| .OpaqueCast _ => throw (.invariant "OpaqueCast after borrowck")',
    ),
    (
        "lean-miri/vendor/Miri/Interpreter/PlaceDynamic.lean",
        '| .OpaqueCast _ => throw (.invalidProgram "OpaqueCast after borrowck")',
    ),
    (f"{_MR}/bb.rs", "| rs::StatementKind::ConstEvalCounter"),
    (f"{_MR}/bb.rs", "| rs::TerminatorKind::TailCall { .. }"),
    (f"{_MR}/rvalue.rs", "| smir::ProjectionElem::OpaqueCast(_) => {"),
)

_MANIFEST_LINE_RE = re.compile(
    r"^\s*--\s+@mir-variant-coverage\s+(?P<variant>\S+)"
    r"\s+trusted=(?P<trusted>\S+)\s+minirust=(?P<minirust>\S+)\s+leanmiri=(?P<leanmiri>\S+)"
    r"\s+positive=(?P<positive>\S+)\s+negative=(?P<negative>\S+)\s*$"
)
_LEAN_NAME_RE = re.compile(r"^[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*$")
_ANCHOR_LINE_RE = re.compile(r"^\s*--\s+@source-anchor\s+(?P<rel>[^\s#]+)#(?P<snippet>.*\S)\s*$")
# Lines that claim to be a manifest / anchor entry (a `--` comment starting with the tag); prose
# mentioning a tag elsewhere (e.g. in a docstring) is ignored, but a claimed entry that does not
# parse strictly is an error.
_MANIFEST_CANDIDATE_RE = re.compile(r"^\s*--\s*@mir-variant-coverage(?![\w-])")
_ANCHOR_CANDIDATE_RE = re.compile(r"^\s*--\s*@source-anchor(?![\w-])")


# ---------------------------------------------------------------------------
# Lean source scanning
# ---------------------------------------------------------------------------

_LEX_INTERESTING_RE = re.compile(r"«|--|/-|\"|'|(?<![\w'!?])r#*\"")
_LEX_INTERPOLATION_CODE_RE = re.compile(r"«|--|/-|\"|'|(?<![\w'!?])r#*\"|[{}]")
_CHAR_LITERAL_RE = re.compile(r"'(?:\\(?:u\{[0-9A-Fa-f]{1,6}\}|x[0-9A-Fa-f]{2}|.)|[^\\'\n])'")
# A string literal is lexed as an interpolated string (`{...}` segments are code, which may nest
# strings and char literals) after `s!` / `m!` / `f!` (any `...!`) and after the
# `interpolatedStr` macros `throwError`, `throwErrorAt <term>`, `trace[...]` and `dbg_trace`.
_INTERPOLATED_STRING_PREFIX_RE = re.compile(
    r"(?:!|(?<![\w'!?])(?:throwError|dbg_trace|trace\[[^\]\n]*\])\s*"
    r"|(?<![\w'!?])throwErrorAt\s+[^\s\"]+\s*)$"
)
# Other string literals are plain; simple `{...}` segments in them still stay visible as code.
_PLAIN_STRING_BRACES_RE = re.compile(r"\{[^{}\"\n]*\}")


def _is_lean_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'!?"


def _blank(segment: str) -> str:
    return re.sub(r"[^\n]", " ", segment)


def _line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


class _LeanLexer:
    """Position-preserving comment / literal stripper (see `strip_lean_source`)."""

    def __init__(self, text: str, keep_strings: bool) -> None:
        self.text = text
        self.n = len(text)
        self.keep = keep_strings
        self.out: list[str] = []
        self.errors: list[str] = []

    def literal(self, start: int, end: int) -> None:
        seg = self.text[start:end]
        self.out.append(seg if self.keep else _blank(seg))

    def code(self, i: int, in_interpolation: bool) -> int:
        """Lex code from `i`; inside an interpolation, stop at (and return the index of) the
        matching `}`."""
        depth = 0
        pattern = _LEX_INTERPOLATION_CODE_RE if in_interpolation else _LEX_INTERESTING_RE
        while i < self.n:
            m = pattern.search(self.text, i)
            if not m:
                self.out.append(self.text[i:])
                return self.n
            j, tok = m.start(), m.group(0)
            self.out.append(self.text[i:j])
            if tok == "{":
                depth += 1
                self.out.append(tok)
                i = j + 1
            elif tok == "}":
                if depth == 0:
                    return j
                depth -= 1
                self.out.append(tok)
                i = j + 1
            else:
                i = self.token(j, tok)
        return self.n

    def token(self, j: int, tok: str) -> int:
        text, n = self.text, self.n
        if tok == "«":
            end = text.find("»", j + 1)
            if end != -1 and "\n" not in text[j + 1 : end]:
                self.out.append(text[j : end + 1])
                return end + 1
            self.out.append(tok)
            return j + 1
        if tok == "--":
            end = text.find("\n", j)
            end = n if end == -1 else end
            self.out.append(_blank(text[j:end]))
            return end
        if tok == "/-":
            depth, k = 1, j + 2
            while k < n and depth:
                if text.startswith("/-", k):
                    depth, k = depth + 1, k + 2
                elif text.startswith("-/", k):
                    depth, k = depth - 1, k + 2
                else:
                    k += 1
            if depth:
                self.errors.append(f"unterminated block comment starting at line {_line_of(text, j)}")
            self.out.append(_blank(text[j:k]))
            return k
        if tok == "'":
            lit = _CHAR_LITERAL_RE.match(text, j) if j == 0 or not _is_lean_ident_char(text[j - 1]) else None
            if lit:
                self.literal(j, lit.end())
                return lit.end()
            self.out.append(tok)
            return j + 1
        if tok.startswith("r"):
            close = '"' + tok[1:-1]
            end = text.find(close, j + len(tok))
            if end == -1:
                self.errors.append(f"unterminated raw string literal starting at line {_line_of(text, j)}")
                end_excl = n
            else:
                end_excl = end + len(close)
            self.literal(j, end_excl)
            return end_excl
        return self.string(j)

    def string(self, j: int) -> int:
        text, n = self.text, self.n
        if _INTERPOLATED_STRING_PREFIX_RE.search(text, max(0, j - 80), j):
            seg_start, k = j, j + 1
            while k < n:
                c = text[k]
                if c == "\\":
                    k += 2
                elif c == '"':
                    self.literal(seg_start, k + 1)
                    return k + 1
                elif c == "{":
                    self.literal(seg_start, k + 1)
                    close = self.code(k + 1, in_interpolation=True)
                    if close >= n:
                        self.errors.append(f"unterminated string interpolation starting at line {_line_of(text, k)}")
                        return n
                    seg_start, k = close, close + 1
                else:
                    k += 1
            self.errors.append(f"unterminated string literal starting at line {_line_of(text, j)}")
            self.literal(seg_start, n)
            return n
        k = j + 1
        while k < n and text[k] != '"':
            k += 2 if text[k] == "\\" else 1
        if k >= n:
            self.errors.append(f"unterminated string literal starting at line {_line_of(text, j)}")
            end_excl = n
        else:
            end_excl = k + 1
        seg = text[j:end_excl]
        if self.keep:
            self.out.append(seg)
        else:
            blanked = list(_blank(seg))
            for im in _PLAIN_STRING_BRACES_RE.finditer(seg):
                blanked[im.start() : im.end()] = list(im.group(0))
            self.out.append("".join(blanked))
        return end_excl


def strip_lean_source(text: str, keep_strings: bool = False) -> tuple[str, list[str]]:
    """`text` with `--` line comments, (nested) `/- -/` block comments (including docstrings)
    and, unless `keep_strings`, string / char literal contents blanked to spaces (newlines kept,
    so offsets and line numbers are preserved). `«...»` identifiers are kept verbatim and the
    `{...}` code of interpolated strings stays visible. Returns the stripped text and lexing
    errors (an unterminated comment, string or interpolation fails closed)."""
    lexer = _LeanLexer(text, keep_strings)
    lexer.code(0, in_interpolation=False)
    return "".join(lexer.out), lexer.errors


_NAMESPACE_RE = re.compile(r"^\s*namespace\s+(\S+)")
_SECTION_RE = re.compile(r"^\s*(?:(?:noncomputable|public|private)\s+)*section\b")
_MUTUAL_RE = re.compile(r"^\s*mutual\b")
_END_RE = re.compile(r"^\s*end\b(?:\s+\S+)?\s*$")
_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|nonrec|unsafe|scoped|local|public|meta)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|example)"
    r"(?![\w'!?])(?:[ \t]+(?P<name>«[^»\n]+»|[^\s:({\[⦃«]+))?"
)
_IDENT_TOKEN_RE = re.compile(r"«[^»\n]+»|[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*")
# `` `name `` / ``` ``name ``` literals (the leading backticks are not part of the capture).
_NAME_LITERAL_RE = re.compile(r"(?<![\w'!?`])``?([^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*)")
_RUN_CMD_RE = re.compile(r"run_cmd(?![\w'!?])")


@dataclass
class LeanDecl:
    kind: str
    written_name: str
    qualified_name: str
    start_line: int  # 0-based
    end_line: int  # exclusive


def _unguillemet(name: str) -> str:
    return name.replace("«", "").replace("»", "")


def scan_lean_declarations(code: str) -> list[LeanDecl]:
    """Named top-level declarations of stripped Lean `code`, with namespace-qualified names and
    line spans (a declaration ends before the next non-blank column-0 line)."""
    lines = code.split("\n")
    stack: list[list[str]] = []
    decls: list[LeanDecl] = []
    for idx, line in enumerate(lines):
        if not line.strip():
            continue
        m_ns = _NAMESPACE_RE.match(line)
        if m_ns:
            stack.append(_unguillemet(m_ns.group(1)).split("."))
            continue
        if _SECTION_RE.match(line) or _MUTUAL_RE.match(line):
            stack.append([])
            continue
        if _END_RE.match(line):
            if stack:
                stack.pop()
            continue
        m_decl = _DECL_RE.match(line)
        if not m_decl or not m_decl.group("name"):
            continue
        written = _unguillemet(m_decl.group("name"))
        if written.startswith("_root_."):
            qualified = written[len("_root_.") :]
        else:
            qualified = ".".join([*(c for comps in stack for c in comps), written])
        end = idx + 1
        while end < len(lines) and (not lines[end].strip() or lines[end][0] in " \t"):
            end += 1
        decls.append(LeanDecl(m_decl.group("kind"), written, qualified, idx, end))
    return decls


def _decl_matches(decl: LeanDecl, name: str) -> bool:
    return (
        decl.written_name == name
        or decl.qualified_name == name
        or decl.qualified_name.endswith("." + name)
    )


# Constructor name after `|`, skipping attributes and `private` / `protected` modifiers.
_CTOR_NAME_RE = re.compile(
    r"\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(«[^»\n]+»|[^\W\d][\w'!?]*)"
)


def parse_inductive_constructors(code: str, inductive: str) -> list[str] | None:
    """Constructor names of `inductive <inductive>` in stripped Lean `code` (in order, duplicates
    kept), or `None` if the inductive is not declared. Handles `| name (args) : T`, several
    constructors per line, multi-line argument lists and `deriving` clauses."""
    m = re.search(
        r"(?m)^[ \t]*(?:(?:private|protected|unsafe|partial|nonrec|public)\s+)*inductive\s+"
        + re.escape(inductive)
        + _NAME_BOUND_R,
        code,
    )
    if not m:
        return None
    rest = code[m.end() :]
    first_bar = re.search(r"(?m)^\s*\|", rest)
    where = re.search(r"(?<![\w'!?])where(?![\w'!?])", rest)
    if where and (first_bar is None or where.start() < first_bar.start()):
        body_start = where.end()
    elif first_bar:
        body_start = first_bar.start()
    else:
        return []
    body_lines: list[str] = []
    for k, line in enumerate(rest[body_start:].split("\n")):
        if re.match(r"^\s*deriving(?![\w'!?])", line):
            break
        if k > 0 and line.strip() and line[0] not in " \t|":
            break
        body_lines.append(line)
    body = "\n".join(body_lines)
    names: list[str] = []
    depth = 0
    pos = 0
    while pos < len(body):
        ch = body[pos]
        if ch in "([{⟨⦃":
            depth += 1
        elif ch in ")]}⟩⦄":
            depth = max(0, depth - 1)
        elif ch == "|" and depth == 0:
            name_m = _CTOR_NAME_RE.match(body, pos + 1)
            if name_m:
                names.append(_unguillemet(name_m.group(1)))
                pos = name_m.end()
                continue
        pos += 1
    return names


def find_trailing_audit_start(code_lines: list[str]) -> int | None:
    """0-based line of the first `run_cmd` of the file's trailing audit region: the maximal
    suffix made only of indented lines, blank lines, `end ...`, `open ... in` /
    `set_option ... in` prefixes and `run_cmd` commands (so no declaration follows it)."""
    region_start = len(code_lines)
    for idx in range(len(code_lines) - 1, -1, -1):
        line = code_lines[idx]
        if (
            not line.strip()
            or line[0] in " \t"
            or _END_RE.match(line)
            or _RUN_CMD_RE.match(line)
            or re.match(r"(?:open|set_option)(?![\w'!?]).*(?<![\w'!?])in\s*$", line)
        ):
            region_start = idx
            continue
        break
    for idx in range(region_start, len(code_lines)):
        if _RUN_CMD_RE.match(code_lines[idx]):
            return idx
    return None


# ---------------------------------------------------------------------------
# Results
# ---------------------------------------------------------------------------


@dataclass
class CheckResult:
    check_id: str
    title: str
    errors: list[str] = field(default_factory=list)
    details: dict[str, Any] = field(default_factory=dict)

    @property
    def ok(self) -> bool:
        return not self.errors

    def to_json(self) -> dict[str, Any]:
        return {"ok": self.ok, "title": self.title, "errors": self.errors, "details": self.details}


def load_suite_module(repo_root: Path) -> ModuleType:
    """Load `scripts/run_nightly_verification_suite.py` from `repo_root` (so fixture trees can
    carry their own copy), falling back to the copy next to this script."""
    candidate = repo_root / SUITE_RELPATH
    if not candidate.is_file():
        candidate = SCRIPT_DIR / Path(SUITE_RELPATH).name
    resolved = candidate.resolve()
    mod_name = "_mir_cov_audit_suite_" + hashlib.sha256(str(resolved).encode()).hexdigest()[:16]
    spec = importlib.util.spec_from_file_location(mod_name, resolved)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {resolved}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[mod_name] = module
    try:
        spec.loader.exec_module(module)
    except BaseException:
        sys.modules.pop(mod_name, None)
        raise
    return module


def _read_text(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return None


class _Audit:
    def __init__(self, repo_root: Path) -> None:
        self.root = repo_root
        self.suite: ModuleType | None = None
        self.suite_error: str | None = None
        try:
            self.suite = load_suite_module(repo_root)
        except Exception as exc:  # noqa: BLE001 - reported as a check failure
            self.suite_error = f"cannot load {SUITE_RELPATH}: {type(exc).__name__}: {exc}"
        self._stage_a: dict[str, Any] | None = None
        self._lean_cache: dict[tuple[str, bool], tuple[str, list[str]] | None] = {}

    # -- helpers ----------------------------------------------------------

    def require_suite(self, res: CheckResult) -> ModuleType | None:
        if self.suite is None:
            res.errors.append(self.suite_error or f"cannot load {SUITE_RELPATH}")
        return self.suite

    def stage_a(self) -> dict[str, Any]:
        if self._stage_a is None:
            assert self.suite is not None
            self._stage_a = self.suite.compute_stage_a_syntactic_completeness(self.root)
        return self._stage_a

    def lean(self, rel: str, keep_strings: bool = False) -> tuple[str, list[str]] | None:
        key = (rel, keep_strings)
        if key not in self._lean_cache:
            text = _read_text(self.root / rel)
            self._lean_cache[key] = None if text is None else strip_lean_source(text, keep_strings)
        return self._lean_cache[key]

    # -- (a) ----------------------------------------------------------------

    def check_mir_ast_constructors(self) -> CheckResult:
        res = CheckResult("a_mir_ast_constructors", "MIR_AST_CATEGORIES == Trusted.MirAst constructors")
        suite = self.require_suite(res)
        if suite is None:
            return res
        categories = list(getattr(suite, "MIR_AST_CATEGORIES", []))
        seen_categories: dict[str, int] = {}
        per_category: dict[str, Any] = {}
        census_total = 0
        lean_total = 0
        lean_constructors: dict[str, list[str]] = {}
        census_sets: dict[str, set[str]] = {}
        for entry in categories:
            cat = str(entry.get("category"))
            seen_categories[cat] = seen_categories.get(cat, 0) + 1
            variants = [(str(v), str(s)) for v, s in entry.get("variants", [])]
            names = [v for v, _s in variants]
            census_total += len(names)
            census_sets[cat] = set(names)
            info: dict[str, Any] = {"census": len(names), "file": entry.get("file")}
            dups = sorted({v for v in names if names.count(v) > 1})
            if dups:
                res.errors.append(f"{cat}: duplicate census entries {dups}")
            for v, s in variants:
                if s not in KNOWN_STATUSES:
                    res.errors.append(f"{cat}.{v}: unknown status {s!r}")
            if cat not in EXPECTED_CATEGORIES:
                res.errors.append(f"{cat}: unexpected census category (expected {list(EXPECTED_CATEGORIES)})")
            rel = str(entry.get("file"))
            if rel not in MIR_AST_FILES:
                res.errors.append(f"{cat}: census file {rel!r} is not one of {list(MIR_AST_FILES)}")
            stripped = self.lean(rel) if rel in MIR_AST_FILES else None
            if stripped is None:
                if rel in MIR_AST_FILES:
                    res.errors.append(f"{cat}: cannot read {rel}")
                per_category[cat] = info
                continue
            code, lex_errors = stripped
            for err in lex_errors:
                res.errors.append(f"{rel}: {err}")
            ctors = parse_inductive_constructors(code, cat)
            if ctors is None:
                res.errors.append(f"{cat}: `inductive {cat}` not found in {rel}")
                per_category[cat] = info
                continue
            lean_constructors[cat] = ctors
            lean_total += len(ctors)
            info["lean"] = len(ctors)
            lean_dups = sorted({c for c in ctors if ctors.count(c) > 1})
            if lean_dups:
                res.errors.append(f"{cat}: duplicate constructors parsed from {rel}: {lean_dups}")
            missing = sorted(set(ctors) - set(names))
            phantom = sorted(set(names) - set(ctors))
            if missing:
                res.errors.append(f"{cat}: constructors missing from MIR_AST_CATEGORIES: {missing}")
            if phantom:
                res.errors.append(f"{cat}: census entries with no `{cat}` constructor in {rel}: {phantom}")
            info.update({"missing_from_census": missing, "phantom_in_census": phantom})
            per_category[cat] = info
        for cat, count in seen_categories.items():
            if count > 1:
                res.errors.append(f"{cat}: category listed {count} times in MIR_AST_CATEGORIES")
        absent = [c for c in EXPECTED_CATEGORIES if c not in seen_categories]
        if absent:
            res.errors.append(f"categories missing from MIR_AST_CATEGORIES: {absent}")
        if census_total != EXPECTED_MIR_AST_TOTAL:
            res.errors.append(f"MIR_AST_CATEGORIES lists {census_total} variants, expected {EXPECTED_MIR_AST_TOTAL}")
        if lean_total != EXPECTED_MIR_AST_TOTAL:
            res.errors.append(f"parsed {lean_total} Trusted.MirAst constructors, expected {EXPECTED_MIR_AST_TOTAL}")
        folds: list[dict[str, Any]] = []
        for fold in RUSTC_VARIANTS_FOLDED_ONTO_CONSTRUCTORS:
            cat = fold["category"]
            rustc = fold["rustc_variant"]
            lean_name = rustc[:1].lower() + rustc[1:]
            target = fold["folded_onto"]
            ctors = lean_constructors.get(cat, [])
            if lean_name in ctors:
                res.errors.append(
                    f"{cat}.{lean_name} now has its own constructor: drop it from "
                    "RUSTC_VARIANTS_FOLDED_ONTO_CONSTRUCTORS and classify it in MIR_AST_CATEGORIES"
                )
            if target not in ctors or target not in census_sets.get(cat, set()):
                res.errors.append(f"{cat}: fold target `.{target}` of rustc `{rustc}` is not a censused constructor")
            lowering = _read_text(self.root / fold["lowering_file"])
            stripped_lines = [] if lowering is None else [ln.strip() for ln in lowering.splitlines()]
            want = [ln.strip() for ln in fold["lowering_lines"]]
            found = any(
                stripped_lines[k : k + len(want)] == want for k in range(max(0, len(stripped_lines) - len(want) + 1))
            )
            if not found:
                res.errors.append(
                    f"{fold['lowering_file']}: lowering arm folding rustc `{cat}::{rustc}` onto `.{target}` not found"
                )
            folds.append({"category": cat, "rustc_variant": rustc, "folded_onto": target, "verified": found})
        res.details = {
            "census_total": census_total,
            "lean_constructor_total": lean_total,
            "expected_total": EXPECTED_MIR_AST_TOTAL,
            "by_category": per_category,
            "rustc_variants_folded_onto_constructors": folds,
        }
        return res

    def check_surface_totals(self) -> CheckResult:
        res = CheckResult("a_surface_totals", "LIntrinsicOp / MiniRust / LeanMiri totals and combined surface floor")
        if self.require_suite(res) is None:
            return res
        stage_a = self.stage_a()
        mir = stage_a["anneal_mir_ast"]
        lintrinsic = int(mir.get("stage1_lowered_lintrinsic_op_variants", 0))
        stripped = self.lean(LINTRINSIC_FILE)
        parsed_lintrinsic: int | None = None
        if stripped is None:
            res.errors.append(f"cannot read {LINTRINSIC_FILE}")
        else:
            ctors = parse_inductive_constructors(stripped[0], "LIntrinsicOp")
            if ctors is None:
                res.errors.append(f"`inductive LIntrinsicOp` not found in {LINTRINSIC_FILE}")
            else:
                parsed_lintrinsic = len(ctors)
                if parsed_lintrinsic != lintrinsic:
                    res.errors.append(
                        f"Stage-A LIntrinsicOp count {lintrinsic} disagrees with the parsed {parsed_lintrinsic}"
                    )
        minirust_items = int(stage_a["minirust_authority"].get("spec_items_total", 0))
        lean_miri_files = int(stage_a["lean_miri_authority"].get("vendored_miri_files", 0))
        mir_total = int(mir.get("total_variants", 0))
        combined = mir_total + lintrinsic + minirust_items + lean_miri_files
        if combined < COMBINED_SURFACE_FLOOR:
            res.errors.append(
                f"combined surface {combined} = {mir_total} MirAst + {lintrinsic} LIntrinsicOp + "
                f"{minirust_items} MiniRust items + {lean_miri_files} LeanMiri files < floor {COMBINED_SURFACE_FLOOR}"
            )
        res.details = {
            "trusted_mir_ast_constructors": mir_total,
            "stage1_lintrinsic_op_variants": lintrinsic,
            "stage1_lintrinsic_op_variants_parsed": parsed_lintrinsic,
            "minirust_spec_items_total": minirust_items,
            "minirust_spec_fns_total": int(stage_a["minirust_authority"].get("spec_fns_total", 0)),
            "lean_miri_vendored_files": lean_miri_files,
            "combined_surface_total": combined,
            "combined_surface_floor": COMBINED_SURFACE_FLOOR,
            "brief_expectation": COMBINED_SURFACE_BRIEF_EXPECTATION,
            "arithmetic": f"{mir_total} + {lintrinsic} + {minirust_items} + {lean_miri_files} = {combined}",
        }
        return res

    # -- (b) ----------------------------------------------------------------

    def check_untested_zero(self) -> CheckResult:
        res = CheckResult("b_untested_variants_zero", "supported_untested == 0 and untested_variants == []")
        if self.require_suite(res) is None:
            return res
        mir = self.stage_a()["anneal_mir_ast"]
        untested = list(mir.get("untested_variants", []))
        count = int(mir.get("supported_untested", -1))
        if count != 0:
            res.errors.append(f"supported_untested == {count}, expected 0")
        if untested:
            res.errors.append(f"untested_variants == {untested}, expected []")
        res.details = {
            "supported_untested": count,
            "untested_variants": untested,
            "proved_corresponding": mir.get("proved_corresponding"),
            "supported_and_tested": mir.get("supported_and_tested"),
            "unsupported_fail_closed": mir.get("unsupported_fail_closed"),
            "total_variants": mir.get("total_variants"),
        }
        return res

    # -- (c) ----------------------------------------------------------------

    def _hygiene(self, res: CheckResult, rel: str, required_mentions: Iterable[str], required_strings: Iterable[str]) -> None:
        stripped = self.lean(rel)
        kept = self.lean(rel, keep_strings=True)
        if stripped is None or kept is None:
            res.errors.append(f"{rel}: missing or unreadable")
            return
        code, lex_errors = stripped
        for err in lex_errors:
            res.errors.append(f"{rel}: {err}")
        code_lines = code.split("\n")
        audit_start = find_trailing_audit_start(code_lines)
        res.details["trailing_audit_line"] = None if audit_start is None else audit_start + 1
        for label, pattern in FORBIDDEN_CODE_PATTERNS:
            for m in pattern.finditer(code):
                res.errors.append(f"{rel}:{_line_of(code, m.start())}: forbidden `{label}` in code")
        audit_offset = len(code) if audit_start is None else sum(len(ln) + 1 for ln in code_lines[:audit_start])
        # Audit-only names are also rejected inside string literals before the audit, so they
        # cannot be smuggled in as `Name.mkSimple "sorryAx"`.
        kept_code = kept[0]
        for label, pattern in AUDIT_ONLY_PATTERNS:
            for m in pattern.finditer(kept_code, 0, audit_offset):
                res.errors.append(f"{rel}:{_line_of(code, m.start())}: `{label}` outside the trailing run_cmd audit")
        if audit_start is None:
            res.errors.append(f"{rel}: no trailing `run_cmd` audit block (nothing but the audit may follow it)")
            return
        audit_code = code[audit_offset:]
        audit_kept = kept[0][audit_offset:]
        for word in required_mentions:
            if not _word_re(word).search(audit_code):
                res.errors.append(f"{rel}: trailing run_cmd audit does not reference `{word}` in code")
        for text in required_strings:
            if text not in audit_kept:
                res.errors.append(f"{rel}: trailing run_cmd audit lost its check {text!r}")

    def check_correspondence_hygiene(self) -> CheckResult:
        res = CheckResult(
            "c_correspondence_test_hygiene", f"{UNTESTED_VARIANT_TEST}: no sorry/axiom/native_decide; run_cmd audit"
        )
        self._hygiene(res, UNTESTED_VARIANT_TEST, REQUIRED_AUDIT_MENTIONS, ())
        return res

    def check_slice_lens_hygiene(self) -> CheckResult:
        res = CheckResult("c_slice_lens_test_hygiene", f"{SLICE_LENS_TEST}: hygiene and non-vacuity run_cmd audit")
        self._hygiene(res, SLICE_LENS_TEST, ("collectAxioms",), (SLICE_LENS_NON_VACUITY_MESSAGE,))
        return res

    def check_variant_manifest(self) -> CheckResult:
        res = CheckResult("c_variant_manifest", f"{UNTESTED_VARIANT_TEST}: @mir-variant-coverage manifest")
        rel = UNTESTED_VARIANT_TEST
        text = _read_text(self.root / rel)
        stripped = self.lean(rel)
        if text is None or stripped is None:
            res.errors.append(f"{rel}: missing or unreadable")
            return res
        code = stripped[0]
        code_lines = code.split("\n")
        audit_start = find_trailing_audit_start(code_lines)
        decls = scan_lean_declarations(code)
        census = self._census_variants()
        entries: dict[str, dict[str, list[str]]] = {}
        for lineno, line in enumerate(text.splitlines(), start=1):
            if not _MANIFEST_CANDIDATE_RE.match(line):
                continue
            m = _MANIFEST_LINE_RE.match(line)
            if not m:
                res.errors.append(f"{rel}:{lineno}: malformed @mir-variant-coverage line")
                continue
            variant = m.group("variant")
            if variant in entries:
                res.errors.append(f"{rel}:{lineno}: duplicate manifest line for {variant}")
                continue
            if variant not in REQUIRED_MANIFEST_VARIANTS:
                where = "a censused" if variant in census else "an unknown"
                res.errors.append(f"{rel}:{lineno}: {variant} is {where} variant outside {list(REQUIRED_MANIFEST_VARIANTS)}")
                continue
            lists: dict[str, list[str]] = {}
            for key in MANIFEST_KEYS:
                names = m.group(key).split(",")
                if any(not _LEAN_NAME_RE.match(nm) for nm in names):
                    res.errors.append(f"{rel}:{lineno}: {variant} {key}= has an empty or invalid theorem name: {m.group(key)!r}")
                    names = [nm for nm in names if _LEAN_NAME_RE.match(nm)]
                dups = sorted({nm for nm in names if names.count(nm) > 1})
                if dups:
                    res.errors.append(f"{rel}:{lineno}: {variant} {key}= repeats {dups}")
                lists[key] = names
            overlap = sorted(set(lists["positive"]) & set(lists["negative"]))
            if overlap:
                res.errors.append(f"{rel}:{lineno}: {variant} lists {overlap} as both positive and negative witnesses")
            entries[variant] = lists
        for variant in REQUIRED_MANIFEST_VARIANTS:
            if variant not in entries:
                res.errors.append(f"{rel}: no @mir-variant-coverage line for {variant}")
        # Theorems declared after the last `run_cmd` escape it, trailing or not.
        cutoff = audit_start
        if cutoff is None:
            run_cmds = [i for i, ln in enumerate(code_lines) if _RUN_CMD_RE.match(ln)]
            cutoff = run_cmds[-1] if run_cmds else None
        audit_code = "\n".join(code_lines[audit_start:]) if audit_start is not None else None
        if audit_code is None:
            res.errors.append(f"{rel}: no trailing run_cmd audit to re-check the manifest against")
        mentions = _VariantMentions(decls, code_lines)
        theorem_report: dict[str, dict[str, list[str]]] = {}
        manifest_names: set[str] = set()
        for variant, lists in entries.items():
            pattern = VARIANT_REFERENCE_RES[variant]
            theorem_report[variant] = lists
            for key, names in lists.items():
                for nm in names:
                    manifest_names.add(nm)
                    if audit_code is not None and not _word_re(nm).search(audit_code):
                        res.errors.append(
                            f"{rel}: {variant} {key}= theorem `{nm}` is not named in code by the trailing run_cmd audit"
                        )
                    thms = [d for d in decls if d.kind == "theorem" and _decl_matches(d, nm)]
                    if not thms:
                        res.errors.append(
                            f"{rel}: {variant} {key}= theorem `{nm}` is not declared in code (`theorem {nm}`)"
                        )
                        continue
                    if cutoff is not None and all(d.start_line >= cutoff for d in thms):
                        res.errors.append(f"{rel}: {variant} {key}= theorem `{nm}` is declared after the run_cmd audit")
                    if not any(mentions.references(d, pattern) for d in thms):
                        res.errors.append(
                            f"{rel}: {variant} {key}= theorem `{nm}` never references {variant} "
                            "(directly or through a declaration of this file)"
                        )
        # Conversely, every theorem of this file that the audit names must be in the manifest.
        unlisted: list[str] = []
        if audit_code is not None:
            for literal in sorted(set(_NAME_LITERAL_RE.findall(audit_code))):
                for d in decls:
                    if d.kind != "theorem" or not _decl_matches(d, literal):
                        continue
                    if not ({literal, d.written_name} & manifest_names) and literal not in unlisted:
                        unlisted.append(literal)
        for literal in unlisted:
            res.errors.append(f"{rel}: the run_cmd audit names theorem `{literal}`, which no @mir-variant-coverage line lists")
        # Divergences documented here must surface in the nightly suite's Pillar 3 registry, and every
        # registry witness pointing at this file must be a kernel-audited manifest theorem — so a
        # divergence can neither be buried in this file nor tracked against an unaudited name.
        tracked_here: dict[str, str] = {}
        seen_ids: set[str] = set()
        tracked = getattr(self.suite, "TRACKED_CORRESPONDENCE_DIVERGENCES", None) if self.suite is not None else None
        if not isinstance(tracked, list):
            res.errors.append(f"{SUITE_RELPATH}: TRACKED_CORRESPONDENCE_DIVERGENCES is missing")
        else:
            for item in tracked:
                if not isinstance(item, dict):
                    continue
                div_id = str(item.get("id", "?"))
                if div_id in seen_ids:
                    res.errors.append(f"{SUITE_RELPATH}: duplicate divergence id `{div_id}` in TRACKED_CORRESPONDENCE_DIVERGENCES")
                seen_ids.add(div_id)
                if item.get("file") == rel:
                    sym = str(item.get("witness_symbol", ""))
                    if sym in tracked_here:
                        res.errors.append(
                            f"{SUITE_RELPATH}: duplicate divergence witness `{sym}` ({tracked_here[sym]} and {div_id})"
                        )
                    tracked_here[sym] = div_id
            for sym, div_id in sorted(tracked_here.items()):
                if sym not in manifest_names:
                    res.errors.append(
                        f"{SUITE_RELPATH}: divergence {div_id} witness `{sym}` is not a manifest theorem of {rel}"
                    )
            for nm in sorted(manifest_names):
                if "diverge" in nm.lower() and nm not in tracked_here:
                    res.errors.append(
                        f"{rel}: divergence theorem `{nm}` is not tracked in {SUITE_RELPATH} "
                        "TRACKED_CORRESPONDENCE_DIVERGENCES"
                    )
        res.details = {
            "entries": theorem_report,
            "declarations_scanned": len(decls),
            "trailing_audit_line": None if audit_start is None else audit_start + 1,
            "tracked_divergences": dict(sorted((v, k) for k, v in tracked_here.items())),
        }
        return res

    def _census_variants(self) -> set[str]:
        if self.suite is None:
            return set()
        return {
            f"{entry['category']}.{v}"
            for entry in getattr(self.suite, "MIR_AST_CATEGORIES", [])
            for v, _s in entry.get("variants", [])
        }

    # -- (d) ----------------------------------------------------------------

    def check_slice_lens_declarations(self) -> CheckResult:
        res = CheckResult("d_slice_lens_declarations", "Episode 1 slice lens definitions and split/adjacency lemmas")
        stripped = self.lean(SEP_LOGIC_LENSES)
        found_defs: dict[str, str] = {}
        if stripped is None:
            res.errors.append(f"cannot read {SEP_LOGIC_LENSES}")
        else:
            for err in stripped[1]:
                res.errors.append(f"{SEP_LOGIC_LENSES}: {err}")
            for decl in scan_lean_declarations(stripped[0]):
                last = decl.qualified_name.rsplit(".", 1)[-1]
                if last in REQUIRED_LENS_DEFINITIONS and decl.kind in LENS_DEFINITION_KINDS:
                    found_defs.setdefault(last, decl.qualified_name)
            for name in REQUIRED_LENS_DEFINITIONS:
                if name not in found_defs:
                    res.errors.append(f"{SEP_LOGIC_LENSES}: no `def`/`structure`/`abbrev` {name}")
        found_lemmas: dict[str, str] = {}
        theory_dir = self.root / LENS_THEORY_DIR
        files = sorted(theory_dir.rglob("*.lean")) if theory_dir.is_dir() else []
        for path in files:
            raw = _read_text(path)
            if raw is None:
                continue
            wanted = [
                nm
                for nm in REQUIRED_LENS_LEMMAS
                if nm not in found_lemmas and all(part in raw for part in nm.split("."))
            ]
            if not wanted:
                continue
            code, _errs = strip_lean_source(raw)
            for decl in scan_lean_declarations(code):
                for nm in wanted:
                    if nm not in found_lemmas and _decl_matches(decl, nm):
                        found_lemmas[nm] = f"{path.relative_to(self.root).as_posix()}:{decl.start_line + 1}"
        for nm in REQUIRED_LENS_LEMMAS:
            if nm not in found_lemmas:
                res.errors.append(f"no declaration of `{nm}` under {LENS_THEORY_DIR}/")
        dogfood_report: dict[str, list[str]] = {}
        if (self.root / "examples").is_dir():
            lens_re = re.compile(r"\b(?:" + "|".join(re.escape(x) for x in REQUIRED_LENS_DEFINITIONS) + r")\b")
            wide_re = _word_re("WidePtrVal")
            for rel in REQUIRED_DOGFOOD_PROOFS:
                d_stripped = self.lean(rel)
                if d_stripped is None:
                    res.errors.append(f"{rel}: missing or unreadable dogfood proof")
                    continue
                d_code, d_errs = d_stripped
                for err in d_errs:
                    res.errors.append(f"{rel}: {err}")
                for label, pattern in FORBIDDEN_CODE_PATTERNS:
                    for m in pattern.finditer(d_code):
                        res.errors.append(f"{rel}:{_line_of(d_code, m.start())}: forbidden `{label}` in code")
                d_lines = d_code.split("\n")
                d_decls = scan_lean_declarations(d_code)
                crate, item = _dogfood_crate_item(rel)
                verified_decls = [d for d in d_decls if d.kind == "theorem" and d.written_name == "verified"]
                if not verified_decls:
                    res.errors.append(f"{rel}: missing `theorem verified`")
                elif len(verified_decls) > 1:
                    res.errors.append(f"{rel}: multiple `theorem verified` declarations ({len(verified_decls)})")
                expected_verified_qname = f"Proof.{crate}.{item}.verified"
                for d in verified_decls:
                    if d.qualified_name != expected_verified_qname:
                        res.errors.append(
                            f"{rel}: `theorem verified` must be declared in `namespace Proof.{crate}.{item}` "
                            f"(found `{d.qualified_name}`)"
                        )
                    # The `verified` statement must stay exactly the generated obligation claim type
                    # (statement-origin isolation: no `Anneal.*` symbol may appear in it).
                    header = " ".join("\n".join(d_lines[d.start_line : d.end_line]).split(":=", 1)[0].split())
                    if not _verified_signature_ok(header, crate, item):
                        res.errors.append(
                            f"{rel}: `theorem verified` must state `<VerificationResult kind> "
                            f"Obligations.{crate}.{item}.<claim>` with no other symbol (found `{header}`)"
                        )
                companions: list[str] = []
                connected: list[str] = []
                nontrivial_ops: list[str] = []
                connect_re = re.compile(
                    r"\bMir\." + re.escape(crate) + r"\." + re.escape(item) + r"\b|\bverified\b"
                    r"|\bSpecs\." + re.escape(crate) + r"\." + re.escape(item) + r"\b"
                )
                lens_op_re = re.compile(
                    r"\b(?:splitAt|of_splitAt|DisjointSlice|takeElems|dropElems|elemOffset|elemPtr"
                    r"|evalSliceFatPtrDerefBorrow)\b"
                )
                for d in d_decls:
                    if d.kind != "theorem" or d.written_name == "verified":
                        continue
                    span_lines = list(d_lines[d.start_line : d.end_line])
                    if span_lines:
                        m_decl = _DECL_RE.match(span_lines[0])
                        if m_decl and m_decl.group("name"):
                            s_i, e_i = m_decl.span("name")
                            span_lines[0] = span_lines[0][:s_i] + (" " * (e_i - s_i)) + span_lines[0][e_i:]
                    body = "\n".join(span_lines)
                    if lens_re.search(body) and wide_re.search(body):
                        companions.append(d.written_name)
                        if connect_re.search(body):
                            connected.append(d.written_name)
                            if lens_op_re.search(body):
                                nontrivial_ops.append(d.written_name)
                if not companions:
                    res.errors.append(
                        f"{rel}: no companion theorem referencing `WidePtrVal` and one of {list(REQUIRED_LENS_DEFINITIONS)}"
                    )
                elif not connected:
                    res.errors.append(
                        f"{rel}: no slice-lens companion theorem is connected to the verified function "
                        f"(it must mention `Mir.{crate}.{item}`, `Specs.{crate}.{item}`, or `verified`)"
                    )
                elif not nontrivial_ops:
                    res.errors.append(
                        f"{rel}: connected slice-lens companion theorem does not use any slice window/split/disjointness "
                        "operation (`splitAt`, `of_splitAt`, `DisjointSlice`, `takeElems`, `dropElems`, `elemOffset`, "
                        "`elemPtr`, or `evalSliceFatPtrDerefBorrow`)"
                    )
                dogfood_report[rel] = companions
        res.details = {"definitions": found_defs, "lemmas": found_lemmas, "dogfood_companions": dogfood_report}
        return res

    def check_blocker_separation(self) -> CheckResult:
        res = CheckResult(
            "d_stage_b_blocker_separation",
            "Stage-B: lifted slice ops do not block anneal_proof_lifters; unsized DSTs do",
        )
        suite = self.require_suite(res)
        if suite is None:
            return res
        lifted = str(getattr(suite, "LIFTED_SLICE_WIDE_PTR_BLOCKER", DEFAULT_LIFTED_SLICE_BLOCKER))
        unsized = str(getattr(suite, "UNSIZED_DST_BLOCKER", DEFAULT_UNSIZED_DST_BLOCKER))
        blockers = {name: set(layers) for name, _pat, layers in getattr(suite, "RUST_CONSTRUCT_BLOCKERS", [])}
        if lifted not in blockers:
            res.errors.append(f"RUST_CONSTRUCT_BLOCKERS has no lifted-slice blocker {lifted!r}")
        elif LIFTERS_LAYER in blockers[lifted]:
            res.errors.append(f"lifted-slice blocker {lifted!r} still affects {LIFTERS_LAYER}")
        if unsized not in blockers:
            res.errors.append(f"RUST_CONSTRUCT_BLOCKERS has no unsized-DST blocker {unsized!r}")
        elif LIFTERS_LAYER not in blockers[unsized]:
            res.errors.append(f"unsized-DST blocker {unsized!r} no longer affects {LIFTERS_LAYER}")
        probe_report: dict[str, Any] = {}
        with tempfile.TemporaryDirectory(prefix="mir_cov_audit_probe_") as tmp:
            for probe in STAGE_B_BLOCKER_PROBES:
                path = Path(tmp) / f"{probe.name}.rs"
                path.write_text(probe.source, encoding="utf-8")
                try:
                    out = suite.analyze_corpus_completeness(probe.name, [path])
                except Exception as exc:  # noqa: BLE001
                    res.errors.append(f"probe {probe.name}: analyze_corpus_completeness raised {exc!r}")
                    continue
                layer = out["layers"][LIFTERS_LAYER]
                lifter_blockers = sorted(b["construct"] for b in out["top_marginal_unlock_blockers"])
                blocked = layer["fully_verifiable_fns"] == 0
                probe_report[probe.name] = {
                    "total_fns": out["total_fns"],
                    "lifters_blocked": blocked,
                    "lifter_blockers": lifter_blockers,
                    "fully_verifiable_by_layer": {k: v["fully_verifiable_fns"] for k, v in out["layers"].items()},
                }
                if out["total_fns"] != 1:
                    res.errors.append(f"probe {probe.name}: expected exactly 1 function, scanned {out['total_fns']}")
                    continue
                if lifted in lifter_blockers:
                    res.errors.append(f"probe {probe.name}: lifted-slice blocker attributed on {LIFTERS_LAYER}")
                if probe.lifters_blocked and (not blocked or unsized not in lifter_blockers):
                    res.errors.append(
                        f"probe {probe.name}: expected {unsized!r} to block {LIFTERS_LAYER}, got blockers {lifter_blockers}"
                    )
                if not probe.lifters_blocked and blocked:
                    res.errors.append(
                        f"probe {probe.name}: lifted slice operations block {LIFTERS_LAYER} via {lifter_blockers}"
                    )
        res.details = {
            "lifted_blocker": {"name": lifted, "layers": sorted(blockers.get(lifted, set()))},
            "unsized_blocker": {"name": unsized, "layers": sorted(blockers.get(unsized, set()))},
            "probes": probe_report,
        }
        return res

    # -- (e) ----------------------------------------------------------------

    def _pins(self, res: CheckResult) -> tuple[dict[str, str], dict[str, str], str | None]:
        lean_miri: dict[str, str] = {}
        minirust: dict[str, str] = {}
        commit: str | None = None
        try:
            pin = json.loads((self.root / LEAN_MIRI_PIN).read_text(encoding="utf-8"))
            tree = pin["vendor_tree"]
            files = list(tree["files"])
            lean_miri = {str(f["path"]): str(f["sha256"]) for f in files}
            manifest = "".join(f"{f['sha256']}  {f['path']}\n" for f in files)
            if hashlib.sha256(manifest.encode("utf-8")).hexdigest() != tree.get("manifest_sha256"):
                res.errors.append(f"{LEAN_MIRI_PIN}: vendor_tree.manifest_sha256 does not match vendor_tree.files")
            if tree.get("file_count") != len(files):
                res.errors.append(f"{LEAN_MIRI_PIN}: vendor_tree.file_count != len(vendor_tree.files)")
        except (OSError, ValueError, KeyError, TypeError) as exc:
            res.errors.append(f"cannot read pins from {LEAN_MIRI_PIN}: {exc!r}")
        try:
            lock = tomllib.loads((self.root / MINIRUST_LOCK).read_text(encoding="utf-8"))
            commit = str(lock["upstream"]["commit"])
            minirust = {str(k): str(v) for k, v in lock["files"].items()}
        except (OSError, ValueError, KeyError, TypeError) as exc:
            res.errors.append(f"cannot read pins from {MINIRUST_LOCK}: {exc!r}")
        return lean_miri, minirust, commit

    def _verify_anchor(
        self,
        rel: str,
        snippet: str,
        pins: tuple[dict[str, str], dict[str, str], str | None],
        file_cache: dict[str, tuple[set[str], str] | None],
    ) -> list[str]:
        lean_miri, minirust, commit = pins
        parts = rel.split("/")
        if rel.startswith("/") or ".." in parts or "" in parts:
            return [f"{rel}: anchor path must be a normalized relative path"]
        if rel.startswith(LEAN_MIRI_VENDOR):
            key, expected = rel[len(LEAN_MIRI_VENDOR) :], lean_miri.get(rel[len(LEAN_MIRI_VENDOR) :])
            pin_src = f"{LEAN_MIRI_PIN} vendor_tree.files"
        elif rel.startswith(MINIRUST_VENDOR):
            prefix = f"{MINIRUST_VENDOR}{commit}/"
            if commit is None or not rel.startswith(prefix):
                return [f"{rel}: not under the pinned MiniRust snapshot {prefix}"]
            key, expected = rel[len(prefix) :], minirust.get(rel[len(prefix) :])
            pin_src = f"{MINIRUST_LOCK} [files]"
        else:
            return [f"{rel}: anchors must point into {LEAN_MIRI_VENDOR} or {MINIRUST_VENDOR}<commit>/"]
        if rel not in file_cache:
            try:
                data = (self.root / rel).read_bytes()
                file_cache[rel] = (
                    {ln.strip() for ln in data.decode("utf-8").splitlines()},
                    hashlib.sha256(data).hexdigest(),
                )
            except (OSError, UnicodeDecodeError):
                file_cache[rel] = None
        cached = file_cache[rel]
        if cached is None:
            return [f"{rel}: vendored file missing or unreadable"]
        lines, digest = cached
        errors: list[str] = []
        if expected is None:
            errors.append(f"{rel}: `{key}` is not pinned in {pin_src}")
        elif digest != expected:
            errors.append(f"{rel}: sha256 {digest} != pinned {expected} ({pin_src})")
        if snippet.strip() not in lines:
            errors.append(f"{rel}: anchor snippet not found as a line: {snippet.strip()!r}")
        return errors

    def check_vendored_anchors(self) -> CheckResult:
        res = CheckResult("e_vendored_source_anchors", "REQUIRED_SOURCE_ANCHORS present in sha256-pinned vendored files")
        pins = self._pins(res)
        cache: dict[str, tuple[set[str], str] | None] = {}
        for rel, snippet in REQUIRED_SOURCE_ANCHORS:
            res.errors.extend(self._verify_anchor(rel, snippet, pins, cache))
        res.details = {
            "required_anchors": len(REQUIRED_SOURCE_ANCHORS),
            "files": sorted(cache),
            "minirust_commit": pins[2],
        }
        return res

    def check_anchor_quotes(self) -> CheckResult:
        res = CheckResult("e_source_anchor_quotes", f"{UNTESTED_VARIANT_TEST} quotes every required source anchor")
        text = _read_text(self.root / UNTESTED_VARIANT_TEST)
        if text is None:
            res.errors.append(f"{UNTESTED_VARIANT_TEST}: missing or unreadable")
            return res
        pins = self._pins(res)
        cache: dict[str, tuple[set[str], str] | None] = {}
        quoted: list[tuple[str, str]] = []
        for lineno, line in enumerate(text.splitlines(), start=1):
            if not _ANCHOR_CANDIDATE_RE.match(line):
                continue
            m = _ANCHOR_LINE_RE.match(line)
            if not m:
                res.errors.append(f"{UNTESTED_VARIANT_TEST}:{lineno}: malformed @source-anchor line")
                continue
            rel, snippet = m.group("rel"), m.group("snippet").strip()
            quoted.append((rel, snippet))
            for err in self._verify_anchor(rel, snippet, pins, cache):
                res.errors.append(f"{UNTESTED_VARIANT_TEST}:{lineno}: {err}")
        quoted_set = set(quoted)
        for rel, snippet in REQUIRED_SOURCE_ANCHORS:
            if (rel, snippet.strip()) not in quoted_set:
                res.errors.append(f"{UNTESTED_VARIANT_TEST}: required anchor not quoted: -- @source-anchor {rel}#{snippet}")
        res.details = {"quoted_anchors": len(quoted), "distinct_quoted_anchors": len(quoted_set)}
        return res


class _VariantMentions:
    """Transitive "declaration references the variant" relation within one file: a declaration
    references it if its own code (excluding a theorem/lemma's own declaration name, so a tautology
    named `tailCall_vacuous : 1 = 1 := rfl` cannot self-match) matches the variant pattern or it
    uses (by written, short or qualified name) a declaration of the same file that does."""

    def __init__(self, decls: list[LeanDecl], code_lines: list[str]) -> None:
        self.decls = decls
        self.index = {id(d): idx for idx, d in enumerate(decls)}
        self.text: list[str] = []
        for d in decls:
            span_lines = list(code_lines[d.start_line : d.end_line])
            if span_lines and d.kind in ("theorem", "lemma"):
                m_decl = _DECL_RE.match(span_lines[0])
                if m_decl and m_decl.group("name"):
                    s, e = m_decl.span("name")
                    span_lines[0] = span_lines[0][:s] + (" " * (e - s)) + span_lines[0][e:]
            self.text.append("\n".join(span_lines))
        self.by_name: dict[str, list[int]] = {}
        for idx, d in enumerate(decls):
            for key in {d.written_name, d.written_name.rsplit(".", 1)[-1], d.qualified_name}:
                self.by_name.setdefault(key, []).append(idx)
        self._refs_cache: dict[int, set[int]] = {}

    def _refs(self, idx: int) -> set[int]:
        if idx not in self._refs_cache:
            out: set[int] = set()
            for tok in _IDENT_TOKEN_RE.findall(self.text[idx]):
                tok = _unguillemet(tok)
                for key in (tok, tok.rsplit(".", 1)[-1]):
                    out.update(self.by_name.get(key, ()))
            out.discard(idx)
            self._refs_cache[idx] = out
        return self._refs_cache[idx]

    def references(self, decl: LeanDecl, pattern: re.Pattern[str]) -> bool:
        seen: set[int] = set()
        stack = [self.index[id(decl)]]
        while stack:
            idx = stack.pop()
            if idx in seen:
                continue
            seen.add(idx)
            if pattern.search(self.text[idx]):
                return True
            stack.extend(self._refs(idx) - seen)
        return False


CHECK_ORDER: tuple[str, ...] = (
    "a_mir_ast_constructors",
    "a_surface_totals",
    "b_untested_variants_zero",
    "c_variant_manifest",
    "c_correspondence_test_hygiene",
    "c_slice_lens_test_hygiene",
    "d_slice_lens_declarations",
    "d_stage_b_blocker_separation",
    "e_vendored_source_anchors",
    "e_source_anchor_quotes",
)


def run_audit(repo_root: Path) -> dict[str, Any]:
    """Run every check against `repo_root` and return the JSON report."""
    audit = _Audit(repo_root)
    runners: dict[str, Callable[[], CheckResult]] = {
        "a_mir_ast_constructors": audit.check_mir_ast_constructors,
        "a_surface_totals": audit.check_surface_totals,
        "b_untested_variants_zero": audit.check_untested_zero,
        "c_variant_manifest": audit.check_variant_manifest,
        "c_correspondence_test_hygiene": audit.check_correspondence_hygiene,
        "c_slice_lens_test_hygiene": audit.check_slice_lens_hygiene,
        "d_slice_lens_declarations": audit.check_slice_lens_declarations,
        "d_stage_b_blocker_separation": audit.check_blocker_separation,
        "e_vendored_source_anchors": audit.check_vendored_anchors,
        "e_source_anchor_quotes": audit.check_anchor_quotes,
    }
    checks: dict[str, Any] = {}
    for check_id in CHECK_ORDER:
        try:
            result = runners[check_id]()
        except Exception as exc:  # noqa: BLE001 - a crashing check fails closed
            result = CheckResult(check_id, check_id, [f"internal error: {type(exc).__name__}: {exc}"])
        checks[check_id] = result.to_json()
    failed = [cid for cid in CHECK_ORDER if not checks[cid]["ok"]]
    return {
        "schema_version": SCHEMA_VERSION,
        "tool": "audit_mir_coverage_matrix",
        "repo_root": str(repo_root),
        "ok": not failed,
        "failed_checks": failed,
        "checks": checks,
        "surface": checks["a_surface_totals"]["details"],
    }


def render_text(report: dict[str, Any]) -> str:
    lines = [f"MIR coverage matrix audit ({report['repo_root']})"]
    for check_id in CHECK_ORDER:
        check = report["checks"][check_id]
        lines.append(f"[{'PASS' if check['ok'] else 'FAIL'}] {check_id}: {check['title']}")
        lines.extend(f"    - {err}" for err in check["errors"])
    surface = report.get("surface") or {}
    if "combined_surface_total" in surface:
        lines.append(
            "Surface: "
            f"{surface['trusted_mir_ast_constructors']} Trusted.MirAst constructors + "
            f"{surface['stage1_lintrinsic_op_variants']} Stage-1 LIntrinsicOp + "
            f"{surface['minirust_spec_items_total']} MiniRust spec items + "
            f"{surface['lean_miri_vendored_files']} LeanMiri vendored files = "
            f"{surface['combined_surface_total']} (floor {surface['combined_surface_floor']})"
        )
    lines.append(
        "OK: all checks passed" if report["ok"] else f"FAILED: {', '.join(report['failed_checks'])}"
    )
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--check", action="store_true", help="Exit 1 if any check fails.")
    parser.add_argument("--json", action="store_true", help="Print the machine-readable report on stdout.")
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=DEFAULT_REPO_ROOT,
        help="Anneal repository root (default: the parent of scripts/).",
    )
    args = parser.parse_args(argv)
    report = run_audit(args.repo_root.resolve())
    if args.json:
        sys.stdout.write(json.dumps(report, indent=2, sort_keys=True) + "\n")
    else:
        sys.stdout.write(render_text(report))
    if args.check and not report["ok"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
