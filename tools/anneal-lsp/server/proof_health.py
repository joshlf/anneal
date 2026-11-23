#!/usr/bin/env python3
"""Fast (<5 ms) structural proof-health linter and transcript latency telemetry for Anneal Lean 4 proofs.

Detects five structural kernel-scaling anti-patterns on Lean 4 files. Comments, nested
block comments (`/- ... -/`), docstrings and string literals are blanked first, so
mentions inside them never count:
1. `dsimp_forbidden_sym`: `wpMirExecSym` or `Trusted.Sequence.length` / `Sequence.length`
   (optionally namespace-qualified or as `.eq_def`) inside the lemma list of a
   simp-family tactic (`dsimp`, `simp`, `simp only`, `simp?`, `simpa`, `simp_all`, ...,
   with or without `(config := ...)` / `+opt` arguments). Purely syntactic: no
   location- or neighbour-based exemptions. Only entries that do not unfold the
   symbol are skipped: erasures `-name`, reverse rewrites `← name`, and arguments
   to other terms (`[h (Sequence.length xs)]`).
2. `dsimp_mir_body_unfold`: `Mir.<...>.body` unfolded inside such a list or `unfold`.
3. `raw_bitwise_unfold`: raw recursive `bitwiseAndBits` or `bitwiseOrBits` unfolded inside
   such a list or `unfold` (excluding `*Fast` wrappers and closed-form mask lemmas).
4. `low_profiler_threshold`: `set_option trace.profiler.threshold <N>` with `<N> < 50`.
5. `duplicate_private_lemma`: `private theorem` / `private lemma` / `private def`
   declarations repeating a name, or repeating a normalized statement (theorems) or
   statement and body (definitions), within the file or in sibling `.lean` files of
   the same directory.

Two further rules come from the shared waiver-pin & 3-axis auditor (the section between
the `BEGIN/END SHARED WAIVER-PIN & 3-AXIS AUDITOR` banners, byte-identical in
`trusted/audit/check_trusted.py`); the finding's `subrule` names the precise hazard:
6. `unpinned_or_drifted_waiver` (always on, Lean and Rust): an `S0`-`S3` waiver directive
   (`anneal:trusted reason = "..."`, `anneal:allow_compile_time_guard`,
   `anneal:documented_intent <rationale>`, `anneal:pinned_compiler_coupled <reason>`, the
   exact `trusted/rustc-capture/src/spec.rs` grammar) without a standalone
   `pin:sha256:<12hex>` doc line (`unpinned_waiver`), with a malformed pin
   (`malformed_waiver_pin`), with a pin whose pre-image (canonical directives + normalized
   item) no longer matches (`drifted_waiver_pin`), attached to nothing (`dangling_waiver`),
   or not auditable (`invalid_waiver_syntax`). `--compute-pins` prints the expected pins.
7. `trivial_or_vacuous_claim` (Lean): syntactically contradictory hypotheses on any
   theorem (`h : False`, `0 = 1`, `5 < 3`, `x < x`, `n < 0` on `Nat`, disjoint
   constructors), plus, on theorems carrying 3-axis metadata (`Kind:` / `Witness:` /
   `Assumes:` / `Subject:`) or an `anneal:` waiver docstring and on `Proof/` claim theorems
   (`verified`, `prove_*`), invalid or conflicting metadata, `S0` padding-pin tier
   mismatches, witness-shape mismatches, trivial conclusions, tautological implications and
   unused subjects. `include_unannotated_vacuity=True` (`--all-theorems`) applies every
   check to every theorem.

Two advisory rules (`ADVISORY_RULES`) are opt-in (`include_advisories=True`, CLI
`--advisories`) and never part of `ALL_RULES` or of a default scan; they point at proof-scaling
traps that are legal Lean and that `scan_projection_and_rewrite_order_hazards` finds
structurally:
A1. `simp_deep_projection_chain`: an uncollapsed `(advanceStmt ...).memory.<field>` /
    `.frame.<field>` projection chain handed to a `simp`-family tactic other than `dsimp`,
    either inside the call (lemma list, configuration, discharger, `simpa ... using`) or by a
    `change` / `show` / `have` / `suffices` that the very next tactic step simplifies
    (`leanprover/lean4#16532`: `Simp.simpProj` builds a `fun s => e = s.i` motive per level).
A2. `try_rw_hyp_before_target`: `try rw [...] at h ⊢` (also `erw` / `rewrite` / `rwa`) naming a
    hypothesis before the goal, so a goal rewrite that fails throws away the hypothesis work.

Comment, string and identifier lexing is shared with the other Lean tools through
`lean_lexer.py` (next to this file); the shared auditor section keeps its own copy of the
lexer because the TCB checker must stay a single file.

Also provides delta-only post-edit checking (`check_post_edit_proof_health`) for
`tools/anneal-lsp/hooks/post_tool_use.py`, unbatched tool-call latency telemetry
(`compute_unbatched_tool_latencies`), and a CLI (`python3 proof_health.py --help`).

Performance: `scan_lean_text` memoizes whole-file results by exact content (plus sibling
declaration-list identity), and in a long-lived process re-scans a localized edit of a large
file (>= 32 KiB) by splicing: only a window of whole column-0 theorems around the edit is
re-scanned, guarded by a neutral-lexer-state sentinel and exact outer-ring code equality, and
anything else falls back to a full scan (`INCREMENTAL_SPLICING`; the TCB checker disables it).
Seeded property tests check spliced results against cold full scans.
"""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

from datetime import datetime
import json
import math
import os
from pathlib import Path
import re
import time
from typing import Any, Iterable
import zlib

# The shared Lean 4 lexer lives next to this file. Hooks, tests and other tools may load
# this module by file path or from any working directory, so make sure the sibling module
# is importable (without disturbing an already imported one) before importing it.
if "lean_lexer" not in sys.modules:
    _SERVER_DIR = str(Path(__file__).resolve().parent)
    if _SERVER_DIR not in sys.path:
        sys.path.insert(0, _SERVER_DIR)
import lean_lexer  # noqa: E402

RULE_DSIMP_FORBIDDEN_SYM = "dsimp_forbidden_sym"
RULE_DSIMP_MIR_BODY_UNFOLD = "dsimp_mir_body_unfold"
RULE_RAW_BITWISE_UNFOLD = "raw_bitwise_unfold"
RULE_LOW_PROFILER_THRESHOLD = "low_profiler_threshold"
RULE_DUPLICATE_PRIVATE_LEMMA = "duplicate_private_lemma"
RULE_UNPINNED_OR_DRIFTED_WAIVER = "unpinned_or_drifted_waiver"
RULE_TRIVIAL_OR_VACUOUS_CLAIM = "trivial_or_vacuous_claim"

ALL_RULES: tuple[str, ...] = (
    RULE_DSIMP_FORBIDDEN_SYM,
    RULE_DSIMP_MIR_BODY_UNFOLD,
    RULE_RAW_BITWISE_UNFOLD,
    RULE_LOW_PROFILER_THRESHOLD,
    RULE_DUPLICATE_PRIVATE_LEMMA,
    RULE_UNPINNED_OR_DRIFTED_WAIVER,
    RULE_TRIVIAL_OR_VACUOUS_CLAIM,
)

# Advisory rules: reported only on request (`include_advisories=True` / `--advisories`),
# never blocking and never part of `ALL_RULES`.
RULE_SIMP_DEEP_PROJECTION_CHAIN = "simp_deep_projection_chain"
RULE_TRY_RW_HYP_BEFORE_TARGET = "try_rw_hyp_before_target"

ADVISORY_RULES: tuple[str, ...] = (
    RULE_SIMP_DEEP_PROJECTION_CHAIN,
    RULE_TRY_RW_HYP_BEFORE_TARGET,
)

# Sub-rules of `simp_deep_projection_chain` (the finding's `subrule`).
SUBRULE_PROJECTION_IN_SIMP_ARGS = "projection_in_simp_arguments"
SUBRULE_SIMP_AFTER_PROJECTION_STATEMENT = "simp_after_projection_statement"

MIN_PROFILER_THRESHOLD = 50
DEFAULT_LONG_CALL_THRESHOLD_MS = 1000.0


class ProofHealthFinding:
    """One structural finding: rule id, 1-based source line, message, fix suggestion
    and the offending symbol. Immutable; compares and hashes by value.

    Rule 6 / rule 7 findings also carry the auditor's sub-rule (`subrule`, e.g.
    `drifted_waiver_pin` or `syntactic_contradiction_hypothesis`) and, for waivers, the
    `expected_pin` / `actual_pin` / `tier`; these keyword-only attributes default to `""`,
    so `ProofHealthFinding(rule, line, message, suggestion, symbol)` keeps its positional
    form and value equality for rules 1-5.

    A plain `__slots__` class rather than a dataclass: importing `dataclasses` costs
    about 10 ms, which every hook process would pay since no bytecode is cached.
    """

    __slots__ = (
        "rule",
        "line",
        "message",
        "suggestion",
        "symbol",
        "subrule",
        "expected_pin",
        "actual_pin",
        "tier",
    )

    def __init__(
        self,
        rule: str,
        line: int,
        message: str,
        suggestion: str,
        symbol: str = "",
        *,
        subrule: str = "",
        expected_pin: str = "",
        actual_pin: str = "",
        tier: str = "",
    ) -> None:
        set_attr = object.__setattr__
        set_attr(self, "rule", rule)
        set_attr(self, "line", line)
        set_attr(self, "message", message)
        set_attr(self, "suggestion", suggestion)
        set_attr(self, "symbol", symbol)
        set_attr(self, "subrule", subrule)
        set_attr(self, "expected_pin", expected_pin)
        set_attr(self, "actual_pin", actual_pin)
        set_attr(self, "tier", tier)

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError("ProofHealthFinding is immutable")

    def _key(self) -> tuple[str, int, str, str, str, str, str, str, str]:
        return (
            self.rule,
            self.line,
            self.message,
            self.suggestion,
            self.symbol,
            self.subrule,
            self.expected_pin,
            self.actual_pin,
            self.tier,
        )

    def __eq__(self, other: object) -> bool:
        if other.__class__ is not ProofHealthFinding:
            return NotImplemented
        return self._key() == other._key()  # type: ignore[attr-defined]

    def __hash__(self) -> int:
        return hash(self._key())

    def __repr__(self) -> str:
        base = "rule=%r, line=%r, message=%r, suggestion=%r, symbol=%r" % self._key()[:5]
        extras = "".join(
            f", {name}={value!r}"
            for name, value in (
                ("subrule", self.subrule),
                ("expected_pin", self.expected_pin),
                ("actual_pin", self.actual_pin),
                ("tier", self.tier),
            )
            if value
        )
        return f"ProofHealthFinding({base}{extras})"

    def to_dict(self) -> dict[str, Any]:
        out: dict[str, Any] = {
            "rule": self.rule,
            "line": self.line,
            "message": self.message,
            "suggestion": self.suggestion,
            "symbol": self.symbol,
        }
        for name in ("subrule", "expected_pin", "actual_pin", "tier"):
            value = getattr(self, name)
            if value:
                out[name] = value
        return out


class PrivateDecl:
    """A `private theorem` / `private lemma` / `private def` declaration.

    `norm_sig` is the normalized header (computed lazily from `raw_header`), `sig_fp`
    a cheap structural fingerprint of the header, `body_start` the offset of the
    definition body in the comment-stripped text of the declaring file (-1 when
    unknown) and `path` that file's path (empty for the scanned text itself).
    """

    __slots__ = (
        "kind",
        "name",
        "norm_sig",
        "_line",
        "_pos",
        "_line_of",
        "file",
        "raw_header",
        "sig_fp",
        "body_start",
        "decl_indent",
        "path",
        "_rename_map",
        "body_keys",
    )

    def __init__(
        self,
        kind: str,
        name: str,
        norm_sig: str,
        line: int,
        file: str,
        raw_header: str = "",
        sig_fp: tuple[int, int, int, int] = (0, 0, 0, 0),
        body_start: int = -1,
        path: str = "",
        decl_indent: int = 0,
        pos: int = -1,
        line_of: Any = None,
    ) -> None:
        self.kind = kind
        self.name = name
        self.norm_sig = norm_sig
        self._line = line
        self._pos = pos
        self._line_of = line_of
        self.file = file
        self.raw_header = raw_header
        self.sig_fp = sig_fp
        self.body_start = body_start
        self.decl_indent = decl_indent
        self.path = path
        self._rename_map: dict[str, str] | None = None
        # `(key1, key2)` of a sibling definition's body (`_body_key1` / `_body_key2`),
        # computed when the sibling is lexed and persisted in the sibling index, so a
        # later process can compare bodies without re-reading the sibling.
        self.body_keys: tuple[Any, Any] | None = None

    @property
    def line(self) -> int:
        if self._line <= 0 and self._pos >= 0 and self._line_of is not None:
            self._line = int(self._line_of(self._pos))
            self._line_of = None
        return self._line

    @line.setter
    def line(self, value: int) -> None:
        self._line = value
        self._line_of = None

    def ensure_norm_sig(self) -> str:
        if not self.norm_sig and self.raw_header:
            self.norm_sig, self._rename_map = _normalize_signature_with_map(self.raw_header)
        return self.norm_sig

    def ensure_rename_map(self) -> dict[str, str]:
        if self._rename_map is None:
            if self.raw_header:
                ns, rmap = _normalize_signature_with_map(self.raw_header)
                if not self.norm_sig:
                    self.norm_sig = ns
                self._rename_map = rmap
            else:
                self._rename_map = {}
        return self._rename_map

    def __repr__(self) -> str:
        return (
            f"PrivateDecl(kind={self.kind!r}, name={self.name!r}, line={self.line!r}, "
            f"file={self.file!r})"
        )


# Lexical helpers. The implementations live in the shared single-pass lexer
# (`lean_lexer.py`); the names below are kept because the rules in this module, the
# PostToolUse hook and the tests use them.

# Lean 4 identifier continuation characters (`isIdRest`): letters (including Unicode
# letters and subscripts), digits, `_`, `'`, `!` and `?` (`get?`, `get!`).
_is_ident_char = lean_lexer.is_ident_char

# Byte table mapping every byte except `\n` to a space.
_BLANK_BYTES_TABLE = lean_lexer._BLANK_BYTES_TABLE

# `seg` with every character except newlines replaced by a space.
_blank = lean_lexer.blank_preserving_newlines
_blank_multiline = lean_lexer.blank_preserving_newlines


def strip_lean_comments_and_strings(text: str, *, keep_strings: bool = False) -> str:
    """Blank out Lean 4 `--` line comments, nested `/- ... -/` block comments
    (docstrings included) and string literals, character for character: the result
    has the same length as `text` and keeps every `\\n`, so offsets and line
    numbers in it are exactly those of `text`.

    String literals honour `\\"` / `\\\\` escapes; raw strings `r"..."` / `r#"..."#`
    end at the matching `"#...`; the quote character literals `'"'` / `'\\"'` do not
    open a string, while an identifier prime before a string (`x'"..."`) does not
    make a character literal; guillemet names `«a--b»` are code, not comments. With
    `keep_strings=True` only comments are blanked.

    Delegates to `lean_lexer.strip_comments_and_strings_preserving_offsets` (about 3 ms
    per MB of Lean source), which blanks exactly the characters that the shared auditor's
    lexer `_scan_lean_comments_and_strings` blanks.
    """
    return lean_lexer.strip_comments_and_strings_preserving_offsets(
        text, keep_strings=keep_strings
    )


# 1-based line of an offset, from the text or from the sorted offsets of its newlines.
_offset_to_line = lean_lexer.offset_to_line

# 1-based line numbers of offsets in a text, counted incrementally from the previous
# query, so a scan's queries cost O(len(text)) in total instead of one prefix count per
# finding.
_LineCounter = lean_lexer.LineCounter


# Tactic and pattern regexes on stripped Lean 4 text.
# Leading literal prefixes (`simp`, `unfold`, `delta`, `set_option`, `private`)
# let CPython's `sre` skip ahead with a literal search instead of trying every offset.
# Cold-path regexes are compiled lazily on first use to keep fresh hook imports fast.
#
# Tactic suffix after `simp` (`dsimp` never accepts `a` / `_all` / `_arith` / `_rw`).
_SIMP_VARIANT_TUPLE: tuple[str, ...] = ("_all_arith", "_all", "_arith", "_rw", "a")
# Identifier boundaries follow Lean 4 (`\w` is Unicode-aware; `'`, `!`, `?` continue
# an identifier; a `.` before or after means the match is only part of a longer name).
_IDENT_BEFORE = r"(?<![\w'!?.])"
_IDENT_AFTER = r"(?![\w'!?.])"
# Optional namespace qualification (`Trusted.Sequence.length`,
# `Anneal.Rustc.V2026_06_01.wpMirExecSym`, including guillemet-escaped Rust segments
# like `Mir.Crate.«match».body`) and optional unfolding-equation suffixes
# (`.eq_def`, `.eq_unfold`, `.eq_<n>`) are part of the flagged symbol; any other
# `.`-suffix (a lemma living in the symbol's namespace) is not.
_IDENT_PART = r"(?:[^\W\d][\w'!?]*|«[^»\n]+»)"
_QUAL_PREFIX = r"(?:" + _IDENT_PART + r"\.)*"
_UNFOLD_EQ_SUFFIX = r"(?:\.(?:eq_def|eq_unfold|eq_\d+))?"
_FORBIDDEN_SIMP_SYM_RE = re.compile(
    _IDENT_BEFORE
    + r"("
    + _QUAL_PREFIX
    + r"(?:wpMirExecSym|Sequence\.length))"
    + _UNFOLD_EQ_SUFFIX
    + _IDENT_AFTER
)
_MIR_BODY_RE = re.compile(
    _IDENT_BEFORE
    + r"("
    + _QUAL_PREFIX
    + r"Mir(?:\.(?:[\w'!?]+|«[^»\n]+»))+\.body)"
    + _UNFOLD_EQ_SUFFIX
    + _IDENT_AFTER
)
_RAW_BITWISE_RE = re.compile(
    _IDENT_BEFORE + _QUAL_PREFIX + r"(bitwise(?:And|Or)Bits)" + _UNFOLD_EQ_SUFFIX + _IDENT_AFTER
)
_EQ_SUFFIX_AT_RE = re.compile(r"\.(?:eq_def|eq_unfold|eq_\d+)(?![\w'!?.])")
# The value is a Lean `numLit`: decimal, or `0x`/`0b`/`0o` prefixed.
_PROFILER_THRESHOLD_RE = re.compile(
    r"set_option\s+trace\.profiler\.threshold\s+"
    r"(0[xX][0-9a-fA-F]+(?:_[0-9a-fA-F]+)*|0[bB][01]+(?:_[01]+)*|0[oO][0-7]+(?:_[01234567]+)*"
    r"|\d+(?:_\d+)*)(?![\w'!?.])"
)
# Declaration names: dotted Lean 4 identifiers (`MirStepStar.mono`, `get?_set?_ne`,
# `Foo.«bar»`, `«guillemet-quoted»`). Modifiers may sit between `private` and the keyword.
_DECL_NAME = _IDENT_PART + r"(?:\." + _IDENT_PART + r")*"
_PRIVATE_LIT_RE = re.compile(
    r"private\s+(?:(?:noncomputable|partial|unsafe|nonrec)\s+)*(theorem|lemma|def)\s+("
    + _DECL_NAME
    + r")"
)
# A line starting in column 0 begins a new top-level command; indented commands inside
# an indented `section` / `namespace` are recognised by `_DECL_BOUNDARY_RE`.
_TOPLEVEL_LINE_RE = re.compile(r"\n(?=\S)")
_DECL_BOUNDARY_RE = re.compile(
    r"\n(?:(?=\S)|([ \t]+)(?=@\[|"
    r"(?:private|protected|public|scoped|local|noncomputable|partial|unsafe|"
    r"theorem|lemma|def|abbrev|opaque|axiom|example|instance|class|structure|"
    r"inductive|mutual|section|namespace|end|variable|open|universe|set_option)(?![\w'!?.])|"
    r"#(?:check|eval|print|reduce)\b))"
)
_EQN_ALT_LINE_RE = re.compile(r"\n[ \t]*\|")
_MATCH_OR_FUN_RE = re.compile(r"(?<![\w'!?.])(?:match|fun|λ)(?![\w'!?])")
_HDR_TOKEN_RE = re.compile(r"«[^»\n]*»|[()\[\]{}]|:=|:|(?<![\w'!?.])where(?![\w'!?])")
_RESERVED_TYPE_NAMES = frozenset(("Type", "Prop", "Sort", "Nat", "Bool", "True", "False"))
_UNFOLD_STOP_WORDS = frozenset(
    (
        "at",
        "by",
        "with",
        "in",
        "where",
        "using",
        "fun",
        "match",
        "let",
        "have",
        "exact",
        "apply",
        "rw",
        "simp",
        "dsimp",
        "simpa",
        "simp_all",
        "simp_arith",
        "simp_all_arith",
        "simp_rw",
        "unfold",
        "delta",
        "cases",
        "induction",
        "rcases",
        "obtain",
        "intro",
        "intros",
        "refine",
        "constructor",
        "trivial",
        "rfl",
        "omega",
        "decide",
        "assumption",
        "contradiction",
        "nomatch",
        "change",
        "show",
        "suffices",
        "calc",
        "conv",
        "done",
        "sorry",
    )
)


def _has_simp_candidate(s: str) -> bool:
    return (
        ("Mir." in s and ".body" in s)
        or "Sequence.length" in s
        or "wpMirExecSym" in s
        or ("bitwise" in s and ("bitwiseAndBits" in s or "bitwiseOrBits" in s))
    )


def _is_simp_unfold_entry(content: str, start: int, end: int | None = None) -> bool:
    """True when the match `content[start:end]` stands as an unfolded `dsimp`/`simp`
    lemma-list entry (optionally `@name`, `(name)`, `(name : T)`, `↓ name`, or
    `name.eq_def ...`), rather than an erasure `-name`, a reverse rewrite `← name` /
    `<- name`, a tuple `(name, other)`, an indexed/projected term `Mir.X.body[0]!` /
    `(Mir.X.body).length`, an inline proposition `(Sequence.length bs = 4)`, or an
    argument `f (Sequence.length bs)`.
    """
    j = start - 1
    open_parens = 0
    saw_dir = False
    while j >= 0:
        ch = content[j]
        if ch in " \t\r\n@":
            j -= 1
        elif ch == "(":
            open_parens += 1
            j -= 1
        elif ch in "↓↑" and not saw_dir:
            saw_dir = True
            j -= 1
        else:
            break
    if j >= 0:
        if content[j] != ",":
            return False
        if (
            content.count("(", 0, j) != content.count(")", 0, j)
            or content.count("{", 0, j) != content.count("}", 0, j)
            or content.count("[", 0, j) != content.count("]", 0, j)
        ):
            return False

    if end is None:
        return True
    is_eq_lemma = ".eq_" in content[start:end]
    n = len(content)
    k = end
    rem_parens = open_parens
    while rem_parens > 0:
        while k < n and content[k] in " \t\r\n":
            k += 1
        if k >= n:
            return False
        if content[k] == ")":
            rem_parens -= 1
            k += 1
            continue
        is_ascription = content[k] == ":" and content[k : k + 2] != ":="
        if is_ascription or is_eq_lemma:
            depth = 1
            bdepth = 0
            while k < n and depth > 0:
                c2 = content[k]
                if c2 == "(":
                    depth += 1
                elif c2 == ")":
                    depth -= 1
                elif c2 in "[{":
                    bdepth += 1
                elif c2 in "]}" and bdepth > 0:
                    bdepth -= 1
                elif not is_ascription and c2 == "," and depth == 1 and bdepth == 0:
                    return False
                k += 1
            if depth != 0:
                return False
            rem_parens -= 1
            continue
        return False

    while k < n and content[k] in " \t\r\n":
        k += 1
    if k >= n or content[k] == ",":
        return True
    return is_eq_lemma or (content[k] == ":" and content[k : k + 2] != ":=")


def _is_symbol_end(stripped: str, end: int) -> bool:
    """True unless the identifier text ending at `end` continues: with more
    identifier characters, or with a `.` component other than an unfolding-equation
    suffix (`.eq_def`, `.eq_unfold`, `.eq_<n>`)."""
    if end >= len(stripped):
        return True
    ch = stripped[end]
    if ch == ".":
        return _EQ_SUFFIX_AT_RE.match(stripped, end) is not None
    return not _is_ident_char(ch)


def _has_mir_body_ident(stripped: str, first_body: int = -1, first_mir: int = -1) -> bool:
    """Exactly `_MIR_BODY_RE.search(stripped) is not None`, without a full regex scan.

    A match never spans a newline (no identifier part does) and always contains a
    `Mir.` before its final `.body`, which ends the symbol (`_is_symbol_end`). So it
    suffices to regex-scan the lines holding such a `.body` with an earlier `Mir.`.
    Every rule-2 finding (simp entry or `unfold`/`delta` target) is a `_MIR_BODY_RE`
    match at the same offset of `stripped`, so `False` soundly skips rule 2.
    """
    p_mir = first_mir if first_mir >= 0 else stripped.find("Mir.", 0)
    if p_mir == -1:
        return False
    n = len(stripped)
    pos = first_body if first_body >= p_mir + 4 else stripped.find(".body", p_mir + 4)
    while pos != -1:
        if _is_symbol_end(stripped, pos + 5):
            line_start = stripped.rfind("\n", 0, pos) + 1
            if stripped.find("Mir.", line_start, pos) != -1:
                nl = stripped.find("\n", pos + 5)
                line_end = n if nl == -1 else nl
                if _MIR_BODY_RE.search(stripped, line_start, line_end) is not None:
                    return True
                pos = stripped.find(".body", line_end)
                continue
        pos = stripped.find(".body", pos + 5)
    return False


def _active_simp_keywords(
    stripped: str, simp_start: int = 0, check_rule1: bool = True
) -> tuple[dict[str, int], bool, bool]:
    """Map of candidate keywords to their first offset in `stripped`, plus
    `(has_mir_body, has_bitwise)`. Avoids scanning twice for the same keyword.

    The offsets anchor `_candidate_search_windows` and must stay exactly the
    unfiltered first occurrences: a window anchored at an occurrence that is not
    itself a simp entry can still be the only one reaching a long (`> 2048` char)
    simp list holding a real entry. `has_mir_body` is exact (`_has_mir_body_ident`)
    and only gates rule-2 checks; `kw_offsets` is cleared only when all three simp
    rules (1, 2, 3) are absent from `stripped`.
    """
    kw_offsets: dict[str, int] = {}
    if check_rule1:
        p = stripped.find("wpMirExecSym", simp_start)
        if p != -1:
            kw_offsets["wpMirExecSym"] = p
        p = stripped.find("Sequence.length", simp_start)
        if p != -1:
            kw_offsets["Sequence.length"] = p
    has_mir_body = False
    p_mir = stripped.find("Mir.", 0)
    if p_mir != -1:
        p_body = stripped.find(".body", 0)
        if p_body != -1:
            kw_offsets[".body"] = p_body
            has_mir_body = _has_mir_body_ident(stripped, first_body=p_body, first_mir=p_mir)
    has_bitwise = False
    p_bw = stripped.find("bitwise", 0)
    if p_bw != -1:
        p = stripped.find("bitwiseAndBits", p_bw)
        if p != -1:
            kw_offsets["bitwiseAndBits"] = p
            has_bitwise = True
        p = stripped.find("bitwiseOrBits", p_bw)
        if p != -1:
            kw_offsets["bitwiseOrBits"] = p
            has_bitwise = True
    if (
        not has_mir_body
        and not has_bitwise
        and "wpMirExecSym" not in kw_offsets
        and "Sequence.length" not in kw_offsets
    ):
        kw_offsets.clear()
    return kw_offsets, has_mir_body, has_bitwise


def _step_back_simp_header_start(stripped: str, open_bracket: int) -> int:
    """Walk backwards from `open_bracket` across `only`, `+opt`/`-opt`, and arbitrarily
    nested `(...)` config/discharger arguments to find a safe window start for `simp`."""
    cur = open_bracket
    floor = open_bracket - 2048 if open_bracket > 2048 else 0
    while cur > floor:
        while cur > floor and stripped[cur - 1] in " \t\r\n":
            cur -= 1
        if cur <= floor:
            break
        if stripped[cur - 1] == ")":
            depth = 1
            cur -= 1
            while cur > floor and depth > 0:
                ch = stripped[cur - 1]
                if ch == ")":
                    depth += 1
                elif ch == "(":
                    depth -= 1
                cur -= 1
            continue
        # Step back over an identifier/flag (`only`, `+arith`, `simp_all_arith?`)
        end_tok = cur
        while cur > floor and (
            _is_ident_char(stripped[cur - 1]) or stripped[cur - 1] in ".+-"
        ):
            cur -= 1
        if cur == end_tok:
            break
    return cur - 16 if cur > 16 else 0


def _candidate_search_windows(
    stripped: str,
    active_kws: dict[str, int] | list[str] | None = None,
    max_bracket_len: int = 2048,
) -> list[tuple[int, int]]:
    n = len(stripped)
    if n <= 8192:
        return [(0, n)]
    if active_kws is None:
        kw_offsets, _, _ = _active_simp_keywords(stripped)
    elif isinstance(active_kws, dict):
        kw_offsets = active_kws
    else:
        kw_offsets = {kw: stripped.find(kw, 0) for kw in active_kws}
        kw_offsets = {kw: p for kw, p in kw_offsets.items() if p != -1}
    if not kw_offsets:
        return []
    raw_spans: list[tuple[int, int]] = []
    for kw, first_pos in kw_offsets.items():
        klen = len(kw)
        check_before = kw[0] != "."
        pos = first_pos
        while pos != -1:
            if not _is_symbol_end(stripped, pos + klen) or (
                check_before and pos > 0 and _is_ident_char(stripped[pos - 1])
            ):
                pos = stripped.find(kw, pos + klen)
                continue
            w_start = pos - max_bracket_len if pos > max_bracket_len else 0
            last_open = stripped.rfind("[", w_start, pos)
            if last_open != -1:
                if stripped.find("]", last_open, pos) == -1:
                    hdr_start = _step_back_simp_header_start(stripped, last_open)
                    if stripped.find("simp", hdr_start, last_open) != -1:
                        raw_spans.append((hdr_start, last_open + 1))
                elif stripped.find("simp", w_start, pos) != -1 and (
                    stripped.count("[", w_start, pos) > stripped.count("]", w_start, pos)
                ):
                    raw_spans.append((w_start, pos + klen))
            pos = stripped.find(kw, pos + klen)
    if not raw_spans:
        return []
    raw_spans.sort()
    merged: list[tuple[int, int]] = [raw_spans[0]]
    for st, en in raw_spans[1:]:
        prev_st, prev_en = merged[-1]
        if st <= prev_en:
            if en > prev_en:
                merged[-1] = (prev_st, en)
        else:
            merged.append((st, en))
    return merged


def _match_simp_head(stripped: str, s_idx: int, n: int) -> tuple[str, int] | None:
    """If `stripped[s_idx:]` begins the `simp...` part of a simp-family tactic header
    followed by `[`, return `(tactic_kind, open_bracket_idx)`; otherwise `None`.
    Supports arbitrarily nested `(...)` inside `(config := ...)` / `(disch := ...)`.
    """
    is_dsimp = False
    if s_idx > 0 and stripped[s_idx - 1] == "d":
        if s_idx > 1 and (_is_ident_char(stripped[s_idx - 2]) or stripped[s_idx - 2] == "."):
            return None
        is_dsimp = True
    elif s_idx > 0 and (_is_ident_char(stripped[s_idx - 1]) or stripped[s_idx - 1] == "."):
        return None

    cur = s_idx + 4
    variant = ""
    if not is_dsimp:
        for cand in _SIMP_VARIANT_TUPLE:
            if stripped.startswith(cand, cur):
                variant = cand
                cur += len(cand)
                break
    qbang_start = cur
    while cur < n and cur - qbang_start < 2 and stripped[cur] in "!?":
        cur += 1
    if cur < n and (_is_ident_char(stripped[cur]) or stripped[cur] == "."):
        return None
    tactic_kind = ("d" if is_dsimp else "") + "simp" + variant + stripped[qbang_start:cur]

    while cur < n:
        while cur < n and stripped[cur] in " \t\r\n":
            cur += 1
        if cur >= n:
            return None
        ch = stripped[cur]
        if ch == "[":
            return tactic_kind, cur
        if ch == "(":
            depth = 1
            cur += 1
            while cur < n and depth > 0:
                c2 = stripped[cur]
                if c2 == "(":
                    depth += 1
                elif c2 == ")":
                    depth -= 1
                cur += 1
            if depth != 0:
                return None
            continue
        if stripped.startswith("only", cur) and (
            cur + 4 >= n or not (_is_ident_char(stripped[cur + 4]) or stripped[cur + 4] == ".")
        ):
            cur += 4
            continue
        if ch in "+-" and cur + 1 < n and (stripped[cur + 1].isalpha() or stripped[cur + 1] == "_"):
            cur += 2
            while cur < n and (_is_ident_char(stripped[cur]) or stripped[cur] == "."):
                cur += 1
            continue
        return None
    return None


def _iter_simp_brackets(
    stripped: str,
    active_kws: dict[str, int] | list[str] | None = None,
) -> Iterable[tuple[str, int, int, str]]:
    """Yield `(tactic_kind, open_bracket_idx, close_bracket_idx, bracket_content)` for
    every candidate simp-family lemma list (`dsimp [...]`, `simp only [...]`,
    `simp? (config := ...) [...]`, `simpa [...]`, `simp_all [...]`, ...) in `stripped`;
    `tactic_kind` is the tactic keyword as written (e.g. `dsimp`, `simp_all?`).
    """
    n = len(stripped)
    seen_open: set[int] = set()
    for win_start, win_end in _candidate_search_windows(stripped, active_kws=active_kws):
        pos = stripped.find("simp", win_start, win_end)
        while pos != -1:
            matched = _match_simp_head(stripped, pos, n)
            if matched is None:
                pos = stripped.find("simp", pos + 4, win_end)
                continue
            tactic_kind, open_idx = matched
            if open_idx in seen_open:
                pos = stripped.find("simp", pos + 4, win_end)
                continue
            seen_open.add(open_idx)

            body_start = open_idx + 1
            first_close = stripped.find("]", body_start)
            if first_close == -1:
                pos = stripped.find("simp", pos + 4, win_end)
                continue
            first_open = stripped.find("[", body_start, first_close)
            if first_open == -1:
                yield tactic_kind, open_idx, first_close, stripped[body_start:first_close]
                pos = stripped.find("simp", pos + 4, win_end)
                continue
            depth = 1
            i = body_start
            while i < n and depth > 0:
                ch = stripped[i]
                if ch == "[":
                    depth += 1
                elif ch == "]":
                    depth -= 1
                i += 1
            if depth == 0:
                close_idx = i - 1
                yield tactic_kind, open_idx, close_idx, stripped[body_start:close_idx]
            pos = stripped.find("simp", pos + 4, win_end)


def _iter_unfold_targets(stripped: str) -> Iterable[tuple[str, int, str]]:
    """Yield `(tactic_kw, token_offset, token)` for every identifier passed to an
    `unfold` or `delta` tactic, across both single-line and indented multiline target
    lists, while rejecting `.unfold`/`.delta` field projections and honoring Lean
    identifier characters (`at'`, `in?`) on stop-word checks.
    """
    n = len(stripped)
    for kw in ("unfold", "delta"):
        klen = len(kw)
        pos = stripped.find(kw, 0)
        while pos != -1:
            end_kw = pos + klen
            if (
                (pos > 0 and (_is_ident_char(stripped[pos - 1]) or stripped[pos - 1] == "."))
                or end_kw >= n
                or stripped[end_kw] not in " \t\r\n"
            ):
                pos = stripped.find(kw, end_kw)
                continue
            line_start = stripped.rfind("\n", 0, pos) + 1
            k_ind = line_start
            while k_ind < pos and stripped[k_ind] in " \t":
                k_ind += 1
            line_indent = k_ind - line_start

            cur = end_kw
            saw_target = False
            while cur < n:
                while cur < n and stripped[cur] in " \t\r":
                    cur += 1
                if cur >= n:
                    break
                if stripped[cur] == "\n":
                    nxt_line = cur + 1
                    k = nxt_line
                    while k < n and stripped[k] in " \t":
                        k += 1
                    if k >= n:
                        cur = k
                        break
                    if stripped[k] in "\r\n":
                        cur = k
                        continue
                    if k - nxt_line <= line_indent:
                        break
                    cur = k
                ch = stripped[cur]
                if not saw_target:
                    # Optional `(config := ...)` or `+opt` / `-opt` flags before targets.
                    if ch == "(":
                        depth = 1
                        cur += 1
                        while cur < n and depth > 0:
                            c2 = stripped[cur]
                            if c2 == "(":
                                depth += 1
                            elif c2 == ")":
                                depth -= 1
                            cur += 1
                        if depth != 0:
                            break
                        continue
                    if ch in "+-" and cur + 1 < n and (
                        stripped[cur + 1].isalpha() or stripped[cur + 1] == "_"
                    ):
                        cur += 2
                        while cur < n and (_is_ident_char(stripped[cur]) or stripped[cur] == "."):
                            cur += 1
                        continue
                if not (_is_ident_char(ch) or ch == "«"):
                    break
                tok_start = cur
                while cur < n:
                    c2 = stripped[cur]
                    if c2 == "«":
                        g_end = stripped.find("»", cur + 1)
                        if g_end == -1 or stripped.find("\n", cur + 1, g_end) != -1:
                            cur += 1
                            break
                        cur = g_end + 1
                    elif _is_ident_char(c2) or c2 == ".":
                        cur += 1
                    else:
                        break
                tok = stripped[tok_start:cur]
                if not tok or tok in _UNFOLD_STOP_WORDS:
                    break
                saw_target = True
                yield kw, tok_start, tok
            pos = stripped.find(kw, end_kw)


def _line_indent_at(stripped: str, pos: int) -> int:
    if pos <= 0 or stripped[pos - 1] == "\n":
        return 0
    line_start = stripped.rfind("\n", 0, pos) + 1
    k = line_start
    n = len(stripped)
    while k < n and stripped[k] in " \t":
        k += 1
    return k - line_start


def _get_decl_boundary_re() -> re.Pattern[str]:
    return _DECL_BOUNDARY_RE


def _next_decl_boundary(stripped: str, start_pos: int, max_end: int, decl_indent: int) -> int:
    """Earliest offset in `stripped[start_pos:max_end]` where a new declaration or
    section/namespace command begins: any column-0 line when `decl_indent == 0`;
    otherwise a column-0 line or a command line indented by at most `decl_indent`
    (declarations inside an indented `section` / `namespace`). One forward regex
    scan that stops at the first boundary, so the cost is the distance to it.
    """
    if decl_indent <= 0:
        m = _TOPLEVEL_LINE_RE.search(stripped, start_pos, max_end)
        return m.start() if m is not None else max_end
    for m in _DECL_BOUNDARY_RE.finditer(stripped, start_pos, max_end):
        ind = m.group(1)
        if ind is None or (len(ind) <= decl_indent and len(ind.expandtabs(2)) <= decl_indent):
            return m.start()
    return max_end


def _decl_header_span(stripped: str, start_pos: int, decl_indent: int = 0) -> tuple[str, int]:
    """Locate the header (binders and `: <type>`) of the declaration whose name ends
    at `start_pos` in comment-stripped text.

    The header ends at the top-level `:=` or `where`, or at the first
    pattern-matching equation line (`| ...` not preceded by a `match` / `fun` in the
    header, so match arms inside a statement stay part of it), and must contain a
    `:`. It never extends past the next declaration boundary (`_next_decl_boundary`)
    or 2,500 characters. Returns `(header, body_start)` with `body_start` the offset
    where the body begins, or `("", -1)` when no complete header is found.
    """
    n = len(stripped)
    max_end = min(n, start_pos + 2500)
    # Fast C `str.find(":=")` path before running regexes across all 2,500 chars:
    # check boundaries only on the short `[start_pos:first_ce]` slice when unambiguous.
    # If `cand0` contains `|`, it is only eligible for this whole-slice check when
    # `stripped[first_ce:max_end]` is also free of `«` (so the non-guillemet branch at
    # line 1091 would run anyway) and no equation-arm line precedes `first_ce` without
    # an earlier `match` / `fun`.
    first_ce = stripped.find(":=", start_pos, max_end)
    if first_ce != -1:
        cand0 = stripped[start_pos:first_ce]
        if (
            ":" in cand0
            and "let " not in cand0
            and "where" not in cand0
            and "«" not in cand0
            and cand0.count("(") == cand0.count(")")
            and cand0.count("{") == cand0.count("}")
            and cand0.count("[") == cand0.count("]")
        ):
            pipe_ok = "|" not in cand0
            if not pipe_ok and stripped.find("«", first_ce, max_end) == -1:
                m_alt = _EQN_ALT_LINE_RE.search(cand0)
                pipe_ok = (
                    m_alt is None
                    or _MATCH_OR_FUN_RE.search(cand0, 0, m_alt.start()) is not None
                )
            if pipe_ok and (
                "\n" not in cand0
                or _next_decl_boundary(stripped, start_pos, first_ce, decl_indent) == first_ce
            ):
                return cand0, first_ce + 2

    limit = _next_decl_boundary(stripped, start_pos, max_end, decl_indent)
    eqn_end = False
    if stripped.find("|", start_pos, limit) != -1:
        m_alt = _EQN_ALT_LINE_RE.search(stripped, start_pos, limit)
        if (
            m_alt is not None
            and _MATCH_OR_FUN_RE.search(stripped, start_pos, m_alt.start()) is None
        ):
            eqn_end = True
            limit = m_alt.start()
    if stripped.find("«", start_pos, limit) == -1:
        search_pos = start_pos
        while search_pos < limit:
            colon_eq = stripped.find(":=", search_pos, limit)
            if colon_eq == -1:
                break
            candidate = stripped[start_pos:colon_eq]
            if "let " in candidate or "where" in candidate:
                break
            if (
                candidate.count("(") == candidate.count(")")
                and candidate.count("{") == candidate.count("}")
                and candidate.count("[") == candidate.count("]")
            ):
                return (candidate, colon_eq + 2) if ":" in candidate else ("", -1)
            search_pos = colon_eq + 2

    # Token walk over guillemet names, brackets, `:=`, `:` and `where` only.
    depth = 0
    colon_pos = -1
    for tm in _HDR_TOKEN_RE.finditer(stripped, start_pos, limit):
        tok = tm.group()
        c = tok[0]
        if c == "«":
            continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            i = tm.start()
            if tok == ":=":
                return (stripped[start_pos:i], i + 2) if colon_pos != -1 else ("", -1)
            if tok == ":":
                if colon_pos == -1:
                    colon_pos = i
            else:  # `where`
                return (stripped[start_pos:i], i) if colon_pos != -1 else ("", -1)
    if eqn_end and colon_pos != -1:
        return stripped[start_pos:limit], limit
    return "", -1


_SIG_PAD_CHARS: tuple[tuple[str, str], ...] = (
    ("(", " ( "),
    (")", " ) "),
    ("{", " { "),
    ("}", " } "),
    ("[", " [ "),
    ("]", " ] "),
    (":", " : "),
    (",", " , "),
    ("=", " = "),
    ("+", " + "),
    ("-", " - "),
    ("*", " * "),
)

_BINDER_IDENT_RE = re.compile(r"[^\W\d][\w'!?]*|«[^»\n]+»")
_BODY_IDENT_RE = re.compile(r"[^\W\d][\w'!?]*|«[^»\n]+»")
_WS_BYTES = b" \t\n\r\x0b\x0c"
# Punctuation counted for the first cheap body comparison.
_BODY_KEY1_CHARS = ",=."
# Characters of binder-bearing body text that regex/exact comparisons may process per scan.
_BODY_COMPARE_BUDGET = 128 * 1024


def _is_valid_binder_ident(tok: str) -> bool:
    return _BINDER_IDENT_RE.fullmatch(tok) is not None


def _pad_outside_guillemets(segment: str) -> str:
    if "«" not in segment:
        padded = segment
        for ch, repl in _SIG_PAD_CHARS:
            if ch in padded:
                padded = padded.replace(ch, repl)
        return padded
    out: list[str] = []
    pos = 0
    n = len(segment)
    while pos < n:
        g = segment.find("«", pos)
        if g == -1:
            chunk = segment[pos:]
            for ch, repl in _SIG_PAD_CHARS:
                if ch in chunk:
                    chunk = chunk.replace(ch, repl)
            out.append(chunk)
            break
        if g > pos:
            chunk = segment[pos:g]
            for ch, repl in _SIG_PAD_CHARS:
                if ch in chunk:
                    chunk = chunk.replace(ch, repl)
            out.append(chunk)
        g_end = segment.find("»", g + 1)
        if g_end != -1 and segment.find("\n", g + 1, g_end) == -1:
            # Pad only `.` projections after `»`, keeping `«a-b:c»` intact as one token.
            out.append(" " + segment[g : g_end + 1])
            pos = g_end + 1
            if pos < n and segment[pos] != ".":
                out.append(" ")
        else:
            out.append("«")
            pos = g + 1
    return "".join(out)


def _apply_rename_to_code_segment(segment: str, rename_map: dict[str, str]) -> str:
    tokens = _pad_outside_guillemets(segment).split()
    if not rename_map:
        return " ".join(tokens)
    out: list[str] = []
    for tok in tokens:
        mapped = rename_map.get(tok)
        if mapped is not None:
            out.append(mapped)
        elif tok.startswith("«"):
            if "»." in tok:
                end_g = tok.index("».") + 1
                head, tail = tok[:end_g], tok[end_g:]
                out.append(rename_map.get(head, head) + tail)
            else:
                out.append(tok)
        elif "." in tok and not tok.startswith("."):
            head, dot, tail = tok.partition(".")
            out.append(rename_map.get(head, head) + dot + tail)
        else:
            out.append(tok)
    return " ".join(out)


def _body_key1(r: str, st: str, b: int, e: int) -> tuple[int, ...] | None:
    """Cheapest body key: punctuation counts on the comment/string-blanked body
    (invariant under binder renaming and layout); `None` for an empty body."""
    if b >= e:
        return None
    cand = (st.count(",", b, e), st.count("=", b, e), st.count(".", b, e))
    if cand != (0, 0, 0) or r[b:e].strip():
        return cand
    return None


def _body_key2(r: str, st: str, b: int, e: int, has_binders: bool) -> tuple[int, ...] | None:
    """Finer body key, a CRC so it can be persisted. With header binders: the
    blanked body with identifiers collapsed to `_` (rename-invariant). Without:
    the comment-stripped body with string literals (no renaming needed). Whitespace
    is dropped in both."""
    if has_binders:
        comp = (
            _BODY_IDENT_RE.sub("_", st[b:e]).encode("utf-8", "surrogatepass").translate(None, _WS_BYTES)
        )
        return (1, len(comp), zlib.crc32(comp))
    comp = _strip_comments_fast(r[b:e]).encode("utf-8", "surrogatepass").translate(None, _WS_BYTES)
    return (0, len(comp), zlib.crc32(comp)) if comp else None


def _strip_comments_fast(raw_slice: str) -> str:
    if "--" not in raw_slice and "/-" not in raw_slice:
        return raw_slice
    return strip_lean_comments_and_strings(raw_slice, keep_strings=True)


def _decl_body_key(
    raw: str,
    stripped: str,
    body_start: int,
    decl_indent: int = 0,
    rename_map: dict[str, str] | None = None,
) -> str:
    """Canonicalized definition body from `body_start` to the next command boundary:
    comments are stripped, string literals (`"..."` / `r#"..."#`) are preserved
    verbatim (including internal spaces!), punctuation/whitespace in code is normalized,
    and header binder variables are alpha-renamed via `rename_map`.
    """
    if body_start < 0 or body_start > len(stripped) or len(raw) != len(stripped):
        return ""
    end = _next_decl_boundary(stripped, body_start, len(stripped), decl_indent)
    no_comments = _strip_comments_fast(raw[body_start:end])
    rmap = rename_map or {}
    if '"' not in no_comments:
        return _apply_rename_to_code_segment(no_comments, rmap)

    parts: list[str] = []
    n = len(no_comments)
    pos = 0
    while pos < n:
        q = no_comments.find('"', pos)
        if q == -1:
            seg = _apply_rename_to_code_segment(no_comments[pos:], rmap)
            if seg:
                parts.append(seg)
            break
        h = q
        while h > pos and no_comments[h - 1] == "#":
            h -= 1
        if (
            h > pos
            and no_comments[h - 1] == "r"
            and (h - 1 == pos or not (_is_ident_char(no_comments[h - 2]) or no_comments[h - 2] == "."))
        ):
            seg = _apply_rename_to_code_segment(no_comments[pos : h - 1], rmap)
            if seg:
                parts.append(seg)
            closer = '"' + "#" * (q - h)
            c = no_comments.find(closer, q + 1)
            str_end = n if c == -1 else c + len(closer)
            parts.append(no_comments[h - 1 : str_end])
            pos = str_end
            continue
        if (
            q > pos
            and q + 1 < n
            and no_comments[q + 1] == "'"
            and (
                (no_comments[q - 1] == "'" and (q - 1 == pos or not _is_ident_char(no_comments[q - 2])))
                or (
                    q - pos >= 2
                    and no_comments[q - 2 : q] == "'\\"
                    and (q - 2 == pos or not _is_ident_char(no_comments[q - 3]))
                )
            )
        ):
            lit_open = q - (1 if no_comments[q - 1] == "'" else 2)
            seg = _apply_rename_to_code_segment(no_comments[pos:lit_open], rmap)
            if seg:
                parts.append(seg)
            parts.append(no_comments[lit_open : q + 2])
            pos = q + 2
            continue
        seg = _apply_rename_to_code_segment(no_comments[pos:q], rmap)
        if seg:
            parts.append(seg)
        cur = q + 1
        while cur < n:
            q2 = no_comments.find('"', cur)
            if q2 == -1:
                cur = n
                break
            bs = 0
            k = q2 - 1
            while k >= q + 1 and no_comments[k] == "\\":
                bs += 1
                k -= 1
            cur = q2 + 1
            if bs % 2 == 0:
                break
        parts.append(no_comments[q:cur])
        pos = cur
    return " ".join(parts)


# `_normalize_signature` is pure; memoizing it lets the before/after scans of one
# edit (and repeated scans in one process) normalize each distinct header once.
_NORM_SIG_CACHE: dict[str, tuple[str, dict[str, str]]] = {}


def _normalize_signature_with_map(raw_header: str) -> tuple[str, dict[str, str]]:
    """Return `(normalized_signature, rename_map)` for `raw_header`."""
    if not raw_header or ":" not in raw_header:
        return "", {}
    cached = _NORM_SIG_CACHE.get(raw_header)
    if cached is not None:
        return cached
    if len(_NORM_SIG_CACHE) >= 8192:
        _NORM_SIG_CACHE.clear()
    res = _normalize_signature_uncached(raw_header)
    _NORM_SIG_CACHE[raw_header] = res
    return res


def _normalize_signature(raw_header: str) -> str:
    """Normalize whitespace/punctuation and alpha-rename binder variables for duplicate detection."""
    return _normalize_signature_with_map(raw_header)[0]


_BINDER_TOKEN_RE = re.compile(r"«[^»\n]*»|[(){}\[\]]|:=|:")
_BRACKET_PAIRS = {"(": ")", "{": "}", "[": "]"}


def _normalize_signature_uncached(raw_header: str) -> tuple[str, dict[str, str]]:
    if "(" not in raw_header and "{" not in raw_header and "[" not in raw_header:
        return _apply_rename_to_code_segment(raw_header, {}), {}
    # One pass over brackets and colons: a `(...)`, `{...}` or `[...]` group whose first
    # `:` (not `:=`) at its own nesting level is preceded only by identifiers binds
    # those identifiers (`(xs : List (Nat × Nat))`, `{α : Type}`, `(«x» : Nat)`).
    groups: list[tuple[int, int]] = []
    stack: list[list[Any]] = []
    for m in _BINDER_TOKEN_RE.finditer(raw_header):
        tok = m.group()
        c = tok[0]
        if c == "«":
            continue
        if c in "({[":
            stack.append([m.start(), c, -1])
        elif c in ")}]":
            if stack and _BRACKET_PAIRS[stack[-1][1]] == c:
                open_idx, _, colon_idx = stack.pop()
                if colon_idx != -1:
                    groups.append((open_idx, colon_idx))
        elif tok == ":" and stack and stack[-1][2] == -1:
            stack[-1][2] = m.start()
    groups.sort()
    rename_map: dict[str, str] = {}
    counter = 0
    for open_idx, colon_idx in groups:
        tokens = _pad_outside_guillemets(raw_header[open_idx + 1 : colon_idx]).split()
        if tokens and all(_is_valid_binder_ident(t) for t in tokens):
            for vname in tokens:
                if vname not in rename_map and vname not in _RESERVED_TYPE_NAMES:
                    rename_map[vname] = f"_v{counter}"
                    counter += 1
    return _apply_rename_to_code_segment(raw_header, rename_map), rename_map


def _header_fingerprint(raw_header: str) -> tuple[int, int, int, int]:
    if not raw_header or ":" not in raw_header:
        return (0, 0, 0, 0)
    return (
        raw_header.count(":"),
        raw_header.count("("),
        raw_header.count("{"),
        raw_header.count("="),
    )


def extract_private_decls(
    stripped: str,
    newline_offsets: list[int] | None = None,
    file_label: str = "",
    *,
    lazy_norm: bool = False,
    file_path: str = "",
    line_of: _LineCounter | None = None,
    start_pos: int = 0,
) -> list[PrivateDecl]:
    if start_pos < 0:
        return []
    pos = stripped.find("private", start_pos)
    if pos == -1:
        return []
    decls: list[PrivateDecl] = []
    if line_of is None and newline_offsets is None:
        line_of = _LineCounter(stripped)
    defer_line = lazy_norm and newline_offsets is None and line_of is not None
    while pos != -1:
        if pos == 0 or not (_is_ident_char(stripped[pos - 1]) or stripped[pos - 1] == "."):
            m = _PRIVATE_LIT_RE.match(stripped, pos)
            if m is not None:
                kind = m.group(1)
                name = m.group(2)
                if defer_line:
                    line = 0
                elif line_of is not None:
                    line = line_of(pos)
                else:
                    line = _offset_to_line(newline_offsets, pos)
                decl_indent = _line_indent_at(stripped, pos)
                raw_header, body_start = _decl_header_span(stripped, m.end(), decl_indent)
                sig_fp = _header_fingerprint(raw_header)
                norm_sig = "" if lazy_norm else _normalize_signature(raw_header)
                decls.append(
                    PrivateDecl(
                        kind=kind,
                        name=name,
                        norm_sig=norm_sig,
                        line=line,
                        file=file_label,
                        raw_header=raw_header,
                        sig_fp=sig_fp,
                        body_start=body_start,
                        path=file_path,
                        decl_indent=decl_indent,
                        pos=pos,
                        line_of=line_of if defer_line else None,
                    )
                )
                pos = stripped.find("private", m.end())
                continue
        pos = stripped.find("private", pos + 7)
    return decls


# Cache sibling private declarations by `(resolved_path, mtime_ns, size, file_crc)`,
# directory `.lean` listings by `(parent_str, mtime_ns)` and comment-stripped sibling
# texts (only needed to compare definition bodies) so warm in-process checks take <0.05 ms.
_SIBLING_PRIVATE_CACHE: dict[str, tuple[int, int, int, list[PrivateDecl]]] = {}
_DIR_LEAN_FILES_CACHE: dict[str, tuple[int, list[Path]]] = {}
_FILE_TEXTS_CACHE: dict[str, tuple[Any, ...]] = {}
_FILE_TEXTS_CACHE_MAX = 128


def _put_file_texts_cache(key: str, val: tuple[Any, ...]) -> None:
    _FILE_TEXTS_CACHE.pop(key, None)
    while len(_FILE_TEXTS_CACHE) >= _FILE_TEXTS_CACHE_MAX:
        _FILE_TEXTS_CACHE.pop(next(iter(_FILE_TEXTS_CACHE)))
    _FILE_TEXTS_CACHE[key] = val

# Each hook invocation is a fresh process, so sibling declarations are persisted per
# directory (`sibling_index_path`) instead of re-reading and re-lexing every sibling
# `.lean` file on every check. Counts stay in the small per-file count cache, which
# keeps at most `COUNT_CACHE_MAX_FILES` entries (least recently checked dropped).
COUNT_CACHE_MAX_FILES = 1024
# Bump whenever rule semantics, signature normalization, or index layout change:
# count entries and sibling indexes written under another version are ignored.
# Version 7 added rules 6 (`unpinned_or_drifted_waiver`) and 7 (`trivial_or_vacuous_claim`):
# a version-6 count entry has no counts for them, and reading its missing keys as `0`
# would report every pre-existing rule 6 / rule 7 finding as newly introduced.
CACHE_FORMAT_VERSION = 7


def sibling_index_path(cache_path: str | Path, directory: str | Path) -> Path:
    """File holding the persisted private-declaration index of `directory`'s `.lean`
    files, next to the count cache `cache_path`."""
    cpath = Path(cache_path)
    tag = zlib.crc32(str(directory).encode("utf-8", "surrogatepass"))
    return cpath.with_name(f"{cpath.name}.siblings-v{CACHE_FORMAT_VERSION}-{tag:08x}.json")


def _index_entry(st: os.stat_result, file_crc: int, decls: list[PrivateDecl]) -> list[Any]:
    return [
        st.st_mtime_ns,
        st.st_size,
        file_crc,
        [
            [
                d.kind,
                d.name,
                d.line,
                d.body_start,
                d.ensure_norm_sig(),
                list(d.sig_fp),
                d.decl_indent,
                d.raw_header if d.kind == "def" else "",
                [list(k) if k is not None else None for k in d.body_keys]
                if d.body_keys is not None
                else None,
            ]
            for d in decls
        ],
    ]


def _decls_from_index_entry(
    entry: Any, st: os.stat_result, path: Path
) -> tuple[int, list[PrivateDecl]] | None:
    """Rebuild `(file_crc, decls)` stored for `path`, or `None` when missing,
    malformed, or recorded for a different `(mtime_ns, size)`."""
    try:
        if len(entry) != 4 or entry[0] != st.st_mtime_ns or entry[1] != st.st_size:
            return None
        file_crc = int(entry[2])
        out: list[PrivateDecl] = []
        for rec in entry[3]:
            if len(rec) != 9:
                return None
            kind, name, line, body_start, norm_sig, fp, decl_indent, raw_header, bkeys = rec
            if kind not in ("theorem", "lemma", "def") or not isinstance(fp, list) or len(fp) != 4:
                return None
            if bkeys is not None and (not isinstance(bkeys, list) or len(bkeys) != 2):
                return None
            out.append(
                PrivateDecl(
                    kind=kind,
                    name=str(name),
                    norm_sig=str(norm_sig),
                    line=int(line),
                    file=path.name,
                    raw_header=str(raw_header),
                    sig_fp=(int(fp[0]), int(fp[1]), int(fp[2]), int(fp[3])),
                    body_start=int(body_start),
                    path=str(path),
                    decl_indent=int(decl_indent),
                )
            )
            if bkeys is not None:
                out[-1].body_keys = (
                    tuple(int(x) for x in bkeys[0]) if bkeys[0] is not None else None,
                    tuple(int(x) for x in bkeys[1]) if bkeys[1] is not None else None,
                )
        return file_crc, out
    except (TypeError, ValueError, IndexError, KeyError, OverflowError):
        return None


def _extract_sibling_private_decls_fast(
    sibling_path: Path, persisted: dict[str, Any] | None = None
) -> list[PrivateDecl]:
    """Private declarations of one sibling file, from the in-process cache, then the
    persisted index (`persisted`, updated in place), then by lexing the file.
    Files inside `RACY_MTIME_WINDOW_NS` verify `file_crc` so same-tick, same-size
    sibling edits never serve stale declarations or stale `_sib` count signatures."""
    key = str(sibling_path)
    try:
        st = sibling_path.stat()
    except (OSError, ValueError):
        return []
    racy = _is_racy(st)
    cached = _SIBLING_PRIVATE_CACHE.get(key)
    if not racy and cached is not None and cached[0] == st.st_mtime_ns and cached[1] == st.st_size:
        file_crc, decls = cached[2], cached[3]
        if persisted is not None:
            old = persisted.get(key)
            if not (
                isinstance(old, list)
                and len(old) == 4
                and old[0] == st.st_mtime_ns
                and old[1] == st.st_size
                and old[2] == file_crc
            ):
                persisted[key] = _index_entry(st, file_crc, decls)
        return decls

    if not racy and persisted is not None:
        entry = persisted.get(key)
        restored = _decls_from_index_entry(entry, st, sibling_path) if entry is not None else None
        if restored is not None:
            file_crc, decls = restored
            _SIBLING_PRIVATE_CACHE[key] = (st.st_mtime_ns, st.st_size, file_crc, decls)
            return decls

    try:
        raw = sibling_path.read_text(encoding="utf-8", errors="replace")
    except (OSError, ValueError):
        return []
    file_crc = _text_crc(raw)
    if cached is not None and (abs(cached[0]), cached[1], cached[2]) == (
        st.st_mtime_ns,
        st.st_size,
        file_crc,
    ):
        decls = cached[3]
        if not racy:
            _SIBLING_PRIVATE_CACHE[key] = (st.st_mtime_ns, st.st_size, file_crc, decls)
            if persisted is not None:
                persisted[key] = _index_entry(st, file_crc, decls)
        return decls

    _FILE_TEXTS_CACHE.pop(key, None)
    decls = []
    if "private" in raw:
        stripped = strip_lean_comments_and_strings(raw)
        _put_file_texts_cache(
            key, (-st.st_mtime_ns if racy else st.st_mtime_ns, st.st_size, raw, stripped)
        )
        decls = extract_private_decls(
            stripped, file_label=sibling_path.name, lazy_norm=True, file_path=key
        )
        sib_budget = _BODY_COMPARE_BUDGET
        for d in decls:
            if d.kind == "def" and d.body_start >= 0:
                end = _next_decl_boundary(stripped, d.body_start, len(stripped), d.decl_indent)
                has_b = "_v0" in d.ensure_norm_sig()
                if has_b:
                    if sib_budget <= 0:
                        continue
                    sib_budget -= end - d.body_start
                d.body_keys = (
                    _body_key1(raw, stripped, d.body_start, end),
                    _body_key2(raw, stripped, d.body_start, end, has_b),
                )
    _SIBLING_PRIVATE_CACHE[key] = (
        -st.st_mtime_ns if racy else st.st_mtime_ns,
        st.st_size,
        file_crc,
        decls,
    )
    if persisted is not None and not racy:
        persisted[key] = _index_entry(st, file_crc, decls)
    return decls


# File timestamps come from a coarse kernel clock, so a second same-size write within
# one tick leaves `(mtime_ns, size)` unchanged. Files modified within this window are
# not persisted in the sibling index and are CRC-checked on access.
RACY_MTIME_WINDOW_NS = 2_000_000_000


def _is_racy(st: os.stat_result) -> bool:
    return time.time_ns() - st.st_mtime_ns < RACY_MTIME_WINDOW_NS


def _file_texts(path_str: str) -> tuple[str, str] | None:
    """`(raw, comment_stripped)` texts of `path_str`."""
    p = Path(path_str)
    try:
        st = p.stat()
    except (OSError, ValueError):
        return None
    racy = _is_racy(st)
    if not racy:
        cached = _FILE_TEXTS_CACHE.get(path_str)
        if cached is not None and cached[0] == st.st_mtime_ns and cached[1] == st.st_size:
            return cached[2], cached[3]
    try:
        raw = p.read_text(encoding="utf-8", errors="replace")
    except (OSError, ValueError):
        return None
    cached = _FILE_TEXTS_CACHE.get(path_str)
    if cached is not None and cached[2] == raw:
        if not racy and cached[0] != st.st_mtime_ns:
            _put_file_texts_cache(path_str, (st.st_mtime_ns, st.st_size, cached[2], cached[3]))
        return cached[2], cached[3]
    stripped = strip_lean_comments_and_strings(raw)
    _put_file_texts_cache(
        path_str, (-st.st_mtime_ns if racy else st.st_mtime_ns, st.st_size, raw, stripped)
    )
    return raw, stripped


def _list_dir_lean_files(parent: Path, max_files: int) -> list[Path]:
    key = str(parent)
    try:
        st = parent.stat()
    except (OSError, ValueError):
        return []
    cached = _DIR_LEAN_FILES_CACHE.get(key)
    if cached is not None and cached[0] == st.st_mtime_ns:
        return cached[1]
    try:
        with os.scandir(parent) as it:
            names = sorted(
                e.name
                for e in it
                if not e.name.startswith(".")
                and e.name.endswith(".lean")
                and e.is_file(follow_symlinks=False)
            )
    except (OSError, ValueError):
        return []
    files = [parent / name for name in names[: max_files + 1]]
    _DIR_LEAN_FILES_CACHE[key] = (st.st_mtime_ns, files)
    return files


def _collect_sibling_private_decl_lists(
    file_path: Path,
    max_siblings: int = 40,
    persisted: dict[str, Any] | None = None,
) -> list[tuple[str, list[PrivateDecl]]]:
    """`(sibling path, cached declaration list)` per sibling `.lean` file, in directory
    order. A sibling's list object is reused while its bytes are unchanged and replaced
    when they change, so list identity doubles as a content stamp (`scan_lean_text`)."""
    parent = file_path.parent
    target_name = file_path.name
    out: list[tuple[str, list[PrivateDecl]]] = []
    count = 0
    for entry in _list_dir_lean_files(parent, max_siblings):
        if count >= max_siblings:
            break
        if entry.name == target_name:
            continue
        count += 1
        out.append((str(entry), _extract_sibling_private_decls_fast(entry, persisted)))
    return out


def _collect_sibling_private_decls(
    file_path: Path,
    max_siblings: int = 40,
    persisted: dict[str, Any] | None = None,
) -> list[PrivateDecl]:
    out: list[PrivateDecl] = []
    for _, decls in _collect_sibling_private_decl_lists(file_path, max_siblings, persisted):
        out.extend(decls)
    return out


def _safe_isfile(path: str | Path) -> bool:
    try:
        return os.path.isfile(path)
    except (OSError, ValueError, TypeError):
        return False


def _load_sibling_index(index_file: Path) -> dict[str, Any]:
    data = _load_cache(index_file)
    return data if isinstance(data, dict) else {}


def _save_sibling_index(index_file: Path, index: dict[str, Any]) -> None:
    # Forget files that no longer exist (renamed, deleted, or malformed sibling keys).
    for key in [k for k in index if not _safe_isfile(k)]:
        del index[key]
    _save_cache(index_file, index)


def _sig_class(kind: str) -> str:
    # A theorem's statement is its whole content (proof irrelevance), so two private
    # theorems/lemmas with the same normalized statement are redundant. Two defs of
    # the same type are only redundant when their bodies coincide too (`maxU8 : Nat`
    # and `maxU16 : Nat` are different definitions).
    return "def" if kind == "def" else "prop"


def _duplicate_private_findings(
    local_decls: list[PrivateDecl],
    ext_decls: list[PrivateDecl],
    raw: str,
    stripped: str,
) -> list[ProofHealthFinding]:
    # Only run full alpha-renaming signature normalization on declarations whose
    # 4-tuple structural fingerprint `(colons, parens, braces, equals)` collides
    # with at least one other local or sibling declaration. The count is deliberately
    # kind-agnostic: renaming a guillemet binder (`«p:q»` -> `_v0`) drops the
    # punctuation inside it, so equal normalized signatures need not have equal
    # fingerprints, and a per-kind count would skip duplicates reported today.
    fp_counts: dict[tuple[int, int, int, int], int] = {}
    has_legacy_decls = False
    for d in ext_decls + local_decls:
        if d.sig_fp != (0, 0, 0, 0):
            fp_counts[d.sig_fp] = fp_counts.get(d.sig_fp, 0) + 1
        elif d.norm_sig:
            has_legacy_decls = True

    def sig_key(d: PrivateDecl) -> tuple[str, str] | None:
        if not (has_legacy_decls or fp_counts.get(d.sig_fp, 0) >= 2):
            return None
        ns = d.ensure_norm_sig()
        return (_sig_class(d.kind), ns) if ns else None

    # Binderless definitions (`"_v0" not in norm_sig`) hash their comment-stripped,
    # whitespace-free UTF-8 bytes directly in C (`bytes.translate`), which separates
    # distinct MIR/ADT/constant tables in one pass with no regexes and no budget cap.
    # Binder-bearing definitions use a 3-step index (punctuation counts -> identifier-
    # collapsed skeleton hash -> exact alpha-renamed key), capped at `_BODY_COMPARE_BUDGET`
    # without dropping already-queued candidates when the cap is reached.
    BodyKey = tuple[int, ...]
    key1_cache: dict[int, BodyKey | None] = {}
    key2_cache: dict[int, BodyKey | None] = {}
    exact_keys: dict[int, str] = {}
    budget = [_BODY_COMPARE_BUDGET]
    spans: dict[int, tuple[str, str, int, int] | None] = {}

    def body_span(d: PrivateDecl, local: bool) -> tuple[str, str, int, int] | None:
        k = id(d)
        if k in spans:
            return spans[k]
        span = None
        texts = (raw, stripped) if local else (_file_texts(d.path) if d.path else None)
        if texts is not None:
            r, st = texts
            if 0 <= d.body_start <= len(st) and len(r) == len(st):
                end = _next_decl_boundary(st, d.body_start, len(st), d.decl_indent)
                span = (r, st, d.body_start, end)
        spans[k] = span
        return span

    def key1(d: PrivateDecl, local: bool) -> BodyKey | None:
        k = id(d)
        if k not in key1_cache:
            if not local and d.body_keys is not None:
                key1_cache[k] = d.body_keys[0]
            else:
                span = body_span(d, local)
                key1_cache[k] = _body_key1(*span) if span is not None else None
        return key1_cache[k]

    def key2(d: PrivateDecl, local: bool, has_binders: bool) -> BodyKey | None:
        k = id(d)
        if k in key2_cache:
            return key2_cache[k]
        if not local and d.body_keys is not None:
            key2_cache[k] = d.body_keys[1]
            return d.body_keys[1]
        span = body_span(d, local)
        if span is None:
            key2_cache[k] = None
            return None
        r, st, b, e = span
        if has_binders:
            # The identifier-collapsing regex is the costly step: budgeted (a
            # skipped definition stays pending and is retried, never dropped).
            if budget[0] <= 0:
                return None
            budget[0] -= e - b
        res = _body_key2(r, st, b, e, has_binders)
        key2_cache[k] = res
        return res

    def exact_key(d: PrivateDecl, local: bool, has_binders: bool, force: bool = False) -> str:
        k = id(d)
        if k in exact_keys:
            return exact_keys[k]
        span = body_span(d, local)
        if span is None:
            exact_keys[k] = ""
            return ""
        if has_binders and not force and budget[0] <= 0:
            return ""
        if has_binders:
            budget[0] -= span[3] - span[2]
        rmap = d.ensure_rename_map() if has_binders else {}
        v = _decl_body_key(span[0], span[1], span[2], d.decl_indent, rmap)
        exact_keys[k] = v
        return v

    # Per signature, definitions are indexed level by level: `key1 -> [pending, by_key2]`
    # and `key2 -> [pending, by_exact]`. A definition enters a deeper level (and pays
    # for its finer key) only once a second definition reaches the same node, so
    # every lookup is a dictionary probe and no pair is compared twice.
    DefIndex = dict[BodyKey, list[Any]]

    def match_in(d: PrivateDecl, index: DefIndex, local: bool, has_binders: bool) -> PrivateDecl | None:
        q1 = key1(d, True)
        node2 = index.get(q1) if q1 is not None else None
        if node2 is None:
            return None
        q2 = key2(d, True, has_binders)
        if q2 is None:
            return None
        pending2, by_key2 = node2
        if pending2:
            rem2: list[PrivateDecl] = []
            for c in pending2:
                c2 = key2(c, local, has_binders)
                if c2 is not None:
                    by_key2.setdefault(c2, [[], {}])[0].append(c)
                else:
                    rem2.append(c)
            pending2[:] = rem2
        node3 = by_key2.get(q2)
        if node3 is None:
            return None
        target = exact_key(d, True, has_binders)
        if not target:
            return None
        pending3, by_exact = node3
        if pending3:
            for c in pending3:
                ce = exact_key(c, local, has_binders, force=True)
                if ce:
                    by_exact.setdefault(ce, c)
            pending3.clear()
        return by_exact.get(target)

    def index_add(d: PrivateDecl, index: DefIndex) -> None:
        q1 = key1(d, True)
        if q1 is None:
            return
        pending2, by_key2 = index.setdefault(q1, [[], {}])
        q2 = key2_cache.get(id(d))
        if q2 is None:
            pending2.append(d)
            return
        pending3, by_exact = by_key2.setdefault(q2, [[], {}])
        ex = exact_keys.get(id(d))
        if ex:
            by_exact.setdefault(ex, d)
        else:
            pending3.append(d)

    local_keys = [sig_key(d) for d in local_decls]
    local_key_counts: dict[tuple[str, str], int] = {}
    for k in local_keys:
        if k is not None:
            local_key_counts[k] = local_key_counts.get(k, 0) + 1

    ext_by_name: dict[str, PrivateDecl] = {}
    ext_by_sig: dict[tuple[str, str], list[PrivateDecl]] = {}
    for d in ext_decls:
        ext_by_name.setdefault(d.name, d)
        k = sig_key(d)
        if k is not None:
            ext_by_sig.setdefault(k, []).append(d)
    # Sibling definitions of one signature, indexed on first use (so sibling texts are
    # only re-read for signatures a local definition shares).
    ext_def_indexes: dict[tuple[str, str], DefIndex] = {}

    def ext_def_index(k: tuple[str, str]) -> DefIndex:
        idx = ext_def_indexes.get(k)
        if idx is None:
            idx = {}
            for c in ext_by_sig.get(k, ()):
                q = key1(c, False)
                if q is not None:
                    idx.setdefault(q, [[], {}])[0].append(c)
            ext_def_indexes[k] = idx
        return idx

    findings: list[ProofHealthFinding] = []
    seen_names: dict[str, PrivateDecl] = {}
    seen_props: dict[tuple[str, str], PrivateDecl] = {}
    seen_def_indexes: dict[tuple[str, str], DefIndex] = {}
    for d, k in zip(local_decls, local_keys):
        same = "signature and body" if d.kind == "def" else "signature"
        has_binders = k is not None and "_v0" in k[1]
        dup_reason: str | None = None
        if d.name in seen_names:
            prev = seen_names[d.name]
            dup_reason = f"duplicates earlier `private {prev.kind} {prev.name}` on L{prev.line}"
        else:
            prev = None
            if k is not None:
                if k[0] == "prop":
                    prev = seen_props.get(k)
                elif k in seen_def_indexes:
                    prev = match_in(d, seen_def_indexes[k], True, has_binders)
            if prev is not None:
                dup_reason = (
                    f"has the same normalized {same} as `private {prev.kind} {prev.name}` "
                    f"on L{prev.line}"
                )
            elif d.name in ext_by_name:
                sib = ext_by_name[d.name]
                dup_reason = (
                    f"duplicates `private {sib.kind} {sib.name}` in sibling file "
                    f"`{sib.file}` (L{sib.line})"
                )
            elif k is not None and k in ext_by_sig:
                sib = (
                    ext_by_sig[k][0]
                    if k[0] == "prop"
                    else match_in(d, ext_def_index(k), False, has_binders)
                )
                if sib is not None:
                    dup_reason = (
                        f"has the same normalized {same} as `private {sib.kind} {sib.name}` "
                        f"in sibling file `{sib.file}` (L{sib.line})"
                    )

        seen_names.setdefault(d.name, d)
        if k is not None:
            if k[0] == "prop":
                seen_props.setdefault(k, d)
            elif local_key_counts[k] >= 2:
                index_add(d, seen_def_indexes.setdefault(k, {}))

        if dup_reason is not None:
            findings.append(
                ProofHealthFinding(
                    rule=RULE_DUPLICATE_PRIVATE_LEMMA,
                    line=d.line,
                    symbol=d.name,
                    message=f"`private {d.kind} {d.name}` {dup_reason}.",
                    suggestion=(
                        "Reuse or generalize the existing helper lemma (or promote shared "
                        "helpers to a common module) instead of duplicating `private` lemmas."
                    ),
                )
            )
    return findings


_ORIG_EXTRACT_PRIVATE_DECLS = extract_private_decls


# `_FILE_TEXTS_CACHE` key prefixes for entries that are not sibling texts. A NUL can
# never occur in a path, so these never collide with the `str(path)` keys under which
# `_file_texts` / `_extract_sibling_private_decls_fast` store text-mode
# (newline-translated) sibling texts whose declaration offsets assume that decoding.
_SCAN_META_KEY_PREFIX = "\x00meta:"
_SCAN_FILE_KEY_PREFIX = "\x00scan:"


def _scan_text_meta(
    text: str, stripped: str | None = None, *, memo: bool = True
) -> tuple[
    str,
    int,
    dict[str, int],
    bool,
    bool,
    bool,
    bool,
    int,
    tuple[tuple[str, str, str, tuple[int, int, int, int], int, int, int], ...],
]:
    """Return `(stripped, first_simp, active_kws, has_mir_body, has_bitwise,
    scan_unfold, has_profiler, first_private, private_specs)` for `text` (lexing it
    unless its comment- and string-blanked code `stripped` is given). With `memo`, the
    keyword and declaration-header index of large texts (`>= 4096` chars) is cached in
    `_FILE_TEXTS_CACHE` so rescanning identical text skips recomputing it. A cache hit
    is verified against the full text (and against `stripped` when given, so the index
    always describes the very code it is used with) and returns a fresh `active_kws`
    dict."""
    n = len(text)
    idx_key = ""
    if memo and n >= 4096:
        idx_key = f"{_SCAN_META_KEY_PREFIX}{n}:{hash(text[:128])}:{hash(text[-128:])}"
        cached = _FILE_TEXTS_CACHE.get(idx_key)
        if (
            cached is not None
            and len(cached) == 10
            and cached[0] == text
            and (stripped is None or cached[1] == stripped)
        ):
            hit = cached[1:]
            return (hit[0], hit[1], dict(hit[2]), *hit[3:])  # type: ignore[return-value]

    st = stripped if stripped is not None else strip_lean_comments_and_strings(text)
    first_simp = st.find("simp", 0)
    active_kws, has_mir_body, has_bitwise = _active_simp_keywords(
        st,
        simp_start=(first_simp + 4) if first_simp != -1 else 0,
        check_rule1=(first_simp != -1),
    )

    # Rules 2 & 3 on `unfold` / `delta` targets need such a tactic plus an exact
    # `Mir.<...>.body` identifier or a raw bitwise name (every target finding is one).
    scan_unfold = (has_mir_body or has_bitwise) and (("unfold" in st) or ("delta" in st))
    has_profiler = "trace.profiler.threshold" in st
    first_private = st.find("private", 0)
    private_specs_list: list[tuple[str, str, str, tuple[int, int, int, int], int, int, int]] = []
    if first_private != -1:
        pos = first_private
        while pos != -1:
            if pos == 0 or not (_is_ident_char(st[pos - 1]) or st[pos - 1] == "."):
                m = _PRIVATE_LIT_RE.match(st, pos)
                if m is not None:
                    decl_indent = _line_indent_at(st, pos)
                    raw_header, body_start = _decl_header_span(st, m.end(), decl_indent)
                    sig_fp = _header_fingerprint(raw_header)
                    private_specs_list.append(
                        (
                            m.group(1),
                            m.group(2),
                            raw_header,
                            sig_fp,
                            body_start,
                            decl_indent,
                            pos,
                        )
                    )
                    pos = st.find("private", m.end())
                    continue
            pos = st.find("private", pos + 7)
    private_specs = tuple(private_specs_list)

    res = (
        st,
        first_simp,
        active_kws,
        has_mir_body,
        has_bitwise,
        scan_unfold,
        has_profiler,
        first_private,
        private_specs,
    )
    if idx_key:
        _put_file_texts_cache(idx_key, (text, *res[:2], dict(active_kws), *res[3:]))
    return res


def scan_lean_text(
    text: str,
    *,
    file_path: str | Path | None = None,
    scan_siblings: bool = True,
    sibling_decls: list[PrivateDecl] | None = None,
    include_unannotated_vacuity: bool = False,
    include_advisories: bool = False,
) -> list[ProofHealthFinding]:
    """Scan Lean 4 source `text` and return all structural proof-health findings.

    Results are memoized in `_SCAN_RESULT_CACHE` for the exact text (looked up by a cheap
    length / head / tail key, then confirmed by full text equality, so a hit never hashes a
    megabyte-sized string), the options, and (when the text can declare `private` items and
    siblings are scanned) the identity of every sibling's cached declaration list, which is
    replaced whenever that sibling's bytes change; an explicit `sibling_decls` list bypasses
    the memo. `include_advisories=True` additionally includes `ADVISORY_RULES` from
    `scan_projection_and_rewrite_order_hazards`.
    """
    cache_key: tuple[int, str, str, str, bool, bool, bool] | None = None
    sib_lists: tuple[list[PrivateDecl], ...] = ()
    sib_names: tuple[str, ...] = ()
    computed_siblings = False
    if sibling_decls is None:
        if scan_siblings and file_path is not None and "private" in text:
            pairs = _collect_sibling_private_decl_lists(Path(file_path))
            sib_names = tuple(p for p, _ in pairs)
            sib_lists = tuple(lst for _, lst in pairs)
            computed_siblings = True
        cache_key = (
            len(text),
            text[:128],
            text[-128:],
            str(file_path) if file_path is not None else "",
            bool(scan_siblings),
            bool(include_unannotated_vacuity),
            bool(include_advisories),
        )
        hit = _SCAN_RESULT_CACHE.get(cache_key)
        if (
            hit is not None
            and hit[0] == text
            and hit[1] == sib_names
            and len(hit[2]) == len(sib_lists)
            and all(a is b for a, b in zip(hit[2], sib_lists))
        ):
            return list(hit[3])
        if include_advisories:
            base_hit = _SCAN_RESULT_CACHE.get((*cache_key[:6], False))
            if (
                base_hit is not None
                and base_hit[0] == text
                and base_hit[1] == sib_names
                and len(base_hit[2]) == len(sib_lists)
                and all(a is b for a, b in zip(base_hit[2], sib_lists))
            ):
                base_scan_key = (cache_key[3], cache_key[4], cache_key[5], False)
                base_prev = _LAST_LEAN_SCAN.get(base_scan_key)
                pre_stripped = base_prev[1] if (base_prev is not None and base_prev[0] == text) else None
                merged = list(base_hit[3]) + scan_projection_and_rewrite_order_hazards(
                    text, stripped=pre_stripped
                )
                merged.sort(key=lambda f: (f.line, f.rule, f.symbol, f.subrule))
                merged_tup = tuple(merged)
                _SCAN_RESULT_CACHE.pop(cache_key, None)
                _SCAN_RESULT_CACHE[cache_key] = (text, sib_names, sib_lists, merged_tup)
                while len(_SCAN_RESULT_CACHE) > _SCAN_RESULT_CACHE_MAX:
                    del _SCAN_RESULT_CACHE[next(iter(_SCAN_RESULT_CACHE))]
                if base_prev is not None and base_prev[0] == text:
                    true_scan_key = (cache_key[3], cache_key[4], cache_key[5], True)
                    if true_scan_key not in _LAST_LEAN_SCAN and len(_LAST_LEAN_SCAN) >= 16:
                        _LAST_LEAN_SCAN.clear()
                    _LAST_LEAN_SCAN[true_scan_key] = (
                        *base_prev[:6],
                        merged_tup,
                    )
                return merged
        else:
            adv_hit = _SCAN_RESULT_CACHE.get((*cache_key[:6], True))
            if (
                adv_hit is not None
                and adv_hit[0] == text
                and adv_hit[1] == sib_names
                and len(adv_hit[2]) == len(sib_lists)
                and all(a is b for a, b in zip(adv_hit[2], sib_lists))
            ):
                filtered = [f for f in adv_hit[3] if f.rule not in _ADVISORY_RULE_SET]
                filtered_tup = tuple(filtered)
                _SCAN_RESULT_CACHE.pop(cache_key, None)
                _SCAN_RESULT_CACHE[cache_key] = (text, sib_names, sib_lists, filtered_tup)
                while len(_SCAN_RESULT_CACHE) > _SCAN_RESULT_CACHE_MAX:
                    del _SCAN_RESULT_CACHE[next(iter(_SCAN_RESULT_CACHE))]
                adv_prev = _LAST_LEAN_SCAN.get((cache_key[3], cache_key[4], cache_key[5], True))
                if adv_prev is not None and adv_prev[0] == text:
                    false_scan_key = (cache_key[3], cache_key[4], cache_key[5], False)
                    if false_scan_key not in _LAST_LEAN_SCAN and len(_LAST_LEAN_SCAN) >= 16:
                        _LAST_LEAN_SCAN.clear()
                    _LAST_LEAN_SCAN[false_scan_key] = (
                        *adv_prev[:6],
                        filtered_tup,
                    )
                return filtered
    findings = _scan_lean_text_uncached(
        text,
        file_path=file_path,
        scan_siblings=scan_siblings,
        sibling_decls=(
            [d for lst in sib_lists for d in lst] if computed_siblings else sibling_decls
        ),
        include_unannotated_vacuity=include_unannotated_vacuity,
        include_advisories=include_advisories,
    )
    if cache_key is not None:
        _SCAN_RESULT_CACHE.pop(cache_key, None)
        _SCAN_RESULT_CACHE[cache_key] = (text, sib_names, sib_lists, tuple(findings))
        while len(_SCAN_RESULT_CACHE) > _SCAN_RESULT_CACHE_MAX:
            del _SCAN_RESULT_CACHE[next(iter(_SCAN_RESULT_CACHE))]
    return findings


# `scan_lean_text` memo: `(len(text), text[:128], text[-128:], file_path, scan_siblings,
# include_unannotated_vacuity, include_advisories)` -> `(text, sibling paths, sibling
# declaration lists, findings)`, least recently stored first; a hit additionally requires
# full `text` equality.
_SCAN_RESULT_CACHE: dict[
    tuple[int, str, str, str, bool, bool, bool],
    tuple[str, tuple[str, ...], tuple[list[PrivateDecl], ...], tuple[ProofHealthFinding, ...]],
] = {}
_SCAN_RESULT_CACHE_MAX = 32


def _scan_lean_text_uncached(
    text: str,
    *,
    file_path: str | Path | None = None,
    scan_siblings: bool = True,
    sibling_decls: list[PrivateDecl] | None = None,
    include_unannotated_vacuity: bool = False,
    include_advisories: bool = False,
    _preparsed: tuple[str, list[tuple[int, int, int, str, str]]] | None = None,
) -> list[ProofHealthFinding]:
    scan_key = (
        str(file_path) if file_path is not None else "",
        bool(scan_siblings),
        bool(include_unannotated_vacuity),
        bool(include_advisories),
    )
    if INCREMENTAL_SPLICING and _preparsed is None and len(text) >= 32768:
        prev_scan = _LAST_LEAN_SCAN.get(scan_key)
        if prev_scan is not None:
            old_text, old_code, c_starts, c_ends, col0_thms, old_sibs, old_findings = prev_scan
            cur_sibs: list[PrivateDecl] | None = None
            if sibling_decls is not None:
                cur_sibs = list(sibling_decls)
            elif scan_siblings and file_path is not None:
                cur_sibs = _collect_sibling_private_decls(Path(file_path))
            else:
                cur_sibs = []
            if len(cur_sibs) == len(old_sibs) and all(a == b for a, b in zip(cur_sibs, old_sibs)):
                if text == old_text:
                    return list(old_findings)
                win_info = _find_incremental_lean_window(
                    old_text, old_code, c_starts, c_ends, col0_thms, text
                )
                if win_info is not None:
                    (
                        safe_lo,
                        safe_hi_old,
                        safe_hi_new,
                        lo_line_offset,
                        cut_lo_line,
                        cut_hi_old_line,
                        cut_hi_new_line,
                        delta_lines,
                        win_code,
                        win_comments,
                    ) = win_info
                    if (
                        "private" not in old_code[safe_lo:safe_hi_old]
                        and "private" not in win_code
                        and not (
                            delta_lines != 0
                            and any(f.rule == RULE_DUPLICATE_PRIVATE_LEMMA for f in old_findings)
                        )
                    ):
                        win_findings = _scan_lean_text_uncached(
                            text[safe_lo:safe_hi_new],
                            file_path=file_path,
                            scan_siblings=False,
                            sibling_decls=[],
                            include_unannotated_vacuity=include_unannotated_vacuity,
                            include_advisories=include_advisories,
                            _preparsed=(win_code, win_comments),
                        )
                        spliced = [f for f in old_findings if f.line < cut_lo_line]
                        for wf in win_findings:
                            adj_line = wf.line + lo_line_offset
                            if cut_lo_line <= adj_line < cut_hi_new_line:
                                spliced.append(
                                    ProofHealthFinding(
                                        wf.rule,
                                        adj_line,
                                        wf.message,
                                        wf.suggestion,
                                        wf.symbol,
                                        subrule=wf.subrule,
                                        expected_pin=wf.expected_pin,
                                        actual_pin=wf.actual_pin,
                                        tier=wf.tier,
                                    )
                                )
                        for f in old_findings:
                            if f.line >= cut_hi_old_line:
                                spliced.append(
                                    f
                                    if delta_lines == 0
                                    else ProofHealthFinding(
                                        f.rule,
                                        f.line + delta_lines,
                                        f.message,
                                        f.suggestion,
                                        f.symbol,
                                        subrule=f.subrule,
                                        expected_pin=f.expected_pin,
                                        actual_pin=f.actual_pin,
                                        tier=f.tier,
                                    )
                                )
                        spliced.sort(key=lambda f: (f.line, f.rule, f.symbol, f.subrule))
                        return spliced

    if _preparsed is not None:
        stripped, comment_blocks = _preparsed
    else:
        stripped, comment_blocks = _scan_lean_comments_and_strings(text)
    # Rules 1-5 keyword and private-declaration index of `stripped`. Whole-file scans memoize
    # it by exact text and code (`_scan_text_meta`); splice windows are one-off texts and skip
    # the memo so they never evict sibling texts from `_FILE_TEXTS_CACHE`.
    (
        _,
        first_simp,
        active_kws,
        has_mir_body,
        has_bitwise,
        scan_unfold,
        has_profiler,
        first_private,
        private_specs,
    ) = _scan_text_meta(text, stripped, memo=_preparsed is None)
    line_of = _LineCounter(stripped)
    findings: list[ProofHealthFinding] = []

    # Rules 1, 2, 3 inside `dsimp [...]` / `simp [...]` bracket lists
    if active_kws and first_simp != -1:
        for tactic_kind, open_idx, close_idx, content in _iter_simp_brackets(
            stripped, active_kws=active_kws
        ):
            if not _has_simp_candidate(content):
                continue
            base_offset = open_idx + 1

            # Rule 1: `dsimp_forbidden_sym`
            # Purely syntactic over unfolded simp-lemma entries, with no location- or
            # neighbour-based exemptions; only entries that keep the symbol folded are
            # skipped: erasures `-sym`, reverse rewrites `← sym`, arguments `[f sym]`.
            if "wpMirExecSym" in content or "Sequence.length" in content:
                for sm in _FORBIDDEN_SIMP_SYM_RE.finditer(content):
                    if not _is_simp_unfold_entry(content, sm.start(), sm.end()):
                        continue
                    sym = sm.group(1)
                    line = line_of(base_offset + sm.start(1))
                    findings.append(
                        ProofHealthFinding(
                            rule=RULE_DSIMP_FORBIDDEN_SYM,
                            line=line,
                            symbol=sym,
                            message=(
                                f"`{sym}` inside `{tactic_kind} [...]` triggers bottom-up symbolic "
                                "expansion or corrupts implicit `Decidable` instances."
                            ),
                            suggestion=(
                                f"Remove `{sym}` from `{tactic_kind} [...]`; use wildcard `change` "
                                "or targeted `rw` lemmas instead."
                            ),
                        )
                    )

            # Rule 2: `dsimp_mir_body_unfold` inside `dsimp` / `simp`
            if has_mir_body and "Mir." in content and ".body" in content:
                for bm in _MIR_BODY_RE.finditer(content):
                    if not _is_simp_unfold_entry(content, bm.start(), bm.end()):
                        continue
                    sym = bm.group(1)
                    line = line_of(base_offset + bm.start(1))
                    findings.append(
                        ProofHealthFinding(
                            rule=RULE_DSIMP_MIR_BODY_UNFOLD,
                            line=line,
                            symbol=sym,
                            message=(
                                f"Unfolding `{sym}` inside `{tactic_kind} [...]` substitutes the "
                                "entire basic-block list into every symbolic step state."
                            ),
                            suggestion=(
                                "Pre-project basic blocks into top-level `itemBBk` definitions "
                                "and use `O(1)` `lookupBlock` `rfl` lemmas."
                            ),
                        )
                    )

            # Rule 3: `raw_bitwise_unfold` inside `dsimp` / `simp`
            if has_bitwise and "bitwise" in content:
                for rwm in _RAW_BITWISE_RE.finditer(content):
                    if not _is_simp_unfold_entry(content, rwm.start(), rwm.end()):
                        continue
                    sym = rwm.group(1)
                    line = line_of(base_offset + rwm.start(1))
                    findings.append(
                        ProofHealthFinding(
                            rule=RULE_RAW_BITWISE_UNFOLD,
                            line=line,
                            symbol=sym,
                            message=(
                                f"Unfolding recursive `{sym}` inside `{tactic_kind} [...]` unrolls "
                                "8-64 nested `Nat.div` trees and stalls kernel `whnf`."
                            ),
                            suggestion=(
                                f"Remove `{sym}` from `{tactic_kind} [...]` and rewrite with "
                                f"`{sym}Fast` or closed-form arithmetic mask lemmas."
                            ),
                        )
                    )

    # Rules 2 & 3 inside `unfold` / `delta` tactics (single-line and multiline)
    if scan_unfold:
        for tactic_kw, tok_off, tok in _iter_unfold_targets(stripped):
            if has_mir_body and ".body" in tok and "Mir." in tok:
                bm = _MIR_BODY_RE.fullmatch(tok)
                if bm is not None:
                    sym = bm.group(1)
                    line = line_of(tok_off + bm.start(1))
                    findings.append(
                        ProofHealthFinding(
                            rule=RULE_DSIMP_MIR_BODY_UNFOLD,
                            line=line,
                            symbol=sym,
                            message=(
                                f"Unfolding `{sym}` via `{tactic_kw}` substitutes the full CFG basic-block "
                                "table into the proof goal."
                            ),
                            suggestion=(
                                "Pre-project basic blocks into top-level `itemBBk` definitions "
                                f"and rewrite with `lookupBlock` lemmas instead of `{tactic_kw} {sym}`."
                            ),
                        )
                    )
                    continue
            if has_bitwise and "bitwise" in tok:
                rwm = _RAW_BITWISE_RE.fullmatch(tok)
                if rwm is not None:
                    sym = rwm.group(1)
                    line = line_of(tok_off + rwm.start(1))
                    findings.append(
                        ProofHealthFinding(
                            rule=RULE_RAW_BITWISE_UNFOLD,
                            line=line,
                            symbol=sym,
                            message=(
                                f"Unfolding recursive `{sym}` via `{tactic_kw}` unrolls bit-by-bit "
                                "`Nat.div` recursion over symbolic naturals."
                            ),
                            suggestion=(
                                f"Do not `{tactic_kw} {sym}`; use `{sym}Fast` or closed-form "
                                "modular arithmetic lemmas."
                            ),
                        )
                    )

    # Rule 4: `low_profiler_threshold`
    if has_profiler:
        for pm in _PROFILER_THRESHOLD_RE.finditer(stripped):
            before = stripped[pm.start() - 1] if pm.start() > 0 else " "
            if _is_ident_char(before) or before == ".":
                continue
            lit = pm.group(1).replace("_", "").lower()
            base = {"0x": 16, "0b": 2, "0o": 8}.get(lit[:2], 10)
            digits = (lit[2:] if base != 10 else lit).lstrip("0") or "0"
            # With more significant digits than the threshold has bits, the value is at
            # least 2**bit_length > threshold in any base. Skipping such literals also
            # keeps huge ones away from `int()` (which refuses over 4300 digits).
            if len(digits) > MIN_PROFILER_THRESHOLD.bit_length():
                continue
            val = int(digits, base)
            if val < MIN_PROFILER_THRESHOLD:
                line = line_of(pm.start())
                findings.append(
                    ProofHealthFinding(
                        rule=RULE_LOW_PROFILER_THRESHOLD,
                        line=line,
                        symbol=f"trace.profiler.threshold={val}",
                        message=(
                            f"`set_option trace.profiler.threshold {val}` (< {MIN_PROFILER_THRESHOLD}) "
                            "formats huge MIR ASTs at every elaborator step and stalls builds."
                        ),
                        suggestion=(
                            f"Remove `trace.profiler.threshold` or set it to `>= {MIN_PROFILER_THRESHOLD}` "
                            "(e.g. `100`) with `set_option pp.deepTerms false`."
                        ),
                    )
                )

    # Rule 5: `duplicate_private_lemma`
    file_label = Path(file_path).name if file_path else ""
    if not private_specs:
        local_decls: list[PrivateDecl] = []
    elif extract_private_decls is not _ORIG_EXTRACT_PRIVATE_DECLS:
        local_decls = extract_private_decls(
            stripped,
            file_label=file_label,
            lazy_norm=True,
            line_of=line_of,
            start_pos=first_private,
        )
    else:
        local_decls = [
            PrivateDecl(
                kind=kind,
                name=name,
                norm_sig="",
                line=0,
                file=file_label,
                raw_header=raw_header,
                sig_fp=sig_fp,
                body_start=body_start,
                decl_indent=decl_indent,
                pos=pos,
                line_of=line_of,
            )
            for kind, name, raw_header, sig_fp, body_start, decl_indent, pos in private_specs
        ]
    ext_decls: list[PrivateDecl] = []
    if sibling_decls is not None:
        ext_decls = list(sibling_decls)
    elif (local_decls or len(text) >= 32768) and scan_siblings and file_path is not None:
        ext_decls = _collect_sibling_private_decls(Path(file_path))
    if local_decls:
        findings.extend(_duplicate_private_findings(local_decls, ext_decls, text, stripped))

    # Rules 6 & 7: waiver pins and non-vacuity (shared auditor)
    findings.extend(
        _lean_waiver_and_vacuity_findings(
            text,
            file_path=file_path,
            include_unannotated_vacuity=include_unannotated_vacuity,
            _preparsed=(stripped, comment_blocks),
        )
    )

    if include_advisories:
        findings.extend(scan_projection_and_rewrite_order_hazards(text, stripped=stripped))

    findings.sort(key=lambda f: (f.line, f.rule, f.symbol, f.subrule))
    if INCREMENTAL_SPLICING and _preparsed is None and len(text) >= 32768:
        thms = _iter_lean_theorem_headers(stripped)
        col0_thms = [kw for kw, _, _ in thms if kw == 0 or stripped[kw - 1] == "\n"]
        if len(col0_thms) >= 8:
            if len(_LAST_LEAN_SCAN) >= 16:
                _LAST_LEAN_SCAN.clear()
            _LAST_LEAN_SCAN[scan_key] = (
                text,
                stripped,
                [c[0] for c in comment_blocks],
                [c[1] for c in comment_blocks],
                col0_thms,
                tuple(ext_decls),
                tuple(findings),
            )
    return findings


_LAST_LEAN_SCAN: dict[
    tuple[str, bool, bool, bool],
    tuple[
        str,
        str,
        list[int],
        list[int],
        list[int],
        tuple[PrivateDecl, ...],
        tuple[ProofHealthFinding, ...],
    ],
] = {}


def scan_lean_file(
    file_path: str | Path,
    *,
    scan_siblings: bool = True,
    include_unannotated_vacuity: bool = False,
    include_advisories: bool = False,
) -> list[ProofHealthFinding]:
    path = Path(file_path)
    key = _SCAN_FILE_KEY_PREFIX + str(path)
    try:
        st = path.stat()
    except (OSError, ValueError):
        st = None
    # Racy files (modified within `RACY_MTIME_WINDOW_NS`) are neither served from nor
    # stored in the cache: a second same-size write within one coarse timestamp tick
    # would leave `(mtime_ns, size)` unchanged while the content differs. Only the decoded
    # text is cached: `scan_lean_text` memoizes results by exact content and lexes lazily
    # (once per full scan, or just the edited window when splicing), so eager lexing here
    # would only duplicate or waste that work.
    cacheable = st is not None and not _is_racy(st)
    if cacheable:
        cached = _FILE_TEXTS_CACHE.get(key)
        if cached is not None and cached[0] == st.st_mtime_ns and cached[1] == st.st_size:
            return scan_lean_text(
                cached[2],
                file_path=path,
                scan_siblings=scan_siblings,
                include_unannotated_vacuity=include_unannotated_vacuity,
                include_advisories=include_advisories,
            )
    # Bytes + decode skips text-mode newline translation; line numbers count `\n`
    # either way and a stray `\r` is whitespace to every rule.
    text = path.read_bytes().decode("utf-8", errors="replace")
    if cacheable:
        _put_file_texts_cache(key, (st.st_mtime_ns, st.st_size, text))
    return scan_lean_text(
        text,
        file_path=path,
        scan_siblings=scan_siblings,
        include_unannotated_vacuity=include_unannotated_vacuity,
        include_advisories=include_advisories,
    )


def count_findings_by_rule(findings: Iterable[ProofHealthFinding]) -> dict[str, int]:
    counts = {rule: 0 for rule in ALL_RULES}
    for f in findings:
        counts[f.rule] = counts.get(f.rule, 0) + 1
    return counts


# ---------------------------------------------------------------------------
# Advisory hazards: deep projection chains under `simp`, and `try rw ... at h ⊢`
# ---------------------------------------------------------------------------

_ADVISORY_RULE_SET: frozenset[str] = frozenset(ADVISORY_RULES)

# How far before a projection chain the `simp` call or statement keyword that contains it
# may start, the longest tactic step / bracket group / `try` block that is followed, and
# how many candidate occurrences before a chain are tried. The bounds keep the scan linear
# on adversarial input; real proofs stay far below them.
_ADV_BACK_WINDOW = 8192
_ADV_STATEMENT_WINDOW = 2048
_ADV_SCAN_LIMIT = 16384
_ADV_MAX_SIMP_CANDIDATES = 24
_ADV_MAX_STATEMENT_CANDIDATES = 12
_ADV_STATEMENT_KEYWORDS = ("change", "show", "have", "suffices")
_ADV_WS = " \t\r\n"
_ADV_STATEMENT_STOPS = frozenset((":=", "by", "from", "at", ";", "<;>"))
_ADV_STEP_STOPS = frozenset((";", "<;>"))
_ADV_USING_STOPS = frozenset((";", "<;>", ","))
_ADV_TRY_STOPS = frozenset(("|",))
_ADV_NO_STOPS: frozenset[str] = frozenset()
_ADV_TURNSTILES = ("⊢", "|-")
_ADV_LOC_STOP_WORDS: frozenset[str] = _UNFOLD_STOP_WORDS | frozenset(
    (
        "λ",
        "try",
        "erw",
        "rewrite",
        "rwa",
        "all_goals",
        "any_goals",
        "repeat",
        "repeat'",
        "focus",
        "first",
        "push_neg",
        "ring",
        "ring_nf",
        "norm_num",
        "norm_cast",
        "field_simp",
        "aesop",
        "grind",
        "linarith",
        "nlinarith",
        "clear",
        "subst",
        "revert",
        "generalize",
        "generalize_proofs",
        "specialize",
        "split",
        "rename_i",
        "congr",
        "ext",
        "funext",
        "tauto",
        "exfalso",
        "left",
        "right",
        "use",
        "then",
        "else",
        "for",
        "while",
        "unless",
    )
)
_ADV_NON_TACTIC_BEFORE_TRY_CHARS = frozenset(":=+-*/,→")
_ADV_NON_TACTIC_BEFORE_TRY_WORDS = frozenset(
    (
        "let",
        "exact",
        "apply",
        "refine",
        "return",
        "fun",
        "λ",
        "have",
        "suffices",
        "show",
        "change",
        "from",
        "use",
        "intro",
        "intros",
        "cases",
        "induction",
        "rcases",
        "obtain",
        "rename_i",
        "clear",
        "subst",
        "revert",
        "specialize",
        "unfold",
        "delta",
        "at",
        "using",
        "if",
        "match",
        "forall",
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "axiom",
        "opaque",
        "structure",
        "class",
        "inductive",
        "instance",
        "namespace",
        "section",
        "end",
        "open",
        "variable",
    )
)
_ADV_GUI_OR_CHAR = (
    r"«[^»\n]*»"
    r"|(?<![\w'!?\u00bb])'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'"
)


class _AdvisoryRegexes:
    """Regexes of the advisory scanner, compiled on first use: scans without
    `include_advisories` (every hook process) never pay for them."""

    __slots__ = (
        "step_token",
        "bracket",
        "projection",
        "advance_stmt_sym",
        "config_item",
        "step_prefix",
        "rw_head",
        "location",
        "next_line",
        "flat_line",
    )

    def __init__(self) -> None:
        # Guillemet identifiers and char literals are skipped whole first so brackets or
        # semicolons inside `«a]b»` or `']'` never desync tactic/bracket boundaries.
        # Standalone `|` excludes `|-` turnstiles and `||` / `|>` / `<|>` operators.
        self.step_token = re.compile(
            _ADV_GUI_OR_CHAR
            + r"|[()\[\]{}⟨⟩;,\n]|:=|=>|<;>|(?<![|<])\|(?![->|])|"
            + r"(?<![\w'!?.\u00ab])(?:by|from|at|fun|λ)(?![\w'!?.\u00bb])"
        )
        self.bracket = re.compile(_ADV_GUI_OR_CHAR + r"|[()\[\]{}⟨⟩]")
        # One projection: `.field`, `.1`, `.«field»`.
        self.projection = re.compile(r"\.(?:[^\W\d][\w'!?]*|\d+|«[^»\n]+»)")
        # Unfolded `advanceStmt` symbol (optionally qualified or `.eq_def` / `.eq_unfold` / `.eq_N`).
        self.advance_stmt_sym = re.compile(
            r"(?<![\w'!?.\u00ab])"
            + _QUAL_PREFIX
            + r"advanceStmt"
            + _UNFOLD_EQ_SUFFIX
            + r"(?![\w'!?.\u00bb])"
        )
        # `(config := ...)`, `(disch := ...)`, `(occs := ...)`: a named argument group.
        self.config_item = re.compile(r"\(\s*[^\W\d][\w'!?]*\s*:=")
        # Combinators that run the tactic after them on the current goal(s).
        self.step_prefix = re.compile(
            r"(?:try|all_goals|any_goals|repeat'?|focus)(?![\w'!?.\u00bb])"
        )
        self.rw_head = re.compile(
            r"(?<![\w'!?.\u00ab])(rw|erw|rewrite|rwa)(?![\w'!?.\u00bb])"
        )
        # One rewrite location on the same line: the goal, `*`, or a hypothesis name.
        self.location = re.compile(r"[ \t]*(⊢|\|-|\*|[^\W\d][\w'!?]*|«[^»\n]+»)")
        # From just past a line end: blank lines, then (group 1) the indentation of the
        # next non-blank line. Always matches; it ends at that line's first character.
        self.next_line = re.compile(r"(?:[ \t\r]*\n)*([ \t\r]*)")
        # The rest of a line that holds no `;` or standalone `|` and only flat, balanced
        # bracket groups.
        atom = _ADV_GUI_OR_CHAR + r"|[^\n;|()\[\]{}]|\|(?=[-|>])|(?<=[|<])\|"
        self.flat_line = re.compile(
            rf"(?:{atom}|\[(?:{atom})*\]|\((?:{atom})*\)|\{{(?:{atom})*\}})*(?=\n|\Z)"
        )


_ADVISORY_REGEXES: _AdvisoryRegexes | None = None


def _advisory_regexes() -> _AdvisoryRegexes:
    global _ADVISORY_REGEXES
    if _ADVISORY_REGEXES is None:
        _ADVISORY_REGEXES = _AdvisoryRegexes()
    return _ADVISORY_REGEXES


def _adv_skip_ws(stripped: str, pos: int, n: int) -> int:
    while pos < n and stripped[pos] in _ADV_WS:
        pos += 1
    return pos


def _adv_word_at(stripped: str, pos: int, word: str, n: int) -> bool:
    """True when the whole token at `pos` is the keyword `word`."""
    if not stripped.startswith(word, pos):
        return False
    end = pos + len(word)
    return end >= n or not (_is_ident_char(stripped[end]) or stripped[end] in ".»")


def _adv_col(stripped: str, pos: int) -> int:
    return pos - (stripped.rfind("\n", 0, pos) + 1)


def _adv_step_col(stripped: str, pos: int) -> int:
    """Column of the first tactic token on `pos`'s line (after leading whitespace and any
    focusing bullets `·`, `.`, `-`, `+`, `*`). Later lines must exceed this column to
    continue the tactic sequence starting on that line."""
    line_start = stripped.rfind("\n", 0, pos) + 1
    k = line_start
    while k < pos and stripped[k] in " \t":
        k += 1
    while k < pos:
        ch = stripped[k]
        if ch in " \t·":
            k += 1
        elif ch in ".-+*" and k + 1 < pos and stripped[k + 1] in " \t":
            k += 1
        else:
            break
    return k - line_start


def _adv_match_close(stripped: str, open_idx: int, n: int) -> int:
    """Offset of the bracket closing the one at `open_idx` (nesting of `()`, `[]`, `{}` and
    `⟨⟩` counted together), or `-1` when it does not close within `_ADV_SCAN_LIMIT`."""
    depth = 0
    hard_end = open_idx + _ADV_SCAN_LIMIT
    if hard_end > n:
        hard_end = n
    for m in _advisory_regexes().bracket.finditer(stripped, open_idx, hard_end):
        tok = m.group()
        if len(tok) != 1:
            continue
        if tok in "([{⟨":
            depth += 1
        else:
            depth -= 1
            if depth <= 0:
                return m.start()
    return -1


def _adv_scan_to(
    stripped: str,
    pos: int,
    n: int,
    min_indent: int,
    stops: frozenset[str],
    *,
    same_line_stops: frozenset[str] = _ADV_NO_STOPS,
    infix_min_indent: int | None = None,
) -> tuple[int, str, int]:
    """Follow the tactic step (or term) starting at `pos` and return `(end, token, next)`,
    where it stops outside every bracket opened after `pos`:

    * at a token of `stops` (`;`, `<;>`, `,`, `:=`, `by`, `from`, `at`) or (before the
      first newline at depth 0) a token of `same_line_stops`: `token` is that token and
      `next` the offset just past it;
    * at a line end whose next non-blank line is indented less than `min_indent` (or
      `infix_min_indent` when the line ends with `<;>` / `<|>`): `token` is `"\\n"` and
      `next` the offset of that next line's first character;
    * at a bracket that closes one opened before `pos` (`token` `")"`), at the end of the
      text, or after `_ADV_SCAN_LIMIT` characters (`token` `""`): `next` is `-1`.
    """
    depth = 0
    crossed_nl = False
    inf_min = min_indent if infix_min_indent is None else infix_min_indent
    hard_end = pos + _ADV_SCAN_LIMIT
    if hard_end > n:
        hard_end = n
    res = _advisory_regexes()
    next_line = res.next_line
    for m in res.step_token.finditer(stripped, pos, hard_end):
        tok = m.group()
        first = tok[0]
        if first in ("«", "'"):
            continue
        if first in "([{⟨":
            depth += 1
        elif first in ")]}⟩":
            if depth == 0:
                return m.start(), ")", -1
            depth -= 1
        elif depth:
            continue
        elif first == "\n":
            line = next_line.match(stripped, m.end())
            k = line.end()
            if k >= n:
                return n, "", -1
            nxt_indent = k - line.start(1)
            req_indent = min_indent
            if inf_min < min_indent and nxt_indent >= inf_min:
                e = m.start() - 1
                while e >= pos and stripped[e] in " \t\r":
                    e -= 1
                if (
                    e >= pos + 2
                    and stripped[e - 2 : e + 1] in ("<;>", "<|>")
                    and not lean_lexer._inside_guillemets(stripped, e)
                ):
                    req_indent = inf_min
            if nxt_indent < req_indent:
                return m.start(), "\n", k
            crossed_nl = True
        elif tok in stops or (not crossed_nl and tok in same_line_stops):
            return m.start(), tok, m.end()
    return hard_end, "", -1


def _adv_scan_at_locations(
    stripped: str, at_end: int, n: int, rw_col: int, *, stop_before_using: bool = False
) -> tuple[list[str], int]:
    """Scan the location list following `at` (ending at `at_end`), crossing blank/comment
    tails and CRLF line breaks into lines indented strictly past `rw_col`. Returns
    `(locations, stop_offset)` stopping before tactic/clause keywords."""
    res = _advisory_regexes()
    location = res.location
    next_line = res.next_line
    locs: list[str] = []
    k = at_end
    while True:
        m = location.match(stripped, k)
        if m is not None:
            tok = m.group(1)
            if (stop_before_using and tok == "using") or tok in _ADV_LOC_STOP_WORDS:
                return locs, m.start(1)
            locs.append(tok)
            k = m.end()
            continue
        k_eol = k
        while k_eol < n and stripped[k_eol] in " \t\r":
            k_eol += 1
        if k_eol < n and stripped[k_eol] == "\n":
            line = next_line.match(stripped, k_eol + 1)
            nxt_k = line.end()
            if nxt_k < n and nxt_k - line.start(1) > rw_col:
                m = location.match(stripped, nxt_k)
                if m is not None:
                    tok = m.group(1)
                    if (stop_before_using and tok == "using") or tok in _ADV_LOC_STOP_WORDS:
                        return locs, m.start(1)
                    locs.append(tok)
                    k = m.end()
                    continue
        return locs, k


def _bracket_unfolds_advance_stmt(bracket_text: str) -> bool:
    """True when `dsimp only [<bracket_text>]` actually unfolds `advanceStmt` (or a
    qualified / `.eq_def` form), excluding erasures `-advanceStmt`, reverse rewrites
    `← advanceStmt`, unrelated `advanceStmt_*` lemmas, guillemet names, or argument
    occurrences."""
    if "advanceStmt" not in bracket_text:
        return False
    has_gui = "«" in bracket_text
    for m in _advisory_regexes().advance_stmt_sym.finditer(bracket_text):
        if has_gui and lean_lexer._inside_guillemets(bracket_text, m.start()):
            continue
        if _is_simp_unfold_entry(bracket_text, m.start(), m.end()):
            return True
    return False


def _parse_simp_call(
    stripped: str, s_idx: int, n: int, has_guillemets: bool = False
) -> tuple[str, bool, int, int, bool, str, tuple[str, ...] | None, int] | None:
    """`(tactic_kind, is_dsimp, args_start, end, has_only, bracket_text, at_locs, using_pos)`
    of the simp-family call whose `simp` is at `s_idx` (`dsimp`, `simp`, `simp?`, `simp!`,
    `simpa`, `simpa ? !`, `simp_all`, `simp_arith`, `simp_rw`, ...), or `None` when `simp`
    is only part of a longer name (`foo.simp`, `simp_wf`, `my_simp`, `«simp»`). `args_start`
    is the offset immediately past the tactic head and any `?`/`!` marks; `using_pos` is the
    offset of `simpa`'s `using` keyword or `-1`.

    `stripped[s_idx:end]` covers named argument groups (`(config := ...)`, `(disch := ...)`),
    `+opt` / `-opt`, `only`, the `[...]` lemma list, optional `at <locs>`, and (for `simpa`)
    the `using` term.
    """
    if has_guillemets and lean_lexer._inside_guillemets(stripped, s_idx):
        return None
    is_dsimp = False
    if s_idx > 0:
        before = stripped[s_idx - 1]
        if before == "d":
            if s_idx > 1 and (_is_ident_char(stripped[s_idx - 2]) or stripped[s_idx - 2] in ".«"):
                return None
            is_dsimp = True
        elif _is_ident_char(before) or before in ".«":
            return None
    cur = s_idx + 4
    variant = ""
    if not is_dsimp:
        for cand in _SIMP_VARIANT_TUPLE:
            if stripped.startswith(cand, cur):
                variant = cand
                cur += len(cand)
                break
    marks_start = cur
    while cur < n and cur - marks_start < 2 and stripped[cur] in "!?":
        cur += 1
    if cur < n and (_is_ident_char(stripped[cur]) or stripped[cur] in ".»"):
        return None
    marks = stripped[marks_start:cur]
    # Allow same-line whitespace-separated `?` / `!` marks (e.g. `simpa ? !`, `simp !`).
    while len(marks) < 2:
        k_mark = cur
        while k_mark < n and stripped[k_mark] in " \t":
            k_mark += 1
        if k_mark >= n or stripped[k_mark] not in "!?":
            break
        m_end = k_mark
        while m_end < n and len(marks) + (m_end - k_mark) < 2 and stripped[m_end] in "!?":
            m_end += 1
        if m_end < n and (_is_ident_char(stripped[m_end]) or stripped[m_end] in ".«»"):
            break
        marks += stripped[k_mark:m_end]
        cur = m_end
    args_start = cur
    tactic_kind = ("d" if is_dsimp else "") + "simp" + variant + marks

    res = _advisory_regexes()
    end = cur
    has_only = False
    bracket_text = ""
    while True:
        k = _adv_skip_ws(stripped, end, n)
        if k >= n:
            break
        ch = stripped[k]
        if ch == "[":
            close = _adv_match_close(stripped, k, n)
            if close != -1:
                bracket_text = stripped[k + 1 : close]
                end = close + 1
            break  # the lemma list is the last argument before `at` / `using`
        if ch == "(":
            if res.config_item.match(stripped, k) is None:
                break  # a parenthesised tactic or term, not an argument of this call
            close = _adv_match_close(stripped, k, n)
            if close == -1:
                break
            end = close + 1
        elif _adv_word_at(stripped, k, "only", n):
            has_only = True
            end = k + 4
        elif ch in "+-" and k + 1 < n and (stripped[k + 1].isalpha() or stripped[k + 1] == "_"):
            k += 2
            while k < n and (_is_ident_char(stripped[k]) or stripped[k] == "."):
                k += 1
            end = k
        else:
            break
    step_col = _adv_step_col(stripped, s_idx)
    at_locs: tuple[str, ...] | None = None
    using_pos = -1
    k = _adv_skip_ws(stripped, end, n)
    if _adv_word_at(stripped, k, "at", n):
        scanned_locs, k_after_at = _adv_scan_at_locations(
            stripped, k + 2, n, step_col, stop_before_using=(variant == "a")
        )
        at_locs = tuple(scanned_locs)
        end = k_after_at
    if variant == "a":
        k = _adv_skip_ws(stripped, end, n)
        if _adv_word_at(stripped, k, "using", n):
            using_pos = k
            end = _adv_scan_to(stripped, k + 5, n, step_col + 1, _ADV_USING_STOPS)[0]
    return tactic_kind, is_dsimp, args_start, end, has_only, bracket_text, at_locs, using_pos


def _advance_stmt_projection_chains(
    stripped: str, has_guillemets: bool = False
) -> list[tuple[int, int, str]]:
    """`(start, end, symbol)` of every uncollapsed `(advanceStmt ...)` projection chain in
    comment- and string-blanked code: `stripped[start:end]` runs from the opening
    parenthesis through the last projection, and `symbol` is the chain with the arguments
    elided (`(advanceStmt ...).memory.locals`).

    A chain is a parenthesised application whose head is `advanceStmt` (optionally
    qualified, `Mir.advanceStmt`, or explicit, `@advanceStmt`; redundant outer parentheses
    allowed) immediately followed by two or more projections. `(advanceStmt ...).memory`
    alone, `advanceStmt'`, `advanceStmt_spec`, `advanceStmt.eq_1` and applications in which
    `advanceStmt` is only an argument (`(f (advanceStmt s l)).memory.locals`) are not.
    """
    n = len(stripped)
    find = stripped.find
    projection = _advisory_regexes().projection
    chains: list[tuple[int, int, str]] = []
    pos = find("advanceStmt")
    while pos != -1:
        after = pos + 11
        if (
            (has_guillemets and lean_lexer._inside_guillemets(stripped, pos))
            or (after < n and (_is_ident_char(stripped[after]) or stripped[after] in ".»"))
        ):
            pos = find("advanceStmt", after)
            continue
        j = pos
        if j > 0 and stripped[j - 1] != "." and (_is_ident_char(stripped[j - 1]) or stripped[j - 1] == "«"):
            pos = find("advanceStmt", after)
            continue
        while j > 0 and (stripped[j - 1] == "." or _is_ident_char(stripped[j - 1]) or stripped[j - 1] in "«»"):
            if stripped[j - 1] == "»":
                line_start = stripped.rfind("\n", 0, j - 1) + 1
                g_open = stripped.rfind("«", line_start, j - 1)
                if g_open == -1:
                    break
                j = g_open
            else:
                j -= 1
        name = stripped[j:after]
        if j > 0 and stripped[j - 1] == "@":
            j -= 1
        while j > 0 and stripped[j - 1] in _ADV_WS:
            j -= 1
        if j == 0 or stripped[j - 1] != "(":
            pos = find("advanceStmt", after)
            continue
        open_idx = j - 1
        close = _adv_match_close(stripped, open_idx, n)
        if close == -1:
            pos = find("advanceStmt", after)
            continue
        while True:  # redundant parentheses: `((advanceStmt ...)).memory.locals`
            outer_close = _adv_skip_ws(stripped, close + 1, n)
            if outer_close >= n or stripped[outer_close] != ")":
                break
            b = open_idx
            while b > 0 and stripped[b - 1] in _ADV_WS:
                b -= 1
            if b == 0 or stripped[b - 1] != "(":
                break
            open_idx = b - 1
            close = outer_close
        k = close + 1
        levels = 0
        while True:
            m = projection.match(stripped, k)
            if m is None:
                break
            levels += 1
            k = m.end()
        if levels >= 2:
            chains.append((open_idx, k, f"({name} ...){stripped[close + 1 : k]}"))
        pos = find("advanceStmt", after)
    return chains


def _enclosing_simp_call(
    stripped: str, a: int, b: int, n: int, has_guillemets: bool = False
) -> tuple[str, bool] | None:
    """`(tactic_kind, is_dsimp)` of the innermost simp-family call whose arguments contain
    `stripped[a:b]`, or `None`."""
    lo = a - _ADV_BACK_WINDOW if a > _ADV_BACK_WINDOW else 0
    s = stripped.rfind("simp", lo, a)
    calls = 0
    while s != -1 and calls < _ADV_MAX_SIMP_CANDIDATES:
        call = _parse_simp_call(stripped, s, n, has_guillemets)
        if call is not None:
            if call[3] >= b:
                return call[0], call[1]
            calls += 1
        s = stripped.rfind("simp", lo, s)
    return None


def _call_mentions_ident(args_slice: str, ident: str, *, using_rel: int = -1) -> bool:
    """True when `args_slice` (after the simp tactic head) references `ident` positively,
    allowing projections (`h.symm`, `h.1`) while excluding qualified names (`Foo.h`,
    `Foo.«h»`), pre-bracket `only` / config flags (`-zeta`, `+zeta`), named config/field
    assignments (`zeta := false`), and simp erasures (`[-h]`). `using_rel` is the offset in
    `args_slice` right past `simpa`'s `using` keyword, or `-1`."""
    if not ident:
        return False
    is_gui = ident[0] == "«"
    klen = len(ident)
    n_sl = len(args_slice)
    has_gui = "«" in args_slice
    pos = args_slice.find(ident)
    while pos != -1:
        end = pos + klen
        valid_before = pos == 0 or not (
            _is_ident_char(args_slice[pos - 1]) or args_slice[pos - 1] in ".«»"
        )
        valid_after = end >= n_sl or not (
            _is_ident_char(args_slice[end])
            or (args_slice[end] == "«" if is_gui else args_slice[end] in "«»")
        )
        if (
            valid_before
            and valid_after
            and (is_gui or not (has_gui and lean_lexer._inside_guillemets(args_slice, pos)))
        ):
            in_using = using_rel != -1 and pos >= using_rel
            if (
                ident == "only"
                and not in_using
                and "[" not in args_slice[:pos]
                and args_slice.count("(", 0, pos) <= args_slice.count(")", 0, pos)
            ):
                pos = args_slice.find(ident, end)
                continue
            f = _adv_skip_ws(args_slice, end, n_sl)
            if args_slice.startswith(":=", f) and not args_slice.startswith(":==", f):
                pos = args_slice.find(ident, end)
                continue
            if (
                not in_using
                and pos > 0
                and args_slice[pos - 1] in "+-"
                and (pos == 1 or args_slice[pos - 2] in _ADV_WS)
                and "[" not in args_slice[: pos - 1]
                and args_slice.count("(", 0, pos - 1) <= args_slice.count(")", 0, pos - 1)
            ):
                pos = args_slice.find(ident, end)
                continue
            # Ignore simp erasure entries `-h` (`[-h]` / `[..., -h]`).
            b = pos - 1
            while b >= 0 and args_slice[b] in _ADV_WS:
                b -= 1
            is_erasure = False
            if b >= 0 and args_slice[b] == "-":
                b2 = b - 1
                while b2 >= 0 and args_slice[b2] in _ADV_WS:
                    b2 -= 1
                if b2 >= 0 and args_slice[b2] in "[,":
                    is_erasure = True
            if not is_erasure:
                return True
        pos = args_slice.find(ident, end)
    return False


def _simp_step_at(
    stripped: str,
    p: int,
    n: int,
    has_guillemets: bool = False,
    *,
    targets: frozenset[str] | None = None,
) -> tuple[str, int] | None:
    """`(tactic_kind, offset)` when the tactic sequence starting at `p` reaches a non-`dsimp`
    simp-family call touching `targets` before `advanceStmt` is collapsed on `targets` by
    `dsimp`, looking through focusing bullets (`·`, `.`, `-`, `+`, `*`), `{...}` / `(...)`
    blocks, and the combinators `try` / `all_goals` / `any_goals` / `repeat` / `focus`."""
    step_prefix = _advisory_regexes().step_prefix
    rem_targets = targets
    for _ in range(8):
        if rem_targets is not None and not rem_targets:
            return None
        step_col = _adv_col(stripped, p) if 0 <= p < n else 0
        for _ in range(8):
            if p < 0 or p >= n:
                return None
            ch = stripped[p]
            if ch in "·({" or (ch in ".-+*" and p + 1 < n and stripped[p + 1] in " \t"):
                p = _adv_skip_ws(stripped, p + 1, n)
                if 0 <= p < n:
                    step_col = _adv_col(stripped, p)
                continue
            m = step_prefix.match(stripped, p)
            if m is None:
                break
            next_p = _adv_skip_ws(stripped, m.end(), n)
            if stripped.find("\n", m.end(), next_p) != -1 and 0 <= next_p < n:
                step_col = _adv_col(stripped, next_p)
            p = next_p
        if p < 0 or p >= n:
            return None
        s = p + 1 if stripped.startswith("dsimp", p) else p
        if not stripped.startswith("simp", s):
            return None
        call = _parse_simp_call(stripped, s, n, has_guillemets)
        if call is None:
            return None
        tactic_kind, is_dsimp, args_start, call_end, _, bracket_text, at_locs, using_pos = call
        has_star = at_locs is not None and "*" in at_locs
        loc_set = (
            frozenset(("⊢",))
            if not at_locs
            else frozenset("⊢" if l in _ADV_TURNSTILES else l for l in at_locs)
        )
        if not is_dsimp:
            if rem_targets is None or has_star or tactic_kind.startswith("simp_all"):
                return tactic_kind, s
            if rem_targets & loc_set:
                return tactic_kind, s
            args_slice = stripped[args_start:call_end]
            using_rel = using_pos + 5 - args_start if using_pos != -1 else -1
            for hyp in rem_targets:
                if hyp != "⊢" and (
                    _call_mentions_ident(args_slice, hyp, using_rel=using_rel)
                    or (hyp == "this" and tactic_kind.startswith("simpa") and using_pos == -1)
                ):
                    return tactic_kind, s
        else:
            # `advanceStmt` is a plain `def` (neither `@[simp]` nor `@[reducible]`), so
            # bare `dsimp`, `dsimp [unrelatedDef]`, and `dsimp [-advanceStmt]` leave it
            # uncollapsed; only an explicit `advanceStmt` unfold entry collapses it.
            if _bracket_unfolds_advance_stmt(bracket_text):
                if rem_targets is None or has_star:
                    return None
                rem_targets = rem_targets - loc_set
                if not rem_targets:
                    return None
        _, tok, nxt = _adv_scan_to(stripped, call_end, n, step_col + 1, _ADV_STEP_STOPS)
        if tok in (";", "<;>"):
            p = _adv_skip_ws(stripped, nxt, n)
        elif tok == "\n" and _adv_col(stripped, nxt) == step_col:
            p = nxt
        else:
            return None
    return None


def _extract_statement_bound_hyp(stripped: str, kw_end: int, stmt_end: int) -> str | None:
    """Identifier bound by `have [h] [binders...] : ...` / `suffices [h] [binders...] : ...`,
    or `None` when destructured (e.g. `have ⟨a, b⟩ : ...`)."""
    n = len(stripped)
    q = _adv_skip_ws(stripped, kw_end, stmt_end)
    if q >= stmt_end:
        return None
    ident: str | None = None
    if stripped[q] == ":" and stripped[q : q + 2] != ":=":
        return "this"
    if stripped[q] in "({[":
        ident = "this"
        after = q
    else:
        m = _advisory_regexes().location.match(stripped, q)
        if m is None:
            return None
        cand = m.group(1)
        if cand in _ADV_TURNSTILES or cand == "*" or cand in _ADV_LOC_STOP_WORDS:
            return None
        ident = cand
        after = _adv_skip_ws(stripped, m.end(), stmt_end + 2)
    while after < stmt_end and stripped[after] in "({[":
        close = _adv_match_close(stripped, after, n)
        if close == -1 or close >= stmt_end:
            return None
        after = _adv_skip_ws(stripped, close + 1, stmt_end + 2)
    if after < n and stripped[after] == ":" and stripped[after : after + 2] != ":=":
        return ident
    return None


def _statement_seq_col(stripped: str, kw_pos: int, col: int) -> int:
    """When `statement_kw` at `kw_pos` immediately follows a top-level `;` or `<;>` tactic
    separator on the same line (e.g. `  intro h; change <chain>\\n  simp` or
    `  have h0 := 1; change <chain>\\n  simp`), return the tactic sequence's column so a
    dedented sibling tactic at that column is checked too."""
    line_start = stripped.rfind("\n", 0, kw_pos) + 1
    if ";" not in stripped[line_start:kw_pos]:
        return col
    b = kw_pos - 1
    while b >= line_start and stripped[b] in " \t":
        b -= 1
    if b < line_start or not (
        stripped[b] == ";" or (b >= line_start + 2 and stripped[b - 2 : b + 1] == "<;>")
    ):
        return col
    depth = 0
    saw_semi = False
    saw_term_arrow_src = False
    arm_arrow_end = -1
    for m in _advisory_regexes().step_token.finditer(stripped, line_start, kw_pos):
        tok = m.group()
        ch = tok[0]
        if ch in ("«", "'"):
            continue
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            if depth == 0:
                return col
            depth -= 1
        elif depth == 0:
            if tok == "by":
                # A `;` after an unparenthesised `by` stays inside that `by` block rather
                # than continuing the enclosing line's tactic sequence.
                return col
            if tok in (":=", "fun", "λ"):
                saw_term_arrow_src = True
            elif tok in (";", "<;>"):
                saw_semi = True
                saw_term_arrow_src = False
            elif tok == "=>" and not saw_semi and not saw_term_arrow_src:
                arm_arrow_end = m.end()
    if depth != 0:
        return col
    if arm_arrow_end != -1:
        k = arm_arrow_end
        while k < kw_pos:
            ch = stripped[k]
            if ch in " \t·":
                k += 1
            elif ch in ".-+*" and k + 1 < kw_pos and stripped[k + 1] in " \t":
                k += 1
            else:
                break
        return k - line_start
    return _adv_step_col(stripped, kw_pos)


_TERM_LINE_END_WORDS = frozenset(
    ("from", "exact", "apply", "refine", "return", "fun", "λ", "show", "change")
)


def _prev_line_ends_term_prefix(stripped: str, line_start: int) -> bool:
    """True when the preceding non-blank line ends with `:=` / `=` / `←` / `→` or a
    term-introducing keyword so a leading `(...)` on `line_start` continues a term."""
    cur = line_start - 1
    while cur >= 0 and stripped[cur] in " \t\r\n":
        cur -= 1
    if cur < 0:
        return False
    prev_start = stripped.rfind("\n", 0, cur) + 1
    ch = stripped[cur]
    if ch in ":=←→+*,":
        return True
    if ch == "-" and (cur == prev_start or stripped[cur - 1] != "|"):
        return True
    if _is_ident_char(ch) or ch == "λ":
        w = cur
        while w > prev_start and _is_ident_char(stripped[w - 1]):
            w -= 1
        if stripped[w : cur + 1] in _TERM_LINE_END_WORDS:
            return True
    return False


def _enclosing_tactic_paren_col(stripped: str, kw_pos: int, col: int) -> int:
    """When `statement_kw` at `kw_pos` is directly wrapped in a tactic-position `(` on the
    same line (`  (suffices ... by ...)` or `  (change ...)`), return the enclosing step's
    column, else `-1`."""
    line_start = stripped.rfind("\n", 0, kw_pos) + 1
    b = kw_pos - 1
    while b >= line_start and stripped[b] in " \t":
        b -= 1
    if b < line_start or stripped[b] != "(":
        return -1
    b_col = b - line_start
    step_c = _adv_step_col(stripped, b)
    if b_col == step_c:
        if _prev_line_ends_term_prefix(stripped, line_start):
            return -1
        return step_c
    seq_c = _statement_seq_col(stripped, b, b_col)
    return seq_c if seq_c != b_col else -1


def _simp_after_statement(
    stripped: str, a: int, b: int, n: int, has_guillemets: bool = False
) -> tuple[str, int, str, int] | None:
    """`(statement_keyword, keyword_offset, tactic_kind, simp_offset)` when `stripped[a:b]`
    lies in the statement of a `change` / `show` / `have` / `suffices` and the following
    tactic sequence simplifies the affected target before `advanceStmt` is collapsed."""
    lo = a - _ADV_STATEMENT_WINDOW if a > _ADV_STATEMENT_WINDOW else 0
    rfind = stripped.rfind
    nearest = [(rfind(kw, lo, a), kw) for kw in _ADV_STATEMENT_KEYWORDS]
    examined = 0
    while examined < _ADV_MAX_STATEMENT_CANDIDATES:
        kw_pos, statement_kw = max(nearest)
        if kw_pos == -1:
            return None
        nearest[nearest.index((kw_pos, statement_kw))] = (
            rfind(statement_kw, lo, kw_pos),
            statement_kw,
        )
        if has_guillemets and lean_lexer._inside_guillemets(stripped, kw_pos):
            continue
        kw_end = kw_pos + len(statement_kw)
        if kw_pos > 0 and (_is_ident_char(stripped[kw_pos - 1]) or stripped[kw_pos - 1] in ".«"):
            continue  # `h.show`, `behave`, `«show»`
        if _is_ident_char(stripped[kw_end]) or stripped[kw_end] in ".»":
            continue  # `have'`, `showFoo` (`kw_end < a <= n`, so the index is valid)
        examined += 1
        col = _adv_col(stripped, kw_pos)
        seq_col = _statement_seq_col(stripped, kw_pos, col)
        min_col = seq_col if seq_col < col else col
        end, tok, nxt = _adv_scan_to(stripped, kw_end, n, min_col + 1, _ADV_STATEMENT_STOPS)
        if end < b:
            continue  # this statement ends before the chain does: try an enclosing one
        step_end = end
        targets: frozenset[str] | None = None
        if statement_kw in ("change", "show"):
            targets = frozenset(("⊢",))
        p = -1
        entered_own_by = False
        if tok in (":=", "from", "by"):
            p = _adv_skip_ws(stripped, nxt, n)
            if tok == "by":
                entered_own_by = True
            elif _adv_word_at(stripped, p, "by", n):
                p = _adv_skip_ws(stripped, p + 2, n)
                entered_own_by = True
            else:
                step_end, tok, nxt = _adv_scan_to(stripped, p, n, min_col + 1, _ADV_STEP_STOPS)
                p = -1
        elif tok == "at":
            c_locs, after_at = _adv_scan_at_locations(stripped, nxt, n, min_col)
            if c_locs and "*" not in c_locs:
                targets = frozenset("⊢" if l in _ADV_TURNSTILES else l for l in c_locs)
            else:
                targets = None
            step_end, tok, nxt = _adv_scan_to(stripped, after_at, n, min_col + 1, _ADV_STEP_STOPS)
        if statement_kw == "have":
            if entered_own_by:
                targets = frozenset(("⊢",))
            else:
                hyp = _extract_statement_bound_hyp(stripped, kw_end, end)
                targets = frozenset((hyp,)) if hyp is not None else None
        elif statement_kw == "suffices":
            if entered_own_by:
                hyp = _extract_statement_bound_hyp(stripped, kw_end, end)
                targets = frozenset((hyp,)) if hyp is not None else None
            else:
                targets = frozenset(("⊢",))
        if p == -1:
            if tok in (";", "<;>"):
                p = _adv_skip_ws(stripped, nxt, n)
            elif tok == "\n" and _adv_col(stripped, nxt) in (col, seq_col):
                p = nxt
            elif tok == ")" and step_end < n and stripped[step_end] == ")":
                wrap_col = _enclosing_tactic_paren_col(stripped, kw_pos, col)
                if wrap_col != -1:
                    _, tok_w, nxt_w = _adv_scan_to(
                        stripped, step_end + 1, n, wrap_col + 1, _ADV_STEP_STOPS
                    )
                    if tok_w in (";", "<;>"):
                        p = _adv_skip_ws(stripped, nxt_w, n)
                    elif tok_w == "\n" and _adv_col(stripped, nxt_w) in (col, seq_col, wrap_col):
                        p = nxt_w
        step = (
            _simp_step_at(stripped, p, n, has_guillemets, targets=targets)
            if p != -1
            else None
        )
        if step is None and statement_kw == "suffices" and entered_own_by and p != -1:
            post_p = -1
            if stripped[p] in "({":
                close_grp = _adv_match_close(stripped, p, n)
                if close_grp != -1:
                    _, tok2, nxt2 = _adv_scan_to(
                        stripped, close_grp + 1, n, min_col + 1, _ADV_STEP_STOPS
                    )
                    if tok2 in (";", "<;>"):
                        post_p = _adv_skip_ws(stripped, nxt2, n)
                    elif tok2 == "\n" and _adv_col(stripped, nxt2) in (col, seq_col):
                        post_p = nxt2
            elif _adv_col(stripped, p) > min_col:
                end2, tok2, nxt2 = _adv_scan_to(stripped, p, n, min_col + 1, _ADV_NO_STOPS)
                if tok2 == "\n" and _adv_col(stripped, nxt2) in (col, seq_col):
                    post_p = nxt2
                elif tok2 == ")" and end2 < n and stripped[end2] == ")":
                    wrap_col = _enclosing_tactic_paren_col(stripped, kw_pos, col)
                    if wrap_col != -1:
                        _, tok3, nxt3 = _adv_scan_to(
                            stripped, end2 + 1, n, wrap_col + 1, _ADV_STEP_STOPS
                        )
                        if tok3 in (";", "<;>"):
                            post_p = _adv_skip_ws(stripped, nxt3, n)
                        elif tok3 == "\n" and _adv_col(stripped, nxt3) in (
                            col,
                            seq_col,
                            wrap_col,
                        ):
                            post_p = nxt3
            if post_p != -1:
                step = _simp_step_at(
                    stripped, post_p, n, has_guillemets, targets=frozenset(("⊢",))
                )
        if step is None:
            continue  # inner term/statement did not lead to `simp`: try an enclosing one
        return statement_kw, kw_pos, step[0], step[1]
    return None


def _is_in_first_arm(stripped: str, line_start: int, t: int) -> bool:
    """True when `try` at `t` sits inside an inline `first | ...` arm at the same bracket
    depth on the current line, so a following standalone `|` begins the next `first`
    alternative rather than continuing `try`."""
    if stripped.find("|", line_start, t) == -1:
        return False
    group_start = line_start
    open_stack: list[int] = []
    # Per-depth state `[active_first_arm, in_fun_binder]`.
    state_by_depth: dict[int, list[bool]] = {0: [False, False]}
    for m in _advisory_regexes().step_token.finditer(stripped, line_start, t):
        tok = m.group()
        ch = tok[0]
        if ch in ("«", "'"):
            continue
        if ch in "([{⟨":
            open_stack.append(m.end())
            state_by_depth[len(open_stack)] = [False, False]
        elif ch in ")]}⟩":
            if open_stack:
                state_by_depth.pop(len(open_stack), None)
                open_stack.pop()
            else:
                group_start = m.end()
                state_by_depth[0] = [False, False]
        else:
            d = len(open_stack)
            g_lo = open_stack[-1] if d > 0 else group_start
            st = state_by_depth.setdefault(d, [False, False])
            if tok in ("fun", "λ"):
                st[1] = True
            elif tok in (";", "<;>"):
                st[1] = False
            elif tok == "=>":
                if st[1]:
                    st[1] = False
                else:
                    st[0] = False
            elif tok == "|":
                st[1] = False
                p_pos = m.start()
                b = p_pos - 1
                while b >= g_lo and stripped[b] in " \t":
                    b -= 1
                if b < g_lo and d == 0:
                    st[0] = True
                elif b >= g_lo + 4 and stripped[b - 4 : b + 1] == "first":
                    before_f = b - 5
                    if before_f < 0 or not (
                        _is_ident_char(stripped[before_f]) or stripped[before_f] in ".«"
                    ):
                        st[0] = True
    return state_by_depth.get(len(open_stack), [False, False])[0]


def _is_non_tactic_try(stripped: str, t: int) -> bool:
    """True when `try` at `t` sits immediately after a term-position operator or keyword
    on the same line (e.g. `have _ := try (by ...)`), so it is a term rather than the
    `try` tactic. Line-leading `-`, `+`, `*` are focusing bullets, not binary operators."""
    line_start = stripped.rfind("\n", 0, t) + 1
    b = t - 1
    while b >= line_start and stripped[b] in " \t":
        b -= 1
    if b < line_start:
        return False
    ch = stripped[b]
    if ch in _ADV_NON_TACTIC_BEFORE_TRY_CHARS:
        if ch in "-+*" and all(c in " \t" for c in stripped[line_start:b]):
            return False
        return True
    if _is_ident_char(ch) or ch == "λ":
        w_start = b
        while w_start > line_start and _is_ident_char(stripped[w_start - 1]):
            w_start -= 1
        if stripped[w_start : b + 1] in _ADV_NON_TACTIC_BEFORE_TRY_WORDS:
            return True
    return False


def _try_rewrite_hyp_before_target(
    stripped: str, has_guillemets: bool = False
) -> list[tuple[int, str, tuple[str, ...]]]:
    """`(at_offset, rewrite_tactic, locations)` for every `rw` / `erw` / `rewrite` / `rwa`
    under a `try` whose location list names a hypothesis before the goal (`⊢` or `|-`).

    Every rewrite of the `try`'s tactic sequence counts, since a failure anywhere in the
    sequence rolls all of it back: the tactic right after `try` (through `(` / `{` or
    combinators such as `all_goals`), later steps after `;` / `<;>`, and the steps of a
    parenthesised or indented block.
    """
    res = _advisory_regexes()
    n = len(stripped)
    find = stripped.find
    rw_head = res.rw_head
    config_item = res.config_item
    flat_line = res.flat_line
    next_line = res.next_line
    hits: list[tuple[int, str, tuple[str, ...]]] = []
    seen: set[int] = set()

    def consider(head: re.Match[str]) -> None:
        h_pos = head.start()
        if h_pos in seen:
            return
        seen.add(h_pos)
        if has_guillemets and lean_lexer._inside_guillemets(stripped, h_pos):
            return
        k = _adv_skip_ws(stripped, head.end(), n)
        while k < n:
            ch = stripped[k]
            if ch == "(":
                if config_item.match(stripped, k) is None:
                    return
                close = _adv_match_close(stripped, k, n)
                if close == -1:
                    return
                k = _adv_skip_ws(stripped, close + 1, n)
            elif ch in "+-" and k + 1 < n and (stripped[k + 1].isalpha() or stripped[k + 1] == "_"):
                k += 2
                while k < n and (_is_ident_char(stripped[k]) or stripped[k] == "."):
                    k += 1
                k = _adv_skip_ws(stripped, k, n)
            else:
                break
        if k >= n or stripped[k] != "[":
            return
        close = _adv_match_close(stripped, k, n)
        if close == -1:
            return
        at_pos = _adv_skip_ws(stripped, close + 1, n)
        if not _adv_word_at(stripped, at_pos, "at", n):
            return
        rw_col = _adv_step_col(stripped, h_pos)
        locs, _ = _adv_scan_at_locations(stripped, at_pos + 2, n, rw_col)
        for i, loc in enumerate(locs):
            if loc in _ADV_TURNSTILES:
                if any(prev != "*" for prev in locs[:i]):
                    hits.append((at_pos, head.group(1), tuple(locs)))
                return

    after_try = 0
    while True:
        t = find("try", after_try)
        if t == -1:
            break
        after_try = t + 3
        if t > 0 and (_is_ident_char(stripped[t - 1]) or stripped[t - 1] in ".«"):
            continue  # `h.try`, `retry`, `«try»`
        if after_try < n and (_is_ident_char(stripped[after_try]) or stripped[after_try] in ".»"):
            continue  # `try?`, `tryFoo`
        if has_guillemets and lean_lexer._inside_guillemets(stripped, t):
            continue
        if _is_non_tactic_try(stripped, t):
            continue
        try_col = _adv_step_col(stripped, t)
        t_col = _adv_col(stripped, t)
        first = _adv_skip_ws(stripped, after_try, n)
        if first >= n or stripped[first] in ":)]}⟩,=":
            continue
        has_nl_after_try = find("\n", after_try, first) != -1
        first_col = _adv_col(stripped, first)
        if has_nl_after_try and first_col <= try_col:
            if stripped[first] in "({":
                close = _adv_match_close(stripped, first, n)
                scope_end = close if close != -1 else min(n, first + _ADV_SCAN_LIMIT)
            else:
                continue  # `try` with no indented tactic block before a sibling step
        else:
            # Only treat a subsequent standalone `|` as ending `try`'s scope when `try`
            # itself sits inside an inline `first | ...` arm; otherwise `|` inside `try`
            # belongs to a nested `cases` / `match` / `first` / `rcases` tactic.
            line_start = stripped.rfind("\n", 0, t) + 1
            in_first_arm = _is_in_first_arm(stripped, line_start, t)
            same_line_stops = (
                _ADV_TRY_STOPS if (in_first_arm and not has_nl_after_try) else _ADV_NO_STOPS
            )
            min_indent = first_col if has_nl_after_try else min(first_col, t_col + 1)
            infix_min = min(min_indent, try_col + 1)
            if not has_nl_after_try and not in_first_arm and stripped[first] not in "({":
                flat = flat_line.match(stripped, first)
                if flat is not None:
                    flat_end = flat.end()
                    line = next_line.match(stripped, flat_end + 1) if flat_end < n else None
                    nxt_ind = (
                        -1
                        if (line is None or line.end() >= n)
                        else line.end() - line.start(1)
                    )
                    if nxt_ind < infix_min or (
                        nxt_ind < min_indent
                        and not stripped[first:flat_end].rstrip(" \t\r").endswith("<|>")
                    ):
                        if find("w", first, flat_end) != -1:
                            for head in rw_head.finditer(stripped, first, flat_end):
                                consider(head)
                        continue
            scope_end = _adv_scan_to(
                stripped,
                first,
                n,
                min_indent,
                _ADV_NO_STOPS,
                same_line_stops=same_line_stops,
                infix_min_indent=infix_min,
            )[0]
        if find("w", first, scope_end) != -1:
            for head in rw_head.finditer(stripped, first, scope_end):
                consider(head)
    return hits


def scan_projection_and_rewrite_order_hazards(
    text: str, *, stripped: str | None = None
) -> list[ProofHealthFinding]:
    """Advisory findings (`ADVISORY_RULES`) for two proof-scaling traps, sorted by line.

    Purely structural and fast (no Lean process); comments, strings and guillemet names
    never match. Pass `stripped` when `strip_lean_comments_and_strings(text)` is already
    at hand (a value of the wrong length is ignored and the text is lexed again).

    `simp_deep_projection_chain` (`leanprover/lean4#16532`). Until the toolchain carries the
    fix, `Simp.simpProj` builds and typechecks a `fun s => e = s.i` motive at every level of
    an uncollapsed projection chain. A chain is `(advanceStmt ...)` followed directly by two
    or more projections, e.g. `(advanceStmt s locals mem).memory.locals` or
    `(advanceStmt s locals).frame.stmtIdx` (see `_advance_stmt_projection_chains`). It is
    reported in two situations, never for `dsimp` (definitional unfolding builds no motive):

    * sub-rule `projection_in_simp_arguments`, at the chain's line: the chain is written
      inside a `simp` / `simp only` / `simp?` / `simpa` / `simp_all` / `simp_arith` /
      `simp_rw` call, that is in its `[...]` lemma list, a `(config := ...)` /
      `(disch := ...)` argument, or the term after `simpa ... using`. The innermost
      enclosing simp-family call decides, so a chain inside `dsimp only [...]` is exempt.
    * sub-rule `simp_after_projection_statement`, at the `simp` call's line: a `change`,
      `show`, `have` or `suffices` states the chain and the first tactic step after the
      statement is such a call (or follows a `dsimp only [...]` step that omitted
      `advanceStmt`; see `_simp_after_statement`), so `simp` meets the chain in the goal or
      hypothesis just introduced. A `dsimp only [advanceStmt, ...]` step in between
      collapses the chain first and silences the finding.

    `try_rw_hyp_before_target`, at the line of the `at` clause: `try rw [...] at h ⊢`
    (also `erw`, `rewrite`, `rwa`; `|-` for `⊢`; any rewrite in the `try`'s sequence or
    block) lists a hypothesis before the goal. `rw` then runs `kabstract` over the
    hypotheses first, and when the goal rewrite fails `try` rolls that work back. Not
    reported: the goal first (`at ⊢ h`), no goal (`at h`), `at *`, or no `try` (a plain
    `rw [...] at h ⊢` is expected to succeed everywhere).
    """
    has_chain_name = "advanceStmt" in text
    has_try = "try" in text and ("⊢" in text or "|-" in text)
    if not has_chain_name and not has_try:
        return []
    if stripped is None or len(stripped) != len(text):
        stripped = strip_lean_comments_and_strings(text)
    n = len(stripped)
    has_guillemets = "«" in stripped
    line_of = _LineCounter(stripped)
    found: dict[tuple[str, int, str, str], ProofHealthFinding] = {}

    if has_chain_name and "advanceStmt" in stripped:
        why = (
            "`Simp.simpProj` builds and typechecks a `fun s => e = s.i` motive at every "
            "projection level (leanprover/lean4#16532)."
        )
        for a, b, symbol in _advance_stmt_projection_chains(stripped, has_guillemets):
            call = _enclosing_simp_call(stripped, a, b, n, has_guillemets)
            if call is not None:
                tactic_kind, is_dsimp = call
                if is_dsimp:
                    continue
                line = line_of(a)
                found.setdefault(
                    (RULE_SIMP_DEEP_PROJECTION_CHAIN, line, symbol, SUBRULE_PROJECTION_IN_SIMP_ARGS),
                    ProofHealthFinding(
                        RULE_SIMP_DEEP_PROJECTION_CHAIN,
                        line,
                        f"Uncollapsed projection chain `{symbol}` inside `{tactic_kind}`: {why}",
                        "Collapse the projections definitionally first with "
                        f"`dsimp only [advanceStmt, ...]`, then run `{tactic_kind}` without "
                        "the chain.",
                        symbol,
                        subrule=SUBRULE_PROJECTION_IN_SIMP_ARGS,
                    ),
                )
                continue
            after = _simp_after_statement(stripped, a, b, n, has_guillemets)
            if after is None:
                continue
            statement_kw, _, tactic_kind, simp_pos = after
            line = line_of(simp_pos)
            found.setdefault(
                (
                    RULE_SIMP_DEEP_PROJECTION_CHAIN,
                    line,
                    symbol,
                    SUBRULE_SIMP_AFTER_PROJECTION_STATEMENT,
                ),
                ProofHealthFinding(
                    RULE_SIMP_DEEP_PROJECTION_CHAIN,
                    line,
                    f"`{tactic_kind}` runs right after `{statement_kw}` stated the uncollapsed "
                    f"projection chain `{symbol}`: {why}",
                    f"Insert `dsimp only [advanceStmt, ...]` between `{statement_kw}` and "
                    f"`{tactic_kind}` so the projections collapse definitionally first.",
                    symbol,
                    subrule=SUBRULE_SIMP_AFTER_PROJECTION_STATEMENT,
                ),
            )

    if has_try and "try" in stripped and ("⊢" in stripped or "|-" in stripped):
        for at_pos, rewrite_kw, locs in _try_rewrite_hyp_before_target(stripped, has_guillemets):
            line = line_of(at_pos)
            written = " ".join(locs)
            goal_at = next(i for i, loc in enumerate(locs) if loc in _ADV_TURNSTILES)
            reordered = " ".join((locs[goal_at],) + locs[:goal_at] + locs[goal_at + 1 :])
            symbol = f"try {rewrite_kw} [...] at {written}"
            found.setdefault(
                (RULE_TRY_RW_HYP_BEFORE_TARGET, line, symbol, ""),
                ProofHealthFinding(
                    RULE_TRY_RW_HYP_BEFORE_TARGET,
                    line,
                    f"`{symbol}` rewrites the hypotheses before the goal: when the rewrite "
                    f"fails on `{locs[goal_at]}`, the `kabstract` work already done at "
                    f"`{' '.join(locs[:goal_at])}` is rolled back and wasted.",
                    f"List the goal first (`at {reordered}`) so a failing goal rewrite aborts "
                    "before any hypothesis is traversed.",
                    symbol,
                ),
            )

    return sorted(found.values(), key=lambda f: (f.line, f.rule, f.symbol, f.subrule))


def default_cache_path() -> Path:
    env_path = os.environ.get("ANNEAL_PROOF_HEALTH_CACHE")
    if env_path and env_path.strip():
        return Path(env_path.strip())
    uid = getattr(os, "getuid", lambda: 0)()
    return Path(f"/tmp/anneal-proof-health-cache-{uid}.json")


def _text_crc(text: str) -> int:
    """CRC-32 of `text` (UTF-16 code units; a near-memcpy encoding for Lean source)."""
    return zlib.crc32(text.encode("utf-16-le", "surrogatepass"))


def _load_cache(cache_file: Path) -> dict[str, Any]:
    """JSON object stored at `cache_file` (per-file rule counts keyed by resolved
    path, or a sibling index); any unreadable or malformed file reads as empty."""
    try:
        if cache_file.is_file():
            data = json.loads(cache_file.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                return data
    except Exception:
        pass
    return {}


_TMP_CACHE_SEQ = 0


def _save_cache(cache_file: Path, data: dict[str, Any]) -> None:
    """Write the cache through a fresh `O_EXCL` temp file and `os.replace`, so
    concurrent hook processes/threads never read a torn file and a symlink planted at
    the cache path (e.g. in a shared `/tmp`) is replaced rather than written through."""
    global _TMP_CACHE_SEQ
    _TMP_CACHE_SEQ += 1
    tmp_path = f"{cache_file}.{os.getpid()}.{_TMP_CACHE_SEQ}.tmp"
    try:
        cache_file.parent.mkdir(parents=True, exist_ok=True)
        try:
            os.unlink(tmp_path)
        except OSError:
            pass
        fd = os.open(tmp_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump(data, fh, separators=(",", ":"))
        os.replace(tmp_path, cache_file)
    except Exception:
        try:
            os.unlink(tmp_path)
        except (OSError, ValueError):
            pass


def _extract_edit_args_list(payload: dict[str, Any] | None) -> list[dict[str, Any]]:
    if not isinstance(payload, dict):
        return []
    candidates: list[dict[str, Any]] = []
    tool_call = payload.get("toolCall")
    if isinstance(tool_call, dict) and isinstance(tool_call.get("args"), dict):
        candidates.append(tool_call["args"])
    if isinstance(payload.get("tool_input"), dict):
        candidates.append(payload["tool_input"])
    if isinstance(payload.get("args"), dict):
        candidates.append(payload["args"])
    candidates.append(payload)
    return candidates


_REPL_RESULT_RE = re.compile(
    r"\bMade\s+(\d{1,9})\s+replacements?\b"
    r"(?:[^\n]*?\bstarting at line\s+(\d{1,9})\b)?"
)


def _replacement_result_hint(payload: dict[str, Any] | None) -> tuple[int | None, int | None]:
    """Parse `(count, start_line)` from a structured `edit_file` result string if present."""
    if not isinstance(payload, dict):
        return None, None
    res = payload.get("result")
    if not isinstance(res, str) or "Made " not in res:
        return None, None
    m = _REPL_RESULT_RE.search(res)
    if m is None:
        return None, None
    cnt = int(m.group(1))
    if cnt < 1:
        return None, None
    raw_line = int(m.group(2)) if m.group(2) is not None else None
    sline = raw_line if raw_line is not None and raw_line >= 1 else None
    return cnt, sline


def _line_start_offset(text: str, one_based_line: int) -> int:
    if one_based_line <= 1:
        return 0
    off = 0
    for _ in range(one_based_line - 1):
        nl = text.find("\n", off)
        if nl == -1:
            return len(text)
        off = nl + 1
    return off


def reconstruct_before_text_from_payload(
    after_text: str,
    payload: dict[str, Any] | None,
) -> str | None:
    """Attempt to reconstruct the pre-edit file text in memory from a PostToolUse
    `edit_file` / `Edit` / `MultiEdit` payload. Returns `None` when the payload does
    not contain reversible diff pairs (e.g. `write_file` / `Write`) or when `Replacement`
    occurs multiple times and cannot be unambiguously inverted without a cache.
    """
    repl_cnt, repl_line = _replacement_result_hint(payload)
    for args in _extract_edit_args_list(payload):
        edits = args.get("edits")
        if isinstance(edits, list) and edits:
            cur = after_text
            ok = True
            for item in reversed(edits):
                if not isinstance(item, dict):
                    ok = False
                    break
                old_s = item.get("old_string", item.get("Target"))
                new_s = item.get("new_string", item.get("Replacement"))
                if not isinstance(old_s, str) or not isinstance(new_s, str):
                    ok = False
                    break
                if old_s == new_s:
                    continue
                if not new_s or new_s not in cur:
                    ok = False
                    break
                occ = cur.count(new_s)
                if occ == 1:
                    cur = cur.replace(new_s, old_s, 1)
                elif item.get("replace_all"):
                    cur = cur.replace(new_s, old_s)
                else:
                    ok = False
                    break
            if ok:
                return cur

        old_s = args.get("Target", args.get("old_string"))
        new_s = args.get("Replacement", args.get("new_string"))
        if isinstance(old_s, str) and isinstance(new_s, str):
            if old_s == new_s:
                return after_text
            if not new_s:
                return None
            occ = after_text.count(new_s)
            if occ == 1:
                return after_text.replace(new_s, old_s, 1)
            if occ > 1:
                if repl_cnt == occ or args.get("replace_all"):
                    return after_text.replace(new_s, old_s)
                if repl_cnt is not None and repl_cnt >= 1 and repl_line is not None:
                    off = _line_start_offset(after_text, repl_line)
                    idx = after_text.find(new_s, off)
                    if idx != -1 and after_text.count("\n", off, idx) == 0:
                        if repl_cnt == 1:
                            return after_text[:idx] + old_s + after_text[idx + len(new_s) :]
                        if after_text.count(new_s, idx) == repl_cnt:
                            return after_text[:idx] + after_text[idx:].replace(new_s, old_s)
                return None
    return None


def _invert_ambiguous_without_cache(
    after_text: str, payload: dict[str, Any] | None
) -> str | None:
    """Best-effort pre-edit text for rule-count baseline when no cache exists and
    `Replacement` / `new_string` occurs multiple times (or mixes a deletion step
    with an insertion step inside `MultiEdit`)."""
    repl_cnt, repl_line = _replacement_result_hint(payload)
    for args in _extract_edit_args_list(payload):
        edits = args.get("edits")
        if isinstance(edits, list) and edits:
            cur = after_text
            deleted_chunks: list[str] = []
            ok = True
            for item in reversed(edits):
                if not isinstance(item, dict):
                    ok = False
                    break
                old_s = item.get("old_string", item.get("Target"))
                new_s = item.get("new_string", item.get("Replacement"))
                if not isinstance(old_s, str) or not isinstance(new_s, str):
                    ok = False
                    break
                if old_s == new_s:
                    continue
                if not new_s:
                    deleted_chunks.append(old_s)
                    continue
                if new_s not in cur:
                    ok = False
                    break
                if item.get("replace_all"):
                    cur = cur.replace(new_s, old_s)
                else:
                    cur = cur.replace(new_s, old_s, 1)
            if ok:
                if deleted_chunks:
                    cur = cur + "\n" + "\n".join(reversed(deleted_chunks))
                return cur

        old_s = args.get("Target", args.get("old_string"))
        new_s = args.get("Replacement", args.get("new_string"))
        if isinstance(old_s, str) and isinstance(new_s, str) and new_s and new_s in after_text:
            if repl_cnt is not None and repl_cnt >= 1:
                off = _line_start_offset(after_text, repl_line) if repl_line is not None else 0
                if after_text.count(new_s, off) >= repl_cnt:
                    return after_text[:off] + after_text[off:].replace(new_s, old_s, repl_cnt)
                return after_text.replace(new_s, old_s, repl_cnt)
            if "old_string" in args and "Target" not in args and not args.get("replace_all"):
                return after_text.replace(new_s, old_s, 1)
            return after_text.replace(new_s, old_s)
    return None


def _replacement_strings(payload: dict[str, Any] | None) -> list[str]:
    """Collect every non-empty inserted string (`Replacement` / `new_string` /
    `edits[*].new_string`) carried by an edit payload."""
    out: list[str] = []
    for args in _extract_edit_args_list(payload):
        edits = args.get("edits")
        if isinstance(edits, list):
            for item in edits:
                if isinstance(item, dict):
                    new_s = item.get("new_string", item.get("Replacement"))
                    if isinstance(new_s, str) and new_s:
                        out.append(new_s)
        new_s = args.get("Replacement", args.get("new_string"))
        if isinstance(new_s, str) and new_s:
            out.append(new_s)
    return out


def _is_pure_deletion(payload: dict[str, Any] | None) -> bool:
    """True when the payload is an edit whose replacement(s) are all empty."""
    for args in _extract_edit_args_list(payload):
        edits = args.get("edits")
        if isinstance(edits, list) and edits:
            if all(
                isinstance(it, dict)
                and isinstance(it.get("old_string", it.get("Target")), str)
                and bool(it.get("old_string", it.get("Target")))
                and it.get("new_string", it.get("Replacement")) == ""
                for it in edits
            ):
                return True
        old_s = args.get("Target", args.get("old_string"))
        new_s = args.get("Replacement", args.get("new_string"))
        if isinstance(old_s, str) and old_s and isinstance(new_s, str) and not new_s:
            return True
    return False


def _write_file_args(payload: dict[str, Any] | None) -> dict[str, Any] | None:
    """Return the structured `write_file` argument dict (`Content` plus optional
    `Overwrite` / `Append` flags) carried by `payload`, if any."""
    for args in _extract_edit_args_list(payload):
        if isinstance(args.get("Content"), str) and "Target" not in args:
            return args
    return None


def _line_spans_of_insertions(
    after_text: str, inserted: list[str], payload: dict[str, Any] | None = None
) -> list[tuple[int, int]]:
    """1-based inclusive line ranges covered by inserted strings in `after_text`."""
    repl_cnt, repl_line = _replacement_result_hint(payload)
    if repl_cnt == 1 and repl_line is not None and len(inserted) == 1:
        ins = inserted[0]
        last = repl_line + ins.count("\n", 0, max(len(ins) - 1, 0))
        return [(repl_line, last)]
    spans: list[tuple[int, int]] = []
    min_off = (
        _line_start_offset(after_text, repl_line)
        if repl_line is not None and len(inserted) == 1
        else 0
    )
    for ins in inserted:
        start = after_text.find(ins, min_off)
        hits = 0
        while start != -1 and hits < 64:
            first = after_text.count("\n", 0, start) + 1
            last = first + ins.count("\n", 0, max(len(ins) - 1, 0))
            spans.append((first, last))
            hits += 1
            start = after_text.find(ins, start + max(len(ins), 1))
    return spans


def _line_text(lines: list[str], line: int) -> str:
    return lines[line - 1].strip() if 0 < line <= len(lines) else ""


def _select_new_findings(
    rule_findings: list[ProofHealthFinding],
    delta: int,
    spans: list[tuple[int, int]],
    before_rule_findings: list[ProofHealthFinding] | None,
    after_lines: list[str],
    before_lines: list[str] | None,
) -> list[ProofHealthFinding]:
    """Attribute a rule's count increase to concrete findings: occurrences inside
    the edited line window first (matching unchanged prefix/suffix lines against
    pre-existing findings before changed lines), then occurrences whose
    `(symbol, source line)` did not exist before the edit, and finally the last
    `delta` occurrences (never returning more than `delta` items)."""
    if delta <= 0:
        return []
    chosen = [f for f in rule_findings if any(a <= f.line <= b for a, b in spans)]
    if before_rule_findings is not None and before_lines is not None:
        max_pref = min(len(before_lines), len(after_lines))
        pref = 0
        while pref < max_pref and before_lines[pref] == after_lines[pref]:
            pref += 1
        max_suff = min(len(before_lines) - pref, len(after_lines) - pref)
        suff = 0
        while (
            suff < max_suff
            and before_lines[len(before_lines) - 1 - suff]
            == after_lines[len(after_lines) - 1 - suff]
        ):
            suff += 1
        diff_first = pref + 1
        diff_last = len(after_lines) - suff

        remaining: dict[tuple[str, str], int] = {}
        for f in before_rule_findings:
            key = (f.symbol, _line_text(before_lines, f.line))
            remaining[key] = remaining.get(key, 0) + 1
        unmatched_outside: list[ProofHealthFinding] = []
        unmatched_inside: list[ProofHealthFinding] = []
        for f in rule_findings:
            if f.line < diff_first or f.line > diff_last:
                key = (f.symbol, _line_text(after_lines, f.line))
                if remaining.get(key, 0) > 0:
                    remaining[key] -= 1
                else:
                    unmatched_outside.append(f)
        for f in rule_findings:
            if diff_first <= f.line <= diff_last:
                key = (f.symbol, _line_text(after_lines, f.line))
                if remaining.get(key, 0) > 0:
                    remaining[key] -= 1
                else:
                    unmatched_inside.append(f)
        unmatched = unmatched_inside + unmatched_outside
        if chosen and len(chosen) > delta:
            narrowed = [f for f in chosen if f in unmatched_inside] or [
                f for f in chosen if f in unmatched
            ]
            if narrowed:
                chosen = narrowed
        if len(chosen) < delta:
            for f in unmatched:
                if f not in chosen:
                    chosen.append(f)
                    if len(chosen) >= delta:
                        break
    if not chosen:
        chosen = rule_findings[-delta:]
    elif len(chosen) > delta:
        chosen = chosen[-delta:]
    return sorted(chosen, key=lambda f: (f.line, f.symbol))


def evaluate_post_edit_proof_health(
    target_file: str | Path,
    payload: dict[str, Any] | None = None,
    *,
    after_text: str | None = None,
    before_text: str | None = None,
    cache_path: str | Path | None = None,
    scan_siblings: bool = True,
) -> dict[str, Any]:
    """Compute delta-only proof-health diagnostics for `target_file` after an edit.

    The pre-edit text comes, in order of preference, from an explicit
    `before_text`, from Claude Code's `tool_response.originalFile`, from inverting
    the edit payload in memory (using `Made <K> replacement(s) ... starting
    at line <L>` result and Claude's `replace_all` to resolve repeated occurrences),
    or from the edit shape itself (a `write_file` that creates a new file starts from
    an empty file; a `write_file` with `Append` starts from the text before the
    appended content). Its counts are taken from the persisted per-file cache when
    the cached entry was recorded by this cache format for exactly that text (same
    length, CRC and sibling CRC/signature stamps), saving the second scan on
    consecutive edits; otherwise the text is scanned. Without a pre-edit text, the
    cached counts are the baseline, then a count-preserving inversion of repeated
    replacements. When none is available (an overwrite or a deletion of a file never
    seen before), the current counts become the baseline and no increase is claimed.
    """
    # Absolute (not symlink-resolved) path, so sibling-index keys do not depend on the
    # working directory of the hook process.
    path = Path(os.path.abspath(target_file))
    try:
        resolved_key = str(path.resolve())
    except (OSError, ValueError):
        resolved_key = str(path)

    if after_text is None:
        after_text = path.read_text(encoding="utf-8", errors="replace")

    cpath = Path(cache_path) if cache_path is not None else default_cache_path()
    cache = _load_cache(cpath)
    # Rust sources only carry rule 6 (waiver pins); everything else is Lean.
    is_rust = path.suffix == ".rs"

    # Sibling declarations only matter when the edited file has private declarations
    # after the edit (a count can only rise if they exist in `after_text`).
    sibling_decls: list[PrivateDecl] = []
    if scan_siblings and not is_rust and "private" in after_text:
        index_file = sibling_index_path(cpath, path.parent)
        sibling_index = _load_sibling_index(index_file)
        had_missing = any(not _safe_isfile(k) for k in sibling_index)
        before_ids = {k: id(v) for k, v in sibling_index.items()}
        sibling_decls = _collect_sibling_private_decls(path, persisted=sibling_index)
        if had_missing or {k: id(v) for k, v in sibling_index.items()} != before_ids:
            _save_sibling_index(index_file, sibling_index)

    def _scan(text: str) -> list[ProofHealthFinding]:
        if is_rust:
            return scan_rust_text(text, file_path=path)
        return scan_lean_text(
            text,
            file_path=path,
            scan_siblings=scan_siblings,
            sibling_decls=sibling_decls,
        )

    after_findings = _scan(after_text)
    after_counts = count_findings_by_rule(after_findings)

    cached_entry = cache.get(resolved_key)
    if not isinstance(cached_entry, dict) or cached_entry.get("_ver") != CACHE_FORMAT_VERSION:
        cached_entry = None
    # Siblings are stamped by per-file content CRC (stored in both `_SIBLING_PRIVATE_CACHE`
    # and the persisted sibling index, and refreshed on racy files) plus normalized
    # declaration headers, so even same-tick same-size sibling edits invalidate `_sib`.
    sib_parts: list[str] = []
    for sib_path in sorted({d.path for d in sibling_decls}):
        st_quad = _SIBLING_PRIVATE_CACHE.get(sib_path)
        sib_parts.append(f"{sib_path}:{st_quad[2]}" if st_quad else f"{sib_path}:?")
    sib_parts.extend(
        f"{d.path}:{d.line}:{d.kind}:{d.name}:{d.ensure_norm_sig()}" for d in sibling_decls
    )
    sib_sig = _text_crc("\n".join(sib_parts))

    def _cached_counts_for(text: str) -> dict[str, int] | None:
        """Cached counts if the entry was recorded for exactly `text`."""
        if (
            cached_entry is None
            or cached_entry.get("_len") != len(text)
            or cached_entry.get("_sib") != sib_sig
            or cached_entry.get("_crc") != _text_crc(text)
        ):
            return None
        return {rule: max(0, _safe_int(cached_entry.get(rule, 0), 0)) for rule in ALL_RULES}

    write_args = _write_file_args(payload)
    # Claude Code reports the exact pre-edit text (`tool_response.originalFile`) for
    # `Edit` / `MultiEdit`, and `type: "create"` when `Write` created the file.
    tool_response = payload.get("tool_response") if isinstance(payload, dict) else None
    if before_text is None and isinstance(tool_response, dict):
        original = tool_response.get("originalFile")
        if isinstance(original, str):
            before_text = original
        elif tool_response.get("type") == "create":
            before_text = ""
    if before_text is None and payload is not None:
        before_text = reconstruct_before_text_from_payload(after_text, payload)
    if before_text is None and write_args is not None:
        content = write_args.get("Content")
        if write_args.get("Append") and isinstance(content, str) and after_text.endswith(content):
            before_text = after_text[: len(after_text) - len(content)]
        elif not write_args.get("Overwrite") and not write_args.get("Append"):
            # `write_file` without `Overwrite` / `Append` only succeeds on a new file.
            before_text = ""

    spans: list[tuple[int, int]] = []
    before_findings: list[ProofHealthFinding] | None = None
    if before_text is not None:
        reused = _cached_counts_for(before_text)
        if reused is not None:
            before_counts = reused
        else:
            before_findings = _scan(before_text)
            before_counts = count_findings_by_rule(before_findings)
        if write_args is not None:
            first_new_line = before_text.count("\n") + 1 if before_text else 1
            spans = [(first_new_line, after_text.count("\n") + 1)]
        else:
            spans = _line_spans_of_insertions(after_text, _replacement_strings(payload), payload)
    elif cached_entry is not None:
        before_counts = {
            rule: max(0, _safe_int(cached_entry.get(rule, 0), 0)) for rule in ALL_RULES
        }
        spans = _line_spans_of_insertions(after_text, _replacement_strings(payload), payload)
    elif _is_pure_deletion(payload):
        # Deleting text cannot add an occurrence; without a cached baseline the
        # current counts become the baseline.
        before_counts = dict(after_counts)
    else:
        ambiguous_before = _invert_ambiguous_without_cache(after_text, payload)
        if ambiguous_before is not None:
            before_findings = _scan(ambiguous_before)
            before_counts = count_findings_by_rule(before_findings)
            before_text = ambiguous_before
            spans = _line_spans_of_insertions(after_text, _replacement_strings(payload), payload)
        else:
            # Unknown pre-edit state (e.g. overwriting an unseen file): record the
            # baseline without claiming any increase.
            before_counts = dict(after_counts)

    entry: dict[str, int] = dict(after_counts)
    entry["_len"] = len(after_text)
    entry["_crc"] = _text_crc(after_text)
    entry["_sib"] = sib_sig
    entry["_ver"] = CACHE_FORMAT_VERSION
    cache.pop(resolved_key, None)
    cache[resolved_key] = entry  # most recently checked last
    for stale in list(cache)[: max(0, len(cache) - COUNT_CACHE_MAX_FILES)]:
        del cache[stale]
    _save_cache(cpath, cache)

    deltas = {rule: after_counts[rule] - before_counts.get(rule, 0) for rule in ALL_RULES}
    increased_rules = [rule for rule in ALL_RULES if deltas[rule] > 0]
    if not increased_rules:
        return {
            "feedback": "",
            "deltas": deltas,
            "before_counts": before_counts,
            "after_counts": after_counts,
            "new_findings": [],
            "all_findings": after_findings,
        }

    if before_findings is None and before_text is not None:
        # Counts came from the cache; attribution may need the old occurrences.
        before_findings = _scan(before_text)
    after_lines = after_text.split("\n")
    before_lines = before_text.split("\n") if before_text is not None else None
    new_findings: list[ProofHealthFinding] = []
    lines: list[str] = [
        f"[Anneal Proof Health] New proof-scaling anti-pattern(s) introduced in `{path.name}`: "
        + ", ".join(f"{r} (+{deltas[r]})" for r in increased_rules)
    ]
    for rule in increased_rules:
        rule_findings = [f for f in after_findings if f.rule == rule]
        before_rule = (
            [f for f in before_findings if f.rule == rule] if before_findings is not None else None
        )
        shown = _select_new_findings(
            rule_findings, deltas[rule], spans, before_rule, after_lines, before_lines
        )
        new_findings.extend(shown)
        line_tags = ", ".join(f"L{f.line}" for f in shown)
        sample = shown[0]
        lines.append(
            f"- `{rule}` (+{deltas[rule]} at {line_tags}): {sample.message} "
            f"Fix: {sample.suggestion}"
        )

    return {
        "feedback": "\n".join(lines),
        "deltas": deltas,
        "before_counts": before_counts,
        "after_counts": after_counts,
        "new_findings": new_findings,
        "all_findings": after_findings,
    }


def check_post_edit_proof_health(
    target_file: str | Path,
    payload: dict[str, Any] | None = None,
    *,
    after_text: str | None = None,
    before_text: str | None = None,
    cache_path: str | Path | None = None,
    scan_siblings: bool = True,
) -> str:
    """Return a formatted `[Anneal Proof Health]` warning string if and only if at least
    one proof-health anti-pattern count strictly increased on this edit; otherwise `""`.
    """
    res = evaluate_post_edit_proof_health(
        target_file,
        payload,
        after_text=after_text,
        before_text=before_text,
        cache_path=cache_path,
        scan_siblings=scan_siblings,
    )
    return str(res["feedback"])


# ---------------------------------------------------------------------------
# Transcript Latency Telemetry (`compute_unbatched_tool_latencies`)
# ---------------------------------------------------------------------------

_CREATED_COMPLETED_RE = re.compile(
    r"Created At:\s*(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z)\s*\r?\n"
    r"Completed At:\s*(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z)"
)


def _is_finite_nonneg_number(val: Any) -> bool:
    if isinstance(val, bool) or not isinstance(val, (int, float)):
        return False
    try:
        return math.isfinite(val) and val >= 0
    except OverflowError:  # an int too large for a float
        return False


def _parse_iso_ts(ts: Any) -> float | None:
    if not isinstance(ts, bool) and isinstance(ts, (int, float)):
        try:
            return float(ts) if math.isfinite(ts) else None
        except OverflowError:  # an int too large for a float
            return None
    if not isinstance(ts, str) or not ts.strip():
        return None
    s = ts.strip()
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    try:
        return datetime.fromisoformat(s).timestamp()
    except (ValueError, OverflowError, OSError):  # naive dates near year 1 / 9999
        return None


def _first_present(obj: dict[str, Any], keys: tuple[str, ...]) -> Any:
    for k in keys:
        v = obj.get(k)
        if v is not None and v != "":
            return v
    return None


def _extract_duration_ms(obj: dict[str, Any]) -> float | None:
    for key in ("duration_ms", "latency_ms", "elapsed_ms", "time_ms"):
        val = obj.get(key)
        if _is_finite_nonneg_number(val):
            return float(val)
    for key in ("duration_s", "latency_s", "elapsed_s"):
        val = obj.get(key)
        if _is_finite_nonneg_number(val):
            ms = float(val) * 1000.0
            return ms if _is_finite_nonneg_number(ms) else None
    start_ts = _parse_iso_ts(_first_present(obj, ("started_at", "created_at", "start_time")))
    end_ts = _parse_iso_ts(_first_present(obj, ("completed_at", "finished_at", "end_time")))
    if start_ts is not None and end_ts is not None and end_ts >= start_ts:
        ms = (end_ts - start_ts) * 1000.0
        return ms if _is_finite_nonneg_number(ms) else None
    content = obj.get("content") if obj.get("content") is not None else obj.get("output")
    if isinstance(content, str) and "Created At:" in content:
        m = _CREATED_COMPLETED_RE.search(content)
        if m:
            t0 = _parse_iso_ts(m.group(1))
            t1 = _parse_iso_ts(m.group(2))
            if t0 is not None and t1 is not None and t1 >= t0:
                return (t1 - t0) * 1000.0
    return None


def _is_structured_tool_result_step(item: dict[str, Any]) -> bool:
    if item.get("source") == "SYSTEM":
        return False
    stype = item.get("type")
    if stype in (
        "SYSTEM_MESSAGE",
        "USER_INPUT",
        "CHECKPOINT",
        "ERROR_MESSAGE",
        "PLANNER_RESPONSE",
    ):
        return False
    return stype in ("GENERIC", "TOOL_RESPONSE", "TOOL_RESULT") or (
        stype is None and ("content" in item or "output" in item)
    )


def _is_backgrounded_long_step(item: dict[str, Any]) -> bool:
    if item.get("status") == "RUNNING":
        return True
    content = item.get("content") or item.get("output")
    return isinstance(content, str) and "running as a background task" in content


def _iter_transcript_items(
    source: str | Path | Iterable[dict[str, Any]],
) -> Iterable[dict[str, Any]]:
    if isinstance(source, dict):
        yield source
        return
    if isinstance(source, (bytes, bytearray)):
        return
    if isinstance(source, (str, Path)):
        path = Path(source)
        try:
            is_file = path.is_file()
        except (OSError, ValueError):  # e.g. inline JSONL content longer than NAME_MAX
            is_file = False
        if is_file:
            with path.open("r", encoding="utf-8", errors="replace") as fh:
                for line in fh:
                    s = line.strip()
                    if not s:
                        continue
                    try:
                        parsed = json.loads(s)
                        if isinstance(parsed, dict):
                            yield parsed
                    except Exception:
                        continue
            return
        if isinstance(source, str) and ("\n" in source or source.strip().startswith("{")):
            for line in source.splitlines():
                s = line.strip()
                if not s:
                    continue
                try:
                    parsed = json.loads(s)
                    if isinstance(parsed, dict):
                        yield parsed
                except Exception:
                    continue
        return
    for item in source:
        if isinstance(item, dict):
            yield item


def _batch_key(obj: dict[str, Any], fallback: str) -> Any:
    """First usable batch id: a non-empty string, an int, or a finite float. Other
    values (lists, dicts, NaN, booleans) are ignored, so a malformed id can neither
    crash the grouping (unhashable keys) nor merge unrelated calls."""
    for key in ("batch_id", "step_index", "turn_id"):
        val = obj.get(key)
        if isinstance(val, bool):
            continue
        if isinstance(val, int) or (isinstance(val, str) and val != ""):
            return val
        if isinstance(val, float) and val == val and val not in (float("inf"), float("-inf")):
            return val
    return fallback


def _safe_int(val: Any, default: int = 1) -> int:
    if isinstance(val, bool):
        return default
    try:
        return int(val)
    except (TypeError, ValueError, OverflowError):  # OverflowError: int(inf)
        return default


def _tool_name(obj: dict[str, Any]) -> str | None:
    for key in ("tool", "name", "tool_name"):
        val = obj.get(key)
        if isinstance(val, str):
            s = val.strip()
            if s:
                return s
    return None


def compute_unbatched_tool_latencies(
    transcript_or_events: str | Path | Iterable[dict[str, Any]],
    *,
    long_call_threshold_ms: float = DEFAULT_LONG_CALL_THRESHOLD_MS,
    tool_filter: str | Iterable[str] | None = None,
) -> dict[str, Any]:
    """Compute tool-call latency statistics from a `.jsonl` transcript or event list,
    separating calls that ran inside a multi-call batch containing a long-running call
    (`>= long_call_threshold_ms`, classified as `"batched_with_long_call"`) from
    standalone/unbatched calls (`"unbatched"`).

    Accepted inputs:
    - explicit latency events `{tool, duration_ms | latency_ms | started_at/completed_at,
      batch_id | step_index | turn_id, batch_size?}`;
    - step objects whose `tool_calls` entries carry their own timings;
    - structured `transcript.jsonl` steps, where a `PLANNER_RESPONSE` step lists its
      `tool_calls` (one batch) and the following result steps report, in order,
      `Created At: ... / Completed At: ...` timestamps for each call. A result step
      without `Completed At` (a call backgrounded while still `RUNNING`, or an error)
      still consumes its call, and a backgrounded call marks its batch as containing
      a long call. These timestamps have one-second resolution, so such durations
      are whole seconds (a sub-second call straddling a second boundary reads 1000 ms).
    Entries without usable timings are skipped without raising.
    """
    if not _is_finite_nonneg_number(long_call_threshold_ms):
        long_call_threshold_ms = DEFAULT_LONG_CALL_THRESHOLD_MS

    allowed_tools: set[str] | None = None
    if isinstance(tool_filter, str):
        allowed_tools = {tool_filter}
    elif tool_filter is not None:
        allowed_tools = set(tool_filter)

    raw_batches: dict[Any, list[dict[str, Any]]] = {}
    long_marked_batches: set[Any] = set()
    auto_batch_seq = 0
    # Calls of the latest planner step still waiting for their result steps, as
    # `(tool, batch_key, number_of_calls_in_that_step)`.
    pending: list[tuple[str, Any, int]] = []

    def _record(tool: str, dur: float, batch_key: Any, src: dict[str, Any], batch_size: int = 1) -> None:
        raw_batches.setdefault(batch_key, []).append(
            {
                "tool": tool,
                "duration_ms": float(dur),
                "batch_id": batch_key,
                "batch_size": max(1, batch_size),
                "explicit_batched_long": bool(
                    src.get("batched_with_long_call")
                    or src.get("classification") == "batched_with_long_call"
                ),
                "is_long_call": bool(src.get("is_long_call", False)),
            }
        )

    for item in _iter_transcript_items(transcript_or_events):
        tc_list = item.get("tool_calls")
        if isinstance(tc_list, list) and tc_list:
            batch_key = _batch_key(item, f"_step_{auto_batch_seq}")
            auto_batch_seq += 1
            step_dur = _extract_duration_ms(item)
            pending = []
            calls = [tc for tc in tc_list if isinstance(tc, dict)]
            for tc in calls:
                tname = _tool_name(tc) or "unknown"
                dur = _extract_duration_ms(tc)
                if dur is None and step_dur is not None and len(calls) == 1:
                    dur = step_dur
                if dur is None:
                    pending.append((tname, batch_key, len(calls)))
                    continue
                _record(tname, dur, batch_key, tc, len(calls))
            continue

        stype = item.get("type")
        if stype in ("PLANNER_RESPONSE", "USER_INPUT"):
            # Do not carry orphaned pending calls across turn boundaries after an interrupt.
            pending = []
            continue

        tname = _tool_name(item)
        if tname is None:
            # Tool result step: pop the matching pending call in lockstep even when
            # it has no `Completed At` (a backgrounded `RUNNING` call or an error), so
            # later siblings of the batch are never shifted onto the wrong tool name.
            if pending and _is_structured_tool_result_step(item):
                ptool, pbatch, psize = pending.pop(0)
                dur = _extract_duration_ms(item)
                if dur is not None:
                    _record(ptool, dur, pbatch, item, psize)
                elif _is_backgrounded_long_step(item):
                    # The call outlived the tool's synchronous wait: a long call.
                    long_marked_batches.add(pbatch)
            continue

        dur = _extract_duration_ms(item)
        if dur is None:
            if item.get("is_long_call") or _is_backgrounded_long_step(item):
                bkey = _batch_key(item, "")
                if bkey != "":
                    long_marked_batches.add(bkey)
            continue
        batch_key = _batch_key(item, f"_single_{auto_batch_seq}")
        if batch_key == f"_single_{auto_batch_seq}":
            auto_batch_seq += 1
        _record(tname, dur, batch_key, item, _safe_int(item.get("batch_size", 1)))

    unbatched: list[dict[str, Any]] = []
    batched_with_long_call: list[dict[str, Any]] = []
    by_tool_unbatched: dict[str, list[float]] = {}
    by_tool_batched_long: dict[str, int] = {}

    for batch_key, batch in raw_batches.items():
        is_multi = len(batch) > 1 or any(r.get("batch_size", 1) > 1 for r in batch)
        has_long = (batch_key in long_marked_batches) or any(
            r["duration_ms"] >= long_call_threshold_ms
            or r.get("is_long_call")
            or r.get("explicit_batched_long")
            for r in batch
        )
        batch_is_skewed = (is_multi and has_long) or any(
            r.get("explicit_batched_long") for r in batch
        )

        for r in batch:
            tname = r["tool"]
            if allowed_tools is not None and tname not in allowed_tools:
                continue
            entry = {
                "tool": tname,
                "duration_ms": r["duration_ms"],
                "batch_id": batch_key,
                "classification": (
                    "batched_with_long_call" if batch_is_skewed else "unbatched"
                ),
            }
            if batch_is_skewed:
                batched_with_long_call.append(entry)
                by_tool_batched_long[tname] = by_tool_batched_long.get(tname, 0) + 1
                by_tool_unbatched.setdefault(tname, [])
            else:
                unbatched.append(entry)
                by_tool_unbatched.setdefault(tname, []).append(r["duration_ms"])

    import statistics  # deferred: telemetry only, keeps cold hook imports fast

    unbatched_durs = [e["duration_ms"] for e in unbatched]
    mean_ms = statistics.mean(unbatched_durs) if unbatched_durs else None
    median_ms = statistics.median(unbatched_durs) if unbatched_durs else None
    if unbatched_durs:
        sorted_durs = sorted(unbatched_durs)
        p95_idx = min(len(sorted_durs) - 1, int(0.95 * (len(sorted_durs) - 1)))
        p95_ms: float | None = sorted_durs[p95_idx]
    else:
        p95_ms = None

    by_tool: dict[str, dict[str, Any]] = {}
    all_seen_tools = sorted(set(by_tool_unbatched.keys()) | set(by_tool_batched_long.keys()))
    for tname in all_seen_tools:
        durs = by_tool_unbatched.get(tname, [])
        by_tool[tname] = {
            "unbatched_count": len(durs),
            "unbatched_mean_ms": statistics.mean(durs) if durs else None,
            "unbatched_median_ms": statistics.median(durs) if durs else None,
            "batched_with_long_call_count": by_tool_batched_long.get(tname, 0),
        }

    return {
        "unbatched_mean_ms": mean_ms,
        "unbatched_median_ms": median_ms,
        "unbatched_p95_ms": p95_ms,
        "unbatched_count": len(unbatched),
        "batched_with_long_call_count": len(batched_with_long_call),
        "total_count": len(unbatched) + len(batched_with_long_call),
        "unbatched": unbatched,
        "batched_with_long_call": batched_with_long_call,
        "by_tool": by_tool,
    }


# ===========================================================================
# BEGIN SHARED WAIVER-PIN & 3-AXIS AUDITOR
# Byte-identical in `tools/anneal-lsp/server/proof_health.py` and
# `trusted/audit/check_trusted.py` (the TCB checker must stay a single stdlib-only
# file, so it cannot import `proof_health`); `test_proof_health.py` enforces equality.
# Promoted from the validated `waiver_pin_audit_proto.py` prototype (`2dd38e6d`).
# ===========================================================================

from bisect import bisect_right as _wa_bisect_right  # noqa: E402
from pathlib import Path  # noqa: E402,F811
import re  # noqa: E402,F811
from typing import Any, Iterable  # noqa: E402,F811

# ---------------------------------------------------------------------------
# Rule Identifiers
# ---------------------------------------------------------------------------

RULE_UNPINNED_WAIVER = "unpinned_waiver"
RULE_MALFORMED_WAIVER_PIN = "malformed_waiver_pin"
RULE_DRIFTED_WAIVER_PIN = "drifted_waiver_pin"
RULE_DANGLING_WAIVER = "dangling_waiver"
RULE_INVALID_WAIVER_SYNTAX = "invalid_waiver_syntax"

RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS = "syntactic_contradiction_hypothesis"
RULE_TRIVIAL_CONCLUSION = "trivial_conclusion"
RULE_UNUSED_SUBJECT_IN_CONCLUSION = "unused_subject_in_conclusion"
RULE_TAUTOLOGICAL_IMPLICATION = "tautological_implication"
RULE_TIER_ASSUMPTION_MISMATCH = "tier_assumption_mismatch"

ALL_WAIVER_RULES: tuple[str, ...] = (
    RULE_UNPINNED_WAIVER,
    RULE_MALFORMED_WAIVER_PIN,
    RULE_DRIFTED_WAIVER_PIN,
    RULE_DANGLING_WAIVER,
    RULE_INVALID_WAIVER_SYNTAX,
)

ALL_VACUITY_RULES: tuple[str, ...] = (
    RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
    RULE_TRIVIAL_CONCLUSION,
    RULE_UNUSED_SUBJECT_IN_CONCLUSION,
    RULE_TAUTOLOGICAL_IMPLICATION,
    RULE_TIER_ASSUMPTION_MISMATCH,
)

ALL_WAIVER_AUDIT_RULES: tuple[str, ...] = ALL_WAIVER_RULES + ALL_VACUITY_RULES

WAIVER_DIRECTIVE_TIERS: dict[str, str] = {
    "trusted": "TCB",
    "allow_compile_time_guard": "S1",
    "documented_intent": "S2",
    "pinned_compiler_coupled": "S3",
}

VALID_3AXIS_KINDS: frozenset[str] = frozenset(
    ("safety", "refinement", "divergence", "codec", "helper")
)
VALID_3AXIS_WITNESSES: frozenset[str] = frozenset(
    ("universal", "exists-sat", "negative")
)
VALID_3AXIS_ASSUMES: dict[str, str] = {
    "S0": "S0",
    "S0_rustcLowering": "S0",
    "S0_fnVerified": "S0",
    "S1": "S1",
    "S1_compileTimeGuard": "S1",
    "S2": "S2",
    "S2_documentedIntent": "S2",
    "S3": "S3",
    "S3_pinnedCompilerCoupled": "S3",
    "TCB": "TCB",
}


# ---------------------------------------------------------------------------
# Immutable Finding & Metadata Record Classes (`__slots__`, no `dataclasses`)
# ---------------------------------------------------------------------------


class WaiverPinFinding:
    """One waiver-pin or 3-axis non-vacuity finding. Immutable; compares and hashes by value."""

    __slots__ = (
        "rule",
        "line",
        "message",
        "suggestion",
        "symbol",
        "expected_pin",
        "actual_pin",
        "tier",
    )

    def __init__(
        self,
        rule: str,
        line: int,
        message: str,
        suggestion: str,
        symbol: str = "",
        expected_pin: str = "",
        actual_pin: str = "",
        tier: str = "",
    ) -> None:
        set_attr = object.__setattr__
        set_attr(self, "rule", rule)
        set_attr(self, "line", line)
        set_attr(self, "message", message)
        set_attr(self, "suggestion", suggestion)
        set_attr(self, "symbol", symbol)
        set_attr(self, "expected_pin", expected_pin)
        set_attr(self, "actual_pin", actual_pin)
        set_attr(self, "tier", tier)

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError("WaiverPinFinding is immutable")

    def _key(self) -> tuple[str, int, str, str, str, str, str, str]:
        return (
            self.rule,
            self.line,
            self.message,
            self.suggestion,
            self.symbol,
            self.expected_pin,
            self.actual_pin,
            self.tier,
        )

    def __eq__(self, other: object) -> bool:
        if other.__class__ is not WaiverPinFinding:
            return NotImplemented
        return self._key() == other._key()  # type: ignore[attr-defined]

    def __hash__(self) -> int:
        return hash(self._key())

    def __repr__(self) -> str:
        return (
            "WaiverPinFinding(rule=%r, line=%r, symbol=%r, tier=%r, expected_pin=%r, actual_pin=%r)"
            % (
                self.rule,
                self.line,
                self.symbol,
                self.tier,
                self.expected_pin,
                self.actual_pin,
            )
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "rule": self.rule,
            "line": self.line,
            "message": self.message,
            "suggestion": self.suggestion,
            "symbol": self.symbol,
            "expected_pin": self.expected_pin,
            "actual_pin": self.actual_pin,
            "tier": self.tier,
        }


class WaiverAnnotation:
    """Parsed `anneal:` directive extracted from a doc comment or `#[doc = "..."]` attribute.

    `canonical` is the directive text with inline `pin:` tokens removed and whitespace collapsed
    outside string literals; every directive of a doc block is folded into that block's pin hash,
    so swapping a waiver's tier (e.g. `documented_intent` -> `pinned_compiler_coupled`), adding a
    waiver, or editing a rationale invalidates the pin just like an edit to the target item.
    """

    __slots__ = (
        "directive",
        "tier",
        "reason",
        "pin_tokens",
        "line",
        "raw_line",
        "syntax_error",
        "canonical",
    )

    def __init__(
        self,
        directive: str,
        tier: str,
        reason: str,
        pin_tokens: tuple[str, ...],
        line: int,
        raw_line: str,
        syntax_error: str = "",
        canonical: str = "",
    ) -> None:
        set_attr = object.__setattr__
        set_attr(self, "directive", directive)
        set_attr(self, "tier", tier)
        set_attr(self, "reason", reason)
        set_attr(self, "pin_tokens", pin_tokens)
        set_attr(self, "line", line)
        set_attr(self, "raw_line", raw_line)
        set_attr(self, "syntax_error", syntax_error)
        set_attr(self, "canonical", canonical)

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError("WaiverAnnotation is immutable")


class TheoremMetadataRecord:
    """Parsed 3-axis theorem metadata and signature analysis for a Lean `theorem`/`lemma`."""

    __slots__ = (
        "name",
        "line",
        "kind",
        "witness",
        "assumes",
        "subject",
        "hypotheses",
        "conclusion",
    )

    def __init__(
        self,
        name: str,
        line: int,
        kind: str,
        witness: str,
        assumes: str,
        subject: str,
        hypotheses: tuple[str, ...],
        conclusion: str,
    ) -> None:
        set_attr = object.__setattr__
        set_attr(self, "name", name)
        set_attr(self, "line", line)
        set_attr(self, "kind", kind)
        set_attr(self, "witness", witness)
        set_attr(self, "assumes", assumes)
        set_attr(self, "subject", subject)
        set_attr(self, "hypotheses", hypotheses)
        set_attr(self, "conclusion", conclusion)

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError("TheoremMetadataRecord is immutable")


# ---------------------------------------------------------------------------
# Fast Offset-to-Line & Normalization Helpers
# ---------------------------------------------------------------------------

_WA_BLANK_BYTES_TABLE = bytes(10 if i == 10 else 32 for i in range(256))
_PIN_EXACT_RE = re.compile(r"^pin:sha256:([0-9a-f]{12})$")
_PIN_TOKEN_RE = re.compile(r"(?<!\S)(pin:\S*)")


def _wa_blank(seg: str) -> str:
    if "\n" not in seg:
        return " " * len(seg)
    if seg.isascii():
        return seg.encode("ascii").translate(_WA_BLANK_BYTES_TABLE).decode("ascii")
    return "\n".join([" " * len(part) for part in seg.split("\n")])


class _WaLineCounter:
    __slots__ = ("text", "off", "line")

    def __init__(self, text: str) -> None:
        self.text = text
        self.off = 0
        self.line = 1

    def __call__(self, offset: int) -> int:
        if offset >= self.off:
            self.line += self.text.count("\n", self.off, offset)
        elif offset * 2 < self.off:
            self.line = self.text.count("\n", 0, offset) + 1
        else:
            self.line -= self.text.count("\n", offset, self.off)
        self.off = offset
        return self.line


def _is_lean_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'!?"


def _is_rust_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch == "_"


def compute_sha256_pin12(normalized_target: str) -> str:
    """Return the 12-hex-character SHA-256 prefix of `normalized_target`."""
    import hashlib  # Lazy: fresh hook processes that never pin skip the OpenSSL import.

    return hashlib.sha256(normalized_target.encode("utf-8")).hexdigest()[:12]


def format_pin_tag(hex12: str) -> str:
    return f"pin:sha256:{hex12}"


_RUST_PUNCT = frozenset("()[]{}:;,.")


def _skip_quoted(text: str, q_start: int, n: int) -> int:
    """Return the offset just past the closing `"` of a backslash-escaped string body starting
    at `q_start` (the first character after the opening quote), or `n` if unterminated."""
    cur = q_start
    while cur < n:
        q = text.find('"', cur)
        if q == -1:
            return n
        bs = 0
        k = q - 1
        while k >= q_start and text[k] == "\\":
            bs += 1
            k -= 1
        cur = q + 1
        if bs % 2 == 0:
            return cur
    return n


def _match_rust_string_literal(text: str, pos: int, n: int) -> int | None:
    """End offset of a Rust raw / byte / C / normal string or char/byte literal at `pos`."""
    end = _match_rust_raw_string(text, pos, n)
    if end is not None:
        return end
    end = _match_rust_char_literal(text, pos, n)
    if end is not None:
        return end
    ch = text[pos]
    if ch == '"':
        return _skip_quoted(text, pos + 1, n)
    if (
        ch in "bc"
        and pos + 1 < n
        and text[pos + 1] == '"'
        and (pos == 0 or not _is_rust_ident_char(text[pos - 1]))
    ):
        return _skip_quoted(text, pos + 2, n)
    return None


def _normalize_rust_item(stripped: str) -> str:
    """Canonicalize a comment-stripped Rust item span for SHA-256 pinning.

    Whitespace runs outside string / raw-string / byte-string / char literals collapse to a
    single space, and whitespace adjacent to `()[]{}:;,.` is dropped (Rust's token stream is
    insensitive to it). Literals are copied verbatim and are recognized with the same lexer as
    the comment stripper, so `'"'` / `b'"'` char literals no longer open a phantom string.
    """
    n = len(stripped)
    out: list[str] = []
    app = out.append
    last = ""
    pending_ws = False
    i = 0
    while i < n:
        ch = stripped[i]
        if ch in " \t\r\n\f\v":
            pending_ws = True
            i += 1
            continue
        end = _match_rust_string_literal(stripped, i, n) if ch in "\"'rbc" else None
        tok = stripped[i:end] if end is not None else ch
        if pending_ws and out and last not in _RUST_PUNCT and tok[0] not in _RUST_PUNCT:
            app(" ")
        app(tok)
        last = tok[-1]
        pending_ws = False
        i = end if end is not None else i + 1
    return "".join(out)


def _match_lean_literal(text: str, pos: int, n: int) -> int | None:
    """End offset of a Lean string / raw string / char literal / `«guillemet»` identifier at
    `pos`, or `None` (a `'` after an identifier character is a prime, not a char literal)."""
    ch = text[pos]
    if ch == '"':
        return _skip_quoted(text, pos + 1, n)
    if ch == "«":
        g = text.find("»", pos + 1)
        return n if g == -1 else g + 1
    if ch == "r" and (pos == 0 or not (_is_lean_ident_char(text[pos - 1]) or text[pos - 1] == ".")):
        p = pos + 1
        while p < n and text[p] == "#":
            p += 1
        if p < n and text[p] == '"':
            closer = '"' + "#" * (p - pos - 1)
            c = text.find(closer, p + 1)
            return n if c == -1 else c + len(closer)
        return None
    if ch == "'" and (pos == 0 or not _is_lean_ident_char(text[pos - 1])):
        if pos + 2 < n and text[pos + 1] == "\\":
            q = pos + 3 if text[pos + 2] != "u" else text.find("}", pos + 2) + 1
            if text[pos + 2] == "x":
                q = pos + 5
            if 0 < q < n and text[q] == "'":
                return q + 1
            return None
        if pos + 2 < n and text[pos + 1] not in "'\\\n" and text[pos + 2] == "'":
            return pos + 3
    return None


_LEAN_CHAR_LIT_RE = re.compile(r"(?<![\w'!?])'(?:\\[^']{1,10}|[^'\\\n])'")


def _normalize_lean_decl(no_comments: str) -> str:
    """Canonicalize a comment-blanked Lean declaration span for SHA-256 pinning.

    Lean is whitespace-sensitive (`xs[i]` indexes but `xs [i]` applies `xs` to a list literal;
    `f x.y` projects but `f x .y` passes a leading-dot constructor; tactic blocks and `where` /
    `|` alternatives are column-sensitive), so unlike Rust this never deletes a separator:
    per line it keeps the exact leading indentation, collapses interior whitespace runs outside
    string / char literals to one space, strips trailing whitespace, and drops blank
    (comment-only) lines.
    """
    if '"' not in no_comments and "«" not in no_comments and _LEAN_CHAR_LIT_RE.search(no_comments) is None:
        fast: list[str] = []
        for raw in no_comments.split("\n"):
            body = raw.split()
            if body:
                fast.append(" " * (len(raw) - len(raw.lstrip(" \t\r\f\v"))) + " ".join(body))
        return "\n".join(fast)
    n = len(no_comments)
    lines: list[str] = []
    cur: list[str] = []
    indent = 0
    at_line_start = True
    pending_ws = False
    i = 0
    while i < n:
        ch = no_comments[i]
        if ch == "\n":
            if cur:
                lines.append(" " * indent + "".join(cur))
            cur = []
            indent = 0
            at_line_start = True
            pending_ws = False
            i += 1
            continue
        if ch in " \t\r\f\v":
            if at_line_start:
                indent += 1
            else:
                pending_ws = True
            i += 1
            continue
        end = _match_lean_literal(no_comments, i, n) if ch in "\"'r«" else None
        tok = no_comments[i:end] if end is not None else ch
        if pending_ws and cur:
            cur.append(" ")
        cur.append(tok)
        at_line_start = False
        pending_ws = False
        i = end if end is not None else i + 1
    if cur:
        lines.append(" " * indent + "".join(cur))
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Directive & Pin Line Parser (`b1f15f743c:trusted/rustc-capture/src/spec.rs`)
# ---------------------------------------------------------------------------


_U128_MAX = (1 << 128) - 1


def _is_ascii_alpha(c: str) -> bool:
    return ("a" <= c <= "z") or ("A" <= c <= "Z")


def _is_ascii_digit(c: str) -> bool:
    return "0" <= c <= "9"


def _lex_spec_tokens(s: str) -> tuple[list[tuple[str, Any]], str]:
    """Lex an `anneal:` directive body exactly like `b1f15f743c:trusted/rustc-capture/src/spec.rs`
    (`lex`): ASCII identifiers/integers only (`u128` range), `"..."` strings admitting only the
    `\\"` and `\\\\` escapes, and `(`, `)`, `=`, `==`, `!=` punctuation."""
    out: list[tuple[str, Any]] = []
    n = len(s)
    i = 0
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
            continue
        if c == "(":
            out.append(("LParen", "("))
            i += 1
            continue
        if c == ")":
            out.append(("RParen", ")"))
            i += 1
            continue
        if c == "=":
            if i + 1 < n and s[i + 1] == "=":
                out.append(("EqEq", "=="))
                i += 2
            else:
                out.append(("Eq", "="))
                i += 1
            continue
        if c == "!":
            if i + 1 < n and s[i + 1] == "=":
                out.append(("Ne", "!="))
                i += 2
            else:
                return [], f"expected `!=` at offset {i}"
            continue
        if c == '"':
            start = i
            i += 1
            val: list[str] = []
            closed = False
            while i < n:
                d = s[i]
                i += 1
                if d == '"':
                    closed = True
                    break
                if d == "\\":
                    if i < n and s[i] in ('"', "\\"):
                        val.append(s[i])
                        i += 1
                    else:
                        return [], f"unsupported escape sequence in string literal at offset {start}"
                else:
                    val.append(d)
            if not closed:
                return [], f"unterminated string literal at offset {start}"
            out.append(("Str", "".join(val)))
            continue
        if _is_ascii_alpha(c) or c == "_":
            start = i
            i += 1
            while i < n and (_is_ascii_alpha(s[i]) or _is_ascii_digit(s[i]) or s[i] == "_"):
                i += 1
            out.append(("Ident", s[start:i]))
            continue
        if _is_ascii_digit(c):
            start = i
            i += 1
            while i < n and _is_ascii_digit(s[i]):
                i += 1
            val_int = int(s[start:i])
            if val_int > _U128_MAX:
                return [], f"integer `{s[start:i]}` too large"
            out.append(("Int", val_int))
            continue
        return [], f"unexpected character `{c}` at offset {i}"
    return out, ""


_INLINE_CODE_SPAN_RE = re.compile(r"`[^`]*`")
_WAIVER_TIERS: frozenset[str] = frozenset(("TCB", "S1", "S2", "S3"))
_DIRECTIVE_HEAD_RE = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_]*)")
_PIN_LINE_ADVICE = "put the pin on its own doc line (`pin:sha256:<12hex>`)"


def _split_pin_tokens(rest: str) -> tuple[str, list[str]]:
    """Split whitespace-delimited `pin:` tokens (outside `"..."` strings) out of `rest`."""
    pins: list[str] = []
    parts: list[str] = []
    n = len(rest)
    i = 0
    while i < n:
        ch = rest[i]
        if ch == '"':
            j = i + 1
            while j < n:
                if rest[j] == "\\" and j + 1 < n:
                    j += 2
                    continue
                if rest[j] == '"':
                    j += 1
                    break
                j += 1
            parts.append(rest[i:j])
            i = j
            continue
        if rest.startswith("pin:", i) and (i == 0 or rest[i - 1].isspace()):
            j = i
            while j < n and not rest[j].isspace():
                j += 1
            pins.append(rest[i:j])
            i = j
            continue
        parts.append(ch)
        i += 1
    return "".join(parts), pins


def _canonical_directive_text(body: str) -> str:
    """Collapse whitespace outside `"..."` strings (string contents are kept verbatim)."""
    out: list[str] = []
    n = len(body)
    pending = False
    i = 0
    while i < n:
        ch = body[i]
        if ch.isspace():
            pending = True
            i += 1
            continue
        if ch == '"':
            j = i + 1
            while j < n:
                if body[j] == "\\" and j + 1 < n:
                    j += 2
                    continue
                if body[j] == '"':
                    j += 1
                    break
                j += 1
        else:
            j = i + 1
        if pending and out:
            out.append(" ")
        out.append(body[i:j])
        pending = False
        i = j
    return "".join(out)


def _structured_directive(toks: list[tuple[str, Any]]) -> tuple[str, str] | None:
    """Match a lexed directive against spec.rs's structured forms; return `(kind, reason)`."""
    kinds = [t[0] for t in toks]
    vals = [t[1] for t in toks]
    if (
        kinds == ["Ident", "Ident", "LParen", "Ident", "EqEq", "Ident", "RParen"]
        and vals[0] == "spec"
        and vals[1] == "ensures"
        and vals[3] == "ret"
    ):
        return ("spec", "")
    if kinds == ["Ident", "Ident"] and vals[0] == "spec" and vals[1] == "well_formed":
        return ("spec", "")
    if kinds == ["Ident", "Ident", "Ne", "Int"] and vals[0] in ("requires", "invariant"):
        return (str(vals[0]), "")
    if kinds == ["Ident", "Ident", "Eq", "Str"] and vals[0] == "trusted" and vals[1] == "reason":
        return ("trusted", str(vals[3]))
    return None


def parse_pin_line(raw_line: str) -> str | None:
    """Return the trimmed text of a standalone pin doc line (`pin:sha256:<12hex>`), else `None`.

    Pin lines contain no `anneal:` substring, so spec.rs's `parse_doc` treats them as ordinary
    documentation: this is the only pin placement compatible with every waiver directive
    (`allow_compile_time_guard` and `trusted reason = "..."` admit no trailing tokens).
    """
    t = raw_line.strip()
    if t.startswith("pin:") and "anneal:" not in t:
        return t
    return None


def parse_anneal_directive_line(raw_line: str, line_no: int) -> WaiverAnnotation | None:
    """Parse one trimmed doc line containing `anneal:` with spec.rs (`parse_doc`) semantics.

    Returns `None` for lines without `anneal:` (ordinary documentation). Valid non-waiver
    directives (`spec`, `requires`, `invariant`) are returned with tier `S0` so that they are
    folded into the block's pin hash. Inline `pin:` tokens are accepted only on the free-form
    `documented_intent` / `pinned_compiler_coupled` rationales, which spec.rs keeps verbatim.
    """
    line = raw_line.strip()
    if "anneal:" not in line:
        return None
    if not line.startswith("anneal:"):
        # Prose that only mentions `anneal:...` inside markdown code spans is documentation.
        if "anneal:" not in _INLINE_CODE_SPAN_RE.sub("", line):
            return None
        return WaiverAnnotation(
            directive="unknown",
            tier="",
            reason="",
            pin_tokens=(),
            line=line_no,
            raw_line=line,
            syntax_error=f"`anneal:` must start the doc-comment line: `{line}`",
        )

    rest = line[len("anneal:") :]
    rest_wo_pins, pins = _split_pin_tokens(rest)
    canonical = "anneal:" + _canonical_directive_text(rest_wo_pins)
    head_m = _DIRECTIVE_HEAD_RE.match(rest)
    head = head_m.group(1) if head_m else "unknown"
    head_tier = WAIVER_DIRECTIVE_TIERS.get(
        head, "S0" if head in ("spec", "requires", "invariant") else ""
    )

    def mk(directive: str, tier: str, reason: str = "", err: str = "") -> WaiverAnnotation:
        return WaiverAnnotation(
            directive=directive,
            tier=tier,
            reason=reason,
            pin_tokens=tuple(pins),
            line=line_no,
            raw_line=line,
            syntax_error=err,
            canonical=canonical,
        )

    # (1) spec.rs: `rest.trim() == "allow_compile_time_guard"` -- nothing else on the line.
    if rest.strip() == "allow_compile_time_guard":
        return mk("allow_compile_time_guard", "S1", "allow_compile_time_guard")
    if head == "allow_compile_time_guard":
        if pins and rest_wo_pins.strip() == "allow_compile_time_guard":
            return mk(
                head,
                "S1",
                err=(
                    "spec.rs requires `anneal:allow_compile_time_guard` to be the entire doc line, "
                    f"so an inline pin makes `cargo anneal` reject it; {_PIN_LINE_ADVICE}"
                ),
            )
        return mk(
            head,
            "S1",
            err=(
                "spec.rs accepts only the bare `anneal:allow_compile_time_guard` directive "
                f"(no rationale, `reason = ...`, or trailing tokens): `{line}`"
            ),
        )

    # (2) spec.rs: `rest.strip_prefix(kw)` on the *untrimmed* remainder, then a non-empty
    # trimmed rationale (free-form, so an inline pin token is tolerated but is not a rationale).
    for kw in ("documented_intent", "pinned_compiler_coupled"):
        if rest.startswith(kw) and (len(rest) == len(kw) or rest[len(kw)].isspace()):
            rationale = _split_pin_tokens(rest[len(kw) :])[0].strip()
            if not rationale:
                return mk(
                    kw,
                    WAIVER_DIRECTIVE_TIERS[kw],
                    err=(
                        f"`anneal:{kw}` requires a non-empty rationale "
                        f"(a `pin:` token is not a rationale): `{line}`"
                    ),
                )
            return mk(kw, WAIVER_DIRECTIVE_TIERS[kw], rationale)

    # (3) Structured directives: spec.rs lexes the whole remainder (pin tokens included).
    toks, err = _lex_spec_tokens(rest)
    if err:
        if pins:
            toks2, err2 = _lex_spec_tokens(rest_wo_pins)
            if not err2 and _structured_directive(toks2) is not None:
                return mk(
                    head,
                    head_tier,
                    err=(
                        f"inline `pin:` token breaks the spec.rs grammar of `anneal:{head}` "
                        f"(`cargo anneal` would reject the line); {_PIN_LINE_ADVICE}"
                    ),
                )
        return mk(head, head_tier, err=f"in `{line}`: {err}")
    kind = _structured_directive(toks)
    if kind is None:
        if head == "trusted":
            return mk("trusted", "TCB", err=f"`anneal:trusted` requires exactly `reason = \"...\"`: `{line}`")
        if head in ("requires", "invariant"):
            return mk(
                head, "S0", err=f"invalid `anneal:{head}` syntax (expected `<ident> != <int>`): `{line}`"
            )
        if head == "spec":
            return mk("spec", "S0", err=f"unsupported `anneal:spec` syntax `{line}`")
        return mk(head, head_tier, err=f"unsupported Anneal directive `{line}`")
    directive, reason = kind
    if directive == "trusted":
        if not reason.strip():
            return mk("trusted", "TCB", err=f"`anneal:trusted` requires a non-empty reason: `{line}`")
        return mk("trusted", "TCB", reason)
    return mk(directive, "S0", directive)


def waiver_hash_input(anns: Iterable[WaiverAnnotation], normalized_item: str) -> str:
    """SHA-256 pin pre-image of a doc block: its canonical directives (source order) + item."""
    directive_lines = [a.canonical for a in anns if a.canonical]
    if not directive_lines:
        return normalized_item
    return "\n".join(directive_lines) + "\n" + normalized_item


def _validate_waiver_block(
    anns: list[WaiverAnnotation],
    block_pins: list[tuple[str, int]],
    target_symbol: str,
    hash_input: str,
) -> list[WaiverPinFinding]:
    """Validate directive syntax and the `pin:sha256:<12hex>` of one doc block.

    `block_pins` are the standalone pin lines of the block; inline pins on free-form waiver
    rationales are also honoured. Every pin of the block must agree and must equal
    `sha256(hash_input)[:12]`, where `hash_input` binds both the block's directives and the
    normalized target item.
    """
    findings: list[WaiverPinFinding] = []
    expected_pin = format_pin_tag(compute_sha256_pin12(hash_input))

    bad = [a for a in anns if a.syntax_error]
    for ann in bad:
        findings.append(
            WaiverPinFinding(
                rule=RULE_INVALID_WAIVER_SYNTAX,
                line=ann.line,
                symbol=target_symbol or ann.directive,
                tier=ann.tier,
                expected_pin=expected_pin,
                actual_pin=ann.pin_tokens[0] if ann.pin_tokens else "",
                message=f"Invalid Anneal directive syntax: {ann.syntax_error}",
                suggestion=(
                    "Use the exact spec.rs forms (`anneal:trusted reason = \"...\"`, "
                    "`anneal:allow_compile_time_guard`, `anneal:documented_intent <rationale>`, "
                    "`anneal:pinned_compiler_coupled <reason>`) and record the pin on its own doc "
                    f"line: `{expected_pin}`."
                ),
            )
        )
    if bad:
        return findings

    waivers = [a for a in anns if a.tier in _WAIVER_TIERS]
    if not waivers:
        return findings
    pins = [p for p, _ in block_pins] + [p for a in waivers for p in a.pin_tokens]

    for ann in waivers:
        if not pins:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_UNPINNED_WAIVER,
                    line=ann.line,
                    symbol=target_symbol or ann.directive,
                    tier=ann.tier,
                    expected_pin=expected_pin,
                    actual_pin="",
                    message=(
                        f"Unpinned `{ann.tier}` waiver `anneal:{ann.directive}` on `{target_symbol}` "
                        f"(missing `{expected_pin}`)."
                    ),
                    suggestion=f"Add the doc line `{expected_pin}` to this waiver's doc block.",
                )
            )
        elif len(set(pins)) > 1:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_MALFORMED_WAIVER_PIN,
                    line=ann.line,
                    symbol=target_symbol or ann.directive,
                    tier=ann.tier,
                    expected_pin=expected_pin,
                    actual_pin=",".join(pins),
                    message=(
                        f"Multiple conflicting `pin:` tokens in the doc block of `{target_symbol}`: "
                        f"{pins!r}."
                    ),
                    suggestion=f"Keep a single `{expected_pin}` pin line.",
                )
            )
        elif _PIN_EXACT_RE.match(pins[0]) is None:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_MALFORMED_WAIVER_PIN,
                    line=ann.line,
                    symbol=target_symbol or ann.directive,
                    tier=ann.tier,
                    expected_pin=expected_pin,
                    actual_pin=pins[0],
                    message=(
                        f"Malformed waiver pin `{pins[0]}` on `anneal:{ann.directive}` for "
                        f"`{target_symbol}` (expected `pin:sha256:<12 lowercase hex digits>`)."
                    ),
                    suggestion=f"Replace `{pins[0]}` with `{expected_pin}`.",
                )
            )
        elif pins[0] != expected_pin:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_DRIFTED_WAIVER_PIN,
                    line=ann.line,
                    symbol=target_symbol or ann.directive,
                    tier=ann.tier,
                    expected_pin=expected_pin,
                    actual_pin=pins[0],
                    message=(
                        f"Waiver pin drift on `{target_symbol}` (`anneal:{ann.directive}`, tier "
                        f"`{ann.tier}`): recorded `{pins[0]}`, but the directives + target "
                        f"declaration hash to `{expected_pin}`."
                    ),
                    suggestion=(
                        f"Re-audit `{target_symbol}` under tier `{ann.tier}` and update the pin to "
                        f"`{expected_pin}`."
                    ),
                )
            )
    return findings


def _collect_block_directives(
    doc_lines: Iterable[tuple[int, str]],
) -> tuple[list[WaiverAnnotation], list[tuple[str, int]]]:
    """Parse `(line_no, text)` doc lines into directives and standalone pin lines."""
    anns: list[WaiverAnnotation] = []
    pins: list[tuple[str, int]] = []
    for line_no, raw in doc_lines:
        if "anneal:" in raw:
            ann = parse_anneal_directive_line(raw, line_no)
            if ann is not None:
                anns.append(ann)
            continue
        if "pin:" in raw:
            p = parse_pin_line(raw)
            if p is not None:
                pins.append((p, line_no))
    return anns, pins


# ---------------------------------------------------------------------------
# Rust (`.rs`) Lexer, Doc-Attribute Extractor & Target Item Span Scanner
# ---------------------------------------------------------------------------


def _match_rust_raw_string(text: str, pos: int, n: int) -> int | None:
    """If `text[pos:]` starts a Rust raw string (`r"..."`, `r#"..."#`, `br#"..."#`, `cr#"..."#`),
    return the end offset past the closing delimiter; otherwise `None`."""
    ch = text[pos]
    if ch not in "rbc":
        return None
    if pos > 0 and _is_rust_ident_char(text[pos - 1]):
        return None
    p = pos
    if ch in "bc":
        if p + 1 < n and text[p + 1] == "r":
            p += 2
        else:
            return None
    else:
        p += 1
    hashes = 0
    while p < n and text[p] == "#":
        hashes += 1
        p += 1
    if p >= n or text[p] != '"':
        return None
    closer = '"' + "#" * hashes
    c = text.find(closer, p + 1)
    return n if c == -1 else c + len(closer)


def _match_rust_char_literal(text: str, pos: int, n: int) -> int | None:
    """If `text[pos:]` starts a Rust character or byte literal (`'x'`, `'\\n'`, `'\\''`,
    `'\\u{1F600}'`, `b'x'`) rather than a lifetime (`'a`, `'static`), return the end offset past
    the closing `'`; otherwise `None`."""
    p = pos
    if text[p] == "b":
        if pos > 0 and _is_rust_ident_char(text[pos - 1]):
            return None
        if p + 1 < n and text[p + 1] == "'":
            p += 1
        else:
            return None
    elif text[p] == "'":
        if pos > 0 and _is_rust_ident_char(text[pos - 1]):
            return None
    else:
        return None

    if p + 2 >= n:
        return None
    if text[p + 1] == "\\":
        # Skip the escaped character first so that `'\''` and `'\\'` close correctly.
        q = p + 3
        if text[p + 2] == "u" and q < n and text[q] == "{":
            close = text.find("}", q, q + 10)
            if close == -1:
                return None
            q = close + 1
        elif text[p + 2] == "x":
            q = p + 5
        return q + 1 if q < n and text[q] == "'" else None
    if text[p + 1] != "'" and text[p + 1] != "\n" and text[p + 2] == "'":
        return p + 3
    return None


def _unescape_rust_doc_string(raw: str) -> str:
    """Decode a Rust (non-raw) string literal body the way `rustc` does for `#[doc = "..."]`:
    `\\n \\r \\t \\\\ \\0 \\' \\"`, `\\xNN`, `\\u{...}`, and `\\`-newline continuations (which
    also skip the following whitespace). Escapes such as `anneal\\x3atrusted` therefore cannot
    hide a waiver directive from the auditor."""
    out: list[str] = []
    i = 0
    n = len(raw)
    simple = {"n": "\n", "r": "\r", "t": "\t", "\\": "\\", "0": "\0", "'": "'", '"': '"'}
    while i < n:
        ch = raw[i]
        if ch != "\\" or i + 1 >= n:
            out.append(ch)
            i += 1
            continue
        nxt = raw[i + 1]
        if nxt in simple:
            out.append(simple[nxt])
            i += 2
            continue
        if nxt == "x" and i + 3 < n and all(c in "0123456789abcdefABCDEF" for c in raw[i + 2 : i + 4]):
            out.append(chr(int(raw[i + 2 : i + 4], 16)))
            i += 4
            continue
        if nxt == "u" and i + 2 < n and raw[i + 2] == "{":
            close = raw.find("}", i + 3)
            if close != -1:
                digits = raw[i + 3 : close].replace("_", "")
                try:
                    out.append(chr(int(digits, 16)))
                    i = close + 1
                    continue
                except ValueError:
                    pass
        if nxt == "\n" or (nxt == "\r" and i + 2 < n and raw[i + 2] == "\n"):
            i += 2 if nxt == "\n" else 3
            while i < n and raw[i] in " \t\r\n":
                i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _find_rust_attr_end(text: str, open_bracket: int, n: int) -> int:
    """Offset just past the `]` matching the `[` at `open_bracket` (string-literal aware)."""
    depth = 0
    p = open_bracket
    while p < n:
        ch = text[p]
        if ch in "\"'rbc":
            end = _match_rust_string_literal(text, p, n)
            if end is not None:
                p = end
                continue
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                return p + 1
        p += 1
    return n


_RUST_ATTR_DOC_ASSIGN_RE = re.compile(r"\bdoc\s*=")


def _scan_rust_tokens_and_docs(
    text: str,
) -> tuple[str, list[tuple[int, int, int, str, bool]], list[tuple[int, int, str]]]:
    """Return `(comment_stripped_text, doc_segments, opaque_doc_attrs)` for Rust source `text`.

    - `comment_stripped_text` has the exact length and newlines of `text`, with all comments
      (`//`, `///`, `//!`, `/* ... */`) and literal `#[doc = ...]` / `#![doc = ...]` attributes
      blanked, while string / char literals, lifetimes, and semantic attributes (`#[repr(C)]`)
      are kept.
    - `doc_segments` holds `(start, end, start_line, doc_text, is_inner)` for every doc comment
      and literal doc attribute; inner docs (`//!`, `/*! */`, `#![doc]`) document the enclosing
      module, never the next item.
    - `opaque_doc_attrs` holds `(start, start_line, kind)` for outer attributes whose doc text
      `rustc` computes (`#[doc = concat!(..)]`, `#[doc = include_str!(..)]`,
      `#[cfg_attr(.., doc = ..)]`): a waiver hidden there is invisible to source scanning.
    """
    n = len(text)
    out: list[str] = []
    app = out.append
    docs: list[tuple[int, int, int, str, bool]] = []
    opaque: list[tuple[int, int, str]] = []
    line_of = _WaLineCounter(text)
    i = 0
    while i < n:
        ch = text[i]
        if ch == "/" and i + 1 < n and text[i + 1] in "/*":
            if text[i + 1] == "/":
                nl = text.find("\n", i + 2)
                end = n if nl == -1 else nl
                raw_comment = text[i:end]
                if raw_comment.startswith("///") and not raw_comment.startswith("////"):
                    docs.append((i, end, line_of(i), raw_comment[3:], False))
                elif raw_comment.startswith("//!"):
                    docs.append((i, end, line_of(i), raw_comment[3:], True))
                app(" " * (end - i))
                i = end
                continue
            depth = 1
            cur = i + 2
            while depth > 0 and cur < n:
                c = text.find("*/", cur)
                if c == -1:
                    cur = n
                    break
                o = text.find("/*", cur, c)
                if o != -1:
                    depth += 1
                    cur = o + 2
                else:
                    depth -= 1
                    cur = c + 2
            raw_blk = text[i:cur]
            body = raw_blk[3 : -2 if raw_blk.endswith("*/") else len(raw_blk)]
            if raw_blk.startswith("/**") and not raw_blk.startswith("/***") and raw_blk != "/**/":
                docs.append((i, cur, line_of(i), body, False))
            elif raw_blk.startswith("/*!"):
                docs.append((i, cur, line_of(i), body, True))
            app(_wa_blank(raw_blk))
            i = cur
            continue

        if ch == "#" and i + 1 < n:
            attr_start = i
            p_bang = i + 1
            while p_bang < n and text[p_bang] in " \t\r\n":
                p_bang += 1
            is_inner = p_bang < n and text[p_bang] == "!"
            p_open = p_bang + 1 if is_inner else p_bang
            while p_open < n and text[p_open] in " \t\r\n":
                p_open += 1
            if p_open < n and text[p_open] == "[":
                p = p_open + 1
                while p < n and text[p].isspace():
                    p += 1
                if text.startswith("doc", p) and (p + 3 < n and not _is_rust_ident_char(text[p + 3])):
                    q = p + 3
                    while q < n and text[q].isspace():
                        q += 1
                    if q < n and text[q] == "=":
                        q += 1
                        while q < n and text[q].isspace():
                            q += 1
                        raw_end = _match_rust_raw_string(text, q, n)
                        doc_val: str | None = None
                        val_end = q
                        if raw_end is not None:
                            q_quote = text.find('"', q)
                            hashes = q_quote - (q + (2 if text[q] in "bc" else 1))
                            doc_val = text[q_quote + 1 : raw_end - 1 - hashes]
                            val_end = raw_end
                        elif q < n and text[q] == '"':
                            val_end = _skip_quoted(text, q + 1, n)
                            doc_val = _unescape_rust_doc_string(text[q + 1 : val_end - 1])
                        if doc_val is not None:
                            while val_end < n and text[val_end].isspace():
                                val_end += 1
                            if val_end < n and text[val_end] == "]":
                                attr_end = val_end + 1
                                docs.append((attr_start, attr_end, line_of(attr_start), doc_val, is_inner))
                                app(_wa_blank(text[attr_start:attr_end]))
                                i = attr_end
                                continue
                        # `#[doc = #var]` is a `quote!` template inside a proc-macro body, not an
                        # attribute of this file; anything else computed by `rustc` is opaque.
                        if not is_inner and doc_val is None and q < n and text[q] != "#":
                            opaque.append((attr_start, line_of(attr_start), "doc = <computed>"))
                elif not is_inner:
                    attr_end = _find_rust_attr_end(text, p_open, n)
                    if _RUST_ATTR_DOC_ASSIGN_RE.search(text, p, attr_end):
                        attr_head = "cfg_attr(.., doc = ..)" if text.startswith("cfg_attr", p) else ".., doc = .."
                        opaque.append((attr_start, line_of(attr_start), attr_head))

        lit_end = _match_rust_string_literal(text, i, n) if ch in "\"'rbc" else None
        if lit_end is not None:
            app(text[i:lit_end])
            i = lit_end
            continue

        app(ch)
        i += 1

    return "".join(out), docs, opaque


def _find_preceding_rust_attributes_start(stripped: str, doc_start: int) -> int:
    """Walk backwards across any outer attributes `#[...]` immediately preceding `doc_start`
    on the same Rust item (e.g., `#[repr(C)]` written above `/// anneal:...`), using
    string-literal-aware forward bracket matching so brackets inside attribute string literals
    (`#[deprecated(note = "use foo[0]")]`) never desync attribute discovery."""
    cur = doc_start
    while cur > 0:
        p = cur
        while p > 0 and stripped[p - 1] in " \t\r\n":
            p -= 1
        if p <= 0 or stripped[p - 1] != "]":
            break
        matched_hash = -1
        search_h = p - 2
        while search_h >= 0:
            h_idx = stripped.rfind("#", 0, search_h + 1)
            if h_idx == -1:
                break
            q_br = h_idx + 1
            while q_br < p and stripped[q_br] in " \t\r\n":
                q_br += 1
            if q_br < p and stripped[q_br] == "[":
                if _find_rust_attr_end(stripped, q_br, p) == p:
                    matched_hash = h_idx
                    break
            search_h = h_idx - 1
        if matched_hash != -1:
            cur = matched_hash
        else:
            break
    return cur


_RUST_ITEM_NAME_RE = re.compile(
    r"\b(?:fn|struct|enum|union|type|const|static|trait|mod|macro_rules!)\s+((?:r#)?[A-Za-z_][A-Za-z0-9_]*)"
)
_RUST_WORD_RE = re.compile(r"(?:r#)?[A-Za-z_][A-Za-z0-9_]*!?")
_RUST_SEMI_ITEMS = frozenset(("const", "static", "type", "use", "extern", "let"))


def _rust_item_kind(stripped: str, i: int, n: int) -> tuple[str, int]:
    """Skip outer attributes, visibility, and qualifiers starting at `i`; return the item
    keyword (`fn`, `struct`, `const`, `impl`, ...) and its offset (`("", i)` if none)."""
    p = i
    while p < n:
        while p < n and stripped[p].isspace():
            p += 1
        if p >= n:
            return "", i
        if stripped[p] == "#":
            q = p + 1
            while q < n and stripped[q].isspace():
                q += 1
            if q < n and stripped[q] == "[":
                p = _find_rust_attr_end(stripped, q, n)
                continue
            return "", i
        m = _RUST_WORD_RE.match(stripped, p)
        if m is None:
            return "", i
        word = m.group(0)
        word_start = p
        p = m.end()
        if word == "pub":
            while p < n and stripped[p].isspace():
                p += 1
            if p < n and stripped[p] == "(":
                depth = 0
                while p < n:
                    if stripped[p] == "(":
                        depth += 1
                    elif stripped[p] == ")":
                        depth -= 1
                        if depth == 0:
                            p += 1
                            break
                    p += 1
            continue
        if word in ("unsafe", "async", "default", "safe"):
            continue
        if word == "extern":
            while p < n and stripped[p].isspace():
                p += 1
            if stripped.startswith("crate", p):
                return "extern", word_start
            if p < n and stripped[p] == '"':
                p = _skip_quoted(stripped, p + 1, n)
            continue
        if word == "const":
            q = p
            while q < n and stripped[q].isspace():
                q += 1
            m2 = _RUST_WORD_RE.match(stripped, q)
            if m2 is not None and m2.group(0) in ("fn", "unsafe", "async", "extern"):
                continue
            return "const", word_start
        return word, word_start
    return "", i


def _extract_rust_target_span(
    stripped: str, search_from: int, pre_attr_start: int
) -> tuple[int, int, str] | None:
    """Scan forward from `search_from` in comment-stripped Rust text to the end of the annotated
    item. Returns `(start_offset, end_offset, item_name)` or `None` if the waiver is dangling.

    `const` / `static` / `type` / `use` / `extern crate` items end at their top-level `;` (so a
    struct-literal initializer `Foo { .. }.with(2)` stays inside the pinned span); other items
    end at the `}` closing their body or at a top-level `;`, where generic-argument depth `<..>`
    is tracked at brace level 0 so a const-generic block in a signature
    (`-> Wrapper<{ N }>`) is never mistaken for the item body.
    """
    n = len(stripped)
    i = search_from
    while i < n and stripped[i] in " \t\r\n":
        i += 1
    if i >= n or stripped[i] == "}":
        return None

    start_off = min(pre_attr_start, i)
    kind, kw_off = _rust_item_kind(stripped, i, n)
    semi_item = kind in _RUST_SEMI_ITEMS
    p = i
    paren = bracket = brace = angle = 0
    saw_item_token = False

    def finish(end: int) -> tuple[int, int, str]:
        if kind == "impl":
            return start_off, end, "impl"
        m = _RUST_ITEM_NAME_RE.search(stripped, kw_off if kind else start_off, end)
        return start_off, end, (m.group(1) if m else "item")

    while p < n:
        ch = stripped[p]
        if ch in " \t\r\n":
            p += 1
            continue
        if ch in "\"'rbc":
            lit_end = _match_rust_string_literal(stripped, p, n)
            if lit_end is not None:
                saw_item_token = True
                p = lit_end
                continue
        top = paren == 0 and bracket == 0 and brace == 0
        if ch == "(":
            paren += 1
        elif ch == ")":
            if paren > 0:
                paren -= 1
        elif ch == "[":
            bracket += 1
        elif ch == "]":
            if bracket > 0:
                bracket -= 1
        elif (
            ch == "<"
            and top
            and not semi_item
            and (p + 1 >= n or stripped[p + 1] not in "<=")
            and (p == 0 or stripped[p - 1] != "<")
        ):
            angle += 1
        elif ch == ">" and top and not semi_item and angle > 0 and stripped[p - 1] not in "-=":
            angle -= 1
        elif ch == "{":
            brace += 1
        elif ch == "}":
            if brace == 0:
                return None
            brace -= 1
            p += 1
            if not semi_item and brace == 0 and paren == 0 and bracket == 0 and angle == 0:
                return finish(p)
            continue
        elif ch == ";" and top and (semi_item or angle == 0):
            if not saw_item_token:
                return None
            return finish(p + 1)
        saw_item_token = True
        p += 1
    return None


def _rust_outer_doc_groups(
    stripped: str, doc_segments: list[tuple[int, int, int, str, bool]]
) -> list[tuple[int, int, list[tuple[int, str]]]]:
    """Group consecutive *outer* doc segments of one item (separated only by whitespace,
    comments, or outer attributes `#[...]`)."""
    groups: list[tuple[int, int, list[tuple[int, str]]]] = []
    for seg_start, seg_end, seg_line, doc_body, is_inner in doc_segments:
        if is_inner:
            continue
        if groups:
            prev_start, prev_end, prev_lines = groups[-1]
            if not stripped[
                prev_end : _find_preceding_rust_attributes_start(stripped, seg_start)
            ].strip():
                groups[-1] = (prev_start, seg_end, prev_lines + [(seg_line, doc_body)])
                continue
        groups.append((seg_start, seg_end, [(seg_line, doc_body)]))
    return groups


def audit_rust_text(text: str, *, file_path: str | Path | None = None) -> list[WaiverPinFinding]:
    """Scan Rust source `text` for `S0`-`S3` waiver pin and directive syntax findings."""
    _ = file_path
    if "anneal" not in text and "doc" not in text:
        return []

    stripped, doc_segments, opaque = _scan_rust_tokens_and_docs(text)
    findings: list[WaiverPinFinding] = []

    for _, op_line, op_kind in opaque:
        findings.append(
            WaiverPinFinding(
                rule=RULE_INVALID_WAIVER_SYNTAX,
                line=op_line,
                symbol=op_kind,
                message=(
                    f"Unauditable computed doc attribute `#[{op_kind}]`: `rustc` expands it before the "
                    "Anneal capture reads doc attributes, so a waiver directive hidden there would evade "
                    "SHA-256 pinning."
                ),
                suggestion="Write Anneal directives only as literal `///` lines or `#[doc = \"...\"]` attributes.",
            )
        )

    for seg_start, seg_end, seg_line, doc_body, is_inner in doc_segments:
        if is_inner:
            for off_l, raw_l in enumerate(doc_body.split("\n")):
                ann = parse_anneal_directive_line(raw_l, seg_line + off_l)
                if ann is not None:
                    findings.append(
                        WaiverPinFinding(
                            rule=RULE_DANGLING_WAIVER,
                            line=ann.line,
                            symbol=ann.directive,
                            tier=ann.tier,
                            message=(
                                f"`anneal:{ann.directive}` sits in an inner doc comment (`//!`, `/*! */`, "
                                "`#![doc]`), which documents the enclosing module rather than the next item."
                            ),
                            suggestion="Move the directive into an outer `///` doc comment on the target item.",
                        )
                    )

    for grp_start, grp_end, line_docs in _rust_outer_doc_groups(stripped, doc_segments):
        doc_lines = [
            (base_line + off_l, raw_l)
            for base_line, doc_body in line_docs
            for off_l, raw_l in enumerate(doc_body.split("\n"))
        ]
        anns, block_pins = _collect_block_directives(doc_lines)
        if not anns:
            continue
        pre_attr_start = _find_preceding_rust_attributes_start(stripped, grp_start)
        target_info = _extract_rust_target_span(stripped, grp_end, pre_attr_start)
        if target_info is None:
            for ann in anns:
                findings.append(
                    WaiverPinFinding(
                        rule=RULE_DANGLING_WAIVER,
                        line=ann.line,
                        symbol=ann.directive,
                        tier=ann.tier,
                        message=(
                            f"Dangling `anneal:{ann.directive}` waiver annotation with no following Rust item declaration."
                        ),
                        suggestion="Attach the waiver doc-comment directly to a `fn`, `struct`, `enum`, `union`, `type`, or `const` item.",
                    )
                )
            continue
        t_start, t_end, item_name = target_info
        hash_input = waiver_hash_input(anns, _normalize_rust_item(stripped[t_start:t_end]))
        findings.extend(_validate_waiver_block(anns, block_pins, item_name, hash_input))

    findings.sort(key=lambda f: (f.line, f.rule, f.symbol))
    return findings


# ---------------------------------------------------------------------------
# Lean 4 (`.lean`) Lexer, Waiver Pin Scanner & 3-Axis Non-Vacuity Auditor
# ---------------------------------------------------------------------------


def _scan_lean_comments_and_strings(
    text: str,
) -> tuple[str, list[tuple[int, int, int, str, str]]]:
    """Single-pass Lean 4 scanner returning:
    - `code_only`: comments AND string literals blanked (preserving offsets and `\\n`),
    - `comment_blocks`: list of `(start_off, end_off, start_line, comment_body, kind)` for `--`
      (`"l"`), `/- ... -/` (`"b"`), `/-- ... -/` docstrings (`"d"`), and `/-! ... -/` module
      docstrings (`"m"`).
    """
    n = len(text)
    if n == 0:
        return "", []
    out_code: list[str] = []
    comments: list[tuple[int, int, int, str, str]] = []
    app_c = out_code.append
    find = text.find
    line_of = _WaLineCounter(text)
    pos = 0
    i_blk = find("/-", 0)
    i_lin = find("--", 0)
    i_str = find('"', 0)
    i_gui = find("«", 0)

    while pos < n:
        if i_blk != -1 and i_blk < pos:
            i_blk = find("/-", pos)
        if i_lin != -1 and i_lin < pos:
            i_lin = find("--", pos)
        if i_str != -1 and i_str < pos:
            i_str = find('"', pos)
        if i_gui != -1 and i_gui < pos:
            i_gui = find("«", pos)

        nxt = n
        kind = 0
        if 0 <= i_blk < nxt:
            nxt = i_blk
            kind = 1
        if 0 <= i_lin < nxt:
            nxt = i_lin
            kind = 2
        if 0 <= i_str < nxt:
            nxt = i_str
            kind = 3
        if 0 <= i_gui < nxt:
            nxt = i_gui
            kind = 4

        if kind == 0:
            tail = text[pos:]
            app_c(tail)
            break
        if nxt > pos:
            seg = text[pos:nxt]
            app_c(seg)

        if kind == 4:
            if (
                nxt > 0
                and nxt + 1 < n
                and text[nxt - 1] == "'"
                and text[nxt + 1] == "'"
                and (nxt < 2 or (not _is_lean_ident_char(text[nxt - 2]) and text[nxt - 2] != "\\"))
            ):
                app_c(" ")
                pos = nxt + 1
                continue
            g_end = find("»", nxt + 1)
            if g_end != -1 and find("\n", nxt + 1, g_end) == -1:
                seg = text[nxt : g_end + 1]
                app_c(seg)
                pos = g_end + 1
            else:
                app_c("«")
                pos = nxt + 1
            continue

        if kind == 2:
            nl = find("\n", nxt + 2)
            end = n if nl == -1 else nl
            comments.append((nxt, end, 0, text[nxt + 2 : end], "l"))
            blank = " " * (end - nxt)
            app_c(blank)
            pos = end
            continue

        if kind == 1:
            depth = 1
            cur = nxt + 2
            while depth > 0 and cur < n:
                c = find("-/", cur)
                if c == -1:
                    cur = n
                    break
                o = find("/-", cur, c)
                if o != -1:
                    depth += 1
                    cur = o + 2
                else:
                    depth -= 1
                    cur = c + 2
            raw_blk = text[nxt:cur]
            inner = raw_blk[3 if raw_blk.startswith("/--") or raw_blk.startswith("/-!") else 2 : -2 if raw_blk.endswith("-/") else len(raw_blk)]
            c_kind = "d" if raw_blk.startswith("/--") else ("m" if raw_blk.startswith("/-!") else "b")
            c_line = line_of(nxt) if (c_kind in ("d", "m") and ("anneal:" in inner or "pin:" in inner)) else 0
            comments.append((nxt, cur, c_line, inner, c_kind))
            app_c(" " * (cur - nxt) if "\n" not in raw_blk else _wa_blank(raw_blk))
            pos = cur
            continue

        # String literal or quote char literal `'\"'` / `'"'`
        if nxt > 0 and text[nxt - 1] in "#r'\\":
            h = nxt
            while h > 0 and text[h - 1] == "#":
                h -= 1
            if (
                h > 0
                and text[h - 1] == "r"
                and (h < 2 or not (_is_lean_ident_char(text[h - 2]) or text[h - 2] == "."))
            ):
                closer = '"' + "#" * (nxt - h)
                c = find(closer, nxt + 1)
                cur = n if c == -1 else c + len(closer)
                seg = text[nxt:cur]
                app_c(_wa_blank(seg))
                pos = cur
                continue
            if (
                nxt + 1 < n
                and text[nxt + 1] == "'"
                and (
                    (
                        text[nxt - 1] == "'"
                        and (
                            nxt < 2
                            or (not _is_lean_ident_char(text[nxt - 2]) and text[nxt - 2] != "\\")
                        )
                    )
                    or (
                        nxt >= 2
                        and text[nxt - 2 : nxt] == "'\\"
                        and (nxt < 3 or not _is_lean_ident_char(text[nxt - 3]))
                    )
                )
            ):
                app_c(" ")
                pos = nxt + 1
                i_str = find('"', pos)
                continue

        cur = nxt + 1
        while cur < n:
            q = find('"', cur)
            if q == -1:
                cur = n
                break
            bs = 0
            k = q - 1
            while k >= nxt + 1 and text[k] == "\\":
                bs += 1
                k -= 1
            cur = q + 1
            if bs % 2 == 0:
                break
        seg = text[nxt:cur]
        app_c(_wa_blank(seg))
        pos = cur

    return "".join(out_code), comments


def _no_comments_slice(
    text: str, comment_blocks: list[tuple[int, int, int, str, str]], starts: list[int], a: int, b: int
) -> str:
    """`text[a:b]` with every comment blanked (string literals preserved), rebuilt on demand
    from the comment offsets (only pinned declarations need it, so the full-file
    comment-blanked copy is never materialized)."""
    k = _wa_bisect_right(starts, a) - 1
    if k < 0:
        k = 0
    parts: list[str] = []
    pos = a
    nb = len(comment_blocks)
    while k < nb:
        cs, ce = comment_blocks[k][0], comment_blocks[k][1]
        if cs >= b:
            break
        if ce > pos:
            lo = cs if cs > pos else pos
            if lo > pos:
                parts.append(text[pos:lo])
            hi = ce if ce < b else b
            parts.append(_wa_blank(text[lo:hi]))
            pos = hi
        k += 1
    if pos < b:
        parts.append(text[pos:b])
    return "".join(parts)


_LEAN_COL0_BOUNDARY_RE = re.compile(r"\n(?=\S)")
_LEAN_NONEMPTY_LINE_RE = re.compile(r"\n([ \t]*)(?=\S)")
_LEAN_CONTINUATION_RE = re.compile(
    r"[ \t]*(?:\||where\b|termination_by\b|decreasing_by\b|deriving\b(?![ \t]+instance\b))"
)
# A line at or left of the declaration's column ends it only if it starts a *command* (optionally
# preceded by `@[...]` attributes or declaration modifiers skipped by `_skip_lean_attrs_and_modifiers`).
# Lean term bodies (`def layoutSize : Nat :=\n8`) and column-0 `structure`/`where` members
# (`protected b : Nat`, `@[simp] aux : 1 = 1 := rfl`) are not followed by a command keyword after
# skipping `@[...]` and modifiers, so they remain inside the pinned span.
_LEAN_BARE_COMMAND_START_RE = re.compile(
    r"#[A-Za-z_]\w*(?!\[)|"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|example|"
    r"end|namespace|section|mutual|variable|universe|open|export|set_option|attribute|"
    r"notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules|"
    r"declare_syntax_cat|initialize|builtin_initialize|deriving|import|"
    r"omit|include|add_decl_doc|register_option|run_cmd|run_elab|run_meta|alias)\b"
)


def _is_lean_command_start(code_only: str, cand: int) -> bool:
    """Return `True` iff `code_only[cand:]` starts a top-level Lean command (after any `@[...]`
    attributes and declaration modifiers)."""
    kw = _skip_lean_attrs_and_modifiers(code_only, cand)
    return _LEAN_BARE_COMMAND_START_RE.match(code_only, kw) is not None


def _lean_indent_of(code_only: str, offset: int, text: str | None = None) -> int:
    """Return the column offset (`0`-based) of `offset`'s line indentation (ignoring any
    leading `/- ... -/` block comment on the same line when `text` is given).

    With `text`, this is the indentation used for a declaration's *own* start line, and it is
    deliberately the smallest plausible column: the first non-blank `text` column of the line,
    or, when the line opens with the tail of a block comment begun on an earlier line, the
    smaller of that and the comment opener's line indentation. A smaller declaration indent
    only keeps more following lines inside the span (conservative: never a pin bypass)."""
    nl = code_only.rfind("\n", 0, offset)
    line_start = 0 if nl == -1 else nl + 1
    if text is None:
        return offset - line_start
    p = line_start
    while p < offset and text[p] in " \t":
        p += 1
    indent = p - line_start
    if p < offset and not text.startswith("/-", p):
        open_pos = text.rfind("/-", 0, offset)
        if open_pos != -1:
            nl0 = text.rfind("\n", 0, open_pos)
            ls0 = 0 if nl0 == -1 else nl0 + 1
            q = ls0
            while q < open_pos and text[q] in " \t":
                q += 1
            if q == open_pos and q - ls0 < indent:
                indent = q - ls0
    return indent


def _find_lean_decl_end(
    code_only: str, after_hdr_pos: int, decl_indent: int = 0, text: str | None = None
) -> int:
    """Find the end offset of a Lean declaration starting at indentation `decl_indent` before `after_hdr_pos`.

    - Any line indented strictly deeper than `decl_indent` (`line_indent > decl_indent`) belongs to
      the declaration's body (`structure`/`class` fields, `where` auxiliary `def`s, tactics) and
      never ends the span.
    - Otherwise a line at `line_indent <= decl_indent` ends the span only if it starts a command
      (`_is_lean_command_start`: a command keyword optionally preceded by `@[...]` attributes and
      modifiers); non-command lines such as a column-0 term body (`def x : Nat :=\\n8`), column-0
      `protected b : Nat` / `@[simp] aux := rfl` members, and pattern-match / `where` /
      `termination_by` continuations stay inside.
    """
    n = len(code_only)
    pos = after_hdr_pos
    # Without any `-/` after the header no line can start with a closed same-line block comment
    # (`/- c -/ def next`), so column-0 `code_only` boundaries are exact. `find` (not `in` on a
    # slice) keeps this O(distance) instead of copying the rest of the file per declaration.
    if decl_indent <= 0 and (text is None or text.find("-/", after_hdr_pos) == -1):
        while pos < n:
            m = _LEAN_COL0_BOUNDARY_RE.search(code_only, pos)
            if m is None:
                return n
            cand = m.start() + 1
            if _LEAN_CONTINUATION_RE.match(code_only, cand) or not _is_lean_command_start(
                code_only, cand
            ):
                pos = cand + 1
                continue
            return m.start()
        return n

    while pos < n:
        m = _LEAN_NONEMPTY_LINE_RE.search(code_only, pos)
        if m is None:
            return n
        ws = m.group(1)
        cand = m.end()
        line_indent = len(ws)
        if text is not None and line_indent > decl_indent:
            # A block comment opened on this very line (`/- c -/ def next`) is blanked to spaces
            # in `code_only`; its opening column is the line's indentation only when at most one
            # space separates `-/` from the command token and the preceding non-empty line in
            # `code_only` is not `where` (so `where\n/- c -/  def helper` keeps `def helper`
            # inside the declaration's `where` block).
            line_start = m.start() + 1
            q = line_start
            while q < cand and text[q] in " \t":
                q += 1
            if q < cand and text.startswith("/-", q) and (
                text.endswith("-/", line_start, cand) or text.endswith("-/ ", line_start, cand)
            ):
                prev_end = m.start()
                while prev_end > after_hdr_pos and code_only[prev_end - 1] in " \t\r\n":
                    prev_end -= 1
                prev_nl = code_only.rfind("\n", after_hdr_pos, prev_end)
                prev_line = code_only[prev_nl + 1 if prev_nl != -1 else after_hdr_pos : prev_end].strip()
                if prev_line != "where" and not prev_line.endswith(" where"):
                    line_indent = q - line_start
        if line_indent > decl_indent:
            pos = cand + 1
            continue
        if _LEAN_CONTINUATION_RE.match(code_only, cand):
            pos = cand + 1
            continue
        if _is_lean_command_start(code_only, cand):
            return m.start()
        pos = cand + 1
    return n


def _extract_lean_decl_span(
    code_only: str, search_from: int, text: str | None = None
) -> tuple[int, int, str, str] | None:
    """Find the Lean declaration immediately following `search_from`.
    Returns `(start_off, end_off, decl_kind, decl_name)` or `None` if dangling."""
    n = len(code_only)
    i = search_from
    while i < n and code_only[i] in " \t\r\n":
        i += 1
    if i >= n:
        return None
    # If the next token is `end`, `namespace`, or `section`, the waiver is dangling!
    for bad_kw in ("end", "namespace", "section"):
        if code_only.startswith(bad_kw, i) and (
            i + len(bad_kw) >= n or not _is_lean_ident_char(code_only[i + len(bad_kw)])
        ):
            return None

    hit = _match_lean_decl_at(code_only, i, skip_in_prefixes=True)
    if hit is None:
        return None
    hdr_end, decl_kind, decl_name = hit
    end_off = _find_lean_decl_end(code_only, hdr_end, _lean_indent_of(code_only, i, text), text)
    return i, end_off, decl_kind, decl_name


_LEAN_DECL_KW_RE = re.compile(
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|example)\b"
    r"(?:[ \t\r\n]+([^\s({\[\:]+))?"
)


def _match_lean_decl_at(
    code_only: str, i: int, *, skip_in_prefixes: bool = False
) -> tuple[int, str, str] | None:
    """If a declaration starts at `i` (after optional `@[...]` attributes, whose arguments may
    nest brackets as in `@[aesop safe [constructors]]`, declaration modifiers, and optionally
    `<command> in` prefixes), return `(header_end, decl_kind, decl_name)`."""
    kw = (
        _skip_lean_prefixes_attrs_and_modifiers(code_only, i)
        if skip_in_prefixes
        else _skip_lean_attrs_and_modifiers(code_only, i)
    )
    m = _LEAN_DECL_KW_RE.match(code_only, kw)
    if m is None:
        return None
    return m.end(), m.group(1), m.group(2) or m.group(1)


# ---------------------------------------------------------------------------
# 3-Axis Theorem Metadata & `TRIVIAL_PROOF` / Vacuity Analysis
# ---------------------------------------------------------------------------

_3AXIS_LINE_RE = re.compile(
    r"^\s*(Kind|Witness|Assumes|Subject)\s*:\s*(.+?)\s*$", re.IGNORECASE
)

_LEAN_THM_NAME_RE = re.compile(r"[ \t\r\n]+([^ \t\r\n({\[:]+)")


def _iter_lean_theorem_headers(code_only: str) -> list[tuple[int, int, str]]:
    """Fast C-level `str.find` scanner returning `(kw_start, name_end, thm_name)`
    for every `theorem` or `lemma` declaration in `code_only`."""
    find = code_only.find
    name_match = _LEAN_THM_NAME_RE.match
    out: list[tuple[int, int, str]] = []
    for kw, kw_len in (("theorem", 7), ("lemma", 5)):
        idx = find(kw, 0)
        while idx != -1:
            nxt = find(kw, idx + kw_len)
            if idx > 0:
                prev_ch = code_only[idx - 1]
                if prev_ch.isalnum() or prev_ch in "_'!?":
                    idx = nxt
                    continue
            m = name_match(code_only, idx + kw_len)
            if m is not None:
                out.append((idx, m.end(), m.group(1)))
            idx = nxt
    out.sort()
    return out


_LEAN_MODIFIERS = (
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "nonrec",
    "scoped",
    "local",
)


def _skip_lean_attrs_and_modifiers(code_only: str, pos: int) -> int:
    """Advance `pos` past any whitespace, `@[...]` attributes, and declaration modifiers
    (`private`, `protected`, `noncomputable`, etc.) to the declaration keyword (`theorem`,
    `lemma`, `def`, ...)."""
    n = len(code_only)
    p = pos
    while p < n:
        while p < n and code_only[p] in " \t\r\n":
            p += 1
        if p >= n:
            break
        if code_only[p] == "@":
            q = p + 1
            while q < n and code_only[q] in " \t":
                q += 1
            if q < n and code_only[q] == "[":
                depth = 1
                q += 1
                while q < n and depth > 0:
                    c = code_only[q]
                    if c == "[":
                        depth += 1
                    elif c == "]":
                        depth -= 1
                    q += 1
                p = q
                continue
        matched_mod = False
        for mod in _LEAN_MODIFIERS:
            if code_only.startswith(mod, p):
                end_m = p + len(mod)
                if end_m < n and code_only[end_m] in " \t\r\n":
                    p = end_m + 1
                    matched_mod = True
                    break
        if not matched_mod:
            break
    return p


_LEAN_IN_PREFIX_CMD_RE = re.compile(
    r"(?:set_option|open|variable|universe|attribute|include|omit|export|"
    r"notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules)\b"
)
_LEAN_IN_TOKEN_RE = re.compile(r"[(){}\[\]\n]|:=|(?<![\w'!?.\u00bb])in(?![\w'!?.\u00bb])")


def _skip_lean_prefixes_attrs_and_modifiers(
    code_only: str, pos: int, limit: int | None = None
) -> int:
    """Advance `pos` past any whitespace, `@[...]` attributes, declaration modifiers, and
    `<command> in` prefixes (`set_option ... in`, `open ... in`, `variable ... in`,
    `attribute ... in`, ...) to the declaration keyword (`theorem`, `lemma`, `def`, ...)."""
    end_lim = len(code_only) if limit is None else min(len(code_only), limit)
    p = pos
    while p < end_lim:
        q = _skip_lean_attrs_and_modifiers(code_only, p)
        if q >= end_lim:
            return end_lim
        m = _LEAN_IN_PREFIX_CMD_RE.match(code_only, q)
        if m is None or m.end() > end_lim:
            return q
        depth = 0
        in_end = -1
        for tm in _LEAN_IN_TOKEN_RE.finditer(code_only, m.end(), end_lim):
            tok = tm.group()
            if tok in "({[":
                depth += 1
            elif tok in ")}]":
                if depth > 0:
                    depth -= 1
            elif tok == "in" and depth == 0:
                in_end = tm.end()
                break
            elif tok == ":=" and depth == 0:
                break
            elif tok == "\n" and depth == 0:
                cand = tm.end()
                while cand < end_lim and code_only[cand] in " \t\r\n":
                    cand += 1
                if cand < end_lim and _is_lean_command_start(code_only, cand):
                    break
        if in_end == -1:
            return q
        p = in_end
    return p


def _parse_3axis_metadata(comment_text: str) -> dict[str, str]:
    meta, _ = _parse_3axis_metadata_and_conflicts(comment_text)
    return meta


_PAREN_ONLY_RE = re.compile(r"[()]")
_WS_RUN_RE = re.compile(r"[ \t\r\n]+")
_STMT_END_SCAN_RE = re.compile(r"[(){}\[\]\n;]|:=|(?<![\w'!?.])let\b")
_ARROW_SCAN_RE = re.compile(r"[(){}\[\]]|→|->|∀|∃")
_PIPE_ARM_RE = re.compile(r"\n[ \t]*\|")


_BINDER_SCAN_RE = re.compile(r"[(){}\[\]]|:=|:")


def _scan_binder_group(seg: str, p: int, limit: int | None = None) -> tuple[int, int]:
    """For a bracket group opening at `seg[p]`, return `(offset past its matching close,
    offset of its first depth-1 `:` that is not `:=`, or -1)` using C-level `str.find`."""
    end_lim = len(seg) if limit is None else limit
    ch = seg[p]
    close_ch = ")" if ch == "(" else ("}" if ch == "{" else "]")
    find = seg.find
    cur = p + 1
    depth = 1
    while depth > 0 and cur < end_lim:
        c_close = find(close_ch, cur, end_lim)
        if c_close == -1:
            cur = end_lim
            break
        c_open = find(ch, cur, c_close)
        if c_open != -1:
            depth += 1
            cur = c_open + 1
        else:
            depth -= 1
            cur = c_close + 1
    # Find the binder's `:` before any nested bracket
    col_idx = find(":", p + 1, cur - 1 if cur > p + 1 else cur)
    if col_idx != -1 and (col_idx + 1 >= cur or seg[col_idx + 1] != "="):
        # Verify no unclosed bracket opened before `col_idx`
        prefix = seg[p + 1 : col_idx]
        if (
            prefix.count("(") == prefix.count(")")
            and prefix.count("{") == prefix.count("}")
            and prefix.count("[") == prefix.count("]")
        ):
            return cur, col_idx
    return cur, -1


def _is_outer_paren_wrapped(t: str) -> bool:
    """Return `True` iff `t` starts with `(` and that opening `(` closes at `len(t) - 1`."""
    n = len(t)
    if n < 2 or t[0] != "(" or t[-1] != ")":
        return False
    find = t.find
    cur = 1
    depth = 1
    while depth > 0 and cur < n:
        c_close = find(")", cur, n)
        if c_close == -1:
            return False
        c_open = find("(", cur, c_close)
        if c_open != -1:
            depth += 1
            cur = c_open + 1
        else:
            depth -= 1
            if depth == 0:
                return c_close == n - 1
            cur = c_close + 1
    return False


def _split_lean_theorem_header_ex(
    code_segment: str, after_name_pos: int, limit_end: int | None = None
) -> tuple[list[tuple[str, str]], str, list[str]] | None:
    """Given `code_segment`, parse starting at `after_name_pos` (up to `limit_end`):
    - explicit/implicit binders `(x : T)`, `{x : T}`, `[inst : C]` before `:`,
    - top-level `∀ ...,` and `→` (`->`) premises inside the theorem statement,
    - the final conclusion before top-level `:=`, `where`, or `|`, and
    - any untracked binders (untyped `(x)`/`{x}`/bare names or unnamed `[C]` instances).
    Returns `(hypotheses_as_(binder_names, type_str), conclusion_str, extra_binders)`.
    """
    n = len(code_segment) if limit_end is None else min(len(code_segment), limit_end)
    i = after_name_pos
    if i < n and code_segment[i] == "." and code_segment.startswith(".{", i):
        close_u = code_segment.find("}", i + 2, n)
        if close_u != -1:
            i = close_u + 1

    binders: list[tuple[str, str]] = []
    extra_binders: list[str] = []
    colon_pos = -1
    p = i
    find = code_segment.find
    while p < n:
        ch = code_segment[p]
        if ch in " \t\r\n":
            p += 1
            while p < n and code_segment[p] in " \t\r\n":
                p += 1
            continue
        if ch == ":":
            if p + 1 < n and code_segment[p + 1] == "=":
                return None
            colon_pos = p
            break
        if ch in "({[":
            close_ch = ")" if ch == "(" else ("}" if ch == "{" else "]")
            fast_close = find(close_ch, p + 1, n)
            if fast_close != -1 and find(ch, p + 1, fast_close) == -1:
                col_idx = find(":", p + 1, fast_close)
                if col_idx != -1 and (
                    col_idx + 1 >= fast_close or code_segment[col_idx + 1] != "="
                ):
                    binders.append(
                        (
                            code_segment[p + 1 : col_idx].strip(),
                            code_segment[col_idx + 1 : fast_close].strip(),
                        )
                    )
                else:
                    inner = code_segment[p + 1 : fast_close].strip()
                    if inner:
                        extra_binders.append(f"[{inner}]" if ch == "[" else f"untyped:{inner}")
                p = fast_close + 1
                continue
            q, colon_in_binder = _scan_binder_group(code_segment, p, n)
            if colon_in_binder != -1:
                binders.append(
                    (
                        code_segment[p + 1 : colon_in_binder].strip(),
                        code_segment[colon_in_binder + 1 : q - 1].strip(),
                    )
                )
            else:
                inner = code_segment[p + 1 : q - 1].strip() if q > p + 1 else ""
                if inner:
                    extra_binders.append(f"[{inner}]" if ch == "[" else f"untyped:{inner}")
            p = q
            continue
        if ch == "w" and code_segment.startswith("where", p):
            return None
        extra_binders.append("bare")
        p += 1

    if colon_pos == -1:
        return None

    # Fast path to find top-level `:=` separating theorem statement from proof body
    stmt_start = colon_pos + 1
    stmt_end = -1
    prefix_slice = ""
    search_eq = stmt_start
    while search_eq < n:
        eq_pos = find(":=", search_eq, n)
        if eq_pos == -1:
            break
        prefix_slice = code_segment[stmt_start:eq_pos]
        if (
            prefix_slice.count("(") == prefix_slice.count(")")
            and prefix_slice.count("{") == prefix_slice.count("}")
            and prefix_slice.count("[") == prefix_slice.count("]")
        ):
            if "let " in prefix_slice:
                last_let = prefix_slice.rfind("let ")
                if "\n" not in prefix_slice[last_let:] and ";" not in prefix_slice[last_let:]:
                    search_eq = eq_pos + 2
                    continue
            stmt_end = eq_pos
            break
        search_eq = eq_pos + 2

    # Check if a pattern-matching arm `\n  | ... =>` or `where` ended the statement before `stmt_end`
    if stmt_end == -1 or "=>" in prefix_slice:
        # Clamp to `n`: the statement can never run into the next theorem, and the parse must stay a
        # pure function of `code_segment[after_name_pos:n]` (the `_THM_AUDIT_CACHE` key).
        search_bound = stmt_end if stmt_end != -1 else n
        pipe_m = _PIPE_ARM_RE.search(code_segment, stmt_start, search_bound)
        if pipe_m is not None:
            decl_end_bound = pipe_m.start()
        else:
            decl_end_bound = (
                stmt_end if stmt_end != -1 else min(_find_lean_decl_end(code_segment, stmt_start), n)
            )
            w_pos = find("where", stmt_start, decl_end_bound)
            if w_pos != -1 and (w_pos == stmt_start or code_segment[w_pos - 1] in " \t\r\n"):
                decl_end_bound = w_pos
        stmt = code_segment[stmt_start:decl_end_bound].strip()
    else:
        stmt = prefix_slice.strip()
    if not stmt:
        return None

    hyps = list(binders)
    cur_stmt = stmt
    while cur_stmt:
        while cur_stmt[0] == "(" and cur_stmt[-1] == ")" and _is_outer_paren_wrapped(cur_stmt):
            cur_stmt = cur_stmt[1:-1].strip()
            if not cur_stmt:
                break

        if not cur_stmt:
            break

        c0 = cur_stmt[0]
        if c0 == "∀" or (
            c0 == "f"
            and cur_stmt.startswith("forall")
            and len(cur_stmt) > 6
            and not _is_lean_ident_char(cur_stmt[6])
        ):
            q_len = 1 if c0 == "∀" else 6
            idx_q = q_len
            comma_idx = -1
            n_cur = len(cur_stmt)
            find_cur = cur_stmt.find
            saw_q_group = False
            saw_q_bare_before_colon = False
            saw_q_bare_colon = False
            while idx_q < n_cur:
                c2 = cur_stmt[idx_q]
                if c2 in " \t\r\n":
                    idx_q += 1
                    continue
                if c2 in "({[":
                    if not saw_q_bare_colon:
                        saw_q_group = True
                    close_ch = ")" if c2 == "(" else ("}" if c2 == "{" else "]")
                    fast_close = find_cur(close_ch, idx_q + 1, n_cur)
                    if fast_close != -1 and find_cur(c2, idx_q + 1, fast_close) == -1:
                        if not saw_q_bare_colon:
                            col_in = find_cur(":", idx_q + 1, fast_close)
                            if col_in != -1 and (
                                col_in + 1 >= fast_close or cur_stmt[col_in + 1] != "="
                            ):
                                hyps.append(
                                    (
                                        cur_stmt[idx_q + 1 : col_in].strip(),
                                        cur_stmt[col_in + 1 : fast_close].strip(),
                                    )
                                )
                            else:
                                inner = cur_stmt[idx_q + 1 : fast_close].strip()
                                if inner:
                                    extra_binders.append(
                                        f"[{inner}]" if c2 == "[" else f"untyped:{inner}"
                                    )
                        idx_q = fast_close + 1
                        continue
                    r, col_in = _scan_binder_group(cur_stmt, idx_q, n_cur)
                    if not saw_q_bare_colon:
                        if col_in != -1:
                            hyps.append(
                                (
                                    cur_stmt[idx_q + 1 : col_in].strip(),
                                    cur_stmt[col_in + 1 : r - 1].strip(),
                                )
                            )
                        else:
                            inner = cur_stmt[idx_q + 1 : r - 1].strip() if r > idx_q + 1 else ""
                            if inner:
                                extra_binders.append(
                                    f"[{inner}]" if c2 == "[" else f"untyped:{inner}"
                                )
                    idx_q = r
                    continue
                if c2 == ",":
                    comma_idx = idx_q
                    break
                if (
                    c2 == ":"
                    and not saw_q_group
                    and (idx_q + 1 >= n_cur or cur_stmt[idx_q + 1] != "=")
                ):
                    saw_q_bare_colon = True
                elif not saw_q_bare_colon:
                    saw_q_bare_before_colon = True
                idx_q += 1
            if comma_idx != -1:
                raw_q_binders = cur_stmt[q_len:comma_idx].strip()
                if saw_q_bare_colon and not saw_q_group:
                    b_n, _, b_t = raw_q_binders.partition(":")
                    hyps.append((b_n.strip(), b_t.strip()))
                elif saw_q_bare_before_colon:
                    extra_binders.append("bare")
                cur_stmt = cur_stmt[comma_idx + 1 :].strip()
                continue

        if "→" not in cur_stmt and "->" not in cur_stmt:
            break

        if "->" not in cur_stmt and not cur_stmt.startswith(("∃", "exists")):
            arrow_parts = cur_stmt.split("→")
            if all(
                "∀" not in p_seg
                and "∃" not in p_seg
                and "forall" not in p_seg
                and p_seg.count("(") == p_seg.count(")")
                and p_seg.count("{") == p_seg.count("}")
                and p_seg.count("[") == p_seg.count("]")
                for p_seg in arrow_parts[:-1]
            ):
                for p_seg in arrow_parts[:-1]:
                    hyps.append(("", p_seg.strip()))
                cur_stmt = arrow_parts[-1].strip()
                if (
                    cur_stmt.startswith("(")
                    or cur_stmt.startswith("∀")
                    or (cur_stmt.startswith("forall") and len(cur_stmt) > 6 and not _is_lean_ident_char(cur_stmt[6]))
                ):
                    continue
                break

        # Single-pass scan for all top-level `→` / `->` premises up to any top-level `∀`/`∃` or `(` wrapper
        depth_a = 0
        seg_start = 0
        advanced = False
        re_loop = False
        for m_a in _ARROW_SCAN_RE.finditer(cur_stmt):
            t_a = m_a.group(0)
            if t_a in "({[":
                depth_a += 1
            elif t_a in ")}]":
                if depth_a > 0:
                    depth_a -= 1
            elif depth_a == 0:
                if t_a == "∀" or t_a == "∃":
                    if m_a.start() == seg_start and t_a == "∀":
                        re_loop = True
                    break
                hyps.append(("", cur_stmt[seg_start : m_a.start()].strip()))
                seg_start = m_a.end()
                advanced = True
                while seg_start < len(cur_stmt) and cur_stmt[seg_start] in " \t\r\n":
                    seg_start += 1
                if seg_start < len(cur_stmt) and (
                    cur_stmt[seg_start] in "(∀"
                    or (cur_stmt[seg_start] == "f" and cur_stmt.startswith("forall", seg_start))
                ):
                    re_loop = True
                    break

        if advanced:
            cur_stmt = cur_stmt[seg_start:].strip()
            if re_loop:
                continue
        break

    return hyps, cur_stmt, extra_binders


def _split_lean_theorem_header(
    code_segment: str, after_name_pos: int, limit_end: int | None = None
) -> tuple[list[tuple[str, str]], str] | None:
    """Given `code_segment`, parse starting at `after_name_pos` (up to `limit_end`):
    - explicit/implicit binders `(x : T)`, `{x : T}`, `[C]` before `:`,
    - top-level `∀ ...,` and `→` (`->`) premises inside the theorem statement, and
    - the final conclusion before top-level `:=`, `where`, or `|`.
    Returns `(hypotheses_as_(binder_names, type_str), conclusion_str)`.
    """
    res = _split_lean_theorem_header_ex(code_segment, after_name_pos, limit_end)
    return None if res is None else (res[0], res[1])


_NORM_CACHE: dict[str, str] = {}


def _norm_expr(s: str) -> str:
    """Normalize whitespace and strip redundant outer parentheses of a Lean expression.

    Results are memoized in `_NORM_CACHE`, which `audit_lean_text` clears at the start of every
    scan (deduplication within one file only; no state survives across scans)."""
    hit = _NORM_CACHE.get(s)
    if hit is not None:
        return hit
    res = _norm_expr_uncached(s)
    _NORM_CACHE[s] = res
    return res


def _norm_expr_uncached(s: str) -> str:
    if "\n" not in s and "  " not in s and "\t" not in s and "\r" not in s:
        t = s.strip()
    else:
        t = " ".join(s.split())
    while len(t) >= 2 and t[0] == "(" and t[-1] == ")" and _is_outer_paren_wrapped(t):
        t = t[1:-1].strip()
    return t


_NUM_LIT_RE = re.compile(r"^\d+$")
_DIGIT_SEARCH = re.compile(r"\d").search
_REL_OP_SEARCH = re.compile(r"[=≠<≤>≥∧∨↔¬]").search
_S0_PIN_TRIGGER_SEARCH = re.compile(
    r"paddingFree|adtPad|hasPinnedCoupledWaiver|pad0|totalPad|rustOrderCanonical|evalConst|compileTimeError"
).search
_RUST_ORDER_CANON_RE = re.compile(r"rustOrderCanonical\s*:?=\s*true")
_IDENT_EXTRACT_RE = re.compile(r"[^\W\d][\w'!?]*")
_DATA_TYPE_WORDS = frozenset(
    (
        "Nat",
        "Int",
        "Bool",
        "String",
        "UInt8",
        "UInt16",
        "UInt32",
        "UInt64",
        "USize",
        "Unit",
        "Type",
        "Prop",
        "Sort",
        "List",
        "Array",
        "Option",
        "Vector",
    )
)


_SPLIT_RE_CACHE: dict[str, re.Pattern[str]] = {}
_TOP_SPLIT_RE_CACHE: dict[str, re.Pattern[str]] = {}


def _split_top_level(expr: str, sep: str) -> list[str]:
    """Split `expr` on `sep` occurrences outside `()`, `[]`, `{}`, `⟨⟩`, and `«...»` (C-level `finditer`)."""
    if sep not in expr:
        return [_norm_expr(expr)]
    pat = _TOP_SPLIT_RE_CACHE.get(sep)
    if pat is None:
        pat = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩]|" + re.escape(sep))
        _TOP_SPLIT_RE_CACHE[sep] = pat
    parts: list[str] = []
    depth = 0
    start = 0
    for m in pat.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            parts.append(expr[start : m.start()])
            start = m.end()
    parts.append(expr[start:])
    return [_norm_expr(p) for p in parts]


_TOP_LEVEL_ARROW_RE = re.compile(
    r"«[^»]*»|[()\[\]{}⟨⟩]|→|(?<![<←])->|∀|∃|λ|"
    r"(?<![\w'.!?])(?:forall|exists|fun|if|match|let|have|show|by)(?![\w'!?])"
)
_TOP_LEVEL_LOOSER_THAN_NOT_RE = re.compile(
    r"«[^»]*»|[()\[\]{}⟨⟩]|↔|<->|→|->|∨|\\/|∧|/\\|∀|∃|λ|"
    r"(?<![\w'.!?])(?:forall|exists|fun|if|match|let|have|show|by)(?![\w'!?])"
)
_CONJ_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩]|∧|/\\")
_CONJ_TOP_BOUND_RE = re.compile(
    r"«[^»]*»|[()\[\]{}⟨⟩]|↔|<->|→|->|<\|>|<\||\|>|\$|∨|\\/|∀|∃|λ|"
    r"(?<![\w'.!?])(?:forall|exists|fun|if|match|let|have|show|by)(?![\w'!?])"
)


def _has_top_level_arrow(expr: str) -> bool:
    """`True` iff `expr` contains a top-level (depth-0 outside `()[]{}⟨⟩` and `«...»`)
    implication/function arrow `→` or `->` before any depth-0 prefix binder (`∀`, `∃`, `fun`,
    `λ`, `if`, `match`, `let`, `have`, `show`, `by`)."""
    if "→" not in expr and "->" not in expr:
        return False
    depth = 0
    for m in _TOP_LEVEL_ARROW_RE.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            return t in ("→", "->")
    return False


def _has_top_level_looser_than_not(expr: str) -> bool:
    """`True` iff `expr` contains a top-level (depth-0 outside `()[]{}⟨⟩` and `«...»`)
    connective with lower Lean 4 precedence than prefix `¬` (prec 40) — namely `∧`/`/\\` (35),
    `∨`/`\\/` (30), `→`/`->` (25), or `↔`/`<->` (20) — before any depth-0 prefix binder.

    In Lean 4, `¬ P → α` parses as `(¬ P) → α` (NOT `¬ (P → α)`), and `¬ P ∨ Q` parses as
    `(¬ P) ∨ Q` (NOT `¬ (P ∨ Q)`), whereas `¬ (P → α)` has `→` at depth 1 and returns `False`.
    """
    if (
        "→" not in expr
        and "->" not in expr
        and "↔" not in expr
        and "<->" not in expr
        and "∨" not in expr
        and "\\/" not in expr
        and "∧" not in expr
        and "/\\" not in expr
    ):
        return False
    depth = 0
    for m in _TOP_LEVEL_LOOSER_THAN_NOT_RE.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            return t in ("↔", "<->", "→", "->", "∨", "\\/", "∧", "/\\")
    return False


def _split_top_level_conjuncts(expr: str) -> list[str]:
    """Split `expr` on top-level `∧` / `/\\` conjuncts outside `()[]{}⟨⟩` and `«...»`,
    only when no looser connective (`↔`, `<->`, `→`, `->`, `∨`, `\\/`, `<|>`, `<|`, `|>`, `$`)
    governs `expr` at depth 0, recursively flattening parenthesized conjunctions."""
    if "∧" not in expr and "/\\" not in expr:
        return [expr]
    bound = len(expr)
    depth = 0
    for m in _CONJ_TOP_BOUND_RE.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if t in ("↔", "<->", "→", "->", "<|>", "<|", "|>", "$", "∨", "\\/"):
                return [expr]
            bound = m.start()
            break
    if bound <= 0:
        return [expr]
    parts: list[str] = []
    depth = 0
    start = 0
    for m in _CONJ_SPLIT_RE.finditer(expr, 0, bound):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            parts.append(expr[start : m.start()])
            start = m.end()
    if not parts:
        return [expr]
    parts.append(expr[start:])
    out: list[str] = []
    for raw_p in parts:
        np = _norm_expr(raw_p)
        if not np:
            continue
        if ("∧" in np or "/\\" in np) and len(np) < len(expr):
            out.extend(_split_top_level_conjuncts(np))
        else:
            out.append(np)
    return out if out else [expr]


_TOP_BOUND_RE = re.compile(
    r"[()\[\]{}]|↔|→|->|<\|>|<\||\|>|\$|∨|∃|∀|λ|"
    r"(?<![\w'.!?])(?:fun|forall|exists|if|match|let|have|show|by)(?![\w'!?])"
)


def _find_top_level_bound(expr: str, *, allow_or: bool) -> int:
    """Return the character offset of the first depth-0 prefix binder/keyword (`∀`, `∃`, `fun`,
    `λ`, `if`, `match`, `let`, `have`, `show`, `by`) whose body extends to the end of `expr`,
    `len(expr)` if none exists, or `-1` if a depth-0 infix connective looser than the target
    (`↔`, `→`, `->`, `<|>`, `<|`, `|>`, `$`, plus `∨` when `allow_or=False`) appears before any
    prefix binder.

    Notice why distinguishing prefix binders from looser infix connectives is essential:
    - In `p ↔ q ∨ True`, `↔` (precedence 20) binds looser than `∨` (30) across the whole
      expression (`p ↔ (q ∨ True)`), so `∨` is NOT the top-level connective (`return -1`).
    - In `f = fun x => x ∨ True` or `∃ y : Nat, y = y ∨ p`, the prefix binder starts at offset
      `4` / `0` *before* `∨`, so there is no `∨` in `expr[:bound]` and `∨` is inside the binder.
    - In `True ∨ ∀ x : Nat, P x` or `x = x ∨ ∃ y : Nat, y > x` or `True ∨ if c then p else q`,
      `∨` appears in `expr[:bound]` *before* the prefix binder, so `∨` IS the top-level connective
      and `expr[op_end:]` (containing the prefix binder) is the right-hand disjunct!
    """
    depth = 0
    for m in _TOP_BOUND_RE.finditer(expr):
        t = m.group(0)
        if t in "([{":
            depth += 1
        elif t in ")]}":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if t in ("↔", "→", "->", "<|>", "<|", "|>", "$"):
                return -1
            if t == "∨":
                if not allow_or:
                    return -1
                continue
            return m.start()
    return len(expr)


def _all_conjuncts_trivial(expr: str) -> bool:
    """`True` iff `expr` has >= 2 top-level `∧` conjuncts and all are trivially true; stops at
    the first non-trivial conjunct (so long genuine conclusions cost one conjunct check)."""
    idx = expr.find("∧")
    if idx == -1:
        return False
    first = expr[:idx]
    if (
        first.count("(") == first.count(")")
        and first.count("[") == first.count("]")
        and first.count("{") == first.count("}")
        and not _is_trivially_true(first)
    ):
        return False
    bound = _find_top_level_bound(expr, allow_or=False)
    if bound <= 0:
        return False
    pat = _SPLIT_RE_CACHE.get("∧")
    if pat is None:
        pat = re.compile(r"[()\[\]{}]|∧")
        _SPLIT_RE_CACHE["∧"] = pat
    depth = 0
    start = 0
    count = 0
    for m in pat.finditer(expr, 0, bound):
        t = m.group(0)
        if t in "([{":
            depth += 1
        elif t in ")]}":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if not _is_trivially_true(expr[start : m.start()]):
                return False
            count += 1
            start = m.end()
    return count >= 1 and _is_trivially_true(expr[start:])


def _any_disjunct_trivial(expr: str) -> bool:
    """`True` iff `expr` has >= 2 top-level `∨` disjuncts and at least one is trivially true
    (e.g. `P ∨ True`, `x = x ∨ P`, or `True ∨ ∀ x, P x`, which can be discharged by
    `Or.inr trivial` / `Or.inl rfl` without proving `P`)."""
    bound = _find_top_level_bound(expr, allow_or=True)
    if bound <= 0:
        return False
    pat = _SPLIT_RE_CACHE.get("∨")
    if pat is None:
        pat = re.compile(r"[()\[\]{}]|∨")
        _SPLIT_RE_CACHE["∨"] = pat
    depth = 0
    start = 0
    count = 0
    found_trivial = False
    for m in pat.finditer(expr, 0, bound):
        t = m.group(0)
        if t in "([{":
            depth += 1
        elif t in ")]}":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            count += 1
            if _is_trivially_true(expr[start : m.start()]):
                found_trivial = True
            start = m.end()
    if count == 0:
        return False
    return found_trivial or _is_trivially_true(expr[start:])


_STANDALONE_EQ_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩]|(?<![=!<>:])=(?!=)")


def _split_top_level_eq(expr: str) -> list[str]:
    """Split `expr` on top-level standalone `=` (excluding `==`, `:=`, `!=`, `<=`, `>=`) outside `()[]{}⟨⟩` and `«...»`."""
    parts: list[str] = []
    depth = 0
    start = 0
    for m in _STANDALONE_EQ_SPLIT_RE.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            parts.append(expr[start : m.start()])
            start = m.end()
    parts.append(expr[start:])
    return [_norm_expr(p) for p in parts]


def _is_trivially_true(conj: str) -> bool:
    """`True`, `¬ False`, a reflexive `a = a` / `a ↔ a` / `a ≤ a` conjunct, a parenthesized
    trivial conjunction/disjunction, or a universally quantified `∀ ..., <trivial>` whose body is
    itself trivially true."""
    raw = conj.strip()
    if raw in ("True", "¬ False", "¬False"):
        return True
    if "=" not in raw and "↔" not in raw and "≤" not in raw and "True" not in raw and "False" not in raw:
        return False
    c = _norm_expr(raw)
    if c in ("True", "¬ False", "¬False"):
        return True
    if len(c) < len(raw):
        if "∧" in c and _all_conjuncts_trivial(c):
            return True
        if "∨" in c and _any_disjunct_trivial(c):
            return True
    if c.startswith("∀") or (
        c.startswith("forall") and len(c) > 6 and not _is_lean_ident_char(c[6])
    ):
        q_len = 1 if c.startswith("∀") else 6
        idx_q = q_len
        n_c = len(c)
        while idx_q < n_c:
            ch = c[idx_q]
            if ch in "({[":
                idx_q, _ = _scan_binder_group(c, idx_q, n_c)
                continue
            if ch == ",":
                body = _norm_expr(c[idx_q + 1 :])
                return (
                    _is_trivially_true(body)
                    or ("∧" in body and _all_conjuncts_trivial(body))
                    or ("∨" in body and _any_disjunct_trivial(body))
                )
            idx_q += 1
    for op in ("↔", "≤", "="):
        if op not in c:
            continue
        if op == "=":
            if c.count("=") == 1 and ":=" not in c:
                lhs, _, rhs = c.partition("=")
                if (
                    lhs.count("(") == lhs.count(")")
                    and lhs.count("[") == lhs.count("]")
                    and lhs.count("{") == lhs.count("}")
                ):
                    nl = _norm_expr(lhs)
                    if nl and nl == _norm_expr(rhs):
                        return True
                continue
            sides = _split_top_level_eq(c)
            if len(sides) == 2 and sides[0] and sides[0] == sides[1]:
                return True
            continue
        if c.count(op) == 1:
            lhs, _, rhs = c.partition(op)
            if (
                lhs.count("(") == lhs.count(")")
                and lhs.count("[") == lhs.count("]")
                and lhs.count("{") == lhs.count("}")
            ):
                nl = _norm_expr(lhs)
                if nl and nl == _norm_expr(rhs):
                    return True
            continue
        sides = _split_top_level(c, op)
        if len(sides) == 2 and sides[0] and sides[0] == sides[1]:
            return True
    return False


_NAT_LIKE_TYPES = frozenset(("Nat", "ℕ", "UInt8", "UInt16", "UInt32", "UInt64", "USize"))
# Generic projections that are always `Nat` (`.length`, `.size`, `.toNat`) plus this repository's
# `Nat`-typed layout fields. NOT `.fst` / `.val` / `.bytes` (A2): `(p : Int × Nat) (h : p.fst < 0)`
# and `(x : {z : Int // z < 5}) (h : x.val < 0)` are satisfiable, so flagging them is a false positive.
_NAT_VALUED_SUFFIXES = (
    ".length",
    ".size",
    ".toNat",
    ".pad0",
    ".padMid",
    ".padTail",
    ".totalPad",
    ".totalSize",
    ".align",
    ".repadWidth",
    ".sumFieldWidths",
    ".totalPadBytes",
    ".tagByteWidth",
    ".toTag",
    ".rawWidth",
)
_NAT_VALUED_PREFIXES = (
    "sumSizes ",
    "maxAlign ",
    "cEnd ",
    "memKey ",
    "nzBit ",
    "Nat.",
    "MirValueCodec.uintByteSize ",
    "Mir.PlaceAndRvalue.alignUp ",
    "PlaceAndRvalue.alignUp ",
)
_NAT_ARITH_SPLIT_RE = re.compile(r"[+*/%^]")


def _is_atomic_nat_like(e: str, nat_vars: frozenset[str]) -> bool:
    return (
        e in nat_vars
        or _NUM_LIT_RE.match(e) is not None
        or e.endswith(_NAT_VALUED_SUFFIXES)
        or e.startswith(_NAT_VALUED_PREFIXES)
    )


def _is_nat_like_operand(e: str, nat_vars: frozenset[str]) -> bool:
    """`True` iff `e` is syntactically `Nat`-valued: a numeral, a binder declared `Nat`-like, a
    known `Nat`-valued projection/function (`.length`, `.size`, `.toNat`, `.totalPad`, `.totalSize`,
    `sumSizes ...`, etc.), or a `+`/`*`/`/`/`%`/`^` combination of `Nat`-like operands. Anything
    else (`f x`, an `Int` / `Real` binder, an undeclared name) may be negative, so `e < 0` is NOT
    a syntactic contradiction for it."""
    if _is_atomic_nat_like(e, nat_vars):
        return True
    if any(op in e for op in ("+", "*", "/", "%", "^")):
        atoms = [a.strip("() ") for a in _NAT_ARITH_SPLIT_RE.split(e)]
        return bool(atoms) and all(a and _is_atomic_nat_like(a, nat_vars) for a in atoms)
    return False


_PURE_DATA_BASE_TYPES = frozenset(
    (
        "Nat",
        "ℕ",
        "Int",
        "ℤ",
        "Bool",
        "String",
        "Char",
        "Unit",
        "PUnit",
        "UInt8",
        "UInt16",
        "UInt32",
        "UInt64",
        "USize",
        "Int8",
        "Int16",
        "Int32",
        "Int64",
        "ISize",
        "Float",
        "ByteArray",
    )
)
_ALWAYS_INHABITED_CONTAINERS = frozenset(("List", "Array", "Option", "BitVec"))
_PARAM_DATA_CONTAINERS = frozenset(("Sum", "Except", "Prod"))
_SAFE_TYPECLASS_HEADS = frozenset(
    (
        "Decidable",
        "DecidableEq",
        "DecidablePred",
        "DecidableRel",
        "BEq",
        "Ord",
        "Repr",
        "ToString",
        "Hashable",
        "SizeOf",
    )
)
_TYPE_UNIVERSE_RE = re.compile(r"^Type(?:\*|\s+(?:[\w.+*]+|\([\w\s.+*]+\)))?$")
_NON_PROP_FORBIDDEN_RE = re.compile(r"[=≠<≤>≥¬∀∃{⊕]|//|:=")
_TOP_LEVEL_INFIX_FOR_TC_RE = re.compile(
    r"«[^»]*»|[()\[\]{}⟨⟩]|×|⊕|:=|//|(?<![=!<>:])=(?!=)|≠|<|≤|>|≥"
)


def _is_type_universe(bt: str) -> bool:
    """`True` iff normalized `bt` is `Type`, `Type*`, or `Type <level>` (strictly above `Prop`;
    excludes `Sort u` which can instantiate to `Prop`)."""
    return _TYPE_UNIVERSE_RE.match(bt) is not None


def _is_safe_typeclass_expr(expr: str) -> bool:
    """`True` iff `expr` is a top-level application of a safe computational typeclass
    (e.g. `Decidable P`, `Decidable (a = b)`, `DecidableEq α`, `BEq α`) with no top-level
    propositional connective or infix relation/product."""
    e = _norm_expr(expr)
    if not e or " " not in e or _has_top_level_looser_than_not(e):
        return False
    head = e.split(None, 1)[0]
    if head not in _SAFE_TYPECLASS_HEADS:
        return False
    depth = 0
    for m in _TOP_LEVEL_INFIX_FOR_TC_RE.finditer(e):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            return False
    return True


def _is_non_prop_binder_type(b_type: str, type_vars: frozenset[str]) -> bool:
    """Conservatively return `True` iff `b_type` is unambiguously a non-propositional data,
    universe/type, or safe computational typeclass binder (never a `Prop` assumption,
    uninhabited type like `Empty`/`Fin 0`, subtype `{x // P x}`, or predicate application)."""
    bt = _norm_expr(b_type)
    if not bt or _has_top_level_looser_than_not(bt):
        return False
    if _is_safe_typeclass_expr(bt):
        return True
    if _NON_PROP_FORBIDDEN_RE.search(bt) is not None:
        return False
    if bt == "Prop" or _is_type_universe(bt):
        return True
    if bt in _PURE_DATA_BASE_TYPES or bt in type_vars:
        return True
    if "×" in bt:
        factors = _split_top_level(bt, "×")
        if len(factors) >= 2:
            return all(f in _PURE_DATA_BASE_TYPES or f in type_vars for f in factors)
    parts = bt.split()
    if len(parts) >= 2:
        head = parts[0]
        if head in _ALWAYS_INHABITED_CONTAINERS:
            return True
        if head in _PARAM_DATA_CONTAINERS and all(
            p.strip("()") in _PURE_DATA_BASE_TYPES or p.strip("()") in type_vars
            for p in parts[1:]
        ):
            return True
    return False


def _is_single_premise_false_elim(
    all_hyps: list[tuple[str, str]],
    target_idx: int,
    extra_binders: list[str] | tuple[str, ...] = (),
) -> bool:
    """`True` iff `all_hyps[target_idx]` is the sole propositional premise of a `: False`
    refutation (`noConfusion`) theorem: `target_idx` binds at most one premise name (rejects
    `(h1 h2 : false = true)`), every other binder in `all_hyps` is a named non-propositional
    data/type/safe-typeclass binder tracked in telescope order, and `extra_binders` contains no
    untyped binders or unsafe anonymous typeclass instances (e.g. `[Fact P]`)."""
    t_names, _ = all_hyps[target_idx]
    if len(t_names.split()) > 1:
        return False
    for eb in extra_binders:
        if not (eb.startswith("[") and eb.endswith("]") and _is_safe_typeclass_expr(eb[1:-1])):
            return False
    type_vars: set[str] = set()
    for i, (b_names, b_type) in enumerate(all_hyps):
        if i == target_idx:
            for tok in b_names.split():
                type_vars.discard(tok)
            continue
        if not b_names:
            return False
        bt = _norm_expr(b_type)
        if not _is_non_prop_binder_type(bt, frozenset(type_vars)):
            return False
        if _is_type_universe(bt):
            for tok in b_names.split():
                type_vars.add(tok)
        else:
            for tok in b_names.split():
                type_vars.discard(tok)
    return True


def _check_hypothesis_contradiction(
    hyp_expr: str, nat_vars: frozenset[str] = frozenset()
) -> str | None:
    """Return a description if `hyp_expr` is a syntactic contradiction, else `None`.

    `nat_vars` are binders of a `Nat`-like type; the vacuous `x < 0` / `0 > x` rule fires only for
    `Nat`-valued operands (`_is_nat_like_operand`). A0-A1 fired for every operand not declared
    `Int`, a false positive on `(x : Real) (h : x < 0)` or `(f : Nat → Int) (h : f 0 < 0)`."""
    if (
        "=" not in hyp_expr
        and "≠" not in hyp_expr
        and "<" not in hyp_expr
        and "≤" not in hyp_expr
        and ">" not in hyp_expr
        and "False" not in hyp_expr
        and "¬" not in hyp_expr
    ):
        return None
    h = _norm_expr(hyp_expr)
    if not h:
        return None
    # An expression whose top-level connective is looser than `¬` (`→`, `->`, `↔`, `<->`, `∨`,
    # `\/`, `∧`, `/\`) is an implication/disjunction/iff/conjunction (e.g. `¬ True → α`,
    # `¬ (x = x) ∨ P`, `none = some x → α`), never an atomic single-premise contradiction.
    if _has_top_level_looser_than_not(h):
        return None
    if h == "False":
        return "`False` hypothesis"
    if h in (
        "true = false",
        "false = true",
        "Bool.true = Bool.false",
        "Bool.false = Bool.true",
    ):
        return f"contradictory boolean equality `{h}`"

    # Check `lhs ≠ rhs` or `¬ lhs = rhs` or `¬ (lhs = rhs)`
    if "≠" in h:
        neq_sides = _split_top_level(h, "≠")
        if len(neq_sides) == 2 and neq_sides[0] and neq_sides[0] == neq_sides[1]:
            return f"irreflexive inequality `{h}`"
    if h.startswith("¬"):
        inner = _norm_expr(h[1:])
        if inner == "True":
            return f"negated `True` hypothesis `{h}`"
        if "=" in inner and not _has_top_level_looser_than_not(inner):
            eq_sides = _split_top_level_eq(inner)
            if len(eq_sides) == 2 and eq_sides[0] and eq_sides[0] == eq_sides[1]:
                return f"negated reflexive equality `{h}`"

    # Check `lhs < rhs` for `x < x`, `< 0`, or numeric `5 < 3`
    if "<" in h and "≤" not in h and "<<" not in h and "←" not in h and "↔" not in h:
        lhs, _, rhs = h.partition("<")
        nl = _norm_expr(lhs)
        nr = _norm_expr(rhs)
        if nl and nl == nr:
            return f"irreflexive strict inequality `{h}`"
        if nr == "0" and _is_nat_like_operand(nl, nat_vars):
            return f"vacuous `< 0` bound `{h}`"
        if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) >= int(nr):
            return f"contradictory numeric inequality `{nl} < {nr}`"

    # Check `lhs ≤ rhs` for numeric `5 ≤ 3`
    if "≤" in h and "↔" not in h:
        lhs, _, rhs = h.partition("≤")
        nl = _norm_expr(lhs)
        nr = _norm_expr(rhs)
        if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) > int(nr):
            return f"contradictory numeric inequality `{nl} ≤ {nr}`"

    # Check `lhs > rhs` for `x > x` or numeric `3 > 5`
    if ">" in h and "->" not in h and "=>" not in h and ">>" not in h and "≥" not in h:
        lhs, _, rhs = h.partition(">")
        nl = _norm_expr(lhs)
        nr = _norm_expr(rhs)
        if nl and nl == nr:
            return f"irreflexive strict inequality `{h}`"
        if nl == "0" and _is_nat_like_operand(nr, nat_vars):
            return f"vacuous `0 > ...` bound `{h}`"
        if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) <= int(nr):
            return f"contradictory numeric inequality `{nl} > {nr}`"

    # Check `lhs = rhs`
    if "=" in h and "==" not in h and "≠" not in h and "≤" not in h and "≥" not in h and ":=" not in h:
        lhs, _, rhs = h.partition("=")
        nl = _norm_expr(lhs)
        nr = _norm_expr(rhs)
        if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) != int(nr):
            return f"distinct numeric literal equality `{nl} = {nr}`"
        if (nl == "none" and (nr == "some" or nr.startswith("some "))) or (
            nr == "none" and (nl == "some" or nl.startswith("some "))
        ):
            return f"disjoint `Option` constructor equality `{h}`"
        if (
            nl == "[]"
            and ("::" in nr or (nr.startswith("[") and nr.endswith("]") and nr != "[]"))
        ) or (
            nr == "[]"
            and ("::" in nl or (nl.startswith("[") and nl.endswith("]") and nl != "[]"))
        ):
            return f"disjoint `List` constructor equality `{h}`"
        if (
            (nl.startswith(".inl ") or nl.startswith("Sum.inl "))
            and (nr.startswith(".inr ") or nr.startswith("Sum.inr "))
        ) or (
            (nr.startswith(".inl ") or nr.startswith("Sum.inl "))
            and (nl.startswith(".inr ") or nl.startswith("Sum.inr "))
        ):
            return f"disjoint `Sum` constructor equality `{h}`"
        if (
            (nl.startswith(".ok ") or nl.startswith("Except.ok "))
            and (nr.startswith(".error ") or nr.startswith("Except.error "))
        ) or (
            (nr.startswith(".ok ") or nr.startswith("Except.ok "))
            and (nl.startswith(".error ") or nl.startswith("Except.error "))
        ):
            return f"disjoint `Except` constructor equality `{h}`"

    return None


def _audit_lean_theorem(
    name: str,
    line: int,
    meta: dict[str, str],
    hyps: list[tuple[str, str]],
    conclusion: str,
    contradiction_only: bool = False,
    extra_binders: list[str] | tuple[str, ...] = (),
) -> list[WaiverPinFinding]:
    """Run all 5 `TRIVIAL_PROOF` and 3-axis metadata checks on a Lean `theorem`/`lemma`.

    With `contradiction_only`, only the hypothesis-contradiction check (step 2) runs, and only
    over named hypotheses (binders such as `(h : False)` / `(h : 0 = 1)` and named `∀`
    binders; anonymous `→` premises are left to the full audit): the scope applied to
    unannotated theorems by default, where a `True` / reflexive conclusion may be a
    deliberate smoke or sanity lemma but an explicitly assumed, syntactically unsatisfiable
    hypothesis is always a vacuity hazard.
    """
    all_hyps = hyps
    if contradiction_only:
        indexed_hyps = [(idx, h) for idx, h in enumerate(all_hyps) if h[0]]
        hyps = [h for _, h in indexed_hyps]
    else:
        indexed_hyps = list(enumerate(all_hyps))
    findings: list[WaiverPinFinding] = []
    norm_conc = "" if contradiction_only else _norm_expr(conclusion)
    is_false_conc = (
        norm_conc == "False"
        if not contradiction_only
        else ("False" in conclusion and _norm_expr(conclusion) == "False")
    )

    kind_raw = meta.get("kind", "")
    witness_raw = meta.get("witness", "")
    assumes_raw = meta.get("assumes", "")
    subject_raw = meta.get("subject", "")

    kind = kind_raw.lower() if kind_raw else ""
    witness = witness_raw.lower() if witness_raw else ""

    # 1. Validate 3-axis metadata values and tier/witness consistency (`RULE_TIER_ASSUMPTION_MISMATCH`)
    if kind_raw and kind not in VALID_3AXIS_KINDS:
        findings.append(
            WaiverPinFinding(
                rule=RULE_TIER_ASSUMPTION_MISMATCH,
                line=line,
                symbol=name,
                message=(
                    f"Theorem `{name}` declares invalid 3-axis `Kind: {kind_raw}` "
                    f"(expected one of {sorted(VALID_3AXIS_KINDS)})."
                ),
                suggestion="Set `Kind:` to `safety`, `refinement`, `divergence`, `codec`, or `helper`.",
            )
        )

    if witness_raw and witness not in VALID_3AXIS_WITNESSES:
        findings.append(
            WaiverPinFinding(
                rule=RULE_TIER_ASSUMPTION_MISMATCH,
                line=line,
                symbol=name,
                message=(
                    f"Theorem `{name}` declares invalid or vacuous 3-axis `Witness: {witness_raw}` "
                    f"(expected one of {sorted(VALID_3AXIS_WITNESSES)})."
                ),
                suggestion="Use `Witness: universal`, `Witness: exists-sat`, or `Witness: negative`.",
            )
        )

    canon_tier = VALID_3AXIS_ASSUMES.get(assumes_raw, "")
    if assumes_raw and not canon_tier:
        findings.append(
            WaiverPinFinding(
                rule=RULE_TIER_ASSUMPTION_MISMATCH,
                line=line,
                symbol=name,
                message=(
                    f"Theorem `{name}` declares invalid 3-axis `Assumes: {assumes_raw}` "
                    "(expected `S0`, `S1`, `S2`, `S3`, or `TCB`)."
                ),
                suggestion="Set `Assumes:` to `S0`, `S1`, `S2`, or `S3` matching the theorem's trust hypotheses.",
            )
        )

    # Hypotheses are joined once with " ; " (never part of an identifier), so a substring test on the
    # joined text equals `any(substring in t for t in hyps)` for every identifier-like trigger below.
    all_hyps_text = " ; ".join([t for _, t in hyps])
    if canon_tier == "S0" and (
        ".rust" in all_hyps_text
        or "AdtRepr.rust" in all_hyps_text
        or "reprRust" in name
        or "canonicalRust" in name
        or "evalConst" in all_hyps_text
        or "compileTimeError" in all_hyps_text
    ):
        # Check if an `S0` theorem secretly pins canonical zero-padding on `#[repr(Rust)]` without an evalConst guard
        mentions_rust_repr = (
            ".rust" in all_hyps_text
            or "AdtRepr.rust" in all_hyps_text
            or "reprRust" in name
            or "canonicalRust" in name
        )
        pins_zero_pad = mentions_rust_repr and (
            "paddingFree 0" in all_hyps_text
            or "adtPad = fun _ => 0" in all_hyps_text
            or "adtPad = (fun _ => 0)" in all_hyps_text
            or "hasPinnedCoupledWaiver" in all_hyps_text
            or "pad0 = 0" in all_hyps_text
            or "totalPad = 0" in all_hyps_text
            or ("rustOrderCanonical" in all_hyps_text
                and _RUST_ORDER_CANON_RE.search(all_hyps_text) is not None)
        )
        has_const_guard = (
            "evalConst" in all_hyps_text
            or "compileTimeError" in all_hyps_text
        )
        if pins_zero_pad and not has_const_guard:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TIER_ASSUMPTION_MISMATCH,
                    line=line,
                    symbol=name,
                    tier="S0",
                    message=(
                        f"Theorem `{name}` claims `Assumes: S0`, but its hypotheses pin canonical "
                        "zero-padding (`paddingFree` / `rustOrderCanonical` / `adtPad = 0`) on `#[repr(Rust)]`."
                    ),
                    suggestion="Change `Assumes: S0` to `Assumes: S3` (or universalize over all `ValidStructLayoutWorld`).",
                )
            )
        if has_const_guard and "≠ .compileTimeError" in all_hyps_text:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TIER_ASSUMPTION_MISMATCH,
                    line=line,
                    symbol=name,
                    tier="S0",
                    message=(
                        f"Theorem `{name}` claims `Assumes: S0`, but assumes a non-`.compileTimeError` "
                        "compile-time guard premise (`S1`)."
                    ),
                    suggestion="Change `Assumes: S0` to `Assumes: S1`.",
                )
            )

    if witness == "exists-sat":
        if "∃" not in norm_conc and "Exists" not in norm_conc and "NonEmpty" not in norm_conc:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TIER_ASSUMPTION_MISMATCH,
                    line=line,
                    symbol=name,
                    tier=canon_tier,
                    message=(
                        f"Theorem `{name}` declares `Witness: exists-sat`, but its conclusion "
                        f"`{norm_conc}` is not an existential witness (`∃ ...`)."
                    ),
                    suggestion="State an existential conclusion `∃ ...` or change `Witness:` to `universal`.",
                )
            )
    elif witness == "negative":
        is_neg_conc = (
            norm_conc.startswith("¬")
            or "¬ " in norm_conc
            or "≠" in norm_conc
            or "= none" in norm_conc
            or "= false" in norm_conc
            or "= .ub" in norm_conc
            or "= .compileTimeError" in norm_conc
            or norm_conc == "False"
        )
        if not is_neg_conc:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TIER_ASSUMPTION_MISMATCH,
                    line=line,
                    symbol=name,
                    tier=canon_tier,
                    message=(
                        f"Theorem `{name}` declares `Witness: negative`, but its conclusion "
                        f"`{norm_conc}` contains no negation or rejection predicate."
                    ),
                    suggestion="Ensure the conclusion states a rejection (`¬ ...`, `≠`, `= none`, `= false`) or change `Witness:`.",
                )
            )

    # 2. Check hypotheses for syntactic contradiction (`RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS`)
    nat_vars: frozenset[str] | None = None
    conc_head = norm_conc.split(" ", 1)[0].lstrip("(¬") if norm_conc else ""
    has_non_eq_neg = "¬" in all_hyps_text
    has_neq = "≠" in all_hyps_text
    any_neg = has_non_eq_neg or has_neq
    seen_pos_hyps: set[str] = set()
    seen_neg_hyps: set[str] = set()
    tautology_hit = False

    has_any_ineq_or_neg_in_all = (
        any_neg
        or "<" in all_hyps_text
        or "≤" in all_hyps_text
        or ">" in all_hyps_text
        or "False" in all_hyps_text
    )
    has_eq_in_all = "=" in all_hyps_text
    conc_head_in_all = bool(conc_head and conc_head in all_hyps_text)

    if has_any_ineq_or_neg_in_all or has_eq_in_all or conc_head_in_all:
        for orig_idx, (_, t) in indexed_hyps:
            has_ineq_or_neg = (
                has_any_ineq_or_neg_in_all
                and (
                    "≠" in t
                    or "<" in t
                    or "≤" in t
                    or ">" in t
                    or "False" in t
                    or "¬" in t
                )
            )
            has_eq = "=" in t
            if not has_ineq_or_neg and not has_eq and not has_non_eq_neg and not (conc_head_in_all and conc_head in t):
                continue
            # If the only trigger in `t` is `=`, and there are no `¬`/`≠` hypotheses in the theorem,
            # and `t` cannot match `norm_conc`, check if `t` can be a constructor/literal equality clash
            if (
                not has_ineq_or_neg
                and has_eq
                and not any_neg
                and not (conc_head_in_all and conc_head in t)
                and "false" not in t
                and "none" not in t
                and "[]" not in t
                and "inl" not in t
                and "ok" not in t
                and _DIGIT_SEARCH(t) is None
            ):
                continue
            nh = _norm_expr(t)
            if not tautology_hit and nh and nh == norm_conc:
                tautology_hit = True
            if not has_ineq_or_neg and not has_eq and not has_non_eq_neg:
                continue
            parts = _split_top_level_conjuncts(nh)
            if len(parts) > 1:
                seen_pos_hyps.add(nh)
            for part in parts:
                if (
                    "=" in part
                    or "≠" in part
                    or "<" in part
                    or "≤" in part
                    or ">" in part
                    or "False" in part
                    or "¬" in part
                ):
                    if nat_vars is None and "0" in part and ("<" in part or ">" in part):
                        nat_vars = frozenset(
                            tok
                            for b_names, b_type in hyps
                            if b_type in _NAT_LIKE_TYPES or b_type.startswith("Fin ")
                            for tok in b_names.split()
                        )
                    reason = _check_hypothesis_contradiction(part, nat_vars or frozenset())
                    if reason is not None and not (
                        is_false_conc
                        and len(parts) == 1
                        and _is_single_premise_false_elim(all_hyps, orig_idx, extra_binders)
                    ):
                        findings.append(
                            WaiverPinFinding(
                                rule=RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                                line=line,
                                symbol=name,
                                tier=canon_tier,
                                message=(
                                    f"Vacuous theorem `{name}`: hypothesis contains {reason}, "
                                    "making the implication vacuously true."
                                ),
                                suggestion="Remove the contradictory hypothesis and prove the theorem over inhabited premises.",
                            )
                        )
                if part.startswith("¬") and not _has_top_level_looser_than_not(part):
                    inner = _norm_expr(part[1:])
                    seen_neg_hyps.add(inner)
                    seen_pos_hyps.add(part)
                elif "≠" in part and not _has_top_level_looser_than_not(part):
                    neq_sides = _split_top_level(part, "≠")
                    if len(neq_sides) == 2 and neq_sides[0] and neq_sides[1]:
                        seen_neg_hyps.add(f"{neq_sides[0]} = {neq_sides[1]}")
                    seen_pos_hyps.add(part)
                else:
                    seen_pos_hyps.add(part)

        contradictory_pairs = seen_pos_hyps & seen_neg_hyps
        if contradictory_pairs:
            sample_p = sorted(contradictory_pairs)[0]
            findings.append(
                WaiverPinFinding(
                    rule=RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                    line=line,
                    symbol=name,
                    tier=canon_tier,
                    message=(
                        f"Vacuous theorem `{name}`: hypotheses simultaneously assume `{sample_p}` and its negation."
                    ),
                    suggestion="Remove the mutually contradictory hypotheses.",
                )
            )

    if contradiction_only:
        return findings

    # 3. Check conclusion for `True`, reflexive `lhs = lhs` / `lhs ≤ lhs` / `lhs ↔ lhs`,
    #    conjunctions of trivial facts, or disjunctions with a trivial disjunct (`RULE_TRIVIAL_CONCLUSION`).
    #    `helper` lemmas and `negative` witnesses (whose point is a rejection) are exempt.
    if kind != "helper" and witness != "negative":
        if "∧" in norm_conc and _all_conjuncts_trivial(norm_conc):
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TRIVIAL_CONCLUSION,
                    line=line,
                    symbol=name,
                    tier=canon_tier,
                    message=(
                        f"Trivial conclusion in theorem `{name}`: every conjunct of `{norm_conc}` is "
                        "trivially true (`True`, `¬ False`, or a reflexive `=` / `↔` / `≤`)."
                    ),
                    suggestion="State the actual semantic postcondition or codec/layout property in the conclusion.",
                )
            )
        elif "∨" in norm_conc and _any_disjunct_trivial(norm_conc):
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TRIVIAL_CONCLUSION,
                    line=line,
                    symbol=name,
                    tier=canon_tier,
                    message=(
                        f"Trivial disjunctive conclusion in theorem `{name}`: `{norm_conc}` contains "
                        "a trivially true disjunct (`True`, `¬ False`, or reflexive `=` / `↔` / `≤`)."
                    ),
                    suggestion="Remove the trivial disjunct or replace `∨` with `∧`.",
                )
            )
        elif "∧" not in norm_conc and "∨" not in norm_conc and _is_trivially_true(norm_conc):
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TRIVIAL_CONCLUSION,
                    line=line,
                    symbol=name,
                    tier=canon_tier,
                    message=f"Trivial conclusion in theorem `{name}`: `{norm_conc}` is trivially true.",
                    suggestion="Replace the trivial/reflexive conclusion with a non-trivial equivalence or invariant.",
                )
            )

    # 4. Check tautological implication (`RULE_TAUTOLOGICAL_IMPLICATION`)
    if tautology_hit:
        findings.append(
            WaiverPinFinding(
                rule=RULE_TAUTOLOGICAL_IMPLICATION,
                line=line,
                symbol=name,
                tier=canon_tier,
                message=(
                    f"Tautological implication in theorem `{name}`: conclusion `{norm_conc}` "
                    "is identical to an explicit hypothesis."
                ),
                suggestion="Strengthen the conclusion or remove the redundant hypothesis that assumes the goal.",
            )
        )

    # 5. Check unused subject in conclusion (`RULE_UNUSED_SUBJECT_IN_CONCLUSION`)
    if subject_raw:
        if subject_raw in conclusion or subject_raw in norm_conc:
            in_conc = True
        else:
            subj_short = subject_raw.split(".")[-1]
            in_conc = subj_short in conclusion or subj_short in norm_conc
        if not in_conc:
            subj_short = subject_raw.split(".")[-1]
            conc_idents = set(_IDENT_EXTRACT_RE.findall(norm_conc))
            connected_via_hyp = False
            for b_names, h_type in hyps:
                if subject_raw in h_type or subj_short in h_type:
                    hyp_vars = {
                        tok
                        for tok in _IDENT_EXTRACT_RE.findall(b_names + " " + h_type)
                        if tok != subj_short
                        and not tok.startswith("h")
                        and tok not in _DATA_TYPE_WORDS
                        and len(tok) >= 1
                        and tok[0].islower()
                    }
                    if hyp_vars & conc_idents:
                        connected_via_hyp = True
                        break
            if not connected_via_hyp:
                findings.append(
                    WaiverPinFinding(
                        rule=RULE_UNUSED_SUBJECT_IN_CONCLUSION,
                        line=line,
                        symbol=name,
                        tier=canon_tier,
                        message=(
                            f"Theorem `{name}` declares `Subject: {subject_raw}`, but its conclusion "
                            f"`{norm_conc}` never references `{subject_raw}` or its constrained state."
                        ),
                        suggestion=f"Constrain `{subject_raw}` in the theorem conclusion or update `Subject:`.",
                    )
                )
    elif kind in ("safety", "refinement", "divergence", "codec"):
        domain_binder_vars: list[str] = []
        all_value_vars: list[str] = []
        for b_names, b_type in hyps:
            if not b_names:
                continue
            if _REL_OP_SEARCH(b_type) is not None:
                continue
            is_primitive = b_type.strip().strip("()").strip() in _DATA_TYPE_WORDS
            for tok in b_names.split():
                tok_clean = tok.strip("()[]{}")
                if (
                    tok_clean
                    and not tok_clean.startswith("_")
                    and not tok_clean.startswith("h")
                    and tok_clean not in _DATA_TYPE_WORDS
                ):
                    all_value_vars.append(tok_clean)
                    if not is_primitive:
                        domain_binder_vars.append(tok_clean)
        target_vars = domain_binder_vars if domain_binder_vars else all_value_vars
        if target_vars:
            conc_idents = set(_IDENT_EXTRACT_RE.findall(norm_conc))
            if not any(v in conc_idents for v in target_vars):
                findings.append(
                    WaiverPinFinding(
                        rule=RULE_UNUSED_SUBJECT_IN_CONCLUSION,
                        line=line,
                        symbol=name,
                        tier=canon_tier,
                        message=(
                            f"`{kind}` theorem `{name}` binds subject parameter(s) {target_vars}, "
                            f"but its conclusion `{norm_conc}` references none of them."
                        ),
                        suggestion="Ensure the conclusion states a property of the bound subject parameter(s).",
                    )
                )

    return findings


def _lean_comment_groups(
    code_only: str, comment_blocks: list[tuple[int, int, int, str, str]]
) -> list[tuple[int, int, list[tuple[int, str, str]]]]:
    """Group consecutive non-module-doc Lean comments of the same declaration (separated only by
    whitespace, `@[...]` attributes, declaration modifiers, or `<command> in` prefixes)."""
    groups: list[tuple[int, int, list[tuple[int, str, str]]]] = []
    for c_start, c_end, c_line, c_body, c_kind in comment_blocks:
        if groups and c_kind != "m":
            p_start, p_end, p_list = groups[-1]
            if p_list[-1][2] != "m":
                gap = code_only[p_end:c_start]
                if (
                    not gap
                    or gap.isspace()
                    or (
                        c_start - p_end <= 512
                        and ":=" not in gap
                        and _skip_lean_prefixes_attrs_and_modifiers(code_only, p_end, c_start) >= c_start
                    )
                ):
                    p_list.append((c_line, c_body, c_kind))
                    groups[-1] = (p_start, c_end, p_list)
                    continue
        groups.append((c_start, c_end, [(c_line, c_body, c_kind)]))
    return groups


def _lean_docstring_lines(c_list: list[tuple[int, str, str]], kind: str = "d") -> list[tuple[int, str]]:
    """`(line_no, text)` lines of the comments of the requested kind (`"d"` = `/-- -/`)."""
    out: list[tuple[int, str]] = []
    for base_line, c_body, c_kind in c_list:
        if c_kind == kind:
            out.extend((base_line + k, raw) for k, raw in enumerate(c_body.split("\n")))
    return out


_3AXIS_KEYS = frozenset(("kind", "witness", "assumes", "subject"))
_META_CACHE: dict[str, tuple[dict[str, str], list[str]]] = {}
_THM_AUDIT_CACHE: dict[tuple[str, str, str, bool], tuple[WaiverPinFinding, ...]] = {}
# In-process incremental splicing (`_find_incremental_lean_window`): only a long-lived process
# re-scanning edited files (the LSP daemon, a hook's before/after pair) benefits. A host that audits
# every file once -- the TCB checker -- turns it off, keeping the splice logic out of its decisions.
INCREMENTAL_SPLICING = True
_LAST_LEAN_AUDIT: dict[
    tuple[str, bool, str],
    tuple[str, str, list[int], list[int], list[int], tuple[WaiverPinFinding, ...]],
] = {}


def _find_incremental_lean_window(
    old_text: str,
    old_code: str,
    c_starts: list[int],
    c_ends: list[int],
    col0_thms: list[int],
    text: str,
) -> (
    tuple[
        int,
        int,
        int,
        int,
        int,
        int,
        int,
        int,
        str,
        list[tuple[int, int, int, str, str]],
    ]
    | None
):
    """If `text` is a localized edit of `old_text`, return two-ring window boundaries
    `(safe_lo, safe_hi_old, safe_hi_new, lo_line_offset, cut_lo_line, cut_hi_old_line,
    cut_hi_new_line, delta_lines, win_code, win_comments)` for `O(window)` incremental
    scanning, or `None` when a full scan is needed."""
    n_old = len(old_text)
    n_new = len(text)
    if n_old < 32768 or n_new < 32768 or len(col0_thms) < 8:
        return None
    step = 4096
    limit = n_old if n_old < n_new else n_new
    p = 0
    while p + step <= limit and old_text[p : p + step] == text[p : p + step]:
        p += step
    while p + 64 <= limit and old_text[p : p + 64] == text[p : p + 64]:
        p += 64
    delta_len = n_new - n_old
    s = n_old
    while s - step >= p and old_text[s - step : s] == text[s + delta_len - step : s + delta_len]:
        s -= step
    while s - 64 >= p and old_text[s - 64 : s] == text[s + delta_len - 64 : s + delta_len]:
        s -= 64
    if (p == 0 and s == n_old) or (p + (n_old - s) < (n_new * 3) // 4):
        return None

    def _backup_col0_decl(kw_pos: int) -> int | None:
        pos = kw_pos
        first_step = True
        while True:
            idx = _wa_bisect_right(c_ends, pos) - 1
            if (
                idx >= 0
                and (first_step or pos - c_ends[idx] <= 64)
                and old_code[c_ends[idx] : pos].strip() == ""
            ):
                c0 = c_starts[idx]
                nl = old_code.rfind("\n", 0, c0)
                pos = 0 if nl == -1 else nl + 1
                first_step = False
            else:
                break
        if pos > 0 and (old_text[pos - 1] != "\n" or old_code[pos - 1] != "\n"):
            return None
        if pos > 0:
            q = pos - 1
            while q > 0 and old_code[q - 1] in " \t\r\n":
                q -= 1
            prev_nl = old_code.rfind("\n", 0, q)
            prev_line = old_code[prev_nl + 1 : q].strip()
            if (
                prev_line.startswith("@")
                or prev_line.endswith("]")
                or prev_line == "where"
                or prev_line.startswith("where ")
                or prev_line.endswith(" where")
                or prev_line.endswith(" in")
                or prev_line == "in"
                or any(
                    prev_line == mod or prev_line.startswith(mod + " ") or prev_line.endswith(" " + mod)
                    for mod in _LEAN_MODIFIERS
                )
            ):
                return None
        return pos

    # `col0_thms[i_lo]` may be the theorem whose body/header contains `p`, so skip `i_lo`
    # and start searching for `cut_lo` at `i_lo - 1` (ensuring at least one full unmodified
    # theorem sits between `cut_lo` and `col0_thms[i_lo]`, keeping all of `col0_thms[i_lo]`'s
    # preceding docstrings, attributes, and modifiers strictly inside `[cut_lo, cut_hi_old)`).
    i_lo = _wa_bisect_right(col0_thms, p) - 2
    cut_lo: int | None = None
    safe_lo: int | None = None
    while i_lo >= 0:
        cand = _backup_col0_decl(col0_thms[i_lo])
        if cand is not None and cand <= p:
            if cut_lo is None:
                cut_lo = cand
            elif cand < cut_lo:
                safe_lo = cand
                break
        i_lo -= 1

    # Similarly, an edit ending at `s` may edit or insert a docstring/attribute that attaches
    # forward across whitespace/modifiers to `col0_thms[i_hi]`, so skip `i_hi` and start
    # searching for `cut_hi_old` at `i_hi + 1`.
    n_thms = len(col0_thms)
    i_hi = _wa_bisect_right(col0_thms, s - 1 if s > 0 else 0) + 1
    cut_hi_old: int | None = None
    safe_hi_old: int | None = None
    while i_hi < n_thms:
        cand = _backup_col0_decl(col0_thms[i_hi])
        if cand is not None and cand >= s:
            if cut_hi_old is None:
                cut_hi_old = cand
            elif cand > cut_hi_old:
                safe_hi_old = cand
                break
        i_hi += 1

    if (
        safe_lo is None
        or cut_lo is None
        or cut_hi_old is None
        or safe_hi_old is None
        or not (safe_lo < cut_lo <= p and s <= cut_hi_old < safe_hi_old)
    ):
        return None

    safe_hi_new = safe_hi_old + delta_len
    cut_hi_new = cut_hi_old + delta_len

    # Both `cut_hi_new` and `safe_hi_new` must be in the neutral lexer state: the outer ring
    # `text[cut_hi_new:safe_hi_new]` must lex identically to `old_code[cut_hi_old:safe_hi_old]`
    # with no comment crossing `cut_hi_new`, and the sentinel after `safe_hi_new` must survive
    # verbatim with no comment crossing `win_len` (catching both strings that stay open past
    # `safe_hi_new` and strings that swallow `cut_hi_new` before closing at a quote inside a
    # comment in `[cut_hi_new, safe_hi_new)`).
    win_len = safe_hi_new - safe_lo
    cut_hi_rel = cut_hi_new - safe_lo
    sentinel = "\nzzIncrementalLexSentinelzz"
    win_sent_code, win_sent_comments = _scan_lean_comments_and_strings(
        text[safe_lo:safe_hi_new] + sentinel
    )
    if len(win_sent_code) != win_len + len(sentinel) or not win_sent_code.endswith(sentinel):
        return None
    if win_sent_code[cut_hi_rel:win_len] != old_code[cut_hi_old:safe_hi_old]:
        return None
    if any((cs < cut_hi_rel < ce) or (ce > win_len) for cs, ce, _, _, _ in win_sent_comments):
        return None

    win_code = win_sent_code[:win_len]
    win_comments = list(win_sent_comments)
    lo_line_offset = old_text.count("\n", 0, safe_lo)
    cut_lo_line = lo_line_offset + old_text.count("\n", safe_lo, cut_lo) + 1
    cut_hi_old_line = cut_lo_line - 1 + old_text.count("\n", cut_lo, cut_hi_old) + 1
    cut_hi_new_line = lo_line_offset + text.count("\n", safe_lo, cut_hi_new) + 1
    delta_lines = cut_hi_new_line - cut_hi_old_line
    return (
        safe_lo,
        safe_hi_old,
        safe_hi_new,
        lo_line_offset,
        cut_lo_line,
        cut_hi_old_line,
        cut_hi_new_line,
        delta_lines,
        win_code,
        win_comments,
    )

# Which theorems the 3-axis / `TRIVIAL_PROOF` audit covers (`audit_lean_text(vacuity_scope=...)`):
# - `"all"`: every `theorem` / `lemma` gets every check (`--all-theorems`, the prototype default).
# - `"annotated"`: theorems with 3-axis metadata, an `anneal:` waiver docstring, or an Anneal
#   `Proof/` claim name (`verified` / `prove_*`) get every check; every other theorem gets only
#   the syntactic hypothesis-contradiction check (the always-on `proof_health.py` scope).
# - `"annotated-only"`: only the annotated / claim theorems are audited (the TCB checker scope).
VACUITY_SCOPES: frozenset[str] = frozenset(("all", "annotated", "annotated-only"))


def is_proof_claim_module(file_path: str | Path | None) -> bool:
    """`True` for files under an Anneal `Proof/` directory (any path component `Proof`)."""
    if file_path is None:
        return False
    return "Proof" in Path(file_path).parts[:-1]


def is_proof_claim_theorem_name(name: str) -> bool:
    """`True` for Anneal claim theorem names: `verified` or `prove_*` (last name component)."""
    short = name.rsplit(".", 1)[-1]
    return short == "verified" or short.startswith("prove_")


def _parse_3axis_metadata_and_conflicts(comment_text: str) -> tuple[dict[str, str], list[str]]:
    """Single-pass C-level line partition 3-axis metadata parser (last value wins) plus
    the keys declared more than once with different values."""
    hit = _META_CACHE.get(comment_text)
    if hit is not None:
        return hit
    meta: dict[str, str] = {}
    conflicts: list[str] = []
    for raw_line in comment_text.split("\n"):
        if ":" not in raw_line:
            continue
        k_part, _, v_part = raw_line.partition(":")
        if len(k_part) > 16:
            continue
        key = k_part.lstrip(" \t*-").rstrip(" \t").lower()
        if key in _3AXIS_KEYS:
            val = v_part.strip()
            if val:
                prev = meta.get(key)
                if prev is not None and prev != val and key not in conflicts:
                    conflicts.append(key)
                meta[key] = val
    res = (meta, conflicts)
    if len(_META_CACHE) < 4096:
        _META_CACHE[comment_text] = res
    return res


def audit_lean_text(
    text: str,
    *,
    file_path: str | Path | None = None,
    check_3axis: bool = True,
    vacuity_scope: str = "all",
    _preparsed: tuple[str, list[tuple[int, int, int, str, str]]] | None = None,
) -> list[WaiverPinFinding]:
    """Scan Lean 4 source `text` for `S0`-`S3` waiver pin findings and 3-axis / `TRIVIAL_PROOF` hazards.

    Waiver directives and pin lines are read only from `/-- ... -/` docstrings (Lean's analogue
    of Rust's `///`); `--` and `/- ... -/` comments are ordinary comments, and directives in a
    `/-! ... -/` module docstring attach to no declaration (dangling). 3-axis metadata may live in
    any comment immediately preceding a declaration. `vacuity_scope` (see `VACUITY_SCOPES`)
    selects which theorems the 3-axis audit covers; `file_path` identifies `Proof/` claim modules.
    """
    if vacuity_scope not in VACUITY_SCOPES:
        raise ValueError(f"unknown vacuity_scope {vacuity_scope!r}")
    if not check_3axis and "anneal:" not in text and "pin:sha256:" not in text:
        return []
    state_key = (
        str(file_path) if file_path is not None else "",
        bool(check_3axis),
        vacuity_scope,
    )
    if INCREMENTAL_SPLICING and _preparsed is None and len(text) >= 32768:
        prev = _LAST_LEAN_AUDIT.get(state_key)
        if prev is not None:
            old_text, old_code, c_starts, c_ends, col0_thms, old_findings = prev
            if text == old_text:
                return list(old_findings)
            win_info = _find_incremental_lean_window(
                old_text, old_code, c_starts, c_ends, col0_thms, text
            )
            if win_info is not None:
                (
                    safe_lo,
                    _safe_hi_old,
                    safe_hi_new,
                    lo_line_offset,
                    cut_lo_line,
                    cut_hi_old_line,
                    cut_hi_new_line,
                    delta_lines,
                    win_code,
                    win_comments,
                ) = win_info
                win_findings = audit_lean_text(
                    text[safe_lo:safe_hi_new],
                    file_path=file_path,
                    check_3axis=check_3axis,
                    vacuity_scope=vacuity_scope,
                    _preparsed=(win_code, win_comments),
                )
                spliced = [f for f in old_findings if f.line < cut_lo_line]
                for wf in win_findings:
                    adj_line = wf.line + lo_line_offset
                    if cut_lo_line <= adj_line < cut_hi_new_line:
                        spliced.append(
                            WaiverPinFinding(
                                rule=wf.rule,
                                line=adj_line,
                                message=wf.message,
                                suggestion=wf.suggestion,
                                symbol=wf.symbol,
                                expected_pin=wf.expected_pin,
                                actual_pin=wf.actual_pin,
                                tier=wf.tier,
                            )
                        )
                for f in old_findings:
                    if f.line >= cut_hi_old_line:
                        spliced.append(
                            f
                            if delta_lines == 0
                            else WaiverPinFinding(
                                rule=f.rule,
                                line=f.line + delta_lines,
                                message=f.message,
                                suggestion=f.suggestion,
                                symbol=f.symbol,
                                expected_pin=f.expected_pin,
                                actual_pin=f.actual_pin,
                                tier=f.tier,
                            )
                        )
                spliced.sort(key=lambda f: (f.line, f.rule, f.symbol))
                return spliced

    claim_module = is_proof_claim_module(file_path)
    if len(_NORM_CACHE) > 8192:
        _NORM_CACHE.clear()
    if _preparsed is not None:
        code_only, comment_blocks = _preparsed
    else:
        code_only, comment_blocks = _scan_lean_comments_and_strings(text)
    comment_starts: list[int] | None = None
    findings: list[WaiverPinFinding] = []
    line_of = _WaLineCounter(text)
    n_code = len(code_only)
    thms: list[tuple[int, int, str]] = []

    decl_comment_map: dict[int, str] = {}

    for grp_start, grp_end, c_list in _lean_comment_groups(code_only, comment_blocks):
        has_meta = False
        has_directive = False
        for _, c_body, c_kind in c_list:
            if ":" not in c_body:
                continue
            if "Kind:" in c_body or "Witness:" in c_body or "Assumes:" in c_body or "Subject:" in c_body:
                has_meta = True
            if c_kind != "l" and c_kind != "b" and ("anneal:" in c_body or "pin:" in c_body):
                has_directive = True
        if not has_meta and not has_directive:
            continue
        meta_text = c_list[0][1] if len(c_list) == 1 else "\n".join(c_body for _, c_body, _ in c_list)
        if has_directive:
            for line_no, raw in _lean_docstring_lines(c_list, "m"):
                if "anneal:" not in raw:
                    continue
                ann = parse_anneal_directive_line(raw, line_no)
                if ann is not None:
                    findings.append(
                        WaiverPinFinding(
                            rule=RULE_DANGLING_WAIVER,
                            line=ann.line,
                            symbol=ann.directive,
                            tier=ann.tier,
                            message=(
                                f"`anneal:{ann.directive}` sits in a `/-! ... -/` module docstring, which "
                                "attaches to no declaration."
                            ),
                            suggestion="Move the directive into the `/-- ... -/` docstring of the target declaration.",
                        )
                    )
            anns, block_pins = _collect_block_directives(_lean_docstring_lines(c_list, "d"))
        else:
            anns, block_pins = [], []
        if not anns and not has_meta:
            continue

        if not anns:
            d_start = grp_end
            while d_start < n_code and code_only[d_start] in " \t\r\n":
                d_start += 1
            if d_start < n_code:
                prev_m = decl_comment_map.get(d_start)
                decl_comment_map[d_start] = f"{prev_m}\n{meta_text}" if prev_m else meta_text
                if not code_only.startswith(("theorem ", "lemma ", "def ", "abbrev "), d_start):
                    kw_off = _skip_lean_prefixes_attrs_and_modifiers(code_only, d_start)
                    if kw_off < n_code and kw_off != d_start:
                        prev_kw = decl_comment_map.get(kw_off)
                        decl_comment_map[kw_off] = f"{prev_kw}\n{meta_text}" if prev_kw else meta_text
            continue

        decl_info = _extract_lean_decl_span(code_only, grp_end, text)
        if decl_info is None:
            for ann in anns:
                findings.append(
                    WaiverPinFinding(
                        rule=RULE_DANGLING_WAIVER,
                        line=ann.line,
                        symbol=ann.directive,
                        tier=ann.tier,
                        message=(
                            f"Dangling `anneal:{ann.directive}` waiver annotation in Lean file "
                            "with no following declaration."
                        ),
                        suggestion="Place the waiver docstring immediately before a `theorem`, `lemma`, or `def` declaration.",
                    )
                )
            continue
        d_start, d_end, _, d_name = decl_info
        prev_m = decl_comment_map.get(d_start)
        decl_comment_map[d_start] = f"{prev_m}\n{meta_text}" if prev_m else meta_text
        kw_off = _skip_lean_prefixes_attrs_and_modifiers(code_only, d_start)
        if kw_off < n_code and kw_off != d_start:
            prev_kw = decl_comment_map.get(kw_off)
            decl_comment_map[kw_off] = f"{prev_kw}\n{meta_text}" if prev_kw else meta_text
        if comment_starts is None:
            comment_starts = [c[0] for c in comment_blocks]
        # `<command> in` prefixes above or between comments in the group belong to the pinned command.
        p_start = _lean_in_prefix_start(code_only, grp_start)
        code_start = p_start
        while code_start < d_start and code_only[code_start] in " \t\r\n":
            code_start += 1
        hash_input = waiver_hash_input(
            anns,
            _normalize_lean_decl(
                _no_comments_slice(text, comment_blocks, comment_starts, code_start, d_end)
            ),
        )
        findings.extend(_validate_waiver_block(anns, block_pins, d_name, hash_input))

    if check_3axis:
        if len(_THM_AUDIT_CACHE) > 4096:
            _THM_AUDIT_CACHE.clear()
        thms = _iter_lean_theorem_headers(code_only)
        n_thms = len(thms)
        for idx_t, (kw_start, name_end, thm_name) in enumerate(thms):
            comment_str = decl_comment_map.get(kw_start, "")
            contradiction_only = False
            if vacuity_scope != "all" and not comment_str and not (
                claim_module and is_proof_claim_theorem_name(thm_name)
            ):
                if vacuity_scope == "annotated-only":
                    continue
                contradiction_only = True
            next_thm_bound = thms[idx_t + 1][0] if idx_t + 1 < n_thms else n_code
            # The audit is a pure function of (name, metadata comment, the exact bounded text
            # `_split_lean_theorem_header` reads, the check scope), so the cache key must be that
            # full slice: A1 truncated it at the first `:=`, which can sit inside a binder's
            # structure literal (`(h : ({ a := 1 } : S).P)`), letting a later edit to the conclusion
            # or to a later hypothesis hit a stale entry (false negatives across scans in one process).
            cache_key = (thm_name, comment_str, code_only[name_end:next_thm_bound], contradiction_only)
            cached_f = _THM_AUDIT_CACHE.get(cache_key)
            if cached_f is not None:
                if cached_f:
                    thm_line = line_of(kw_start)
                    for tf in cached_f:
                        findings.append(
                            WaiverPinFinding(
                                rule=tf.rule,
                                line=thm_line,
                                message=tf.message,
                                suggestion=tf.suggestion,
                                symbol=tf.symbol,
                                expected_pin=tf.expected_pin,
                                actual_pin=tf.actual_pin,
                                tier=tf.tier,
                            )
                        )
                continue

            local_findings: list[WaiverPinFinding] = []
            meta, conflicts = _parse_3axis_metadata_and_conflicts(comment_str) if comment_str else ({}, [])
            if conflicts:
                for key in conflicts:
                    local_findings.append(
                        WaiverPinFinding(
                            rule=RULE_TIER_ASSUMPTION_MISMATCH,
                            line=0,
                            symbol=thm_name,
                            message=(
                                f"Theorem `{thm_name}` declares conflicting 3-axis `{key.capitalize()}:` "
                                "values; a later line would silently override an earlier one."
                            ),
                            suggestion=f"Keep exactly one `{key.capitalize()}:` line.",
                        )
                    )
            parsed = _split_lean_theorem_header_ex(code_only, name_end, next_thm_bound)
            if parsed is not None:
                hyps, conc, extra_binders = parsed
                local_findings.extend(
                    _audit_lean_theorem(
                        thm_name, 0, meta, hyps, conc, contradiction_only, extra_binders
                    )
                )
            _THM_AUDIT_CACHE[cache_key] = tuple(local_findings)
            if local_findings:
                thm_line = line_of(kw_start)
                for tf in local_findings:
                    findings.append(
                        WaiverPinFinding(
                            rule=tf.rule,
                            line=thm_line,
                            message=tf.message,
                            suggestion=tf.suggestion,
                            symbol=tf.symbol,
                            expected_pin=tf.expected_pin,
                            actual_pin=tf.actual_pin,
                            tier=tf.tier,
                        )
                    )

    findings.sort(key=lambda f: (f.line, f.rule, f.symbol))
    if INCREMENTAL_SPLICING and _preparsed is None and len(text) >= 32768:
        if not thms:
            thms = _iter_lean_theorem_headers(code_only)
        col0_thms = [kw for kw, _, _ in thms if kw == 0 or code_only[kw - 1] == "\n"]
        if len(col0_thms) >= 8:
            if len(_LAST_LEAN_AUDIT) >= 16:
                _LAST_LEAN_AUDIT.clear()
            _LAST_LEAN_AUDIT[state_key] = (
                text,
                code_only,
                [c[0] for c in comment_blocks],
                [c[1] for c in comment_blocks],
                col0_thms,
                tuple(findings),
            )
    return findings


_LEAN_IN_SUFFIX_RE = re.compile(r"(?<![\w'!?.\u00bb])in[ \t\r]*$")


def _lean_in_prefix_start(code_only: str, pos: int) -> int:
    """Start of the chain of `<command> in` prefixes (`open Foo in`, `set_option opt v in`,
    `attribute [local simp] x in`, `variable (n : Nat) in`, ...) ending right before `pos` (a
    declaration's leading docstring or its first token), else `pos`.

    Lean parses `cmd in decl` as one command, so a waiver pin must bind these prefixes too:
    otherwise `set_option debug.skipKernelTC true in` (or `open Other in`, re-resolving every
    name of the statement) could be added before or edited above a pinned declaration's
    docstring without drifting its pin. A prefix may span several lines; its first line is the
    nearest prefix-command start above the `in` line (bounded walk).
    """
    start = pos
    while True:
        q = start
        while q > 0 and code_only[q - 1] in " \t\r\n":
            q -= 1
        if q == 0:
            return start
        line_start = code_only.rfind("\n", 0, q) + 1
        if _LEAN_IN_SUFFIX_RE.search(code_only, line_start, q) is None:
            return start
        cmd = line_start
        found_start = -1
        for _ in range(64):
            k = cmd
            while k < q and code_only[k] in " \t":
                k += 1
            kw = _skip_lean_attrs_and_modifiers(code_only, k)
            if _LEAN_IN_PREFIX_CMD_RE.match(code_only, kw) is not None:
                found_start = k
                break
            if _is_lean_command_start(code_only, k) or cmd == 0:
                break
            cmd = code_only.rfind("\n", 0, cmd - 1) + 1
        if found_start == -1 or found_start >= start:
            return start
        start = found_start


def compute_lean_decl_pins(text: str) -> dict[str, str]:
    """Map each top-level Lean declaration name in `text` to its `pin:sha256:<12hex>` tag
    (the hash binds the declaration's `/-- -/` directives and its normalized text)."""
    code_only, comment_blocks = _scan_lean_comments_and_strings(text)
    comment_starts = [c[0] for c in comment_blocks]
    n = len(code_only)
    anns_by_decl: dict[int, list[WaiverAnnotation]] = {}
    grp_start_by_decl: dict[int, int] = {}
    post_doc_start_by_decl: dict[int, int] = {}
    for grp_start, grp_end, c_list in _lean_comment_groups(code_only, comment_blocks):
        d = grp_end
        while d < n and code_only[d] in " \t\r\n":
            d += 1
        kw_off = _skip_lean_prefixes_attrs_and_modifiers(code_only, d)
        anns, _ = _collect_block_directives(_lean_docstring_lines(c_list, "d"))
        for key_off in (d,) if d == kw_off else (d, kw_off):
            if key_off in anns_by_decl:
                if anns:
                    anns_by_decl[key_off].extend(anns)
            else:
                anns_by_decl[key_off] = list(anns)
            if key_off not in grp_start_by_decl or grp_start < grp_start_by_decl[key_off]:
                grp_start_by_decl[key_off] = grp_start
            post_doc_start_by_decl[key_off] = d
    pins: dict[str, str] = {}
    pos = 0
    while pos < n:
        d_start = pos
        while d_start < n and code_only[d_start] in " \t\r\n":
            d_start += 1
        if d_start >= n:
            break
        hit = _match_lean_decl_at(code_only, d_start, skip_in_prefixes=True)
        if hit is None:
            nl = code_only.find("\n", d_start)
            if nl == -1:
                break
            pos = nl + 1
            continue
        hdr_end, _, d_name = hit
        kw_off = _skip_lean_prefixes_attrs_and_modifiers(code_only, d_start)
        doc_grp_start = grp_start_by_decl.get(kw_off, -1)
        if 0 <= doc_grp_start and d_start < doc_grp_start:
            pos = doc_grp_start
            continue
        post_doc_d = post_doc_start_by_decl.get(kw_off, d_start)
        d_end = _find_lean_decl_end(
            code_only, hdr_end, _lean_indent_of(code_only, post_doc_d, text), text
        )
        lead = grp_start_by_decl.get(kw_off, post_doc_d)
        p_start = _lean_in_prefix_start(code_only, lead)
        code_start = p_start
        while code_start < post_doc_d and code_only[code_start] in " \t\r\n":
            code_start += 1
        hash_input = waiver_hash_input(
            anns_by_decl.get(kw_off, []),
            _normalize_lean_decl(
                _no_comments_slice(text, comment_blocks, comment_starts, code_start, d_end)
            ),
        )
        pins[d_name] = format_pin_tag(compute_sha256_pin12(hash_input))
        pos = d_end
    return pins


def compute_rust_item_pins(text: str) -> dict[str, str]:
    """Map each doc-commented Rust item name in `text` to its `pin:sha256:<12hex>` tag
    (the hash binds the item's doc-block directives and its normalized text)."""
    stripped, doc_segments, _ = _scan_rust_tokens_and_docs(text)
    pins: dict[str, str] = {}
    for grp_start, grp_end, line_docs in _rust_outer_doc_groups(stripped, doc_segments):
        doc_lines = [
            (base_line + off_l, raw_l)
            for base_line, doc_body in line_docs
            for off_l, raw_l in enumerate(doc_body.split("\n"))
        ]
        anns, _ = _collect_block_directives(doc_lines)
        pre_attr = _find_preceding_rust_attributes_start(stripped, grp_start)
        info = _extract_rust_target_span(stripped, grp_end, pre_attr)
        if info is not None:
            t_start, t_end, name = info
            hash_input = waiver_hash_input(anns, _normalize_rust_item(stripped[t_start:t_end]))
            pins[name] = format_pin_tag(compute_sha256_pin12(hash_input))
    return pins


def audit_file(
    file_path: str | Path,
    *,
    check_3axis: bool = True,
    vacuity_scope: str = "all",
) -> list[WaiverPinFinding]:
    """Scan a `.rs` or `.lean` file on disk for waiver-pin and 3-axis non-vacuity findings."""
    path = Path(file_path)
    text = path.read_bytes().decode("utf-8", errors="replace")
    if path.suffix == ".rs":
        return audit_rust_text(text, file_path=path)
    return audit_lean_text(text, file_path=path, check_3axis=check_3axis, vacuity_scope=vacuity_scope)


def count_audit_findings_by_rule(findings: Iterable[WaiverPinFinding]) -> dict[str, int]:
    counts = {rule: 0 for rule in ALL_WAIVER_AUDIT_RULES}
    for f in findings:
        counts[f.rule] = counts.get(f.rule, 0) + 1
    return counts

# ===========================================================================
# END SHARED WAIVER-PIN & 3-AXIS AUDITOR
# ===========================================================================


# ---------------------------------------------------------------------------
# Rules 6 & 7 on top of the shared auditor, Rust scanning, cache control, and CLI
# ---------------------------------------------------------------------------

_WAIVER_SUBRULE_SET: frozenset[str] = frozenset(ALL_WAIVER_RULES)


def _from_audit_finding(wf: WaiverPinFinding) -> ProofHealthFinding:
    """Map a shared-auditor finding onto rule 6 (waiver sub-rules) or rule 7 (vacuity)."""
    return ProofHealthFinding(
        RULE_UNPINNED_OR_DRIFTED_WAIVER
        if wf.rule in _WAIVER_SUBRULE_SET
        else RULE_TRIVIAL_OR_VACUOUS_CLAIM,
        wf.line,
        wf.message,
        wf.suggestion,
        wf.symbol,
        subrule=wf.rule,
        expected_pin=wf.expected_pin,
        actual_pin=wf.actual_pin,
        tier=wf.tier,
    )


def _lean_waiver_and_vacuity_findings(
    text: str,
    *,
    file_path: str | Path | None = None,
    include_unannotated_vacuity: bool = False,
    _preparsed: tuple[str, list[tuple[int, int, int, str, str]]] | None = None,
) -> list[ProofHealthFinding]:
    """Rules 6 and 7 on Lean `text`. Rule 6 needs an `anneal:` directive (Lean docstrings
    are read verbatim, so the directive head cannot be escaped); rule 7 needs a `theorem` or
    `lemma`. Text with neither skips the auditor entirely."""
    has_theorem = "theorem" in text or "lemma" in text
    if not has_theorem and "anneal:" not in text and "pin:sha256:" not in text:
        return []
    return [
        _from_audit_finding(wf)
        for wf in audit_lean_text(
            text,
            file_path=file_path,
            check_3axis=has_theorem,
            vacuity_scope="all" if include_unannotated_vacuity else "annotated",
            _preparsed=_preparsed,
        )
    ]


def scan_rust_text(text: str, *, file_path: str | Path | None = None) -> list[ProofHealthFinding]:
    """Rule 6 on Rust source: waivers in `///`, `/** */` and literal `#[doc = "..."]` docs.

    The fast path is sound: a directive or pin in a `///` / `/** */` comment appears
    verbatim, and one hidden behind string escapes (`#[doc = "anneal\\x3a..."]`) or a
    computed doc attribute (`concat!`, `include_str!`, `cfg_attr`) needs a `doc` token.
    """
    if "anneal:" not in text and "pin:sha256:" not in text and "doc" not in text:
        return []
    findings = [_from_audit_finding(wf) for wf in audit_rust_text(text, file_path=file_path)]
    findings.sort(key=lambda f: (f.line, f.rule, f.symbol))
    return findings


def scan_rust_file(file_path: str | Path) -> list[ProofHealthFinding]:
    path = Path(file_path)
    return scan_rust_text(path.read_bytes().decode("utf-8", errors="replace"), file_path=path)


def scan_file(
    file_path: str | Path,
    *,
    scan_siblings: bool = True,
    include_unannotated_vacuity: bool = False,
    include_advisories: bool = False,
) -> list[ProofHealthFinding]:
    """Scan one `.lean` (rules 1-7, plus advisory rules with `include_advisories`) or
    `.rs` (rule 6) file."""
    path = Path(file_path)
    if path.suffix == ".rs":
        return scan_rust_file(path)
    return scan_lean_file(
        path,
        scan_siblings=scan_siblings,
        include_unannotated_vacuity=include_unannotated_vacuity,
        include_advisories=include_advisories,
    )


def clear_in_process_caches() -> None:
    """Forget every in-process memo (as in a fresh process); persisted caches are untouched.

    `_FILE_TEXTS_CACHE` also holds the `scan_lean_file` text memo and the `_scan_text_meta`
    rules 1-5 index (its `_SCAN_FILE_KEY_PREFIX` / `_SCAN_META_KEY_PREFIX` entries)."""
    _SIBLING_PRIVATE_CACHE.clear()
    _DIR_LEAN_FILES_CACHE.clear()
    _FILE_TEXTS_CACHE.clear()
    _NORM_SIG_CACHE.clear()
    _SCAN_RESULT_CACHE.clear()
    _LAST_LEAN_SCAN.clear()
    _LAST_LEAN_AUDIT.clear()
    _THM_AUDIT_CACHE.clear()
    _META_CACHE.clear()
    _NORM_CACHE.clear()
    _SPLIT_RE_CACHE.clear()


# Directories never descended into when a CLI path is a directory.
_CLI_SKIP_DIRS = frozenset(
    (".git", ".lake", "target", "build", "node_modules", "__pycache__", ".venv", "lake-packages")
)


def _iter_cli_files(raw: str) -> list[Path]:
    """`.lean` / `.rs` files named by one CLI path argument (a file, or a directory walked
    recursively in sorted order, skipping hidden and build directories)."""
    p = Path(raw)
    if p.is_file():
        return [p]
    out: list[Path] = []
    for directory, dirs, files in os.walk(p):
        dirs[:] = sorted(d for d in dirs if d not in _CLI_SKIP_DIRS and not d.startswith("."))
        for name in sorted(files):
            if name.endswith((".lean", ".rs")) and not name.startswith("."):
                out.append(Path(directory) / name)
    return out


_CLI_USAGE = (
    "Usage: proof_health.py [--json] [--all-theorems] [--advisories] [--compute-pins] "
    "[--no-siblings] <file.lean|file.rs|directory> [...]\n"
    "  Scans Lean files for rules 1-7 and Rust files for rule 6; exits 0 when clean,\n"
    "  1 on findings, 2 on usage or I/O errors.\n"
    "  --json          machine-readable report ({ok, finding_count, files_scanned, counts, findings})\n"
    "  --all-theorems  apply every rule 7 check to every theorem (include_unannotated_vacuity)\n"
    "  --advisories    also report advisory rules on Lean files (simp_deep_projection_chain,\n"
    "                  try_rw_hyp_before_target); advisories are marked (`advisory:` / JSON\n"
    "                  `\"advisory\": true`, `advisory_count`) and never fail the exit status\n"
    "  --compute-pins  print the expected `pin:sha256:<12hex>` of every Lean declaration and\n"
    "                  doc-commented Rust item instead of scanning\n"
    "  --no-siblings   skip sibling `.lean` files for rule 5"
)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint (`0` = clean, `1` = findings, `2` = usage / I/O error)."""
    args = list(sys.argv[1:] if argv is None else argv)
    json_mode = all_theorems = compute_pins = advisories = False
    scan_siblings = True
    raw_paths: list[str] = []
    for arg in args:
        if arg == "--json":
            json_mode = True
        elif arg == "--all-theorems":
            all_theorems = True
        elif arg == "--advisories":
            advisories = True
        elif arg == "--compute-pins":
            compute_pins = True
        elif arg == "--no-siblings":
            scan_siblings = False
        elif arg in ("-h", "--help"):
            print(_CLI_USAGE)
            return 0
        elif arg.startswith("-") and arg != "-":
            print(f"error: unknown flag `{arg}`\n{_CLI_USAGE}", file=sys.stderr)
            return 2
        else:
            raw_paths.append(arg)
    if not raw_paths:
        print(f"error: expected at least one file or directory\n{_CLI_USAGE}", file=sys.stderr)
        return 2
    files: list[Path] = []
    for raw in raw_paths:
        try:
            exists = Path(raw).exists()
        except (OSError, ValueError):
            exists = False
        if not exists:
            print(f"error: path not found: {raw}", file=sys.stderr)
            return 2
        files.extend(_iter_cli_files(raw))

    if compute_pins:
        pins_by_file: dict[str, dict[str, str]] = {}
        for f in files:
            try:
                text = f.read_bytes().decode("utf-8", errors="replace")
            except OSError as error:
                print(f"error: cannot read {f}: {error}", file=sys.stderr)
                return 2
            pins = compute_rust_item_pins(text) if f.suffix == ".rs" else compute_lean_decl_pins(text)
            pins_by_file[str(f)] = pins
        if json_mode:
            print(json.dumps(pins_by_file, indent=2, sort_keys=True))
        else:
            for fname, pins in pins_by_file.items():
                for name, tag in pins.items():
                    print(f"{fname}: {name} {tag}")
        return 0

    all_findings: list[dict[str, Any]] = []
    counts = {rule: 0 for rule in ALL_RULES}
    if advisories:
        counts.update({rule: 0 for rule in ADVISORY_RULES})
    advisory_count = 0
    for f in files:
        try:
            findings = scan_file(
                f,
                scan_siblings=scan_siblings,
                include_unannotated_vacuity=all_theorems,
                include_advisories=advisories,
            )
        except OSError as error:
            print(f"error: cannot read {f}: {error}", file=sys.stderr)
            return 2
        for finding in findings:
            counts[finding.rule] = counts.get(finding.rule, 0) + 1
            entry = finding.to_dict()
            entry["file"] = str(f)
            is_advisory = finding.rule in _ADVISORY_RULE_SET
            if is_advisory:
                entry["advisory"] = True
                advisory_count += 1
            all_findings.append(entry)
            if not json_mode:
                tag = f"{finding.rule}/{finding.subrule}" if finding.subrule else finding.rule
                if is_advisory:
                    tag = "advisory:" + tag
                print(
                    f"{f}:{finding.line}: [{tag}] ({finding.symbol}) {finding.message} "
                    f"Suggestion: {finding.suggestion}"
                )
    ok = len(all_findings) == advisory_count
    if json_mode:
        report: dict[str, Any] = {
            "ok": ok,
            "finding_count": len(all_findings),
            "files_scanned": len(files),
            "counts": counts,
            "findings": all_findings,
        }
        if advisories:
            report["advisory_count"] = advisory_count
        print(json.dumps(report, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
