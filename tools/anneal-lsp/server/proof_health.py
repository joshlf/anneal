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

Also provides delta-only post-edit checking (`check_post_edit_proof_health`) for
`tools/anneal-lsp/hooks/post_tool_use.py` and unbatched tool-call latency telemetry
(`compute_unbatched_tool_latencies`).
"""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

from bisect import bisect_right
import json
import os
from pathlib import Path
import re
from typing import Any, Iterable

RULE_DSIMP_FORBIDDEN_SYM = "dsimp_forbidden_sym"
RULE_DSIMP_MIR_BODY_UNFOLD = "dsimp_mir_body_unfold"
RULE_RAW_BITWISE_UNFOLD = "raw_bitwise_unfold"
RULE_LOW_PROFILER_THRESHOLD = "low_profiler_threshold"
RULE_DUPLICATE_PRIVATE_LEMMA = "duplicate_private_lemma"

ALL_RULES: tuple[str, ...] = (
    RULE_DSIMP_FORBIDDEN_SYM,
    RULE_DSIMP_MIR_BODY_UNFOLD,
    RULE_RAW_BITWISE_UNFOLD,
    RULE_LOW_PROFILER_THRESHOLD,
    RULE_DUPLICATE_PRIVATE_LEMMA,
)

MIN_PROFILER_THRESHOLD = 50
DEFAULT_LONG_CALL_THRESHOLD_MS = 1000.0


class ProofHealthFinding:
    """One structural finding: rule id, 1-based source line, message, fix suggestion
    and the offending symbol. Immutable; compares and hashes by value.

    A plain `__slots__` class rather than a dataclass: importing `dataclasses` costs
    about 10 ms, which every hook process would pay since no bytecode is cached.
    """

    __slots__ = ("rule", "line", "message", "suggestion", "symbol")

    def __init__(
        self, rule: str, line: int, message: str, suggestion: str, symbol: str = ""
    ) -> None:
        set_attr = object.__setattr__
        set_attr(self, "rule", rule)
        set_attr(self, "line", line)
        set_attr(self, "message", message)
        set_attr(self, "suggestion", suggestion)
        set_attr(self, "symbol", symbol)

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError("ProofHealthFinding is immutable")

    def _key(self) -> tuple[str, int, str, str, str]:
        return (self.rule, self.line, self.message, self.suggestion, self.symbol)

    def __eq__(self, other: object) -> bool:
        if other.__class__ is not ProofHealthFinding:
            return NotImplemented
        return self._key() == other._key()  # type: ignore[attr-defined]

    def __hash__(self) -> int:
        return hash(self._key())

    def __repr__(self) -> str:
        return (
            "ProofHealthFinding(rule=%r, line=%r, message=%r, suggestion=%r, symbol=%r)"
            % self._key()
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "rule": self.rule,
            "line": self.line,
            "message": self.message,
            "suggestion": self.suggestion,
            "symbol": self.symbol,
        }


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
        "line",
        "file",
        "raw_header",
        "sig_fp",
        "body_start",
        "decl_indent",
        "path",
        "_rename_map",
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
    ) -> None:
        self.kind = kind
        self.name = name
        self.norm_sig = norm_sig
        self.line = line
        self.file = file
        self.raw_header = raw_header
        self.sig_fp = sig_fp
        self.body_start = body_start
        self.decl_indent = decl_indent
        self.path = path
        self._rename_map: dict[str, str] | None = None

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


def _is_ident_char(ch: str) -> bool:
    # Lean 4 identifier continuation characters (`isIdRest`): letters (including
    # Unicode letters and subscripts), digits, `_`, `'`, `!` and `?` (`get?`, `get!`).
    return ch.isalnum() or ch in "_'!?"


# Byte table mapping every byte except `\n` to a space (`bytes.translate` is a tight
# C loop; ASCII text round-trips through it unchanged in length).
_BLANK_BYTES_TABLE = bytes(10 if i == 10 else 32 for i in range(256))


def _blank(seg: str) -> str:
    """`seg` with every character except newlines replaced by a space."""
    if "\n" not in seg:
        return " " * len(seg)
    if seg.isascii():
        return seg.encode("ascii").translate(_BLANK_BYTES_TABLE).decode("ascii")
    return "\n".join([" " * len(part) for part in seg.split("\n")])


def strip_lean_comments_and_strings(text: str, *, keep_strings: bool = False) -> str:
    """Blank out Lean 4 `--` line comments, nested `/- ... -/` block comments
    (docstrings included) and string literals, character for character: the result
    has the same length as `text` and keeps every `\\n`, so offsets and line
    numbers in it are exactly those of `text`.

    String literals honour `\\"` / `\\\\` escapes; raw strings `r"..."` / `r#"..."#`
    end at the matching `"#...`; the quote character literals `'"'` / `'\\"'` do not
    open a string, while an identifier prime before a string (`x'"..."`) does not
    make a character literal; guillemet names `«a--b»` are code, not comments. With
    `keep_strings=True` only comments are blanked. The scan jumps between delimiters
    with `str.find`, about 3 ms per MB of Lean source.
    """
    n = len(text)
    if n == 0:
        return ""
    out: list[str] = []
    app = out.append  # bound once: the loop runs once per comment/string token
    find = text.find
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
            app(text[pos:])
            break
        if nxt > pos:
            app(text[pos:nxt])

        if kind == 4:
            # Lean 4 guillemet identifier `«...»` (single-line): `--` or `/-` inside
            # `«a--b»` is part of the identifier name, not a comment start.
            g_end = find("»", nxt + 1)
            if g_end != -1 and find("\n", nxt + 1, g_end) == -1:
                app(text[nxt : g_end + 1])
                pos = g_end + 1
            else:
                app("«")
                pos = nxt + 1
            continue

        if kind == 2:
            # `--` line comment up to (not including) the newline
            nl = find("\n", nxt + 2)
            end = n if nl == -1 else nl
            app(" " * (end - nxt))
            pos = end
            continue

        if kind == 1:
            # `/- ... -/` block comment with arbitrary nesting depth
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
            if find("\n", nxt, cur) == -1:
                app(" " * (cur - nxt))
            else:
                app(_blank(text[nxt:cur]))
            pos = cur
            continue

        # Raw string literal `r"..."` / `r#"..."#` and quote character literals `'"'` / `'\"'`
        if nxt > 0 and text[nxt - 1] in "#r'":
            h = nxt
            while h > 0 and text[h - 1] == "#":
                h -= 1
            if (
                h > 0
                and text[h - 1] == "r"
                and (h < 2 or not (_is_ident_char(text[h - 2]) or text[h - 2] == "."))
            ):
                closer = '"' + "#" * (nxt - h)
                c = find(closer, nxt + 1)
                cur = n if c == -1 else c + len(closer)
                app(text[nxt:cur] if keep_strings else _blank(text[nxt:cur]))
                pos = cur
                continue
            if (
                nxt + 1 < n
                and text[nxt + 1] == "'"
                and (
                    (
                        text[nxt - 1] == "'"
                        and (nxt < 2 or not _is_ident_char(text[nxt - 2]))
                    )
                    or (
                        nxt >= 2
                        and text[nxt - 2 : nxt] == "'\\"
                        and (nxt < 3 or not _is_ident_char(text[nxt - 3]))
                    )
                )
            ):
                app('"' if keep_strings else " ")
                pos = nxt + 1
                i_str = find('"', pos)
                continue
        q = find('"', nxt + 1)
        if q == -1:
            cur = n
        elif text[q - 1] != "\\":
            cur = q + 1
        else:
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
        if keep_strings:
            app(text[nxt:cur])
        elif find("\n", nxt, cur) == -1:
            app(" " * (cur - nxt))
        else:
            app(_blank(text[nxt:cur]))
        pos = cur
    return "".join(out)


def _offset_to_line(text_or_offsets: str | list[int], offset: int) -> int:
    if isinstance(text_or_offsets, str):
        return text_or_offsets.count("\n", 0, offset) + 1
    return bisect_right(text_or_offsets, offset) + 1


class _LineCounter:
    """1-based line numbers of offsets in `text`, counted incrementally from the
    previous query, so a scan's queries cost O(len(text)) in total instead of one
    prefix count per finding."""

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


# Tactic and pattern regexes on stripped Lean 4 text.
# Leading literal prefixes (`simp`, `unfold`, `delta`, `set_option`, `private`)
# let CPython's `sre` skip ahead with a literal search instead of trying every offset.
# Cold-path regexes are compiled lazily on first use to keep fresh hook imports fast.
_SIMP_VARIANT_TUPLE: tuple[str, ...] = ("_all_arith", "_all", "_arith", "_rw", "a")
_IDENT_BEFORE = r"(?<![\w'!?.])"
_IDENT_AFTER = r"(?![\w'!?.])"
_QUAL_PREFIX = r"(?:[^\W\d][\w'!?]*\.)*"
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
    _IDENT_BEFORE + r"(" + _QUAL_PREFIX + r"Mir(?:\.[\w'!?]+)+\.body)" + _UNFOLD_EQ_SUFFIX + _IDENT_AFTER
)
_RAW_BITWISE_RE = re.compile(
    _IDENT_BEFORE + _QUAL_PREFIX + r"(bitwise(?:And|Or)Bits)" + _UNFOLD_EQ_SUFFIX + _IDENT_AFTER
)
_EQ_SUFFIX_AT_RE = re.compile(r"\.(?:eq_def|eq_unfold|eq_\d+)(?![\w'!?.])")
_PROFILER_THRESHOLD_RE = re.compile(
    r"set_option\s+trace\.profiler\.threshold\s+(\d+(?:_\d+)*)(?![\w'!?])"
)
_DECL_NAME = r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*|«[^»\n]*»"
_PRIVATE_LIT_RE = re.compile(
    r"private\s+(?:(?:noncomputable|partial|unsafe|nonrec)\s+)*(theorem|lemma|def)\s+("
    + _DECL_NAME
    + r")"
)
_TOPLEVEL_LINE_RE = re.compile(r"\n(?=\S)")
_DECL_BOUNDARY_RE: re.Pattern[str] | None = None
_EQN_ALT_LINE_RE: re.Pattern[str] | None = None
_MATCH_OR_FUN_RE: re.Pattern[str] | None = None
_HDR_TOKEN_RE: re.Pattern[str] | None = None
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
        if (content[k] == ":" and content[k : k + 2] != ":=") or is_eq_lemma:
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
                elif c2 == "," and depth == 1 and bdepth == 0:
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


def _active_simp_keywords(
    stripped: str, simp_start: int = 0, check_rule1: bool = True
) -> tuple[dict[str, int], bool, bool]:
    """Map of candidate keywords to their first offset in `stripped`, plus
    `(has_mir_body, has_bitwise)`. Avoids scanning twice for the same keyword."""
    kw_offsets: dict[str, int] = {}
    if check_rule1:
        p = stripped.find("wpMirExecSym", simp_start)
        if p != -1:
            kw_offsets["wpMirExecSym"] = p
        p = stripped.find("Sequence.length", simp_start)
        if p != -1:
            kw_offsets["Sequence.length"] = p
    p_body = stripped.find(".body", 0)
    has_mir_body = p_body != -1 and stripped.find("Mir.", 0) != -1
    if has_mir_body:
        kw_offsets[".body"] = p_body
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
    return kw_offsets, has_mir_body, has_bitwise


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
                yield kw, tok_start, tok
            pos = stripped.find(kw, end_kw)


def _line_indent_at(stripped: str, pos: int) -> int:
    line_start = stripped.rfind("\n", 0, pos) + 1
    k = line_start
    n = len(stripped)
    while k < n and stripped[k] in " \t":
        k += 1
    return k - line_start


def _get_decl_boundary_re() -> re.Pattern[str]:
    global _DECL_BOUNDARY_RE
    if _DECL_BOUNDARY_RE is None:
        _DECL_BOUNDARY_RE = re.compile(
            r"\n(?:(?=\S)|([ \t]+)(?=@\[|"
            r"(?:private|protected|public|scoped|local|noncomputable|partial|unsafe|"
            r"theorem|lemma|def|abbrev|opaque|axiom|example|instance|class|structure|"
            r"inductive|mutual|section|namespace|end|variable|open|universe|set_option)(?![\w'!?.])|"
            r"#(?:check|eval|print|reduce)\b))"
        )
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
    for m in _get_decl_boundary_re().finditer(stripped, start_pos, max_end):
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
    global _EQN_ALT_LINE_RE, _MATCH_OR_FUN_RE, _HDR_TOKEN_RE
    n = len(stripped)
    max_end = min(n, start_pos + 2500)
    first_ce = stripped.find(":=", start_pos, max_end)
    if first_ce != -1:
        cand0 = stripped[start_pos:first_ce]
        if (
            ":" in cand0
            and "|" not in cand0
            and "let " not in cand0
            and "where" not in cand0
            and "«" not in cand0
            and cand0.count("(") == cand0.count(")")
            and cand0.count("{") == cand0.count("}")
            and cand0.count("[") == cand0.count("]")
            and _next_decl_boundary(stripped, start_pos, first_ce, decl_indent) == first_ce
        ):
            return cand0, first_ce + 2

    limit = _next_decl_boundary(stripped, start_pos, max_end, decl_indent)
    if _EQN_ALT_LINE_RE is None:
        _EQN_ALT_LINE_RE = re.compile(r"\n[ \t]*\|")
        _MATCH_OR_FUN_RE = re.compile(r"(?<![\w'!?.])(?:match|fun|λ)(?![\w'!?])")
        _HDR_TOKEN_RE = re.compile(r"«[^»\n]*»|[()\[\]{}]|:=|:|(?<![\w'!?.])where(?![\w'!?])")
    eqn_end = False
    m_alt = _EQN_ALT_LINE_RE.search(stripped, start_pos, limit)
    if m_alt is not None and _MATCH_OR_FUN_RE.search(stripped, start_pos, m_alt.start()) is None:  # type: ignore[union-attr]
        eqn_end = True
        limit = m_alt.start()
    if "«" not in stripped[start_pos:limit]:
        search_pos = start_pos
        while search_pos < limit:
            colon_eq = stripped.find(":=", search_pos, limit)
            if colon_eq == -1:
                break
            candidate = stripped[start_pos:colon_eq]
            if (
                candidate.count("(") == candidate.count(")")
                and candidate.count("{") == candidate.count("}")
                and candidate.count("[") == candidate.count("]")
                and "let " not in candidate
                and "where" not in candidate
            ):
                return (candidate, colon_eq + 2) if ":" in candidate else ("", -1)
            search_pos = colon_eq + 2

    depth = 0
    colon_pos = -1
    for tm in _HDR_TOKEN_RE.finditer(stripped, start_pos, limit):  # type: ignore[union-attr]
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
) -> list[PrivateDecl]:
    pos = stripped.find("private", 0)
    if pos == -1:
        return []
    decls: list[PrivateDecl] = []
    if line_of is None and newline_offsets is None:
        line_of = _LineCounter(stripped)
    while pos != -1:
        if pos == 0 or not (_is_ident_char(stripped[pos - 1]) or stripped[pos - 1] == "."):
            m = _PRIVATE_LIT_RE.match(stripped, pos)
            if m is not None:
                kind = m.group(1)
                name = m.group(2)
                if line_of is not None:
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
_FILE_TEXTS_CACHE: dict[str, tuple[int, int, str, str]] = {}

COUNT_CACHE_MAX_FILES = 1024
# Bump whenever rule semantics, signature normalization, or index layout change:
# count entries and sibling indexes written under another version are ignored.
CACHE_FORMAT_VERSION = 4


def sibling_index_path(cache_path: str | Path, directory: str | Path) -> Path:
    """File holding the persisted private-declaration index of `directory`'s `.lean`
    files, next to the count cache `cache_path`."""
    import zlib

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
            if len(rec) == 8:
                kind, name, line, body_start, norm_sig, fp, decl_indent, raw_header = rec
            else:
                return None
            if kind not in ("theorem", "lemma", "def"):
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
        return file_crc, out
    except (TypeError, ValueError, IndexError, KeyError):
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
    except OSError:
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
    except OSError:
        return []
    file_crc = _text_crc(raw)
    if cached is not None and cached[0] == st.st_mtime_ns and cached[1] == st.st_size and cached[2] == file_crc:
        decls = cached[3]
        if persisted is not None and not racy:
            persisted[key] = _index_entry(st, file_crc, decls)
        return decls

    _FILE_TEXTS_CACHE.pop(key, None)
    decls = []
    if "private" in raw:
        stripped = strip_lean_comments_and_strings(raw)
        _FILE_TEXTS_CACHE[key] = (st.st_mtime_ns, st.st_size, raw, stripped)
        decls = extract_private_decls(
            stripped, file_label=sibling_path.name, lazy_norm=True, file_path=key
        )
    _SIBLING_PRIVATE_CACHE[key] = (st.st_mtime_ns, st.st_size, file_crc, decls)
    if persisted is not None and not racy:
        persisted[key] = _index_entry(st, file_crc, decls)
    return decls


# File timestamps come from a coarse kernel clock, so a second same-size write within
# one tick leaves `(mtime_ns, size)` unchanged. Files modified within this window are
# not persisted in the sibling index and are CRC-checked on access.
RACY_MTIME_WINDOW_NS = 2_000_000_000


def _is_racy(st: os.stat_result) -> bool:
    import time

    return time.time_ns() - st.st_mtime_ns < RACY_MTIME_WINDOW_NS


def _file_texts(path_str: str) -> tuple[str, str] | None:
    """`(raw, comment_stripped)` texts of `path_str`."""
    p = Path(path_str)
    try:
        st = p.stat()
    except OSError:
        return None
    if not _is_racy(st):
        cached = _FILE_TEXTS_CACHE.get(path_str)
        if cached is not None and cached[0] == st.st_mtime_ns and cached[1] == st.st_size:
            return cached[2], cached[3]
    try:
        raw = p.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None
    cached = _FILE_TEXTS_CACHE.get(path_str)
    if cached is not None and cached[2] == raw:
        return cached[2], cached[3]
    stripped = strip_lean_comments_and_strings(raw)
    _FILE_TEXTS_CACHE[path_str] = (st.st_mtime_ns, st.st_size, raw, stripped)
    return raw, stripped


def _list_dir_lean_files(parent: Path, max_files: int) -> list[Path]:
    key = str(parent)
    try:
        st = parent.stat()
    except OSError:
        return []
    cached = _DIR_LEAN_FILES_CACHE.get(key)
    if cached is not None and cached[0] == st.st_mtime_ns:
        return cached[1]
    files: list[Path] = []
    try:
        entries = sorted(parent.iterdir(), key=lambda p: p.name)
    except OSError:
        return []
    for entry in entries:
        if len(files) >= max_files + 1:
            break
        if entry.name.startswith(".") or entry.suffix != ".lean":
            continue
        if entry.is_symlink() or not entry.is_file():
            continue
        files.append(entry)
    _DIR_LEAN_FILES_CACHE[key] = (st.st_mtime_ns, files)
    return files


def _collect_sibling_private_decls(
    file_path: Path,
    max_siblings: int = 40,
    persisted: dict[str, Any] | None = None,
) -> list[PrivateDecl]:
    parent = file_path.parent
    target_name = file_path.name
    out: list[PrivateDecl] = []
    count = 0
    for entry in _list_dir_lean_files(parent, max_siblings):
        if count >= max_siblings:
            break
        if entry.name == target_name:
            continue
        count += 1
        out.extend(_extract_sibling_private_decls_fast(entry, persisted))
    return out


def _load_sibling_index(index_file: Path) -> dict[str, Any]:
    data = _load_cache(index_file)
    return data if isinstance(data, dict) else {}


def _save_sibling_index(index_file: Path, index: dict[str, Any]) -> None:
    for key in [k for k in index if not os.path.isfile(k)]:
        del index[key]
    _save_cache(index_file, index)


def _sig_class(kind: str) -> str:
    return "def" if kind == "def" else "prop"


def _duplicate_private_findings(
    local_decls: list[PrivateDecl],
    ext_decls: list[PrivateDecl],
    raw: str,
    stripped: str,
) -> list[ProofHealthFinding]:
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
            key: BodyKey | None = None
            span = body_span(d, local)
            if span is not None:
                r, st, b, e = span
                if b < e:
                    cand = (st.count(",", b, e), st.count("=", b, e), st.count(".", b, e))
                    if cand != (0, 0, 0) or r[b:e].strip():
                        key = cand
            key1_cache[k] = key
        return key1_cache[k]

    def key2(d: PrivateDecl, local: bool, has_binders: bool) -> BodyKey | None:
        k = id(d)
        if k in key2_cache:
            return key2_cache[k]
        span = body_span(d, local)
        if span is None:
            key2_cache[k] = None
            return None
        r, st, b, e = span
        if not has_binders:
            noc = _strip_comments_fast(r[b:e])
            comp = noc.encode("utf-8", "surrogatepass").translate(None, _WS_BYTES)
            res: BodyKey | None = (0, len(comp), hash(comp)) if comp else None
            key2_cache[k] = res
            return res
        if budget[0] <= 0:
            return None
        budget[0] -= e - b
        comp = (
            _BODY_IDENT_RE.sub("_", st[b:e])
            .encode("utf-8", "surrogatepass")
            .translate(None, _WS_BYTES)
        )
        res = (1, len(comp), hash(comp))
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


def scan_lean_text(
    text: str,
    *,
    file_path: str | Path | None = None,
    scan_siblings: bool = True,
    sibling_decls: list[PrivateDecl] | None = None,
) -> list[ProofHealthFinding]:
    """Scan Lean 4 source `text` and return all structural proof-health findings."""
    stripped = strip_lean_comments_and_strings(text)
    line_of = _LineCounter(stripped)
    findings: list[ProofHealthFinding] = []

    first_simp = stripped.find("simp", 0)
    has_unfold_kw = first_simp != -1 or "unfold" in stripped or "delta" in stripped
    if has_unfold_kw:
        active_kws, has_mir_body, has_bitwise = _active_simp_keywords(
            stripped,
            simp_start=(first_simp + 4) if first_simp != -1 else 0,
            check_rule1=(first_simp != -1),
        )
    else:
        active_kws, has_mir_body, has_bitwise = {}, False, False

    # Rules 1, 2, 3 inside `dsimp [...]` / `simp [...]` bracket lists
    if active_kws and first_simp != -1:
        for tactic_kind, open_idx, close_idx, content in _iter_simp_brackets(
            stripped, active_kws=active_kws
        ):
            if not _has_simp_candidate(content):
                continue
            base_offset = open_idx + 1

            # Rule 1: `dsimp_forbidden_sym`
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
    if (has_mir_body or has_bitwise) and ("unfold" in stripped or "delta" in stripped):
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
    if "profiler.threshold" in stripped:
        for pm in _PROFILER_THRESHOLD_RE.finditer(stripped):
            before = stripped[pm.start() - 1] if pm.start() > 0 else " "
            if _is_ident_char(before) or before == ".":
                continue
            val = int(pm.group(1).replace("_", ""))
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
    local_decls = extract_private_decls(
        stripped,
        file_label=Path(file_path).name if file_path else "",
        lazy_norm=True,
        line_of=line_of,
    )
    if local_decls:
        ext_decls: list[PrivateDecl] = []
        if sibling_decls is not None:
            ext_decls = list(sibling_decls)
        elif scan_siblings and file_path is not None:
            ext_decls = _collect_sibling_private_decls(Path(file_path))
        findings.extend(_duplicate_private_findings(local_decls, ext_decls, text, stripped))

    findings.sort(key=lambda f: (f.line, f.rule, f.symbol))
    return findings


def scan_lean_file(
    file_path: str | Path,
    *,
    scan_siblings: bool = True,
) -> list[ProofHealthFinding]:
    path = Path(file_path)
    # Bytes + decode skips text-mode newline translation; line numbers count `\n`
    # either way and a stray `\r` is whitespace to every rule.
    text = path.read_bytes().decode("utf-8", errors="replace")
    return scan_lean_text(text, file_path=path, scan_siblings=scan_siblings)


def count_findings_by_rule(findings: Iterable[ProofHealthFinding]) -> dict[str, int]:
    counts = {rule: 0 for rule in ALL_RULES}
    for f in findings:
        counts[f.rule] = counts.get(f.rule, 0) + 1
    return counts


def default_cache_path() -> Path:
    env_path = os.environ.get("ANNEAL_PROOF_HEALTH_CACHE")
    if env_path and env_path.strip():
        return Path(env_path.strip())
    uid = getattr(os, "getuid", lambda: 0)()
    return Path(f"/tmp/anneal-proof-health-cache-{uid}.json")


def _text_crc(text: str) -> int:
    """CRC-32 of `text` (UTF-16 code units; a near-memcpy encoding for Lean source)."""
    import zlib

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
        except OSError:
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


_JETSKI_REPL_RESULT_RE: re.Pattern[str] | None = None


def _jetski_result_hint(payload: dict[str, Any] | None) -> tuple[int | None, int | None]:
    """Parse `(count, start_line)` from Jetski's `edit_file` result string if present."""
    global _JETSKI_REPL_RESULT_RE
    if not isinstance(payload, dict):
        return None, None
    res = payload.get("result")
    if not isinstance(res, str) or "Made " not in res:
        return None, None
    if _JETSKI_REPL_RESULT_RE is None:
        _JETSKI_REPL_RESULT_RE = re.compile(
            r"\bMade\s+(\d+)\s+replacements?\b(?:[^\n]*?\bstarting at line\s+(\d+)\b)?"
        )
    m = _JETSKI_REPL_RESULT_RE.search(res)
    if m is None:
        return None, None
    cnt = int(m.group(1))
    sline = int(m.group(2)) if m.group(2) is not None else None
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
    repl_cnt, repl_line = _jetski_result_hint(payload)
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
                if repl_cnt == 1 and repl_line is not None:
                    off = _line_start_offset(after_text, repl_line)
                    idx = after_text.find(new_s, off)
                    if idx != -1 and after_text.count("\n", off, idx) == 0:
                        return after_text[:idx] + old_s + after_text[idx + len(new_s) :]
                return None
    return None


def _invert_ambiguous_without_cache(
    after_text: str, payload: dict[str, Any] | None
) -> str | None:
    """Best-effort pre-edit text for rule-count baseline when no cache exists and
    `Replacement` / `new_string` occurs multiple times (or mixes a deletion step
    with an insertion step inside `MultiEdit`)."""
    repl_cnt, _ = _jetski_result_hint(payload)
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
    """Return the Jetski `write_file` argument dict (`Content` plus optional
    `Overwrite` / `Append` flags) carried by `payload`, if any."""
    for args in _extract_edit_args_list(payload):
        if isinstance(args.get("Content"), str) and "Target" not in args:
            return args
    return None


def _line_spans_of_insertions(
    after_text: str, inserted: list[str], payload: dict[str, Any] | None = None
) -> list[tuple[int, int]]:
    """1-based inclusive line ranges covered by inserted strings in `after_text`."""
    repl_cnt, repl_line = _jetski_result_hint(payload)
    if repl_cnt == 1 and repl_line is not None and len(inserted) == 1:
        ins = inserted[0]
        last = repl_line + ins.count("\n", 0, max(len(ins) - 1, 0))
        return [(repl_line, last)]
    spans: list[tuple[int, int]] = []
    for ins in inserted:
        start = after_text.find(ins)
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
    the edit payload in memory (using Jetski's `Made <K> replacement(s) ... starting
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
    path = Path(os.path.abspath(target_file))
    try:
        resolved_key = str(path.resolve())
    except OSError:
        resolved_key = str(path)

    if after_text is None:
        after_text = path.read_text(encoding="utf-8", errors="replace")

    cpath = Path(cache_path) if cache_path is not None else default_cache_path()
    cache = _load_cache(cpath)

    sibling_decls: list[PrivateDecl] = []
    if scan_siblings and "private" in after_text:
        index_file = sibling_index_path(cpath, path.parent)
        sibling_index = _load_sibling_index(index_file)
        had_missing = any(not os.path.isfile(k) for k in sibling_index)
        before_ids = {k: id(v) for k, v in sibling_index.items()}
        sibling_decls = _collect_sibling_private_decls(path, persisted=sibling_index)
        if had_missing or {k: id(v) for k, v in sibling_index.items()} != before_ids:
            _save_sibling_index(index_file, sibling_index)

    def _scan(text: str) -> list[ProofHealthFinding]:
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
        return {rule: _safe_int(cached_entry.get(rule, 0), 0) for rule in ALL_RULES}

    write_args = _write_file_args(payload)
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
        before_counts = {rule: _safe_int(cached_entry.get(rule, 0), 0) for rule in ALL_RULES}
        spans = _line_spans_of_insertions(after_text, _replacement_strings(payload), payload)
    elif _is_pure_deletion(payload):
        before_counts = dict(after_counts)
    else:
        ambiguous_before = _invert_ambiguous_without_cache(after_text, payload)
        if ambiguous_before is not None:
            before_findings = _scan(ambiguous_before)
            before_counts = count_findings_by_rule(before_findings)
            before_text = ambiguous_before
            spans = _line_spans_of_insertions(after_text, _replacement_strings(payload), payload)
        else:
            before_counts = dict(after_counts)

    entry: dict[str, int] = dict(after_counts)
    entry["_len"] = len(after_text)
    entry["_crc"] = _text_crc(after_text)
    entry["_sib"] = sib_sig
    entry["_ver"] = CACHE_FORMAT_VERSION
    cache.pop(resolved_key, None)
    cache[resolved_key] = entry
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

_CREATED_COMPLETED_RE: re.Pattern[str] | None = None


def _is_finite_nonneg_number(val: Any) -> bool:
    if isinstance(val, bool) or not isinstance(val, (int, float)):
        return False
    import math

    return math.isfinite(val) and val >= 0


def _parse_iso_ts(ts: Any) -> float | None:
    if not isinstance(ts, bool) and isinstance(ts, (int, float)):
        import math

        return float(ts) if math.isfinite(ts) else None
    if not isinstance(ts, str) or not ts.strip():
        return None
    from datetime import datetime

    s = ts.strip()
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    try:
        return datetime.fromisoformat(s).timestamp()
    except ValueError:
        return None


def _first_present(obj: dict[str, Any], keys: tuple[str, ...]) -> Any:
    for k in keys:
        v = obj.get(k)
        if v is not None and v != "":
            return v
    return None


def _extract_duration_ms(obj: dict[str, Any]) -> float | None:
    global _CREATED_COMPLETED_RE
    for key in ("duration_ms", "latency_ms", "elapsed_ms", "time_ms"):
        val = obj.get(key)
        if _is_finite_nonneg_number(val):
            return float(val)
    for key in ("duration_s", "latency_s", "elapsed_s"):
        val = obj.get(key)
        if _is_finite_nonneg_number(val):
            return float(val) * 1000.0
    start_ts = _parse_iso_ts(_first_present(obj, ("started_at", "created_at", "start_time")))
    end_ts = _parse_iso_ts(_first_present(obj, ("completed_at", "finished_at", "end_time")))
    if start_ts is not None and end_ts is not None and end_ts >= start_ts:
        return (end_ts - start_ts) * 1000.0
    content = obj.get("content") if obj.get("content") is not None else obj.get("output")
    if isinstance(content, str) and "Created At:" in content:
        if _CREATED_COMPLETED_RE is None:
            _CREATED_COMPLETED_RE = re.compile(
                r"Created At:\s*(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z)\s*\r?\n"
                r"Completed At:\s*(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z)"
            )
        m = _CREATED_COMPLETED_RE.search(content)
        if m:
            t0 = _parse_iso_ts(m.group(1))
            t1 = _parse_iso_ts(m.group(2))
            if t0 is not None and t1 is not None and t1 >= t0:
                return (t1 - t0) * 1000.0
    return None


def _is_jetski_tool_result_step(item: dict[str, Any]) -> bool:
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
    if isinstance(source, (str, Path)):
        path = Path(source)
        if path.is_file():
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
    for key in ("batch_id", "step_index", "turn_id"):
        val = obj.get(key)
        if val is not None and val != "" and not isinstance(val, bool):
            return val
    return fallback


def _safe_int(val: Any, default: int = 1) -> int:
    if isinstance(val, bool):
        return default
    try:
        return int(val)
    except (TypeError, ValueError):
        return default


def _tool_name(obj: dict[str, Any]) -> str | None:
    name = obj.get("tool") or obj.get("name") or obj.get("tool_name")
    return str(name) if name is not None and str(name).strip() else None


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
    - Jetski `transcript.jsonl` steps, where a `PLANNER_RESPONSE` step lists its
      `tool_calls` (one batch) and the following result steps report, in order,
      `Created At: ... / Completed At: ...` timestamps for each call. A result step
      without `Completed At` (a call backgrounded while still `RUNNING`, or an error)
      still consumes its call, and a backgrounded call marks its batch as containing
      a long call. These timestamps have one-second resolution, so such durations
      are whole seconds (a sub-second call straddling a second boundary reads 1000 ms).
    Entries without usable timings are skipped without raising.
    """
    import statistics

    allowed_tools: set[str] | None = None
    if isinstance(tool_filter, str):
        allowed_tools = {tool_filter}
    elif tool_filter is not None:
        allowed_tools = set(tool_filter)

    raw_batches: dict[Any, list[dict[str, Any]]] = {}
    long_marked_batches: set[Any] = set()
    auto_batch_seq = 0
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
            if pending and _is_jetski_tool_result_step(item):
                ptool, pbatch, psize = pending.pop(0)
                dur = _extract_duration_ms(item)
                if dur is not None:
                    _record(ptool, dur, pbatch, item, psize)
                elif _is_backgrounded_long_step(item):
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
