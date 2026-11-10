#!/usr/bin/env python3
"""Fast (<5 ms) structural proof-health linter and transcript latency telemetry for Anneal Lean 4 proofs.

Detects five structural kernel-scaling anti-patterns on Lean 4 files. Comments, nested
block comments (`/- ... -/`), docstrings and string literals are blanked first, so
mentions inside them never count:
1. `dsimp_forbidden_sym`: `wpMirExecSym` or `Trusted.Sequence.length` / `Sequence.length`
   (optionally namespace-qualified or as `.eq_def`) inside the lemma list of a
   simp-family tactic (`dsimp`, `simp`, `simp only`, `simp?`, `simpa`, `simp_all`, ...,
   with or without `(config := ...)` / `+opt` arguments). Purely syntactic: no
   location- or neighbour-based exemptions; only erasures `-name` do not count.
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
        "path",
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
    ) -> None:
        self.kind = kind
        self.name = name
        self.norm_sig = norm_sig
        self.line = line
        self.file = file
        self.raw_header = raw_header
        self.sig_fp = sig_fp
        self.body_start = body_start
        self.path = path

    def ensure_norm_sig(self) -> str:
        if not self.norm_sig and self.raw_header:
            self.norm_sig = _normalize_signature(self.raw_header)
        return self.norm_sig

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
    open a string, and identifier primes (`st'`) are left untouched. With
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
    while pos < n:
        if i_blk != -1 and i_blk < pos:
            i_blk = find("/-", pos)
        if i_lin != -1 and i_lin < pos:
            i_lin = find("--", pos)
        if i_str != -1 and i_str < pos:
            i_str = find('"', pos)

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

        if kind == 0:
            app(text[pos:])
            break
        if nxt > pos:
            app(text[pos:nxt])

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

        # Raw string literal `r"..."` / `r#"..."#`: no escapes, closed by `"`
        # followed by as many `#` as opened it.
        h = nxt
        while h > 0 and text[h - 1] == "#":
            h -= 1
        if h > 0 and text[h - 1] == "r" and (h < 2 or not _is_ident_char(text[h - 2])):
            closer = '"' + "#" * (nxt - h)
            c = find(closer, nxt + 1)
            cur = n if c == -1 else c + len(closer)
            app(text[nxt:cur] if keep_strings else _blank(text[nxt:cur]))
            pos = cur
            continue
        # Quote character literals `'"'` and `'\"'` do not open a string.
        if (
            nxt > 0
            and nxt + 1 < n
            and text[nxt + 1] == "'"
            and (
                text[nxt - 1] == "'"
                or (nxt >= 2 and text[nxt - 2 : nxt] == "'\\")
            )
        ):
            app('"' if keep_strings else " ")
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
        else:
            self.line -= self.text.count("\n", offset, self.off)
        self.off = offset
        return self.line


# Tactic and pattern regexes on stripped Lean 4 text.
# Leading literal prefixes (`simp`, `unfold`, `delta`, `set_option`, `private`)
# let CPython's `sre` skip ahead with a literal search instead of trying every offset.
#
# Header of a simp-family tactic, ending at the `[` of its lemma list: `simp`,
# `simpa`, `simp_all`, `simp_arith`, `simp_all_arith` or `simp_rw` (`dsimp` is
# recognised by looking one character back), optional `?` / `!` suffixes, then any
# mix of `(config := ...)` / `(disch := ...)` arguments, `+opt` / `-opt` flags and
# `only`.
_SIMP_HEAD_RE = re.compile(
    r"simp(a|_all_arith|_all|_arith|_rw)?([?!]{0,2})"
    r"(?:\s*\((?:[^()]|\([^()]*\))*\)|\s+(?:only\b|[+-][^\W\d][\w.]*))*"
    r"\s*\["
)
# Identifier boundaries follow Lean 4 (`\w` is Unicode-aware; `'`, `!`, `?` continue
# an identifier; a `.` before or after means the match is only part of a longer name).
_IDENT_BEFORE = r"(?<![\w'!?.])"
_IDENT_AFTER = r"(?![\w'!?.])"
# Optional namespace qualification (`Trusted.Sequence.length`,
# `Anneal.Rustc.V2026_06_01.wpMirExecSym`) and optional unfolding-equation suffixes
# (`.eq_def`, `.eq_unfold`, `.eq_<n>`) are part of the flagged symbol; any other
# `.`-suffix (a lemma living in the symbol's namespace) is not.
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
_UNFOLD_LIT_RE = re.compile(r"unfold([ \t]+[^\n;]+)")
_DELTA_LIT_RE = re.compile(r"delta([ \t]+[^\n;]+)")
_UNFOLD_STOP_RE = re.compile(r"\b(?:at|by|with|in|where|using)\b|:=")
_PROFILER_THRESHOLD_RE = re.compile(
    r"set_option\s+trace\.profiler\.threshold\s+(\d+)\b"
)
# Declaration names: dotted Lean 4 identifiers (`MirStepStar.mono`, `get?_set?_ne`)
# or `«guillemet-quoted»` names. Modifiers may sit between `private` and the keyword.
_DECL_NAME = r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*|«[^»\n]*»"
_PRIVATE_LIT_RE = re.compile(
    r"private\s+(?:(?:noncomputable|partial|unsafe|nonrec)\s+)*(theorem|lemma|def)\s+("
    + _DECL_NAME
    + r")"
)
# A line starting in column 0 begins a new top-level command; a line starting with
# `|` begins a pattern-matching equation of the current declaration.
_TOPLEVEL_LINE_RE = re.compile(r"\n(?=\S)")
_EQN_ALT_LINE_RE = re.compile(r"\n[ \t]*\|")
_MATCH_OR_FUN_RE = re.compile(r"(?<![\w'!?.])(?:match|fun|λ)(?![\w'!?])")
_HDR_TOKEN_RE = re.compile(r"[()\[\]{}]|:=|:|(?<![\w'!?.])where(?![\w'!?])")
_RESERVED_TYPE_NAMES = frozenset(("Type", "Prop", "Sort", "Nat", "Bool", "True", "False"))


def _has_simp_candidate(s: str) -> bool:
    return (
        ("Mir." in s and ".body" in s)
        or "Sequence.length" in s
        or "wpMirExecSym" in s
        or ("bitwise" in s and ("bitwiseAndBits" in s or "bitwiseOrBits" in s))
    )


def _is_erase_entry(content: str, start: int) -> bool:
    """True when the lemma-list entry starting at `content[start]` is a simp-set
    erasure `-name`, which removes the declaration from the simp set instead of
    unfolding it."""
    j = start - 1
    while j >= 0 and content[j] in " \t\r\n":
        j -= 1
    if j < 0 or content[j] != "-":
        return False
    j -= 1
    while j >= 0 and content[j] in " \t\r\n":
        j -= 1
    return j < 0 or content[j] == ","


def _active_simp_keywords(stripped: str) -> tuple[list[str], bool, bool]:
    """Scan `stripped` once to determine active candidate keywords plus `(has_mir_body, has_bitwise)`."""
    active_kws: list[str] = []
    if "wpMirExecSym" in stripped:
        active_kws.append("wpMirExecSym")
    if "Sequence.length" in stripped:
        active_kws.append("Sequence.length")
    has_mir_body = ".body" in stripped and "Mir." in stripped
    if has_mir_body:
        active_kws.append(".body")
    has_bitwise = False
    if "bitwise" in stripped:
        if "bitwiseAndBits" in stripped:
            active_kws.append("bitwiseAndBits")
            has_bitwise = True
        if "bitwiseOrBits" in stripped:
            active_kws.append("bitwiseOrBits")
            has_bitwise = True
    return active_kws, has_mir_body, has_bitwise


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


def _candidate_search_windows(
    stripped: str,
    active_kws: list[str] | None = None,
    max_bracket_len: int = 2048,
) -> list[tuple[int, int]]:
    n = len(stripped)
    if n <= 8192:
        return [(0, n)]
    if active_kws is None:
        active_kws, _, _ = _active_simp_keywords(stripped)
    if not active_kws:
        return []
    raw_spans: list[tuple[int, int]] = []
    for kw in active_kws:
        klen = len(kw)
        check_before = kw[0] != "."
        pos = stripped.find(kw, 0)
        while pos != -1:
            # Occurrences inside longer names (`Trusted.Sequence.length_append`,
            # `bitwiseAndBitsFast`, `MySequence.length`) can never be findings; skip
            # them before any bracket work so lemma-dense proofs stay cheap.
            if not _is_symbol_end(stripped, pos + klen) or (
                check_before and pos > 0 and _is_ident_char(stripped[pos - 1])
            ):
                pos = stripped.find(kw, pos + klen)
                continue
            w_start = pos - max_bracket_len if pos > max_bracket_len else 0
            last_open = stripped.rfind("[", w_start, pos)
            if last_open != -1:
                if stripped.find("]", last_open, pos) == -1:
                    # Room for `(config := ...)` / `+opt` / `only` between the
                    # tactic keyword and its `[`.
                    hdr_start = last_open - 256 if last_open > 256 else 0
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


def _iter_simp_brackets(
    stripped: str,
    active_kws: list[str] | None = None,
) -> Iterable[tuple[str, int, int, str]]:
    """Yield `(tactic_kind, open_bracket_idx, close_bracket_idx, bracket_content)` for
    every candidate simp-family lemma list (`dsimp [...]`, `simp only [...]`,
    `simp? (config := ...) [...]`, `simpa [...]`, `simp_all [...]`, ...) in `stripped`;
    `tactic_kind` is the tactic keyword as written (e.g. `dsimp`, `simp_all?`).
    """
    n = len(stripped)
    seen_open: set[int] = set()
    for win_start, win_end in _candidate_search_windows(stripped, active_kws=active_kws):
        for m in _SIMP_HEAD_RE.finditer(stripped, win_start, win_end):
            s_idx = m.start()
            prefix = ""
            if s_idx > 0 and stripped[s_idx - 1] == "d":
                if s_idx > 1 and (_is_ident_char(stripped[s_idx - 2]) or stripped[s_idx - 2] == "."):
                    continue
                prefix = "d"
            elif s_idx > 0 and (_is_ident_char(stripped[s_idx - 1]) or stripped[s_idx - 1] == "."):
                continue
            tactic_kind = prefix + "simp" + (m.group(1) or "") + m.group(2)

            open_idx = m.end() - 1
            if open_idx in seen_open:
                continue
            seen_open.add(open_idx)

            first_close = stripped.find("]", m.end())
            if first_close == -1:
                continue
            first_open = stripped.find("[", m.end(), first_close)
            if first_open == -1:
                yield tactic_kind, open_idx, first_close, stripped[open_idx + 1 : first_close]
                continue
            depth = 1
            i = m.end()
            while i < n and depth > 0:
                ch = stripped[i]
                if ch == "[":
                    depth += 1
                elif ch == "]":
                    depth -= 1
                i += 1
            if depth == 0:
                close_idx = i - 1
                yield tactic_kind, open_idx, close_idx, stripped[open_idx + 1 : close_idx]


def _decl_header_span(stripped: str, start_pos: int) -> tuple[str, int]:
    """Locate the header (binders and `: <type>`) of the declaration whose name ends
    at `start_pos` in comment-stripped text.

    The header ends at the top-level `:=` or `where`, or at the first
    pattern-matching equation line (`| ...` not preceded by a `match` / `fun` in the
    header, so match arms inside a statement stay part of it), and must contain a
    `:`. It never extends past the next column-0 command or 2,500 characters.
    Returns `(header, body_start)` with `body_start` the offset where the body
    begins, or `("", -1)` when no complete header is found.
    """
    n = len(stripped)
    limit = min(n, start_pos + 2500)
    m_top = _TOPLEVEL_LINE_RE.search(stripped, start_pos, limit)
    if m_top is not None:
        limit = m_top.start()
    eqn_end = False
    m_alt = _EQN_ALT_LINE_RE.search(stripped, start_pos, limit)
    if m_alt is not None and _MATCH_OR_FUN_RE.search(stripped, start_pos, m_alt.start()) is None:
        eqn_end = True
        limit = m_alt.start()
    # Fast C `str.find(":=")` + `str.count` delimiter balance check (skips `{ field := val }`
    # structure literals inside binders/types while staying in C).
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

    # Token walk over brackets, `:=`, `:` and `where` only (not every character).
    depth = 0
    colon_pos = -1
    for tm in _HDR_TOKEN_RE.finditer(stripped, start_pos, limit):
        tok = tm.group()
        c = tok[0]
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


def _decl_body_key(raw: str, stripped: str, body_start: int) -> str:
    """Definition body from `body_start` to the next column-0 command, with comments
    removed but string literals kept (`.adt "S"` and `.adt "U"` are different
    bodies) and whitespace runs collapsed; empty when the body position is unknown.
    `stripped` is `strip_lean_comments_and_strings(raw)`, so offsets agree."""
    if body_start < 0 or body_start > len(stripped) or len(raw) != len(stripped):
        return ""
    m = _TOPLEVEL_LINE_RE.search(stripped, body_start)
    end = m.start() if m is not None else len(stripped)
    body = strip_lean_comments_and_strings(raw[body_start:end], keep_strings=True)
    return " ".join(body.split())


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


_BINDER_IDENT_RE = re.compile(r"[^\W\d][\w'!?]*")


def _is_valid_binder_ident(tok: str) -> bool:
    return _BINDER_IDENT_RE.fullmatch(tok) is not None


# `_normalize_signature` is pure; memoizing it lets the before/after scans of one
# edit (and repeated scans in one process) normalize each distinct header once.
_NORM_SIG_CACHE: dict[str, str] = {}


def _normalize_signature(raw_header: str) -> str:
    """Normalize whitespace/punctuation and alpha-rename binder variables for duplicate detection."""
    if not raw_header or ":" not in raw_header:
        return ""
    cached = _NORM_SIG_CACHE.get(raw_header)
    if cached is None:
        if len(_NORM_SIG_CACHE) >= 8192:
            _NORM_SIG_CACHE.clear()
        cached = _NORM_SIG_CACHE[raw_header] = _normalize_signature_uncached(raw_header)
    return cached


def _normalize_signature_uncached(raw_header: str) -> str:
    padded = raw_header
    for ch, repl in _SIG_PAD_CHARS:
        if ch in padded:
            padded = padded.replace(ch, repl)
    padded_tokens = padded.split()
    if not padded_tokens:
        return ""
    if "(" not in raw_header and "{" not in raw_header:
        return " ".join(padded_tokens)
    rename_map: dict[str, str] = {}
    counter = 0
    n = len(raw_header)
    pos = 0
    # Next `(` / `{` at or after `pos`, re-searched only once `pos` passes them, so
    # the binder walk stays linear in the header length.
    p1 = raw_header.find("(")
    p2 = raw_header.find("{")
    while pos < n:
        if p1 != -1 and p1 < pos:
            p1 = raw_header.find("(", pos)
        if p2 != -1 and p2 < pos:
            p2 = raw_header.find("{", pos)
        if p1 == -1 and p2 == -1:
            break
        open_idx = p1 if (p2 == -1 or (p1 != -1 and p1 < p2)) else p2
        close_ch = ")" if raw_header[open_idx] == "(" else "}"
        close_idx = raw_header.find(close_ch, open_idx + 1)
        if close_idx == -1:
            break
        inner = raw_header[open_idx + 1 : close_idx]
        if (
            ":" in inner
            and "(" not in inner
            and ")" not in inner
            and "{" not in inner
            and "}" not in inner
        ):
            lhs = inner.partition(":")[0].strip()
            if lhs:
                tokens = lhs.split()
                if all(_is_valid_binder_ident(t) for t in tokens):
                    for vname in tokens:
                        if vname not in rename_map and vname not in _RESERVED_TYPE_NAMES:
                            rename_map[vname] = f"_v{counter}"
                            counter += 1
            pos = close_idx + 1
        else:
            pos = open_idx + 1
    if not rename_map:
        return " ".join(padded_tokens)
    out_tokens: list[str] = []
    for tok in padded_tokens:
        mapped = rename_map.get(tok)
        if mapped is not None:
            out_tokens.append(mapped)
        elif "." in tok and not tok.startswith("."):
            head, dot, tail = tok.partition(".")
            out_tokens.append(rename_map.get(head, head) + dot + tail)
        else:
            out_tokens.append(tok)
    return " ".join(out_tokens)


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
                raw_header, body_start = _decl_header_span(stripped, m.end())
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
                    )
                )
                pos = stripped.find("private", m.end())
                continue
        pos = stripped.find("private", pos + 7)
    return decls


# Cache sibling private declarations by `(resolved_path, mtime_ns, size)`, directory
# `.lean` listings by `(parent_str, mtime_ns)` and comment-stripped sibling texts (only
# needed to compare definition bodies) so warm in-process checks take <0.05 ms.
_SIBLING_PRIVATE_CACHE: dict[str, tuple[int, int, list[PrivateDecl]]] = {}
_DIR_LEAN_FILES_CACHE: dict[str, tuple[int, list[Path]]] = {}
_FILE_TEXTS_CACHE: dict[str, tuple[int, int, str, str]] = {}

# Each hook invocation is a fresh process, so sibling declarations are persisted per
# directory (`sibling_index_path`) instead of re-reading and re-lexing every sibling
# `.lean` file on every check. Counts stay in the small per-file count cache, which
# keeps at most `COUNT_CACHE_MAX_FILES` entries (least recently checked dropped).
COUNT_CACHE_MAX_FILES = 1024


def sibling_index_path(cache_path: str | Path, directory: str | Path) -> Path:
    """File holding the persisted private-declaration index of `directory`'s `.lean`
    files, next to the count cache `cache_path`."""
    import zlib

    cpath = Path(cache_path)
    tag = zlib.crc32(str(directory).encode("utf-8", "surrogatepass"))
    return cpath.with_name(f"{cpath.name}.siblings-{tag:08x}.json")


def _index_entry(st: os.stat_result, decls: list[PrivateDecl]) -> list[Any]:
    return [
        st.st_mtime_ns,
        st.st_size,
        [
            [d.kind, d.name, d.line, d.body_start, d.ensure_norm_sig(), list(d.sig_fp)]
            for d in decls
        ],
    ]


def _decls_from_index_entry(
    entry: Any, st: os.stat_result, path: Path
) -> list[PrivateDecl] | None:
    """Rebuild the declarations stored for `path`, or `None` when the entry is
    missing, malformed, or recorded for a different `(mtime_ns, size)`."""
    try:
        if entry[0] != st.st_mtime_ns or entry[1] != st.st_size:
            return None
        out: list[PrivateDecl] = []
        for kind, name, line, body_start, norm_sig, fp in entry[2]:
            if kind not in ("theorem", "lemma", "def"):
                return None
            out.append(
                PrivateDecl(
                    kind=kind,
                    name=str(name),
                    norm_sig=str(norm_sig),
                    line=int(line),
                    file=path.name,
                    sig_fp=(int(fp[0]), int(fp[1]), int(fp[2]), int(fp[3])),
                    body_start=int(body_start),
                    path=str(path),
                )
            )
        return out
    except (TypeError, ValueError, IndexError, KeyError):
        return None


def _extract_sibling_private_decls_fast(
    sibling_path: Path, persisted: dict[str, Any] | None = None
) -> list[PrivateDecl]:
    """Private declarations of one sibling file, from the in-process cache, then the
    persisted index (`persisted`, updated in place), then by lexing the file."""
    key = str(sibling_path)
    try:
        st = sibling_path.stat()
    except OSError:
        return []
    cached = _SIBLING_PRIVATE_CACHE.get(key)
    if cached is not None and cached[0] == st.st_mtime_ns and cached[1] == st.st_size:
        decls = cached[2]
        if persisted is not None:
            old = persisted.get(key)
            if not (
                isinstance(old, list)
                and len(old) == 3
                and old[0] == st.st_mtime_ns
                and old[1] == st.st_size
            ):
                persisted[key] = _index_entry(st, decls)
        return decls

    if persisted is not None:
        entry = persisted.get(key)
        restored = _decls_from_index_entry(entry, st, sibling_path) if entry is not None else None
        if restored is not None:
            _SIBLING_PRIVATE_CACHE[key] = (st.st_mtime_ns, st.st_size, restored)
            return restored

    try:
        raw = sibling_path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    decls = []
    if "private" in raw:
        # The same lexer as for the scanned file, so nested comments, strings and
        # attributes before `private` are handled identically (~3 ms per MB).
        stripped = strip_lean_comments_and_strings(raw)
        decls = extract_private_decls(
            stripped, file_label=sibling_path.name, lazy_norm=True, file_path=key
        )
    _SIBLING_PRIVATE_CACHE[key] = (st.st_mtime_ns, st.st_size, decls)
    if persisted is not None:
        persisted[key] = _index_entry(st, decls)
    return decls


def _file_texts(path_str: str) -> tuple[str, str] | None:
    """`(raw, comment_stripped)` texts of `path_str` (cached by `(mtime_ns, size)`)."""
    p = Path(path_str)
    try:
        st = p.stat()
    except OSError:
        return None
    cached = _FILE_TEXTS_CACHE.get(path_str)
    if cached is not None and cached[0] == st.st_mtime_ns and cached[1] == st.st_size:
        return cached[2], cached[3]
    try:
        raw = p.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None
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
    # Forget files that no longer exist (renamed or deleted siblings).
    for key in [k for k in index if not os.path.isfile(k)]:
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
    # with at least one other local or sibling declaration.
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

    # Definition bodies are compared in two steps: a cheap key (counts taken on the
    # comment- and string-blanked body, independent of whitespace layout) rejects
    # almost every pair, and only bodies with equal cheap keys are compared exactly,
    # comments removed but string literals kept and whitespace collapsed.
    quick_keys: dict[int, tuple[int, int, int] | None] = {}
    exact_keys: dict[int, str] = {}

    def body_span(d: PrivateDecl, local: bool) -> tuple[str, str, int, int] | None:
        texts = (raw, stripped) if local else (_file_texts(d.path) if d.path else None)
        if texts is None:
            return None
        r, st = texts
        if d.body_start < 0 or d.body_start > len(st) or len(r) != len(st):
            return None
        m = _TOPLEVEL_LINE_RE.search(st, d.body_start)
        return r, st, d.body_start, (m.start() if m is not None else len(st))

    def quick_key(d: PrivateDecl, local: bool) -> tuple[int, int, int] | None:
        k = id(d)
        if k not in quick_keys:
            key = None
            span = body_span(d, local)
            if span is not None:
                st, b, e = span[1], span[2], span[3]
                visible = e - b - st.count(" ", b, e) - st.count("\n", b, e) - st.count("\t", b, e)
                if visible > 0:
                    key = (visible, st.count("(", b, e), st.count(":", b, e))
            quick_keys[k] = key
        return quick_keys[k]

    def exact_key(d: PrivateDecl, local: bool) -> str:
        k = id(d)
        v = exact_keys.get(k)
        if v is None:
            span = body_span(d, local)
            v = _decl_body_key(span[0], span[1], span[2]) if span is not None else ""
            exact_keys[k] = v
        return v

    def match_in(
        d: PrivateDecl, buckets: dict[tuple[int, int, int], list[PrivateDecl]], local: bool
    ) -> PrivateDecl | None:
        q = quick_key(d, True)
        if q is None:
            return None
        for c in buckets.get(q, ()):
            if exact_key(c, local) == exact_key(d, True):
                return c
        return None

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
    # Sibling definitions of one signature, bucketed by cheap body key on first use
    # (so sibling texts are only re-read for signatures a local definition shares).
    ext_def_buckets: dict[tuple[str, str], dict[tuple[int, int, int], list[PrivateDecl]]] = {}

    def ext_def_bucket(k: tuple[str, str]) -> dict[tuple[int, int, int], list[PrivateDecl]]:
        b = ext_def_buckets.get(k)
        if b is None:
            b = {}
            for c in ext_by_sig.get(k, ()):
                q = quick_key(c, False)
                if q is not None:
                    b.setdefault(q, []).append(c)
            ext_def_buckets[k] = b
        return b

    findings: list[ProofHealthFinding] = []
    seen_names: dict[str, PrivateDecl] = {}
    seen_props: dict[tuple[str, str], PrivateDecl] = {}
    seen_def_buckets: dict[tuple[str, str], dict[tuple[int, int, int], list[PrivateDecl]]] = {}
    for d, k in zip(local_decls, local_keys):
        same = "signature and body" if d.kind == "def" else "signature"
        dup_reason: str | None = None
        if d.name in seen_names:
            prev = seen_names[d.name]
            dup_reason = f"duplicates earlier `private {prev.kind} {prev.name}` on L{prev.line}"
        else:
            prev = None
            if k is not None:
                if k[0] == "prop":
                    prev = seen_props.get(k)
                elif k in seen_def_buckets:
                    prev = match_in(d, seen_def_buckets[k], True)
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
                    else match_in(d, ext_def_bucket(k), False)
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
                q = quick_key(d, True)
                if q is not None:
                    seen_def_buckets.setdefault(k, {}).setdefault(q, []).append(d)

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

    active_kws, has_mir_body, has_bitwise = _active_simp_keywords(stripped)

    # Rules 1, 2, 3 inside `dsimp [...]` / `simp [...]` bracket lists
    if active_kws and "simp" in stripped:
        for tactic_kind, open_idx, close_idx, content in _iter_simp_brackets(
            stripped, active_kws=active_kws
        ):
            if not _has_simp_candidate(content):
                continue
            base_offset = open_idx + 1

            # Rule 1: `dsimp_forbidden_sym`
            # The rule is purely syntactic, as specified: any occurrence inside a
            # `dsimp`/`simp` bracket list counts, whatever the `at` location or the
            # other list entries (no identifier- or location-based exemptions). Only
            # erasures `-name`, which keep the symbol folded, are not occurrences.
            if "wpMirExecSym" in content or "Sequence.length" in content:
                for sm in _FORBIDDEN_SIMP_SYM_RE.finditer(content):
                    if _is_erase_entry(content, sm.start()):
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
                    if _is_erase_entry(content, bm.start()):
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
                    if _is_erase_entry(content, rwm.start()):
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

    # Rules 2 & 3 inside `unfold` / `delta` tactics
    if has_mir_body or has_bitwise:
        tactic_regexes = []
        if "unfold" in stripped:
            tactic_regexes.append(_UNFOLD_LIT_RE)
        if "delta" in stripped:
            tactic_regexes.append(_DELTA_LIT_RE)
        for rx in tactic_regexes:
            for um in rx.finditer(stripped):
                if um.start() > 0 and _is_ident_char(stripped[um.start() - 1]):
                    continue
                arg_span = um.group(1)
                if ".body" not in arg_span and "bitwise" not in arg_span:
                    continue
                stop_m = _UNFOLD_STOP_RE.search(arg_span)
                if stop_m is not None:
                    arg_span = arg_span[: stop_m.start()]
                arg_base = um.start(1)
                for bm in _MIR_BODY_RE.finditer(arg_span):
                    sym = bm.group(1)
                    line = line_of(arg_base + bm.start(1))
                    findings.append(
                        ProofHealthFinding(
                            rule=RULE_DSIMP_MIR_BODY_UNFOLD,
                            line=line,
                            symbol=sym,
                            message=(
                                f"Unfolding `{sym}` via `unfold` substitutes the full CFG basic-block "
                                "table into the proof goal."
                            ),
                            suggestion=(
                                "Pre-project basic blocks into top-level `itemBBk` definitions "
                                "and rewrite with `lookupBlock` lemmas instead of unfolding `.body`."
                            ),
                        )
                    )
                for rwm in _RAW_BITWISE_RE.finditer(arg_span):
                    sym = rwm.group(1)
                    line = line_of(arg_base + rwm.start(1))
                    findings.append(
                        ProofHealthFinding(
                            rule=RULE_RAW_BITWISE_UNFOLD,
                            line=line,
                            symbol=sym,
                            message=(
                                f"Unfolding recursive `{sym}` via `unfold` unrolls bit-by-bit "
                                "`Nat.div` recursion over symbolic naturals."
                            ),
                            suggestion=(
                                f"Do not `unfold {sym}`; use `{sym}Fast` or closed-form "
                                "modular arithmetic lemmas."
                            ),
                        )
                    )

    # Rule 4: `low_profiler_threshold`
    if "profiler.threshold" in stripped:
        for pm in _PROFILER_THRESHOLD_RE.finditer(stripped):
            if pm.start() > 0 and _is_ident_char(stripped[pm.start() - 1]):
                continue
            val = int(pm.group(1))
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


def _save_cache(cache_file: Path, data: dict[str, Any]) -> None:
    """Write the cache through a fresh `O_EXCL` temp file and `os.replace`, so
    concurrent hook processes never read a torn file and a symlink planted at the
    cache path (e.g. in a shared `/tmp`) is replaced rather than written through."""
    tmp_path = f"{cache_file}.{os.getpid()}.tmp"
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


def reconstruct_before_text_from_payload(
    after_text: str,
    payload: dict[str, Any] | None,
) -> str | None:
    """Attempt to reconstruct the pre-edit file text in memory from a PostToolUse
    `edit_file` / `Edit` / `MultiEdit` payload. Returns `None` when the payload does
    not contain reversible diff pairs (e.g. `write_file` / `Write`) or when `Replacement`
    occurs multiple times and cannot be unambiguously inverted without a cache.
    """
    for args in _extract_edit_args_list(payload):
        # Claude MultiEdit: `edits` list of `{old_string/Target, new_string/Replacement}`
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
                if cur.count(new_s) == 1:
                    cur = cur.replace(new_s, old_s, 1)
                else:
                    cur = cur.replace(new_s, old_s)
            if ok:
                return cur

        # Single edit: Jetski `Target`/`Replacement` or Claude `old_string`/`new_string`
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
                # Ambiguous multi-occurrence replacement: return None so caller prefers
                # cached pre-edit counts if available, or falls back to full replacement.
                return None
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
    """True when the payload is a single edit whose replacement is empty."""
    for args in _extract_edit_args_list(payload):
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


def _line_spans_of_insertions(after_text: str, inserted: list[str]) -> list[tuple[int, int]]:
    """1-based inclusive line ranges covered by every occurrence of each inserted
    string in `after_text`."""
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
    the edited line ranges first, then occurrences whose `(symbol, source line)`
    did not exist before the edit, and only as a last resort the last `delta`
    occurrences."""
    chosen = [f for f in rule_findings if any(a <= f.line <= b for a, b in spans)]
    if before_rule_findings is not None and before_lines is not None:
        remaining: dict[tuple[str, str], int] = {}
        for f in before_rule_findings:
            key = (f.symbol, _line_text(before_lines, f.line))
            remaining[key] = remaining.get(key, 0) + 1
        unmatched: list[ProofHealthFinding] = []
        for f in rule_findings:
            key = (f.symbol, _line_text(after_lines, f.line))
            if remaining.get(key, 0) > 0:
                remaining[key] -= 1
            else:
                unmatched.append(f)
        if chosen and len(chosen) > delta:
            narrowed = [f for f in chosen if f in unmatched]
            if narrowed:
                chosen = narrowed
        if len(chosen) < delta:
            for f in unmatched:
                if f not in chosen:
                    chosen.append(f)
    if not chosen:
        chosen = rule_findings[-delta:] if delta > 0 else []
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
    the edit payload in memory, or from the edit shape itself (a `write_file` that
    creates a new file starts from an empty file; a `write_file` with `Append`
    starts from the text before the appended content). Its counts are taken from the
    persisted per-file cache when the cached entry was recorded for exactly that
    text (same length and CRC, same sibling declarations), which saves the second
    scan on consecutive edits; otherwise the text is scanned. Without a pre-edit
    text, the cached counts are the baseline. When neither is available (an
    overwrite or a deletion of a file never seen before), the current counts become
    the baseline and no increase is claimed.
    """
    # Absolute (not symlink-resolved) path, so sibling-index keys do not depend on the
    # working directory of the hook process.
    path = Path(os.path.abspath(target_file))
    try:
        resolved_key = str(path.resolve())
    except OSError:
        resolved_key = str(path)

    if after_text is None:
        after_text = path.read_text(encoding="utf-8", errors="replace")

    cpath = Path(cache_path) if cache_path is not None else default_cache_path()
    cache = _load_cache(cpath)

    # Sibling declarations only matter when the edited file has private declarations
    # after the edit (a count can only rise if they exist in `after_text`).
    sibling_decls: list[PrivateDecl] = []
    if scan_siblings and "private" in after_text:
        index_file = sibling_index_path(cpath, path.parent)
        sibling_index = _load_sibling_index(index_file)
        before_ids = {k: id(v) for k, v in sibling_index.items()}
        sibling_decls = _collect_sibling_private_decls(path, persisted=sibling_index)
        if {k: id(v) for k, v in sibling_index.items()} != before_ids:
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
    if not isinstance(cached_entry, dict):
        cached_entry = None
    sib_sig = _text_crc(
        "\n".join(f"{d.file}:{d.line}:{d.kind}:{d.name}" for d in sibling_decls)
    )

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
            spans = _line_spans_of_insertions(after_text, _replacement_strings(payload))
    elif cached_entry is not None:
        before_counts = {rule: _safe_int(cached_entry.get(rule, 0), 0) for rule in ALL_RULES}
        spans = _line_spans_of_insertions(after_text, _replacement_strings(payload))
    elif _is_pure_deletion(payload):
        # Deleting text cannot add an occurrence; without a cached baseline the
        # current counts become the baseline.
        before_counts = dict(after_counts)
    else:
        # A Jetski `edit_file` replaces every occurrence of `Target`, so an
        # ambiguous replacement is inverted by reverting all occurrences.
        ambiguous_before: str | None = None
        for args in _extract_edit_args_list(payload):
            old_s = args.get("Target", args.get("old_string"))
            new_s = args.get("Replacement", args.get("new_string"))
            if isinstance(old_s, str) and isinstance(new_s, str) and new_s and new_s in after_text:
                ambiguous_before = after_text.replace(new_s, old_s)
                break
        if ambiguous_before is not None:
            before_findings = _scan(ambiguous_before)
            before_counts = count_findings_by_rule(before_findings)
            before_text = ambiguous_before
            spans = _line_spans_of_insertions(after_text, _replacement_strings(payload))
        else:
            # Unknown pre-edit state (e.g. overwriting an unseen file): record the
            # baseline without claiming any increase.
            before_counts = dict(after_counts)

    entry: dict[str, int] = dict(after_counts)
    entry["_len"] = len(after_text)
    entry["_crc"] = _text_crc(after_text)
    entry["_sib"] = sib_sig
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


def _parse_iso_ts(ts: Any) -> float | None:
    if isinstance(ts, (int, float)):
        return float(ts)
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


def _extract_duration_ms(obj: dict[str, Any]) -> float | None:
    for key in ("duration_ms", "latency_ms", "elapsed_ms", "time_ms"):
        val = obj.get(key)
        if isinstance(val, (int, float)) and val >= 0:
            return float(val)
    for key in ("duration_s", "latency_s", "elapsed_s"):
        val = obj.get(key)
        if isinstance(val, (int, float)) and val >= 0:
            return float(val) * 1000.0
    start_ts = _parse_iso_ts(
        obj.get("started_at") or obj.get("created_at") or obj.get("start_time")
    )
    end_ts = _parse_iso_ts(
        obj.get("completed_at") or obj.get("finished_at") or obj.get("end_time")
    )
    if start_ts is not None and end_ts is not None and end_ts >= start_ts:
        return (end_ts - start_ts) * 1000.0
    content = obj.get("content") or obj.get("output")
    if isinstance(content, str):
        m = _CREATED_COMPLETED_RE.search(content)
        if m:
            t0 = _parse_iso_ts(m.group(1))
            t1 = _parse_iso_ts(m.group(2))
            if t0 is not None and t1 is not None and t1 >= t0:
                return (t1 - t0) * 1000.0
    return None


def _load_transcript_items(
    source: str | Path | Iterable[dict[str, Any]],
) -> list[dict[str, Any]]:
    if isinstance(source, (str, Path)):
        path = Path(source)
        if path.is_file():
            raw = path.read_text(encoding="utf-8", errors="replace")
        elif isinstance(source, str) and ("\n" in source or source.strip().startswith("{")):
            raw = source
        else:
            return []
        items: list[dict[str, Any]] = []
        for line in raw.splitlines():
            s = line.strip()
            if not s:
                continue
            try:
                parsed = json.loads(s)
                if isinstance(parsed, dict):
                    items.append(parsed)
            except Exception:
                continue
        return items
    return [item for item in source if isinstance(item, dict)]


def _batch_key(obj: dict[str, Any], fallback: str) -> Any:
    for key in ("batch_id", "step_index", "turn_id"):
        val = obj.get(key)
        if val is not None:
            return val
    return fallback


def _safe_int(val: Any, default: int = 1) -> int:
    try:
        return int(val)
    except (TypeError, ValueError):
        return default


def _tool_name(obj: dict[str, Any]) -> str | None:
    name = obj.get("tool") or obj.get("name") or obj.get("tool_name")
    return str(name) if name is not None else None


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
      `Created At: ... / Completed At: ...` timestamps for each call. These
      timestamps have one-second resolution, so such durations are whole seconds
      (a sub-second call that straddles a second boundary reads as 1000 ms).
    Entries without usable timings are skipped without raising.
    """
    import statistics

    items = _load_transcript_items(transcript_or_events)
    allowed_tools: set[str] | None = None
    if isinstance(tool_filter, str):
        allowed_tools = {tool_filter}
    elif tool_filter is not None:
        allowed_tools = set(tool_filter)

    raw_batches: dict[Any, list[dict[str, Any]]] = {}
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
                "batch_size": batch_size,
                "explicit_batched_long": bool(
                    src.get("batched_with_long_call")
                    or src.get("classification") == "batched_with_long_call"
                ),
                "is_long_call": bool(src.get("is_long_call", False)),
            }
        )

    for item in items:
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

        tname = _tool_name(item)
        dur = _extract_duration_ms(item)
        if dur is None:
            continue
        if tname is None:
            # Jetski result step: attribute it to the next pending call in order.
            if pending and item.get("type") not in ("SYSTEM_MESSAGE", "USER_INPUT"):
                ptool, pbatch, psize = pending.pop(0)
                _record(ptool, dur, pbatch, item, psize)
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
        has_long = any(
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
