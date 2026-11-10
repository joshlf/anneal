#!/usr/bin/env python3
"""Fast (<5 ms) structural proof-health linter and transcript latency telemetry for Anneal Lean 4 proofs.

Detects five structural kernel-scaling anti-patterns on Lean 4 files with zero false
positives on comments, nested block comments (`/- ... -/`), docstrings, or string literals:
1. `dsimp_forbidden_sym`: `wpMirExecSym` or `Trusted.Sequence.length` / `Sequence.length`
   inside `dsimp` / `simp` bracket lists.
2. `dsimp_mir_body_unfold`: `Mir.<...>.body` unfolded inside `dsimp`, `simp`, or `unfold`.
3. `raw_bitwise_unfold`: raw recursive `bitwiseAndBits` or `bitwiseOrBits` unfolded inside
   `dsimp`, `simp`, or `unfold` (excluding `*Fast` wrappers and closed-form mask lemmas).
4. `low_profiler_threshold`: `set_option trace.profiler.threshold <N>` with `<N> < 50`.
5. `duplicate_private_lemma`: duplicate `private theorem` / `private lemma` / `private def`
   declaration name or normalized type signature within the same file or across sibling
   `.lean` files in the same directory.

Also provides delta-only post-edit checking (`check_post_edit_proof_health`) for
`tools/anneal-lsp/hooks/post_tool_use.py` and unbatched tool-call latency telemetry
(`compute_unbatched_tool_latencies`).
"""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

from bisect import bisect_right
from dataclasses import asdict, dataclass
from datetime import datetime
import json
import os
from pathlib import Path
import re
import statistics
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


@dataclass(frozen=True)
class ProofHealthFinding:
    rule: str
    line: int
    message: str
    suggestion: str
    symbol: str = ""

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class PrivateDecl:
    kind: str
    name: str
    norm_sig: str
    line: int
    file: str
    raw_header: str = ""
    sig_fp: tuple[int, int, int, int] = (0, 0, 0, 0)

    def ensure_norm_sig(self) -> str:
        if not self.norm_sig and self.raw_header:
            self.norm_sig = _normalize_signature(self.raw_header)
        return self.norm_sig


_LINE_COMMENT_BATCH_RE = re.compile(r"--[^\n]*")


def _is_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch == "_" or ch == "'"


def strip_lean_comments_and_strings(text: str) -> str:
    """Replace Lean 4 `--` line comments, nested `/- ... -/` block comments, and
    string/char literals with spaces while preserving every `\\n` line number.

    Uses cached single-pass C `str.find` (`fastsearch` SIMD) plus batch C `re.sub`
    across `--`-only spans so 300-400 KB Lean 4 files strip in ~0.3 ms.
    """
    n = len(text)
    if n == 0:
        return ""
    out: list[str] = []
    pos = 0
    i_blk = text.find("/-", 0)
    i_lin = text.find("--", 0)
    i_str = text.find('"', 0)
    while pos < n:
        if i_blk != -1 and i_blk < pos:
            i_blk = text.find("/-", pos)
        if i_lin != -1 and i_lin < pos:
            i_lin = text.find("--", pos)
        if i_str != -1 and i_str < pos:
            i_str = text.find('"', pos)

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
            out.append(text[pos:])
            break

        if kind == 2:
            # `--` line comment up to `\n`
            if nxt > pos:
                out.append(text[pos:nxt])
            nl = text.find("\n", nxt + 2)
            if nl == -1:
                out.append(" ")
                break
            out.append(" \n")
            pos = nl + 1
            continue

        if nxt > pos:
            out.append(text[pos:nxt])
        if kind == 1:
            # `/- ... -/` block comment with arbitrary nesting depth
            depth = 1
            cur = nxt + 2
            while depth > 0 and cur < n:
                c = text.find("-/", cur)
                if c == -1:
                    cur = n
                    break
                o = text.find("/-", cur, c)
                if o != -1:
                    depth += 1
                    cur = o + 2
                else:
                    depth -= 1
                    cur = c + 2
            nl_cnt = text.count("\n", nxt, cur)
            out.append(" " if nl_cnt == 0 else (" " + "\n" * nl_cnt + " "))
            pos = cur
        else:
            # Guard against quote character literals `'"'` and `'\"'`
            if (
                nxt > 0
                and nxt + 1 < n
                and text[nxt + 1] == "'"
                and (
                    text[nxt - 1] == "'"
                    or (nxt >= 2 and text[nxt - 2 : nxt] == "'\\")
                )
            ):
                out.append(" ")
                pos = nxt + 1
                i_str = text.find('"', pos)
                continue
            cur = nxt + 1
            while cur < n:
                q = text.find('"', cur)
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
            nl_cnt = text.count("\n", nxt, cur)
            out.append(" " if nl_cnt == 0 else (" " + "\n" * nl_cnt + " "))
            pos = cur
    return "".join(out)


def _build_newline_offsets(text: str) -> list[int]:
    offsets: list[int] = []
    idx = text.find("\n")
    while idx != -1:
        offsets.append(idx)
        idx = text.find("\n", idx + 1)
    return offsets


def _offset_to_line(text_or_offsets: str | list[int], offset: int) -> int:
    if isinstance(text_or_offsets, str):
        return text_or_offsets.count("\n", 0, offset) + 1
    return bisect_right(text_or_offsets, offset) + 1


# Tactic and pattern regexes on stripped Lean 4 text.
# Leading literal prefixes (`simp`, `unfold`, `delta`, `set_option`, `private`)
# enable CPython `sre` SIMD `memchr` fast-forwarding instead of char-by-char `\b` scans.
_SIMP_LIT_RE = re.compile(r"simp\??(?:\s+only)?\s*\[")
_FORBIDDEN_SIMP_SYM_RE = re.compile(
    r"(?<![A-Za-z0-9_'.])(wpMirExecSym|(?:Trusted\.)?Sequence\.length)(?![A-Za-z0-9_'.])"
)
_MIR_BODY_RE = re.compile(
    r"(?<![A-Za-z0-9_'.])(Mir(?:\.[A-Za-z0-9_']+)+\.body)(?![A-Za-z0-9_'.])"
)
_RAW_BITWISE_RE = re.compile(
    r"(?<![A-Za-z0-9_'])(?:[A-Za-z0-9_']+\.)?(bitwise(?:And|Or)Bits)(?![A-Za-z0-9_'])"
)
_UNFOLD_LIT_RE = re.compile(r"unfold([ \t]+[^\n;]+)")
_DELTA_LIT_RE = re.compile(r"delta([ \t]+[^\n;]+)")
_UNFOLD_STOP_RE = re.compile(r"\b(?:at|by|with|in|where|using)\b|:=")
_PROFILER_THRESHOLD_RE = re.compile(
    r"set_option\s+trace\.profiler\.threshold\s+(\d+)\b"
)
_PRIVATE_LIT_RE = re.compile(
    r"private\s+(theorem|lemma|def)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)
_TOKEN_SPLIT_RE = re.compile(r"(\.?[A-Za-z_][A-Za-z0-9_']*)")
_AT_CLAUSE_AFTER_BRACKET_RE = re.compile(r"^\s*at\b")
_LOCAL_TBYTES_RE = re.compile(r"\btBytes\b")
_RESERVED_TYPE_NAMES = frozenset(("Type", "Prop", "Sort", "Nat", "Bool", "True", "False"))


def _has_simp_candidate(s: str) -> bool:
    return (
        ("Mir." in s and ".body" in s)
        or "Sequence.length" in s
        or "wpMirExecSym" in s
        or ("bitwise" in s and ("bitwiseAndBits" in s or "bitwiseOrBits" in s))
    )


def _active_simp_keywords(stripped: str) -> tuple[list[str], bool, bool]:
    """Scan `stripped` once to determine active candidate keywords plus `(has_mir_body, has_bitwise)`."""
    active_kws: list[str] = []
    if "wpMirExecSym" in stripped:
        active_kws.append("wpMirExecSym")
    if "Sequence.length" in stripped:
        active_kws.append("Sequence.length")
    has_mir_body = "Mir." in stripped and ".body" in stripped
    if has_mir_body:
        active_kws.append("Mir.")
    has_bitwise = False
    if "bitwise" in stripped:
        if "bitwiseAndBits" in stripped:
            active_kws.append("bitwiseAndBits")
            has_bitwise = True
        if "bitwiseOrBits" in stripped:
            active_kws.append("bitwiseOrBits")
            has_bitwise = True
    return active_kws, has_mir_body, has_bitwise


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
        pos = stripped.find(kw, 0)
        while pos != -1:
            w_start = pos - max_bracket_len if pos > max_bracket_len else 0
            last_open = stripped.rfind("[", w_start, pos)
            if last_open != -1:
                if stripped.find("]", last_open, pos) == -1:
                    hdr_start = last_open - 48 if last_open > 48 else 0
                    if "simp" in stripped[hdr_start:last_open]:
                        raw_spans.append((hdr_start, last_open + 1))
                elif "simp" in stripped[w_start:pos] and (
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
    every candidate `dsimp [...]` / `simp [...]` invocation in `stripped`.
    """
    n = len(stripped)
    seen_open: set[int] = set()
    for win_start, win_end in _candidate_search_windows(stripped, active_kws=active_kws):
        for m in _SIMP_LIT_RE.finditer(stripped, win_start, win_end):
            s_idx = m.start()
            if s_idx > 0 and stripped[s_idx - 1] == "d":
                if s_idx > 1 and _is_ident_char(stripped[s_idx - 2]):
                    continue
                tactic_kind = "dsimp"
            else:
                if s_idx > 0 and _is_ident_char(stripped[s_idx - 1]):
                    continue
                tactic_kind = "simp"

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


def _extract_decl_header_and_type(stripped: str, start_pos: int) -> str:
    """Extract the declaration binders and `: <type>` header up to top-level `:=` or `where`."""
    n = len(stripped)
    limit = min(n, start_pos + 2500)
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
            return candidate if ":" in candidate else ""
        search_pos = colon_eq + 2

    paren_depth = 0
    brace_depth = 0
    bracket_depth = 0
    colon_pos = -1
    i = start_pos
    while i < limit:
        ch = stripped[i]
        if ch == "(":
            paren_depth += 1
        elif ch == ")":
            if paren_depth > 0:
                paren_depth -= 1
        elif ch == "{":
            brace_depth += 1
        elif ch == "}":
            if brace_depth > 0:
                brace_depth -= 1
        elif ch == "[":
            bracket_depth += 1
        elif ch == "]":
            if bracket_depth > 0:
                bracket_depth -= 1
        elif paren_depth == 0 and brace_depth == 0 and bracket_depth == 0:
            if ch == ":" and i + 1 < limit and stripped[i + 1] == "=":
                header = stripped[start_pos:i]
                return header if colon_pos != -1 else ""
            if ch == ":" and (i + 1 >= limit or stripped[i + 1] != "="):
                if colon_pos == -1:
                    colon_pos = i
            if (
                ch == "w"
                and stripped.startswith("where", i)
                and (i == start_pos or not _is_ident_char(stripped[i - 1]))
                and (i + 5 >= limit or not _is_ident_char(stripped[i + 5]))
            ):
                header = stripped[start_pos:i]
                return header if colon_pos != -1 else ""
        i += 1
    return ""


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


def _is_valid_binder_ident(tok: str) -> bool:
    if not tok or not (tok[0].isalpha() or tok[0] == "_"):
        return False
    return all(_is_ident_char(c) for c in tok)


def _normalize_signature(raw_header: str) -> str:
    """Normalize whitespace/punctuation and alpha-rename binder variables for duplicate detection."""
    if not raw_header or ":" not in raw_header:
        return ""
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
    while pos < n:
        p1 = raw_header.find("(", pos)
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
) -> list[PrivateDecl]:
    pos = stripped.find("private", 0)
    if pos == -1:
        return []
    decls: list[PrivateDecl] = []
    prev_pos = 0
    cur_line = 1
    while pos != -1:
        if pos == 0 or not _is_ident_char(stripped[pos - 1]):
            m = _PRIVATE_LIT_RE.match(stripped, pos)
            if m is not None:
                kind = m.group(1)
                name = m.group(2)
                if newline_offsets is not None:
                    line = _offset_to_line(newline_offsets, pos)
                else:
                    cur_line += stripped.count("\n", prev_pos, pos)
                    prev_pos = pos
                    line = cur_line
                raw_header = _extract_decl_header_and_type(stripped, m.end())
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
                    )
                )
                pos = stripped.find("private", m.end())
                continue
        pos = stripped.find("private", pos + 7)
    return decls


# Cache sibling private declarations by `(resolved_path, mtime_ns, size)` and directory
# `.lean` listings by `(parent_str, mtime_ns)` so warm checks take <0.05 ms.
_SIBLING_PRIVATE_CACHE: dict[str, tuple[int, int, list[PrivateDecl]]] = {}
_DIR_LEAN_FILES_CACHE: dict[str, tuple[int, list[Path]]] = {}


def _extract_sibling_private_decls_fast(sibling_path: Path) -> list[PrivateDecl]:
    key = str(sibling_path)
    try:
        st = sibling_path.stat()
    except OSError:
        return []
    cached = _SIBLING_PRIVATE_CACHE.get(key)
    if cached is not None and cached[0] == st.st_mtime_ns and cached[1] == st.st_size:
        return cached[2]

    try:
        raw = sibling_path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []

    if "private" not in raw:
        _SIBLING_PRIVATE_CACHE[key] = (st.st_mtime_ns, st.st_size, [])
        return []

    # If the file is small (<16 KB), strip comments/strings across the whole file;
    # for larger files, scan literal `private` anchors and strip only the 2,500-char
    # header slices so even 1.5 MB sibling files scan in <1 ms.
    if len(raw) <= 16384:
        stripped = strip_lean_comments_and_strings(raw)
        decls = extract_private_decls(stripped, file_label=sibling_path.name, lazy_norm=True)
    else:
        decls = []
        for m in _PRIVATE_LIT_RE.finditer(raw):
            pos = m.start()
            line_start = raw.rfind("\n", 0, pos) + 1
            if raw[line_start:pos].strip():
                continue
            # Verify the match is not inside an open `/- ... -/` block comment
            last_open = raw.rfind("/-", 0, pos)
            if last_open != -1 and raw.rfind("-/", last_open, pos) == -1:
                continue
            kind = m.group(1)
            name = m.group(2)
            slice_start = m.end()
            chunk = strip_lean_comments_and_strings(raw[slice_start : slice_start + 2500])
            raw_header = _extract_decl_header_and_type(chunk, 0)
            sig_fp = _header_fingerprint(raw_header)
            line = raw.count("\n", 0, pos) + 1
            decls.append(
                PrivateDecl(
                    kind=kind,
                    name=name,
                    norm_sig="",
                    line=line,
                    file=sibling_path.name,
                    raw_header=raw_header,
                    sig_fp=sig_fp,
                )
            )
    _SIBLING_PRIVATE_CACHE[key] = (st.st_mtime_ns, st.st_size, decls)
    return decls


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


def _collect_sibling_private_decls(file_path: Path, max_siblings: int = 40) -> list[PrivateDecl]:
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
        out.extend(_extract_sibling_private_decls_fast(entry))
    return out


def scan_lean_text(
    text: str,
    *,
    file_path: str | Path | None = None,
    scan_siblings: bool = True,
    sibling_decls: list[PrivateDecl] | None = None,
) -> list[ProofHealthFinding]:
    """Scan Lean 4 source `text` and return all structural proof-health findings."""
    stripped = strip_lean_comments_and_strings(text)
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
            if "wpMirExecSym" in content or "Sequence.length" in content:
                trailing = stripped[close_idx + 1 : close_idx + 32]
                has_at_clause = bool(_AT_CLAUSE_AFTER_BRACKET_RE.match(trailing))
                has_local_tbytes = "tBytes" in content and bool(_LOCAL_TBYTES_RE.search(content))
                for sm in _FORBIDDEN_SIMP_SYM_RE.finditer(content):
                    sym = sm.group(1)
                    # In `simp [...] at h` or `simp [tBytes, Trusted.Sequence.length, hLen]`,
                    # propositional `simp` is discharging a pure list-length hypothesis rather
                    # than unfolding `Sequence.length` across an active MIR goal.
                    if (
                        tactic_kind == "simp"
                        and sym != "wpMirExecSym"
                        and (has_at_clause or has_local_tbytes)
                    ):
                        continue
                    line = _offset_to_line(stripped, base_offset + sm.start(1))
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
                    sym = bm.group(1)
                    line = _offset_to_line(stripped, base_offset + bm.start(1))
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
                    sym = rwm.group(1)
                    line = _offset_to_line(stripped, base_offset + rwm.start(1))
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
                    line = _offset_to_line(stripped, arg_base + bm.start(1))
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
                    line = _offset_to_line(stripped, arg_base + rwm.start(1))
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
                line = _offset_to_line(stripped, pm.start())
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
    )
    if local_decls:
        ext_decls: list[PrivateDecl] = []
        if sibling_decls is not None:
            ext_decls = list(sibling_decls)
        elif scan_siblings and file_path is not None:
            ext_decls = _collect_sibling_private_decls(Path(file_path))

        # Only run full alpha-renaming signature normalization on declarations whose
        # 4-tuple structural fingerprint `(colons, parens, braces, equals)` collides
        # with at least one other local or sibling declaration.
        fp_counts: dict[tuple[int, int, int, int], int] = {}
        for d in ext_decls:
            if d.sig_fp != (0, 0, 0, 0):
                fp_counts[d.sig_fp] = fp_counts.get(d.sig_fp, 0) + 1
            elif d.norm_sig:
                fp_counts[(-1, -1, -1, -1)] = 2
        for d in local_decls:
            if d.sig_fp != (0, 0, 0, 0):
                fp_counts[d.sig_fp] = fp_counts.get(d.sig_fp, 0) + 1
            elif d.norm_sig:
                fp_counts[(-1, -1, -1, -1)] = 2

        has_legacy_decls = (-1, -1, -1, -1) in fp_counts
        ext_by_name: dict[str, PrivateDecl] = {}
        ext_by_sig: dict[str, PrivateDecl] = {}
        for d in ext_decls:
            ext_by_name.setdefault(d.name, d)
            if has_legacy_decls or fp_counts.get(d.sig_fp, 0) >= 2:
                ns = d.ensure_norm_sig()
                if ns:
                    ext_by_sig.setdefault(ns, d)

        seen_names: dict[str, PrivateDecl] = {}
        seen_sigs: dict[str, PrivateDecl] = {}
        for d in local_decls:
            ns = (
                d.ensure_norm_sig()
                if (has_legacy_decls or fp_counts.get(d.sig_fp, 0) >= 2)
                else ""
            )
            dup_reason: str | None = None
            if d.name in seen_names:
                prev = seen_names[d.name]
                dup_reason = f"duplicates earlier `private {prev.kind} {prev.name}` on L{prev.line}"
            elif ns and ns in seen_sigs:
                prev = seen_sigs[ns]
                dup_reason = (
                    f"has the same normalized signature as `private {prev.kind} {prev.name}` "
                    f"on L{prev.line}"
                )
            elif d.name in ext_by_name:
                sib = ext_by_name[d.name]
                dup_reason = (
                    f"duplicates `private {sib.kind} {sib.name}` in sibling file "
                    f"`{sib.file}` (L{sib.line})"
                )
            elif ns and ns in ext_by_sig:
                sib = ext_by_sig[ns]
                dup_reason = (
                    f"has the same normalized signature as `private {sib.kind} {sib.name}` "
                    f"in sibling file `{sib.file}` (L{sib.line})"
                )

            seen_names.setdefault(d.name, d)
            if ns:
                seen_sigs.setdefault(ns, d)

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

    findings.sort(key=lambda f: (f.line, f.rule, f.symbol))
    return findings


def scan_lean_file(
    file_path: str | Path,
    *,
    scan_siblings: bool = True,
) -> list[ProofHealthFinding]:
    path = Path(file_path)
    text = path.read_text(encoding="utf-8", errors="replace")
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


def _load_cache(cache_file: Path) -> dict[str, dict[str, int]]:
    try:
        if cache_file.is_file():
            data = json.loads(cache_file.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                return data
    except Exception:
        pass
    return {}


def _save_cache(cache_file: Path, data: dict[str, dict[str, int]]) -> None:
    try:
        cache_file.parent.mkdir(parents=True, exist_ok=True)
        cache_file.write_text(json.dumps(data, sort_keys=True), encoding="utf-8")
    except Exception:
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


def evaluate_post_edit_proof_health(
    target_file: str | Path,
    payload: dict[str, Any] | None = None,
    *,
    after_text: str | None = None,
    before_text: str | None = None,
    cache_path: str | Path | None = None,
    scan_siblings: bool = True,
) -> dict[str, Any]:
    """Compute delta-only proof-health diagnostics for `target_file` after an edit."""
    path = Path(target_file)
    try:
        resolved_key = str(path.resolve())
    except OSError:
        resolved_key = str(path)

    if after_text is None:
        after_text = path.read_text(encoding="utf-8", errors="replace")

    cpath = Path(cache_path) if cache_path is not None else default_cache_path()
    cache = _load_cache(cpath)

    sibling_decls = _collect_sibling_private_decls(path) if scan_siblings else []
    after_findings = scan_lean_text(
        after_text,
        file_path=path,
        scan_siblings=scan_siblings,
        sibling_decls=sibling_decls,
    )
    after_counts = count_findings_by_rule(after_findings)

    before_findings: list[ProofHealthFinding] | None = None
    if before_text is None and payload is not None:
        before_text = reconstruct_before_text_from_payload(after_text, payload)

    if before_text is not None:
        before_findings = scan_lean_text(
            before_text,
            file_path=path,
            scan_siblings=scan_siblings,
            sibling_decls=sibling_decls,
        )
        before_counts = count_findings_by_rule(before_findings)
    elif resolved_key in cache and isinstance(cache[resolved_key], dict):
        cached_counts = cache[resolved_key]
        before_counts = {rule: int(cached_counts.get(rule, 0)) for rule in ALL_RULES}
    else:
        # Check if an ambiguous multi-occurrence `Target`/`Replacement` can be inverted
        ambiguous_before: str | None = None
        for args in _extract_edit_args_list(payload):
            old_s = args.get("Target", args.get("old_string"))
            new_s = args.get("Replacement", args.get("new_string"))
            if isinstance(old_s, str) and isinstance(new_s, str) and new_s and new_s in after_text:
                ambiguous_before = after_text.replace(new_s, old_s)
                break
        if ambiguous_before is not None:
            before_findings = scan_lean_text(
                ambiguous_before,
                file_path=path,
                scan_siblings=scan_siblings,
                sibling_decls=sibling_decls,
            )
            before_counts = count_findings_by_rule(before_findings)
        else:
            before_counts = {rule: 0 for rule in ALL_RULES}

    cache[resolved_key] = after_counts
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

    before_set = (
        {(f.rule, f.symbol, f.message) for f in before_findings}
        if before_findings is not None
        else set()
    )
    new_findings: list[ProofHealthFinding] = []
    lines_by_rule: dict[str, list[ProofHealthFinding]] = {r: [] for r in increased_rules}
    for f in after_findings:
        if f.rule not in lines_by_rule:
            continue
        if (f.rule, f.symbol, f.message) not in before_set:
            lines_by_rule[f.rule].append(f)
            new_findings.append(f)

    header_parts = [f"{r} (+{deltas[r]})" for r in increased_rules]
    lines: list[str] = [
        f"[Anneal Proof Health] New proof-scaling anti-pattern(s) introduced in `{path.name}`: "
        + ", ".join(header_parts)
    ]
    for rule in increased_rules:
        candidates = lines_by_rule[rule] or [f for f in after_findings if f.rule == rule]
        # Report the newly introduced occurrences (up to delta[rule] latest occurrences)
        shown = candidates[-deltas[rule] :] if deltas[rule] > 0 else candidates
        line_tags = ", ".join(f"L{f.line}" for f in shown)
        sample = shown[0]
        lines.append(
            f"- `{rule}` (+{deltas[rule]} at {line_tags}): {sample.message} "
            f"Fix: {sample.suggestion}"
        )

    feedback = "\n".join(lines)
    return {
        "feedback": feedback,
        "deltas": deltas,
        "before_counts": before_counts,
        "after_counts": after_counts,
        "new_findings": new_findings or [f for f in after_findings if f.rule in increased_rules],
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
    """
    items = _load_transcript_items(transcript_or_events)
    allowed_tools: set[str] | None = None
    if isinstance(tool_filter, str):
        allowed_tools = {tool_filter}
    elif tool_filter is not None:
        allowed_tools = set(tool_filter)

    raw_batches: dict[Any, list[dict[str, Any]]] = {}
    auto_batch_seq = 0

    for item in items:
        # Case 1: Step object containing a `tool_calls` array
        tc_list = item.get("tool_calls")
        if isinstance(tc_list, list) and tc_list:
            batch_key = (
                item.get("batch_id")
                or item.get("step_index")
                or item.get("turn_id")
                or f"_step_{auto_batch_seq}"
            )
            auto_batch_seq += 1
            step_dur = _extract_duration_ms(item)
            for tc in tc_list:
                if not isinstance(tc, dict):
                    continue
                tname = str(
                    tc.get("tool") or tc.get("name") or tc.get("tool_name") or "unknown"
                )
                dur = _extract_duration_ms(tc)
                if dur is None:
                    dur = step_dur
                if dur is None:
                    continue
                rec = {
                    "tool": tname,
                    "duration_ms": float(dur),
                    "batch_id": batch_key,
                    "explicit_batched_long": bool(
                        tc.get("batched_with_long_call")
                        or tc.get("classification") == "batched_with_long_call"
                    ),
                    "is_long_call": bool(tc.get("is_long_call", False)),
                }
                raw_batches.setdefault(batch_key, []).append(rec)
            continue

        # Case 2: Direct tool-call latency event dict
        tname_raw = item.get("tool") or item.get("tool_name") or item.get("name")
        dur = _extract_duration_ms(item)
        if tname_raw is not None and dur is not None:
            batch_key = item.get("batch_id")
            if batch_key is None:
                batch_key = item.get("step_index")
            if batch_key is None:
                batch_key = item.get("turn_id")
            if batch_key is None:
                batch_key = f"_single_{auto_batch_seq}"
                auto_batch_seq += 1
            rec = {
                "tool": str(tname_raw),
                "duration_ms": float(dur),
                "batch_id": batch_key,
                "batch_size": int(item.get("batch_size", 1)),
                "explicit_batched_long": bool(
                    item.get("batched_with_long_call")
                    or item.get("classification") == "batched_with_long_call"
                ),
                "is_long_call": bool(item.get("is_long_call", False)),
            }
            raw_batches.setdefault(batch_key, []).append(rec)

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
