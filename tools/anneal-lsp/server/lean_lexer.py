#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared single-pass Lean 4 lexical and scope scanner (standard library only).

One module owns the lexical facts that every structural Lean tool in this repository needs,
so the delimiter state machine exists once instead of once per tool:

* `strip_comments_and_strings_preserving_offsets` / `scan_lean_source`: blank comments and
  string literals character for character. The result has exactly the length of the input
  and a `\\n` exactly where the input has one, so every offset and line number of the
  blanked text is an offset and line number of the source.
* `match_balanced_attribute` / `scan_balanced_attributes`: `@[...]` attribute spans with
  nested `[]` / `()` / `{}`.
* `NamespaceTracker`: `namespace` / `section` / `mutual` / `end` scopes (including
  single-command `namespace Foo in <cmd>` / `section ... in <cmd>` prefixes) with an
  `O(log K)` `namespace_at(offset)` (`K` scope transitions).
* `is_ident_start`, `is_ident_char`, `blank_preserving_newlines`, `LineCounter`,
  `offset_to_line`: the primitives the above are built from.

Lexical model (what `strip_comments_and_strings_preserving_offsets` treats as what):

* `-- ...` is a comment up to, not including, the newline.
* `/- ... -/` is a comment and nests to any depth; `/-- ... -/` and `/-! ... -/` are the
  same token with a doc kind. A comment that never closes extends to the end of the text.
  The body is searched from just past the opening `/-`, so `/--/` is a complete comment
  and inside a comment `-/` closes even when a `/` precedes it (`/-/`).
* `"..."` is a string literal in which a `"` preceded by an odd run of backslashes does not
  close it. `r"..."`, `r#"..."#`, `r##"..."##`, ... are raw strings that end at the first
  `"` followed by as many `#` as opened them; an `r` that continues an identifier or follows
  a `.` (`x.r"..."`, `ident_r"..."`) does not make the string raw.
* `'"'` and `'\\"'` are character literals, so their `"` opens nothing, and `'«'` is a
  character literal, so its `«` opens nothing. All other character literals (`'a'`, `'\\\\'`,
  `'\\''`, `'»'`, `'\\n'`, `'\\x22'`, `'\\u0022'`, ...) contain no delimiter and are ordinary
  code. A `'` that continues an identifier is a prime, not a quote, so `x'"hello"` is `x'`
  applied to a string, and in `f '\\''"hello"` the string starts after the literal `'\\''`.
* `«...»` on one line is a single identifier whose characters (`--`, `/-`, `"`, `[`, ...)
  are never delimiters. A `«` with no `»` before the end of its line is an ordinary
  character and swallows nothing.

Blanked characters become spaces. Only the delimiter-relevant character of a quote or
guillemet character literal is blanked (`'"'` becomes `' '`); the apostrophes and all other
character literals stay, since they are code.

The default mode is, character for character, the code channel of the waiver-pin and 3-axis
auditor's own lexer (the section duplicated verbatim in `proof_health.py` and the trusted
checker, which must stay a single self-contained file). Tools that mix both lexers rely on
that equality, and `test_proof_health.py` enforces it on seeded delimiter soups and on real
proof files; `is_ident_char` is pinned to the auditor's identifier predicate for the same
reason.

Import cost matters: hook processes import this module without cached bytecode, so it
uses plain `__slots__` classes (no `dataclasses`, no `typing`), imports `re` and compiles
its regular expressions only when the attribute or scope scanner first needs them, and
jumps between delimiters with `str.find` (about 3 ms per MB).
"""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

from bisect import bisect_left, bisect_right

__all__ = [
    "AttributeSpan",
    "DOC_COMMENT",
    "DocSpan",
    "LeanScanResult",
    "LineCounter",
    "MODULE_DOC_COMMENT",
    "NamespaceTracker",
    "SCOPE_MUTUAL",
    "SCOPE_NAMESPACE",
    "SCOPE_SECTION",
    "blank_preserving_newlines",
    "is_ident_char",
    "is_ident_start",
    "match_balanced_attribute",
    "offset_to_line",
    "scan_balanced_attributes",
    "scan_lean_source",
    "strip_comments_and_strings_preserving_offsets",
    "track_namespaces",
]


# ---------------------------------------------------------------------------
# Core lexical primitives
# ---------------------------------------------------------------------------


def _is_lean_subscript(cp: int) -> bool:
    """True when code point `cp` is a Lean 4 subscript letter/digit (`isSubScriptAlnum`),
    which may continue an identifier (`isIdRest`) but never start one (`isIdFirst`)."""
    return 0x2080 <= cp <= 0x209C or 0x1D62 <= cp <= 0x1D6A or cp == 0x2C7C


def is_ident_start(ch: str) -> bool:
    """True when the single character `ch` can start a Lean 4 identifier component
    (`isIdFirst`): `_`, an ASCII letter, or a Unicode letter other than Lean's binder
    symbols (`λ`, `Π`, `Σ`) and subscript letters (`ₐ`..`ₜ`, `ᵢ`..`ᵪ`, `ⱼ`).

    Guillemet components (`«...»`) are delimited, not classified, and are handled by the
    scanners themselves.
    """
    if len(ch) != 1:
        return False
    if ch == "_":
        return True
    if not ch.isalpha():
        return False
    cp = ord(ch)
    if cp < 0x80:
        return True
    return cp not in (0x03BB, 0x03A0, 0x03A3) and not _is_lean_subscript(cp)


def is_ident_char(ch: str) -> bool:
    """True when the single character `ch` can continue a Lean 4 identifier component
    (`isIdRest`): a letter, a digit (subscripts such as `₁` and `ₐ` included), `_`, `'`,
    `!` or `?` (`get?`, `get!`, `h₁'`).

    Unicode is classified by `str.isalnum`, a superset of the toolchain's own tables that
    does not move when a toolchain release reclassifies a block (accented Latin letters, for
    instance). Over-accepting only makes word-boundary checks more conservative. On every
    character the predicate equals the auditor's `_is_lean_ident_char`, which the lexer
    parity described in the module docstring depends on; unlike it, empty or multi-character
    strings return `False`.
    """
    return len(ch) == 1 and (ch.isalnum() or ch in "_'!?")


# Byte table mapping every byte except `\n` to a space (`bytes.translate` is a tight C
# loop; ASCII text round-trips through it unchanged in length).
_BLANK_BYTES_TABLE = b" " * 10 + b"\n" + b" " * 245


def blank_preserving_newlines(seg: str) -> str:
    """`seg` with every character except `\\n` replaced by a space (same length, same
    newline offsets)."""
    if "\n" not in seg:
        return " " * len(seg)
    if seg.isascii():
        return seg.encode("ascii").translate(_BLANK_BYTES_TABLE).decode("ascii")
    return "\n".join([" " * len(part) for part in seg.split("\n")])


class LineCounter:
    """1-based line numbers of offsets in `text`, counted incrementally from the previous
    query: a scan whose queries move forward costs `O(len(text))` in total (amortized
    `O(1)` per query on top of the distance moved) instead of one prefix count per query.
    Backward queries are answered too, from whichever of the start and the previous offset
    is closer."""

    __slots__ = ("text", "off", "line")

    def __init__(self, text: str) -> None:
        self.text = text
        self.off = 0
        self.line = 1

    def __call__(self, offset: int) -> int:
        if offset <= 0:
            self.off = 0
            self.line = 1
            return 1
        n = len(self.text)
        if offset > n:
            offset = n
        if offset >= self.off:
            self.line += self.text.count("\n", self.off, offset)
        elif offset * 2 < self.off:
            self.line = self.text.count("\n", 0, offset) + 1
        else:
            self.line -= self.text.count("\n", offset, self.off)
        self.off = offset
        return self.line


def offset_to_line(text_or_offsets: str | list[int], offset: int) -> int:
    """1-based line number of `offset`, given either the text itself (`O(offset)`) or the
    sorted offsets of its `\\n` characters (`O(log N)`). Both forms agree at every offset: a
    newline character belongs to the line it ends."""
    if offset <= 0:
        return 1
    if isinstance(text_or_offsets, str):
        return text_or_offsets.count("\n", 0, offset) + 1
    return bisect_left(text_or_offsets, offset) + 1


# ---------------------------------------------------------------------------
# Single-pass offset- and newline-preserving scanner
# ---------------------------------------------------------------------------

DOC_COMMENT = "doc"  # `/-- ... -/`
MODULE_DOC_COMMENT = "moddoc"  # `/-! ... -/`


class DocSpan(tuple):
    """`(start_pos, end_pos, kind, line_no)` of one doc comment: `text[start_pos:end_pos]`
    is the whole token from `/--` or `/-!` through its closing `-/` (or the end of the text
    when unterminated), `kind` is `DOC_COMMENT` or `MODULE_DOC_COMMENT`, and `line_no` is
    the 1-based line of `start_pos`. An immutable tuple with named fields."""

    __slots__ = ()

    def __new__(cls, start_pos: int, end_pos: int, kind: str, line_no: int) -> DocSpan:
        return tuple.__new__(cls, (start_pos, end_pos, kind, line_no))

    @property
    def start_pos(self) -> int:
        return self[0]

    @property
    def end_pos(self) -> int:
        return self[1]

    @property
    def kind(self) -> str:
        return self[2]

    @property
    def line_no(self) -> int:
        return self[3]

    def __repr__(self) -> str:
        return "DocSpan(start_pos=%r, end_pos=%r, kind=%r, line_no=%r)" % tuple(self)


class LeanScanResult:
    """What one lexing pass learned about a Lean 4 source text. Immutable.

    * `stripped`: the text with comments (and, unless kept, string literals) blanked;
      same length and newline offsets as the source.
    * `doc_comments`: a `DocSpan` for every `/-- ... -/` and `/-! ... -/`, in source order.
    * `unclosed_block_comment_pos`: offset of the `/-` that opens a block comment still
      open at the end of the text (the outermost one), or `-1`.
    * `unclosed_string_pos`: offset of the `"` that opens a string literal (raw or not)
      still open at the end of the text, or `-1`.
    """

    __slots__ = ("stripped", "doc_comments", "unclosed_block_comment_pos", "unclosed_string_pos")

    def __init__(
        self,
        stripped: str,
        doc_comments: tuple[DocSpan, ...] = (),
        unclosed_block_comment_pos: int = -1,
        unclosed_string_pos: int = -1,
    ) -> None:
        set_attr = object.__setattr__
        set_attr(self, "stripped", stripped)
        set_attr(self, "doc_comments", doc_comments)
        set_attr(self, "unclosed_block_comment_pos", unclosed_block_comment_pos)
        set_attr(self, "unclosed_string_pos", unclosed_string_pos)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("LeanScanResult is immutable")

    def __repr__(self) -> str:
        return (
            f"LeanScanResult(len(stripped)={len(self.stripped)}, "
            f"doc_comments={len(self.doc_comments)}, "
            f"unclosed_block_comment_pos={self.unclosed_block_comment_pos}, "
            f"unclosed_string_pos={self.unclosed_string_pos})"
        )


def _blank_string_keeping_quotes(text: str, start: int, end: int, closer_len: int) -> str:
    """The string literal `text[start:end]` with its body blanked and its delimiters kept:
    the opening `"` and the last `closer_len` characters (`"`, or `"#...` for a raw string;
    `0` when the literal is unterminated)."""
    body_end = end - closer_len
    return '"' + blank_preserving_newlines(text[start + 1 : body_end]) + text[body_end:end]


def _scan(
    text: str,
    keep_strings: bool,
    retain_quotes: bool,
    docs: list[tuple[int, int, str]] | None,
) -> tuple[str, int, int]:
    """The single lexing pass: `(stripped, unclosed_block_comment_pos, unclosed_string_pos)`;
    appends `(start, end, kind)` of every doc comment to `docs` when it is a list.

    The loop runs once per comment, string or guillemet token and copies the code between
    tokens in whole slices; `str.find` locates the next occurrence of each of the four
    token openers and each position is only re-searched once the scan has passed it.
    """
    n = len(text)
    if n == 0:
        return "", -1, -1
    out: list[str] = []
    app = out.append  # bound once: the loop runs once per token
    find = text.find
    unclosed_blk = -1
    unclosed_str = -1
    pos = 0
    # Next occurrence of each opener at or after `pos`; `n` when there is none.
    i_lin = find("--", 0)
    if i_lin == -1:
        i_lin = n
    i_blk = find("/-", 0)
    if i_blk == -1:
        i_blk = n
    i_str = find('"', 0)
    if i_str == -1:
        i_str = n
    i_gui = find("«", 0)
    if i_gui == -1:
        i_gui = n
    while pos < n:
        if i_lin < pos:
            i_lin = find("--", pos)
            if i_lin == -1:
                i_lin = n
        if i_blk < pos:
            i_blk = find("/-", pos)
            if i_blk == -1:
                i_blk = n
        if i_str < pos:
            i_str = find('"', pos)
            if i_str == -1:
                i_str = n
        if i_gui < pos:
            i_gui = find("«", pos)
            if i_gui == -1:
                i_gui = n

        nxt = i_lin
        if i_blk < nxt:
            nxt = i_blk
        if i_str < nxt:
            nxt = i_str
        if i_gui < nxt:
            nxt = i_gui

        if nxt == n:
            app(text[pos:])
            break
        if nxt > pos:
            app(text[pos:nxt])

        if nxt == i_lin:
            # `--` line comment up to (not including) the newline.
            nl = find("\n", nxt + 2)
            end = n if nl == -1 else nl
            app(" " * (end - nxt))
            pos = end
            continue

        if nxt == i_blk:
            # `/- ... -/` block comment with arbitrary nesting depth.
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
            if depth > 0:
                unclosed_blk = nxt
            if docs is not None and (depth > 0 or cur >= nxt + 5):
                marker = text[nxt + 2 : nxt + 3]
                if marker == "-":
                    docs.append((nxt, cur, DOC_COMMENT))
                elif marker == "!":
                    docs.append((nxt, cur, MODULE_DOC_COMMENT))
            if find("\n", nxt, cur) == -1:
                app(" " * (cur - nxt))
            else:
                app(blank_preserving_newlines(text[nxt:cur]))
            pos = cur
            continue

        if nxt == i_gui:
            # `'«'` is a character literal, not an opening guillemet. Its `«` is blanked
            # with the literals so that a `»` in a later comment can never pair with it.
            if (
                nxt > 0
                and nxt + 1 < n
                and text[nxt - 1] == "'"
                and text[nxt + 1] == "'"
                and (nxt < 2 or (not is_ident_char(text[nxt - 2]) and text[nxt - 2] != "\\"))
            ):
                app("«" if keep_strings else " ")
                pos = nxt + 1
                continue
            # Guillemet identifier `«...»` on one line: everything inside is part of the
            # name. Without a closing `»` on the line, `«` is an ordinary character.
            # Bound the `»` search to the current line so repeated unclosed `«` never
            # scan quadratically to EOF.
            nl = find("\n", nxt + 1)
            g_end = find("»", nxt + 1, n if nl == -1 else nl)
            if g_end != -1:
                app(text[nxt : g_end + 1])
                pos = g_end + 1
            else:
                app("«")
                pos = nxt + 1
            continue

        # `nxt` is a `"`. A raw string or a quote character literal is recognised by the
        # character before it: `#` or `r` (`r"`, `r#"`), `'` (`'"'`) or a backslash (`'\"'`).
        if nxt > 0 and text[nxt - 1] in "#r'\\":
            h = nxt
            while h > 0 and text[h - 1] == "#":
                h -= 1
            if (
                h > 0
                and text[h - 1] == "r"
                and (h < 2 or not (is_ident_char(text[h - 2]) or text[h - 2] == "."))
            ):
                closer = '"' + "#" * (nxt - h)
                c = find(closer, nxt + 1)
                if c == -1:
                    cur = n
                    closer_len = 0
                    unclosed_str = nxt
                else:
                    closer_len = len(closer)
                    cur = c + closer_len
                if keep_strings:
                    app(text[nxt:cur])
                elif retain_quotes:
                    app(_blank_string_keeping_quotes(text, nxt, cur, closer_len))
                else:
                    app(blank_preserving_newlines(text[nxt:cur]))
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
                            or (not is_ident_char(text[nxt - 2]) and text[nxt - 2] != "\\")
                        )
                    )
                    or (
                        nxt >= 2
                        and text[nxt - 2 : nxt] == "'\\"
                        and (nxt < 3 or not is_ident_char(text[nxt - 3]))
                    )
                )
            ):
                # `'"'` or `'\"'`: the quote is the literal's character, not a delimiter.
                app('"' if keep_strings else " ")
                pos = nxt + 1
                continue

        # Ordinary string literal: ends at the first `"` not escaped by an odd backslash run.
        closer_len = 1
        q = find('"', nxt + 1)
        if q == -1:
            cur = n
            closer_len = 0
        elif text[q - 1] != "\\":
            cur = q + 1
        else:
            cur = nxt + 1
            closer_len = 0
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
                    closer_len = 1
                    break
        if closer_len == 0:
            unclosed_str = nxt
        if keep_strings:
            app(text[nxt:cur])
        elif retain_quotes:
            app(_blank_string_keeping_quotes(text, nxt, cur, closer_len))
        elif find("\n", nxt, cur) == -1:
            app(" " * (cur - nxt))
        else:
            app(blank_preserving_newlines(text[nxt:cur]))
        pos = cur
    return "".join(out), unclosed_blk, unclosed_str


def strip_comments_and_strings_preserving_offsets(
    text: str, *, keep_strings: bool = False, retain_quotes: bool = False
) -> str:
    """Blank out Lean 4 comments and string literals character for character.

    The result `out` satisfies `len(out) == len(text)` and `out[i] == "\\n"` exactly when
    `text[i] == "\\n"`; every other character is either the source character or a space.
    See the module docstring for the lexical model.

    * `keep_strings=True`: blank only comments; string, raw string and character literals
      are left intact.
    * `retain_quotes=True` (with strings blanked): keep each string literal's delimiters,
      the opening `"` and the closing `"` (plus the `#` marks of a raw string), and blank
      only its body, so the literal still reads as one token (`"   "`) to later passes.
      It does not affect the quote or guillemet inside a character literal, which is
      content rather than a delimiter and is blanked either way.
    """
    return _scan(text, keep_strings, retain_quotes, None)[0]


def scan_lean_source(
    text: str, *, keep_strings: bool = False, retain_quotes: bool = False
) -> LeanScanResult:
    """One lexing pass over `text` returning the blanked text (exactly
    `strip_comments_and_strings_preserving_offsets(text, ...)`) together with the doc
    comment spans and the offsets of an unterminated block comment or string literal."""
    docs: list[tuple[int, int, str]] = []
    stripped, unclosed_blk, unclosed_str = _scan(text, keep_strings, retain_quotes, docs)
    if not docs:
        return LeanScanResult(stripped, (), unclosed_blk, unclosed_str)
    line_of = LineCounter(text)  # doc comments are in source order: one forward sweep
    spans = tuple([DocSpan(start, end, kind, line_of(start)) for start, end, kind in docs])
    return LeanScanResult(stripped, spans, unclosed_blk, unclosed_str)


def _inside_guillemets(stripped: str, pos: int) -> bool:
    """True when `pos` lies strictly inside a `«...»` identifier closed on its line."""
    line_start = stripped.rfind("\n", 0, pos) + 1
    g = stripped.rfind("«", line_start, pos)
    if g == -1:
        return False
    nl = stripped.find("\n", pos)
    line_end = len(stripped) if nl == -1 else nl
    close = stripped.find("»", g + 1, line_end)
    return close != -1 and close >= pos


# ---------------------------------------------------------------------------
# Balanced `@[...]` attribute scanner
# ---------------------------------------------------------------------------


class AttributeSpan(tuple):
    """`(start_pos, end_pos, line_no, content)` of one `@[...]` attribute list:
    `text[start_pos:end_pos]` runs from the `@` through the matching `]`, `line_no` is the
    1-based line of the `@`, and `content` is the source text between `@[` and `]`
    (string arguments included). An immutable tuple with named fields."""

    __slots__ = ()

    def __new__(cls, start_pos: int, end_pos: int, line_no: int, content: str) -> AttributeSpan:
        return tuple.__new__(cls, (start_pos, end_pos, line_no, content))

    @property
    def start_pos(self) -> int:
        return self[0]

    @property
    def end_pos(self) -> int:
        return self[1]

    @property
    def line_no(self) -> int:
        return self[2]

    @property
    def content(self) -> str:
        return self[3]

    def __repr__(self) -> str:
        return "AttributeSpan(start_pos=%r, end_pos=%r, line_no=%r, content=%r)" % tuple(self)


_CLOSER_OF = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
_ATTR_TOKEN_RE = None  # compiled by `_attr_token_re` on first use


def _attr_token_re():
    """Compiled pattern of the tokens that matter inside an attribute list of comment- and
    string-blanked code: a guillemet identifier or a character literal (skipped whole, so
    the brackets inside `«a]b»` and `']'` never count), a nested `@[`, or one bracket. A
    `'` right after an identifier character or `»` is a prime and starts no character
    literal."""
    global _ATTR_TOKEN_RE
    if _ATTR_TOKEN_RE is None:
        import re  # deferred: importing this module must stay cheap

        _ATTR_TOKEN_RE = re.compile(
            r"«[^»\n]*»"
            r"|(?<![\w'!?\u00bb])'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'"
            r"|@\[|[\[\](){}⟨⟩]"
        )
    return _ATTR_TOKEN_RE


def _is_as_pattern_at(stripped: str, pos: int) -> bool:
    """True when `@[` at `pos` immediately follows an identifier (`xs@[a, b]`, `«xs»@[a]`),
    making it a Lean 4 as-pattern rather than an attribute list opener."""
    return pos > 0 and (is_ident_char(stripped[pos - 1]) or stripped[pos - 1] == "»")


def match_balanced_attribute(stripped: str, pos: int) -> int | None:
    """The offset just past the `]` that closes the attribute list `@[` starting at
    `stripped[pos]`, or `None` when `pos` is not at `@[` or the list is malformed.

    `stripped` must be comment- and string-blanked code (see
    `strip_comments_and_strings_preserving_offsets`). Nested `[...]`, `(...)`, `{...}` and
    `⟨...⟩` are tracked; brackets inside guillemet identifiers and character literals are
    ignored, and `@[` inside a guillemet identifier (`«@[foo]»`) or attached to an
    identifier as an as-pattern (`xs@[a, b]`) is not an attribute. The list is malformed,
    and rejected, when a closing bracket does not match the innermost open one, when another
    standalone `@[` starts before it is closed (attribute lists do not nest, so a missing
    `]` never swallows the following declaration), or when the text ends first. Every
    rejection stops at the offending token, so scanning is linear.
    """
    if pos < 0 or not stripped.startswith("@[", pos):
        return None
    if _is_as_pattern_at(stripped, pos) or _inside_guillemets(stripped, pos):
        return None
    expected = ["]"]
    for m in _attr_token_re().finditer(stripped, pos + 2):
        tok = m.group()
        if len(tok) != 1:
            if tok == "@[":
                if _is_as_pattern_at(stripped, m.start()):
                    expected.append("]")
                    continue
                return None
            continue  # guillemet identifier or character literal
        closer = _CLOSER_OF.get(tok)
        if closer is not None:
            expected.append(closer)
        elif tok == expected[-1]:
            expected.pop()
            if not expected:
                return m.end()
        else:
            return None
    return None


def scan_balanced_attributes(
    text: str, pos: int = 0, *, stripped: str | None = None
) -> list[AttributeSpan]:
    """Every well-formed `@[...]` attribute list of `text` starting at or after `pos`, in
    source order (`match_balanced_attribute` decides what is well formed).

    `stripped` is `strip_comments_and_strings_preserving_offsets(text)` when the caller
    already has it; attributes inside comments, strings and guillemet identifiers are never
    reported. A malformed `@[` is skipped and scanning resumes right after it.
    """
    if stripped is None or len(stripped) != len(text):
        stripped = strip_comments_and_strings_preserving_offsets(text)
    spans: list[AttributeSpan] = []
    find = stripped.find
    line_of = LineCounter(stripped)
    start = find("@[", pos if pos > 0 else 0)
    while start != -1:
        end = match_balanced_attribute(stripped, start)
        if end is None:
            start = find("@[", start + 2)
            continue
        spans.append(AttributeSpan(start, end, line_of(start), text[start + 2 : end - 1]))
        start = find("@[", end)
    return spans


# ---------------------------------------------------------------------------
# `O(log K)` namespace and scope tracker
# ---------------------------------------------------------------------------

SCOPE_NAMESPACE = "namespace"
SCOPE_SECTION = "section"
SCOPE_MUTUAL = "mutual"

_SCOPE_KEYWORDS = (SCOPE_NAMESPACE, SCOPE_SECTION, SCOPE_MUTUAL, "end")
_WHITESPACE = " \t\r\n"

# Keywords that can follow a scope command and are therefore never its name
# (`section variable (x : Nat)`, `end theorem ...` on one line).
_NOT_A_SCOPE_NAME = frozenset(
    (
        "abbrev", "add_decl_doc", "at", "attribute", "axiom", "builtin_initialize", "by",
        "class", "declare_syntax_cat", "def", "deriving", "do", "elab", "elab_rules", "else",
        "end", "example", "export", "from", "fun", "have", "if", "import", "in", "include",
        "inductive", "infix", "infixl", "infixr", "initialize", "instance", "lemma", "let",
        "local", "macro", "macro_rules", "match", "meta", "module", "mutual", "namespace",
        "noncomputable", "nonrec", "notation", "omit", "opaque", "open", "partial", "postfix",
        "prefix", "private", "protected", "public", "scoped", "section", "set_option", "show",
        "structure", "syntax", "termination_by", "then", "theorem", "universe", "unsafe",
        "variable", "where", "with",
    )
)  # fmt: skip

_DECL_MODIFIERS = (
    "private",
    "protected",
    "public",
    "noncomputable",
    "partial",
    "unsafe",
    "nonrec",
    "scoped",
    "local",
)

_NON_CMD_AFTER_CHARS = frozenset(":=<>≤≥≠+-*/,)]}|")
_NON_CMD_BEFORE_CHARS = frozenset(":=<>≤≥≠+-*/,|([{→")
_NON_CMD_BEFORE_WORDS = frozenset(
    (
        "let", "have", "show", "exact", "apply", "refine", "return", "fun", "λ",
        "match", "if", "then", "else", "do", "by", "from", "with", "case", "cases",
        "induction", "rcases", "obtain", "intro", "rw", "erw", "rewrite",
        "unfold", "change", "suffices", "for", "while", "unless",
    )
)  # fmt: skip
_SCOPE_BLOCK_WINDOW = 8192

_SCOPE_RES = None  # compiled by `_scope_res` on first use


def _scope_res():
    """Compiled regex bundle `(name_re, part_re, bracket_re, quot_re, line_re, cont_re,
    cmd_re, strict_cmd_re, in_prefix_re, in_tok_re)` for `NamespaceTracker`, compiled once
    on first use."""
    global _SCOPE_RES
    if _SCOPE_RES is None:
        import re  # deferred: importing this module must stay cheap

        # Match Lean 4 `isIdFirst` for non-guillemet parts: exclude digits, binder symbols
        # (`λ`, `Π`, `Σ`), and Lean subscript letters/digits (`₀`..`ₜ`, `ᵢ`..`ᵪ`, `ⱼ`).
        id_start = r"[^\W\d\u03bb\u03a0\u03a3\u2080-\u209c\u1d62-\u1d6a\u2c7c]"
        part = rf"(?:{id_start}[\w'!?]*|«[^»\n]+»)"
        gui_or_char = (
            r"«[^»\n]*»"
            r"|(?<![\w'!?\u00bb])'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'"
        )
        name_re = re.compile(part + r"(?:\." + part + r")*")
        part_re = re.compile(part)
        bracket_re = re.compile(gui_or_char + r"|[\[\](){}⟨⟩]")
        quot_re = re.compile(gui_or_char + r"|`[\(\[\{]|[\[\](){}⟨⟩]")
        line_re = re.compile(r"\n([ \t]*)(?=\S)")
        cont_re = re.compile(
            r"[ \t]*(?:\||where\b|termination_by\b|decreasing_by\b|deriving\b(?![ \t]+instance\b))"
        )
        cmd_re = re.compile(
            r"#[A-Za-z_]\w*(?!\[)|"
            r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|example|"
            r"end|namespace|section|mutual|variable|universe|open|export|set_option|attribute|"
            r"notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules|"
            r"declare_syntax_cat|initialize|builtin_initialize|deriving|import|"
            r"omit|include|add_decl_doc|register_option|run_cmd|run_elab|run_meta|alias)"
            r"(?![\w'!?.])"
        )
        # Subset of `cmd_re` that cannot start a tactic inside `:= by ...` on the same line.
        strict_cmd_re = re.compile(
            r"#[A-Za-z_]\w*(?!\[)|"
            r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|example|"
            r"end|namespace|section|mutual|declare_syntax_cat|initialize|builtin_initialize|"
            r"deriving|import|add_decl_doc|register_option|alias)"
            r"(?![\w'!?.])"
        )
        in_prefix_re = re.compile(
            r"(?:namespace|section|set_option|open|variable|universe|attribute|include|omit|export|"
            r"notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules)"
            r"(?![\w'!?.])"
        )
        in_tok_re = re.compile(
            gui_or_char + r"|[(){}\[\]⟨⟩\n;]|:=|(?<![\w'!?.\u00bb])in(?![\w'!?.\u00bb])"
        )
        _SCOPE_RES = (
            name_re,
            part_re,
            bracket_re,
            quot_re,
            line_re,
            cont_re,
            cmd_re,
            strict_cmd_re,
            in_prefix_re,
            in_tok_re,
        )
    return _SCOPE_RES


def _merge_spans(raw: list[tuple[int, int]]) -> list[tuple[int, int]]:
    if not raw:
        return []
    raw.sort()
    merged = [raw[0]]
    for lo, hi in raw[1:]:
        prev_lo, prev_hi = merged[-1]
        if lo <= prev_hi:
            if hi > prev_hi:
                merged[-1] = (prev_lo, hi)
        else:
            merged.append((lo, hi))
    return merged


def _closed_bracket_spans(stripped: str, bracket_re) -> list[tuple[int, int]]:
    """Merged `(open_pos, close_pos)` intervals of balanced `()`, `[]`, `{}`, `⟨⟩` groups in
    `stripped`."""
    stack: list[tuple[str, int]] = []
    raw: list[tuple[int, int]] = []
    for m in bracket_re.finditer(stripped):
        tok = m.group()
        if len(tok) != 1:
            continue
        closer = _CLOSER_OF.get(tok)
        if closer is not None:
            stack.append((closer, m.start()))
        elif stack and stack[-1][0] == tok:
            _, open_pos = stack.pop()
            raw.append((open_pos, m.start()))
        else:
            stack.clear()
    return _merge_spans(raw)


def _quotation_spans(
    stripped: str, quot_re, *, has_guillemets: bool = False
) -> list[tuple[int, int]]:
    """Merged `(open_pos, close_pos)` spans of Lean syntax quotations (`` `(...) ``,
    `` `[...] ``, `` `{...} ``). Jumps between backticks with single-byte `str.find` so
    files with a few quotations avoid scanning non-quotation brackets, while advancing past
    each visited span so even hundreds of unclosed quotations stay strictly `O(N)`."""
    spans: list[tuple[int, int]] = []
    find = stripped.find
    n = len(stripped)
    pos = 0
    while True:
        q = find("`", pos)
        if q == -1 or q + 1 >= n:
            break
        ch = stripped[q + 1]
        closer = _CLOSER_OF.get(ch)
        if closer is None or ch == "⟨":
            pos = q + 1
            continue
        if has_guillemets and _inside_guillemets(stripped, q):
            pos = q + 2
            continue
        stack: list[tuple[str, int, bool]] = [(closer, q + 1, True)]
        end_pos = n
        for m in quot_re.finditer(stripped, q + 2):
            tok = m.group()
            if len(tok) == 2 and tok[0] == "`":
                stack.append((_CLOSER_OF[tok[1]], m.start() + 1, True))
                continue
            if len(tok) != 1:
                continue
            c = _CLOSER_OF.get(tok)
            if c is not None:
                stack.append((c, m.start(), False))
            elif stack and stack[-1][0] == tok:
                _, open_pos, is_quot = stack.pop()
                if is_quot:
                    spans.append((open_pos, m.start()))
                if not stack:
                    end_pos = m.end()
                    break
            else:
                stack.clear()
                end_pos = m.end()
                break
        pos = end_pos
    return _merge_spans(spans)


def _inside_spans(spans: list[tuple[int, int]], pos: int) -> bool:
    if not spans:
        return False
    i = bisect_right(spans, (pos, 1 << 62)) - 1
    return i >= 0 and spans[i][0] < pos < spans[i][1]


def _is_non_command_scope_token(stripped: str, pos: int, kw: str, line_start: int, n: int) -> bool:
    """True when a standalone `namespace`/`section`/`mutual`/`end` token at `pos` is in
    expression/field/tactic position on the same line rather than a scope command."""
    after = pos + len(kw)
    k = after
    while k < n and stripped[k] in " \t\r":
        k += 1
    if k < n and stripped[k] in _NON_CMD_AFTER_CHARS:
        return True
    b = pos - 1
    while b >= line_start and stripped[b] in " \t":
        b -= 1
    if b >= line_start:
        ch = stripped[b]
        if ch in _NON_CMD_BEFORE_CHARS:
            return True
        if is_ident_char(ch) or ch == "λ":
            w_start = b
            while w_start > line_start and is_ident_char(stripped[w_start - 1]):
                w_start -= 1
            if stripped[w_start : b + 1] in _NON_CMD_BEFORE_WORDS:
                return True
    return False


def _enclosing_col0_block(stripped: str, pos: int, line_start: int, cmd_re, n: int) -> tuple[int, int]:
    """Bounded `(blk_start, blk_end)` enclosing `pos` between column-0 command lines."""
    lo_limit = max(0, line_start - _SCOPE_BLOCK_WINDOW)
    blk_start = lo_limit
    cur = line_start
    while cur > lo_limit:
        prev_nl = stripped.rfind("\n", lo_limit, cur)
        cand = 0 if prev_nl == -1 else prev_nl + 1
        if cand < n and stripped[cand] not in _WHITESPACE:
            kw_pos = _skip_attrs_and_mods(stripped, cand)
            if cmd_re.match(stripped, kw_pos) is not None:
                blk_start = cand
                break
        if prev_nl == -1:
            blk_start = 0
            break
        cur = prev_nl
    hi_limit = min(n, pos + _SCOPE_BLOCK_WINDOW)
    blk_end = hi_limit
    cur = stripped.find("\n", pos, hi_limit)
    while cur != -1 and cur + 1 < hi_limit:
        cand = cur + 1
        if stripped[cand] not in _WHITESPACE:
            kw_pos = _skip_attrs_and_mods(stripped, cand)
            if cmd_re.match(stripped, kw_pos) is not None:
                blk_end = cand
                break
        cur = stripped.find("\n", cand, hi_limit)
    return blk_start, blk_end


def _scope_keyword_hits(
    stripped: str,
    bracket_re,
    quot_re,
    cmd_re,
    *,
    quot_spans: list[tuple[int, int]] | None = None,
) -> list[tuple[int, str]]:
    """Offsets of standalone top-level `namespace`, `section`, `mutual` and `end` tokens,
    sorted by offset."""
    n = len(stripped)
    find = stripped.find
    has_guillemets = "«" in stripped
    hits: list[tuple[int, str]] = []
    for kw in _SCOPE_KEYWORDS:
        klen = len(kw)
        pos = find(kw)
        while pos != -1:
            end = pos + klen
            if pos > 0:
                before = stripped[pos - 1]
                if is_ident_char(before) or before == "." or before == "«":
                    pos = find(kw, end)
                    continue
            if end < n:
                after = stripped[end]
                if is_ident_char(after) or after == "." or after == "»":
                    pos = find(kw, end)
                    continue
            if not (has_guillemets and _inside_guillemets(stripped, pos)):
                hits.append((pos, kw))
            pos = find(kw, end)
    if not hits:
        return hits
    hits.sort()
    if quot_spans is None:
        quot_spans = (
            _quotation_spans(stripped, quot_re, has_guillemets=has_guillemets)
            if "`" in stripped
            else []
        )
    filtered: list[tuple[int, str]] = []
    cached_line_start = -1
    cached_line_spans: list[tuple[int, int]] = []
    cached_blk_bounds = (-1, -1)
    cached_blk_spans: list[tuple[int, int]] = []
    for p, kw in hits:
        if quot_spans and _inside_spans(quot_spans, p):
            continue
        line_start = stripped.rfind("\n", 0, p) + 1
        if _is_non_command_scope_token(stripped, p, kw, line_start, n):
            continue
        prefix = stripped[line_start:p]
        if any(c in prefix for c in "([{⟨"):
            if line_start != cached_line_start:
                line_end = stripped.find("\n", p)
                if line_end == -1:
                    line_end = n
                cached_line_start = line_start
                cached_line_spans = [
                    (line_start + lo, line_start + hi)
                    for lo, hi in _closed_bracket_spans(stripped[line_start:line_end], bracket_re)
                ]
            if _inside_spans(cached_line_spans, p):
                continue
        if p > line_start:
            blk_bounds = _enclosing_col0_block(stripped, p, line_start, cmd_re, n)
            blk_start, blk_end = blk_bounds
            if blk_start < line_start and any(c in stripped[blk_start:line_start] for c in "([{⟨"):
                if blk_bounds != cached_blk_bounds:
                    cached_blk_bounds = blk_bounds
                    cached_blk_spans = [
                        (blk_start + lo, blk_start + hi)
                        for lo, hi in _closed_bracket_spans(stripped[blk_start:blk_end], bracket_re)
                    ]
                if _inside_spans(cached_blk_spans, p):
                    continue
        filtered.append((p, kw))
    return filtered


def _column_of(stripped: str, pos: int) -> int:
    return pos - (stripped.rfind("\n", 0, pos) + 1)


def _line_indent_of(stripped: str, pos: int) -> int:
    line_start = stripped.rfind("\n", 0, pos) + 1
    k = line_start
    n = len(stripped)
    while k < n and stripped[k] in " \t":
        k += 1
    return k - line_start


def _skip_attrs_and_mods(stripped: str, pos: int) -> int:
    n = len(stripped)
    p = pos
    while p < n:
        while p < n and stripped[p] in _WHITESPACE:
            p += 1
        if p >= n:
            break
        if stripped.startswith("@[", p):
            end_attr = match_balanced_attribute(stripped, p)
            if end_attr is not None:
                p = end_attr
                continue
        matched = False
        for mod in _DECL_MODIFIERS:
            if stripped.startswith(mod, p):
                end_m = p + len(mod)
                if end_m < n and stripped[end_m] in _WHITESPACE:
                    p = end_m + 1
                    matched = True
                    break
        if not matched:
            break
    return p


def _find_in_governed_end(
    stripped: str,
    in_end: int,
    cmd_indent: int,
    *,
    quot_spans: list[tuple[int, int]] = (),  # type: ignore[assignment]
) -> tuple[int, bool]:
    """Given `<scope_cmd> in` ending at `in_end` with governing line indentation
    `cmd_indent`, return `(end_offset, is_mutual)` for the single command governed by `in`.

    When `is_mutual` is `True`, `end_offset` is the offset of the `mutual` keyword and the
    `in`-scope stays active until that `mutual` block's matching `end`. Otherwise
    `end_offset` is the offset where the governed command ends (`in_end` when `in` is
    dangling before `end` or EOF).
    """
    _, _, bracket_re, _, line_re, cont_re, cmd_re, strict_cmd_re, in_prefix_re, in_tok_re = (
        _scope_res()
    )
    n = len(stripped)

    def is_cmd_start(cand: int) -> bool:
        kw = _skip_attrs_and_mods(stripped, cand)
        return cmd_re.match(stripped, kw) is not None

    def is_strict_top_cmd(cand: int) -> bool:
        kw = _skip_attrs_and_mods(stripped, cand)
        return strict_cmd_re.match(stripped, kw) is not None

    # Advance past any chained `<cmd> in` prefixes (`open ... in`, `set_option ... in`,
    # `namespace ... in`, ...) and leading `@[...]` / modifiers to the target command head.
    p = in_end
    while p < n:
        q = _skip_attrs_and_mods(stripped, p)
        if q >= n:
            return in_end, False
        if stripped.startswith("end", q) and (
            q + 3 >= n or not (is_ident_char(stripped[q + 3]) or stripped[q + 3] == ".")
        ):
            return in_end, False
        pm = in_prefix_re.match(stripped, q)
        if pm is None:
            p = q
            break
        depth = 0
        chained_in = -1
        for tm in in_tok_re.finditer(stripped, pm.end()):
            tok = tm.group()
            if len(tok) > 2 or tok[0] in ("«", "'"):
                continue
            if tok in "({[⟨":
                depth += 1
            elif tok in ")}]⟩":
                if depth > 0:
                    depth -= 1
            elif depth > 0:
                continue
            elif tok == "in":
                chained_in = tm.end()
                break
            elif tok in (":=", ";"):
                break
            elif tok == "\n":
                cand = tm.end()
                while cand < n and stripped[cand] in _WHITESPACE:
                    cand += 1
                if cand < n and is_cmd_start(cand):
                    break
        if chained_in == -1:
            p = q
            break
        p = chained_in

    if p >= n:
        return in_end, False
    if stripped.startswith("mutual", p) and (
        p + 6 >= n or not (is_ident_char(stripped[p + 6]) or stripped[p + 6] == ".")
    ):
        return p, True

    # Check if a second command shares the target command's opening line (e.g. via `;` or an
    # inline `end` / `def` / `namespace` after `:= expr`).
    line_end = stripped.find("\n", p)
    if line_end == -1:
        line_end = n
    depth = 0
    body_eq_end = -1
    in_block_body = False
    after_head = cmd_re.match(stripped, p)
    scan_from = after_head.end() if after_head is not None else p
    for tm in in_tok_re.finditer(stripped, scan_from, line_end):
        tok = tm.group()
        if len(tok) > 2 or tok[0] in ("«", "'"):
            continue
        if tok in "({[⟨":
            depth += 1
        elif tok in ")}]⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if tok == ";":
                if body_eq_end == -1:
                    return tm.start(), False
                after_semi = tm.end()
                while after_semi < line_end and stripped[after_semi] in " \t":
                    after_semi += 1
                if after_semi < line_end and is_strict_top_cmd(after_semi):
                    return tm.start(), False
            elif tok == ":=" and body_eq_end == -1:
                body_eq_end = tm.end()
                after_eq = body_eq_end
                while after_eq < line_end and stripped[after_eq] in " \t":
                    after_eq += 1
                for blk_kw in ("by", "do"):
                    if stripped.startswith(blk_kw, after_eq) and (
                        after_eq + 2 >= line_end
                        or not (
                            is_ident_char(stripped[after_eq + 2]) or stripped[after_eq + 2] == "."
                        )
                    ):
                        in_block_body = True
                        break
    if body_eq_end != -1:
        # Look for an inline command keyword after `:= <atom>` at bracket depth 0 on the same
        # line. Inside `:= by ...` or `:= do ...`, tactic/do prefixes (`open`, `set_option`, ...)
        # belong to the body rather than starting a sibling top-level command.
        body_pos = body_eq_end
        while body_pos < line_end and stripped[body_pos] in " \t":
            body_pos += 1
        b_depth = 0
        saw_atom = False
        while body_pos < line_end:
            ch = stripped[body_pos]
            if ch in " \t":
                if b_depth == 0:
                    saw_atom = True
                body_pos += 1
                continue
            if ch == "«":
                bm = bracket_re.match(stripped, body_pos, line_end)
                if bm is not None and len(bm.group()) > 1:
                    body_pos = bm.end()
                    continue
                body_pos += 1
                continue
            if ch == "'" and (
                body_pos == 0 or not (is_ident_char(stripped[body_pos - 1]) or stripped[body_pos - 1] == "»")
            ):
                bm = bracket_re.match(stripped, body_pos, line_end)
                if bm is not None and len(bm.group()) > 1:
                    body_pos = bm.end()
                    continue
                body_pos += 1
                continue
            if ch in "({[⟨":
                b_depth += 1
                body_pos += 1
                continue
            if ch in ")}]⟩":
                if b_depth > 0:
                    b_depth -= 1
                body_pos += 1
                continue
            if (
                b_depth == 0
                and saw_atom
                and (
                    body_pos == 0
                    or not (is_ident_char(stripped[body_pos - 1]) or stripped[body_pos - 1] in ".«")
                )
            ):
                if is_strict_top_cmd(body_pos) if in_block_body else is_cmd_start(body_pos):
                    return body_pos, False
            while body_pos < line_end:
                c = stripped[body_pos]
                if c in " \t(){}[]⟨⟩«":
                    break
                if c == "'" and (
                    body_pos == 0
                    or not (is_ident_char(stripped[body_pos - 1]) or stripped[body_pos - 1] == "»")
                ):
                    break
                body_pos += 1

    # Multi-line scan: any non-continuation command starting at or left of the governed
    # command's own line indentation ends it (skipping commands inside syntax quotations).
    stop_indent = max(cmd_indent, _line_indent_of(stripped, p))
    cur = line_end
    while cur < n:
        m = line_re.search(stripped, cur)
        if m is None:
            return n, False
        indent = len(m.group(1))
        cand = m.end()
        if (
            indent <= stop_indent
            and not (quot_spans and _inside_spans(quot_spans, cand))
            and not cont_re.match(stripped, cand)
            and is_cmd_start(cand)
        ):
            return m.start(), False
        cur = cand + 1
    return n, False


class NamespaceTracker:
    """The `namespace` / `section` / `mutual` scopes of a Lean 4 source text, queryable by
    offset in `O(log K)` for `K` scope transitions.

    Build one with `NamespaceTracker.from_source(text)` (or `track_namespaces`).

    * `namespace A.B` opens one namespace scope per component (`A`, then `B`), `section`
      and `section S` open a section, `mutual` opens a mutual block, and `end` / `end A.B`
      closes one scope per name component (one without a name), innermost first, exactly
      as the Lean elaborator does.
    * A scope begins right after its header (the end of the name, or of the keyword) and
      ends where the closing `end` keyword starts, so several commands sharing one line
      (`namespace A def x := 1 end A def y := 2` or `namespace A; def x := 1; end A; def y := 2`)
      resolve per command, not per line.
    * Single-command `namespace A.B in <cmd>` and `section [S] in <cmd>` prefixes scope
      `<cmd>` under `A.B` / `S` and automatically pop at the end of `<cmd>` without
      corrupting subsequent file scope.
    * Scope keywords inside balanced `(...)`, `[...]`, `{...}` groups (such as syntax
      quotations `` `(command| namespace Foo ... end Foo) ``), guillemet identifiers
      (`«end»`, `Mir.Demo.«end»`), or `.end` field projections open or close nothing.
    * `violations` lists structural mismatches in source order: an `end` with no open scope
      or with more name components than open scopes, an `end` whose name is missing or
      differs from the scopes it closes, a `namespace` without a name, and a `mutual` block
      still open at the end of the text. (An unclosed `namespace` or `section` at the end of
      a file is legal Lean and not a violation.) Scopes are closed even when the name
      mismatches, as in Lean, so one typo does not shift every later query.
    """

    __slots__ = ("_offsets", "_namespaces", "_scopes", "violations")

    def __init__(
        self,
        offsets: list[int],
        namespaces: list[tuple[str, ...]],
        scopes: list[tuple[tuple[str, str], ...]],
        violations: tuple[str, ...],
    ) -> None:
        self._offsets = offsets
        self._namespaces = namespaces
        self._scopes = scopes
        self.violations = violations

    def namespace_at(self, offset: int) -> tuple[str, ...]:
        """Components of the namespace enclosing `offset` (`()` at the root): one binary
        search over the sorted transition offsets."""
        i = bisect_right(self._offsets, offset) - 1
        return self._namespaces[i] if i >= 0 else ()

    def scopes_at(self, offset: int) -> tuple[tuple[str, str], ...]:
        """Every open scope at `offset`, outermost first, as `(kind, name)` pairs with kind
        `SCOPE_NAMESPACE`, `SCOPE_SECTION` or `SCOPE_MUTUAL` (`name` is `""` for an
        anonymous section or a mutual block). Same `O(log K)` lookup as `namespace_at`."""
        i = bisect_right(self._offsets, offset) - 1
        return self._scopes[i] if i >= 0 else ()

    @property
    def transitions(self) -> tuple[tuple[int, tuple[str, ...]], ...]:
        """`(offset, namespace)` for every scope transition, in source order: from `offset`
        up to the next transition, `namespace_at` returns `namespace`."""
        return tuple(zip(self._offsets, self._namespaces))

    def __len__(self) -> int:
        return len(self._offsets)

    def __repr__(self) -> str:
        return (
            f"NamespaceTracker(transitions={len(self._offsets)}, "
            f"violations={len(self.violations)})"
        )

    @classmethod
    def from_source(cls, text: str, *, stripped: str | None = None) -> NamespaceTracker:
        """Track the scopes of `text`; pass `stripped` when the comment- and string-blanked
        code (`strip_comments_and_strings_preserving_offsets(text)`) is already at hand."""
        if stripped is None or len(stripped) != len(text):
            stripped = strip_comments_and_strings_preserving_offsets(text)
        n = len(stripped)
        name_re, part_re, bracket_re, quot_re, _, _, cmd_re, *_ = _scope_res()
        line_of = LineCounter(stripped)
        offsets: list[int] = []
        namespaces: list[tuple[str, ...]] = []
        scopes_list: list[tuple[tuple[str, str], ...]] = []
        violations: list[str] = []
        stack: list[tuple[str, str]] = []
        mutual_starts: list[int] = []
        # Pending single-command `in` scopes: `[end_off, count, mutual_pos_or_neg1, stack_base]`.
        pending_in: list[list[int]] = []
        consumed = 0  # scope keywords before this offset belong to an earlier header

        def record(offset: int) -> None:
            ns = tuple([nm for kind, nm in stack if kind == SCOPE_NAMESPACE])
            sc = tuple(stack)
            if offsets and offset < offsets[-1]:
                offset = offsets[-1]
            if offsets and offsets[-1] == offset:
                namespaces[-1] = ns
                scopes_list[-1] = sc
            else:
                offsets.append(offset)
                namespaces.append(ns)
                scopes_list.append(sc)

        def flush_pending_up_to(limit_off: int) -> None:
            while pending_in and pending_in[-1][2] == -1 and pending_in[-1][0] <= limit_off:
                end_off, count, _, base = pending_in.pop()
                if len(stack) >= base + count:
                    del stack[base : base + count]
                record(end_off)

        def scope_name(after_kw: int, kw_col: int) -> tuple[str, int]:
            k = after_kw
            crossed_line = False
            while k < n and stripped[k] in _WHITESPACE:
                if stripped[k] == "\n":
                    crossed_line = True
                k += 1
            if k == after_kw or k >= n:
                return "", after_kw
            if crossed_line and _column_of(stripped, k) <= kw_col:
                return "", after_kw
            m = name_re.match(stripped, k)
            if m is None or m.group() in _NOT_A_SCOPE_NAME:
                return "", after_kw
            return m.group(), m.end()

        def next_code_char(k: int) -> tuple[str, int]:
            while k < n and stripped[k] in _WHITESPACE:
                k += 1
            return (stripped[k] if k < n else ""), k

        def match_in_keyword(k: int) -> int:
            """End offset of standalone `in` right at/after `k`, or `-1`."""
            ch, k = next_code_char(k)
            if ch != "i" or not stripped.startswith("in", k):
                return -1
            if k + 2 < n and (is_ident_char(stripped[k + 2]) or stripped[k + 2] == "."):
                return -1
            return k + 2

        has_guillemets = "«" in stripped
        quot_spans: list[tuple[int, int]] = (
            _quotation_spans(stripped, quot_re, has_guillemets=has_guillemets)
            if "`" in stripped
            else []
        )

        for pos, kw in _scope_keyword_hits(
            stripped, bracket_re, quot_re, cmd_re, quot_spans=quot_spans
        ):
            if pos < consumed:
                continue
            flush_pending_up_to(pos)
            # Unclosed syntax quotation fragments (`| namespace $n ...`) open or close nothing.
            b = pos - 1
            while b >= 0 and stripped[b] in _WHITESPACE:
                b -= 1
            if b >= 0 and stripped[b] in "(|":
                continue
            after_kw = pos + len(kw)
            following, _ = next_code_char(after_kw)
            if following == "$" or (kw == "end" and following == ")"):
                continue
            kw_col = _column_of(stripped, pos)

            if kw == SCOPE_MUTUAL:
                for entry in pending_in:
                    if entry[2] == -2 and entry[0] == pos:
                        entry[2] = pos
                stack.append((SCOPE_MUTUAL, ""))
                mutual_starts.append(pos)
                consumed = after_kw
                record(after_kw)
                continue

            name, name_end = scope_name(after_kw, kw_col)
            consumed = name_end
            if kw == "end":
                # If an `in`-scoped command sits at the top of the stack without an open
                # `mutual` inside it, an explicit `end` belongs to the enclosing scope, so
                # close the `in`-scope right before `end`.
                while (
                    pending_in
                    and pending_in[-1][2] < 0
                    and pending_in[-1][3] + pending_in[-1][1] == len(stack)
                ):
                    _, count, _, base = pending_in.pop()
                    del stack[base : base + count]
                    record(pos)
                if not stack:
                    violations.append(
                        f"line {line_of(pos)}: `end{' ' + name if name else ''}` has no open "
                        "scope to close"
                    )
                    continue
                parts = part_re.findall(name) if name else []
                count = len(parts) if parts else 1
                closing = stack[-count:] if count <= len(stack) else list(stack)
                if count > len(stack):
                    violations.append(
                        f"line {line_of(pos)}: `end {name}` closes {count} scopes but only "
                        f"{len(stack)} are open"
                    )
                elif not parts:
                    kind, open_name = closing[-1]
                    if open_name:
                        violations.append(
                            f"line {line_of(pos)}: `end` is missing the name of the open "
                            f"{kind} `{open_name}`"
                        )
                else:
                    opened = [open_name for _, open_name in closing]
                    if opened != parts:
                        described = ", ".join(
                            f"{kind} `{open_name}`" if open_name else f"anonymous {kind}"
                            for kind, open_name in closing
                        )
                        violations.append(
                            f"line {line_of(pos)}: `end {name}` does not match the open "
                            f"{described}"
                        )
                popped_mutuals: list[int] = []
                for kind, _ in closing:
                    if kind == SCOPE_MUTUAL and mutual_starts:
                        popped_mutuals.append(mutual_starts.pop())
                del stack[len(stack) - len(closing) :]
                record(pos)
                if popped_mutuals:
                    popped_set = set(popped_mutuals)
                    while pending_in and pending_in[-1][2] in popped_set:
                        _, p_count, _, base = pending_in.pop()
                        if len(stack) >= base + p_count:
                            del stack[base : base + p_count]
                        record(name_end)
                continue

            if kw == SCOPE_NAMESPACE and not name:
                violations.append(f"line {line_of(pos)}: `namespace` without a name")
                continue

            in_end = match_in_keyword(name_end)
            if in_end != -1:
                consumed = in_end
                cmd_indent = min(kw_col, _line_indent_of(stripped, pos))
                end_off, is_mut = _find_in_governed_end(
                    stripped, in_end, cmd_indent, quot_spans=quot_spans
                )
                if not is_mut and end_off <= in_end:
                    continue
                pushed = part_re.findall(name) if name else [""]
                base = len(stack)
                for part in pushed:
                    stack.append((kw if name else SCOPE_SECTION, part))
                pending_in.append([end_off, len(pushed), -2 if is_mut else -1, base])
                record(in_end)
                continue

            if name:
                for part in part_re.findall(name):
                    stack.append((kw, part))
            else:
                stack.append((SCOPE_SECTION, ""))
            record(name_end)

        flush_pending_up_to(n)
        for pos in mutual_starts:
            violations.append(f"line {line_of(pos)}: `mutual` block is never closed by `end`")
        return cls(offsets, namespaces, scopes_list, tuple(violations))


def track_namespaces(text: str, *, stripped: str | None = None) -> NamespaceTracker:
    """`NamespaceTracker.from_source(text, stripped=stripped)`."""
    return NamespaceTracker.from_source(text, stripped=stripped)
