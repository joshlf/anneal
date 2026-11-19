#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Validate and synchronize the hermetic Miri differential test corpus.

This script checks three invariants for `tests/miri-diff/`:

1. Manifest <-> Corpus consistency (`--check-manifest`, always enabled):
   Verifies that the `[[tests]]` entries in `tests/miri-diff/manifest.toml`
   list, in order, exactly the zero-argument `pub fn <name>()` items of
   `tests/miri-diff/corpus/src/lib.rs` other than `helper_add_ten` and the
   items that a `const __ANNEAL_MODEL_<name>: &str = "<name>"` marker declares
   as model items, that every entry has a dispatch arm in
   `tests/miri-diff/corpus/examples/miri_eval.rs`, that every
   `miri_verdict = "ub"` entry records a valid `miri_ub_span`, that all
   `upstream_path` values are clean relative paths (`tests/pass/...`,
   `tests/panic/...`, `tests/fail/...`), and that all `[tests.known_anneal_bug]`
   entries are marked `status = "open_bug"` with either `observed_anneal_tag`
   diverging from `miri_verdict` or `bug_class = "ub_location_mismatch"` whose
   `observed_anneal_ub_span` does not contain `miri_ub_span`.

2. Upstream public Miri checkout verification (`--miri-tests-dir <path>`):
   When pointed at a local clone of `https://github.com/rust-lang/rust`
   (`src/tools/miri/tests`) or `https://github.com/rust-lang/miri` (`tests`)
   at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, verifies the upstream
   suite layout (`pass/`, `panic/`, `fail/`).

3. Live Miri oracle execution (`--eval-miri`):
   Compiles `tests/miri-diff/corpus` and runs `miri -Zmiri-tree-borrows` on
   every test entry via `examples/miri_eval.rs`, asserting that live Miri
   produces the exact `miri_verdict` and (for `"ub"` entries) `miri_ub_span`
   recorded in `manifest.toml`.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib


def parse_args() -> argparse.Namespace:
    script_dir = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=script_dir / "manifest.toml",
        help="Path to tests/miri-diff/manifest.toml",
    )
    parser.add_argument(
        "--corpus-dir",
        type=Path,
        default=script_dir / "corpus",
        help="Path to tests/miri-diff/corpus",
    )
    parser.add_argument(
        "--miri-tests-dir",
        type=Path,
        default=os.environ.get("MIRI_TESTS_DIR"),
        help=(
            "Optional path to a checkout of upstream Miri tests "
            "(e.g. <rust-checkout>/src/tools/miri/tests or <miri-checkout>/tests)"
        ),
    )
    parser.add_argument(
        "--eval-miri",
        action="store_true",
        help=(
            "Run live Miri on all corpus tests and verify every miri_verdict "
            "and miri_ub_span in manifest.toml"
        ),
    )
    parser.add_argument(
        "--rustc-bin",
        type=Path,
        default=None,
        help="Explicit path to rustc (defaults to nightly-2026-06-01 rustc in ~/.rustup)",
    )
    parser.add_argument(
        "--miri-bin",
        type=Path,
        default=None,
        help="Explicit path to miri driver (defaults to nightly-2026-06-01 miri in ~/.rustup)",
    )
    parser.add_argument(
        "--miri-sysroot",
        type=Path,
        default=None,
        help="Explicit path to Miri sysroot (defaults to ~/.cache/miri)",
    )
    return parser.parse_args()


def resolve_default_toolchain_bin(tool_name: str) -> Path:
    home = Path.home()
    candidates = sorted(
        home.glob(f".rustup/toolchains/nightly-2026-06-01-*/bin/{tool_name}")
    )
    if candidates:
        return candidates[0]
    return Path(tool_name)


def parse_rustc_pos(raw: str) -> tuple[str, int, int]:
    parts = raw.strip().rstrip(":").rsplit(":", 2)
    if len(parts) != 3:
        raise ValueError(f"Invalid source position '{raw}'; expected <file>:<line>:<col>")
    file_part, line_str, col_str = parts[0].strip(), parts[1].strip(), parts[2].strip()
    if not file_part:
        raise ValueError(f"Empty file in source position '{raw}'")
    line = int(line_str)
    col = int(col_str)
    if line <= 0 or col <= 0:
        raise ValueError(f"Non-positive line/col in source position '{raw}'")
    return file_part, line, col


def parse_anneal_span(raw: str) -> tuple[str, int, int, int, int]:
    trimmed = raw.strip()
    if ": " not in trimmed:
        raise ValueError(
            f"Invalid Anneal span '{raw}'; expected '<file>:<sline>:<scol>: <eline>:<ecol>'"
        )
    left, right = trimmed.split(": ", 1)
    file_part, start_line, start_col = parse_rustc_pos(left)
    end_parts = right.strip().split(":")
    if len(end_parts) != 2:
        raise ValueError(f"Invalid Anneal span end '{raw}'")
    end_line = int(end_parts[0].strip())
    end_col = int(end_parts[1].strip())
    if end_line <= 0 or end_col <= 0:
        raise ValueError(f"Non-positive end line/col in Anneal span '{raw}'")
    return file_part, start_line, start_col, end_line, end_col


def normalize_file(path_str: str) -> str:
    s = path_str.replace("\\", "/").strip()
    if s.startswith("./"):
        s = s[2:]
    return s


def files_match(a: str, b: str) -> bool:
    na = normalize_file(a)
    nb = normalize_file(b)
    if not na or not nb:
        return False
    return na == nb or na.endswith("/" + nb) or nb.endswith("/" + na)


def span_contains_pos(
    span: tuple[str, int, int, int, int], pos: tuple[str, int, int]
) -> bool:
    s_file, s_line, s_col, e_line, e_col = span
    p_file, p_line, p_col = pos
    if not files_match(s_file, p_file):
        return False
    return (s_line, s_col) <= (p_line, p_col) <= (e_line, e_col)


def is_stdlib_or_driver_path(path_str: str) -> bool:
    s = normalize_file(path_str)
    return (
        "/.rustup/" in s
        or "/library/core/" in s
        or "/library/std/" in s
        or "/library/alloc/" in s
        or s.endswith("miri_eval.rs")
    )


def extract_ub_span_from_stderr(stderr: str) -> str:
    idx = stderr.find("error: Undefined Behavior:")
    if idx < 0:
        raise RuntimeError(f"Missing 'error: Undefined Behavior:' header in:\n{stderr}")
    after = stderr[idx:]
    arrows: list[str] = []
    backtraces: list[str] = []
    for raw_line in after.splitlines()[1:]:
        trimmed = raw_line.strip()
        if trimmed.startswith("warning:") or trimmed.startswith("error: aborting"):
            break
        if "-->" in trimmed:
            cand = trimmed.split("-->", 1)[1].strip()
            try:
                parse_rustc_pos(cand)
                arrows.append(cand)
            except ValueError:
                pass
        elif trimmed.startswith("= note:") and " at " in trimmed:
            cand = trimmed.rsplit(" at ", 1)[1].strip()
            try:
                parse_rustc_pos(cand)
                backtraces.append(cand)
            except ValueError:
                pass
    for a in arrows:
        f, _, _ = parse_rustc_pos(a)
        if not is_stdlib_or_driver_path(f):
            return a
    for b in backtraces:
        f, _, _ = parse_rustc_pos(b)
        if not is_stdlib_or_driver_path(f):
            return b
    if arrows:
        return arrows[0]
    if backtraces:
        return backtraces[0]
    raise RuntimeError(f"Could not extract UB source span from Miri stderr:\n{stderr}")


_CHAR_LIT_RE = re.compile(
    r"b?'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F_]+\}|.)|[^'\\\n])'"
)
_RAW_STR_START_RE = re.compile(r'(?:b|c)?r(#*)"')


def _strip_rust_comments(src: str, *, blank_strings: bool = False) -> str:
    """Strip Rust line and nested block comments while preserving line structure.

    Handles cooked strings (`"..."`, `b"..."`, `c"..."`), raw strings
    (`r#"..."#`, `br#"..."#`, `cr#"..."#`), and char literals. When
    ``blank_strings`` is True, string literal interiors are also replaced with
    spaces (keeping outer quotes and newlines) so string contents cannot
    masquerade as top-level Rust items or markers.
    """
    out: list[str] = []
    n = len(src)
    i = 0
    while i < n:
        ch = src[i]
        if ch == "/" and i + 1 < n and src[i + 1] == "/":
            i += 2
            out.append("  ")
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if ch == "/" and i + 1 < n and src[i + 1] == "*":
            depth = 1
            i += 2
            out.append("  ")
            while i < n and depth > 0:
                if src[i] == "/" and i + 1 < n and src[i + 1] == "*":
                    depth += 1
                    out.append("  ")
                    i += 2
                elif src[i] == "*" and i + 1 < n and src[i + 1] == "/":
                    depth -= 1
                    out.append("  ")
                    i += 2
                else:
                    out.append("\n" if src[i] == "\n" else " ")
                    i += 1
            continue
        if i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_"):
            raw_m = _RAW_STR_START_RE.match(src, i)
            if raw_m is not None:
                hashes = raw_m.group(1)
                closing = '"' + hashes
                out.append(raw_m.group(0))
                i = raw_m.end()
                end_idx = src.find(closing, i)
                body_end = n if end_idx < 0 else end_idx
                body = src[i:body_end]
                if blank_strings:
                    out.append("".join("\n" if c == "\n" else " " for c in body))
                else:
                    out.append(body)
                if end_idx >= 0:
                    out.append(closing)
                    i = end_idx + len(closing)
                else:
                    i = n
                continue
        if ch == '"' or (
            ch in ("b", "c")
            and i + 1 < n
            and src[i + 1] == '"'
            and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_"))
        ):
            if ch in ("b", "c"):
                out.append(ch + '"')
                i += 2
            else:
                out.append('"')
                i += 1
            while i < n:
                c = src[i]
                if c == "\\":
                    esc = src[i : min(i + 2, n)]
                    if blank_strings:
                        out.append("".join("\n" if ec == "\n" else " " for ec in esc))
                    else:
                        out.append(esc)
                    i += len(esc)
                elif c == '"':
                    out.append('"')
                    i += 1
                    break
                else:
                    out.append("\n" if c == "\n" else (" " if blank_strings else c))
                    i += 1
            continue
        if ch == "'" or (
            ch == "b"
            and i + 1 < n
            and src[i + 1] == "'"
            and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_"))
        ):
            cm = _CHAR_LIT_RE.match(src, i)
            if cm is not None:
                lit = cm.group(0)
                if blank_strings:
                    prefix_len = 2 if lit.startswith("b'") else 1
                    inner_len = len(lit) - prefix_len - 1
                    out.append(lit[:prefix_len] + (" " * inner_len) + "'")
                else:
                    out.append(lit)
                i = cm.end()
                continue
        out.append(ch)
        i += 1
    return "".join(out)


def _advance_rust_literal(src: str, i: int) -> int | None:
    """If ``src[i:]`` begins a raw string, cooked string, or char literal, return
    its end index; otherwise return ``None``.
    """
    n = len(src)
    ch = src[i]
    at_word_start = i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_")
    if at_word_start:
        raw_m = _RAW_STR_START_RE.match(src, i)
        if raw_m is not None:
            closing = '"' + raw_m.group(1)
            end_idx = src.find(closing, raw_m.end())
            return n if end_idx < 0 else end_idx + len(closing)
    if ch == '"' or (
        ch in ("b", "c") and i + 1 < n and src[i + 1] == '"' and at_word_start
    ):
        k = i + (2 if ch in ("b", "c") else 1)
        while k < n:
            if src[k] == "\\":
                k = min(k + 2, n)
            elif src[k] == '"':
                return k + 1
            else:
                k += 1
        return n
    if ch == "'" or (ch == "b" and i + 1 < n and src[i + 1] == "'" and at_word_start):
        cm = _CHAR_LIT_RE.match(src, i)
        if cm is not None:
            return cm.end()
    return None


def _mask_nested_blocks_and_attrs(clean_src: str) -> str:
    """Blank `{ ... }` bodies (`brace_depth >= 1`), top-level `#[...]`/`#![...]`
    attributes, and top-level `macro!(...)`/`macro![...]` bodies in
    comment-stripped Rust source while keeping outer `{`/`}` and string/char
    literals at depth 0 intact.
    """
    out: list[str] = []
    n = len(clean_src)
    i = 0
    brace_depth = 0
    while i < n:
        ch = clean_src[i]
        # Skip string / raw-string / char literals at any depth so braces or
        # brackets inside literals never skew delimiter tracking.
        lit_end = _advance_rust_literal(clean_src, i)
        if lit_end is not None:
            seg = clean_src[i:lit_end]
            if brace_depth == 0:
                out.append(seg)
            else:
                out.append("".join("\n" if c == "\n" else " " for c in seg))
            i = lit_end
            continue
        if brace_depth == 0 and ch == "#":
            j = i + 1
            while j < n and clean_src[j] in (" ", "\t"):
                j += 1
            if j < n and clean_src[j] == "!":
                j += 1
                while j < n and clean_src[j] in (" ", "\t"):
                    j += 1
            if j < n and clean_src[j] == "[":
                bracket_depth = 1
                k = j + 1
                while k < n and bracket_depth > 0:
                    inner_lit_end = _advance_rust_literal(clean_src, k)
                    if inner_lit_end is not None:
                        k = inner_lit_end
                        continue
                    kc = clean_src[k]
                    if kc == "[":
                        bracket_depth += 1
                    elif kc == "]":
                        bracket_depth -= 1
                    k += 1
                seg = clean_src[i:k]
                out.append("".join("\n" if c == "\n" else " " for c in seg))
                i = k
                continue
        # Mask top-level `ident!(...)` / `ident![...]` macro invocation bodies so
        # tokens inside bracketed/parenthesized macros cannot masquerade as items.
        if (
            brace_depth == 0
            and ch == "!"
            and i > 0
            and (clean_src[i - 1].isalnum() or clean_src[i - 1] == "_" or clean_src[i - 1] in (" ", "\t"))
        ):
            p = i - 1
            while p >= 0 and clean_src[p] in (" ", "\t"):
                p -= 1
            if p >= 0 and (clean_src[p].isalnum() or clean_src[p] == "_"):
                j = i + 1
                while j < n and clean_src[j] in (" ", "\t", "\n", "\r"):
                    j += 1
                if j < n and clean_src[j] in ("(", "["):
                    open_d = clean_src[j]
                    close_d = ")" if open_d == "(" else "]"
                    d = 1
                    k = j + 1
                    while k < n and d > 0:
                        inner_lit_end = _advance_rust_literal(clean_src, k)
                        if inner_lit_end is not None:
                            k = inner_lit_end
                            continue
                        if clean_src[k] == open_d:
                            d += 1
                        elif clean_src[k] == close_d:
                            d -= 1
                        k += 1
                    out.append("!")
                    seg = clean_src[i + 1 : k]
                    out.append("".join("\n" if c == "\n" else " " for c in seg))
                    i = k
                    continue
        if ch == "{":
            if brace_depth == 0:
                out.append("{")
            else:
                out.append(" ")
            brace_depth += 1
            i += 1
            continue
        if ch == "}":
            if brace_depth > 0:
                brace_depth -= 1
            out.append("}" if brace_depth == 0 else " ")
            i += 1
            continue
        if brace_depth > 0:
            out.append("\n" if ch == "\n" else " ")
        else:
            out.append(ch)
        i += 1
    return "".join(out)


_TOP_PREFIX = r"(?:^|[;}])\s*"
_FN_QUALS = r"(?:const\s+|unsafe\s+|extern(?:\s+(?:(?:b|c)?r#*)?\"[^\"]*\"#*)?\s+)*"


def check_manifest_and_corpus(manifest_path: Path, corpus_dir: Path) -> dict:
    with manifest_path.open("rb") as f:
        manifest = tomllib.load(f)

    if manifest.get("schema_version") != 1:
        raise ValueError(f"Unsupported schema_version: {manifest.get('schema_version')}")

    lib_rs = (corpus_dir / "src" / "lib.rs").read_text(encoding="utf-8")
    eval_rs = (corpus_dir / "examples" / "miri_eval.rs").read_text(encoding="utf-8")
    clean_lib = _strip_rust_comments(lib_rs, blank_strings=False)
    clean_lib_no_str = _strip_rust_comments(lib_rs, blank_strings=True)
    top_lib = _mask_nested_blocks_and_attrs(clean_lib)
    top_lib_no_str = _mask_nested_blocks_and_attrs(clean_lib_no_str)
    clean_eval = _strip_rust_comments(eval_rs, blank_strings=False)
    clean_eval_no_str = _strip_rust_comments(eval_rs, blank_strings=True)

    # A `const __ANNEAL_MODEL_<name>: &str = "<name>";` (or `: () = ();`) marker
    # makes `<name>` a model item (an intra-crate callee or a static), never a
    # manifest test, matching `trusted/rustc-capture` (`specs.rs`) and
    # `crates/anneal-difftest/src/mutators_miri.rs`.
    raw_marker_names = re.findall(
        _TOP_PREFIX
        + r"(?:pub(?:\s*\([^)]*\))?\s+)?const\s+__ANNEAL_MODEL_([A-Za-z0-9_]+)\b",
        top_lib_no_str,
    )
    seen_markers: set[str] = set()
    dup_markers: set[str] = set()
    for m_name in raw_marker_names:
        if m_name in seen_markers:
            dup_markers.add(m_name)
        seen_markers.add(m_name)
    if dup_markers:
        raise ValueError(
            "corpus/src/lib.rs declares duplicate __ANNEAL_MODEL_* markers: "
            f"{sorted(dup_markers)}"
        )

    parsed_markers: dict[str, tuple[str, str]] = {}
    for m in re.finditer(
        _TOP_PREFIX
        + r"(?:pub(?:\s*\([^)]*\))?\s+)?const\s+__ANNEAL_MODEL_([A-Za-z0-9_]+)\s*:\s*([^=;]+?)\s*=\s*([^;]+?)\s*;",
        top_lib,
    ):
        # Guard against `; pub const __ANNEAL_MODEL_...` text inside a top-level
        # string literal in `top_lib` overwriting a real marker declaration.
        if "const" not in top_lib_no_str[m.start() : m.start(2)]:
            continue
        m_name = m.group(1)
        m_ty = re.sub(r"\s+", "", m.group(2))
        m_val = m.group(3).strip()
        parsed_markers[m_name] = (m_ty, m_val)

    mismatched_markers: list[str] = []
    for m_name in sorted(seen_markers):
        entry_tv = parsed_markers.get(m_name)
        if entry_tv is None:
            mismatched_markers.append(m_name)
            continue
        m_ty, m_val = entry_tv
        if m_ty in ("&str", "&'staticstr"):
            raw_val_m = re.fullmatch(r'r(#*)"([^"]*)"\1', m_val)
            str_ok = (m_val == f'"{m_name}"') or (
                raw_val_m is not None and raw_val_m.group(2) == m_name
            )
            if not str_ok:
                mismatched_markers.append(m_name)
        elif m_ty == "()":
            if re.sub(r"\s+", "", m_val) != "()":
                mismatched_markers.append(m_name)
        else:
            mismatched_markers.append(m_name)
    if mismatched_markers:
        raise ValueError(
            "corpus/src/lib.rs declares __ANNEAL_MODEL_<name> markers whose type/value "
            f"is neither `&str = \"<name>\"` nor `() = ()`: {mismatched_markers}"
        )

    model_names = seen_markers
    item_names = {
        ident
        for ident in re.findall(
            _TOP_PREFIX
            + r"(?:pub(?:\s*\([^)]*\))?\s+)?"
            + _FN_QUALS
            + r"(?:fn|const|static(?:\s+mut)?|struct|enum|union|type)\s+([A-Za-z0-9_]+)\b",
            top_lib_no_str,
        )
        if not ident.startswith("__ANNEAL_MODEL_")
    }
    stale_markers = sorted(model_names - item_names)
    if stale_markers:
        raise ValueError(
            "corpus/src/lib.rs declares __ANNEAL_MODEL_* markers that name no "
            f"top-level item: {stale_markers}"
        )

    def _after_optional_generics(src: str, pos: int) -> int:
        n = len(src)
        while pos < n and src[pos].isspace():
            pos += 1
        if pos >= n or src[pos] != "<":
            return pos
        gdepth = pdepth = bdepth = cdepth = 0
        i = pos
        while i < n:
            if src[i : i + 2] == "->":
                i += 2
                continue
            ch = src[i]
            if ch == "(":
                pdepth += 1
            elif ch == ")":
                pdepth = max(0, pdepth - 1)
            elif ch == "[":
                bdepth += 1
            elif ch == "]":
                bdepth = max(0, bdepth - 1)
            elif ch == "{":
                cdepth += 1
            elif ch == "}":
                cdepth = max(0, cdepth - 1)
            elif ch == "<" and pdepth == 0 and bdepth == 0 and cdepth == 0:
                gdepth += 1
            elif ch == ">" and pdepth == 0 and bdepth == 0 and cdepth == 0:
                gdepth -= 1
                if gdepth == 0:
                    i += 1
                    while i < n and src[i].isspace():
                        i += 1
                    return i
            i += 1
        return pos

    restricted_zero_arg_fns: list[str] = []
    for m in re.finditer(
        _TOP_PREFIX + r"pub\s*\([^)]*\)\s+" + _FN_QUALS + r"fn\s+([A-Za-z0-9_]+)\b",
        top_lib_no_str,
    ):
        name = m.group(1)
        if name == "helper_add_ten" or name in model_names:
            continue
        after_gen = _after_optional_generics(top_lib_no_str, m.end())
        if re.match(r"\(\s*\)", top_lib_no_str[after_gen:]):
            restricted_zero_arg_fns.append(name)
    restricted_zero_arg_fns.sort()
    if restricted_zero_arg_fns:
        raise ValueError(
            "corpus/src/lib.rs declares non-exported `pub(...)` zero-arg functions "
            "without `__ANNEAL_MODEL_*` markers (not callable from examples/miri_eval.rs): "
            f"{restricted_zero_arg_fns}"
        )

    fn_names_in_lib = [
        m.group(1)
        for m in re.finditer(
            _TOP_PREFIX + r"pub\s+" + _FN_QUALS + r"fn\s+([A-Za-z0-9_]+)\s*\(\s*\)",
            top_lib_no_str,
        )
        if m.group(1) != "helper_add_ten" and m.group(1) not in model_names
    ]
    all_unmarked_top_fns = [
        m.group(1)
        for m in re.finditer(
            _TOP_PREFIX
            + r"(?:pub(?:\s*\([^)]*\))?\s+)?"
            + _FN_QUALS
            + r"fn\s+([A-Za-z0-9_]+)\b",
            top_lib_no_str,
        )
        if m.group(1) != "helper_add_ten" and m.group(1) not in model_names
    ]
    rogue_top_fns = sorted(set(all_unmarked_top_fns) - set(fn_names_in_lib))
    if rogue_top_fns:
        raise ValueError(
            "corpus/src/lib.rs declares top-level functions (private, parameterized, "
            "`pub(...)`, or generic) without `__ANNEAL_MODEL_*` markers: "
            f"{rogue_top_fns}"
        )

    tests = manifest.get("tests", [])
    manifest_names = [t["name"] for t in tests]
    seen_manifest: set[str] = set()
    dup_manifest: set[str] = set()
    for name in manifest_names:
        if name in seen_manifest:
            dup_manifest.add(name)
        seen_manifest.add(name)
    if dup_manifest:
        raise ValueError(
            f"manifest.toml declares duplicate [[tests]] names: {sorted(dup_manifest)}"
        )
    if manifest_names != fn_names_in_lib:
        missing_in_manifest = set(fn_names_in_lib) - set(manifest_names)
        missing_in_lib = set(manifest_names) - set(fn_names_in_lib)
        raise ValueError(
            f"Manifest test list does not match corpus/src/lib.rs: "
            f"missing_in_manifest={sorted(missing_in_manifest)}, "
            f"missing_in_lib={sorted(missing_in_lib)}"
        )

    eval_arms: list[str] = []
    for m in re.finditer(r'(r(#*))?"([^"]+)"(#*)\s*=>', clean_eval):
        if m.start() > 0 and (
            clean_eval[m.start() - 1].isalnum() or clean_eval[m.start() - 1] == "_"
        ):
            continue
        is_raw = m.group(1) is not None
        open_hashes = m.group(2) or ""
        arm_name = m.group(3)
        close_hashes = m.group(4)
        if (not is_raw and close_hashes) or (is_raw and open_hashes != close_hashes):
            continue
        prefix = f"r{open_hashes}" if is_raw else ""
        expected_masked = f'{prefix}"' + (" " * len(arm_name)) + f'"{close_hashes}'
        if (
            clean_eval_no_str[m.start() : m.end(4)] == expected_masked
            and clean_eval_no_str[m.end() - 2 : m.end()] == "=>"
        ):
            eval_arms.append(arm_name)
    seen_eval_arms: set[str] = set()
    dup_eval_arms: set[str] = set()
    for arm in eval_arms:
        if arm in seen_eval_arms:
            dup_eval_arms.add(arm)
        seen_eval_arms.add(arm)
    if dup_eval_arms:
        raise ValueError(
            "corpus/examples/miri_eval.rs declares duplicate dispatch arms: "
            f"{sorted(dup_eval_arms)}"
        )
    extra_eval_arms = sorted(seen_eval_arms - set(manifest_names))
    if extra_eval_arms:
        raise ValueError(
            "corpus/examples/miri_eval.rs has dispatch arms absent from manifest.toml "
            f"(e.g. orphaned or model-marked items): {extra_eval_arms}"
        )

    allowed_test_keys = {
        "name",
        "category",
        "upstream_path",
        "miri_verdict",
        "miri_ub_span",
        "fuel",
        "known_anneal_bug",
    }
    allowed_bug_keys = {
        "status",
        "bug_class",
        "observed_anneal_tag",
        "observed_anneal_ub_span",
        "suspected_component",
        "summary",
    }

    for entry in tests:
        name = entry["name"]
        unknown_test = sorted(set(entry.keys()) - allowed_test_keys)
        if unknown_test:
            raise ValueError(
                f"Test '{name}' has unknown keys in [[tests]]: {unknown_test}"
            )
        upstream_path = entry["upstream_path"]
        if not upstream_path.startswith(("tests/pass/", "tests/panic/", "tests/fail/")):
            raise ValueError(
                f"Test '{name}' has invalid upstream_path '{upstream_path}'; "
                "must start with tests/pass/, tests/panic/, or tests/fail/"
            )
        if name not in seen_eval_arms:
            raise ValueError(
                f"Test '{name}' is missing a dispatch arm in corpus/examples/miri_eval.rs"
            )

        verdict = entry["miri_verdict"]
        miri_ub_span_raw = entry.get("miri_ub_span")
        miri_pos = None
        if verdict == "ub":
            if not miri_ub_span_raw:
                raise ValueError(
                    f"Test '{name}' has miri_verdict = 'ub' but is missing 'miri_ub_span'"
                )
            miri_pos = parse_rustc_pos(miri_ub_span_raw)
        elif miri_ub_span_raw is not None:
            raise ValueError(
                f"Test '{name}' has miri_ub_span '{miri_ub_span_raw}' "
                f"but miri_verdict is '{verdict}'"
            )

        bug = entry.get("known_anneal_bug")
        if bug is not None:
            unknown_bug = sorted(set(bug.keys()) - allowed_bug_keys)
            if unknown_bug:
                raise ValueError(
                    f"Test '{name}' has unknown keys in [tests.known_anneal_bug]: "
                    f"{unknown_bug}"
                )
            if bug.get("status") != "open_bug":
                raise ValueError(
                    f"Test '{name}' known_anneal_bug must have status = 'open_bug'"
                )
            bug_class = bug.get("bug_class", "")
            obs_tag = bug.get("observed_anneal_tag")
            obs_span_raw = bug.get("observed_anneal_ub_span")
            if obs_span_raw is not None and obs_tag != "ub":
                raise ValueError(
                    f"Test '{name}' has observed_anneal_ub_span '{obs_span_raw}' "
                    f"but observed_anneal_tag is '{obs_tag}' (expected 'ub')"
                )
            obs_span = parse_anneal_span(obs_span_raw) if obs_span_raw else None

            if bug_class == "ub_location_mismatch":
                if verdict != "ub" or obs_tag != "ub" or obs_span is None or miri_pos is None:
                    raise ValueError(
                        f"Test '{name}' with bug_class = 'ub_location_mismatch' requires "
                        "miri_verdict = 'ub', observed_anneal_tag = 'ub', miri_ub_span, "
                        "and observed_anneal_ub_span"
                    )
                if span_contains_pos(obs_span, miri_pos):
                    raise ValueError(
                        f"Test '{name}' has stale ub_location_mismatch: "
                        f"observed_anneal_ub_span '{obs_span_raw}' contains "
                        f"miri_ub_span '{miri_ub_span_raw}'"
                    )
            elif obs_tag == verdict:
                raise ValueError(
                    f"Test '{name}' has stale known_anneal_bug: "
                    f"observed_anneal_tag == miri_verdict ({verdict})"
                )

    return manifest


def check_upstream_miri_dir(miri_tests_dir: Path, manifest: dict) -> None:
    root = miri_tests_dir.resolve()
    if (root / "tests" / "pass").is_dir():
        tests_root = root / "tests"
    elif (root / "pass").is_dir():
        tests_root = root
    else:
        raise ValueError(
            f"Directory {root} does not contain Miri's pass/, panic/, and fail/ subdirectories"
        )

    for subdir in ("pass", "panic", "fail"):
        if not (tests_root / subdir).is_dir():
            raise ValueError(f"Missing expected Miri test subdirectory: {tests_root / subdir}")

    verified_files = 0
    for entry in manifest["tests"]:
        rel = entry["upstream_path"].removeprefix("tests/")
        candidate = tests_root / rel
        if candidate.is_file():
            verified_files += 1

    print(
        f"Verified upstream Miri test directory structure at {tests_root} "
        f"({verified_files}/{len(manifest['tests'])} exact upstream file paths present)."
    )


def eval_miri_oracle(
    corpus_dir: Path,
    manifest: dict,
    rustc_bin: Path,
    miri_bin: Path,
    miri_sysroot: Path,
) -> None:
    if not (miri_sysroot / "lib" / "rustlib").is_dir():
        raise RuntimeError(
            f"Miri sysroot is missing lib/rustlib at {miri_sysroot}; "
            "missing Miri sysroot is a hard error"
        )

    lib_rs = Path("src/lib.rs")
    eval_rs = Path("examples/miri_eval.rs")
    miri_flags = manifest.get("miri_flags", ["-Zmiri-tree-borrows"])

    with tempfile.TemporaryDirectory(prefix="anneal-miri-oracle-") as tmp:
        rlib_path = Path(tmp) / "libmiri_diff_corpus.rlib"
        compile_cmd = [
            str(rustc_bin),
            "--sysroot",
            str(miri_sysroot),
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=miri_diff_corpus",
            "-Zalways-encode-mir",
            "-Zmir-opt-level=0",
            "-C",
            "debug-assertions=off",
            "-C",
            "overflow-checks=on",
            str(lib_rs),
            "-o",
            str(rlib_path),
        ]
        subprocess.run(compile_cmd, cwd=corpus_dir, check=True)

        ub_span_checked = 0
        for entry in manifest["tests"]:
            name = entry["name"]
            expected = entry["miri_verdict"]
            expected_ub_span = entry.get("miri_ub_span")
            env = os.environ.copy()
            env["MIRI_DIFF_TEST"] = name
            cmd = [
                str(miri_bin),
                "--sysroot",
                str(miri_sysroot),
                *miri_flags,
                "-Zmiri-disable-isolation",
                "--edition=2024",
                str(eval_rs),
                "--extern",
                f"miri_diff_corpus={rlib_path}",
            ]
            proc = subprocess.run(
                cmd, cwd=corpus_dir, env=env, capture_output=True, text=True
            )
            stdout = proc.stdout.strip()
            stderr = proc.stderr

            actual_ub_span = None
            if proc.returncode == 0:
                actual = None
                for line in stdout.splitlines():
                    if line.startswith("MIRI_PASS:"):
                        actual = "pass:" + line.removeprefix("MIRI_PASS:")
                        break
                if actual is None:
                    raise RuntimeError(
                        f"Miri succeeded on '{name}' without MIRI_PASS line:\n{stdout}\n{stderr}"
                    )
            elif "error: Undefined Behavior:" in stderr:
                actual = "ub"
                actual_ub_span = extract_ub_span_from_stderr(stderr)
            elif "panicked at" in stderr or "explicit panic" in stderr:
                actual = "panic"
            else:
                raise RuntimeError(
                    f"Unexpected Miri failure on '{name}' (exit {proc.returncode}):\n{stderr}"
                )

            if actual != expected:
                raise AssertionError(
                    f"Miri oracle mismatch on '{name}': manifest expects '{expected}', "
                    f"live Miri produced '{actual}'"
                )
            if expected == "ub":
                if actual_ub_span != expected_ub_span:
                    raise AssertionError(
                        f"Miri UB span mismatch on '{name}': manifest expects "
                        f"'{expected_ub_span}', live Miri produced '{actual_ub_span}'"
                    )
                ub_span_checked += 1

    print(
        f"Live Miri oracle verified all {len(manifest['tests'])} corpus tests "
        f"(including {ub_span_checked} UB fault spans) with flags {miri_flags}."
    )


def main() -> int:
    args = parse_args()
    manifest = check_manifest_and_corpus(args.manifest, args.corpus_dir)
    bug_count = sum(1 for t in manifest["tests"] if "known_anneal_bug" in t)
    print(
        f"Validated {args.manifest.name}: {len(manifest['tests'])} tests "
        f"({len(manifest['tests']) - bug_count} matching Miri, "
        f"{bug_count} tracked open Anneal bugs)."
    )

    if args.miri_tests_dir is not None:
        check_upstream_miri_dir(args.miri_tests_dir, manifest)

    if args.eval_miri:
        rustc_bin = args.rustc_bin or resolve_default_toolchain_bin("rustc")
        miri_bin = args.miri_bin or resolve_default_toolchain_bin("miri")
        miri_sysroot = args.miri_sysroot or (Path.home() / ".cache" / "miri")
        eval_miri_oracle(args.corpus_dir, manifest, rustc_bin, miri_bin, miri_sysroot)

    return 0


if __name__ == "__main__":
    sys.exit(main())
