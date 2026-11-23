#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Fast static Pass-1 TrustedBoundary & proof-health scanner for Lean 4 files."""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import sys
from typing import Any

LOCKED_INIT_MODULES: frozenset[str] = frozenset({
    "Init.BinderNameHint",
    "Init.Coe",
    "Init.Control.Basic",
    "Init.Control.Do",
    "Init.Control.Except",
    "Init.Control.Id",
    "Init.Control.MonadAttach",
    "Init.Control.Option",
    "Init.Control.State",
    "Init.Conv",
    "Init.Core",
    "Init.Data.Array.Basic",
    "Init.Data.Array.GetLit",
    "Init.Data.Array.Set",
    "Init.Data.BitVec.BasicAux",
    "Init.Data.ByteArray.Bootstrap",
    "Init.Data.Cast",
    "Init.Data.Char.Basic",
    "Init.Data.Fin.Basic",
    "Init.Data.Format.Basic",
    "Init.Data.Int.Basic",
    "Init.Data.List.Basic",
    "Init.Data.List.Notation",
    "Init.Data.List.ToArrayImpl",
    "Init.Data.Nat.Basic",
    "Init.Data.Nat.Bitwise.Basic",
    "Init.Data.Nat.Div.Basic",
    "Init.Data.NeZero",
    "Init.Data.Option.Basic",
    "Init.Data.Repr",
    "Init.Data.String.Bootstrap",
    "Init.Data.ToString.Basic",
    "Init.Data.UInt.BasicAux",
    "Init.Data.Zero",
    "Init.GetElem",
    "Init.Grind.Attr",
    "Init.Grind.Interactive",
    "Init.Grind.Tactics",
    "Init.Meta",
    "Init.Meta.Defs",
    "Init.MetaTypes",
    "Init.Notation",
    "Init.NotationExtra",
    "Init.Prelude",
    "Init.SimpLemmas",
    "Init.SizeOf",
    "Init.Syntax",
    "Init.Tactics",
    "Init.Util",
    "Init.WF",
    "Init.WFTactics",
})

BANNED_PASS1_TACTICS: dict[str, str] = {
    "omega": "Use Workbench.Pass1.LinearArith + scripts/farkas_cert_gen.py",
    "bv_decide": "Use Workbench.Pass1.BitTrieLrat or Anneal.BitVec",
    "native_decide": "Emits Lean.ofReduceBool / _native.* axioms; use decide or rfl",
    "grind": "Excluded from Pass-1 allowedTheoryTacticKinds",
    "rcases": "Use nested `cases` or pattern-matching theorems",
    "obtain": "Use `cases` with named constructors",
    "by_cases": "Case-split an explicit Bool check or Nat.lt_or_ge",
    "simp_all": "Use targeted `simp only [...]` or `dsimp only [...]` + `rw`",
    "conv": "Factor helper equality lemma instead of `conv`",
    "by_elab": "Metaprogramming tactics are forbidden in Pass 1",
    "run_tac": "Metaprogramming tactics are forbidden in Pass 1",
    "run_cmd": "Metaprogramming commands are forbidden in Pass 1",
}

BANNED_PASS1_COMMANDS: dict[str, str] = {
    "axiom": "Custom axioms are forbidden",
    "sorry": "Unfinished proof obligation (`sorry`)",
    "admit": "Unfinished proof obligation (`admit`)",
    "opaque": "`opaque` declarations are rejected in Pass 1",
    "partial": "`partial` definitions emit isPartial constants",
    "unsafe": "`unsafe` definitions are rejected by the kernel audit",
    "termination_by": "Well-founded recursion emits auxiliary defs; prefer @Nat.rec / structural recursion",
    "decreasing_by": "Well-founded recursion tactic block rejected in Pass 1",
    "macro": "Custom macros are forbidden in Pass 1",
    "macro_rules": "Custom macro_rules are forbidden in Pass 1",
    "elab": "Custom elaborators are forbidden in Pass 1",
    "syntax": "Custom syntax declarations are forbidden in Pass 1",
    "initialize": "Module initializers are forbidden in Pass 1",
    "builtin_initialize": "Builtin initializers are forbidden in Pass 1",
}


def strip_comments_and_strings(src: str) -> str:
    """Replaces comments and string contents with spaces, keeping newlines/columns."""
    out: list[str] = []
    i = 0
    n = len(src)
    block_depth = 0
    in_string = False

    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend([" ", " "])
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend([" ", " "])
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if in_string:
            if ch == "\\" and i + 1 < n:
                out.extend([" ", "\n" if nxt == "\n" else " "])
                i += 2
                continue
            if ch == '"':
                in_string = False
                out.append('"')
                i += 1
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if ch == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
            continue

        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend([" ", " "])
            i += 2
            continue

        if ch == '"':
            in_string = True
            out.append('"')
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def find_large_list_literals(masked: str, limit: int = 33) -> list[tuple[int, int, int]]:
    """Returns (line, col, count) for flat `[...]` literals with >= limit items."""
    hits: list[tuple[int, int, int]] = []
    # Track bracket stack: (kind, start_line, start_col, comma_count)
    stack: list[list[int | str]] = []
    line = 1
    col = 0
    for ch in masked:
        if ch == "\n":
            line += 1
            col = 0
            continue
        col += 1
        if ch in "([{":
            stack.append([ch, line, col, 0, 0])
        elif ch in ")]}":
            if stack:
                kind, s_line, s_col, commas, has_tok = stack.pop()
                if kind == "[" and ch == "]":
                    elem_count = (int(commas) + 1) if int(has_tok) else 0
                    if elem_count >= limit:
                        hits.append((int(s_line), int(s_col), elem_count))
        elif ch == ",":
            if stack and stack[-1][0] == "[":
                stack[-1][3] = int(stack[-1][3]) + 1
        elif not ch.isspace():
            if stack:
                stack[-1][4] = 1
    return hits


def line_col(masked: str, offset: int) -> tuple[int, int]:
    line = masked.count("\n", 0, offset) + 1
    last_nl = masked.rfind("\n", 0, offset)
    col = offset + 1 if last_nl == -1 else offset - last_nl
    return line, col


def is_default_pass1_path(path: pathlib.Path) -> bool:
    parts = set(path.parts)
    return bool(parts & {"Pass1", "theory", "correspondence"}) or path.name == "Pass1.lean"


def scan_file(
    path: pathlib.Path,
    force_pass1: bool,
    allow_import_prefixes: tuple[str, ...],
) -> list[dict[str, Any]]:
    raw = path.read_text(encoding="utf-8")
    masked = strip_comments_and_strings(raw)
    findings: list[dict[str, Any]] = []
    pass1 = force_pass1 or is_default_pass1_path(path)

    def add(severity: str, code: str, ln: int, col: int, msg: str) -> None:
        findings.append({
            "file": str(path),
            "line": ln,
            "column": col,
            "severity": severity,
            "code": code,
            "message": msg,
        })

    if pass1:
        if not re.match(r"\s*(?:module\s+)?prelude\b", masked):
            m_first = re.search(r"\S+", masked)
            ln, col = line_col(masked, m_first.start()) if m_first else (1, 1)
            add("error", "MISSING_PRELUDE", ln, col,
                "Pass-1 module must begin with `prelude` (or `module` then `prelude`) before imports.")

        for m in re.finditer(r"(?m)^\s*(?:public\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.']+)", masked):
            mod = m.group(1)
            if mod in LOCKED_INIT_MODULES:
                continue
            if any(mod == p.rstrip(".") or mod.startswith(p) for p in allow_import_prefixes):
                continue
            ln, col = line_col(masked, m.start(1))
            add("error", "DISALLOWED_IMPORT", ln, col,
                f"Import `{mod}` is outside the 51 locked Init.* foundation modules.")

        for m in re.finditer(r"\bnoncomputable\s+section\b", masked):
            ln, col = line_col(masked, m.start())
            add("error", "NONCOMPUTABLE_SECTION", ln, col,
                "`noncomputable section` is banned in Pass 1; mark individual definitions `noncomputable def`.")

        for m in re.finditer(r"#(eval|reduce|check)\b", masked):
            ln, col = line_col(masked, m.start())
            add("error", "BANNED_HASH_CMD", ln, col,
                f"`#{m.group(1)}` is forbidden in Pass-1 modules.")

        for m in re.finditer(r"\bset_option\b", masked):
            ln, col = line_col(masked, m.start())
            add("error", "BANNED_SET_OPTION", ln, col,
                "`set_option` is forbidden in Pass-1 modules.")

        for m in re.finditer(r"@\[\s*(implemented_by|extern|csimp)\b", masked):
            ln, col = line_col(masked, m.start())
            add("error", "BANNED_ATTR", ln, col,
                f"`@[{m.group(1)}]` compiler override attribute is forbidden.")

        for m in re.finditer(r"\+\s*(native|kernel)\b", masked):
            ln, col = line_col(masked, m.start())
            add("error", "BANNED_TACTIC_CONFIG", ln, col,
                f"Tactic configuration `+{m.group(1)}` is forbidden in Pass 1.")

        for m in re.finditer(r"(?<![A-Za-z0-9_.'])(decide!|rfl')(?![A-Za-z0-9_'])", masked):
            ln, col = line_col(masked, m.start())
            add("error", "BANNED_TACTIC", ln, col,
                f"`{m.group(1)}` is forbidden in Pass 1.")

        for kw, hint in BANNED_PASS1_TACTICS.items():
            pat = rf"(?<![A-Za-z0-9_.']){re.escape(kw)}(?![A-Za-z0-9_.'])"
            for m in re.finditer(pat, masked):
                ln, col = line_col(masked, m.start())
                add("error", "BANNED_TACTIC", ln, col, f"Banned Pass-1 tactic `{kw}`: {hint}")

        for kw, hint in BANNED_PASS1_COMMANDS.items():
            pat = rf"(?<![A-Za-z0-9_.']){re.escape(kw)}(?![A-Za-z0-9_.'])"
            for m in re.finditer(pat, masked):
                ln, col = line_col(masked, m.start())
                add("error", "BANNED_COMMAND", ln, col, f"Banned Pass-1 construct `{kw}`: {hint}")

        for ln, col, count in find_large_list_literals(masked):
            add("error", "LARGE_LIST_LITERAL", ln, col,
                f"List literal has {count} items (>= 33 expands to banned `%[...|...]` macro); chunk via `++`.")

    else:
        for kw in ("sorry", "admit"):
            pat = rf"(?<![A-Za-z0-9_.']){kw}(?![A-Za-z0-9_.'])"
            for m in re.finditer(pat, masked):
                ln, col = line_col(masked, m.start())
                add("warning", "OPEN_SORRY", ln, col, f"Open `{kw}` token.")

    # Advisory across Pass-1 files: bare `simp [foo]` (without `only`)
    if pass1:
        for m in re.finditer(r"(?<![A-Za-z0-9_.'])simp\s*\[", masked):
            ln, col = line_col(masked, m.start())
            add("warning", "BARE_SIMP_LIST", ln, col,
                "Prefer `simp only [...]` or `dsimp only [...]` to avoid realizing cross-module `.eq_1` diamonds.")

    findings.sort(key=lambda item: (item["file"], item["line"], item["column"], item["code"]))
    return findings


def collect_lean_files(targets: list[str]) -> list[pathlib.Path]:
    files: list[pathlib.Path] = []
    for raw in targets:
        p = pathlib.Path(raw)
        if p.is_file() and p.suffix == ".lean":
            files.append(p)
        elif p.is_dir():
            for root, dirs, filenames in os.walk(p, followlinks=False):
                dirs[:] = sorted(d for d in dirs if d not in {".lake", ".git", "target", "__pycache__"})
                for fn in sorted(filenames):
                    if fn.endswith(".lean"):
                        files.append(pathlib.Path(root) / fn)
    return files


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", help="Lean files or directories to scan.")
    parser.add_argument("--pass1", action="store_true",
                        help="Enforce strict Pass-1 TrustedBoundary rules on all scanned files.")
    parser.add_argument("--allow-import-prefix", action="append",
                        default=["Anneal.", "Trusted.", "Workbench.Pass1."],
                        help="Allowed non-Init module prefix in Pass-1 mode.")
    parser.add_argument("--strict-warnings", action="store_true",
                        help="Return exit code 1 on warnings as well as errors.")
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON.")
    args = parser.parse_args(argv)

    lean_files = collect_lean_files(args.paths)
    all_findings: list[dict[str, Any]] = []
    prefixes = tuple(args.allow_import_prefix)
    for lf in lean_files:
        all_findings.extend(scan_file(lf, args.pass1, prefixes))

    errors = [f for f in all_findings if f["severity"] == "error"]
    warnings = [f for f in all_findings if f["severity"] == "warning"]

    if args.json:
        print(json.dumps({
            "scanned_files": len(lean_files),
            "error_count": len(errors),
            "warning_count": len(warnings),
            "findings": all_findings,
        }, indent=2))
    else:
        for f in all_findings:
            print(f"[{f['severity'].upper()}] {f['file']}:{f['line']}:{f['column']} "
                  f"({f['code']}): {f['message']}")
        print(f"Scanned {len(lean_files)} Lean file(s): "
              f"{len(errors)} error(s), {len(warnings)} warning(s).")

    if errors or (args.strict_warnings and warnings):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
