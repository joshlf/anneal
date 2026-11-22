#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Analyzes a large Lean 4 file's declaration DAG and proposes safe submodule splits."""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from typing import Any

DECL_START_RE = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+|partial\s+|@\[[^\]]+\]\s*)*"
    r"(inductive|structure|class|def|abbrev|theorem|instance)\s+([A-Za-z_][A-Za-z0-9_.']*)"
)
IDENT_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_.']*\b")
UNFOLD_OR_SIMP_RE = re.compile(r"\b(?:unfold\s+([A-Za-z_][A-Za-z0-9_.']*)|simp\s*\[([^\]]+)\])")


def analyze_lean_module(path: pathlib.Path, target_lines: int = 800) -> dict[str, Any]:
    lines = path.read_text(encoding="utf-8").splitlines()
    decls: list[dict[str, Any]] = []
    cur: dict[str, Any] | None = None

    for idx, line in enumerate(lines, start=1):
        m = DECL_START_RE.match(line)
        if m:
            if cur is not None:
                cur["end_line"] = idx - 1
                cur["line_count"] = cur["end_line"] - cur["start_line"] + 1
                decls.append(cur)
            cur = {
                "kind": m.group(1),
                "name": m.group(2),
                "start_line": idx,
                "end_line": idx,
                "body_lines": [line],
            }
        elif cur is not None:
            cur["body_lines"].append(line)

    if cur is not None:
        cur["end_line"] = len(lines)
        cur["line_count"] = cur["end_line"] - cur["start_line"] + 1
        decls.append(cur)

    known_names = {d["name"] for d in decls}
    for d in decls:
        text = "\n".join(d.pop("body_lines"))
        refs = sorted({
            tok for tok in IDENT_RE.findall(text)
            if tok in known_names and tok != d["name"]
        })
        eq1_targets: set[str] = set()
        for um in UNFOLD_OR_SIMP_RE.finditer(text):
            if um.group(1) and um.group(1) in known_names:
                eq1_targets.add(um.group(1))
            if um.group(2):
                for item in um.group(2).split(","):
                    tok = item.strip().lstrip("←").strip()
                    if tok in known_names:
                        eq1_targets.add(tok)
        d["internal_deps"] = refs
        d["eq1_realize_targets"] = sorted(eq1_targets)

    # Greedy contiguous chunking respecting `target_lines`
    chunks: list[dict[str, Any]] = []
    bucket: list[dict[str, Any]] = []
    bucket_lines = 0
    for d in decls:
        if bucket and bucket_lines + d["line_count"] > target_lines:
            chunks.append( summarize_chunk(len(chunks) + 1, bucket) )
            bucket = []
            bucket_lines = 0
        bucket.append(d)
        bucket_lines += d["line_count"]
    if bucket:
        chunks.append(summarize_chunk(len(chunks) + 1, bucket))

    decl_to_chunk = {
        nm: ch["chunk_index"]
        for ch in chunks
        for nm in ch["declarations"]
    }
    cross_chunk_eq1_hazards: list[dict[str, Any]] = []
    for d in decls:
        src_c = decl_to_chunk[d["name"]]
        for tgt in d["eq1_realize_targets"]:
            tgt_c = decl_to_chunk.get(tgt, src_c)
            if tgt_c != src_c:
                cross_chunk_eq1_hazards.append({
                    "consumer_decl": d["name"],
                    "consumer_chunk": src_c,
                    "target_def": tgt,
                    "target_chunk": tgt_c,
                    "advice": (
                        f"Replace `unfold {tgt}` / `simp [{tgt}]` with `dsimp only [{tgt}]` "
                        f"or prove `{tgt}_eq` in chunk {tgt_c} to prevent cross-module `.eq_1` diamond collisions."
                    ),
                })

    return {
        "file": str(path),
        "total_lines": len(lines),
        "declaration_count": len(decls),
        "target_lines_per_chunk": target_lines,
        "proposed_chunks": chunks,
        "cross_chunk_eq1_hazards": cross_chunk_eq1_hazards,
    }


def summarize_chunk(idx: int, bucket: list[dict[str, Any]]) -> dict[str, Any]:
    names = [d["name"] for d in bucket]
    name_set = set(names)
    ext_deps = sorted({
        dep for d in bucket for dep in d["internal_deps"] if dep not in name_set
    })
    return {
        "chunk_index": idx,
        "start_line": bucket[0]["start_line"],
        "end_line": bucket[-1]["end_line"],
        "line_span": bucket[-1]["end_line"] - bucket[0]["start_line"] + 1,
        "decl_count": len(bucket),
        "first_decl": names[0],
        "last_decl": names[-1],
        "declarations": names,
        "depends_on_earlier_decls": ext_deps,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", help="Path to `.lean` file to analyze.")
    parser.add_argument("--target-lines", type=int, default=800,
                        help="Target maximum lines per submodule chunk (default: 800).")
    parser.add_argument("--json", action="store_true", help="Emit JSON output.")
    args = parser.parse_args(argv)

    plan = analyze_lean_module(pathlib.Path(args.file), args.target_lines)
    if args.json:
        print(json.dumps(plan, indent=2))
    else:
        print(f"Module {plan['file']}: {plan['total_lines']} lines, "
              f"{plan['declaration_count']} declaration(s) -> "
              f"{len(plan['proposed_chunks'])} chunk(s):")
        for ch in plan["proposed_chunks"]:
            print(f"  Chunk {ch['chunk_index']}: L{ch['start_line']}-L{ch['end_line']} "
                  f"({ch['line_span']}L, {ch['decl_count']} decls: "
                  f"{ch['first_decl']} .. {ch['last_decl']})")
        if plan["cross_chunk_eq1_hazards"]:
            print(f"\nCross-chunk `.eq_1` / `realizeConst` hazards ({len(plan['cross_chunk_eq1_hazards'])}):")
            for hz in plan["cross_chunk_eq1_hazards"]:
                print(f"  - {hz['consumer_decl']} (chunk {hz['consumer_chunk']}) -> "
                      f"{hz['target_def']} (chunk {hz['target_chunk']}): {hz['advice']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
