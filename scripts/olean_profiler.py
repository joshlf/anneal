#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Profiles `.olean` artifact sizes and per-declaration `Lean.Expr` DAG/tree bloat."""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
from typing import Any

EXPR_PROFILER_LEAN = r"""import Lean
import {module}

open Lean

partial def exprStats (root : Expr) : Nat × Nat :=
  let cap := 10000000
  let rec go (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
    if let some cached := (← get).get? e then
      return cached
    let t ← match e with
      | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => pure 1
      | .mdata _ b | .proj _ _ b => do pure (Nat.min cap (1 + (← go b)))
      | .app f a => do pure (Nat.min cap (1 + (← go f) + (← go a)))
      | .lam _ ty body _ | .forallE _ ty body _ => do
        pure (Nat.min cap (1 + (← go ty) + (← go body)))
      | .letE _ ty val body _ => do
        pure (Nat.min cap (1 + (← go ty) + (← go val) + (← go body)))
    modify (·.insert e t)
    return t
  let (treeN, vis) := (go root).run {}
  (vis.size, treeN)

def main : IO Unit := do
  let env ← importModules #[{ module := `{module} }] {} 0
  let pfx := "{prefix}"
  let mut rows : Array (Nat × String × Nat × Nat × Nat) := #[]
  for (name, ci) in env.constants.map₁.toList do
    let s := name.toString
    if s == pfx || s.startsWith (pfx ++ ".") then
      let (td, tt) := exprStats ci.type
      let (vd, vt) := match ci.value? with
        | some v => exprStats v
        | none => (0, 0)
      let dag := td + vd
      let tree := tt + vt
      let refs := ci.getUsedConstantsAsSet.size
      rows := rows.push (dag, s, tree, td, refs)
  let sorted := rows.qsort (fun a b => a.1 > b.1)
  let top := (sorted.toList.take {top_n}).map (fun (dag, nm, tree, tyDag, refs) =>
    Json.mkObj [
      ("decl", toJson nm),
      ("total_dag_nodes", toJson dag),
      ("type_dag_nodes", toJson tyDag),
      ("total_tree_nodes_capped", toJson tree),
      ("direct_const_refs", toJson refs)
    ])
  IO.println (Json.arr top.toArray).compress
"""


def find_lean_wrapper(disable_wrapper: bool) -> list[str]:
    if disable_wrapper:
        return []
    for candidate in (
        os.environ.get("ANNEAL_LEAN_RUN"),
        str(pathlib.Path.home() / ".local" / "bin" / "anneal-lean-run"),
        shutil.which("anneal-lean-run"),
    ):
        if candidate and os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return [candidate, "--mode", "file", "--"]
    return []


def scan_olean_sizes(root: pathlib.Path, top_n: int) -> list[dict[str, Any]]:
    oleans: list[dict[str, Any]] = []
    search_root = root / ".lake" / "build" / "lib" if (root / ".lake").is_dir() else root
    if not search_root.exists():
        return oleans
    for dirpath, _, filenames in os.walk(search_root, followlinks=False):
        for fn in filenames:
            if fn.endswith(".olean"):
                fp = pathlib.Path(dirpath) / fn
                sz = fp.stat().st_size
                oleans.append({
                    "path": str(fp.relative_to(root) if fp.is_relative_to(root) else fp),
                    "bytes": sz,
                    "kib": round(sz / 1024.0, 2),
                })
    oleans.sort(key=lambda r: r["bytes"], reverse=True)
    return oleans[:top_n]


WORKBENCH_LEAN_DIR = pathlib.Path(__file__).resolve().parents[1] / "lean"


def resolve_standalone_lean() -> tuple[pathlib.Path, pathlib.Path]:
    if (WORKBENCH_LEAN_DIR / "lean-toolchain").is_file() and shutil.which("lake"):
        proc = subprocess.run(
            ["lake", "env", "which", "lean"],
            cwd=str(WORKBENCH_LEAN_DIR),
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode == 0 and proc.stdout.strip():
            lb = pathlib.Path(proc.stdout.strip()).resolve()
            pref = subprocess.run([str(lb), "--print-prefix"], capture_output=True, text=True, check=True)
            return lb, pathlib.Path(pref.stdout.strip()).resolve()
    which_lean = shutil.which("lean")
    if not which_lean:
        raise RuntimeError("Could not locate `lean` executable on PATH.")
    lb = pathlib.Path(which_lean).resolve()
    pref = subprocess.run([str(lb), "--print-prefix"], capture_output=True, text=True, check=True)
    return lb, pathlib.Path(pref.stdout.strip()).resolve()


def profile_module_exprs(
    lake_dir: pathlib.Path,
    module: str,
    prefix: str,
    top_n: int,
    disable_wrapper: bool,
    lean_paths: list[pathlib.Path] | None = None,
) -> list[dict[str, Any]]:
    src = (
        EXPR_PROFILER_LEAN
        .replace("{module}", module)
        .replace("{prefix}", prefix or module)
        .replace("{top_n}", str(top_n))
    )
    wrapper = find_lean_wrapper(disable_wrapper)
    extra_paths = [str(p.resolve()) for p in (lean_paths or [])]
    use_lake = (
        (lake_dir / "lakefile.toml").is_file() or (lake_dir / "lakefile.lean").is_file()
    )
    with tempfile.TemporaryDirectory(prefix="workbench-olean-prof-") as tmpdir:
        drv = pathlib.Path(tmpdir) / "ProfileExprs.lean"
        drv.write_text(src, encoding="utf-8")
        env = dict(os.environ)
        if use_lake and not extra_paths:
            cmd = [*wrapper, "lake", "env", "lean", "--run", str(drv)]
            cwd = str(lake_dir)
        else:
            lean_bin, sysroot = resolve_standalone_lean()
            search_dirs = [str(lake_dir.resolve()), *extra_paths, str(sysroot / "lib" / "lean")]
            env["LEAN_PATH"] = os.pathsep.join(search_dirs)
            cmd = [*wrapper, str(lean_bin), "--run", str(drv)]
            cwd = tmpdir
        proc = subprocess.run(
            cmd,
            cwd=cwd,
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            raise RuntimeError(
                f"Lean Expr profiler failed (exit {proc.returncode}):\n"
                f"{proc.stdout}\n{proc.stderr}"
            )
        lines = [ln.strip() for ln in proc.stdout.splitlines() if ln.strip().startswith("[")]
        return json.loads(lines[-1]) if lines else []


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", help="Lake workspace root or directory containing `.olean` files.")
    parser.add_argument("--module", help="Optional Lean module to inspect per-declaration Expr DAG nodes.")
    parser.add_argument("--lean-path", action="append", default=[], dest="lean_paths",
                        help="Extra `.olean` directory on `LEAN_PATH` for Lake-free trees (repeatable).")
    parser.add_argument("--prefix", default="", help="Declaration namespace prefix (defaults to --module).")
    parser.add_argument("--top", type=int, default=20, help="Maximum rows to display (default: 20).")
    parser.add_argument("--no-wrapper", action="store_true", help="Run `lake`/`lean` without `anneal-lean-run`.")
    parser.add_argument("--json", action="store_true", help="Emit JSON output.")
    args = parser.parse_args(argv)

    root = pathlib.Path(args.target).resolve()
    olean_rows = scan_olean_sizes(root, args.top)
    decl_rows: list[dict[str, Any]] = []
    if args.module:
        decl_rows = profile_module_exprs(
            root,
            args.module,
            args.prefix,
            args.top,
            args.no_wrapper,
            [pathlib.Path(p) for p in args.lean_paths],
        )

    if args.json:
        print(json.dumps({"oleans": olean_rows, "declarations": decl_rows}, indent=2))
    else:
        print(f"Top {len(olean_rows)} .olean file(s) under {root}:")
        for row in olean_rows:
            print(f"  {row['kib']:9.2f} KiB  {row['path']}")
        if decl_rows:
            print(f"\nTop {len(decl_rows)} declaration(s) by Expr DAG nodes in `{args.module}`:")
            for d in decl_rows:
                print(f"  DAG={d['total_dag_nodes']:7d}  Tree={d['total_tree_nodes_capped']:9d}  "
                      f"Refs={d['direct_const_refs']:4d}  {d['decl']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
