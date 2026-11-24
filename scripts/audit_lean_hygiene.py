#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Compiled Lean 4 Environment hygiene auditor (`._unsafe_rec`, `isPartial`, axioms)."""

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

STANDARD_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]

LEAN_INSPECTOR_TEMPLATE = r"""import Lean
{imports}

open Lean

def startsWithAny (nm : String) (prefixes : List String) : Bool :=
  prefixes.any (fun p => nm == p || nm.startsWith (p ++ "."))

partial def collectTransitiveAxioms (env : Environment) (root : Name) : List String :=
  let rec visit (nm : Name) : StateM (Std.HashSet Name × Std.HashSet String) Unit := do
    let (seen, _) ← get
    if seen.contains nm then
      return ()
    modify fun (s, a) => (s.insert nm, a)
    if let some ci := env.find? nm then
      match ci with
      | .axiomInfo _ =>
        modify fun (s, a) => (s, a.insert nm.toString)
      | _ => pure ()
      for dep in ci.getUsedConstantsAsSet do
        visit dep
  let (_, (_, axs)) := (visit root).run ({}, {})
  axs.toList

def main : IO Unit := do
  let env ← importModules #[{module_names}] {} 0
  let prefixes : List String := [{prefix_literals}]
  let mut totalDecls : Nat := 0
  let mut unsafeRec : List String := []
  let mut partialOrUnsafe : List String := []
  let mut sorryDecls : List String := []
  let mut badAxiomDecls : List (String × List String) := []
  let mut eqSplitters : List String := []
  let mut foreignRealized : List (String × String) := []
  let mut foundationRealized : List (String × String) := []
  let mut realizedModCounts : Std.HashMap String (List String) := {}
  let mut allAxiomsUsed : Std.HashSet String := {}

  for i in [:env.header.moduleData.size] do
    let mName := env.header.modules[i]!.module.toString
    if startsWithAny mName prefixes then
      let mData := env.header.moduleData[i]!
      for c in mData.constNames do
        let cs := c.toString
        if !(startsWithAny cs prefixes) && !(cs.startsWith "_private.") then
          let isReservedFoundationThm :=
            match env.find? c with
            | some (.thmInfo _) => Lean.isReservedName env c
            | _ => false
          if isReservedFoundationThm then
            foundationRealized := (mName, cs) :: foundationRealized
            let prev := realizedModCounts.getD cs []
            if !(prev.contains mName) then
              realizedModCounts := realizedModCounts.insert cs (mName :: prev)
          else
            foreignRealized := (mName, cs) :: foreignRealized

  let mut dupRealized : List (String × List String) := []
  for (cs, mods) in realizedModCounts.toList do
    if mods.length > 1 then
      dupRealized := (cs, mods.mergeSort) :: dupRealized

  for (name, ci) in env.constants.map₁.toList do
    let s := name.toString
    if startsWithAny s prefixes then
      totalDecls := totalDecls + 1
      if s.endsWith "._unsafe_rec" then
        unsafeRec := s :: unsafeRec
      let isPart := match ci with
        | .defnInfo v => v.safety == .partial
        | _ => false
      if (ci.isUnsafe || isPart) && !s.endsWith "._unsafe_rec" then
        partialOrUnsafe := s :: partialOrUnsafe
      if s.endsWith ".eq_1" || s.endsWith ".splitter" then
        eqSplitters := s :: eqSplitters
      if !ci.isUnsafe then
        let axs := collectTransitiveAxioms env name
        for ax in axs do
          allAxiomsUsed := allAxiomsUsed.insert ax
        if axs.contains "sorryAx" then
          sorryDecls := s :: sorryDecls
        let disallowed := axs.filter (fun ax =>
          ax != "propext" && ax != "Classical.choice" && ax != "Quot.sound" && ax != "sorryAx")
        if !disallowed.isEmpty then
          badAxiomDecls := (s, disallowed) :: badAxiomDecls

  let jsonObj := Json.mkObj [
    ("total_constants", Json.num totalDecls),
    ("unsafe_rec", toJson unsafeRec.mergeSort),
    ("partial_or_unsafe", toJson partialOrUnsafe.mergeSort),
    ("sorry_decls", toJson sorryDecls.mergeSort),
    ("eq_or_splitter_decls", toJson eqSplitters.mergeSort),
    ("foreign_realized_consts", Json.arr (foreignRealized.map (fun (m, c) =>
      Json.mkObj [("module", toJson m), ("const", toJson c)])).toArray),
    ("foundation_realized_helpers", Json.arr (foundationRealized.map (fun (m, c) =>
      Json.mkObj [("module", toJson m), ("const", toJson c)])).toArray),
    ("duplicate_realized_helpers", Json.arr (dupRealized.map (fun (c, ms) =>
      Json.mkObj [("const", toJson c), ("modules", toJson ms)])).toArray),
    ("axioms_used", toJson allAxiomsUsed.toList.mergeSort),
    ("disallowed_axiom_decls", Json.arr (badAxiomDecls.map (fun (d, axs) =>
      Json.mkObj [("decl", toJson d), ("axioms", toJson axs)])).toArray)
  ]
  IO.println jsonObj.compress
"""


def find_lean_wrapper(disable_wrapper: bool) -> list[str]:
    if disable_wrapper:
        return []
    env_override = os.environ.get("ANNEAL_LEAN_RUN")
    if env_override and os.path.isfile(env_override) and os.access(env_override, os.X_OK):
        return [env_override, "--mode", "file", "--"]
    local_bin = pathlib.Path.home() / ".local" / "bin" / "anneal-lean-run"
    if local_bin.is_file() and os.access(local_bin, os.X_OK):
        return [str(local_bin), "--mode", "file", "--"]
    path_hit = shutil.which("anneal-lean-run")
    if path_hit:
        return [path_hit, "--mode", "file", "--"]
    return []


def run_environment_audit(
    lake_dir: pathlib.Path,
    modules: list[str],
    namespaces: list[str],
    disable_wrapper: bool = False,
) -> dict[str, Any]:
    imports = "\n".join(f"import {m}" for m in modules)
    mod_names = ", ".join(f"{{ module := `{m} }}" for m in modules)
    ns_list = namespaces if namespaces else modules
    prefix_lits = ", ".join(json.dumps(ns) for ns in ns_list)

    driver_src = (
        LEAN_INSPECTOR_TEMPLATE
        .replace("{imports}", imports)
        .replace("{module_names}", mod_names)
        .replace("{prefix_literals}", prefix_lits)
    )

    wrapper = find_lean_wrapper(disable_wrapper)
    with tempfile.TemporaryDirectory(prefix="workbench-hygiene-") as tmpdir:
        driver_path = pathlib.Path(tmpdir) / "InspectEnv.lean"
        driver_path.write_text(driver_src, encoding="utf-8")
        cmd = [
            *wrapper,
            "lake",
            "env",
            "lean",
            "-DElab.async=false",
            "-Ddebug.skipKernelTC=false",
            "--run",
            str(driver_path),
        ]
        proc = subprocess.run(
            cmd,
            cwd=str(lake_dir),
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            raise RuntimeError(
                f"Lean environment audit failed (exit {proc.returncode}):\n"
                f"{proc.stdout}\n{proc.stderr}"
            )
        lines = [ln.strip() for ln in proc.stdout.splitlines() if ln.strip().startswith("{")]
        if not lines:
            raise RuntimeError(f"No JSON payload emitted by Lean inspector:\n{proc.stdout}")
        data: dict[str, Any] = json.loads(lines[-1])

    unsafe_rec_fixes = []
    for ur in data.get("unsafe_rec", []):
        parent = ur[: -len("._unsafe_rec")] if ur.endswith("._unsafe_rec") else ur
        unsafe_rec_fixes.append({
            "auxiliary": ur,
            "parent_decl": parent,
            "remediation": (
                "Rewrite recursion structurally via `@Nat.rec` / `List.foldr`, "
                "or mark logical specification helpers `noncomputable def`."
            ),
        })
    data["unsafe_rec_remediations"] = unsafe_rec_fixes
    data["clean"] = (
        not data["unsafe_rec"]
        and not data["partial_or_unsafe"]
        and not data["sorry_decls"]
        and not data["disallowed_axiom_decls"]
        and not data.get("foreign_realized_consts")
        and not data.get("duplicate_realized_helpers")
    )
    return data


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake-dir", required=True,
                        help="Path to the Lake workspace directory containing lakefile.toml/lean.")
    parser.add_argument("--module", action="append", required=True, dest="modules",
                        help="Lean module name to import and inspect (repeatable).")
    parser.add_argument("--namespace", action="append", default=[], dest="namespaces",
                        help="Declaration namespace prefix to audit (defaults to --module names).")
    parser.add_argument("--allow-partial", action="store_true",
                        help="Do not fail exit code on partial/unsafe defs (for Lab/meta modules).")
    parser.add_argument("--no-wrapper", action="store_true",
                        help="Invoke `lake` directly without `anneal-lean-run`.")
    parser.add_argument("--json", action="store_true", help="Emit JSON report.")
    args = parser.parse_args(argv)

    report = run_environment_audit(
        lake_dir=pathlib.Path(args.lake_dir).resolve(),
        modules=args.modules,
        namespaces=args.namespaces,
        disable_wrapper=args.no_wrapper,
    )
    if args.allow_partial:
        ok = (
            not report["sorry_decls"]
            and not report["disallowed_axiom_decls"]
        )
    else:
        ok = bool(report["clean"])
    report["passed_gate"] = ok

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(f"Audited {report['total_constants']} constant(s) across {args.modules}:")
        print(f"  Axioms used:          {report['axioms_used']}")
        print(f"  sorryAx constants:    {len(report['sorry_decls'])}")
        print(f"  Disallowed axioms:    {len(report['disallowed_axiom_decls'])}")
        print(f"  ._unsafe_rec helpers: {len(report['unsafe_rec'])}")
        print(f"  partial/unsafe defs:  {len(report['partial_or_unsafe'])}")
        print(f"  .eq_1 / .splitter:    {len(report['eq_or_splitter_decls'])}")
        print(f"  foreign realized:     {len(report.get('foreign_realized_consts', []))}")
        for fr in report.get("foreign_realized_consts", []):
            print(f"  [FOREIGN] {fr['module']} emitted out-of-namespace `{fr['const']}`")
        for fix in report["unsafe_rec_remediations"]:
            print(f"  [FIX] {fix['parent_decl']} ({fix['auxiliary']}): {fix['remediation']}")

    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
