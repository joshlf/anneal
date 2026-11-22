#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Compiles any standalone `.lean` file and runs fresh `Kernel.Environment.replay` audit."""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import time
from typing import Any

REPLAY_DRIVER_LEAN = r"""import Lean

open Lean

def isIndAux (n : Name) : Bool :=
  let s := n.toString
  s.endsWith ".rec" || s.endsWith ".recOn" || s.endsWith ".casesOn" ||
  s.endsWith ".noConfusion" || s.endsWith ".noConfusionType" ||
  s.endsWith ".ctorIdx" || s.endsWith ".toCtorIdx" || s.endsWith ".elim" ||
  s.endsWith ".ctorElim" || s.endsWith ".ctorElimType" ||
  s.endsWith ".below" || s.endsWith ".ibelow" || s.endsWith ".brecOn" ||
  s.endsWith ".binductionOn" || s.endsWith ".mk" ||
  s.endsWith ".inj" || s.endsWith ".injEq" || s.endsWith ".sizeOf_spec" ||
  s.endsWith "._flat_ctor" || (s.splitOn ".below.").length > 1 ||
  (s.splitOn "_sizeOf").length > 1

def main (args : List String) : IO UInt32 := do
  match args with
  | modNameStr :: baseModStr :: reachPrefix :: rootsCsv :: _ =>
    let modName := modNameStr.toName
    let baseMod := baseModStr.toName
    initSearchPath (← findSysroot)
    let t0 ← IO.monoMsNow
    let base ← importModules #[{ module := baseMod }] {} (trustLevel := 0) (loadExts := false) (level := .private)
    let full ← importModules #[{ module := modName }] {} (trustLevel := 0) (loadExts := false) (level := .private)
    let mut newConsts : Std.HashMap Name ConstantInfo := {}
    let mut total : Nat := 0
    let mut theorems : Nat := 0
    let mut defs : Nat := 0
    let mut inducts : Nat := 0
    let mut userAxioms : Array String := #[]
    let mut opaques : Array String := #[]
    let mut unsafeOrPartial : Array String := #[]
    let mut scopedConsts : Array Name := #[]
    for (n, ci) in full.constants.map₁.toList do
      if !base.constants.contains n then
        newConsts := newConsts.insert n ci
        total := total + 1
        match ci with
        | .thmInfo _ => theorems := theorems + 1
        | .defnInfo dv =>
          defs := defs + 1
          if dv.safety != .safe then
            unsafeOrPartial := unsafeOrPartial.push n.toString
        | .inductInfo iv =>
          inducts := inducts + 1
          if iv.isUnsafe then
            unsafeOrPartial := unsafeOrPartial.push n.toString
        | .axiomInfo _ => userAxioms := userAxioms.push n.toString
        | .opaqueInfo _ => opaques := opaques.push n.toString
        | _ => pure ()
        if !reachPrefix.isEmpty && (n.toString == reachPrefix || n.toString.startsWith (reachPrefix ++ ".")) then
          scopedConsts := scopedConsts.push n
    let tReplay0 ← IO.monoMsNow
    let _replayed ← base.toKernelEnv.replay newConsts
    let tReplay1 ← IO.monoMsNow

    -- Direct transitive axiom collection over kernel ConstantInfo (no exportedAxiomsExt)
    let mut visitedAx : NameSet := {}
    let mut stackAx : List Name := newConsts.fold (init := []) fun acc n _ => n :: acc
    let mut usedAxioms : NameSet := {}
    while !stackAx.isEmpty do
      match stackAx with
      | [] => pure ()
      | cur :: rest =>
        stackAx := rest
        if !visitedAx.contains cur then
          visitedAx := visitedAx.insert cur
          if let some ci := full.find? cur then
            if ci.isAxiom then
              usedAxioms := usedAxioms.insert cur
            for u in ci.getUsedConstantsAsSet do
              if !visitedAx.contains u then
                stackAx := u :: stackAx
            for a in ci.all do
              if !visitedAx.contains a then
                stackAx := a :: stackAx
    let axList := (usedAxioms.toArray.qsort Name.lt).toList.map Name.toString
    let allowedAxioms := ["propext", "Classical.choice", "Quot.sound"]
    let badAxioms := axList.filter (fun a => !allowedAxioms.contains a)

    -- Optional reachability closure from `--reach-root` within `--reach-prefix`
    let mut unreached : List String := []
    if !rootsCsv.isEmpty && !reachPrefix.isEmpty then
      let roots := (rootsCsv.splitOn ",").filter (fun s => !s.isEmpty) |>.map String.toName
      let mut visR : NameSet := {}
      let mut stR : List Name := roots
      while !stR.isEmpty do
        match stR with
        | [] => pure ()
        | cur :: rest =>
          stR := rest
          if !visR.contains cur then
            visR := visR.insert cur
            if let some ci := newConsts.get? cur then
              for u in ci.getUsedConstantsAsSet do
                if !visR.contains u then stR := u :: stR
              for a in ci.all do
                if !visR.contains a then stR := a :: stR
      unreached := ((scopedConsts.filter (fun n => !visR.contains n && !isIndAux n)).qsort Name.lt).toList.map Name.toString

    let ok := total > 0 && userAxioms.isEmpty && opaques.isEmpty &&
              unsafeOrPartial.isEmpty && badAxioms.isEmpty && unreached.isEmpty
    let payload := Json.mkObj [
      ("module", toJson modNameStr),
      ("base_module", toJson baseModStr),
      ("replayed_constants", toJson total),
      ("theorems", toJson theorems),
      ("defs", toJson defs),
      ("inductives", toJson inducts),
      ("replay_ms", toJson (tReplay1 - tReplay0)),
      ("total_audit_ms", toJson (tReplay1 - t0)),
      ("user_axioms", toJson userAxioms.toList.mergeSort),
      ("opaques", toJson opaques.toList.mergeSort),
      ("unsafe_or_partial", toJson unsafeOrPartial.toList.mergeSort),
      ("used_axioms", toJson axList),
      ("disallowed_axioms", toJson badAxioms),
      ("unreached_non_aux", toJson unreached),
      ("passed", toJson ok)
    ]
    IO.println payload.compress
    return if ok then 0 else 1
  | _ =>
    IO.eprintln "Expected arguments: <module> <baseModule> <reachPrefix> <rootsCsv>"
    return 2
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


def resolve_lean_bin(explicit: str | None) -> str:
    if explicit:
        return explicit
    tc = pathlib.Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.34.1" / "bin" / "lean"
    if tc.is_file() and os.access(tc, os.X_OK):
        return str(tc)
    hit = shutil.which("lean")
    if hit:
        return hit
    raise FileNotFoundError("Could not locate `lean` binary; pass `--lean-bin`.")


def run_replay_audit(
    lean_file: pathlib.Path,
    base_module: str = "Init",
    extra_lean_paths: list[str] | None = None,
    root_dir: pathlib.Path | None = None,
    module_name: str | None = None,
    reach_prefix: str = "",
    reach_roots: list[str] | None = None,
    lean_bin: str | None = None,
    disable_wrapper: bool = False,
) -> tuple[int, dict[str, Any]]:
    src = lean_file.resolve()
    if not src.is_file():
        raise FileNotFoundError(f"Lean file not found: {src}")

    lean_exe = resolve_lean_bin(lean_bin)
    prefix_proc = subprocess.run(
        [lean_exe, "--print-prefix"], capture_output=True, text=True, check=True
    )
    sysroot_lib = str(pathlib.Path(prefix_proc.stdout.strip()) / "lib" / "lean")

    root = root_dir.resolve() if root_dir else src.parent
    if module_name:
        mod = module_name
    else:
        rel = src.relative_to(root).with_suffix("")
        mod = ".".join(rel.parts)

    wrapper = find_lean_wrapper(disable_wrapper)
    with tempfile.TemporaryDirectory(prefix="workbench-replay-") as tmp:
        tmp_path = pathlib.Path(tmp)
        olean_path = tmp_path / pathlib.Path(*mod.split(".")).with_suffix(".olean")
        olean_path.parent.mkdir(parents=True, exist_ok=True)
        driver_path = tmp_path / "ReplayAudit.lean"
        driver_path.write_text(REPLAY_DRIVER_LEAN, encoding="utf-8")

        lean_paths = [str(tmp_path), *(extra_lean_paths or []), sysroot_lib]
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join(lean_paths)

        t0 = time.monotonic()
        compile_cmd = [
            *wrapper,
            lean_exe,
            "-R", str(root),
            "-DElab.async=false",
            "-Ddebug.skipKernelTC=false",
            "-o", str(olean_path),
            str(src),
        ]
        c_proc = subprocess.run(compile_cmd, env=env, capture_output=True, text=True, check=False)
        compile_ms = round((time.monotonic() - t0) * 1000.0, 1)
        if c_proc.returncode != 0:
            return c_proc.returncode, {
                "passed": False,
                "stage": "compile",
                "file": str(src),
                "module": mod,
                "compile_ms": compile_ms,
                "stdout": c_proc.stdout,
                "stderr": c_proc.stderr,
            }

        roots_csv = ",".join(reach_roots or [])
        replay_cmd = [
            *wrapper,
            lean_exe,
            "--run", str(driver_path),
            mod, base_module, reach_prefix, roots_csv,
        ]
        r_proc = subprocess.run(replay_cmd, env=env, capture_output=True, text=True, check=False)
        lines = [ln.strip() for ln in r_proc.stdout.splitlines() if ln.strip().startswith("{")]
        if not lines:
            return r_proc.returncode or 1, {
                "passed": False,
                "stage": "replay",
                "file": str(src),
                "module": mod,
                "compile_ms": compile_ms,
                "stdout": r_proc.stdout,
                "stderr": r_proc.stderr,
            }
        payload: dict[str, Any] = json.loads(lines[-1])
        payload["file"] = str(src)
        payload["compile_ms"] = compile_ms
        return (0 if payload.get("passed") else 1), payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", help="Path to standalone `.lean` file to compile and kernel-replay.")
    parser.add_argument("--root-dir", help="Optional module root directory (default: file's parent).")
    parser.add_argument("--module", help="Optional Lean module name (default: inferred from path).")
    parser.add_argument("--base-module", default="Init",
                        help="Trusted base module to replay on top of (default: `Init`).")
    parser.add_argument("--lean-path", action="append", default=[], dest="lean_paths",
                        help="Additional LEAN_PATH entry for imported `.olean` directories (repeatable).")
    parser.add_argument("--reach-prefix", default="",
                        help="Optional namespace prefix for dead-code reachability checking.")
    parser.add_argument("--reach-root", action="append", default=[], dest="reach_roots",
                        help="Root constant name for reachability closure (repeatable).")
    parser.add_argument("--lean-bin", help="Explicit path to `lean` binary (defaults to v4.34.1).")
    parser.add_argument("--no-wrapper", action="store_true",
                        help="Invoke `lean` directly without `anneal-lean-run`.")
    parser.add_argument("--json", action="store_true", help="Emit JSON report.")
    args = parser.parse_args(argv)

    rc, report = run_replay_audit(
        lean_file=pathlib.Path(args.file),
        base_module=args.base_module,
        extra_lean_paths=args.lean_paths,
        root_dir=pathlib.Path(args.root_dir) if args.root_dir else None,
        module_name=args.module,
        reach_prefix=args.reach_prefix,
        reach_roots=args.reach_roots,
        lean_bin=args.lean_bin,
        disable_wrapper=args.no_wrapper,
    )

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        if report.get("stage") == "compile":
            print(f"[FAIL: compile] {report['file']} ({report['compile_ms']} ms)", file=sys.stderr)
            if report.get("stdout"):
                print(report["stdout"], file=sys.stderr)
            if report.get("stderr"):
                print(report["stderr"], file=sys.stderr)
        elif "replayed_constants" in report:
            status = "PASS" if report["passed"] else "FAIL"
            print(f"[{status}] Replayed {report['replayed_constants']} constant(s) "
                  f"(theorems={report['theorems']}, defs={report['defs']}, inducts={report['inductives']}) "
                  f"in compile={report['compile_ms']}ms, replay={report['replay_ms']}ms")
            print(f"  Used axioms:       {report['used_axioms']}")
            print(f"  User axioms:       {report['user_axioms']}")
            print(f"  Opaques:           {report['opaques']}")
            print(f"  Unsafe/partial:    {report['unsafe_or_partial']}")
            print(f"  Disallowed axioms: {report['disallowed_axioms']}")
            if args.reach_prefix:
                print(f"  Unreached non-aux: {report['unreached_non_aux']}")
        else:
            print(json.dumps(report, indent=2), file=sys.stderr)
    return rc


if __name__ == "__main__":
    sys.exit(main())
