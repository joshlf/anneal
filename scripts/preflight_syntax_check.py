#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Fast Lean 4 `TrustedBoundary` CST syntax preflight checker (no elaboration)."""

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

DEFAULT_LAKE_DIR = pathlib.Path(__file__).resolve().parents[1] / "lean"

LEAN_SYNTAX_CHECKER = r"""import Lean
open Lean Parser

def allowedHeaderKinds : List Name := [
  ``Parser.Module.header, ``Parser.Module.prelude, ``Parser.Module.import]

def allowedCommandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.universe,
  ``Parser.Command.variable, ``Parser.Command.open, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in, ``Parser.Command.attribute,
  ``Parser.Command.moduleDoc]

def allowedDeclarationKinds : List Name := [
  ``Parser.Command.abbrev, ``Parser.Command.definition,
  ``Parser.Command.theorem, ``Parser.Command.opaque,
  ``Parser.Command.instance, ``Parser.Command.inductive,
  ``Parser.Command.classInductive, ``Parser.Command.structure]

def allowedCommandSyntaxKinds : List Name := [
  ``Parser.Command.declModifiers, ``Parser.Command.declId,
  ``Parser.Command.declSig, ``Parser.Command.optDeclSig,
  ``Parser.Command.declValSimple, ``Parser.Command.declValEqns,
  ``Parser.Command.whereStructInst, ``Parser.Command.docComment,
  ``Parser.Command.private, ``Parser.Command.protected,
  ``Parser.Command.noncomputable, ``Parser.Command.openSimple,
  ``Parser.Command.sectionHeader, ``Parser.Command.eraseAttr,
  ``Parser.Command.ctor, ``Parser.Command.optDeriving,
  ``Parser.Command.optDefDeriving, ``Parser.Command.classTk,
  ``Parser.Command.structureTk, ``Parser.Command.extends,
  ``Parser.Command.structCtor, ``Parser.Command.structFields,
  ``Parser.Command.structSimpleBinder, ``Parser.Command.structExplicitBinder,
  ``Parser.Command.structImplicitBinder, ``Parser.Command.structInstBinder,
  ``Parser.Command.structParent, ``Parser.Termination.suffix,
  ``Lean.binderIdent, ``Lean.explicitBinders,
  ``Lean.bracketedExplicitBinders, ``Lean.unbracketedExplicitBinders]

def allowedTermSyntaxKinds : List Name := [
  ``Parser.Term.anonymousCtor, ``Parser.Term.app, ``Parser.Term.arrow,
  ``Parser.Term.attrInstance, ``Parser.Term.attrKind,
  ``Parser.Term.attributes, ``Parser.Term.basicFun,
  ``Parser.Term.binderDefault, ``Parser.Term.cdot, ``Parser.Term.dotIdent,
  ``Parser.Term.explicit, ``Parser.Term.explicitBinder,
  ``Parser.Term.forall, ``Parser.Term.fromTerm, ``Parser.Term.fun,
  ``Parser.Term.have, `Lean.Parser.Term.haveDecl, `Lean.Parser.Term.haveId,
  `Lean.Parser.Term.haveIdDecl, `Lean.Parser.Term.haveIdLhs, ``Parser.Term.hole,
  ``Parser.Term.hygienicLParen, ``Parser.Term.implicitBinder,
  ``Parser.Term.instBinder, ``Parser.Term.let, ``Parser.Term.letConfig,
  ``Parser.Term.letDecl, ``Parser.Term.letId, ``Parser.Term.letIdDecl,
  ``Parser.Term.letPatDecl, ``Parser.Term.match, ``Parser.Term.matchAlt,
  ``Parser.Term.matchAlts, ``Parser.Term.matchAltsWhereDecls,
  ``Parser.Term.matchDiscr, ``Parser.Term.namedArgument,
  ``Parser.Term.nomatch, ``Parser.Term.optEllipsis, ``Parser.Term.paren,
  ``Parser.Term.proj, ``Parser.Term.prop, ``Parser.Term.show,
  ``Parser.Term.sort, ``Parser.Term.strictImplicitBinder,
  ``Parser.Term.structInst, ``Parser.Term.structInstField,
  ``Parser.Term.structInstFieldDef, ``Parser.Term.structInstFieldEqns,
  ``Parser.Term.structInstFields, ``Parser.Term.structInstLVal,
  ``Parser.Term.subst, ``Parser.Term.syntheticHole, ``Parser.Term.tuple,
  ``Parser.Term.type, ``Parser.Term.typeAscription, ``Parser.Term.typeSpec,
  ``Parser.Attr.simple, ``Parser.Attr.instance, `Lean.Parser.Attr.simp,
  `fieldIdx, `group, `hygieneInfo, `num, `str, `char, `scientific]

def allowedNotationSyntaxKinds : List Name := [
  `term!_, `termIfThenElse, `termDepIfThenElse, `«term[_]»,
  `«term_&&_», `«term_||_», `«term_+_», `«term_-_», `«term_*_»,
  `«term_::_», `«term_++_», `«term_<_», `«term_≤_», `«term_>_»,
  `«term_≥_», `«term_==_», `«term_!=_», `«term_=_», `«term_≠_»,
  `«term__[_]_?», `«term_×_», `«term_↔_», `«term_∈_», `«term_∧_»,
  `«term_∨_», `«term¬_», `«term∃_,_», `«term‹_›», `Lean.cdot, `Lean.cdotTk]

def allowedTheoryTacticKinds : List Name := [
  ``Parser.Term.byTactic, ``Parser.Term.binderTactic,
  `Lean.Parser.Tactic.apply, `Lean.Parser.Tactic.cases,
  `Lean.Parser.Tactic.change, `Lean.Parser.Tactic.constructor,
  `Lean.Parser.Tactic.decide, `Lean.Parser.Tactic.dsimp,
  `Lean.Parser.Tactic.elimTarget, `Lean.Parser.Tactic.exact,
  `Lean.Parser.Tactic.first, `Lean.Parser.Tactic.induction,
  `Lean.Parser.Tactic.inductionAlt, `Lean.Parser.Tactic.inductionAltLHS,
  `Lean.Parser.Tactic.inductionAlts, `Lean.Parser.Tactic.injection,
  `Lean.Parser.Tactic.intro, `Lean.Parser.Tactic.left,
  `Lean.Parser.Tactic.location, `Lean.Parser.Tactic.locationHyp,
  `Lean.Parser.Tactic.optConfig, `Lean.Parser.Tactic.paren,
  `Lean.Parser.Tactic.refine, `Lean.Parser.Tactic.revert,
  `Lean.Parser.Tactic.right, `Lean.Parser.Tactic.rwRule,
  `Lean.Parser.Tactic.rwRuleSeq, `Lean.Parser.Tactic.rwSeq,
  `Lean.Parser.Tactic.simp, `Lean.Parser.Tactic.simpLemma,
  `Lean.Parser.Tactic.subst, `Lean.Parser.Tactic.tacticHave__,
  `Lean.Parser.Tactic.tacticLet__, `Lean.Parser.Tactic.«tacticNomatch_,,»,
  `Lean.Parser.Tactic.tacticRepeat_, `Lean.Parser.Tactic.tacticRfl,
  `Lean.Parser.Tactic.tacticSeq, `Lean.Parser.Tactic.tacticSeq1Indented,
  `Lean.Parser.Tactic.«tactic_<;>_», `Lean.Parser.Tactic.unfold,
  `tacticFunext___]

def allowedTrustedSyntaxKinds : NameSet :=
  .ofList <|
    allowedHeaderKinds ++
    allowedCommandKinds ++
    allowedDeclarationKinds ++
    allowedCommandSyntaxKinds ++
    allowedTermSyntaxKinds ++
    allowedNotationSyntaxKinds

def allowedTheorySyntaxKinds : NameSet :=
  allowedTrustedSyntaxKinds ++ .ofList allowedTheoryTacticKinds

def allowedAttributeNames : List Name :=
  [`simp, `instance, `reducible, `semireducible, `irreducible]

def isValidSourceIdent (id : Name) : Bool :=
  id.isAnonymous ||
    (!id.hasMacroScopes && id.eraseMacroScopes == id &&
     !id.toString.isEmpty &&
     id.components.all fun
       | .str .anonymous seg => !seg.isEmpty && seg != "_root_"
       | _ => false)

def isAllowedNestedCommand (k : SyntaxNodeKind) : Bool :=
  allowedCommandKinds.contains k &&
    ![``Parser.Command.namespace, ``Parser.Command.section,
      ``Parser.Command.end, ``Parser.Command.mutual].contains k

structure Violation where
  line : Nat
  column : Nat
  message : String
  deriving BEq

def posOfSyntax (fmap : FileMap) (s : Syntax) : Nat × Nat :=
  match s.getPos? with
  | some p =>
    let pos := fmap.toPosition p
    (pos.line, pos.column + 1)
  | none => (1, 1)

def pushUnique (acc : Array Violation) (v : Violation) : Array Violation :=
  if acc.any (fun x => x.line == v.line && x.message == v.message) then acc
  else acc.push v

def inspectNodeKind (k : SyntaxNodeKind) (args : Array Syntax) : Array String := Id.run do
  let mut errs : Array String := #[]
  if k == ``Parser.Module.header then
    if (args[1]?.map Syntax.getArgs |>.getD #[]).isEmpty then
      errs := errs.push "explicit prelude is required"
  else if k == ``Parser.Command.sectionHeader then
    if !args.all (·.getArgs.isEmpty) then
      errs := errs.push "section/namespace modifiers are unsupported"
  else if k == ``Parser.Command.declaration then
    let declKind := args[1]?.map Syntax.getKind |>.getD .anonymous
    if !allowedDeclarationKinds.contains declKind then
      errs := errs.push s!"unsupported declaration kind {declKind}"
  else if k == ``Parser.Command.mutual then
    if !(args.size == 3 && args[1]!.getArgs.all (isAllowedNestedCommand ·.getKind)) then
      errs := errs.push "unsupported mutual-block shape"
  else if k == ``Parser.Command.in then
    if !(args.size == 3 &&
         [``Parser.Command.open, ``Parser.Command.variable].contains args[0]!.getKind &&
         isAllowedNestedCommand args[2]!.getKind) then
      errs := errs.push "unsupported `in` command"
  else if k == ``Parser.Command.open then
    let openDecl := args[1]?.getD .missing
    if !openDecl.isOfKind ``Parser.Command.openSimple then
      errs := errs.push s!"unsupported open command {openDecl.getKind}"
  else if k == ``Parser.Attr.simple then
    let attrName := args[0]?.map Syntax.getId |>.getD .anonymous
    if !allowedAttributeNames.contains attrName then
      errs := errs.push s!"unsupported attribute {attrName}"
    if !(args[1]?.map Syntax.getArgs |>.getD #[]).isEmpty then
      errs := errs.push s!"unsupported arguments on attribute {attrName}"
  else if k == ``Parser.Attr.instance || k == `Lean.Parser.Attr.simp then
    if !(args.extract 1 args.size).all (·.getArgs.isEmpty) then
      errs := errs.push s!"unsupported arguments on attribute {k}"
  else if k == ``Parser.Command.eraseAttr then
    let attrName := args[1]?.map Syntax.getId |>.getD .anonymous
    if !allowedAttributeNames.contains attrName then
      errs := errs.push s!"unsupported attribute removal {attrName}"
  return errs

partial def inspectSyntaxFull (fmap : FileMap) (allowedKinds : NameSet) (s : Syntax)
    (acc : Array Violation) : Array Violation :=
  let (ln, col) := posOfSyntax fmap s
  match s with
  | .missing =>
    pushUnique acc { line := ln, column := col, message := "unexpected missing syntax node" }
  | .atom _ _ => acc
  | .ident _ _ val _ =>
    if isValidSourceIdent val then acc
    else pushUnique acc { line := ln, column := col, message := s!"invalid source identifier `{val}`" }
  | .node _ k args =>
    let acc :=
      if k == nullKind || allowedKinds.contains k then acc
      else pushUnique acc { line := ln, column := col, message := s!"unsupported syntax kind `{k}`" }
    let acc := (inspectNodeKind k args).foldl
      (fun a msg => pushUnique a { line := ln, column := col, message := msg }) acc
    args.foldl (fun a c => inspectSyntaxFull fmap allowedKinds c a) acc

def foundationModules : Array Name := #[
  `Init.BinderNameHint, `Init.Coe, `Init.Control.Basic, `Init.Control.Do,
  `Init.Control.Except, `Init.Control.Id, `Init.Control.MonadAttach,
  `Init.Control.Option, `Init.Control.State, `Init.Conv, `Init.Core,
  `Init.Data.Array.Basic, `Init.Data.Array.GetLit, `Init.Data.Array.Set,
  `Init.Data.BitVec.BasicAux, `Init.Data.ByteArray.Bootstrap, `Init.Data.Cast,
  `Init.Data.Char.Basic, `Init.Data.Fin.Basic, `Init.Data.Format.Basic,
  `Init.Data.Int.Basic, `Init.Data.List.Basic, `Init.Data.List.Notation,
  `Init.Data.List.ToArrayImpl, `Init.Data.Nat.Basic,
  `Init.Data.Nat.Bitwise.Basic, `Init.Data.Nat.Div.Basic, `Init.Data.NeZero,
  `Init.Data.Option.Basic, `Init.Data.Repr, `Init.Data.String.Bootstrap,
  `Init.Data.ToString.Basic, `Init.Data.UInt.BasicAux, `Init.Data.Zero,
  `Init.GetElem, `Init.Grind.Attr, `Init.Grind.Interactive,
  `Init.Grind.Tactics, `Init.Meta, `Init.Meta.Defs, `Init.MetaTypes,
  `Init.Notation, `Init.NotationExtra, `Init.Prelude, `Init.SimpLemmas,
  `Init.SizeOf, `Init.Syntax, `Init.Tactics, `Init.Util, `Init.WF,
  `Init.WFTactics
]

def loadFoundationParserEnv : IO Environment := do
  unsafe enableInitializersExecution
  let env ← importModules (foundationModules.map fun n => { module := n }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := true) (level := .private)
  return env

def main (args : List String) : IO Unit := do
  let manifestPath := args[0]!
  let role := args[1]?.getD "theory"
  let allowedKinds :=
    if role == "trusted" then allowedTrustedSyntaxKinds else allowedTheorySyntaxKinds
  let rawManifest ← IO.FS.readFile manifestPath
  let filesJson ← IO.ofExcept (Json.parse rawManifest)
  let filesArr ← IO.ofExcept filesJson.getArr?
  let env ← loadFoundationParserEnv
  let mut fileReports : Array Json := #[]
  for item in filesArr do
    let path ← IO.ofExcept item.getStr?
    let txt ← IO.FS.readFile path
    let ictx := mkInputContext txt path
    let (hdr, pstate, msgs) ← parseHeader ictx
    let mut bad : Array Violation := inspectSyntaxFull ictx.fileMap allowedKinds hdr #[]
    for m in msgs.toList do
      if m.severity == .error then
        let d ← m.data.toString
        bad := pushUnique bad { line := m.pos.line, column := m.pos.column + 1, message := s!"parseHeader error: {d}" }
    let mut s := pstate
    repeat
      let (cmd, s', msgs') := parseCommand ictx { env, options := {} } s {}
      for m in msgs'.toList do
        if m.severity == .error then
          let d ← m.data.toString
          bad := pushUnique bad { line := m.pos.line, column := m.pos.column + 1, message := s!"parseCommand error: {d}" }
      if !Parser.isTerminalCommand cmd then
        bad := inspectSyntaxFull ictx.fileMap allowedKinds cmd bad
      if Parser.isTerminalCommand cmd then break
      s := s'
    let vJson := bad.map fun v => Json.mkObj [
      ("line", Json.num v.line),
      ("column", Json.num v.column),
      ("message", Json.str v.message)
    ]
    fileReports := fileReports.push <| Json.mkObj [
      ("file", Json.str path),
      ("clean", Json.bool bad.isEmpty),
      ("violations", Json.arr vJson)
    ]
  let out := Json.mkObj [
    ("role", Json.str role),
    ("files", Json.arr fileReports)
  ]
  IO.println out.compress
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


def collect_lean_targets(raw_paths: list[str]) -> list[pathlib.Path]:
    out: list[pathlib.Path] = []
    for raw in raw_paths:
        p = pathlib.Path(raw).resolve()
        if p.is_file() and p.suffix == ".lean":
            out.append(p)
        elif p.is_dir():
            for child in sorted(p.rglob("*.lean")):
                if ".lake" not in child.parts and child.is_file():
                    out.append(child)
    return out


def run_syntax_preflight(
    files: list[pathlib.Path],
    role: str = "theory",
    lake_dir: pathlib.Path | None = None,
    disable_wrapper: bool = False,
) -> dict[str, Any]:
    if role not in {"theory", "trusted"}:
        raise ValueError(f"Unsupported role: {role!r}")
    resolved_files = [str(f.resolve()) for f in files]
    if not resolved_files:
        return {"role": role, "clean": True, "total_violations": 0, "files": []}

    eff_lake_dir = lake_dir.resolve() if lake_dir else DEFAULT_LAKE_DIR
    wrapper = find_lean_wrapper(disable_wrapper)

    with tempfile.TemporaryDirectory(prefix="workbench-cst-") as tmpdir:
        tmp = pathlib.Path(tmpdir)
        driver_path = tmp / "SyntaxPreflight.lean"
        manifest_path = tmp / "files.json"
        driver_path.write_text(LEAN_SYNTAX_CHECKER, encoding="utf-8")
        manifest_path.write_text(json.dumps(resolved_files), encoding="utf-8")

        if (eff_lake_dir / "lakefile.toml").is_file() or (eff_lake_dir / "lakefile.lean").is_file():
            cmd = [
                *wrapper,
                "lake",
                "env",
                "lean",
                "-DElab.async=false",
                "--run",
                str(driver_path),
                str(manifest_path),
                role,
            ]
            cwd = str(eff_lake_dir)
        else:
            cmd = [
                *wrapper,
                "lean",
                "-DElab.async=false",
                "--run",
                str(driver_path),
                str(manifest_path),
                role,
            ]
            cwd = None

        proc = subprocess.run(
            cmd,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            raise RuntimeError(
                f"Lean CST syntax preflight failed (exit {proc.returncode}):\n"
                f"{proc.stdout}\n{proc.stderr}"
            )
        lines = [ln.strip() for ln in proc.stdout.splitlines() if ln.strip().startswith("{")]
        if not lines:
            raise RuntimeError(f"No JSON emitted by Lean CST syntax preflight:\n{proc.stdout}")
        data: dict[str, Any] = json.loads(lines[-1])

    total_v = sum(len(f.get("violations", [])) for f in data.get("files", []))
    data["total_violations"] = total_v
    data["clean"] = total_v == 0
    return data


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", help="Lean `.lean` files or directories to inspect.")
    parser.add_argument("--role", choices=("theory", "trusted"), default="theory",
                        help="Syntax allowlist role (`theory` permits 26 tactics; `trusted` is tactic-free).")
    parser.add_argument("--lake-dir", default=None,
                        help="Optional Lake workspace directory used only to select the pinned Lean toolchain.")
    parser.add_argument("--no-wrapper", action="store_true",
                        help="Invoke `lake`/`lean` without `anneal-lean-run`.")
    parser.add_argument("--json", action="store_true", help="Emit JSON output.")
    args = parser.parse_args(argv)

    targets = collect_lean_targets(args.paths)
    lake_dir = pathlib.Path(args.lake_dir) if args.lake_dir else None
    report = run_syntax_preflight(
        files=targets,
        role=args.role,
        lake_dir=lake_dir,
        disable_wrapper=args.no_wrapper,
    )

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(
            f"Checked {len(report['files'])} file(s) under role `{report['role']}`: "
            f"{report['total_violations']} violation(s)."
        )
        for f in report["files"]:
            for v in f["violations"]:
                print(f"  [FAIL] {f['file']}:{v['line']}:{v['column']}: {v['message']}")

    return 0 if report["clean"] else 1


if __name__ == "__main__":
    sys.exit(main())
