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
  ``Parser.Module.header, ``Parser.Module.moduleTk, ``Parser.Module.prelude,
  ``Parser.Module.import, ``Parser.Module.public, ``Parser.Module.all]

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
  ``Parser.Command.public, ``Parser.Command.noncomputable,
  ``Parser.Command.openSimple,
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
  [`simp, `instance, `reducible, `semireducible, `irreducible, `expose]

def allowedTheoryImportAllModules : List Name :=
  [`Init.Data.Nat.Bitwise.Basic]

def forbiddenPureTermKinds : NameSet := .ofList [
  ``Lean.includeStr,
  `Lean.Parser.Term.dbgTrace, `Lean.Parser.Term.idbg,
  `Lean.Parser.Term.doDbgTrace, `Lean.Parser.Term.doIdbg,
  `Lean.Parser.Tactic.dbgTrace, `termPrintln!__]

def forbiddenPureIdentifiers : List Name := [
  `dbgTrace, `dbgTraceVal, `dbgTraceIfShared,
  `dbgStackTrace, `dbgStackTraceIf, `dbgSleep,
  `lean_dbg_trace, `lean_dbg_trace_if_shared,
  `lean_dbg_stack_trace, `lean_dbg_sleep,
  `loadDynlib, `loadPlugin,
  `lean_load_dynlib, `lean_load_plugin,
  `lean_dynlib_load, `lean_dynlib_get, `lean_dynlib_symbol_run_as_init,
  `includeStr]

def forbiddenPureRootNamespaces : List Name := [
  `Lake, `IO, `BaseIO, `EIO, `EST, `ST, `Task, `System]

def forbiddenSysUvPrefixes : List Name := [
  `Init.System, `Std.Internal.UV, `Internal.UV,
  `Lean.LoadDynlib, `Lean.loadDynlib, `Lean.loadPlugin, `Lean.Dynlib,
  `Dynlib]

def isForbiddenPureNamespace (n : Name) : Bool :=
  let u := n.replacePrefix rootNamespace .anonymous
  let r := u.getRoot
  forbiddenPureRootNamespaces.contains r ||
    forbiddenSysUvPrefixes.any fun pre => u == pre || pre.isPrefixOf u

def isForbiddenPureImport (m : Name) : Bool :=
  let r := m.getRoot
  r == `Lean || r == `Lake ||
    m == `Init.System || (`Init.System).isPrefixOf m ||
    m == `Std.Internal.UV || (`Std.Internal.UV).isPrefixOf m

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

def candidateOpenNamespaces (currNs : Name) (openDecls : List OpenDecl)
    (id : Name) : List Name :=
  let rec scopeCandidates : Name → List Name
    | .anonymous => [id.replacePrefix rootNamespace .anonymous]
    | ns@(.str p _) => (ns ++ id) :: scopeCandidates p
    | _ => []
  let openCandidates := openDecls.filterMap fun
    | OpenDecl.simple ns _ => some (ns ++ id)
    | _ => none
  (scopeCandidates currNs ++ openCandidates).eraseDups

def extendOpenDeclsForOpenCmd (currNs : Name) (openDecls : List OpenDecl)
    (openStx : Syntax) : List OpenDecl :=
  if !openStx.isOfKind ``Parser.Command.open then
    openDecls
  else
    let openDecl := openStx[1]
    if !openDecl.isOfKind ``Parser.Command.openSimple then
      openDecls
    else
      openDecl[0].getArgs.foldl (init := openDecls) fun ods idStx =>
        let id := idStx.getId
        let hasOpenDecl (ns : Name) : Bool :=
          ods.any fun
            | OpenDecl.simple existing _ => existing == ns
            | _ => false
        let cands := candidateOpenNamespaces currNs ods id
        let ods' := cands.foldl (init := ods) fun acc ns =>
          if hasOpenDecl ns then acc else OpenDecl.simple ns [] :: acc
        let stripped := id.replacePrefix rootNamespace .anonymous
        if hasOpenDecl stripped then ods'
        else OpenDecl.simple stripped [] :: ods'

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

def isValidSectionHeaderSlot (child : Syntax) : Bool :=
  child.isOfKind nullKind &&
    (child.getArgs.isEmpty ||
      (child.getArgs.size == 1 &&
        match child.getArgs[0]! with
        | .atom _ "public" => true
        | _ => false) ||
      (child.getArgs.size == 3 &&
        match child.getArgs[0]!, child.getArgs[1]!, child.getArgs[2]! with
        | .atom _ "@[", .atom _ "expose", .atom _ "]" => true
        | _, _, _ => false))

def inspectNodeKind (k : SyntaxNodeKind) (args : Array Syntax)
    (requirePrelude : Bool := true) : Array String := Id.run do
  let mut errs : Array String := #[]
  if k == ``Parser.Module.header then
    if requirePrelude && (args[1]?.map Syntax.getArgs |>.getD #[]).isEmpty then
      errs := errs.push "explicit prelude is required"
  else if k == ``Parser.Command.sectionHeader then
    if !args.all isValidSectionHeaderSlot then
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
    (acc : Array Violation) (requirePrelude : Bool := true)
    (currNs : Name := .anonymous) (openDecls : List OpenDecl := [])
    (checkPureRefs : Bool := true) : Array Violation :=
  let (ln, col) := posOfSyntax fmap s
  match s with
  | .missing =>
    pushUnique acc { line := ln, column := col, message := "unexpected missing syntax node" }
  | .atom _ _ => acc
  | .ident _ _ val _ =>
    let acc :=
      if isValidSourceIdent val then acc
      else pushUnique acc { line := ln, column := col, message := s!"invalid source identifier `{val}`" }
    if !checkPureRefs then acc
    else
      let isBad (cand : Name) : Bool :=
        forbiddenPureIdentifiers.contains cand || isForbiddenPureNamespace cand
      let allCands := val :: candidateOpenNamespaces currNs openDecls val
      if allCands.any isBad then
        pushUnique acc { line := ln, column := col, message := s!"disallowed reference `{val}`" }
      else acc
  | .node _ k args =>
    let acc :=
      if forbiddenPureTermKinds.contains k then
        pushUnique acc { line := ln, column := col, message := s!"disallowed syntax `{k}`" }
      else acc
    let acc :=
      if k == nullKind || allowedKinds.contains k then acc
      else pushUnique acc { line := ln, column := col, message := s!"unsupported syntax kind `{k}`" }
    let acc := (inspectNodeKind k args requirePrelude).foldl
      (fun a msg => pushUnique a { line := ln, column := col, message := msg }) acc
    if k == ``Parser.Command.in && checkPureRefs && args.size == 3 then
      let acc := inspectSyntaxFull fmap allowedKinds args[0]! acc requirePrelude currNs openDecls checkPureRefs
      let acc := inspectSyntaxFull fmap allowedKinds args[1]! acc requirePrelude currNs openDecls checkPureRefs
      let nextOpen := extendOpenDeclsForOpenCmd currNs openDecls args[0]!
      inspectSyntaxFull fmap allowedKinds args[2]! acc requirePrelude currNs nextOpen checkPureRefs
    else if k == ``Parser.Command.mutual && checkPureRefs && args.size == 3 then
      let acc := inspectSyntaxFull fmap allowedKinds args[0]! acc requirePrelude currNs openDecls checkPureRefs
      let (acc, _) := args[1]!.getArgs.foldl (init := (acc, openDecls)) fun (a, mutOpen) child =>
        let a' := inspectSyntaxFull fmap allowedKinds child a requirePrelude currNs mutOpen checkPureRefs
        (a', extendOpenDeclsForOpenCmd currNs mutOpen child)
      inspectSyntaxFull fmap allowedKinds args[2]! acc requirePrelude currNs openDecls checkPureRefs
    else
      args.foldl (fun a c => inspectSyntaxFull fmap allowedKinds c a requirePrelude currNs openDecls checkPureRefs) acc

def collectScopedExtensionNamespaces (env : Environment) : IO NameSet := do
  let exts ← scopedEnvExtensionsRef.get
  let mut acc : NameSet := {}
  for ext in exts do
    for (ns, _) in (ext.ext.getState env).scopedEntries.map do
      acc := acc.insert ns
  return acc

def collectScopedNamespacePrefixes (scopedNamespaces : NameSet) : NameSet :=
  let rec insertPrefixes (acc : NameSet) : Name → NameSet
    | .anonymous => acc
    | ns@(.str p _) => insertPrefixes (acc.insert ns) p
    | _ => acc
  scopedNamespaces.foldl (init := {}) fun acc ns =>
    match ns with
    | .str p _ => insertPrefixes acc p
    | _ => acc

structure ParseScope where
  header : String
  currNamespace : Name
  openDecls : List OpenDecl
  deriving Inhabited

def nameOfParseScopes : List ParseScope → Nat → Name
  | _, 0 => .anonymous
  | [], _ => .anonymous
  | s :: ss, n + 1 =>
    if s.header == "" then .anonymous
    else .str (nameOfParseScopes ss n) s.header

def checkNamespaceAllowed (scopedNamespaces : NameSet) (how : String)
    (ln col : Nat) (ns : Name) (acc : Array Violation) : Array Violation :=
  if scopedNamespaces.contains ns then
    pushUnique acc { line := ln, column := col, message := s!"cannot {how} namespace `{ns}` with scoped syntax or extensions" }
  else if isForbiddenPureNamespace ns then
    pushUnique acc { line := ln, column := col, message := s!"cannot {how} forbidden namespace `{ns}`" }
  else acc

def pushParseScopes (scopedNamespaces : NameSet) (isNewNamespace : Bool)
    (ln col : Nat) (header : Name) (parserEnv : Environment)
    (scopes : List ParseScope) (acc : Array Violation) :
    Environment × List ParseScope × Array Violation :=
  match header with
  | .anonymous => (parserEnv, scopes, acc)
  | .str p seg =>
    let (parserEnv, scopes, acc) :=
      pushParseScopes scopedNamespaces isNewNamespace ln col p parserEnv scopes acc
    let top := scopes.head!
    let newNs := if isNewNamespace then Name.mkStr top.currNamespace seg else top.currNamespace
    let acc :=
      if isNewNamespace then checkNamespaceAllowed scopedNamespaces "enter" ln col newNs acc
      else acc
    let parserEnv := parserEnv.registerNamespace newNs
    let parserEnv := Parser.parserExtension.pushScope parserEnv
    let newScope : ParseScope := { top with header := seg, currNamespace := newNs }
    (parserEnv, newScope :: scopes, acc)
  | _ =>
    (parserEnv, scopes, pushUnique acc { line := ln, column := col, message := s!"invalid scope name `{header}`" })

def checkDeclNamespacePrefixes (scopedNamespaces : NameSet) (currNs : Name)
    (ln col : Nat) (id : Name) (parserEnv : Environment) (acc : Array Violation) :
    Environment × Array Violation :=
  if (`_root_).isPrefixOf id then
    (parserEnv, acc)
  else
    let rec walkPrefix (ns : Name) (env : Environment) (a : Array Violation) :
        Name × Environment × Array Violation :=
      match ns with
      | .anonymous => (currNs, env, a)
      | .str p seg =>
        let (base, env, a) := walkPrefix p env a
        let full := Name.mkStr base seg
        let a := checkNamespaceAllowed scopedNamespaces "declare in" ln col full a
        (full, env.registerNamespace full, a)
      | _ =>
        (currNs, env, pushUnique a { line := ln, column := col, message := s!"invalid declaration namespace `{id}`" })
    match id with
    | .str .anonymous _ => (parserEnv, acc)
    | .str pre _ =>
      let (_, env, a) := walkPrefix pre parserEnv acc
      (env, a)
    | _ => (parserEnv, acc)

def declarationIdent? (stx : Syntax) : Option Name :=
  let decl := stx[1]
  if decl.getKind == ``Parser.Command.instance then
    if decl[3].isNone then none else some decl[3][0][0].getId
  else
    some decl[1][0].getId

partial def applyCommandScope (fmap : FileMap) (scopedNamespaces scopedPrefixes : NameSet)
    (parserEnv : Environment) (scopes : List ParseScope) (stx : Syntax)
    (acc : Array Violation) : Environment × List ParseScope × Array Violation := Id.run do
  let (ln, col) := posOfSyntax fmap stx
  let k := stx.getKind
  if k == ``Parser.Command.namespace then
    return pushParseScopes scopedNamespaces true ln col stx[1].getId parserEnv scopes acc
  else if k == ``Parser.Command.section then
    if stx[2].isNone then
      let top := scopes.head!
      let parserEnv := Parser.parserExtension.pushScope parserEnv
      return (parserEnv, { top with header := "" } :: scopes, acc)
    else
      return pushParseScopes scopedNamespaces false ln col stx[2][0].getId parserEnv scopes acc
  else if k == ``Parser.Command.end then
    let header? := if stx[1].isNone then none else some stx[1][0].getId
    let endSize := match header? with
      | none => 1
      | some n => n.getNumParts
    if scopes.length <= 1 then
      return (parserEnv, scopes, pushUnique acc { line := ln, column := col, message := "unexpected `end` command with no active scope" })
    let mut bad := acc
    match header? with
    | none =>
      if scopes.head!.header != "" then
        bad := pushUnique bad { line := ln, column := col, message := s!"missing scope name `{scopes.head!.header}` after `end`" }
    | some header =>
      if endSize >= scopes.length then
        bad := pushUnique bad { line := ln, column := col, message := s!"`end {header}` closes more scopes than are open" }
      else
        let expected := nameOfParseScopes scopes endSize
        if expected != header then
          bad := pushUnique bad { line := ln, column := col, message := s!"mismatched `end {header}` (expected `{expected}`)" }
    let dropN := Nat.min endSize (scopes.length - 1)
    let mut env := parserEnv
    for _ in [:dropN] do
      env := Parser.parserExtension.popScope env
    return (env, scopes.drop dropN, bad)
  else if k == ``Parser.Command.open then
    let top := scopes.head!
    let mut openDecls := top.openDecls
    let mut bad := acc
    let openDecl := stx[1]
    if openDecl.isOfKind ``Parser.Command.openSimple then
      let hasOpenDecl (ods : List OpenDecl) (ns : Name) : Bool :=
        ods.any fun
          | OpenDecl.simple existing _ => existing == ns
          | _ => false
      for idStx in openDecl[0].getArgs do
        let (iln, icol) := posOfSyntax fmap idStx
        let id := idStx.getId
        let candidates := candidateOpenNamespaces top.currNamespace openDecls id
        let mut added := false
        for ns in candidates do
          bad := checkNamespaceAllowed scopedNamespaces "open" iln icol ns bad
          if parserEnv.isNamespace ns || scopedPrefixes.contains ns then
            if !hasOpenDecl openDecls ns then
              openDecls := OpenDecl.simple ns [] :: openDecls
            added := true
        if !added then
          let stripped := id.replacePrefix rootNamespace .anonymous
          bad := checkNamespaceAllowed scopedNamespaces "open" iln icol stripped bad
          if !hasOpenDecl openDecls stripped then
            openDecls := OpenDecl.simple stripped [] :: openDecls
    return (parserEnv, { top with openDecls := openDecls } :: scopes.tail!, bad)
  else if k == ``Parser.Command.in && stx.getArgs.size == 3 then
    let top := scopes.head!
    let tmpEnv := Parser.parserExtension.pushScope parserEnv
    let (tmpEnv, tmpScopes, bad) :=
      applyCommandScope fmap scopedNamespaces scopedPrefixes tmpEnv (top :: scopes) stx[0] acc
    let (tmpEnv, _, bad) :=
      applyCommandScope fmap scopedNamespaces scopedPrefixes tmpEnv tmpScopes stx[2] bad
    return (Parser.parserExtension.popScope tmpEnv, scopes, bad)
  else if k == ``Parser.Command.mutual && stx.getArgs.size == 3 then
    let top := scopes.head!
    let mut tmpEnv := Parser.parserExtension.pushScope parserEnv
    let mut tmpScopes := top :: scopes
    let mut bad := acc
    for child in stx[1].getArgs do
      let (e', sc', b') :=
        applyCommandScope fmap scopedNamespaces scopedPrefixes tmpEnv tmpScopes child bad
      tmpEnv := e'
      tmpScopes := sc'
      bad := b'
    return (Parser.parserExtension.popScope tmpEnv, scopes, bad)
  else if k == ``Parser.Command.declaration then
    match declarationIdent? stx with
    | some id =>
      let (env, bad) := checkDeclNamespacePrefixes scopedNamespaces scopes.head!.currNamespace ln col id parserEnv acc
      return (env, scopes, bad)
    | none => return (parserEnv, scopes, acc)
  else
    return (parserEnv, scopes, acc)

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
  let baseEnv ← loadFoundationParserEnv
  let scopedNamespaces ← collectScopedExtensionNamespaces baseEnv
  let scopedPrefixes := collectScopedNamespacePrefixes scopedNamespaces
  let mut fileReports : Array Json := #[]
  for item in filesArr do
    let path ← IO.ofExcept item.getStr?
    let txt ← IO.FS.readFile path
    let ictx := mkInputContext txt path
    let (hdr, pstate, msgs) ← parseHeader ictx
    let mut bad : Array Violation :=
      inspectSyntaxFull ictx.fileMap allowedKinds hdr.raw #[] (requirePrelude := true) (checkPureRefs := false)
    for m in msgs.toList do
      if m.severity == .error then
        let d ← m.data.toString
        bad := pushUnique bad { line := m.pos.line, column := m.pos.column + 1, message := s!"parseHeader error: {d}" }
    let (hln, hcol) := posOfSyntax ictx.fileMap hdr.raw
    let isModule := Elab.HeaderSyntax.isModule hdr
    let imports := Elab.HeaderSyntax.imports hdr
    for imp in imports do
      if imp.isMeta then
        bad := pushUnique bad { line := hln, column := hcol, message := "import modifiers are unsupported (`meta`)" }
      if !imp.isExported && !isModule then
        bad := pushUnique bad { line := hln, column := hcol, message := "non-exported `import` requires `module` header" }
      if imp.importAll then
        let allowImportAll :=
          isModule && role == "theory" && allowedTheoryImportAllModules.contains imp.module
        if !allowImportAll then
          bad := pushUnique bad { line := hln, column := hcol, message := s!"unsupported `import all {imp.module}`" }
      if isForbiddenPureImport imp.module then
        bad := pushUnique bad { line := hln, column := hcol, message := s!"disallowed sysroot import `{imp.module}`" }
    let mut parserEnv := baseEnv
    let mut scopes : List ParseScope :=
      [{ header := "", currNamespace := .anonymous, openDecls := [] }]
    let mut s := pstate
    repeat
      let top := scopes.head!
      let pmctx : ParserModuleContext := {
        env := parserEnv
        options := {}
        currNamespace := top.currNamespace
        openDecls := top.openDecls
      }
      let (cmd, s', msgs') := parseCommand ictx pmctx s {}
      for m in msgs'.toList do
        if m.severity == .error then
          let d ← m.data.toString
          bad := pushUnique bad { line := m.pos.line, column := m.pos.column + 1, message := s!"parseCommand error: {d}" }
      if !Parser.isTerminalCommand cmd then
        if !allowedCommandKinds.contains cmd.getKind then
          let (cln, ccol) := posOfSyntax ictx.fileMap cmd
          bad := pushUnique bad { line := cln, column := ccol, message := s!"unsupported command `{cmd.getKind}`" }
        bad := inspectSyntaxFull ictx.fileMap allowedKinds cmd bad
          (requirePrelude := true) (currNs := top.currNamespace) (openDecls := top.openDecls) (checkPureRefs := true)
        let (nextEnv, nextScopes, bad') :=
          applyCommandScope ictx.fileMap scopedNamespaces scopedPrefixes parserEnv scopes cmd bad
        parserEnv := nextEnv
        scopes := nextScopes
        bad := bad'
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
