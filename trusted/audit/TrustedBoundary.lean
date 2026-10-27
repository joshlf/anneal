-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean.Elab.Import
import Lean.Parser.Tactic
import Lean.Replay

/-! Pinned to Lean 4.34.1. This inspector never imports project extensions for
execution. Its parser environment and audited environment are separate from
the tooling environment used to run this file. See trusted/README.md and
trusted/audit/README.md. -/

open Lean

namespace TrustedBoundary

def fail (message : String) : IO α := throw <| IO.userError s!"policy:{message}"

def field [FromJson α] (j : Json) (key : String) : IO α :=
  IO.ofExcept <| j.getObjValAs? α key

def names (j : Json) (key : String) : IO (Array Name) := do
  return (← field (α := Array String) key (j := j)).map String.toName

def artifacts (j : Json) : IO (NameMap ImportArtifacts) := do
  let entries ← field (α := Array (String × Array (Array String))) j "artifacts"
  let mut result := {}
  for (n, parts) in entries do
    if (result.find? n.toName).isSome then fail s!"duplicate artifact module {n}"
    result := result.insert n.toName (.ofArrays (parts.map (·.map System.FilePath.mk)))
  return result

def graph (env : Environment) : Json :=
  Json.mkObj <| (env.header.modules.zip env.header.moduleData).toList.map fun (m, d) =>
    (m.module.toString, toJson d.imports)

def importEnv (j : Json) (roots : Array Name) (extensions := false) : IO Environment := do
  let arts ← artifacts j
  -- No search fallback is needed for any admitted declared import. Unknown
  -- modules are rejected by the runner's complete-DAG admission and this audit.
  if extensions then unsafe enableInitializersExecution
  let env ← importModules (roots.map fun n => {module := n}) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := extensions)
    (level := .private) (arts := arts)
  unless env.header.modules.size == env.header.moduleData.size do
    throw <| IO.userError "module/data array alignment failure"
  return env.setExporting false

def validateGraph (j : Json) (env : Environment) : IO Unit := do
  let expected ← field (α := Json) j "graph"
  unless graph env == expected do fail "compiled module/import DAG differs from admitted DAG"

def commandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace, ``Parser.Command.section,
  ``Parser.Command.end, ``Parser.Command.universe, ``Parser.Command.variable,
  ``Parser.Command.open, ``Parser.Command.export, ``Parser.Command.mutual,
  ``Parser.Command.in, ``Parser.Command.attribute, ``Parser.Command.moduleDoc]

partial def atomWithin (s : Syntax) (value : String) : Bool :=
  s.isAtom && s.getAtomVal == value || s.getArgs.any (atomWithin · value)

partial def identWithin (s : Syntax) (value : Name) : Bool :=
  s.isIdent && s.getId == value || s.getArgs.any (identWithin · value)

def allowedAttributeNames : List Name := [`simp, `instance, `reducible, `semireducible, `irreducible]

def validCandidateFeatures : List Name := [
  `refinement, `step_result, `memory, `mir_ast, `mir_semantics, `rustc_capture]

structure ParseTrustState where
  scopes : List (Bool × Name) := []
  trustDeclarations : Array (String × String) := #[]

def currentNamespace (st : ParseTrustState) : Name :=
  st.scopes.foldl (init := .anonymous) fun acc (isNs, n) =>
    if isNs then acc ++ n else acc

def extractTrustModifier (isTrustedModule : Bool) (allowMacroAttr : Bool)
    (mods : Syntax) : IO (Option String) := do
  let attrsOpt := mods[1]
  if attrsOpt.getArgs.isEmpty then return none
  let attrs := attrsOpt[0]
  let mut trustStatus? : Option String := none
  for elem in attrs[1].getArgs do
    if elem.getKind == ``Parser.Term.attrInstance then
      unless elem.getArgs.size == 2 do fail "unsupported attribute-operation shape"
      if atomWithin elem[0] "scoped" || atomWithin elem[0] "local" then
        fail "scoped/local attribute modifiers are unsupported"
      let attr := elem[1]
      let k := attr.getKind
      if k == ``Parser.Attr.simple then
        let attrName := attr[0].getId
        let extraArgs := attr[1].getArgs
        if attrName == `vetted then
          unless isTrustedModule do fail "trust attribute @[vetted] is only allowed in Trusted modules"
          unless extraArgs.isEmpty do fail "@[vetted] does not accept arguments"
          if trustStatus?.isSome then fail "multiple trust attributes on a single declaration"
          trustStatus? := some "vetted"
        else if attrName == `candidate then
          unless isTrustedModule do fail "trust attribute @[candidate] is only allowed in Trusted modules"
          unless extraArgs.size == 1 && extraArgs[0]!.isIdent do
            fail "@[candidate] requires a single feature identifier"
          let feat := extraArgs[0]!.getId
          unless validCandidateFeatures.contains feat do
            fail s!"unknown candidate feature {feat}"
          if trustStatus?.isSome then fail "multiple trust attributes on a single declaration"
          trustStatus? := some s!"candidate:{feat}"
        else
          unless allowedAttributeNames.contains attrName do fail s!"unsupported attribute {attrName}"
          unless extraArgs.isEmpty do fail s!"unsupported arguments on attribute {attrName}"
      else if k == `Lean.Parser.Attr.macro then
        unless isTrustedModule && allowMacroAttr &&
            (attr[1].getId == ``Parser.Command.declaration || attr[1].getId == ``Parser.Command.mutual) do
          fail "unsupported macro attribute"
        if trustStatus?.isSome && trustStatus? != some "vetted" then
          fail "multiple trust attributes on a single declaration"
        trustStatus? := some "vetted"
      else if k != ``Parser.Attr.instance && k != `Lean.Parser.Attr.simp then
        fail s!"unsupported attribute form {k}"
  return trustStatus?

def inspectAttribute (allowTrustAttrs : Bool) (s : Syntax) : IO Unit := do
  let k := s.getKind
  if k == ``Parser.Attr.simple then
    let attrName := s[0].getId
    if allowTrustAttrs && (attrName == `vetted || attrName == `candidate) then
      pure ()
    else
      unless allowedAttributeNames.contains attrName do fail s!"unsupported attribute {attrName}"
  else if allowTrustAttrs && k == `Lean.Parser.Attr.macro then
    pure ()
  else if k != ``Parser.Attr.instance && k != `Lean.Parser.Attr.simp then
    fail s!"unsupported attribute form {k}"

-- Admission of syntax is a versioned cooperative policy, not a Lean sandbox.
-- A term `unsafe t` can generate a *safe* opaque kernel choice body with a
-- different native implemented_by function. isUnsafe alone does not catch it.
partial def inspectSyntax (allowTrustAttrs : Bool) (s : Syntax) : IO Unit := do
  let k := s.getKind
  if [``Parser.Command.unsafe, ``Parser.Command.partial, ``Parser.Command.meta,
      ``Parser.Command.axiom, ``Parser.Command.example, ``Parser.Command.coinductive,
      ``Parser.Command.openScoped, ``Parser.Command.set_option,
      ``Parser.Term.set_option, ``Parser.Term.unsafe, ``Parser.Tactic.set_option,
      `Lean.byElab, `Lean.Parser.Tactic.runTac,
      `Lean.Parser.Tactic.nativeDecide].contains k then
    fail s!"unsupported source form {k}"
  if k == ``Parser.Command.optDeriving || k == ``Parser.Command.optDefDeriving then
    if atomWithin s "deriving" then fail "deriving clauses are unsupported"
  if k == ``Parser.Term.attrInstance then
    unless s.getArgs.size == 2 do fail "unsupported attribute-operation shape"
    inspectAttribute allowTrustAttrs s[1]
  if k == ``Parser.Command.eraseAttr then
    unless allowedAttributeNames.contains s[1].getId do fail s!"unsupported attribute removal {s[1].getId}"
  if k == `Lean.Parser.Tactic.decide then
    if identWithin s `native || atomWithin s "native" then
      fail "native decide configuration is unsupported"
  if k == ``Parser.Command.declaration then
    inspectSyntax allowTrustAttrs s[0]
    let decl := s[1]
    if decl.getKind == ``Parser.Command.inductive then
      for i in [:decl.getArgs.size] do
        if i == 4 then
          for ctor in decl[4].getArgs do
            for j in [:ctor.getArgs.size] do
              inspectSyntax (if j == 2 then allowTrustAttrs else false) ctor[j]!
        else
          inspectSyntax false decl[i]!
    else
      inspectSyntax false decl
  else if k == ``Parser.Command.declModifiers || k == ``Parser.Term.attributes || k == `null
      || k == ``Parser.Command.mutual || k == ``Parser.Command.in then
    for child in s.getArgs do inspectSyntax allowTrustAttrs child
  else
    for child in s.getArgs do inspectSyntax false child

partial def inspectCommand (isTrustedModule : Bool) (s : Syntax)
    (st : ParseTrustState) : IO ParseTrustState := do
  unless commandKinds.contains s.getKind do fail s!"unsupported command {s.getKind}"
  inspectSyntax isTrustedModule s
  if s.isOfKind ``Parser.Command.namespace then
    let pushed := s[1].getId.components.map (true, ·)
    return { st with scopes := st.scopes ++ pushed }
  if s.isOfKind ``Parser.Command.section then
    let secArgs := s[2].getArgs
    let pushed := if secArgs.isEmpty then [(false, .anonymous)] else secArgs[0]!.getId.components.map (false, ·)
    return { st with scopes := st.scopes ++ pushed }
  if s.isOfKind ``Parser.Command.end then
    let endArgs := s[1].getArgs
    let count := if endArgs.isEmpty then 1 else endArgs[0]!.getId.components.length
    if st.scopes.length < count then fail "unmatched `end` command"
    return { st with scopes := st.scopes.take (st.scopes.length - count) }
  if s.isOfKind ``Parser.Command.in then
    unless s.getArgs.size == 3 do fail "unsupported command-wrapper shape"
    let st1 ← inspectCommand isTrustedModule s[0] st
    return ← inspectCommand isTrustedModule s[2] st1
  if s.isOfKind ``Parser.Command.mutual then
    unless s.getArgs.size == 3 do fail "unsupported mutual-block shape"
    let mut cur := st
    for child in s[1].getArgs do
      cur ← inspectCommand isTrustedModule child cur
    return cur
  if s.isOfKind ``Parser.Command.declaration && isTrustedModule then
    let mods := s[0]
    let decl := s[1]
    let curNs := currentNamespace st
    let relName ←
      if decl.getKind == ``Parser.Command.instance then
        if decl[3].getArgs.isEmpty then
          fail s!"unnamed instance in {curNs}; Trusted instances must be named"
        else
          pure decl[3][0][0].getId
      else
        pure decl[1][0].getId
    let fullName := curNs ++ relName
    let allowMacroAttr := fullName == `Trusted.expandTrustDeclaration
    let some status ← extractTrustModifier true allowMacroAttr mods
      | fail s!"missing @[vetted] or @[candidate <feature>] attribute on Trusted declaration {fullName}"
    let mut nextSt := { st with trustDeclarations := st.trustDeclarations.push (fullName.toString, status) }
    if decl.getKind == ``Parser.Command.inductive then
      for ctor in decl[4].getArgs do
        let ctorFullName := fullName ++ ctor[3].getId
        let ctorStatusOpt ← extractTrustModifier true false ctor[2]
        let ctorStatus := ctorStatusOpt.getD status
        if status.startsWith "candidate:" && ctorStatus == "vetted" then
          fail s!"constructor {ctorFullName} of candidate inductive {fullName} cannot be marked @[vetted]"
        nextSt := { nextSt with trustDeclarations := nextSt.trustDeclarations.push (ctorFullName.toString, ctorStatus) }
    return nextSt
  return st

def inspectSource (parserEnv : Environment) (moduleName : Name) (path : System.FilePath) : IO Json := do
  let text ← IO.FS.readFile path
  let ctx := Parser.mkInputContext text path.toString
  let (header, initial, log) ← Parser.parseHeader ctx
  if log.hasErrors || initial.recovering then fail s!"header parser error in {moduleName}"
  if Elab.HeaderSyntax.isModule header then fail "module headers are unsupported"
  unless atomWithin header.raw "prelude" do fail "explicit prelude is required"
  if atomWithin header.raw "public" || atomWithin header.raw "meta" || atomWithin header.raw "all" then
    fail "explicit import modifiers are unsupported"
  let imports := Elab.HeaderSyntax.imports header
  for imp in imports do
    if imp.importAll || imp.isMeta || !imp.isExported then fail "import modifiers are unsupported"
  let isTrustedModule := moduleName == `Trusted || moduleName.getRoot == `Trusted
  let mut state := initial
  let mut messages := log
  let mut trustState : ParseTrustState := {}
  repeat
    let previous := state.pos
    let (stx, next, nextMessages) := Parser.parseCommand ctx {env := parserEnv, options := {}} state messages
    state := next
    messages := nextMessages
    if messages.hasErrors || state.recovering then fail s!"command parser error in {moduleName}"
    if stx.isOfKind ``Parser.Command.eoi then break
    if state.pos <= previous then throw <| IO.userError "parser made no progress"
    trustState ← inspectCommand isTrustedModule stx trustState
  unless trustState.scopes.isEmpty do fail s!"unclosed namespace or section in {moduleName}"
  return Json.mkObj [
    ("module", toJson moduleName),
    ("imports", toJson imports),
    ("trustDeclarations", toJson trustState.trustDeclarations)]

-- Unlike ConstantInfo.getUsedConstantsAsSet, include all recursor-rule bodies,
-- constructor parents, mutual metadata and literal types, as well as types.
partial def expressionEdges (e : Expr) : IO NameSet := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then fail "open expression in stored declaration"
  let mut result := e.getUsedConstantsAsSet
  let mut pending := [e]
  let mut seen : Std.HashSet Expr := {}
  while !pending.isEmpty do
    let x := pending.head!
    pending := pending.tail!
    if !seen.contains x then
      seen := seen.insert x
      match x with
      | .lit (.natVal _) => result := result.insert `Nat
      | .lit (.strVal _) => result := result.insert `String
      | .app a b => pending := a :: b :: pending
      | .forallE _ a b _ | .lam _ a b _ => pending := a :: b :: pending
      | .letE _ t v b _ => pending := t :: v :: b :: pending
      | .proj _ _ b | .mdata _ b => pending := b :: pending
      | _ => pure ()
  return result

def declarationEdges (ci : ConstantInfo) : IO NameSet := do
  let mut result ← expressionEdges ci.type
  if let some value := ci.value? (allowOpaque := true) then
    result := result ++ (← expressionEdges value)
  match ci with
  | .defnInfo v => result := result ++ .ofList v.all
  | .thmInfo v => result := result ++ .ofList v.all
  | .opaqueInfo v => result := result ++ .ofList v.all
  | .inductInfo v => result := result ++ .ofList (v.all ++ v.ctors)
  | .ctorInfo v => result := result.insert v.induct
  | .recInfo v =>
    result := result ++ .ofList v.all
    for rule in v.rules do
      result := (result.insert rule.ctor) ++ (← expressionEdges rule.rhs)
  | _ => pure ()
  return result

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def origin (env : Environment) (n : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? n | fail s!"unknown declaration origin: {n}"
  let some mod := env.header.modules[idx]? | fail s!"invalid module index: {n}"
  return mod.module

def closure (lookup : Name → IO ConstantInfo) (provenance : Name → IO Name)
    (allowed : Array Name) (axioms : Array (String × String)) (roots : Array Name) : IO (Array Name × Nat) := do
  let mut pending := roots.toList
  let mut visited : NameSet := {}
  let mut reachedAxioms : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !visited.contains n then
      visited := visited.insert n
      let m ← provenance n
      unless allowed.contains m do fail s!"foreign dependency {n} from {m}"
      let ci ← lookup n
      if ci.isAxiom then
        unless axioms.contains (n.toString, m.toString) do fail s!"unapproved axiom {n} from {m}"
        reachedAxioms := reachedAxioms.insert n
      pending := (← declarationEdges ci).toList ++ pending
  return (reachedAxioms.toArray.qsort Name.lt, visited.size)

/-- Enforce Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation:
    Starting from `ci.type` of a claim theorem `rootName`, walk all referenced
    constants (unfolding intermediate definitions in `unfoldModules` such as
    `Mir.<Item>.claim`, while stopping at `trusted ++ foundation`), and reject
    any constant whose module origin belongs to `forbiddenInType` (`theory/`). -/
def checkStatementOrigins (lookup : Name → IO ConstantInfo) (provenance : Name → IO Name)
    (forbiddenInType : Array Name) (unfoldModules : Array Name)
    (rootName : Name) (rootType : Expr) : IO Unit := do
  let initial ← expressionEdges rootType
  let mut pending := initial.toList
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !visited.contains n then
      visited := visited.insert n
      let m ← provenance n
      if forbiddenInType.contains m then
        fail s!"theorem statement of {rootName} depends on untrusted theory declaration {n} from {m}"
      if unfoldModules.contains m then
        let ci ← lookup n
        pending := (← declarationEdges ci).toList ++ pending

def parseTrustMap (j : Json) : IO (Std.HashMap Name String) := do
  let decls ← field (α := Array (String × String)) j "trustDeclarations"
  let mut declMap : Std.HashMap Name String := {}
  for (n, status) in decls do
    declMap := declMap.insert n.toName status
  return declMap

def classifyTrustedConstant (declMap : Std.HashMap Name String) (cName : Name) : IO (String × Name) := do
  let userName := (privateToUserName? cName).getD cName
  let mut cur := userName
  while !cur.isAnonymous do
    if let some status := declMap.get? cur then
      return (status, cur)
    cur := cur.getPrefix
  fail s!"unclassified Trusted constant {cName}"

partial def exprEdgesWithCandidateGuards (e : Expr) :
    IO (NameSet × Array (String × Expr)) := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then fail "open expression in stored declaration"
  let mut result : NameSet := {}
  let mut guarded : Array (String × Expr) := #[]
  let mut pending := [e]
  let mut seen : Std.HashSet Expr := {}
  while !pending.isEmpty do
    let x := pending.head!
    pending := pending.tail!
    if !seen.contains x then
      seen := seen.insert x
      if x.getAppFn.isConstOf `Trusted.candidate then
        let args := x.getAppArgs
        if args.size < 3 then fail "partially applied Trusted.candidate is unsupported"
        let .lit (.strVal feat) := args[0]!
          | fail "Trusted.candidate feature argument must be a string literal"
        unless validCandidateFeatures.contains feat.toName do
          fail s!"unknown candidate feature {feat} in Trusted.candidate"
        result := result.insert `Trusted.candidate
        result := result.insert `String
        pending := args[1]! :: (args.extract 3 args.size).toList ++ pending
        guarded := guarded.push (feat, args[2]!)
      else
        match x with
        | .const n _ => result := result.insert n
        | .lit (.natVal _) => result := result.insert `Nat
        | .lit (.strVal _) => result := result.insert `String
        | .app a b => pending := a :: b :: pending
        | .forallE _ a b _ | .lam _ a b _ => pending := a :: b :: pending
        | .letE _ t v b _ => pending := t :: v :: b :: pending
        | .proj s _ b =>
          result := result.insert s
          pending := b :: pending
        | .mdata _ b => pending := b :: pending
        | _ => pure ()
  return (result, guarded)

def checkTrustedNonContamination (locals : Std.HashMap Name ConstantInfo)
    (statusMap : Std.HashMap Name String)
    (ownerMap : Std.HashMap Name Name) : IO Unit := do
  -- Collect constants that are candidate constructors of vetted inductives, or
  -- appear in the type of such a candidate constructor (used by matcher helpers).
  let mut vettedInductCandidateCtors : Std.HashMap Name (Array (Name × String)) := {}
  let mut allowedInMatcherHelper : NameSet := {}
  for (cName, ci) in locals do
    if let .ctorInfo v := ci then
      if statusMap.get? v.induct == some "vetted" then
        let ctorStatus := statusMap.getD cName "vetted"
        if ctorStatus.startsWith "candidate:" then
          let feat := (ctorStatus.drop 10).toString
          let prev := vettedInductCandidateCtors.getD v.induct #[]
          vettedInductCandidateCtors := vettedInductCandidateCtors.insert v.induct (prev.push (cName, feat))
          allowedInMatcherHelper := allowedInMatcherHelper.insert cName
          for dep in (← expressionEdges ci.type) do
            if let some depStatus := statusMap.get? dep then
              if depStatus.startsWith "candidate:" && depStatus != ctorStatus then
                fail s!"candidate constructor {cName} ({ctorStatus}) of vetted inductive {v.induct} references {dep} ({depStatus}) in its type"
              if depStatus == ctorStatus then
                allowedInMatcherHelper := allowedInMatcherHelper.insert dep
  for (cName, ci) in locals do
    if statusMap.get? cName == some "vetted" then
      let userName := (privateToUserName? cName).getD cName
      let owner := ownerMap.getD cName userName
      let isInductOwner := match locals.get? owner with | some (.inductInfo _) => true | _ => false
      if userName == owner then
        for dep in (← expressionEdges ci.type) do
          if let some depStatus := statusMap.get? dep then
            if depStatus != "vetted" then
              fail s!"vetted declaration {cName} references {depStatus} declaration {dep} in its type"
        if let some val := ci.value? (allowOpaque := true) then
          let (unguardedEdges, guardedBranches) ← exprEdgesWithCandidateGuards val
          for dep in unguardedEdges do
            if let some depStatus := statusMap.get? dep then
              if depStatus != "vetted" then
                fail s!"vetted declaration {cName} references {depStatus} declaration {dep} without a Trusted.candidate guard"
          let mut guardedFeats : Std.HashSet String := {}
          let mut pendingGuarded := guardedBranches.toList
          while !pendingGuarded.isEmpty do
            let (feat, body) := pendingGuarded.head!
            pendingGuarded := pendingGuarded.tail!
            guardedFeats := guardedFeats.insert feat
            let expectedStatus := s!"candidate:{feat}"
            let (bodyEdges, innerGuarded) ← exprEdgesWithCandidateGuards body
            for dep in bodyEdges do
              if let some depStatus := statusMap.get? dep then
                if depStatus != "vetted" && depStatus != expectedStatus then
                  fail s!"Trusted.candidate \"{feat}\" branch in {cName} references {dep} ({depStatus})"
            pendingGuarded := innerGuarded.toList ++ pendingGuarded
          let mut directDeps ← declarationEdges ci
          for (hName, hCi) in locals do
            if hName != cName && ownerMap.get? hName == some owner then
              directDeps := directDeps ++ (← declarationEdges hCi)
          let mut dispatchedCandidateFeats : Std.HashSet String := {}
          for dep in directDeps do
            let depOwner := ownerMap.getD dep dep
            if let some ctors := vettedInductCandidateCtors.get? depOwner then
              for (ctorName, feat) in ctors do
                dispatchedCandidateFeats := dispatchedCandidateFeats.insert feat
                unless guardedFeats.contains feat do
                  fail s!"vetted declaration {cName} matches on candidate constructor {ctorName} (candidate:{feat}) without a Trusted.candidate \"{feat}\" guard"
          for feat in guardedFeats do
            unless dispatchedCandidateFeats.contains feat do
              fail s!"vetted declaration {cName} uses Trusted.candidate \"{feat}\" without matching on a vetted inductive with a candidate:{feat} constructor"
      else if !isInductOwner then
        if let some val := ci.value? (allowOpaque := true) then
          let (unguardedEdges, _) ← exprEdgesWithCandidateGuards val
          for dep in unguardedEdges do
            if let some depStatus := statusMap.get? dep then
              if depStatus != "vetted" && !allowedInMatcherHelper.contains dep then
                fail s!"vetted helper {cName} references {depStatus} declaration {dep} without a Trusted.candidate guard"

def collectActiveCandidateFeatures (lookup : Name → IO ConstantInfo)
    (provenance : Name → IO Name) (trusted : Array Name)
    (statusMap : Std.HashMap Name String) (ownerMap : Std.HashMap Name Name)
    (roots : Array Name) : IO (Array String) := do
  let mut pending := roots.toList
  let mut visited : NameSet := {}
  let mut activeFeats : Std.HashSet String := {}
  let mut deferred : Std.HashMap String (Array Expr) := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !visited.contains n then
      visited := visited.insert n
      let m ← provenance n
      let ci ← lookup n
      if trusted.contains m then
        let status := statusMap.getD n "vetted"
        if status.startsWith "candidate:" then
          let feat := (status.drop 10).toString
          if !activeFeats.contains feat then
            activeFeats := activeFeats.insert feat
            if let some bodies := deferred.get? feat then
              deferred := deferred.erase feat
              for b in bodies do
                pending := (← expressionEdges b).toList ++ pending
          pending := (← declarationEdges ci).toList ++ pending
        else
          let userName := (privateToUserName? n).getD n
          let owner := ownerMap.getD n userName
          let isTopLevelDef := userName == owner && (match ci with | .inductInfo _ | .recInfo _ | .ctorInfo _ => false | _ => true)
          if isTopLevelDef then
            pending := (← expressionEdges ci.type).toList ++ pending
            if let some val := ci.value? (allowOpaque := true) then
              let (unguarded, guarded) ← exprEdgesWithCandidateGuards val
              pending := unguarded.toList ++ pending
              for (feat, body) in guarded do
                if activeFeats.contains feat then
                  pending := (← expressionEdges body).toList ++ pending
                else
                  let prev := deferred.getD feat #[]
                  deferred := deferred.insert feat (prev.push body)
          else
            for dep in (← declarationEdges ci) do
              if (statusMap.getD dep "vetted") == "vetted" then
                pending := dep :: pending
      else
        pending := (← declarationEdges ci).toList ++ pending
  return activeFeats.toArray.qsort (· < ·)

/-- Verify module allowlists, declaration provenance, absence of axioms and
    `unsafe`/`partial` declarations across all non-foundation modules, and
    return the non-foundation declaration map for `toKernelEnv.replay`. -/
def verifyAndCollectLocals (env : Environment) (foundation : Array Name)
    (trusted : Array Name) (allowedAll : Array Name) :
    IO (Std.HashMap Name ConstantInfo × NameSet) := do
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut extraNames : NameSet := {}
  for m in env.header.modules, data in env.header.moduleData do
    unless data.constNames == data.constants.map ConstantInfo.name do fail s!"invalid inventory {m.module}"
    unless allowedAll.contains m.module do fail s!"foreign module {m.module}"
    for ci in data.constants do
      let orig ← origin env ci.name
      if foundation.contains m.module then
        unless foundation.contains orig do fail s!"inventory origin mismatch {ci.name}"
      else
        if locals.contains ci.name then fail s!"duplicate declaration {ci.name}"
        unless orig == m.module do fail s!"inventory origin mismatch {ci.name}"
      let some stored := env.checked.get.find? ci.name | fail s!"missing stored declaration {ci.name}"
      unless stored.type == ci.type && stored.value? true == ci.value? true do
        fail s!"stored declaration differs from inventory {ci.name}"
      if !foundation.contains m.module then
        let isTrusted := trusted.contains m.module
        if ci.isUnsafe || ci.isPartial then
          fail (if isTrusted then s!"unsafe/partial Trusted declaration {ci.name}" else s!"unsafe/partial declaration {ci.name} in {m.module}")
        if ci.isAxiom then
          fail (if isTrusted then s!"Trusted axiom {ci.name}" else s!"strict axiom declaration {ci.name} in {m.module}")
        if ci.hasValue true && (ci.value? true).isNone then fail s!"missing stored body {ci.name}"
        locals := locals.insert ci.name ci
    for n in data.extraConstNames do
      if !foundation.contains m.module then
        unless (← origin env n) == m.module do fail s!"IR helper provenance mismatch {n}"
        if (env.checked.get.find? n).isSome then
          unless locals.contains n do fail s!"uninventoried kernel compiler helper {n}"
        else if trusted.contains m.module then
          extraNames := extraNames.insert n
      else
        unless foundation.contains (← origin env n) do fail s!"IR helper provenance mismatch {n}"
  for (n, _) in env.checked.get.constants do
    if !foundation.contains (← origin env n) && !locals.contains n then
      fail s!"uninventoried constant {n}"
  return (locals, extraNames)

def audit (j : Json) (env : Environment) : IO Json := do
  validateGraph j env
  let trusted ← names j "trusted"
  let foundation ← names j "foundation"
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let declMap ← parseTrustMap j
  let (locals, extraNames) ← verifyAndCollectLocals env foundation trusted (trusted ++ foundation)
  let mut statusMap : Std.HashMap Name String := {}
  let mut ownerMap : Std.HashMap Name Name := {}
  let mut inventory := #[]
  for (cName, ci) in locals do
    let orig ← origin env cName
    let (trustStatus, ownerName) ← classifyTrustedConstant declMap cName
    statusMap := statusMap.insert cName trustStatus
    ownerMap := ownerMap.insert cName ownerName
    inventory := inventory.push <| Json.mkObj [
      ("name", toJson cName), ("module", toJson orig), ("kind", toJson (kind ci)),
      ("trustStatus", toJson trustStatus),
      ("dependencies", toJson ((← declarationEdges ci).toArray.qsort Name.lt))]
  checkTrustedNonContamination locals statusMap ownerMap
  let roots := locals.toArray.map (·.1)
  let lookup n := match env.checked.get.find? n with
    | some ci => pure ci | none => fail s!"missing dependency declaration {n}"
  let (reachedAxioms, visited) ← closure lookup (origin env) (trusted ++ foundation) axiomPolicy roots
  let base ← importEnv j foundation
  let _ ← base.toKernelEnv.replay locals
  return Json.mkObj [
    ("graph", graph env), ("declarations", .arr inventory),
    ("kernelDeclarations", toJson locals.size), ("compilerOnlyNames", toJson extraNames.size),
    ("reachableDeclarations", toJson visited), ("axioms", toJson reachedAxioms),
    ("replay", toJson true)]

def downstreamAudit (j : Json) (env : Environment) : IO Json := do
  let foundation ← names j "foundation"
  let trusted ← names j "trusted"
  let theory ← names j "theory"
  let examples ← names j "examples"
  let claimModules ← names j "claimModules"
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let allDownstream := theory ++ examples ++ claimModules
  let allowedAll := foundation ++ trusted ++ allDownstream
  let (replayLocals, _) ← verifyAndCollectLocals env foundation trusted allowedAll
  let lookup n := match env.checked.get.find? n with
    | some ci => pure ci | none => fail s!"missing dependency declaration {n}"
  let loadedMods : NameSet := .ofList (env.header.modules.toList.map (·.module))
  for reqMod in allDownstream do
    unless loadedMods.contains reqMod do fail s!"missing required downstream module {reqMod}"
  let mut claimTheoremsChecked := 0
  for (cName, ci) in replayLocals do
    let m ← origin env cName
    if claimModules.contains m && kind ci == "theorem" then
      checkStatementOrigins lookup (origin env) (theory ++ examples) claimModules cName ci.type
      claimTheoremsChecked := claimTheoremsChecked + 1
      let _ ← closure lookup (origin env) (foundation ++ trusted ++ theory ++ claimModules) axiomPolicy #[cName]
    else if (theory ++ examples).contains m then
      let _ ← closure lookup (origin env) (foundation ++ trusted ++ theory ++ examples) axiomPolicy #[cName]
  let base ← importEnv j foundation
  let _ ← base.toKernelEnv.replay replayLocals
  return Json.mkObj [
    ("downstreamModules", toJson (allDownstream.map Name.toString)),
    ("replayedDeclarations", toJson replayLocals.size),
    ("claimTheoremsChecked", toJson claimTheoremsChecked),
    ("replay", toJson true)]

def graphTests : IO Json := do
  let hidden := `Foreign.onlyInRule
  let recInfo : ConstantInfo := .recInfo {
    name := `Trusted.rec, levelParams := [], type := .sort .zero,
    all := [`Trusted.Data], numParams := 0, numIndices := 0, numMotives := 0, numMinors := 0,
    rules := [{ctor := `Trusted.ctor, nfields := 0, rhs := .const hidden []}], k := false, isUnsafe := false}
  let edges ← declarationEdges recInfo
  unless [hidden, `Trusted.Data, `Trusted.ctor].all edges.contains do
    throw <| IO.userError "recursor-rule graph regression"
  let opaqueInfo : ConstantInfo := .opaqueInfo {
    name := `Trusted.sealed, levelParams := [], type := .sort .zero,
    value := .const `Foreign.body [], isUnsafe := false}
  unless (← declarationEdges opaqueInfo).contains `Foreign.body do
    throw <| IO.userError "opaque-body graph regression"
  let ctor : ConstantInfo := .ctorInfo {
    name := `Trusted.ctor, levelParams := [], type := .sort .zero,
    induct := `Foreign.Parent, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false}
  unless (← declarationEdges ctor).contains `Foreign.Parent do
    throw <| IO.userError "constructor-parent graph regression"
  let typeOnly : ConstantInfo := .defnInfo {
    name := `Trusted.typeOnly, levelParams := [], type := .const `Foreign.Type [],
    value := .sort .zero, hints := .opaque, safety := .safe}
  unless (← declarationEdges typeOnly).contains `Foreign.Type do
    throw <| IO.userError "type-only graph regression"
  unless (← expressionEdges (.proj `Foreign.Struct 0 (.lit (.strVal "x")))).contains `Foreign.Struct
      && (← expressionEdges (.lit (.strVal "x"))).contains `String
      && (← expressionEdges (.lit (.natVal 3))).contains `Nat do
    throw <| IO.userError "projection/literal graph regression"
  let lookup (n : Name) : IO ConstantInfo := do
    if n == `Trusted.rec then return recInfo
    if n == `Proof.claimHelper then
      return .defnInfo {
        name := n, levelParams := [], type := .sort .zero,
        value := .const `Anneal.SecretHelper [], hints := .opaque, safety := .safe}
    return .defnInfo {
      name := n, levelParams := [], type := .sort .zero,
      value := .sort .zero, hints := .opaque, safety := .safe}
  let provenance n := pure <|
    if n == hidden then `Foreign
    else if n == `Anneal.SecretHelper then `Anneal
    else if n == `Proof.claimHelper then `Proof
    else `Trusted
  let rejected ← try
    let _ ← closure lookup provenance #[`Trusted] #[] #[`Trusted.rec]
    pure false
  catch error => pure <| error.toString.endsWith s!"foreign dependency {hidden} from Foreign"
  unless rejected do throw <| IO.userError "foreign closure was accepted"
  let stmtRejected ← try
    checkStatementOrigins lookup provenance #[`Anneal] #[`Proof] `Proof.prove_foo (.const `Proof.claimHelper [])
    pure false
  catch error =>
    pure <| error.toString.endsWith "theorem statement of Proof.prove_foo depends on untrusted theory declaration Anneal.SecretHelper from Anneal"
  unless stmtRejected do throw <| IO.userError "statement origin leak into theory/ was accepted"
  return Json.mkObj [("graphTests", toJson true)]

def run (j : Json) : IO Json := do
  let mode ← field (α := String) j "mode"
  if mode == "graph-tests" then return ← graphTests
  initSearchPath (← field (α := String) j "sysroot")
  let foundation ← names j "foundation"
  if mode == "preflight" then
    let env ← importEnv j foundation true
    validateGraph j env
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ← sources.mapM fun (n, p) => inspectSource env n.toName p
    return Json.mkObj [("headers", .arr headers), ("graph", graph env)]
  if mode == "preflight-negatives" then
    let env ← importEnv j foundation true
    validateGraph j env
    let cases ← field (α := Array (String × String)) j "cases"
    for (modStr, p) in cases do
      let rejected ← try
        let _ ← inspectSource env modStr.toName p
        pure false
      catch err =>
        pure <| err.toString.startsWith "policy:"
      unless rejected do
        fail s!"negative preflight case `{p}` was not rejected by policy"
    return Json.mkObj [("preflightNegatives", toJson cases.size)]
  if mode == "audit" then
    let trusted ← names j "trusted"
    let env ← importEnv j (foundation ++ trusted)
    return ← audit j env
  if mode == "downstream-audit" then
    let trusted ← names j "trusted"
    let theory ← names j "theory"
    let examples ← names j "examples"
    let claimModules ← names j "claimModules"
    let env ← importEnv j (foundation ++ trusted ++ theory ++ examples ++ claimModules)
    return ← downstreamAudit j env
  throw <| IO.userError s!"unknown inspector mode {mode}"

end TrustedBoundary

def main (args : List String) : IO UInt32 := do
  let [request, output] := args | IO.eprintln "expected request and result files"; return 2
  try
    let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile request)
    let result ← TrustedBoundary.run j
    IO.FS.writeFile output <| (Json.mkObj [("ok", toJson true), ("result", result)]).pretty
    return 0
  catch error =>
    let message := error.toString
    let category := if message.startsWith "policy:" then "policy" else "operational"
    IO.FS.writeFile output <| (Json.mkObj [
      ("ok", toJson false), ("category", toJson category), ("message", toJson message)]).pretty
    IO.eprintln message
    return if category == "policy" then 1 else 2
