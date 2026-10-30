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

/-!
# Trusted Boundary and Kernel Environment Inspector (`TrustedBoundary.lean`)

Pinned to Lean 4.34.1. This file implements the Lean side of Anneal's
mechanical trust-boundary enforcement, paired with the Rust orchestrator in
`trusted/cargo-anneal/src/audit.rs`.

## Security Model and Trust Tiers

Anneal's soundness promise is that `cargo anneal verify` and
`cargo anneal audit-repo` never report that a crate or repository is verified
unless the Lean 4 kernel has checked a proof of `Trusted.CrateTheorem Mir.crate`
that depends only on sound axioms (`{Classical.choice, Quot.sound, propext}`)
and on TCB components permitted by the active release channel and crate trust
policy.

Code in an Anneal verification run falls into four categories:

1. **Foundation (`Init.*` locked by `trusted/lean/foundation-lock.json`):**
   The pinned Lean 4.34.1 prelude and core library modules. Only the three
   standard axioms listed in `foundation-lock.json` are permitted; `sorryAx`
   and all non-locked modules (`Std`, `Lean`, etc.) are excluded.
2. **Vetted TCB (`trusted/lean/`, marked `@[vetted]`):**
   Primitive semantic definitions and theorem envelopes audited against the
   Rust Reference and enabled on both `alpha` and `stable` release channels.
3. **Candidate-Trusted TCB (`trusted/lean/`, marked `@[candidate <feature>]`):**
   TCB definitions (and the `rustc_capture` lowering constructors) that could
   cause a false verification result if buggy, but have not yet completed
   line-by-line Rust Reference auditing. Candidate features are disabled by
   default (`VettedOnly`), unconditionally forbidden on the `stable` release
   channel, and usable on `alpha` only when the target crate explicitly opts in.
4. **Untrusted (`theory/` and `.anneal/Proof.lean`):**
   Derived lemmas, simulation proofs, the plan-guided symbolic evaluator
   (`Anneal.FunctionalTranslation`), and synthesized per-crate proof scripts.
   Bugs in untrusted code must never cause a false positive.

## Threat Model and Two-Phase Enforcement (`"preflight"` and `"audit"`)

Lean's elaborator is not a sandbox: elaborating an arbitrary `.lean` file can
execute `IO` side effects (`#eval`, `run_tac`, `by_elab`), register parser or
elaborator extensions, disable kernel typechecking (`set_option
debug.skipKernelTC true`), attach compiler overrides (`@[extern]`,
`@[implemented_by]`, `@[csimp]`), or use `unsafe t` inside a safe definition
(which elaborates to a safe `opaque` auxiliary constant backed by an unchecked
`@[implemented_by]` hook). Moreover, even in a pure environment with zero
custom axioms, an untrusted proof script could prove a trivial theorem (such as
`theorem verify_crate : True := trivial`) or redefine `Mir.crate` unless
module-origin boundaries and exact theorem types are checked in the compiled
`.olean` environment.

To close both elaboration-time and post-elaboration threat vectors, this
inspector operates in two isolated phases:

- **Phase 1 (`"preflight"`):** Runs *before* Lean compiles any project or crate
  `.lean` file. The inspector loads only `foundation` (`Init.*`) so project
  files cannot inject syntax or macro extensions, parses each `.lean` source
  file with `Parser.parseHeader` and `Parser.parseCommand`, rejects any
  command, term, tactic, or attribute outside a closed pure allowlist, and
  extracts the file's declared imports and `@[vetted]` /
  `@[candidate <feature>]` declaration table.
- **Phase 2 (`"audit"`):** Runs *after* `audit.rs` compiles the admitted
  modules in topological order with `-DElab.async=false` and
  `-Ddebug.skipKernelTC=false`. The inspector loads all compiled `.olean`
  artifacts with `trustLevel := 0`, `plugins := #[]`, `loadExts := false` (so
  no `[init]` extensions execute), and `level := .private` (so `private`
  declarations are visible), and verifies five properties:
  1. **Inventory completeness and provenance (`verifyAndCollectLocals`):**
     Every constant in `env.checked` belongs to an admitted module's
     inventory, matches its stored declaration, and—for all non-foundation
     modules—is neither `isUnsafe`, `isPartial`, nor `isAxiom`.
  2. **Vetted vs. candidate non-contamination
     (`checkTrustedNonContamination`):**
     `@[vetted]` types never reference `@[candidate]` constants, and
     `@[vetted]` bodies reference `@[candidate <feat>]` constants only inside
     `Trusted.candidate "<feat>" (...)` branch guards placed at minor premises
     of eliminators for `@[vetted]` inductives with `@[candidate <feat>]`
     constructors.
  3. **Crate theorem envelope and axiom closure (`closure`):**
     - When auditing a crate (`hasCrate == true`), `Mir.crate : Trusted.Crate`
       is an axiom-free definition originating in `Mir` and `Proof.verify_crate
       : Trusted.CrateTheorem Mir.crate` is a theorem originating in `Proof`.
     - Every reachable axiom across all non-foundation declarations belongs to
       the locked `foundation` axiom allowlist (`{Classical.choice, Quot.sound,
       propext}`).
  4. **Active candidate feature reachability
     (`collectActiveCandidateFeatures`):**
     Traverses the crate's dependency closure (`Mir` and `Proof`), releasing a
     `Trusted.candidate "<feat>"` branch if and only if a `candidate:<feat>`
     constant or constructor is reached, and reports the active candidate
     features for policy enforcement by `audit.rs`.
  5. **Independent kernel replay (`base.toKernelEnv.replay locals`):**
     Replays every non-foundation declaration from scratch through Lean's
     kernel typechecker on top of a freshly imported `foundation`-only
     environment.
-/

open Lean

namespace TrustedBoundary

/-- Throw a policy-rejection error prefixed with `"policy:"` so `main` and
    `audit.rs` distinguish policy violations (exit code 1) from operational or
    I/O failures (exit code 2). -/
def fail (message : String) : IO α := throw <| IO.userError s!"policy:{message}"

/-- Extract and deserialize required field `key` from JSON object `j`. -/
def field [FromJson α] (j : Json) (key : String) : IO α :=
  IO.ofExcept <| j.getObjValAs? α key

/-- Extract an array of dot-separated Lean `Name`s from JSON field `key`. -/
def names (j : Json) (key : String) : IO (Array Name) := do
  return (← field (α := Array String) key (j := j)).map String.toName

/-- Build the explicit module-to-artifact map (`NameMap ImportArtifacts`) from
    the runner's `"artifacts"` table, rejecting duplicate module entries so
    `importModules` resolves every module to the exact runner-admitted `.olean`
    paths without consulting ambient search paths. -/
def artifacts (j : Json) : IO (NameMap ImportArtifacts) := do
  let entries ← field (α := Array (String × Array (Array String))) j "artifacts"
  let mut result := {}
  for (n, parts) in entries do
    if (result.find? n.toName).isSome then fail s!"duplicate artifact module {n}"
    result := result.insert n.toName (.ofArrays (parts.map (·.map System.FilePath.mk)))
  return result

/-- Serialize the compiled module header import DAG of `env` as a JSON object
    mapping each module name to its array of `Import` edges. -/
def graph (env : Environment) : Json :=
  Json.mkObj <| (env.header.modules.zip env.header.moduleData).toList.map fun (m, d) =>
    (m.module.toString, toJson d.imports)

/-- Import `roots` from the explicit artifact map in `j` at `trustLevel := 0`.

    - `extensions` is `true` only during `"preflight"` when importing the
      locked `foundation` (`Init.*`) modules, because Lean's built-in command
      and tactic parsers are registered as environment extensions in `Init`.
      During `"audit"`, `extensions` is `false` (`loadExts := false`), ensuring
      that project `.olean` files cannot execute `[init]` initializers or
      mutate environment extensions when loaded.
    - `level := .private` and `env.setExporting false` load and expose private
      declarations (such as compiler-generated `_match_1` splitters and
      `private` helpers) so they cannot hide from inventory, axiom, or
      non-contamination checks. -/
def importEnv (j : Json) (roots : Array Name) (extensions := false) : IO Environment := do
  let arts ← artifacts j
  if extensions then unsafe enableInitializersExecution
  let env ← importModules (roots.map fun n => {module := n}) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := extensions)
    (level := .private) (arts := arts)
  unless env.header.modules.size == env.header.moduleData.size do
    throw <| IO.userError "module/data array alignment failure"
  return env.setExporting false

/-- Verify that the import DAG recorded inside the loaded `.olean` headers of
    `env` exactly matches the `"graph"` admitted by `audit.rs` during
    `"preflight"`. -/
def validateGraph (j : Json) (env : Environment) : IO Unit := do
  let expected ← field (α := Json) j "graph"
  unless graph env == expected do fail "compiled module/import DAG differs from admitted DAG"

/-- Closed allowlist of top-level command syntax kinds permitted in any
    non-foundation `.lean` source file (`Trusted`, `Anneal`, `Mir`, `Proof`).
    Commands that execute code or extend the parser/elaborator (`#eval`,
    `#check`, `macro`, `elab`, `syntax`, `initialize`, `builtin_initialize`,
    `notation`, `infix`, etc.) are excluded; the single surface macro
    `Trusted.expandTrustDeclaration` is admitted via its `@[macro ...]`
    attribute on a standard `Parser.Command.declaration`. -/
def commandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace, ``Parser.Command.section,
  ``Parser.Command.end, ``Parser.Command.universe, ``Parser.Command.variable,
  ``Parser.Command.open, ``Parser.Command.export, ``Parser.Command.mutual,
  ``Parser.Command.in, ``Parser.Command.attribute, ``Parser.Command.moduleDoc]

/-- Return `true` if `s` or any syntax descendant is an atom equal to
    `value`. -/
def atomWithin (s : Syntax) (value : String) : Bool :=
  (s.find? fun x => x.isAtom && x.getAtomVal == value).isSome

/-- Return `true` if `s` or any syntax descendant is an identifier equal to
    `value`. -/
def identWithin (s : Syntax) (value : Name) : Bool :=
  (s.find? fun x => x.isIdent && x.getId == value).isSome

/-- Closed allowlist of non-trust attributes permitted on declarations.
    Compiler-override and metaprogramming attributes (`@[extern]`,
    `@[implemented_by]`, `@[csimp]`, `@[init]`, `@[app_unexpander]`, etc.) are
    rejected because they can alter runtime or elaboration behavior outside the
    kernel. -/
def allowedAttributeNames : List Name := [`simp, `instance, `reducible, `semireducible, `irreducible]

/-- Closed set of subsystem feature identifiers allowed in
    `@[candidate <feature>]` attributes and `Trusted.candidate "<feature>"`
    term guards. Must match `VALID_CANDIDATE_FEATURES` in `audit.rs`. -/
def validCandidateFeatures : List Name := [
  `refinement, `step_result, `memory, `mir_ast, `mir_semantics, `rustc_capture]

/-- Parser state threaded across commands in `inspectSource` to track open
    `namespace`/`section` scopes and record the trust classification
    (`"vetted"` or `"candidate:<feature>"`) of every declaration in
    `Trusted.*`. -/
structure ParseTrustState where
  /-- Stack of open scopes: `(true, name)` for a `namespace` component (which
      contributes to qualified declaration names) and `(false, name)` for a
      `section` scope (which does not). -/
  scopes : List (Bool × Name) := []
  /-- Pairs `(fullDeclarationName, trustStatus)` collected from `Trusted.*`. -/
  trustDeclarations : Array (String × String) := #[]

/-- Reconstruct the active Lean namespace from `st.scopes`. -/
def currentNamespace (st : ParseTrustState) : Name :=
  st.scopes.foldl (init := .anonymous) fun acc (isNs, n) =>
    if isNs then acc ++ n else acc

/-- Validate a single `Parser.Term.attrInstance` syntax node `elem` and return
    `some "vetted"` or `some "candidate:<feature>"` if `elem` is a trust
    attribute, or `none` if `elem` is an ordinary allowed attribute.

    - `allowTrustAttrs` is `true` only on top-level declarations and inductive
      constructors inside `Trusted.*` modules; trust attributes in `theory/`,
      `Mir`, `Proof`, or nested inside terms are rejected.
    - `allowMacroAttr` is `true` during `inspectSyntax` on `Trusted.*`
      declaration modifiers and during `extractTrustModifier` on
      `Trusted.expandTrustDeclaration` in `Trusted/Refinement.lean`, which
      carries `@[macro Lean.Parser.Command.declaration, macro
      Lean.Parser.Command.mutual]` so Lean strips `@[vetted]` and
      `@[candidate <feature>]` during elaboration after `"preflight"` has
      recorded them. -/
def inspectAttrInstance (allowTrustAttrs : Bool) (allowMacroAttr : Bool)
    (elem : Syntax) : IO (Option String) := do
  unless elem.getArgs.size == 2 do fail "unsupported attribute-operation shape"
  if atomWithin elem[0] "scoped" || atomWithin elem[0] "local" then
    fail "scoped/local attribute modifiers are unsupported"
  let attr := elem[1]
  let k := attr.getKind
  if k == ``Parser.Attr.simple then
    let attrName := attr[0].getId
    let extraArgs := attr[1].getArgs
    if attrName == `vetted then
      unless allowTrustAttrs do fail "trust attribute @[vetted] is only allowed in Trusted modules"
      unless extraArgs.isEmpty do fail "@[vetted] does not accept arguments"
      return some "vetted"
    else if attrName == `candidate then
      unless allowTrustAttrs do fail "trust attribute @[candidate] is only allowed in Trusted modules"
      unless extraArgs.size == 1 && extraArgs[0]!.isIdent do
        fail "@[candidate] requires a single feature identifier"
      let feat := extraArgs[0]!.getId
      unless validCandidateFeatures.contains feat do
        fail s!"unknown candidate feature {feat}"
      return some s!"candidate:{feat}"
    else
      unless allowedAttributeNames.contains attrName do fail s!"unsupported attribute {attrName}"
      unless extraArgs.isEmpty do fail s!"unsupported arguments on attribute {attrName}"
      return none
  else if k == `Lean.Parser.Attr.macro then
    unless allowTrustAttrs && allowMacroAttr &&
        (attr[1].getId == ``Parser.Command.declaration || attr[1].getId == ``Parser.Command.mutual) do
      fail "unsupported macro attribute"
    return some "vetted"
  else if k == ``Parser.Attr.instance || k == `Lean.Parser.Attr.simp then
    return none
  else
    fail s!"unsupported attribute form {k}"

/-- Extract the unique trust classification (`"vetted"` or
    `"candidate:<feature>"`) from a `Parser.Command.declModifiers` node `mods`,
    rejecting declarations that combine multiple trust attributes. -/
def extractTrustModifier (isTrustedModule : Bool) (allowMacroAttr : Bool)
    (mods : Syntax) : IO (Option String) := do
  let attrsOpt := mods[1]
  if attrsOpt.getArgs.isEmpty then return none
  let attrs := attrsOpt[0]
  let mut trustStatus? : Option String := none
  let mut sawMacroAttr := false
  for elem in attrs[1].getArgs do
    if elem.getKind == ``Parser.Term.attrInstance then
      let isMacro := elem.getArgs.size == 2 && elem[1].getKind == `Lean.Parser.Attr.macro
      if let some st ← inspectAttrInstance isTrustedModule allowMacroAttr elem then
        if trustStatus?.isSome && !(isMacro && sawMacroAttr && trustStatus? == some "vetted") then
          fail "multiple trust attributes on a single declaration"
        if isMacro then sawMacroAttr := true
        trustStatus? := some st
  return trustStatus?

/-- Return `true` if `s` is a reserved Lean compiler helper name component that
    user-written declarations in source syntax must not impersonate. -/
def isReservedHelperComponent (s : String) : Bool :=
  s.startsWith "_" || s.startsWith "match_" ||
    ["rec", "recOn", "casesOn", "ctorIdx", "ctorElim", "ctorElimType",
     "noConfusion", "noConfusionType"].contains s

/-- Validate that a user-declared identifier `id` (for a `namespace`, `section`,
    top-level declaration, inductive constructor, structure constructor/field,
    or `where`/`let rec` helper) does not escape the current namespace via
    `_root_` or impersonate a compiler-generated helper name. -/
def validateUserDeclIdent (context : String) (id : Name) : IO Unit := do
  if id.components.any (fun c => c == `_root_ || isReservedHelperComponent c.toString) then
    fail s!"invalid or reserved {context} name {id}"

/-- Recursively validate syntax node `s` during `"preflight"`.

    Why source-syntax inspection is needed in addition to `.olean` kernel
    checks:
    1. Elaboration-time tactics and terms (`by_elab`, `run_tac`,
       `native_decide`, `decide +native`, `bv_decide`, `include_str`, `sleep`,
       `dbg_trace`, `idbg`) can execute arbitrary code, read host files, or
       bypass kernel proof construction during compilation.
    2. `set_option` (at command, term, tactic, or `grind` level) can set
       `debug.skipKernelTC true` or alter elaborator soundness flags.
    3. A term `unsafe t` inside a safe definition elaborates into a *safe*
       `opaque` auxiliary constant with an `@[implemented_by]` override;
       checking `ConstantInfo.isUnsafe` on the top-level definition does not
       catch it.
    4. `deriving` handlers and `computedFields` can synthesize instances or
       `@[csimp]` overrides via metaprograms. -/
partial def inspectSyntax (allowTrustAttrs : Bool) (s : Syntax) : IO Unit := do
  if s.isAtom &&
      ["set_option", "rfl'", "unhygienic", "decide!", "bv_decide",
       "native_decide", "include_str", "by_elab", "run_tac",
       "partial_fixpoint", "coinductive_fixpoint", "inductive_fixpoint"].contains s.getAtomVal then
    fail s!"unsupported syntax keyword {s.getAtomVal}"
  let k := s.getKind
  if [``Parser.Command.unsafe, ``Parser.Command.partial, ``Parser.Command.meta,
      ``Parser.Command.axiom, ``Parser.Command.example, ``Parser.Command.coinductive,
      ``Parser.Command.computedFields, ``Parser.Command.computedField,
      ``Parser.Command.openScoped, ``Parser.Command.set_option,
      ``Parser.Term.set_option, ``Parser.Term.unsafe, ``Parser.Tactic.set_option,
      `Lean.Parser.Tactic.Grind.setOption, `Lean.byElab, `Lean.includeStr,
      `Lean.Parser.Tactic.runTac, `Lean.Parser.Tactic.nativeDecide,
      `Lean.Parser.Tactic.decideBang, `Lean.Parser.Tactic.bvDecide,
      `Lean.Parser.Tactic.rfl', `Lean.Parser.Tactic.unhygienic,
      `Lean.Parser.Tactic.sleep, `Lean.Parser.Term.idbg,
      `Lean.Parser.Term.doIdbg, `Lean.Parser.Term.dbgTrace,
      `Lean.Parser.Term.doDbgTrace, `Lean.Parser.Termination.partialFixpoint,
      `Lean.Parser.Termination.coinductiveFixpoint,
      `Lean.Parser.Termination.inductiveFixpoint].contains k then
    fail s!"unsupported source form {k}"
  if k == ``Parser.Term.attrKind then
    if atomWithin s "scoped" || atomWithin s "local" then
      fail "scoped/local attribute modifiers are unsupported"
  if k == ``Parser.Command.optDeriving || k == ``Parser.Command.optDefDeriving then
    if atomWithin s "deriving" then fail "deriving clauses are unsupported"
  if k == ``Parser.Term.attrInstance then
    let _ ← inspectAttrInstance allowTrustAttrs allowTrustAttrs s
  if k == ``Parser.Command.eraseAttr then
    unless allowedAttributeNames.contains s[1].getId do fail s!"unsupported attribute removal {s[1].getId}"
  if k == `Lean.Parser.Tactic.decide then
    unless s[1].getArgs.isEmpty do
      fail "decide configuration is unsupported"
  if k == `Lean.Parser.Term.letRecDecl then
    let inner := s[2][0]
    if inner.isOfKind `Lean.Parser.Term.letIdDecl || inner.isOfKind `Lean.Parser.Term.letEqnsDecl then
      validateUserDeclIdent "local recursive/where" inner[0].getId
    else
      fail "pattern bindings in local recursive/where declarations are unsupported"
  if k == ``Parser.Command.structCtor then
    validateUserDeclIdent "structure constructor" s[1].getId
  if k == ``Parser.Command.structSimpleBinder then
    validateUserDeclIdent "structure field" s[1].getId
  if k == ``Parser.Command.structExplicitBinder || k == ``Parser.Command.structImplicitBinder
      || k == ``Parser.Command.structInstBinder then
    for idStx in s[2].getArgs do
      validateUserDeclIdent "structure field" idStx.getId
  if k == ``Parser.Command.structParent && !s[0].getArgs.isEmpty then
    validateUserDeclIdent "structure parent projection" s[0][0].getId
  if k == ``Parser.Command.declaration then
    -- Allow trust attributes on the declaration's outer `declModifiers`
    -- (`s[0]`) and on each inductive constructor's `declModifiers` (`ctor[2]`),
    -- but forbid them everywhere else inside the declaration's signature or
    -- body.
    inspectSyntax allowTrustAttrs s[0]
    let decl := s[1]
    if decl.getKind == ``Parser.Command.inductive
        || decl.getKind == ``Parser.Command.classInductive then
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

/-- Validate a top-level command `s` and update `st` with any namespace/section
    scope changes and (when `isTrustedModule` is `true`) the trust
    classifications of all declared constants and inductive constructors.

    Every declaration in a `Trusted.*` module must carry an explicit `@[vetted]`
    or `@[candidate <feature>]` attribute, and every `instance` in `Trusted.*`
    must be explicitly named so its preflight name matches its `.olean`
    `ConstantInfo.name` without running the elaborator's instance-naming
    heuristic. Constructors of an inductive `I` inherit `I`'s trust status by
    default; a `@[vetted]` inductive may mark individual constructors as
    `@[candidate <feature>]` (for incremental language/TCB extensions), whereas
    a `@[candidate <feature>]` inductive is forbidden from marking any of its
    constructors `@[vetted]`. -/
partial def inspectCommand (isTrustedModule : Bool) (s : Syntax)
    (st : ParseTrustState) : IO ParseTrustState := do
  unless commandKinds.contains s.getKind do fail s!"unsupported command {s.getKind}"
  inspectSyntax isTrustedModule s
  if s.isOfKind ``Parser.Command.namespace then
    if !s[0].getArgs.all (·.getArgs.isEmpty) || atomWithin s "noncomputable"
        || atomWithin s "meta" || atomWithin s "public" || atomWithin s "expose" then
      fail "section/namespace modifiers are unsupported"
    let nsId := s[1].getId
    validateUserDeclIdent "namespace" nsId
    let pushed := nsId.components.map (true, ·)
    return { st with scopes := st.scopes ++ pushed }
  if s.isOfKind ``Parser.Command.section then
    if !s[0].getArgs.all (·.getArgs.isEmpty) || atomWithin s "noncomputable"
        || atomWithin s "meta" || atomWithin s "public" || atomWithin s "expose" then
      fail "section/namespace modifiers are unsupported"
    let secArgs := s[2].getArgs
    let pushed ←
      if secArgs.isEmpty then
        pure [(false, .anonymous)]
      else
        let secId := secArgs[0]!.getId
        validateUserDeclIdent "section" secId
        pure (secId.components.map (false, ·))
    return { st with scopes := st.scopes ++ pushed }
  if s.isOfKind ``Parser.Command.end then
    let endArgs := s[1].getArgs
    let count := if endArgs.isEmpty then 1 else endArgs[0]!.getId.components.length
    if st.scopes.length < count then fail "unmatched `end` command"
    if !endArgs.isEmpty then
      let endComps := endArgs[0]!.getId.components
      let popped := (st.scopes.drop (st.scopes.length - count)).map (·.2)
      unless popped == endComps do fail "mismatched `end` command"
    return { st with scopes := st.scopes.take (st.scopes.length - count) }
  if s.isOfKind ``Parser.Command.in then
    unless s.getArgs.size == 3 do fail "unsupported command-wrapper shape"
    if s[0].isOfKind ``Parser.Command.namespace
        || s[0].isOfKind ``Parser.Command.section
        || s[0].isOfKind ``Parser.Command.end then
      fail "scope commands are unsupported inside `in`"
    let st1 ← inspectCommand isTrustedModule s[0] st
    let st2 ← inspectCommand isTrustedModule s[2] st1
    return { st2 with scopes := st.scopes }
  if s.isOfKind ``Parser.Command.mutual then
    unless s.getArgs.size == 3 do fail "unsupported mutual-block shape"
    let mut cur := st
    for child in s[1].getArgs do
      cur ← inspectCommand isTrustedModule child cur
    return cur
  if s.isOfKind ``Parser.Command.declaration then
    let mods := s[0]
    let decl := s[1]
    let curNs := currentNamespace st
    let relName ←
      if decl.getKind == ``Parser.Command.instance then
        if decl[3].getArgs.isEmpty then
          if isTrustedModule then
            fail s!"unnamed instance in {curNs}; Trusted instances must be named"
          else
            pure .anonymous
        else
          pure decl[3][0][0].getId
      else
        pure decl[1][0].getId
    validateUserDeclIdent "declaration" relName
    let isInd :=
      decl.getKind == ``Parser.Command.inductive
        || decl.getKind == ``Parser.Command.classInductive
    if isInd then
      for ctor in decl[4].getArgs do
        validateUserDeclIdent "constructor" ctor[3].getId
    if isTrustedModule then
      let fullName := curNs ++ relName
      -- Only `Trusted.expandTrustDeclaration` itself may carry `@[macro ...]`.
      let allowMacroAttr := fullName == `Trusted.expandTrustDeclaration
      let some status ← extractTrustModifier true allowMacroAttr mods
        | fail s!"missing @[vetted] or @[candidate <feature>] attribute on Trusted declaration {fullName}"
      let mut nextSt := { st with trustDeclarations := st.trustDeclarations.push (fullName.toString, status) }
      if isInd then
        for ctor in decl[4].getArgs do
          let ctorFullName := fullName ++ ctor[3].getId
          let ctorStatusOpt ← extractTrustModifier true false ctor[2]
          let ctorStatus := ctorStatusOpt.getD status
          -- A candidate inductive cannot contain a vetted constructor because
          -- constructing or eliminating the inductive requires the candidate
          -- type.
          if status.startsWith "candidate:" && ctorStatus == "vetted" then
            fail s!"constructor {ctorFullName} of candidate inductive {fullName} cannot be marked @[vetted]"
          nextSt := { nextSt with trustDeclarations := nextSt.trustDeclarations.push (ctorFullName.toString, ctorStatus) }
      return nextSt
  return st

/-- Parse and validate a single `.lean` source file during `"preflight"` using
    only the `foundation` parser environment `parserEnv`.

    Requires an explicit `prelude` header so Lean never injects an implicit
    `import Init` edge outside the `foundation-lock.json` subset, and rejects
    `module`, `public`, `meta`, and `import all` header modifiers. -/
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

/-- Collect all constant names referenced anywhere inside `e` without splitting
    `Trusted.candidate` guards, recording primitive literal types (`Nat` and
    `String`) and structure-projection type names (`.proj s _ b`), and rejecting
    open expressions containing free variables, metavariables, or loose bound
    variables. -/
partial def expressionEdges (e : Expr) : IO NameSet := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then fail "open expression in stored declaration"
  let mut result : NameSet := {}
  let mut pending := [e]
  let mut seen : Std.HashSet Expr := {}
  while !pending.isEmpty do
    let x := pending.head!
    pending := pending.tail!
    if !seen.contains x then
      seen := seen.insert x
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
  return result

/-- Strip leading `.forallE` binders and `.mdata` wrappers from `e`. -/
partial def stripForall (e : Expr) : Expr :=
  match e with
  | .forallE _ _ b _ => stripForall b
  | .mdata _ b => stripForall b
  | _ => e

/-- Strip leading `.lam` binders and `.mdata` wrappers from `e`, returning the
    list of binder domain types and the inner body. -/
partial def stripLams (e : Expr) : List Expr × Expr :=
  match e with
  | .lam _ d b _ =>
    let (doms, body) := stripLams b
    (d :: doms, body)
  | .mdata _ b => stripLams b
  | _ => ([], e)

/-- Return `true` if `u` is a compiler-generated `.match_N` or
    `._sparseCasesOn_N` splitter constant. -/
def isMatcherSplitter (u : Name) : Bool :=
  match u with
  | .str _ s => s.startsWith "match_" || s.startsWith "_sparseCasesOn_"
  | _ => false

/-- Return `true` if `u` is a compiler-generated proof helper underneath a
    `.match_N` or `._sparseCasesOn_N` splitter (such as `match_1._proof_1` for
    wildcard arm inequality hypotheses). -/
def isUnderMatcherSplitter (u : Name) (ci : ConstantInfo) : Bool :=
  match ci, u with
  | .thmInfo _, .str p s => isMatcherSplitter p && s.startsWith "_proof_"
  | _, _ => false

/-- Return `true` if `u` is a compiler-generated equational or unfolding theorem
    for a definition (`_eq_N`, `eq_N`, `_congr_simp`, `_unfold`). -/
def isCompilerEqThm (u : Name) (ci : ConstantInfo) : Bool :=
  match ci, u with
  | .thmInfo _, .str _ s =>
    s.startsWith "_eq_" || s.startsWith "eq_" || s.startsWith "_congr_" || s.startsWith "_unfold"
  | _, _ => false

/-- Return `true` if `u` is one of Lean's compiler-generated inductive recursor,
    constructor-index, no-confusion, or `SizeOf` helpers for an extensible
    `@[vetted]` inductive in `extensibleInducts`. -/
def isExtensibleInductHelper (extensibleInducts : NameSet) (u : Name) : Bool :=
  match u with
  | .str p s =>
    extensibleInducts.contains p &&
      ["rec", "recOn", "casesOn", "ctorIdx", "ctorElim", "ctorElimType",
       "noConfusion", "noConfusionType", "_sizeOf_1", "_sizeOf_inst"].contains s
  | _ => false

/-- Derive per-parameter trust statuses (`"vetted"` or `"candidate:<feat>"`) for
    eliminators of extensible `@[vetted]` inductives (`I.rec`, `I.recOn`,
    `I.casesOn`) and compiler-generated matcher splitters (`.match_N` and
    `._sparseCasesOn_N`).

    For `I.rec`, `I.recOn`, and `I.casesOn`, a parameter in the `.forallE`
    telescope of `ci.type` whose stripped return type applies the motive to a
    constructor `ctorName` of `I` receives `statusMap[ctorName]`. For `.match_N`
    and `._sparseCasesOn_N` splitters, parameter `p` receives status
    `"candidate:<feat>"` if and only if `p` is referenced in the splitter's body
    and every occurrence of `p` lies inside a `"candidate:<feat>"` minor-premise
    argument of an eliminator or `ctorElim` call. -/
def deriveEliminatorParamStatuses (locals : Std.HashMap Name ConstantInfo)
    (statusMap : Std.HashMap Name String) (extensibleInducts : NameSet) :
    Std.HashMap Name (Array String) := Id.run do
  let mut result : Std.HashMap Name (Array String) := {}
  for (cName, ci) in locals do
    let u := (privateToUserName? cName).getD cName
    if let .str indName suffix := u then
      if extensibleInducts.contains indName && ["rec", "recOn", "casesOn"].contains suffix then
        if let some (.inductInfo iv) := locals.get? indName then
          let ctorSet : NameSet := .ofList iv.ctors
          let mut cur := ci.type
          let mut statuses : Array String := #[]
          while cur.isForall do
            let .forallE _ dom body _ := cur | break
            let retDom := stripForall dom
            let mut st := "vetted"
            if let some lastArg := retDom.getAppArgs.back? then
              if let .const ctorName _ := lastArg.getAppFn then
                if ctorSet.contains ctorName then
                  st := statusMap.getD ctorName "vetted"
            statuses := statuses.push st
            cur := body
          result := result.insert cName statuses
  let mut changed := true
  while changed do
    changed := false
    for (cName, ci) in locals do
      let u := (privateToUserName? cName).getD cName
      if isMatcherSplitter u && !result.contains cName then
        if let some val := ci.value? (allowOpaque := true) then
          let (doms, body) := stripLams val
          let numParams := doms.length
          let mut paramStates : Array (Option String) := Array.replicate numParams none
          let mut conflict : Array Bool := Array.replicate numParams false
          let mut pending : List (Nat × String × Expr) := [(0, "vetted", body)]
          let mut seen : Std.HashSet (Nat × String × Expr) := {}
          while !pending.isEmpty do
            let item := pending.head!
            pending := pending.tail!
            if !seen.contains item then
              seen := seen.insert item
              let (depth, ctx, x) := item
              if let .bvar idx := x then
                if idx >= depth && idx < depth + numParams then
                  let p := numParams - 1 - (idx - depth)
                  match paramStates[p]! with
                  | none => paramStates := paramStates.set! p (some ctx)
                  | some prev => if prev != ctx then conflict := conflict.set! p true
              else
                let fn := x.getAppFn
                let args := x.getAppArgs
                let mut handledApp := false
                if !args.isEmpty then
                  if let .const target _ := fn then
                    if let .str indName "ctorElim" := (privateToUserName? target).getD target then
                      if extensibleInducts.contains indName && args.size == 5 then
                        if let some (.inductInfo iv) := locals.get? indName then
                          let idxOpt :=
                            args[2]!.rawNatLit? <|>
                              (if args[2]! == mkConst ``Nat.zero then some 0 else none)
                          if let some idx := idxOpt then
                            if h : idx < iv.ctors.length then
                              let ctorName := iv.ctors[idx]
                              let ctorSt := statusMap.getD ctorName "vetted"
                              handledApp := true
                              for j in [:5] do
                                let argCtx := if j == 4 && ctx == "vetted" then ctorSt else ctx
                                pending := (depth, argCtx, args[j]!) :: pending
                    if !handledApp then
                      if let some tStatuses := result.get? target then
                        handledApp := true
                        for j in [:args.size] do
                          let tSt := if j < tStatuses.size then tStatuses[j]! else "vetted"
                          let argCtx := if ctx == "vetted" then tSt else ctx
                          pending := (depth, argCtx, args[j]!) :: pending
                if !handledApp then
                  match x with
                  | .app a b => pending := (depth, ctx, a) :: (depth, ctx, b) :: pending
                  | .lam _ d b _ | .forallE _ d b _ =>
                    pending := (depth, "vetted", d) :: (depth + 1, ctx, b) :: pending
                  | .letE _ t v b _ =>
                    pending :=
                      (depth, "vetted", t) :: (depth, "vetted", v) :: (depth + 1, ctx, b) :: pending
                  | .proj _ _ b | .mdata _ b => pending := (depth, ctx, b) :: pending
                  | _ => pure ()
          let mut finalStatuses : Array String := Array.replicate numParams "vetted"
          let mut hasCandidate := false
          for p in [:numParams] do
            if !conflict[p]! then
              if let some st := paramStates[p]! then
                if st.startsWith "candidate:" then
                  finalStatuses := finalStatuses.set! p st
                  hasCandidate := true
          if hasCandidate then
            result := result.insert cName finalStatuses
            changed := true
  return result

/-- Lexical scope state for the single-pass `extractScopedEdges` traversal:
    - `.vetted`: outside any candidate minor premise or `Trusted.candidate`
      guard.
    - `.minorPremise feat outerFeat?`: at a `"candidate:<feat>"` eliminator
      minor-premise spine (beneath zero or more leading `.lam`, `.letE`, or
      `.mdata` binders), optionally nested inside an outer
      `Trusted.candidate "<outerFeat>"` guard. Only in this state is
      `@Trusted.candidate "<feat>" α body` permitted, and any `.lam` binder
      domain `d` enters `.binderDom feat`.
    - `.binderDom feat`: inside a pattern-binder domain `d` of a
      `"candidate:<feat>"` minor premise.
    - `.guarded feat`: inside the return type `α` or body of a validated
      `@Trusted.candidate "<feat>" α body` guard. -/
inductive Scope where
  | vetted
  | minorPremise (feat : String) (outerFeat? : Option String)
  | binderDom (feat : String)
  | guarded (feat : String)
  deriving BEq, Hashable, Inhabited

/-- Drop any active `.minorPremise` spine when descending into a subexpression
    that is not a minor-premise body (such as `.app` arguments, `.forallE`
    binders, `.letE` types/values, or `.proj` targets). -/
def Scope.nonPremise : Scope → Scope
  | .vetted | .minorPremise _ none => .vetted
  | .guarded outer | .minorPremise _ (some outer) => .guarded outer
  | .binderDom feat => .binderDom feat

/-- Constant dependencies of a kernel `Expr` partitioned by `Scope`. -/
structure ScopedEdges where
  /-- Constants referenced outside any `Trusted.candidate` guard or minor
      premise binder domain. -/
  unguarded : NameSet := {}
  /-- Constants referenced inside pattern-binder domains of
      `"candidate:<feat>"` minor premises, keyed by `feat`. -/
  binderDoms : Std.HashMap String NameSet := {}
  /-- Constants referenced inside `@Trusted.candidate "<feat>" α body` guards,
      keyed by `feat` (with an entry present for every `feat` guard encountered,
      even if its body references only bound variables). -/
  guarded : Std.HashMap String NameSet := {}

/-- Traverse a closed kernel `Expr` `rootExpr` in a single pass under
    eliminator parameter statuses `elimStatuses`, validating that every
    `@Trusted.candidate "<feat>" α body` application occurs in `.minorPremise
    feat _` scope and partitioning all referenced constants into
    `ScopedEdges`. -/
partial def extractScopedEdges (elimStatuses : Std.HashMap Name (Array String))
    (rootExpr : Expr) : IO ScopedEdges := do
  if rootExpr.hasFVar || rootExpr.hasMVar || rootExpr.hasLooseBVars then
    fail "open expression in stored declaration"
  let mut edges : ScopedEdges := {}
  let recordConst (e : ScopedEdges) (sc : Scope) (n : Name) : ScopedEdges :=
    match sc with
    | .vetted | .minorPremise _ none =>
      { e with unguarded := e.unguarded.insert n }
    | .guarded outer | .minorPremise _ (some outer) =>
      let prev := e.guarded.getD outer {}
      { e with guarded := e.guarded.insert outer (prev.insert n) }
    | .binderDom feat =>
      let prev := e.binderDoms.getD feat {}
      { e with binderDoms := e.binderDoms.insert feat (prev.insert n) }
  let mut pending : List (Scope × Expr) := [(.vetted, rootExpr)]
  let mut seen : Std.HashSet (Scope × Expr) := {}
  while !pending.isEmpty do
    let item := pending.head!
    pending := pending.tail!
    if !seen.contains item then
      seen := seen.insert item
      let (sc, x) := item
      let baseSc := sc.nonPremise
      let fn := x.getAppFn
      let args := x.getAppArgs
      if fn.isConstOf `Trusted.candidate then
        unless args.size == 3 do
          fail "partially or over-applied Trusted.candidate is unsupported"
        let .lit (.strVal feat) := args[0]!
          | fail "Trusted.candidate feature argument must be a string literal"
        unless validCandidateFeatures.contains feat.toName do
          fail s!"unknown candidate feature {feat} in Trusted.candidate"
        match sc with
        | .minorPremise expectedFeat _ =>
          unless expectedFeat == feat do
            fail s!"Trusted.candidate \"{feat}\" is only permitted inside a candidate:{feat} eliminator minor premise (found in candidate:{expectedFeat} scope)"
        | _ =>
          fail s!"Trusted.candidate \"{feat}\" is only permitted inside a candidate:{feat} eliminator minor premise"
        edges := recordConst (recordConst edges baseSc `Trusted.candidate) baseSc `String
        let prev := edges.guarded.getD feat {}
        edges := { edges with guarded := edges.guarded.insert feat prev }
        pending := (.guarded feat, args[1]!) :: (.guarded feat, args[2]!) :: pending
      else
        let mut handledElim := false
        if !args.isEmpty then
          if let .const cName _ := fn then
            if !(sc matches .binderDom _) then
              if let some paramStatuses := elimStatuses.get? cName then
                handledElim := true
                edges := recordConst edges baseSc cName
                let outerFeat? :=
                  match baseSc with
                  | .guarded outer => some outer
                  | _ => none
                for j in [:args.size] do
                  let pStatus := if j < paramStatuses.size then paramStatuses[j]! else "vetted"
                  let childScope :=
                    if pStatus.startsWith "candidate:" then
                      .minorPremise (pStatus.drop 10).toString outerFeat?
                    else
                      baseSc
                  pending := (childScope, args[j]!) :: pending
        if !handledElim then
          match x with
          | .const n _ => edges := recordConst edges sc n
          | .lit (.natVal _) => edges := recordConst edges sc `Nat
          | .lit (.strVal _) => edges := recordConst edges sc `String
          | .app a b | .forallE _ a b _ =>
            pending := (baseSc, a) :: (baseSc, b) :: pending
          | .lam _ d b _ =>
            match sc with
            | .minorPremise feat _ =>
              pending := (.binderDom feat, d) :: (sc, b) :: pending
            | _ =>
              pending := (baseSc, d) :: (baseSc, b) :: pending
          | .letE _ t v b _ =>
            pending := (baseSc, t) :: (baseSc, v) :: (sc, b) :: pending
          | .proj s _ b =>
            edges := recordConst edges sc s
            pending := (baseSc, b) :: pending
          | .mdata _ b =>
            pending := (sc, b) :: pending
          | _ => pure ()
  return edges

/-- Collect the complete set of direct kernel constant dependencies of `ci`,
    including its type, its value (with `allowOpaque := true` so `opaque`
    definitions cannot conceal dependencies), mutual-block peers (`v.all`),
    inductive constructors (`v.ctors`), constructor parent inductives
    (`v.induct`), and recursor reduction rule RHS expressions (`rule.rhs`). -/
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

/-- Human-readable kind tag for a kernel `ConstantInfo`. -/
def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

/-- Return the defining module name for kernel constant `n` in `env`. -/
def origin (env : Environment) (n : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? n | fail s!"unknown declaration origin: {n}"
  let some mod := env.header.modules[idx]? | fail s!"invalid module index: {n}"
  return mod.module

/-- Compute the transitive kernel dependency closure of `roots` and verify that
    every reachable axiom `n` (`ci.isAxiom`) with defining module `m ←
    provenance n` appears in the locked `foundation` axiom allowlist `axioms`
    (`{Classical.choice, Quot.sound, propext}`). -/
def closure (lookup : Name → IO ConstantInfo) (provenance : Name → IO Name)
    (axioms : Array (String × String)) (roots : Array Name) : IO (Array Name × Nat) := do
  let mut pending := roots.toList
  let mut visited : NameSet := {}
  let mut reachedAxioms : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !visited.contains n then
      visited := visited.insert n
      let m ← provenance n
      let ci ← lookup n
      if ci.isAxiom then
        unless axioms.contains (n.toString, m.toString) do fail s!"unapproved axiom {n} from {m}"
        reachedAxioms := reachedAxioms.insert n
      pending := (← declarationEdges ci).toList ++ pending
  return (reachedAxioms.toArray.qsort Name.lt, visited.size)

/-- Parse the `"trustDeclarations"` table produced by `"preflight"` into a map
    from `Name` to trust status (`"vetted"` or `"candidate:<feature>"`),
    rejecting duplicate declaration names. -/
def parseTrustMap (j : Json) : IO (Std.HashMap Name String) := do
  let decls ← field (α := Array (String × String)) j "trustDeclarations"
  let mut declMap : Std.HashMap Name String := {}
  for (n, status) in decls do
    let key := n.toName
    if declMap.contains key then fail s!"duplicate trust declaration {n}"
    declMap := declMap.insert key status
  return declMap

/-- Classify a compiled `Trusted.*` kernel constant `cName` by stripping any
    `_private.<module>.0.` prefix (`privateToUserName?`) and walking its name
    prefixes from longest to shortest until an explicit entry in `declMap` is
    found.

    Returning `(status, ownerUserName)` maps both user-written declarations
    (and constructors) to their exact preflight entry and compiler-generated
    auxiliary constants (such as `Foo.rec`, `Foo.casesOn`, `bar.match_1`,
    `bar._eq_1`, or structure field projections) to the trust status and name
    of the owning declaration (`ownerUserName`). Fails closed if `cName` does
    not belong to any classified declaration in `declMap`. -/
def classifyTrustedConstant (declMap : Std.HashMap Name String) (cName : Name) : IO (String × Name) := do
  let userName := (privateToUserName? cName).getD cName
  let mut cur := userName
  while !cur.isAnonymous do
    if let some status := declMap.get? cur then
      return (status, cur)
    cur := cur.getPrefix
  fail s!"unclassified Trusted constant {cName}"

/-- Enforce the two-color non-contamination boundary between `@[vetted]` and
    `@[candidate <feature>]` declarations across all compiled `locals`, and
    return `(extensibleInducts, elimStatuses)` for candidate feature
    reachability.

    1. **Candidate constructors of `@[vetted]` inductives:**
       If constructor `cName` of a `@[vetted]` inductive `v.induct` has status
       `candidate:<feat>`, its field types (`ci.type`) may reference only
       `vetted` or `candidate:<feat>` declarations (never a different candidate
       feature) and may not use `Trusted.candidate`. `v.induct` is recorded in
       `extensibleInducts`, and `cName` together with the owners of any
       `candidate:<feat>` types in `ci.type` are added to
       `allowedInInductHelperOwners`.
    2. **Eliminator parameter statuses (`deriveEliminatorParamStatuses`):**
       Assigns per-parameter trust statuses to `I.rec`, `I.recOn`, `I.casesOn`,
       and compiler-generated `.match_N` / `._sparseCasesOn_N` splitters.
    3. **Unified scoped-edge check (`extractScopedEdges`):**
       - Compiler-generated inductive helpers (`isExtensibleInductHelper`),
         matcher splitters (`isMatcherSplitter`), and splitter proof helpers
         (`isUnderMatcherSplitter`) may not use `Trusted.candidate`; when
         `vetted`, their dependencies may reference only `vetted` constants or
         constants whose owner is in `allowedInInductHelperOwners`.
       - Every other non-equational-theorem declaration in `locals` (whether
         `@[vetted]`, `@[candidate <feat>]`, `theory/`, `Mir`, or `Proof`) must
         have a guard-free type (`extractScopedEdges {} ci.type`) and a
         well-scoped body (`extractScopedEdges elimStatuses val`) whose minor
         premise binder domains (`binderDoms[feat]`) reference only `vetted` or
         `allowedInInductHelperOwners` for `feat` and whose
         `Trusted.candidate "<feat>"` bodies (`guarded[feat]`) reference only
         `vetted` or `candidate:<feat>` constants. When the declaration itself
         is `@[vetted]`, all unguarded dependencies in `typeEdges` and
         `valEdges` (plus `ci.all`) must also be `vetted`. -/
def checkTrustedNonContamination (locals : Std.HashMap Name ConstantInfo)
    (trustedLocals : Std.HashMap Name ConstantInfo)
    (statusMap : Std.HashMap Name String)
    (ownerMap : Std.HashMap Name Name) :
    IO (NameSet × Std.HashMap Name (Array String)) := do
  -- Pass 1: Index `@[candidate <feat>]` constructors of `@[vetted]` inductives
  -- and validate that their field types do not cross-contaminate features.
  let mut extensibleInducts : NameSet := {}
  let mut allowedInInductHelperOwners : NameSet := {}
  for (cName, ci) in trustedLocals do
    if let .ctorInfo v := ci then
      let _ ← extractScopedEdges {} ci.type
      if statusMap.get? v.induct == some "vetted" then
        let ctorStatus := statusMap.getD cName "vetted"
        if ctorStatus.startsWith "candidate:" then
          extensibleInducts := extensibleInducts.insert v.induct
          allowedInInductHelperOwners := allowedInInductHelperOwners.insert cName
          for dep in (← expressionEdges ci.type) do
            if let some depStatus := statusMap.get? dep then
              if depStatus.startsWith "candidate:" && depStatus != ctorStatus then
                fail s!"candidate constructor {cName} ({ctorStatus}) of vetted inductive {v.induct} references {dep} ({depStatus}) in its type"
              if depStatus == ctorStatus then
                allowedInInductHelperOwners :=
                  allowedInInductHelperOwners.insert (ownerMap.getD dep dep)
  let elimStatuses := deriveEliminatorParamStatuses locals statusMap extensibleInducts
  -- Pass 2: Verify every non-equational-theorem declaration in `locals` and
  -- record guarded features per `@[vetted]` owner.
  let mut ownerGuardedFeats : Std.HashMap Name (Std.HashSet String) := {}
  for (cName, ci) in locals do
    let userName := (privateToUserName? cName).getD cName
    let isVetted := statusMap.get? cName == some "vetted"
    let isInductDef :=
      match ci with
      | .inductInfo _ => extensibleInducts.contains cName
      | _ => false
    if isInductDef || isExtensibleInductHelper extensibleInducts userName
        || isMatcherSplitter userName || isUnderMatcherSplitter userName ci then
      let _ ← extractScopedEdges {} ci.type
      if let some val := ci.value? (allowOpaque := true) then
        let _ ← extractScopedEdges {} val
      if isVetted then
        for dep in (← declarationEdges ci) do
          if let some depStatus := statusMap.get? dep then
            let depOwner := ownerMap.getD dep dep
            if depStatus != "vetted" && !allowedInInductHelperOwners.contains depOwner then
              fail s!"vetted helper {cName} references {depStatus} declaration {dep} without a Trusted.candidate guard"
    else if !isCompilerEqThm userName ci then
      let typeEdges ← extractScopedEdges {} ci.type
      let valEdges ←
        match ci.value? (allowOpaque := true) with
        | some val => extractScopedEdges elimStatuses val
        | none => pure {}
      for (feat, domDeps) in valEdges.binderDoms do
        let expectedStatus := s!"candidate:{feat}"
        for dep in domDeps do
          if let some depStatus := statusMap.get? dep then
            let depOwner := ownerMap.getD dep dep
            if depStatus != "vetted" &&
                !(depStatus == expectedStatus && allowedInInductHelperOwners.contains depOwner) then
              fail s!"declaration {cName} references {dep} ({depStatus}) in minor-premise binder domain"
      for (feat, bodyDeps) in valEdges.guarded do
        let expectedStatus := s!"candidate:{feat}"
        for dep in bodyDeps do
          if let some depStatus := statusMap.get? dep then
            if depStatus != "vetted" && depStatus != expectedStatus then
              fail s!"Trusted.candidate \"{feat}\" branch in {cName} references {dep} ({depStatus})"
      if isVetted then
        for dep in typeEdges.unguarded do
          if let some depStatus := statusMap.get? dep then
            if depStatus != "vetted" then
              fail s!"vetted declaration {cName} references {depStatus} declaration {dep} in its type"
        for dep in valEdges.unguarded ++ NameSet.ofList ci.all do
          if let some depStatus := statusMap.get? dep then
            if depStatus != "vetted" then
              fail s!"vetted declaration {cName} references {depStatus} declaration {dep} without a Trusted.candidate guard"
        let owner := ownerMap.getD cName userName
        let mut guardedFeats := ownerGuardedFeats.getD owner {}
        for (feat, _) in valEdges.guarded do
          guardedFeats := guardedFeats.insert feat
        ownerGuardedFeats := ownerGuardedFeats.insert owner guardedFeats
  -- Pass 3: Verify compiler-generated equational theorems (`_eq_N`,
  -- `_congr_simp`, `_unfold`) of `@[vetted]` definitions against their owner's
  -- guarded feature set.
  for (cName, ci) in trustedLocals do
    let userName := (privateToUserName? cName).getD cName
    if statusMap.get? cName == some "vetted" && isCompilerEqThm userName ci then
      let owner := ownerMap.getD cName userName
      let guardedFeats := ownerGuardedFeats.getD owner {}
      for dep in (← declarationEdges ci) do
        if let some depStatus := statusMap.get? dep then
          let depOwner := ownerMap.getD dep dep
          if depStatus != "vetted" && !allowedInInductHelperOwners.contains depOwner then
            let feat := (depStatus.drop 10).toString
            unless depStatus.startsWith "candidate:" && guardedFeats.contains feat do
              fail s!"vetted equational theorem {cName} references {dep} ({depStatus})"
  return (extensibleInducts, elimStatuses)

/-- Traverse `rootExpr` during candidate feature reachability analysis,
    returning `(immediateConstants, deferredBranches)`.

    Whenever an eliminator argument has status `"candidate:<feat>"` or a
    `@Trusted.candidate "<feat>" α body` guard is encountered:
    - If `activeFeats.contains feat`, traversal continues directly into the
      branch in the same pass.
    - Otherwise, `(feat, branchExpr)` is appended to `deferredBranches` so it is
      traversed if and only if `feat` later enters `activeFeats`. -/
partial def collectCandidateEdges (elimStatuses : Std.HashMap Name (Array String))
    (activeFeats : Std.HashSet String) (rootExpr : Expr) :
    IO (NameSet × Array (String × Expr)) := do
  let mut immediate : NameSet := {}
  let mut deferred : Array (String × Expr) := #[]
  let mut pending : List Expr := [rootExpr]
  let mut seen : Std.HashSet Expr := {}
  while !pending.isEmpty do
    let x := pending.head!
    pending := pending.tail!
    if !seen.contains x then
      seen := seen.insert x
      let fn := x.getAppFn
      let args := x.getAppArgs
      if fn.isConstOf `Trusted.candidate && args.size == 3 then
        if let .lit (.strVal feat) := args[0]! then
          immediate := (immediate.insert `Trusted.candidate).insert `String
          if activeFeats.contains feat then
            pending := args[1]! :: args[2]! :: pending
          else
            deferred := (deferred.push (feat, args[1]!)).push (feat, args[2]!)
      else
        let mut handledElim := false
        if !args.isEmpty then
          if let .const cName _ := fn then
            if let some paramStatuses := elimStatuses.get? cName then
              handledElim := true
              immediate := immediate.insert cName
              for j in [:args.size] do
                let pStatus := if j < paramStatuses.size then paramStatuses[j]! else "vetted"
                if pStatus.startsWith "candidate:" then
                  let feat := (pStatus.drop 10).toString
                  if activeFeats.contains feat then
                    pending := args[j]! :: pending
                  else
                    deferred := deferred.push (feat, args[j]!)
                else
                  pending := args[j]! :: pending
        if !handledElim then
          match x with
          | .const n _ => immediate := immediate.insert n
          | .lit (.natVal _) => immediate := immediate.insert `Nat
          | .lit (.strVal _) => immediate := immediate.insert `String
          | .app a b | .forallE _ a b _ | .lam _ a b _ =>
            pending := a :: b :: pending
          | .letE _ t v b _ =>
            pending := t :: v :: b :: pending
          | .proj s _ b =>
            immediate := immediate.insert s
            pending := b :: pending
          | .mdata _ b =>
            pending := b :: pending
          | _ => pure ()
  return (immediate, deferred)

/-- Compute the sorted list of candidate-trusted features (`@[candidate
    <feat>]`) actively reached by a crate's verification closure (`roots`,
    comprising all declarations in `Mir` and `Proof`).

    Why reachability is demand-driven across `Trusted.candidate "<feat>"`
    guards:
    - A `@[vetted]` or `theory/` definition or theorem may pattern-match on a
      `@[vetted]` inductive that has both `@[vetted]` constructors and
      `@[candidate <feat>]` constructors (with the latter arms wrapped in
      `Trusted.candidate "<feat>" body`).
    - When `collectActiveCandidateFeatures` visits a `@[vetted]` or `theory/`
      definition, it immediately traverses the definition's type and unguarded
      body edges, but *defers* traversing subexpressions inside a
      `"candidate:<feat>"` minor-premise guard unless `<feat>` is in
      `activeFeats`. When visiting a `@[vetted]` extensible inductive, recursor,
      or compiler-generated matcher splitter, it follows only `vetted` edges so
      that merely mentioning or matching on the inductive type does not activate
      its candidate constructors.
    - If `Mir`, `Proof`, or any already-active dependency directly references a
      `candidate:<feat>` constructor or declaration, `<feat>` is inserted into
      `activeFeats`, releasing all deferred `<feat>` branch expressions (which
      are themselves traversed via `collectCandidateEdges elimStatuses
      activeFeats` so nested guards for other features remain deferred until
      those features become active). -/
def collectActiveCandidateFeatures (lookup : Name → IO ConstantInfo)
    (provenance : Name → IO Name) (trusted : Array Name)
    (statusMap : Std.HashMap Name String) (extensibleInducts : NameSet)
    (elimStatuses : Std.HashMap Name (Array String))
    (roots : Array Name) : IO (Array String) := do
  let mut pending := roots.toList
  let mut pendingExprs : List Expr := []
  let mut visited : NameSet := {}
  let mut activeFeats : Std.HashSet String := {}
  let mut deferred : Std.HashMap String (Array Expr) := {}
  while !pending.isEmpty || !pendingExprs.isEmpty do
    while !pendingExprs.isEmpty do
      let e := pendingExprs.head!
      pendingExprs := pendingExprs.tail!
      let (immediate, guarded) ← collectCandidateEdges elimStatuses activeFeats e
      pending := immediate.toList ++ pending
      for (feat, subExpr) in guarded do
        if activeFeats.contains feat then
          pendingExprs := subExpr :: pendingExprs
        else
          let prev := deferred.getD feat #[]
          deferred := deferred.insert feat (prev.push subExpr)
    if !pending.isEmpty then
      let n := pending.head!
      pending := pending.tail!
      if !visited.contains n then
        visited := visited.insert n
        let m ← provenance n
        let ci ← lookup n
        let status := if trusted.contains m then statusMap.getD n "vetted" else "vetted"
        if status.startsWith "candidate:" then
          let feat := (status.drop 10).toString
          if !activeFeats.contains feat then
            activeFeats := activeFeats.insert feat
            if let some bodies := deferred.get? feat then
              deferred := deferred.erase feat
              for b in bodies do
                pendingExprs := b :: pendingExprs
          pending := (← declarationEdges ci).toList ++ pending
        else
          let userName := (privateToUserName? n).getD n
          let isExtInduct :=
            match ci with
            | .inductInfo _ => extensibleInducts.contains n
            | _ => false
          let isAutoHelper :=
            isExtInduct || isExtensibleInductHelper extensibleInducts userName
              || isMatcherSplitter userName || isUnderMatcherSplitter userName ci
          if isAutoHelper then
            for dep in (← declarationEdges ci) do
              if (statusMap.getD dep "vetted") == "vetted" then
                pending := dep :: pending
          else
            pending := (← expressionEdges ci.type).toList ++ pending
            if let some val := ci.value? (allowOpaque := true) then
              pendingExprs := val :: pendingExprs
            else
              for dep in (← declarationEdges ci) do
                if (statusMap.getD dep "vetted") == "vetted" then
                  pending := dep :: pending
  return activeFeats.toArray.qsort (· < ·)

/-- Verify module allowlists, declaration provenance, and the absence of axioms
    and `unsafe`/`partial` declarations across all loaded modules, returning
    `(locals, extraNames)` where `locals` maps every non-foundation constant to
    its `ConstantInfo` for `base.toKernelEnv.replay`.

    Specifically checks that:
    1. Every module in `allowedAll` is loaded in `env.header.modules`, and every
       loaded module belongs to `allowedAll`.
    2. Each module's `constNames` array matches `constants.map
       ConstantInfo.name`,
       and every constant's `origin` matches its module (`foundation` for
       foundation modules; exact `m.module` with no duplicate names for
       non-foundation modules).
    3. Every constant in `data.constants` is present in `env.checked` with the
       exact same `type` and `value? (allowOpaque := true)`.
    4. No non-foundation constant (`Trusted`, `Anneal`, `Mir`, `Proof`) is
       `isUnsafe`, `isPartial`, or `isAxiom`, or lacks a body when
       `ci.hasValue true`—even if that constant is never referenced by a
       theorem—and no non-`Trusted` module declares a constant in the `Trusted`
       namespace.
    5. Every compiler-only IR helper (`data.extraConstNames`) has matching
       module provenance, and no non-foundation constant exists in `env.checked`
       outside `locals`. -/
def verifyAndCollectLocals (env : Environment) (foundation : Array Name)
    (trusted : Array Name) (allowedAll : Array Name) :
    IO (Std.HashMap Name ConstantInfo × NameSet) := do
  let loadedMods : NameSet := .ofList (env.header.modules.toList.map (·.module))
  for reqMod in allowedAll do
    unless loadedMods.contains reqMod do fail s!"missing required module {reqMod}"
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
        if !isTrusted then
          let userName := (privateToUserName? ci.name).getD ci.name
          if userName == `Trusted || userName.getRoot == `Trusted then
            fail s!"non-Trusted module {m.module} cannot declare constant {ci.name} in Trusted namespace"
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

/-- Execute Phase 2 (`"audit"`) on the compiled `.olean` environment `env`.

    When `hasCrate` is `false` (`cargo anneal audit-repo`), audits the
    repository's `trusted/lean/` (`trusted`) and `theory/` (`theory`) modules.
    When `hasCrate` is `true` (`cargo anneal verify`), additionally audits the
    target crate's `.anneal/Mir.lean` (`Mir`) and `.anneal/Proof.lean`
    (`Proof`):

    - **Why `Mir.crate` and `Proof.verify_crate` are checked by module origin,
      kind, universe parameters, axiom closure, and exact kernel `Expr`
      equality:**
      `Mir.crate` represents the lowered Rust crate and its specifications as an
      axiom-free, universe-monomorphic `Trusted.Crate` definition in `Mir`
      (which `audit.rs` and `validateGraph` restrict to importing only
      `foundation ++ trusted`). Checking `proofCi.type == Expr.app (Expr.const
      ``Trusted.CrateTheorem []) (Expr.const ``Mir.crate [])` (with
      `trustedLocals` provenance on `Trusted.Crate` and `Trusted.CrateTheorem`
      and empty `levelParams`) guarantees that the theorem proved by the
      untrusted `Proof` module is literally `Trusted.CrateTheorem Mir.crate`—not
      `True` or a spoofed predicate from `theory/`—while allowing `Proof`'s
      proof term (`ci.value?`) to use arbitrary pure lemmas and evaluators from
      `theory/`.
    - **Why `base.toKernelEnv.replay locals` runs at the end:**
      Importing `.olean` files into `Environment` trusts the serialized
      `.olean` constant table. Replaying all `locals` (`Trusted`, `Anneal`,
      `Mir`, and `Proof`) into a fresh `foundation`-only `Kernel.Environment`
      forces Lean's kernel typechecker to re-verify every definition and theorem
      body from scratch. -/
def audit (j : Json) (env : Environment) (foundation : Array Name)
    (trusted : Array Name) (theory : Array Name) (hasCrate : Bool) : IO Json := do
  validateGraph j env
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let declMap ← parseTrustMap j
  let crateModules : Array Name := if hasCrate then #[`Mir, `Proof] else #[]
  let allowedAll := foundation ++ trusted ++ theory ++ crateModules
  let (locals, extraNames) ← verifyAndCollectLocals env foundation trusted allowedAll
  let lookup n := match env.checked.get.find? n with
    | some ci => pure ci | none => fail s!"missing dependency declaration {n}"
  let mut trustedLocals : Std.HashMap Name ConstantInfo := {}
  let mut statusMap : Std.HashMap Name String := {}
  let mut ownerMap : Std.HashMap Name Name := {}
  let mut matchedDeclKeys : NameSet := {}
  let mut inventory := #[]
  let mut trustedRoots : Array Name := #[]
  let mut allLocalRoots : Array Name := #[]
  let mut crateRoots : Array Name := #[]
  for (cName, ci) in locals do
    allLocalRoots := allLocalRoots.push cName
    let orig ← origin env cName
    if trusted.contains orig then
      let (trustStatus, ownerName) ← classifyTrustedConstant declMap cName
      let userName := (privateToUserName? cName).getD cName
      matchedDeclKeys := matchedDeclKeys.insert userName
      matchedDeclKeys := matchedDeclKeys.insert ownerName
      trustedLocals := trustedLocals.insert cName ci
      statusMap := statusMap.insert cName trustStatus
      ownerMap := ownerMap.insert cName ownerName
      trustedRoots := trustedRoots.push cName
      inventory := inventory.push <| Json.mkObj [
        ("name", toJson cName), ("module", toJson orig), ("kind", toJson (kind ci)),
        ("trustStatus", toJson trustStatus),
        ("dependencies", toJson ((← declarationEdges ci).toArray.qsort Name.lt))]
    else if orig == `Mir || orig == `Proof then
      crateRoots := crateRoots.push cName
  for (declKey, _) in declMap do
    unless matchedDeclKeys.contains declKey do
      fail s!"unmatched trust declaration {declKey}"
  let (extensibleInducts, elimStatuses) ←
    checkTrustedNonContamination locals trustedLocals statusMap ownerMap
  let (allAxioms, allVisited) ← closure lookup (origin env) axiomPolicy allLocalRoots
  let report ←
    if !hasCrate then
      pure <| Json.mkObj [
        ("graph", graph env), ("declarations", .arr inventory),
        ("kernelDeclarations", toJson trustedLocals.size),
        ("replayedDeclarations", toJson locals.size),
        ("compilerOnlyNames", toJson extraNames.size),
        ("reachableDeclarations", toJson allVisited),
        ("axioms", toJson allAxioms), ("replay", toJson true)]
    else
      unless trustedLocals.contains `Trusted.Crate do
        fail "Trusted.Crate must originate in a Trusted module"
      unless trustedLocals.contains `Trusted.CrateTheorem do
        fail "Trusted.CrateTheorem must originate in a Trusted module"
      let some mirCrateCi := env.checked.get.find? `Mir.crate
        | fail "missing required declaration Mir.crate in Mir"
      unless (← origin env `Mir.crate) == `Mir do fail "Mir.crate must originate in module Mir"
      unless kind mirCrateCi == "definition" do fail s!"Mir.crate must be a definition, found {kind mirCrateCi}"
      unless mirCrateCi.levelParams.isEmpty do
        fail "Mir.crate must not have universe parameters"
      let expectedCrateType := Expr.const `Trusted.Crate []
      unless mirCrateCi.type == expectedCrateType do
        fail s!"Mir.crate has type {mirCrateCi.type}, expected Trusted.Crate"
      let _ ← closure lookup (origin env) #[] #[`Mir.crate]
      let some proofCi := env.checked.get.find? `Proof.verify_crate
        | fail "missing required theorem Proof.verify_crate in Proof"
      unless (← origin env `Proof.verify_crate) == `Proof do fail "Proof.verify_crate must originate in module Proof"
      unless kind proofCi == "theorem" do fail s!"Proof.verify_crate must be a theorem, found {kind proofCi}"
      unless proofCi.levelParams.isEmpty do
        fail "Proof.verify_crate must not have universe parameters"
      let expectedTheoremType := Expr.app (Expr.const `Trusted.CrateTheorem []) (Expr.const `Mir.crate [])
      unless proofCi.type == expectedTheoremType do
        fail s!"Proof.verify_crate has type {proofCi.type}, expected Trusted.CrateTheorem Mir.crate"
      let (crateAxioms, crateVisited) ← closure lookup (origin env) axiomPolicy #[`Proof.verify_crate]
      let candidateFeatures ←
        collectActiveCandidateFeatures lookup (origin env) trusted statusMap
          extensibleInducts elimStatuses crateRoots
      pure <| Json.mkObj [
        ("verifiedTheorem", toJson "Proof.verify_crate"),
        ("expectedType", toJson "Trusted.CrateTheorem Mir.crate"),
        ("replayedDeclarations", toJson locals.size),
        ("reachableDeclarations", toJson crateVisited),
        ("axioms", toJson crateAxioms),
        ("candidateFeatures", toJson candidateFeatures),
        ("replay", toJson true)]
  -- Replay all non-foundation constants from scratch in a clean kernel
  -- environment containing only `foundation` (`Init.*`).
  let base ← importEnv j foundation
  let _ ← base.toKernelEnv.replay locals
  return report

/-- Dispatch `"preflight"` or `"audit"` from the JSON request `j`. -/
def run (j : Json) : IO Json := do
  let mode ← field (α := String) j "mode"
  initSearchPath (← field (α := String) j "sysroot")
  let foundation ← names j "foundation"
  if mode == "preflight" then
    let env ← importEnv j foundation true
    validateGraph j env
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ← sources.mapM fun (n, p) => inspectSource env n.toName p
    return Json.mkObj [("headers", .arr headers), ("graph", graph env)]
  if mode == "audit" then
    let trusted ← names j "trusted"
    let theory ← names j "theory"
    let hasCrate ← field (α := Bool) j "hasCrate"
    let crateModules : Array Name := if hasCrate then #[`Mir, `Proof] else #[]
    let env ← importEnv j (foundation ++ trusted ++ theory ++ crateModules)
    return ← audit j env foundation trusted theory hasCrate
  throw <| IO.userError s!"unknown inspector mode {mode}"

end TrustedBoundary

/-- CLI entry point invoked by `audit.rs` via `lean --run TrustedBoundary.lean
    <request.json> <result.json>`. Exit code 0 indicates success, 1 indicates a
    policy rejection (`"policy:..."`), and 2 indicates an operational
    failure. -/
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
