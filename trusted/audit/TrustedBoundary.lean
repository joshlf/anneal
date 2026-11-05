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

Pinned to Lean 4.34.1, commit
`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`. `trusted/audit`
invokes this file in two phases over JSON IPC (`run` and `main`):

- **`"preflight"`** parses every non-foundation `.lean` source against the
  locked foundation environment only. It admits a closed command, attribute,
  and identifier grammar and reads each `Trusted` module's trust tier from its
  `-- anneal-trust-tier: <tier>` directive.
- **`"audit"`** loads the compiled `.olean` files with `trustLevel := 0`,
  `plugins := #[]`, and `loadExts := false`, and checks the kernel environment:
  declaration provenance and inventory, the foundation axiom allowlist,
  module-level trust-tier separation, `Trusted` namespace hygiene, and a full
  kernel replay of every non-foundation constant (`base.toKernelEnv.replay`).

## Module-level trust tiers

Every kernel constant has a unique origin module (`origin env n`, read directly
from `env.getModuleIdxFor? n` in the `.olean`), and its trust tier is determined
solely by that origin module:

| Tier | Origin module |
| :--- | :--- |
| `foundation` | locked foundation modules (`Init.*`) |
| `vetted`, `candidate:<feature>` | `Trusted` modules (`trusted/lean/`) |
| `theory` | `theory/` modules (`Anneal.*`) |

Every constant compiled into a `Trusted` module `m`—including user declarations,
constructors, recursors (`rec`), auxiliary recursors (`casesOn`, `recOn`,
`noConfusion`, `below`, `brecOn`), structure projections, matchers (`match_1`),
equation lemmas (`eq_1`), and `where`/`private` helpers—has origin module `m`
in the `.olean` and therefore inherits `m`'s module tier without surface-syntax
name prediction or compiler-suffix heuristics.

The audit enforces two rules on the kernel dependency graph (`declarationEdges`):

- **Origin rule:** a `Trusted` constant refers only to `foundation` and
  `Trusted` constants (never `theory`).
- **Vetted rule:** a `vetted` constant refers only to `foundation` and `vetted`
  constants (never `candidate:<feature>`).
-/

open Lean

namespace TrustedBoundary

/-- Throw a policy-rejection error prefixed with `"policy:"` (exit code 1). -/
def fail (message : String) : IO α :=
  throw <| IO.userError s!"policy:{message}"

/-- Extract and deserialize required field `key` from JSON object `j`. -/
def field [FromJson α] (j : Json) (key : String) : IO α :=
  IO.ofExcept <| j.getObjValAs? α key

/-- Extract an array of dot-separated Lean `Name`s from JSON field `key`. -/
def names (j : Json) (key : String) : IO (Array Name) := do
  return (← field (α := Array String) j key).map String.toName

/-- Build the explicit module-to-artifact map (`NameMap ImportArtifacts`) from
`"artifacts"`, rejecting duplicate module entries. -/
def artifacts (j : Json) : IO (NameMap ImportArtifacts) := do
  let entries ← field (α := Array (String × Array (Array String))) j "artifacts"
  let mut result := {}
  for (n, parts) in entries do
    if (result.find? n.toName).isSome then
      fail s!"duplicate artifact module {n}"
    result := result.insert n.toName
      (.ofArrays (parts.map (·.map System.FilePath.mk)))
  return result

/-- Serialize the compiled module header import DAG of `env` as JSON. -/
def graph (env : Environment) : Json :=
  Json.mkObj <|
    (env.header.modules.zip env.header.moduleData).toList.map fun (m, d) =>
      (m.module.toString, toJson d.imports)

/-- Import `roots` from the explicit artifact map in `j` at `trustLevel := 0`
with `level := .private`. -/
def importEnv (j : Json) (roots : Array Name)
    (extensions := false) : IO Environment := do
  let arts ← artifacts j
  if extensions then unsafe enableInitializersExecution
  let env ← importModules (roots.map fun n => { module := n }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := extensions)
    (level := .private) (arts := arts)
  unless env.header.modules.size == env.header.moduleData.size do
    throw <| IO.userError "module/data array alignment failure"
  return env.setExporting false

/-- Verify that the import DAG in `env` matches `"graph"` from `"preflight"`. -/
def validateGraph (j : Json) (env : Environment) : IO Unit := do
  let expected ← field (α := Json) j "graph"
  unless graph env == expected do
    fail "compiled module/import DAG differs from admitted DAG"

/-! ## Phase 1: source preflight -/

/-- Closed allowlist of top-level command syntax kinds permitted in source
files. -/
def commandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.universe,
  ``Parser.Command.variable, ``Parser.Command.open, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in, ``Parser.Command.attribute,
  ``Parser.Command.moduleDoc]

/-- Return `true` if `s` or any syntax descendant is an atom equal to `val`. -/
def atomWithin (s : Syntax) (val : String) : Bool :=
  (s.find? fun x => x.isAtom && x.getAtomVal == val).isSome

/-- Closed allowlist of attributes permitted on declarations. -/
def allowedAttributeNames : List Name :=
  [`simp, `instance, `reducible, `semireducible, `irreducible]

/-- Closed set of feature identifiers allowed in
`-- anneal-trust-tier: candidate:<feature>`. -/
def validCandidateFeatures : List Name :=
  [`refinement, `step_result, `memory, `mir_ast, `mir_semantics, `rustc_capture]

/-- Extract the module-level `-- anneal-trust-tier: <tier>` directive from
`text`. Every `Trusted` module must declare a single valid tier (`vetted` or
`candidate:<feature>`), and non-`Trusted` modules may not declare one. -/
def extractModuleTier (isTrustedModule : Bool) (moduleName : Name)
    (text : String) : IO (Option String) := do
  let mut tier? : Option String := none
  for rawLine in text.splitOn "\n" do
    let line := rawLine.trimAscii.toString
    if line.startsWith "-- anneal-trust-tier:" then
      unless isTrustedModule do
        fail s!"trust tier directive is only allowed in Trusted modules ({moduleName})"
      if tier?.isSome then
        fail s!"multiple trust tier directives in {moduleName}"
      let t := (line.drop 21).trimAscii.toString
      if t == "vetted" then
        tier? := some "vetted"
      else if t.startsWith "candidate:" then
        let feat := (t.drop 10).toString.toName
        unless validCandidateFeatures.contains feat do
          fail s!"unknown candidate feature {feat} in {moduleName}"
        tier? := some t
      else
        fail s!"invalid trust tier {t} in {moduleName}"
  if isTrustedModule && tier?.isNone then
    fail s!"missing `-- anneal-trust-tier: vetted` or `-- anneal-trust-tier: candidate:<feature>` in {moduleName}"
  return tier?

/-- Validate a single `Parser.Term.attrInstance` syntax node `elem`. -/
def inspectAttrInstance (elem : Syntax) : IO Unit := do
  unless elem.getArgs.size == 2 do fail "unsupported attribute-operation shape"
  if atomWithin elem[0] "scoped" || atomWithin elem[0] "local" then
    fail "scoped/local attribute modifiers are unsupported"
  let attr := elem[1]
  let k := attr.getKind
  if k == ``Parser.Attr.simple then
    let attrName := attr[0].getId
    unless allowedAttributeNames.contains attrName do
      fail s!"unsupported attribute {attrName}"
    unless attr[1].getArgs.isEmpty do
      fail s!"unsupported arguments on attribute {attrName}"
  else if k == ``Parser.Attr.instance || k == `Lean.Parser.Attr.simp then
    pure ()
  else
    fail s!"unsupported attribute form {k}"

/-- Recursively validate syntax node `s` during `"preflight"`. -/
partial def inspectSyntax (s : Syntax) : IO Unit := do
  if s.isIdent then
    let id := s.getId
    if !id.isAnonymous &&
        (id.hasMacroScopes || id.eraseMacroScopes != id ||
         id.toString.isEmpty ||
         id.components.any (fun c =>
           match c with
           | .str .anonymous seg => seg.isEmpty || seg == "_root_"
           | _ => true)) then
      fail s!"invalid identifier {id}"
  if s.isAtom &&
      ["set_option", "rfl'", "unhygienic", "decide!", "bv_decide",
       "native_decide", "include_str", "by_elab", "run_tac",
       "with_decl_name%", "private_decl%", "decl_name%",
       "partial_fixpoint", "coinductive_fixpoint",
       "inductive_fixpoint"].contains s.getAtomVal then
    fail s!"unsupported syntax keyword {s.getAtomVal}"
  let k := s.getKind
  if [``Parser.Command.unsafe, ``Parser.Command.partial, ``Parser.Command.meta,
      ``Parser.Command.axiom, ``Parser.Command.example,
      ``Parser.Command.coinductive, ``Parser.Command.computedFields,
      ``Parser.Command.computedField, ``Parser.Command.openScoped,
      ``Parser.Command.set_option, ``Parser.Term.set_option,
      ``Parser.Term.unsafe, ``Parser.Tactic.set_option,
      `Lean.Parser.Tactic.Grind.setOption, `Lean.byElab, `Lean.includeStr,
      `Lean.Parser.Tactic.runTac, `Lean.Parser.Tactic.nativeDecide,
      `Lean.Parser.Tactic.decideBang, `Lean.Parser.Tactic.bvDecide,
      `Lean.Parser.Tactic.rfl', `Lean.Parser.Tactic.unhygienic,
      `Lean.Parser.Tactic.sleep, `Lean.Parser.Tactic.dbgTrace,
      `Lean.Parser.Term.idbg, `Lean.Parser.Term.doIdbg,
      `Lean.Parser.Term.dbgTrace, `Lean.Parser.Term.doDbgTrace,
      `Lean.Parser.Term.withDeclName, `Lean.Parser.Term.privateDecl,
      `Lean.Parser.Term.declName, `Lean.Parser.Termination.partialFixpoint,
      `Lean.Parser.Termination.coinductiveFixpoint,
      `Lean.Parser.Termination.inductiveFixpoint].contains k then
    fail s!"unsupported source form {k}"
  if k == ``Parser.Term.attrKind then
    if atomWithin s "scoped" || atomWithin s "local" then
      fail "scoped/local attribute modifiers are unsupported"
  if k == ``Parser.Command.optDeriving ||
      k == ``Parser.Command.optDefDeriving then
    if atomWithin s "deriving" then fail "deriving clauses are unsupported"
  if k == ``Parser.Term.attrInstance then
    inspectAttrInstance s
  if k == ``Parser.Command.eraseAttr then
    unless allowedAttributeNames.contains s[1].getId do
      fail s!"unsupported attribute removal {s[1].getId}"
  if k == `Lean.Parser.Tactic.decide then
    unless s[1].getArgs.all (·.getArgs.isEmpty) do
      fail "decide configuration is unsupported"
  for child in s.getArgs do inspectSyntax child

/-- Validate a top-level command `s` during `"preflight"`. -/
partial def inspectCommand (s : Syntax) : IO Unit := do
  unless commandKinds.contains s.getKind do
    fail s!"unsupported command {s.getKind}"
  inspectSyntax s
  if s.isOfKind ``Parser.Command.open then
    if atomWithin s "scoped" then
      fail "open scoped is unsupported"
  if s.isOfKind ``Parser.Command.namespace ||
      s.isOfKind ``Parser.Command.section then
    if !s[0].getArgs.all (·.getArgs.isEmpty) || atomWithin s "noncomputable" ||
        atomWithin s "meta" || atomWithin s "public" ||
        atomWithin s "expose" then
      fail "section/namespace modifiers are unsupported"
  if s.isOfKind ``Parser.Command.in then
    unless s.getArgs.size == 3 do fail "unsupported command-wrapper shape"
    unless [``Parser.Command.open, ``Parser.Command.variable].contains
        s[0].getKind do
      fail "only `open` and `variable` commands are permitted on the LHS of `in`"
    if (s.find? fun x =>
        [``Parser.Command.namespace, ``Parser.Command.section,
         ``Parser.Command.end, ``Parser.Command.mutual].contains
          x.getKind).isSome then
      fail "scope or mutual commands are unsupported inside `in`"
    inspectCommand s[0]
    inspectCommand s[2]
  if s.isOfKind ``Parser.Command.mutual then
    unless s.getArgs.size == 3 do fail "unsupported mutual-block shape"
    for child in s[1].getArgs do
      inspectCommand child
  if s.isOfKind ``Parser.Command.declaration then
    let decl := s[1]
    unless [``Parser.Command.abbrev, ``Parser.Command.definition,
            ``Parser.Command.theorem, ``Parser.Command.opaque,
            ``Parser.Command.instance, ``Parser.Command.inductive,
            ``Parser.Command.classInductive,
            ``Parser.Command.structure].contains decl.getKind do
      fail s!"unsupported declaration kind {decl.getKind}"

/-- Parse and validate a single `.lean` source file during `"preflight"`. -/
def inspectSource (parserEnv : Environment) (moduleName : Name)
    (path : System.FilePath) : IO Json := do
  let text ← IO.FS.readFile path
  let isTrustedModule :=
    moduleName == `Trusted || moduleName.getRoot == `Trusted
  let tier? ← extractModuleTier isTrustedModule moduleName text
  let ctx := Parser.mkInputContext text path.toString
  let (header, initial, log) ← Parser.parseHeader ctx
  if log.hasErrors || initial.recovering then
    fail s!"header parser error in {moduleName}"
  if Elab.HeaderSyntax.isModule header then
    fail "module headers are unsupported"
  unless atomWithin header.raw "prelude" do
    fail "explicit prelude is required"
  if atomWithin header.raw "public" || atomWithin header.raw "meta" ||
      atomWithin header.raw "all" then
    fail "explicit import modifiers are unsupported"
  let imports := Elab.HeaderSyntax.imports header
  for imp in imports do
    if imp.importAll || imp.isMeta || !imp.isExported then
      fail "import modifiers are unsupported"
  let mut state := initial
  let mut messages := log
  repeat
    let previous := state.pos
    let (stx, next, nextMessages) :=
      Parser.parseCommand ctx { env := parserEnv, options := {} } state messages
    state := next
    messages := nextMessages
    if messages.hasErrors || state.recovering then
      fail s!"command parser error in {moduleName}"
    if stx.isOfKind ``Parser.Command.eoi then break
    if state.pos <= previous then
      throw <| IO.userError "parser made no progress"
    inspectCommand stx
  return Json.mkObj [
    ("module", toJson moduleName),
    ("imports", toJson imports),
    ("trustTier", toJson tier?)]

/-! ## Phase 2: kernel environment audit -/

/-- Collect all constant names referenced anywhere inside `e`. -/
partial def expressionEdges (e : Expr) : IO NameSet := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    fail "open expression in stored declaration"
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
      | .app a b | .forallE _ a b _ | .lam _ a b _ =>
        pending := a :: b :: pending
      | .letE _ t v b _ => pending := t :: v :: b :: pending
      | .proj s _ b =>
        result := result.insert s
        pending := b :: pending
      | .mdata _ b => pending := b :: pending
      | _ => pure ()
  return result

/-- The kernel dependency edges of `ci`: every constant in its type and value,
the other members of its mutual block, and its inductive structure
(constructors of an inductive, the inductive of a constructor, and the
constructors and rule right-hand sides of a recursor). -/
def declarationEdges (ci : ConstantInfo) : IO NameSet := do
  let mut result ← expressionEdges ci.type
  if let some value := ci.value? (allowOpaque := true) then
    result := result ++ (← expressionEdges value)
  result := result ++ .ofList ci.all
  match ci with
  | .inductInfo v => result := result ++ .ofList v.ctors
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
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

/-- Return the defining module name for kernel constant `n` in `env`. -/
def origin (env : Environment) (n : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? n
    | fail s!"unknown declaration origin: {n}"
  let some mod := env.header.modules[idx]?
    | fail s!"invalid module index: {n}"
  return mod.module

/-- Compute the transitive kernel dependency closure of `roots`, verify that
every reachable axiom belongs to `axioms`, and return the sorted reached
axioms and the set of reached constants. -/
def closure (lookup : Name → IO ConstantInfo) (provenance : Name → IO Name)
    (axioms : Array (String × String)) (roots : Array Name) :
    IO (Array Name × NameSet) := do
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
        unless axioms.contains (n.toString, m.toString) do
          fail s!"unapproved axiom {n} from {m}"
        reachedAxioms := reachedAxioms.insert n
      pending := (← declarationEdges ci).toList ++ pending
  return (reachedAxioms.toArray.qsort Name.lt, visited)

/-- Verify module allowlists, declaration provenance, `Trusted` namespace
hygiene, and the absence of axioms and `unsafe`/`partial` declarations across
all loaded modules. Return every non-foundation constant with its origin module,
and the compiler-only (IR) names of `Trusted` modules. -/
def verifyAndCollectLocals (env : Environment) (foundation : Array Name)
    (trusted : Array Name) (allowedAll : Array Name) :
    IO (Std.HashMap Name ConstantInfo × Std.HashMap Name Name × NameSet) := do
  let loadedMods : NameSet :=
    .ofList (env.header.modules.toList.map (·.module))
  for reqMod in allowedAll do
    unless loadedMods.contains reqMod do
      fail s!"missing required module {reqMod}"
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut origins : Std.HashMap Name Name := {}
  let mut extraNames : NameSet := {}
  for m in env.header.modules, data in env.header.moduleData do
    unless data.constNames == data.constants.map ConstantInfo.name do
      fail s!"invalid inventory {m.module}"
    unless allowedAll.contains m.module do fail s!"foreign module {m.module}"
    for ci in data.constants do
      let orig ← origin env ci.name
      if foundation.contains m.module then
        unless foundation.contains orig do
          fail s!"inventory origin mismatch {ci.name}"
      else
        if locals.contains ci.name then
          fail s!"duplicate declaration {ci.name}"
        unless orig == m.module do
          fail s!"inventory origin mismatch {ci.name}"
      let some stored := env.checked.get.find? ci.name
        | fail s!"missing stored declaration {ci.name}"
      unless stored.type == ci.type && stored.value? true == ci.value? true do
        fail s!"stored declaration differs from inventory {ci.name}"
      if !foundation.contains m.module then
        let isTrusted := trusted.contains m.module
        if !isTrusted && (privateToUserName ci.name).getRoot == `Trusted then
          fail s!"non-Trusted module {m.module} cannot declare constant {ci.name} in Trusted namespace"
        if !isTrusted && (ci matches .opaqueInfo _) then
          fail s!"opaque declaration {ci.name} in {m.module} is not allowed outside Trusted"
        if ci.isUnsafe || ci.isPartial then
          fail (if isTrusted then
            s!"unsafe/partial Trusted declaration {ci.name}"
          else
            s!"unsafe/partial declaration {ci.name} in {m.module}")
        if ci.isAxiom then
          fail (if isTrusted then
            s!"Trusted axiom {ci.name}"
          else
            s!"strict axiom declaration {ci.name} in {m.module}")
        if ci matches .quotInfo _ then
          fail s!"unexpected quotient primitive {ci.name} in {m.module}"
        if ci.hasValue true && (ci.value? true).isNone then
          fail s!"missing stored body {ci.name}"
        locals := locals.insert ci.name ci
        origins := origins.insert ci.name orig
    for n in data.extraConstNames do
      if !foundation.contains m.module then
        unless (← origin env n) == m.module do
          fail s!"IR helper provenance mismatch {n}"
        if (env.checked.get.find? n).isSome then
          unless locals.contains n do
            fail s!"uninventoried kernel compiler helper {n}"
        else if trusted.contains m.module then
          extraNames := extraNames.insert n
      else
        unless foundation.contains (← origin env n) do
          fail s!"IR helper provenance mismatch {n}"
  for (n, _) in env.checked.get.constants do
    if !foundation.contains (← origin env n) && !locals.contains n then
      fail s!"uninventoried constant {n}"
  return (locals, origins, extraNames)

/-- Parse `"moduleTiers"` produced by `"preflight"` and verify that every
module in `trusted` has a valid trust tier (`"vetted"` or
`"candidate:<feature>"`). -/
def parseModuleTiers (j : Json) (trusted : Array Name) :
    IO (Std.HashMap Name String) := do
  let entries ← field (α := Array (String × String)) j "moduleTiers"
  let mut tierMap : Std.HashMap Name String := {}
  for (mStr, status) in entries do
    let m := mStr.toName
    if tierMap.contains m then fail s!"duplicate module tier for {m}"
    unless trusted.contains m do
      fail s!"trust tier declared for non-Trusted module {m}"
    unless status == "vetted" || (status.startsWith "candidate:" &&
        validCandidateFeatures.contains (status.drop 10).toString.toName) do
      fail s!"invalid trust tier {status} for {m}"
    tierMap := tierMap.insert m status
  for m in trusted do
    unless tierMap.contains m do
      fail s!"missing trust tier for Trusted module {m}"
  return tierMap

/-- Enforce the origin rule and the vetted rule on every `Trusted` constant.
Edges to constants outside `locals` are foundation constants:
`verifyAndCollectLocals` has inventoried every non-foundation constant into
`locals`. -/
def checkTierReferences (locals : Std.HashMap Name ConstantInfo)
    (origins : Std.HashMap Name Name)
    (moduleTiers : Std.HashMap Name String) : IO Unit := do
  for (cName, ci) in locals do
    let orig := origins.getD cName .anonymous
    if let some tier := moduleTiers.get? orig then
      for dep in ← declarationEdges ci do
        if let some depOrigin := origins.get? dep then
          let some depTier := moduleTiers.get? depOrigin
            | fail s!"Trusted constant {cName} references {dep} from non-Trusted module {depOrigin}"
          if tier == "vetted" && depTier != "vetted" then
            fail s!"vetted constant {cName} references {depTier} constant {dep}"

/-- Execute Phase 2 (`"audit"`) on the compiled `.olean` environment `env`. -/
def audit (j : Json) (env : Environment) (foundation : Array Name)
    (trusted : Array Name) (theory : Array Name) : IO Json := do
  validateGraph j env
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let moduleTiers ← parseModuleTiers j trusted
  let allowedAll := foundation ++ trusted ++ theory
  let (locals, origins, extraNames) ←
    verifyAndCollectLocals env foundation trusted allowedAll
  let lookup n :=
    match env.checked.get.find? n with
    | some ci => pure ci
    | none => fail s!"missing dependency declaration {n}"
  checkTierReferences locals origins moduleTiers
  let mut inventory := #[]
  for (cName, ci) in locals do
    let orig := origins.getD cName .anonymous
    if let some tier := moduleTiers.get? orig then
      inventory := inventory.push <| Json.mkObj [
        ("name", toJson cName), ("module", toJson orig),
        ("kind", toJson (kind ci)), ("trustStatus", toJson tier),
        ("dependencies", toJson ((← declarationEdges ci).toArray.qsort Name.lt))]
  let allLocalRoots := locals.fold (init := #[]) fun acc n _ => acc.push n
  let (allAxioms, allVisited) ←
    closure lookup (origin env) axiomPolicy allLocalRoots
  -- Replay every non-foundation constant through the kernel.
  let base ← importEnv j foundation
  discard <| base.toKernelEnv.replay locals
  return Json.mkObj [
    ("graph", graph env), ("declarations", .arr inventory),
    ("kernelDeclarations", toJson inventory.size),
    ("replayedDeclarations", toJson locals.size),
    ("compilerOnlyNames", toJson extraNames.size),
    ("reachableDeclarations", toJson allVisited.size),
    ("axioms", toJson allAxioms), ("replay", toJson true)]

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
    let env ← importEnv j (foundation ++ trusted ++ theory)
    return ← audit j env foundation trusted theory
  throw <| IO.userError s!"unknown inspector mode {mode}"

end TrustedBoundary

/-- CLI entry point invoked via `lean --run TrustedBoundary.lean <req.json>
<res.json>`. -/
def main (args : List String) : IO UInt32 := do
  let [request, output] := args
    | IO.eprintln "expected request and result files"; return 2
  try
    let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile request)
    let result ← TrustedBoundary.run j
    IO.FS.writeFile output <|
      (Json.mkObj [("ok", toJson true), ("result", result)]).pretty
    return 0
  catch error =>
    let message := error.toString
    let category :=
      if message.startsWith "policy:" then "policy" else "operational"
    IO.FS.writeFile output <|
      (Json.mkObj [
        ("ok", toJson false), ("category", toJson category),
        ("message", toJson message)]).pretty
    IO.eprintln message
    return if category == "policy" then 1 else 2
