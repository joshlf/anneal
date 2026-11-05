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

- **`"preflight"` (purely syntactic admission before elaboration):**
  Lean elaboration is Turing-complete and effectful: commands such as `#eval`
  and tactics/terms such as `run_tac`, `by_elab`, `native_decide`, and
  `include_str` can execute arbitrary code or read host files during
  compilation, while attributes such as `@[implemented_by]` and `@[extern]`
  alter code generation without appearing in kernel proof terms. `"preflight"`
  therefore parses every non-foundation `.lean` file using `Parser.parseHeader`
  and `Parser.parseCommand`—which never invoke the elaborator—against the locked
  foundation parser environment only. It enforces a closed command, attribute,
  and identifier grammar and extracts each `Trusted` module's
  `-- anneal-trust-tier: <tier>` directive before `lean` compiles any file.
- **`"audit"` (kernel `.olean` inspection and replay):**
  Loads the compiled `.olean` files with `trustLevel := 0`, `plugins := #[]`,
  and `loadExts := false` (so no `[init]` initializers or persistent environment
  extensions from audited modules are deserialized or executed). It verifies
  module-level trust-tier separation, `Trusted` namespace hygiene, the
  foundation axiom allowlist, and a full kernel replay of every non-foundation
  constant against the foundation environment (`base.toKernelEnv.replay`).

## Module roles and trust tiers

Every admitted module in the environment is classified into a single
`ModuleRole`:

| `ModuleRole` | Directory / Source | Meaning |
| :--- | :--- | :--- |
| `.foundation` | Toolchain `Init.*` (`foundation-lock.json`) | Pinned Lean 4 standard prelude and core types |
| `.trusted .vetted` | `trusted/lean/` (`-- anneal-trust-tier: vetted`) | Human-audited TCB definitions |
| `.trusted (.candidate f)` | `trusted/lean/` (`-- anneal-trust-tier: candidate:<f>`) | Alpha TCB definitions gated behind opt-in feature `f` |
| `.theory` | `theory/` (`Anneal.*`) | Untrusted proof automation checked by the kernel |

Every kernel constant `c` has a unique defining module (`origin env c`, read
directly from `env.getModuleIdxFor? c` in the `.olean`), and therefore a unique
`ModuleRole`. This includes compiler-generated constants such as constructors,
recursors (`rec`, `casesOn`, `recOn`, `noConfusion`, `below`, `brecOn`),
structure projections, pattern matchers (`match_1`), equation lemmas (`eq_1`),
and `where`/`private` helpers, all of which are compiled into the same `.olean`
and inherit their defining module's `ModuleRole` without surface-syntax name
prediction or suffix heuristics.

On every kernel dependency edge `c → dep` (`declarationEdges`), `checkTierReferences`
enforces two rules:

- **Origin rule:** a `.trusted _` constant may only reference `.foundation` or
  `.trusted _` constants (never `.theory`).
- **Vetted rule:** a `.trusted .vetted` constant may only reference
  `.foundation` or `.trusted .vetted` constants (never
  `.trusted (.candidate _)`).
-/

open Lean

namespace TrustedBoundary

/-! ## Domain types: `TrustTier` and `ModuleRole` -/

/-- Closed set of subsystem feature identifiers allowed in
`-- anneal-trust-tier: candidate:<feature>`. -/
def validCandidateFeatures : List Name :=
  [`refinement, `step_result, `memory, `mir_ast, `mir_semantics, `rustc_capture]

/-- Module-level trust tier declared by a `Trusted` module via its
`-- anneal-trust-tier:` directive. -/
inductive TrustTier where
  | vetted
  | candidate (feature : Name)
  deriving BEq, DecidableEq

namespace TrustTier

/-- Render a `TrustTier` in its canonical wire format (`"vetted"` or
`"candidate:<feature>"`). -/
def render : TrustTier → String
  | .vetted => "vetted"
  | .candidate feat => s!"candidate:{feat}"

/-- Parse `"vetted"` or `"candidate:<feature>"` when `<feature>` belongs to
`validCandidateFeatures`. -/
def parse? (raw : String) : Option TrustTier :=
  if raw == "vetted" then
    some .vetted
  else if let some rest := raw.dropPrefix? "candidate:" then
    let feat := rest.toString.toName
    if validCandidateFeatures.contains feat then
      some (.candidate feat)
    else
      none
  else
    none

end TrustTier

/-- Partition of every admitted module in the kernel environment into its
repository role. Representing these three roles as mutually exclusive
constructors of one sum type makes overlapping or missing module classifications
unrepresentable. -/
inductive ModuleRole where
  | foundation
  | trusted (tier : TrustTier)
  | theory
  deriving BEq, DecidableEq

/-! ## JSON IPC and environment-loading helpers -/

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
  entries.foldlM (init := {}) fun acc (n, parts) => do
    let modName := n.toName
    if (acc.find? modName).isSome then
      fail s!"duplicate artifact module {n}"
    return acc.insert modName
      (.ofArrays (parts.map (·.map System.FilePath.mk)))

/-- Serialize the compiled module header import DAG of `env` as JSON. -/
def graph (env : Environment) : Json :=
  Json.mkObj <|
    (env.header.modules.zip env.header.moduleData).toList.map fun (m, d) =>
      (m.module.toString, toJson d.imports)

/-- Import `roots` from the explicit artifact map in `j` at `trustLevel := 0`
with `level := .private`.
- In `"preflight"`, `extensions := true` loads the locked `Init.*` parser
  extensions so `Parser.parseCommand` can parse standard Lean syntax.
- In `"audit"`, `extensions := false` disables loading persistent environment
  extensions or `[init]` initializers from compiled `.olean` files. -/
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

/-- Verify that the import DAG recorded in the `.olean` headers of `env` is
identical to the admitted `"graph"` from `"preflight"`. -/
def validateGraph (j : Json) (env : Environment) : IO Unit := do
  let expected ← field (α := Json) j "graph"
  unless graph env == expected do
    fail "compiled module/import DAG differs from admitted DAG"

/-! ## Phase 1: source preflight -/

/-- Closed allowlist of top-level command syntax kinds permitted in source
files. Commands such as `#eval`, `#check`, `macro`, `syntax`, `elab`,
`initialize`, and `axiom` are excluded. -/
def allowedCommandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.universe,
  ``Parser.Command.variable, ``Parser.Command.open, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in, ``Parser.Command.attribute,
  ``Parser.Command.moduleDoc]

/-- Closed allowlist of declaration syntax kinds permitted inside
`Parser.Command.declaration`. -/
def allowedDeclarationKinds : List Name := [
  ``Parser.Command.abbrev, ``Parser.Command.definition,
  ``Parser.Command.theorem, ``Parser.Command.opaque,
  ``Parser.Command.instance, ``Parser.Command.inductive,
  ``Parser.Command.classInductive, ``Parser.Command.structure]

/-- Closed allowlist of attributes permitted on declarations. Compiler-override
and metaprogramming attributes (`extern`, `implemented_by`, `csimp`, `init`,
`macro`, `elab_as_elim`, etc.) are excluded. -/
def allowedAttributeNames : List Name :=
  [`simp, `instance, `reducible, `semireducible, `irreducible]

/-- Keyword atoms rejected anywhere inside a command syntax tree. -/
def forbiddenAtomKeywords : List String := [
  "set_option", "rfl'", "unhygienic", "decide!", "bv_decide",
  "native_decide", "include_str", "by_elab", "run_tac",
  "with_decl_name%", "private_decl%", "decl_name%",
  "partial_fixpoint", "coinductive_fixpoint", "inductive_fixpoint"]

/-- Syntax node kinds rejected anywhere inside a command syntax tree. -/
def forbiddenSyntaxKinds : List Name := [
  ``Parser.Command.unsafe, ``Parser.Command.partial, ``Parser.Command.meta,
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
  `Lean.Parser.Termination.inductiveFixpoint]

/-- Return `true` if `s` or any syntax descendant is an atom equal to `val`. -/
def atomWithin (s : Syntax) (val : String) : Bool :=
  (s.find? fun x => x.isAtom && x.getAtomVal == val).isSome

/-- Return `true` if `id` is a valid user-written identifier with non-empty
string components, no macro scopes, and no `_root_` namespace escape. -/
def isValidSourceIdent (id : Name) : Bool :=
  id.isAnonymous ||
    (!id.hasMacroScopes && id.eraseMacroScopes == id &&
     !id.toString.isEmpty &&
     id.components.all fun
       | .str .anonymous seg => !seg.isEmpty && seg != "_root_"
       | _ => false)

/-- Extract the module-level `-- anneal-trust-tier: <tier>` directive from
`text`. Every `Trusted` module must declare a single valid `TrustTier`, and
non-`Trusted` modules may not declare one. -/
def extractModuleTier (isTrustedModule : Bool) (moduleName : Name)
    (text : String) : IO (Option TrustTier) := do
  let directives := (text.splitOn "\n").filterMap fun rawLine =>
    (rawLine.trimAscii.toString.dropPrefix? "-- anneal-trust-tier:").map
      (·.trimAscii.toString)
  match isTrustedModule, directives with
  | false, [] => pure none
  | false, _ :: _ =>
    fail s!"trust tier directive is only allowed in Trusted modules ({moduleName})"
  | true, [] =>
    fail s!"missing `-- anneal-trust-tier: vetted` or `-- anneal-trust-tier: candidate:<feature>` in {moduleName}"
  | true, [rawTier] =>
    match TrustTier.parse? rawTier with
    | some tier => pure (some tier)
    | none => fail s!"invalid trust tier {rawTier} in {moduleName}"
  | true, _ :: _ :: _ =>
    fail s!"multiple trust tier directives in {moduleName}"

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
  if s.isIdent && !isValidSourceIdent s.getId then
    fail s!"invalid identifier {s.getId}"
  if s.isAtom && forbiddenAtomKeywords.contains s.getAtomVal then
    fail s!"unsupported syntax keyword {s.getAtomVal}"
  let k := s.getKind
  if forbiddenSyntaxKinds.contains k then
    fail s!"unsupported source form {k}"
  if k == ``Parser.Term.attrKind then
    if atomWithin s "scoped" || atomWithin s "local" then
      fail "scoped/local attribute modifiers are unsupported"
  else if k == ``Parser.Command.optDeriving ||
      k == ``Parser.Command.optDefDeriving then
    if atomWithin s "deriving" then fail "deriving clauses are unsupported"
  else if k == ``Parser.Term.attrInstance then
    inspectAttrInstance s
  else if k == ``Parser.Command.eraseAttr then
    unless allowedAttributeNames.contains s[1].getId do
      fail s!"unsupported attribute removal {s[1].getId}"
  else if k == `Lean.Parser.Tactic.decide then
    unless s[1].getArgs.all (·.getArgs.isEmpty) do
      fail "decide configuration is unsupported"
  for child in s.getArgs do inspectSyntax child

/-- Validate a top-level command `s` during `"preflight"`. -/
partial def inspectCommand (s : Syntax) : IO Unit := do
  let k := s.getKind
  unless allowedCommandKinds.contains k do
    fail s!"unsupported command {k}"
  inspectSyntax s
  if k == ``Parser.Command.open then
    if atomWithin s "scoped" then
      fail "open scoped is unsupported"
  else if k == ``Parser.Command.namespace || k == ``Parser.Command.section then
    if !s[0].getArgs.all (·.getArgs.isEmpty) || atomWithin s "noncomputable" ||
        atomWithin s "meta" || atomWithin s "public" ||
        atomWithin s "expose" then
      fail "section/namespace modifiers are unsupported"
  else if k == ``Parser.Command.in then
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
  else if k == ``Parser.Command.mutual then
    unless s.getArgs.size == 3 do fail "unsupported mutual-block shape"
    for child in s[1].getArgs do
      inspectCommand child
  else if k == ``Parser.Command.declaration then
    let decl := s[1]
    unless allowedDeclarationKinds.contains decl.getKind do
      fail s!"unsupported declaration kind {decl.getKind}"

/-- Parse and validate all commands in `ctx` starting from `initial` and `log`
using the pure foundation `parserEnv`. -/
partial def parseAndInspectCommands (ctx : Parser.InputContext)
    (parserEnv : Environment) (moduleName : Name)
    (state : Parser.ModuleParserState) (messages : MessageLog) : IO Unit := do
  let previous := state.pos
  let (stx, nextState, nextMessages) :=
    Parser.parseCommand ctx { env := parserEnv, options := {} } state messages
  if nextMessages.hasErrors || nextState.recovering then
    fail s!"command parser error in {moduleName}"
  if stx.isOfKind ``Parser.Command.eoi then
    return ()
  if nextState.pos <= previous then
    throw <| IO.userError "parser made no progress"
  inspectCommand stx
  parseAndInspectCommands ctx parserEnv moduleName nextState nextMessages

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
  parseAndInspectCommands ctx parserEnv moduleName initial log
  return Json.mkObj [
    ("module", toJson moduleName),
    ("imports", toJson imports),
    ("trustTier", toJson (tier?.map TrustTier.render))]

/-! ## Phase 2: kernel environment audit -/

/-- Pure DAG traversal collecting every constant referenced inside `pending`.
Uses `seen` to avoid re-traversing shared DAG subterms in kernel `Expr`s. -/
partial def collectExprConsts (pending : List Expr)
    (seen : Std.HashSet Expr := {}) (acc : NameSet := {}) : NameSet :=
  match pending with
  | [] => acc
  | x :: rest =>
    if seen.contains x then
      collectExprConsts rest seen acc
    else
      let seen := seen.insert x
      match x with
      | .const n _ => collectExprConsts rest seen (acc.insert n)
      | .lit (.natVal _) => collectExprConsts rest seen (acc.insert `Nat)
      | .lit (.strVal _) => collectExprConsts rest seen (acc.insert `String)
      | .app a b | .forallE _ a b _ | .lam _ a b _ =>
        collectExprConsts (a :: b :: rest) seen acc
      | .letE _ t v b _ =>
        collectExprConsts (t :: v :: b :: rest) seen acc
      | .proj s _ b =>
        collectExprConsts (b :: rest) seen (acc.insert s)
      | .mdata _ b =>
        collectExprConsts (b :: rest) seen acc
      | .bvar _ | .fvar _ | .mvar _ | .sort _ =>
        collectExprConsts rest seen acc

/-- Verify that `e` contains no free variables, metavariables, or loose bound
variables, and return the set of all constants referenced inside `e`. -/
def expressionEdges (e : Expr) : IO NameSet := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    fail "open expression in stored declaration"
  return collectExprConsts [e]

/-- The kernel dependency edges of `ci`: every constant in its type and value,
the other members of its mutual block, and its inductive structure
(constructors of an inductive, the inductive of a constructor, and the
constructors and rule right-hand sides of a recursor). -/
def declarationEdges (ci : ConstantInfo) : IO NameSet := do
  let typeEdges ← expressionEdges ci.type
  let valEdges ← match ci.value? (allowOpaque := true) with
    | some value => expressionEdges value
    | none => pure {}
  let baseEdges := typeEdges ++ valEdges ++ .ofList ci.all
  match ci with
  | .inductInfo v => return baseEdges ++ .ofList v.ctors
  | .ctorInfo v => return baseEdges.insert v.induct
  | .recInfo v =>
    v.rules.foldlM (init := baseEdges ++ .ofList v.all) fun acc rule => do
      return (acc.insert rule.ctor) ++ (← expressionEdges rule.rhs)
  | .axiomInfo _ | .defnInfo _ | .thmInfo _ | .opaqueInfo _ | .quotInfo _ =>
    return baseEdges

/-- Human-readable kind tag for a kernel `ConstantInfo`. -/
def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Return the defining module name for kernel constant `n` in `env`. -/
def origin (env : Environment) (n : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? n
    | fail s!"unknown declaration origin: {n}"
  let some mod := env.header.modules[idx]?
    | fail s!"invalid module index: {n}"
  return mod.module

/-- Return the defining module name and `ModuleRole` for constant `n` in
`env`. -/
def constProvenance (env : Environment)
    (roles : Std.HashMap Name ModuleRole) (n : Name) :
    IO (Name × ModuleRole) := do
  let orig ← origin env n
  let some role := roles.get? orig
    | fail s!"foreign module {orig} for {n}"
  return (orig, role)

/-- Compute the transitive kernel dependency closure of `pending`, verify that
every reachable axiom belongs to `axioms`, and return the sorted reached
axioms and the set of reached constants. -/
partial def closure (lookup : Name → IO ConstantInfo)
    (provenance : Name → IO Name) (axioms : Array (String × String))
    (pending : List Name) (visited : NameSet := {})
    (reachedAxioms : NameSet := {}) : IO (Array Name × NameSet) := do
  match pending with
  | [] => return (reachedAxioms.toArray.qsort Name.lt, visited)
  | n :: rest =>
    if visited.contains n then
      closure lookup provenance axioms rest visited reachedAxioms
    else
      let visited := visited.insert n
      let m ← provenance n
      let ci ← lookup n
      let reachedAxioms ← if ci.isAxiom then do
        unless axioms.contains (n.toString, m.toString) do
          fail s!"unapproved axiom {n} from {m}"
        pure (reachedAxioms.insert n)
      else
        pure reachedAxioms
      let deps ← declarationEdges ci
      closure lookup provenance axioms (deps.toList ++ rest) visited
        reachedAxioms

/-- Build the complete map from module name to `ModuleRole`, verifying that
`foundation`, `trusted`, and `theory` are pairwise disjoint and that every
`Trusted` module has a valid `TrustTier`. -/
def buildModuleRoles (j : Json) (foundation trusted theory : Array Name) :
    IO (Std.HashMap Name ModuleRole) := do
  let tierEntries ← field (α := Array (String × String)) j "moduleTiers"
  let tierMap ← tierEntries.foldlM (init := ({} : Std.HashMap Name TrustTier))
    fun acc (mStr, rawTier) => do
      let m := mStr.toName
      if acc.contains m then fail s!"duplicate module tier for {m}"
      unless trusted.contains m do
        fail s!"trust tier declared for non-Trusted module {m}"
      let some tier := TrustTier.parse? rawTier
        | fail s!"invalid trust tier {rawTier} for {m}"
      return acc.insert m tier
  let roles0 := foundation.foldl (init := ({} : Std.HashMap Name ModuleRole))
    fun acc m => acc.insert m .foundation
  let roles1 ← trusted.foldlM (init := roles0) fun acc m => do
    if acc.contains m then fail s!"overlapping module role for {m}"
    let some tier := tierMap.get? m
      | fail s!"missing trust tier for Trusted module {m}"
    return acc.insert m (.trusted tier)
  theory.foldlM (init := roles1) fun acc m => do
    if acc.contains m then fail s!"overlapping module role for {m}"
    return acc.insert m .theory

/-- Enforce per-constant policy invariants on a non-foundation constant `ci`
defined in module `m` with `role`:
- Non-`Trusted` modules cannot declare constants in the `Trusted` root
  namespace (`privateToUserName` strips any `_private.<mod>.0` prefix first so
  `private` declarations inside `namespace Trusted` are also caught).
- Non-`Trusted` modules cannot declare `opaque` constants.
- No non-foundation module may declare `unsafe`, `partial`, `axiom`, or `quot`
  constants, or omit a definition body. -/
def validateLocalConstant (m : Name) (role : ModuleRole)
    (ci : ConstantInfo) : IO Unit := do
  let isTrusted := role matches .trusted _
  if !isTrusted && (privateToUserName ci.name).getRoot == `Trusted then
    fail s!"non-Trusted module {m} cannot declare constant {ci.name} in Trusted namespace"
  if !isTrusted && (ci matches .opaqueInfo _) then
    fail s!"opaque declaration {ci.name} in {m} is not allowed outside Trusted"
  if ci.isUnsafe || ci.isPartial then
    fail (if isTrusted then
      s!"unsafe/partial Trusted declaration {ci.name}"
    else
      s!"unsafe/partial declaration {ci.name} in {m}")
  if ci.isAxiom then
    fail (if isTrusted then
      s!"Trusted axiom {ci.name}"
    else
      s!"strict axiom declaration {ci.name} in {m}")
  if ci matches .quotInfo _ then
    fail s!"unexpected quotient primitive {ci.name} in {m}"
  if ci.hasValue true && (ci.value? true).isNone then
    fail s!"missing stored body {ci.name}"

/-- Verify module allowlists, declaration provenance, `Trusted` namespace
hygiene, and the absence of axioms and `unsafe`/`partial` declarations across
all loaded modules. Return every non-foundation constant and the compiler-only
(IR) names of `Trusted` modules. -/
def verifyAndCollectLocals (env : Environment)
    (roles : Std.HashMap Name ModuleRole) :
    IO (Std.HashMap Name ConstantInfo × NameSet) := do
  let loadedMods : NameSet :=
    .ofList (env.header.modules.toList.map (·.module))
  for (reqMod, _) in roles do
    unless loadedMods.contains reqMod do
      fail s!"missing required module {reqMod}"
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut extraNames : NameSet := {}
  for m in env.header.modules, data in env.header.moduleData do
    unless data.constNames == data.constants.map ConstantInfo.name do
      fail s!"invalid inventory {m.module}"
    let some role := roles.get? m.module
      | fail s!"foreign module {m.module}"
    for ci in data.constants do
      let (orig, origRole) ← constProvenance env roles ci.name
      match role with
      | .foundation =>
        unless origRole == .foundation do
          fail s!"inventory origin mismatch {ci.name}"
      | .trusted _ | .theory =>
        if locals.contains ci.name then
          fail s!"duplicate declaration {ci.name}"
        unless orig == m.module do
          fail s!"inventory origin mismatch {ci.name}"
      let some stored := env.checked.get.find? ci.name
        | fail s!"missing stored declaration {ci.name}"
      unless stored.type == ci.type && stored.value? true == ci.value? true do
        fail s!"stored declaration differs from inventory {ci.name}"
      if role != .foundation then
        validateLocalConstant m.module role ci
        locals := locals.insert ci.name ci
    for n in data.extraConstNames do
      let (orig, origRole) ← constProvenance env roles n
      match role with
      | .foundation =>
        unless origRole == .foundation do
          fail s!"IR helper provenance mismatch {n}"
      | .trusted _ | .theory =>
        unless orig == m.module do
          fail s!"IR helper provenance mismatch {n}"
        if (env.checked.get.find? n).isSome then
          unless locals.contains n do
            fail s!"uninventoried kernel compiler helper {n}"
        else if role matches .trusted _ then
          extraNames := extraNames.insert n
  for (n, _) in env.checked.get.constants do
    let (_, origRole) ← constProvenance env roles n
    if origRole != .foundation && !locals.contains n then
      fail s!"uninventoried constant {n}"
  return (locals, extraNames)

/-- Enforce the origin rule and the vetted rule on every `Trusted` constant:
- **Origin rule:** a `.trusted _` constant may only reference `.foundation` or
  `.trusted _` constants (never `.theory`).
- **Vetted rule:** a `.trusted .vetted` constant may only reference
  `.foundation` or `.trusted .vetted` constants (never
  `.trusted (.candidate _)`). -/
def checkTierReferences (env : Environment)
    (roles : Std.HashMap Name ModuleRole)
    (locals : Std.HashMap Name ConstantInfo) : IO Unit := do
  for (cName, ci) in locals do
    let (_, cRole) ← constProvenance env roles cName
    if let .trusted tier := cRole then
      for dep in ← declarationEdges ci do
        let (depOrigin, depRole) ← constProvenance env roles dep
        match depRole with
        | .foundation => pure ()
        | .trusted depTier =>
          if tier == .vetted && depTier != .vetted then
            fail s!"vetted constant {cName} references {depTier.render} constant {dep}"
        | .theory =>
          fail s!"Trusted constant {cName} references {dep} from non-Trusted module {depOrigin}"

/-- Execute Phase 2 (`"audit"`) on the compiled `.olean` environment `env`. -/
def audit (j : Json) (env : Environment) (foundation : Array Name)
    (trusted : Array Name) (theory : Array Name) : IO Json := do
  validateGraph j env
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let roles ← buildModuleRoles j foundation trusted theory
  let (locals, extraNames) ← verifyAndCollectLocals env roles
  let lookup n :=
    match env.checked.get.find? n with
    | some ci => pure ci
    | none => fail s!"missing dependency declaration {n}"
  checkTierReferences env roles locals
  let inventory ← locals.foldM (init := #[]) fun acc cName ci => do
    let (orig, cRole) ← constProvenance env roles cName
    match cRole with
    | .trusted tier =>
      let deps := (← declarationEdges ci).toArray.qsort Name.lt
      return acc.push <| Json.mkObj [
        ("name", toJson cName), ("module", toJson orig),
        ("kind", toJson (kind ci)), ("trustStatus", toJson tier.render),
        ("dependencies", toJson deps)]
    | .foundation | .theory => return acc
  let allLocalRoots := locals.fold (init := []) fun acc n _ => n :: acc
  let (allAxioms, allVisited) ←
    closure lookup (origin env) axiomPolicy allLocalRoots
  -- Replay every non-foundation constant from scratch through the Lean kernel
  -- against the locked foundation environment (`loadExts := false`).
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
  match mode with
  | "preflight" =>
    let env ← importEnv j foundation true
    validateGraph j env
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ← sources.mapM fun (n, p) => inspectSource env n.toName p
    return Json.mkObj [("headers", .arr headers), ("graph", graph env)]
  | "audit" =>
    let trusted ← names j "trusted"
    let theory ← names j "theory"
    let env ← importEnv j (foundation ++ trusted ++ theory)
    audit j env foundation trusted theory
  | _ => throw <| IO.userError s!"unknown inspector mode {mode}"

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
