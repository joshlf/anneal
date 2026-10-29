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

def inspectAttribute (s : Syntax) : IO Unit := do
  let k := s.getKind
  if k == ``Parser.Attr.simple then
    unless allowedAttributeNames.contains s[0].getId do fail s!"unsupported attribute {s[0].getId}"
  else if k != ``Parser.Attr.instance && k != `Lean.Parser.Attr.simp then
    fail s!"unsupported attribute form {k}"

-- Admission of syntax is a versioned cooperative policy, not a Lean sandbox.
-- A term `unsafe t` can generate a *safe* opaque kernel choice body with a
-- different native implemented_by function. isUnsafe alone does not catch it.
partial def inspectSyntax (s : Syntax) : IO Unit := do
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
    inspectAttribute s[1]
  if k == ``Parser.Command.eraseAttr then
    unless allowedAttributeNames.contains s[1].getId do fail s!"unsupported attribute removal {s[1].getId}"
  if k == `Lean.Parser.Tactic.decide then
    if identWithin s `native || atomWithin s "native" then
      fail "native decide configuration is unsupported"
  for child in s.getArgs do inspectSyntax child

partial def inspectCommand (s : Syntax) : IO Unit := do
  unless commandKinds.contains s.getKind do fail s!"unsupported command {s.getKind}"
  inspectSyntax s
  if s.isOfKind ``Parser.Command.in then
    unless s.getArgs.size == 3 do fail "unsupported command-wrapper shape"
    inspectCommand s[0]
    inspectCommand s[2]
  if s.isOfKind ``Parser.Command.mutual then
    unless s.getArgs.size == 3 do fail "unsupported mutual-block shape"
    for child in s[1].getArgs do inspectCommand child

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
  let mut state := initial
  let mut messages := log
  repeat
    let previous := state.pos
    let (stx, next, nextMessages) := Parser.parseCommand ctx {env := parserEnv, options := {}} state messages
    state := next
    messages := nextMessages
    if messages.hasErrors || state.recovering then fail s!"command parser error in {moduleName}"
    if stx.isOfKind ``Parser.Command.eoi then break
    if state.pos <= previous then throw <| IO.userError "parser made no progress"
    inspectCommand stx
  return Json.mkObj [("module", toJson moduleName), ("imports", toJson imports)]

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

def audit (j : Json) (env : Environment) : IO Json := do
  validateGraph j env
  let trusted ← names j "trusted"
  let foundation ← names j "foundation"
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut allNames : NameSet := {}
  let mut extraNames : NameSet := {}
  let mut inventory := #[]
  for m in env.header.modules, data in env.header.moduleData do
    unless data.constNames == data.constants.map ConstantInfo.name do fail s!"invalid inventory {m.module}"
    unless (trusted ++ foundation).contains m.module do fail s!"foreign module {m.module}"
    for ci in data.constants do
      let orig ← origin env ci.name
      if trusted.contains m.module then
        if allNames.contains ci.name then fail s!"duplicate declaration {ci.name}"
        unless orig == m.module do fail s!"inventory origin mismatch {ci.name}"
      else
        unless foundation.contains orig do fail s!"inventory origin mismatch {ci.name}"
      allNames := allNames.insert ci.name
      let some stored := env.checked.get.find? ci.name | fail s!"missing stored declaration {ci.name}"
      unless stored.type == ci.type && stored.value? true == ci.value? true do
        fail s!"stored declaration differs from inventory {ci.name}"
      if trusted.contains m.module then
        if ci.isUnsafe || ci.isPartial then fail s!"unsafe/partial Trusted declaration {ci.name}"
        if ci.isAxiom then fail s!"Trusted axiom {ci.name}"
        if ci.hasValue true && (ci.value? true).isNone then fail s!"missing stored body {ci.name}"
        locals := locals.insert ci.name ci
        inventory := inventory.push <| Json.mkObj [
          ("name", toJson ci.name), ("module", toJson m.module), ("kind", toJson (kind ci)),
          ("dependencies", toJson ((← declarationEdges ci).toArray.qsort Name.lt))]
    for n in data.extraConstNames do
      if trusted.contains m.module then
        unless (← origin env n) == m.module do fail s!"IR helper provenance mismatch {n}"
        if (env.checked.get.find? n).isSome then
          unless locals.contains n do fail s!"uninventoried kernel compiler helper {n}"
        else
          extraNames := extraNames.insert n
      else
        unless foundation.contains (← origin env n) do fail s!"IR helper provenance mismatch {n}"
  for (n, _) in env.checked.get.constants do
    if trusted.contains (← origin env n) && !locals.contains n then fail s!"uninventoried Trusted constant {n}"
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

/-- Audit downstream `theory/`, `examples/`, and `tests/` modules:
    1. Enforce Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation on
       all theorem declarations in `claimModules` (rejecting any reference in
       `ci.type` to `theory`).
    2. Enforce the strict zero-custom-axiom policy on `theory`, `examples`, and
       `claimModules`, and the `file-local-axioms` policy on `testModules`.
    3. Replay all safe, axiom-free declarations in `base.toKernelEnv.replay`. -/
def downstreamAudit (j : Json) (env : Environment) : IO Json := do
  let foundation ← names j "foundation"
  let trusted ← names j "trusted"
  let theory ← names j "theory"
  let examples ← names j "examples"
  let claimModules ← names j "claimModules"
  let testModules ← names j "testModules"
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let strictDownstream := theory ++ examples ++ claimModules
  let allDownstream := strictDownstream ++ testModules
  let allowedAll := foundation ++ trusted ++ allDownstream
  let lookup n := match env.checked.get.find? n with
    | some ci => pure ci | none => fail s!"missing dependency declaration {n}"
  let mut replayLocals : Std.HashMap Name ConstantInfo := {}
  let mut claimTheoremsChecked := 0
  let mut localTestAxioms : NameSet := {}
  let mut seenModules : NameSet := {}
  for m in env.header.modules, data in env.header.moduleData do
    unless allowedAll.contains m.module do fail s!"foreign module {m.module}"
    if allDownstream.contains m.module then
      seenModules := seenModules.insert m.module
    for ci in data.constants do
      if foundation.contains m.module then
        unless foundation.contains (← origin env ci.name) do fail s!"inventory origin mismatch {ci.name}"
      else
        unless (← origin env ci.name) == m.module do fail s!"inventory origin mismatch {ci.name}"
      if trusted.contains m.module || strictDownstream.contains m.module then
        if ci.isUnsafe || ci.isPartial then fail s!"unsafe/partial declaration {ci.name} in {m.module}"
        if ci.isAxiom then fail s!"strict axiom declaration {ci.name} in {m.module}"
        replayLocals := replayLocals.insert ci.name ci
      else if testModules.contains m.module then
        if ci.isUnsafe || ci.isPartial then fail s!"unsafe/partial test declaration {ci.name} in {m.module}"
        if ci.isAxiom then localTestAxioms := localTestAxioms.insert ci.name
      if claimModules.contains m.module && kind ci == "theorem" then
        checkStatementOrigins lookup (origin env) theory claimModules ci.name ci.type
        claimTheoremsChecked := claimTheoremsChecked + 1
        let _ ← closure lookup (origin env) (foundation ++ trusted ++ theory ++ claimModules) axiomPolicy #[ci.name]
      else if (theory ++ examples).contains m.module then
        let _ ← closure lookup (origin env) (foundation ++ trusted ++ theory ++ examples) axiomPolicy #[ci.name]
      else if testModules.contains m.module then
        -- File-local test axioms: only foundational axioms or axioms declared in `m.module` itself.
        let mut pending := [ci.name]
        let mut visited : NameSet := {}
        while !pending.isEmpty do
          let n := pending.head!
          pending := pending.tail!
          if !visited.contains n then
            visited := visited.insert n
            let modName ← origin env n
            unless allowedAll.contains modName do fail s!"foreign dependency {n} from {modName}"
            let depCi ← lookup n
            if depCi.isAxiom then
              if n == `sorryAx then fail s!"{ci.name} in {m.module} depends on sorryAx"
              let isFoundational := axiomPolicy.contains (n.toString, modName.toString)
              let isSameFile := modName == m.module
              unless isFoundational || isSameFile do
                fail s!"{ci.name} in {m.module} depends on foreign axiom {n} from {modName}"
            pending := (← declarationEdges depCi).toList ++ pending
  for reqMod in allDownstream do
    unless seenModules.contains reqMod do fail s!"missing required downstream module {reqMod}"
  let base ← importEnv j foundation
  let _ ← base.toKernelEnv.replay replayLocals
  return Json.mkObj [
    ("downstreamModules", toJson (allDownstream.map Name.toString)),
    ("replayedDeclarations", toJson replayLocals.size),
    ("claimTheoremsChecked", toJson claimTheoremsChecked),
    ("localTestAxioms", toJson localTestAxioms.size),
    ("replay", toJson true)]

/-- Audit a captured crate's `Mir` and `Proof` modules for `cargo anneal verify`:
    1. Verify that `Mir` contains only data declarations (no `axiom` or `theorem`
       declarations) and depends only on `foundation ++ trusted ++ #[`Mir]`.
    2. Verify that `Mir.crate` is a `.defnInfo` constant with exact kernel type
       `Trusted.Crate`.
    3. Verify that `Proof.verify_crate` is a `.thmInfo` constant whose kernel
       type `ci.type` is literally the AST application
       `Expr.app (Expr.const ``Trusted.CrateTheorem []) (Expr.const ``Mir.crate [])`.
    4. Enforce Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation on
       `Proof.verify_crate` (unfolding `Mir`), confirm zero custom axioms in its
       transitive closure, and replay all declarations in `base.toKernelEnv.replay`. -/
def verifyCrateAudit (j : Json) (env : Environment) : IO Json := do
  let foundation ← names j "foundation"
  let trusted ← names j "trusted"
  let theory ← names j "theory"
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let crateModules : Array Name := #[`Mir, `Proof]
  let allowedForMir := foundation ++ trusted ++ #[`Mir]
  let allowedAll := foundation ++ trusted ++ theory ++ crateModules
  let lookup n := match env.checked.get.find? n with
    | some ci => pure ci | none => fail s!"missing dependency declaration {n}"
  let mut replayLocals : Std.HashMap Name ConstantInfo := {}
  let mut seenModules : NameSet := {}
  for m in env.header.modules, data in env.header.moduleData do
    unless allowedAll.contains m.module do fail s!"foreign module {m.module}"
    if crateModules.contains m.module then
      seenModules := seenModules.insert m.module
    for ci in data.constants do
      if foundation.contains m.module then
        unless foundation.contains (← origin env ci.name) do fail s!"inventory origin mismatch {ci.name}"
      else
        unless (← origin env ci.name) == m.module do fail s!"inventory origin mismatch {ci.name}"
      if trusted.contains m.module || theory.contains m.module || crateModules.contains m.module then
        if ci.isUnsafe || ci.isPartial then fail s!"unsafe/partial declaration {ci.name} in {m.module}"
        if ci.isAxiom then fail s!"axiom declaration {ci.name} in {m.module}"
        replayLocals := replayLocals.insert ci.name ci
      if m.module == `Mir then
        if kind ci == "theorem" then fail s!"Mir module must contain only data declarations, found theorem {ci.name}"
        checkStatementOrigins lookup (origin env) (theory ++ #[`Proof]) #[`Mir] ci.name ci.type
        let _ ← closure lookup (origin env) allowedForMir axiomPolicy #[ci.name]
      else if m.module == `Proof then
        let _ ← closure lookup (origin env) allowedAll axiomPolicy #[ci.name]
  for reqMod in crateModules do
    unless seenModules.contains reqMod do fail s!"missing required crate verification module {reqMod}"
  let some mirCrateCi := env.checked.get.find? `Mir.crate
    | fail "missing required declaration Mir.crate in Mir"
  unless (← origin env `Mir.crate) == `Mir do fail "Mir.crate must originate in module Mir"
  unless kind mirCrateCi == "definition" do fail s!"Mir.crate must be a definition, found {kind mirCrateCi}"
  let expectedCrateType := Expr.const `Trusted.Crate []
  unless mirCrateCi.type == expectedCrateType do
    fail s!"Mir.crate has type {mirCrateCi.type}, expected Trusted.Crate"
  let some proofCi := env.checked.get.find? `Proof.verify_crate
    | fail "missing required theorem Proof.verify_crate in Proof"
  unless (← origin env `Proof.verify_crate) == `Proof do fail "Proof.verify_crate must originate in module Proof"
  unless kind proofCi == "theorem" do fail s!"Proof.verify_crate must be a theorem, found {kind proofCi}"
  let expectedTheoremType := Expr.app (Expr.const `Trusted.CrateTheorem []) (Expr.const `Mir.crate [])
  unless proofCi.type == expectedTheoremType do
    fail s!"Proof.verify_crate has type {proofCi.type}, expected Trusted.CrateTheorem Mir.crate"
  checkStatementOrigins lookup (origin env) (theory ++ #[`Proof]) #[`Mir] proofCi.name proofCi.type
  let (reachedAxioms, visited) ← closure lookup (origin env) allowedAll axiomPolicy #[`Proof.verify_crate]
  let base ← importEnv j foundation
  let _ ← base.toKernelEnv.replay replayLocals
  return Json.mkObj [
    ("verifiedTheorem", toJson "Proof.verify_crate"),
    ("expectedType", toJson "Trusted.CrateTheorem Mir.crate"),
    ("replayedDeclarations", toJson replayLocals.size),
    ("reachableDeclarations", toJson visited),
    ("axioms", toJson reachedAxioms),
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
  -- Verify that Statement-vs.-Proof origin check catches a `theory/` reference
  -- hidden inside an unfolded claim definition in `ci.type`.
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
  if mode == "setup" then
    let moduleName := (← field (α := String) j "module").toName
    let imports ← field (α := Array Import) j "imports"
    let setup : ModuleSetup := {
      name := moduleName, imports? := some imports, importArts := (← artifacts j)}
    return toJson setup
  let foundation ← names j "foundation"
  if mode == "foundation" then
    let env ← importEnv j foundation
    return Json.mkObj [("graph", graph env)]
  if mode == "preflight" then
    let env ← importEnv j foundation true
    validateGraph j env
    let sources ← field (α := Array (String × String)) j "sources"
    let headers ← sources.mapM fun (n, p) => inspectSource env n.toName p
    return Json.mkObj [("headers", .arr headers), ("graph", graph env)]
  if mode == "audit" then
    let trusted ← names j "trusted"
    let env ← importEnv j (foundation ++ trusted)
    return ← audit j env
  if mode == "downstream-audit" then
    let trusted ← names j "trusted"
    let theory ← names j "theory"
    let examples ← names j "examples"
    let claimModules ← names j "claimModules"
    let testModules ← names j "testModules"
    let env ← importEnv j (foundation ++ trusted ++ theory ++ examples ++ claimModules ++ testModules)
    return ← downstreamAudit j env
  if mode == "verify-crate" then
    let trusted ← names j "trusted"
    let theory ← names j "theory"
    let env ← importEnv j (foundation ++ trusted ++ theory ++ #[`Mir, `Proof])
    return ← verifyCrateAudit j env
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
