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

def isStdlibMod (m : Name) : Bool :=
  let s := m.toString
  m == `Init || s.startsWith "Init." || m == `Std || s.startsWith "Std."

def graph (env : Environment) : Json :=
  Json.mkObj <| (env.header.modules.zip env.header.moduleData).toList.map fun (m, d) =>
    (m.module.toString, toJson d.imports)

def graphFor (env : Environment) (tracked : Array Name) : Json :=
  Json.mkObj <| (env.header.modules.zip env.header.moduleData).toList.filterMap fun (m, d) =>
    if tracked.contains m.module then some (m.module.toString, toJson d.imports) else none

def importEnv (j : Json) (roots : Array Name) (extensions := false) : IO Environment := do
  let arts ← artifacts j
  -- Admitted project/locked modules resolve strictly through `arts`; standard
  -- library modules (`Init.*`, `Std.*`) resolve from the pinned `sysroot`
  -- initialized by `initSearchPath`, and any non-stdlib/unadmitted module is
  -- rejected by complete-DAG admission and `audit` / `downstreamAudit`.
  if extensions then unsafe enableInitializersExecution
  let env ← importModules (roots.map fun n => {module := n}) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := extensions)
    (level := .private) (arts := arts)
  unless env.header.modules.size == env.header.moduleData.size do
    throw <| IO.userError "module/data array alignment failure"
  return env.setExporting false

def validateGraph (j : Json) (env : Environment) (tracked : Array Name) : IO Unit := do
  let expected ← field (α := Json) j "graph"
  unless graphFor env tracked == expected do fail "compiled module/import DAG differs from admitted DAG"

def commandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace, ``Parser.Command.section,
  ``Parser.Command.end, ``Parser.Command.universe, ``Parser.Command.variable,
  ``Parser.Command.open, ``Parser.Command.openScoped, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in, ``Parser.Command.attribute,
  ``Parser.Command.moduleDoc, ``Parser.Command.set_option,
  `Lean.Parser.Command.notation, `Lean.Parser.Command.mixfix]

def isAllowedOptionName (opt : Name) : Bool :=
  let s := opt.toString
  s == "maxHeartbeats" || s == "maxRecDepth" ||
  s.startsWith "pp." || s.startsWith "linter."

partial def atomWithin (s : Syntax) (value : String) : Bool :=
  s.isAtom && s.getAtomVal == value || s.getArgs.any (atomWithin · value)

partial def identWithin (s : Syntax) (value : Name) : Bool :=
  s.isIdent && s.getId == value || s.getArgs.any (identWithin · value)

def allowedAttributeNames : List Name := [
  `simp, `instance, `reducible, `instance_reducible, `semireducible, `irreducible,
  `ext, `grind, `partial_fixpoint_monotone, `inline, `always_inline,
  `specialize, `match_pattern, `coe, `default_instance]

def allowedDerivingClasses : List Name := [
  `DecidableEq, `BEq, `Repr, `Inhabited, `Ord, `Hashable, `ToString, `Nonempty]

def inspectAttribute (s : Syntax) : IO Unit := do
  let k := s.getKind
  if k == ``Parser.Attr.simple then
    unless allowedAttributeNames.contains s[0].getId do fail s!"unsupported attribute {s[0].getId}"
  else if k != ``Parser.Attr.instance && k != `Lean.Parser.Attr.simp &&
          k != `Lean.Parser.Attr.ext && k != `Lean.Parser.Attr.grind then
    fail s!"unsupported attribute form {k}"

def isNativeDecideAxiom (n : Name) : Bool :=
  n == `Lean.ofReduceBool || n == `Lean.ofReduceNat ||
  (n.toString.splitOn "._native.").length > 1

-- Admission of syntax is a versioned cooperative policy, not a Lean sandbox.
-- A term `unsafe t` can generate a *safe* opaque kernel choice body with a
-- different native implemented_by function. isUnsafe alone does not catch it.
partial def inspectSyntax (s : Syntax) (allowAxioms : Bool := false)
    (allowProvisionalNative : Bool := false) : IO Unit := do
  let k := s.getKind
  if [``Parser.Command.unsafe, ``Parser.Command.partial, ``Parser.Command.meta,
      ``Parser.Command.example, ``Parser.Command.coinductive,
      ``Parser.Term.unsafe,
      `Lean.byElab, `Lean.Parser.Tactic.runTac].contains k then
    fail s!"unsupported source form {k}"
  if k == `Lean.Parser.Tactic.nativeDecide then
    unless allowProvisionalNative do
      fail s!"unsupported source form {k} (provisional native evaluation requires --provisional)"
  if k == ``Parser.Command.axiom then
    unless allowAxioms do
      fail s!"unsupported source form {k} (axioms are only permitted in Assumptions.* modules)"
  if k == ``Parser.Command.set_option || k == ``Parser.Term.set_option || k == ``Parser.Tactic.set_option then
    let optName := s[1].getId
    unless isAllowedOptionName optName do
      fail s!"unsupported set_option {optName}"
  if k == ``Parser.Command.derivingClass then
    let cls := s[1].getId
    unless allowedDerivingClasses.contains cls do
      fail s!"unsupported deriving class {cls}"
  if k == ``Parser.Term.attrInstance then
    unless s.getArgs.size == 2 do fail "unsupported attribute-operation shape"
    inspectAttribute s[1]
  if k == ``Parser.Command.eraseAttr then
    unless allowedAttributeNames.contains s[1].getId do fail s!"unsupported attribute removal {s[1].getId}"
  if k == `Lean.Parser.Tactic.decide then
    if (identWithin s `native || atomWithin s "native") && !allowProvisionalNative then
      fail "native decide configuration is unsupported"
  for child in s.getArgs do inspectSyntax child allowAxioms allowProvisionalNative

partial def inspectCommand (s : Syntax) (allowAxioms : Bool := false)
    (allowProvisionalNative : Bool := false) : IO Unit := do
  unless commandKinds.contains s.getKind do fail s!"unsupported command {s.getKind}"
  inspectSyntax s allowAxioms allowProvisionalNative
  if s.isOfKind ``Parser.Command.in then
    unless s.getArgs.size == 3 do fail "unsupported command-wrapper shape"
    inspectCommand s[0] allowAxioms allowProvisionalNative
    inspectCommand s[2] allowAxioms allowProvisionalNative
  if s.isOfKind ``Parser.Command.mutual then
    unless s.getArgs.size == 3 do fail "unsupported mutual-block shape"
    for child in s[1].getArgs do inspectCommand child allowAxioms allowProvisionalNative

partial def collectIdents (s : Syntax) (acc : Array Name := #[]) : Array Name :=
  let acc := if s.isIdent then acc.push s.getId else acc
  s.getArgs.foldl (fun a c => collectIdents c a) acc

def inspectSource (parserEnv : Environment) (moduleName : Name) (path : System.FilePath)
    (allowedAxiomModules : Array Name := #[]) (allowProvisionalNative : Bool := false) : IO Json := do
  let text ← IO.FS.readFile path
  let ctx := Parser.mkInputContext text path.toString
  let (header, initial, log) ← Parser.parseHeader ctx
  if log.hasErrors || initial.recovering then fail s!"header parser error in {moduleName}"
  if Elab.HeaderSyntax.isModule header then fail "module headers are unsupported"
  let hasPrelude := atomWithin header.raw "prelude"
  if atomWithin header.raw "public" || atomWithin header.raw "meta" || atomWithin header.raw "all" then
    fail "explicit import modifiers are unsupported"
  let imports := Elab.HeaderSyntax.imports header
  for imp in imports do
    let isImplicitInitMeta := !hasPrelude && imp.module == `Init && !imp.importAll && imp.isExported && imp.isMeta
    if !isImplicitInitMeta && (imp.importAll || imp.isMeta || !imp.isExported) then
      fail "import modifiers are unsupported"
  let allowAxioms :=
    moduleName.toString.startsWith "Assumptions." || allowedAxiomModules.contains moduleName
  let allowModProvisional :=
    allowProvisionalNative && moduleName.toString.startsWith "Proof."
  let mut pEnv := parserEnv
  let mut state := initial
  let mut messages := log
  repeat
    let previous := state.pos
    let (stx, next, nextMessages) := Parser.parseCommand ctx {env := pEnv, options := {}} state messages
    state := next
    messages := nextMessages
    if messages.hasErrors || state.recovering then fail s!"command parser error in {moduleName}"
    if stx.isOfKind ``Parser.Command.eoi then break
    if state.pos <= previous then throw <| IO.userError "parser made no progress"
    inspectCommand stx allowAxioms allowModProvisional
    if stx.isOfKind ``Parser.Command.open || stx.isOfKind ``Parser.Command.openScoped then
      for id in collectIdents stx do
        pEnv := Parser.parserExtension.activateScoped pEnv id
  return Json.mkObj [("module", toJson moduleName), ("imports", toJson imports)]

-- Unlike ConstantInfo.getUsedConstantsAsSet, include all recursor-rule bodies,
-- constructor parents, mutual metadata and literal types, as well as types.
def expressionEdges (e : Expr) : IO NameSet := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then fail "open expression in stored declaration"
  let mut result := e.getUsedConstantsAsSet
  if (e.find? fun | .lit (.natVal _) => true | _ => false).isSome then
    result := result.insert `Nat
  if (e.find? fun | .lit (.strVal _) => true | _ => false).isSome then
    result := result.insert `String
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

def mkCachedDeclarationEdges : IO (ConstantInfo → IO NameSet) := do
  let cache ← IO.mkRef ({} : Std.HashMap Name NameSet)
  return fun ci => do
    if let some cached := (← cache.get)[ci.name]? then
      return cached
    let computed ← declarationEdges ci
    cache.modify (·.insert ci.name computed)
    return computed

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def origin (env : Environment) (n : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? n | fail s!"unknown declaration origin: {n}"
  let some mod := env.header.modules[idx]? | fail s!"invalid module index: {n}"
  return mod.module

/-- Verify that `ci` in `m`'s constant inventory either has primary
    `origin env ci.name == m`, or is a Lean-reserved auxiliary declaration
    (`Lean.isReservedName env ci.name`, e.g., lazily realized `.eq_k` /
    `.congr_simp` / `.splitter` theorems) identically realized by an audited
    sibling module `origMod` in `allowedSiblings` with identical kernel `type`
    and `value`. -/
def checkInventoryOrigin (env : Environment) (m : Name)
    (allowedSiblings : Name → Bool) (ci : ConstantInfo) : IO Unit := do
  let origMod ← origin env ci.name
  if origMod != m then
    unless allowedSiblings origMod && Lean.isReservedName env ci.name do
      fail s!"inventory origin mismatch {ci.name}"
    let some stored := env.checked.get.find? ci.name
      | fail s!"missing stored declaration {ci.name}"
    unless stored.type == ci.type && stored.value? true == ci.value? true do
      fail s!"stored declaration differs from inventory {ci.name}"

/-- Check whether `ci` is the Lean equation compiler's codegen-only `_unsafe_rec`
    companion for a total, safe, non-partial recursive definition `parent` in the
    same module. Such companions are never referenced by kernel terms and are
    rejected if reached in `closure`. -/
def isCodegenUnsafeRec (env : Environment) (modName : Name) (ci : ConstantInfo) : IO Bool := do
  if ci.isUnsafe || !ci.isPartial then return false
  let .str parent "_unsafe_rec" := ci.name | return false
  let some parentCi := env.checked.get.find? parent | return false
  if parentCi.isUnsafe || parentCi.isPartial then return false
  return (← origin env parent) == modName

def closure (lookup : Name → IO ConstantInfo) (provenance : Name → IO Name)
    (allowed : Array Name) (axioms : Array (String × String)) (roots : Array Name)
    (edgesOf : ConstantInfo → IO NameSet := declarationEdges) : IO (Array Name × Nat) := do
  let mut pending := roots.toList
  let mut visited : NameSet := {}
  let mut reachedAxioms : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !visited.contains n then
      visited := visited.insert n
      let m ← provenance n
      unless allowed.contains m || isStdlibMod m do fail s!"foreign dependency {n} from {m}"
      let ci ← lookup n
      if ci.isUnsafe || ci.isPartial then
        fail s!"dependency on unsafe/partial declaration {n} from {m}"
      if ci.isAxiom then
        unless axioms.contains (n.toString, m.toString) do fail s!"unapproved axiom {n} from {m}"
        reachedAxioms := reachedAxioms.insert n
      pending := (← edgesOf ci).toList ++ pending
  return (reachedAxioms.toArray.qsort Name.lt, visited.size)

/-- Enforce Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation:
    Starting from `ci.type` of a claim theorem `rootName`, walk all referenced
    constants (unfolding intermediate definitions in `unfoldModules` such as
    `Mir.<Item>.claim`, while stopping at `trusted ++ foundation`), and reject
    any constant whose module origin belongs to `forbiddenInType` (`theory/`). -/
def checkStatementOrigins (lookup : Name → IO ConstantInfo) (provenance : Name → IO Name)
    (forbiddenInType : Array Name) (unfoldModules : Array Name)
    (rootName : Name) (rootType : Expr)
    (edgesOf : ConstantInfo → IO NameSet := declarationEdges) : IO Unit := do
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
        pending := (← edgesOf ci).toList ++ pending

def audit (j : Json) (env : Environment) : IO Json := do
  let trusted ← names j "trusted"
  let foundation ← names j "foundation"
  validateGraph j env (trusted ++ foundation)
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  let edgesOf ← mkCachedDeclarationEdges
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut allNames : NameSet := {}
  let mut extraNames : NameSet := {}
  let mut inventory := #[]
  for m in env.header.modules, data in env.header.moduleData do
    unless data.constNames == data.constants.map ConstantInfo.name do fail s!"invalid inventory {m.module}"
    unless (trusted ++ foundation).contains m.module || isStdlibMod m.module do
      fail s!"foreign module {m.module}"
    if !trusted.contains m.module then
      for ci in data.constants do
        if locals.contains ci.name then fail s!"duplicate declaration {ci.name}"
        allNames := allNames.insert ci.name
    else
      for ci in data.constants do
        if allNames.contains ci.name then fail s!"duplicate declaration {ci.name}"
        allNames := allNames.insert ci.name
        unless (← origin env ci.name) == m.module do fail s!"inventory origin mismatch {ci.name}"
        let some stored := env.checked.get.find? ci.name | fail s!"missing stored declaration {ci.name}"
        unless stored.type == ci.type && stored.value? true == ci.value? true do
          fail s!"stored declaration differs from inventory {ci.name}"
        if (← isCodegenUnsafeRec env m.module ci) then
          extraNames := extraNames.insert ci.name
        else
          if ci.isUnsafe || ci.isPartial then fail s!"unsafe/partial Trusted declaration {ci.name}"
          if ci.isAxiom then fail s!"Trusted axiom {ci.name}"
          if ci.hasValue true && (ci.value? true).isNone then fail s!"missing stored body {ci.name}"
          locals := locals.insert ci.name ci
          inventory := inventory.push <| Json.mkObj [
            ("name", toJson ci.name), ("module", toJson m.module), ("kind", toJson (kind ci)),
            ("dependencies", toJson ((← edgesOf ci).toArray.qsort Name.lt))]
      for n in data.extraConstNames do
        unless (← origin env n) == m.module do fail s!"IR helper provenance mismatch {n}"
        if (env.checked.get.find? n).isSome then
          unless locals.contains n || extraNames.contains n do fail s!"uninventoried kernel compiler helper {n}"
        else
          extraNames := extraNames.insert n
  for (n, _) in env.checked.get.constants do
    if trusted.contains (← origin env n) && !locals.contains n && !extraNames.contains n then
      fail s!"uninventoried Trusted constant {n}"
  let roots := locals.toArray.map (·.1)
  let lookup n := match env.checked.get.find? n with
    | some ci => pure ci | none => fail s!"missing dependency declaration {n}"
  let (reachedAxioms, visited) ← closure lookup (origin env) (trusted ++ foundation) axiomPolicy roots edgesOf
  let baseRoots := env.header.modules.filterMap fun m =>
    if foundation.contains m.module || isStdlibMod m.module then some m.module else none
  let base ← importEnv j baseRoots
  let _ ← base.toKernelEnv.replay locals
  return Json.mkObj [
    ("graph", graphFor env (trusted ++ foundation)), ("declarations", .arr inventory),
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
  let edgesOf ← mkCachedDeclarationEdges
  let mut replayLocals : Std.HashMap Name ConstantInfo := {}
  let mut claimTheoremsChecked := 0
  let mut claimRoots : Array Name := #[]
  let mut theoryExampleRoots : Array Name := #[]
  let mut localTestAxioms : NameSet := {}
  let mut seenModules : NameSet := {}
  for m in env.header.modules, data in env.header.moduleData do
    unless allowedAll.contains m.module || isStdlibMod m.module do fail s!"foreign module {m.module}"
    if allDownstream.contains m.module then
      seenModules := seenModules.insert m.module
    if trusted.contains m.module || allDownstream.contains m.module then
      let mut testModRoots : List (Name × Name) := []
      let allowedSiblings : Name → Bool :=
        if allDownstream.contains m.module then allDownstream.contains else fun _ => false
      for ci in data.constants do
        checkInventoryOrigin env m.module allowedSiblings ci
        if !(← isCodegenUnsafeRec env m.module ci) then
          if trusted.contains m.module || strictDownstream.contains m.module then
            if ci.isUnsafe || ci.isPartial then fail s!"unsafe/partial declaration {ci.name} in {m.module}"
            if ci.isAxiom then fail s!"strict axiom declaration {ci.name} in {m.module}"
            replayLocals := replayLocals.insert ci.name ci
          else if testModules.contains m.module then
            if ci.isUnsafe || ci.isPartial then fail s!"unsafe/partial test declaration {ci.name} in {m.module}"
            if ci.isAxiom then localTestAxioms := localTestAxioms.insert ci.name
          if claimModules.contains m.module && kind ci == "theorem" then
            checkStatementOrigins lookup (origin env) theory claimModules ci.name ci.type edgesOf
            claimTheoremsChecked := claimTheoremsChecked + 1
            claimRoots := claimRoots.push ci.name
          else if (theory ++ examples).contains m.module then
            theoryExampleRoots := theoryExampleRoots.push ci.name
          else if testModules.contains m.module then
            testModRoots := (ci.name, ci.name) :: testModRoots
      if testModules.contains m.module && !testModRoots.isEmpty then
        -- File-local test axioms: only foundational axioms or axioms declared in `m.module` itself.
        let mut pending := testModRoots.reverse
        let mut visited : NameSet := {}
        while !pending.isEmpty do
          let (rootName, n) := pending.head!
          pending := pending.tail!
          if !visited.contains n then
            visited := visited.insert n
            let modName ← origin env n
            unless allowedAll.contains modName || isStdlibMod modName do
              fail s!"foreign dependency {n} from {modName}"
            let depCi ← lookup n
            if depCi.isUnsafe || depCi.isPartial then
              fail s!"{rootName} in {m.module} depends on unsafe/partial declaration {n} from {modName}"
            if depCi.isAxiom then
              if n == `sorryAx then fail s!"{rootName} in {m.module} depends on sorryAx"
              let isFoundational := axiomPolicy.contains (n.toString, modName.toString)
              let isSameFile := modName == m.module
              unless isFoundational || isSameFile do
                fail s!"{rootName} in {m.module} depends on foreign axiom {n} from {modName}"
            let deps := (← edgesOf depCi).toList.map fun d => (rootName, d)
            pending := deps ++ pending
  if !claimRoots.isEmpty then
    let _ ← closure lookup (origin env) (foundation ++ trusted ++ theory ++ claimModules) axiomPolicy claimRoots edgesOf
  if !theoryExampleRoots.isEmpty then
    let _ ← closure lookup (origin env) (foundation ++ trusted ++ theory ++ examples) axiomPolicy theoryExampleRoots edgesOf
  for reqMod in allDownstream do
    unless seenModules.contains reqMod do fail s!"missing required downstream module {reqMod}"
  let baseRoots := env.header.modules.filterMap fun m =>
    if foundation.contains m.module || isStdlibMod m.module then some m.module else none
  let base ← importEnv j baseRoots
  let _ ← base.toKernelEnv.replay replayLocals
  return Json.mkObj [
    ("downstreamModules", toJson (allDownstream.map Name.toString)),
    ("replayedDeclarations", toJson replayLocals.size),
    ("claimTheoremsChecked", toJson claimTheoremsChecked),
    ("localTestAxioms", toJson localTestAxioms.size),
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

/-- Audit a `.anneal/` verification workspace compiled by `cargo anneal verify`:
    1. Run `inspectSource` on all generated and authored workspace `.lean` files,
       permitting `axiom` declarations only in `Assumptions.*` modules and
       benign `set_option` forms (`maxHeartbeats`, `maxRecDepth`, `pp.*`,
       `linter.*`).
    2. Enforce Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation on
       each `Verify.<Item>.verified` theorem (`checkStatementOrigins`),
       unfolding workspace definitions (`Verify.*`, `Obligations.*`, `Specs.*`,
       `Mir.*`, `Assumptions.*`, `Proof.*`) and rejecting any reference in
       `ci.type` to `Anneal.*` (`theory/`).
    3. Walk the constant closure of each `Verify.<Item>.verified` theorem,
       rejecting `sorryAx` and any axiom outside foundational axioms (`propext`,
       `Quot.sound`, `Classical.choice`) and `Assumptions.*`, and classifying
       each item as `VerifiedUnconditional` or `VerifiedConditional`.
    4. Replay all workspace declarations in `baseEnv.toKernelEnv.replay`. -/
def verifyAudit (j : Json) : IO Json := do
  let searchDirs := (← match j.getObjValAs? (Array String) "searchPath" with
    | .ok d => pure d
    | .error _ => pure #[]).toList.map System.FilePath.mk
  initSearchPath (← field (α := String) j "sysroot") searchDirs
  let allowAssumptions ← match j.getObjValAs? Bool "allowAssumptions" with
    | .ok b => pure b
    | .error _ => pure false
  let allowProvisionalNative ← match j.getObjValAs? Bool "allowProvisionalNative" with
    | .ok b => pure b
    | .error _ => pure false
  let sources ← match j.getObjValAs? (Array (String × String)) "sources" with
    | .ok s => pure s
    | .error _ => pure #[]
  if !sources.isEmpty then
    unsafe enableInitializersExecution
    let parserEnv ← importModules #[{ module := `Init }, { module := `Std }] {}
      (trustLevel := 0) (plugins := #[]) (loadExts := true) (level := .private)
    for (modStr, srcPath) in sources do
      let _ ← inspectSource parserEnv modStr.toName srcPath #[] allowProvisionalNative
  let verifyModules ← names j "verifyModules"
  if verifyModules.isEmpty then fail "verifyModules must not be empty"
  let crateRollupMods ← match j.getObjValAs? (Array String) "crateRollupModules" with
    | .ok arr => pure (arr.map String.toName)
    | .error _ => pure #[]
  let allAuditModules := verifyModules ++ crateRollupMods
  let env ← importModules (allAuditModules.map fun n => { module := n }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  unless env.header.modules.size == env.header.moduleData.size do
    throw <| IO.userError "module/data array alignment failure"
  let env := env.setExporting false
  let isFoundationMod := isStdlibMod
  let isTrustedMod (m : Name) : Bool :=
    m == `Trusted || m.toString.startsWith "Trusted."
  let isTheoryMod (m : Name) : Bool :=
    m == `Anneal || m.toString.startsWith "Anneal."
  let isAssumptionsMod (m : Name) : Bool :=
    m.toString.startsWith "Assumptions."
  let isWorkspaceMod (m : Name) : Bool :=
    let s := m.toString
    s.startsWith "Mir." || s.startsWith "Obligations." ||
    s.startsWith "Specs." || s.startsWith "Assumptions." ||
    s.startsWith "Proof." || s.startsWith "Verify." ||
    m == `CrateVerify || s.startsWith "CrateVerify."
  let lookup n := match env.checked.get.find? n with
    | some ci => pure ci
    | none => fail s!"missing dependency declaration {n}"
  let mut theoryMods : Array Name := #[]
  let mut workspaceMods : Array Name := #[]
  let mut baseMods : Array Name := #[]
  let mut replayLocals : Std.HashMap Name ConstantInfo := {}
  for m in env.header.modules, data in env.header.moduleData do
    unless isFoundationMod m.module || isTrustedMod m.module ||
           isTheoryMod m.module || isWorkspaceMod m.module do
      fail s!"foreign module {m.module}"
    if isTheoryMod m.module then
      theoryMods := theoryMods.push m.module
    if isWorkspaceMod m.module then
      workspaceMods := workspaceMods.push m.module
    else
      baseMods := baseMods.push m.module
    if isWorkspaceMod m.module then
      for ci in data.constants do
        checkInventoryOrigin env m.module isWorkspaceMod ci
        if !(← isCodegenUnsafeRec env m.module ci) then
          if ci.isUnsafe || ci.isPartial then
            fail s!"unsafe/partial declaration {ci.name} in {m.module}"
          if ci.isAxiom then
            if ci.name == `sorryAx then
              fail s!"incomplete proof (sorryAx) in {m.module}"
            else if isNativeDecideAxiom ci.name then
              unless allowProvisionalNative && m.module.toString.startsWith "Proof." do
                fail s!"unapproved native_decide axiom {ci.name} in {m.module} (provisional native evaluation requires --provisional)"
            else unless isAssumptionsMod m.module do
              fail s!"unapproved axiom declaration {ci.name} in {m.module} (axioms are only permitted in Assumptions.*)"
          replayLocals := replayLocals.insert ci.name ci
  let edgesOf ← mkCachedDeclarationEdges
  let mut cleanNonWorkspace : NameSet := {}
  let mut itemReports : Array Json := #[]
  for verifyMod in verifyModules do
    unless verifyMod.toString.startsWith "Verify." do
      fail s!"invalid Verify module name {verifyMod}"
    let thmName := verifyMod.str "verified"
    let ci ← lookup thmName
    unless (← origin env thmName) == verifyMod do
      fail s!"{thmName} not defined in {verifyMod}"
    unless kind ci == "theorem" do
      fail s!"{thmName} must be a theorem declaration (found {kind ci})"
    let headConst := ci.type.getAppFn
    let isUbException :=
      headConst.isConstOf `Trusted.VerificationResult.UbExceptionVerificationResult
    unless headConst.isConstOf `Trusted.VerificationResult.VerificationResult ||
           headConst.isConstOf `Trusted.VerificationResult.StatefulVerificationResult ||
           headConst.isConstOf `Trusted.VerificationResult.ModularVerificationResult ||
           headConst.isConstOf `Trusted.VerificationResult.TraceVerificationResult ||
           headConst.isConstOf `Trusted.VerificationResult.TotalVerificationResult ||
           headConst.isConstOf `Trusted.VerificationResult.StatefulEquivVerificationResult ||
           isUbException ||
           headConst.isConstOf `Trusted.VerificationResult.CrateVerificationResult do
      fail s!"{thmName} statement must be a Trusted.VerificationResult certificate type"
    if isUbException then
      unless allowAssumptions do
        fail s!"{thmName} is a scoped UB exception (UbExceptionVerificationResult) (conditional verification requires allow_assumptions)"
    checkStatementOrigins lookup (origin env) theoryMods workspaceMods thmName ci.type edgesOf
    let mut pending := [thmName]
    let mut visited : NameSet := {}
    let mut visitedNonWorkspace : NameSet := {}
    let mut reachedAssumptions : NameSet := {}
    let mut reachedProvisional : NameSet := {}
    while !pending.isEmpty do
      let n := pending.head!
      pending := pending.tail!
      if !visited.contains n && !cleanNonWorkspace.contains n then
        visited := visited.insert n
        let modName ← origin env n
        if !isWorkspaceMod modName && !isNativeDecideAxiom n then
          visitedNonWorkspace := visitedNonWorkspace.insert n
        let depCi ← lookup n
        if depCi.isUnsafe || depCi.isPartial then
          fail s!"{thmName} depends on unsafe/partial declaration {n} from {modName}"
        if depCi.isAxiom then
          if n == `sorryAx then
            fail s!"{thmName} depends on sorryAx"
          let isFoundational :=
            isFoundationMod modName &&
            (n == `propext || n == `Quot.sound || n == `Classical.choice)
          if !isFoundational then
            if isNativeDecideAxiom n then
              unless allowProvisionalNative do
                fail s!"{thmName} depends on provisional native_decide axiom {n} from {modName} (provisional native evaluation requires --provisional)"
              reachedProvisional := reachedProvisional.insert n
            else if isAssumptionsMod modName then
              unless allowAssumptions do
                fail s!"{thmName} depends on assumption axiom {n} from {modName} (conditional verification requires allow_assumptions)"
              reachedAssumptions := reachedAssumptions.insert n
            else
              fail s!"{thmName} depends on unapproved axiom {n} from {modName}"
        pending := (← edgesOf depCi).toList ++ pending
    cleanNonWorkspace := cleanNonWorkspace ++ visitedNonWorkspace
    let itemSuffix := (verifyMod.toString.drop 7).toString
    let sortedAssumptions := (reachedAssumptions.toArray.qsort Name.lt).map Name.toString
    let sortedProvisional := (reachedProvisional.toArray.qsort Name.lt).map Name.toString
    let status :=
      if !sortedProvisional.isEmpty then "ProvisionalNative"
      else if isUbException then "VerifiedUbException"
      else if sortedAssumptions.isEmpty then "VerifiedUnconditional"
      else "VerifiedConditional"
    let combinedDeps :=
      if !sortedProvisional.isEmpty then sortedProvisional ++ sortedAssumptions
      else sortedAssumptions
    let assumptionsCsv := String.intercalate "," combinedDeps.toList
    IO.println s!"VERIFY_AUDIT_ITEM\t{verifyMod}\t{status}\t{assumptionsCsv}"
    itemReports := itemReports.push <| Json.mkObj [
      ("item", toJson itemSuffix),
      ("theorem", toJson thmName.toString),
      ("status", toJson status),
      ("assumptions", toJson combinedDeps)
    ]
  for rollupMod in crateRollupMods do
    let thmName := rollupMod.str "verified"
    let ci ← lookup thmName
    unless (← origin env thmName) == rollupMod do
      fail s!"{thmName} not defined in {rollupMod}"
    unless kind ci == "theorem" do
      fail s!"{thmName} must be a theorem declaration (found {kind ci})"
    let headConst := ci.type.getAppFn
    unless headConst.isConstOf `Trusted.VerificationResult.CrateVerificationResult do
      fail s!"{thmName} statement must be Trusted.VerificationResult.CrateVerificationResult"
    checkStatementOrigins lookup (origin env) theoryMods workspaceMods thmName ci.type edgesOf
    let mut pending := [thmName]
    let mut visited : NameSet := {}
    let mut visitedNonWorkspace : NameSet := {}
    while !pending.isEmpty do
      let n := pending.head!
      pending := pending.tail!
      if !visited.contains n && !cleanNonWorkspace.contains n then
        visited := visited.insert n
        let modName ← origin env n
        if !isWorkspaceMod modName && !isNativeDecideAxiom n then
          visitedNonWorkspace := visitedNonWorkspace.insert n
        let depCi ← lookup n
        if depCi.isUnsafe || depCi.isPartial then
          fail s!"{thmName} depends on unsafe/partial declaration {n} from {modName}"
        if depCi.isAxiom then
          if n == `sorryAx then
            fail s!"{thmName} depends on sorryAx"
          let isFoundational :=
            isFoundationMod modName &&
            (n == `propext || n == `Quot.sound || n == `Classical.choice)
          if !isFoundational then
            if isNativeDecideAxiom n then
              unless allowProvisionalNative do
                fail s!"{thmName} depends on provisional native_decide axiom {n} from {modName} (provisional native evaluation requires --provisional)"
            else if isAssumptionsMod modName then
              unless allowAssumptions do
                fail s!"{thmName} depends on assumption axiom {n} from {modName} (conditional verification requires allow_assumptions)"
            else
              fail s!"{thmName} depends on unapproved axiom {n} from {modName}"
        pending := (← edgesOf depCi).toList ++ pending
    cleanNonWorkspace := cleanNonWorkspace ++ visitedNonWorkspace
  let baseEnv ← importModules (baseMods.map fun n => { module := n }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let _ ← baseEnv.toKernelEnv.replay replayLocals
  return Json.mkObj [
    ("items", .arr itemReports),
    ("replayedDeclarations", toJson replayLocals.size),
    ("replay", toJson true)
  ]

def runVerifyAuditCli (rest : List String) : IO Json := do
  let sysroot ← Lean.findSysroot "lean"
  let leanPathStr := (← IO.getEnv "LEAN_PATH").getD ""
  let sp := System.SearchPath.parse leanPathStr
  let mut allowAssumptions := false
  let mut allowProvisionalNative := false
  let mut verifyModules : Array Json := #[]
  let mut crateRollupModules : Array Json := #[]
  let mut sources : Array Json := #[]
  for arg in rest do
    if arg == "--allow-assumptions=true" then
      allowAssumptions := true
    else if arg == "--allow-assumptions=false" then
      allowAssumptions := false
    else if arg == "--allow-provisional-native=true" then
      allowProvisionalNative := true
    else if arg == "--allow-provisional-native=false" then
      allowProvisionalNative := false
    else if arg.startsWith "--verify-modules=" then
      let csv := (arg.drop 17).toString
      for m in csv.splitOn "," do
        if !m.isEmpty then
          verifyModules := verifyModules.push (toJson m)
    else if arg.startsWith "--crate-rollup-modules=" then
      let csv := (arg.drop 23).toString
      for m in csv.splitOn "," do
        if !m.isEmpty then
          crateRollupModules := crateRollupModules.push (toJson m)
    else if arg.startsWith "--source=" then
      let kv := (arg.drop 9).toString
      match kv.splitOn "=" with
      | modName :: pathParts =>
        let p := String.intercalate "=" pathParts
        sources := sources.push (toJson (modName, p))
      | [] => pure ()
  let j := Json.mkObj [
    ("mode", toJson "verify-audit"),
    ("sysroot", toJson sysroot.toString),
    ("searchPath", toJson (sp.map (·.toString)).toArray),
    ("allowAssumptions", toJson allowAssumptions),
    ("allowProvisionalNative", toJson allowProvisionalNative),
    ("verifyModules", .arr verifyModules),
    ("crateRollupModules", .arr crateRollupModules),
    ("sources", .arr sources)
  ]
  verifyAudit j

def run (j : Json) : IO Json := do
  let mode ← field (α := String) j "mode"
  if mode == "graph-tests" then return ← graphTests
  if mode == "verify-audit" then return ← verifyAudit j
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
    return Json.mkObj [("graph", graphFor env foundation)]
  if mode == "preflight" then
    let fEnv ← importEnv j foundation
    validateGraph j fEnv foundation
    let sources ← field (α := Array (String × String)) j "sources"
    let allowedAxiomMods ← match j.getObjValAs? (Array String) "allowedAxiomModules" with
      | .ok arr => pure (arr.map String.toName)
      | .error _ => pure #[]
    let allowProvisionalNative := match j.getObjValAs? Bool "allowProvisionalNative" with
      | .ok b => b
      | .error _ => false
    let mut needsStd := false
    for (_, p) in sources do
      let txt ← IO.FS.readFile p
      if (txt.splitOn "Std").length > 1 then needsStd := true
    let parserRoots := (if needsStd then #[`Init, `Std] else #[`Init]) ++
      foundation.filter (!isStdlibMod ·)
    let parserEnv ← importEnv j parserRoots true
    let headers ← sources.mapM fun (n, p) =>
      inspectSource parserEnv n.toName p allowedAxiomMods allowProvisionalNative
    return Json.mkObj [("headers", .arr headers), ("graph", graphFor fEnv foundation)]
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
  throw <| IO.userError s!"unknown inspector mode {mode}"

end TrustedBoundary

def main (args : List String) : IO UInt32 := do
  match args with
  | "verify-audit" :: rest =>
    try
      let _ ← TrustedBoundary.runVerifyAuditCli rest
      return 0
    catch error =>
      let message := error.toString
      let category := if message.startsWith "policy:" then "policy" else "operational"
      IO.eprintln message
      return if category == "policy" then 1 else 2
  | [request, output] =>
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
  | _ =>
    IO.eprintln "expected request and result files"
    return 2
