import Lean.Meta.Basic
import Lean.Meta.SynthInstance
import Lean.PrettyPrinter
import Lean.Replay
import Lean.Util.CollectAxioms
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr
import Trusted.VerificationResult

/-!
# Compiled `.olean` / `.olean.private` `MetaM` Environment Auditor and Constructive Specification-Strength Harness (Prototype)

This prototype module combines two complementary verification-integrity mechanisms
directly inside Lean `v4.34.1` with zero external Python source-text regex scanning:

1. **Compiled `.olean` / `.olean.private` `MetaM` Environment Auditor**:
   Inspects compiled Lean `v4.34.1` module environments (`OLeanLevel.private`,
   `env.setExporting false`, `env.checked.get`, `Lean.collectAxioms`, and compiler
   override attribute tables `@[implemented_by]`, `@[extern]`, `@[csimp]`) across
   the full kernel constant graph (`ci.type`, `ci.value? (allowOpaque := true)`,
   recursor `rules`, inductive `ctors`, constructor `induct`, mutual `all`, `.proj`
   struct references, and `Nat`/`String` literals).
   - Enforces statement-vs.-proof origin separation (rejecting `Proof.*` / `Anneal.*`
     leaks in `ci.type` while permitting them inside `ci.value?`).
   - Detects Lean `v4.34.1` `module`-system `.olean` files missing their companion
     `.olean.private` artifacts (which hold private axioms and theorem proof terms).
   - Optionally replays target declarations inside a fresh `baseEnv.toKernelEnv.replay`.

2. **Constructive Specification-Strength Mutant Harness (`SpecStrengthCert`, `MultiMutantSpecCert`)**:
   Inspired by *DafnyCert* (`arXiv:2611.15548`) and *Proving the Wrong Program*
   (`arXiv:2611.04701`), provides kernel-checked, completely constructive witnesses
   (zero `Classical.choice`, zero `sorryAx`) certifying that a contract `(req, ens)`
   is non-vacuous, realizable, and kills concrete specification mutants. Bridges
   directly to `Trusted.VerificationResult` (`ItemSpec`, `StatefulItemSpec`,
   `ModularItemSpec`) and provides a `MetaM` gate (`auditSpecStrengthCertInEnv`)
   that ensures registered specification-strength certificates actually match the
   target specification and pass the full environment audit themselves.
-/

namespace Anneal.OleanSpecStrengthAuditorProto

open Lean
open Trusted.VerificationResult
open Trusted.MirSemantics
open Trusted.ITree

/-! ## Part 1: Compiled `.olean` / `.olean.private` `MetaM` Environment Auditor -/

/-- Policy governing compiled-environment and `MetaM` trust-boundary audits. -/
structure AuditPolicy where
  /-- Foundational axioms permitted in audited closures. -/
  allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  /-- Whether `Lean.trustCompiler` is permitted (false by default). -/
  allowTrustCompiler : Bool := false
  /-- Whether axioms originating in `Assumptions.*` modules/namespaces are allowed. -/
  allowAssumptionsNamespace : Bool := false
  /-- Whether provisional `native_decide` axioms (`Lean.ofReduceBool`,
      `Lean.ofReduceNat`, `._native.`) are permitted. -/
  allowProvisionalNative : Bool := false
  /-- Whether compiler override attributes (`@[implemented_by]`, `@[extern]`,
      `@[csimp]`) are forbidden on non-stdlib declarations in the closure. -/
  checkCompilerOverrides : Bool := true
  /-- Whether a Lean `v4.34.1` `module`-system `.olean` (`ModuleData.isModule = true`)
      must have a companion `.olean.private` artifact on disk. -/
  requirePrivateOleanForModuleSystem : Bool := true
  /-- Whether every target declaration must be a theorem (`.thmInfo`). -/
  requireTheoremKind : Bool := false
  /-- Whether to reject `partial` / `._unsafe_rec` and `unsafe` dependencies. -/
  forbidPartialAndUnsafe : Bool := true
  /-- Namespace/module roots explicitly unfolded when checking statement-origin
      separation over `ci.type`. -/
  statementUnfoldRoots : Array Name := #[`Specs, `Mir, `Obligations, `Verify, `CrateVerify, `Proof]
  /-- Namespace/module roots forbidden anywhere in the unfolded `ci.type` closure. -/
  statementForbiddenRoots : Array Name := #[`Proof, `Anneal]
  /-- Trusted boundary roots where statement-origin unfolding stops (unless a
      constant also matches `statementForbiddenRoots`). -/
  statementAllowedRoots : Array Name := #[`Init, `Std, `Trusted]
  /-- Whether to enforce statement-vs.-proof origin separation on targets. -/
  checkStatementOrigin : Bool := true
  /-- Whether to cross-check transitive axioms against `Lean.collectAxioms` in
      `env.setExporting false`. -/
  crossCheckCollectAxioms : Bool := true
  deriving Repr, Inhabited

/-- Constructive policy forbidding `Classical.choice` (allowing only `propext` and `Quot.sound`). -/
def AuditPolicy.constructive : AuditPolicy :=
  { allowedAxioms := #[``propext, ``Quot.sound] }

/-- Strict verification-claim policy requiring `.thmInfo` and statement-origin separation. -/
def AuditPolicy.strictClaim : AuditPolicy :=
  { requireTheoremKind := true, checkStatementOrigin := true }

/-- Constructive verification-claim policy (no `Classical.choice`, theorem kind required). -/
def AuditPolicy.constructiveClaim : AuditPolicy :=
  { allowedAxioms := #[``propext, ``Quot.sound]
    requireTheoremKind := true
    checkStatementOrigin := true }

/-- Structured audit violation reported fail-closed by the environment auditor. -/
inductive AuditViolation where
  | missingDeclaration (decl : Name)
  | notTheoremKind (decl : Name) (actualKind : String)
  | openTermExpression (target : Name) (decl : Name) (part : String)
  | sorryAxiomReached (target : Name) (via : Name)
  | nativeDecideReached (target : Name) (axiomName : Name) (moduleName? : Option Name)
  | unapprovedAxiom (target : Name) (axiomName : Name) (moduleName? : Option Name) (reason : String)
  | unsafeDeclaration (target : Name) (decl : Name) (moduleName? : Option Name)
  | partialOrUnsafeRecDependency (target : Name) (decl : Name) (moduleName? : Option Name) (reason : String)
  | compilerOverrideAttribute (target : Name) (decl : Name) (attrKind : String) (detail : String)
  | statementOriginLeak (target : Name) (leakedConst : Name) (moduleName? : Option Name) (viaChain : Array Name)
  | missingPrivateArtifact (moduleName : Name) (expectedPath : String)
  | specStrengthCertMissing (specName : Name) (reason : String)
  | specStrengthCertInvalidType (certDecl : Name) (expectedSpec : Name) (actualType : String)
  | kernelReplayFailed (detail : String)
  deriving Repr, BEq

/-- Deterministic metrics recorded for every audit run. -/
structure AuditStats where
  targetsAudited : Nat := 0
  reachableDeclarations : Nat := 0
  axiomsFound : Array Name := #[]
  modulesLoaded : Nat := 0
  privateArtifactsChecked : Nat := 0
  kernelReplayedDeclarations : Nat := 0
  elapsedMicros : Nat := 0
  deriving Repr, BEq, Inhabited

/-- Outcome of an audit run. -/
inductive AuditVerdict where
  | ok (stats : AuditStats)
  | rejected (violations : Array AuditViolation) (stats : AuditStats)
  deriving Repr, BEq

def AuditVerdict.isOk : AuditVerdict → Bool
  | .ok _ => true
  | .rejected _ _ => false

def AuditVerdict.violations : AuditVerdict → Array AuditViolation
  | .ok _ => #[]
  | .rejected vs _ => vs

def AuditVerdict.stats : AuditVerdict → AuditStats
  | .ok s => s
  | .rejected _ s => s

def AuditViolation.tag : AuditViolation → String
  | .missingDeclaration _ => "missingDeclaration"
  | .notTheoremKind _ _ => "notTheoremKind"
  | .openTermExpression _ _ _ => "openTermExpression"
  | .sorryAxiomReached _ _ => "sorryAxiomReached"
  | .nativeDecideReached _ _ _ => "nativeDecideReached"
  | .unapprovedAxiom _ _ _ _ => "unapprovedAxiom"
  | .unsafeDeclaration _ _ _ => "unsafeDeclaration"
  | .partialOrUnsafeRecDependency _ _ _ _ => "partialOrUnsafeRecDependency"
  | .compilerOverrideAttribute _ _ _ _ => "compilerOverrideAttribute"
  | .statementOriginLeak _ _ _ _ => "statementOriginLeak"
  | .missingPrivateArtifact _ _ => "missingPrivateArtifact"
  | .specStrengthCertMissing _ _ => "specStrengthCertMissing"
  | .specStrengthCertInvalidType _ _ _ => "specStrengthCertInvalidType"
  | .kernelReplayFailed _ => "kernelReplayFailed"

private def optNameToJson : Option Name → Json
  | none => Json.null
  | some n => toJson n.toString

instance : ToJson AuditViolation where
  toJson
    | .missingDeclaration decl =>
      Json.mkObj [("kind", toJson "missingDeclaration"), ("decl", toJson decl.toString)]
    | .notTheoremKind decl actualKind =>
      Json.mkObj [
        ("kind", toJson "notTheoremKind"),
        ("decl", toJson decl.toString),
        ("actualKind", toJson actualKind)]
    | .openTermExpression target decl part =>
      Json.mkObj [
        ("kind", toJson "openTermExpression"),
        ("target", toJson target.toString),
        ("decl", toJson decl.toString),
        ("part", toJson part)]
    | .sorryAxiomReached target via =>
      Json.mkObj [
        ("kind", toJson "sorryAxiomReached"),
        ("target", toJson target.toString),
        ("via", toJson via.toString)]
    | .nativeDecideReached target axiomName mod? =>
      Json.mkObj [
        ("kind", toJson "nativeDecideReached"),
        ("target", toJson target.toString),
        ("axiomName", toJson axiomName.toString),
        ("module", optNameToJson mod?)]
    | .unapprovedAxiom target axiomName mod? reason =>
      Json.mkObj [
        ("kind", toJson "unapprovedAxiom"),
        ("target", toJson target.toString),
        ("axiomName", toJson axiomName.toString),
        ("module", optNameToJson mod?),
        ("reason", toJson reason)]
    | .unsafeDeclaration target decl mod? =>
      Json.mkObj [
        ("kind", toJson "unsafeDeclaration"),
        ("target", toJson target.toString),
        ("decl", toJson decl.toString),
        ("module", optNameToJson mod?)]
    | .partialOrUnsafeRecDependency target decl mod? reason =>
      Json.mkObj [
        ("kind", toJson "partialOrUnsafeRecDependency"),
        ("target", toJson target.toString),
        ("decl", toJson decl.toString),
        ("module", optNameToJson mod?),
        ("reason", toJson reason)]
    | .compilerOverrideAttribute target decl attrKind detail =>
      Json.mkObj [
        ("kind", toJson "compilerOverrideAttribute"),
        ("target", toJson target.toString),
        ("decl", toJson decl.toString),
        ("attrKind", toJson attrKind),
        ("detail", toJson detail)]
    | .statementOriginLeak target leakedConst mod? viaChain =>
      Json.mkObj [
        ("kind", toJson "statementOriginLeak"),
        ("target", toJson target.toString),
        ("leakedConst", toJson leakedConst.toString),
        ("module", optNameToJson mod?),
        ("viaChain", toJson (viaChain.map Name.toString))]
    | .missingPrivateArtifact moduleName expectedPath =>
      Json.mkObj [
        ("kind", toJson "missingPrivateArtifact"),
        ("module", toJson moduleName.toString),
        ("expectedPath", toJson expectedPath)]
    | .specStrengthCertMissing specName reason =>
      Json.mkObj [
        ("kind", toJson "specStrengthCertMissing"),
        ("specName", toJson specName.toString),
        ("reason", toJson reason)]
    | .specStrengthCertInvalidType certDecl expectedSpec actualType =>
      Json.mkObj [
        ("kind", toJson "specStrengthCertInvalidType"),
        ("certDecl", toJson certDecl.toString),
        ("expectedSpec", toJson expectedSpec.toString),
        ("actualType", toJson actualType)]
    | .kernelReplayFailed detail =>
      Json.mkObj [
        ("kind", toJson "kernelReplayFailed"),
        ("detail", toJson detail)]

instance : ToJson AuditStats where
  toJson s :=
    Json.mkObj [
      ("targetsAudited", toJson s.targetsAudited),
      ("reachableDeclarations", toJson s.reachableDeclarations),
      ("axiomsFound", toJson ((s.axiomsFound.qsort Name.lt).map Name.toString)),
      ("modulesLoaded", toJson s.modulesLoaded),
      ("privateArtifactsChecked", toJson s.privateArtifactsChecked),
      ("kernelReplayedDeclarations", toJson s.kernelReplayedDeclarations),
      ("elapsedMicros", toJson s.elapsedMicros)]

instance : ToJson AuditVerdict where
  toJson
    | .ok stats =>
      Json.mkObj [
        ("status", toJson "ok"),
        ("violations", Json.arr #[]),
        ("stats", toJson stats)]
    | .rejected violations stats =>
      Json.mkObj [
        ("status", toJson "rejected"),
        ("violations", toJson violations),
        ("stats", toJson stats)]

/-- Deterministic machine-readable JSON receipt for an `AuditVerdict`. -/
def auditReportJson (verdict : AuditVerdict) : Json :=
  toJson verdict

/-! ### Core Helpers: Naming, Provenance, Graph Edges, and Compiler Override Index -/

/-- Human-readable kind string for a kernel `ConstantInfo`. -/
def constantInfoKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Check whether `m` is part of the Lean standard library (`Init`, `Init.*`, `Std`, `Std.*`).
    Note: `Lean.*` compiler/metaprogramming modules are deliberately excluded from `isStdlibMod`. -/
def isStdlibMod (m : Name) : Bool :=
  let s := m.toString
  m == `Init || s.startsWith "Init." || m == `Std || s.startsWith "Std."

/-- Check whether `m` is part of the pinned Lean compiler library (`Lean`, `Lean.*`).
    Used only to avoid redundant on-disk sysroot scans in `checkPrivateOleanArtifactsIO`;
    `Lean.*` is NEVER treated as trusted stdlib in declaration/override audits. -/
def isLeanCompilerMod (m : Name) : Bool :=
  let s := m.toString
  m == `Lean || s.startsWith "Lean."

/-- Test whether `n` starts with namespace/module root `root` (e.g. `Anneal` matches
    both `Anneal` and `Anneal.Foo.bar`). Unmangles `_private.<mod>.0.<name>` prefixes
    before matching so private constants cannot evade namespace-root checks. -/
def matchesRootPrefix (n : Name) (root : Name) : Bool :=
  let check (cand : Name) : Bool :=
    let cs := cand.toString
    let rs := root.toString
    cand == root || cs.startsWith (rs ++ ".")
  check n || check (Lean.privateToUserName n)

/-- Test whether a module name or constant name matches any root in `roots`. -/
def matchesAnyRoot (n : Name) (modName? : Option Name) (roots : Array Name) : Bool :=
  roots.any fun r =>
    matchesRootPrefix n r ||
    match modName? with
    | some m => matchesRootPrefix m r
    | none => false

/-- Look up the defining module name of constant `n` in `env`, or `none` if `n`
    is local to `env.header.mainModule` (in-memory elaboration). -/
def originModule? (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.modules[idx]?).map (·.module)
  | none => none

/-- Effective module name of `n` (`originModule?` falling back to `env.header.mainModule`
    when `env.header.mainModule` is non-anonymous). -/
def effectiveModule? (env : Environment) (n : Name) : Option Name :=
  match originModule? env n with
  | some m => some m
  | none => if env.header.mainModule.isAnonymous then none else some env.header.mainModule

/-- Test whether `n` is a `native_decide` axiom (`Lean.ofReduceBool`, `Lean.ofReduceNat`,
    or a generated `._native.` auxiliary axiom). -/
def isNativeDecideAxiom (n : Name) : Bool :=
  n == ``Lean.ofReduceBool || n == ``Lean.ofReduceNat ||
  n == `Lean.ofReduceBool || n == `Lean.ofReduceNat ||
  (n.toString.splitOn "._native.").length > 1

/-- Test whether `n` is `Lean.trustCompiler`. -/
def isTrustCompilerAxiom (n : Name) : Bool :=
  n == ``Lean.trustCompiler || n == `Lean.trustCompiler

/-- Test whether `n` has a `._unsafe_rec` component anywhere in its name. -/
def hasUnsafeRecComponent (n : Name) : Bool :=
  match n with
  | .str _ "_unsafe_rec" => true
  | _ => (n.toString.splitOn "._unsafe_rec").length > 1

/-- Check whether `ci` is the Lean equation compiler's dead codegen-only `_unsafe_rec`
    companion for a safe, total, non-partial parent `defnInfo` in the same module.
    Such companions are skipped during module inventory scans, but are ALWAYS rejected
    if ever reached in any declaration's transitive closure. -/
def isCodegenUnsafeRec (env : Environment) (modName? : Option Name) (ci : ConstantInfo) : Bool :=
  if ci.isUnsafe || !ci.isPartial then false
  else
    match ci.name with
    | .str parent "_unsafe_rec" =>
      match env.checked.get.find? parent with
      | some parentCi =>
        if parentCi.isUnsafe || parentCi.isPartial then false
        else
          match parentCi with
          | .defnInfo _ => originModule? env parent == modName?
          | _ => false
      | none => false
    | _ => false

/-- Inspect `e : Expr` for open term artifacts (`FVar`, `MVar`, loose `BVar`) and
    extract all constant edges, including `.const`, `.proj` struct names, and
    `Nat`/`String` literal type dependencies. Total (no `partial`, no `unsafe`). -/
def expressionEdges (e : Expr) : Except String NameSet := do
  if e.hasFVar then
    throw "free variable (FVar) in stored expression"
  if e.hasMVar then
    throw "metavariable (MVar) in stored expression"
  if e.hasLooseBVars then
    throw "loose bound variable (BVar) in stored expression"
  let mut result := e.getUsedConstantsAsSet
  if (e.find? fun | .lit (.natVal _) => true | _ => false).isSome then
    result := result.insert ``Nat
  if (e.find? fun | .lit (.strVal _) => true | _ => false).isSome then
    result := result.insert ``String
  return result

/-- Extract all kernel dependency edges of `ci : ConstantInfo`:
    `ci.type`, `ci.value? (allowOpaque := true)` (critical for opaque/partial/theorem
    bodies), mutual `all`, inductive `ctors`, constructor `induct`, and every recursor
    rule's `ctor` and `rhs`. Returns `(edges, openTermViolations)`. -/
def declarationEdges (target : Name) (ci : ConstantInfo) : NameSet × Array AuditViolation := Id.run do
  let mut edges : NameSet := {}
  let mut violations : Array AuditViolation := #[]
  match expressionEdges ci.type with
  | .ok es => edges := edges ++ es
  | .error msg => violations := violations.push (.openTermExpression target ci.name s!"type: {msg}")
  if let some val := ci.value? (allowOpaque := true) then
    match expressionEdges val with
    | .ok es => edges := edges ++ es
    | .error msg => violations := violations.push (.openTermExpression target ci.name s!"value: {msg}")
  match ci with
  | .defnInfo v =>
    for a in v.all do edges := edges.insert a
  | .thmInfo v =>
    for a in v.all do edges := edges.insert a
  | .opaqueInfo v =>
    for a in v.all do edges := edges.insert a
  | .inductInfo v =>
    for a in v.all do edges := edges.insert a
    for c in v.ctors do edges := edges.insert c
  | .ctorInfo v =>
    edges := edges.insert v.induct
  | .recInfo v =>
    for a in v.all do edges := edges.insert a
    for rule in v.rules do
      edges := edges.insert rule.ctor
      match expressionEdges rule.rhs with
      | .ok es => edges := edges ++ es
      | .error msg =>
        violations := violations.push (.openTermExpression target ci.name s!"recRule({rule.ctor}): {msg}")
  | _ => pure ()
  return (edges, violations)

/-- Index of `@[csimp]` theorems and redirected `fromDeclName`s collected directly
    from BOTH the live extension state AND raw `importedEntries` (so `@[csimp]` is
    caught even when `.olean`s are loaded with `loadExts := false`!). -/
structure CSimpIndex where
  thmNames : NameSet := {}
  fromToThm : Std.HashMap Name (Name × Name) := {}

/-- Build `CSimpIndex` across all non-stdlib imported modules and the live local state. -/
def buildCSimpIndex (privEnv : Environment) : CSimpIndex := Id.run do
  let mut thmNames : NameSet := {}
  let mut fromToThm : Std.HashMap Name (Name × Name) := {}
  -- 1. Live local state (populated during elaboration or `loadExts := true`).
  let st := Lean.Compiler.CSimp.ext.getState privEnv
  thmNames := st.thmNames.fold (init := thmNames) fun acc thm => acc.insert thm
  let (thmNames', fromToThm') := st.map.fold (init := (thmNames, fromToThm)) fun (tAcc, mAcc) fromDecl ent =>
    if !((originModule? privEnv ent.thmName).any isStdlibMod) then
      (tAcc.insert ent.thmName, mAcc.insert fromDecl (ent.toDeclName, ent.thmName))
    else
      (tAcc, mAcc)
  thmNames := thmNames'
  fromToThm := fromToThm'
  -- 2. Raw imported module entries (works even under `loadExts := false`!).
  let mods := privEnv.header.modules
  for h : modIdx in [:mods.size] do
    let modName := mods[modIdx].module
    if !isStdlibMod modName then
      let rawEntries := Lean.Compiler.CSimp.ext.ext.getModuleEntries privEnv modIdx
      for raw in rawEntries do
        let ent := match raw with
          | .global e => e
          | .scoped _ e => e
        thmNames := thmNames.insert ent.thmName
        fromToThm := fromToThm.insert ent.fromDeclName (ent.toDeclName, ent.thmName)
  return { thmNames, fromToThm }

/-- Pure `MonadEnv` runner allowing `Lean.collectAxioms` to run directly on any
    `Environment` value (in pure code, `IO`, or `MetaM`) with `env.setExporting false`. -/
private abbrev EnvReadM := ReaderT Environment Id

private instance : MonadEnv EnvReadM where
  getEnv := read
  modifyEnv _ := pure ()

/-- Cross-check axioms using Lean's built-in `Lean.collectAxioms` in `env.setExporting false`. -/
def collectAxiomsPrivate (env : Environment) (declName : Name) : Array Name :=
  let privEnv := env.setExporting false
  (Lean.collectAxioms (m := EnvReadM) declName).run privEnv

/-- Linear-time $O(V + E)$ batch axiom collector over `env.checked.get` in
    `env.setExporting false`. Avoids the $O(T \cdot (V + E))$ penalty of calling
    `Lean.collectAxioms` per declaration when `importModules (loadExts := false)`
    leaves `exportedAxiomsExt` unpopulated. -/
def collectAxiomsBatchPrivate (env : Environment) (targets : Array Name) : Array Name := Id.run do
  let privEnv := env.setExporting false
  let kenv := privEnv.checked.get
  let modConstTotal := privEnv.header.moduleData.foldl (init := 0) fun acc d => acc + d.constants.size
  let fuel := max 250000 (modConstTotal * 2 + targets.size * 2 + 16384)
  let mut pending : Array Name := #[]
  let mut seen : NameSet := {}
  let mut axs : NameSet := {}
  for t in targets do
    if !seen.contains t then
      seen := seen.insert t
      pending := pending.push t
  for _ in [:fuel] do
    if pending.isEmpty then
      break
    let c := pending.back!
    pending := pending.pop
    if let some ci := kenv.find? c then
      if ci.isAxiom then
        axs := axs.insert c
      for d in ci.type.getUsedConstants do
        if !seen.contains d then
          seen := seen.insert d
          pending := pending.push d
      match ci with
      | .defnInfo v =>
        for d in v.value.getUsedConstants do
          if !seen.contains d then
            seen := seen.insert d
            pending := pending.push d
      | .thmInfo v =>
        for d in v.value.getUsedConstants do
          if !seen.contains d then
            seen := seen.insert d
            pending := pending.push d
      | .opaqueInfo v =>
        for d in v.value.getUsedConstants do
          if !seen.contains d then
            seen := seen.insert d
            pending := pending.push d
      | .inductInfo v =>
        for ctor in v.ctors do
          if !seen.contains ctor then
            seen := seen.insert ctor
            pending := pending.push ctor
      | _ => pure ()
  return axs.toArray.qsort Name.lt

private def pushUniqueViolation (vs : Array AuditViolation) (v : AuditViolation) : Array AuditViolation :=
  if vs.contains v then vs else vs.push v

/-- Validate an axiom `axName` reached from `target` under `policy`. -/
def checkAxiomAllowed (privEnv : Environment) (policy : AuditPolicy)
    (target : Name) (axName : Name) : Option AuditViolation :=
  let modName? := originModule? privEnv axName
  if axName == ``sorryAx || axName == `sorryAx then
    some (.sorryAxiomReached target axName)
  else if isNativeDecideAxiom axName then
    if policy.allowProvisionalNative then none
    else some (.nativeDecideReached target axName modName?)
  else if isTrustCompilerAxiom axName then
    if policy.allowTrustCompiler then none
    else some (.unapprovedAxiom target axName modName? "Lean.trustCompiler is disallowed by policy")
  else if policy.allowedAxioms.contains axName then
    none
  else if policy.allowAssumptionsNamespace &&
          matchesAnyRoot axName modName? #[`Assumptions] then
    none
  else
    some (.unapprovedAxiom target axName modName? "axiom not in policy.allowedAxioms")

/-- Check whether `n` is a `partial def` (either `.defnInfo` with `safety == .partial`,
    a `._unsafe_rec` symbol, or an `.opaqueInfo` backed by `@[implemented_by ..._unsafe_rec]`
    or a sibling `n._unsafe_rec` partial/unsafe helper). -/
def detectPartialOrUnsafeRec (privEnv : Environment) (n : Name) (ci : ConstantInfo) : Option String :=
  if ci.isPartial then
    some "constant marked partial in kernel ConstantInfo"
  else if hasUnsafeRecComponent n then
    some "reachable _unsafe_rec partial/unsafe recursion helper"
  else
    match ci with
    | .opaqueInfo _ =>
      match Lean.Compiler.getImplementedBy? privEnv n with
      | some imp =>
        let impIsPartial := match privEnv.checked.get.find? imp with
          | some impCi => impCi.isPartial || impCi.isUnsafe
          | none => false
        if hasUnsafeRecComponent imp || impIsPartial then
          some s!"opaque partial definition backed by implemented_by {imp}"
        else none
      | none =>
        let recName := n.str "_unsafe_rec"
        match privEnv.checked.get.find? recName with
        | some recCi =>
          if recCi.isPartial || recCi.isUnsafe then
            some s!"opaque partial definition with sibling {recName}"
          else none
        | none => none
    | _ => none

/-- Check compiler override attributes (`@[implemented_by]`, `@[extern]`, `@[csimp]`)
    on non-stdlib declaration `n`. Skips `implemented_by` entries that were already
    classified as `partial def` backing (`_unsafe_rec`). -/
def checkCompilerOverridesOnDecl (privEnv : Environment) (csimpIdx : CSimpIndex)
    (target : Name) (n : Name) (ci : ConstantInfo) (alreadyPartial : Bool) : Array AuditViolation := Id.run do
  let modName? := originModule? privEnv n
  if modName?.any isStdlibMod then
    return #[]
  let mut vs : Array AuditViolation := #[]
  if !alreadyPartial then
    if let some imp := Lean.Compiler.getImplementedBy? privEnv n then
      vs := vs.push (.compilerOverrideAttribute target n "implemented_by" s!"implemented_by {imp}")
  if Lean.isExternC privEnv n then
    let cSym := (Lean.getExternNameFor privEnv `all n).getD "<extern_c>"
    vs := vs.push (.compilerOverrideAttribute target n "extern_c" s!"extern \"{cSym}\"")
  else if Lean.isExtern privEnv n then
    vs := vs.push (.compilerOverrideAttribute target n "extern" "extern compiler attribute")
  if Lean.Compiler.hasCSimpAttribute privEnv n || csimpIdx.thmNames.contains n then
    vs := vs.push (.compilerOverrideAttribute target n "csimp" "declaration tagged @[csimp]")
  if let some (toDecl, thmName) := csimpIdx.fromToThm[n]? then
    vs := vs.push (.compilerOverrideAttribute target n "csimp_target"
      s!"replaced in compiled code by {toDecl} via @[csimp] {thmName}")
  -- Also detect `.opaqueInfo` whose `implemented_by` was not classified as partial.
  let _ := ci
  return vs

/-- Fuel-bounded (structurally total, zero `partial`) statement-origin separation walk
    over `ci.type` of `target`.
    Rejects any constant matching `policy.statementForbiddenRoots` (by module origin
    OR unmangled namespace prefix). Unfolds constants in `policy.statementUnfoldRoots`
    as well as any non-boundary local/helper definitions (stopping only at
    `policy.statementAllowedRoots` when not forbidden), catching leaks hidden inside
    `Specs.*`, `Mir.*`, reducible `abbrev` aliases, or typeclass instances. -/
def checkStatementOriginsInEnv (privEnv : Environment) (policy : AuditPolicy)
    (target : Name) (rootType : Expr) : Array AuditViolation := Id.run do
  match expressionEdges rootType with
  | .error msg =>
    return #[.openTermExpression target target s!"statement type: {msg}"]
  | .ok initEdges =>
    let kenv := privEnv.checked.get
    let initSorted := initEdges.toArray.qsort Name.lt
    let mut pending : Array (Name × Array Name) := #[]
    let mut seen : NameSet := {}
    let mut vs : Array AuditViolation := #[]
    for n in initSorted do
      seen := seen.insert n
      pending := pending.push (n, #[n])
    let modConstTotal := privEnv.header.moduleData.foldl (init := 0) fun acc d => acc + d.constants.size
    let fuel := max 200000 (modConstTotal * 2 + 8192)
    for _ in [:fuel] do
      if pending.isEmpty then
        break
      let (n, chain) := pending.back!
      pending := pending.pop
      let modName? := originModule? privEnv n
      let isForbidden := matchesAnyRoot n modName? policy.statementForbiddenRoots
      if isForbidden then
        vs := pushUniqueViolation vs (.statementOriginLeak target n modName? chain)
      let isAllowedBoundary :=
        !isForbidden &&
        match modName? with
        | some m => policy.statementAllowedRoots.any (matchesRootPrefix m ·)
        | none => false
      let shouldUnfold :=
        matchesAnyRoot n modName? policy.statementUnfoldRoots ||
        (!isAllowedBoundary && !isForbidden)
      if shouldUnfold then
        if let some depCi := kenv.find? n then
          let (depEdges, openVs) := declarationEdges target depCi
          vs := openVs.foldl pushUniqueViolation vs
          for d in depEdges.toArray.qsort Name.lt do
            if !seen.contains d then
              seen := seen.insert d
              pending := pending.push (d, chain.push d)
    if !pending.isEmpty then
      vs := pushUniqueViolation vs (.statementOriginLeak target target none #[`fuel_exhausted])
    return vs

/-- Audit a list of target declarations in a given `Environment` (pure total core,
    always inspecting `env.setExporting false` and `env.checked.get`).
    Uses an iterative, bounded $O(V + E)$ worklist (zero `partial`, zero `unsafe`,
    $O(1)$ call-stack space in the Lean interpreter) with per-edge root attribution. -/
def auditDeclsInEnvPure (env : Environment) (targets : Array Name)
    (policy : AuditPolicy := {}) : AuditVerdict := Id.run do
  let privEnv := env.setExporting false
  let kenv := privEnv.checked.get
  let csimpIdx := if policy.checkCompilerOverrides then buildCSimpIndex privEnv else {}
  let mut violations : Array AuditViolation := #[]
  let mut allAxioms : NameSet := {}
  let mut pending : Array (Name × Name) := #[]
  let mut visited : NameSet := {}
  let mut stmtSeen : NameSet := {}
  let modConstTotal := privEnv.header.moduleData.foldl (init := 0) fun acc d => acc + d.constants.size
  let fuel := max 250000 (modConstTotal * 2 + targets.size * 2 + 16384)
  for target in targets do
    match kenv.find? target with
    | none =>
      violations := pushUniqueViolation violations (.missingDeclaration target)
    | some rootCi =>
      if policy.requireTheoremKind && !rootCi.isTheorem then
        violations := pushUniqueViolation violations
          (.notTheoremKind target (constantInfoKind rootCi))
      if policy.checkStatementOrigin then
        match expressionEdges rootCi.type with
        | .error msg =>
          violations := pushUniqueViolation violations
            (.openTermExpression target target s!"statement type: {msg}")
        | .ok initEdges =>
          let sortedInit := initEdges.toArray.qsort Name.lt
          let mut pendingStmt : Array (Name × Array Name) := #[]
          let mut localStmtSeen : NameSet := stmtSeen
          let prevViolCount := violations.size
          for n in sortedInit do
            if !localStmtSeen.contains n then
              localStmtSeen := localStmtSeen.insert n
              pendingStmt := pendingStmt.push (n, #[n])
          for _ in [:fuel] do
            if pendingStmt.isEmpty then
              break
            let (n, chain) := pendingStmt.back!
            pendingStmt := pendingStmt.pop
            let modName? := originModule? privEnv n
            let isForbidden := matchesAnyRoot n modName? policy.statementForbiddenRoots
            if isForbidden then
              violations := pushUniqueViolation violations
                (.statementOriginLeak target n modName? chain)
            let isAllowedBoundary :=
              !isForbidden &&
              match modName? with
              | some m => policy.statementAllowedRoots.any (matchesRootPrefix m ·)
              | none => false
            let shouldUnfold :=
              matchesAnyRoot n modName? policy.statementUnfoldRoots ||
              (!isAllowedBoundary && !isForbidden)
            if shouldUnfold then
              if let some depCi := kenv.find? n then
                let (depEdges, openVs) := declarationEdges target depCi
                violations := openVs.foldl pushUniqueViolation violations
                for d in depEdges.toArray.qsort Name.lt do
                  if !localStmtSeen.contains d then
                    localStmtSeen := localStmtSeen.insert d
                    pendingStmt := pendingStmt.push (d, chain.push d)
          if !pendingStmt.isEmpty then
            violations := pushUniqueViolation violations
              (.statementOriginLeak target target none #[`fuel_exhausted])
          if violations.size == prevViolCount then
            stmtSeen := localStmtSeen
      if !visited.contains target then
        visited := visited.insert target
        pending := pending.push (target, target)
  -- Single iterative O(V + E) graph closure across all targets.
  for _ in [:fuel] do
    if pending.isEmpty then
      break
    let (rootTarget, n) := pending.back!
    pending := pending.pop
    match kenv.find? n with
    | none =>
      violations := pushUniqueViolation violations (.missingDeclaration n)
    | some ci =>
      let modName? := originModule? privEnv n
      if policy.forbidPartialAndUnsafe && ci.isUnsafe then
        violations := pushUniqueViolation violations (.unsafeDeclaration rootTarget n modName?)
      let partialReason? :=
        if policy.forbidPartialAndUnsafe then detectPartialOrUnsafeRec privEnv n ci
        else none
      if let some reason := partialReason? then
        violations := pushUniqueViolation violations
          (.partialOrUnsafeRecDependency rootTarget n modName? reason)
      if policy.checkCompilerOverrides then
        let ovs := checkCompilerOverridesOnDecl privEnv csimpIdx rootTarget n ci partialReason?.isSome
        violations := ovs.foldl pushUniqueViolation violations
      if ci.isAxiom then
        allAxioms := allAxioms.insert n
        if let some axViol := checkAxiomAllowed privEnv policy rootTarget n then
          violations := pushUniqueViolation violations axViol
      let (edges, openVs) := declarationEdges rootTarget ci
      violations := openVs.foldl pushUniqueViolation violations
      for d in edges.toArray.qsort Name.lt do
        if !visited.contains d then
          visited := visited.insert d
          pending := pending.push (rootTarget, d)
  if !pending.isEmpty then
    violations := pushUniqueViolation violations
      (.kernelReplayFailed "closure fuel exhausted during batch audit")
  -- Cross-check against `Lean.collectAxioms` in `env.setExporting false`.
  if policy.crossCheckCollectAxioms then
    if targets.size <= 32 then
      for target in targets do
        if (kenv.find? target).isSome then
          let collected := collectAxiomsPrivate privEnv target
          for ax in collected do
            allAxioms := allAxioms.insert ax
            if let some axViol := checkAxiomAllowed privEnv policy target ax then
              violations := pushUniqueViolation violations axViol
    else
      let batchAxs := collectAxiomsBatchPrivate privEnv targets
      let repTarget := targets[0]!
      for ax in batchAxs do
        allAxioms := allAxioms.insert ax
        if let some axViol := checkAxiomAllowed privEnv policy repTarget ax then
          violations := pushUniqueViolation violations axViol
      for idx in [0, targets.size - 1] do
        if h : idx < targets.size then
          let target := targets[idx]
          if (kenv.find? target).isSome then
            let collected := collectAxiomsPrivate privEnv target
            for ax in collected do
              allAxioms := allAxioms.insert ax
              if let some axViol := checkAxiomAllowed privEnv policy target ax then
                violations := pushUniqueViolation violations axViol
  let stats : AuditStats := {
    targetsAudited := targets.size
    reachableDeclarations := visited.size
    axiomsFound := allAxioms.toArray.qsort Name.lt
    modulesLoaded := privEnv.header.modules.size
  }
  if violations.isEmpty then
    return .ok stats
  else
    return .rejected violations stats

/-- Timed `IO` wrapper around `auditDeclsInEnvPure`. -/
def auditDeclsInEnvIO (env : Environment) (targets : Array Name)
    (policy : AuditPolicy := {}) : IO AuditVerdict := do
  let t0 ← IO.monoNanosNow
  let verdict := auditDeclsInEnvPure env targets policy
  let t1 ← IO.monoNanosNow
  let elapsedMicros := (t1 - t0) / 1000
  return match verdict with
    | .ok s => .ok { s with elapsedMicros }
    | .rejected vs s => .rejected vs { s with elapsedMicros }

/-- Timed `MetaM` wrapper auditing declarations in the current live `Environment`. -/
def auditDeclsInMetaM (targets : Array Name) (policy : AuditPolicy := {}) : MetaM AuditVerdict := do
  let env ← getEnv
  liftM <| auditDeclsInEnvIO env targets policy

/-- Check on-disk `.olean` and `.olean.private` artifact integrity across the
    module import closure starting from `rootModules`.
    For every Lean `v4.34.1` `module`-system `.olean` (`ModuleData.isModule = true`),
    verifies that the companion `.olean.private` exists when
    `policy.requirePrivateOleanForModuleSystem = true`. -/
def checkPrivateOleanArtifactsIO (rootModules : Array Name)
    (policy : AuditPolicy := {}) (checkToolchainMods : Bool := false) :
    IO (Array AuditViolation × Nat) := do
  let mut violations : Array AuditViolation := #[]
  let mut checkedCount : Nat := 0
  let mut pending : Array Name := rootModules
  let mut seen : NameSet := {}
  for m in rootModules do seen := seen.insert m
  let fuel : Nat := 10000
  for _ in [:fuel] do
    if pending.isEmpty then
      break
    let modName := pending.back!
    pending := pending.pop
    if !checkToolchainMods && (isStdlibMod modName || isLeanCompilerMod modName) &&
       !rootModules.contains modName then
      continue
    let oleanPath? ← try
      let p ← Lean.findOLean modName
      pure (some p)
    catch _ =>
      pure none
    match oleanPath? with
    | none =>
      violations := pushUniqueViolation violations
        (.missingPrivateArtifact modName s!"<olean not found on LEAN_PATH for {modName}>")
    | some oleanPath =>
      if !(← oleanPath.pathExists) then
        violations := pushUniqueViolation violations
          (.missingPrivateArtifact modName oleanPath.toString)
      else
        let (modData, _region) ← Lean.readModuleData oleanPath
        checkedCount := checkedCount + 1
        if modData.isModule && policy.requirePrivateOleanForModuleSystem then
          let privPath := OLeanLevel.private.adjustFileName oleanPath
          if !(← privPath.pathExists) then
            violations := pushUniqueViolation violations
              (.missingPrivateArtifact modName privPath.toString)
        for imp in modData.imports do
          if !seen.contains imp.module then
            seen := seen.insert imp.module
            pending := pending.push imp.module
  if !pending.isEmpty then
    violations := pushUniqueViolation violations (.kernelReplayFailed "artifact scan fuel exhausted")
  return (violations, checkedCount)

/-- Run a computation with `extraSearchPaths` temporarily prepended to `Lean.searchPathRef`,
    restoring the previous search path in `finally`. -/
def withExtraSearchPaths (extraSearchPaths : List System.FilePath) (act : IO α) : IO α := do
  if extraSearchPaths.isEmpty then
    act
  else
    let prev ← Lean.searchPathRef.get
    Lean.searchPathRef.set (extraSearchPaths ++ prev)
    try
      act
    finally
      Lean.searchPathRef.set prev

/-- End-to-end on-disk compiled `.olean` / `.olean.private` module auditor:
    1. Checks `.olean` / `.olean.private` presence via `checkPrivateOleanArtifactsIO`.
    2. Loads `rootModules` at `trustLevel := 0`, `loadExts := false`, `level := OLeanLevel.private`.
    3. Applies `env.setExporting false` so private constants and theorem proofs are visible.
    4. Selects `explicitTargets` (or all non-codegen-`_unsafe_rec` declarations—or all theorems
       when `theoremsOnly := true`—declared in `rootModules`).
    5. Audits all selected targets via `auditDeclsInEnvPure` (full `ConstantInfo` graph closure
       + `Lean.collectAxioms` cross-check + compiler overrides + statement-origin separation).
    6. Optionally replays target-module declarations in `baseEnv.toKernelEnv.replay`. -/
def auditCompiledModulesIO
    (rootModules : Array Name)
    (policy : AuditPolicy := {})
    (explicitTargets? : Option (Array Name) := none)
    (theoremsOnly : Bool := false)
    (extraSearchPaths : List System.FilePath := [])
    (runKernelReplay : Bool := false) : IO AuditVerdict := do
  let t0 ← IO.monoNanosNow
  withExtraSearchPaths extraSearchPaths do
    let (artifactViolations, privChecked) ← checkPrivateOleanArtifactsIO rootModules policy
    if !artifactViolations.isEmpty then
      let t1 ← IO.monoNanosNow
      return .rejected artifactViolations {
        privateArtifactsChecked := privChecked
        elapsedMicros := (t1 - t0) / 1000
      }
    let imports := rootModules.map fun m => ({ module := m } : Import)
    let env ← Lean.importModules imports {} (trustLevel := 0) (plugins := #[])
      (loadExts := false) (level := OLeanLevel.private)
    let privEnv := env.setExporting false
    let targets : Array Name := match explicitTargets? with
      | some ts => ts
      | none => Id.run do
        let mut acc : Array Name := #[]
        for m in privEnv.header.modules, data in privEnv.header.moduleData do
          if rootModules.contains m.module then
            for ci in data.constants do
              if !isCodegenUnsafeRec privEnv (some m.module) ci then
                if !theoremsOnly || ci.isTheorem then
                  acc := acc.push ci.name
        return acc
    let verdict := auditDeclsInEnvPure privEnv targets policy
    let mut violations := verdict.violations
    let mut replayedCount : Nat := 0
    if runKernelReplay && violations.isEmpty then
      let mut replayLocals : Std.HashMap Name ConstantInfo := {}
      let mut baseMods : Array Name := #[]
      for m in privEnv.header.modules, data in privEnv.header.moduleData do
        if rootModules.contains m.module then
          for ci in data.constants do
            if !isCodegenUnsafeRec privEnv (some m.module) ci then
              replayLocals := replayLocals.insert ci.name ci
        else
          baseMods := baseMods.push m.module
      try
        let baseEnv ← Lean.importModules (baseMods.map fun m => ({ module := m } : Import)) {}
          (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := OLeanLevel.private)
        let _ ← baseEnv.toKernelEnv.replay replayLocals
        replayedCount := replayLocals.size
      catch err =>
        violations := pushUniqueViolation violations (.kernelReplayFailed err.toString)
    let t1 ← IO.monoNanosNow
    let baseStats := verdict.stats
    let finalStats : AuditStats := {
      baseStats with
      privateArtifactsChecked := privChecked
      kernelReplayedDeclarations := replayedCount
      elapsedMicros := (t1 - t0) / 1000
    }
    if violations.isEmpty then
      return .ok finalStats
    else
      return .rejected violations finalStats

/-! ## Part 2: Constructive *DafnyCert*-Style Specification-Strength Mutant Harness -/

/-- Constructive specification-strength certificate (*DafnyCert*, `arXiv:2611.15548`)
    for a contract `(req, ens)`:
    - `req_nonvacuous` proves `req` is satisfiable by concrete input `x₀`.
    - `mutant_killed` proves there is a valid input `x₁` and buggy mutant output
      `y_mutant` that `ens x₁` constructively refutes. -/
structure SpecStrengthCert {In : Type u} {Out : Type v}
    (req : In → Prop) (ens : In → Out → Prop) : Type (max u v) where
  x₀ : In
  req_nonvacuous : req x₀
  x₁ : In
  mutant_req : req x₁
  y_mutant : Out
  mutant_killed : ¬ ens x₁ y_mutant

/-- Semantic category of a specification mutant (*Proving the Wrong Program*, `arXiv:2611.04701`). -/
inductive MutantCategory where
  | wrongReturn
  | offByOneScalar
  | swappedByteOrder
  | wrapOverflow
  | truncatedLength
  | wrongBranchTag
  | unpreservedFrame
  | custom (label : String)
  deriving DecidableEq, Repr, Inhabited

/-- A single named, categorized constructive mutant kill against `(req, ens)`. -/
structure NamedMutantKill {In : Type u} {Out : Type v}
    (req : In → Prop) (ens : In → Out → Prop) : Type (max u v) where
  name : String
  category : MutantCategory
  input : In
  input_valid : req input
  mutantOutput : Out
  killed : ¬ ens input mutantOutput

/-- Multi-mutant specification-strength certificate additionally certifying
    **realizability** (`ens x₀ y₀`, ruling out unsatisfiable `ens := False` contracts)
    and a non-empty categorized suite of constructive mutant kills. -/
structure MultiMutantSpecCert {In : Type u} {Out : Type v}
    (req : In → Prop) (ens : In → Out → Prop) : Type (max u v) where
  x₀ : In
  req_nonvacuous : req x₀
  y₀ : Out
  ens_realizable : ens x₀ y₀
  kills : List (NamedMutantKill req ens)
  kills_nonempty : kills ≠ []

/-- Extract a single-mutant `SpecStrengthCert` constructively from a `MultiMutantSpecCert`. -/
def MultiMutantSpecCert.toSpecStrengthCert {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (c : MultiMutantSpecCert req ens) : SpecStrengthCert req ens :=
  match h : c.kills with
  | [] => False.elim (c.kills_nonempty h)
  | k :: _ =>
    { x₀ := c.x₀
      req_nonvacuous := c.req_nonvacuous
      x₁ := k.input
      mutant_req := k.input_valid
      y_mutant := k.mutantOutput
      mutant_killed := k.killed }

/-- Categories killed by `c`. -/
def MultiMutantSpecCert.killedCategories {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (c : MultiMutantSpecCert req ens) : List MutantCategory :=
  c.kills.map (·.category)

/-- Number of constructive mutant kills recorded in `c`. -/
def MultiMutantSpecCert.killCount {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (c : MultiMutantSpecCert req ens) : Nat :=
  c.kills.length

/-- Decidable check whether `c` kills at least one mutant in `cat`. -/
def MultiMutantSpecCert.coversCategory {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (c : MultiMutantSpecCert req ens) (cat : MutantCategory) : Bool :=
  c.kills.any fun k => decide (k.category = cat)

/-- Decidable batch check whether `c` covers every category in `required`. -/
def MultiMutantSpecCert.coversAllCategories {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (c : MultiMutantSpecCert req ens) (required : List MutantCategory) : Bool :=
  required.all c.coversCategory

/-- Constructive soundness of `coversCategory`: returning `true` implies a concrete
    kill witness in `c.kills` with that category. -/
theorem MultiMutantSpecCert.covers_implies_exists_kill {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (c : MultiMutantSpecCert req ens) (cat : MutantCategory)
    (h : c.coversCategory cat = true) :
    ∃ k, k ∈ c.kills ∧ k.category = cat := by
  unfold MultiMutantSpecCert.coversCategory at h
  exact aux c.kills h
where
  aux : ∀ (ks : List (NamedMutantKill req ens)),
      ks.any (fun k => decide (k.category = cat)) = true →
      ∃ k, k ∈ ks ∧ k.category = cat
    | [], h => Bool.noConfusion h
    | k :: ks, h => by
      simp only [List.any_cons, Bool.or_eq_true] at h
      cases h with
      | inl hk =>
        exact ⟨k, List.Mem.head ks, of_decide_eq_true hk⟩
      | inr hks =>
        match aux ks hks with
        | ⟨k', hMem, hCat⟩ => exact ⟨k', List.Mem.tail k hMem, hCat⟩

/-! ### Constructive Metatheorems (Zero `Classical.choice`, Zero `sorryAx`) -/

/-- A vacuous `requires := False` specification can never admit a `SpecStrengthCert`. -/
theorem no_cert_of_vacuous_req {In : Type u} {Out : Type v}
    (ens : In → Out → Prop) :
    SpecStrengthCert (fun (_ : In) => False) ens → False :=
  fun c => c.req_nonvacuous

/-- Any unsatisfiable precondition `∀ x, ¬ req x` can never admit a `SpecStrengthCert`. -/
theorem no_cert_of_unsatisfiable_req {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (hUnsat : ∀ x : In, ¬ req x) :
    SpecStrengthCert req ens → False :=
  fun c => hUnsat c.x₀ c.req_nonvacuous

/-- A trivial `ensures := True` specification can never admit a `SpecStrengthCert`. -/
theorem no_cert_of_trivial_ens {In : Type u} {Out : Type v}
    (req : In → Prop) :
    SpecStrengthCert req (fun (_ : In) (_ : Out) => True) → False :=
  fun c => c.mutant_killed trivial

/-- Any universally satisfied postcondition (`∀ x y, req x → ens x y`) can never admit
    a `SpecStrengthCert`. -/
theorem no_cert_of_universal_ens {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (hUniv : ∀ x y, req x → ens x y) :
    SpecStrengthCert req ens → False :=
  fun c => c.mutant_killed (hUniv c.x₁ c.y_mutant c.mutant_req)

/-- An unsatisfiable postcondition (`∀ x y, req x → ¬ ens x y`, including `ens := False`)
    can never admit a `MultiMutantSpecCert` (realizability gate). -/
theorem no_multi_cert_of_unsatisfiable_ens {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (hUnsat : ∀ x y, req x → ¬ ens x y) :
    MultiMutantSpecCert req ens → False :=
  fun c => hUnsat c.x₀ c.y₀ c.req_nonvacuous c.ens_realizable

/-- Any implementation exhibiting the certified mutant output on `c.x₁` is provably
    rejected by the specification `(req, ens)`. -/
theorem mutant_impl_rejected_by_spec {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (f_mut : In → Out)
    (c : SpecStrengthCert req ens)
    (hMut : f_mut c.x₁ = c.y_mutant) :
    ¬ (∀ x, req x → ens x (f_mut x)) :=
  fun hSpec => c.mutant_killed (hMut ▸ hSpec c.x₁ c.mutant_req)

/-- Any implementation matching any kill in a `MultiMutantSpecCert` is provably
    rejected by the specification `(req, ens)`. -/
theorem multi_mutant_impl_rejected_by_spec {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (f_mut : In → Out)
    (c : MultiMutantSpecCert req ens)
    (k : NamedMutantKill req ens)
    (_hk : k ∈ c.kills)
    (hMut : f_mut k.input = k.mutantOutput) :
    ¬ (∀ x, req x → ens x (f_mut x)) :=
  fun hSpec => k.killed (hMut ▸ hSpec k.input k.input_valid)

/-- Bridging metatheorem to `Trusted.VerificationResult.ItemSpec`: an `ItemSpec`
    that leaves `post` at its default (`fun _ _ => True`) can never admit a
    `SpecStrengthCert`. -/
theorem no_itemSpec_cert_of_default_post (defId : String)
    (pre : List Value → Prop) :
    letI : ItemSpec defId := { pre := pre }
    SpecStrengthCert (ItemSpec.pre (defId := defId)) (ItemSpec.post (defId := defId)) → False :=
  fun c => c.mutant_killed trivial

/-- Bridging metatheorem to `Trusted.VerificationResult.StatefulItemSpec`: leaving
    `post` at its default (`fun _ _ _ _ => True`) can never admit a `SpecStrengthCert`. -/
theorem no_statefulItemSpec_cert_of_default_post (defId : String)
    (pre : List Value → Memory → Prop) :
    letI : StatefulItemSpec defId := { pre := pre }
    SpecStrengthCert
      (fun (p : List Value × Memory) => StatefulItemSpec.pre (defId := defId) p.1 p.2)
      (fun (p : List Value × Memory) (r : Value × Memory) =>
        StatefulItemSpec.post (defId := defId) p.1 p.2 r.1 r.2) → False :=
  fun c => c.mutant_killed trivial

/-! ### Typeclass Bridges to `Trusted.VerificationResult` -/

/-- Typeclass certifying single-mutant specification strength for `ItemSpec defId`. -/
class ItemSpecStrengthCert (defId : String) [s : ItemSpec defId] : Type where
  cert : SpecStrengthCert s.pre s.post

/-- Typeclass certifying multi-mutant specification strength + realizability for `ItemSpec defId`. -/
class ItemMultiMutantCert (defId : String) [s : ItemSpec defId] : Type where
  cert : MultiMutantSpecCert s.pre s.post

/-- Typeclass certifying single-mutant specification strength for `StatefulItemSpec defId`. -/
class StatefulItemSpecStrengthCert (defId : String) [s : StatefulItemSpec defId] : Type where
  cert : SpecStrengthCert
    (fun (p : List Value × Memory) => s.pre p.1 p.2)
    (fun (p : List Value × Memory) (r : Value × Memory) => s.post p.1 p.2 r.1 r.2)

/-- Typeclass certifying multi-mutant specification strength + realizability for `StatefulItemSpec defId`. -/
class StatefulItemMultiMutantCert (defId : String) [s : StatefulItemSpec defId] : Type where
  cert : MultiMutantSpecCert
    (fun (p : List Value × Memory) => s.pre p.1 p.2)
    (fun (p : List Value × Memory) (r : Value × Memory) => s.post p.1 p.2 r.1 r.2)

/-- Typeclass certifying specification strength for `ModularItemSpec defId`, including
    a constructive witness that `s.envAssumed` is itself non-vacuous. -/
class ModularItemSpecStrengthCert (defId : String) [s : ModularItemSpec defId] : Type where
  handler : ExternalCallHandler
  handler_valid : s.envAssumed handler
  cert : SpecStrengthCert
    (fun (p : List Value × Memory) => s.pre p.1 p.2)
    (fun (p : List Value × Memory) (r : Value × Memory) => s.post p.1 p.2 r.1 r.2)

/-- Typeclass certifying multi-mutant specification strength + non-vacuous rely handler
    for `ModularItemSpec defId`. -/
class ModularItemMultiMutantCert (defId : String) [s : ModularItemSpec defId] : Type where
  handler : ExternalCallHandler
  handler_valid : s.envAssumed handler
  cert : MultiMutantSpecCert
    (fun (p : List Value × Memory) => s.pre p.1 p.2)
    (fun (p : List Value × Memory) (r : Value × Memory) => s.post p.1 p.2 r.1 r.2)

/-- A `ModularItemSpec` with vacuous rely predicate `envAssumed := fun _ => False`
    can never admit a `ModularItemSpecStrengthCert`. -/
theorem no_modularItemSpec_cert_of_vacuous_envAssumed (defId : String)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) :
    letI : ModularItemSpec defId := { envAssumed := fun _ => False, pre := pre, post := post }
    ModularItemSpecStrengthCert defId → False :=
  fun c => c.handler_valid

/-! ### `MetaM` Spec-Strength Gate (`auditSpecStrengthCertInEnv`) -/

private def recognisedCertHeads : Array Name := #[
  ``SpecStrengthCert,
  ``MultiMutantSpecCert,
  ``ItemSpecStrengthCert,
  ``ItemMultiMutantCert,
  ``StatefulItemSpecStrengthCert,
  ``StatefulItemMultiMutantCert,
  ``ModularItemSpecStrengthCert,
  ``ModularItemMultiMutantCert
]

/-- `MetaM` specification-strength gate verifying that:
    1. A registered `SpecStrengthCert` / `MultiMutantSpecCert` (or `*Item*Cert`)
       declaration `certDecl` exists in the environment;
    2. Its kernel type reduces via `whnf` to a recognised certificate constructor
       matching `expectedReq?` / `expectedEns?` (when supplied) via `Meta.isDefEq`
       (preventing certificate substitution from an unrelated strong specification);
    3. The certificate declaration itself passes the `MetaM` environment audit under
       `policy` (default `AuditPolicy.constructive`, preventing `sorry`-faked,
       `Classical.choice`-tainted, `partial`, `unsafe`, or `@[implemented_by]` certs). -/
def auditSpecStrengthCertInEnv
    (specName : Name)
    (certDecl? : Option Name)
    (expectedReq? : Option Expr := none)
    (expectedEns? : Option Expr := none)
    (policy : AuditPolicy := { AuditPolicy.constructive with checkStatementOrigin := false }) :
    MetaM AuditVerdict := do
  let t0 ← IO.monoNanosNow
  match certDecl? with
  | none =>
    let t1 ← IO.monoNanosNow
    return .rejected
      #[.specStrengthCertMissing specName "no registered SpecStrengthCert or MultiMutantSpecCert declaration"]
      { elapsedMicros := (t1 - t0) / 1000 }
  | some certDecl =>
    let env ← getEnv
    let privEnv := env.setExporting false
    match privEnv.checked.get.find? certDecl with
    | none =>
      let t1 ← IO.monoNanosNow
      return .rejected #[.missingDeclaration certDecl] { elapsedMicros := (t1 - t0) / 1000 }
    | some ci =>
      let ty ← Meta.whnf ci.type
      let fn := ty.getAppFn
      let args := ty.getAppArgs
      let headOk := match fn with
        | .const n _ => recognisedCertHeads.contains n
        | _ => false
      if !headOk then
        let tyStr := toString (← Meta.ppExpr ty)
        let t1 ← IO.monoNanosNow
        return .rejected
          #[.specStrengthCertInvalidType certDecl specName s!"not a SpecStrengthCert type: {tyStr}"]
          { elapsedMicros := (t1 - t0) / 1000 }
      -- When `expectedReq?` / `expectedEns?` are provided, verify definitional match on
      -- `SpecStrengthCert` / `MultiMutantSpecCert` arguments `[In, Out, req, ens]`.
      let isDirectCert := fn.isConstOf ``SpecStrengthCert || fn.isConstOf ``MultiMutantSpecCert
      if isDirectCert && args.size >= 4 then
        if let some expReq := expectedReq? then
          unless (← Meta.isDefEq args[2]! expReq) do
            let tyStr := toString (← Meta.ppExpr ty)
            let t1 ← IO.monoNanosNow
            return .rejected
              #[.specStrengthCertInvalidType certDecl specName s!"precondition mismatch: {tyStr}"]
              { elapsedMicros := (t1 - t0) / 1000 }
        if let some expEns := expectedEns? then
          unless (← Meta.isDefEq args[3]! expEns) do
            let tyStr := toString (← Meta.ppExpr ty)
            let t1 ← IO.monoNanosNow
            return .rejected
              #[.specStrengthCertInvalidType certDecl specName s!"postcondition mismatch: {tyStr}"]
              { elapsedMicros := (t1 - t0) / 1000 }
      else if expectedReq?.isSome || expectedEns?.isSome then
        let tyStr := toString (← Meta.ppExpr ty)
        let t1 ← IO.monoNanosNow
        return .rejected
          #[.specStrengthCertInvalidType certDecl specName s!"expected direct SpecStrengthCert/MultiMutantSpecCert, got {tyStr}"]
          { elapsedMicros := (t1 - t0) / 1000 }
      -- Audit the certificate declaration itself so `sorry`-faked or unsound certs are rejected.
      let envVerdict ← liftM <| auditDeclsInEnvIO privEnv #[certDecl] policy
      let t1 ← IO.monoNanosNow
      let elapsedMicros := (t1 - t0) / 1000
      return match envVerdict with
        | .ok s => .ok { s with elapsedMicros }
        | .rejected vs s => .rejected vs { s with elapsedMicros }

/-- `MetaM` gate using typeclass synthesis to locate an `ItemSpecStrengthCert` (or
    `ItemMultiMutantCert`) for `ItemSpec defId`, rejecting fail-closed if none is
    registered or if any constant in the synthesized witness fails the environment audit. -/
def auditItemSpecStrengthBySynth (defId : String)
    (policy : AuditPolicy := { AuditPolicy.constructive with checkStatementOrigin := false }) :
    MetaM AuditVerdict := do
  let t0 ← IO.monoNanosNow
  let specName := Name.mkSimple defId
  let defIdExpr := mkStrLit defId
  let itemSpecTy := mkApp (mkConst ``ItemSpec) defIdExpr
  let some itemSpecInst ← Meta.synthInstance? itemSpecTy
    | do
      let t1 ← IO.monoNanosNow
      return .rejected
        #[.specStrengthCertMissing specName s!"no ItemSpec instance found for \"{defId}\""]
        { elapsedMicros := (t1 - t0) / 1000 }
  let singleCertTy := mkApp2 (mkConst ``ItemSpecStrengthCert) defIdExpr itemSpecInst
  let multiCertTy := mkApp2 (mkConst ``ItemMultiMutantCert) defIdExpr itemSpecInst
  let certInst? ← match (← Meta.synthInstance? multiCertTy) with
    | some inst => pure (some inst)
    | none => Meta.synthInstance? singleCertTy
  match certInst? with
  | none =>
    let t1 ← IO.monoNanosNow
    return .rejected
      #[.specStrengthCertMissing specName s!"no ItemSpecStrengthCert or ItemMultiMutantCert instance found for \"{defId}\""]
      { elapsedMicros := (t1 - t0) / 1000 }
  | some certInst =>
    match expressionEdges certInst with
    | .error msg =>
      let t1 ← IO.monoNanosNow
      return .rejected
        #[.openTermExpression specName specName s!"synthesized cert instance: {msg}"]
        { elapsedMicros := (t1 - t0) / 1000 }
    | .ok constSet =>
      let env ← getEnv
      let privEnv := env.setExporting false
      let targets := constSet.toArray.qsort Name.lt
      let envVerdict ← liftM <| auditDeclsInEnvIO privEnv targets policy
      let t1 ← IO.monoNanosNow
      let elapsedMicros := (t1 - t0) / 1000
      return match envVerdict with
        | .ok s => .ok { s with elapsedMicros }
        | .rejected vs s => .rejected vs { s with elapsedMicros }

/-! ## Part 3: Representative Constructive `MultiMutantSpecCert` Examples -/

/-! ### Example 1: `fxfs_storage_boundary::vmo_subslice_bounds_valid` -/

/-- Exact precondition modeled on `fxfs_storage_boundary::vmo_subslice_bounds_valid`:
    `sub_start ≤ sub_end ≤ buf_len` and `base_offset + buf_len < 2^64`. -/
def fxfsVmoSubslicePre (args : List Value) : Prop :=
  ∃ (base len s e : Nat),
    s ≤ e ∧
    e ≤ len ∧
    base + len < 18446744073709551616 ∧
    args =
      [ .scalar { bits := base, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := s, sizeBytes := 8 }
      , .scalar { bits := e, sizeBytes := 8 } ]

/-- Exact postcondition modeled on `fxfs_storage_boundary::vmo_subslice_bounds_valid`:
    `ret = base_offset + (sub_end - sub_start)` as an 8-byte scalar. -/
def fxfsVmoSubslicePost (args : List Value) (ret : Value) : Prop :=
  ∀ (base len s e : Nat),
    args =
      [ .scalar { bits := base, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := s, sizeBytes := 8 }
      , .scalar { bits := e, sizeBytes := 8 } ] →
    ret = .scalar { bits := base + (e - s), sizeBytes := 8 }

/-- `ItemSpec` bridge instance for `fxfs_storage_boundary::vmo_subslice_bounds_valid`. -/
instance fxfsVmoSubsliceItemSpec :
    ItemSpec "fxfs_storage_boundary::vmo_subslice_bounds_valid" where
  pre := fxfsVmoSubslicePre
  post := fxfsVmoSubslicePost

/-- Constructive `MultiMutantSpecCert` for `fxfs_storage_boundary::vmo_subslice_bounds_valid`,
    certifying realizability and killing `wrongReturn`, `wrapOverflow`, `truncatedLength`,
    and `swappedByteOrder` mutants with zero `Classical.choice` and zero `sorryAx`. -/
def fxfsVmoSubsliceMultiCert :
    MultiMutantSpecCert fxfsVmoSubslicePre fxfsVmoSubslicePost where
  x₀ :=
    [ .scalar { bits := 4096, sizeBytes := 8 }
    , .scalar { bits := 4096, sizeBytes := 8 }
    , .scalar { bits := 64, sizeBytes := 8 }
    , .scalar { bits := 192, sizeBytes := 8 } ]
  req_nonvacuous := ⟨4096, 4096, 64, 192, by decide, by decide, by decide, rfl⟩
  y₀ := .scalar { bits := 4224, sizeBytes := 8 }
  ens_realizable := by
    intro base len s e h
    injection h with h1 hRest1
    injection h1 with h1s
    injection h1s with hBase _
    injection hRest1 with h2 hRest2
    injection h2 with h2s
    injection h2s with hLen _
    injection hRest2 with h3 hRest3
    injection h3 with h3s
    injection h3s with hS _
    injection hRest3 with h4 _
    injection h4 with h4s
    injection h4s with hE _
    subst hBase; subst hLen; subst hS; subst hE
    rfl
  kills :=
    [ { name := "fxfs_wrong_return_zero"
        category := .wrongReturn
        input :=
          [ .scalar { bits := 4096, sizeBytes := 8 }
          , .scalar { bits := 4096, sizeBytes := 8 }
          , .scalar { bits := 64, sizeBytes := 8 }
          , .scalar { bits := 192, sizeBytes := 8 } ]
        input_valid := ⟨4096, 4096, 64, 192, by decide, by decide, by decide, rfl⟩
        mutantOutput := .scalar { bits := 0, sizeBytes := 8 }
        killed := by
          intro h
          have hEq := h 4096 4096 64 192 rfl
          injection hEq with hS
          injection hS with hBits _
          exact Nat.noConfusion hBits }
    , { name := "fxfs_wrap_overflow_32bit_trunc"
        category := .wrapOverflow
        input :=
          [ .scalar { bits := 4294967288, sizeBytes := 8 }
          , .scalar { bits := 32, sizeBytes := 8 }
          , .scalar { bits := 0, sizeBytes := 8 }
          , .scalar { bits := 16, sizeBytes := 8 } ]
        input_valid := ⟨4294967288, 32, 0, 16, by decide, by decide, by decide, rfl⟩
        -- Mutant wraps `(0xFFFF_FFF8 + 16)` modulo `2^32` to `8`.
        mutantOutput := .scalar { bits := 8, sizeBytes := 8 }
        killed := by
          intro h
          have hEq := h 4294967288 32 0 16 rfl
          injection hEq with hS
          injection hS with hBits _
          exact absurd hBits (by decide) }
    , { name := "fxfs_truncated_length_drops_delta"
        category := .truncatedLength
        input :=
          [ .scalar { bits := 4096, sizeBytes := 8 }
          , .scalar { bits := 4096, sizeBytes := 8 }
          , .scalar { bits := 64, sizeBytes := 8 }
          , .scalar { bits := 192, sizeBytes := 8 } ]
        input_valid := ⟨4096, 4096, 64, 192, by decide, by decide, by decide, rfl⟩
        -- Mutant omits `(sub_end - sub_start)` and returns bare `base_offset`.
        mutantOutput := .scalar { bits := 4096, sizeBytes := 8 }
        killed := by
          intro h
          have hEq := h 4096 4096 64 192 rfl
          injection hEq with hS
          injection hS with hBits _
          exact absurd hBits (by decide) }
    , { name := "fxfs_swapped_byte_order_be64"
        category := .swappedByteOrder
        input :=
          [ .scalar { bits := 0x0102, sizeBytes := 8 }
          , .scalar { bits := 0x0400, sizeBytes := 8 }
          , .scalar { bits := 0, sizeBytes := 8 }
          , .scalar { bits := 0x0010, sizeBytes := 8 } ]
        input_valid := ⟨0x0102, 0x0400, 0, 0x0010, by decide, by decide, by decide, rfl⟩
        -- Expected `0x0112`; mutant returns byte-swapped `0x1201`.
        mutantOutput := .scalar { bits := 0x1201, sizeBytes := 8 }
        killed := by
          intro h
          have hEq := h 0x0102 0x0400 0 0x0010 rfl
          injection hEq with hS
          injection hS with hBits _
          exact absurd hBits (by decide) }
    ]
  kills_nonempty := by intro h; cases h

instance fxfsVmoSubsliceItemMultiCert :
    ItemMultiMutantCert "fxfs_storage_boundary::vmo_subslice_bounds_valid" where
  cert := fxfsVmoSubsliceMultiCert

instance fxfsVmoSubsliceItemSingleCert :
    ItemSpecStrengthCert "fxfs_storage_boundary::vmo_subslice_bounds_valid" where
  cert := fxfsVmoSubsliceMultiCert.toSpecStrengthCert

/-- Proof that `fxfsVmoSubsliceMultiCert` covers all 4 required storage-boundary mutant categories. -/
theorem fxfsVmoSubslice_covers_required_categories :
    fxfsVmoSubsliceMultiCert.coversAllCategories
      [.wrongReturn, .wrapOverflow, .truncatedLength, .swappedByteOrder] = true := rfl

/-! ### Example 2: `fuchsia_usercopy::usercopy_copyin_bracketed` -/

/-- Precondition modeled on `fuchsia_usercopy::usercopy_copyin_bracketed`. -/
def fuchsiaUsercopyCopyinPre (args : List Value) (mem : Memory) : Prop :=
  ∃ (in_range dest_len fo v : Nat),
    (in_range = 0 ∨ in_range = 1) ∧
    fo ≤ dest_len ∧
    dest_len < 18446744073709551616 ∧
    (v = 0 ∨ v = 1) ∧
    args =
      [ .scalar { bits := in_range, sizeBytes := 1 }
      , .scalar { bits := dest_len, sizeBytes := 8 }
      , .scalar { bits := fo, sizeBytes := 8 }
      , .scalar { bits := v, sizeBytes := 1 } ] ∧
    mem = emptyMemory

/-- Postcondition modeled on `fuchsia_usercopy::usercopy_copyin_bracketed`:
    preserves `mem' = mem` and returns `(fault_offset, dest_len - fault_offset)` when
    `source_in_restricted_range = 1` or `(0, dest_len)` when `0`. -/
def fuchsiaUsercopyCopyinPost (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=
  mem' = mem ∧
  ∀ (in_range dest_len fo v : Nat),
    args =
      [ .scalar { bits := in_range, sizeBytes := 1 }
      , .scalar { bits := dest_len, sizeBytes := 8 }
      , .scalar { bits := fo, sizeBytes := 8 }
      , .scalar { bits := v, sizeBytes := 1 } ] →
    if in_range = 1 then
      ret = .aggregate 0
        [ .scalar { bits := fo, sizeBytes := 8 }
        , .scalar { bits := dest_len - fo, sizeBytes := 8 } ]
    else
      ret = .aggregate 0
        [ .scalar { bits := 0, sizeBytes := 8 }
        , .scalar { bits := dest_len, sizeBytes := 8 } ]

/-- Constructive rely predicate for the bracketed `hermetic_copy_stub` external call. -/
def fuchsiaHermeticCopyRely (h : ExternalCallHandler) : Prop :=
  ∀ (count fo v : Nat) (mem : Memory),
    fo ≤ count →
    h { defPath := "fuchsia_usercopy::hermetic_copy_stub"
        args :=
          [ .scalar { bits := count, sizeBytes := 8 }
          , .scalar { bits := fo, sizeBytes := 8 }
          , .scalar { bits := v, sizeBytes := 1 } ]
        memory := mem } =
      ITree.ret (.returned (.scalar { bits := fo, sizeBytes := 8 }) mem)

/-- Constructive external-call handler witnessing non-vacuity of `fuchsiaHermeticCopyRely`. -/
def fuchsiaHermeticCopyWitnessHandler : ExternalCallHandler := fun req =>
  match req.args with
  | [ _, .scalar foScalar, _ ] => ITree.ret (.returned (.scalar foScalar) req.memory)
  | _ => ITree.ret (.returned (.scalar { bits := 0, sizeBytes := 8 }) req.memory)

theorem fuchsiaHermeticCopyWitnessHandler_valid :
    fuchsiaHermeticCopyRely fuchsiaHermeticCopyWitnessHandler := by
  intro _count _fo _v _mem _hLe
  rfl

/-- `StatefulItemSpec` bridge instance for `fuchsia_usercopy::usercopy_copyin_bracketed`. -/
instance fuchsiaUsercopyCopyinStatefulSpec :
    StatefulItemSpec "fuchsia_usercopy::usercopy_copyin_bracketed" where
  pre := fuchsiaUsercopyCopyinPre
  post := fuchsiaUsercopyCopyinPost

/-- `ModularItemSpec` bridge instance for `fuchsia_usercopy::usercopy_copyin_bracketed`. -/
instance fuchsiaUsercopyCopyinModularSpec :
    ModularItemSpec "fuchsia_usercopy::usercopy_copyin_bracketed" where
  envAssumed := fuchsiaHermeticCopyRely
  pre := fuchsiaUsercopyCopyinPre
  post := fuchsiaUsercopyCopyinPost

/-- Mutated memory state simulating a frame-corruption mutant (`nextAllocId` bumped). -/
def mutatedFrameMemory : Memory :=
  { emptyMemory with nextAllocId := 1 }

/-- Constructive `MultiMutantSpecCert` for `fuchsia_usercopy::usercopy_copyin_bracketed`,
    certifying realizability and killing `wrongBranchTag`, `truncatedLength`,
    `offByOneScalar`, and `unpreservedFrame` mutants with zero `Classical.choice`. -/
def fuchsiaUsercopyCopyinMultiCert :
    MultiMutantSpecCert
      (fun (p : List Value × Memory) => fuchsiaUsercopyCopyinPre p.1 p.2)
      (fun (p : List Value × Memory) (r : Value × Memory) =>
        fuchsiaUsercopyCopyinPost p.1 p.2 r.1 r.2) where
  x₀ :=
    ( [ .scalar { bits := 1, sizeBytes := 1 }
      , .scalar { bits := 256, sizeBytes := 8 }
      , .scalar { bits := 64, sizeBytes := 8 }
      , .scalar { bits := 1, sizeBytes := 1 } ]
    , emptyMemory )
  req_nonvacuous := ⟨1, 256, 64, 1, Or.inr rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
  y₀ :=
    ( .aggregate 0
        [ .scalar { bits := 64, sizeBytes := 8 }
        , .scalar { bits := 192, sizeBytes := 8 } ]
    , emptyMemory )
  ens_realizable := by
    refine ⟨rfl, ?_⟩
    intro in_range dest_len fo v h
    injection h with h1 hRest1
    injection h1 with h1s; injection h1s with hIR _
    injection hRest1 with h2 hRest2
    injection h2 with h2s; injection h2s with hDL _
    injection hRest2 with h3 hRest3
    injection h3 with h3s; injection h3s with hFO _
    injection hRest3 with h4 _
    injection h4 with h4s; injection h4s with hV _
    subst hIR; subst hDL; subst hFO; subst hV
    rfl
  kills :=
    [ { name := "usercopy_wrong_branch_tag_ignores_in_range"
        category := .wrongBranchTag
        input :=
          ( [ .scalar { bits := 1, sizeBytes := 1 }
            , .scalar { bits := 256, sizeBytes := 8 }
            , .scalar { bits := 64, sizeBytes := 8 }
            , .scalar { bits := 1, sizeBytes := 1 } ]
          , emptyMemory )
        input_valid := ⟨1, 256, 64, 1, Or.inr rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
        -- Mutant takes the `in_range = 0` branch and returns `(0, 256)`.
        mutantOutput :=
          ( .aggregate 0
              [ .scalar { bits := 0, sizeBytes := 8 }
              , .scalar { bits := 256, sizeBytes := 8 } ]
          , emptyMemory )
        killed := by
          intro h
          have hVal := h.2 1 256 64 1 rfl
          simp only [ite_true] at hVal
          injection hVal with _ hFields
          injection hFields with hF0 _
          injection hF0 with hS
          injection hS with hBits _
          exact Nat.noConfusion hBits }
    , { name := "usercopy_truncated_uninit_length"
        category := .truncatedLength
        input :=
          ( [ .scalar { bits := 1, sizeBytes := 1 }
            , .scalar { bits := 256, sizeBytes := 8 }
            , .scalar { bits := 64, sizeBytes := 8 }
            , .scalar { bits := 1, sizeBytes := 1 } ]
          , emptyMemory )
        input_valid := ⟨1, 256, 64, 1, Or.inr rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
        -- Mutant drops `uninit_len` to `0`, returning `(64, 0)` instead of `(64, 192)`.
        mutantOutput :=
          ( .aggregate 0
              [ .scalar { bits := 64, sizeBytes := 8 }
              , .scalar { bits := 0, sizeBytes := 8 } ]
          , emptyMemory )
        killed := by
          intro h
          have hVal := h.2 1 256 64 1 rfl
          simp only [ite_true] at hVal
          injection hVal with _ hFields
          injection hFields with _ hRest
          injection hRest with hF1 _
          injection hF1 with hS
          injection hS with hBits _
          exact Nat.noConfusion hBits }
    , { name := "usercopy_off_by_one_fault_offset"
        category := .offByOneScalar
        input :=
          ( [ .scalar { bits := 1, sizeBytes := 1 }
            , .scalar { bits := 256, sizeBytes := 8 }
            , .scalar { bits := 64, sizeBytes := 8 }
            , .scalar { bits := 1, sizeBytes := 1 } ]
          , emptyMemory )
        input_valid := ⟨1, 256, 64, 1, Or.inr rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
        -- Mutant returns `(65, 191)` (off-by-one `fault_offset + 1`).
        mutantOutput :=
          ( .aggregate 0
              [ .scalar { bits := 65, sizeBytes := 8 }
              , .scalar { bits := 191, sizeBytes := 8 } ]
          , emptyMemory )
        killed := by
          intro h
          have hVal := h.2 1 256 64 1 rfl
          simp only [ite_true] at hVal
          injection hVal with _ hFields
          injection hFields with hF0 _
          injection hF0 with hS
          injection hS with hBits _
          exact absurd hBits (by decide) }
    , { name := "usercopy_unpreserved_frame_memory"
        category := .unpreservedFrame
        input :=
          ( [ .scalar { bits := 0, sizeBytes := 1 }
            , .scalar { bits := 256, sizeBytes := 8 }
            , .scalar { bits := 0, sizeBytes := 8 }
            , .scalar { bits := 1, sizeBytes := 1 } ]
          , emptyMemory )
        input_valid := ⟨0, 256, 0, 1, Or.inl rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
        -- Mutant returns the right tuple `(0, 256)` but corrupts output memory frame.
        mutantOutput :=
          ( .aggregate 0
              [ .scalar { bits := 0, sizeBytes := 8 }
              , .scalar { bits := 256, sizeBytes := 8 } ]
          , mutatedFrameMemory )
        killed := by
          intro h
          have hMem : mutatedFrameMemory = emptyMemory := h.1
          have hAlloc : (1 : Nat) = 0 := congrArg (fun m => m.nextAllocId) hMem
          exact Nat.noConfusion hAlloc }
    ]
  kills_nonempty := by intro h; cases h

instance fuchsiaUsercopyCopyinStatefulMultiCert :
    StatefulItemMultiMutantCert "fuchsia_usercopy::usercopy_copyin_bracketed" where
  cert := fuchsiaUsercopyCopyinMultiCert

instance fuchsiaUsercopyCopyinStatefulSingleCert :
    StatefulItemSpecStrengthCert "fuchsia_usercopy::usercopy_copyin_bracketed" where
  cert := fuchsiaUsercopyCopyinMultiCert.toSpecStrengthCert

instance fuchsiaUsercopyCopyinModularMultiCert :
    ModularItemMultiMutantCert "fuchsia_usercopy::usercopy_copyin_bracketed" where
  handler := fuchsiaHermeticCopyWitnessHandler
  handler_valid := fuchsiaHermeticCopyWitnessHandler_valid
  cert := fuchsiaUsercopyCopyinMultiCert

instance fuchsiaUsercopyCopyinModularSingleCert :
    ModularItemSpecStrengthCert "fuchsia_usercopy::usercopy_copyin_bracketed" where
  handler := fuchsiaHermeticCopyWitnessHandler
  handler_valid := fuchsiaHermeticCopyWitnessHandler_valid
  cert := fuchsiaUsercopyCopyinMultiCert.toSpecStrengthCert

/-- Proof that `fuchsiaUsercopyCopyinMultiCert` covers all 4 required usercopy mutant categories. -/
theorem fuchsiaUsercopyCopyin_covers_required_categories :
    fuchsiaUsercopyCopyinMultiCert.coversAllCategories
      [.wrongBranchTag, .truncatedLength, .offByOneScalar, .unpreservedFrame] = true := rfl

/-! ### Diagnostic Contrast: Weak Upper-Bound-Only Spec (`weak_vmo_subslice_upper_bound_only`) -/

/-- Under-specified postcondition that only checks `ret ≤ base + len` (upper bound only),
    forgetting the exact subslice length `base + (e - s)`. -/
def weak_vmo_subslice_upper_bound_only (args : List Value) (ret : Value) : Prop :=
  ∀ (base len s e : Nat),
    args =
      [ .scalar { bits := base, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := s, sizeBytes := 8 }
      , .scalar { bits := e, sizeBytes := 8 } ] →
    ∃ r, ret = .scalar { bits := r, sizeBytes := 8 } ∧ r ≤ base + len

/-- A single-mutant harness PASSES `weak_vmo_subslice_upper_bound_only` by killing an
    out-of-bounds return `base + len + 1`... -/
def weakVmoSubsliceSingleCert :
    SpecStrengthCert fxfsVmoSubslicePre weak_vmo_subslice_upper_bound_only where
  x₀ :=
    [ .scalar { bits := 4096, sizeBytes := 8 }
    , .scalar { bits := 4096, sizeBytes := 8 }
    , .scalar { bits := 64, sizeBytes := 8 }
    , .scalar { bits := 192, sizeBytes := 8 } ]
  req_nonvacuous := ⟨4096, 4096, 64, 192, by decide, by decide, by decide, rfl⟩
  x₁ :=
    [ .scalar { bits := 4096, sizeBytes := 8 }
    , .scalar { bits := 4096, sizeBytes := 8 }
    , .scalar { bits := 64, sizeBytes := 8 }
    , .scalar { bits := 192, sizeBytes := 8 } ]
  mutant_req := ⟨4096, 4096, 64, 192, by decide, by decide, by decide, rfl⟩
  y_mutant := .scalar { bits := 8193, sizeBytes := 8 }
  mutant_killed := by
    intro h
    match h 4096 4096 64 192 rfl with
    | ⟨r, hEq, hLe⟩ =>
      injection hEq with hS
      injection hS with hBits _
      subst hBits
      exact absurd hLe (by decide)

/-- Truncated-length buggy implementation returning bare `base` (dropping `e - s`). -/
def truncatedVmoSubsliceMutant (args : List Value) : Value :=
  match args with
  | .scalar baseScalar :: _ => .scalar { bits := baseScalar.bits, sizeBytes := 8 }
  | _ => .scalar { bits := 0, sizeBytes := 8 }

/-- ...YET the buggy `truncatedVmoSubsliceMutant` satisfies `weak_vmo_subslice_upper_bound_only`
    on EVERY valid input (so a single-mutant `SpecStrengthCert` misses the bug!). -/
theorem weak_vmo_subslice_truncated_mutant_survives :
    ∀ args, fxfsVmoSubslicePre args →
      weak_vmo_subslice_upper_bound_only args (truncatedVmoSubsliceMutant args) := by
  intro args _hPre base len s e hArgs
  subst hArgs
  exact ⟨base, rfl, Nat.le_add_right base len⟩

/-- Conversely, the strong specification `fxfsVmoSubslicePost` (backed by
    `fxfsVmoSubsliceMultiCert`'s `.truncatedLength` kill) constructively rejects
    `truncatedVmoSubsliceMutant`. -/
theorem strong_vmo_subslice_rejects_truncated_mutant :
    ¬ (∀ args, fxfsVmoSubslicePre args →
        fxfsVmoSubslicePost args (truncatedVmoSubsliceMutant args)) := by
  intro hSpec
  have hInput : fxfsVmoSubslicePre
      [ .scalar { bits := 4096, sizeBytes := 8 }
      , .scalar { bits := 4096, sizeBytes := 8 }
      , .scalar { bits := 64, sizeBytes := 8 }
      , .scalar { bits := 192, sizeBytes := 8 } ] :=
    ⟨4096, 4096, 64, 192, by decide, by decide, by decide, rfl⟩
  have hPost := hSpec _ hInput 4096 4096 64 192 rfl
  simp only [truncatedVmoSubsliceMutant] at hPost
  injection hPost with hS
  injection hS with hBits _
  exact absurd hBits (by decide)

end Anneal.OleanSpecStrengthAuditorProto
