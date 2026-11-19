import Lean.Meta.Basic
import Lean.Meta.SynthInstance
import Lean.PrettyPrinter
import Lean.Replay
import Lean.Util.CollectAxioms
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr
import Lean.Compiler.IR.CompilerM
import Trusted.VerificationResult

/-!
# Compiled `.olean` / `.olean.private` `MetaM` Environment Auditor and Constructive Specification-Strength Harness (Prototype)

This prototype module combines two complementary verification-integrity mechanisms
directly inside Lean `v4.34.1` with zero external Python source-text regex scanning:

1. **Compiled `.olean` / `.olean.private` `MetaM` Environment Auditor**:
   Inspects compiled Lean `v4.34.1` module environments (`OLeanLevel.private`,
   `env.setExporting false`, `env.checked.get`, `Lean.collectAxioms`, and compiler
   override attribute tables `@[implemented_by]`, `@[extern]`, `@[csimp]`, `@[init]`) across
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
      `@[csimp]`, `@[init]`) are forbidden on non-stdlib declarations in the closure. -/
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
  /-- Module roots where statement-origin unfolding stops (unless a constant also
      matches `statementForbiddenRoots`). A boundary is trusted by module *name*, and
      only toolchain names are path-verified by `auditCompiledModulesIO`, so the default
      is the toolchain stdlib alone. `Trusted` is deliberately NOT a default boundary:
      unfolding the genuine `Trusted.*` library is harmless (it cannot reach `Proof.*` /
      `Anneal.*`), while a package-provided module merely *named* `Trusted.*` then gets
      no cover. Any extra root listed here must be pinned to a directory through
      `auditCompiledModulesIO (pinnedModuleRoots := ...)`. -/
  statementAllowedRoots : Array Name := #[`Init, `Std]
  /-- Whether to enforce statement-vs.-proof origin separation on targets. -/
  checkStatementOrigin : Bool := true
  /-- Whether to cross-check transitive axioms against `Lean.collectAxioms` in
      `env.setExporting false`. -/
  crossCheckCollectAxioms : Bool := true
  /-- Extra module roots (beyond the toolchain `Init` / `Std` libraries) whose axioms
      are honoured when their names appear in `allowedAxioms`. An allowed axiom *name*
      declared anywhere else (e.g. a `prelude` module re-declaring `propext`) is rejected. -/
  allowedAxiomModuleRoots : Array Name := #[]
  /-- Whether an audit over an empty target set may report `ok`. Defaults to `false`
      so that an audit which inspected nothing can never be mistaken for a pass. -/
  allowEmptyTargetSet : Bool := false
  /-- Optional override of the closure / statement-walk fuel (used to exercise the
      fail-closed fuel-exhaustion path; `none` selects the environment-sized default). -/
  fuelOverride? : Option Nat := none
  /-- Heartbeat budget for re-checking each provisionally accepted native-evaluation
      axiom `ax : e = true` (`recheckProvisionalNativeIO`). `e` is first evaluated by
      `Meta.whnf` (at `.all` transparency so `@[irreducible]` cannot block evaluation)
      under this budget; only if that settles on a Bool literal is the kernel asked to
      certify the result by reduction alone. A confirmed axiom no longer depends on
      trusting the compiler, a refuted one is rejected, and an axiom that cannot be
      decided within the budget stays provisional. `0` disables the re-check. -/
  nativeRecheckHeartbeats : Nat := 200000
  /-- When `true` (or automatically whenever `allowProvisionalNative` is `true`), also
      reject any ambient `unsafe` declaration, `@[implemented_by]`, `@[extern]`,
      `@[init]`, non-stdlib `@[csimp]`, or non-companion `_unsafe_rec` sibling anywhere in the
      non-toolchain modules declaring reached non-stdlib constants (and their
      non-toolchain transitive imports). This closes closed-section `@[local csimp]`
      poisoning whose attribute entry is erased at `end` and whose target may be fully
      inlined into compiled IR. In the same mode every constant of those modules whose
      type has the `@[csimp]` shape `@f = @g` is audited like a target, because an erased
      `@[local csimp]` lemma redirects compiled code on the strength of its proof alone. -/
  forbidAmbientModuleOverrides : Bool := false
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
  /-- A module whose *name* carries trust (toolchain `Init.*` / `Std.*` / `Lean.*`, or a
      root listed in `statementAllowedRoots` / `allowedAxiomModuleRoots`) resolved to an
      `.olean` outside the directory that name is pinned to, or has no pin at all. -/
  | moduleProvenanceSpoofed (moduleName : Name) (resolvedPath : String) (expected : String)
  /-- `importModules` (or reading a module header) failed; reported structurally
      instead of escaping as an untyped `IO` exception. -/
  | environmentLoadFailed (detail : String)
  /-- The audit selected zero target declarations. -/
  | noAuditTargets (context : String)
  /-- A bounded graph walk ran out of fuel before reaching a fixed point. -/
  | auditFuelExhausted (target : Name) (phase : String)
  /-- More than one (or zero) candidate specification instance exists for a `defId`,
      so a certificate cannot be bound to the specification a claim was proven against. -/
  | specInstanceAmbiguous (specName : Name) (specClass : Name) (candidates : Array Name)
  /-- A certificate does not kill every mutant category required by the gate. -/
  | specStrengthCoverageGap (certDecl : Name) (missing : Array String) (reason : String)
  deriving Repr, BEq

/-- Deterministic metrics recorded for every audit run. -/
structure AuditStats where
  targetsAudited : Nat := 0
  reachableDeclarations : Nat := 0
  axiomsFound : Array Name := #[]
  /-- Native-evaluation axioms accepted only because `allowProvisionalNative := true`.
      A non-empty list means the verdict is *provisional*, never kernel-checked. -/
  provisionalNativeAxioms : Array Name := #[]
  /-- Native-evaluation axioms `ax : e = true` whose statement the kernel re-proved by
      reduction within `AuditPolicy.nativeRecheckHeartbeats`; they no longer rest on the
      compiler and are therefore not listed as provisional. -/
  kernelConfirmedNativeAxioms : Array Name := #[]
  modulesLoaded : Nat := 0
  privateArtifactsChecked : Nat := 0
  kernelReplayedDeclarations : Nat := 0
  /-- Wall-clock time spent in `importModules` (part of `elapsedMicros`). -/
  importMicros : Nat := 0
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
  | .moduleProvenanceSpoofed _ _ _ => "moduleProvenanceSpoofed"
  | .environmentLoadFailed _ => "environmentLoadFailed"
  | .noAuditTargets _ => "noAuditTargets"
  | .auditFuelExhausted _ _ => "auditFuelExhausted"
  | .specInstanceAmbiguous _ _ _ => "specInstanceAmbiguous"
  | .specStrengthCoverageGap _ _ _ => "specStrengthCoverageGap"

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
    | .moduleProvenanceSpoofed moduleName resolvedPath expected =>
      Json.mkObj [
        ("kind", toJson "moduleProvenanceSpoofed"),
        ("module", toJson moduleName.toString),
        ("resolvedPath", toJson resolvedPath),
        ("expected", toJson expected)]
    | .environmentLoadFailed detail =>
      Json.mkObj [
        ("kind", toJson "environmentLoadFailed"),
        ("detail", toJson detail)]
    | .noAuditTargets context =>
      Json.mkObj [
        ("kind", toJson "noAuditTargets"),
        ("context", toJson context)]
    | .auditFuelExhausted target phase =>
      Json.mkObj [
        ("kind", toJson "auditFuelExhausted"),
        ("target", toJson target.toString),
        ("phase", toJson phase)]
    | .specInstanceAmbiguous specName specClass candidates =>
      Json.mkObj [
        ("kind", toJson "specInstanceAmbiguous"),
        ("specName", toJson specName.toString),
        ("specClass", toJson specClass.toString),
        ("candidates", toJson ((candidates.qsort Name.lt).map Name.toString))]
    | .specStrengthCoverageGap certDecl missing reason =>
      Json.mkObj [
        ("kind", toJson "specStrengthCoverageGap"),
        ("certDecl", toJson certDecl.toString),
        ("missing", toJson missing),
        ("reason", toJson reason)]

instance : ToJson AuditStats where
  toJson s :=
    Json.mkObj [
      ("targetsAudited", toJson s.targetsAudited),
      ("reachableDeclarations", toJson s.reachableDeclarations),
      ("axiomsFound", toJson ((s.axiomsFound.qsort Name.lt).map Name.toString)),
      ("provisionalNativeAxioms",
        toJson ((s.provisionalNativeAxioms.qsort Name.lt).map Name.toString)),
      ("kernelConfirmedNativeAxioms",
        toJson ((s.kernelConfirmedNativeAxioms.qsort Name.lt).map Name.toString)),
      ("modulesLoaded", toJson s.modulesLoaded),
      ("privateArtifactsChecked", toJson s.privateArtifactsChecked),
      ("kernelReplayedDeclarations", toJson s.kernelReplayedDeclarations),
      ("importMicros", toJson s.importMicros),
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

/-- Structural validation of an auxiliary native-evaluation axiom.

    Lean `v4.34.1`'s `Lean.Meta.nativeEqTrue` (the engine behind `native_decide` and
    `bv_decide`) emits an axiom whose final name component starts with `ax_`, whose
    `isUnsafe` flag is `false`, and whose type is the binder-free proposition
    `@Eq.{1} Bool e Bool.true` using the toolchain stdlib `Eq`, `Bool`, and `Bool.true`
    for a closed `e` (never literally `Bool.false`). A hand-written `axiom foo._native.bar : False`,
    a `prelude` module re-declaring its own `Eq`/`Bool`, an `unsafe` axiom, or a literal
    `false = true` axiom all fail this check and are rejected as `.unapprovedAxiom`.

    This is a necessary condition only: a hand-written axiom that also copies the
    name and `@Eq Bool e true` shape with a non-literal `e` cannot be told apart from
    genuine compiler output without re-running the evaluation, which is why accepted
    native axioms are always surfaced in `AuditStats.provisionalNativeAxioms`. -/
def isWellFormedNativeAxiom (privEnv : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  let nameOk := match n with
    | .str _ s => s.startsWith "ax_"
    | _ => false
  let stdlibCoreOk :=
    (originModule? privEnv ``Eq).any isStdlibMod &&
    (originModule? privEnv ``Bool).any isStdlibMod &&
    (originModule? privEnv ``Bool.true).any isStdlibMod
  let typeOk := match ci.type with
    | .app (.app (.app (.const ``Eq [lvl]) (.const ``Bool [])) e) (.const ``Bool.true []) =>
      lvl == Level.succ Level.zero && !e.hasLooseBVars && !e.hasFVar && !e.hasMVar &&
      !(e.isConstOf ``Bool.false)
    | _ => false
  ci.isAxiom && !ci.isUnsafe && nameOk && stdlibCoreOk && typeOk

/-- Test whether `n` is `Lean.trustCompiler`. -/
def isTrustCompilerAxiom (n : Name) : Bool :=
  n == ``Lean.trustCompiler || n == `Lean.trustCompiler

/-- Test whether `n` has a `._unsafe_rec` component anywhere in its name. -/
def hasUnsafeRecComponent (n : Name) : Bool :=
  match n with
  | .str _ "_unsafe_rec" => true
  | _ => (n.toString.splitOn "._unsafe_rec").length > 1

/-- Check whether `ci` is the Lean equation compiler's dead codegen-only `_unsafe_rec`
    companion for a safe, total, non-partial parent `defnInfo` in the same module
    with matching kernel `type` and `levelParams`, and whose body actually contains a
    recursive call to at least one `._unsafe_rec` constant (empirically true for 100% of
    genuine equation-compiler companions, ruling out non-recursive metaprogram forgeries).
    Such companions are skipped during module inventory scans, but are ALWAYS rejected
    if ever reached directly in a kernel dependency closure. -/
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
          | .defnInfo _ =>
            let callsUnsafeRec :=
              match ci.value? (allowOpaque := true) with
              | some val =>
                val.getUsedConstantsAsSet.any fun d =>
                  match d with
                  | .str _ "_unsafe_rec" => true
                  | _ => false
              | none => false
            originModule? env parent == modName? &&
            ci.type == parentCi.type &&
            ci.levelParams == parentCi.levelParams &&
            callsUnsafeRec
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

/-- Build `CSimpIndex` across all non-stdlib imported modules and the live local state,
    including closed-scope `@[scoped csimp]` entries recorded in `StateStack.newEntries`
    and `StateStack.scopedEntries`. -/
def buildCSimpIndex (privEnv : Environment) : CSimpIndex := Id.run do
  let mut thmNames : NameSet := {}
  let mut fromToThm : Std.HashMap Name (Name × Name) := {}
  let addEntry (tAcc : NameSet) (mAcc : Std.HashMap Name (Name × Name))
      (ent : Lean.Compiler.CSimp.Entry) : NameSet × Std.HashMap Name (Name × Name) :=
    if !((originModule? privEnv ent.thmName).any isStdlibMod) then
      (tAcc.insert ent.thmName, mAcc.insert ent.fromDeclName (ent.toDeclName, ent.thmName))
    else
      (tAcc, mAcc)
  -- 1. Live active state (global, local, and currently open scoped entries).
  let st := Lean.Compiler.CSimp.ext.getState privEnv
  thmNames := st.thmNames.fold (init := thmNames) fun acc thm =>
    if !((originModule? privEnv thm).any isStdlibMod) then acc.insert thm else acc
  let (t1, m1) := st.map.fold (init := (thmNames, fromToThm)) fun (tAcc, mAcc) _ ent =>
    addEntry tAcc mAcc ent
  thmNames := t1
  fromToThm := m1
  -- 2. Live `StateStack` `newEntries` & `scopedEntries` (catches closed-scope
  --    `@[scoped csimp]` entries whose namespace ended before auditing!).
  let stack := Lean.Compiler.CSimp.ext.ext.getState privEnv
  for raw in stack.newEntries do
    let ent := match raw with
      | .global e => e
      | .scoped _ e => e
    let (t', m') := addEntry thmNames fromToThm ent
    thmNames := t'
    fromToThm := m'
  let (t2, m2) := stack.scopedEntries.map.fold (init := (thmNames, fromToThm)) fun acc _ arr =>
    arr.foldl (init := acc) fun (tAcc, mAcc) ent => addEntry tAcc mAcc ent
  thmNames := t2
  fromToThm := m2
  -- 3. Raw imported module entries (works even under `loadExts := false`!).
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

/-- Validate an axiom `axName` reached from `target` under `policy`.

    Trust is granted by *module provenance*, never by name alone:
    - names in `policy.allowedAxioms` are honoured only when declared in the toolchain
      stdlib (`Init` / `Std`) or under `policy.allowedAxiomModuleRoots`, so a `prelude`
      module re-declaring `propext` with a different statement is rejected;
    - `policy.allowAssumptionsNamespace` admits axioms declared in `Assumptions.*`
      *modules*; an `axiom Assumptions.foo` declared in any other module is rejected;
    - `._native.`-named axioms must additionally satisfy `isWellFormedNativeAxiom`. -/
def checkAxiomAllowed (privEnv : Environment) (policy : AuditPolicy)
    (target : Name) (axName : Name) : Option AuditViolation :=
  let modName? := originModule? privEnv axName
  let effMod? := effectiveModule? privEnv axName
  let fromStdlib := modName?.any isStdlibMod
  if axName == ``sorryAx || axName == `sorryAx then
    some (.sorryAxiomReached target axName)
  else if axName == ``Lean.ofReduceBool || axName == ``Lean.ofReduceNat then
    if !fromStdlib then
      some (.unapprovedAxiom target axName modName?
        "native-evaluation axiom name declared outside the toolchain stdlib")
    else if policy.allowProvisionalNative then none
    else some (.nativeDecideReached target axName modName?)
  else if isNativeDecideAxiom axName then
    match privEnv.checked.get.find? axName with
    | some ci =>
      if !isWellFormedNativeAxiom privEnv axName ci then
        some (.unapprovedAxiom target axName modName?
          "axiom name mimics a native_decide auxiliary axiom but fails structural/stdlib validation")
      else if policy.allowProvisionalNative then none
      else some (.nativeDecideReached target axName modName?)
    | none =>
      some (.unapprovedAxiom target axName modName? "native-named axiom missing from kernel environment")
  else if isTrustCompilerAxiom axName then
    if policy.allowTrustCompiler && fromStdlib then none
    else some (.unapprovedAxiom target axName modName? "Lean.trustCompiler is disallowed by policy")
  else if policy.allowedAxioms.contains axName then
    if fromStdlib ||
       effMod?.any (fun m => policy.allowedAxiomModuleRoots.any (matchesRootPrefix m ·)) then
      none
    else
      some (.unapprovedAxiom target axName modName?
        "allowed axiom name declared outside the toolchain stdlib and policy.allowedAxiomModuleRoots")
  else if policy.allowAssumptionsNamespace &&
          effMod?.any (fun m => matchesRootPrefix m `Assumptions) then
    none
  else
    some (.unapprovedAxiom target axName modName? "axiom not in policy.allowedAxioms")

/-- Check whether `n` is a `partial def` or a reachable `._unsafe_rec` helper.

    In Lean `v4.34.1` a user `partial def foo` is stored as a *safe* `.opaqueInfo foo`
    (`isPartial = false`, `isUnsafe = false`, carrying no `@[implemented_by]` entry)
    next to a sibling `.defnInfo foo._unsafe_rec` with `safety = .partial`, which the
    code generator selects purely by name. The sibling lookup below is therefore the
    only compiled trace of `partial`; `@[implemented_by]` is reported separately (and
    always) by `checkCompilerOverridesOnDecl`. -/
def detectPartialOrUnsafeRec (privEnv : Environment) (n : Name) (ci : ConstantInfo) : Option String :=
  if ci.isPartial then
    some "constant marked partial in kernel ConstantInfo"
  else if hasUnsafeRecComponent n then
    some "reachable _unsafe_rec partial/unsafe recursion helper"
  else
    match ci with
    | .opaqueInfo _ =>
      let recName := n.str "_unsafe_rec"
      match privEnv.checked.get.find? recName with
      | some recCi =>
        if recCi.isPartial || recCi.isUnsafe then
          some s!"opaque partial definition with sibling {recName}"
        else none
      | none => none
    | _ => none

/-- Check compiler override attributes (`@[implemented_by]`, `@[extern]`, `@[csimp]`,
    `@[init]` / `@[builtin_init]`) affecting declaration `n`.

    Attributes *attached to* `n` are skipped only when `n` itself lives in the toolchain
    stdlib. `@[csimp]` redirections are different: the theorem may live in an untrusted
    module while redirecting a stdlib function (`@[csimp] theorem : @Nat.add = @evil`),
    so the redirection lookup runs for every `n` (`CSimpIndex.fromToThm` only ever
    indexes non-stdlib theorems). -/
def checkCompilerOverridesOnDecl (privEnv : Environment) (csimpIdx : CSimpIndex)
    (target : Name) (n : Name) : Array AuditViolation := Id.run do
  let declIsStdlib := (originModule? privEnv n).any isStdlibMod
  let mut vs : Array AuditViolation := #[]
  if !declIsStdlib then
    if let some imp := Lean.Compiler.getImplementedBy? privEnv n then
      let impNote := match privEnv.checked.get.find? imp with
        | some impCi =>
          if impCi.isUnsafe then " (unsafe implementation)"
          else if impCi.isPartial then " (partial implementation)"
          else ""
        | none => " (implementation absent from kernel environment)"
      vs := vs.push (.compilerOverrideAttribute target n "implemented_by" s!"implemented_by {imp}{impNote}")
    if Lean.isExternC privEnv n then
      let cSym := (Lean.getExternNameFor privEnv `all n).getD "<extern_c>"
      vs := vs.push (.compilerOverrideAttribute target n "extern_c" s!"extern \"{cSym}\"")
    else if Lean.isExtern privEnv n then
      vs := vs.push (.compilerOverrideAttribute target n "extern" "extern compiler attribute")
    if Lean.Compiler.hasCSimpAttribute privEnv n || csimpIdx.thmNames.contains n then
      vs := vs.push (.compilerOverrideAttribute target n "csimp" "declaration tagged @[csimp]")
    -- `initialize x : T ← act` elaborates to `@[init initFn] opaque x : T`. The kernel
    -- sees an opaque constant, while compiled code reads whatever `initFn` returned when
    -- the defining module was loaded: a value that may depend on the file system, the
    -- clock, or the environment of that particular process. Two honest `native_decide`
    -- runs in different processes can therefore certify contradictory facts about `x`.
    if let some initFn := Lean.getInitFnNameFor? privEnv n then
      vs := vs.push (.compilerOverrideAttribute target n "init"
        s!"compiled value is produced at module load time by initializer {initFn}")
    else if Lean.isIOUnitInitFn privEnv n then
      vs := vs.push (.compilerOverrideAttribute target n "init"
        "IO action executed at module load time")
  if let some (toDecl, thmName) := csimpIdx.fromToThm[n]? then
    vs := vs.push (.compilerOverrideAttribute target n "csimp_target"
      s!"replaced in compiled code by {toDecl} via @[csimp] {thmName}")
  return vs

/-- Graph-walk fuel for `privEnv`: `policy.fuelOverride?` when set, otherwise twice the
    imported constant count plus slack (every walk visits each constant at most once). -/
def auditFuel (privEnv : Environment) (policy : AuditPolicy) (extra : Nat := 0) : Nat :=
  match policy.fuelOverride? with
  | some f => f
  | none =>
    let modConstTotal :=
      privEnv.header.moduleData.foldl (init := 0) fun acc d => acc + d.constants.size
    max 250000 (modConstTotal * 2 + extra * 2 + 16384)

/-- Fuel-bounded (structurally total, zero `partial`) statement-origin separation walk
    over the statement `rootType` of `target`.

    Rejects any constant matching `policy.statementForbiddenRoots` (by module origin
    OR unmangled namespace prefix). Unfolds constants in `policy.statementUnfoldRoots`
    as well as any non-boundary local/helper definitions (stopping only at
    `policy.statementAllowedRoots` when not forbidden), catching leaks hidden inside
    `Specs.*`, `Mir.*`, reducible `abbrev` aliases, structure fields, or typeclass
    instances.

    Module attribution uses `effectiveModule?`, so declarations of the module currently
    being elaborated (which carry no imported-module index) are attributed to
    `env.header.mainModule`; an in-process audit running inside a `Proof.*` / `Anneal.*`
    module therefore cannot launder un-namespaced helpers into a statement.

    `cleanSeen` carries constants already proven leak-free by earlier fully clean walks;
    the returned set extends it only when this walk found no violation. -/
def statementOriginWalk (privEnv : Environment) (policy : AuditPolicy)
    (target : Name) (rootType : Expr) (cleanSeen : NameSet) :
    Array AuditViolation × NameSet := Id.run do
  match expressionEdges rootType with
  | .error msg =>
    return (#[.openTermExpression target target s!"statement type: {msg}"], cleanSeen)
  | .ok initEdges =>
    let kenv := privEnv.checked.get
    let mut pending : Array (Name × Array Name) := #[]
    let mut seen : NameSet := cleanSeen
    let mut vs : Array AuditViolation := #[]
    for n in initEdges.toArray.qsort Name.lt do
      if !seen.contains n then
        seen := seen.insert n
        pending := pending.push (n, #[n])
    for _ in [:auditFuel privEnv policy] do
      if pending.isEmpty then
        break
      let (n, chain) := pending.back!
      pending := pending.pop
      let modName? := effectiveModule? privEnv n
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
        match kenv.find? n with
        | some depCi =>
          let (depEdges, openVs) := declarationEdges target depCi
          vs := openVs.foldl pushUniqueViolation vs
          for d in depEdges.toArray.qsort Name.lt do
            if !seen.contains d then
              seen := seen.insert d
              pending := pending.push (d, chain.push d)
        | none =>
          vs := pushUniqueViolation vs (.missingDeclaration n)
    if !pending.isEmpty then
      vs := pushUniqueViolation vs (.auditFuelExhausted target "statement-origin walk")
    return (vs, if vs.isEmpty then seen else cleanSeen)

/-- Statement-origin separation check for a single `target` (see `statementOriginWalk`). -/
def checkStatementOriginsInEnv (privEnv : Environment) (policy : AuditPolicy)
    (target : Name) (rootType : Expr) : Array AuditViolation :=
  (statementOriginWalk privEnv policy target rootType {}).1

/-- Test whether module `m` belongs to the pinned Lean toolchain (`Init`, `Std`, `Lean`). -/
private def isToolchainMod (m : Name) : Bool :=
  isStdlibMod m || matchesRootPrefix m `Lean

/-- Extract all function callees (`fap`/`pap`) from a compiled `Lean.IR.Decl` using a
    fuel-bounded iterative worklist (zero `partial`, zero `unsafe`). Returns
    `(callees, isExternIr, fuelExhausted)`. -/
private def irDeclCallees (d : Lean.IR.Decl) (fuel : Nat := 65536) : NameSet × Bool × Bool := Id.run do
  match d with
  | .extern .. => return ({}, true, false)
  | .fdecl _ _ _ body _ =>
    let mut stack : Array Lean.IR.FnBody := #[body]
    let mut acc : NameSet := {}
    for _ in [:fuel] do
      if stack.isEmpty then
        return (acc, false, false)
      let cur := stack.back!
      stack := stack.pop
      match cur with
      | .vdecl _ _ (.fap f _) b => acc := acc.insert f; stack := stack.push b
      | .vdecl _ _ (.pap f _) b => acc := acc.insert f; stack := stack.push b
      | .vdecl _ _ _ b => stack := stack.push b
      | .jdecl _ _ v b => stack := stack.push b; stack := stack.push v
      | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b
      | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => stack := stack.push b
      | .case _ _ _ alts =>
        for alt in alts do
          match alt with
          | .ctor _ b => stack := stack.push b
          | .default b => stack := stack.push b
      | _ => pure ()
    return (acc, false, !stack.isEmpty)

/-- Walk compiled IR (`Lean.IR.findEnvDecl`, available both in-process and on-disk under
    `loadExts := false`) starting from `startDecl`, following IR-only non-toolchain
    auxiliary functions (`_closed_*`, `_boxed`, `_redArg`, `_lambda_*`) transitively to
    collect every reached kernel-level callee (and flag any non-toolchain IR `.extern`
    callee or fuel exhaustion). Catches non-inlined `@[local csimp]` and IR-level
    redirections invisible in kernel terms. -/
private def collectIRCalleesForDecl (privEnv : Environment) (csimpIdx : CSimpIndex)
    (rootTarget : Name) (startDecl : Name) (irVisited : NameSet) (fuel : Nat := 8192) :
    Array Name × Array AuditViolation × NameSet := Id.run do
  let kenv := privEnv.checked.get
  let mut irSeen := irVisited
  let mut irStack : Array Name := #[]
  let mut kernelCallees : Array Name := #[]
  let mut vs : Array AuditViolation := #[]
  if !irSeen.contains startDecl then
    irSeen := irSeen.insert startDecl
    irStack := irStack.push startDecl
  for _ in [:fuel] do
    if irStack.isEmpty then
      return (kernelCallees, vs, irSeen)
    let cur := irStack.back!
    irStack := irStack.pop
    if let some irDecl := Lean.IR.findEnvDecl privEnv cur then
      let (callees, isExt, exhausted) := irDeclCallees irDecl
      if exhausted then
        vs := pushUniqueViolation vs (.auditFuelExhausted rootTarget s!"IR body walk ({cur})")
      let curMod? := originModule? privEnv cur
      if isExt && !(curMod?.any isToolchainMod) then
        if cur != startDecl then
          vs := pushUniqueViolation vs
            (.compilerOverrideAttribute rootTarget cur "ir_extern_callee"
              s!"compiled IR of {startDecl} calls extern IR declaration {cur}")
        else if !Lean.isExtern privEnv cur then
          -- An `extern` IR declaration without an `@[extern]` attribute is the opaque stub
          -- a `module`-system `.olean` stores in place of every function body; the real
          -- bodies live in the `.ir` companion, which Lean's loader treats as optional.
          -- Without it there is no compiled code to inspect, so nothing can be concluded.
          vs := pushUniqueViolation vs
            (.environmentLoadFailed
              s!"compiled IR of module {curMod?.getD .anonymous} was not loaded (its declarations carry opaque stubs); the .ir companion artifact is missing")
      for f in callees.toArray.qsort Name.lt do
        match kenv.find? f with
        | some fCi =>
          let fMod? := originModule? privEnv f
          let fIsTool := fMod?.any isToolchainMod
          let fHasNonStdSibling := match kenv.find? (f.str "_unsafe_rec") with
            | some _ => !((originModule? privEnv (f.str "_unsafe_rec")).any isStdlibMod)
            | none => false
          if !fIsTool || csimpIdx.fromToThm.contains f || fHasNonStdSibling then
            let f' := match f with
              | .str owner "_unsafe_rec" =>
                if isCodegenUnsafeRec privEnv (originModule? privEnv owner) fCi then owner else f
              | _ => f
            kernelCallees := kernelCallees.push f'
        | none =>
          -- IR-only auxiliary (`_redArg`, `_lam_N`, `_boxed`, specialisations, ...).
          -- Descend unless it is *owned by a toolchain module*. Its name says nothing
          -- about ownership: specialising a toolchain function for user code emits the
          -- copy into the user's module under a toolchain-rooted name (a `for` loop over
          -- a range becomes `Std.Legacy.Range.forIn'.loop._at_.<user>.spec_0`), and that
          -- copy contains the user's loop body.
          let ownedByToolchain := (originModule? privEnv f).any isToolchainMod
          if !ownedByToolchain && !irSeen.contains f then
            irSeen := irSeen.insert f
            irStack := irStack.push f
  if !irStack.isEmpty then
    vs := pushUniqueViolation vs (.auditFuelExhausted rootTarget s!"IR callee walk ({startDecl})")
  return (kernelCallees, vs, irSeen)

/-- Whether `ty` has the only shape `@[csimp]` accepts (`Lean.Compiler.CSimp.add`): a
    constant replacement `@Eq _ (.const f us) (.const g us)`. Any constant of this type,
    theorem or not, can have been registered as a compiler simplification lemma. -/
def csimpShape? (ty : Expr) : Option (Name × Name) :=
  match ty.eq? with
  | some (_, .const f us, .const g vs) => if us == vs then some (f, g) else none
  | _ => none

/-- Scan all non-toolchain modules declaring any reached non-toolchain constant (and
    their downward non-toolchain transitive imports, plus `kenv.constants.map₂` if any
    local constant was reached) for ambient `unsafe` declarations, `@[implemented_by]`,
    `@[extern]`, non-stdlib `@[csimp]`, or non-companion `_unsafe_rec` siblings.

    Because `@[local csimp]` is erased when its `section` closes (leaving zero entries in
    `CSimp.ext` on disk) and its target can be fully inlined into compiled IR, scanning
    ambient non-toolchain modules closes the only way `@[local csimp]` can introduce a
    compiled-vs.-kernel discrepancy.

    Also returns every ambient constant whose type has the `@[csimp]` shape
    (`csimpShape?`). A `@[local csimp]` lemma leaves no attribute entry behind, and its
    replacement function may be an ordinary definition with no override of its own; the
    redirection is then only as sound as the lemma's *proof*. Callers must therefore
    audit those constants as roots, so that a lemma resting on `sorryAx` or a custom
    axiom cannot silently rewrite compiled code. -/
private def ambientModuleOverrideViolations (privEnv : Environment) (csimpIdx : CSimpIndex)
    (repTarget : Name) (visited : NameSet) : Array AuditViolation × Array Name := Id.run do
  let kenv := privEnv.checked.get
  let nMods := privEnv.header.moduleNames.size
  let mut modIdxMap : Std.HashMap Name Nat := {}
  for i in [:nMods] do
    modIdxMap := modIdxMap.insert privEnv.header.moduleNames[i]! i
  let mut activeMods := Array.replicate nMods false
  let mut sawLocal := false
  for n in visited.toArray do
    match privEnv.getModuleIdxFor? n with
    | none => sawLocal := true
    | some idx =>
      if idx.toNat < nMods then
        let m := privEnv.header.moduleNames[idx.toNat]!
        if !isToolchainMod m then
          activeMods := activeMods.set! idx.toNat true
  if sawLocal then
    for imp in privEnv.header.imports do
      if !isToolchainMod imp.module then
        if let some j := modIdxMap[imp.module]? then
          activeMods := activeMods.set! j true
  -- Downward transitive closure over non-toolchain imports (bounded by `nMods`).
  for _ in [:nMods] do
    let mut changed := false
    for i in [:nMods] do
      if activeMods[i]! then
        for imp in privEnv.header.moduleData[i]!.imports do
          if !isToolchainMod imp.module then
            if let some j := modIdxMap[imp.module]? then
              if !activeMods[j]! then
                activeMods := activeMods.set! j true
                changed := true
    if !changed then break
  let mut vs : Array AuditViolation := #[]
  let mut checked : NameSet := {}
  let mut ambientDecls : Array (Name × ConstantInfo) := #[]
  for i in [:nMods] do
    if activeMods[i]! then
      let mdata := privEnv.header.moduleData[i]!
      for d in mdata.constNames do
        if !checked.contains d then
          if let some dCi := kenv.find? d then
            checked := checked.insert d
            ambientDecls := ambientDecls.push (d, dCi)
      for d in mdata.extraConstNames do
        if !checked.contains d then
          if let some dCi := kenv.find? d then
            checked := checked.insert d
            ambientDecls := ambientDecls.push (d, dCi)
  if sawLocal then
    for (d, dCi) in kenv.constants.map₂.toList do
      if !checked.contains d then
        checked := checked.insert d
        ambientDecls := ambientDecls.push (d, dCi)
  let mut lemmaRoots : Array Name := #[]
  for (d, dCi) in ambientDecls do
    if (csimpShape? dCi.type).isSome then
      lemmaRoots := lemmaRoots.push d
    if dCi.isUnsafe then
      vs := pushUniqueViolation vs
        (.compilerOverrideAttribute repTarget d "ambient_unsafe"
          s!"ambient unsafe declaration {d} in non-toolchain module closure can poison compiled code via local overrides")
    let ovs := checkCompilerOverridesOnDecl privEnv csimpIdx repTarget d
    for ov in ovs do
      vs := pushUniqueViolation vs ov
    if let .str owner "_unsafe_rec" := d then
      let dMod? := originModule? privEnv d
      if !(dMod?.any isStdlibMod) && !isCodegenUnsafeRec privEnv dMod? dCi then
        let isOpaquePartial := match kenv.find? owner with
          | some (.opaqueInfo _) => dCi.isPartial || dCi.isUnsafe
          | _ => false
        if !isOpaquePartial then
          vs := pushUniqueViolation vs
            (.compilerOverrideAttribute repTarget owner "ambient_unsafe_rec_sibling"
              s!"ambient non-companion _unsafe_rec sibling {d} in non-toolchain module closure")
  return (vs, lemmaRoots.qsort Name.lt)

/-- Audit a list of target declarations in a given `Environment` (pure total core,
    always inspecting `env.setExporting false` and `env.checked.get`).
    Uses an iterative, bounded $O(V + E)$ worklist (zero `partial`, zero `unsafe`,
    $O(1)$ call-stack space in the Lean interpreter) with per-edge root attribution.

    Fails closed on an empty target set (unless `policy.allowEmptyTargetSet`), on fuel
    exhaustion (`.auditFuelExhausted`), and on environments imported below
    `OLeanLevel.private` (`.environmentLoadFailed`). Stdlib trust in this pure entrypoint is by
    module *name* as recorded in `env.header`; `auditCompiledModulesIO` additionally
    verifies that such modules were loaded from the pinned toolchain directory. -/
def auditDeclsInEnvPure (env : Environment) (targets : Array Name)
    (policy : AuditPolicy := {}) : AuditVerdict := Id.run do
  let privEnv := env.setExporting false
  let kenv := privEnv.checked.get
  let csimpIdx := if policy.checkCompilerOverrides then buildCSimpIndex privEnv else {}
  let mut violations : Array AuditViolation := #[]
  let mut allAxioms : NameSet := {}
  let mut provisional : NameSet := {}
  let mut pending : Array (Name × Name) := #[]
  let mut visited : NameSet := {}
  let mut irVisited : NameSet := {}
  let mut stmtSeen : NameSet := {}
  let fuel := auditFuel privEnv policy targets.size
  if privEnv.header.isModule then
    -- `header.isModule` is set exactly when imports were loaded below
    -- `OLeanLevel.private` (elaboration inside a `module` file): theorem bodies and
    -- private constants of imports are then absent, so nothing can be concluded.
    violations := violations.push
      (.environmentLoadFailed
        "environment was imported below OLeanLevel.private; private constants and theorem bodies of imports are unavailable")
  if targets.isEmpty && !policy.allowEmptyTargetSet then
    violations := violations.push
      (.noAuditTargets "empty target set (policy.allowEmptyTargetSet = false)")
  for target in targets do
    match kenv.find? target with
    | none =>
      violations := pushUniqueViolation violations (.missingDeclaration target)
    | some rootCi =>
      if policy.requireTheoremKind && !rootCi.isTheorem then
        violations := pushUniqueViolation violations
          (.notTheoremKind target (constantInfoKind rootCi))
      if policy.checkStatementOrigin then
        let (stmtVs, stmtSeen') := statementOriginWalk privEnv policy target rootCi.type stmtSeen
        violations := stmtVs.foldl pushUniqueViolation violations
        stmtSeen := stmtSeen'
      if !visited.contains target then
        visited := visited.insert target
        pending := pending.push (target, target)
  -- Iterative O(V + E) graph closure. Phase 0 closes over the audit targets. Phase 1
  -- runs only in ambient mode (requested explicitly via
  -- `policy.forbidAmbientModuleOverrides`, or implied by `policy.allowProvisionalNative`,
  -- where compiled code affects proof soundness): it scans the non-toolchain modules
  -- behind everything reached so far for ambient overrides and then closes over every
  -- ambient constant of `@[csimp]` shape, so an erased `@[local csimp]` lemma is held to
  -- the same axiom policy as the targets themselves.
  let ambientMode := policy.checkCompilerOverrides &&
    (policy.forbidAmbientModuleOverrides || policy.allowProvisionalNative) && !targets.isEmpty
  for phase in [0:2] do
    if phase == 1 then
      if !ambientMode then
        break
      let (ambVs, lemmaRoots) := ambientModuleOverrideViolations privEnv csimpIdx targets[0]! visited
      violations := ambVs.foldl pushUniqueViolation violations
      for r in lemmaRoots do
        if !visited.contains r then
          visited := visited.insert r
          pending := pending.push (r, r)
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
        if policy.forbidPartialAndUnsafe then
          if let some reason := detectPartialOrUnsafeRec privEnv n ci then
            violations := pushUniqueViolation violations
              (.partialOrUnsafeRecDependency rootTarget n modName? reason)
        if policy.checkCompilerOverrides then
          let ovs := checkCompilerOverridesOnDecl privEnv csimpIdx rootTarget n
          violations := ovs.foldl pushUniqueViolation violations
        if ci.isAxiom then
          allAxioms := allAxioms.insert n
          match checkAxiomAllowed privEnv policy rootTarget n with
          | some axViol => violations := pushUniqueViolation violations axViol
          | none => if isNativeDecideAxiom n then provisional := provisional.insert n
        let (edges, openVs) := declarationEdges rootTarget ci
        violations := openVs.foldl pushUniqueViolation violations
        for d in edges.toArray.qsort Name.lt do
          if !visited.contains d then
            visited := visited.insert d
            pending := pending.push (rootTarget, d)
        -- Compiled IR callee audit: catches non-inlined `@[local csimp]` and IR-level
        -- redirections whose callees never appear in kernel terms.
        if policy.checkCompilerOverrides && !(modName?.any isToolchainMod) then
          let (irCallees, irVs, irVisited') :=
            collectIRCalleesForDecl privEnv csimpIdx rootTarget n irVisited
          irVisited := irVisited'
          violations := irVs.foldl pushUniqueViolation violations
          for d in irCallees do
            if !visited.contains d then
              visited := visited.insert d
              pending := pending.push (rootTarget, d)
        -- Name-based compiler override. Lean's code generator compiles `n` from a sibling
        -- constant `n._unsafe_rec` whenever one exists, with no attribute involved. Check
        -- EVERY reached `n` (including stdlib `n`, guarding on the *sibling's* origin
        -- module so user-declared `<StdlibFn>._unsafe_rec` is caught!). Only skip `.opaqueInfo`
        -- parents when `recCi` is partial/unsafe (already reported by `detectPartialOrUnsafeRec`);
        -- a safe `def foo._unsafe_rec` next to `opaque foo` is an override. For companion-shaped
        -- siblings, audit compiler override attributes on `recName` itself, its compiled IR,
        -- and its kernel dependencies.
        if policy.checkCompilerOverrides then
          let recName := n.str "_unsafe_rec"
          if let some recCi := kenv.find? recName then
            let recMod? := originModule? privEnv recName
            if !(recMod?.any isStdlibMod) then
              let handledByOpaquePartial := match ci with
                | .opaqueInfo _ => recCi.isPartial || recCi.isUnsafe
                | _ => false
              if !handledByOpaquePartial then
                if policy.forbidPartialAndUnsafe && recCi.isUnsafe then
                  violations := pushUniqueViolation violations
                    (.unsafeDeclaration rootTarget recName recMod?)
                let recOvs := checkCompilerOverridesOnDecl privEnv csimpIdx rootTarget recName
                violations := recOvs.foldl pushUniqueViolation violations
                if !isCodegenUnsafeRec privEnv modName? recCi then
                  violations := pushUniqueViolation violations
                    (.compilerOverrideAttribute rootTarget n "unsafe_rec_sibling"
                      s!"compiled code for {n} is taken from sibling {recName}, which is not an equation-compiler companion ({constantInfoKind recCi}, partial={recCi.isPartial}, unsafe={recCi.isUnsafe})")
                let (recEdges, recOpenVs) := declarationEdges rootTarget recCi
                violations := recOpenVs.foldl pushUniqueViolation violations
                for d in recEdges.toArray.qsort Name.lt do
                  if d != recName then
                    -- Companions of the same recursion group are audited through their owners.
                    let d' := match d with
                      | .str owner "_unsafe_rec" =>
                        match kenv.find? d with
                        | some dCi =>
                          if isCodegenUnsafeRec privEnv (originModule? privEnv owner) dCi then owner else d
                        | none => d
                      | _ => d
                    if !visited.contains d' then
                      visited := visited.insert d'
                      pending := pending.push (rootTarget, d')
                let (recIrCallees, recIrVs, irVisited') :=
                  collectIRCalleesForDecl privEnv csimpIdx rootTarget recName irVisited
                irVisited := irVisited'
                violations := recIrVs.foldl pushUniqueViolation violations
                for d in recIrCallees do
                  if d != recName && !visited.contains d then
                    visited := visited.insert d
                    pending := pending.push (rootTarget, d)
    if !pending.isEmpty then
      violations := pushUniqueViolation violations
        (.auditFuelExhausted (targets[0]?.getD .anonymous) "kernel dependency closure")
      break
  -- Cross-check against `Lean.collectAxioms` in `env.setExporting false`.
  if policy.crossCheckCollectAxioms then
    if targets.size <= 32 then
      for target in targets do
        if (kenv.find? target).isSome then
          let collected := collectAxiomsPrivate privEnv target
          for ax in collected do
            allAxioms := allAxioms.insert ax
            match checkAxiomAllowed privEnv policy target ax with
            | some axViol => violations := pushUniqueViolation violations axViol
            | none => if isNativeDecideAxiom ax then provisional := provisional.insert ax
    else
      let batchAxs := collectAxiomsBatchPrivate privEnv targets
      let repTarget := targets[0]!
      for ax in batchAxs do
        allAxioms := allAxioms.insert ax
        match checkAxiomAllowed privEnv policy repTarget ax with
        | some axViol => violations := pushUniqueViolation violations axViol
        | none => if isNativeDecideAxiom ax then provisional := provisional.insert ax
      for idx in [0, targets.size - 1] do
        if h : idx < targets.size then
          let target := targets[idx]
          if (kenv.find? target).isSome then
            let collected := collectAxiomsPrivate privEnv target
            for ax in collected do
              allAxioms := allAxioms.insert ax
              match checkAxiomAllowed privEnv policy target ax with
              | some axViol => violations := pushUniqueViolation violations axViol
              | none => if isNativeDecideAxiom ax then provisional := provisional.insert ax
  let stats : AuditStats := {
    targetsAudited := targets.size
    reachableDeclarations := visited.size
    axiomsFound := allAxioms.toArray.qsort Name.lt
    provisionalNativeAxioms := provisional.toArray.qsort Name.lt
    modulesLoaded := privEnv.header.modules.size
  }
  if violations.isEmpty then
    return .ok stats
  else
    return .rejected violations stats

/-- Choose a throw-away theorem name guaranteed absent from `kenv` so a hostile user
    declaration cannot collide with the re-check name and force `addDeclCore` to fail
    with `.alreadyDeclared`. -/
private def freshRecheckName (privEnv : Environment) (axName : Name) (rhs : Bool) : Name := Id.run do
  let kenv := privEnv.checked.get
  let suffix := if rhs then "true" else "false"
  let base := (axName.str "_kernel_recheck").str suffix
  if (kenv.find? base).isNone then
    return base
  let bound :=
    privEnv.header.moduleData.foldl (init := 250000) (fun acc d => acc + d.constants.size) +
    kenv.constants.map₂.toList.length + 4
  for i in [:bound] do
    let cand := base.num i
    if (kenv.find? cand).isNone then
      return cand
  return base.str "_fallback"

/-- Ask the kernel whether the Bool expression `e` of the native-evaluation axiom
    `axName : e = true` reduces to `rhs`, by type-checking `Eq.refl rhs : e = rhs` as a
    throw-away theorem under a guaranteed-fresh name. `maxHeartbeats` is the kernel's
    absolute per-thread heartbeat threshold; exceeding it (or any other kernel failure)
    yields `false`. Nothing is added to `privEnv`. -/
def kernelProvesNativeEq (privEnv : Environment) (axName : Name) (ci : ConstantInfo)
    (rhs : Bool) (maxHeartbeats : Nat) : Bool :=
  match ci.type with
  | .app (.app (.app (.const ``Eq [lvl]) boolTy) e) _ =>
    let kenv := privEnv.checked.get
    let rhsExpr := if rhs then mkConst ``Bool.true else mkConst ``Bool.false
    let decl := Declaration.thmDecl {
      name := freshRecheckName privEnv axName rhs
      levelParams := ci.levelParams
      type := mkApp3 (mkConst ``Eq [lvl]) boolTy e rhsExpr
      value := mkApp2 (mkConst ``Eq.refl [lvl]) boolTy rhsExpr
    }
    match kenv.addDeclCore maxHeartbeats.toUSize 512 decl none with
    | .ok _ => true
    | .error _ => false
  | _ => false

/-- Evaluate the closed Bool expression `e` with `Meta.withTransparency .all (Meta.whnf e)`
    under a heartbeat budget (unfolding `@[irreducible]` definitions just like Lean's
    kernel does). Returns `some b` when `e` weak-head-reduces to the literal `b`, and
    `none` on timeout, on any elaborator exception, or when reduction gets stuck.

    The kernel only polls its heartbeat threshold at coarse intervals (measured: a
    unary recursion over a `10^8` literal ran for seconds past a small threshold), so
    it cannot be handed an expression of unknown cost. `Meta.whnf` checks its budget at
    every step and therefore serves as the cost gate; its answer is never trusted on
    its own, only used to decide whether asking the kernel is affordable. -/
def boundedEvalBoolIO (privEnv : Environment) (e : Expr) (maxHeartbeats : Nat) :
    IO (Option Bool) := do
  -- Smart unfolding makes `Meta.whnf` reduce `f` through a sibling constant `f._sunfold`
  -- looked up purely by name; a hand-written `def f._sunfold` would steer (or block) the
  -- evaluation of `f` here while leaving the kernel's view of `f` untouched. Disable it
  -- so the gate unfolds the same definitions the kernel does.
  let options := Lean.Meta.smartUnfolding.set ({} : Options) false
  let coreCtx : Core.Context := {
    fileName := "<native-recheck>"
    fileMap := default
    options := options
    maxHeartbeats := maxHeartbeats
    initHeartbeats := (← IO.getNumHeartbeats)
  }
  let coreState : Core.State := { env := privEnv }
  let act : MetaM (Option Bool) := do
    let r ← Meta.withTransparency .all <| Meta.whnf e
    if r.isConstOf ``Bool.true then return some true
    else if r.isConstOf ``Bool.false then return some false
    else return none
  try
    let (r, _, _) ← act.toIO coreCtx coreState
    return r
  catch _ =>
    return none

/-- Post-pass over a verdict of `auditDeclsInEnvPure`: re-check every provisionally
    accepted native-evaluation axiom `ax : e = true`, within
    `policy.nativeRecheckHeartbeats`.

    `e` is evaluated by `boundedEvalBoolIO`; if that settles on a literal, the kernel
    is asked to certify it (`kernelProvesNativeEq`), so the outcome rests on the kernel
    alone:
    - kernel proves `e = true`: the axiom is kernel-provable and is moved from
      `provisionalNativeAxioms` to `kernelConfirmedNativeAxioms`.
    - kernel proves `e = false`: the axiom is false. This is what a forged "native"
      axiom looks like, and also what a genuine `native_decide` produces when compiled
      code disagrees with kernel semantics (`@[implemented_by]`, `@[csimp]`, a forged
      `_unsafe_rec` sibling, a miscompilation). Rejected as `.unapprovedAxiom`.
    - undecided within budget: stays provisional. A false axiom can still hide behind
      an expression that is too expensive to evaluate, or one on which reduction gets
      stuck (an `opaque` constant, well-founded recursion the kernel cannot unfold),
      which is exactly why such axioms keep the provisional label. Lean keeps no record
      that would tell a compiler-emitted native axiom from a hand-written one.

    Both `Meta.whnf` and the kernel run *compiled* code when they reduce
    `Lean.reduceBool` / `Lean.reduceNat`. An axiom whose dependencies reach those
    (visible as a dependency on `Lean.trustCompiler`) is never re-checked, so the
    auditor never executes untrusted compiled code. -/
def recheckProvisionalNativeIO (privEnv : Environment) (policy : AuditPolicy)
    (verdict : AuditVerdict) : IO AuditVerdict := do
  let stats := verdict.stats
  if policy.nativeRecheckHeartbeats == 0 || stats.provisionalNativeAxioms.isEmpty then
    return verdict
  let kenv := privEnv.checked.get
  let budget := policy.nativeRecheckHeartbeats
  let mut confirmed : Array Name := #[]
  let mut stillProvisional : Array Name := #[]
  let mut violations := verdict.violations
  for ax in stats.provisionalNativeAxioms do
    let decided? : Option (ConstantInfo × Bool) ← match kenv.find? ax with
      | none => pure none
      | some ci =>
        let reachesNativeHook := (collectAxiomsPrivate privEnv ax).any fun a =>
          isTrustCompilerAxiom a || a == ``Lean.ofReduceBool || a == ``Lean.ofReduceNat
        if reachesNativeHook then
          pure none
        else
          match ci.type with
          | .app (.app (.app (.const ``Eq _) _) e) _ =>
            pure ((← boundedEvalBoolIO privEnv e budget).map (ci, ·))
          | _ => pure none
    match decided? with
    | none => stillProvisional := stillProvisional.push ax
    | some (ci, metaValue) =>
      -- `Meta.whnf` found the evaluation cheap; the kernel alone is the judge. Its
      -- literal is only a hint for which polarity to try first: if the kernel does not
      -- agree with it, the opposite polarity is tried before giving up, so a disagreement
      -- between the two evaluators can never by itself keep a false axiom provisional.
      let thresholdFirst := (← IO.getNumHeartbeats) + 100 * budget
      let kernelValue? : Option Bool ←
        if kernelProvesNativeEq privEnv ax ci metaValue thresholdFirst then
          pure (some metaValue)
        else
          let thresholdSecond := (← IO.getNumHeartbeats) + 100 * budget
          if kernelProvesNativeEq privEnv ax ci (!metaValue) thresholdSecond then
            pure (some (!metaValue))
          else
            pure none
      match kernelValue? with
      | some true => confirmed := confirmed.push ax
      | some false =>
        violations := pushUniqueViolation violations
          (.unapprovedAxiom ax ax (originModule? privEnv ax)
            "native-evaluation axiom is refuted by kernel evaluation: its Bool expression reduces to `false`")
      | none => stillProvisional := stillProvisional.push ax
  let stats' : AuditStats :=
    { stats with
      provisionalNativeAxioms := stillProvisional
      kernelConfirmedNativeAxioms := confirmed }
  return if violations.isEmpty then .ok stats' else .rejected violations stats'

/-- Timed `IO` wrapper around `auditDeclsInEnvPure` followed by
    `recheckProvisionalNativeIO`. -/
def auditDeclsInEnvIO (env : Environment) (targets : Array Name)
    (policy : AuditPolicy := {}) : IO AuditVerdict := do
  let t0 ← IO.monoNanosNow
  let verdict ← recheckProvisionalNativeIO (env.setExporting false) policy
    (auditDeclsInEnvPure env targets policy)
  let t1 ← IO.monoNanosNow
  let elapsedMicros := (t1 - t0) / 1000
  return match verdict with
    | .ok s => .ok { s with elapsedMicros }
    | .rejected vs s => .rejected vs { s with elapsedMicros }

/-- Timed `MetaM` wrapper auditing declarations in the current live `Environment`. -/
def auditDeclsInMetaM (targets : Array Name) (policy : AuditPolicy := {}) : MetaM AuditVerdict := do
  let env ← getEnv
  liftM <| auditDeclsInEnvIO env targets policy

/-- Check on-disk `.olean` / `.olean.server` / `.olean.private` artifact integrity across
    the module import closure starting from `rootModules`.
    For every Lean `v4.34.1` `module`-system `.olean` (`ModuleData.isModule = true`),
    verifies that the companion `.olean.server` and `.olean.private` parts exist when
    `policy.requirePrivateOleanForModuleSystem = true`. Lean's own loader needs all three
    parts at `OLeanLevel.private`; checking them here turns what would otherwise be an
    untyped `IO` exception into a structured `.missingPrivateArtifact`. With
    `policy.checkCompilerOverrides` the compiled-code companions `.ir.sig` and `.ir` are
    required as well: the loader would otherwise continue without any function bodies.
    Unreadable module headers are reported as `.environmentLoadFailed`. -/
def checkPrivateOleanArtifactsIO (rootModules : Array Name)
    (policy : AuditPolicy := {}) (checkToolchainMods : Bool := false) :
    IO (Array AuditViolation × Nat) := do
  let mut violations : Array AuditViolation := #[]
  let mut checkedCount : Nat := 0
  let mut pending : Array Name := rootModules
  let mut seen : NameSet := {}
  for m in rootModules do seen := seen.insert m
  let fuel : Nat := 100000
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
        match (← (Lean.readModuleData oleanPath).toBaseIO) with
        | .error err =>
          violations := pushUniqueViolation violations
            (.environmentLoadFailed s!"cannot read module header {oleanPath}: {err}")
        | .ok (modData, _region) =>
          checkedCount := checkedCount + 1
          if modData.isModule && policy.requirePrivateOleanForModuleSystem then
            for level in [OLeanLevel.server, OLeanLevel.private] do
              let partPath := level.adjustFileName oleanPath
              if !(← partPath.pathExists) then
                violations := pushUniqueViolation violations
                  (.missingPrivateArtifact modName partPath.toString)
            -- Function bodies of a `module` file are compiled into `.ir` (next to its
            -- `.ir.sig`); the `.olean` parts only keep opaque stubs. Lean's loader skips
            -- both silently when `.ir.sig` is absent, which would blind every check on
            -- compiled code, so they are required whenever such checks are enabled.
            if policy.checkCompilerOverrides then
              for ext in ["ir.sig", "ir"] do
                let partPath := oleanPath.withExtension ext
                if !(← partPath.pathExists) then
                  violations := pushUniqueViolation violations
                    (.missingPrivateArtifact modName partPath.toString)
          for imp in modData.imports do
            if !seen.contains imp.module then
              seen := seen.insert imp.module
              pending := pending.push imp.module
  if !pending.isEmpty then
    violations := pushUniqueViolation violations
      (.auditFuelExhausted (rootModules[0]?.getD .anonymous) "artifact scan")
  return (violations, checkedCount)

/-- Verify that every loaded module whose *name* carries trust was resolved from the
    directory that name is pinned to.

    Stdlib exemptions elsewhere in the auditor (compiler-override checks, foundational
    axiom provenance, the statement-origin boundary, the artifact scan) key on module
    names. Without this check a package could ship its own `Std/Evil.lean` and inherit
    that trust. Two classes of names are checked:
    - toolchain names (`Init.*`, `Std.*`, `Lean.*`) must resolve under the pinned
      toolchain library directory (`toolchainLibDir?`, default: the running toolchain);
    - any non-toolchain root listed in `policy.statementAllowedRoots` (when statement
      origins are checked) or `policy.allowedAxiomModuleRoots` must have an entry in
      `pinnedModuleRoots` and resolve under it. An unpinned trust-bearing root fails
      closed.

    Paths are compared after `IO.FS.realPath`, so neither `..` segments in a search-path
    entry nor a symlinked directory can fake the prefix. -/
def checkModuleProvenanceIO (moduleNames : Array Name)
    (policy : AuditPolicy := {})
    (toolchainLibDir? : Option System.FilePath := none)
    (pinnedModuleRoots : Array (Name × System.FilePath) := #[]) :
    IO (Array AuditViolation) := do
  let realDir? (d : System.FilePath) : IO (Option System.FilePath) :=
    try
      let rp ← IO.FS.realPath d
      pure (some rp)
    catch _ =>
      pure none
  let libDir ← match toolchainLibDir? with
    | some d => pure d
    | none => Lean.getLibDir (← Lean.getBuildDir)
  let libDirReal? ← realDir? libDir
  let mut pinnedReal : Array (Name × Option System.FilePath) := #[]
  for (r, d) in pinnedModuleRoots do
    pinnedReal := pinnedReal.push (r, ← realDir? d)
  let isToolchainName (m : Name) : Bool := isStdlibMod m || isLeanCompilerMod m
  let trustRoots :=
    ((if policy.checkStatementOrigin then policy.statementAllowedRoots else #[]) ++
      policy.allowedAxiomModuleRoots).filter (!isToolchainName ·)
  let sep := System.FilePath.pathSeparator.toString
  let isEqualOrUnder (p dir : System.FilePath) : Bool :=
    let ds := dir.toString
    let ps := p.toString
    if ds == sep then ps.startsWith sep
    else
      let dsNorm := if ds.endsWith sep then (ds.dropEnd sep.length).toString else ds
      ps == dsNorm || ps.startsWith (dsNorm ++ sep)
  let mut violations : Array AuditViolation := #[]
  for m in moduleNames do
    -- `none`: name carries no trust. `some (none, why)`: trust-bearing but unpinned / missing pin dir.
    let expected? : Option (Option System.FilePath × String) :=
      if isToolchainName m then
        match libDirReal? with
        | some d => some (some d, "the pinned toolchain library directory")
        | none => some (none, s!"pinned toolchain library directory does not exist: {libDir}")
      else
        match pinnedReal.find? (fun (r, _) => matchesRootPrefix m r) with
        | some (r, some d) => some (some d, s!"the directory pinned for module root {r}")
        | some (r, none) =>
          some (none, s!"pinned directory for module root {r} does not exist")
        | none =>
          match trustRoots.find? (matchesRootPrefix m ·) with
          | none => none
          | some r =>
            some (none, s!"module root {r} carries trust but has no pinnedModuleRoots entry")
    match expected? with
    | none => pure ()
    | some (none, why) =>
      violations := pushUniqueViolation violations (.moduleProvenanceSpoofed m "<unpinned>" why)
    | some (some dir, why) =>
      let oleanPath? ← try
        let p ← Lean.findOLean m
        pure (some p)
      catch _ =>
        pure none
      match oleanPath? with
      | none =>
        violations := pushUniqueViolation violations
          (.moduleProvenanceSpoofed m "<unresolvable>" s!"expected under {why}")
      | some p =>
        -- 1. Verify the containing directory of `p` itself resides under `dir`, so a
        --    symlinked `.olean` inside an untrusted search-path directory cannot hijack
        --    sibling `.olean.server` / `.olean.private` / `.ir` files from outside `dir`.
        match p.parent with
        | none =>
          violations := pushUniqueViolation violations
            (.moduleProvenanceSpoofed m p.toString s!"missing parent directory; expected under {why}")
        | some parentDir =>
          match (← realDir? parentDir) with
          | none =>
            violations := pushUniqueViolation violations
              (.moduleProvenanceSpoofed m parentDir.toString s!"unresolvable parent; expected under {why}")
          | some parentReal =>
            unless isEqualOrUnder parentReal dir do
              violations := pushUniqueViolation violations
                (.moduleProvenanceSpoofed m parentDir.toString
                  s!"artifact directory resolves outside {why}")
        -- 2. Verify the `.olean` file itself AND every existing companion part
        --    (`.olean.server`, `.olean.private`, `.ir.sig`, `.ir`) resolve via `realPath`
        --    to the exact expected file path denoted by module `m` inside `dir` (blocking
        --    both split-artifact symlinks outside `dir` and intra-root module/companion
        --    aliasing via symlinked directories or companion files).
        let expectedOlean := Lean.modToFilePath dir m "olean"
        let parts : Array (String × System.FilePath × System.FilePath) := #[
          ("olean", p, expectedOlean),
          ("olean.server", OLeanLevel.server.adjustFileName p,
            OLeanLevel.server.adjustFileName expectedOlean),
          ("olean.private", OLeanLevel.private.adjustFileName p,
            OLeanLevel.private.adjustFileName expectedOlean),
          ("ir.sig", p.withExtension "ir.sig", expectedOlean.withExtension "ir.sig"),
          ("ir", p.withExtension "ir", expectedOlean.withExtension "ir")
        ]
        for (partLabel, partPath, expectedPart) in parts do
          let mustExist := partLabel == "olean"
          let existsNow ← partPath.pathExists
          if mustExist || existsNow then
            match (← realDir? partPath) with
            | none =>
              violations := pushUniqueViolation violations
                (.moduleProvenanceSpoofed m partPath.toString
                  s!"unresolvable {partLabel} artifact; expected under {why}")
            | some partReal =>
              unless isEqualOrUnder partReal dir do
                violations := pushUniqueViolation violations
                  (.moduleProvenanceSpoofed m partPath.toString
                    s!"{partLabel} artifact resolves outside {why}")
              if partReal != expectedPart then
                violations := pushUniqueViolation violations
                  (.moduleProvenanceSpoofed m partPath.toString
                    s!"{partLabel} artifact resolves to a different module's artifact inside {why}")
  return violations

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

/-- Compiled modules loaded at `OLeanLevel.private` and ready to be audited, possibly
    several times under different policies or target selections.

    Re-importing a module that is already mapped in the current process cannot reuse
    its compacted region (the region's base address is taken), so every additional
    `importModules` call costs the full size of the import closure in heap memory.
    Loading once and auditing many times keeps batch audits inside a fixed memory budget. -/
structure LoadedModules where
  /-- Environment with `setExporting false` already applied. -/
  privEnv : Environment
  rootModules : Array Name
  extraSearchPaths : List System.FilePath
  privateArtifactsChecked : Nat
  /-- Wall-clock time of the artifact scan plus `importModules`. -/
  importMicros : Nat

/-- Phase 1 of the on-disk auditor: check `.olean` / `.olean.server` / `.olean.private`
    artifact presence (`checkPrivateOleanArtifactsIO`) and load `rootModules` at
    `trustLevel := 0`, `loadExts := false`, `level := OLeanLevel.private`. Any failure
    is returned as a structured `AuditVerdict.rejected` (`.noAuditTargets`,
    `.missingPrivateArtifact`, `.environmentLoadFailed`), never as an `IO` exception. -/
def loadCompiledModulesIO
    (rootModules : Array Name)
    (policy : AuditPolicy := {})
    (extraSearchPaths : List System.FilePath := []) : IO (Except AuditVerdict LoadedModules) := do
  let t0 ← IO.monoNanosNow
  withExtraSearchPaths extraSearchPaths do
    if rootModules.isEmpty then
      let t1 ← IO.monoNanosNow
      return .error (.rejected #[.noAuditTargets "no root modules supplied"]
        { elapsedMicros := (t1 - t0) / 1000 })
    let (artifactViolations, privChecked) ← checkPrivateOleanArtifactsIO rootModules policy
    if !artifactViolations.isEmpty then
      let t1 ← IO.monoNanosNow
      return .error (.rejected artifactViolations {
        privateArtifactsChecked := privChecked
        elapsedMicros := (t1 - t0) / 1000
      })
    let imports := rootModules.map fun m => ({ module := m } : Import)
    let loaded ← (Lean.importModules imports {} (trustLevel := 0) (plugins := #[])
      (loadExts := false) (level := OLeanLevel.private)).toBaseIO
    let t1 ← IO.monoNanosNow
    match loaded with
    | .error err =>
      return .error (.rejected #[.environmentLoadFailed err.toString] {
        privateArtifactsChecked := privChecked
        importMicros := (t1 - t0) / 1000
        elapsedMicros := (t1 - t0) / 1000
      })
    | .ok env =>
      return .ok {
        privEnv := env.setExporting false
        rootModules
        extraSearchPaths
        privateArtifactsChecked := privChecked
        importMicros := (t1 - t0) / 1000
      }

/-- Phase 2 of the on-disk auditor, run against an already loaded `LoadedModules`:
    1. Verifies that modules whose names carry trust were loaded from the directories
       those names are pinned to (`checkModuleProvenanceIO`, `.moduleProvenanceSpoofed`).
    2. Selects `explicitTargets?` (or all non-codegen-`_unsafe_rec` declarations—or all
       theorems when `theoremsOnly := true`—declared in `targetModules?`, defaulting to
       the loaded root modules).
    3. Audits all selected targets via `auditDeclsInEnvPure` (full `ConstantInfo` graph
       closure + `Lean.collectAxioms` cross-check + compiler overrides + statement-origin
       separation).
    4. Optionally replays the selected modules' declarations in
       `baseEnv.toKernelEnv.replay` (one additional `importModules` of the base modules).

    `elapsedMicros` in the result covers load plus audit; `importMicros` isolates the
    load so repeated audits of one `LoadedModules` can be compared fairly. -/
def auditLoadedModulesIO
    (loaded : LoadedModules)
    (policy : AuditPolicy := {})
    (explicitTargets? : Option (Array Name) := none)
    (theoremsOnly : Bool := false)
    (runKernelReplay : Bool := false)
    (toolchainLibDir? : Option System.FilePath := none)
    (pinnedModuleRoots : Array (Name × System.FilePath) := #[])
    (targetModules? : Option (Array Name) := none) : IO AuditVerdict := do
  let t0 ← IO.monoNanosNow
  let privEnv := loaded.privEnv
  let targetModules := targetModules?.getD loaded.rootModules
  let finish (t1 : Nat) (s : AuditStats) : AuditStats :=
    { s with
      modulesLoaded := privEnv.header.modules.size
      privateArtifactsChecked := loaded.privateArtifactsChecked
      importMicros := loaded.importMicros
      elapsedMicros := loaded.importMicros + (t1 - t0) / 1000 }
  withExtraSearchPaths loaded.extraSearchPaths do
    let provenanceViolations ←
      checkModuleProvenanceIO (privEnv.header.modules.map (·.module)) policy
        toolchainLibDir? pinnedModuleRoots
    if !provenanceViolations.isEmpty then
      let t1 ← IO.monoNanosNow
      return .rejected provenanceViolations (finish t1 {})
    let mut inventoryViolations : Array AuditViolation := #[]
    for m in privEnv.header.modules, data in privEnv.header.moduleData do
      if targetModules.contains m.module then
        unless data.constNames == data.constants.map ConstantInfo.name do
          inventoryViolations := pushUniqueViolation inventoryViolations
            (.environmentLoadFailed s!"constNames/constants inventory mismatch in module {m.module}")
        for ci in data.constants do
          match privEnv.checked.get.find? ci.name with
          | none =>
            inventoryViolations := pushUniqueViolation inventoryViolations
              (.environmentLoadFailed s!"inventoried constant {ci.name} missing from kernel env in {m.module}")
          | some stored =>
            unless stored.type == ci.type && stored.value? true == ci.value? true do
              inventoryViolations := pushUniqueViolation inventoryViolations
                (.environmentLoadFailed s!"stored kernel declaration differs from module inventory for {ci.name} in {m.module}")
    if !inventoryViolations.isEmpty then
      let t1 ← IO.monoNanosNow
      return .rejected inventoryViolations (finish t1 {})
    let targets : Array Name := match explicitTargets? with
      | some ts => ts
      | none => Id.run do
        let mut acc : Array Name := #[]
        for m in privEnv.header.modules, data in privEnv.header.moduleData do
          if targetModules.contains m.module then
            for ci in data.constants do
              if !isCodegenUnsafeRec privEnv (some m.module) ci then
                if !theoremsOnly || ci.isTheorem then
                  acc := acc.push ci.name
        return acc
    let verdict ← recheckProvisionalNativeIO privEnv policy
      (auditDeclsInEnvPure privEnv targets policy)
    let mut violations := verdict.violations
    let mut replayedCount : Nat := 0
    if runKernelReplay && violations.isEmpty then
      let pinnedRoots := pinnedModuleRoots.map (·.1)
      let isBaseTrustedMod (modName : Name) : Bool :=
        !targetModules.contains modName &&
        (isStdlibMod modName || isLeanCompilerMod modName ||
          pinnedRoots.any (matchesRootPrefix modName ·))
      let mut replayLocals : Std.HashMap Name ConstantInfo := {}
      let mut baseMods : Array Name := #[]
      for m in privEnv.header.modules, data in privEnv.header.moduleData do
        if isBaseTrustedMod m.module then
          baseMods := baseMods.push m.module
        else
          for ci in data.constants do
            if !isCodegenUnsafeRec privEnv (some m.module) ci then
              replayLocals := replayLocals.insert ci.name ci
      try
        let baseEnv ← Lean.importModules (baseMods.map fun m => ({ module := m } : Import)) {}
          (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := OLeanLevel.private)
        let _ ← baseEnv.toKernelEnv.replay replayLocals
        replayedCount := replayLocals.size
      catch err =>
        violations := pushUniqueViolation violations (.kernelReplayFailed err.toString)
    let t1 ← IO.monoNanosNow
    let finalStats := finish t1 { verdict.stats with kernelReplayedDeclarations := replayedCount }
    if violations.isEmpty then
      return .ok finalStats
    else
      return .rejected violations finalStats

/-- End-to-end on-disk compiled `.olean` / `.olean.private` module auditor
    (`loadCompiledModulesIO` followed by `auditLoadedModulesIO`):
    1. Checks `.olean` / `.olean.server` / `.olean.private` presence via
       `checkPrivateOleanArtifactsIO`.
    2. Loads `rootModules` at `trustLevel := 0`, `loadExts := false`, `level := OLeanLevel.private`
       (load failures surface as `.environmentLoadFailed`).
    3. Verifies that modules whose names carry trust were loaded from the directories
       those names are pinned to (`checkModuleProvenanceIO`, `.moduleProvenanceSpoofed`).
    4. Applies `env.setExporting false` so private constants and theorem proofs are visible.
    5. Selects `explicitTargets` (or all non-codegen-`_unsafe_rec` declarations—or all theorems
       when `theoremsOnly := true`—declared in `rootModules`).
    6. Audits all selected targets via `auditDeclsInEnvPure` (full `ConstantInfo` graph closure
       + `Lean.collectAxioms` cross-check + compiler overrides + statement-origin separation).
    7. Optionally replays target-module declarations in `baseEnv.toKernelEnv.replay`. -/
def auditCompiledModulesIO
    (rootModules : Array Name)
    (policy : AuditPolicy := {})
    (explicitTargets? : Option (Array Name) := none)
    (theoremsOnly : Bool := false)
    (extraSearchPaths : List System.FilePath := [])
    (runKernelReplay : Bool := false)
    (toolchainLibDir? : Option System.FilePath := none)
    (pinnedModuleRoots : Array (Name × System.FilePath) := #[]) : IO AuditVerdict := do
  match (← loadCompiledModulesIO rootModules policy extraSearchPaths) with
  | .error verdict => return verdict
  | .ok loaded =>
    auditLoadedModulesIO loaded policy explicitTargets? theoremsOnly runKernelReplay
      toolchainLibDir? pinnedModuleRoots

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

/-- A single named, categorized, *discriminating* constructive mutant kill against
    `(req, ens)`.

    Besides the rejected `mutantOutput`, a kill must exhibit a `referenceOutput` that
    the specification *accepts on the same input*. Without it, a specification that is
    simply unsatisfiable on `input` (`∀ y, ¬ ens input y`, i.e. unimplementable there)
    would "kill" every mutant vacuously; with it, each kill proves the specification
    genuinely separates a correct behaviour from the buggy one. -/
structure NamedMutantKill {In : Type u} {Out : Type v}
    (req : In → Prop) (ens : In → Out → Prop) : Type (max u v) where
  name : String
  category : MutantCategory
  input : In
  input_valid : req input
  referenceOutput : Out
  reference_accepted : ens input referenceOutput
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

/-- A discriminating kill's accepted reference output and rejected mutant output are
    provably distinct. -/
theorem NamedMutantKill.reference_ne_mutant {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (k : NamedMutantKill req ens) : k.referenceOutput ≠ k.mutantOutput :=
  fun h => k.killed (h ▸ k.reference_accepted)

/-- No kill can sit at an input where the specification is unimplementable
    (`∀ y, ¬ ens x y`): rejecting a mutant there would be vacuous. This closes the gap
    left by `MultiMutantSpecCert.ens_realizable`, which only witnesses realizability
    at the single input `x₀`. -/
theorem no_kill_at_unrealizable_input {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (k : NamedMutantKill req ens) (hDead : ∀ y, ¬ ens k.input y) : False :=
  hDead k.referenceOutput k.reference_accepted

/-- Strongest specification-strength certificate: `(req, ens)` is satisfiable, is
    realizable on *every* valid input, and pins the output *uniquely*.

    A finite mutant list only shows that a handful of hand-picked wrong outputs are
    rejected. A deterministic specification rejects every deviating output on every
    valid input at once (`DeterministicSpecCert.kills_every_deviation`), so no mutant
    category can be silently missing from the suite. -/
structure DeterministicSpecCert {In : Type u} {Out : Type v}
    (req : In → Prop) (ens : In → Out → Prop) : Prop where
  req_nonvacuous : ∃ x, req x
  realizable : ∀ x, req x → ∃ y, ens x y
  unique : ∀ x y y', req x → ens x y → ens x y' → y = y'

/-- Under a deterministic specification, any output differing from an accepted
    reference output on a valid input is rejected. -/
theorem DeterministicSpecCert.kills_every_deviation {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (c : DeterministicSpecCert req ens) {x : In} {yRef yMut : Out}
    (hReq : req x) (hRef : ens x yRef) (hNe : yMut ≠ yRef) : ¬ ens x yMut :=
  fun hMut => hNe (c.unique x yMut yRef hReq hMut hRef)

/-- Under a deterministic specification, any implementation that deviates from a
    spec-satisfying reference implementation on even one valid input violates the
    specification. -/
theorem DeterministicSpecCert.deviating_impl_rejected {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (c : DeterministicSpecCert req ens) (fRef fMut : In → Out)
    (hRef : ∀ x, req x → ens x (fRef x)) {x : In} (hReq : req x)
    (hNe : fMut x ≠ fRef x) : ¬ (∀ x, req x → ens x (fMut x)) :=
  fun hSpec => hNe (c.unique x (fMut x) (fRef x) hReq (hSpec x hReq) (hRef x hReq))

/-- A trivial `ensures := True` postcondition over an output type with two distinct
    values is never deterministic. -/
theorem no_deterministic_cert_of_trivial_ens {In : Type u} {Out : Type v}
    (req : In → Prop) (y₁ y₂ : Out) (hNe : y₁ ≠ y₂) :
    DeterministicSpecCert req (fun (_ : In) (_ : Out) => True) → False :=
  fun c => match c.req_nonvacuous with
    | ⟨x, hx⟩ => hNe (c.unique x y₁ y₂ hx trivial trivial)

/-- A vacuous `requires := False` precondition is never deterministic. -/
theorem no_deterministic_cert_of_vacuous_req {In : Type u} {Out : Type v}
    (ens : In → Out → Prop) :
    DeterministicSpecCert (fun (_ : In) => False) ens → False :=
  fun c => match c.req_nonvacuous with
    | ⟨_, hx⟩ => hx

/-- Witness that a contract constrains behaviour on more than a single point: two valid
    inputs whose accepted outputs are not interchangeable.

    Every other certificate in this harness can be satisfied by a contract whose
    precondition admits exactly one input (`requires := x = 5`): it is non-vacuous,
    realizable, kills mutants, and is even deterministic, yet it says nothing about any
    other input. Such an over-restrictive precondition is the dual of a vacuous one.
    `InputSensitiveSpecCert` rules it out, together with contracts whose postcondition
    ignores the input altogether. -/
structure InputSensitiveSpecCert {In : Type u} {Out : Type v}
    (req : In → Prop) (ens : In → Out → Prop) : Type (max u v) where
  x₁ : In
  x₂ : In
  req₁ : req x₁
  req₂ : req x₂
  y₁ : Out
  y₂ : Out
  ens₁ : ens x₁ y₁
  ens₂ : ens x₂ y₂
  not_interchangeable : ¬ ens x₁ y₂

/-- The two inputs of an `InputSensitiveSpecCert` are provably distinct. -/
theorem InputSensitiveSpecCert.inputs_ne {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (c : InputSensitiveSpecCert req ens) : c.x₁ ≠ c.x₂ :=
  fun h => c.not_interchangeable (h ▸ c.ens₂)

/-- An `InputSensitiveSpecCert` yields a single-mutant `SpecStrengthCert`: the output
    required at `x₂` is a rejected mutant at `x₁`. -/
def InputSensitiveSpecCert.toSpecStrengthCert {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (c : InputSensitiveSpecCert req ens) : SpecStrengthCert req ens :=
  { x₀ := c.x₁
    req_nonvacuous := c.req₁
    x₁ := c.x₁
    mutant_req := c.req₁
    y_mutant := c.y₂
    mutant_killed := c.not_interchangeable }

/-- A precondition satisfied by at most one input can never be input-sensitive. -/
theorem no_input_sensitive_cert_of_singleton_req {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (hSingle : ∀ x x', req x → req x' → x = x') :
    InputSensitiveSpecCert req ens → False :=
  fun c => c.inputs_ne (hSingle c.x₁ c.x₂ c.req₁ c.req₂)

/-- A postcondition that does not depend on the input (any output accepted for one valid
    input is accepted for every valid input) can never be input-sensitive. -/
theorem no_input_sensitive_cert_of_input_independent_ens {In : Type u} {Out : Type v}
    {req : In → Prop} {ens : In → Out → Prop}
    (hIndep : ∀ x x' y, req x → req x' → ens x y → ens x' y) :
    InputSensitiveSpecCert req ens → False :=
  fun c => c.not_interchangeable (hIndep c.x₂ c.x₁ c.y₂ c.req₂ c.req₁ c.ens₂)

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

/-- Constructive direct specification-strength certificate for a modular rely–guarantee
    contract `(envAssumed, pre, post)`: pairs a non-vacuous external-call handler witness
    `handler_valid : envAssumed handler` with a `SpecStrengthCert` over `(pre, post)`. -/
structure ModularSpecStrengthCert
    (envAssumed : ExternalCallHandler → Prop)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Type where
  handler : ExternalCallHandler
  handler_valid : envAssumed handler
  cert : SpecStrengthCert
    (fun (p : List Value × Memory) => pre p.1 p.2)
    (fun (p : List Value × Memory) (r : Value × Memory) => post p.1 p.2 r.1 r.2)

/-- Constructive direct multi-mutant specification-strength certificate for a modular
    rely–guarantee contract `(envAssumed, pre, post)`. -/
structure ModularMultiMutantSpecCert
    (envAssumed : ExternalCallHandler → Prop)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Type where
  handler : ExternalCallHandler
  handler_valid : envAssumed handler
  cert : MultiMutantSpecCert
    (fun (p : List Value × Memory) => pre p.1 p.2)
    (fun (p : List Value × Memory) (r : Value × Memory) => post p.1 p.2 r.1 r.2)

/-- Constructive direct deterministic specification-strength certificate for a modular
    rely–guarantee contract `(envAssumed, pre, post)`. -/
structure ModularDeterministicSpecCert
    (envAssumed : ExternalCallHandler → Prop)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Prop where
  handler_nonvacuous : ∃ h, envAssumed h
  cert : DeterministicSpecCert
    (fun (p : List Value × Memory) => pre p.1 p.2)
    (fun (p : List Value × Memory) (r : Value × Memory) => post p.1 p.2 r.1 r.2)

/-- Constructive direct input-sensitivity specification-strength certificate for a
    modular rely–guarantee contract `(envAssumed, pre, post)`: pairs a non-vacuous
    external-call handler witness with an `InputSensitiveSpecCert` over `(pre, post)`. -/
structure ModularInputSensitiveSpecCert
    (envAssumed : ExternalCallHandler → Prop)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Type where
  handler : ExternalCallHandler
  handler_valid : envAssumed handler
  cert : InputSensitiveSpecCert
    (fun (p : List Value × Memory) => pre p.1 p.2)
    (fun (p : List Value × Memory) (r : Value × Memory) => post p.1 p.2 r.1 r.2)

/-- A modular contract with vacuous rely predicate `envAssumed := fun _ => False`
    can never admit a `ModularSpecStrengthCert`. -/
theorem no_modular_cert_of_vacuous_envAssumed
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) :
    ModularSpecStrengthCert (fun _ => False) pre post → False :=
  fun c => c.handler_valid

/-- A modular contract with vacuous rely predicate `envAssumed := fun _ => False`
    can never admit a `ModularInputSensitiveSpecCert`. -/
theorem no_modular_input_sensitive_cert_of_vacuous_envAssumed
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) :
    ModularInputSensitiveSpecCert (fun _ => False) pre post → False :=
  fun c => c.handler_valid

/-- A modular contract whose precondition holds on at most one `(args, mem)` input
    can never admit a `ModularInputSensitiveSpecCert`. -/
theorem no_modular_input_sensitive_cert_of_singleton_req
    (envAssumed : ExternalCallHandler → Prop)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (hSingle : ∀ a₁ m₁ a₂ m₂, pre a₁ m₁ → pre a₂ m₂ → (a₁, m₁) = (a₂, m₂)) :
    ModularInputSensitiveSpecCert envAssumed pre post → False :=
  fun c => no_input_sensitive_cert_of_singleton_req
    (fun p p' h1 h2 => hSingle p.1 p.2 p'.1 p'.2 h1 h2) c.cert

/-- A modular contract whose postcondition ignores the input can never admit a
    `ModularInputSensitiveSpecCert`. -/
theorem no_modular_input_sensitive_cert_of_input_independent_ens
    (envAssumed : ExternalCallHandler → Prop)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (hIndep : ∀ a₁ m₁ a₂ m₂ r m', pre a₁ m₁ → pre a₂ m₂ → post a₁ m₁ r m' → post a₂ m₂ r m') :
    ModularInputSensitiveSpecCert envAssumed pre post → False :=
  fun c => no_input_sensitive_cert_of_input_independent_ens
    (fun p p' r h1 h2 hPost => hIndep p.1 p.2 p'.1 p'.2 r.1 r.2 h1 h2 hPost) c.cert

/-- A modular contract with vacuous precondition `pre := fun _ _ => False`
    can never admit a `ModularSpecStrengthCert`. -/
theorem no_modular_cert_of_vacuous_req
    (envAssumed : ExternalCallHandler → Prop)
    (post : List Value → Memory → Value → Memory → Prop) :
    ModularSpecStrengthCert envAssumed (fun _ _ => False) post → False :=
  fun c => c.cert.req_nonvacuous

/-- A modular contract with trivial postcondition `post := fun _ _ _ _ => True`
    can never admit a `ModularSpecStrengthCert`. -/
theorem no_modular_cert_of_trivial_ens
    (envAssumed : ExternalCallHandler → Prop)
    (pre : List Value → Memory → Prop) :
    ModularSpecStrengthCert envAssumed pre (fun _ _ _ _ => True) → False :=
  fun c => c.cert.mutant_killed trivial

/-! ### `MetaM` Spec-Strength Gate (`auditSpecStrengthCertInEnv`) -/

/-- Certificate heads stated directly over `(In, Out, req, ens)`. -/
private def directCertHeads : Array Name := #[
  ``SpecStrengthCert,
  ``MultiMutantSpecCert,
  ``DeterministicSpecCert,
  ``InputSensitiveSpecCert
]

/-- Direct modular certificate heads stated over `(envAssumed, pre, post)`. -/
private def directModularCertHeads : Array Name := #[
  ``ModularSpecStrengthCert,
  ``ModularMultiMutantSpecCert,
  ``ModularDeterministicSpecCert,
  ``ModularInputSensitiveSpecCert
]

/-- Certificate typeclass heads paired with the specification class they certify. -/
private def classCertHeads : Array (Name × Name) := #[
  (``ItemSpecStrengthCert, ``ItemSpec),
  (``ItemMultiMutantCert, ``ItemSpec),
  (``StatefulItemSpecStrengthCert, ``StatefulItemSpec),
  (``StatefulItemMultiMutantCert, ``StatefulItemSpec),
  (``ModularItemSpecStrengthCert, ``ModularItemSpec),
  (``ModularItemMultiMutantCert, ``ModularItemSpec)
]

/-- Certificate heads whose witness carries a categorized `MultiMutantSpecCert`. -/
private def multiMutantCertHeads : Array Name := #[
  ``MultiMutantSpecCert,
  ``ModularMultiMutantSpecCert,
  ``ItemMultiMutantCert,
  ``StatefulItemMultiMutantCert,
  ``ModularItemMultiMutantCert
]

/-- Outcome of normalizing a declaration's conclusion type against `specClass`.
    `fuelExhausted` is treated fail-closed as a potential competing instance so deep
    alias/let/beta chains cannot slip past the uniqueness scan. -/
private inductive SpecConclusionMatch where
  | matched (arg : Expr)
  | notMatched
  | fuelExhausted

/-- Weakly normalize an extracted `defId` argument expression (stripping `.mdata`,
    zeta-reducing `.letE`, beta-reducing `.lam` applications, reducing `.proj` of
    constructors, and unfolding `.defnInfo` aliases up to `fuel`) so wrapped string
    literals resolve cleanly. -/
private def normalizeDefIdArg (kenv : Kernel.Environment) (e : Expr) (fuel : Nat := 32) : Expr :=
  match fuel with
  | 0 => e
  | fuel + 1 =>
    match e with
    | .mdata _ inner => normalizeDefIdArg kenv inner fuel
    | .letE _ _ val body _ => normalizeDefIdArg kenv (body.instantiate1 val) fuel
    | .proj structName idx s =>
      let s' := normalizeDefIdArg kenv s fuel
      match s'.getAppFn with
      | .const ctorName _ =>
        match kenv.find? ctorName with
        | some (.ctorInfo cinfo) =>
          let sArgs := s'.getAppArgs
          if cinfo.induct == structName && cinfo.numParams + idx < sArgs.size then
            normalizeDefIdArg kenv sArgs[cinfo.numParams + idx]! fuel
          else e
        | _ => e
      | _ => e
    | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .mdata _ inner => normalizeDefIdArg kenv (mkAppN inner args) fuel
      | .lam .. => normalizeDefIdArg kenv (fn.beta args) fuel
      | .letE _ _ val body _ => normalizeDefIdArg kenv (mkAppN (body.instantiate1 val) args) fuel
      | .proj structName idx s =>
        let s' := normalizeDefIdArg kenv s fuel
        match s'.getAppFn with
        | .const ctorName _ =>
          match kenv.find? ctorName with
          | some (.ctorInfo cinfo) =>
            let sArgs := s'.getAppArgs
            if cinfo.induct == structName && cinfo.numParams + idx < sArgs.size then
              normalizeDefIdArg kenv (mkAppN sArgs[cinfo.numParams + idx]! args) fuel
            else e
          | _ => e
        | _ => e
      | .const c lvls =>
        match kenv.find? c with
        | some (.defnInfo v) =>
          if v.levelParams.length == lvls.length then
            normalizeDefIdArg kenv ((v.value.instantiateLevelParams v.levelParams lvls).beta args) fuel
          else e
        | _ => e
      | _ => e

/-- Pure structural normalizer for testing whether `ty` concludes in `specClass <arg>`
    (stripping `∀` telescopes via `getForallBody` without consuming fuel, stripping
    `.mdata`, zeta-reducing `.letE`, beta-reducing `.lam`, reducing `.proj` of
    constructors, and delta-unfolding `.defnInfo` heads up to `fuel`).
    Returns `.fuelExhausted` (fail-closed) if `fuel` runs out before reaching a
    non-reducible head. -/
private def specClassConclusionMatch (kenv : Kernel.Environment) (specClass : Name) (ty : Expr)
    (fuel : Nat := 64) : SpecConclusionMatch :=
  match fuel with
  | 0 => .fuelExhausted
  | fuel + 1 =>
    let ty := ty.getForallBody
    match ty with
    | .mdata _ inner => specClassConclusionMatch kenv specClass inner fuel
    | .letE _ _ val body _ =>
      specClassConclusionMatch kenv specClass (body.instantiate1 val) fuel
    | .proj structName idx s =>
      let s' := normalizeDefIdArg kenv s fuel
      match s'.getAppFn with
      | .const ctorName _ =>
        match kenv.find? ctorName with
        | some (.ctorInfo cinfo) =>
          let sArgs := s'.getAppArgs
          if cinfo.induct == structName && cinfo.numParams + idx < sArgs.size then
            specClassConclusionMatch kenv specClass sArgs[cinfo.numParams + idx]! fuel
          else .notMatched
        | _ => .notMatched
      | _ => .notMatched
    | _ =>
      let fn := ty.getAppFn
      let args := ty.getAppArgs
      match fn with
      | .mdata _ inner =>
        specClassConclusionMatch kenv specClass (mkAppN inner args) fuel
      | .lam .. =>
        specClassConclusionMatch kenv specClass (fn.beta args) fuel
      | .letE _ _ val body _ =>
        specClassConclusionMatch kenv specClass (mkAppN (body.instantiate1 val) args) fuel
      | .proj structName idx s =>
        let s' := normalizeDefIdArg kenv s fuel
        match s'.getAppFn with
        | .const ctorName _ =>
          match kenv.find? ctorName with
          | some (.ctorInfo cinfo) =>
            let sArgs := s'.getAppArgs
            if cinfo.induct == structName && cinfo.numParams + idx < sArgs.size then
              specClassConclusionMatch kenv specClass (mkAppN sArgs[cinfo.numParams + idx]! args) fuel
            else .notMatched
          | _ => .notMatched
        | _ => .notMatched
      | .const c lvls =>
        if c == specClass then
          .matched (normalizeDefIdArg kenv (args[0]?.getD (.bvar 0)))
        else
          match kenv.find? c with
          | some (.defnInfo v) =>
            if v.levelParams.length == lvls.length then
              specClassConclusionMatch kenv specClass
                ((v.value.instantiateLevelParams v.levelParams lvls).beta args) fuel
            else .notMatched
          | _ => .notMatched
      | _ => .notMatched

/-- Compatibility wrapper returning `some arg` when `ty` concludes in `specClass arg`
    (or `some (.bvar 0)` on fuel exhaustion so callers fail closed). -/
def specClassConclusionArg? (kenv : Kernel.Environment) (specClass : Name) (ty : Expr)
    (fuel : Nat := 64) : Option Expr :=
  match specClassConclusionMatch kenv specClass ty fuel with
  | .matched arg => some arg
  | .fuelExhausted => some (.bvar 0)
  | .notMatched => none

/-- Compute the exact subset of imported modules that transitively import the module
    declaring `declName` (plus that module itself). Any module outside this set cannot
    reference `declName` directly or transitively under any kernel reduction. -/
private def modulesReachingDecl (privEnv : Environment) (declName : Name) : Array Bool :=
  let nMods := privEnv.header.moduleNames.size
  match privEnv.getModuleIdxFor? declName with
  | none => Array.replicate nMods false
  | some targetIdx => Id.run do
    let mut modIdxMap : Std.HashMap Name Nat := {}
    for i in [:nMods] do
      modIdxMap := modIdxMap.insert privEnv.header.moduleNames[i]! i
    let mut r := Array.replicate nMods false
    if targetIdx.toNat < nMods then
      r := r.set! targetIdx.toNat true
    for _ in [:nMods] do
      let mut changed := false
      for i in [:nMods] do
        if !r[i]! then
          for imp in privEnv.header.moduleData[i]!.imports do
            if let some j := modIdxMap[imp.module]? then
              if r[j]! then
                r := r.set! i true
                changed := true
                break
      if !changed then break
    return r

/-- Collect all kernel constants declared in any module that transitively imports
    `specClass`'s module, plus all local constants in `kenv.constants.map₂`. -/
private def constantsReachingSpecClass (privEnv : Environment) (specClass : Name) :
    Array (Name × ConstantInfo) := Id.run do
  let kenv := privEnv.checked.get
  let reaches := modulesReachingDecl privEnv specClass
  let mut seen : NameSet := {}
  let mut out : Array (Name × ConstantInfo) := #[]
  for i in [:reaches.size] do
    if reaches[i]! then
      let mdata := privEnv.header.moduleData[i]!
      for n in mdata.constNames do
        if !seen.contains n then
          if let some ci := kenv.find? n then
            seen := seen.insert n
            out := out.push (n, ci)
      for n in mdata.extraConstNames do
        if !seen.contains n then
          if let some ci := kenv.find? n then
            seen := seen.insert n
            out := out.push (n, ci)
  for (n, ci) in kenv.constants.map₂.toList do
    if !seen.contains n then
      seen := seen.insert n
      out := out.push (n, ci)
  return out

/-- Pure fast-skip test: returns `true` only when `ci.type`'s conclusion head is a
    non-reducible kernel constant (inductive, constructor, axiom, opaque, or theorem)
    different from `specClass`, or a non-reducible non-constant (`sort`, `lit`, `bvar`).
    Never skips `.letE`, `.lam`, `.mdata`, `.proj`, `.defnInfo`, `.recInfo`, or `.quotInfo`. -/
private def canFastSkipSpecCandidate (kenv : Kernel.Environment) (specClass : Name)
    (ci : ConstantInfo) : Bool :=
  let concl := ci.type.getForallBody
  match concl with
  | .letE .. | .mdata .. | .proj .. => false
  | _ =>
    match concl.getAppFn with
    | .const head _ =>
      if head == specClass then false
      else match kenv.find? head with
        | some (.inductInfo _) | some (.ctorInfo _) | some (.axiomInfo _)
        | some (.opaqueInfo _) | some (.thmInfo _) => true
        | _ => false
    | .lam .. | .letE .. | .mdata .. | .proj .. => false
    | _ => true

/-- Pure scan for all non-constructor constants in modules reaching `specClass` (plus
    local constants) whose type concludes (up to `getForallBody`, `.mdata`, `.letE`,
    `.lam`, `.proj`, and `.defnInfo` unfolding) in `specClass "<defId>"`, or in
    `specClass e` for a non-literal `e` (or exhausts fuel, fail-closed).

    Scans the kernel environment rather than the instance table, so `attribute [-instance]`,
    plain non-`instance` `def`s, `let`/`lam`/`proj`-wrapped types, and alias chains
    cannot hide a competing specification for the same `defId`. -/
def specInstanceCandidates (privEnv : Environment) (specClass : Name) (defId : String) :
    Array Name := Id.run do
  let kenv := privEnv.checked.get
  let classMod? := originModule? privEnv specClass
  let mut found : Array Name := #[]
  for (n, ci) in constantsReachingSpecClass privEnv specClass do
    match ci with
    | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ | .thmInfo _ =>
      if specClass.isPrefixOf n && originModule? privEnv n == classMod? then
        continue
      if canFastSkipSpecCandidate kenv specClass ci then
        continue
      match specClassConclusionMatch kenv specClass ci.type with
      | .notMatched => pure ()
      | .fuelExhausted => found := found.push n
      | .matched arg =>
        match arg with
        | Expr.lit (Literal.strVal s) =>
          if s == defId then found := found.push n
        | _ => found := found.push n
    | _ => pure ()
  return found.qsort Name.lt

/-- Full `MetaM` scan for all non-constructor constants in modules reaching `specClass`
    (plus local constants) whose type reduces under `Meta.withTransparency .all`
    (`Meta.forallTelescopeReducing` + `Meta.whnf`, covering β/ζ/δ/ι/projection/quotient
    reductions) to `specClass "<defId>"`, or to `specClass e` for a non-literal `e`, or
    fails to reduce cleanly (fail-closed). -/
def specInstanceCandidatesMeta (specClass : Name) (defId : String) : MetaM (Array Name) := do
  let privEnv := (← getEnv).setExporting false
  let kenv := privEnv.checked.get
  let classMod? := originModule? privEnv specClass
  let mut found : Array Name := #[]
  for (n, ci) in constantsReachingSpecClass privEnv specClass do
    match ci with
    | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ | .thmInfo _ =>
      if specClass.isPrefixOf n && originModule? privEnv n == classMod? then
        continue
      if canFastSkipSpecCandidate kenv specClass ci then
        continue
      let isCandidate ← try
        Meta.withTransparency .all do
          Meta.forallTelescopeReducing ci.type fun _ body => do
            let body ← Meta.whnf body
            if body.getAppFn.constName? == some specClass then
              let arg := body.getAppArgs[0]?.getD (.bvar 0)
              let arg ← Meta.whnf arg
              match arg with
              | Expr.lit (Literal.strVal s) => return (s == defId)
              | _ => return true
            else
              return false
      catch _ =>
        -- Fail closed if reduction throws (e.g. heartbeat/recursion limit).
        pure true
      if isCandidate then
        found := found.push n
    | _ => pure ()
  return found.qsort Name.lt

/-- Resolve *the* specification instance of `specClass` for `defId`, failing closed
    unless exactly one candidate constant exists and typeclass synthesis selects it.

    A verification claim is stated against whichever instance resolved when the claim
    was elaborated. If a second instance for the same `defId` exists (declared later,
    with higher priority, after erasing the first, or hidden behind `let`/beta/projection/
    alias/recursor reductions), a certificate could be checked against a stronger
    specification than the one actually verified; uniqueness rules that substitution out. -/
def resolveUniqueSpecInstance (specName : Name) (specClass : Name) (defId : String) :
    MetaM (Except AuditViolation Expr) := do
  let candidates ← specInstanceCandidatesMeta specClass defId
  if candidates.isEmpty then
    return .error (.specStrengthCertMissing specName
      s!"no {specClass} instance found for \"{defId}\"")
  if candidates.size != 1 then
    return .error (.specInstanceAmbiguous specName specClass candidates)
  let specTy := mkApp (mkConst specClass) (mkStrLit defId)
  match (← Meta.synthInstance? specTy) with
  | none =>
    return .error (.specStrengthCertMissing specName
      s!"no {specClass} instance found for \"{defId}\"")
  | some inst =>
    -- The instance must be the candidate constant itself, with no arguments. If it is
    -- an application (`@Ext.toItemSpec extInst`, `@paramSpec cfgInst`), the specification
    -- depends on further instance arguments whose own uniqueness is not established: a
    -- second `extInst` / `cfgInst` declared later would silently change which
    -- specification this resolves to.
    if inst.isConstOf candidates[0]! then
      return .ok inst
    else
      return .error (.specInstanceAmbiguous specName specClass
        (candidates.push (inst.getAppFn.constName?.getD .anonymous)))

/-- Bind the (weak-head-normal) certificate type `ty` of `certDecl` to the target
    specification. Returns `none` when bound, or the violation explaining why not.

    A certificate that cannot be tied to the specification under audit is worthless, so
    binding information is mandatory: direct certificates need *both* `expectedReq?` and
    `expectedEns?`; typeclass certificates need `expectedDefId?` and must mention the
    unique specification instance for that `defId`. -/
private def checkCertBinding (specName certDecl : Name) (ty : Expr)
    (expectedReq? expectedEns? : Option Expr) (expectedDefId? : Option String)
    (expectedEnvAssumed? : Option Expr := none) :
    MetaM (Option AuditViolation) := do
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  let tyStr := toString (← Meta.ppExpr ty)
  let invalid (msg : String) : AuditViolation :=
    .specStrengthCertInvalidType certDecl specName s!"{msg}: {tyStr}"
  let some head := fn.constName?
    | return some (invalid "not a SpecStrengthCert type")
  if directCertHeads.contains head then
    if expectedEnvAssumed?.isSome then
      return some (invalid "expected Modular*SpecCert binding envAssumed, got")
    if args.size != 4 then
      return some (invalid "malformed direct certificate type")
    match expectedReq?, expectedEns? with
    | some expReq, some expEns =>
      unless (← Meta.isDefEq args[2]! expReq) do
        return some (invalid "precondition mismatch")
      unless (← Meta.isDefEq args[3]! expEns) do
        return some (invalid "postcondition mismatch")
      return none
    | _, _ =>
      return some (invalid
        "unbound certificate (both expectedReq? and expectedEns? are required to bind a direct certificate to its specification)")
  else if directModularCertHeads.contains head then
    if args.size != 3 then
      return some (invalid "malformed direct modular certificate type")
    match expectedEnvAssumed?, expectedReq?, expectedEns? with
    | some expEnv, some expPre, some expPost =>
      unless (← Meta.isDefEq args[0]! expEnv) do
        return some (invalid "rely predicate (envAssumed) mismatch")
      unless (← Meta.isDefEq args[1]! expPre) do
        return some (invalid "precondition mismatch")
      unless (← Meta.isDefEq args[2]! expPost) do
        return some (invalid "postcondition mismatch")
      return none
    | _, _, _ =>
      return some (invalid
        "unbound modular certificate (expectedEnvAssumed?, expectedReq?, and expectedEns? are all required)")
  else
    match classCertHeads.find? (·.1 == head) with
    | none => return some (invalid "not a SpecStrengthCert type")
    | some (_, specClass) =>
      if expectedReq?.isSome || expectedEns?.isSome || expectedEnvAssumed?.isSome then
        return some (invalid "expected direct SpecStrengthCert/MultiMutantSpecCert/Modular*SpecCert, got")
      let some defId := expectedDefId?
        | return some (invalid
            "unbound certificate (expectedDefId? is required to bind a typeclass certificate to its specification)")
      if args.size != 2 then
        return some (invalid "malformed typeclass certificate type")
      unless (← Meta.isDefEq args[0]! (mkStrLit defId)) do
        return some (invalid s!"certificate is for a different defId than \"{defId}\"")
      match (← resolveUniqueSpecInstance specName specClass defId) with
      | .error v => return some v
      | .ok inst =>
        unless (← Meta.isDefEq args[1]! inst) do
          return some (invalid "certificate is stated against a different specification instance")
        return none

/-- Stable human-readable label of a `MutantCategory` (used in audit receipts). -/
def MutantCategory.label : MutantCategory → String
  | .wrongReturn => "wrongReturn"
  | .offByOneScalar => "offByOneScalar"
  | .swappedByteOrder => "swappedByteOrder"
  | .wrapOverflow => "wrapOverflow"
  | .truncatedLength => "truncatedLength"
  | .wrongBranchTag => "wrongBranchTag"
  | .unpreservedFrame => "unpreservedFrame"
  | .custom label => s!"custom:{label}"

/-- Reflect a `MutantCategory` value into the `Expr` denoting it. -/
def MutantCategory.toExpr : MutantCategory → Expr
  | .wrongReturn => mkConst ``MutantCategory.wrongReturn
  | .offByOneScalar => mkConst ``MutantCategory.offByOneScalar
  | .swappedByteOrder => mkConst ``MutantCategory.swappedByteOrder
  | .wrapOverflow => mkConst ``MutantCategory.wrapOverflow
  | .truncatedLength => mkConst ``MutantCategory.truncatedLength
  | .wrongBranchTag => mkConst ``MutantCategory.wrongBranchTag
  | .unpreservedFrame => mkConst ``MutantCategory.unpreservedFrame
  | .custom label => mkApp (mkConst ``MutantCategory.custom) (mkStrLit label)

/-- Decide, by reducing `MultiMutantSpecCert.coversCategory multiExpr cat` to a `Bool`
    literal, which of the `required` categories the certificate term `multiExpr` fails
    to kill. Anything that does not reduce to `Bool.true` counts as missing. -/
private def missingMutantCategories (multiExpr : Expr) (required : List MutantCategory) :
    MetaM (Array String) := do
  let mut missing : Array String := #[]
  for cat in required do
    let covers ← Meta.mkAppM ``MultiMutantSpecCert.coversCategory #[multiExpr, cat.toExpr]
    let r ← Meta.whnf covers
    unless r.isConstOf ``Bool.true do
      missing := missing.push cat.label
  return missing

/-- Enforce `required` mutant-category coverage on the certificate expression `certExpr`
    whose weak-head-normal type has head constant `head`. Single-mutant and
    `DeterministicSpecCert` witnesses carry no categorized kills and therefore cannot
    satisfy a non-empty `required` list. -/
private def checkCategoryCoverage (certLabel : Name) (head : Name) (certExpr : Expr)
    (required : List MutantCategory) : MetaM (Option AuditViolation) := do
  if required.isEmpty then
    return none
  let multiExpr? : Option Expr ←
    if head == ``MultiMutantSpecCert then pure (some certExpr)
    else if multiMutantCertHeads.contains head then
      pure (some (← Meta.mkProjection certExpr `cert))
    else pure none
  match multiExpr? with
  | none =>
    return some (.specStrengthCoverageGap certLabel (required.map (·.label)).toArray
      "certificate carries no categorized mutant kills")
  | some multiExpr =>
    let missing ← missingMutantCategories multiExpr required
    if missing.isEmpty then
      return none
    else
      return some (.specStrengthCoverageGap certLabel missing
        "required mutant categories are not killed by the certificate")

/-- `MetaM` specification-strength gate verifying that:
    1. A registered `SpecStrengthCert` / `MultiMutantSpecCert` / `DeterministicSpecCert`
       (or `*Item*Cert`) declaration `certDecl` exists in the environment;
    2. Its kernel type reduces via `whnf` to a recognised certificate head that is
       *bound* to the target specification (`checkCertBinding`): direct certificates
       must match both `expectedReq?` and `expectedEns?` up to `Meta.isDefEq`;
       typeclass certificates must match `expectedDefId?` and the unique specification
       instance for it. Omitting the binding information is rejected, never waved
       through (preventing certificate substitution from an unrelated strong spec);
    3. The certificate declaration itself passes the `MetaM` environment audit under
       `policy` (default `AuditPolicy.constructive`, preventing `sorry`-faked,
       `Classical.choice`-tainted, `partial`, `unsafe`, or `@[implemented_by]` certs);
    4. When `requiredCategories` is non-empty, the certificate is a categorized
       multi-mutant certificate whose kills cover every required `MutantCategory`
       (`.specStrengthCoverageGap` otherwise). -/
def auditSpecStrengthCertInEnv
    (specName : Name)
    (certDecl? : Option Name)
    (expectedReq? : Option Expr := none)
    (expectedEns? : Option Expr := none)
    (policy : AuditPolicy := { AuditPolicy.constructive with checkStatementOrigin := false })
    (expectedDefId? : Option String := none)
    (requiredCategories : List MutantCategory := [])
    (expectedEnvAssumed? : Option Expr := none) :
    MetaM AuditVerdict := do
  let t0 ← IO.monoNanosNow
  let reject (vs : Array AuditViolation) : MetaM AuditVerdict := do
    let t1 ← IO.monoNanosNow
    return .rejected vs { elapsedMicros := (t1 - t0) / 1000 }
  match certDecl? with
  | none =>
    reject #[.specStrengthCertMissing specName
      "no registered SpecStrengthCert or MultiMutantSpecCert declaration"]
  | some certDecl =>
    let env ← getEnv
    let privEnv := env.setExporting false
    match privEnv.checked.get.find? certDecl with
    | none => reject #[.missingDeclaration certDecl]
    | some ci =>
      let ty ← Meta.whnf ci.type
      match (← checkCertBinding specName certDecl ty expectedReq? expectedEns? expectedDefId?
          expectedEnvAssumed?) with
      | some v => reject #[v]
      | none =>
        -- Audit the certificate declaration BEFORE reducing it via `Meta.whnf` in
        -- `checkCategoryCoverage`, so `sorry`-faked, `partial`, `unsafe`, or
        -- `Classical.choice`-tainted certs always fail with their true soundness
        -- violation rather than being masked by `.specStrengthCoverageGap` (and
        -- unaudited terms are never evaluated by `whnf`).
        let envVerdict ← liftM <| auditDeclsInEnvIO privEnv #[certDecl] policy
        match envVerdict with
        | .rejected vs s =>
          let t1 ← IO.monoNanosNow
          return .rejected vs { s with elapsedMicros := (t1 - t0) / 1000 }
        | .ok s =>
          let certExpr := mkConst certDecl (ci.levelParams.map mkLevelParam)
          let head := ty.getAppFn.constName?.getD .anonymous
          match (← checkCategoryCoverage certDecl head certExpr requiredCategories) with
          | some v =>
            let t1 ← IO.monoNanosNow
            return .rejected #[v] { s with elapsedMicros := (t1 - t0) / 1000 }
          | none =>
            let t1 ← IO.monoNanosNow
            return .ok { s with elapsedMicros := (t1 - t0) / 1000 }

/-- Pair a 2-ary precondition `pre : A → M → Prop` and 4-ary postcondition
    `post : A → M → R → M → Prop` into `A × M → Prop` and `A × M → R × M → Prop`. -/
private def pairStatefulContract (pre post : Expr) : MetaM (Option (Expr × Expr)) := do
  let postTy ← Meta.whnf (← Meta.inferType post)
  Meta.forallBoundedTelescope postTy (some 4) fun xs _ => do
    if xs.size != 4 then
      return none
    else
      let aTy ← Meta.inferType xs[0]!
      let mTy ← Meta.inferType xs[1]!
      let rTy ← Meta.inferType xs[2]!
      let inTy ← Meta.mkAppM ``Prod #[aTy, mTy]
      let outTy ← Meta.mkAppM ``Prod #[rTy, mTy]
      let req ← Meta.withLocalDeclD `p inTy fun p => do
        Meta.mkLambdaFVars #[p]
          (mkApp2 pre (← Meta.mkAppM ``Prod.fst #[p]) (← Meta.mkAppM ``Prod.snd #[p]))
      let ens ← Meta.withLocalDeclD `p inTy fun p =>
        Meta.withLocalDeclD `r outTy fun r => do
          Meta.mkLambdaFVars #[p, r]
            (mkApp4 post (← Meta.mkAppM ``Prod.fst #[p]) (← Meta.mkAppM ``Prod.snd #[p])
              (← Meta.mkAppM ``Prod.fst #[r]) (← Meta.mkAppM ``Prod.snd #[r]))
      return some (req, ens)

/-- Claim-bound specification-strength gate.

    Reads the contract straight out of the audited verification claim (`claimDecl`, which
    must be a `.thmInfo` when `requireClaimTheorem := true`):
    - `VerificationResult c`: binds a direct `SpecStrengthCert` / `MultiMutantSpecCert` /
      `DeterministicSpecCert` against `(c.pre, c.post)`.
    - `StatefulVerificationResult c` / `TotalVerificationResult c`: binds a direct
      certificate against paired `(c.pre, c.post)` over `(List Value × Memory, Value × Memory)`.
    - `ModularVerificationResult c`: binds a direct `ModularSpecStrengthCert` /
      `ModularMultiMutantSpecCert` / `ModularDeterministicSpecCert` against ALL THREE
      components `(c.envAssumed, c.pre, c.post)` (witnessing rely non-vacuity as well as
      pre/post strength).

    Because the expected contract comes from the claim's own statement, a certificate
    for any other specification (a stronger sibling instance, a shadowing instance, or a
    spec that was never verified) cannot be substituted. -/
def auditClaimSpecStrengthInEnv
    (claimDecl : Name)
    (certDecl? : Option Name)
    (policy : AuditPolicy := { AuditPolicy.constructive with checkStatementOrigin := false })
    (requiredCategories : List MutantCategory := [])
    (requireClaimTheorem : Bool := true) :
    MetaM AuditVerdict := do
  let t0 ← IO.monoNanosNow
  let reject (vs : Array AuditViolation) : MetaM AuditVerdict := do
    let t1 ← IO.monoNanosNow
    return .rejected vs { elapsedMicros := (t1 - t0) / 1000 }
  let privEnv := (← getEnv).setExporting false
  match privEnv.checked.get.find? claimDecl with
  | none => reject #[.missingDeclaration claimDecl]
  | some ci =>
    if requireClaimTheorem && !ci.isTheorem then
      reject #[.notTheoremKind claimDecl (constantInfoKind ci)]
    else
      let ty ← Meta.whnf ci.type
      let args := ty.getAppArgs
      let head := ty.getAppFn.constName?.getD .anonymous
      let tyStr := toString (← Meta.ppExpr ty)
      let notClaim (why : String) : AuditViolation :=
        .specStrengthCertInvalidType claimDecl claimDecl s!"{why}: {tyStr}"
      if args.size != 1 then
        reject #[notClaim "claim is not a supported VerificationResult"]
      else if head == ``VerificationResult then
        let c := args[0]!
        let pre ← Meta.mkAppM ``Claim.pre #[c]
        let post ← Meta.mkAppM ``Claim.post #[c]
        auditSpecStrengthCertInEnv claimDecl certDecl? (some pre) (some post) policy none
          requiredCategories
      else if head == ``StatefulVerificationResult then
        let c := args[0]!
        let pre ← Meta.mkAppM ``StatefulClaim.pre #[c]
        let post ← Meta.mkAppM ``StatefulClaim.post #[c]
        match (← pairStatefulContract pre post) with
        | none => reject #[notClaim "stateful claim postcondition is not 4-ary"]
        | some (req, ens) =>
          auditSpecStrengthCertInEnv claimDecl certDecl? (some req) (some ens) policy none
            requiredCategories
      else if head == ``TotalVerificationResult then
        let c := args[0]!
        let pre ← Meta.mkAppM ``TotalClaim.pre #[c]
        let post ← Meta.mkAppM ``TotalClaim.post #[c]
        match (← pairStatefulContract pre post) with
        | none => reject #[notClaim "total claim postcondition is not 4-ary"]
        | some (req, ens) =>
          auditSpecStrengthCertInEnv claimDecl certDecl? (some req) (some ens) policy none
            requiredCategories
      else if head == ``ModularVerificationResult then
        let c := args[0]!
        let envAssumed ← Meta.mkAppM ``ModularClaim.envAssumed #[c]
        let pre ← Meta.mkAppM ``ModularClaim.pre #[c]
        let post ← Meta.mkAppM ``ModularClaim.post #[c]
        auditSpecStrengthCertInEnv claimDecl certDecl? (some pre) (some post) policy none
          requiredCategories (expectedEnvAssumed? := some envAssumed)
      else
        reject #[notClaim "claim is not a VerificationResult / StatefulVerificationResult / TotalVerificationResult / ModularVerificationResult"]

/-- Shared implementation of the typeclass-synthesis gates: resolves the unique
    specification instance of `specClass` for `defId`, synthesizes a
    `multiCertClass` (falling back to `singleCertClass` unless `requireMultiMutant`)
    certificate for exactly that instance, audits every constant of the witness FIRST,
    and then checks any required mutant-category coverage. -/
private def auditSpecStrengthBySynthCore
    (specClass multiCertClass singleCertClass : Name)
    (defId : String) (policy : AuditPolicy) (requireMultiMutant : Bool)
    (requiredCategories : List MutantCategory) :
    MetaM AuditVerdict := do
  let t0 ← IO.monoNanosNow
  let reject (vs : Array AuditViolation) : MetaM AuditVerdict := do
    let t1 ← IO.monoNanosNow
    return .rejected vs { elapsedMicros := (t1 - t0) / 1000 }
  let specName := Name.mkSimple defId
  let defIdExpr := mkStrLit defId
  match (← resolveUniqueSpecInstance specName specClass defId) with
  | .error v => reject #[v]
  | .ok specInst =>
    let singleCertTy := mkApp2 (mkConst singleCertClass) defIdExpr specInst
    let multiCertTy := mkApp2 (mkConst multiCertClass) defIdExpr specInst
    let needMulti := requireMultiMutant || !requiredCategories.isEmpty
    let cert? : Option (Expr × Name) ← match (← Meta.synthInstance? multiCertTy) with
      | some inst => pure (some (inst, multiCertClass))
      | none =>
        if needMulti then pure none
        else pure ((← Meta.synthInstance? singleCertTy).map (·, singleCertClass))
    match cert? with
    | none =>
      let wanted := if needMulti then s!"{multiCertClass}"
        else s!"{singleCertClass} or {multiCertClass}"
      reject #[.specStrengthCertMissing specName s!"no {wanted} instance found for \"{defId}\""]
    | some (certInst, certHead) =>
      match expressionEdges certInst with
      | .error msg =>
        reject #[.openTermExpression specName specName s!"synthesized cert instance: {msg}"]
      | .ok constSet =>
        let env ← getEnv
        let privEnv := env.setExporting false
        let targets := constSet.toArray.qsort Name.lt
        let envVerdict ← liftM <| auditDeclsInEnvIO privEnv targets policy
        match envVerdict with
        | .rejected vs s =>
          let t1 ← IO.monoNanosNow
          return .rejected vs { s with elapsedMicros := (t1 - t0) / 1000 }
        | .ok s =>
          match (← checkCategoryCoverage specName certHead certInst requiredCategories) with
          | some v =>
            let t1 ← IO.monoNanosNow
            return .rejected #[v] { s with elapsedMicros := (t1 - t0) / 1000 }
          | none =>
            let t1 ← IO.monoNanosNow
            return .ok { s with elapsedMicros := (t1 - t0) / 1000 }

/-- `MetaM` gate using typeclass synthesis to locate an `ItemSpecStrengthCert` (or
    `ItemMultiMutantCert`) for the unique `ItemSpec defId`, rejecting fail-closed if the
    specification instance is missing or ambiguous, if no certificate is registered, or
    if any constant in the synthesized witness fails the environment audit. -/
def auditItemSpecStrengthBySynth (defId : String)
    (policy : AuditPolicy := { AuditPolicy.constructive with checkStatementOrigin := false })
    (requireMultiMutant : Bool := false)
    (requiredCategories : List MutantCategory := []) :
    MetaM AuditVerdict :=
  auditSpecStrengthBySynthCore ``ItemSpec ``ItemMultiMutantCert ``ItemSpecStrengthCert
    defId policy requireMultiMutant requiredCategories

/-- `auditItemSpecStrengthBySynth` for `StatefulItemSpec defId`. -/
def auditStatefulItemSpecStrengthBySynth (defId : String)
    (policy : AuditPolicy := { AuditPolicy.constructive with checkStatementOrigin := false })
    (requireMultiMutant : Bool := false)
    (requiredCategories : List MutantCategory := []) :
    MetaM AuditVerdict :=
  auditSpecStrengthBySynthCore ``StatefulItemSpec ``StatefulItemMultiMutantCert
    ``StatefulItemSpecStrengthCert defId policy requireMultiMutant requiredCategories

/-- `auditItemSpecStrengthBySynth` for `ModularItemSpec defId` (the certificate also
    carries a constructive witness that the rely predicate `envAssumed` is non-vacuous). -/
def auditModularItemSpecStrengthBySynth (defId : String)
    (policy : AuditPolicy := { AuditPolicy.constructive with checkStatementOrigin := false })
    (requireMultiMutant : Bool := false)
    (requiredCategories : List MutantCategory := []) :
    MetaM AuditVerdict :=
  auditSpecStrengthBySynthCore ``ModularItemSpec ``ModularItemMultiMutantCert
    ``ModularItemSpecStrengthCert defId policy requireMultiMutant requiredCategories

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

/-- Introduction rule: on well-formed arguments `fxfsVmoSubslicePost` accepts exactly
    `base_offset + (sub_end - sub_start)`. Used as the accepted reference output of
    every discriminating kill below. -/
theorem fxfsVmoSubslicePost_exact (base len s e : Nat) :
    fxfsVmoSubslicePost
      [ .scalar { bits := base, sizeBytes := 8 }
      , .scalar { bits := len, sizeBytes := 8 }
      , .scalar { bits := s, sizeBytes := 8 }
      , .scalar { bits := e, sizeBytes := 8 } ]
      (.scalar { bits := base + (e - s), sizeBytes := 8 }) := by
  intro base' len' s' e' h
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

/-- Constructive `MultiMutantSpecCert` for `fxfs_storage_boundary::vmo_subslice_bounds_valid`,
    certifying realizability and killing `wrongReturn`, `wrapOverflow`, `truncatedLength`,
    `swappedByteOrder`, and `offByOneScalar` mutants (each against an accepted reference
    output on the same input) with zero `Classical.choice` and zero `sorryAx`. -/
def fxfsVmoSubsliceMultiCert :
    MultiMutantSpecCert fxfsVmoSubslicePre fxfsVmoSubslicePost where
  x₀ :=
    [ .scalar { bits := 4096, sizeBytes := 8 }
    , .scalar { bits := 4096, sizeBytes := 8 }
    , .scalar { bits := 64, sizeBytes := 8 }
    , .scalar { bits := 192, sizeBytes := 8 } ]
  req_nonvacuous := ⟨4096, 4096, 64, 192, by decide, by decide, by decide, rfl⟩
  y₀ := .scalar { bits := 4224, sizeBytes := 8 }
  ens_realizable := fxfsVmoSubslicePost_exact 4096 4096 64 192
  kills :=
    [ { name := "fxfs_wrong_return_zero"
        category := .wrongReturn
        input :=
          [ .scalar { bits := 4096, sizeBytes := 8 }
          , .scalar { bits := 4096, sizeBytes := 8 }
          , .scalar { bits := 64, sizeBytes := 8 }
          , .scalar { bits := 192, sizeBytes := 8 } ]
        input_valid := ⟨4096, 4096, 64, 192, by decide, by decide, by decide, rfl⟩
        referenceOutput := .scalar { bits := 4224, sizeBytes := 8 }
        reference_accepted := fxfsVmoSubslicePost_exact 4096 4096 64 192
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
        referenceOutput := .scalar { bits := 4294967304, sizeBytes := 8 }
        reference_accepted := fxfsVmoSubslicePost_exact 4294967288 32 0 16
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
        referenceOutput := .scalar { bits := 4224, sizeBytes := 8 }
        reference_accepted := fxfsVmoSubslicePost_exact 4096 4096 64 192
        -- Mutant omits `(sub_end - sub_start)` and returns bare `base_offset`.
        mutantOutput := .scalar { bits := 4096, sizeBytes := 8 }
        killed := by
          intro h
          have hEq := h 4096 4096 64 192 rfl
          injection hEq with hS
          injection hS with hBits _
          exact absurd hBits (by decide) }
    , { name := "fxfs_swapped_byte_order_bswap64"
        category := .swappedByteOrder
        input :=
          [ .scalar { bits := 0x0102, sizeBytes := 8 }
          , .scalar { bits := 0x0400, sizeBytes := 8 }
          , .scalar { bits := 0, sizeBytes := 8 }
          , .scalar { bits := 0x0010, sizeBytes := 8 } ]
        input_valid := ⟨0x0102, 0x0400, 0, 0x0010, by decide, by decide, by decide, rfl⟩
        referenceOutput := .scalar { bits := 0x0112, sizeBytes := 8 }
        reference_accepted := fxfsVmoSubslicePost_exact 0x0102 0x0400 0 0x0010
        -- Expected `0x0000_0000_0000_0112`; mutant returns the full 64-bit byte swap
        -- `0x1201_0000_0000_0000`.
        mutantOutput := .scalar { bits := 0x1201000000000000, sizeBytes := 8 }
        killed := by
          intro h
          have hEq := h 0x0102 0x0400 0 0x0010 rfl
          injection hEq with hS
          injection hS with hBits _
          exact absurd hBits (by decide) }
    , { name := "fxfs_off_by_one_inclusive_end"
        category := .offByOneScalar
        input :=
          [ .scalar { bits := 4096, sizeBytes := 8 }
          , .scalar { bits := 4096, sizeBytes := 8 }
          , .scalar { bits := 64, sizeBytes := 8 }
          , .scalar { bits := 192, sizeBytes := 8 } ]
        input_valid := ⟨4096, 4096, 64, 192, by decide, by decide, by decide, rfl⟩
        referenceOutput := .scalar { bits := 4224, sizeBytes := 8 }
        reference_accepted := fxfsVmoSubslicePost_exact 4096 4096 64 192
        -- Mutant treats `sub_end` as inclusive and returns `base + (e - s) + 1`.
        mutantOutput := .scalar { bits := 4225, sizeBytes := 8 }
        killed := by
          intro h
          have hEq := h 4096 4096 64 192 rfl
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

/-- Proof that `fxfsVmoSubsliceMultiCert` covers all required storage-boundary mutant categories. -/
theorem fxfsVmoSubslice_covers_required_categories :
    fxfsVmoSubsliceMultiCert.coversAllCategories
      [.wrongReturn, .wrapOverflow, .truncatedLength, .swappedByteOrder, .offByOneScalar] = true := rfl

/-- `fxfs_storage_boundary::vmo_subslice_bounds_valid` is a *deterministic* specification:
    realizable on every valid input and pinning the returned offset uniquely, so every
    deviating return value on every valid input is rejected, not just the five sampled
    mutants above. -/
theorem fxfsVmoSubslice_deterministic :
    DeterministicSpecCert fxfsVmoSubslicePre fxfsVmoSubslicePost where
  req_nonvacuous := ⟨_, fxfsVmoSubsliceMultiCert.req_nonvacuous⟩
  realizable := by
    intro args hPre
    match hPre with
    | ⟨base, len, s, e, _, _, _, hArgs⟩ =>
      subst hArgs
      exact ⟨_, fxfsVmoSubslicePost_exact base len s e⟩
  unique := by
    intro args y y' hPre h h'
    match hPre with
    | ⟨base, len, s, e, _, _, _, hArgs⟩ =>
      have e1 := h base len s e hArgs
      have e2 := h' base len s e hArgs
      rw [e1, e2]

/-- `fxfs_storage_boundary::vmo_subslice_bounds_valid` is input-sensitive: two valid
    argument tuples require different offsets (`4224` vs. `0x112`), so the precondition
    is not a single point and the postcondition genuinely depends on the arguments. -/
def fxfsVmoSubsliceInputSensitive :
    InputSensitiveSpecCert fxfsVmoSubslicePre fxfsVmoSubslicePost where
  x₁ :=
    [ .scalar { bits := 4096, sizeBytes := 8 }
    , .scalar { bits := 4096, sizeBytes := 8 }
    , .scalar { bits := 64, sizeBytes := 8 }
    , .scalar { bits := 192, sizeBytes := 8 } ]
  x₂ :=
    [ .scalar { bits := 0x0102, sizeBytes := 8 }
    , .scalar { bits := 0x0400, sizeBytes := 8 }
    , .scalar { bits := 0, sizeBytes := 8 }
    , .scalar { bits := 0x0010, sizeBytes := 8 } ]
  req₁ := ⟨4096, 4096, 64, 192, by decide, by decide, by decide, rfl⟩
  req₂ := ⟨0x0102, 0x0400, 0, 0x0010, by decide, by decide, by decide, rfl⟩
  y₁ := .scalar { bits := 4224, sizeBytes := 8 }
  y₂ := .scalar { bits := 0x0112, sizeBytes := 8 }
  ens₁ := fxfsVmoSubslicePost_exact 4096 4096 64 192
  ens₂ := fxfsVmoSubslicePost_exact 0x0102 0x0400 0 0x0010
  not_interchangeable := by
    intro h
    have hEq := h 4096 4096 64 192 rfl
    injection hEq with hS
    injection hS with hBits _
    exact absurd hBits (by decide)

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

/-- Introduction rule for the faulting branch (`source_in_restricted_range = 1`): the
    postcondition accepts `(fault_offset, dest_len - fault_offset)` with memory preserved. -/
theorem fuchsiaUsercopyCopyinPost_fault (dest_len fo v : Nat) (mem : Memory) :
    fuchsiaUsercopyCopyinPost
      [ .scalar { bits := 1, sizeBytes := 1 }
      , .scalar { bits := dest_len, sizeBytes := 8 }
      , .scalar { bits := fo, sizeBytes := 8 }
      , .scalar { bits := v, sizeBytes := 1 } ]
      mem
      (.aggregate 0
        [ .scalar { bits := fo, sizeBytes := 8 }
        , .scalar { bits := dest_len - fo, sizeBytes := 8 } ])
      mem := by
  refine ⟨rfl, ?_⟩
  intro in_range dest_len' fo' v' h
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

/-- Introduction rule for the non-faulting branch (`source_in_restricted_range = 0`):
    the postcondition accepts `(0, dest_len)` with memory preserved. -/
theorem fuchsiaUsercopyCopyinPost_noFault (dest_len fo v : Nat) (mem : Memory) :
    fuchsiaUsercopyCopyinPost
      [ .scalar { bits := 0, sizeBytes := 1 }
      , .scalar { bits := dest_len, sizeBytes := 8 }
      , .scalar { bits := fo, sizeBytes := 8 }
      , .scalar { bits := v, sizeBytes := 1 } ]
      mem
      (.aggregate 0
        [ .scalar { bits := 0, sizeBytes := 8 }
        , .scalar { bits := dest_len, sizeBytes := 8 } ])
      mem := by
  refine ⟨rfl, ?_⟩
  intro in_range dest_len' fo' v' h
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

/-- Constructive `MultiMutantSpecCert` for `fuchsia_usercopy::usercopy_copyin_bracketed`,
    certifying realizability and killing `wrongBranchTag` (in both directions),
    `truncatedLength`, `offByOneScalar`, and `unpreservedFrame` mutants, each against an
    accepted reference output on the same input, with zero axioms. -/
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
  ens_realizable := fuchsiaUsercopyCopyinPost_fault 256 64 1 emptyMemory
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
        referenceOutput :=
          ( .aggregate 0
              [ .scalar { bits := 64, sizeBytes := 8 }
              , .scalar { bits := 192, sizeBytes := 8 } ]
          , emptyMemory )
        reference_accepted := fuchsiaUsercopyCopyinPost_fault 256 64 1 emptyMemory
        -- Mutant takes the `in_range = 0` branch and returns `(0, 256)`.
        mutantOutput :=
          ( .aggregate 0
              [ .scalar { bits := 0, sizeBytes := 8 }
              , .scalar { bits := 256, sizeBytes := 8 } ]
          , emptyMemory )
        killed := by
          intro h
          have hVal := (ite_eq_left rfl).mp (h.2 1 256 64 1 rfl)
          injection hVal with _ hFields
          injection hFields with hF0 _
          injection hF0 with hS
          injection hS with hBits _
          exact Nat.noConfusion hBits }
    , { name := "usercopy_wrong_branch_tag_spurious_fault"
        category := .wrongBranchTag
        input :=
          ( [ .scalar { bits := 0, sizeBytes := 1 }
            , .scalar { bits := 256, sizeBytes := 8 }
            , .scalar { bits := 64, sizeBytes := 8 }
            , .scalar { bits := 1, sizeBytes := 1 } ]
          , emptyMemory )
        input_valid := ⟨0, 256, 64, 1, Or.inl rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
        referenceOutput :=
          ( .aggregate 0
              [ .scalar { bits := 0, sizeBytes := 8 }
              , .scalar { bits := 256, sizeBytes := 8 } ]
          , emptyMemory )
        reference_accepted := fuchsiaUsercopyCopyinPost_noFault 256 64 1 emptyMemory
        -- Mutant takes the `in_range = 1` branch although the source is not in the
        -- restricted range, returning `(64, 192)` instead of `(0, 256)`.
        mutantOutput :=
          ( .aggregate 0
              [ .scalar { bits := 64, sizeBytes := 8 }
              , .scalar { bits := 192, sizeBytes := 8 } ]
          , emptyMemory )
        killed := by
          intro h
          have hVal := (ite_eq_right (by decide)).mp (h.2 0 256 64 1 rfl)
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
        referenceOutput :=
          ( .aggregate 0
              [ .scalar { bits := 64, sizeBytes := 8 }
              , .scalar { bits := 192, sizeBytes := 8 } ]
          , emptyMemory )
        reference_accepted := fuchsiaUsercopyCopyinPost_fault 256 64 1 emptyMemory
        -- Mutant drops `uninit_len` to `0`, returning `(64, 0)` instead of `(64, 192)`.
        mutantOutput :=
          ( .aggregate 0
              [ .scalar { bits := 64, sizeBytes := 8 }
              , .scalar { bits := 0, sizeBytes := 8 } ]
          , emptyMemory )
        killed := by
          intro h
          have hVal := (ite_eq_left rfl).mp (h.2 1 256 64 1 rfl)
          injection hVal with _ hFields
          injection hFields with _ hRest
          injection hRest with hF1 _
          injection hF1 with hS
          injection hS with hBits _
          exact absurd hBits (by decide) }
    , { name := "usercopy_off_by_one_fault_offset"
        category := .offByOneScalar
        input :=
          ( [ .scalar { bits := 1, sizeBytes := 1 }
            , .scalar { bits := 256, sizeBytes := 8 }
            , .scalar { bits := 64, sizeBytes := 8 }
            , .scalar { bits := 1, sizeBytes := 1 } ]
          , emptyMemory )
        input_valid := ⟨1, 256, 64, 1, Or.inr rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
        referenceOutput :=
          ( .aggregate 0
              [ .scalar { bits := 64, sizeBytes := 8 }
              , .scalar { bits := 192, sizeBytes := 8 } ]
          , emptyMemory )
        reference_accepted := fuchsiaUsercopyCopyinPost_fault 256 64 1 emptyMemory
        -- Mutant returns `(65, 191)` (off-by-one `fault_offset + 1`).
        mutantOutput :=
          ( .aggregate 0
              [ .scalar { bits := 65, sizeBytes := 8 }
              , .scalar { bits := 191, sizeBytes := 8 } ]
          , emptyMemory )
        killed := by
          intro h
          have hVal := (ite_eq_left rfl).mp (h.2 1 256 64 1 rfl)
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
        referenceOutput :=
          ( .aggregate 0
              [ .scalar { bits := 0, sizeBytes := 8 }
              , .scalar { bits := 256, sizeBytes := 8 } ]
          , emptyMemory )
        reference_accepted := fuchsiaUsercopyCopyinPost_noFault 256 0 1 emptyMemory
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

/-- Direct claim-bound multi-mutant certificate for `ModularVerificationResult`
    of `fuchsia_usercopy::usercopy_copyin_bracketed` (constructive: `[propext, Quot.sound]`
    via `Trusted.ITree.ret`, zero `Classical.choice`). -/
def fuchsiaUsercopyCopyinModularDirectMultiCert :
    ModularMultiMutantSpecCert
      fuchsiaHermeticCopyRely
      fuchsiaUsercopyCopyinPre
      fuchsiaUsercopyCopyinPost where
  handler := fuchsiaHermeticCopyWitnessHandler
  handler_valid := fuchsiaHermeticCopyWitnessHandler_valid
  cert := fuchsiaUsercopyCopyinMultiCert

/-- Proof that `fuchsiaUsercopyCopyinMultiCert` covers all 4 required usercopy mutant categories. -/
theorem fuchsiaUsercopyCopyin_covers_required_categories :
    fuchsiaUsercopyCopyinMultiCert.coversAllCategories
      [.wrongBranchTag, .truncatedLength, .offByOneScalar, .unpreservedFrame] = true := rfl

/-- `fuchsia_usercopy::usercopy_copyin_bracketed` is a *deterministic* specification:
    realizable on every valid input and pinning both the returned tuple and the output
    memory uniquely, so every deviating `(ret, mem')` on every valid input is rejected. -/
theorem fuchsiaUsercopyCopyin_deterministic :
    DeterministicSpecCert
      (fun (p : List Value × Memory) => fuchsiaUsercopyCopyinPre p.1 p.2)
      (fun (p : List Value × Memory) (r : Value × Memory) =>
        fuchsiaUsercopyCopyinPost p.1 p.2 r.1 r.2) where
  req_nonvacuous := ⟨_, fuchsiaUsercopyCopyinMultiCert.req_nonvacuous⟩
  realizable := by
    intro p hPre
    match p, hPre with
    | (args, mem), ⟨in_range, dest_len, fo, v, hIR, _, _, _, hArgs, _⟩ =>
      subst hArgs
      cases hIR with
      | inl h0 =>
        subst h0
        exact ⟨(_, mem), fuchsiaUsercopyCopyinPost_noFault dest_len fo v mem⟩
      | inr h1 =>
        subst h1
        exact ⟨(_, mem), fuchsiaUsercopyCopyinPost_fault dest_len fo v mem⟩
  unique := by
    intro p r r' hPre h h'
    match p, r, r', hPre, h, h' with
    | (args, mem), (ret, m1), (ret', m2),
      ⟨in_range, dest_len, fo, v, hIR, _, _, _, hArgs, _⟩, ⟨hm1, hv1⟩, ⟨hm2, hv2⟩ =>
      have e1 := hv1 in_range dest_len fo v hArgs
      have e2 := hv2 in_range dest_len fo v hArgs
      have hm1' : m1 = mem := hm1
      have hm2' : m2 = mem := hm2
      cases hIR with
      | inl h0 =>
        subst h0
        have e1' : ret = .aggregate 0
            [ .scalar { bits := 0, sizeBytes := 8 }
            , .scalar { bits := dest_len, sizeBytes := 8 } ] := e1
        have e2' : ret' = .aggregate 0
            [ .scalar { bits := 0, sizeBytes := 8 }
            , .scalar { bits := dest_len, sizeBytes := 8 } ] := e2
        rw [e1', e2', hm1', hm2']
      | inr h1 =>
        subst h1
        have e1' : ret = .aggregate 0
            [ .scalar { bits := fo, sizeBytes := 8 }
            , .scalar { bits := dest_len - fo, sizeBytes := 8 } ] := e1
        have e2' : ret' = .aggregate 0
            [ .scalar { bits := fo, sizeBytes := 8 }
            , .scalar { bits := dest_len - fo, sizeBytes := 8 } ] := e2
        rw [e1', e2', hm1', hm2']

/-- Direct claim-bound deterministic certificate for `ModularVerificationResult`
    of `fuchsia_usercopy::usercopy_copyin_bracketed` (constructive: `[propext, Quot.sound]`
    via `Trusted.ITree.ret`, zero `Classical.choice`). -/
theorem fuchsiaUsercopyCopyinModularDirectDetCert :
    ModularDeterministicSpecCert
      fuchsiaHermeticCopyRely
      fuchsiaUsercopyCopyinPre
      fuchsiaUsercopyCopyinPost where
  handler_nonvacuous := ⟨fuchsiaHermeticCopyWitnessHandler, fuchsiaHermeticCopyWitnessHandler_valid⟩
  cert := fuchsiaUsercopyCopyin_deterministic

/-- `fuchsia_usercopy::usercopy_copyin_bracketed` is input-sensitive: the faulting and
    non-faulting argument tuples require different result tuples (`(64, 192)` vs.
    `(0, 256)`). -/
def fuchsiaUsercopyCopyinInputSensitive :
    InputSensitiveSpecCert
      (fun (p : List Value × Memory) => fuchsiaUsercopyCopyinPre p.1 p.2)
      (fun (p : List Value × Memory) (r : Value × Memory) =>
        fuchsiaUsercopyCopyinPost p.1 p.2 r.1 r.2) where
  x₁ :=
    ( [ .scalar { bits := 1, sizeBytes := 1 }
      , .scalar { bits := 256, sizeBytes := 8 }
      , .scalar { bits := 64, sizeBytes := 8 }
      , .scalar { bits := 1, sizeBytes := 1 } ]
    , emptyMemory )
  x₂ :=
    ( [ .scalar { bits := 0, sizeBytes := 1 }
      , .scalar { bits := 256, sizeBytes := 8 }
      , .scalar { bits := 64, sizeBytes := 8 }
      , .scalar { bits := 1, sizeBytes := 1 } ]
    , emptyMemory )
  req₁ := ⟨1, 256, 64, 1, Or.inr rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
  req₂ := ⟨0, 256, 64, 1, Or.inl rfl, by decide, by decide, Or.inr rfl, rfl, rfl⟩
  y₁ :=
    ( .aggregate 0
        [ .scalar { bits := 64, sizeBytes := 8 }
        , .scalar { bits := 192, sizeBytes := 8 } ]
    , emptyMemory )
  y₂ :=
    ( .aggregate 0
        [ .scalar { bits := 0, sizeBytes := 8 }
        , .scalar { bits := 256, sizeBytes := 8 } ]
    , emptyMemory )
  ens₁ := fuchsiaUsercopyCopyinPost_fault 256 64 1 emptyMemory
  ens₂ := fuchsiaUsercopyCopyinPost_noFault 256 64 1 emptyMemory
  not_interchangeable := by
    intro h
    have hVal := (ite_eq_left rfl).mp (h.2 1 256 64 1 rfl)
    injection hVal with _ hFields
    injection hFields with hF0 _
    injection hF0 with hS
    injection hS with hBits _
    exact Nat.noConfusion hBits

/-- Direct claim-bound input-sensitivity certificate for `ModularVerificationResult`
    of `fuchsia_usercopy::usercopy_copyin_bracketed` (constructive: `[propext, Quot.sound]`
    via `Trusted.ITree.ret`, zero `Classical.choice`). -/
def fuchsiaUsercopyCopyinModularDirectInputSensitiveCert :
    ModularInputSensitiveSpecCert
      fuchsiaHermeticCopyRely
      fuchsiaUsercopyCopyinPre
      fuchsiaUsercopyCopyinPost where
  handler := fuchsiaHermeticCopyWitnessHandler
  handler_valid := fuchsiaHermeticCopyWitnessHandler_valid
  cert := fuchsiaUsercopyCopyinInputSensitive

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

/-- The weak upper-bound-only specification is provably *not* deterministic: on the
    sampled valid input it accepts both the correct offset `4224` and the truncated
    offset `4096`, so it can never obtain a `DeterministicSpecCert`. -/
theorem weak_vmo_subslice_not_deterministic :
    DeterministicSpecCert fxfsVmoSubslicePre weak_vmo_subslice_upper_bound_only → False := by
  intro c
  have hInput : fxfsVmoSubslicePre
      [ .scalar { bits := 4096, sizeBytes := 8 }
      , .scalar { bits := 4096, sizeBytes := 8 }
      , .scalar { bits := 64, sizeBytes := 8 }
      , .scalar { bits := 192, sizeBytes := 8 } ] :=
    ⟨4096, 4096, 64, 192, by decide, by decide, by decide, rfl⟩
  have accepts : ∀ r : Nat, r ≤ 8192 →
      weak_vmo_subslice_upper_bound_only
        [ .scalar { bits := 4096, sizeBytes := 8 }
        , .scalar { bits := 4096, sizeBytes := 8 }
        , .scalar { bits := 64, sizeBytes := 8 }
        , .scalar { bits := 192, sizeBytes := 8 } ]
        (.scalar { bits := r, sizeBytes := 8 }) := by
    intro r hr base len s e h
    injection h with h1 hRest1
    injection h1 with h1s
    injection h1s with hBase _
    injection hRest1 with h2 _
    injection h2 with h2s
    injection h2s with hLen _
    subst hBase; subst hLen
    exact ⟨r, rfl, hr⟩
  have hEq := c.unique _ _ _ hInput (accepts 4224 (by decide)) (accepts 4096 (by decide))
  injection hEq with hS
  injection hS with hBits _
  exact absurd hBits (by decide)

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
