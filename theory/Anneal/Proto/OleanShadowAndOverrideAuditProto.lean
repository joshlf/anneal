module

public import Lean
import all Lean.Compiler.LCNF.Specialize
import all Lean.AuxRecursor
import all Lean.Compiler.LCNF.ToImpure

/-!
# Prototype: `.olean` private-name, unreferenced-axiom, shadowing, and compiler-override audits

Track P prototype (never merged). Pure, total `Lean` / `IO` audit checks for four trust-boundary
gaps in the compiled-environment auditors, pinned to Lean 4.34.1:

1. **Vector 1 — `_private.<mod>.0.<user>` namespace spoofing.** A structural parser
   (`parsePrivateName`) for the `mkPrivateName` encoding, declaring-module binding, user-suffix
   anti-spoofing, `_at_` specialization context verification, and extension-target coverage
   (`auditPrivateNames`).
2. **Vector 2 — unreferenced top-level axioms (`leanprover/lean4#16781`).** Reachability-only
   collectors (`Lean.collectAxioms`, `#print axioms`) never see an axiom that no checked root
   mentions. `auditUnreferencedAxioms` sweeps every axiom in every non-toolchain module's data,
   in `env.constants.map₂`, and in the kernel environment, fails closed on any exporting view,
   rejects non-toolchain re-declarations of foundational or foreign-assumption axioms, and
   classifies each axiom accurately.
3. **Vector 3 — `.olean` resolution, shadowing, symlinks and binary headers
   (`leanprover/lean4#16737`).** `pathWithinRoot` (canonical, symlink-free root and component
   containment), `auditOleanResolutionAndShadowing` (`Lean.findOLean` + multi-root probing +
   companion-part completeness), and a pure `ByteArray` header / compacted-region root + field
   validator (`validateOleanBinaryBytes`).
4. **Vector 4 — `Init.ShareCommon` (`leanprover/lean4#16779`), compiler-override hooks
   (`google/zerocopy#4321`), and opaque-theorem readiness (`leanprover/lean4#14896`).**
   `auditShareCommon` (unconditionally scanning proof bodies, LCNF, and IR), `auditCompilerHooks`
   (covering `.olean`, `.ir`, live `stateStack`/`scopedEntries`/pipeline state, and typed
   `specCacheExt` / `taggedReturnAttr` / `sparseCasesOnExt`), the structural scanner
   `scanOpaqueTheoremReliance`, and the kernel replay oracle `checkOpaqueTheoremReplay`
   (supporting theorems, definitions, mutual blocks, `opaque`, and inductive declarations).

`runAllFourVectorAudits` runs all of them over one environment.

Totality: every traversal is structurally recursive or explicitly fuel-bounded; running out of
fuel is reported as `auditFuelExhausted` (fail closed). Zero declarations use unverified
recursion, low-level escape hatches, incomplete proofs, or native tactic evaluation.

Toolchain modules are identified by name *and* provenance: a module counts as a toolchain module
only if its name is under a toolchain root and its `.olean` resolves (via `Lean.findOLean`) to a
regular, symlink-free file inside the canonical sysroot library directory.
-/

open Lean

namespace Anneal.Proto.OleanShadowAndOverrideAuditProto

public section

/-! ## Shared result types -/

/-- Every finding the prototype can report. -/
inductive ViolationKind where
  -- Vector 1
  | malformedPrivateName
  | privateModuleMismatch
  | privateUserSuffixSpoof
  -- Vector 2
  | exportedOnlyEnvironment
  | referencedUnapprovedAxiom
  | unreferencedTopLevelAxiom
  | unreferencedSorryOrNativeAxiom
  | unreferencedAssumptionAxiom
  | uninventoriedKernelAxiom
  -- Vector 3
  | oleanUnresolved
  | oleanShadowed
  | toolchainShadowed
  | oleanOutsideApprovedRoot
  | oleanHeaderInvalid
  -- Vector 4
  | shareCommonImport
  | shareCommonReference
  | compilerOverrideHook
  | foreignCompilerTag
  | postponedCompilation
  | opaqueTheoremStructural
  | opaqueTheoremDeltaReliance
  | nativeEvaluatorReachable
  -- shared
  | environmentLoadFailed
  | auditFuelExhausted
  deriving BEq, Repr, Inhabited, Hashable

def ViolationKind.tag : ViolationKind → String
  | .malformedPrivateName => "malformedPrivateName"
  | .privateModuleMismatch => "privateModuleMismatch"
  | .privateUserSuffixSpoof => "privateUserSuffixSpoof"
  | .exportedOnlyEnvironment => "exportedOnlyEnvironment"
  | .referencedUnapprovedAxiom => "referencedUnapprovedAxiom"
  | .unreferencedTopLevelAxiom => "unreferencedTopLevelAxiom"
  | .unreferencedSorryOrNativeAxiom => "unreferencedSorryOrNativeAxiom"
  | .unreferencedAssumptionAxiom => "unreferencedAssumptionAxiom"
  | .uninventoriedKernelAxiom => "uninventoriedKernelAxiom"
  | .oleanUnresolved => "oleanUnresolved"
  | .oleanShadowed => "oleanShadowed"
  | .toolchainShadowed => "toolchainShadowed"
  | .oleanOutsideApprovedRoot => "oleanOutsideApprovedRoot"
  | .oleanHeaderInvalid => "oleanHeaderInvalid"
  | .shareCommonImport => "shareCommonImport"
  | .shareCommonReference => "shareCommonReference"
  | .compilerOverrideHook => "compilerOverrideHook"
  | .foreignCompilerTag => "foreignCompilerTag"
  | .postponedCompilation => "postponedCompilation"
  | .opaqueTheoremStructural => "opaqueTheoremStructural"
  | .opaqueTheoremDeltaReliance => "opaqueTheoremDeltaReliance"
  | .nativeEvaluatorReachable => "nativeEvaluatorReachable"
  | .environmentLoadFailed => "environmentLoadFailed"
  | .auditFuelExhausted => "auditFuelExhausted"

structure AuditViolation where
  kind : ViolationKind
  decl : Name
  module : Name
  detail : String
  deriving Inhabited, BEq, Repr

def AuditViolation.render (v : AuditViolation) : String :=
  s!"[{v.kind.tag}] {v.decl} ({v.module}): {v.detail}"

/-- Aggregate result of one audit run. `violations` are hard failures; `policyFlags` are
findings that a policy may choose to accept (currently: structural opaque-theorem readiness
flags, which are advisory until `leanprover/lean4#14896` lands). -/
structure AuditSummary where
  modulesChecked : Nat := 0
  declsChecked : Nat := 0
  oleansChecked : Nat := 0
  axiomsSwept : Nat := 0
  hookEntriesChecked : Nat := 0
  violations : Array AuditViolation := #[]
  policyFlags : Array AuditViolation := #[]
  elapsedMs : Nat := 0
  /-- Part of `elapsedMs` spent inside `importModules` (build-library sweeps only). -/
  importMs : Nat := 0
  /-- Build-directory modules outside the closure of the swept library roots (validated by
  Vector 3 but not loaded; build-library sweeps only). -/
  strayArtifacts : Nat := 0
  /-- Rendered findings already recorded (deduplication). -/
  seen : Std.HashSet String := {}
  deriving Inhabited

def AuditSummary.merge (a b : AuditSummary) : AuditSummary :=
  { modulesChecked := max a.modulesChecked b.modulesChecked
    declsChecked := a.declsChecked + b.declsChecked
    oleansChecked := a.oleansChecked + b.oleansChecked
    axiomsSwept := a.axiomsSwept + b.axiomsSwept
    hookEntriesChecked := a.hookEntriesChecked + b.hookEntriesChecked
    violations := a.violations ++ b.violations
    policyFlags := a.policyFlags ++ b.policyFlags
    elapsedMs := a.elapsedMs + b.elapsedMs
    seen := b.seen.fold (·.insert ·) a.seen }

/-- Audit monad: an accumulating summary over `IO`. -/
abbrev AuditM := StateT AuditSummary IO

/-- Pure audit monad, used for per-module checks that run in parallel tasks. -/
abbrev PureAuditM := StateM AuditSummary

def report {m : Type → Type} [Monad m] [MonadStateOf AuditSummary m]
    (kind : ViolationKind) (decl module : Name) (detail : String) : m Unit :=
  modifyThe AuditSummary fun s =>
    let v : AuditViolation := { kind, decl, module, detail }
    let key := "V" ++ v.render
    if s.seen.contains key then s
    else { s with violations := s.violations.push v, seen := s.seen.insert key }

def flag {m : Type → Type} [Monad m] [MonadStateOf AuditSummary m]
    (kind : ViolationKind) (decl module : Name) (detail : String) : m Unit :=
  modifyThe AuditSummary fun s =>
    let v : AuditViolation := { kind, decl, module, detail }
    let key := "F" ++ v.render
    if s.seen.contains key then s
    else { s with policyFlags := s.policyFlags.push v, seen := s.seen.insert key }

/-- Fold a sub-summary (e.g. from a parallel task) into the running summary. -/
def absorb (s : AuditSummary) : AuditM Unit := do
  for v in s.violations do report v.kind v.decl v.module v.detail
  for v in s.policyFlags do flag v.kind v.decl v.module v.detail
  modify fun t => { t with
    declsChecked := t.declsChecked + s.declsChecked
    oleansChecked := t.oleansChecked + s.oleansChecked
    axiomsSwept := t.axiomsSwept + s.axiomsSwept
    hookEntriesChecked := t.hookEntriesChecked + s.hookEntriesChecked }

/-! ## Environment context -/

/-- Name roots shipped by the pinned toolchain. -/
def toolchainRoots : List Name := [`Init, `Std, `Lean, `Lake]

def isToolchainName (m : Name) : Bool := toolchainRoots.contains m.getRoot

/-- Explicit `Init.ShareCommon` surface (`leanprover/lean4#16779`). Raw names: several of these
live in the root namespace and must not be resolved against `Lean.ShareCommon`. -/
def shareCommonSymbols : List Name :=
  [`ShareCommon.StateFactoryBuilder, `ShareCommon.StateFactoryBuilder.mk,
   `ShareCommon.StateFactory, `ShareCommon.StateFactory.mk, `ShareCommon.StateFactory.mkImpl,
   `ShareCommon.StateFactoryImpl, `ShareCommon.StateFactoryPointed, `ShareCommon.State,
   `ShareCommon.State.mk, `ShareCommon.StatePointed, `ShareCommon.mkStateImpl,
   `ShareCommon.State.shareCommon, `ShareCommon.shareCommon', `ShareCommon.Object.eq,
   `ShareCommon.Object.hash, `MonadShareCommon, `MonadShareCommon.withShareCommon,
   `withShareCommon, `shareCommonM, `ShareCommonT, `ShareCommonM, `ShareCommonT.withShareCommon,
   `ShareCommonT.monadShareCommon, `ShareCommonT.run, `ShareCommonM.run]

def shareCommonModule : Name := `Init.ShareCommon

/-- What every environment audit needs to know. -/
structure AuditContext where
  env : Environment
  /-- Modules proven to be toolchain modules by name *and* canonical sysroot provenance. -/
  toolchain : NameSet
  /-- When auditing a live elaboration environment, the module its own declarations belong to. -/
  liveModule? : Option Name := none

def origin? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let m ← env.header.modules[idx.toNat]?
  return m.module

/-- Owning module of `n`: the imported module that declares it, or the live module when `n` is a
declaration of the environment being elaborated (looked up with exporting disabled so private live
declarations resolve accurately). -/
def ownerOf (ctx : AuditContext) (n : Name) : Option Name :=
  match origin? ctx.env n with
  | some m => some m
  | none =>
    let fullEnv := ctx.env.setExporting false
    if fullEnv.contains n || (IR.findEnvDecl fullEnv n).isSome then ctx.liveModule? else none

def AuditContext.isToolchainModule (ctx : AuditContext) (m : Name) : Bool :=
  ctx.toolchain.contains m

/-- One module's stored data, imported (`idx? = some i`) or synthesized for the live module by
`Lean.mkModuleData` (`idx? = none`). -/
structure ModuleView where
  module : Name
  idx? : Option Nat
  data : ModuleData

instance : Inhabited ModuleView := ⟨{ module := .anonymous, idx? := none, data := default }⟩

/-- Non-toolchain imported modules plus (in live mode) the live module itself, minus `exclude`. -/
def nonToolchainViews (ctx : AuditContext) (exclude : NameSet := {}) : IO (Array ModuleView) := do
  let env := ctx.env
  let mut out : Array ModuleView := #[]
  for h : i in [0:env.header.modules.size] do
    let m := env.header.modules[i].module
    if ctx.isToolchainModule m || exclude.contains m then continue
    let some data := env.header.moduleData[i]? | continue
    out := out.push { module := m, idx? := some i, data }
  if let some lm := ctx.liveModule? then
    let data ← mkModuleData (env.setExporting false)
    out := out.push { module := lm, idx? := none, data }
  return out

/-- Run a pure per-module check over every view in parallel (one task per module) and fold the
results back in view order. -/
def runPerView (views : Array ModuleView) (f : ModuleView → PureAuditM Unit) : AuditM Unit := do
  let tasks := views.map fun v => Task.spawn fun _ => ((f v).run {}).2
  for t in tasks do absorb t.get

/-! ## Generic fuel-bounded closure -/

def literalEdges (e : Expr) (acc : NameSet) : NameSet :=
  let acc := if (e.find? fun | .lit (.natVal _) => true | _ => false).isSome then acc.insert ``Nat else acc
  if (e.find? fun | .lit (.strVal _) => true | _ => false).isSome then acc.insert ``String else acc

def exprEdges (e : Expr) (acc : NameSet) : NameSet :=
  literalEdges e (e.getUsedConstants.foldl (·.insert ·) acc)

/-- Every constant a declaration mentions: type, value (including theorem and opaque bodies),
mutual blocks, constructors and parent inductive, recursor rules, literal types. `.proj` nodes
are covered because `Expr.getUsedConstants` returns their structure name. -/
def declEdges (ci : ConstantInfo) : NameSet := Id.run do
  let mut acc := exprEdges ci.type {}
  if let some v := ci.value? (allowOpaque := true) then acc := exprEdges v acc
  match ci with
  | .defnInfo v => acc := v.all.foldl (·.insert ·) acc
  | .thmInfo v => acc := v.all.foldl (·.insert ·) acc
  | .opaqueInfo v => acc := v.all.foldl (·.insert ·) acc
  | .inductInfo v => acc := (v.all ++ v.ctors).foldl (·.insert ·) acc
  | .ctorInfo v => acc := acc.insert v.induct
  | .recInfo v =>
    acc := v.all.foldl (·.insert ·) acc
    for r in v.rules do
      acc := exprEdges r.rhs (acc.insert r.ctor)
  | _ => pure ()
  return acc

/-- Lookup `n` across both `env.setExporting false` and `env.checked.get` so neither `isExporting`
nor uninventoried kernel-only declarations can hide dependencies. -/
def findAnyConst? (env : Environment) (n : Name) : Option ConstantInfo :=
  match (env.setExporting false).find? n with
  | some ci => some ci
  | none => env.checked.get.find? n

/-- Duplicate declarations `importModules` merges instead of rejecting. -/
def mergeableDuplicate (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.type == b.type && a.levelParams == b.levelParams &&
  match a, b with
  | .thmInfo x, .thmInfo y => x.all == y.all
  | .thmInfo x, .axiomInfo y | .axiomInfo y, .thmInfo x => x.all == [y.name] && !y.isUnsafe
  | .axiomInfo x, .axiomInfo y => x.isUnsafe == y.isUnsafe
  | _, _ => false

/-- Transitive kernel dependency closure of `roots` (roots included), plus any extra edges from
shadowed `mergeableDuplicate` module declarations. `none` = fuel exhausted. -/
def depClosure (env : Environment) (roots : Array Name) (fuel : Nat)
    (extraEdges : Std.HashMap Name NameSet := {}) : Option NameSet := Id.run do
  let fullEnv := env.setExporting false
  let kenv := env.checked.get
  let mut visited : NameSet := {}
  let mut pending : List Name := []
  for r in roots do
    unless visited.contains r do
      visited := visited.insert r
      pending := r :: pending
  for _ in [0:fuel] do
    match pending with
    | [] => return some visited
    | n :: rest =>
      pending := rest
      let ci? := match fullEnv.find? n with | some c => some c | none => kenv.find? n
      if let some ci := ci? then
        for d in declEdges ci do
          unless visited.contains d do
            visited := visited.insert d
            pending := d :: pending
      if let some ext := extraEdges[n]? then
        for d in ext do
          unless visited.contains d do
            visited := visited.insert d
            pending := d :: pending
  if pending.isEmpty then some visited else none

/-- Kernel-native evaluators: the kernel and `Meta.whnf` reduce these by running compiled code. -/
def kernelNativeEvaluators : List Name := [``Lean.reduceBool, ``Lean.reduceNat]

/-- Whether the closure of `roots` reaches a native evaluator. Fails closed (`true`) when the fuel
runs out. -/
def reachesNativeEvaluator (env : Environment) (roots : Array Name) (fuel : Nat) : Bool :=
  match depClosure env roots fuel with
  | none => true
  | some s => kernelNativeEvaluators.any s.contains

/-! ## Vector 1 — `_private` name structure -/

inductive NamePart where
  | str (s : String)
  | num (n : Nat)
  deriving BEq, Repr, Inhabited

/-- Allocation-free check whether `n` contains any `"_private"` component. -/
def hasPrivateComponent : Name → Bool
  | .anonymous => false
  | .str p s => s == "_private" || hasPrivateComponent p
  | .num p _ => hasPrivateComponent p

/-- Allocation-free check whether `n` contains any `"_at_"` specialization component. -/
def hasAtComponent : Name → Bool
  | .anonymous => false
  | .str p s => s == "_at_" || hasAtComponent p
  | .num p _ => hasAtComponent p

/-- Components of a name, root first (structural recursion on `Name`). -/
def nameParts (n : Name) : Array NamePart :=
  let rec go : Name → List NamePart → List NamePart
    | .anonymous, acc => acc
    | .str p s, acc => go p (.str s :: acc)
    | .num p k, acc => go p (.num k :: acc)
  (go n []).toArray

def partsToName (ps : List NamePart) : Name :=
  ps.foldl (fun acc p => match p with | .str s => acc.str s | .num n => acc.num n) .anonymous

/-- Decoded `_private.<module>.0.<user>` name. -/
structure PrivateNameView where
  module : Name
  user : Name
  deriving BEq, Repr, Inhabited

inductive PrivateNameError where
  | nonLeadingPrivate
  | nestedPrivate
  | missingSeparator
  | nonZeroSeparator (k : Nat)
  | numericModuleSegment (k : Nat)
  | emptyModule
  | emptyModuleComponent
  | emptyUser
  | emptyUserComponent
  | leadingNumericUser (k : Nat)
  deriving BEq, Repr, Inhabited

def PrivateNameError.render : PrivateNameError → String
  | .nonLeadingPrivate => "`_private` component is not the leading component"
  | .nestedPrivate => "nested `_private` component"
  | .missingSeparator => "missing numeric `.0` separator"
  | .nonZeroSeparator k => s!"non-zero numeric separator `.{k}`"
  | .numericModuleSegment k => s!"numeric segment `.{k}` inside the module part"
  | .emptyModule => "empty module part"
  | .emptyModuleComponent => "empty string component inside the module part"
  | .emptyUser => "empty user suffix"
  | .emptyUserComponent => "empty string component inside the user suffix"
  | .leadingNumericUser k => s!"leading numeric segment `.{k}` in user suffix (double separator)"

def privateMarker : NamePart := .str "_private"

/-- Structural parser for Lean's `mkPrivateName` encoding `_private.<mod>.0.<user>`.
`.ok none` means the name has no `_private` component at all. -/
def parsePrivateName (n : Name) : Except PrivateNameError (Option PrivateNameView) :=
  if !hasPrivateComponent n then .ok none
  else
    let ps := (nameParts n).toList
    let markers := ps.filter (· == privateMarker)
    match ps with
    | p :: rest =>
      if p != privateMarker then .error .nonLeadingPrivate
      else if markers.length > 1 then .error .nestedPrivate
      else
        let modParts := rest.takeWhile (fun | .str _ => true | .num _ => false)
        let after := rest.drop modParts.length
        match after with
        | [] => .error .missingSeparator
        | .str _ :: _ => .error .missingSeparator
        | .num k :: userParts =>
          if modParts.isEmpty then .error .emptyModule
          else if modParts.contains (.str "") then .error .emptyModuleComponent
          else if k != 0 then
            if userParts.contains (.num 0) then .error (.numericModuleSegment k)
            else .error (.nonZeroSeparator k)
          else match userParts with
            | [] => .error .emptyUser
            | .num uk :: _ => .error (.leadingNumericUser uk)
            | _ =>
              if userParts.contains (.str "") then .error .emptyUserComponent
              else .ok (some { module := partsToName modParts, user := partsToName userParts })
    | [] => .ok none

/-- Constants whose names are reserved for the kernel, foundations, `Init.ShareCommon`, compiler
intrinsics (`ConstantFold.builtinFolders`, `builtinRuntimeTypes`), or native evaluation. -/
def reservedConstantNames : NameSet := Id.run do
  let mut s : NameSet := {}
  for (k, _) in Compiler.LCNF.Simp.ConstantFold.builtinFolders.toList do
    s := s.insert k
  for k in Compiler.LCNF.builtinRuntimeTypes do
    s := s.insert k
  for k in shareCommonSymbols do
    s := s.insert k
  let extras : List Name :=
    [`sorryAx, ``propext, ``Quot.sound, ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind, ``Quot.lcInv,
     ``Classical.choice, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler,
     ``Lean.reduceBool, ``Lean.reduceNat, ``Eq, ``Eq.rec, ``Eq.refl, ``Eq.recOn, ``Eq.ndrec,
     ``Eq.ndrecOn, ``HEq, ``HEq.refl, ``HEq.rec, ``HEq.ndrec, ``Acc.rec, ``False, ``False.rec,
     ``Empty, ``Empty.rec, ``And, ``And.rec, ``Iff, ``Iff.rec,
     ``lcUnreachable, ``lcProof, ``lcCast, ``lcErased, ``lcAny, ``lcVoid,
     ``Decidable, ``Decidable.isTrue, ``Decidable.isFalse, ``Decidable.decide,
     ``Bool, ``Bool.true, ``Bool.false, ``Nat, ``Nat.zero, ``Nat.succ, ``String,
     ``Array.getInternalBorrowed, ``Array.get!InternalBorrowed, ``Array.ugetBorrowed,
     ``OfNat, ``OfNat.ofNat]
  for k in extras do s := s.insert k
  return s

/-- Root namespaces reserved for foundational, native-evaluation, or `ShareCommon` machinery
outside `toolchainRoots`. -/
def reservedSpoofRoots : List Name := [`ShareCommon, `sorryAx, `Quot, `Classical]

/-- Namespaces that carry trust: a private declaration may use one as its user suffix only when
its own module is in the same namespace. -/
def privilegedRoots : List Name := [`Trusted, `Assumptions, `Verify, `CrateVerify]

/-- Split a name at `_at_` components (the compiler's specialization encoding
`<key>._at_.<context>.spec_<n>`). -/
def splitAtSegments (n : Name) : List Name :=
  let rec go : List NamePart → List NamePart → List Name
    | [], cur => [partsToName cur.reverse]
    | p :: ps, cur => if p == .str "_at_" then partsToName cur.reverse :: go ps [] else go ps (p :: cur)
  go (nameParts n).toList []

def isDigits (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

def hasNumSuffix (s pre : String) : Bool := s.startsWith pre && isDigits (s.drop pre.length).toString

def isDigitsOrUnderscore (s : String) : Bool :=
  !s.isEmpty && (s.any Char.isDigit) && s.all fun c => c.isDigit || c == '_'

def hasIndexedSuffix (s pre : String) : Bool :=
  s.startsWith pre && isDigitsOrUnderscore (s.drop pre.length).toString

/-- Exact closed set of components Lean 4.34.1 appends when realizing auxiliary declarations or
compiler stages of an existing declaration (matcher equations/splitters, equation/unfolding lemmas,
functional induction/cases principles, reduced-arity/boxed/sparse-cases compiler helpers). Never
admits arbitrary `_`-prefixed names. -/
def isRealizedAuxComponent : NamePart → Bool
  | .str s =>
    hasNumSuffix s "eq_" || hasNumSuffix s "match_" || hasNumSuffix s "proof_" ||
    hasNumSuffix s "congr_eq_" || hasIndexedSuffix s "_sparseCasesOn_" ||
    hasNumSuffix s "_closed_" || hasNumSuffix s "_boxed_const_" ||
    hasIndexedSuffix s "_lam_" || hasIndexedSuffix s "_lambda_" ||
    hasIndexedSuffix s "_elam_" || hasIndexedSuffix s "_jp_" || hasIndexedSuffix s "_rec_" ||
    ["eq_def", "eq_unfold", "congr_simp", "splitter", "induct", "induct_unfolding",
     "fun_cases", "fun_cases_unfolding", "_redArg", "_boxed", "_unfold", "_sunfold",
     "_cstage1", "_cstage2", "_unary", "_mutual", "_flat_parse"].contains s
  | .num _ => false

/-- Trailing components produced by `LCNF.Specialize` after `<ctxDecl>` in `<key>._at_.<ctxDecl>.spec_<n>...`. -/
def isSpecTrailComponent : NamePart → Bool
  | .str s => hasNumSuffix s "spec_" || isRealizedAuxComponent (.str s)
  | .num _ => false

def hasNativePart (n : Name) : Bool :=
  (nameParts n).any fun | .str s => s == "_native" || s.startsWith "_native" | .num _ => false

/-- A private user suffix that is a realized auxiliary of an existing declaration: `fullName` itself
is never an axiom or opaque constant, some proper prefix `base` of `user` is an imported constant
whose owning module satisfies `baseOwnerOk`, and every remaining component is in the closed
`isRealizedAuxComponent` set. -/
def isRealizedAuxOfForeign (ctx : AuditContext) (fullName owner user : Name) (baseOwnerOk : Name → Bool) : Bool :=
  match findAnyConst? ctx.env fullName with
  | some (.axiomInfo _) | some (.opaqueInfo _) => false
  | _ =>
    let ps := (nameParts user).toList
    (List.range ps.length).any fun k =>
      k > 0 &&
      let rest := ps.drop k
      !rest.isEmpty && rest.all isRealizedAuxComponent &&
      let base := partsToName (ps.take k)
      ((match origin? ctx.env base with
        | some bm => baseOwnerOk bm
        | none => false) ||
       (let privCands := (Name.mkNum (`_private ++ owner) 0 ++ base, owner) :: (List.range k).filterMap fun j =>
          if j == 0 then none else
          let mod := partsToName (ps.take j)
          some (Name.mkNum (`_private ++ mod) 0 ++ base, mod)
        privCands.any fun (pn, mod) =>
          match origin? ctx.env pn with
          | some bm => bm == mod && baseOwnerOk bm
          | none => false))

/-- User-suffix spoofing check for a private name `fullName` owned by non-toolchain module `owner`.
Realized auxiliaries of genuine toolchain / privileged declarations are permitted only when their
trailing suffix consists strictly of closed `isRealizedAuxComponent` markers on a non-axiom. -/
def userSuffixSpoof? (ctx : AuditContext) (fullName owner : Name) (v : PrivateNameView) : Option String :=
  let root := v.user.getRoot
  if hasNativePart v.user then
    some s!"user suffix {v.user} spoofs a native-evaluation identifier"
  else if reservedConstantNames.contains v.user then
    some s!"user suffix {v.user} spoofs a reserved foundational / compiler / ShareCommon constant"
  else if root == `ShareCommon || root == `sorryAx then
    some s!"user suffix {v.user} is under reserved root {root}"
  else if reservedSpoofRoots.contains root then
    if isRealizedAuxOfForeign ctx fullName owner v.user (fun bm => ctx.isToolchainModule bm || bm == owner) then none
    else some s!"user suffix {v.user} is under reserved root {root}"
  else if isToolchainName v.user then
    if isRealizedAuxOfForeign ctx fullName owner v.user (fun bm => ctx.isToolchainModule bm || bm == owner) then none
    else some s!"user suffix {v.user} is under a reserved toolchain root"
  else if privilegedRoots.contains root && owner.getRoot != root then
    if isRealizedAuxOfForeign ctx fullName owner v.user (fun bm => (bm.getRoot == root && !ctx.isToolchainModule bm) || bm == owner) then none
    else some s!"user suffix {v.user} spoofs privileged namespace {root} from module {owner}"
  else none

/-- Validate the final `<ctxDecl>.spec_<n>...` segment of a multi-segment `_at_` specialization
name declared in `owner`'s `extraConstNames`. -/
def checkSpecContextSegment (ctx : AuditContext) (owner fullName seg : Name) : PureAuditM Unit := do
  let ps := (nameParts seg).toList
  let hasSpec := ps.any fun | .str s => hasNumSuffix s "spec_" | .num _ => false
  unless hasSpec do
    report .privateModuleMismatch fullName owner
      s!"specialization context segment {seg} has no `.spec_<n>` suffix"
    return
  let matchedPrefix? := (List.range ps.length).find? fun k =>
    k > 0 &&
    let base := partsToName (ps.take k)
    let rest := ps.drop k
    (rest.any fun | .str s => hasNumSuffix s "spec_" | .num _ => false) &&
    rest.all isSpecTrailComponent &&
    ownerOf ctx base == some owner
  match matchedPrefix? with
  | none =>
    report .privateModuleMismatch fullName owner
      s!"specialization context segment {seg} does not belong to declaring module {owner}"
  | some k =>
    let base := partsToName (ps.take k)
    match parsePrivateName base with
    | .error e => report .malformedPrivateName fullName owner e.render
    | .ok none => pure ()
    | .ok (some v) =>
      unless v.module == owner do
        report .privateModuleMismatch fullName owner
          s!"specialization context {base} embeds module {v.module}, expected {owner}"
      if let some why := userSuffixSpoof? ctx base owner v then
        report .privateUserSuffixSpoof fullName owner why

/-- Check one name owned by non-toolchain module `owner`. `isIROnly` names (extra constant names
created by the code generator) may carry the `<key>._at_.<ctx>.spec_<n>` specialization encoding,
where every key segment must resolve to its owner and the final context segment must belong to
`owner`. -/
def checkPrivateName (ctx : AuditContext) (owner : Name) (n : Name) (isIROnly : Bool) : PureAuditM Unit := do
  if !hasPrivateComponent n && !(isIROnly && hasAtComponent n) then return
  if isIROnly && hasAtComponent n then
    let segs := splitAtSegments n
    if segs.any (·.isAnonymous) || segs.length < 2 then
      report .malformedPrivateName n owner "empty segment in `_at_` specialization name"
      return
    let mut i := 0
    for seg in segs do
      let isKey := i + 1 < segs.length
      i := i + 1
      if isKey then
        match parsePrivateName seg with
        | .error e => report .malformedPrivateName n owner e.render
        | .ok none =>
          unless (ownerOf ctx seg).isSome do
            report .privateModuleMismatch n owner s!"specialization key {seg} does not resolve to an existing declaration"
        | .ok (some v) =>
          unless ownerOf ctx seg == some v.module do
            report .privateModuleMismatch n owner
              s!"specialization key {seg} does not resolve to a declaration of {v.module}"
      else
        match parsePrivateName seg with
        | .error e => report .malformedPrivateName n owner e.render
        | .ok _ => checkSpecContextSegment ctx owner n seg
  else
    match parsePrivateName n with
    | .error e => report .malformedPrivateName n owner e.render
    | .ok none => pure ()
    | .ok (some v) =>
      unless v.module == owner do
        report .privateModuleMismatch n owner s!"embedded module {v.module} is not the declaring module {owner}"
      if let some why := userSuffixSpoof? ctx n owner v then
        report .privateUserSuffixSpoof n owner why

/-- Structural `_private` validation on an arbitrary constant name referenced by a compiler-hook
extension entry (which may legitimately reference an imported declaration from another module, e.g.
the RHS of `@[csimp]`, but must never carry a malformed `_private` encoding or unowned/forged
embedded module). -/
def checkExtensionRefName (ctx : AuditContext) (storingMod : Name) (n : Name) (mustOwn : Bool) :
    PureAuditM Unit := do
  if !hasPrivateComponent n && !(mustOwn && hasAtComponent n) then return
  if mustOwn then
    checkPrivateName ctx storingMod n (hasAtComponent n)
  else
    match parsePrivateName n with
    | .error e => report .malformedPrivateName n storingMod s!"extension target: {e.render}"
    | .ok none => pure ()
    | .ok (some v) =>
      match ownerOf ctx n with
      | some actualOwner =>
        unless actualOwner == v.module do
          report .privateModuleMismatch n storingMod
            s!"extension target embeds {v.module} but is owned by {actualOwner}"
        if !ctx.isToolchainModule actualOwner then
          if let some why := userSuffixSpoof? ctx n actualOwner v then
            report .privateUserSuffixSpoof n storingMod s!"extension target: {why}"
      | none =>
        report .privateModuleMismatch n storingMod
          s!"extension target {n} embeds {v.module} but does not resolve in environment"

/-- Vector 1 over every non-toolchain module (and the live module): stored `constNames` and
`constants`, IR-only `extraConstNames`, kernel-only constants, and declaration names targeted by
compiler-hook extension entries. -/
def auditPrivateNames (ctx : AuditContext) (views : Array ModuleView) : AuditM Unit := do
  let env := ctx.env
  runPerView views fun v => do
    let m := v.module
    let aligned : Bool := Id.run do
      unless v.data.constNames.size == v.data.constants.size do return false
      for idx in [0:v.data.constNames.size] do
        if v.data.constNames[idx]! != v.data.constants[idx]!.name then return false
      return true
    for n in v.data.constNames do
      checkPrivateName ctx m n false
    let mut totalChecked := v.data.constNames.size + v.data.extraConstNames.size
    unless aligned do
      report .environmentLoadFailed m m "module constNames array differs from stored constants array"
      let mut seenConsts : NameSet := v.data.constNames.foldl (·.insert ·) {}
      for ci in v.data.constants do
        unless seenConsts.contains ci.name do
          seenConsts := seenConsts.insert ci.name
          totalChecked := totalChecked + 1
          checkPrivateName ctx m ci.name false
    for n in v.data.extraConstNames do
      checkPrivateName ctx m n true
    -- Extension targets stored by this module (`.olean` + `.ir`).
    if let some i := v.idx? then
      for (src, tgt) in Compiler.implementedByAttr.ext.getModuleEntries env i ++ Compiler.implementedByAttr.ext.getModuleIREntries env i do
        checkExtensionRefName ctx m src true
        checkExtensionRefName ctx m tgt false
      for (n, _) in externAttr.ext.getModuleEntries env i ++ externAttr.ext.getModuleIREntries env i do
        checkExtensionRefName ctx m n true
      for (n, _) in exportAttr.ext.getModuleEntries env i ++ exportAttr.ext.getModuleIREntries env i do
        checkExtensionRefName ctx m n true
      for (n, fn) in regularInitAttr.ext.getModuleEntries env i ++ regularInitAttr.ext.getModuleIREntries env i do
        checkExtensionRefName ctx m n true
        unless fn.isAnonymous do checkExtensionRefName ctx m fn false
      for (n, fn) in builtinInitAttr.ext.getModuleEntries env i ++ builtinInitAttr.ext.getModuleIREntries env i do
        checkExtensionRefName ctx m n true
        unless fn.isAnonymous do checkExtensionRefName ctx m fn false
      for e in Compiler.CSimp.ext.ext.getModuleEntries env i ++ Compiler.CSimp.ext.ext.getModuleIREntries env i do
        let ent := match e with | .global a => a | .scoped _ a => a
        checkExtensionRefName ctx m ent.fromDeclName false
        checkExtensionRefName ctx m ent.toDeclName false
        checkExtensionRefName ctx m ent.thmName false
      for installer in Compiler.LCNF.passManagerExt.getModuleEntries env i ++ Compiler.LCNF.passManagerExt.getModuleIREntries env i do
        checkExtensionRefName ctx m installer false
      for fe in Compiler.LCNF.Simp.ConstantFold.folderExt.getModuleEntries env i ++ Compiler.LCNF.Simp.ConstantFold.folderExt.getModuleIREntries env i do
        checkExtensionRefName ctx m fe.declName false
        checkExtensionRefName ctx m fe.folderDeclName false
      for n in IR.UnboxResult.unboxAttr.ext.getModuleEntries env i ++ IR.UnboxResult.unboxAttr.ext.getModuleIREntries env i do
        checkExtensionRefName ctx m n true
      for n in neverExtractAttr.ext.getModuleEntries env i ++ neverExtractAttr.ext.getModuleIREntries env i do
        checkExtensionRefName ctx m n true
      for (n, _) in Compiler.inlineAttrs.ext.getModuleEntries env i ++ Compiler.inlineAttrs.ext.getModuleIREntries env i do
        checkExtensionRefName ctx m n true
      for entry in Compiler.LCNF.postponedCompileDeclsExt.getModuleEntries env i ++ Compiler.LCNF.postponedCompileDeclsExt.getModuleIREntries env i do
        for n in entry.declNames do checkExtensionRefName ctx m n true
      for n in auxRecExt.getModuleEntries env i ++ auxRecExt.getModuleIREntries env i do
        checkExtensionRefName ctx m n true
      for (n, _) in noConfusionExt.getModuleEntries env i ++ noConfusionExt.getModuleIREntries env i do
        checkExtensionRefName ctx m n true
      for n in sparseCasesOnExt.getModuleEntries env i ++ sparseCasesOnExt.getModuleIREntries env i do
        checkExtensionRefName ctx m n true
      for n in Compiler.LCNF.taggedReturnAttr.ext.getModuleEntries env i ++
          Compiler.LCNF.taggedReturnAttr.ext.getModuleIREntries env i do
        checkExtensionRefName ctx m n true
      for se in Compiler.LCNF.Specialize.specCacheExt.getModuleEntries env i ++
          Compiler.LCNF.Specialize.specCacheExt.getModuleIREntries env i do
        checkExtensionRefName ctx m se.declName true
      for sig in Compiler.LCNF.impureSigExt.getModuleEntries env i ++ Compiler.LCNF.impureSigExt.getModuleIREntries env i do
        checkExtensionRefName ctx m sig.name true
      for (dn, _) in Compiler.LCNF.UnreachableBranches.functionSummariesExt.getModuleEntries env i ++
          Compiler.LCNF.UnreachableBranches.functionSummariesExt.getModuleIREntries env i do
        checkExtensionRefName ctx m dn true
      for di in Meta.defaultInstanceExtension.getModuleEntries env i ++ Meta.defaultInstanceExtension.getModuleIREntries env i do
        checkExtensionRefName ctx m di.className false
        checkExtensionRefName ctx m di.instanceName false
      for d in Compiler.LCNF.baseExt.getModuleEntries env i do checkExtensionRefName ctx m d.name true
      for d in Compiler.LCNF.baseExt.getModuleIREntries env i do checkExtensionRefName ctx m d.name true
      for d in Compiler.LCNF.monoExt.getModuleEntries env i do checkExtensionRefName ctx m d.name true
      for d in Compiler.LCNF.monoExt.getModuleIREntries env i do checkExtensionRefName ctx m d.name true
      for d in IR.declMapExt.getModuleEntries env i do checkExtensionRefName ctx m d.name true
      for d in IR.declMapExt.getModuleIREntries env i do checkExtensionRefName ctx m d.name true
    modify fun s => { s with declsChecked := s.declsChecked + totalChecked }
  -- Live `env.constants.map₂` and live extension targets.
  if let some lm := ctx.liveModule? then
    let ((), s) := (do
      for (n, _) in ctx.env.constants.map₂.toList do
        checkPrivateName ctx lm n false
      for e in Compiler.CSimp.ext.ext.getState env |>.newEntries do
        let ent := match e with | .global a => a | .scoped _ a => a
        checkExtensionRefName ctx lm ent.fromDeclName false
        checkExtensionRefName ctx lm ent.toDeclName false
        checkExtensionRefName ctx lm ent.thmName false
      for n in auxRecExt.getEntries env do
        if (origin? env n).isNone then checkExtensionRefName ctx lm n true
      for (n, _) in (noConfusionExt.getState env).toList do
        if (origin? env n).isNone then checkExtensionRefName ctx lm n true
      for n in sparseCasesOnExt.getEntries env do
        if (origin? env n).isNone then checkExtensionRefName ctx lm n true
      for (_, dn) in (Compiler.LCNF.Specialize.specCacheExt.getState env).toList do
        checkExtensionRefName ctx lm dn true : PureAuditM Unit).run {}
    absorb s
  -- Kernel stage-2 constants not covered by `map₁` (defense against direct kernel injection).
  let nonToolSet : NameSet := views.foldl (fun acc v => acc.insert v.module) {}
  let kenv := env.checked.get
  let (_, ks) := (do
    let stage2 := kenv.constants.foldStage2 (fun acc n _ => acc.push n) #[]
    for n in stage2 do
      let om := (ownerOf ctx n).getD env.header.mainModule
      if nonToolSet.contains om || ctx.liveModule?.isSome then
        checkPrivateName ctx om n false : PureAuditM Unit).run {}
  absorb ks

/-! ## Vector 2 — whole-environment axiom sweep -/

structure AxiomPolicy where
  allowClassicalChoice : Bool := true
  allowAssumptions : Bool := false
  allowedAssumptions : NameSet := {}
  allowedAssumptionModules : NameSet := {}
  closureFuel : Nat := 2000000
  /-- Whole-module audits (`roots? = none`) of at most this many constants compute the exact
  dependency closure; larger ones screen every non-toolchain declaration's direct references to
  forbidden toolchain axioms inside the shared kernel traversal (non-toolchain axioms are always
  reported, reachable or not). -/
  implicitClosureMaxConsts : Nat := 5000
  deriving Inhabited

/-- Foundational axioms, admitted only together with their declaring toolchain module. -/
def foundationalAxioms (p : AxiomPolicy) : List (Name × Name) :=
  [(``propext, `Init.Core), (``Quot.sound, `Init.Prelude)] ++
    (if p.allowClassicalChoice then [(``Classical.choice, `Init.Prelude)] else [])

def isSorryOrNativeName (n : Name) : Bool :=
  n == ``sorryAx || [``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler].contains n ||
  hasNativePart n ||
  (match parsePrivateName n with
   | .ok (some v) => reservedConstantNames.contains v.user || hasNativePart v.user
   | _ => false)

def isFoundationalOk (ctx : AuditContext) (p : AxiomPolicy) (n : Name) : Bool :=
  match origin? ctx.env n with
  | some m => ctx.isToolchainModule m && (foundationalAxioms p).contains (n, m)
  | none => false

/-- Strict module-bound assumption check: `n` is admitted in module `m` iff `allowAssumptions` holds,
`m` is the actual owner of `n` (`ownerOf ctx n == some m`), `m` is a non-toolchain `Assumptions.*`
module, `n` is under `Assumptions.*` and not `_private`-encoded, and `n` or `m` is allowlisted. -/
def isAssumptionOkInModule (ctx : AuditContext) (p : AxiomPolicy) (n m : Name) : Bool :=
  p.allowAssumptions &&
  ownerOf ctx n == some m &&
  !ctx.isToolchainModule m &&
  m.getRoot == `Assumptions &&
  n.getRoot == `Assumptions &&
  (p.allowedAssumptions.contains n || p.allowedAssumptionModules.contains m) &&
  (parsePrivateName n matches .ok none)

def isAssumptionOk (ctx : AuditContext) (p : AxiomPolicy) (n : Name) : Bool :=
  match ownerOf ctx n with
  | some m => isAssumptionOkInModule ctx p n m
  | none => false

/-- Whether an environment provably exposes all private declarations of every non-toolchain module:
`isExporting` is `false`, and if `header.isModule` is set then every non-toolchain import is an
`import all`. -/
def privateDataLoaded (ctx : AuditContext) : Bool :=
  !ctx.env.isExporting &&
  (!ctx.env.header.isModule ||
   ctx.env.header.modules.all fun mi => ctx.isToolchainModule mi.module || mi.importAll)

/-- Vector 2. Sweeps every axiom across `moduleData`, live `map₂`, and `env.checked.get`, fails
closed on any exporting view, rejects non-toolchain re-declarations of foundational or foreign
`Assumptions.*` axioms, and classifies every reachable and unreferenced axiom. -/
def auditUnreferencedAxioms (ctx : AuditContext) (views : Array ModuleView) (p : AxiomPolicy)
    (roots? : Option (Array Name)) : AuditM Unit := do
  let rawEnv := ctx.env
  unless rawEnv.header.modules.size == rawEnv.header.moduleData.size do
    report .environmentLoadFailed .anonymous rawEnv.header.mainModule
      "environment modules and moduleData arrays have different sizes"
    return
  unless privateDataLoaded ctx do
    report .exportedOnlyEnvironment .anonymous rawEnv.header.mainModule
      "exporting or module-system environment without private data loaded: private axioms may be hidden"
    return
  let env := rawEnv.setExporting false
  -- Inventory: (i) every module's stored constants, (ii) synthesized live module view, (iii) live `map₂`.
  let mut inventory : NameSet := {}
  let mut candidates : Array (Name × Name) := #[]
  let mut candPairs : Std.HashSet (Name × Name) := {}
  let pushCand (n m : Name) (cands : Array (Name × Name)) (pairs : Std.HashSet (Name × Name)) :
      Array (Name × Name) × Std.HashSet (Name × Name) :=
    if pairs.contains (n, m) then (cands, pairs)
    else (cands.push (n, m), pairs.insert (n, m))
  for h : i in [0:env.header.moduleData.size] do
    let d := env.header.moduleData[i]
    let m := (env.header.modules[i]?.map (·.module)).getD .anonymous
    let isTool := ctx.isToolchainModule m
    for ci in d.constants do
      if let .axiomInfo _ := ci then
        inventory := inventory.insert ci.name
        unless isTool do
          let (c', p') := pushCand ci.name m candidates candPairs
          candidates := c'; candPairs := p'
  for v in views do
    if v.idx?.isNone then
      for ci in v.data.constants do
        if let .axiomInfo _ := ci then
          inventory := inventory.insert ci.name
          let (c', p') := pushCand ci.name v.module candidates candPairs
          candidates := c'; candPairs := p'
  for (n, ci) in env.constants.map₂.toList do
    if let .axiomInfo _ := ci then
      inventory := inventory.insert n
      let owner := (ownerOf ctx n).getD env.header.mainModule
      let (c', p') := pushCand n owner candidates candPairs
      candidates := c'; candPairs := p'
  -- (iv) kernel environment: every axiom in stage 1 and stage 2 must be inventoried.
  let kenv := env.checked.get
  let kernelAxioms : Array Name :=
    kenv.constants.foldStage2 (fun acc n ci => if ci matches .axiomInfo _ then acc.push n else acc)
      (kenv.constants.map₁.fold (fun acc n ci => if ci matches .axiomInfo _ then acc.push n else acc) #[])
  for n in kernelAxioms do
    unless inventory.contains n do
      let owner := (ownerOf ctx n).getD env.header.mainModule
      report .uninventoriedKernelAxiom n owner "axiom present in the kernel environment but in no module inventory"
      inventory := inventory.insert n
      unless ctx.isToolchainModule owner do
        let (c', p') := pushCand n owner candidates candPairs
        candidates := c'; candPairs := p'
  modify fun s => { s with axiomsSwept := s.axiomsSwept + candidates.size }
  -- Verify shadowed `moduleData` constants against the active environment in parallel across views
  -- and record any extra dependency edges from shadowed `mergeableDuplicate` proofs so co-imported
  -- duplicate equation / auxiliary theorems cannot hide unapproved axiom references.
  let hasMap2 := !env.constants.map₂.isEmpty
  let dupTasks := views.map fun v => Task.spawn fun _ => Id.run do
    let mut errs : Array (Name × Name × String) := #[]
    let mut edges : Array (Name × NameSet) := #[]
    if let some modIdx := v.idx? then
      for ci in v.data.constants do
        if env.getModuleIdxFor? ci.name != some modIdx || (hasMap2 && env.constants.map₂.contains ci.name) then
          match findAnyConst? env ci.name with
          | none =>
            errs := errs.push (ci.name, v.module, "declaration present in moduleData is missing from the environment")
          | some stored =>
            if mergeableDuplicate stored ci then
              edges := edges.push (ci.name, declEdges ci)
            else
              errs := errs.push (ci.name, v.module, "shadowed declaration in moduleData is not a mergeable duplicate")
    return (errs, edges)
  let mut extraEdges : Std.HashMap Name NameSet := {}
  for dt in dupTasks do
    let (errs, edges) := dt.get
    for (dn, dm, msg) in errs do
      report .environmentLoadFailed dn dm msg
    for (dn, es) in edges do
      extraEdges := extraEdges.insert dn (extraEdges.getD dn {} ++ es)
  -- Reachability: when `roots?` is `some roots`, close `roots`; when `roots?` is `none` and the
  -- audited view set is moderate (`≤ 5000` constants) or `allowClassicalChoice` is disabled, seed
  -- reachability from all non-axiom declarations in `views` + `map₂` (leaving unused axioms out of
  -- `reachable` while catching `sorryAx`, `ofReduceBool`, `Classical.choice`, and shadowed proofs).
  -- Larger fast sweeps with `allowClassicalChoice = true` screen non-foundational toolchain axioms
  -- in C++ inside `kernelScanChunk`.
  let viewConstCount := views.foldl (fun acc v => acc + v.data.constants.size) 0 +
    env.constants.map₂.toList.length
  let reachable ← match roots? with
    | some roots =>
      match depClosure env roots p.closureFuel extraEdges with
      | some s => pure s
      | none =>
        report .auditFuelExhausted .anonymous env.header.mainModule "axiom reachability closure exhausted its fuel"
        return
    | none =>
      if viewConstCount ≤ p.implicitClosureMaxConsts || !p.allowClassicalChoice then
        let mut seedSet : NameSet := {}
        for v in views do
          for ci in v.data.constants do
            unless ci matches .axiomInfo _ do
              seedSet := seedSet ++ declEdges ci
        for (_, ci) in env.constants.map₂.toList do
          unless ci matches .axiomInfo _ do
            seedSet := seedSet ++ declEdges ci
        match depClosure env seedSet.toArray p.closureFuel extraEdges with
        | some s => pure s
        | none =>
          report .auditFuelExhausted .anonymous env.header.mainModule "axiom reachability closure exhausted its fuel"
          return
      else
        pure ({} : NameSet)
  -- Reachable axioms (any origin, checking both `env` and `kenv`).
  let mut confirmedReachable : Std.HashSet (Name × Name) := {}
  for n in reachable do
    let some ci := findAnyConst? env n | continue
    unless ci matches .axiomInfo _ do continue
    let om := (ownerOf ctx n).getD .anonymous
    confirmedReachable := confirmedReachable.insert (n, om)
    if isFoundationalOk ctx p n || isAssumptionOkInModule ctx p n om then continue
    report .referencedUnapprovedAxiom n om "axiom reachable from a checked root is not admitted"
  -- Every non-toolchain candidate `(n, m)` is judged against its storing module `m` directly, so a
  -- non-toolchain module re-declaring `propext` or a foreign `Assumptions.*` axiom cannot hide
  -- behind the primary owner's allowlist entry or behind `reachable.contains n` when `n` was
  -- omitted from `constNames`.
  for (n, m) in candidates do
    if confirmedReachable.contains (n, m) then continue
    if isAssumptionOkInModule ctx p n m then continue
    if reachable.contains n then
      report .referencedUnapprovedAxiom n m
        "non-toolchain axiom in reachable set is unapproved or re-declares a foreign axiom"
    else if isSorryOrNativeName n then
      report .unreferencedSorryOrNativeAxiom n m "unreferenced sorryAx-class / native-evaluation axiom"
    else if m.getRoot == `Assumptions then
      report .unreferencedAssumptionAxiom n m "unreferenced assumption axiom is not admitted"
    else
      report .unreferencedTopLevelAxiom n m "unreferenced top-level axiom"

/-! ## Vector 3 — paths, shadowing, binary headers -/

/-- Errors of the pure `.olean` header / compacted-region validator. -/
inductive OleanHeaderError where
  | tooShort (size : Nat)
  | tooLarge (size max : Nat)
  | badMagic
  | badFormatVersion (v : Nat)
  | badFlags (f : Nat)
  | badVersionString (why : String)
  | versionMismatch (got expected : String)
  | badGithash
  | githashMismatch (got expected : String)
  | zeroBaseAddr
  | misalignedBaseAddr (b : Nat)
  | baseAddrWraps
  | misalignedDataSize (size : Nat)
  | scalarRootPtr (r : Nat)
  | misalignedRootPtr (r : Nat)
  | rootOutOfBounds (r : Nat)
  | rootRcNonzero (rc : Nat)
  | rootNotConstructor (tag : Nat)
  | rootSizeInvalid (sz : Nat)
  | rootChildInvalid (fieldIdx : Nat) (why : String)
  | overlappingParentRegion (base size : Nat)
  deriving BEq, Repr, Inhabited

def OleanHeaderError.render : OleanHeaderError → String
  | .tooShort s => s!"file too short ({s} bytes)"
  | .tooLarge s m => s!"file size {s} exceeds limit {m}"
  | .badMagic => "bad magic (expected \"olean\")"
  | .badFormatVersion v => s!"unsupported format version {v}"
  | .badFlags f => s!"unknown flag bits {f}"
  | .badVersionString why => s!"malformed Lean version string: {why}"
  | .versionMismatch g e => s!"Lean version {g} does not match pinned {e}"
  | .badGithash => "githash is not 40 lowercase hex characters"
  | .githashMismatch g e => s!"githash {g} does not match pinned {e}"
  | .zeroBaseAddr => "base address is zero"
  | .misalignedBaseAddr b => s!"base address {b} is not 8-byte aligned"
  | .baseAddrWraps => "base address + file size wraps around 2^64"
  | .misalignedDataSize s => s!"data size of a {s}-byte file is not 8-byte aligned"
  | .scalarRootPtr r => s!"root pointer {r} is a scalar"
  | .misalignedRootPtr r => s!"root pointer {r} is not 8-byte aligned"
  | .rootOutOfBounds r => s!"root pointer {r} is outside the compacted region"
  | .rootRcNonzero rc => s!"root object has nonzero reference count {rc} (not compacted)"
  | .rootNotConstructor t => s!"root object tag {t} is not a constructor"
  | .rootSizeInvalid sz => s!"root object size {sz} is invalid"
  | .rootChildInvalid idx why => s!"root object field #{idx} invalid: {why}"
  | .overlappingParentRegion b sz => s!"compacted region [{b}, {b + sz}) overlaps an earlier region in the same chain"

structure OleanHeaderConfig where
  expectedVersion? : Option String := some "4.34.1"
  expectedGithash? : Option String := some "5045d0056413266e57c625dcd7c365b10e377c52"
  maxBytes : Nat := 512 * 1024 * 1024
  /-- Delta parts (`.olean.server`, `.olean.private`, `.ir`) layer on top of an earlier compacted
  region mapped below `baseAddr`, so root field pointers `< baseAddr` (non-null, 8-byte aligned)
  legitimately target the parent region; base `.olean` and `.ir.sig` parts set this `false`. -/
  allowParentRegionPtrs : Bool := false
  /-- Exact `(baseAddr, fileSize)` bounds of earlier compacted regions in the same layered chain.
  When non-empty, `[baseAddr, baseAddr + fileSize)` must be disjoint from every parent region and
  any parent pointer `< baseAddr` must fall inside `[pBase + 96, pBase + pSize)` of a parent. -/
  parentRegions : Array (Nat × Nat) := #[]
  /-- Optional parent regions from an accompanying compacted chain (e.g. `.olean*` when validating
  `.ir`) that `< baseAddr` pointers may also target without sharing the primary overlap set. -/
  auxParentRegions : Array (Nat × Nat) := #[]
  deriving Inhabited

structure OleanHeaderInfo where
  version : String
  githash : String
  gmp : Bool
  baseAddr : Nat
  rootPtr : Nat
  rootOffset : Nat
  rootSize : Nat
  fileSize : Nat
  deriving Repr, Inhabited, BEq

/-- Little-endian unsigned integer of `n` bytes at `off` (missing bytes read as `0`; callers check
bounds first). Structural recursion on `n`. -/
def readLE (bs : ByteArray) (off : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (bs.get! off).toNat + 256 * readLE bs (off + 1) n

def bytesToString (bs : ByteArray) (off len : Nat) : List UInt8 :=
  (List.range len).map fun i => bs.get! (off + i)

def headerSize : Nat := 88
def u64Bound : Nat := 2 ^ 64
/-- Exact largest constructor tag of the Lean 4.34.1 runtime (`#define LeanMaxCtorTag 243` in `lean.h`;
`244` is `LeanPromise`, `245` is `LeanClosure`). -/
def maxCtorTag : Nat := 243
def leanArrayTag : Nat := 246
def leanScalarArrayTag : Nat := 248
def leanStringTag : Nat := 249
def leanMPZTag : Nat := 250

/-- Validate a non-scalar pointer referenced by the root constructor: for base `.olean`/`.ir.sig`
parts (`allowParent == false`), `ptr` must lie inside `[base + 96, base + size)`; for layered delta
parts (`.olean.server`, `.olean.private`, `.ir`), `ptr < base` may reference a parent region
(verified against `allowedParents` whenever provided), and any `ptr ≥ base` must have a valid
compacted header (`m_rc == 0`, allowed tag, in-bounds payload). -/
def validateCompactedChild (bs : ByteArray) (base size ptr : Nat) (allowParent : Bool)
    (allowedParents : Array (Nat × Nat) := #[]) :
    Except String Unit := do
  if ptr == 0 then throw "null pointer"
  unless ptr % 8 == 0 do throw s!"misaligned pointer {ptr}"
  if allowParent && ptr < base then
    unless allowedParents.isEmpty ||
        allowedParents.any (fun (pb, psz) => pb + headerSize + 8 ≤ ptr && ptr + 8 ≤ pb + psz) do
      throw s!"parent pointer {ptr} outside parent compacted region(s)"
    return ()
  unless base + headerSize + 8 ≤ ptr && ptr + 8 ≤ base + size do
    throw s!"pointer {ptr} outside compacted region"
  let off := ptr - base
  let rc := readLE bs off 4
  unless rc == 0 do throw s!"nonzero m_rc {rc}"
  let csSz := readLE bs (off + 4) 2
  let other := (bs.get! (off + 6)).toNat
  let tag := (bs.get! (off + 7)).toNat
  if tag ≤ maxCtorTag then
    unless csSz ≥ 8 + 8 * other && off + csSz ≤ size do
      throw s!"constructor size {csSz} out of bounds"
  else if tag == leanArrayTag then
    unless off + 24 ≤ size do throw "truncated LeanArray header"
    let arrSz := readLE bs (off + 8) 8
    let arrCap := readLE bs (off + 16) 8
    unless arrSz ≤ arrCap && off + 24 + 8 * arrSz ≤ size do
      throw s!"LeanArray size {arrSz} (cap {arrCap}) exceeds file bounds"
  else if tag == leanScalarArrayTag then
    unless off + 24 ≤ size do throw "truncated LeanScalarArray header"
    let sSz := readLE bs (off + 8) 8
    let sCap := readLE bs (off + 16) 8
    let elemSz := if other == 0 then 1 else other
    unless sSz ≤ sCap && off + 24 + elemSz * sSz ≤ size do
      throw s!"LeanScalarArray size {sSz} exceeds file bounds"
  else if tag == leanStringTag then
    unless off + 32 ≤ size do throw "truncated LeanString header"
    let strSz := readLE bs (off + 8) 8
    let strCap := readLE bs (off + 16) 8
    let strLen := readLE bs (off + 24) 8
    unless strSz ≥ 1 && strSz ≤ strCap && strLen < strSz && off + 32 + strSz ≤ size &&
        bs.get! (off + 32 + strSz - 1) == 0 do
      throw s!"LeanString size {strSz} invalid or missing NUL terminator"
  else if tag == leanMPZTag then
    unless off + 16 ≤ size do throw "truncated LeanMPZ object"
  else
    throw s!"forbidden runtime object tag {tag} in compacted region"

/-- Pure, total validator of Lean 4.34.1's 88-byte `.olean` header (shared by `.olean`,
`.olean.server`, `.olean.private`, `.ir.sig`, `.ir`), the compacted region's root constructor, and
all direct object-pointer fields of the root constructor. -/
def validateOleanBinaryBytes (bs : ByteArray) (cfg : OleanHeaderConfig := {}) :
    Except OleanHeaderError OleanHeaderInfo := do
  let size := bs.size
  if size < headerSize + 8 then throw (.tooShort size)
  if size > cfg.maxBytes then throw (.tooLarge size cfg.maxBytes)
  unless bytesToString bs 0 5 == "olean".toUTF8.toList do throw .badMagic
  let ver := (bs.get! 5).toNat
  unless ver == 2 do throw (.badFormatVersion ver)
  let flags := (bs.get! 6).toNat
  unless flags &&& (255 - 1) == 0 do throw (.badFlags flags)
  -- [7, 40): NUL-padded ASCII version string.
  let vbytes := bytesToString bs 7 33
  let vchars := vbytes.takeWhile (· != 0)
  let vrest := vbytes.drop vchars.length
  if vchars.isEmpty then throw (.badVersionString "empty")
  unless vchars.all (fun b => b ≥ 0x20 && b ≤ 0x7e) do throw (.badVersionString "non-printable byte")
  unless vrest.all (· == 0) do throw (.badVersionString "non-NUL byte after the terminator")
  let version := String.ofList (vchars.map fun b => Char.ofNat b.toNat)
  if let some e := cfg.expectedVersion? then
    unless version == e do throw (.versionMismatch version e)
  -- [40, 80): lowercase hex githash.
  let gbytes := bytesToString bs 40 40
  unless gbytes.all (fun b => (b ≥ 0x30 && b ≤ 0x39) || (b ≥ 0x61 && b ≤ 0x66)) do throw .badGithash
  let githash := String.ofList (gbytes.map fun b => Char.ofNat b.toNat)
  if let some e := cfg.expectedGithash? then
    unless githash == e do throw (.githashMismatch githash e)
  -- [80, 88): base address.
  let base := readLE bs 80 8
  if base == 0 then throw .zeroBaseAddr
  unless base % 8 == 0 do throw (.misalignedBaseAddr base)
  unless base + size < u64Bound do throw .baseAddrWraps
  unless (size - headerSize) % 8 == 0 do throw (.misalignedDataSize size)
  for (pBase, pSize) in cfg.parentRegions do
    unless base + size ≤ pBase || pBase + pSize ≤ base do
      throw (.overlappingParentRegion base size)
  -- [88, 96): root pointer.
  let root := readLE bs 88 8
  unless root % 2 == 0 do throw (.scalarRootPtr root)
  unless root % 8 == 0 do throw (.misalignedRootPtr root)
  unless base + headerSize + 8 ≤ root && root + 8 ≤ base + size do throw (.rootOutOfBounds root)
  let off := root - base
  -- Root object header: m_rc (u32) | m_cs_sz (u16) | m_other (u8) | m_tag (u8).
  let rc := readLE bs off 4
  unless rc == 0 do throw (.rootRcNonzero rc)
  let csSz := readLE bs (off + 4) 2
  let other := (bs.get! (off + 6)).toNat
  let tag := (bs.get! (off + 7)).toNat
  unless tag ≤ maxCtorTag do throw (.rootNotConstructor tag)
  unless csSz ≥ 8 + 8 * other && off + csSz ≤ size do throw (.rootSizeInvalid csSz)
  let allowedParents := cfg.parentRegions ++ cfg.auxParentRegions
  -- Validate every object-pointer field of the root constructor (`ModuleData` / `IR` root).
  for idx in [0:other] do
    let fptr := readLE bs (off + 8 + 8 * idx) 8
    if fptr % 2 == 0 then
      match validateCompactedChild bs base size fptr cfg.allowParentRegionPtrs allowedParents with
      | .ok () => pure ()
      | .error why => throw (.rootChildInvalid idx why)
  return { version, githash, gmp := flags &&& 1 == 1, baseAddr := base, rootPtr := root,
           rootOffset := off, rootSize := csSz, fileSize := size }

def isLayeredCompanionPath (p : System.FilePath) : Bool :=
  let s := p.toString
  s.endsWith ".olean.server" || s.endsWith ".olean.private" || s.endsWith ".ir"

/-- Read and validate one artifact part. Rejects symlinks and non-regular files via `lstat` and
checks the size limit from metadata before reading. -/
def validateOleanFile (p : System.FilePath) (cfg : OleanHeaderConfig := {}) :
    IO (Except String OleanHeaderInfo) := do
  let md ← try p.symlinkMetadata catch e => return .error s!"cannot lstat {p}: {e}"
  if md.type == .symlink then return .error s!"{p} is a symlink"
  unless md.type == .file do return .error s!"{p} is not a regular file"
  if md.byteSize.toNat > cfg.maxBytes then
    return .error (OleanHeaderError.tooLarge md.byteSize.toNat cfg.maxBytes).render
  let bs ← try IO.FS.readBinFile p catch e => return .error s!"cannot read {p}: {e}"
  let cfg' := { cfg with allowParentRegionPtrs := cfg.allowParentRegionPtrs || isLayeredCompanionPath p }
  return match validateOleanBinaryBytes bs cfg' with
    | .ok i => .ok i
    | .error e => .error e.render

def stripTrailingSlashes (s : String) : String :=
  let rec go : List Char → List Char
    | [] => []
    | c :: cs => if c == '/' && cs.all (· == '/') then [] else c :: go cs
  let r := String.ofList (go s.toList)
  if r.isEmpty && s.startsWith "/" then "/" else r

/-- Verify that `root` is an absolute, existing, non-symlink directory whose canonical `realPath`
equals `root` itself (rejecting symlinks both at `root` and on any ancestor directory). -/
def validateCanonicalRootDir (root : System.FilePath) : IO (Except String System.FilePath) := do
  unless root.isAbsolute do return .error s!"root {root} must be absolute"
  let rootStr := stripTrailingSlashes root.toString
  let rootClean : System.FilePath := ⟨rootStr⟩
  if rootClean.components.any (fun c => c == "." || c == "..") then
    return .error s!"root {root} contains `.` or `..` component"
  let rmd ← try rootClean.symlinkMetadata catch _ => return .error s!"root {root} does not exist"
  if rmd.type == .symlink then return .error s!"root {root} is a symlink"
  unless rmd.type == .dir do return .error s!"root {root} is not a directory"
  let realRoot ← try IO.FS.realPath rootClean catch _ => return .error s!"root {root} cannot be canonicalized"
  unless realRoot.components == rootClean.components do
    return .error s!"root {root} has a symlinked ancestor (canonicalizes to {realRoot})"
  return .ok realRoot

/-- Component-boundary root containment with pre-validated canonical `realRoot` (`validateCanonicalRootDir`
already proved `realRoot == ⟨rootStr⟩` with no symlinks at or above `rootStr`, and `lstat` below
verifies every relative component is a non-symlink directory and the leaf is a regular file). -/
def pathWithinVerifiedRoot (rootStr : String) (realRoot target : System.FilePath) :
    IO (Except String System.FilePath) := do
  unless target.isAbsolute do return .error "target path must be absolute"
  let tStr := target.toString
  let pre := if rootStr == "/" then "/" else rootStr ++ "/"
  unless tStr.startsWith pre do return .error s!"{target} is not under root {rootStr}"
  let rel := (tStr.drop pre.length).toString
  let comps := rel.splitOn "/"
  if comps.isEmpty || comps.any (fun c => c.isEmpty || c == "." || c == "..") then
    return .error s!"{target} has an empty, `.` or `..` component below {rootStr}"
  let mut cur : System.FilePath := realRoot
  let mut i := 0
  for c in comps do
    i := i + 1
    cur := cur / c
    let md ← try cur.symlinkMetadata catch _ => return .error s!"{cur} does not exist"
    if md.type == .symlink then return .error s!"{cur} is a symlink"
    if i == comps.length then
      unless md.type == .file do return .error s!"{cur} is not a regular file"
    else
      unless md.type == .dir do return .error s!"{cur} is not a directory"
  return .ok cur

/-- Component-boundary root containment. `root` itself must be a canonical, symlink-free directory;
`target` must be lexically `root/<rel>` with no empty, `.` or `..` components in `<rel>`; every
component from `root` down must be a non-symlink; and the canonical target must equal the canonical
root followed by `<rel>`. -/
def pathWithinRoot (root target : System.FilePath) : IO (Except String System.FilePath) := do
  let rootStr := stripTrailingSlashes root.toString
  match ← validateCanonicalRootDir root with
  | .error e => return .error e
  | .ok realRoot => pathWithinVerifiedRoot rootStr realRoot target

def modRelPath (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString (escape := false)))

def partExts : Array String := #["olean", "olean.server", "olean.private", "ir.sig", "ir"]

def entryExists (p : System.FilePath) : IO Bool := do
  try let _ ← p.symlinkMetadata; pure true catch _ => pure false

structure ResolutionConfig where
  sysrootLibDir : System.FilePath
  approvedBuildRoots : Array System.FilePath
  /-- Search path to probe; `none` = the active `searchPathRef`. -/
  searchPath? : Option SearchPath := none
  validateBinaries : Bool := true
  validateToolchainBinaries : Bool := false
  header : OleanHeaderConfig := {}

/-- Canonical identity of a search-path root (deduplicates exact lexical/canonical sysroot entries
while preserving symlink detection). -/
def canonicalRoot (p : System.FilePath) : IO String := do
  try pure (← IO.FS.realPath p).toString catch _ => pure s!"<missing>{p}"

/-- Vector 3. For every module: `Lean.findOLean` resolution, multi-root shadowing of any artifact
part, toolchain-name shadowing outside the sysroot, approved-root containment of the resolved
`.olean` and every existing companion part, companion-part completeness (`.olean.server` ↔
`.olean.private` and `.ir.sig` ↔ `.ir`), and binary header + root-field validation. -/
def auditOleanResolutionAndShadowing (mods : Array Name) (cfg : ResolutionConfig) : AuditM Unit := do
  let sp ← match cfg.searchPath? with
    | some sp => pure sp
    | none => searchPathRef.get
  let sysCanon ← canonicalRoot cfg.sysrootLibDir
  let verifiedSys ← validateCanonicalRootDir cfg.sysrootLibDir
  let mut verifiedBuildRoots : Array (String × System.FilePath) := #[]
  for r in cfg.approvedBuildRoots do
    if let .ok realR ← validateCanonicalRootDir r then
      verifiedBuildRoots := verifiedBuildRoots.push (stripTrailingSlashes r.toString, realR)
  let mut roots : Array (System.FilePath × String × Bool) := #[]
  for r in sp do
    let c ← canonicalRoot r
    let nonCanon := match ← validateCanonicalRootDir r with | .error _ => true | .ok _ => false
    -- Keep non-canonical (e.g. symlinked) search-path entries distinct so symlinked search-path
    -- shadowing or resolution is never hidden by canonical deduplication.
    let key := if nonCanon then s!"<noncanon>{r}->{c}" else c
    unless roots.any (fun (_, k, _) => k == key) do
      roots := roots.push (r, key, c == sysCanon && !nonCanon)
  let saved ← searchPathRef.get
  searchPathRef.set sp
  let modTasks ← try
      let ts ← mods.mapM fun m => IO.asTask do
        let act : AuditM Unit := do
          let isTool := isToolchainName m
          let rel := modRelPath m
          let mut present : Array String := #[]
          for (r, key, isSys) in roots do
            let mut presentExts : Array String := #[]
            for ext in partExts do
              if ← entryExists ⟨(r / rel).toString ++ "." ++ ext⟩ then
                presentExts := presentExts.push ext
            if !presentExts.isEmpty then
              present := present.push key
              if isTool && !isSys then
                report .toolchainShadowed m m s!"toolchain module has artifacts in non-sysroot root {r}"
              let hasOlean := presentExts.contains "olean"
              let hasSrv := presentExts.contains "olean.server"
              let hasPriv := presentExts.contains "olean.private"
              let hasIrSig := presentExts.contains "ir.sig"
              let hasIr := presentExts.contains "ir"
              unless hasOlean do
                report .oleanOutsideApprovedRoot m m
                  s!"orphan companion artifact(s) {presentExts} without `.olean` in {r}"
              unless hasSrv == hasPriv do
                report .oleanOutsideApprovedRoot m m
                  s!"incomplete module-system `.olean` companions ({presentExts}) in {r}: `.olean.server` and `.olean.private` must appear together"
              unless hasIrSig == hasIr do
                report .oleanOutsideApprovedRoot m m
                  s!"incomplete IR companions ({presentExts}) in {r}: `.ir.sig` and `.ir` must appear together"
          if present.size ≥ 2 then
            report .oleanShadowed m m s!"module artifacts present in {present.size} search-path roots: {present}"
          let resolved ← try pure (some (← findOLean m)) catch _ => pure none
          match resolved with
          | none => report .oleanUnresolved m m "Lean.findOLean cannot resolve the module"
          | some olean =>
            let matchedRoot? ← if isTool then
                match verifiedSys with
                | .error _ => pure none
                | .ok realSys =>
                  let sStr := stripTrailingSlashes cfg.sysrootLibDir.toString
                  match ← pathWithinVerifiedRoot sStr realSys olean with
                  | .ok _ => pure (some (sStr, realSys))
                  | .error _ => pure none
              else do
                let mut hit? : Option (String × System.FilePath) := none
                for (rStr, realR) in verifiedBuildRoots do
                  if hit?.isNone then
                    if let .ok _ ← pathWithinVerifiedRoot rStr realR olean then
                      hit? := some (rStr, realR)
                pure hit?
            match matchedRoot? with
            | none =>
              report .oleanOutsideApprovedRoot m m
                s!"{olean} is not a symlink-free regular file inside a canonical approved root"
            | some (rootStr, realRoot) =>
              let base := (olean.toString.dropEnd 6).toString
              let mut oleanChain : Array (Nat × Nat) := #[]
              let mut irChain : Array (Nat × Nat) := #[]
              for ext in partExts do
                let p : System.FilePath := ⟨base ++ "." ++ ext⟩
                if ← entryExists p then
                  match ← pathWithinVerifiedRoot rootStr realRoot p with
                  | .error e => report .oleanOutsideApprovedRoot m m s!"companion part: {e}"
                  | .ok _ =>
                    if cfg.validateBinaries && (!isTool || cfg.validateToolchainBinaries) then
                      let isIr := ext == "ir.sig" || ext == "ir"
                      let pCfg := if isIr then
                          { cfg.header with parentRegions := irChain, auxParentRegions := oleanChain }
                        else
                          { cfg.header with parentRegions := oleanChain }
                      match ← validateOleanFile p pCfg with
                      | .ok info =>
                        if isIr then irChain := irChain.push (info.baseAddr, info.fileSize)
                        else oleanChain := oleanChain.push (info.baseAddr, info.fileSize)
                        modify fun s => { s with oleansChecked := s.oleansChecked + 1 }
                      | .error e => report .oleanHeaderInvalid m m s!"{p}: {e}"
        let ((), ms) ← StateT.run act {}
        return ms
      ts.mapM fun t => (IO.wait t : IO (Except IO.Error AuditSummary))
    finally
      searchPathRef.set saved
  for r in modTasks do
    match r with
    | .ok ms => absorb ms
    | .error e => report .oleanHeaderInvalid .anonymous .anonymous s!"Vector 3 task failed: {e}"

/-- Toolchain modules by name *and* provenance: toolchain-named modules whose `.olean` resolves to a
symlink-free regular file inside the canonical sysroot library. Other toolchain-named modules are
reported and are *not* treated as toolchain modules by the environment audits. -/
def computeToolchainModules (env : Environment) (sysrootLibDir : System.FilePath)
    (known : NameSet := {}) : AuditM NameSet := do
  let verifiedSys ← validateCanonicalRootDir sysrootLibDir
  let sStr := stripTrailingSlashes sysrootLibDir.toString
  let toCheck := env.header.modules.filterMap fun mi =>
    if isToolchainName mi.module && !known.contains mi.module then some mi.module else none
  let tasks ← toCheck.mapM fun m => IO.asTask do
    let resolved ← try pure (some (← findOLean m)) catch _ => pure none
    match resolved with
    | none => return (m, Except.error (.oleanUnresolved, "toolchain-named module cannot be resolved"))
    | some p =>
      match verifiedSys with
      | .error e =>
        return (m, Except.error (.oleanOutsideApprovedRoot, s!"invalid sysroot {sysrootLibDir}: {e}"))
      | .ok realSys =>
        match ← pathWithinVerifiedRoot sStr realSys p with
        | .ok _ => return (m, Except.ok ())
        | .error e =>
          return (m, Except.error (.oleanOutsideApprovedRoot, s!"toolchain-named module outside the sysroot: {e}"))
  let mut out : NameSet := known
  for t in tasks do
    match ← (IO.wait t : IO (Except IO.Error (Name × Except (ViolationKind × String) Unit))) with
    | .ok (m, .ok ()) => out := out.insert m
    | .ok (m, .error (k, msg)) => report k m m msg
    | .error e => report .oleanOutsideApprovedRoot .anonymous .anonymous s!"toolchain resolution task failed: {e}"
  return out

/-- Strip any artifact suffix (`.olean.private`, `.olean.server`, `.olean`, `.ir.sig`, `.ir`) from
a filename to recover its stem, or `none` if not an artifact file. -/
def artifactStem? (fileName : String) : Option String :=
  if fileName.endsWith ".olean.private" then some (fileName.dropEnd 14).toString
  else if fileName.endsWith ".olean.server" then some (fileName.dropEnd 13).toString
  else if fileName.endsWith ".olean" then some (fileName.dropEnd 6).toString
  else if fileName.endsWith ".ir.sig" then some (fileName.dropEnd 7).toString
  else if fileName.endsWith ".ir" then some (fileName.dropEnd 3).toString
  else none

/-- Bounded walk of a build library directory collecting the module names of its `.olean` and
companion files while reporting any symlinks inside `libDir` immediately (so symlinked `.olean`
files or symlinked subdirectories can never silently bypass Vector 3). -/
def listOleanModules (libDir : System.FilePath) (fuel : Nat := 100000) : AuditM (Array Name) := do
  match ← validateCanonicalRootDir libDir with
  | .error e =>
    report .oleanOutsideApprovedRoot .anonymous .anonymous s!"build library root invalid: {e}"
    return #[]
  | .ok _ => pure ()
  let mut seenMods : NameSet := {}
  let mut result : Array Name := #[]
  let mut pending : List (System.FilePath × Name) := [(libDir, .anonymous)]
  let mut done := false
  for _ in [0:fuel] do
    match pending with
    | [] => done := true; break
    | (dir, pre) :: rest =>
      pending := rest
      for entry in ← dir.readDir do
        let md ← entry.path.symlinkMetadata
        if md.type == .symlink then
          let modGuess := match artifactStem? entry.fileName with
            | some stem => pre.str stem
            | none => pre.str entry.fileName
          report .oleanOutsideApprovedRoot modGuess modGuess
            s!"symlink entry inside build library: {entry.path}"
          if !seenMods.contains modGuess then
            seenMods := seenMods.insert modGuess
            result := result.push modGuess
        else if md.type == .dir then
          pending := (entry.path, pre.str entry.fileName) :: pending
        else if md.type == .file then
          if let some stem := artifactStem? entry.fileName then
            let m := pre.str stem
            if !seenMods.contains m then
              seenMods := seenMods.insert m
              result := result.push m
  unless done do report .auditFuelExhausted .anonymous .anonymous s!"directory walk of {libDir} exhausted its fuel"
  return result

/-! ## Vector 4a — `Init.ShareCommon` -/

/-- Foreign C extern symbol names backing `Init.ShareCommon` primitives. -/
def shareCommonExternSymbols : List String :=
  ["lean_sharecommon_quick", "lean_state_sharecommon", "lean_sharecommon_eq", "lean_sharecommon_hash"]

def isShareCommonConst (env : Environment) (c : Name) : Bool :=
  shareCommonSymbols.contains c || origin? env c == some shareCommonModule

def constEdges (e : Expr) (acc : NameSet) : NameSet :=
  e.getUsedConstants.foldl (·.insert ·) acc

/-- Every constant of the `Init.ShareCommon` surface present in `env`: the explicit symbols plus
every constant stored by the `Init.ShareCommon` module (one `O(1)` hash lookup per node). -/
def shareCommonSet (env : Environment) : Std.HashSet Name := Id.run do
  let mut out : Std.HashSet Name := shareCommonSymbols.foldl (·.insert ·) {}
  for h : i in [0:env.header.modules.size] do
    if env.header.modules[i].module == shareCommonModule then
      if let some d := env.header.moduleData[i]? then
        for n in d.constNames ++ d.extraConstNames do out := out.insert n
  return out

def isShareCommonNode (sc : Std.HashSet Name) : Expr → Bool
  | .const c _ => sc.contains c
  | _ => false

def recordScExprHits (sc : Std.HashSet Name) (e : Expr) (acc : Array Name) : Array Name :=
  if (e.find? (isShareCommonNode sc)).isNone then acc
  else e.getUsedConstants.foldl (fun a c => if sc.contains c && !a.contains c then a.push c else a) acc

def recordScConst (sc : Std.HashSet Name) (c : Name) (acc : Array Name) : Array Name :=
  if sc.contains c && !acc.contains c then acc.push c else acc

/-- Zero-allocation LCNF value scan against `sc : Std.HashSet Name` (checks `let` values,
constructors, projections, and full/partial applications; types are erased before codegen and top
`d.type` is screened once per declaration). `none` = fuel exhausted. -/
def lcnfCodeShareCommonHits (sc : Std.HashSet Name) (fuel : Nat) (c : Compiler.LCNF.Code .pure)
    (acc : Array Name) : Option (Array Name) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match c with
    | .let decl k =>
      let acc := match decl.value with
        | .const n _ _ _ => recordScConst sc n acc
        | .proj typeName _ _ _ => recordScConst sc typeName acc
        | .ctor info _ _ => recordScConst sc info.name acc
        | .fap fn _ _ | .pap fn _ _ => recordScConst sc fn acc
        | _ => acc
      lcnfCodeShareCommonHits sc fuel k acc
    | .fun decl k _ => do
      let acc ← lcnfCodeShareCommonHits sc fuel decl.value acc
      lcnfCodeShareCommonHits sc fuel k acc
    | .jp decl k => do
      let acc ← lcnfCodeShareCommonHits sc fuel decl.value acc
      lcnfCodeShareCommonHits sc fuel k acc
    | .jmp _ _ => some acc
    | .cases cs => do
      let mut acc := recordScConst sc cs.typeName acc
      for alt in cs.alts do
        match alt with
        | .alt ctor _ code _ => acc ← lcnfCodeShareCommonHits sc fuel code (recordScConst sc ctor acc)
        | .default code => acc ← lcnfCodeShareCommonHits sc fuel code acc
        | .ctorAlt info code _ => acc ← lcnfCodeShareCommonHits sc fuel code (recordScConst sc info.name acc)
      return acc
    | .return _ => some acc
    | .unreach _ => some acc
    | _ => some acc

def lcnfDeclShareCommonHits (sc : Std.HashSet Name) (d : Compiler.LCNF.Decl .pure) (fuel : Nat) :
    Option (Array Name) :=
  let acc := recordScExprHits sc d.type #[]
  match d.value with
  | .code c => lcnfCodeShareCommonHits sc fuel c acc
  | .extern extData =>
    let hasScSym := extData.entries.any fun
      | .standard _ fn | .inline _ fn => shareCommonExternSymbols.any fun s => (fn.splitOn s).length > 1
      | _ => false
    some (if hasScSym then recordScConst sc `ShareCommon.shareCommon' acc else acc)

/-- Check if an `ExternAttrData` invokes a `ShareCommon` C runtime symbol directly. -/
def externDataTouchesShareCommon (ed : ExternAttrData) : Bool :=
  ed.entries.any fun
    | .standard _ fn => shareCommonExternSymbols.contains fn
    | .inline _ pat => shareCommonExternSymbols.any fun s => (pat.splitOn s).length > 1
    | _ => false

/-- Vector 4a: direct imports of `Init.ShareCommon` and references to its surface from LCNF bodies
(`baseExt` / `monoExt`), compiled IR (`IR.declMapExt`), and `@[extern]` bindings. -/
def shareCommonView (ctx : AuditContext) (sc : Std.HashSet Name) (fuel : Nat) (v : ModuleView) :
    PureAuditM Unit := do
  let env := ctx.env
  let imports := if v.idx?.isNone then env.header.imports else v.data.imports
  if imports.any (·.module == shareCommonModule) then
    report .shareCommonImport v.module v.module "non-toolchain module imports Init.ShareCommon"
  let checkLcnf (d : Compiler.LCNF.Decl .pure) : PureAuditM Unit := do
    match lcnfDeclShareCommonHits sc d fuel with
    | none => report .auditFuelExhausted d.name v.module "LCNF body walk exhausted its fuel"
    | some cs =>
      for c in cs do report .shareCommonReference d.name v.module s!"LCNF body references {c}"
  let checkIr (d : IR.Decl) : PureAuditM Unit := do
    if let .extern dn _ _ ed := d then
      if externDataTouchesShareCommon ed then
        report .shareCommonReference dn v.module "compiled IR extern binds a ShareCommon runtime symbol"
    for c in IR.collectUsedDecls env [d] do
      if sc.contains c || isShareCommonConst env c then
        report .shareCommonReference d.name v.module s!"compiled IR references {c}"
  match v.idx? with
  | some i =>
    for d in Compiler.LCNF.baseExt.getModuleEntries env i do checkLcnf d
    for d in Compiler.LCNF.monoExt.getModuleEntries env i do checkLcnf d
    for d in Compiler.LCNF.baseExt.getModuleIREntries env i do checkLcnf d
    for d in Compiler.LCNF.monoExt.getModuleIREntries env i do checkLcnf d
    for d in IR.declMapExt.getModuleEntries env i do checkIr d
    for d in IR.declMapExt.getModuleIREntries env i do checkIr d
  | none =>
    for n in v.data.constNames ++ v.data.extraConstNames do
      if let some d := Compiler.LCNF.getDeclCore? env Compiler.LCNF.baseExt n then checkLcnf d
      if let some d := Compiler.LCNF.getDeclCore? env Compiler.LCNF.monoExt n then checkLcnf d
      if let some d := IR.findEnvDecl env n then checkIr d

/-- Kernel references to the `Init.ShareCommon` surface from one declaration (type, value
including theorem and opaque bodies, recursor rules). -/
def kernelShareCommonRefs (env : Environment) (ci : ConstantInfo) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for c in declEdges ci do
    if isShareCommonConst env c then out := out.push c
  return out

/-! ## Vector 4b — compiler-override hook inventory -/

/-- Name of a registered persistent extension whose (possibly private) declaration name has user
name `user` (used for extensions that are not accessible by name, e.g. `tagged_return`). -/
def findExtName (user : Name) : IO (Option Name) := do
  for e in ← persistentEnvExtensionsRef.get do
    if e.name == user || privateToUserName e.name == user then return some e.name
  return none

/-- Single-pass count table of persistent extension entries stored by `ModuleData`. -/
def moduleExtCounts (d : ModuleData) : Std.HashMap Name Nat := Id.run do
  let mut m : Std.HashMap Name Nat := {}
  for (n, es) in d.entries do
    if !es.isEmpty then m := m.insert n (m.getD n 0 + es.size)
  return m

/-- Hook extensions where *any* stored entry by a non-toolchain module is an override. -/
def hardHookExtensions : List (Name × String) :=
  [(`Lean.Compiler.implementedByAttr, "implemented_by"), (`Lean.externAttr, "extern"),
   (`Lean.exportAttr, "export"), (`Lean.regularInitAttr, "init"),
   (`Lean.builtinInitAttr, "builtin_init"), (`Lean.Compiler.CSimp.ext, "csimp"),
   (`Lean.Compiler.LCNF.passManagerExt, "cpass"),
   (`Lean.Compiler.LCNF.Simp.ConstantFold.folderExt, "constant_fold"),
   (`Lean.Compiler.LCNF.taggedReturnAttr, "tagged_return"),
   (`Lean.IR.UnboxResult.unboxAttr, "unbox"), (`Lean.neverExtractAttr, "never_extract"),
   (`Lean.Compiler.LCNF.postponedCompileDeclsExt, "postponed_compile")]

def isMacroInline (k : Compiler.InlineAttributeKind) : Bool := k matches .macroInline

/-- Count leading `forallE` binders (bounded by fuel). -/
def countForallBinders (e : Expr) (fuel : Nat := 4096) : Nat :=
  let rec go (cur : Expr) (acc : Nat) : Nat → Nat
    | 0 => acc
    | k + 1 => match cur with | .forallE _ _ b _ => go b (acc + 1) k | _ => acc
  go e 0 fuel

/-- The code generator marks the generated `I.ctorIdx` of every inductive `I` `@[macro_inline]`.
Exempt strictly genuine generated `I.ctorIdx`: `n = I.ctorIdx`, `I` an inductive in the same module
`m`, `I.ctorIdx` a safe non-partial definition in `m` with `iv.numParams + iv.numIndices + 1`
binders returning `Nat`, no `let` bindings, and body constants restricted to `iv.type`'s constants
plus `{I, I.casesOn, I.rec, Nat}` (blocking custom user-authored `@[macro_inline] def I.ctorIdx`). -/
def isGeneratedMacroInline (ctx : AuditContext) (m n : Name) : Bool :=
  match n with
  | .str I "ctorIdx" =>
    match findAnyConst? ctx.env I, findAnyConst? ctx.env n with
    | some (.inductInfo iv), some (.defnInfo dv) =>
      ownerOf ctx I == some m && ownerOf ctx n == some m &&
      dv.safety == .safe &&
      countForallBinders dv.type == iv.numParams + iv.numIndices + 1 &&
      dv.type.getForallBody == mkConst ``Nat &&
      (dv.value.find? fun | .letE .. => true | _ => false).isNone &&
      let allowed := (exprEdges iv.type {})
        |>.insert I |>.insert (I.str "casesOn") |>.insert (I.str "rec") |>.insert ``Nat
      (exprEdges dv.value {}).all allowed.contains
    | _, _ => false
  | _ => false

/-- Legitimate shapes for an `auxRecExt`-tagged declaration owned by `m`: a numeric matcher helper
(`match_on_same_ctor`), `<Ind>.(casesOn|recOn|brecOn|binductionOn|below|ibelow|ctorElim)` (including
indexed mutual/nested variants `below_<n>`, `ibelow_<n>`, `brecOn_<n>`) on an inductive `<Ind>`
owned by `m`, or `<Ctor>.elim` on a constructor `<Ctor>` owned by `m`. -/
def genuineOwnedAuxRec (ctx : AuditContext) (m n : Name) : Bool :=
  match n with
  | .num _ _ => true
  | .str target s =>
    if s == "casesOn" || s == "recOn" || s == "brecOn" || hasNumSuffix s "brecOn_" ||
       s == "binductionOn" || hasNumSuffix s "binductionOn_" ||
       s == "below" || hasNumSuffix s "below_" ||
       s == "ibelow" || hasNumSuffix s "ibelow_" || s == "ctorElim" then
      (findAnyConst? ctx.env target matches some (.inductInfo _)) && ownerOf ctx target == some m
    else if s == "elim" then
      (findAnyConst? ctx.env target matches some (.ctorInfo _)) && ownerOf ctx target == some m
    else false
  | _ => false

/-- Legitimate shapes for a `noConfusionExt`-tagged declaration owned by `m`: `<IndOrCtor>.noConfusion`
where `<IndOrCtor>` is an inductive or constructor also owned by `m`. -/
def genuineOwnedNoConfusion (ctx : AuditContext) (m n : Name) : Bool :=
  match n with
  | .str target "noConfusion" =>
    (match findAnyConst? ctx.env target with
     | some (.inductInfo _) | some (.ctorInfo _) => ownerOf ctx target == some m
     | _ => false)
  | _ => false

/-- Legitimate shapes for a `sparseCasesOn`-tagged declaration owned by `m`: `<Ctor>.elim` on a
constructor in `m`, or a `._sparseCasesOn_<k>[_<i>]` helper. -/
def genuineOwnedSparseCasesOn (ctx : AuditContext) (m n : Name) : Bool :=
  match n with
  | .str ctor "elim" =>
    (findAnyConst? ctx.env ctor matches some (.ctorInfo _)) && ownerOf ctx ctor == some m
  | .str _ s => hasIndexedSuffix s "_sparseCasesOn_"
  | _ => false

/-- Structural fingerprint of a `Compiler.LCNF.PassManager` to detect live pipeline tampering. -/
def passManagerFingerprint (pm : Compiler.LCNF.PassManager) :
    Array (Array (Name × Nat × Nat × Nat)) :=
  let phaseTag : Compiler.LCNF.Phase → Nat
    | .base => 0 | .mono => 1 | .impure => 2
  let fp (ps : Array Compiler.LCNF.Pass) :=
    ps.map fun p => (p.name, p.occurrence, phaseTag p.phase, phaseTag p.phaseOut)
  #[fp pm.basePasses, fp pm.monoPasses, fp pm.monoPassesNoLambda, fp pm.impurePasses]

def builtinFolderKeySet : NameSet :=
  Compiler.LCNF.Simp.ConstantFold.builtinFolders.toList.foldl (fun s (k, _) => s.insert k) {}

/-- Strip up to `fuel` leading lambda binders from `e` (used to inspect `specCacheExt` keys). -/
def stripLeadingLams : Expr → Nat → Expr
  | e, 0 => e
  | .lam _ _ b _, k + 1 => stripLeadingLams b k
  | e, _ + 1 => e

/-- Validate one `Compiler.LCNF.Specialize.CacheEntry` stored by module `m`:
1. `declName` must NOT be a kernel declaration (`constNames` or `findAnyConst?`),
2. `declName` must be an IR-only declaration owned by `m` (`extraConstNames` + `ownerOf`) with an
   actual compiled IR body (`IR.findEnvDecl`), and
3. stripping leading lambdas from `key` must expose a constant head `kfn` matching the specialization
   prefix `<kfn>._at_.` of `declName` with a `.spec_<n>` marker. -/
def validateSpecCacheEntry (ctx : AuditContext) (m : Name) (modKernelNames modExtraNames : NameSet)
    (e : Compiler.LCNF.Specialize.CacheEntry) : PureAuditM Unit := do
  modify fun s => { s with hookEntriesChecked := s.hookEntriesChecked + 1 }
  let env := ctx.env
  let dn := e.declName
  if modKernelNames.contains dn || (findAnyConst? env dn).isSome then
    report .compilerOverrideHook dn m "specialize_cache: entry targets a kernel declaration"
    return
  unless modExtraNames.contains dn && ownerOf ctx dn == some m do
    report .foreignCompilerTag dn m "specialize_cache: entry target is not owned by the storing module"
    return
  if (IR.findEnvDecl env dn).isNone then
    report .compilerOverrideHook dn m "specialize_cache: entry target has no compiled IR body"
    return
  let keyBody := stripLeadingLams e.key 256
  match keyBody.getAppFn with
  | .const kfn _ =>
    let dnStr := dn.toString
    let kStr := kfn.toString
    unless dnStr.startsWith (kStr ++ "._at_.") && (dnStr.splitOn ".spec_").length > 1 do
      report .compilerOverrideHook dn m
        s!"specialize_cache: target {dn} does not match specialization key head {kfn}"
  | _ =>
    report .compilerOverrideHook dn m "specialize_cache: specialization key is not constant-headed"

/-- Vector 4b per-module view: typed `.olean` and `.ir` entries across all hook extensions (including
`taggedReturnAttr`, `sparseCasesOnExt`, and `Specialize.specCacheExt`), generic `d.entries` fallback
counts, live local state, and foreign/forged compiler-intrinsic tags. -/
def hooksView (ctx : AuditContext) (generic : Array (Name × String)) (v : ModuleView) :
    PureAuditM Unit := do
  let env := ctx.env
  let hook (n m : Name) (what : String) : PureAuditM Unit := do
    modify fun s => { s with hookEntriesChecked := s.hookEntriesChecked + 1 }
    report .compilerOverrideHook n m what
  let m := v.module
  let extCounts := moduleExtCounts v.data
  for (extName, label) in generic do
    let k := extCounts.getD extName 0
    if k > 0 then hook m m s!"{label}: module stores {k} entr{if k == 1 then "y" else "ies"}"
  let modKernelNames : NameSet := v.data.constNames.foldl (·.insert ·) {}
  let modExtraNames : NameSet := v.data.extraConstNames.foldl (·.insert ·) {}
  match v.idx? with
  | some i =>
    for (n, _) in Compiler.implementedByAttr.ext.getModuleEntries env i ++ Compiler.implementedByAttr.ext.getModuleIREntries env i do
      hook n m "implemented_by"
    for (n, _) in externAttr.ext.getModuleEntries env i ++ externAttr.ext.getModuleIREntries env i do
      hook n m "extern"
    for (n, _) in exportAttr.ext.getModuleEntries env i ++ exportAttr.ext.getModuleIREntries env i do
      hook n m "export"
    for (n, _) in regularInitAttr.ext.getModuleEntries env i ++ regularInitAttr.ext.getModuleIREntries env i do
      hook n m "init"
    for (n, _) in builtinInitAttr.ext.getModuleEntries env i ++ builtinInitAttr.ext.getModuleIREntries env i do
      hook n m "builtin_init"
    for e in Compiler.CSimp.ext.ext.getModuleEntries env i ++ Compiler.CSimp.ext.ext.getModuleIREntries env i do
      let ent := match e with | .global a => a | .scoped _ a => a
      hook ent.fromDeclName m s!"csimp: {ent.fromDeclName} ↦ {ent.toDeclName}"
    for installer in Compiler.LCNF.passManagerExt.getModuleEntries env i ++ Compiler.LCNF.passManagerExt.getModuleIREntries env i do
      hook installer m "cpass"
    for fe in Compiler.LCNF.Simp.ConstantFold.folderExt.getModuleEntries env i ++ Compiler.LCNF.Simp.ConstantFold.folderExt.getModuleIREntries env i do
      hook fe.declName m "constant_fold"
    for n in Compiler.LCNF.taggedReturnAttr.ext.getModuleEntries env i ++
        Compiler.LCNF.taggedReturnAttr.ext.getModuleIREntries env i do
      hook n m "tagged_return"
    for n in IR.UnboxResult.unboxAttr.ext.getModuleEntries env i ++ IR.UnboxResult.unboxAttr.ext.getModuleIREntries env i do
      hook n m "unbox"
    for n in neverExtractAttr.ext.getModuleEntries env i ++ neverExtractAttr.ext.getModuleIREntries env i do
      hook n m "never_extract"
    for (n, k) in Compiler.inlineAttrs.ext.getModuleEntries env i ++ Compiler.inlineAttrs.ext.getModuleIREntries env i do
      if isMacroInline k && !isGeneratedMacroInline ctx m n then hook n m "macro_inline"
    for entry in Compiler.LCNF.postponedCompileDeclsExt.getModuleEntries env i ++ Compiler.LCNF.postponedCompileDeclsExt.getModuleIREntries env i do
      for n in entry.declNames do
        report .postponedCompilation n m "compilation postponed (no IR stored)"
    for n in auxRecExt.getModuleEntries env i ++ auxRecExt.getModuleIREntries env i do
      if origin? env n != some m then
        report .foreignCompilerTag n m "auxiliary-recursor tag on a foreign declaration"
      else if !genuineOwnedAuxRec ctx m n then
        report .compilerOverrideHook n m "auxiliary-recursor tag on a non-recursor declaration"
    for n in sparseCasesOnExt.getModuleEntries env i ++ sparseCasesOnExt.getModuleIREntries env i do
      if origin? env n != some m then
        report .foreignCompilerTag n m "sparse-cases tag on a foreign declaration"
      else if !genuineOwnedSparseCasesOn ctx m n then
        report .compilerOverrideHook n m "sparse-cases tag on a non-sparseCasesOn declaration"
    for (n, _) in noConfusionExt.getModuleEntries env i ++ noConfusionExt.getModuleIREntries env i do
      if origin? env n != some m then
        report .foreignCompilerTag n m "noConfusion tag on a foreign declaration"
      else if !genuineOwnedNoConfusion ctx m n then
        report .compilerOverrideHook n m "noConfusion tag on a non-noConfusion declaration"
    for se in Compiler.LCNF.Specialize.specCacheExt.getModuleEntries env i ++
        Compiler.LCNF.Specialize.specCacheExt.getModuleIREntries env i do
      validateSpecCacheEntry ctx m modKernelNames modExtraNames se
  | none =>
    for n in v.data.constNames ++ v.data.extraConstNames do
      if (Compiler.implementedByAttr.getParam? env n).isSome then hook n m "implemented_by"
      if (getExternAttrData? env n).isSome then hook n m "extern"
      if (exportAttr.getParam? env n).isSome then hook n m "export"
      if (regularInitAttr.getParam? env n).isSome then hook n m "init"
      if (builtinInitAttr.getParam? env n).isSome then hook n m "builtin_init"
      if Compiler.LCNF.taggedReturnAttr.hasTag env n then hook n m "tagged_return"
      if IR.UnboxResult.unboxAttr.hasTag env n then hook n m "unbox"
      if neverExtractAttr.hasTag env n then hook n m "never_extract"
      if (Compiler.getInlineAttribute? env n).any isMacroInline && !isGeneratedMacroInline ctx m n then
        hook n m "macro_inline"
    for n in auxRecExt.getEntries env do
      if (origin? env n).isNone then
        unless genuineOwnedAuxRec ctx m n do
          report .compilerOverrideHook n m "auxiliary-recursor tag on a non-recursor declaration"
      else
        report .foreignCompilerTag n m "auxiliary-recursor tag on a foreign declaration"
    for n in sparseCasesOnExt.getEntries env do
      if (origin? env n).isNone then
        unless genuineOwnedSparseCasesOn ctx m n do
          report .compilerOverrideHook n m "sparse-cases tag on a non-sparseCasesOn declaration"
      else
        report .foreignCompilerTag n m "sparse-cases tag on a foreign declaration"
    for (n, _) in (noConfusionExt.getState env).toList do
      if (origin? env n).isNone then
        unless genuineOwnedNoConfusion ctx m n do
          report .compilerOverrideHook n m "noConfusion tag on a non-noConfusion declaration"
      else
        report .foreignCompilerTag n m "noConfusion tag on a foreign declaration"
    for entry in Compiler.LCNF.postponedCompileDeclsExt.getEntries env do
      for n in entry.declNames do
        report .postponedCompilation n m "compilation postponed (no IR stored)"
    for (key, dn) in (Compiler.LCNF.Specialize.specCacheExt.getState env).toList do
      validateSpecCacheEntry ctx m modKernelNames modExtraNames { key, declName := dn }

/-- Environment-wide live compiler-state checks (`CSimp` `stateStack`/`newEntries`/`scopedEntries`,
`passManagerExt` live passes & pipeline fingerprint, and `ConstantFold.folderExt` live folders). -/
def auditLiveCompilerState (ctx : AuditContext) : AuditM Unit := do
  let env := ctx.env
  let ownerMod := ctx.liveModule?.getD env.header.mainModule
  let mut toolchainCSimp : Std.HashSet (Name × Name × Name) := {}
  for h : i in [0:env.header.modules.size] do
    let m := env.header.modules[i].module
    if ctx.isToolchainModule m then
      for e in Compiler.CSimp.ext.ext.getModuleEntries env i ++ Compiler.CSimp.ext.ext.getModuleIREntries env i do
        let ent := match e with | .global a => a | .scoped _ a => a
        toolchainCSimp := toolchainCSimp.insert (ent.fromDeclName, ent.toDeclName, ent.thmName)
  let csimpState := Compiler.CSimp.ext.ext.getState env
  for frame in csimpState.stateStack do
    for (k, ent) in frame.state.map.toList do
      unless k == ent.fromDeclName && toolchainCSimp.contains (k, ent.toDeclName, ent.thmName) do
        modify fun s => { s with hookEntriesChecked := s.hookEntriesChecked + 1 }
        report .compilerOverrideHook k ownerMod s!"csimp: {ent.fromDeclName} ↦ {ent.toDeclName}"
  for e in csimpState.newEntries do
    let ent := match e with | .global a => a | .scoped _ a => a
    unless toolchainCSimp.contains (ent.fromDeclName, ent.toDeclName, ent.thmName) do
      modify fun s => { s with hookEntriesChecked := s.hookEntriesChecked + 1 }
      report .compilerOverrideHook ent.fromDeclName ownerMod s!"csimp: {ent.fromDeclName} ↦ {ent.toDeclName}"
  for (_, entries) in csimpState.scopedEntries.map.toList do
    for ent in entries.toArray do
      unless toolchainCSimp.contains (ent.fromDeclName, ent.toDeclName, ent.thmName) do
        modify fun s => { s with hookEntriesChecked := s.hookEntriesChecked + 1 }
        report .compilerOverrideHook ent.fromDeclName ownerMod s!"csimp: {ent.fromDeclName} ↦ {ent.toDeclName}"
  let (livePasses, livePM) := Compiler.LCNF.passManagerExt.getState env
  for p in livePasses do
    modify fun s => { s with hookEntriesChecked := s.hookEntriesChecked + 1 }
    report .compilerOverrideHook p ownerMod "cpass: live compiler pass registered"
  unless passManagerFingerprint livePM == passManagerFingerprint Compiler.LCNF.builtinPassManager do
    modify fun s => { s with hookEntriesChecked := s.hookEntriesChecked + 1 }
    report .compilerOverrideHook `compiler_pipeline ownerMod "cpass: live PassManager differs from builtinPassManager"
  let (liveFolders, liveFolderMap) := Compiler.LCNF.Simp.ConstantFold.folderExt.getState env
  for fe in liveFolders do
    modify fun s => { s with hookEntriesChecked := s.hookEntriesChecked + 1 }
    report .compilerOverrideHook fe.declName ownerMod s!"constant_fold: live folder {fe.folderDeclName}"
  let mut liveFolderKeys : NameSet := {}
  for (k, _) in liveFolderMap.toList do
    liveFolderKeys := liveFolderKeys.insert k
    unless builtinFolderKeySet.contains k do
      modify fun s => { s with hookEntriesChecked := s.hookEntriesChecked + 1 }
      report .compilerOverrideHook k ownerMod "constant_fold: live folder key outside builtinFolders"
  unless liveFolderKeys.size == builtinFolderKeySet.size do
    modify fun s => { s with hookEntriesChecked := s.hookEntriesChecked + 1 }
    report .compilerOverrideHook `constant_fold ownerMod "constant_fold: live folder table differs from builtinFolders"

def auditCompilerHooks (ctx : AuditContext) (views : Array ModuleView) : AuditM Unit := do
  let mut generic : Array (Name × String) := #[]
  for (u, label) in hardHookExtensions do
    match ← findExtName u with
    | some n => generic := generic.push (n, label)
    | none => report .environmentLoadFailed u .anonymous s!"hook extension for {label} is not registered"
  for req in [`Lean.sparseCasesOnExt, `Lean.Compiler.LCNF.Specialize.specCacheExt] do
    if (← findExtName req).isNone then
      report .environmentLoadFailed req .anonymous s!"compiler extension {req} is not registered"
  runPerView views (hooksView ctx generic)
  auditLiveCompilerState ctx

/-! ## Vector 4c — opaque-theorem readiness (`leanprover/lean4#14896`) -/

/-- Index of the major premise of recursor-like constant `f`, if it is a kernel recursor (`.rec`,
`.rec_1`, ...) or one of its auxiliary `casesOn` / `recOn` wrappers. -/
def majorPremiseIdx? (env : Environment) (f : Name) : Option (Nat × RecursorVal) := do
  match findAnyConst? env f with
  | some (.recInfo rv) => return (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices, rv)
  | _ =>
    match f with
    | .str ind s =>
      let some (.recInfo rv) := findAnyConst? env (ind.str "rec") | none
      if s == "casesOn" then return (rv.numParams + 1 + rv.numIndices, rv)
      else if s == "recOn" then return (rv.numParams + rv.numMotives + rv.numIndices, rv)
      else none
    | _ => none

/-- Whether an application of recursor-like `rv` at universe levels `us` eliminates into a
non-`Prop` sort. -/
def isLargeElimination (env : Environment) (rv : RecursorVal) (us : List Level) : Bool :=
  let indLevels := match findAnyConst? env rv.getMajorInduct with
    | some ci => ci.levelParams.length
    | none => 0
  if rv.levelParams.length > indLevels then
    match us with
    | u :: _ => !(u.normalize == Level.zero)
    | [] => true
  else false

/-- Extract a theorem constant heading `e` (unwrapping metadata, trivial `let x := v; x` bindings,
and constant-body head beta redexes up to bounded fuel). -/
def isTheoremHead (env : Environment) (e : Expr) (fuel : Nat := 16) : Option Name :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .mdata _ b => isTheoremHead env b fuel
    | .letE _ _ v (.bvar 0) _ => isTheoremHead env v fuel
    | _ =>
      match e.getAppFn with
      | .const c _ => if (findAnyConst? env c) matches some (.thmInfo _) then some c else none
      | .mdata _ fn => isTheoremHead env fn fuel
      | .lam _ _ body _ =>
        if !body.hasLooseBVars then isTheoremHead env body fuel else none
      | _ => none

/-- Extract a theorem constant from a non-`Prop` `.proj` scrutinee `s`, unwrapping projections,
trivial `let` bindings, and non-constructor-headed definition/opaque aliases (`def wrap := thm` or
`id thm`) up to `fuel` steps so wrapped theorem projections cannot evade Layer A. -/
def projScrutineeTheorem? (env : Environment) (s : Expr) (fuel : Nat := 32) : Option Name :=
  match isTheoremHead env s with
  | some t => some t
  | none =>
    let rec go (cur : Expr) : Nat → Option Name
      | 0 => none
      | k + 1 =>
        match isTheoremHead env cur with
        | some t => some t
        | none =>
          match cur with
          | .mdata _ b => go b k
          | .letE _ _ v b _ =>
            if !b.hasLooseBVars then go b k
            else if b == .bvar 0 then go v k
            else none
          | .proj _ _ inner => go inner k
          | _ =>
            match cur.getAppFn with
            | .const fn _ =>
              match findAnyConst? env fn with
              | some (.thmInfo _) => some fn
              | some (.defnInfo dv) =>
                let args := cur.getAppArgs
                if fn == ``id && args.size ≥ 2 then go args[1]! k
                else if args.isEmpty then go dv.value k
                else none
              | some (.opaqueInfo ov) =>
                if cur.getAppArgs.isEmpty then go ov.value k else none
              | _ => none
            | _ => none
    go s fuel

def isTheoremConstNode (env : Environment) : Expr → Bool
  | .const c _ => ((findAnyConst? env c) matches some (.thmInfo _))
  | _ => false

/-- Some theorem constant occurring anywhere in `e` (Lean's cached `Expr.find?`). A major premise
that merely *wraps* a theorem (`id t`, `cast h t`, `(fun x => x) t`, `And.left t`, ...) still needs
the theorem's body once the kernel has unfolded the wrapper, so a head-only test is not enough. -/
def mentionedTheorem? (env : Environment) (e : Expr) : Option Name :=
  match e.find? (isTheoremConstNode env) with
  | some (.const c _) => some c
  | _ => none

/-- Whether inductive `S` lives in `Prop` (its type's final codomain is `Sort 0`). -/
def isPropInductive (env : Environment) (S : Name) : Bool :=
  match findAnyConst? env S with
  | some (.inductInfo iv) => iv.type.getForallBody.isProp
  | _ => false

/-- Check whether a `Prop`-typed major premise `e` either mentions a theorem directly (`Expr.find?`)
or unfolds through non-constructor-headed `Prop`-valued definitions/opaques (`def wrap := thm`,
`id`, `Eq.mp`, projections, `match`) to a theorem within `fuel` steps. -/
def propMajorReachesTheorem? (env : Environment) (e : Expr) (fuel : Nat := 64) : Option Name :=
  match mentionedTheorem? env e with
  | some t => some t
  | none =>
    let isCtorHeaded (v : Expr) : Bool :=
      match v.getAppFn with
      | .const fn _ => ((findAnyConst? env fn) matches some (.ctorInfo _))
      | _ => false
    let isPropCodomain (ty : Expr) : Bool :=
      let cod := ty.getForallBody
      cod.isProp || (match cod.getAppFn with | .const ind _ => isPropInductive env ind | _ => false)
    Id.run do
      let mut visited : NameSet := {}
      let mut todo : List Name := e.getUsedConstants.toList
      for _ in [0:fuel] do
        match todo with
        | [] => return none
        | c :: rest =>
          todo := rest
          if visited.contains c then continue
          visited := visited.insert c
          match findAnyConst? env c with
          | some (.thmInfo _) => return some c
          | some (.defnInfo dv) =>
            if isPropCodomain dv.type && !isCtorHeaded dv.value then
              todo := (exprEdges dv.value {}).toList ++ todo
          | some (.opaqueInfo ov) =>
            if isPropCodomain ov.type && !isCtorHeaded ov.value then
              todo := (exprEdges ov.value {}).toList ++ todo
          | _ => pure ()
      return none

/-- The δ-position test of Layer A for a single node (no recursion into subterms):
`(idx, rv)`-major premise of a non-K large elimination that is headed by a theorem, or a
projection out of a theorem-headed term of a non-`Prop` structure. Checks `isTheoremHead` before
`isPropInductive` on `.proj` so non-theorem projections perform zero environment lookups. -/
def opaqueHitAt? (env : Environment) (e : Expr) : Option (Name × String) :=
  match e with
  | .app .. =>
    match e.getAppFn with
    | .const fn us =>
      match majorPremiseIdx? env fn with
      | some (idx, rv) =>
        if !rv.k && isLargeElimination env rv us then
          let args := e.getAppArgs
          if h : idx < args.size then
            match isTheoremHead env args[idx] with
            | some t => some (t, s!"major premise of {fn}")
            | none =>
              -- Only a `Prop` major premise can be (a wrapper around) a theorem whose body iota
              -- reduction needs; a data major premise merely carries proofs as constructor arguments.
              if isPropInductive env rv.getMajorInduct then
                (propMajorReachesTheorem? env args[idx]).map (·, s!"theorem inside the major premise of {fn}")
              else none
          else none
        else none
      | none => none
    | _ => none
  | .proj S _ s =>
    match projScrutineeTheorem? env s with
    | some thm => if isPropInductive env S then none else some (thm, "scrutinee of Expr.proj")
    | none => none
  | _ => none

/-- Cheap syntactic screen applied before `opaqueHitAt?`: an application headed by a constant whose
last component is `rec`, `rec_<n>`, `casesOn`, or `recOn` at a non-zero first universe level, or a
`.proj` whose scrutinee is not an unadorned bound/free variable. -/
def maybeOpaqueHit (e : Expr) : Bool :=
  match e with
  | .app .. =>
    match e.getAppFn with
    | .const (.str _ s) (u :: _) =>
      (s == "rec" || s.startsWith "rec_" || s == "casesOn" || s == "recOn") && !(u == Level.zero)
    | _ => false
  | .proj _ _ (.bvar _) | .proj _ _ (.fvar _) => false
  | .proj .. => true
  | _ => false

/-- Pre-filter for Layer A using Lean's cached `Expr.find?`. -/
def needsOpaqueScan (env : Environment) (ci : ConstantInfo) : Bool :=
  let p : Expr → Bool := fun e => maybeOpaqueHit e && (opaqueHitAt? env e).isSome
  (ci.type.find? p).isSome || ((ci.value? (allowOpaque := true)).any fun v => (v.find? p).isSome)

/-- Layer A: structural scan for theorems in kernel δ-reduction positions — the major premise of a
non-K large elimination (a recursor, `rec_<n>`, `casesOn` or `recOn` whose motive is not
`Prop`-valued), or the scrutinee of `Expr.proj`. Shared subterms are visited once. `.error ()` =
fuel exhausted. -/
def scanOpaqueTheoremReliance (env : Environment) (ci : ConstantInfo) (fuel : Nat := 2000000) :
    Except Unit (Array (Name × String)) := Id.run do
  unless needsOpaqueScan env ci do return .ok #[]
  let mut todo : List Expr := [ci.type]
  if let some v := ci.value? (allowOpaque := true) then todo := v :: todo
  let mut seen : Std.HashSet Expr := {}
  let mut out : Array (Name × String) := #[]
  for _ in [0:fuel] do
    match todo with
    | [] => return .ok out
    | e :: rest =>
      todo := rest
      if seen.contains e then continue
      seen := seen.insert e
      if let some hit := opaqueHitAt? env e then
        unless out.contains hit do out := out.push hit
      match e with
      | .app .. => todo := e.getAppFn :: e.getAppArgs.toList ++ todo
      | .proj _ _ s => todo := s :: todo
      | .lam _ t b _ | .forallE _ t b _ => todo := t :: b :: todo
      | .letE _ t v b _ => todo := t :: v :: b :: todo
      | .mdata _ b => todo := b :: todo
      | _ => pure ()
  if todo.isEmpty then .ok out else .error ()

inductive OpaqueReplayResult where
  | noTheoremDependencies
  | clean (erased renamed : Nat)
  | deltaReliance (erased renamed : Nat) (err : String)
  | originalRejected (err : String)
  | refusedNativeEvaluator
  | fuelExhausted (why : String)
  | notFound
  deriving Repr, Inhabited, BEq

/-- Absolute kernel heartbeat threshold for a relative budget (never `0` = unlimited). -/
def kernelHeartbeatThreshold (budget : Nat) : IO USize := do
  let now ← IO.getNumHeartbeats
  let raw := now + 1000 * (max budget 1)
  return (min (max raw 1) (USize.size - 1)).toUSize

def replayPrefix : Name := `_opaqueTheoremReplay

def freshReplayName (env : Environment) (n : Name) (tag : String) : Name := Id.run do
  let fullEnv := env.setExporting false
  let kenv := env.checked.get
  let base := (replayPrefix.str tag) ++ n
  let mut c := base
  for i in [0:1000] do
    if !fullEnv.contains c && (kenv.find? c).isNone then return c
    c := base.appendIndexAfter i
  return base.str "fresh_exhausted"

def kernelErrorString (e : Kernel.Exception) : String :=
  match e with
  | .appTypeMismatch .. => "application type mismatch"
  | .declTypeMismatch .. => "declaration type mismatch"
  | .deterministicTimeout => "deterministic timeout"
  | .excessiveMemory => "excessive memory"
  | .deepRecursion => "deep recursion"
  | .interrupted => "interrupted"
  | _ => "kernel rejected the declaration"

/-- Replayable unit in the unified theorem/definition/opaque/inductive DAG for `checkOpaqueTheoremReplay`. -/
inductive ReplayNode where
  | thmAsAxiom (name : Name)
  | defGroup (names : List Name)
  | opaq (name : Name)
  | induct (name : Name)

/-- Layer B: exact kernel-opaque replay oracle (`leanprover/lean4#14896`).
Refuses to invoke the kernel when `declName`'s closure reaches `Lean.reduceBool` or
`Lean.reduceNat`. Otherwise walks dependencies through theorem *types*, definition types/bodies
(including mutual blocks), `opaque` types/bodies, and inductive/constructor/recursor declarations;
replaces every dependency `.thmInfo` with an `.axiomInfo` carrying the rewritten `type` and
identical `levelParams`; rewrites every definition (or mutual block), `opaque`, and non-nested
single inductive whose type/body/constructors reach an erased theorem; inserts all rewritten nodes
in unified DAG topological order; and replays `declName` (supporting `.thmInfo`, `.defnInfo`,
`.opaqueInfo`, and `.inductInfo`) against both the original and theorem-erased `Kernel.Environment`. -/
def checkOpaqueTheoremReplay (env : Environment) (declName : Name) (fuel : Nat := 200000)
    (maxRenamed : Nat := 512) (heartbeats : Nat := 200000) : IO OpaqueReplayResult := do
  let some ci := findAnyConst? env declName | return .notFound
  if reachesNativeEvaluator env #[declName] fuel then return .refusedNativeEvaluator
  let targetGroup : NameSet := match ci with
    | .defnInfo dv => dv.all.foldl (·.insert ·) (NameSet.empty.insert declName)
    | .inductInfo iv =>
      let base := iv.ctors.foldl (·.insert ·) (NameSet.empty.insert declName)
      base.insert (declName.str "rec")
    | _ => NameSet.empty.insert declName
  let mut initPending : List Name := []
  for m in targetGroup do
    if let some mci := findAnyConst? env m then
      initPending := (declEdges mci).toList ++ initPending
  -- Collect dependency theorems (walking their statement types!), definitions, opaques, and inductives.
  let mut defs : Array Name := #[]
  let mut opaques : Array Name := #[]
  let mut inducts : Array Name := #[]
  let mut thms : Array Name := #[]
  let mut thmSet : NameSet := {}
  let mut visited : NameSet := targetGroup
  let mut pending : List Name := initPending
  let mut exhausted := true
  for _ in [0:fuel] do
    match pending with
    | [] => exhausted := false; break
    | n :: rest =>
      pending := rest
      if visited.contains n then continue
      visited := visited.insert n
      match findAnyConst? env n with
      | some (.thmInfo tv) =>
        thms := thms.push n
        thmSet := thmSet.insert n
        pending := (exprEdges tv.type {}).toList ++ pending
      | some (.defnInfo dv) =>
        defs := defs.push n
        let groupEdges := dv.all.foldl (fun acc sib =>
          match findAnyConst? env sib with
          | some (.defnInfo sdv) => exprEdges sdv.value (exprEdges sdv.type acc)
          | _ => acc) (exprEdges dv.value (exprEdges dv.type {}))
        for sib in dv.all do
          if !visited.contains sib && !targetGroup.contains sib then
            visited := visited.insert sib
            defs := defs.push sib
        pending := groupEdges.toList ++ pending
      | some (.opaqueInfo ov) =>
        opaques := opaques.push n
        pending := (exprEdges ov.value (exprEdges ov.type {})).toList ++ pending
      | some (.inductInfo iv) =>
        let mut indEdges := exprEdges iv.type {}
        for c in iv.ctors do
          if let some cci := findAnyConst? env c then
            indEdges := exprEdges cci.type indEdges
        if iv.all == [n] && !iv.isNested then
          inducts := inducts.push n
        pending := indEdges.toList ++ pending
      | some (.ctorInfo cv) =>
        pending := cv.induct :: (exprEdges cv.type {}).toList ++ pending
      | some (.recInfo rv) =>
        pending := rv.getMajorInduct :: (declEdges (.recInfo rv)).toList ++ pending
      | _ => pure ()
  if exhausted then return .fuelExhausted "dependency walk"
  if thms.isEmpty then return .noTheoremDependencies
  -- Reachability fixpoint: which defs, opaques, inductives, and theorem statements reach an erased theorem?
  let nodeEdges (n : Name) : NameSet :=
    match findAnyConst? env n with
    | some (.thmInfo tv) => exprEdges tv.type {}
    | some (.defnInfo dv) =>
      dv.all.foldl (fun acc sib =>
        match findAnyConst? env sib with
        | some (.defnInfo sdv) => exprEdges sdv.value (exprEdges sdv.type acc)
        | _ => acc) (exprEdges dv.value (exprEdges dv.type {}))
    | some (.opaqueInfo ov) => exprEdges ov.value (exprEdges ov.type {})
    | some (.inductInfo iv) =>
      iv.ctors.foldl (fun acc c =>
        match findAnyConst? env c with
        | some cci => exprEdges cci.type acc
        | none => acc) (exprEdges iv.type {})
    | _ => {}
  let cands := defs ++ opaques ++ inducts
  let mut reach : NameSet := thmSet
  let mut stable := false
  for _ in [0:cands.size + 1] do
    let mut changed := false
    for c in cands do
      if !reach.contains c && (nodeEdges c).any reach.contains then
        reach := reach.insert c
        changed := true
    if !changed then stable := true; break
  unless stable do return .fuelExhausted "theorem-reachability fixpoint"
  let renamedDefs := defs.filter reach.contains
  let renamedOpaques := opaques.filter reach.contains
  let renamedInducts := inducts.filter reach.contains
  let totalRenamed := renamedDefs.size + renamedOpaques.size + renamedInducts.size
  if totalRenamed > maxRenamed then return .fuelExhausted s!"{totalRenamed} declarations to rewrite"
  let fullEnv := env.setExporting false
  let origKenv := env.checked.get
  let mut ren : NameMap Name := {}
  for t in thms do ren := ren.insert t (freshReplayName env t "thm")
  for d in renamedDefs do ren := ren.insert d (freshReplayName env d "def")
  for o in renamedOpaques do ren := ren.insert o (freshReplayName env o "opaq")
  let mut renamedIndAssoc : NameSet := {}
  for ind in renamedInducts do
    let some (.inductInfo iv) := findAnyConst? env ind | return .fuelExhausted s!"missing inductive {ind}"
    let ind' := freshReplayName env ind "ind"
    ren := ren.insert ind ind'
    ren := ren.insert (ind.str "rec") (ind'.str "rec")
    renamedIndAssoc := renamedIndAssoc.insert ind |>.insert (ind.str "rec")
    for c in iv.ctors do
      let c' := match c with
        | .str p s =>
          let cand := ind'.str s
          if p == ind && !fullEnv.contains cand && (origKenv.find? cand).isNone then cand
          else freshReplayName env c "ctor"
        | _ => freshReplayName env c "ctor"
      ren := ren.insert c c'
      renamedIndAssoc := renamedIndAssoc.insert c
  let rw (e : Expr) : Expr := e.replace fun
    | .const n us => (ren.find? n).map (Expr.const · us)
    | _ => none
  -- Build unified ReplayNode list (grouping mutual definitions by `dv.all`).
  let mut nodes : Array ReplayNode := thms.map .thmAsAxiom
  let mut groupedDefs : NameSet := {}
  for d in renamedDefs do
    if !groupedDefs.contains d then
      let group := match findAnyConst? env d with
        | some (.defnInfo dv) =>
          let g := dv.all.filter renamedDefs.contains
          if g.isEmpty then [d] else g
        | _ => [d]
      for g in group do groupedDefs := groupedDefs.insert g
      nodes := nodes.push (.defGroup group)
  for o in renamedOpaques do nodes := nodes.push (.opaq o)
  for ind in renamedInducts do nodes := nodes.push (.induct ind)
  let allRenamedSet : NameSet := thmSet ++
    renamedDefs.foldl (·.insert ·) {} ++
    renamedOpaques.foldl (·.insert ·) {} ++
    renamedIndAssoc
  let nodeNames : ReplayNode → List Name
    | .thmAsAxiom t => [t]
    | .defGroup gs => gs
    | .opaq o => [o]
    | .induct ind =>
      match findAnyConst? env ind with
      | some (.inductInfo iv) => ind :: (ind.str "rec") :: iv.ctors
      | _ => [ind, ind.str "rec"]
  let nodeDeps (nd : ReplayNode) : List Name :=
    let own := nodeNames nd
    let es := own.foldl (fun acc x => acc ++ nodeEdges x) ({} : NameSet)
    es.toList.filter fun x => allRenamedSet.contains x && !own.contains x
  -- Unified topological insertion into `kenv`.
  let mut kenv := env.toKernelEnv
  let mut added : NameSet := {}
  let mut remaining := nodes
  for _ in [0:nodes.size + 1] do
    if remaining.isEmpty then break
    let mut next : Array ReplayNode := #[]
    for nd in remaining do
      if (nodeDeps nd).all added.contains then
        match nd with
        | .thmAsAxiom t =>
          let some tci := findAnyConst? env t | return .fuelExhausted s!"missing theorem {t}"
          let some t' := ren.find? t | return .fuelExhausted s!"missing rename for {t}"
          let decl := Declaration.axiomDecl {
            name := t', levelParams := tci.levelParams, type := rw tci.type, isUnsafe := false }
          match kenv.addDeclCore (← kernelHeartbeatThreshold heartbeats) 0 decl none with
          | .ok k => kenv := k; added := added.insert t
          | .error e =>
            return .deltaReliance thms.size totalRenamed
              s!"theorem statement of {t} rejected when prior theorems opaque: {kernelErrorString e}"
        | .defGroup gs =>
          let mut dvals : List DefinitionVal := []
          let allNames' := gs.filterMap ren.find?
          for g in gs do
            let some (.defnInfo dv) := findAnyConst? env g | return .fuelExhausted s!"missing definition {g}"
            let some g' := ren.find? g | return .fuelExhausted s!"missing rename for {g}"
            dvals := dvals ++ [{ dv with name := g', type := rw dv.type, value := rw dv.value, all := allNames' }]
          let decl := match dvals with
            | [single] => Declaration.defnDecl single
            | many => Declaration.mutualDefnDecl many
          match kenv.addDeclCore (← kernelHeartbeatThreshold heartbeats) 0 decl none with
          | .ok k =>
            kenv := k
            for g in gs do added := added.insert g
          | .error e =>
            return .deltaReliance thms.size totalRenamed
              s!"rewritten definition {gs} rejected: {kernelErrorString e}"
        | .opaq o =>
          let some (.opaqueInfo ov) := findAnyConst? env o | return .fuelExhausted s!"missing opaque {o}"
          let some o' := ren.find? o | return .fuelExhausted s!"missing rename for {o}"
          let decl := Declaration.opaqueDecl {
            ov with name := o', type := rw ov.type, value := rw ov.value, all := [o'] }
          match kenv.addDeclCore (← kernelHeartbeatThreshold heartbeats) 0 decl none with
          | .ok k => kenv := k; added := added.insert o
          | .error e =>
            return .deltaReliance thms.size totalRenamed
              s!"rewritten opaque {o} rejected: {kernelErrorString e}"
        | .induct ind =>
          let some (.inductInfo iv) := findAnyConst? env ind | return .fuelExhausted s!"missing inductive {ind}"
          let some ind' := ren.find? ind | return .fuelExhausted s!"missing rename for {ind}"
          let mut ctors' : List Constructor := []
          for c in iv.ctors do
            let some cci := findAnyConst? env c | return .fuelExhausted s!"missing constructor {c}"
            let some c' := ren.find? c | return .fuelExhausted s!"missing rename for {c}"
            ctors' := ctors' ++ [{ name := c', type := rw cci.type }]
          let decl := Declaration.inductDecl iv.levelParams iv.numParams
            [{ name := ind', type := rw iv.type, ctors := ctors' }] iv.isUnsafe
          match kenv.addDeclCore (← kernelHeartbeatThreshold heartbeats) 0 decl none with
          | .ok k =>
            kenv := k
            for nm in nodeNames (.induct ind) do added := added.insert nm
          | .error e =>
            return .deltaReliance thms.size totalRenamed
              s!"rewritten inductive {ind} rejected: {kernelErrorString e}"
      else
        next := next.push nd
    if next.size == remaining.size then return .fuelExhausted "dependency cycle among rewritten declarations"
    remaining := next
  unless remaining.isEmpty do return .fuelExhausted "topological ordering incomplete"
  -- Replay target declaration (supporting `.thmInfo`, `.defnInfo`, `.opaqueInfo`, and `.inductInfo`).
  let mkTargetDecl (tag : String) (rewrite : Expr → Expr) : Option Declaration := Id.run do
    match ci with
    | .thmInfo tv =>
      let n' := freshReplayName env declName tag
      return some (.thmDecl { tv with name := n', type := rewrite tv.type, value := rewrite tv.value })
    | .opaqueInfo ov =>
      let n' := freshReplayName env declName tag
      return some (.opaqueDecl { ov with name := n', type := rewrite ov.type, value := rewrite ov.value, all := [n'] })
    | .inductInfo iv =>
      if iv.all == [declName] && !iv.isNested then
        let ind' := freshReplayName env declName tag
        let mut selfRen : NameMap Name := {}
        selfRen := selfRen.insert declName ind'
        for c in iv.ctors do
          let c' := match c with
            | .str p s => if p == declName then ind'.str s else freshReplayName env c tag
            | _ => freshReplayName env c tag
          selfRen := selfRen.insert c c'
        let rwSelf (e : Expr) : Expr := (rewrite e).replace fun
          | .const n us => (selfRen.find? n).map (Expr.const · us)
          | _ => none
        let mut ctors' : List Constructor := []
        for c in iv.ctors do
          let some cci := findAnyConst? env c | return none
          let some c' := selfRen.find? c | return none
          ctors' := ctors' ++ [{ name := c', type := rwSelf cci.type }]
        return some (.inductDecl iv.levelParams iv.numParams
          [{ name := ind', type := rwSelf iv.type, ctors := ctors' }] iv.isUnsafe)
      else
        return none
    | .defnInfo dv =>
      if dv.all.length ≤ 1 then
        let n' := freshReplayName env declName tag
        return some (.defnDecl { dv with name := n', type := rewrite dv.type, value := rewrite dv.value, all := [n'] })
      else
        let mut selfRen : NameMap Name := {}
        for s in dv.all do selfRen := selfRen.insert s (freshReplayName env s tag)
        let rwSelf (e : Expr) : Expr := (rewrite e).replace fun
          | .const n us => (selfRen.find? n).map (Expr.const · us)
          | _ => none
        let all' := dv.all.filterMap selfRen.find?
        let mut dvals : List DefinitionVal := []
        for s in dv.all do
          let some (.defnInfo sdv) := findAnyConst? env s | return none
          let some s' := selfRen.find? s | return none
          dvals := dvals ++ [{ sdv with name := s', type := rwSelf sdv.type, value := rwSelf sdv.value, all := all' }]
        return some (.mutualDefnDecl dvals)
    | _ => return none
  let some orig := mkTargetDecl "orig" id | return .noTheoremDependencies
  match env.toKernelEnv.addDeclCore (← kernelHeartbeatThreshold heartbeats) 0 orig none with
  | .error e => return .originalRejected (kernelErrorString e)
  | .ok _ => pure ()
  let some erased := mkTargetDecl "erased" rw | return .noTheoremDependencies
  match kenv.addDeclCore (← kernelHeartbeatThreshold heartbeats) 0 erased none with
  | .ok _ => return .clean thms.size totalRenamed
  | .error e => return .deltaReliance thms.size totalRenamed (kernelErrorString e)

/-- Non-foundational toolchain axioms (`sorryAx` and native-evaluation trust axioms) screened in
C++ when auditing whole modules without an explicit root list. -/
def forbiddenToolchainAxioms : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- One traversal per kernel declaration shared by Vector 4a (`Init.ShareCommon` references),
implicit forbidden-axiom screening, and Layer A (opaque-theorem δ positions). All types,
definition/opaque bodies, and recursor rules are always scanned via `Expr.find?`; when
`scanThmBodies` is `false` on compiled `.olean` modules, theorem proof bodies are still screened at
100% coverage in pure C++ via `Expr.getUsedConstants` (zero per-node Lean closure callbacks) so
`Init.ShareCommon` and `sorryAx`/`ofReduceBool` inside compiled theorem proofs can never hide. -/
def kernelScanChunk (ctx : AuditContext) (sc : Std.HashSet Name) (structural scanThmBodies : Bool)
    (checkImplicitAxioms : Bool) (fuel : Nat) (v : ModuleView) (lo hi : Nat) : PureAuditM Unit := do
  let env := ctx.env
  let includeThmBodies := scanThmBodies || v.idx?.isNone
  let isBadConst (c : Name) : Bool :=
    sc.contains c || (checkImplicitAxioms && forbiddenToolchainAxioms.contains c)
  let pFull : Expr → Bool := fun e =>
    (match e with | .const c _ => isBadConst c | _ => false) ||
    (structural && maybeOpaqueHit e && (opaqueHitAt? env e).isSome)
  let consts := v.data.constants[lo:hi].toArray
  let mut fullExprs : Array Expr := #[]
  let mut fastThmVals : Array Expr := #[]
  for ci in consts do
    fullExprs := fullExprs.push ci.type
    match ci with
    | .thmInfo _ =>
      if let some val := ci.value? (allowOpaque := true) then
        if includeThmBodies then fullExprs := fullExprs.push val
        else fastThmVals := fastThmVals.push val
    | _ =>
      if let some val := ci.value? (allowOpaque := true) then fullExprs := fullExprs.push val
    if let .recInfo rv := ci then
      for r in rv.rules do fullExprs := fullExprs.push r.rhs
  -- Overlap the C++ `getUsedConstants` theorem-body screen with the `fullExprs.find?` traversal on
  -- separate worker threads so large modules never serialize the two region walks on a single core.
  -- Without the structural scan the screen is a pure constant-membership test, so one C++
  -- `getUsedConstants` pass over the whole slice (types, values, theorem bodies, recursor rules)
  -- replaces the per-node Lean `find?` callback; with it, `find?` covers the full expressions and
  -- `getUsedConstants` the theorem bodies excluded from the structural walk.
  let (fullHit, fastThmHit) :=
    if structural then
      let fastThmTask := Task.spawn fun _ =>
        !fastThmVals.isEmpty && ((mkAppN (.sort .zero) fastThmVals).getUsedConstants.any isBadConst)
      let fullHit := !fullExprs.isEmpty && ((mkAppN (.sort .zero) fullExprs).find? pFull).isSome
      (fullHit, fastThmTask.get)
    else
      let hit := (mkAppN (.sort .zero) (fullExprs ++ fastThmVals)).getUsedConstants.any isBadConst
      (hit, hit)
  if !fullHit && !fastThmHit then return
  let mut reportedForbidden : NameSet := {}
  for ci in consts do
    let exprBad (e : Expr) : Bool :=
      if structural then (e.find? pFull).isSome else e.getUsedConstants.any isBadConst
    let hasHit : Bool := match ci with
      | .thmInfo _ =>
        (fullHit && exprBad ci.type) ||
        (match ci.value? (allowOpaque := true) with
         | none => false
         | some val =>
           if includeThmBodies then fullHit && exprBad val
           else fastThmHit && val.getUsedConstants.any isBadConst)
      | .recInfo rv =>
        fullHit && (
          exprBad ci.type ||
          ((ci.value? (allowOpaque := true)).any exprBad) ||
          rv.rules.any fun r => exprBad r.rhs)
      | _ =>
        fullHit && (
          exprBad ci.type ||
          ((ci.value? (allowOpaque := true)).any exprBad))
    unless hasHit == true do continue
    for c in kernelShareCommonRefs env ci do
      report .shareCommonReference ci.name v.module s!"kernel declaration references {c}"
    if checkImplicitAxioms && !(ci matches .axiomInfo _) then
      let edges := declEdges ci
      for fa in forbiddenToolchainAxioms do
        if edges.contains fa && !reportedForbidden.contains fa then
          if let some om := ownerOf ctx fa then
            if ctx.isToolchainModule om then
              reportedForbidden := reportedForbidden.insert fa
              report .referencedUnapprovedAxiom fa om
                s!"axiom reachable from {ci.name} in {v.module} is not admitted"
    if structural && (!(ci matches .thmInfo _) || includeThmBodies) then
      match scanOpaqueTheoremReliance env ci fuel with
      | .error () => report .auditFuelExhausted ci.name v.module "structural opaque-theorem scan exhausted its fuel"
      | .ok hits =>
        for (t, why) in hits do
          flag .opaqueTheoremStructural ci.name v.module s!"theorem {t} in δ position ({why})"

/-- Vector 4a over modules: imports, kernel references (one whole-module cached traversal per
module so shared subterms inside a compacted `.olean` region are visited at most once), LCNF and IR. -/
def auditShareCommon (ctx : AuditContext) (views : Array ModuleView) (structural : Bool := true)
    (theoremBodies : Bool := true) (fuel : Nat := 2000000) (checkImplicitAxioms : Bool := false) :
    AuditM Unit := do
  let sc := shareCommonSet ctx.env
  let lcnfTasks := views.map fun v => Task.spawn fun _ => ((shareCommonView ctx sc 100000 v).run {}).2
  let kernTasks := views.map fun v => Task.spawn fun _ =>
    ((kernelScanChunk ctx sc structural theoremBodies checkImplicitAxioms fuel v 0 v.data.constants.size).run {}).2
  for i in [0:views.size] do
    absorb lcnfTasks[i]!.get
    absorb kernTasks[i]!.get

/-- Vector 4c Layer B on each requested declaration (hard violations). Layer A runs inside
`auditShareCommon`'s shared kernel traversal. -/
def auditOpaqueTheorems (ctx : AuditContext) (replayTargets : Array Name := #[])
    (fuel : Nat := 2000000) : AuditM Unit := do
  let env := ctx.env
  for n in replayTargets do
    let m := (ownerOf ctx n).getD .anonymous
    match ← checkOpaqueTheoremReplay env n fuel with
    | .deltaReliance e r err => report .opaqueTheoremDeltaReliance n m s!"accepted, but rejected with {e} theorem(s) opaque ({r} declaration(s) rewritten): {err}"
    | .originalRejected err => report .opaqueTheoremDeltaReliance n m s!"original replay rejected: {err}"
    | .refusedNativeEvaluator => report .nativeEvaluatorReachable n m "kernel replay refused: native evaluator reachable"
    | .fuelExhausted why => report .auditFuelExhausted n m s!"opaque-theorem replay: {why}"
    | .notFound => report .auditFuelExhausted n m "opaque-theorem replay target not found"
    | .clean .. | .noTheoremDependencies => pure ()

/-! ## Unified entry point -/

structure FourVectorConfig where
  axioms : AxiomPolicy := {}
  axiomRoots? : Option (Array Name) := none
  resolution? : Option ResolutionConfig := none
  /-- Modules to resolve for Vector 3 (default: every module of the environment). -/
  resolutionModules? : Option (Array Name) := none
  replayTargets : Array Name := #[]
  runStructuralOpaqueScan : Bool := true
  /-- Also run Layer A structural opaque-theorem scan inside theorem proof bodies (`Init.ShareCommon`
  screening of theorem proof bodies is *always* enabled regardless of this flag). -/
  kernelScanTheoremBodies : Bool := true

/-- Build an audit context: toolchain modules by name and sysroot provenance. -/
def mkAuditContext (env : Environment) (sysrootLibDir : System.FilePath) (liveModule? : Option Name := none)
    (knownToolchain : NameSet := {}) : AuditM AuditContext := do
  let toolchain ← computeToolchainModules env sysrootLibDir knownToolchain
  return { env, toolchain, liveModule? }

/-- Run all four vectors over one environment, skipping modules in `exclude` (already audited).
Environment-pure vectors (1, 2, 4a, 4b) execute concurrently across the worker pool and are absorbed
in deterministic vector order. -/
def runAllFourVectorAudits (ctx : AuditContext) (cfg : FourVectorConfig := {}) (exclude : NameSet := {}) :
    AuditM Unit := do
  let t0 ← IO.monoMsNow
  let views ← nonToolchainViews ctx exclude
  modify fun s => { s with modulesChecked := s.modulesChecked + views.size }
  let viewConstCount := views.foldl (fun acc v => acc + v.data.constants.size) 0 +
    (ctx.env.setExporting false).constants.map₂.toList.length
  let checkImplicitAxioms := cfg.axiomRoots?.isNone && viewConstCount > cfg.axioms.implicitClosureMaxConsts &&
    cfg.axioms.allowClassicalChoice
  let runSub (act : AuditM Unit) : IO (Task (Except IO.Error AuditSummary)) :=
    IO.asTask do pure (← StateT.run act {}).2
  let tV1 ← runSub (auditPrivateNames ctx views)
  let tV2 ← runSub (auditUnreferencedAxioms ctx views cfg.axioms cfg.axiomRoots?)
  let tV4a ← runSub (auditShareCommon ctx views cfg.runStructuralOpaqueScan cfg.kernelScanTheoremBodies 2000000 checkImplicitAxioms)
  let tV4b ← runSub (auditCompilerHooks ctx views)
  let absorbTask (label : String) (tk : Task (Except IO.Error AuditSummary)) : AuditM Unit := do
    match ← IO.wait tk with
    | .ok ms => absorb ms
    | .error e => report .environmentLoadFailed .anonymous .anonymous s!"{label} task failed: {e}"
  if let some rc := cfg.resolution? then
    let mods := cfg.resolutionModules?.getD (ctx.env.header.modules.map (·.module))
    let (_, v3s) ← StateT.run (auditOleanResolutionAndShadowing mods rc) {}
    absorbTask "Vector 1" tV1
    absorbTask "Vector 2" tV2
    absorb v3s
  else
    absorbTask "Vector 1" tV1
    absorbTask "Vector 2" tV2
  absorbTask "Vector 4a" tV4a
  absorbTask "Vector 4b" tV4b
  auditOpaqueTheorems ctx cfg.replayTargets
  let t1 ← IO.monoMsNow
  modify fun s => { s with elapsedMs := s.elapsedMs + (t1 - t0) }

/-- Import graph and constant names of one build module, read (memory-mapped) only after its
binary header passed `validateOleanFile`. -/
structure BuildModuleInfo where
  imports : Array Name
  constants : Array ConstantInfo

/-- Transitive closure of `m` over build-module imports (fuel-bounded). -/
def buildClosure (info : Std.HashMap Name BuildModuleInfo) (m : Name) (fuel : Nat := 100000) : Option NameSet := Id.run do
  let mut seen : NameSet := NameSet.empty.insert m
  let mut todo : List Name := [m]
  for _ in [0:fuel] do
    match todo with
    | [] => return some seen
    | x :: rest =>
      todo := rest
      for i in (info.getD x { imports := #[], constants := #[] }).imports do
        if info.contains i && !seen.contains i then
          seen := seen.insert i
          todo := i :: todo
  if todo.isEmpty then some seen else none

/-- First non-mergeable duplicate constant when adding `mods` to a batch whose constants are
`owners` (`importModules` rejects exactly these: "environment already contains"). -/
def addToBatch (info : Std.HashMap Name BuildModuleInfo) (owners : Std.HashMap Name (Name × ConstantInfo))
    (mods : List Name) : Except (Name × Name × Name) (Std.HashMap Name (Name × ConstantInfo)) := do
  let mut owners := owners
  for m in mods do
    for ci in (info.getD m { imports := #[], constants := #[] }).constants do
      match owners[ci.name]? with
      | some (o, prev) =>
        if o != m && !mergeableDuplicate prev ci then throw (ci.name, o, m)
      | none => owners := owners.insert ci.name (m, ci)
  return owners

/-- Sweep a compiled build library directory, fail closed at every stage:

1. Vector 3 on every build module first (including symlinks and orphan companions discovered in
   `buildLib`), *before* any byte is handed to `readModuleData` or `importModules`; modules with
   any Vector 3 finding are quarantined.
2. Fast single-batch path when `bad` is empty and all requested `roots` co-import cleanly; automatic
   fallback to `readModuleData` conflict-free batch partitioning when `bad` is non-empty or when two
   build modules realize incompatible duplicate auxiliaries.
3. Every validated module in scope is audited across Vectors 1, 2, and 4, and every toolchain module
   seen is verified by Vector 3. -/
def auditBuildLibrary (buildLib sysrootLib : System.FilePath) (cfg : FourVectorConfig := {})
    (roots? : Option (Array Name) := none) : AuditM Unit := do
  let t0 ← IO.monoMsNow
  let sp : SearchPath := [buildLib, sysrootLib]
  let hdr := (cfg.resolution?.map (·.header)).getD {}
  let before := (← get).violations.size
  let mods := (← listOleanModules buildLib).qsort Name.lt
  -- 1. Vector 3 over build modules before loading anything.
  auditOleanResolutionAndShadowing mods
    { sysrootLibDir := sysrootLib, approvedBuildRoots := #[buildLib], searchPath? := some sp, header := hdr }
  let mut bad : NameSet := (← get).violations[before:].foldl (fun acc v => acc.insert v.module) {}
  let roots := roots?.getD (mods.filter (·.isAtomic))
  let modSet : NameSet := mods.foldl (·.insert ·) {}
  let missingRoots := roots.filter (!modSet.contains ·)
  for mr in missingRoots do
    report .oleanUnresolved mr mr "requested library root not present in build directory"
  -- Import graph of the validated modules reachable from the roots, with a deduplicated queue and
  -- import-boundary + binary-header check *before* anything is imported: every import that is not
  -- a build-directory module must be a toolchain-named module resolving inside the canonical
  -- sysroot with complete companions and a valid pinned 4.34.1 `.olean` header.
  let initTodo := roots.filter fun r => modSet.contains r && !bad.contains r
  let mut info : Std.HashMap Name BuildModuleInfo := {}
  let mut extImporters : Std.HashMap Name (Array Name) := {}
  let mut extOrder : Array Name := #[]
  let mut queued : NameSet := initTodo.foldl (·.insert ·) {}
  let mut frontier : Array Name := initTodo
  let savedG ← searchPathRef.get
  searchPathRef.set sp
  try
    for _ in [0:mods.size + 1] do
      if frontier.isEmpty then break
      let readTasks ← frontier.mapM fun m => do
        let t ← IO.asTask do
          let (d, _) ← readModuleData (buildLib / (modRelPath m ++ ".olean"))
          return (d.imports.map (·.module), d.constants)
        return (m, t)
      let mut nextFrontier : Array Name := #[]
      for (m, rt) in readTasks do
        match ← IO.wait rt with
        | .error e =>
          -- Fail closed on the module itself: it must never reach `importModules`.
          report .environmentLoadFailed m m s!"readModuleData failed: {e}"
          bad := bad.insert m
        | .ok (imps, consts) =>
          info := info.insert m { imports := imps, constants := consts }
          for i in imps do
            if modSet.contains i then
              if !bad.contains i && !queued.contains i then
                queued := queued.insert i
                nextFrontier := nextFrontier.push i
            else
              let prev := extImporters.getD i #[]
              if prev.isEmpty then extOrder := extOrder.push i
              extImporters := extImporters.insert i (prev.push m)
      frontier := nextFrontier
    unless frontier.isEmpty do
      report .auditFuelExhausted .anonymous .anonymous "build-library import graph walk exhausted its fuel"
    let verifiedSys ← validateCanonicalRootDir sysrootLib
    let sysStr := stripTrailingSlashes sysrootLib.toString
    let boundaryTasks ← extOrder.mapM fun i => IO.asTask do
      if !isToolchainName i then
        return (i, some (.oleanOutsideApprovedRoot,
          s!"imported by {extImporters.getD i #[]} but neither a build-directory module nor a toolchain module inside the sysroot"))
      match ← (try pure (some (← findOLean i)) catch _ => pure none) with
      | none =>
        return (i, some (.oleanUnresolved, s!"toolchain import {i} could not be resolved"))
      | some p =>
        match verifiedSys with
        | .error e => return (i, some (.oleanOutsideApprovedRoot, e))
        | .ok realSys =>
          match ← pathWithinVerifiedRoot sysStr realSys p with
          | .error e => return (i, some (.oleanOutsideApprovedRoot, e))
          | .ok _ =>
            let base := (p.toString.dropEnd 6).toString
            let hasSrv ← entryExists ⟨base ++ ".olean.server"⟩
            let hasPriv ← entryExists ⟨base ++ ".olean.private"⟩
            let hasIrSig ← entryExists ⟨base ++ ".ir.sig"⟩
            let hasIr ← entryExists ⟨base ++ ".ir"⟩
            if hasSrv != hasPriv || hasIrSig != hasIr then
              return (i, some (.oleanOutsideApprovedRoot, s!"incomplete toolchain companion artifacts for {i}"))
            match ← validateOleanFile p hdr with
            | .ok _ => return (i, none)
            | .error e => return (i, some (.oleanHeaderInvalid, s!"{p}: {e}"))
    for bt in boundaryTasks do
      match ← IO.wait bt with
      | .error e =>
        report .oleanHeaderInvalid .anonymous .anonymous s!"boundary validation task failed: {e}"
      | .ok (i, some (vk, msg)) =>
        report vk i i msg
        for m in extImporters.getD i #[] do
          report .environmentLoadFailed m m s!"imports {i}, which failed pre-import boundary validation"
          bad := bad.insert m
      | .ok (_, none) => pure ()
  finally
    searchPathRef.set savedG
  let validRoots := roots.filter (fun r => modSet.contains r && !bad.contains r)
  -- 2a. Fast single-batch path when all artifacts passed Vector 3 (`bad.isEmpty`).
  if bad.isEmpty && missingRoots.isEmpty && !validRoots.isEmpty then
    let saved ← searchPathRef.get
    searchPathRef.set sp
    let singleEnv? ← try
        let ti ← IO.monoMsNow
        let env ← importModules (validRoots.map ({ module := · })) {} (loadExts := false) (level := .private)
        let dt := (← IO.monoMsNow) - ti
        pure (some (env.setExporting false, dt))
      catch _ =>
        pure none
      finally
        searchPathRef.set saved
    if let some (env, importMs) := singleEnv? then
      let saved2 ← searchPathRef.get
      searchPathRef.set sp
      let mut audited : NameSet := {}
      let mut seen : NameSet := {}
      try
        match ← mkAuditContext env sysrootLib with
        | ctx =>
          runAllFourVectorAudits ctx { cfg with resolution? := none }
          for mi in env.header.modules do
            seen := seen.insert mi.module
            if ctx.isToolchainModule mi.module then
              pure ()
            else if modSet.contains mi.module && !bad.contains mi.module then
              audited := audited.insert mi.module
            else
              report .oleanOutsideApprovedRoot mi.module mi.module
                "loaded non-toolchain module resolved outside the approved build directory"
      finally
        searchPathRef.set saved2
      -- Any newly discovered transitive toolchain module (beyond `extOrder`, which already passed
      -- `validateOleanFile` pre-import) also has its binary header validated when `bad` is non-empty
      -- or `validateToolchainBinaries` is requested.
      let wantTcBin := (cfg.resolution?.map (·.validateToolchainBinaries)).getD false
      let tcSeen := seen.toArray.filter isToolchainName
      auditOleanResolutionAndShadowing tcSeen
        { sysrootLibDir := sysrootLib, approvedBuildRoots := #[], searchPath? := some sp,
          validateToolchainBinaries := wantTcBin, header := hdr }
      let stray := (mods.filter fun m => !audited.contains m).size
      let t1 ← IO.monoMsNow
      modify fun s => { s with modulesChecked := audited.size, elapsedMs := t1 - t0, importMs, strayArtifacts := stray }
      return
  -- 2b. General conflict-partitioning fallback (when `bad` is non-empty or roots conflict).
  let mut inScope : NameSet := {}
  for r in validRoots do
    match buildClosure info r with
    | some cl => inScope := cl.toList.foldl (·.insert ·) inScope
    | none => report .auditFuelExhausted r r "import closure exhausted its fuel"
  let stray := (mods.filter fun m => !inScope.contains m && !bad.contains m).size
  let mut alive : NameSet :=
    info.fold (fun acc m _ => if inScope.contains m && !bad.contains m then acc.insert m else acc) {}
  for m in mods do
    if !inScope.contains m then continue
    if let some i := info[m]? then
      for x in i.imports do
        if bad.contains x then
          report .environmentLoadFailed m m s!"imports {x}, which failed Vector 3"
          alive := alive.erase m
  let mut covered : NameSet := {}
  let mut batches : Array (Array Name × NameSet × Std.HashMap Name (Name × ConstantInfo)) := #[]
  for _ in [0:mods.size + 1] do
    let cands := mods.filter fun m => alive.contains m && !covered.contains m
    if cands.isEmpty then break
    let importedByCand : NameSet := cands.foldl (fun acc m =>
      (info.getD m { imports := #[], constants := #[] }).imports.foldl (·.insert ·) acc) {}
    let sinks := cands.filter (!importedByCand.contains ·)
    let sinks := sinks.filter (·.isAtomic) ++ sinks.filter (!·.isAtomic)
    let mut progress := false
    for s in sinks do
      let some cl := buildClosure info s
        | report .auditFuelExhausted s s "import closure exhausted its fuel"; alive := alive.erase s; continue
      if cl.toList.any (fun x => modSet.contains x && !alive.contains x) then
        report .environmentLoadFailed s s "imports an unloadable module"; alive := alive.erase s; progress := true; continue
      match addToBatch info {} cl.toList with
      | .error (n, a, b) =>
        report .environmentLoadFailed s s s!"its own import closure declares {n} in both {a} and {b}"
        alive := alive.erase s
        progress := true
      | .ok _ =>
        let mut placed := false
        for bi in [0:batches.size] do
          if placed then break
          let (bRoots, members, owners) := batches[bi]!
          let fresh := cl.toList.filter (!members.contains ·)
          if let .ok owners' := addToBatch info owners fresh then
            batches := batches.set! bi (bRoots.push s, fresh.foldl (·.insert ·) members, owners')
            placed := true
        unless placed do
          if let .ok owners := addToBatch info {} cl.toList then batches := batches.push (#[s], cl, owners)
        covered := cl.toList.foldl (·.insert ·) covered
        progress := true
    unless progress do break
  -- 3. Import and audit each batch.
  let saved ← searchPathRef.get
  searchPathRef.set sp
  let mut audited : NameSet := {}
  let mut toolchain : NameSet := {}
  let mut seen : NameSet := {}
  let mut importMs := 0
  try
    for (bRoots, _, _) in batches do
      let ti ← IO.monoMsNow
      let env? ← try
          let env ← importModules (bRoots.map ({ module := · })) {} (loadExts := false) (level := .private)
          importMs := importMs + ((← IO.monoMsNow) - ti)
          pure (some (env.setExporting false))
        catch e =>
          for r in bRoots do report .environmentLoadFailed r r s!"importModules failed: {e}"
          pure none
      let some env := env? | continue
      let ctx ← mkAuditContext env sysrootLib none toolchain
      toolchain := ctx.toolchain
      runAllFourVectorAudits ctx { cfg with resolution? := none } audited
      for mi in env.header.modules do
        seen := seen.insert mi.module
        if ctx.isToolchainModule mi.module then
          pure ()
        else if modSet.contains mi.module && !bad.contains mi.module then
          audited := audited.insert mi.module
        else
          report .oleanOutsideApprovedRoot mi.module mi.module
            "loaded non-toolchain module resolved outside the approved build directory"
  finally
    searchPathRef.set saved
  for m in mods do
    if alive.contains m && !audited.contains m then
      report .environmentLoadFailed m m "validated module was not covered by any import batch"
  let wantTcBin := (cfg.resolution?.map (·.validateToolchainBinaries)).getD false
  let tcSeen := seen.toArray.filter isToolchainName
  auditOleanResolutionAndShadowing tcSeen
    { sysrootLibDir := sysrootLib, approvedBuildRoots := #[], searchPath? := some sp,
      validateToolchainBinaries := wantTcBin, header := hdr }
  let t1 ← IO.monoMsNow
  modify fun s => { s with modulesChecked := audited.size, elapsedMs := t1 - t0, importMs, strayArtifacts := stray }

/-- Run an `AuditM` action from scratch. -/
def AuditM.run' (x : AuditM α) : IO (α × AuditSummary) := StateT.run x {}

end

end Anneal.Proto.OleanShadowAndOverrideAuditProto
