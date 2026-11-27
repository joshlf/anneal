import Lean

/-!
# Prototype: `.olean` private-name, unreferenced-axiom, shadowing, and compiler-override audits

Track P prototype (never merged). Pure, total `Lean` / `IO` audit checks for four trust-boundary
gaps in the compiled-environment auditors, pinned to Lean 4.34.1:

1. **Vector 1 — `_private.<mod>.0.<user>` namespace spoofing.** A structural parser
   (`parsePrivateName`) for the `mkPrivateName` encoding, declaring-module binding, and user-suffix
   anti-spoofing (`auditPrivateNames`).
2. **Vector 2 — unreferenced top-level axioms (`leanprover/lean4#16781`).** Reachability-only
   collectors (`Lean.collectAxioms`, `#print axioms`) never see an axiom that no checked root
   mentions. `auditUnreferencedAxioms` sweeps every axiom in every non-toolchain module's data,
   in `env.constants.map₂`, and in the kernel environment, and classifies each one.
3. **Vector 3 — `.olean` resolution, shadowing, symlinks and binary headers
   (`leanprover/lean4#16737`).** `pathWithinRoot` (component-boundary root containment without
   symlinks), `auditOleanResolutionAndShadowing` (`Lean.findOLean` + multi-root probing), and a
   pure `ByteArray` header / compacted-region validator (`validateOleanBinaryBytes`).
4. **Vector 4 — `Init.ShareCommon` (`leanprover/lean4#16779`), compiler-override hooks
   (`google/zerocopy#4321`), and opaque-theorem readiness (`leanprover/lean4#14896`).**
   `auditShareCommon`, `auditCompilerHooks`, the structural scanner `scanOpaqueTheoremReliance`,
   and the kernel replay oracle `checkOpaqueTheoremReplay`.

`runAllFourVectorAudits` runs all of them over one environment.

Totality: every traversal is structurally recursive or explicitly fuel-bounded; running out of
fuel is reported as `auditFuelExhausted` (fail closed). This file declares nothing `partial` or
`unsafe` and uses no `sorry` or `native_decide`.

Toolchain modules are identified by name *and* provenance: a module counts as a toolchain module
only if its name is under a toolchain root and its `.olean` resolves (via `Lean.findOLean`) to a
regular, symlink-free file inside the canonical sysroot library directory.
-/

open Lean

namespace Anneal.Proto.OleanShadowAndOverrideAuditProto

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
declaration of the environment being elaborated. -/
def ownerOf (ctx : AuditContext) (n : Name) : Option Name :=
  match origin? ctx.env n with
  | some m => some m
  | none => if ctx.env.contains n then ctx.liveModule? else none

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
    let data ← mkModuleData env
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

/-- Transitive kernel dependency closure of `roots` (roots included). `none` = fuel exhausted. -/
def depClosure (env : Environment) (roots : Array Name) (fuel : Nat) : Option NameSet := Id.run do
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
      let some ci := env.find? n | continue
      for d in declEdges ci do
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

/-- Components of a name, root first (structural recursion on `Name`). -/
def nameParts : Name → Array NamePart
  | .anonymous => #[]
  | .str p s => (nameParts p).push (.str s)
  | .num p n => (nameParts p).push (.num n)

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

def privateMarker : NamePart := .str "_private"

/-- Structural parser for Lean's `mkPrivateName` encoding `_private.<mod>.0.<user>`.
`.ok none` means the name has no `_private` component at all. -/
def parsePrivateName (n : Name) : Except PrivateNameError (Option PrivateNameView) :=
  let ps := (nameParts n).toList
  let markers := ps.filter (· == privateMarker)
  if markers.isEmpty then .ok none
  else match ps with
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
          else if userParts.isEmpty then .error .emptyUser
          else .ok (some { module := partsToName modParts, user := partsToName userParts })
    | [] => .ok none

/-- Constants whose names are reserved for the kernel, the foundations, or native evaluation. -/
def reservedConstantNames : List Name :=
  [``sorryAx, ``propext, ``Quot.sound, ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind,
   ``Classical.choice, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler,
   ``Lean.reduceBool, ``Lean.reduceNat, ``Eq, ``Eq.rec, ``Eq.refl, ``HEq, ``Acc.rec,
   ``Nat, ``String, ``Decidable.decide]

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

/-- Components Lean appends when it *realizes* auxiliary declarations of an existing declaration
in the module that first needs them (matcher equations and splitters, equation lemmas, unfolding
lemmas, functional induction / cases principles, reduced-arity compiler copies). -/
def isRealizedAuxComponent : NamePart → Bool
  | .str s =>
    hasNumSuffix s "eq_" || hasNumSuffix s "match_" || hasNumSuffix s "proof_" ||
    hasNumSuffix s "congr_eq_" ||
    ["eq_def", "eq_unfold", "splitter", "induct", "induct_unfolding", "fun_cases",
     "fun_cases_unfolding"].contains s ||
    -- compiler-internal components (`_redArg`, `_sparseCasesOn_<n>`, `_unfold`, ...), but never
    -- the private marker or a native-evaluation component
    (s.startsWith "_" && s != "_private" && !s.startsWith "_native")
  | .num _ => false

/-- A private user suffix that is a realized auxiliary of an existing declaration: some proper
prefix `base` of `user` is an imported constant whose owning module satisfies `baseOwnerOk` (a
genuine toolchain / privileged module, or the declaring module itself, whose *public* declaration
it then is) and every remaining component is a realized-auxiliary component. -/
def isRealizedAuxOfForeign (ctx : AuditContext) (owner user : Name) (baseOwnerOk : Name → Bool) : Bool :=
  let ps := (nameParts user).toList
  (List.range ps.length).any fun k =>
    k > 0 &&
    let base := partsToName (ps.take k)
    let rest := ps.drop k
    rest.all isRealizedAuxComponent &&
    -- `base` itself, or `base` as a private declaration of a module named by one of its prefixes
    -- (the embedded module must then be the module that actually declares it).
    let privCands := (Name.mkNum (`_private ++ owner) 0 ++ base, owner) :: (List.range k).filterMap fun j =>
      if j == 0 then none else
      let mod := partsToName (ps.take j)
      some (Name.mkNum (`_private ++ mod) 0 ++ base, mod)
    (match origin? ctx.env base with
     | some bm => baseOwnerOk bm
     | none => false) ||
    privCands.any fun (pn, mod) =>
      match origin? ctx.env pn with
      | some bm => bm == mod && baseOwnerOk bm
      | none => false

/-- User-suffix spoofing check for a private name owned by non-toolchain module `owner`. Realized
auxiliaries of genuine toolchain / privileged declarations (e.g. matcher equations of a `Trusted`
declaration realized in the module that first rewrites with them) are not spoofs. -/
def userSuffixSpoof? (ctx : AuditContext) (owner : Name) (v : PrivateNameView) : Option String :=
  let root := v.user.getRoot
  if reservedConstantNames.contains v.user then
    some s!"user suffix {v.user} spoofs a reserved foundational / native-evaluation constant"
  else if isToolchainName v.user then
    if isRealizedAuxOfForeign ctx owner v.user (fun bm => ctx.isToolchainModule bm || bm == owner) then none
    else some s!"user suffix {v.user} is under a reserved toolchain root"
  else if privilegedRoots.contains root && owner.getRoot != root then
    if isRealizedAuxOfForeign ctx owner v.user (fun bm => (bm.getRoot == root && !ctx.isToolchainModule bm) || bm == owner) then none
    else some s!"user suffix {v.user} spoofs privileged namespace {root} from module {owner}"
  else none

/-- Check one name owned by non-toolchain module `owner`. `isIROnly` names (extra constant names
created by the code generator) may carry the specialization encoding, in which case the key
segment may be a private name of an existing foreign declaration. -/
def checkPrivateName (ctx : AuditContext) (owner : Name) (n : Name) (isIROnly : Bool) : PureAuditM Unit := do
  let segs := if isIROnly then splitAtSegments n else [n]
  let segs := if segs.length > 1 then segs else [n]
  let mut i := 0
  for seg in segs do
    -- Every segment but the last is a specialization key (possibly itself nested).
    let isKey := i + 1 < segs.length
    i := i + 1
    match parsePrivateName seg with
    | .error e => report .malformedPrivateName n owner e.render
    | .ok none => pure ()
    | .ok (some v) =>
      if isKey then
        -- Specialization key: must be an existing declaration whose owner is the embedded module.
        unless ownerOf ctx seg == some v.module do
          report .privateModuleMismatch n owner
            s!"specialization key {seg} does not resolve to a declaration of {v.module}"
      else
        unless v.module == owner do
          report .privateModuleMismatch n owner s!"embedded module {v.module} is not the declaring module {owner}"
        if let some why := userSuffixSpoof? ctx owner v then
          report .privateUserSuffixSpoof n owner why

/-- Vector 1 over every non-toolchain module (and the live module): declarations, IR-only extra
names, and every declaration name that a compiler-hook extension entry targets. -/
def auditPrivateNames (ctx : AuditContext) (views : Array ModuleView) : AuditM Unit := do
  runPerView views fun v => do
    for n in v.data.constNames do
      checkPrivateName ctx v.module n false
    for n in v.data.extraConstNames do
      checkPrivateName ctx v.module n true
    modify fun s => { s with declsChecked := s.declsChecked + v.data.constNames.size + v.data.extraConstNames.size }
  -- Live `env.constants.map₂` (may contain constants that `mkModuleData` would not export).
  if let some lm := ctx.liveModule? then
    let ((), s) := (do
      for (n, _) in ctx.env.constants.map₂.toList do
        checkPrivateName ctx lm n false : PureAuditM Unit).run {}
    absorb s

/-! ## Vector 2 — whole-environment axiom sweep -/

structure AxiomPolicy where
  allowClassicalChoice : Bool := true
  allowAssumptions : Bool := false
  allowedAssumptions : NameSet := {}
  allowedAssumptionModules : NameSet := {}
  /-- Accept a module-system environment only when its private data is provably loaded. -/
  closureFuel : Nat := 2000000
  deriving Inhabited

/-- Foundational axioms, admitted only together with their declaring toolchain module. -/
def foundationalAxioms (p : AxiomPolicy) : List (Name × Name) :=
  [(``propext, `Init.Core), (``Quot.sound, `Init.Prelude)] ++
    (if p.allowClassicalChoice then [(``Classical.choice, `Init.Prelude)] else [])

def isSorryOrNativeName (n : Name) : Bool :=
  n == ``sorryAx || [``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler].contains n ||
  (nameParts n).any (fun | .str s => s.startsWith "_native" | _ => false) ||
  (match parsePrivateName n with
   | .ok (some v) => reservedConstantNames.contains v.user
   | _ => false)

def isFoundationalOk (ctx : AuditContext) (p : AxiomPolicy) (n : Name) : Bool :=
  match origin? ctx.env n with
  | some m => ctx.isToolchainModule m && (foundationalAxioms p).contains (n, m)
  | none => false

def isAssumptionOk (ctx : AuditContext) (p : AxiomPolicy) (n : Name) : Bool :=
  p.allowAssumptions &&
  (match ownerOf ctx n with
   | some m =>
     !ctx.isToolchainModule m && m.getRoot == `Assumptions && n.getRoot == `Assumptions &&
     (p.allowedAssumptions.contains n || p.allowedAssumptionModules.contains m)
   | none => false) &&
  (parsePrivateName n matches .ok none)

/-- Whether a module-system environment provably has the private data of every non-toolchain
module loaded: not exporting, and every non-toolchain import is an `import all`. -/
def privateDataLoaded (ctx : AuditContext) : Bool :=
  !ctx.env.isExporting &&
  ctx.env.header.modules.all fun mi => ctx.isToolchainModule mi.module || mi.importAll

/-- Vector 2. With `roots? = some roots`, reachable axioms are classified against the policy and
every other non-toolchain axiom is reported as unreferenced; with `roots? = none` every
non-admitted non-toolchain axiom is reported as unreferenced. -/
def auditUnreferencedAxioms (ctx : AuditContext) (views : Array ModuleView) (p : AxiomPolicy)
    (roots? : Option (Array Name)) : AuditM Unit := do
  let env := ctx.env
  if env.header.isModule && !privateDataLoaded ctx then
    report .exportedOnlyEnvironment .anonymous env.header.mainModule
      "module-system environment without loaded private data: `.olean.private` axioms may be hidden"
    return
  -- Inventory: (i) every module's stored constants, (ii) live `map₂`.
  let mut inventory : NameSet := {}
  let mut candidates : Array (Name × Name) := #[]
  for h : i in [0:env.header.moduleData.size] do
    let d := env.header.moduleData[i]
    let m := (env.header.modules[i]?.map (·.module)).getD .anonymous
    let isTool := ctx.isToolchainModule m
    for ci in d.constants do
      if let .axiomInfo _ := ci then
        inventory := inventory.insert ci.name
        unless isTool do candidates := candidates.push (ci.name, m)
  for v in views do
    if v.idx?.isNone then
      for ci in v.data.constants do
        if let .axiomInfo _ := ci then
          unless inventory.contains ci.name do
            inventory := inventory.insert ci.name
            candidates := candidates.push (ci.name, v.module)
  for (n, ci) in env.constants.map₂.toList do
    if let .axiomInfo _ := ci then
      unless inventory.contains n do
        inventory := inventory.insert n
        candidates := candidates.push (n, (ownerOf ctx n).getD env.header.mainModule)
  -- (iii) kernel environment: every axiom must be inventoried.
  let kenv := env.checked.get
  let kernelAxioms : Array Name :=
    kenv.constants.foldStage2 (fun acc n ci => if ci matches .axiomInfo _ then acc.push n else acc)
      (kenv.constants.map₁.fold (fun acc n ci => if ci matches .axiomInfo _ then acc.push n else acc) #[])
  for n in kernelAxioms do
    unless inventory.contains n do
      let owner := (ownerOf ctx n).getD env.header.mainModule
      report .uninventoriedKernelAxiom n owner "axiom present in the kernel environment but in no module inventory"
      inventory := inventory.insert n
      candidates := candidates.push (n, owner)
  modify fun s => { s with axiomsSwept := s.axiomsSwept + candidates.size }
  -- Reachability.
  let reachable ← match roots? with
    | none => pure ({} : NameSet)
    | some roots =>
      match depClosure env roots p.closureFuel with
      | some s => pure s
      | none =>
        report .auditFuelExhausted .anonymous env.header.mainModule "axiom reachability closure exhausted its fuel"
        return
  -- Reachable axioms (any origin).
  for n in reachable do
    let some ci := env.find? n | continue
    unless ci matches .axiomInfo _ do continue
    if isFoundationalOk ctx p n || isAssumptionOk ctx p n then continue
    report .referencedUnapprovedAxiom n ((ownerOf ctx n).getD .anonymous) "axiom reachable from a checked root is not admitted"
  -- Unreferenced non-toolchain axioms.
  for (n, m) in candidates do
    if reachable.contains n then continue
    if isAssumptionOk ctx p n then continue
    if isSorryOrNativeName n then
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

structure OleanHeaderConfig where
  expectedVersion? : Option String := some "4.34.1"
  expectedGithash? : Option String := some "5045d0056413266e57c625dcd7c365b10e377c52"
  maxBytes : Nat := 512 * 1024 * 1024
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
/-- Largest constructor tag of the Lean runtime (`LeanMaxCtorTag`). -/
def maxCtorTag : Nat := 244

/-- Pure, total validator of Lean 4.34.1's 88-byte `.olean` header (shared by `.olean`,
`.olean.server`, `.olean.private`, `.ir.sig`, `.ir`) and of the compacted region's root object. -/
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
  return { version, githash, gmp := flags &&& 1 == 1, baseAddr := base, rootPtr := root,
           rootOffset := off, rootSize := csSz, fileSize := size }

/-- Read and validate one artifact part. The size limit is checked from metadata before reading. -/
def validateOleanFile (p : System.FilePath) (cfg : OleanHeaderConfig := {}) :
    IO (Except String OleanHeaderInfo) := do
  let md ← try p.metadata catch e => return .error s!"cannot stat {p}: {e}"
  if md.byteSize.toNat > cfg.maxBytes then
    return .error (OleanHeaderError.tooLarge md.byteSize.toNat cfg.maxBytes).render
  let bs ← try IO.FS.readBinFile p catch e => return .error s!"cannot read {p}: {e}"
  return match validateOleanBinaryBytes bs cfg with
    | .ok i => .ok i
    | .error e => .error e.render

def stripTrailingSlashes (s : String) : String :=
  let rec go : List Char → List Char
    | [] => []
    | c :: cs => if c == '/' && cs.all (· == '/') then [] else c :: go cs
  let r := String.ofList (go s.toList)
  if r.isEmpty && s.startsWith "/" then "/" else r

/-- Component-boundary root containment. `target` must be lexically `root/<rel>` with no empty,
`.` or `..` components in `<rel>`; every component from the root down must be a non-symlink
(intermediate directories, final regular file); and the canonical target must be exactly the
canonical root followed by `<rel>`. Returns the canonical target. -/
def pathWithinRoot (root target : System.FilePath) : IO (Except String System.FilePath) := do
  unless root.isAbsolute && target.isAbsolute do return .error "paths must be absolute"
  let rootStr := stripTrailingSlashes root.toString
  let tStr := target.toString
  let pre := if rootStr == "/" then "/" else rootStr ++ "/"
  unless tStr.startsWith pre do return .error s!"{target} is not under root {root}"
  let rel := (tStr.drop pre.length).toString
  let comps := rel.splitOn "/"
  if comps.isEmpty || comps.any (fun c => c.isEmpty || c == "." || c == "..") then
    return .error s!"{target} has an empty, `.` or `..` component below {root}"
  let realRoot ← try IO.FS.realPath ⟨rootStr⟩ catch _ => return .error s!"root {root} does not exist"
  let mut cur : System.FilePath := ⟨rootStr⟩
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
  let realTarget ← try IO.FS.realPath target catch _ => return .error s!"cannot canonicalize {target}"
  let expected := comps.foldl (fun (acc : System.FilePath) (c : String) => acc / (c : System.FilePath)) realRoot
  unless realTarget.components == expected.components do
    return .error s!"{target} canonicalizes to {realTarget}, not {expected}"
  return .ok realTarget

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

/-- Canonical identity of a search-path root (deduplicates repeated `LEAN_PATH` entries). -/
def canonicalRoot (p : System.FilePath) : IO String := do
  try pure (← IO.FS.realPath p).toString catch _ => pure s!"<missing>{p}"

/-- Vector 3. For every module: `Lean.findOLean` resolution, multi-root shadowing of any artifact
part, toolchain-name shadowing outside the sysroot, approved-root containment of the resolved
`.olean` and every existing companion part, and binary header validation. -/
def auditOleanResolutionAndShadowing (mods : Array Name) (cfg : ResolutionConfig) : AuditM Unit := do
  let sp ← match cfg.searchPath? with
    | some sp => pure sp
    | none => searchPathRef.get
  let sysCanon ← canonicalRoot cfg.sysrootLibDir
  let mut roots : Array (System.FilePath × String) := #[]
  for r in sp do
    let c ← canonicalRoot r
    unless roots.any (·.2 == c) do roots := roots.push (r, c)
  let saved ← searchPathRef.get
  searchPathRef.set sp
  let mut toValidate : Array (Name × System.FilePath) := #[]
  try
    for m in mods do
      let isTool := isToolchainName m
      let rel := modRelPath m
      -- Multi-root probing of every part.
      let mut present : Array String := #[]
      for (r, c) in roots do
        let mut here := false
        for ext in partExts do
          if ← entryExists ⟨(r / rel).toString ++ "." ++ ext⟩ then here := true
        if here then
          present := present.push c
          if isTool && c != sysCanon then
            report .toolchainShadowed m m s!"toolchain module has artifacts in non-sysroot root {r}"
      if present.size ≥ 2 then
        report .oleanShadowed m m s!"module artifacts present in {present.size} search-path roots: {present}"
      -- `Lean.findOLean` resolution and containment.
      let resolved ← try pure (some (← findOLean m)) catch _ => pure none
      let some olean := resolved
        | report .oleanUnresolved m m "Lean.findOLean cannot resolve the module"; continue
      let approved := if isTool then #[cfg.sysrootLibDir] else cfg.approvedBuildRoots
      let mut root? : Option System.FilePath := none
      for r in approved do
        if root?.isNone then
          if let .ok _ ← pathWithinRoot r olean then root? := some r
      let some root := root?
        | report .oleanOutsideApprovedRoot m m s!"{olean} is not a symlink-free regular file inside an approved root"; continue
      let base := (olean.toString.dropEnd 6).toString
      for ext in partExts do
        let p : System.FilePath := ⟨base ++ "." ++ ext⟩
        unless ← entryExists p do continue
        match ← pathWithinRoot root p with
        | .error e => report .oleanOutsideApprovedRoot m m s!"companion part: {e}"
        | .ok _ =>
          if cfg.validateBinaries && (!isTool || cfg.validateToolchainBinaries) then
            toValidate := toValidate.push (m, p)
  finally
    searchPathRef.set saved
  -- Binary validation of every part, in parallel IO tasks.
  let tasks ← toValidate.mapM fun (m, p) => do
    let t ← IO.asTask (validateOleanFile p cfg.header)
    return (m, p, t)
  for (m, p, t) in tasks do
    match ← IO.wait t with
    | .ok (.ok _) => modify fun s => { s with oleansChecked := s.oleansChecked + 1 }
    | .ok (.error e) => report .oleanHeaderInvalid m m s!"{p}: {e}"
    | .error e => report .oleanHeaderInvalid m m s!"{p}: {e}"

/-- Toolchain modules by name *and* provenance: toolchain-named modules whose `.olean` resolves to a
symlink-free regular file inside the canonical sysroot library. Other toolchain-named modules are
reported and are *not* treated as toolchain modules by the environment audits. -/
def computeToolchainModules (env : Environment) (sysrootLibDir : System.FilePath)
    (known : NameSet := {}) : AuditM NameSet := do
  let mut out : NameSet := known
  for mi in env.header.modules do
    let m := mi.module
    unless isToolchainName m do continue
    if known.contains m then continue
    let resolved ← try pure (some (← findOLean m)) catch _ => pure none
    match resolved with
    | none => report .oleanUnresolved m m "toolchain-named module cannot be resolved"
    | some p =>
      match ← pathWithinRoot sysrootLibDir p with
      | .ok _ => out := out.insert m
      | .error e => report .oleanOutsideApprovedRoot m m s!"toolchain-named module outside the sysroot: {e}"
  return out

/-- Bounded walk of a build library directory collecting the module names of its `.olean` files. -/
def listOleanModules (libDir : System.FilePath) (fuel : Nat := 100000) : AuditM (Array Name) := do
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
        if md.type == .dir then
          pending := (entry.path, pre.str entry.fileName) :: pending
        else if md.type == .file && entry.fileName.endsWith ".olean" then
          result := result.push (pre.str (entry.fileName.dropEnd 6).toString)
  unless done do report .auditFuelExhausted .anonymous .anonymous s!"directory walk of {libDir} exhausted its fuel"
  return result

/-! ## Vector 4a — `Init.ShareCommon` -/

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

def isShareCommonConst (env : Environment) (c : Name) : Bool :=
  shareCommonSymbols.contains c || origin? env c == some shareCommonModule

def constEdges (e : Expr) (acc : NameSet) : NameSet :=
  e.getUsedConstants.foldl (·.insert ·) acc

/-- Value-level constants of an LCNF body: `let` values (constants, projections, constructors,
full / partial applications), `cases` types and alternative constructors. Types are not walked
(compiled code can only reach a constant through a value). Fuel-bounded; `none` = exhausted. -/
def lcnfCodeConsts (fuel : Nat) (c : Compiler.LCNF.Code .pure) (acc : NameSet) : Option NameSet :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match c with
    | .let decl k =>
      let acc := match decl.value with
        | .const n _ _ _ => acc.insert n
        | .proj typeName _ _ _ => acc.insert typeName
        | .ctor info _ _ => acc.insert info.name
        | .fap fn _ _ | .pap fn _ _ => acc.insert fn
        | _ => acc
      lcnfCodeConsts fuel k acc
    | .fun decl k _ => do
      let acc ← lcnfCodeConsts fuel decl.value acc
      lcnfCodeConsts fuel k acc
    | .jp decl k => do
      let acc ← lcnfCodeConsts fuel decl.value acc
      lcnfCodeConsts fuel k acc
    | .jmp _ _ => some acc
    | .cases cs => do
      let mut acc := acc.insert cs.typeName
      for alt in cs.alts do
        match alt with
        | .alt ctor _ code _ => acc ← lcnfCodeConsts fuel code (acc.insert ctor)
        | .default code => acc ← lcnfCodeConsts fuel code acc
        | .ctorAlt info code _ => acc ← lcnfCodeConsts fuel code (acc.insert info.name)
      return acc
    | .return _ => some acc
    | .unreach _ => some acc
    | _ => some acc

def lcnfDeclConsts (d : Compiler.LCNF.Decl .pure) (fuel : Nat) : Option NameSet :=
  let acc := constEdges d.type {}
  match d.value with
  | .code c => lcnfCodeConsts fuel c acc
  | .extern _ => some acc

/-- Vector 4a: direct imports of `Init.ShareCommon` and references to its surface from kernel
declarations, LCNF bodies (`baseExt` / `monoExt`) and compiled IR (`IR.declMapExt`). -/
def shareCommonView (ctx : AuditContext) (fuel : Nat) (v : ModuleView) : PureAuditM Unit := do
  let env := ctx.env
  do
    let imports := if v.idx?.isNone then env.header.imports else v.data.imports
    if imports.any (·.module == shareCommonModule) then
      report .shareCommonImport v.module v.module "non-toolchain module imports Init.ShareCommon"
    -- Kernel declarations are screened by `kernelScanView` (shared with Layer A).
    -- LCNF and IR, per stored entry (imported) or per local declaration (live).
    let names := v.data.constNames ++ v.data.extraConstNames
    let mut lcnf : Array (Compiler.LCNF.Decl .pure) := #[]
    let mut ir : Array IR.Decl := #[]
    match v.idx? with
    | some i =>
      lcnf := Compiler.LCNF.baseExt.getModuleEntries env i ++ Compiler.LCNF.monoExt.getModuleEntries env i ++
        Compiler.LCNF.baseExt.getModuleIREntries env i ++ Compiler.LCNF.monoExt.getModuleIREntries env i
      ir := IR.declMapExt.getModuleEntries env i ++ IR.declMapExt.getModuleIREntries env i
    | none =>
      for n in names do
        if let some d := Compiler.LCNF.getDeclCore? env Compiler.LCNF.baseExt n then lcnf := lcnf.push d
        if let some d := Compiler.LCNF.getDeclCore? env Compiler.LCNF.monoExt n then lcnf := lcnf.push d
        if let some d := IR.findEnvDecl env n then ir := ir.push d
    for d in lcnf do
      match lcnfDeclConsts d fuel with
      | none => report .auditFuelExhausted d.name v.module "LCNF body walk exhausted its fuel"
      | some cs =>
        for c in cs do
          if isShareCommonConst env c then
            report .shareCommonReference d.name v.module s!"LCNF body references {c}"
    for d in ir do
      for c in IR.collectUsedDecls env [d] do
        if isShareCommonConst env c then
          report .shareCommonReference d.name v.module s!"compiled IR references {c}"

/-- Every constant of the `Init.ShareCommon` surface present in `env`: the explicit symbols plus
every constant stored by the `Init.ShareCommon` module (one hash lookup per node in the scan). -/
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

/-- Kernel references to the `Init.ShareCommon` surface from one declaration (type, value
including theorem and opaque bodies, recursor rules), screened by Lean's cached `Expr.find?`. -/
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

/-- Number of entries a module stored for the extension named `ext`. -/
def moduleExtEntryCount (d : ModuleData) (ext : Name) : Nat :=
  d.entries.foldl (fun acc (n, es) => if n == ext then acc + es.size else acc) 0

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

/-- The code generator marks the generated `I.ctorIdx` of every inductive `I` `@[macro_inline]`.
Exempt exactly that: `n = I.ctorIdx`, `I` an inductive, both owned by the same module `m`. -/
def isGeneratedMacroInline (ctx : AuditContext) (m n : Name) : Bool :=
  match n with
  | .str I "ctorIdx" =>
    (ctx.env.find? I matches some (.inductInfo _)) && ownerOf ctx I == some m && ownerOf ctx n == some m
  | _ => false

/-- Vector 4b. Typed `.olean` and `.ir` entries (`getModuleEntries` / `getModuleIREntries`),
generic per-extension entry counts (catching inaccessible extensions such as `tagged_return` and
the sparse-cases tag), live state of the live module, and foreign compiler tags. -/
def hooksView (ctx : AuditContext) (generic : Array (Name × String)) (sparseExt? : Option Name)
    (v : ModuleView) : PureAuditM Unit := do
  let env := ctx.env
  let hook (n m : Name) (what : String) : PureAuditM Unit := do
    modify fun s => { s with hookEntriesChecked := s.hookEntriesChecked + 1 }
    report .compilerOverrideHook n m what
  do
    let m := v.module
    -- Generic entry counts (any extension in `hardHookExtensions`).
    for (extName, label) in generic do
      let k := moduleExtEntryCount v.data extName
      if k > 0 then hook m m s!"{label}: module stores {k} entr{if k == 1 then "y" else "ies"}"
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
      for e in Compiler.CSimp.ext.ext.getModuleEntries env i do
        let ent := match e with | .global a => a | .scoped _ a => a
        hook ent.fromDeclName m s!"csimp: {ent.fromDeclName} ↦ {ent.toDeclName}"
      for installer in Compiler.LCNF.passManagerExt.getModuleEntries env i do
        hook installer m "cpass"
      for fe in Compiler.LCNF.Simp.ConstantFold.folderExt.getModuleEntries env i do
        hook fe.declName m "constant_fold"
      for n in IR.UnboxResult.unboxAttr.ext.getModuleEntries env i ++ IR.UnboxResult.unboxAttr.ext.getModuleIREntries env i do
        hook n m "unbox"
      for n in neverExtractAttr.ext.getModuleEntries env i ++ neverExtractAttr.ext.getModuleIREntries env i do
        hook n m "never_extract"
      for (n, k) in Compiler.inlineAttrs.ext.getModuleEntries env i ++ Compiler.inlineAttrs.ext.getModuleIREntries env i do
        if isMacroInline k && !isGeneratedMacroInline ctx m n then hook n m "macro_inline"
      for entry in Compiler.LCNF.postponedCompileDeclsExt.getModuleEntries env i do
        for n in entry.declNames do
          report .postponedCompilation n m "compilation postponed (no IR stored)"
      for n in auxRecExt.getModuleEntries env i do
        unless origin? env n == some m do
          report .foreignCompilerTag n m "auxiliary-recursor tag on a foreign declaration"
      for (n, _) in noConfusionExt.getModuleEntries env i do
        unless origin? env n == some m do
          report .foreignCompilerTag n m "noConfusion tag on a foreign declaration"
    | none =>
      -- Live module: per local declaration, plus local extension state.
      for n in v.data.constNames ++ v.data.extraConstNames do
        if (Compiler.implementedByAttr.getParam? env n).isSome then hook n m "implemented_by"
        if (getExternAttrData? env n).isSome then hook n m "extern"
        if (exportAttr.getParam? env n).isSome then hook n m "export"
        if (regularInitAttr.getParam? env n).isSome then hook n m "init"
        if (builtinInitAttr.getParam? env n).isSome then hook n m "builtin_init"
        if IR.UnboxResult.unboxAttr.hasTag env n then hook n m "unbox"
        if neverExtractAttr.hasTag env n then hook n m "never_extract"
        if (Compiler.getInlineAttribute? env n).any isMacroInline && !isGeneratedMacroInline ctx m n then
          hook n m "macro_inline"
      for e in Compiler.CSimp.ext.ext.getState env |>.newEntries do
        let ent := match e with | .global a => a | .scoped _ a => a
        hook ent.fromDeclName m s!"csimp: {ent.fromDeclName} ↦ {ent.toDeclName}"
      for n in auxRecExt.getEntries env do
        unless (origin? env n).isNone do
          report .foreignCompilerTag n m "auxiliary-recursor tag on a foreign declaration"
      for entry in Compiler.LCNF.postponedCompileDeclsExt.getEntries env do
        for n in entry.declNames do
          report .postponedCompilation n m "compilation postponed (no IR stored)"
    -- Sparse-cases tags (inaccessible extension): stored entries must all be owned declarations.
    if let some se := sparseExt? then
      let stored := moduleExtEntryCount v.data se
      let owned := v.data.constNames.foldl (fun a n => if isSparseCasesOn env n then a + 1 else a) 0
      if stored > owned then
        report .foreignCompilerTag m m s!"sparse-cases tag: {stored} stored entries but only {owned} owned tagged declarations"

def auditCompilerHooks (ctx : AuditContext) (views : Array ModuleView) : AuditM Unit := do
  let mut generic : Array (Name × String) := #[]
  for (u, label) in hardHookExtensions do
    match ← findExtName u with
    | some n => generic := generic.push (n, label)
    | none => report .environmentLoadFailed u .anonymous s!"hook extension for {label} is not registered"
  let sparseExt? ← findExtName `Lean.sparseCasesOnExt
  if sparseExt?.isNone then
    report .environmentLoadFailed `Lean.sparseCasesOnExt .anonymous "sparse-cases extension is not registered"
  runPerView views (hooksView ctx generic sparseExt?)

/-! ## Vector 4c — opaque-theorem readiness (`leanprover/lean4#14896`) -/

/-- Index of the major premise of recursor-like constant `f`, if it is a kernel recursor or one of
its auxiliary `casesOn` / `recOn` wrappers. -/
def majorPremiseIdx? (env : Environment) (f : Name) : Option (Nat × RecursorVal) := do
  match env.find? f with
  | some (.recInfo rv) => return (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices, rv)
  | _ =>
    match f with
    | .str ind s =>
      let some (.recInfo rv) := env.find? (ind.str "rec") | none
      if s == "casesOn" then return (rv.numParams + 1 + rv.numIndices, rv)
      else if s == "recOn" then return (rv.numParams + rv.numMotives + rv.numIndices, rv)
      else none
    | _ => none

/-- Whether an application of recursor-like `rv` at universe levels `us` eliminates into a
non-`Prop` sort. A recursor with a motive universe parameter (one more level parameter than its
inductive) is a large eliminator; its first level argument is the motive's universe. Recursors
without that extra parameter eliminate only into `Prop`. -/
def isLargeElimination (env : Environment) (rv : RecursorVal) (us : List Level) : Bool :=
  let indLevels := match env.find? rv.getMajorInduct with
    | some ci => ci.levelParams.length
    | none => 0
  if rv.levelParams.length > indLevels then
    match us with
    | u :: _ => !(u.normalize == Level.zero)
    | [] => true
  else false

def isTheoremHead (env : Environment) (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const c _ => if (env.find? c) matches some (.thmInfo _) then some c else none
  | _ => none

/-- Whether inductive `S` lives in `Prop` (its type's final codomain is `Sort 0`). -/
def isPropInductive (env : Environment) (S : Name) : Bool :=
  match env.find? S with
  | some (.inductInfo iv) => iv.type.getForallBody.isProp
  | _ => false

/-- The δ-position test of Layer A for a single node (no recursion into subterms):
`(idx, rv)`-major premise of a non-K large elimination that is headed by a theorem, or a
projection out of a theorem-headed term of a non-`Prop` structure. -/
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
            (isTheoremHead env args[idx]).map (·, s!"major premise of {fn}")
          else none
        else none
      | none => none
    | _ => none
  | .proj S _ s =>
    if isPropInductive env S then none
    else (isTheoremHead env s).map (·, "scrutinee of Expr.proj")
  | _ => none

/-- Cheap syntactic screen applied before `opaqueHitAt?`: an application headed by a constant whose
last component is `rec`, `casesOn` or `recOn` at a non-zero first universe level, or a `.proj`. -/
def maybeOpaqueHit (e : Expr) : Bool :=
  match e with
  | .app .. =>
    match e.getAppFn with
    | .const (.str _ s) (u :: _) => (s == "rec" || s == "casesOn" || s == "recOn") && !(u == Level.zero)
    | _ => false
  | .proj .. => true
  | _ => false

/-- Pre-filter for Layer A using Lean's cached `Expr.find?`: only declarations that contain a
δ-position hit need the detailed walk. -/
def needsOpaqueScan (env : Environment) (ci : ConstantInfo) : Bool :=
  let p : Expr → Bool := fun e => maybeOpaqueHit e && (opaqueHitAt? env e).isSome
  (ci.type.find? p).isSome || ((ci.value? (allowOpaque := true)).any fun v => (v.find? p).isSome)

/-- Layer A: structural scan for theorems in kernel δ-reduction positions — the major premise of a
non-K large elimination (a recursor, `casesOn` or `recOn` whose motive is not `Prop`-valued), or
the scrutinee of `Expr.proj`. Shared subterms are visited once. `.error ()` = fuel exhausted. -/
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
  let base := (replayPrefix.str tag) ++ n
  let mut c := base
  for i in [0:1000] do
    if !env.contains c then return c
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

/-- Layer B: exact kernel-opaque replay oracle. Refuses to invoke the kernel when the closure
reaches a native evaluator. Otherwise every theorem `t` the declaration depends on (directly or
through the bodies of definitions) is replaced by a fresh *axiom* with the identical level
parameters and type; every definition whose body reaches such a theorem through definition bodies
is re-added under a fresh name with its references rewritten; then the declaration is replayed
both unchanged and with the rewriting. Proof irrelevance makes each axiom copy definitionally
equal to the theorem it replaces wherever only its type matters, so the rewritten replay fails
exactly when the kernel had to δ-unfold a theorem body. -/
def checkOpaqueTheoremReplay (env : Environment) (declName : Name) (fuel : Nat := 200000)
    (maxRenamed : Nat := 512) (heartbeats : Nat := 200000) : IO OpaqueReplayResult := do
  let some ci := env.find? declName | return .notFound
  if reachesNativeEvaluator env #[declName] fuel then return .refusedNativeEvaluator
  -- Collect definitions reachable through definition bodies, and the theorems they mention.
  let mut defs : Array Name := #[]
  let mut thms : NameSet := {}
  let mut visited : NameSet := NameSet.empty.insert declName
  let mut pending : List Name := (declEdges ci).toList
  let mut exhausted := true
  for _ in [0:fuel] do
    match pending with
    | [] => exhausted := false; break
    | n :: rest =>
      pending := rest
      if visited.contains n then continue
      visited := visited.insert n
      match env.find? n with
      | some (.thmInfo _) => thms := thms.insert n
      | some (.defnInfo dv) =>
        defs := defs.push n
        pending := (exprEdges dv.value (exprEdges dv.type {})).toList ++ pending
      | _ => pure ()
  if exhausted then return .fuelExhausted "dependency walk"
  if thms.isEmpty then return .noTheoremDependencies
  -- Definitions whose bodies reach an erased theorem (fixpoint, bounded by |defs| + 1 rounds).
  let edgesOf (n : Name) : NameSet :=
    match env.find? n with
    | some (.defnInfo dv) => exprEdges dv.value (exprEdges dv.type {})
    | _ => {}
  let mut reach : NameSet := thms
  let mut stable := false
  for _ in [0:defs.size + 1] do
    let mut changed := false
    for d in defs do
      if !reach.contains d && (edgesOf d).any reach.contains then
        reach := reach.insert d
        changed := true
    if !changed then stable := true; break
  unless stable do return .fuelExhausted "theorem-reachability fixpoint"
  let renamedDefs := defs.filter reach.contains
  if renamedDefs.size > maxRenamed then return .fuelExhausted s!"{renamedDefs.size} definitions to rewrite"
  let mut ren : NameMap Name := {}
  for t in thms do ren := ren.insert t (freshReplayName env t "thm")
  for d in renamedDefs do ren := ren.insert d (freshReplayName env d "def")
  let rw (e : Expr) : Expr := e.replace fun
    | .const n us => (ren.find? n).map (Expr.const · us)
    | _ => none
  let mut kenv := env.toKernelEnv
  -- Theorem → axiom copies.
  for t in thms do
    let some tci := env.find? t | return .fuelExhausted s!"missing theorem {t}"
    let some t' := ren.find? t | return .fuelExhausted s!"missing rename for {t}"
    let decl := Declaration.axiomDecl { name := t', levelParams := tci.levelParams, type := tci.type, isUnsafe := false }
    match kenv.addDeclCore (← kernelHeartbeatThreshold heartbeats) 0 decl none with
    | .ok k => kenv := k
    | .error e => return .fuelExhausted s!"axiom copy of {t} rejected: {kernelErrorString e}"
  -- Rewritten definitions in dependency order (bounded passes).
  let mut added : NameSet := {}
  let mut remaining := renamedDefs
  for _ in [0:renamedDefs.size + 1] do
    if remaining.isEmpty then break
    let mut next : Array Name := #[]
    for d in remaining do
      let deps := (edgesOf d).toList.filter fun x => renamedDefs.contains x && x != d
      if deps.all added.contains then
        let some (.defnInfo dv) := env.find? d | return .fuelExhausted s!"missing definition {d}"
        let some d' := ren.find? d | return .fuelExhausted s!"missing rename for {d}"
        let decl := Declaration.defnDecl { dv with name := d', type := rw dv.type, value := rw dv.value, all := [d'] }
        match kenv.addDeclCore (← kernelHeartbeatThreshold heartbeats) 0 decl none with
        | .ok k => kenv := k; added := added.insert d
        | .error e =>
          return .deltaReliance thms.size renamedDefs.size s!"rewritten definition {d} rejected: {kernelErrorString e}"
      else next := next.push d
    if next.size == remaining.size then return .fuelExhausted "definition dependency cycle"
    remaining := next
  unless remaining.isEmpty do return .fuelExhausted "definition ordering"
  -- Replay: original first (must be accepted), then rewritten.
  let mkDecl (name : Name) (type value : Expr) : Option Declaration :=
    match ci with
    | .thmInfo _ => some (.thmDecl { name, levelParams := ci.levelParams, type, value })
    | .defnInfo dv => some (.defnDecl { dv with name, type, value, all := [name] })
    | _ => none
  let some v := ci.value? (allowOpaque := true) | return .noTheoremDependencies
  let some orig := mkDecl (freshReplayName env declName "orig") ci.type v | return .noTheoremDependencies
  match env.toKernelEnv.addDeclCore (← kernelHeartbeatThreshold heartbeats) 0 orig none with
  | .error e => return .originalRejected (kernelErrorString e)
  | .ok _ => pure ()
  let some erased := mkDecl (freshReplayName env declName "erased") (rw ci.type) (rw v) | return .noTheoremDependencies
  match kenv.addDeclCore (← kernelHeartbeatThreshold heartbeats) 0 erased none with
  | .ok _ => return .clean thms.size renamedDefs.size
  | .error e => return .deltaReliance thms.size renamedDefs.size (kernelErrorString e)

/-- One traversal per kernel declaration shared by Vector 4a (`Init.ShareCommon` references) and
Layer A (opaque-theorem δ positions): Lean's cached `Expr.find?` screens type, value and recursor
rules with the union of both node predicates, and only declarations with a hit get the detailed
checks. Every compacted expression is thus read once per audit. -/
def kernelScanChunk (ctx : AuditContext) (sc : Std.HashSet Name) (structural theoremBodies : Bool) (fuel : Nat)
    (v : ModuleView) (lo hi : Nat) : PureAuditM Unit := do
  let env := ctx.env
  let p : Expr → Bool := fun e =>
    isShareCommonNode sc e || (structural && maybeOpaqueHit e && (opaqueHitAt? env e).isSome)
  let exprsOf (ci : ConstantInfo) : List Expr := Id.run do
    let value? := match ci with
      | .thmInfo _ => if theoremBodies then ci.value? (allowOpaque := true) else none
      | _ => ci.value? (allowOpaque := true)
    let mut exprs : List Expr := ci.type :: value?.toList
    if let .recInfo rv := ci then exprs := exprs ++ rv.rules.map (·.rhs)
    return exprs
  let consts := v.data.constants[lo:hi].toArray
  -- One cached traversal over the whole slice first: a module's compacted expressions share
  -- subterms across declarations, which a per-declaration `find?` would re-visit.
  let all : Expr := mkAppN (.sort .zero) (consts.foldl (fun acc ci => acc ++ (exprsOf ci).toArray) #[])
  if (all.find? p).isNone then return
  for ci in consts do
    let exprs := exprsOf ci
    unless exprs.any (fun e => (e.find? p).isSome) do continue
    for c in kernelShareCommonRefs env ci do
      report .shareCommonReference ci.name v.module s!"kernel declaration references {c}"
    if structural then
      match scanOpaqueTheoremReliance env ci fuel with
      | .error () => report .auditFuelExhausted ci.name v.module "structural opaque-theorem scan exhausted its fuel"
      | .ok hits =>
        for (t, why) in hits do
          flag .opaqueTheoremStructural ci.name v.module s!"theorem {t} in δ position ({why})"

/-- Vector 4a over modules: imports, kernel references (shared traversal), LCNF and IR. -/
def auditShareCommon (ctx : AuditContext) (views : Array ModuleView) (structural : Bool := true)
    (theoremBodies : Bool := true) (fuel : Nat := 2000000) : AuditM Unit := do
  let sc := shareCommonSet ctx.env
  runPerView views (shareCommonView ctx 100000)
  runPerView views fun v => kernelScanChunk ctx sc structural theoremBodies fuel v 0 v.data.constants.size

/-- Vector 4c Layer B on each requested declaration (hard violations). Layer A runs inside
`auditShareCommon`'s shared kernel traversal. -/
def auditOpaqueTheorems (ctx : AuditContext) (replayTargets : Array Name := #[])
    (fuel : Nat := 2000000) : AuditM Unit := do
  let env := ctx.env
  for n in replayTargets do
    let m := (ownerOf ctx n).getD .anonymous
    match ← checkOpaqueTheoremReplay env n fuel with
    | .deltaReliance e r err => report .opaqueTheoremDeltaReliance n m s!"accepted, but rejected with {e} theorem(s) opaque ({r} definition(s) rewritten): {err}"
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
  /-- Screen theorem bodies in the shared kernel traversal (Layer A and `Init.ShareCommon`
  references inside proofs). Theorem bodies are never executed and are by far the bulk of compiled
  data, so a fast sweep may turn this off; types and all other values are always screened. -/
  kernelScanTheoremBodies : Bool := true

/-- Build an audit context: toolchain modules by name and sysroot provenance. -/
def mkAuditContext (env : Environment) (sysrootLibDir : System.FilePath) (liveModule? : Option Name := none)
    (knownToolchain : NameSet := {}) : AuditM AuditContext := do
  let toolchain ← computeToolchainModules env sysrootLibDir knownToolchain
  return { env, toolchain, liveModule? }

/-- Run all four vectors over one environment, skipping modules in `exclude` (already audited). -/
def runAllFourVectorAudits (ctx : AuditContext) (cfg : FourVectorConfig := {}) (exclude : NameSet := {}) :
    AuditM Unit := do
  let t0 ← IO.monoMsNow
  let views ← nonToolchainViews ctx exclude
  modify fun s => { s with modulesChecked := s.modulesChecked + views.size }
  auditPrivateNames ctx views
  auditUnreferencedAxioms ctx views cfg.axioms cfg.axiomRoots?
  if let some rc := cfg.resolution? then
    let mods := cfg.resolutionModules?.getD (ctx.env.header.modules.map (·.module))
    auditOleanResolutionAndShadowing mods rc
  auditShareCommon ctx views cfg.runStructuralOpaqueScan cfg.kernelScanTheoremBodies
  auditCompilerHooks ctx views
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

/-- Duplicate declarations `importModules` merges instead of rejecting (independently realized
theorems: same name, type, level parameters and mutual block; mirrors the toolchain's rule, with
axiom pairs approximated by type equality — a wrong merge guess only makes the later
`importModules` fail, which is reported). -/
def mergeableDuplicate (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.type == b.type && a.levelParams == b.levelParams &&
  match a, b with
  | .thmInfo x, .thmInfo y => x.all == y.all
  | .thmInfo x, .axiomInfo y | .axiomInfo y, .thmInfo x => x.all == [y.name] && !y.isUnsafe
  | .axiomInfo x, .axiomInfo y => x.isUnsafe == y.isUnsafe
  | _, _ => false

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

1. Vector 3 on every build module first (resolution, shadowing, containment, and binary header
   validation of every artifact part), *before* any byte is handed to `readModuleData` or
   `importModules`; modules with any Vector 3 finding are not loaded.
2. Build modules are not all co-importable (two modules may realize the same auxiliary lemma), so
   the import graph and constant names are read and the import roots are partitioned into
   conflict-free batches; a module whose own closure contains a duplicate constant is reported as
   `environmentLoadFailed` (it can never be loaded) and is not imported.
3. Each batch is imported once (`.private` level, no extensions) and audited (Vectors 1, 2, 4), every
   module exactly once; Vector 3 resolution is then repeated for every toolchain module seen. -/
def auditBuildLibrary (buildLib sysrootLib : System.FilePath) (cfg : FourVectorConfig := {})
    (roots? : Option (Array Name) := none) : AuditM Unit := do
  let t0 ← IO.monoMsNow
  let sp : SearchPath := [buildLib, sysrootLib]
  let hdr := (cfg.resolution?.map (·.header)).getD {}
  let mods := (← listOleanModules buildLib).qsort Name.lt
  let before := (← get).violations.size
  -- 1. Vector 3 over build modules before loading anything.
  auditOleanResolutionAndShadowing mods
    { sysrootLibDir := sysrootLib, approvedBuildRoots := #[buildLib], searchPath? := some sp, header := hdr }
  let bad : NameSet := (← get).violations[before:].foldl (fun acc v => acc.insert v.module) {}
  -- 2. Import graph of the validated modules reachable from the library roots (default: every
  -- single-component module, i.e. every `lean_lib` root present in the build directory).
  let roots := roots?.getD (mods.filter (·.isAtomic))
  let modSet : NameSet := mods.foldl (·.insert ·) {}
  let mut info : Std.HashMap Name BuildModuleInfo := {}
  let mut todo : List Name := roots.toList.filter modSet.contains
  for _ in [0:mods.size + 1] do
    match todo with
    | [] => break
    | m :: rest =>
      todo := rest
      if info.contains m || bad.contains m then continue
      let (d, _) ← readModuleData (buildLib / (modRelPath m ++ ".olean"))
      let imps := d.imports.map (·.module)
      info := info.insert m { imports := imps, constants := d.constants }
      todo := imps.toList.filter (fun i => modSet.contains i && !info.contains i) ++ todo
  let mut inScope : NameSet := {}
  for r in roots do
    if bad.contains r then continue
    match buildClosure info r with
    | some cl => inScope := cl.toList.foldl (·.insert ·) inScope
    | none => report .auditFuelExhausted r r "import closure exhausted its fuel"
  let stray := (mods.filter fun m => !inScope.contains m && !bad.contains m).size
  -- A module importing an unloaded module is itself unloadable.
  let mut alive : NameSet := info.fold (fun acc m _ => if inScope.contains m then acc.insert m else acc) {}
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
      if cl.toList.any (!alive.contains ·) then
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
          let (roots, members, owners) := batches[bi]!
          let fresh := cl.toList.filter (!members.contains ·)
          if let .ok owners' := addToBatch info owners fresh then
            batches := batches.set! bi (roots.push s, fresh.foldl (·.insert ·) members, owners')
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
    for (roots, _, _) in batches do
      let ti ← IO.monoMsNow
      let env? ← try
          let env ← importModules (roots.map ({ module := · })) {} (loadExts := false) (level := .private)
          importMs := importMs + ((← IO.monoMsNow) - ti)
          pure (some env)
        catch e =>
          for r in roots do report .environmentLoadFailed r r s!"importModules failed: {e}"
          pure none
      let some env := env? | continue
      let ctx ← mkAuditContext env sysrootLib none toolchain
      toolchain := ctx.toolchain
      runAllFourVectorAudits ctx { cfg with resolution? := none } audited
      for mi in env.header.modules do
        seen := seen.insert mi.module
        unless ctx.isToolchainModule mi.module do audited := audited.insert mi.module
  finally
    searchPathRef.set saved
  for m in mods do
    if alive.contains m && !audited.contains m then
      report .environmentLoadFailed m m "validated module was not covered by any import batch"
  -- Toolchain modules seen: resolution / shadowing / sysroot containment (no binary re-read).
  let tcSeen := seen.toArray.filter isToolchainName
  auditOleanResolutionAndShadowing tcSeen
    { sysrootLibDir := sysrootLib, approvedBuildRoots := #[], searchPath? := some sp, header := hdr }
  let t1 ← IO.monoMsNow
  modify fun s => { s with modulesChecked := audited.size, elapsedMs := t1 - t0, importMs, strayArtifacts := stray }

/-- Run an `AuditM` action from scratch. -/
def AuditM.run' (x : AuditM α) : IO (α × AuditSummary) := StateT.run x {}

end Anneal.Proto.OleanShadowAndOverrideAuditProto
