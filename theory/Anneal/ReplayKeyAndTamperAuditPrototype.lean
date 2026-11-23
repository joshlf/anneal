/-!
# `.olean` Replay-Key Alignment, Mutual `.all` Integrity, & 18-Vector Tamper Audit Prototype

Standalone, pure-`Init` kernel-checked Lean 4 model for Anneal Fleet workstream
`ws-proto-olean-replay-key-and-tamper-audit` (`ep1-prototype-replay-key-mismatch-and-tamper-model`).

This module models and proves:
1. The `leanprover/lean4#16677` (`issue16675`) `.olean` replay key-vs-`ConstantInfo.name` mismatch
   across `.recInfo`, `.ctorInfo`, `.quotInfo`, and `.thmInfo` duplicate short-circuiting.
2. The `TrustedBoundary.lean` (`downstreamAudit` line 408 / `verifyAudit` line 607) `replayLocals`
   overwrite vulnerability when `constNames == constants.map ConstantInfo.name` and duplicate-name
   checks are omitted.
3. The `lowmem_lean` (`cl/1027843093`) multi-element mutual `.all` block invariants on
   `thmDecl`/`opaqueDecl`/`defnDecl`/`inductDecl`/`recDecl`.
4. The `pillar_1` (`cl/1027950821`) unconditional ban on `Lean.ofReduceNat`, `Lean.ofReduceBool`,
   `Lean.trustCompiler`, `._native.*`, `sorryAx`, and `unsafe`/`partial` declarations.
5. All 18 `bensherman` (`cl/1027652636`) negative elaborator/environment/artifact tamper vectors
   (`V01`–`V18`), including comment-and-string-stripping source defense-in-depth, `.olean.{server,private}`
   strict presence, `import all` private-instance leakage, `Topic.Proofs.Defs` non-exemption, and
   clean-env kernel replay isolation (`V06` & `V09`).
6. End-to-end semantic soundness of clean-env kernel replay via a genuine `SemVal` consistency model
   establishing that no audited unconditional package can inhabit `False`.
-/

namespace Anneal.ReplayKeyAndTamperAuditPrototype

/-! ## Section 1: Hierarchical Names (`SymName`) -/

/-- Component of a hierarchical Lean-style name. -/
inductive NamePart where
  | str (s : String)
  | num (k : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Hierarchical declaration / module name. -/
inductive SymName where
  | anonymous
  | str (parent : SymName) (s : String)
  | num (parent : SymName) (k : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace SymName

/-- Construct a single-component name. -/
def mkSimple (s : String) : SymName :=
  .str .anonymous s

/-- Construct a hierarchical name from a list of string segments. -/
def ofList (parts : List String) : SymName :=
  parts.foldl .str .anonymous

/-- Convert a hierarchical name to its root-to-leaf list of `NamePart`s. -/
def toParts : SymName → List NamePart
  | .anonymous => []
  | .str p s => p.toParts ++ [.str s]
  | .num p k => p.toParts ++ [.num k]

/-- Rebuild a hierarchical name from a list of `NamePart`s. -/
def ofParts (parts : List NamePart) : SymName :=
  parts.foldl (fun acc p => match p with | .str s => .str acc s | .num k => .num acc k) .anonymous

/-- Render a hierarchical name in dot-separated form. -/
def toString : SymName → String
  | .anonymous => ""
  | .str .anonymous s => s
  | .str p s => p.toString ++ "." ++ s
  | .num .anonymous k => Nat.repr k
  | .num p k => p.toString ++ "." ++ Nat.repr k

instance : ToString SymName := ⟨SymName.toString⟩

/-- True iff the name is `.anonymous`. -/
def isAnonymous : SymName → Bool
  | .anonymous => true
  | _ => false

/-- Return the leading string component, if any. -/
def getRoot (n : SymName) : Option String :=
  match n.toParts with
  | .str s :: _ => some s
  | _ => none

/-- Return the trailing string component, if any. -/
def lastStringPart? : SymName → Option String
  | .str _ s => some s
  | _ => none

/-- Check whether `pre` is a structural prefix of `n`. -/
def hasPrefix (pre n : SymName) : Bool :=
  let pp := pre.toParts
  let np := n.toParts
  pp.length <= np.length && np.take pp.length == pp

/-- Collect all non-empty proper suffixes of a list of parts. -/
def properPartSuffixes : List NamePart → List (List NamePart)
  | [] => []
  | _ :: rest =>
    let rec go : List NamePart → List (List NamePart)
      | [] => []
      | xs@(_ :: tl) => xs :: go tl
    go rest

/-- Extract all non-empty proper suffix names (e.g. `Pkg.Nat.add` ↦ `[Nat.add, add]`). -/
def properSuffixes (n : SymName) : List SymName :=
  (properPartSuffixes n.toParts).map ofParts

/-- Detect Lean's `_private` name encoding. -/
def isPrivateName (n : SymName) : Bool :=
  n.toParts.any fun
    | .str s => s == "_private"
    | .num _ => false

/-- Pure `List Char` prefix check (100% kernel-reducible without `String.Slice` internals). -/
def charListStartsWith : List Char → List Char → Bool
  | [], _ => true
  | p :: ps, x :: ys => p == x && charListStartsWith ps ys
  | _ :: _, [] => false

/-- Pure `List Char` substring check (100% kernel-reducible). -/
def charListContainsSub (pat : List Char) : List Char → Bool
  | [] => pat.isEmpty
  | xs@(_ :: tl) => charListStartsWith pat xs || charListContainsSub pat tl

/-- Kernel-reducible string prefix check. -/
def strStartsWith (s pre : String) : Bool :=
  charListStartsWith pre.toList s.toList

/-- Kernel-reducible string substring check. -/
def strContainsSub (s pat : String) : Bool :=
  charListContainsSub pat.toList s.toList

/-- Detect internal / compiler-generated name components (leading `_` or numeric suffix). -/
def hasInternalPart (n : SymName) : Bool :=
  n.toParts.any fun
    | .str s => strStartsWith s "_"
    | .num _ => true

/-- Check whether a character list consists solely of ASCII decimal digits and is non-empty. -/
def isNonEmptyDigitsChars (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all fun c => '0' ≤ c && c ≤ '9'

/-- Check whether a string consists solely of ASCII decimal digits and is non-empty. -/
def isNonEmptyDigits (s : String) : Bool :=
  isNonEmptyDigitsChars s.toList

/-- Detect Lean-reserved lazily realized auxiliary names (`.eq_1`, `.eq_def`, `.splitter`, etc.). -/
def isReservedAuxName (n : SymName) : Bool :=
  match n.lastStringPart? with
  | none => false
  | some s =>
    let cs := s.toList
    s == "eq_def" || s == "congr_simp" || s == "splitter" ||
    s == "induct" || s == "induct_unfolding" || s == "fun_cases" ||
    s == "below" || s == "brecOn" || s == "casesOn" || s == "recOn" ||
    s == "noConfusion" || s == "noConfusionType" || s == "ctorIdx" || s == "elim" ||
    (charListStartsWith ['e', 'q', '_'] cs && isNonEmptyDigitsChars (cs.drop 3)) ||
    (charListStartsWith ['m', 'a', 't', 'c', 'h', '_'] cs && isNonEmptyDigitsChars (cs.drop 6))

/-- Extract `parent` when `n = parent._unsafe_rec`. -/
def unsafeRecParent? : SymName → Option SymName
  | .str parent "_unsafe_rec" => some parent
  | _ => none

/-- Canonical well-known Lean & Anneal symbol names. -/
def sorryAxName : SymName := mkSimple "sorryAx"
def propextName : SymName := mkSimple "propext"
def quotName : SymName := mkSimple "Quot"
def quotMkName : SymName := ofList ["Quot", "mk"]
def quotLiftName : SymName := ofList ["Quot", "lift"]
def quotIndName : SymName := ofList ["Quot", "ind"]
def quotSoundName : SymName := ofList ["Quot", "sound"]
def classicalChoiceName : SymName := ofList ["Classical", "choice"]
def ofReduceBoolName : SymName := ofList ["Lean", "ofReduceBool"]
def ofReduceNatName : SymName := ofList ["Lean", "ofReduceNat"]
def trustCompilerName : SymName := ofList ["Lean", "trustCompiler"]
def falseName : SymName := mkSimple "False"
def trueName : SymName := mkSimple "True"
def trueIntroName : SymName := ofList ["True", "intro"]
def natName : SymName := mkSimple "Nat"
def natZeroName : SymName := ofList ["Nat", "zero"]
def natSuccName : SymName := ofList ["Nat", "succ"]
def natAddName : SymName := ofList ["Nat", "add"]
def stringName : SymName := mkSimple "String"
def eqName : SymName := mkSimple "Eq"
def eqReflName : SymName := ofList ["Eq", "refl"]
def verificationResultName : SymName :=
  ofList ["Trusted", "VerificationResult", "VerificationResult"]

/-- Exact set of Lean's 3 foundational axioms. -/
def isFoundationalAxiom (n : SymName) : Bool :=
  n == propextName || n == quotSoundName || n == classicalChoiceName

/-- Check if a name carries a `._native.` component or native-reduction/compiler-trust axiom (`pillar_1`). -/
def hasNativeComponent (n : SymName) : Bool :=
  n.toParts.any fun
    | .str s => s == "_native" || strStartsWith s "_native" || strContainsSub s "._native."
    | .num _ => false

/-- True for `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, or any `._native.*` axiom. -/
def isNativeReductionAxiom (n : SymName) : Bool :=
  n == ofReduceBoolName || n == ofReduceNatName || n == trustCompilerName ||
  hasNativeComponent n

/-- True iff the module belongs to the Lean standard library (`Init`, `Init.*`, `Std`, `Std.*`). -/
def isStdlibModule (m : SymName) : Bool :=
  match m.getRoot with
  | some "Init" | some "Std" => true
  | _ => false

/-- True iff the module is under `Assumptions.*`. -/
def isAssumptionsModule (m : SymName) : Bool :=
  match m.toParts with
  | .str "Assumptions" :: _ :: _ => true
  | _ => false

/-- True iff the module is a proof module (`Proof.*` or `*.Proofs` / `*.Proofs.*`). -/
def isProofModuleName (m : SymName) : Bool :=
  m.toParts.any fun
    | .str "Proof" | .str "Proofs" => true
    | _ => false

/-- True iff the module is a `Verify.*` or `CrateVerify` module. -/
def isVerifyModuleName (m : SymName) : Bool :=
  match m.getRoot with
  | some "Verify" | some "CrateVerify" => true
  | _ => false

/--
Strict check for whether a module name qualifies as `strictExempt` (`Defs` / `<Topic>.Defs`).
Explicitly rejects spoofed proof-nested paths such as `Topic.Proofs.Defs` (`V15`).
-/
def isStrictExemptModuleName (m : SymName) : Bool :=
  let parts := m.toParts
  let endsWithDefs := match m.lastStringPart? with
    | some "Defs" => true
    | _ => false
  let hasForbiddenSegment := parts.any fun
    | .str s =>
      s == "Proof" || s == "Proofs" || s == "Verify" || s == "CrateVerify" ||
      s == "Spec" || s == "Specs" || s == "Test" || s == "Tests" || s == "Assumptions"
    | .num _ => true
  endsWithDefs && !hasForbiddenSegment

end SymName

/-! ## Section 2: Expression Skeletons (`ExprSkeleton`) & Failures -/

/-- Structural AST for kernel expressions (pure `Init`, zero meta imports). -/
inductive ExprSkeleton where
  | sort (lvl : Nat)
  | const (name : SymName)
  | app (fn arg : ExprSkeleton)
  | lam (dom body : ExprSkeleton)
  | forallE (dom body : ExprSkeleton)
  | bvar (idx : Nat)
  | fvar (id : Nat)
  | mvar (id : Nat)
  | natLit (n : Nat)
  | strLit (s : String)
  | proj (structName : SymName) (idx : Nat) (structExpr : ExprSkeleton)
  deriving DecidableEq, Repr, Inhabited

/-- Granular, structured audit failure diagnostics covering all inventory, kernel, and tamper checks. -/
inductive AuditFailure where
  | missingOleanBase (modName : SymName)
  | missingOleanServer (modName : SymName)
  | missingOleanPrivate (modName : SymName)
  | inventoryLengthMismatch (modName : SymName) (namesLen constsLen : Nat)
  | replayMapDrift (modName : SymName)
  | keyNameMismatch (modName mapKey ciName : SymName)
  | duplicateConstName (modName name : SymName)
  | anonymousConstantName (modName : SymName)
  | originMismatch (modName ciName actualOrigin : SymName)
  | missingStoredValue (modName ciName : SymName)
  | unsafeOrPartialDecl (modName ciName : SymName)
  | invalidMutualAll (modName ciName : SymName) (reason : String)
  | openExpression (ctxName : SymName)
  | forbiddenAxiom (rootName axName axOrigin : SymName)
  | forbiddenNativeReductionAxiom (rootName axName : SymName)
  | statementTheoryLeak (rootName depName depMod : SymName)
  | forbiddenImportAll (modName importedMod : SymName)
  | privateInstanceLeakViaImportAll (modName importedMod instName : SymName)
  | forbiddenSourceOption (modName : SymName) (token : String)
  | forbiddenMacroOrElab (modName : SymName) (extKind : String) (declName : SymName)
  | forbiddenInitOrCodegenHook (modName : SymName) (hookKind : String) (declName : SymName)
  | forbiddenInstanceOrCoe (modName : SymName) (extKind : String) (declName : SymName)
  | forbiddenReducibilityOverride (modName target : SymName)
  | forbiddenShadowingOrExport (modName aliasName shadowed : SymName)
  | spoofedExemptModule (modName : SymName)
  | unknownConstant (name : SymName)
  | kernelTypeError (ciName : SymName) (detail : String)
  | kernelReplayMissingDep (ciName dep : SymName)
  | invalidVerifyRoot (rootName : SymName) (detail : String)
  | extraConstProvenanceMismatch (modName name : SymName)
  deriving DecidableEq, Repr

namespace ExprSkeleton

/-- Check whether `e` contains any free de Bruijn variable `idx ≥ depth`. -/
def hasLooseBVarsAt (depth : Nat) : ExprSkeleton → Bool
  | .sort _ => false
  | .const _ => false
  | .app fn arg => hasLooseBVarsAt depth fn || hasLooseBVarsAt depth arg
  | .lam dom body => hasLooseBVarsAt depth dom || hasLooseBVarsAt (depth + 1) body
  | .forallE dom body => hasLooseBVarsAt depth dom || hasLooseBVarsAt (depth + 1) body
  | .bvar idx => decide (depth ≤ idx)
  | .fvar _ => false
  | .mvar _ => false
  | .natLit _ => false
  | .strLit _ => false
  | .proj _ _ se => hasLooseBVarsAt depth se

/-- Check whether `e` contains any free variable `.fvar`. -/
def hasFVar : ExprSkeleton → Bool
  | .sort _ => false
  | .const _ => false
  | .app fn arg => hasFVar fn || hasFVar arg
  | .lam dom body => hasFVar dom || hasFVar body
  | .forallE dom body => hasFVar dom || hasFVar body
  | .bvar _ => false
  | .fvar _ => true
  | .mvar _ => false
  | .natLit _ => false
  | .strLit _ => false
  | .proj _ _ se => hasFVar se

/-- Check whether `e` contains any metavariable `.mvar`. -/
def hasMVar : ExprSkeleton → Bool
  | .sort _ => false
  | .const _ => false
  | .app fn arg => hasMVar fn || hasMVar arg
  | .lam dom body => hasMVar dom || hasMVar body
  | .forallE dom body => hasMVar dom || hasMVar body
  | .bvar _ => false
  | .fvar _ => false
  | .mvar _ => true
  | .natLit _ => false
  | .strLit _ => false
  | .proj _ _ se => hasMVar se

/-- True iff `e` contains any `.fvar`, `.mvar`, or unbound `.bvar`. -/
def hasOpenVars (e : ExprSkeleton) : Bool :=
  hasFVar e || hasMVar e || hasLooseBVarsAt 0 e

/-- Collect all constant names referenced by `e`, including literal types and projection structures. -/
def usedConstants : ExprSkeleton → List SymName
  | .sort _ => []
  | .const n => [n]
  | .app fn arg => usedConstants fn ++ usedConstants arg
  | .lam dom body => usedConstants dom ++ usedConstants body
  | .forallE dom body => usedConstants dom ++ usedConstants body
  | .bvar _ => []
  | .fvar _ => []
  | .mvar _ => []
  | .natLit _ => [SymName.natName]
  | .strLit _ => [SymName.stringName]
  | .proj structName _ se => structName :: usedConstants se

/-- Mirrors `TrustedBoundary.expressionEdges`: rejects open expressions and includes `Nat`/`String`/struct edges. -/
def expressionEdges (ctxName : SymName) (e : ExprSkeleton) : Except AuditFailure (List SymName) :=
  if hasOpenVars e then
    .error (.openExpression ctxName)
  else
    .ok (usedConstants e)

/-- Shift de Bruijn indices `≥ cutoff` upward by `shift`. -/
def liftBVar (shift cutoff : Nat) : ExprSkeleton → ExprSkeleton
  | .sort l => .sort l
  | .const n => .const n
  | .app fn arg => .app (liftBVar shift cutoff fn) (liftBVar shift cutoff arg)
  | .lam dom body => .lam (liftBVar shift cutoff dom) (liftBVar shift (cutoff + 1) body)
  | .forallE dom body => .forallE (liftBVar shift cutoff dom) (liftBVar shift (cutoff + 1) body)
  | .bvar idx => if cutoff ≤ idx then .bvar (idx + shift) else .bvar idx
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .natLit n => .natLit n
  | .strLit s => .strLit s
  | .proj s i se => .proj s i (liftBVar shift cutoff se)

/-- Substitute `arg` for de Bruijn variable `depth`, decrementing higher indices. -/
def instantiateBVarAt (depth : Nat) (arg : ExprSkeleton) : ExprSkeleton → ExprSkeleton
  | .sort l => .sort l
  | .const n => .const n
  | .app fn a => .app (instantiateBVarAt depth arg fn) (instantiateBVarAt depth arg a)
  | .lam dom body =>
    .lam (instantiateBVarAt depth arg dom) (instantiateBVarAt (depth + 1) arg body)
  | .forallE dom body =>
    .forallE (instantiateBVarAt depth arg dom) (instantiateBVarAt (depth + 1) arg body)
  | .bvar idx =>
    if idx == depth then liftBVar depth 0 arg
    else if depth < idx then .bvar (idx - 1)
    else .bvar idx
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .natLit n => .natLit n
  | .strLit s => .strLit s
  | .proj s i se => .proj s i (instantiateBVarAt depth arg se)

/-- Instantiate bound variable `0` with `arg`. -/
def instantiateBVar (body arg : ExprSkeleton) : ExprSkeleton :=
  instantiateBVarAt 0 arg body

/-- Extract the head function of a nested application. -/
def getAppFn : ExprSkeleton → ExprSkeleton
  | .app fn _ => getAppFn fn
  | e => e

/-- Extract the non-dependent return target of a telescope `A₁ → ... → A_k → R`. -/
def telescopeTarget : ExprSkeleton → ExprSkeleton
  | .forallE _ body => telescopeTarget body
  | e => e

/-- Extract the list of argument domain types from a telescope `A₁ → ... → A_k → R`. -/
def telescopeDomains : ExprSkeleton → List ExprSkeleton
  | .forallE dom body => dom :: telescopeDomains body
  | _ => []

/-- Construct a non-dependent arrow `dom → cod` (shifting `cod` under the binder). -/
def arrow (dom cod : ExprSkeleton) : ExprSkeleton :=
  .forallE dom (liftBVar 1 0 cod)

end ExprSkeleton

/-! ## Section 3: Declarations, Module Inventories, & Package Context -/

/-- Safety classification of a Lean declaration. -/
inductive DeclSafety where
  | safe
  | unsafeDecl
  | partialDecl
  deriving DecidableEq, Repr, Inhabited

/-- A single recursor computation rule. -/
structure RecRule where
  ctor : SymName
  nfields : Nat
  rhs : ExprSkeleton
  deriving DecidableEq, Repr, Inhabited

/-- All 8 Lean `ConstantInfo` declaration kinds. -/
inductive DeclKind where
  | axiomDecl
  | defnDecl
  | thmDecl
  | opaqueDecl
  | quotDecl
  | inductDecl (ctors : List SymName)
  | ctorDecl (inductParent : SymName)
  | recDecl (rules : List RecRule)
  deriving DecidableEq, Repr, Inhabited

/-- Coarse kind tag for comparing mutual sibling compatibility. -/
inductive MutualKindTag where
  | axiomTag | defnTag | thmTag | opaqueTag | quotTag | inductTag | ctorTag | recTag
  deriving DecidableEq, Repr, Inhabited

def DeclKind.tag : DeclKind → MutualKindTag
  | .axiomDecl => .axiomTag
  | .defnDecl => .defnTag
  | .thmDecl => .thmTag
  | .opaqueDecl => .opaqueTag
  | .quotDecl => .quotTag
  | .inductDecl _ => .inductTag
  | .ctorDecl _ => .ctorTag
  | .recDecl _ => .recTag

/-- Whether this `DeclKind` carries an `.all` mutual-group list in Lean's `ConstantInfo`. -/
def DeclKind.carriesMutualAll : DeclKind → Bool
  | .defnDecl | .thmDecl | .opaqueDecl | .inductDecl _ | .recDecl _ => true
  | .axiomDecl | .quotDecl | .ctorDecl _ => false

/-- Complete structural representation of a stored `.olean` `ConstantInfo` record. -/
structure ConstantRecord where
  name : SymName
  kind : DeclKind
  safety : DeclSafety := .safe
  type : ExprSkeleton
  value? : Option ExprSkeleton := none
  hasValue : Bool := false
  all : List SymName := []
  originModule : SymName
  isPrivate : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace ConstantRecord

def isAxiom (ci : ConstantRecord) : Bool :=
  match ci.kind with
  | .axiomDecl => true
  | _ => false

def isTheorem (ci : ConstantRecord) : Bool :=
  match ci.kind with
  | .thmDecl => true
  | _ => false

def isUnsafe (ci : ConstantRecord) : Bool :=
  ci.safety == .unsafeDecl

def isPartial (ci : ConstantRecord) : Bool :=
  ci.safety == .partialDecl

/-- Collect dependency edges across recursor computation rules (total recursive for clean proofs). -/
def recRuleEdges (ctxName : SymName) :
    List RecRule → List SymName → Except AuditFailure (List SymName)
  | [], acc => .ok acc
  | rule :: rest, acc => do
    let rhsEdges ← ExprSkeleton.expressionEdges ctxName rule.rhs
    recRuleEdges ctxName rest (rule.ctor :: (rhsEdges ++ acc))

theorem recRuleEdges_preserves (ctxName : SymName) (rs : List RecRule) :
    ∀ {acc res : List SymName},
      recRuleEdges ctxName rs acc = .ok res →
      ∀ x ∈ acc, x ∈ res := by
  induction rs with
  | nil =>
    intro acc res hr x hx
    simp only [recRuleEdges, Except.ok.injEq] at hr
    subst hr; exact hx
  | cons r0 rtl ih =>
    intro acc res hr x hx
    simp only [recRuleEdges, bind, Except.bind] at hr
    cases hre : ExprSkeleton.expressionEdges ctxName r0.rhs with
    | error _ => rw [hre] at hr; cases hr
    | ok re =>
      rw [hre] at hr
      exact ih hr x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))

/-- Mirrors `TrustedBoundary.declarationEdges` including `.all`, ctor parent, and recursor rules. -/
def declarationEdges (ci : ConstantRecord) : Except AuditFailure (List SymName) := do
  let mut result ← ExprSkeleton.expressionEdges ci.name ci.type
  if let some val := ci.value? then
    let valEdges ← ExprSkeleton.expressionEdges ci.name val
    result := result ++ valEdges
  match ci.kind with
  | .defnDecl | .thmDecl | .opaqueDecl =>
    return result ++ ci.all
  | .inductDecl ctors =>
    return result ++ ci.all ++ ctors
  | .ctorDecl parent =>
    return parent :: result
  | .recDecl rules =>
    recRuleEdges ci.name rules (result ++ ci.all)
  | .axiomDecl | .quotDecl =>
    return result

end ConstantRecord

/-- Role of a module in the Anneal trust architecture. -/
inductive ModuleRole where
  | foundation
  | trusted
  | theory
  | defsExempt
  | proof
  | spec
  | verify
  | assumptions
  | test
  deriving DecidableEq, Repr, Inhabited

/-- Multi-part `.olean` artifact presence on disk (`V17`, `V18`). -/
structure OleanArtifactParts where
  isModuleMode : Bool := false
  hasOlean : Bool := true
  hasServer : Bool := true
  hasPrivate : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- Import edge metadata from a module header (`V14`). -/
structure ImportSpec where
  module : SymName
  importAll : Bool := false
  isExported : Bool := true
  isMeta : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Persistent environment extension entries serialized in `.olean` (`V01`–`V16`). -/
inductive EnvExtEntry where
  | macroEntry (declName targetKind : SymName)
  | commandElabEntry (declName targetKind : SymName)
  | localCommandElabEntry (declName targetKind : SymName) (persistedGlobal : Bool)
  | scopedElabEntry (declName scope : SymName)
  | scopedMacroEntry (declName scope : SymName)
  | scopedInstanceEntry (declName scope targetClass : SymName)
  | termElabEntry (declName targetKind : SymName)
  | delabEntry (declName targetConst : SymName)
  | appUnexpanderEntry (declName targetConst : SymName)
  | instanceEntry (declName targetDecl targetOrigin : SymName) (isPrivateInst : Bool)
  | defaultInstanceEntry (declName targetClass : SymName)
  | coeEntry (declName sourceType targetType : SymName)
  | reducibilityOverride (target targetOrigin : SymName) (newStatus : String)
  | exportAlias (aliasName target targetOrigin : SymName)
  | regularInitHook (declName : SymName)
  | metaInitHook (declName : SymName)
  | implementedByHook (declName implName : SymName)
  | externHook (declName externSym : SymName)
  | cachedExportedAxioms (decl : SymName) (claimedAxioms : List SymName)
  deriving DecidableEq, Repr, Inhabited

/-- Complete `.olean` + header + extension inventory for a single compiled module. -/
structure ModuleInventory where
  moduleName : SymName
  role : ModuleRole
  oleanParts : OleanArtifactParts := {}
  imports : List ImportSpec := []
  constNames : List SymName := []
  constants : List ConstantRecord := []
  extraConstNames : List SymName := []
  replayMap : List (SymName × ConstantRecord) := []
  extEntries : List EnvExtEntry := []
  sourceText? : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- Audit policy configuration. -/
structure AuditConfig where
  allowAssumptions : Bool := false
  allowProvisionalNative : Bool := false
  enforceStrictProofs : Bool := true
  kernelFuel : Nat := 128
  deriving DecidableEq, Repr, Inhabited

/-- Full package input submitted to the replay-key and tamper audit pipeline. -/
structure PackageAuditInput where
  baseEnv : List ConstantRecord
  modules : List ModuleInventory
  verifyRoots : List SymName := []
  claimRoots : List SymName := []
  deriving DecidableEq, Repr, Inhabited

/-! ## Section 4: Comment- and String-Stripping Source Defense-in-Depth Scanner -/

namespace SourceScanner

/-- Single-character state machine for linear-time comment/string/char-literal stripping. -/
inductive ScanState where
  | normal
  | sawDash
  | sawSlash
  | inLine
  | inBlock (depth : Nat)
  | inBlockSawSlash (depth : Nat)
  | inBlockSawDash (depth : Nat)
  | inString (escaped : Bool)
  | sawQuote
  | sawQuoteChar (first : Char)
  | inCharEsc
  | inCharEscDone
  deriving DecidableEq, Repr

/-- Advance the comment/string/char-literal stripper by one character (accumulating reversed output). -/
def stripStepOne (acc : ScanState × List Char) (c : Char) : ScanState × List Char :=
  let (st, rev) := acc
  match st with
  | .normal =>
    if c == '-' then (.sawDash, rev)
    else if c == '/' then (.sawSlash, rev)
    else if c == '"' then (.inString false, ' ' :: rev)
    else if c == '\'' then (.sawQuote, rev)
    else (.normal, c :: rev)
  | .sawDash =>
    if c == '-' then (.inLine, ' ' :: ' ' :: rev)
    else if c == '/' then (.sawSlash, '-' :: rev)
    else if c == '"' then (.inString false, ' ' :: '-' :: rev)
    else if c == '\'' then (.sawQuote, '-' :: rev)
    else (.normal, c :: '-' :: rev)
  | .sawSlash =>
    if c == '-' then (.inBlock 1, ' ' :: ' ' :: rev)
    else if c == '/' then (.sawSlash, '/' :: rev)
    else if c == '"' then (.inString false, ' ' :: '/' :: rev)
    else if c == '\'' then (.sawQuote, '/' :: rev)
    else (.normal, c :: '/' :: rev)
  | .inLine =>
    if c == '\n' then (.normal, '\n' :: rev)
    else (.inLine, ' ' :: rev)
  | .inBlock depth =>
    if c == '/' then (.inBlockSawSlash depth, rev)
    else if c == '-' then (.inBlockSawDash depth, rev)
    else if c == '\n' then (.inBlock depth, '\n' :: rev)
    else (.inBlock depth, ' ' :: rev)
  | .inBlockSawSlash depth =>
    if c == '-' then (.inBlock (depth + 1), ' ' :: ' ' :: rev)
    else if c == '/' then (.inBlockSawSlash depth, ' ' :: rev)
    else if c == '\n' then (.inBlock depth, '\n' :: ' ' :: rev)
    else (.inBlock depth, ' ' :: ' ' :: rev)
  | .inBlockSawDash depth =>
    if c == '/' then
      if depth <= 1 then (.normal, ' ' :: ' ' :: rev)
      else (.inBlock (depth - 1), ' ' :: ' ' :: rev)
    else if c == '-' then (.inBlockSawDash depth, ' ' :: rev)
    else if c == '\n' then (.inBlock depth, '\n' :: ' ' :: rev)
    else (.inBlock depth, ' ' :: ' ' :: rev)
  | .inString true =>
    (.inString false, ' ' :: rev)
  | .inString false =>
    if c == '\\' then (.inString true, ' ' :: rev)
    else if c == '"' then (.normal, ' ' :: rev)
    else if c == '\n' then (.inString false, '\n' :: rev)
    else (.inString false, ' ' :: rev)
  | .sawQuote =>
    if c == '\\' then (.inCharEsc, ' ' :: ' ' :: rev)
    else if c == '\'' then (.normal, '\'' :: '\'' :: rev)
    else if c == '\n' then (.normal, '\n' :: '\'' :: rev)
    else (.sawQuoteChar c, rev)
  | .sawQuoteChar first =>
    if c == '\'' then (.normal, ' ' :: ' ' :: ' ' :: rev)
    else if c == '-' then (.sawDash, first :: '\'' :: rev)
    else if c == '/' then (.sawSlash, first :: '\'' :: rev)
    else if c == '"' then (.inString false, ' ' :: first :: '\'' :: rev)
    else (.normal, c :: first :: '\'' :: rev)
  | .inCharEsc =>
    (.inCharEscDone, ' ' :: rev)
  | .inCharEscDone =>
    if c == '\'' then (.normal, ' ' :: rev)
    else (.normal, c :: rev)

/-- Strip `-- ...` line comments, nested `/- ... -/` block comments, `"..."` strings, and `'...'` chars. -/
def stripChars (cs : List Char) : List Char :=
  let (st, rev) := cs.foldl stripStepOne (.normal, [])
  let rev' := match st with
    | .sawDash => '-' :: rev
    | .sawSlash => '/' :: rev
    | .sawQuote => '\'' :: rev
    | .sawQuoteChar c => c :: '\'' :: rev
    | _ => rev
  rev'.reverse

/-- Replace all comments, string literals, and char literals with spaces (preserving newlines). -/
def stripCommentsAndStrings (src : String) : String :=
  String.ofList (stripChars src.toList)

/-- True iff `c` separates source tokens (keeping `.`, `_`, `+`, digits, and letters inside tokens). -/
def isTokenSep (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' ||
  c == '(' || c == ')' || c == '[' || c == ']' || c == '{' || c == '}' ||
  c == ',' || c == ';' || c == ':'

/-- Single-character tokenizer fold step (zero `List.brecOn`, linear kernel reduction). -/
def tokenizeStep (acc : List Char × List (List Char)) (c : Char) :
    List Char × List (List Char) :=
  let (cur, toks) := acc
  if isTokenSep c then
    if cur.isEmpty then ([], toks)
    else ([], cur.reverse :: toks)
  else
    (c :: cur, toks)

/-- Split stripped character stream into contiguous non-empty character-list tokens. -/
def tokenizeChars (cs : List Char) : List (List Char) :=
  let (cur, toks) := cs.foldl tokenizeStep ([], [])
  let toks' := if cur.isEmpty then toks else cur.reverse :: toks
  toks'.reverse

/-- Split stripped source text into contiguous non-empty tokens. -/
def tokenize (s : String) : List String :=
  (tokenizeChars s.toList).map String.ofList

/-- Scan token pairs for two-token patterns such as `hygiene false` or `quotPrecheck false`. -/
def hasAdjacentPairChars (a b : List Char) : List (List Char) → Bool
  | x :: y :: rest => (x == a && y == b) || hasAdjacentPairChars a b (y :: rest)
  | _ => false

/-- Scan string token pairs for two-token patterns. -/
def hasAdjacentPair (a b : String) (toks : List String) : Bool :=
  hasAdjacentPairChars a.toList b.toList (toks.map String.toList)

/-- Scan stripped character-list tokens for `native_decide`, `bv_decide`, or `decide` with `+native`/`native`. -/
def hasNativeDecideTokensChars : List (List Char) → Bool
  | [] => false
  | tok :: rest =>
    if tok == "native_decide".toList || tok == "bv_decide".toList then true
    else if tok == "decide".toList then
      let window := rest.take 6
      window.any (fun w => w == "+native".toList || w == "native".toList) ||
        hasNativeDecideTokensChars rest
    else
      hasNativeDecideTokensChars rest

/-- Scan stripped source tokens for `native_decide`, `bv_decide`, or `decide` configured with `+native`/`native`. -/
def hasNativeDecideTokens (toks : List String) : Bool :=
  hasNativeDecideTokensChars (toks.map String.toList)

/-- Defense-in-depth source scanner over comment- and string-stripped tokens. -/
def scanSourceDefenseInDepth (cfg : AuditConfig) (modName : SymName) (role : ModuleRole)
    (src : String) : Except AuditFailure Unit := do
  let toks := tokenizeChars (stripChars src.toList)
  if toks.contains "debug.skipKernelTC".toList then
    throw (.forbiddenSourceOption modName "debug.skipKernelTC")
  if toks.contains "allowUnsafeReducibility".toList then
    throw (.forbiddenSourceOption modName "allowUnsafeReducibility")
  if toks.contains "backward.privateInPublic".toList then
    throw (.forbiddenSourceOption modName "backward.privateInPublic")
  if hasAdjacentPairChars "hygiene".toList "false".toList toks then
    throw (.forbiddenSourceOption modName "hygiene false")
  if hasAdjacentPairChars "quotPrecheck".toList "false".toList toks then
    throw (.forbiddenSourceOption modName "quotPrecheck false")
  let allowModProvisional := cfg.allowProvisionalNative && role == .proof
  if !allowModProvisional && hasNativeDecideTokensChars toks then
    throw (.forbiddenSourceOption modName "native_decide/decide +native")

end SourceScanner

/-! ## Section 5: Executable Structural Kernel Typechecker & Semantic Consistency Model -/

/-- Association-list kernel environment mapping declared `SymName` to `ConstantRecord`. -/
abbrev KernelEnv := List (SymName × ConstantRecord)

namespace KernelEnv

/-- Lookup a constant by key in a `KernelEnv`. -/
def lookup (env : KernelEnv) (n : SymName) : Option ConstantRecord :=
  match env with
  | [] => none
  | (k, ci) :: rest => if k == n then some ci else lookup rest n

/-- Membership check for a constant name in `KernelEnv`. -/
def contains (env : KernelEnv) (n : SymName) : Bool :=
  (lookup env n).isSome

/-- Insert a constant at the front of `KernelEnv`. -/
def insert (env : KernelEnv) (k : SymName) (ci : ConstantRecord) : KernelEnv :=
  (k, ci) :: env

/-- Overwrite-by-key helper (faithfully modeling `Std.HashMap.insert` overwrite behavior). -/
def insertOverwrite (env : KernelEnv) (k : SymName) (ci : ConstantRecord) : KernelEnv :=
  match env with
  | [] => [(k, ci)]
  | (k', ci') :: rest =>
    if k' == k then (k, ci) :: rest
    else (k', ci') :: insertOverwrite rest k ci

/-- Build the imported environment directly from `constNames.zip constants` (modeling `finalizeImport`). -/
def finalizeImportedEnv (invs : List ModuleInventory) : KernelEnv :=
  invs.foldl (fun acc inv => acc ++ inv.constNames.zip inv.constants) []

theorem lookup_insert_self (env : KernelEnv) (k : SymName) (ci : ConstantRecord) :
    lookup (insert env k ci) k = some ci := by
  simp [lookup, insert]

theorem lookup_insert_ne (env : KernelEnv) (k k' : SymName) (ci : ConstantRecord)
    (hne : k ≠ k') :
    lookup (insert env k ci) k' = lookup env k' := by
  simp [lookup, insert, hne]

theorem lookup_insertOverwrite_self (env : KernelEnv) (k : SymName) (ci : ConstantRecord) :
    lookup (insertOverwrite env k ci) k = some ci := by
  induction env with
  | nil => simp [insertOverwrite, lookup]
  | cons hd tl ih =>
    rcases hd with ⟨k', ci'⟩
    by_cases h : k' = k
    · subst h; simp [insertOverwrite, lookup]
    · simp [insertOverwrite, lookup, h, ih]

theorem lookup_append_left {e₁ e₂ : KernelEnv} {k : SymName} {ci : ConstantRecord}
    (h : lookup e₁ k = some ci) :
    lookup (e₁ ++ e₂) k = some ci := by
  induction e₁ with
  | nil => simp [lookup] at h
  | cons hd tl ih =>
    rcases hd with ⟨k', ci'⟩
    by_cases hk : k' = k
    · subst hk; simp [lookup] at h ⊢; exact h
    · simp [lookup, hk] at h ⊢; exact ih h

theorem lookup_append_none {e₁ e₂ : KernelEnv} {k : SymName}
    (h : lookup e₁ k = none) :
    lookup (e₁ ++ e₂) k = lookup e₂ k := by
  induction e₁ with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨k', ci'⟩
    by_cases hk : k' = k
    · subst hk; simp [lookup] at h
    · simp [lookup, hk] at h ⊢; exact ih h

theorem lookup_mem {env : KernelEnv} {k : SymName} {ci : ConstantRecord}
    (h : lookup env k = some ci) :
    (k, ci) ∈ env := by
  induction env with
  | nil => simp [lookup] at h
  | cons hd tl ih =>
    rcases hd with ⟨k', ci'⟩
    by_cases hk : k' = k
    · subst hk; simp [lookup] at h; subst h; exact List.mem_cons_self
    · simp [lookup, hk] at h; exact List.mem_cons_of_mem _ (ih h)

theorem lookup_of_mem_nodup {env : KernelEnv} {k : SymName} {ci : ConstantRecord}
    (hnodup : (env.map Prod.fst).Nodup)
    (hmem : (k, ci) ∈ env) :
    lookup env k = some ci := by
  induction env with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨k', ci'⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases hnodup with ⟨hnotmem, htl⟩
    cases hmem with
    | head => simp [lookup]
    | tail _ hmem' =>
      have hne : k' ≠ k := by
        intro heq
        subst heq
        exact hnotmem (List.mem_map.mpr ⟨(k', ci), hmem', rfl⟩)
      simp [lookup, hne]
      exact ih htl hmem'

end KernelEnv

/-- Lean's impredicative universe `imax` rule (`imax u 0 = 0`, `imax u (v+1) = max u (v+1)`). -/
def imaxLevel (u v : Nat) : Nat :=
  if v == 0 then 0 else max u v

/-- Maximum universe level supported by the semantic consistency model (`0 = Prop`, `1 = Type 0`). -/
def maxModelUniverse : Nat := 1

/-- Check whether `e` is a valid non-dependent structure constructor type whose fields are closed. -/
def structFieldTypes? (structName : SymName) (ty : ExprSkeleton) : Option (List ExprSkeleton) :=
  match ty with
  | .const n => if n == structName then some [] else none
  | .forallE dom body =>
    if ExprSkeleton.hasOpenVars dom then none
    else if ExprSkeleton.hasLooseBVarsAt 0 body then none
    else
      match structFieldTypes? structName body with
      | some rest => some (dom :: rest)
      | none => none
  | _ => none

/-- Extract the `idx`-th field type of a single-constructor structure `structName` in `env`. -/
def lookupStructFieldType? (env : KernelEnv) (structName : SymName) (idx : Nat) :
    Option ExprSkeleton :=
  match env.lookup structName with
  | some indCi =>
    match indCi.kind with
    | .inductDecl [ctorName] =>
      match env.lookup ctorName with
      | some ctorCi =>
        if ctorCi.kind == .ctorDecl structName then
          match structFieldTypes? structName ctorCi.type with
          | some fields => fields[idx]?
          | none => none
        else none
      | none => none
    | _ => none
  | none => none

/-!
Mutually recursive fuel-indexed structural kernel typechecker:
- `whnf`: δ-unfolding of transparent `defnDecl`s and sound β-reduction (checking argument typing
  at strictly smaller fuel so semantic soundness follows by direct induction on `fuel`).
- `isDefEq`: weak-head normalization followed by structural congruence under binders.
- `inferType`: dependent type inference covering `sort`, `bvar`, `const`, `natLit`, `strLit`,
  `forallE` (with `imax`), `lam`, `app`, and `proj`.
-/
mutual

def whnf (env : KernelEnv) : Nat → List ExprSkeleton → ExprSkeleton → ExprSkeleton
  | 0, _, e => e
  | fuel + 1, ctx, e =>
    match e with
    | .const n =>
      match env.lookup n with
      | some ci =>
        match ci.kind, ci.value? with
        | .defnDecl, some v => whnf env fuel ctx v
        | _, _ => e
      | none => e
    | .app fn arg =>
      let fn' := whnf env fuel ctx fn
      match fn' with
      | .lam dom body =>
        match inferType env fuel ctx dom, inferType env fuel ctx arg with
        | .ok (.sort u), .ok argTy =>
          if u ≤ maxModelUniverse && isDefEq env fuel ctx argTy dom then
            whnf env fuel ctx (ExprSkeleton.instantiateBVar body arg)
          else
            .app fn' arg
        | _, _ => .app fn' arg
      | _ => .app fn' arg
    | _ => e

def isDefEq (env : KernelEnv) : Nat → List ExprSkeleton → ExprSkeleton → ExprSkeleton → Bool
  | 0, _, e₁, e₂ => e₁ == e₂
  | fuel + 1, ctx, e₁, e₂ =>
    let w₁ := whnf env fuel ctx e₁
    let w₂ := whnf env fuel ctx e₂
    if w₁ == w₂ then true
    else
      match w₁, w₂ with
      | .app f₁ a₁, .app f₂ a₂ =>
        isDefEq env fuel ctx f₁ f₂ && isDefEq env fuel ctx a₁ a₂
      | .forallE d₁ b₁, .forallE d₂ b₂ =>
        isDefEq env fuel ctx d₁ d₂ && isDefEq env fuel (d₁ :: ctx) b₁ b₂
      | .lam d₁ b₁, .lam d₂ b₂ =>
        isDefEq env fuel ctx d₁ d₂ && isDefEq env fuel (d₁ :: ctx) b₁ b₂
      | .proj s₁ i₁ x₁, .proj s₂ i₂ x₂ =>
        s₁ == s₂ && i₁ == i₂ && isDefEq env fuel ctx x₁ x₂
      | _, _ => false

def inferType (env : KernelEnv) :
    Nat → List ExprSkeleton → ExprSkeleton → Except AuditFailure ExprSkeleton
  | 0, _, _ => .error (.kernelTypeError .anonymous "kernel fuel exhausted")
  | fuel + 1, ctx, e =>
    match e with
    | .sort l =>
      if l ≤ maxModelUniverse then .ok (.sort (l + 1))
      else .error (.kernelTypeError .anonymous "universe level exceeds model bound")
    | .bvar idx =>
      match ctx[idx]? with
      | some ty => .ok (ExprSkeleton.liftBVar (idx + 1) 0 ty)
      | none => .error (.openExpression .anonymous)
    | .fvar _ | .mvar _ => .error (.openExpression .anonymous)
    | .const n =>
      match env.lookup n with
      | some ci => .ok ci.type
      | none => .error (.unknownConstant n)
    | .natLit _ =>
      if env.contains SymName.natName then .ok (.const SymName.natName)
      else .error (.unknownConstant SymName.natName)
    | .strLit _ =>
      if env.contains SymName.stringName then .ok (.const SymName.stringName)
      else .error (.unknownConstant SymName.stringName)
    | .forallE dom body => do
      let domSort ← inferType env fuel ctx dom
      match whnf env fuel ctx domSort with
      | .sort u =>
        if !(u ≤ maxModelUniverse) then
          throw (.kernelTypeError .anonymous "domain universe exceeds model bound")
        let bodySort ← inferType env fuel (dom :: ctx) body
        match whnf env fuel (dom :: ctx) bodySort with
        | .sort v =>
          if !(v ≤ maxModelUniverse) then
            throw (.kernelTypeError .anonymous "codomain universe exceeds model bound")
          return .sort (imaxLevel u v)
        | _ => throw (.kernelTypeError .anonymous "forallE codomain is not a sort")
      | _ => throw (.kernelTypeError .anonymous "forallE domain is not a sort")
    | .lam dom body => do
      let domSort ← inferType env fuel ctx dom
      match whnf env fuel ctx domSort with
      | .sort u =>
        if !(u ≤ maxModelUniverse) then
          throw (.kernelTypeError .anonymous "lambda domain universe exceeds model bound")
        let bodyTy ← inferType env fuel (dom :: ctx) body
        let bodyTySort ← inferType env fuel (dom :: ctx) bodyTy
        match whnf env fuel (dom :: ctx) bodyTySort with
        | .sort v =>
          if !(v ≤ maxModelUniverse) then
            throw (.kernelTypeError .anonymous "lambda codomain universe exceeds model bound")
          return .forallE dom bodyTy
        | _ => throw (.kernelTypeError .anonymous "lambda codomain type is not a sort")
      | _ => throw (.kernelTypeError .anonymous "lambda domain is not a sort")
    | .app fn arg => do
      let fnTy ← inferType env fuel ctx fn
      match whnf env fuel ctx fnTy with
      | .forallE dom bodyTy =>
        let domSort ← inferType env fuel ctx dom
        match whnf env fuel ctx domSort with
        | .sort u =>
          if !(u ≤ maxModelUniverse) then
            throw (.kernelTypeError .anonymous "application domain universe exceeds model bound")
          let argTy ← inferType env fuel ctx arg
          if isDefEq env fuel ctx argTy dom then
            return ExprSkeleton.instantiateBVar bodyTy arg
          else
            throw (.kernelTypeError .anonymous "application argument type mismatch")
        | _ => throw (.kernelTypeError .anonymous "application domain is not a sort")
      | _ => throw (.kernelTypeError .anonymous "application head does not have function type")
    | .proj structName idx structExpr => do
      let sTy ← inferType env fuel ctx structExpr
      if !isDefEq env fuel ctx sTy (.const structName) then
        throw (.kernelTypeError structName "projection target type mismatch")
      match lookupStructFieldType? env structName idx with
      | some fTy => return fTy
      | none => throw (.kernelTypeError structName "invalid projection field index")

end

/-- Canonical quotient types checked by `kernelCheckDecl` (preventing `lean4#16677` `.quotInfo` bypass). -/
def isCanonicalQuotDecl (env : KernelEnv) (ci : ConstantRecord) : Bool :=
  let natRelTy := ExprSkeleton.arrow (.const SymName.natName)
    (ExprSkeleton.arrow (.const SymName.natName) (.sort 0))
  if ci.name == SymName.quotName then
    env.contains SymName.natName && ci.type == ExprSkeleton.arrow natRelTy (.sort 0)
  else if ci.name == SymName.quotMkName then
    env.contains SymName.quotName && env.contains SymName.natName &&
    ci.type == ExprSkeleton.arrow (.const SymName.natName) (.const SymName.trueName)
  else if ci.name == SymName.quotLiftName || ci.name == SymName.quotIndName then
    env.contains SymName.quotName && env.contains SymName.eqName &&
    ci.type == ExprSkeleton.arrow (.const SymName.trueName) (.const SymName.trueName)
  else
    false

/-- Check whether a list has duplicate elements. -/
def hasDuplicates [DecidableEq α] : List α → Bool
  | [] => false
  | x :: xs => xs.contains x || hasDuplicates xs

theorem hasDuplicates_eq_false_iff_nodup [DecidableEq α] (xs : List α) :
    hasDuplicates xs = false ↔ xs.Nodup := by
  induction xs with
  | nil => simp [hasDuplicates]
  | cons x tl ih =>
    simp [hasDuplicates, Bool.or_eq_false_iff, ih, List.nodup_cons]

theorem nodup_getElem_inj {xs : List α} (hnd : xs.Nodup) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (heq : xs[i] = xs[j]) : i = j := by
  induction xs generalizing i j with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons x tl ih =>
    rw [List.nodup_cons] at hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact absurd (heq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj)) hnd.1
    | succ i' =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact absurd (heq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi)) hnd.1
      | succ j' =>
        simp only [List.getElem_cons_succ] at heq
        exact congrArg Nat.succ (ih hnd.2 (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) heq)

/-- Canonical elimination type for a simple 0-argument inductive `indName` with constructors `ctors` into `Prop`. -/
def canonicalPropRecType (indName : SymName) (ctors : List SymName) : ExprSkeleton :=
  -- `∀ (motive : indName → Prop), (motive c_0) → ... → (motive c_{k-1}) → ∀ (x : indName), motive x`
  let rec buildMinors (depth : Nat) : List SymName → ExprSkeleton
    | [] =>
      .forallE (.const indName) (.app (.bvar depth) (.bvar 0))
    | c :: rest =>
      .forallE (.app (.bvar (depth - 1)) (.const c)) (buildMinors (depth + 1) rest)
  .forallE (ExprSkeleton.arrow (.const indName) (.sort 0)) (buildMinors 1 ctors)

/-- Canonical `False`-like empty inductive recursor type: `∀ (C : Prop), indName → C`. -/
def canonicalEmptyPropRecType (indName : SymName) : ExprSkeleton :=
  .forallE (.sort 0) (ExprSkeleton.arrow (.const indName) (.bvar 0))

/-- Check whether `ci.name` is one of the built-in primitive types with special carriers. -/
def isBuiltinCarrierName (n : SymName) : Bool :=
  n == SymName.natName || n == SymName.stringName

/--
Check whether a recursor declaration `ci` matches a canonical generated eliminator for an
inductive already present in `env` (preventing forged `T.rec : False` under any key or name).
-/
def isCanonicalRecDecl (env : KernelEnv) (ci : ConstantRecord) (rules : List RecRule) : Bool :=
  match ci.all with
  | [indName] =>
    match env.lookup indName with
    | some indCi =>
      match indCi.kind with
      | .inductDecl ctors =>
        let expectedRecName := SymName.str indName "rec"
        let ctorsPresent := ctors.all fun c =>
          match env.lookup c with
          | some cCi => cCi.kind == .ctorDecl indName && cCi.type == .const indName
          | none => false
        let rulesOk := rules.all fun r => ctors.contains r.ctor && !ExprSkeleton.hasOpenVars r.rhs
        let typeOk :=
          (ctorsPresent && (indCi.type == .sort 0 || indCi.type == .sort 1) &&
            ci.type == canonicalPropRecType indName ctors) ||
          (ctors.isEmpty && (indCi.type == .sort 0 || indCi.type == .sort 1) &&
            ci.type == canonicalEmptyPropRecType indName)
        ci.name == expectedRecName && !isBuiltinCarrierName indName && rulesOk && typeOk
      | _ => false
    | none => false
  | _ => false

/-- Check whether an inductive arity is a `Prop`-returning telescope `A₁ → ... → A_k → Prop`. -/
def isValidPropInductArity (env : KernelEnv) (fuel : Nat) (ty : ExprSkeleton) : Bool :=
  match ty with
  | .sort 0 => true
  | .forallE dom body =>
    match inferType env fuel [] dom with
    | .ok (.sort u) =>
      u ≤ maxModelUniverse && !ExprSkeleton.hasLooseBVarsAt 0 body &&
      isValidPropInductArity env fuel body
    | _ => false
  | _ => false

/-- Check whether an inductive type is `Type 0` (`sort 1`) or a valid `Prop`-returning arity. -/
def isValidInductArity (env : KernelEnv) (fuel : Nat) (ty : ExprSkeleton) : Bool :=
  ty == .sort 1 || isValidPropInductArity env fuel ty

/-- Check whether a constructor type targets `inductParent` with closed domain types. -/
def isValidCtorType (env : KernelEnv) (fuel : Nat) (inductParent : SymName) (ty : ExprSkeleton) : Bool :=
  match ty with
  | .const n => n == inductParent
  | .forallE dom body =>
    match inferType env fuel [] dom with
    | .ok (.sort u) =>
      u ≤ maxModelUniverse && !ExprSkeleton.hasLooseBVarsAt 0 body &&
      isValidCtorType env fuel inductParent body
    | _ => false
  | _ => false

/--
Clean-environment kernel declaration checker (`kernelCheckDecl`).
Verifies closedness, safety, name freshness, well-typedness of `ci.type` and `ci.value?`,
and structural formation of inductives, constructors, recursors, and quotients.
-/
def kernelCheckDecl (env : KernelEnv) (fuel : Nat) (allowAxiom : Bool)
    (ci : ConstantRecord) : Except AuditFailure KernelEnv := do
  if ci.name.isAnonymous then
    throw (.anonymousConstantName ci.originModule)
  if env.contains ci.name then
    throw (.duplicateConstName ci.originModule ci.name)
  if ci.isUnsafe || ci.isPartial then
    throw (.unsafeOrPartialDecl ci.originModule ci.name)
  if ExprSkeleton.hasOpenVars ci.type then
    throw (.openExpression ci.name)
  let tySort ← inferType env fuel [] ci.type
  let tySortW := whnf env fuel [] tySort
  match tySortW with
  | .sort u =>
    if !(u ≤ maxModelUniverse + 1) then
      throw (.kernelTypeError ci.name "declaration type universe exceeds model bound")
  | _ =>
    throw (.kernelTypeError ci.name "declaration type is not a valid sort")
  match ci.kind with
  | .axiomDecl =>
    if !allowAxiom then
      throw (.forbiddenAxiom ci.name ci.name ci.originModule)
    if ci.value?.isSome || ci.hasValue then
      throw (.kernelTypeError ci.name "axiom cannot carry a value")
    return env.insert ci.name ci
  | .defnDecl =>
    match ci.value? with
    | none => throw (.missingStoredValue ci.originModule ci.name)
    | some val =>
      if ExprSkeleton.hasOpenVars val then
        throw (.openExpression ci.name)
      let valTy ← inferType env fuel [] val
      if !isDefEq env fuel [] valTy ci.type then
        throw (.kernelTypeError ci.name "definition body type mismatch")
      return env.insert ci.name ci
  | .thmDecl =>
    if tySortW != .sort 0 then
      throw (.kernelTypeError ci.name "theorem type must inhabit Prop (sort 0)")
    match ci.value? with
    | none => throw (.missingStoredValue ci.originModule ci.name)
    | some val =>
      if ExprSkeleton.hasOpenVars val then
        throw (.openExpression ci.name)
      let valTy ← inferType env fuel [] val
      if !isDefEq env fuel [] valTy ci.type then
        throw (.kernelTypeError ci.name "theorem proof term type mismatch")
      return env.insert ci.name ci
  | .opaqueDecl =>
    match ci.value? with
    | none => throw (.missingStoredValue ci.originModule ci.name)
    | some val =>
      if ExprSkeleton.hasOpenVars val then
        throw (.openExpression ci.name)
      let valTy ← inferType env fuel [] val
      if !isDefEq env fuel [] valTy ci.type then
        throw (.kernelTypeError ci.name "opaque body type mismatch")
      return env.insert ci.name ci
  | .quotDecl =>
    if !isCanonicalQuotDecl env ci then
      throw (.kernelTypeError ci.name "non-canonical quotient declaration")
    return env.insert ci.name ci
  | .inductDecl ctors =>
    if !ci.all.contains ci.name then
      throw (.invalidMutualAll ci.originModule ci.name "inductive name missing from .all")
    if !isValidInductArity env fuel ci.type then
      throw (.kernelTypeError ci.name "invalid inductive arity")
    if ctors.any SymName.isAnonymous then
      throw (.anonymousConstantName ci.originModule)
    if hasDuplicates ctors || ctors.contains ci.name || ctors.any env.contains then
      throw (.duplicateConstName ci.originModule ci.name)
    return env.insert ci.name ci
  | .ctorDecl inductParent =>
    match env.lookup inductParent with
    | none => throw (.kernelReplayMissingDep ci.name inductParent)
    | some indCi =>
      match indCi.kind with
      | .inductDecl ctors =>
        if !ctors.contains ci.name then
          throw (.kernelTypeError ci.name "constructor not listed in parent inductive")
        if !(indCi.type == .sort 0 || indCi.type == .sort 1) then
          throw (.kernelTypeError ci.name "constructor parent must be an unindexed inductive")
        if ctors.length == 1 && ci.type != .const inductParent then
          throw (.kernelTypeError ci.name "dynamic single-ctor inductive cannot alter struct projection fields")
        if !isValidCtorType env fuel inductParent ci.type then
          throw (.kernelTypeError ci.name "constructor type does not target parent inductive")
        return env.insert ci.name ci
      | _ => throw (.kernelTypeError ci.name "constructor parent is not an inductive")
  | .recDecl rules =>
    if !isCanonicalRecDecl env ci rules then
      throw (.kernelTypeError ci.name "recursor does not match canonical inductive eliminator")
    return env.insert ci.name ci

/-! ### Genuine Semantic Consistency Model (`SemVal`) -/

/--
Strictly-positive `Type 1` semantic domain for `ExprSkeleton` (Proof-Irrelevant Model of CoC
with `Prop : Type 0 : Type 1`, dependent `Π`-types, `Nat`, `String`, and inductive carriers).
-/
inductive SemVal : Type 1 where
  | err
  | sort2
  | sort1
  | propSort
  | prop (P : Prop)
  | prf
  | ty (α : Type 0) (dec : α → SemVal)
  | funVal (α : Type 0) (dec : α → SemVal) (f : α → SemVal)
  | base (tag : SymName) (idx : Nat)
  | strVal (s : String)

/-- Underlying Lean `Type 0` carrier of a semantic type. -/
def SemVal.carrier : SemVal → Type 0
  | .prop P => PLift P
  | .propSort => Prop
  | .ty α _ => α
  | _ => PEmpty

/-- Canonical decoder from `v.carrier` back into `SemVal`. -/
def SemVal.decode : (v : SemVal) → v.carrier → SemVal
  | .prop _, _ => .prf
  | .propSort, P => .prop P
  | .ty _ dec, a => dec a
  | .err, x => x.elim
  | .sort2, x => x.elim
  | .sort1, x => x.elim
  | .prf, x => x.elim
  | .funVal _ _ _, x => x.elim
  | .base _ _, x => x.elim
  | .strVal _, x => x.elim

/-- Semantic inhabitability relation `v ∈ ⟦T⟧`. Note `Inhabits v (.prop False) ↔ False`! -/
def Inhabits (v : SemVal) (T : SemVal) : Prop :=
  match T with
  | .prop P => v = .prf ∧ P
  | .propSort => ∃ P : Prop, v = .prop P
  | .ty α dec => ∃ a : α, dec a = v
  | .sort1 =>
    v = .propSort ∨
    (∃ P : Prop, v = .prop P) ∨
    (∃ (α : Type 0) (dec : α → SemVal), Function.Injective dec ∧ v = .ty α dec)
  | .sort2 => v = .sort1
  | _ => False

theorem inhabits_prop_false_iff (v : SemVal) : Inhabits v (.prop False) ↔ False := by
  simp [Inhabits]

theorem not_inhabits_prop_false (v : SemVal) : ¬ Inhabits v (.prop False) :=
  fun h => h.2

/-- Extract the underlying proposition when `v = .prop P`, defaulting to `False`. -/
def semAsProp : SemVal → Prop
  | .prop P => P
  | _ => False

/-- True iff `T` is a valid semantic type (`Prop`, a proposition, or a `ty` with injective decoder). -/
def IsSemType (T : SemVal) : Prop :=
  match T with
  | .prop _ => True
  | .propSort => True
  | .ty _ dec => Function.Injective dec
  | _ => False

theorem isSemType_decode_injective {T : SemVal} (hT : IsSemType T) :
    Function.Injective T.decode := by
  cases T with
  | prop P =>
    intro a b _
    cases a; cases b; rfl
  | propSort =>
    intro P Q h
    cases h; rfl
  | ty α dec =>
    exact hT
  | err | sort2 | sort1 | prf | funVal _ _ _ | base _ _ | strVal _ =>
    exact False.elim hT

theorem inhabits_iff_exists_decode {v T : SemVal} (hT : IsSemType T) :
    Inhabits v T ↔ ∃ a : T.carrier, T.decode a = v := by
  cases T with
  | prop P =>
    constructor
    · intro ⟨hv, hP⟩
      exact ⟨⟨hP⟩, hv.symm⟩
    · intro ⟨⟨hP⟩, hv⟩
      exact ⟨hv.symm, hP⟩
  | propSort =>
    constructor
    · intro ⟨P, hv⟩
      exact ⟨P, hv.symm⟩
    · intro ⟨P, hv⟩
      exact ⟨P, hv.symm⟩
  | ty α dec =>
    exact Iff.rfl
  | err | sort2 | sort1 | prf | funVal _ _ _ | base _ _ | strVal _ =>
    exact False.elim hT

theorem inhabits_sort_implies_isSemType {T : SemVal} {u : Nat}
    (h : Inhabits T (if u == 0 then .propSort else .sort1)) :
    IsSemType T := by
  by_cases hu : u = 0
  · subst hu
    simp only [BEq.rfl, ↓reduceIte, Inhabits] at h
    rcases h with ⟨P, rfl⟩
    trivial
  · have hne : (u == 0) = false := beq_false_of_ne hu
    simp only [hne, Bool.false_eq_true, ↓reduceIte, Inhabits] at h
    rcases h with rfl | ⟨P, rfl⟩ | ⟨α, dec, hinj, rfl⟩
    · trivial
    · trivial
    · exact hinj

/-- Semantic lambda abstraction (collapsing proof-valued and empty-domain functions to `.prf`). -/
noncomputable def semLam (domV : SemVal) (bodyFn : domV.carrier → SemVal) : SemVal :=
  letI := Classical.propDecidable
  if ∀ a : domV.carrier, bodyFn a = .prf then
    .prf
  else
    .funVal domV.carrier domV.decode bodyFn

/-- Semantic dependent product (`Π`) supporting impredicative `Prop` (`imax u 0 = 0`) and `Type 0`. -/
noncomputable def semPi (domV : SemVal) (bodyFn : domV.carrier → SemVal) : SemVal :=
  letI := Classical.propDecidable
  if ∀ a : domV.carrier, ∃ P : Prop, bodyFn a = .prop P then
    .prop (∀ a : domV.carrier, semAsProp (bodyFn a))
  else
    .ty ((a : domV.carrier) → (bodyFn a).carrier)
      (fun f => semLam domV (fun a => (bodyFn a).decode (f a)))

/-- Semantic application via classical inversion of the injective domain decoder. -/
noncomputable def semApp (fnV argV : SemVal) : SemVal :=
  letI := Classical.propDecidable
  match fnV with
  | .prf => .prf
  | .funVal α dec f =>
    if h : ∃ a : α, dec a = argV then
      f (Classical.choose h)
    else
      .err
  | _ => .err

theorem semApp_semLam {domV : SemVal} (hDom : IsSemType domV)
    (bodyFn : domV.carrier → SemVal) (a : domV.carrier) :
    semApp (semLam domV bodyFn) (domV.decode a) = bodyFn a := by
  unfold semLam
  split
  · rename_i hall
    simp only [semApp, hall a]
  · unfold semApp
    have hex : ∃ x : domV.carrier, domV.decode x = domV.decode a := ⟨a, rfl⟩
    simp only [hex, ↓reduceDIte]
    have hch := Classical.choose_spec hex
    have heq := isSemType_decode_injective hDom hch
    rw [heq]

/-- Semantic valuation of closed/open `ExprSkeleton` expressions under environment model `M` and context `γ`. -/
noncomputable def evalExpr (M : SymName → SemVal) (γ : List SemVal) : ExprSkeleton → SemVal
  | .sort 0 => .propSort
  | .sort 1 => .sort1
  | .sort _ => .sort2
  | .const n => M n
  | .bvar idx => γ[idx]?.getD .err
  | .fvar _ | .mvar _ => .err
  | .natLit n => .base SymName.natName n
  | .strLit s => .strVal s
  | .app fn arg => semApp (evalExpr M γ fn) (evalExpr M γ arg)
  | .lam dom body =>
    let domV := evalExpr M γ dom
    semLam domV (fun a => evalExpr M (domV.decode a :: γ) body)
  | .forallE dom body =>
    let domV := evalExpr M γ dom
    semPi domV (fun a => evalExpr M (domV.decode a :: γ) body)
  | .proj _ idx se =>
    semApp (evalExpr M γ se) (.base (SymName.mkSimple "Fin") idx)

/-- Helper lemma: shifting de Bruijn indices preserves `evalExpr` when matching elements are inserted into `γ`. -/
theorem evalExpr_liftBVar (M : SymName → SemVal) (e : ExprSkeleton) :
    ∀ (pre mid suf : List SemVal),
      evalExpr M (pre ++ mid ++ suf) (ExprSkeleton.liftBVar mid.length pre.length e) =
      evalExpr M (pre ++ suf) e := by
  induction e with
  | sort l => intro _ _ _; cases l with | zero => rfl | succ m => cases m <;> rfl
  | const n => intro _ _ _; rfl
  | fvar _ | mvar _ | natLit _ | strLit _ => intro _ _ _; rfl
  | bvar idx =>
    intro pre mid suf
    simp only [ExprSkeleton.liftBVar]
    by_cases h : pre.length ≤ idx
    · simp only [h, ↓reduceIte, evalExpr]
      have h1 : (pre ++ mid ++ suf)[idx + mid.length]? = suf[idx - pre.length]? := by
        rw [List.append_assoc, List.getElem?_append_right (by omega)]
        rw [List.getElem?_append_right (by omega)]
        congr 1; omega
      have h2 : (pre ++ suf)[idx]? = suf[idx - pre.length]? := by
        rw [List.getElem?_append_right h]
      rw [h1, h2]
    · simp only [h, ↓reduceIte, evalExpr]
      have hlt : idx < pre.length := Nat.lt_of_not_le h
      rw [List.append_assoc, List.getElem?_append_left hlt, List.getElem?_append_left hlt]
  | app fn arg ihf iha =>
    intro pre mid suf
    simp only [ExprSkeleton.liftBVar, evalExpr, ihf pre mid suf, iha pre mid suf]
  | lam dom body ihd ihb =>
    intro pre mid suf
    simp only [ExprSkeleton.liftBVar, evalExpr]
    have hd : evalExpr M (pre ++ mid ++ suf) (ExprSkeleton.liftBVar mid.length pre.length dom) =
        evalExpr M (pre ++ suf) dom := ihd pre mid suf
    generalize h1 : evalExpr M (pre ++ mid ++ suf) (ExprSkeleton.liftBVar mid.length pre.length dom) = d1 at hd ⊢
    generalize h2 : evalExpr M (pre ++ suf) dom = d2 at hd ⊢
    subst hd
    congr 1
    funext a
    exact ihb (d1.decode a :: pre) mid suf
  | forallE dom body ihd ihb =>
    intro pre mid suf
    simp only [ExprSkeleton.liftBVar, evalExpr]
    have hd : evalExpr M (pre ++ mid ++ suf) (ExprSkeleton.liftBVar mid.length pre.length dom) =
        evalExpr M (pre ++ suf) dom := ihd pre mid suf
    generalize h1 : evalExpr M (pre ++ mid ++ suf) (ExprSkeleton.liftBVar mid.length pre.length dom) = d1 at hd ⊢
    generalize h2 : evalExpr M (pre ++ suf) dom = d2 at hd ⊢
    subst hd
    congr 1
    funext a
    exact ihb (d1.decode a :: pre) mid suf
  | proj s i se ih =>
    intro pre mid suf
    simp only [ExprSkeleton.liftBVar, evalExpr, ih pre mid suf]

/-- Helper lemma: substituting a de Bruijn variable commutes with `evalExpr`. -/
theorem evalExpr_instantiateBVarAt (M : SymName → SemVal) (arg : ExprSkeleton) (e : ExprSkeleton) :
    ∀ (pre suf : List SemVal),
      evalExpr M (pre ++ suf) (ExprSkeleton.instantiateBVarAt pre.length arg e) =
      evalExpr M (pre ++ [evalExpr M suf arg] ++ suf) e := by
  induction e with
  | sort l => intro _ _; cases l with | zero => rfl | succ m => cases m <;> rfl
  | const n => intro _ _; rfl
  | fvar _ | mvar _ | natLit _ | strLit _ => intro _ _; rfl
  | bvar idx =>
    intro pre suf
    simp only [ExprSkeleton.instantiateBVarAt]
    by_cases heq : idx = pre.length
    · subst heq
      simp only [BEq.rfl, ↓reduceIte]
      have hlift := evalExpr_liftBVar M arg [] pre suf
      simp only [List.nil_append, List.length_nil] at hlift
      rw [hlift]
      simp only [evalExpr, List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self, List.cons_append, List.getElem?_cons_zero, Option.getD_some]
    · have hbeq : (idx == pre.length) = false := beq_false_of_ne heq
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      by_cases hgt : pre.length < idx
      · simp only [hgt, ↓reduceIte, evalExpr]
        have h1 : (pre ++ suf)[idx - 1]? = suf[idx - 1 - pre.length]? :=
          List.getElem?_append_right (by omega)
        have h2 : (pre ++ [evalExpr M suf arg] ++ suf)[idx]? = suf[idx - 1 - pre.length]? := by
          rw [List.append_assoc, List.getElem?_append_right (by omega)]
          have hsub : idx - pre.length = (idx - 1 - pre.length) + 1 := by omega
          rw [hsub, List.cons_append, List.nil_append, List.getElem?_cons_succ]
        rw [h1, h2]
      · simp only [hgt, ↓reduceIte, evalExpr]
        have hlt : idx < pre.length := by omega
        rw [List.getElem?_append_left hlt, List.append_assoc, List.getElem?_append_left hlt]
  | app fn a ihf iha =>
    intro pre suf
    simp only [ExprSkeleton.instantiateBVarAt, evalExpr, ihf pre suf, iha pre suf]
  | lam dom body ihd ihb =>
    intro pre suf
    simp only [ExprSkeleton.instantiateBVarAt, evalExpr]
    have hd := ihd pre suf
    generalize h1 : evalExpr M (pre ++ suf) (ExprSkeleton.instantiateBVarAt pre.length arg dom) = d1 at hd ⊢
    generalize h2 : evalExpr M (pre ++ [evalExpr M suf arg] ++ suf) dom = d2 at hd ⊢
    subst hd
    congr 1
    funext a
    exact ihb (d1.decode a :: pre) suf
  | forallE dom body ihd ihb =>
    intro pre suf
    simp only [ExprSkeleton.instantiateBVarAt, evalExpr]
    have hd := ihd pre suf
    generalize h1 : evalExpr M (pre ++ suf) (ExprSkeleton.instantiateBVarAt pre.length arg dom) = d1 at hd ⊢
    generalize h2 : evalExpr M (pre ++ [evalExpr M suf arg] ++ suf) dom = d2 at hd ⊢
    subst hd
    congr 1
    funext a
    exact ihb (d1.decode a :: pre) suf
  | proj s i se ih =>
    intro pre suf
    simp only [ExprSkeleton.instantiateBVarAt, evalExpr, ih pre suf]

theorem evalExpr_instantiateBVar (M : SymName → SemVal) (body arg : ExprSkeleton) (γ : List SemVal) :
    evalExpr M γ (ExprSkeleton.instantiateBVar body arg) =
    evalExpr M (evalExpr M γ arg :: γ) body := by
  exact evalExpr_instantiateBVarAt M arg body [] γ

/-- Closed expressions evaluate identically in any context `γ`. -/
theorem evalExpr_closed (M : SymName → SemVal) (e : ExprSkeleton) :
    ∀ (pre suf : List SemVal),
      ExprSkeleton.hasLooseBVarsAt pre.length e = false →
      evalExpr M (pre ++ suf) e = evalExpr M pre e := by
  induction e with
  | sort l => intro _ _ _; cases l with | zero => rfl | succ m => cases m <;> rfl
  | const n => intro _ _ _; rfl
  | fvar _ | mvar _ | natLit _ | strLit _ => intro _ _ _; rfl
  | bvar idx =>
    intro pre suf h
    simp only [ExprSkeleton.hasLooseBVarsAt, decide_eq_false_iff_not, Nat.not_le] at h
    simp only [evalExpr, List.getElem?_append_left h]
  | app fn arg ihf iha =>
    intro pre suf h
    simp only [ExprSkeleton.hasLooseBVarsAt, Bool.or_eq_false_iff] at h
    simp only [evalExpr, ihf pre suf h.1, iha pre suf h.2]
  | lam dom body ihd ihb =>
    intro pre suf h
    simp only [ExprSkeleton.hasLooseBVarsAt, Bool.or_eq_false_iff] at h
    simp only [evalExpr]
    have hd := ihd pre suf h.1
    generalize h1 : evalExpr M (pre ++ suf) dom = d1 at hd ⊢
    generalize h2 : evalExpr M pre dom = d2 at hd ⊢
    subst hd
    congr 1
    funext a
    exact ihb (d1.decode a :: pre) suf h.2
  | forallE dom body ihd ihb =>
    intro pre suf h
    simp only [ExprSkeleton.hasLooseBVarsAt, Bool.or_eq_false_iff] at h
    simp only [evalExpr]
    have hd := ihd pre suf h.1
    generalize h1 : evalExpr M (pre ++ suf) dom = d1 at hd ⊢
    generalize h2 : evalExpr M pre dom = d2 at hd ⊢
    subst hd
    congr 1
    funext a
    exact ihb (d1.decode a :: pre) suf h.2
  | proj s i se ih =>
    intro pre suf h
    simp only [evalExpr, ih pre suf h]

/-- Context satisfaction: each semantic value in `γ` inhabits the evaluation of the corresponding type in `ctx`. -/
inductive CtxSat (M : SymName → SemVal) : List SemVal → List ExprSkeleton → Prop where
  | nil : CtxSat M [] []
  | cons {v : SemVal} {γ : List SemVal} {ty : ExprSkeleton} {ctx : List ExprSkeleton} :
      Inhabits v (evalExpr M γ ty) →
      CtxSat M γ ctx →
      CtxSat M (v :: γ) (ty :: ctx)

theorem ctxSat_lookup {M : SymName → SemVal} {γ : List SemVal} {ctx : List ExprSkeleton}
    (hsat : CtxSat M γ ctx) :
    ∀ {idx : Nat} {ty : ExprSkeleton},
      ctx[idx]? = some ty →
      Inhabits (γ[idx]?.getD .err) (evalExpr M γ (ExprSkeleton.liftBVar (idx + 1) 0 ty)) := by
  induction hsat with
  | nil =>
    intro idx ty h
    simp at h
  | @cons v γ' ty' ctx' hinh hrest ih =>
    intro idx ty h
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      have hlift := evalExpr_liftBVar M ty' [] [v] γ'
      simp only [List.nil_append, List.length_singleton, List.length_nil, List.cons_append] at hlift
      rw [hlift]
      exact hinh
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      have hsub := ih h
      have hlift1 := evalExpr_liftBVar M (ExprSkeleton.liftBVar (k + 1) 0 ty) [] [v] γ'
      simp only [List.nil_append, List.length_singleton, List.length_nil, List.cons_append] at hlift1
      have hcomp : ∀ (e : ExprSkeleton) (a b c : Nat),
          ExprSkeleton.liftBVar a c (ExprSkeleton.liftBVar b c e) =
          ExprSkeleton.liftBVar (a + b) c e := by
        intro e
        induction e with
        | sort _ | const _ | fvar _ | mvar _ | natLit _ | strLit _ => intro _ _ _; rfl
        | bvar j =>
          intro a b c
          simp only [ExprSkeleton.liftBVar]
          by_cases hj : c ≤ j
          · have hj' : c ≤ j + b := Nat.le_trans hj (Nat.le_add_right j b)
            simp only [hj, hj', ↓reduceIte, ExprSkeleton.liftBVar]
            congr 1; omega
          · simp only [hj, ↓reduceIte, ExprSkeleton.liftBVar]
        | app f x ihf ihx => intro a b c; simp [ExprSkeleton.liftBVar, ihf, ihx]
        | lam d b' ihd ihb => intro a b c; simp [ExprSkeleton.liftBVar, ihd, ihb]
        | forallE d b' ihd ihb => intro a b c; simp [ExprSkeleton.liftBVar, ihd, ihb]
        | proj s i x ihx => intro a b c; simp [ExprSkeleton.liftBVar, ihx]
      have h2 : ExprSkeleton.liftBVar (k + 1 + 1) 0 ty =
          ExprSkeleton.liftBVar 1 0 (ExprSkeleton.liftBVar (k + 1) 0 ty) := by
        rw [hcomp]; congr 1; omega
      rw [h2, hlift1]
      exact hsub

/-- Semantic soundness invariant of a `KernelEnv` with respect to a model `M`. -/
structure EnvSound (env : KernelEnv) (M : SymName → SemVal) : Prop where
  has_false : env.contains SymName.falseName = true
  has_true : env.contains SymName.trueName = true
  has_nat : env.contains SymName.natName = true
  has_string : env.contains SymName.stringName = true
  false_interp : M SymName.falseName = .prop False
  true_interp : M SymName.trueName = .prop True
  nat_interp : M SymName.natName = .ty Nat (fun n => .base SymName.natName n)
  string_interp : M SymName.stringName = .ty String (fun s => .strVal s)
  const_sound : ∀ n ci, env.lookup n = some ci →
    n = ci.name ∧
    ExprSkeleton.hasOpenVars ci.type = false ∧
    (∀ c ∈ ci.type.usedConstants, env.contains c = true) ∧
    Inhabits (M ci.name) (evalExpr M [] ci.type)
  defn_sound : ∀ n ci v, env.lookup n = some ci →
    ci.kind = .defnDecl → ci.value? = some v →
    ExprSkeleton.hasOpenVars v = false ∧
    (∀ c ∈ v.usedConstants, env.contains c = true) ∧
    M ci.name = evalExpr M [] v
  induct_sound : ∀ n ci ctors, env.lookup n = some ci →
    ci.kind = .inductDecl ctors →
    ctors.Nodup ∧
    (ci.type = .sort 0 → M n = .prop (!ctors.isEmpty)) ∧
    (ci.type = .sort 1 → isBuiltinCarrierName n = false →
      M n = .ty (Fin ctors.length) (fun i => .base n i.val))
  ctor_sound : ∀ n ci p indCi ctors, env.lookup n = some ci →
    ci.kind = .ctorDecl p → ci.type = .const p →
    env.lookup p = some indCi → indCi.kind = .inductDecl ctors →
    (indCi.type = .sort 0 → M n = .prf) ∧
    (indCi.type = .sort 1 → isBuiltinCarrierName p = false →
      ∀ (i : Fin ctors.length), ctors[i.val]? = some n → M n = .base p i.val)
  proj_sound : ∀ structName idx fTy v,
    lookupStructFieldType? env structName idx = some fTy →
    Inhabits v (M structName) →
    Inhabits (semApp v (.base (SymName.mkSimple "Fin") idx)) (evalExpr M [] fTy)

/-- Every decoded carrier element unconditionally inhabits its semantic type. -/
theorem decode_inhabits_self (d : SemVal) (a : d.carrier) : Inhabits (d.decode a) d := by
  cases d with
  | prop P =>
    cases a with
    | up hP => exact ⟨rfl, hP⟩
  | propSort => exact ⟨a, rfl⟩
  | ty α dec => exact ⟨a, rfl⟩
  | err | sort2 | sort1 | prf | funVal _ _ _ | base _ _ | strVal _ => exact a.elim

/-- Helper: `semPi` is a valid semantic type whenever domain and codomain are valid semantic types. -/
theorem semPi_inhabits_sort {domV : SemVal} {bodyFn : domV.carrier → SemVal} {u v : Nat}
    (hDom : Inhabits domV (if u == 0 then .propSort else .sort1))
    (hBody : ∀ a : domV.carrier, Inhabits (bodyFn a) (if v == 0 then .propSort else .sort1)) :
    Inhabits (semPi domV bodyFn) (if imaxLevel u v == 0 then .propSort else .sort1) := by
  have _ : IsSemType domV := inhabits_sort_implies_isSemType hDom
  unfold semPi
  by_cases hv : v = 0
  · subst hv
    have hall : ∀ a : domV.carrier, ∃ P : Prop, bodyFn a = .prop P := by
      intro a
      have ha := hBody a
      simp only [BEq.rfl, ↓reduceIte, Inhabits] at ha
      exact ha
    simp only [imaxLevel, BEq.rfl, ↓reduceIte, Inhabits]
    refine ⟨∀ a : domV.carrier, semAsProp (bodyFn a), ?_⟩
    split
    · rfl
    · exact absurd hall (by assumption)
  · have hne : (v == 0) = false := beq_false_of_ne hv
    have himax : (imaxLevel u v == 0) = false := by
      simp only [imaxLevel, hne, Bool.false_eq_true, ↓reduceIte]
      exact beq_false_of_ne (by omega)
    simp only [himax, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hall
      exact Or.inr (Or.inl ⟨∀ a : domV.carrier, semAsProp (bodyFn a), rfl⟩)
    · right; right
      refine ⟨(a : domV.carrier) → (bodyFn a).carrier,
        fun f => semLam domV (fun a => (bodyFn a).decode (f a)), ?_, rfl⟩
      intro f₁ f₂ heq
      dsimp only at heq
      funext a
      have hBa : IsSemType (bodyFn a) := inhabits_sort_implies_isSemType (hBody a)
      have h1 := semApp_semLam (inhabits_sort_implies_isSemType hDom)
        (fun x => (bodyFn x).decode (f₁ x)) a
      have h2 := semApp_semLam (inhabits_sort_implies_isSemType hDom)
        (fun x => (bodyFn x).decode (f₂ x)) a
      rw [heq] at h1
      have hdec : (bodyFn a).decode (f₁ a) = (bodyFn a).decode (f₂ a) := h1.symm.trans h2
      exact isSemType_decode_injective hBa hdec

/-- Helper: `semLam` inhabits `semPi` whenever every fiber `bodyVal a` inhabits `codFn a`. -/
theorem semLam_inhabits_semPi {domV : SemVal} {bodyVal codFn : domV.carrier → SemVal}
    (hCodType : ∀ a : domV.carrier, IsSemType (codFn a))
    (hBody : ∀ a : domV.carrier, Inhabits (bodyVal a) (codFn a)) :
    Inhabits (semLam domV bodyVal) (semPi domV codFn) := by
  unfold semPi
  split
  · rename_i hall
    have hallPrf : ∀ a : domV.carrier, bodyVal a = .prf := by
      intro a
      rcases hall a with ⟨P, hP⟩
      have ha := hBody a
      rw [hP] at ha
      exact ha.1
    have hallProp : ∀ a : domV.carrier, semAsProp (codFn a) := by
      intro a
      rcases hall a with ⟨P, hP⟩
      have ha := hBody a
      rw [hP] at ha ⊢
      exact ha.2
    unfold semLam
    simp only [Inhabits]
    refine ⟨?_, hallProp⟩
    split
    · rfl
    · exact absurd hallPrf (by assumption)
  · have hex : ∀ a : domV.carrier, ∃ b : (codFn a).carrier, (codFn a).decode b = bodyVal a :=
      fun a => (inhabits_iff_exists_decode (hCodType a)).mp (hBody a)
    let f : (a : domV.carrier) → (codFn a).carrier := fun a => Classical.choose (hex a)
    have hf : ∀ a : domV.carrier, (codFn a).decode (f a) = bodyVal a :=
      fun a => Classical.choose_spec (hex a)
    simp only [Inhabits]
    refine ⟨f, ?_⟩
    congr 1
    funext a
    exact hf a

/-- Helper: `semApp` preserves inhabitability across `semPi`. -/
theorem semApp_inhabits {fnV argV domV : SemVal} {codFn : domV.carrier → SemVal}
    (hDom : IsSemType domV)
    (hFn : Inhabits fnV (semPi domV codFn))
    (hArg : Inhabits argV domV) :
    ∃ a : domV.carrier, domV.decode a = argV ∧ Inhabits (semApp fnV argV) (codFn a) := by
  rcases (inhabits_iff_exists_decode hDom).mp hArg with ⟨a, ha⟩
  refine ⟨a, ha, ?_⟩
  unfold semPi at hFn
  split at hFn
  · rename_i hall
    rcases hall a with ⟨P, hP⟩
    simp only [Inhabits] at hFn
    rcases hFn with ⟨hfnPrf, hAll⟩
    have hPa : P := by
      have := hAll a
      rw [hP] at this
      exact this
    rw [hfnPrf, hP]
    exact ⟨rfl, hPa⟩
  · simp only [Inhabits] at hFn
    rcases hFn with ⟨f, hf⟩
    rw [← hf, ← ha, semApp_semLam hDom]
    exact decode_inhabits_self (codFn a) (f a)

/-- Helper: semantic evaluation of `.sort u` for `u ≤ maxModelUniverse`. -/
theorem evalExpr_sort_eq (M : SymName → SemVal) (γ : List SemVal) {u : Nat}
    (hu : u ≤ maxModelUniverse) :
    evalExpr M γ (.sort u) = if u == 0 then .propSort else .sort1 := by
  cases u with
  | zero => rfl
  | succ m =>
    have hm : m = 0 := by unfold maxModelUniverse at hu; omega
    subst hm; rfl

/-- Helper: every field type extracted by `structFieldTypes?` is closed. -/
theorem structFieldTypes?_closed (structName : SymName) (ty : ExprSkeleton) :
    ∀ {fields : List ExprSkeleton},
      structFieldTypes? structName ty = some fields →
      ∀ f ∈ fields, ExprSkeleton.hasOpenVars f = false := by
  induction ty with
  | const n =>
    intro fields h f hf
    simp only [structFieldTypes?] at h
    split at h <;> simp at h
    subst h; cases hf
  | forallE dom body _ ihb =>
    intro fields h f hf
    simp only [structFieldTypes?] at h
    split at h
    · simp at h
    · rename_i hopen
      split at h
      · simp at h
      · cases hsub : structFieldTypes? structName body with
        | none => simp [hsub] at h
        | some rest =>
          simp only [hsub, Option.some.injEq] at h
          subst h
          cases hf with
          | head =>
            cases hdom : ExprSkeleton.hasOpenVars dom with
            | false => rfl
            | true => exact False.elim (hopen hdom)
          | tail _ hmem =>
            exact ihb hsub f hmem
  | sort _ | app _ _ | lam _ _ | bvar _ | fvar _ | mvar _ | natLit _ | strLit _ | proj _ _ _ =>
    intro fields h; simp [structFieldTypes?] at h

theorem lookupStructFieldType?_closed {env : KernelEnv} {structName : SymName} {idx : Nat}
    {fTy : ExprSkeleton}
    (h : lookupStructFieldType? env structName idx = some fTy) :
    ExprSkeleton.hasOpenVars fTy = false := by
  unfold lookupStructFieldType? at h
  cases h1 : env.lookup structName with
  | none => simp [h1] at h
  | some indCi =>
    simp only [h1] at h
    cases h2 : indCi.kind with
    | inductDecl ctors =>
      simp only [h2] at h
      cases ctors with
      | nil => simp at h
      | cons ctorName rest =>
        cases rest with
        | cons _ _ => simp at h
        | nil =>
          cases h3 : env.lookup ctorName with
          | none => simp [h3] at h
          | some ctorCi =>
            simp only [h3] at h
            split at h
            · cases h4 : structFieldTypes? structName ctorCi.type with
              | none => simp [h4] at h
              | some fields =>
                simp only [h4] at h
                exact structFieldTypes?_closed structName ctorCi.type h4 fTy (List.mem_of_getElem? h)
            · simp at h
    | axiomDecl | defnDecl | thmDecl | opaqueDecl | quotDecl | ctorDecl _ | recDecl _ =>
      simp [h2] at h

/--
Simultaneous fuel-induction semantic soundness of the structural kernel typechecker:
For any sound environment `(env, M)` and satisfied context `(γ, ctx)`:
1. `whnf` preserves `evalExpr M γ`;
2. `isDefEq` implies semantic equality `evalExpr M γ e₁ = evalExpr M γ e₂`;
3. `inferType` implies semantic inhabitability `Inhabits (evalExpr M γ e) (evalExpr M γ T)`.
-/
theorem kernel_sound_at_fuel {env : KernelEnv} {M : SymName → SemVal} (henv : EnvSound env M) :
    ∀ (fuel : Nat),
      (∀ (ctx : List ExprSkeleton) (γ : List SemVal) (e : ExprSkeleton),
        CtxSat M γ ctx →
        evalExpr M γ (whnf env fuel ctx e) = evalExpr M γ e) ∧
      (∀ (ctx : List ExprSkeleton) (γ : List SemVal) (e₁ e₂ : ExprSkeleton),
        CtxSat M γ ctx →
        isDefEq env fuel ctx e₁ e₂ = true →
        evalExpr M γ e₁ = evalExpr M γ e₂) ∧
      (∀ (ctx : List ExprSkeleton) (γ : List SemVal) (e T : ExprSkeleton),
        CtxSat M γ ctx →
        inferType env fuel ctx e = .ok T →
        Inhabits (evalExpr M γ e) (evalExpr M γ T)) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro _ _ _ _; rfl
    · intro _ _ e₁ e₂ _ h
      simp only [isDefEq, beq_iff_eq] at h
      rw [h]
    · intro _ _ _ _ _ h
      simp [inferType] at h
  | succ k ih =>
    rcases ih with ⟨ihWhnf, ihDefEq, ihInfer⟩
    refine ⟨?_, ?_, ?_⟩
    · -- Part 1: whnf soundness
      intro ctx γ e hsat
      cases e with
      | const n =>
        simp only [whnf]
        split
        · rename_i ci hlu
          split
          · rename_i v hkind hval
            have ⟨hclosed, _, hdef⟩ := henv.defn_sound n ci v hlu hkind hval
            have ⟨hnEq, _, _, _⟩ := henv.const_sound n ci hlu
            rw [ihWhnf ctx γ v hsat]
            have hnoLoose : ExprSkeleton.hasLooseBVarsAt 0 v = false := by
              simp only [ExprSkeleton.hasOpenVars, Bool.or_eq_false_iff] at hclosed
              exact hclosed.2
            have hcl := evalExpr_closed M v [] γ hnoLoose
            simp only [List.nil_append] at hcl
            rw [hcl, ← hdef, ← hnEq]
            rfl
          · rfl
        · rfl
      | app fn arg =>
        simp only [whnf]
        have hfnEq := ihWhnf ctx γ fn hsat
        split
        · rename_i dom body hw
          split
          · rename_i u argTy hdom harg
            split
            · rename_i hcond
              rw [Bool.and_eq_true] at hcond
              have hDomInh := ihInfer ctx γ dom (.sort u) hsat hdom
              rw [evalExpr_sort_eq M γ (of_decide_eq_true hcond.1)] at hDomInh
              have hDomT : IsSemType (evalExpr M γ dom) := inhabits_sort_implies_isSemType hDomInh
              have hArgInh := ihInfer ctx γ arg argTy hsat harg
              have hTyEq := ihDefEq ctx γ argTy dom hsat hcond.2
              rw [hTyEq] at hArgInh
              rcases (inhabits_iff_exists_decode hDomT).mp hArgInh with ⟨a, ha⟩
              rw [ihWhnf ctx γ (ExprSkeleton.instantiateBVar body arg) hsat]
              rw [evalExpr_instantiateBVar]
              simp only [evalExpr]
              rw [← hfnEq, hw]
              simp only [evalExpr]
              rw [← ha, semApp_semLam hDomT]
            · simp only [evalExpr, hfnEq]
          · simp only [evalExpr, hfnEq]
        · simp only [evalExpr, hfnEq]
      | sort _ | lam _ _ | forallE _ _ | bvar _ | fvar _ | mvar _ | natLit _ | strLit _ | proj _ _ _ =>
        rfl
    · -- Part 2: isDefEq soundness
      intro ctx γ e₁ e₂ hsat hdeq
      simp only [isDefEq] at hdeq
      have hw₁ := ihWhnf ctx γ e₁ hsat
      have hw₂ := ihWhnf ctx γ e₂ hsat
      rw [← hw₁, ← hw₂]
      generalize hw1eq : whnf env k ctx e₁ = w₁ at hdeq ⊢
      generalize hw2eq : whnf env k ctx e₂ = w₂ at hdeq ⊢
      by_cases heq : w₁ = w₂
      · rw [heq]
      · have hbeq : (w₁ == w₂) = false := beq_false_of_ne heq
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hdeq
        cases w₁ <;> cases w₂ <;> simp at hdeq
        · rename_i f₁ a₁ f₂ a₂
          simp only [evalExpr, ihDefEq ctx γ f₁ f₂ hsat hdeq.1, ihDefEq ctx γ a₁ a₂ hsat hdeq.2]
        · rename_i d₁ b₁ d₂ b₂
          have hd := ihDefEq ctx γ d₁ d₂ hsat hdeq.1
          simp only [evalExpr]
          generalize h1 : evalExpr M γ d₁ = dv1 at hd ⊢
          generalize h2 : evalExpr M γ d₂ = dv2 at hd ⊢
          subst hd
          congr 1
          funext a
          have hsat' : CtxSat M (dv1.decode a :: γ) (d₁ :: ctx) := by
            refine CtxSat.cons ?_ hsat
            rw [h1]
            exact decode_inhabits_self dv1 a
          exact ihDefEq (d₁ :: ctx) (dv1.decode a :: γ) b₁ b₂ hsat' hdeq.2
        · rename_i d₁ b₁ d₂ b₂
          have hd := ihDefEq ctx γ d₁ d₂ hsat hdeq.1
          simp only [evalExpr]
          generalize h1 : evalExpr M γ d₁ = dv1 at hd ⊢
          generalize h2 : evalExpr M γ d₂ = dv2 at hd ⊢
          subst hd
          congr 1
          funext a
          have hsat' : CtxSat M (dv1.decode a :: γ) (d₁ :: ctx) := by
            refine CtxSat.cons ?_ hsat
            rw [h1]
            exact decode_inhabits_self dv1 a
          exact ihDefEq (d₁ :: ctx) (dv1.decode a :: γ) b₁ b₂ hsat' hdeq.2
        · rename_i s₁ i₁ x₁ s₂ i₂ x₂
          rcases hdeq with ⟨⟨hs, hi⟩, hx⟩
          subst hs; subst hi
          simp only [evalExpr, ihDefEq ctx γ x₁ x₂ hsat hx]
    · -- Part 3: inferType soundness
      intro ctx γ e T hsat hinf
      cases e with
      | sort l =>
        simp only [inferType] at hinf
        split at hinf
        · rename_i hl
          injection hinf with hT
          subst hT
          cases l with
          | zero => exact Or.inl rfl
          | succ m =>
            have hm : m = 0 := by unfold maxModelUniverse at hl; omega
            subst hm
            rfl
        · cases hinf
      | bvar idx =>
        simp only [inferType] at hinf
        split at hinf
        · rename_i ty hget
          injection hinf with hT
          subst hT
          exact ctxSat_lookup hsat hget
        · cases hinf
      | fvar _ | mvar _ =>
        simp [inferType] at hinf
      | const n =>
        simp only [inferType] at hinf
        split at hinf
        · rename_i ci hlu
          injection hinf with hT
          subst hT
          have ⟨hnEq, hclosed, _, hinh⟩ := henv.const_sound n ci hlu
          have hnoLoose : ExprSkeleton.hasLooseBVarsAt 0 ci.type = false := by
            simp only [ExprSkeleton.hasOpenVars, Bool.or_eq_false_iff] at hclosed
            exact hclosed.2
          have hcl := evalExpr_closed M ci.type [] γ hnoLoose
          simp only [List.nil_append] at hcl
          simp only [evalExpr, hcl, hnEq]
          exact hinh
        · cases hinf
      | natLit n =>
        simp only [inferType] at hinf
        split at hinf
        · injection hinf with hT
          subst hT
          simp only [evalExpr, henv.nat_interp, Inhabits]
          exact ⟨n, rfl⟩
        · cases hinf
      | strLit s =>
        simp only [inferType] at hinf
        split at hinf
        · injection hinf with hT
          subst hT
          simp only [evalExpr, henv.string_interp, Inhabits]
          exact ⟨s, rfl⟩
        · cases hinf
      | forallE dom body =>
        simp only [inferType, bind, Except.bind] at hinf
        cases hds : inferType env k ctx dom with
        | error _ => simp [hds] at hinf
        | ok domSort =>
          rw [hds] at hinf
          dsimp only at hinf
          split at hinf
          · rename_i u hdw
            split at hinf
            · cases hinf
            · rename_i hnotu
              have hu : u ≤ maxModelUniverse := by
                cases h : decide (u ≤ maxModelUniverse)
                · exfalso; exact hnotu (by simp [h])
                · exact of_decide_eq_true h
              cases hbs : inferType env k (dom :: ctx) body with
              | error _ => simp [hbs] at hinf
              | ok bodySort =>
                rw [hbs] at hinf
                dsimp only at hinf
                split at hinf
                · rename_i v hbw
                  split at hinf
                  · cases hinf
                  · rename_i hnotv
                    have hv : v ≤ maxModelUniverse := by
                      cases h : decide (v ≤ maxModelUniverse)
                      · exfalso; exact hnotv (by simp [h])
                      · exact of_decide_eq_true h
                    simp only [pure, Except.pure, Except.ok.injEq] at hinf
                    subst hinf
                    have hDomInh := ihInfer ctx γ dom domSort hsat hds
                    rw [← ihWhnf ctx γ domSort hsat, hdw, evalExpr_sort_eq M γ hu] at hDomInh
                    have hBodyInh : ∀ a : (evalExpr M γ dom).carrier,
                        Inhabits (evalExpr M ((evalExpr M γ dom).decode a :: γ) body)
                          (if v == 0 then .propSort else .sort1) := by
                      intro a
                      have hsat' : CtxSat M ((evalExpr M γ dom).decode a :: γ) (dom :: ctx) :=
                        CtxSat.cons (decode_inhabits_self (evalExpr M γ dom) a) hsat
                      have hb := ihInfer (dom :: ctx) ((evalExpr M γ dom).decode a :: γ) body bodySort hsat' hbs
                      rw [← ihWhnf (dom :: ctx) ((evalExpr M γ dom).decode a :: γ) bodySort hsat',
                        hbw, evalExpr_sort_eq M _ hv] at hb
                      exact hb
                    have himaxLe : imaxLevel u v ≤ maxModelUniverse := by
                      unfold imaxLevel maxModelUniverse at *
                      split <;> omega
                    simp only [evalExpr, evalExpr_sort_eq M γ himaxLe]
                    exact semPi_inhabits_sort hDomInh hBodyInh
                · cases hinf
          · cases hinf
      | lam dom body =>
        simp only [inferType, bind, Except.bind] at hinf
        cases hds : inferType env k ctx dom with
        | error _ => simp [hds] at hinf
        | ok domSort =>
          rw [hds] at hinf
          dsimp only at hinf
          split at hinf
          · rename_i u hdw
            split at hinf
            · cases hinf
            · cases hbt : inferType env k (dom :: ctx) body with
              | error _ => simp [hbt] at hinf
              | ok bodyTy =>
                rw [hbt] at hinf
                dsimp only at hinf
                cases hbts : inferType env k (dom :: ctx) bodyTy with
                | error _ => simp [hbts] at hinf
                | ok bodyTySort =>
                  rw [hbts] at hinf
                  dsimp only at hinf
                  split at hinf
                  · rename_i v hbw
                    split at hinf
                    · cases hinf
                    · rename_i hnotv
                      have hv : v ≤ maxModelUniverse := by
                        cases h : decide (v ≤ maxModelUniverse)
                        · exfalso; exact hnotv (by simp [h])
                        · exact of_decide_eq_true h
                      simp only [pure, Except.pure, Except.ok.injEq] at hinf
                      subst hinf
                      have hCodType : ∀ a : (evalExpr M γ dom).carrier,
                          IsSemType (evalExpr M ((evalExpr M γ dom).decode a :: γ) bodyTy) := by
                        intro a
                        have hsat' : CtxSat M ((evalExpr M γ dom).decode a :: γ) (dom :: ctx) :=
                          CtxSat.cons (decode_inhabits_self (evalExpr M γ dom) a) hsat
                        have hts := ihInfer (dom :: ctx) ((evalExpr M γ dom).decode a :: γ)
                          bodyTy bodyTySort hsat' hbts
                        rw [← ihWhnf (dom :: ctx) ((evalExpr M γ dom).decode a :: γ)
                          bodyTySort hsat', hbw, evalExpr_sort_eq M _ hv] at hts
                        exact inhabits_sort_implies_isSemType hts
                      have hBodyInh : ∀ a : (evalExpr M γ dom).carrier,
                          Inhabits (evalExpr M ((evalExpr M γ dom).decode a :: γ) body)
                            (evalExpr M ((evalExpr M γ dom).decode a :: γ) bodyTy) := by
                        intro a
                        have hsat' : CtxSat M ((evalExpr M γ dom).decode a :: γ) (dom :: ctx) :=
                          CtxSat.cons (decode_inhabits_self (evalExpr M γ dom) a) hsat
                        exact ihInfer (dom :: ctx) ((evalExpr M γ dom).decode a :: γ)
                          body bodyTy hsat' hbt
                      simp only [evalExpr]
                      exact semLam_inhabits_semPi hCodType hBodyInh
                  · cases hinf
          · cases hinf
      | app fn arg =>
        simp only [inferType, bind, Except.bind] at hinf
        cases hft : inferType env k ctx fn with
        | error _ => simp [hft] at hinf
        | ok fnTy =>
          rw [hft] at hinf
          dsimp only at hinf
          split at hinf
          · rename_i dom bodyTy hfw
            cases hds : inferType env k ctx dom with
            | error _ => simp [hds] at hinf
            | ok domSort =>
              rw [hds] at hinf
              dsimp only at hinf
              split at hinf
              · rename_i u hdw
                split at hinf
                · cases hinf
                · rename_i hnotu
                  have hu : u ≤ maxModelUniverse := by
                    cases h : decide (u ≤ maxModelUniverse)
                    · exfalso; exact hnotu (by simp [h])
                    · exact of_decide_eq_true h
                  cases hat : inferType env k ctx arg with
                  | error _ => simp [hat] at hinf
                  | ok argTy =>
                    rw [hat] at hinf
                    dsimp only at hinf
                    split at hinf
                    · rename_i hdeq
                      simp only [pure, Except.pure, Except.ok.injEq] at hinf
                      subst hinf
                      have hFnInh := ihInfer ctx γ fn fnTy hsat hft
                      rw [← ihWhnf ctx γ fnTy hsat, hfw] at hFnInh
                      simp only [evalExpr] at hFnInh
                      have hDomInh := ihInfer ctx γ dom domSort hsat hds
                      rw [← ihWhnf ctx γ domSort hsat, hdw, evalExpr_sort_eq M γ hu] at hDomInh
                      have hDomT := inhabits_sort_implies_isSemType hDomInh
                      have hArgInh := ihInfer ctx γ arg argTy hsat hat
                      rw [ihDefEq ctx γ argTy dom hsat hdeq] at hArgInh
                      rcases semApp_inhabits hDomT hFnInh hArgInh with ⟨a, ha, hres⟩
                      rw [evalExpr_instantiateBVar]
                      rw [← ha]
                      exact hres
                    · cases hinf
              · cases hinf
          · cases hinf
      | proj structName idx structExpr =>
        simp only [inferType, bind, Except.bind] at hinf
        cases hst : inferType env k ctx structExpr with
        | error _ => simp [hst] at hinf
        | ok sTy =>
          rw [hst] at hinf
          dsimp only at hinf
          split at hinf
          · cases hinf
          · rename_i hnotdeq
            have hdeq : isDefEq env k ctx sTy (.const structName) = true := by
              cases h : isDefEq env k ctx sTy (.const structName)
              · exfalso; exact hnotdeq (by simp [h])
              · rfl
            split at hinf
            · rename_i fTy hfield
              simp only [pure, Except.pure, Except.ok.injEq] at hinf
              subst hinf
              have hSInh := ihInfer ctx γ structExpr sTy hsat hst
              rw [ihDefEq ctx γ sTy (.const structName) hsat hdeq] at hSInh
              simp only [evalExpr] at hSInh ⊢
              have hpr := henv.proj_sound structName idx fTy (evalExpr M γ structExpr) hfield hSInh
              have hopen := lookupStructFieldType?_closed hfield
              have hnoLoose : ExprSkeleton.hasLooseBVarsAt 0 fTy = false := by
                simp only [ExprSkeleton.hasOpenVars, Bool.or_eq_false_iff] at hopen
                exact hopen.2
              have hcl := evalExpr_closed M fTy [] γ hnoLoose
              simp only [List.nil_append] at hcl
              rw [hcl]
              exact hpr
            · cases hinf

/-! ## Section 6: Clean-Env Kernel Replay & Consistency Preservation -/

/-- If two models agree on every constant mentioned in `e`, they evaluate `e` identically. -/
theorem evalExpr_eq_of_agree {M₁ M₂ : SymName → SemVal} (e : ExprSkeleton)
    (hagree : ∀ c ∈ e.usedConstants, M₁ c = M₂ c) :
    ∀ (γ : List SemVal), evalExpr M₁ γ e = evalExpr M₂ γ e := by
  induction e with
  | sort l => intro _; cases l with | zero => rfl | succ m => cases m <;> rfl
  | const n =>
    intro _
    exact hagree n (by simp [ExprSkeleton.usedConstants])
  | bvar _ | fvar _ | mvar _ | natLit _ | strLit _ => intro _; rfl
  | app fn arg ihf iha =>
    intro γ
    simp only [evalExpr]
    rw [ihf (fun c hc => hagree c (by simp [ExprSkeleton.usedConstants, hc])) γ,
        iha (fun c hc => hagree c (by simp [ExprSkeleton.usedConstants, hc])) γ]
  | lam dom body ihd ihb =>
    intro γ
    simp only [evalExpr]
    have hd := ihd (fun c hc => hagree c (by simp [ExprSkeleton.usedConstants, hc])) γ
    generalize h1 : evalExpr M₁ γ dom = d1 at hd ⊢
    generalize h2 : evalExpr M₂ γ dom = d2 at hd ⊢
    subst hd
    congr 1
    funext a
    exact ihb (fun c hc => hagree c (by simp [ExprSkeleton.usedConstants, hc])) (d1.decode a :: γ)
  | forallE dom body ihd ihb =>
    intro γ
    simp only [evalExpr]
    have hd := ihd (fun c hc => hagree c (by simp [ExprSkeleton.usedConstants, hc])) γ
    generalize h1 : evalExpr M₁ γ dom = d1 at hd ⊢
    generalize h2 : evalExpr M₂ γ dom = d2 at hd ⊢
    subst hd
    congr 1
    funext a
    exact ihb (fun c hc => hagree c (by simp [ExprSkeleton.usedConstants, hc])) (d1.decode a :: γ)
  | proj s i se ih =>
    intro γ
    simp only [evalExpr]
    rw [ih (fun c hc => hagree c (by simp [ExprSkeleton.usedConstants, hc])) γ]

/-- Every constant referenced by a typechecked expression exists in `env`. -/
theorem inferType_usedConstants_in_env {env : KernelEnv} :
    ∀ (fuel : Nat) (ctx : List ExprSkeleton) (e T : ExprSkeleton),
      inferType env fuel ctx e = .ok T →
      ∀ c ∈ e.usedConstants, env.contains c = true := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [inferType] at h
  | succ k ih =>
    intro ctx e T hinf c hc
    cases e with
    | sort _ | bvar _ | fvar _ | mvar _ => simp [ExprSkeleton.usedConstants] at hc
    | const n =>
      simp only [ExprSkeleton.usedConstants, List.mem_singleton] at hc
      subst hc
      simp only [inferType] at hinf
      split at hinf
      · rename_i ci hlu
        simp [KernelEnv.contains, hlu]
      · cases hinf
    | natLit _ =>
      simp only [ExprSkeleton.usedConstants, List.mem_singleton] at hc
      subst hc
      simp only [inferType] at hinf
      split at hinf
      · assumption
      · cases hinf
    | strLit _ =>
      simp only [ExprSkeleton.usedConstants, List.mem_singleton] at hc
      subst hc
      simp only [inferType] at hinf
      split at hinf
      · assumption
      · cases hinf
    | forallE dom body =>
      simp only [inferType, bind, Except.bind] at hinf
      cases hds : inferType env k ctx dom with
      | error _ => simp [hds] at hinf
      | ok domSort =>
        rw [hds] at hinf; dsimp only at hinf
        split at hinf
        · split at hinf
          · cases hinf
          · cases hbs : inferType env k (dom :: ctx) body with
            | error _ => simp [hbs] at hinf
            | ok bodySort =>
              simp only [ExprSkeleton.usedConstants, List.mem_append] at hc
              rcases hc with hc | hc
              · exact ih ctx dom domSort hds c hc
              · exact ih (dom :: ctx) body bodySort hbs c hc
        · cases hinf
    | lam dom body =>
      simp only [inferType, bind, Except.bind] at hinf
      cases hds : inferType env k ctx dom with
      | error _ => simp [hds] at hinf
      | ok domSort =>
        rw [hds] at hinf; dsimp only at hinf
        split at hinf
        · split at hinf
          · cases hinf
          · cases hbt : inferType env k (dom :: ctx) body with
            | error _ => simp [hbt] at hinf
            | ok bodyTy =>
              simp only [ExprSkeleton.usedConstants, List.mem_append] at hc
              rcases hc with hc | hc
              · exact ih ctx dom domSort hds c hc
              · exact ih (dom :: ctx) body bodyTy hbt c hc
        · cases hinf
    | app fn arg =>
      simp only [inferType, bind, Except.bind] at hinf
      cases hft : inferType env k ctx fn with
      | error _ => simp [hft] at hinf
      | ok fnTy =>
        rw [hft] at hinf; dsimp only at hinf
        split at hinf
        · rename_i dom _ _
          cases hds : inferType env k ctx dom with
          | error _ => simp [hds] at hinf
          | ok domSort =>
            rw [hds] at hinf; dsimp only at hinf
            split at hinf
            · split at hinf
              · cases hinf
              · cases hat : inferType env k ctx arg with
                | error _ => simp [hat] at hinf
                | ok argTy =>
                  simp only [ExprSkeleton.usedConstants, List.mem_append] at hc
                  rcases hc with hc | hc
                  · exact ih ctx fn fnTy hft c hc
                  · exact ih ctx arg argTy hat c hc
            · cases hinf
        · cases hinf
    | proj structName idx structExpr =>
      simp only [inferType, bind, Except.bind] at hinf
      cases hst : inferType env k ctx structExpr with
      | error _ => simp [hst] at hinf
      | ok sTy =>
        rw [hst] at hinf; dsimp only at hinf
        split at hinf
        · cases hinf
        · split at hinf
          · rename_i fTy hfield
            simp only [ExprSkeleton.usedConstants, List.mem_cons] at hc
            rcases hc with rfl | hc
            · unfold lookupStructFieldType? at hfield
              cases hlu : env.lookup c with
              | none => simp [hlu] at hfield
              | some _ => simp [KernelEnv.contains, hlu]
            · exact ih ctx structExpr sTy hst c hc
          · cases hinf

/-- Helper: construct a semantic value inhabiting any valid inductive arity. -/
noncomputable def interpInductArity (M : SymName → SemVal) (indName : SymName)
    (ctors : List SymName) : ExprSkeleton → SemVal
  | .sort 0 => .prop (!ctors.isEmpty)
  | .sort 1 => .ty (Fin ctors.length) (fun i => .base indName i.val)
  | .forallE dom body =>
    semLam (evalExpr M [] dom) (fun _ => interpInductArity M indName ctors body)
  | _ => .err

theorem isValidPropInductArity_isSemType {env : KernelEnv} {M : SymName → SemVal}
    (henv : EnvSound env M) (fuel : Nat) :
    ∀ (ty : ExprSkeleton),
      isValidPropInductArity env fuel ty = true →
      Inhabits (evalExpr M [] ty) .sort1 := by
  intro ty hvalid
  induction ty with
  | sort l =>
    cases l with
    | zero => exact Or.inl rfl
    | succ _ => simp [isValidPropInductArity] at hvalid
  | forallE dom body _ ihb =>
    simp only [isValidPropInductArity] at hvalid
    split at hvalid
    · rename_i u hdom
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hvalid
      rcases hvalid with ⟨⟨huDec, hnoLoose⟩, hbodyValid⟩
      have hu : u ≤ maxModelUniverse := of_decide_eq_true huDec
      have hDomInh := (kernel_sound_at_fuel henv fuel).2.2 [] [] dom (.sort u) CtxSat.nil hdom
      rw [evalExpr_sort_eq M [] hu] at hDomInh
      have hBodySort := ihb hbodyValid
      have hclosed : ∀ a : (evalExpr M [] dom).carrier,
          evalExpr M [(evalExpr M [] dom).decode a] body = evalExpr M [] body := by
        intro a
        have h := evalExpr_closed M body [] [(evalExpr M [] dom).decode a] hnoLoose
        simp only [List.nil_append] at h
        exact h
      have hpi := semPi_inhabits_sort (u := u) (v := 1)
        (bodyFn := fun a => evalExpr M [(evalExpr M [] dom).decode a] body)
        hDomInh (fun a => by rw [hclosed a]; exact hBodySort)
      have himax : (imaxLevel u 1 == 0) = false := by
        simp [imaxLevel]
      simp only [himax, Bool.false_eq_true, ↓reduceIte] at hpi
      exact hpi
    · simp at hvalid
  | const _ | app _ _ | lam _ _ | bvar _ | fvar _ | mvar _ | natLit _ | strLit _ | proj _ _ _ =>
    simp [isValidPropInductArity] at hvalid

theorem interpPropInductArity_inhabits {env : KernelEnv} {M : SymName → SemVal}
    (henv : EnvSound env M) (fuel : Nat) (indName : SymName) (ctors : List SymName) :
    ∀ (ty : ExprSkeleton),
      isValidPropInductArity env fuel ty = true →
      Inhabits (interpInductArity M indName ctors ty) (evalExpr M [] ty) := by
  intro ty hvalid
  induction ty with
  | sort l =>
    cases l with
    | zero => exact ⟨!ctors.isEmpty, rfl⟩
    | succ _ => simp [isValidPropInductArity] at hvalid
  | forallE dom body _ ihb =>
    simp only [isValidPropInductArity] at hvalid
    split at hvalid
    · rename_i u hdom
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hvalid
      rcases hvalid with ⟨⟨huDec, hnoLoose⟩, hbodyValid⟩
      have hbodyInh := ihb hbodyValid
      have hbodySort := isValidPropInductArity_isSemType henv fuel body hbodyValid
      have hbodySem : IsSemType (evalExpr M [] body) :=
        inhabits_sort_implies_isSemType (u := 1) hbodySort
      have hbodyClosed : ∀ a : (evalExpr M [] dom).carrier,
          evalExpr M [(evalExpr M [] dom).decode a] body = evalExpr M [] body := by
        intro a
        have h := evalExpr_closed M body [] [(evalExpr M [] dom).decode a] hnoLoose
        simp only [List.nil_append] at h
        exact h
      simp only [interpInductArity, evalExpr]
      apply semLam_inhabits_semPi
      · intro a; rw [hbodyClosed a]; exact hbodySem
      · intro a; rw [hbodyClosed a]; exact hbodyInh
    · simp at hvalid
  | const _ | app _ _ | lam _ _ | bvar _ | fvar _ | mvar _ | natLit _ | strLit _ | proj _ _ _ =>
    simp [isValidPropInductArity] at hvalid

theorem interpInductArity_inhabits {env : KernelEnv} {M : SymName → SemVal}
    (henv : EnvSound env M) (fuel : Nat) (indName : SymName) (ctors : List SymName)
    {ty : ExprSkeleton} (hvalid : isValidInductArity env fuel ty = true) :
    Inhabits (interpInductArity M indName ctors ty) (evalExpr M [] ty) := by
  simp only [isValidInductArity, Bool.or_eq_true, beq_iff_eq] at hvalid
  rcases hvalid with rfl | hprop
  · right; right
    refine ⟨Fin ctors.length, fun i => .base indName i.val, ?_, rfl⟩
    intro i j heq
    injection heq with _ hval
    exact Fin.ext hval
  · exact interpPropInductArity_inhabits henv fuel indName ctors ty hprop

/-- Helper: build a semantic inhabitant for a constructor telescope `A₁ → ... → A_k → inductParent`. -/
noncomputable def interpCtorType (M : SymName → SemVal) (leafVal : SemVal) :
    ExprSkeleton → SemVal
  | .const _ => leafVal
  | .forallE dom body =>
    semLam (evalExpr M [] dom) (fun _ => interpCtorType M leafVal body)
  | _ => .err

theorem isValidCtorType_isSemType {env : KernelEnv} {M : SymName → SemVal}
    (henv : EnvSound env M) (fuel : Nat) (inductParent : SymName)
    (hParentSort : Inhabits (M inductParent) .sort1) :
    ∀ (ty : ExprSkeleton),
      isValidCtorType env fuel inductParent ty = true →
      Inhabits (evalExpr M [] ty) .sort1 := by
  intro ty hvalid
  induction ty with
  | const n =>
    simp only [isValidCtorType, beq_iff_eq] at hvalid
    subst hvalid
    exact hParentSort
  | forallE dom body _ ihb =>
    simp only [isValidCtorType] at hvalid
    split at hvalid
    · rename_i u hdom
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hvalid
      rcases hvalid with ⟨⟨huDec, hnoLoose⟩, hbodyValid⟩
      have hu : u ≤ maxModelUniverse := of_decide_eq_true huDec
      have hDomInh := (kernel_sound_at_fuel henv fuel).2.2 [] [] dom (.sort u) CtxSat.nil hdom
      rw [evalExpr_sort_eq M [] hu] at hDomInh
      have hBodySort := ihb hbodyValid
      have hclosed : ∀ a : (evalExpr M [] dom).carrier,
          evalExpr M [(evalExpr M [] dom).decode a] body = evalExpr M [] body := by
        intro a
        have h := evalExpr_closed M body [] [(evalExpr M [] dom).decode a] hnoLoose
        simp only [List.nil_append] at h
        exact h
      have hpi := semPi_inhabits_sort (u := u) (v := 1)
        (bodyFn := fun a => evalExpr M [(evalExpr M [] dom).decode a] body)
        hDomInh (fun a => by rw [hclosed a]; exact hBodySort)
      have himax : (imaxLevel u 1 == 0) = false := by simp [imaxLevel]
      simp only [himax, Bool.false_eq_true, ↓reduceIte] at hpi
      exact hpi
    · simp at hvalid
  | sort _ | app _ _ | lam _ _ | bvar _ | fvar _ | mvar _ | natLit _ | strLit _ | proj _ _ _ =>
    simp [isValidCtorType] at hvalid

theorem interpCtorType_inhabits {env : KernelEnv} {M : SymName → SemVal}
    (henv : EnvSound env M) (fuel : Nat) (inductParent : SymName) (leafVal : SemVal)
    (hParentSort : Inhabits (M inductParent) .sort1)
    (hLeaf : Inhabits leafVal (M inductParent)) :
    ∀ (ty : ExprSkeleton),
      isValidCtorType env fuel inductParent ty = true →
      Inhabits (interpCtorType M leafVal ty) (evalExpr M [] ty) := by
  intro ty hvalid
  induction ty with
  | const n =>
    simp only [isValidCtorType, beq_iff_eq] at hvalid
    subst hvalid
    exact hLeaf
  | forallE dom body _ ihb =>
    simp only [isValidCtorType] at hvalid
    split at hvalid
    · rename_i u hdom
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hvalid
      rcases hvalid with ⟨⟨_, hnoLoose⟩, hbodyValid⟩
      have hbodyInh := ihb hbodyValid
      have hbodySort := isValidCtorType_isSemType henv fuel inductParent hParentSort body hbodyValid
      have hbodySem : IsSemType (evalExpr M [] body) :=
        inhabits_sort_implies_isSemType (u := 1) hbodySort
      have hclosed : ∀ a : (evalExpr M [] dom).carrier,
          evalExpr M [(evalExpr M [] dom).decode a] body = evalExpr M [] body := by
        intro a
        have h := evalExpr_closed M body [] [(evalExpr M [] dom).decode a] hnoLoose
        simp only [List.nil_append] at h
        exact h
      simp only [interpCtorType, evalExpr]
      apply semLam_inhabits_semPi
      · intro a; rw [hclosed a]; exact hbodySem
      · intro a; rw [hclosed a]; exact hbodyInh
    · simp at hvalid
  | sort _ | app _ _ | lam _ _ | bvar _ | fvar _ | mvar _ | natLit _ | strLit _ | proj _ _ _ =>
    simp [isValidCtorType] at hvalid

/-- Find the 0-based index of `target` in a list. -/
def listIndexOf? [DecidableEq α] (target : α) : List α → Option Nat
  | [] => none
  | x :: xs =>
    if x == target then some 0
    else (listIndexOf? target xs).map (· + 1)

theorem listIndexOf?_spec [DecidableEq α] (target : α) (xs : List α) :
    ∀ {i : Nat}, listIndexOf? target xs = some i → xs[i]? = some target := by
  induction xs with
  | nil => intro i h; simp [listIndexOf?] at h
  | cons x tl ih =>
    intro i h
    simp only [listIndexOf?] at h
    split at h
    · rename_i hxeq
      simp only [beq_iff_eq] at hxeq
      injection h with hi; subst hi; subst hxeq; rfl
    · cases hsub : listIndexOf? target tl with
      | none => simp [hsub] at h
      | some j =>
        simp only [hsub, Option.map_some, Option.some.injEq] at h
        subst h
        exact ih hsub

theorem listIndexOf?_isSome_of_mem [DecidableEq α] {target : α} {xs : List α}
    (hmem : target ∈ xs) : ∃ i, listIndexOf? target xs = some i := by
  induction xs with
  | nil => cases hmem
  | cons x tl ih =>
    simp only [listIndexOf?]
    by_cases hxeq : x = target
    · subst hxeq; exact ⟨0, by simp⟩
    · have hbeq : (x == target) = false := beq_false_of_ne hxeq
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      cases hmem with
      | head => exact absurd rfl hxeq
      | tail _ htl =>
        rcases ih htl with ⟨j, hj⟩
        exact ⟨j + 1, by simp [hj]⟩

/-- Helper: simplify `semPi` when every fiber evaluates to `.prop`. -/
theorem semPi_eq_prop {domV : SemVal} {bodyFn : domV.carrier → SemVal}
    (hall : ∀ a : domV.carrier, ∃ P : Prop, bodyFn a = .prop P) :
    semPi domV bodyFn = .prop (∀ a : domV.carrier, semAsProp (bodyFn a)) := by
  unfold semPi
  split
  · rfl
  · exact absurd hall (by assumption)

/-- Helper: `canonicalEmptyPropRecType` (`∀ C : Prop, indName → C`) is inhabited whenever `M indName` is empty. -/
theorem canonicalEmptyPropRecType_inhabits {M : SymName → SemVal} {indName : SymName}
    (hEmpty : ¬ Nonempty (M indName).carrier) :
    Inhabits .prf (evalExpr M [] (canonicalEmptyPropRecType indName)) := by
  have hinner : ∀ (C : Prop),
      semPi (M indName) (fun _ => .prop C) = .prop (∀ _ : (M indName).carrier, C) := by
    intro C
    rw [semPi_eq_prop (fun _ => ⟨C, rfl⟩)]
    rfl
  have houter : evalExpr M [] (canonicalEmptyPropRecType indName) =
      .prop (∀ C : Prop, semAsProp (semPi (M indName) (fun _ => .prop C))) := by
    unfold canonicalEmptyPropRecType ExprSkeleton.arrow
    change semPi .propSort (fun C : Prop => semPi (M indName) (fun _ => .prop C)) = _
    exact semPi_eq_prop (fun C => ⟨∀ _ : (M indName).carrier, C, hinner C⟩)
  rw [houter]
  refine ⟨rfl, fun C => ?_⟩
  rw [hinner C]
  exact fun x => False.elim (hEmpty ⟨x⟩)

/-- Helper: `canonicalPropRecType` is semantically valid (inhabited by `.prf`) for any sound inductive. -/
theorem canonicalPropRecType_inhabits {M : SymName → SemVal} {indName : SymName}
    {ctors : List SymName}
    (hIndType : IsSemType (M indName))
    (hCtorsInImg : ∀ c ∈ ctors, ∃ x : (M indName).carrier, M c = (M indName).decode x)
    (hCover : ∀ (x : (M indName).carrier), ∃ c ∈ ctors, M c = (M indName).decode x) :
    Inhabits .prf (evalExpr M [] (canonicalPropRecType indName ctors)) := by
  have hMinorWalk :
      ∀ (rem : List SymName) (γ : List SemVal) (motiveV : SemVal)
        (motiveFn : (M indName).carrier → Prop),
        γ.length ≥ 1 →
        γ[γ.length - 1]? = some motiveV →
        (∀ x : (M indName).carrier, semApp motiveV ((M indName).decode x) = .prop (motiveFn x)) →
        (∀ c ∈ rem, ∃ x : (M indName).carrier, M c = (M indName).decode x) →
        ∃ P : Prop,
          evalExpr M γ (canonicalPropRecType.buildMinors indName γ.length rem) = .prop P ∧
          ((∀ x : (M indName).carrier, (∀ c ∈ rem, M c ≠ (M indName).decode x) → motiveFn x) → P) := by
    intro rem
    induction rem with
    | nil =>
      intro γ motiveV motiveFn hlen hlast hmotive _
      have hidx : ∀ (v : SemVal), (v :: γ)[γ.length]? = some motiveV := by
        intro v
        cases hglen : γ.length with
        | zero => omega
        | succ m =>
          simp only [List.getElem?_cons_succ]
          rw [hglen] at hlast
          simpa using hlast
      have hbody : ∀ (x : (M indName).carrier),
          evalExpr M ((M indName).decode x :: γ) (.app (.bvar γ.length) (.bvar 0)) =
          .prop (motiveFn x) := by
        intro x
        simp only [evalExpr, hidx, List.getElem?_cons_zero, Option.getD_some]
        exact hmotive x
      have hpi : evalExpr M γ (canonicalPropRecType.buildMinors indName γ.length []) =
          .prop (∀ x : (M indName).carrier, motiveFn x) := by
        simp only [canonicalPropRecType.buildMinors, evalExpr]
        unfold semPi
        have hall : ∀ x : (M indName).carrier,
            ∃ P : Prop, evalExpr M ((M indName).decode x :: γ) (.app (.bvar γ.length) (.bvar 0)) = .prop P :=
          fun x => ⟨motiveFn x, hbody x⟩
        split
        · congr 1
          apply propext
          constructor
          · intro h x
            have hx := h x
            dsimp only at hx
            have hb := hbody x
            simp only [evalExpr] at hb
            rw [hb] at hx
            exact hx
          · intro h x
            dsimp only
            have hb := hbody x
            simp only [evalExpr] at hb
            rw [hb]
            exact h x
        · exact absurd hall (by assumption)
      refine ⟨∀ x : (M indName).carrier, motiveFn x, hpi, fun h x => h x (fun _ hc => by cases hc)⟩
    | cons c rest ih =>
      intro γ motiveV motiveFn hlen hlast hmotive hmemC
      rcases hmemC c (List.mem_cons_self) with ⟨xc, hxc⟩
      have hdomEq : semApp (γ[γ.length - 1]?.getD .err) (M c) = .prop (motiveFn xc) := by
        simp only [hlast, Option.getD_some, hxc]
        exact hmotive xc
      have hsub := ih (.prf :: γ) motiveV motiveFn (by simp)
        (by
          simp only [List.length_cons, Nat.add_sub_cancel]
          cases hglen : γ.length with
          | zero => omega
          | succ m =>
            simp only [List.getElem?_cons_succ]
            rw [hglen] at hlast
            simpa using hlast)
        hmotive (fun c' hc' => hmemC c' (List.mem_cons_of_mem _ hc'))
      rcases hsub with ⟨Prest, hrestEq, hrestImp⟩
      have hpi : evalExpr M γ (canonicalPropRecType.buildMinors indName γ.length (c :: rest)) =
          .prop (motiveFn xc → Prest) := by
        simp only [canonicalPropRecType.buildMinors, evalExpr]
        rw [hdomEq]
        have hstep : ∀ a : (SemVal.prop (motiveFn xc)).carrier,
            evalExpr M ((SemVal.prop (motiveFn xc)).decode a :: γ)
              (canonicalPropRecType.buildMinors indName (γ.length + 1) rest) = .prop Prest :=
          fun _ => hrestEq
        rw [semPi_eq_prop (fun a => ⟨Prest, hstep a⟩)]
        congr 1
        apply propext
        constructor
        · intro h hmc
          have h1 := h ⟨hmc⟩
          rw [hstep ⟨hmc⟩] at h1
          exact h1
        · intro h a
          rw [hstep a]
          exact h a.down
      refine ⟨motiveFn xc → Prest, hpi, ?_⟩
      intro hallOut hmc
      apply hrestImp
      intro x hnotRest
      by_cases hxeq : M c = (M indName).decode x
      · rw [hxc] at hxeq
        have heq := isSemType_decode_injective hIndType hxeq
        rw [← heq]
        exact hmc
      · apply hallOut x
        intro c' hc'
        cases hc' with
        | head => exact hxeq
        | tail _ hr => exact hnotRest c' hr
  have hmotiveApp : ∀ (f : (semPi (M indName) (fun _ => .propSort)).carrier)
      (x : (M indName).carrier),
      ∃ P : Prop, semApp ((semPi (M indName) (fun _ => .propSort)).decode f)
        ((M indName).decode x) = .prop P := by
    intro f x
    unfold semPi at f ⊢
    by_cases hall : ∀ _ : (M indName).carrier, ∃ P : Prop, SemVal.propSort = .prop P
    · rcases hall x with ⟨P, hP⟩
      cases hP
    · have hEq : (letI := Classical.propDecidable;
          if ∀ _ : (M indName).carrier, ∃ P : Prop, SemVal.propSort = .prop P then
            SemVal.prop (∀ _ : (M indName).carrier, semAsProp .propSort)
          else
            SemVal.ty ((_ : (M indName).carrier) → SemVal.propSort.carrier)
              (fun g => semLam (M indName) (fun y => SemVal.propSort.decode (g y)))) =
          SemVal.ty ((_ : (M indName).carrier) → Prop)
            (fun g => semLam (M indName) (fun y => .prop (g y))) := by
        split
        · exact absurd (by assumption) hall
        · rfl
      have hdecEq : ∀ (T₁ T₂ : SemVal) (h : T₁ = T₂) (u : T₁.carrier),
          T₁.decode u = T₂.decode (h ▸ u) := by
        intro T₁ T₂ h u; subst h; rfl
      rw [hdecEq _ _ hEq f]
      have hdecSimple : (SemVal.ty ((_ : (M indName).carrier) → Prop)
          (fun g => semLam (M indName) (fun y => .prop (g y)))).decode (hEq ▸ f) =
          semLam (M indName) (fun y => .prop ((hEq ▸ f) y)) := rfl
      rw [hdecSimple, semApp_semLam hIndType]
      exact ⟨(hEq ▸ f) x, rfl⟩
  have houterAll : ∀ (a : (semPi (M indName) (fun _ => .propSort)).carrier),
      ∃ P : Prop,
        evalExpr M [(semPi (M indName) (fun _ => .propSort)).decode a]
          (canonicalPropRecType.buildMinors indName 1 ctors) = .prop P ∧ P := by
    intro a
    let motiveV := (semPi (M indName) (fun _ => .propSort)).decode a
    let motiveFn : (M indName).carrier → Prop :=
      fun x => semAsProp (semApp motiveV ((M indName).decode x))
    have hmEq : ∀ x : (M indName).carrier,
        semApp motiveV ((M indName).decode x) = .prop (motiveFn x) := by
      intro x
      rcases hmotiveApp a x with ⟨P, hP⟩
      simp only [motiveFn, motiveV]
      rw [hP]
      rfl
    rcases hMinorWalk ctors [motiveV] motiveV motiveFn (by simp) rfl hmEq hCtorsInImg with ⟨P, hPeq, hPimp⟩
    refine ⟨P, hPeq, ?_⟩
    apply hPimp
    intro x hnotAny
    rcases hCover x with ⟨c, hc, hce⟩
    exact absurd hce (hnotAny c hc)
  have houterPi :
      evalExpr M [] (canonicalPropRecType indName ctors) =
      .prop (∀ a : (semPi (M indName) (fun _ => .propSort)).carrier,
        semAsProp (evalExpr M [(semPi (M indName) (fun _ => .propSort)).decode a]
          (canonicalPropRecType.buildMinors indName 1 ctors))) := by
    unfold canonicalPropRecType
    change semPi (semPi (M indName) (fun _ => .propSort))
        (fun a => evalExpr M [(semPi (M indName) (fun _ => .propSort)).decode a]
          (canonicalPropRecType.buildMinors indName 1 ctors)) = _
    exact semPi_eq_prop (fun a => let ⟨P, h1, _⟩ := houterAll a; ⟨P, h1⟩)
  rw [houterPi]
  refine ⟨rfl, ?_⟩
  intro a
  rcases houterAll a with ⟨P, hPeq, hP⟩
  rw [hPeq]
  exact hP

/-- Helper: `isCanonicalQuotDecl` types are inhabited in any sound environment `M`. -/
theorem isCanonicalQuotDecl_inhabits {env : KernelEnv} {M : SymName → SemVal}
    (henv : EnvSound env M) {ci : ConstantRecord}
    (hq : isCanonicalQuotDecl env ci = true) :
    ∃ v : SemVal, Inhabits v (evalExpr M [] ci.type) := by
  unfold isCanonicalQuotDecl at hq
  dsimp only at hq
  split at hq
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    rw [hq.2]
    let natRelTy := ExprSkeleton.arrow (.const SymName.natName)
      (ExprSkeleton.arrow (.const SymName.natName) (.sort 0))
    refine ⟨semLam (evalExpr M [] natRelTy) (fun _ => .prop True), ?_⟩
    have hpi : evalExpr M [] (ExprSkeleton.arrow natRelTy (.sort 0)) =
        semPi (evalExpr M [] natRelTy) (fun _ => .propSort) := rfl
    rw [hpi]
    exact semLam_inhabits_semPi (fun _ => trivial) (fun _ => ⟨True, rfl⟩)
  · split at hq
    · simp only [Bool.and_eq_true, beq_iff_eq] at hq
      rw [hq.2]
      refine ⟨.prf, ?_⟩
      have hpi : evalExpr M [] (ExprSkeleton.arrow (.const SymName.natName) (.const SymName.trueName)) =
          semPi (M SymName.natName) (fun _ => .prop True) := by
        simp only [ExprSkeleton.arrow, evalExpr, ExprSkeleton.liftBVar, henv.true_interp]
      rw [hpi, semPi_eq_prop (fun _ => ⟨True, rfl⟩)]
      exact ⟨rfl, fun _ => trivial⟩
    · split at hq
      · simp only [Bool.and_eq_true, beq_iff_eq] at hq
        rw [hq.2]
        refine ⟨.prf, ?_⟩
        have hpi : evalExpr M [] (ExprSkeleton.arrow (.const SymName.trueName) (.const SymName.trueName)) =
            semPi (.prop True) (fun _ => .prop True) := by
          simp only [ExprSkeleton.arrow, evalExpr, ExprSkeleton.liftBVar]
          rw [henv.true_interp]
        rw [hpi, semPi_eq_prop (fun _ => ⟨True, rfl⟩)]
        exact ⟨rfl, fun _ => trivial⟩
      · simp at hq

/-- Helper: extending a sound `KernelEnv` with a fresh constant preserves `EnvSound`. -/
theorem envSound_insert {env : KernelEnv} {M : SymName → SemVal} (henv : EnvSound env M)
    {ci : ConstantRecord} {newVal : SemVal}
    (hfresh : env.contains ci.name = false)
    (hclosed : ExprSkeleton.hasOpenVars ci.type = false)
    (hdeps : ∀ c ∈ ci.type.usedConstants, env.contains c = true)
    (hinh : Inhabits newVal (evalExpr M [] ci.type))
    (hdefn : ∀ v, ci.kind = .defnDecl → ci.value? = some v →
      ExprSkeleton.hasOpenVars v = false ∧
      (∀ c ∈ v.usedConstants, env.contains c = true) ∧
      newVal = evalExpr M [] v)
    (hind : ∀ ctors, ci.kind = .inductDecl ctors →
      ctors.Nodup ∧
      (ci.type = .sort 0 → newVal = .prop (!ctors.isEmpty)) ∧
      (ci.type = .sort 1 → isBuiltinCarrierName ci.name = false →
        newVal = .ty (Fin ctors.length) (fun i => .base ci.name i.val)))
    (hctor : ∀ p indCi ctors, ci.kind = .ctorDecl p → ci.type = .const p →
      env.lookup p = some indCi → indCi.kind = .inductDecl ctors →
      (indCi.type = .sort 0 → newVal = .prf) ∧
      (indCi.type = .sort 1 → isBuiltinCarrierName p = false →
        ∀ (i : Fin ctors.length), ctors[i.val]? = some ci.name → newVal = .base p i.val))
    (hnoNewProj : ∀ structName idx fTy,
      lookupStructFieldType? (env.insert ci.name ci) structName idx = some fTy →
      lookupStructFieldType? env structName idx = some fTy ∧
      structName ≠ ci.name ∧
      (∀ c ∈ fTy.usedConstants, env.contains c = true)) :
    EnvSound (env.insert ci.name ci) (fun n => if n == ci.name then newVal else M n) := by
  have hneOfCont : ∀ c, env.contains c = true → c ≠ ci.name := by
    intro c hc heq
    subst heq
    rw [hfresh] at hc
    cases hc
  have hM'Eq : ∀ c, env.contains c = true →
      (if c == ci.name then newVal else M c) = M c := by
    intro c hc
    have hne := hneOfCont c hc
    simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
  have hcontMono : ∀ c, env.contains c = true → (env.insert ci.name ci).contains c = true := by
    intro c hc
    have hne := hneOfCont c hc
    simp only [KernelEnv.contains, KernelEnv.lookup_insert_ne env ci.name c ci hne.symm]
    exact hc
  have hEvalOld : ∀ e, (∀ c ∈ e.usedConstants, env.contains c = true) →
      evalExpr (fun n => if n == ci.name then newVal else M n) [] e = evalExpr M [] e :=
    fun e he => evalExpr_eq_of_agree e (fun c hc => hM'Eq c (he c hc)) []
  refine {
    has_false := hcontMono _ henv.has_false
    has_true := hcontMono _ henv.has_true
    has_nat := hcontMono _ henv.has_nat
    has_string := hcontMono _ henv.has_string
    false_interp := by rw [hM'Eq _ henv.has_false]; exact henv.false_interp
    true_interp := by rw [hM'Eq _ henv.has_true]; exact henv.true_interp
    nat_interp := by rw [hM'Eq _ henv.has_nat]; exact henv.nat_interp
    string_interp := by rw [hM'Eq _ henv.has_string]; exact henv.string_interp
    const_sound := by
      intro n cj hlu
      by_cases hn : ci.name = n
      · subst hn
        rw [KernelEnv.lookup_insert_self] at hlu
        injection hlu with hcj; subst hcj
        refine ⟨rfl, hclosed, fun c hc => hcontMono c (hdeps c hc), ?_⟩
        rw [hEvalOld ci.type hdeps]
        simp only [BEq.rfl, ↓reduceIte]
        exact hinh
      · rw [KernelEnv.lookup_insert_ne _ _ _ _ hn] at hlu
        have ⟨hnEq, hcl, hd, hi⟩ := henv.const_sound n cj hlu
        refine ⟨hnEq, hcl, fun c hc => hcontMono c (hd c hc), ?_⟩
        rw [hEvalOld cj.type hd, ← hnEq]
        have hcontN : env.contains n = true := by simp [KernelEnv.contains, hlu]
        rw [hM'Eq n hcontN, hnEq]
        exact hi
    defn_sound := by
      intro n cj v hlu hk hv
      by_cases hn : ci.name = n
      · subst hn
        rw [KernelEnv.lookup_insert_self] at hlu
        injection hlu with hcj; subst hcj
        have ⟨hvcl, hvd, hveq⟩ := hdefn v hk hv
        refine ⟨hvcl, fun c hc => hcontMono c (hvd c hc), ?_⟩
        rw [hEvalOld v hvd]
        simp only [BEq.rfl, ↓reduceIte]
        exact hveq
      · rw [KernelEnv.lookup_insert_ne _ _ _ _ hn] at hlu
        have ⟨hnEq, _, _, _⟩ := henv.const_sound n cj hlu
        have ⟨hvcl, hvd, hveq⟩ := henv.defn_sound n cj v hlu hk hv
        refine ⟨hvcl, fun c hc => hcontMono c (hvd c hc), ?_⟩
        rw [hEvalOld v hvd, ← hnEq]
        have hcontN : env.contains n = true := by simp [KernelEnv.contains, hlu]
        rw [hM'Eq n hcontN, hnEq]
        exact hveq
    induct_sound := by
      intro n cj ctors hlu hk
      by_cases hn : ci.name = n
      · subst hn
        rw [KernelEnv.lookup_insert_self] at hlu
        injection hlu with hcj; subst hcj
        simp only [BEq.rfl, ↓reduceIte]
        exact hind ctors hk
      · rw [KernelEnv.lookup_insert_ne _ _ _ _ hn] at hlu
        have hcontN : env.contains n = true := by simp [KernelEnv.contains, hlu]
        rw [hM'Eq n hcontN]
        exact henv.induct_sound n cj ctors hlu hk
    ctor_sound := by
      intro n cj p indCi ctors hlu hk hty hluP hkindP
      by_cases hn : ci.name = n
      · subst hn
        rw [KernelEnv.lookup_insert_self] at hlu
        injection hlu with hcj; subst hcj
        by_cases hp : ci.name = p
        · subst hp
          rw [KernelEnv.lookup_insert_self] at hluP
          injection hluP with hciEq; subst hciEq
          rw [hk] at hkindP; cases hkindP
        · rw [KernelEnv.lookup_insert_ne _ _ _ _ hp] at hluP
          simp only [BEq.rfl, ↓reduceIte]
          exact hctor p indCi ctors hk hty hluP hkindP
      · rw [KernelEnv.lookup_insert_ne _ _ _ _ hn] at hlu
        have hcontN : env.contains n = true := by simp [KernelEnv.contains, hlu]
        by_cases hp : ci.name = p
        · subst hp
          have ⟨_, _, hdepsCj, _⟩ := henv.const_sound n cj hlu
          have hpin : ci.name ∈ cj.type.usedConstants := by rw [hty]; simp [ExprSkeleton.usedConstants]
          have hpcont := hdepsCj ci.name hpin
          rw [hfresh] at hpcont; cases hpcont
        · rw [KernelEnv.lookup_insert_ne _ _ _ _ hp] at hluP
          rw [hM'Eq n hcontN]
          exact henv.ctor_sound n cj p indCi ctors hlu hk hty hluP hkindP
    proj_sound := by
      intro structName idx fTy v hfield hv
      rcases hnoNewProj structName idx fTy hfield with ⟨hfieldOld, _, hfDeps⟩
      have hScont : env.contains structName = true := by
        unfold lookupStructFieldType? at hfieldOld
        cases hluS : env.lookup structName with
        | none => simp [hluS] at hfieldOld
        | some _ => simp [KernelEnv.contains, hluS]
      rw [hM'Eq structName hScont] at hv
      rw [hEvalOld fTy hfDeps]
      exact henv.proj_sound structName idx fTy v hfieldOld hv
  }

/-- Helper: every constant in a field extracted by `lookupStructFieldType?` is in `env` when `EnvSound` holds. -/
theorem structFieldTypes?_usedConstants (structName : SymName) (ty : ExprSkeleton) :
    ∀ {fields : List ExprSkeleton},
      structFieldTypes? structName ty = some fields →
      ∀ f ∈ fields, ∀ c ∈ f.usedConstants, c ∈ ty.usedConstants := by
  induction ty with
  | const n =>
    intro fields h f hf
    simp only [structFieldTypes?] at h
    split at h <;> simp at h
    subst h; cases hf
  | forallE dom body _ ihb =>
    intro fields h f hf c hc
    simp only [structFieldTypes?] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · cases hsub : structFieldTypes? structName body with
        | none => simp [hsub] at h
        | some rest =>
          simp only [hsub, Option.some.injEq] at h
          subst h
          cases hf with
          | head => simp [ExprSkeleton.usedConstants, hc]
          | tail _ hmem =>
            simp only [ExprSkeleton.usedConstants, List.mem_append]
            exact Or.inr (ihb hsub f hmem c hc)
  | sort _ | app _ _ | lam _ _ | bvar _ | fvar _ | mvar _ | natLit _ | strLit _ | proj _ _ _ =>
    intro fields h; simp [structFieldTypes?] at h

/--
Core Kernel Soundness Preservation Theorem:
Every declaration accepted by `kernelCheckDecl` with `allowAxiom = false` extends any sound
semantic model `M` of `env` to a sound semantic model `M'` of `env'`.
-/
theorem kernelCheckDecl_preserves_sound {env env' : KernelEnv} {M : SymName → SemVal}
    (henv : EnvSound env M) (fuel : Nat) (ci : ConstantRecord)
    (hcheck : kernelCheckDecl env fuel false ci = .ok env') :
    ∃ M' : SymName → SemVal, EnvSound env' M' := by
  unfold kernelCheckDecl at hcheck
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hcheck
  split at hcheck; · cases hcheck
  split at hcheck; · cases hcheck
  rename_i hnotCont
  have hfresh : env.contains ci.name = false := by
    cases h : env.contains ci.name
    · rfl
    · exact absurd h hnotCont
  split at hcheck; · cases hcheck
  split at hcheck; · cases hcheck
  rename_i hnotOpen
  have hclosed : ExprSkeleton.hasOpenVars ci.type = false := by
    cases h : ExprSkeleton.hasOpenVars ci.type
    · rfl
    · exact absurd h hnotOpen
  cases htyInf : inferType env fuel [] ci.type with
  | error _ => simp [htyInf] at hcheck
  | ok tySort =>
    rw [htyInf] at hcheck; dsimp only at hcheck
    have hdeps : ∀ c ∈ ci.type.usedConstants, env.contains c = true :=
      inferType_usedConstants_in_env fuel [] ci.type tySort htyInf
    cases htyW : whnf env fuel [] tySort with
    | sort u =>
      rw [htyW] at hcheck; dsimp only at hcheck
      split at hcheck; · cases hcheck
      have hprojKeep : ∀ (hnotInd1 : ∀ c, ci.kind = .inductDecl [c] → c ≠ ci.name ∧ env.lookup c = none)
          (hnotCtorFields : ∀ p, ci.kind = .ctorDecl p → ci.type = .const p ∨
            (∀ indCi, env.lookup p = some indCi → indCi.kind ≠ .inductDecl [ci.name])),
          ∀ structName idx fTy,
            lookupStructFieldType? (env.insert ci.name ci) structName idx = some fTy →
            lookupStructFieldType? env structName idx = some fTy ∧
            structName ≠ ci.name ∧
            (∀ c ∈ fTy.usedConstants, env.contains c = true) := by
        intro hnotInd1 hnotCtorFields structName idx fTy hfield
        unfold lookupStructFieldType? at hfield ⊢
        by_cases hs : ci.name = structName
        · subst hs
          rw [KernelEnv.lookup_insert_self] at hfield
          dsimp only at hfield
          cases hk : ci.kind with
          | inductDecl ctors =>
            rw [hk] at hfield
            cases ctors with
            | nil => simp at hfield
            | cons c0 rest =>
              cases rest with
              | cons _ _ => simp at hfield
              | nil =>
                dsimp only at hfield
                have ⟨hne0, hlu0⟩ := hnotInd1 c0 hk
                rw [KernelEnv.lookup_insert_ne _ _ _ _ (Ne.symm hne0), hlu0] at hfield
                simp at hfield
          | axiomDecl | defnDecl | thmDecl | opaqueDecl | quotDecl | ctorDecl _ | recDecl _ =>
            rw [hk] at hfield; simp at hfield
        · rw [KernelEnv.lookup_insert_ne _ _ _ _ hs] at hfield
          cases hluS : env.lookup structName with
          | none => rw [hluS] at hfield; simp at hfield
          | some indCi =>
            rw [hluS] at hfield; dsimp only at hfield
            cases hindK : indCi.kind with
            | inductDecl ctors =>
              rw [hindK] at hfield
              cases ctors with
              | nil => simp at hfield
              | cons c0 rest =>
                cases rest with
                | cons _ _ => simp at hfield
                | nil =>
                  dsimp only at hfield
                  by_cases hc0 : ci.name = c0
                  · subst hc0
                    rw [KernelEnv.lookup_insert_self] at hfield
                    dsimp only at hfield
                    split at hfield
                    · rename_i hck
                      simp only [beq_iff_eq] at hck
                      rcases hnotCtorFields structName hck with hconst | hneInd
                      · rw [hconst] at hfield
                        simp [structFieldTypes?] at hfield
                      · exact absurd hindK (hneInd indCi hluS)
                    · simp at hfield
                  · rw [KernelEnv.lookup_insert_ne _ _ _ _ hc0] at hfield
                    refine ⟨by dsimp only; rw [hindK]; exact hfield, Ne.symm hs, ?_⟩
                    cases hluC : env.lookup c0 with
                    | none => rw [hluC] at hfield; simp at hfield
                    | some ctorCi =>
                      rw [hluC] at hfield; dsimp only at hfield
                      split at hfield
                      · cases hsf : structFieldTypes? structName ctorCi.type with
                        | none => rw [hsf] at hfield; simp at hfield
                        | some fs =>
                          rw [hsf] at hfield; dsimp only at hfield
                          have ⟨_, _, hctorDeps, _⟩ := henv.const_sound c0 ctorCi hluC
                          exact fun c hc => hctorDeps c
                            (structFieldTypes?_usedConstants structName ctorCi.type hsf fTy
                              (List.mem_of_getElem? hfield) c hc)
                      · simp at hfield
            | axiomDecl | defnDecl | thmDecl | opaqueDecl | quotDecl | ctorDecl _ | recDecl _ =>
              rw [hindK] at hfield; simp at hfield
      cases hkind : ci.kind with
      | axiomDecl =>
        rw [hkind] at hcheck; simp at hcheck
      | defnDecl =>
        rw [hkind] at hcheck; dsimp only at hcheck
        cases hval : ci.value? with
        | none => rw [hval] at hcheck; cases hcheck
        | some val =>
          rw [hval] at hcheck; dsimp only at hcheck
          split at hcheck; · cases hcheck
          rename_i hvalNotOpen
          have hvcl : ExprSkeleton.hasOpenVars val = false := by
            cases h : ExprSkeleton.hasOpenVars val
            · rfl
            · exact absurd h hvalNotOpen
          cases hvalInf : inferType env fuel [] val with
          | error _ => rw [hvalInf] at hcheck; cases hcheck
          | ok valTy =>
            rw [hvalInf] at hcheck; dsimp only at hcheck
            split at hcheck; · cases hcheck
            rename_i hnotDeq
            have hdeq : isDefEq env fuel [] valTy ci.type = true := by
              cases h : isDefEq env fuel [] valTy ci.type
              · exact absurd (by simp [h]) hnotDeq
              · rfl
            injection hcheck with henvEq; subst henvEq
            have hvDeps := inferType_usedConstants_in_env fuel [] val valTy hvalInf
            have hvInh := (kernel_sound_at_fuel henv fuel).2.2 [] [] val valTy CtxSat.nil hvalInf
            have hvEq := (kernel_sound_at_fuel henv fuel).2.1 [] [] valTy ci.type CtxSat.nil hdeq
            rw [hvEq] at hvInh
            refine ⟨fun n => if n == ci.name then evalExpr M [] val else M n,
              envSound_insert henv hfresh hclosed hdeps hvInh
                (fun v' _ hv' => by rw [hval] at hv'; injection hv' with h; subst h; exact ⟨hvcl, hvDeps, rfl⟩)
                (fun _ hk => by rw [hkind] at hk; cases hk)
                (fun _ _ _ hk => by rw [hkind] at hk; cases hk)
                (hprojKeep (fun _ hk => by rw [hkind] at hk; cases hk) (fun _ hk => by rw [hkind] at hk; cases hk))⟩
      | thmDecl =>
        rw [hkind] at hcheck; dsimp only at hcheck
        split at hcheck; · cases hcheck
        cases hval : ci.value? with
        | none => rw [hval] at hcheck; cases hcheck
        | some val =>
          rw [hval] at hcheck; dsimp only at hcheck
          split at hcheck; · cases hcheck
          cases hvalInf : inferType env fuel [] val with
          | error _ => rw [hvalInf] at hcheck; cases hcheck
          | ok valTy =>
            rw [hvalInf] at hcheck; dsimp only at hcheck
            split at hcheck; · cases hcheck
            rename_i hnotDeq
            have hdeq : isDefEq env fuel [] valTy ci.type = true := by
              cases h : isDefEq env fuel [] valTy ci.type
              · exact absurd (by simp [h]) hnotDeq
              · rfl
            injection hcheck with henvEq; subst henvEq
            have hvInh := (kernel_sound_at_fuel henv fuel).2.2 [] [] val valTy CtxSat.nil hvalInf
            have hvEq := (kernel_sound_at_fuel henv fuel).2.1 [] [] valTy ci.type CtxSat.nil hdeq
            rw [hvEq] at hvInh
            refine ⟨fun n => if n == ci.name then evalExpr M [] val else M n,
              envSound_insert henv hfresh hclosed hdeps hvInh
                (fun _ hk => by rw [hkind] at hk; cases hk)
                (fun _ hk => by rw [hkind] at hk; cases hk)
                (fun _ _ _ hk => by rw [hkind] at hk; cases hk)
                (hprojKeep (fun _ hk => by rw [hkind] at hk; cases hk) (fun _ hk => by rw [hkind] at hk; cases hk))⟩
      | opaqueDecl =>
        rw [hkind] at hcheck; dsimp only at hcheck
        cases hval : ci.value? with
        | none => rw [hval] at hcheck; cases hcheck
        | some val =>
          rw [hval] at hcheck; dsimp only at hcheck
          split at hcheck; · cases hcheck
          cases hvalInf : inferType env fuel [] val with
          | error _ => rw [hvalInf] at hcheck; cases hcheck
          | ok valTy =>
            rw [hvalInf] at hcheck; dsimp only at hcheck
            split at hcheck; · cases hcheck
            rename_i hnotDeq
            have hdeq : isDefEq env fuel [] valTy ci.type = true := by
              cases h : isDefEq env fuel [] valTy ci.type
              · exact absurd (by simp [h]) hnotDeq
              · rfl
            injection hcheck with henvEq; subst henvEq
            have hvInh := (kernel_sound_at_fuel henv fuel).2.2 [] [] val valTy CtxSat.nil hvalInf
            have hvEq := (kernel_sound_at_fuel henv fuel).2.1 [] [] valTy ci.type CtxSat.nil hdeq
            rw [hvEq] at hvInh
            refine ⟨fun n => if n == ci.name then evalExpr M [] val else M n,
              envSound_insert henv hfresh hclosed hdeps hvInh
                (fun _ hk => by rw [hkind] at hk; cases hk)
                (fun _ hk => by rw [hkind] at hk; cases hk)
                (fun _ _ _ hk => by rw [hkind] at hk; cases hk)
                (hprojKeep (fun _ hk => by rw [hkind] at hk; cases hk) (fun _ hk => by rw [hkind] at hk; cases hk))⟩
      | quotDecl =>
        rw [hkind] at hcheck; dsimp only at hcheck
        split at hcheck; · cases hcheck
        rename_i hnotQ
        have hq : isCanonicalQuotDecl env ci = true := by
          cases h : isCanonicalQuotDecl env ci
          · exact absurd (by simp [h]) hnotQ
          · rfl
        injection hcheck with henvEq; subst henvEq
        rcases isCanonicalQuotDecl_inhabits henv hq with ⟨qVal, hqInh⟩
        refine ⟨fun n => if n == ci.name then qVal else M n,
          envSound_insert henv hfresh hclosed hdeps hqInh
            (fun _ hk => by rw [hkind] at hk; cases hk)
            (fun _ hk => by rw [hkind] at hk; cases hk)
            (fun _ _ _ hk => by rw [hkind] at hk; cases hk)
            (hprojKeep (fun _ hk => by rw [hkind] at hk; cases hk) (fun _ hk => by rw [hkind] at hk; cases hk))⟩
      | inductDecl ctors =>
        rw [hkind] at hcheck; dsimp only at hcheck
        split at hcheck; · cases hcheck
        split at hcheck; · cases hcheck
        rename_i hnotArity
        have harity : isValidInductArity env fuel ci.type = true := by
          cases h : isValidInductArity env fuel ci.type
          · exact absurd (by simp [h]) hnotArity
          · rfl
        split at hcheck; · cases hcheck
        split at hcheck; · cases hcheck
        rename_i hnotDup
        have hctorsClean : (hasDuplicates ctors || ctors.contains ci.name || ctors.any env.contains) = false := by
          cases h : (hasDuplicates ctors || ctors.contains ci.name || ctors.any env.contains)
          · rfl
          · exact absurd h hnotDup
        simp only [Bool.or_eq_false_iff] at hctorsClean
        injection hcheck with henvEq; subst henvEq
        let indVal := interpInductArity M ci.name ctors ci.type
        have hindInh := interpInductArity_inhabits henv fuel ci.name ctors harity
        refine ⟨fun n => if n == ci.name then indVal else M n,
          envSound_insert henv hfresh hclosed hdeps hindInh
            (fun _ hk => by rw [hkind] at hk; cases hk)
            (fun ctors' hk => by
              rw [hkind] at hk; injection hk with hceq; subst hceq
              refine ⟨(hasDuplicates_eq_false_iff_nodup ctors).mp hctorsClean.1.1, ?_, ?_⟩
              · intro hty0; simp [indVal, hty0, interpInductArity]
              · intro hty1 _; simp [indVal, hty1, interpInductArity])
            (fun _ _ _ hk => by rw [hkind] at hk; cases hk)
            (hprojKeep
              (fun c0 hk => by
                rw [hkind] at hk; injection hk with hceq; subst hceq
                have hne : c0 ≠ ci.name := by
                  intro heq; subst heq
                  have := hctorsClean.1.2
                  simp at this
                have hnone : env.lookup c0 = none := by
                  have := hctorsClean.2
                  simp only [List.any_cons, List.any_nil, Bool.or_false, KernelEnv.contains,
                    Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at this
                  exact this
                exact ⟨hne, hnone⟩)
              (fun _ hk => by rw [hkind] at hk; cases hk))⟩
      | ctorDecl inductParent =>
        rw [hkind] at hcheck; dsimp only at hcheck
        cases hluP : env.lookup inductParent with
        | none => rw [hluP] at hcheck; cases hcheck
        | some indCi =>
          rw [hluP] at hcheck; dsimp only at hcheck
          cases hindK : indCi.kind with
          | inductDecl ctors =>
            rw [hindK] at hcheck; dsimp only at hcheck
            split at hcheck; · cases hcheck
            rename_i hnotMem
            have hmemC : ci.name ∈ ctors := by
              by_cases hm : ci.name ∈ ctors
              · exact hm
              · exfalso; apply hnotMem; simp [hm]
            split at hcheck; · cases hcheck
            rename_i hnotSort01
            have hsort01 : indCi.type = .sort 0 ∨ indCi.type = .sort 1 := by
              cases h : (indCi.type == .sort 0 || indCi.type == .sort 1)
              · exfalso; apply hnotSort01; simp [h]
              · simp only [Bool.or_eq_true, beq_iff_eq] at h; exact h
            split at hcheck; · cases hcheck
            rename_i hnotLen1
            split at hcheck; · cases hcheck
            rename_i hnotCtorTy
            have hctorTy : isValidCtorType env fuel inductParent ci.type = true := by
              cases h : isValidCtorType env fuel inductParent ci.type
              · exfalso; apply hnotCtorTy; simp [h]
              · rfl
            injection hcheck with henvEq; subst henvEq
            have ⟨hpEq, _, _, hpInh⟩ := henv.const_sound inductParent indCi hluP
            rw [← hpEq] at hpInh
            have hParentSort : Inhabits (M inductParent) .sort1 := by
              rcases hsort01 with h0 | h1
              · rw [h0] at hpInh
                simp only [evalExpr, Inhabits] at hpInh
                exact Or.inr (Or.inl hpInh)
              · rw [h1] at hpInh; exact hpInh
            rcases listIndexOf?_isSome_of_mem hmemC with ⟨idx, hidx⟩
            have hidxSpec := listIndexOf?_spec ci.name ctors hidx
            have hidxLt : idx < ctors.length := by
              cases hlt : decide (idx < ctors.length)
              · have hge : ctors.length ≤ idx := Nat.le_of_not_lt (of_decide_eq_false hlt)
                rw [List.getElem?_eq_none hge] at hidxSpec; cases hidxSpec
              · exact of_decide_eq_true hlt
            let leafVal : SemVal :=
              if indCi.type == .sort 0 then .prf
              else if inductParent == SymName.natName then .base SymName.natName 0
              else if inductParent == SymName.stringName then .strVal ""
              else .base inductParent idx
            have hleafInh : Inhabits leafVal (M inductParent) := by
              rcases henv.induct_sound inductParent indCi ctors hluP hindK with ⟨_, hs0, hs1⟩
              rcases hsort01 with h0 | h1
              · have hne : ((!ctors.isEmpty) = true) := by
                  cases ctors with
                  | nil => cases hmemC
                  | cons _ _ => rfl
                rw [hs0 h0]
                simp only [leafVal, h0, BEq.rfl, ↓reduceIte, Inhabits]
                exact ⟨trivial, hne⟩
              · have hne0 : (indCi.type == .sort 0) = false := by rw [h1]; rfl
                by_cases hnat : inductParent = SymName.natName
                · subst hnat
                  rw [henv.nat_interp]
                  simp only [leafVal, hne0, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Inhabits]
                  exact ⟨0, rfl⟩
                · by_cases hstr : inductParent = SymName.stringName
                  · subst hstr
                    rw [henv.string_interp]
                    have hneNat : (SymName.stringName == SymName.natName) = false := by decide
                    simp only [leafVal, hne0, hneNat, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Inhabits]
                    exact ⟨"", rfl⟩
                  · have hnb : isBuiltinCarrierName inductParent = false := by
                      simp [isBuiltinCarrierName, beq_false_of_ne hnat, beq_false_of_ne hstr]
                    rw [hs1 h1 hnb]
                    simp only [leafVal, hne0, beq_false_of_ne hnat, beq_false_of_ne hstr,
                      Bool.false_eq_true, ↓reduceIte, Inhabits]
                    exact ⟨⟨idx, hidxLt⟩, rfl⟩
            let ctorVal := interpCtorType M leafVal ci.type
            have hctorInh := interpCtorType_inhabits henv fuel inductParent leafVal hParentSort hleafInh ci.type hctorTy
            have hctorsNodup : ctors.Nodup :=
              (henv.induct_sound inductParent indCi ctors hluP hindK).1
            refine ⟨fun n => if n == ci.name then ctorVal else M n,
              envSound_insert henv hfresh hclosed hdeps hctorInh
                (fun _ hk => by rw [hkind] at hk; cases hk)
                (fun _ hk => by rw [hkind] at hk; cases hk)
                (fun p' indCi' ctors' hk htyP hluP' hindK' => by
                  rw [hkind] at hk; injection hk with hpeq; subst hpeq
                  rw [hluP] at hluP'; injection hluP' with hieq; subst hieq
                  rw [hindK] at hindK'; injection hindK' with hceq; subst hceq
                  constructor
                  · intro h0
                    simp only [ctorVal, htyP, interpCtorType, leafVal, h0, BEq.rfl, ↓reduceIte]
                  · intro h1 hnb i hi
                    have hne0 : (indCi.type == .sort 0) = false := by rw [h1]; rfl
                    simp only [isBuiltinCarrierName, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnb
                    have huniq : idx = i.val := by
                      have hget1 : ctors[idx] = ci.name := by
                        rw [List.getElem?_eq_getElem hidxLt] at hidxSpec
                        injection hidxSpec
                      have hget2 : ctors[i.val] = ci.name := by
                        rw [List.getElem?_eq_getElem i.isLt] at hi
                        injection hi
                      exact nodup_getElem_inj hctorsNodup hidxLt i.isLt (hget1.trans hget2.symm)
                    simp only [ctorVal, htyP, interpCtorType, leafVal, hne0,
                      beq_false_of_ne hnb.1, beq_false_of_ne hnb.2, Bool.false_eq_true, ↓reduceIte, huniq])
                (hprojKeep
                  (fun _ hk => by rw [hkind] at hk; cases hk)
                  (fun p' hk => by
                    rw [hkind] at hk; injection hk with hpeq; subst hpeq
                    by_cases hct : ci.type = .const inductParent
                    · exact Or.inl hct
                    · right
                      intro indCi' hlu' hk'
                      rw [hluP] at hlu'; injection hlu' with hieq; subst hieq
                      rw [hindK] at hk'; injection hk' with hceq; subst hceq
                      exact hnotLen1 (by simp [hct])))⟩
          | axiomDecl | defnDecl | thmDecl | opaqueDecl | quotDecl | ctorDecl _ | recDecl _ =>
            rw [hindK] at hcheck; cases hcheck
      | recDecl rules =>
        rw [hkind] at hcheck; dsimp only at hcheck
        split at hcheck; · cases hcheck
        rename_i hnotRec
        have hrec : isCanonicalRecDecl env ci rules = true := by
          cases h : isCanonicalRecDecl env ci rules
          · exact absurd (by simp [h]) hnotRec
          · rfl
        injection hcheck with henvEq; subst henvEq
        unfold isCanonicalRecDecl at hrec
        cases hall : ci.all with
        | nil => rw [hall] at hrec; simp at hrec
        | cons indName rest =>
          cases rest with
          | cons _ _ => rw [hall] at hrec; simp at hrec
          | nil =>
            rw [hall] at hrec; dsimp only at hrec
            cases hluI : env.lookup indName with
            | none => rw [hluI] at hrec; simp at hrec
            | some indCi =>
              rw [hluI] at hrec; dsimp only at hrec
              cases hindK : indCi.kind with
              | inductDecl ctors =>
                rw [hindK] at hrec; dsimp only at hrec
                simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hrec
                rcases hrec with ⟨⟨⟨_, hnbF⟩, _⟩, htypeOk⟩
                have hrecInh : Inhabits .prf (evalExpr M [] ci.type) := by
                  rcases henv.induct_sound indName indCi ctors hluI hindK with ⟨_, hs0, hs1⟩
                  rcases htypeOk with ⟨⟨hcp, h01⟩, htyEq⟩ | ⟨⟨hempty, h01⟩, htyEq⟩
                  · rw [htyEq]
                    have hcpAll : ∀ c ∈ ctors, ∃ cCi, env.lookup c = some cCi ∧
                        cCi.kind = .ctorDecl indName ∧ cCi.type = .const indName := by
                      intro c hc
                      have hcOk := (List.all_eq_true.mp hcp) c hc
                      cases hluC : env.lookup c with
                      | none => simp [hluC] at hcOk
                      | some cCi =>
                        simp only [hluC, Bool.and_eq_true, beq_iff_eq] at hcOk
                        exact ⟨cCi, rfl, hcOk.1, hcOk.2⟩
                    rcases h01 with h0 | h1
                    · have hIndM := hs0 h0
                      have hIndType : IsSemType (M indName) := by rw [hIndM]; trivial
                      have hCtorsImg : ∀ c ∈ ctors, ∃ x : (M indName).carrier, M c = (M indName).decode x := by
                        intro c hc
                        rcases hcpAll c hc with ⟨cCi, hluC, hck, hct⟩
                        have hMc := (henv.ctor_sound c cCi indName indCi ctors hluC hck hct hluI hindK).1 h0
                        have hne : ((!ctors.isEmpty) = true) := by
                          cases ctors with | nil => cases hc | cons _ _ => rfl
                        have hAux : ∀ (T : SemVal), T = .prop ((!ctors.isEmpty) = true) →
                            ∃ x : T.carrier, SemVal.prf = T.decode x := by
                          intro T hT; subst hT; exact ⟨⟨hne⟩, rfl⟩
                        rw [hMc]
                        exact hAux (M indName) hIndM
                      have hCov : ∀ x : (M indName).carrier, ∃ c ∈ ctors, M c = (M indName).decode x := by
                        have hAux : ∀ (T : SemVal), T = .prop ((!ctors.isEmpty) = true) →
                            ∀ x : T.carrier, ∃ c ∈ ctors, M c = T.decode x := by
                          intro T hT x; subst hT
                          cases ctors with
                          | nil => cases x.down
                          | cons c0 _ =>
                            rcases hcpAll c0 List.mem_cons_self with ⟨cCi, hluC, hck, hct⟩
                            have hMc := (henv.ctor_sound c0 cCi indName indCi _ hluC hck hct hluI hindK).1 h0
                            exact ⟨c0, List.mem_cons_self, hMc⟩
                        exact hAux (M indName) hIndM
                      exact canonicalPropRecType_inhabits hIndType hCtorsImg hCov
                    · have hIndM := hs1 h1 hnbF
                      have hIndType : IsSemType (M indName) := by
                        rw [hIndM]
                        intro i j h; injection h with _ hv; exact Fin.ext hv
                      have hCtorsImg : ∀ c ∈ ctors, ∃ x : (M indName).carrier, M c = (M indName).decode x := by
                        intro c hc
                        rcases hcpAll c hc with ⟨cCi, hluC, hck, hct⟩
                        rcases listIndexOf?_isSome_of_mem hc with ⟨idx, hidx⟩
                        have hidxSpec := listIndexOf?_spec c ctors hidx
                        have hidxLt : idx < ctors.length := by
                          cases hlt : decide (idx < ctors.length)
                          · have hge := Nat.le_of_not_lt (of_decide_eq_false hlt)
                            rw [List.getElem?_eq_none hge] at hidxSpec; cases hidxSpec
                          · exact of_decide_eq_true hlt
                        have hMc := (henv.ctor_sound c cCi indName indCi ctors hluC hck hct hluI hindK).2
                          h1 hnbF ⟨idx, hidxLt⟩ hidxSpec
                        have hAux : ∀ (T : SemVal),
                            T = .ty (Fin ctors.length) (fun i => .base indName i.val) →
                            ∃ x : T.carrier, SemVal.base indName idx = T.decode x := by
                          intro T hT; subst hT; exact ⟨⟨idx, hidxLt⟩, rfl⟩
                        rw [hMc]
                        exact hAux (M indName) hIndM
                      have hCov : ∀ x : (M indName).carrier, ∃ c ∈ ctors, M c = (M indName).decode x := by
                        have hAux : ∀ (T : SemVal),
                            T = .ty (Fin ctors.length) (fun i => .base indName i.val) →
                            ∀ x : T.carrier, ∃ c ∈ ctors, M c = T.decode x := by
                          intro T hT x; subst hT
                          have hget : ctors[x.val]? = some ctors[x.val] := List.getElem?_eq_getElem x.isLt
                          have hmem : ctors[x.val] ∈ ctors := List.getElem_mem x.isLt
                          rcases hcpAll ctors[x.val] hmem with ⟨cCi, hluC, hck, hct⟩
                          have hMc := (henv.ctor_sound ctors[x.val] cCi indName indCi ctors hluC hck hct hluI hindK).2
                            h1 hnbF x hget
                          exact ⟨ctors[x.val], hmem, hMc⟩
                        exact hAux (M indName) hIndM
                      exact canonicalPropRecType_inhabits hIndType hCtorsImg hCov
                  · rw [htyEq]
                    have hnil : ctors = [] := by
                      cases ctors with | nil => rfl | cons _ _ => simp at hempty
                    subst hnil
                    apply canonicalEmptyPropRecType_inhabits
                    rcases h01 with h0 | h1
                    · rw [hs0 h0]; intro ⟨⟨hF⟩⟩; cases hF
                    · rw [hs1 h1 hnbF]; intro ⟨x⟩; exact Nat.not_lt_zero x.val x.isLt
                refine ⟨fun n => if n == ci.name then .prf else M n,
                  envSound_insert henv hfresh hclosed hdeps hrecInh
                    (fun _ hk => by rw [hkind] at hk; cases hk)
                    (fun _ hk => by rw [hkind] at hk; cases hk)
                    (fun _ _ _ hk => by rw [hkind] at hk; cases hk)
                    (hprojKeep (fun _ hk => by rw [hkind] at hk; cases hk) (fun _ hk => by rw [hkind] at hk; cases hk))⟩
              | axiomDecl | defnDecl | thmDecl | opaqueDecl | quotDecl | ctorDecl _ | recDecl _ =>
                rw [hindK] at hrec; simp at hrec
    | const _ | app _ _ | lam _ _ | forallE _ _ | bvar _ | fvar _ | mvar _
    | natLit _ | strLit _ | proj _ _ _ =>
      rw [htyW] at hcheck; cases hcheck

/-- Clean-environment sequential kernel replay over a list of declarations. -/
def replayCleanEnv (env : KernelEnv) (fuel : Nat) (allowAxiom : Bool) :
    List ConstantRecord → Except AuditFailure KernelEnv
  | [] => .ok env
  | ci :: rest => do
    let env' ← kernelCheckDecl env fuel allowAxiom ci
    replayCleanEnv env' fuel allowAxiom rest

theorem replayCleanEnv_preserves_sound {env env' : KernelEnv} {M : SymName → SemVal}
    (henv : EnvSound env M) (fuel : Nat) (decls : List ConstantRecord)
    (hrep : replayCleanEnv env fuel false decls = .ok env') :
    ∃ M' : SymName → SemVal, EnvSound env' M' := by
  induction decls generalizing env M with
  | nil =>
    simp only [replayCleanEnv, Except.ok.injEq] at hrep
    subst hrep
    exact ⟨M, henv⟩
  | cons ci rest ih =>
    simp only [replayCleanEnv, bind, Except.bind] at hrep
    cases hstep : kernelCheckDecl env fuel false ci with
    | error _ => simp [hstep] at hrep
    | ok env1 =>
      rw [hstep] at hrep
      rcases kernelCheckDecl_preserves_sound henv fuel ci hstep with ⟨M1, henv1⟩
      exact ih henv1 hrep

/-- Every declaration added during `replayCleanEnv` is present in the output environment at its own name. -/
theorem kernelCheckDecl_env_eq {env env' : KernelEnv} {fuel : Nat} {allowAxiom : Bool}
    {ci : ConstantRecord}
    (h : kernelCheckDecl env fuel allowAxiom ci = .ok env') :
    env' = env.insert ci.name ci ∧ env.contains ci.name = false := by
  unfold kernelCheckDecl at h
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h; · cases h
  split at h; · cases h
  rename_i hnotCont
  have hfresh : env.contains ci.name = false := by
    cases hc : env.contains ci.name
    · rfl
    · exact absurd hc hnotCont
  split at h; · cases h
  split at h; · cases h
  cases hty : inferType env fuel [] ci.type with
  | error _ => rw [hty] at h; cases h
  | ok tySort =>
    rw [hty] at h; dsimp only at h
    cases htw : whnf env fuel [] tySort with
    | sort u =>
      rw [htw] at h; dsimp only at h
      split at h; · cases h
      cases hk : ci.kind with
      | axiomDecl =>
        rw [hk] at h; dsimp only at h
        split at h; · cases h
        split at h; · cases h
        injection h with heq; exact ⟨heq.symm, hfresh⟩
      | defnDecl =>
        rw [hk] at h; dsimp only at h
        cases hv : ci.value? with
        | none => rw [hv] at h; cases h
        | some val =>
          rw [hv] at h; dsimp only at h
          split at h; · cases h
          cases hvi : inferType env fuel [] val with
          | error _ => rw [hvi] at h; cases h
          | ok _ =>
            rw [hvi] at h; dsimp only at h
            split at h; · cases h
            injection h with heq; exact ⟨heq.symm, hfresh⟩
      | thmDecl =>
        rw [hk] at h; dsimp only at h
        split at h; · cases h
        cases hv : ci.value? with
        | none => rw [hv] at h; cases h
        | some val =>
          rw [hv] at h; dsimp only at h
          split at h; · cases h
          cases hvi : inferType env fuel [] val with
          | error _ => rw [hvi] at h; cases h
          | ok _ =>
            rw [hvi] at h; dsimp only at h
            split at h; · cases h
            injection h with heq; exact ⟨heq.symm, hfresh⟩
      | opaqueDecl =>
        rw [hk] at h; dsimp only at h
        cases hv : ci.value? with
        | none => rw [hv] at h; cases h
        | some val =>
          rw [hv] at h; dsimp only at h
          split at h; · cases h
          cases hvi : inferType env fuel [] val with
          | error _ => rw [hvi] at h; cases h
          | ok _ =>
            rw [hvi] at h; dsimp only at h
            split at h; · cases h
            injection h with heq; exact ⟨heq.symm, hfresh⟩
      | quotDecl =>
        rw [hk] at h; dsimp only at h
        split at h; · cases h
        injection h with heq; exact ⟨heq.symm, hfresh⟩
      | inductDecl _ =>
        rw [hk] at h; dsimp only at h
        split at h; · cases h
        split at h; · cases h
        split at h; · cases h
        split at h; · cases h
        injection h with heq; exact ⟨heq.symm, hfresh⟩
      | ctorDecl p =>
        rw [hk] at h; dsimp only at h
        cases hp : env.lookup p with
        | none => rw [hp] at h; cases h
        | some indCi =>
          rw [hp] at h; dsimp only at h
          cases hpk : indCi.kind with
          | inductDecl _ =>
            rw [hpk] at h; dsimp only at h
            split at h; · cases h
            split at h; · cases h
            split at h; · cases h
            split at h; · cases h
            injection h with heq; exact ⟨heq.symm, hfresh⟩
          | axiomDecl | defnDecl | thmDecl | opaqueDecl | quotDecl | ctorDecl _ | recDecl _ =>
            rw [hpk] at h; cases h
      | recDecl _ =>
        rw [hk] at h; dsimp only at h
        split at h; · cases h
        injection h with heq; exact ⟨heq.symm, hfresh⟩
    | const _ | app _ _ | lam _ _ | forallE _ _ | bvar _ | fvar _ | mvar _
    | natLit _ | strLit _ | proj _ _ _ =>
      rw [htw] at h; cases h

theorem replayCleanEnv_contains_decl {env env' : KernelEnv} {fuel : Nat} {allowAxiom : Bool}
    {decls : List ConstantRecord}
    (hrep : replayCleanEnv env fuel allowAxiom decls = .ok env') :
    (∀ n ci, env.lookup n = some ci → env'.lookup n = some ci) ∧
    (∀ ci ∈ decls, env'.lookup ci.name = some ci) := by
  induction decls generalizing env with
  | nil =>
    simp only [replayCleanEnv, Except.ok.injEq] at hrep
    subst hrep
    exact ⟨fun _ _ h => h, fun _ hc => by cases hc⟩
  | cons d rest ih =>
    simp only [replayCleanEnv, bind, Except.bind] at hrep
    cases hstep : kernelCheckDecl env fuel allowAxiom d with
    | error _ => simp [hstep] at hrep
    | ok env1 =>
      rw [hstep] at hrep
      have ⟨henv1, hfresh⟩ := kernelCheckDecl_env_eq hstep
      have ⟨hmono, hrest⟩ := ih hrep
      constructor
      · intro n ci hlu
        apply hmono
        rw [henv1]
        have hne : d.name ≠ n := by
          intro heq; subst heq
          simp [KernelEnv.contains, hlu] at hfresh
        rw [KernelEnv.lookup_insert_ne _ _ _ _ hne]
        exact hlu
      · intro ci hmem
        cases hmem with
        | head =>
          apply hmono
          rw [henv1, KernelEnv.lookup_insert_self]
        | tail _ htl =>
          exact hrest ci htl

/-- Core Semantic Consistency Corollary: no constant in a sound `KernelEnv` can have type `False`. -/
theorem kernelEnv_no_false {env : KernelEnv} {M : SymName → SemVal}
    (henv : EnvSound env M) :
    ∀ n ci, env.lookup n = some ci → ci.type ≠ .const SymName.falseName := by
  intro n ci hlu hty
  have ⟨_, _, _, hinh⟩ := henv.const_sound n ci hlu
  rw [hty] at hinh
  simp only [evalExpr, henv.false_interp, Inhabits] at hinh
  exact hinh.2

/-- Canonical `Init`/`Std`/`Trusted` foundation declarations for the consistent base model. -/
def baseFalseDecl : ConstantRecord := {
  name := SymName.falseName
  kind := .inductDecl []
  type := .sort 0
  all := [SymName.falseName]
  originModule := SymName.ofList ["Init", "Prelude"]
}

def baseTrueDecl : ConstantRecord := {
  name := SymName.trueName
  kind := .inductDecl [SymName.trueIntroName]
  type := .sort 0
  all := [SymName.trueName]
  originModule := SymName.ofList ["Init", "Prelude"]
}

def baseTrueIntroDecl : ConstantRecord := {
  name := SymName.trueIntroName
  kind := .ctorDecl SymName.trueName
  type := .const SymName.trueName
  originModule := SymName.ofList ["Init", "Prelude"]
}

def baseNatDecl : ConstantRecord := {
  name := SymName.natName
  kind := .inductDecl [SymName.natZeroName, SymName.natSuccName]
  type := .sort 1
  all := [SymName.natName]
  originModule := SymName.ofList ["Init", "Prelude"]
}

def baseNatZeroDecl : ConstantRecord := {
  name := SymName.natZeroName
  kind := .ctorDecl SymName.natName
  type := .const SymName.natName
  originModule := SymName.ofList ["Init", "Prelude"]
}

def baseNatSuccDecl : ConstantRecord := {
  name := SymName.natSuccName
  kind := .ctorDecl SymName.natName
  type := ExprSkeleton.arrow (.const SymName.natName) (.const SymName.natName)
  originModule := SymName.ofList ["Init", "Prelude"]
}

def baseNatAddDecl : ConstantRecord := {
  name := SymName.natAddName
  kind := .opaqueDecl
  type := ExprSkeleton.arrow (.const SymName.natName)
    (ExprSkeleton.arrow (.const SymName.natName) (.const SymName.natName))
  value? := some (.lam (.const SymName.natName) (.lam (.const SymName.natName) (.bvar 0)))
  hasValue := true
  all := [SymName.natAddName]
  originModule := SymName.ofList ["Init", "Prelude"]
}

def baseStringDecl : ConstantRecord := {
  name := SymName.stringName
  kind := .inductDecl []
  type := .sort 1
  all := [SymName.stringName]
  originModule := SymName.ofList ["Init", "Prelude"]
}

def baseEqDecl : ConstantRecord := {
  name := SymName.eqName
  kind := .inductDecl [SymName.eqReflName]
  type := ExprSkeleton.arrow (.const SymName.natName)
    (ExprSkeleton.arrow (.const SymName.natName) (.sort 0))
  all := [SymName.eqName]
  originModule := SymName.ofList ["Init", "Prelude"]
}

def baseEqReflDecl : ConstantRecord := {
  name := SymName.eqReflName
  kind := .ctorDecl SymName.eqName
  type := .forallE (.const SymName.natName) (.app (.app (.const SymName.eqName) (.bvar 0)) (.bvar 0))
  originModule := SymName.ofList ["Init", "Prelude"]
}

def basePropextDecl : ConstantRecord := {
  name := SymName.propextName
  kind := .axiomDecl
  type := .forallE (.sort 0) (.forallE (.sort 0)
    (ExprSkeleton.arrow (ExprSkeleton.arrow (.bvar 1) (.bvar 0))
      (ExprSkeleton.arrow (ExprSkeleton.arrow (.bvar 0) (.bvar 1)) (.const SymName.trueName))))
  originModule := SymName.ofList ["Init", "Core"]
}

def baseQuotSoundDecl : ConstantRecord := {
  name := SymName.quotSoundName
  kind := .axiomDecl
  type := ExprSkeleton.arrow (.const SymName.trueName) (.const SymName.trueName)
  originModule := SymName.ofList ["Init", "Core"]
}

def baseClassicalChoiceDecl : ConstantRecord := {
  name := SymName.classicalChoiceName
  kind := .axiomDecl
  type := ExprSkeleton.arrow (.const SymName.trueName) (.const SymName.trueName)
  originModule := SymName.ofList ["Init", "Classical"]
}

def verificationResultMkName : SymName :=
  SymName.ofList ["Trusted", "VerificationResult", "VerificationResult", "mk"]

def baseVerificationResultDecl : ConstantRecord := {
  name := SymName.verificationResultName
  kind := .inductDecl [verificationResultMkName]
  type := ExprSkeleton.arrow (.const SymName.natName) (.sort 0)
  all := [SymName.verificationResultName]
  originModule := SymName.ofList ["Trusted", "VerificationResult"]
}

def baseVerificationResultMkDecl : ConstantRecord := {
  name := verificationResultMkName
  kind := .ctorDecl SymName.verificationResultName
  type := .forallE (.const SymName.natName)
    (.forallE (.const SymName.trueName)
      (.app (.const SymName.verificationResultName) (.bvar 1)))
  originModule := SymName.ofList ["Trusted", "VerificationResult"]
}

/-- Consistent standard base constant list (foundational `Init` + `Trusted.VerificationResult`). -/
def standardBaseDecls : List ConstantRecord := [
  baseFalseDecl,
  baseTrueDecl,
  baseTrueIntroDecl,
  baseNatDecl,
  baseNatZeroDecl,
  baseNatSuccDecl,
  baseNatAddDecl,
  baseStringDecl,
  baseEqDecl,
  baseEqReflDecl,
  basePropextDecl,
  baseQuotSoundDecl,
  baseClassicalChoiceDecl,
  baseVerificationResultDecl,
  baseVerificationResultMkDecl
]

/-- Convert a list of declarations into a `KernelEnv` keyed by `ci.name`. -/
def mkBaseKernelEnv (decls : List ConstantRecord) : KernelEnv :=
  decls.map fun ci => (ci.name, ci)

def standardBaseEnv : KernelEnv :=
  mkBaseKernelEnv standardBaseDecls

/-- Concrete semantic model for `standardBaseEnv` proving it is genuinely consistent. -/
noncomputable def standardBaseModel (n : SymName) : SemVal :=
  if n == SymName.falseName then .prop False
  else if n == SymName.trueName then .prop True
  else if n == SymName.trueIntroName then .prf
  else if n == SymName.natName then .ty Nat (fun k => .base SymName.natName k)
  else if n == SymName.natZeroName then .base SymName.natName 0
  else if n == SymName.natSuccName then
    semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (k : Nat) => .base SymName.natName (k + 1))
  else if n == SymName.natAddName then
    semLam (.ty Nat (fun k => .base SymName.natName k))
      (fun (_ : Nat) => semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (m : Nat) => .base SymName.natName m))
  else if n == SymName.stringName then .ty String (fun s => .strVal s)
  else if n == SymName.eqName then
    semLam (.ty Nat (fun k => .base SymName.natName k))
      (fun (a : Nat) => semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (b : Nat) => .prop (a = b)))
  else if n == SymName.eqReflName then .prf
  else if n == SymName.propextName then .prf
  else if n == SymName.quotSoundName then .prf
  else if n == SymName.classicalChoiceName then .prf
  else if n == SymName.verificationResultName then
    semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (_ : Nat) => .prop True)
  else if n == verificationResultMkName then .prf
  else .err

/-- Constructive proof that `standardBaseEnv` is semantically sound under `standardBaseModel`. -/
theorem standardBaseEnv_sound : EnvSound standardBaseEnv standardBaseModel := by
  have hNatTy : standardBaseModel SymName.natName = .ty Nat (fun k => .base SymName.natName k) := by
    simp [standardBaseModel, SymName.natName, SymName.falseName, SymName.trueName, SymName.trueIntroName,
      SymName.mkSimple, SymName.ofList]
  have hNatInj : Function.Injective (fun k : Nat => SemVal.base SymName.natName k) := by
    intro a b h; cases h; rfl
  have hStrTy : standardBaseModel SymName.stringName = .ty String (fun s => .strVal s) := by
    simp [standardBaseModel, SymName.stringName, SymName.falseName, SymName.trueName,
      SymName.trueIntroName, SymName.natName, SymName.natZeroName, SymName.natSuccName, SymName.natAddName,
      SymName.mkSimple, SymName.ofList]
  have hStrInj : Function.Injective SemVal.strVal := by intro a b h; cases h; rfl
  have hFalseTy : standardBaseModel SymName.falseName = .prop False := by
    simp [standardBaseModel]
  have hTrueTy : standardBaseModel SymName.trueName = .prop True := by
    simp [standardBaseModel, SymName.trueName, SymName.falseName, SymName.mkSimple]
  have hTrueIntro : standardBaseModel SymName.trueIntroName = .prf := by
    simp [standardBaseModel, SymName.trueIntroName, SymName.falseName, SymName.trueName,
      SymName.mkSimple, SymName.ofList]
  have hNatZero : standardBaseModel SymName.natZeroName = .base SymName.natName 0 := by
    simp [standardBaseModel, SymName.natZeroName, SymName.falseName, SymName.trueName,
      SymName.trueIntroName, SymName.natName, SymName.mkSimple, SymName.ofList]
  have hNatSucc : standardBaseModel SymName.natSuccName =
      semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (k : Nat) => .base SymName.natName (k + 1)) := by
    simp [standardBaseModel, SymName.natSuccName, SymName.falseName, SymName.trueName,
      SymName.trueIntroName, SymName.natName, SymName.natZeroName, SymName.mkSimple, SymName.ofList]
  have hNatAdd : standardBaseModel SymName.natAddName =
      semLam (.ty Nat (fun k => .base SymName.natName k))
        (fun (_ : Nat) => semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (m : Nat) => .base SymName.natName m)) := by
    simp [standardBaseModel, SymName.natAddName, SymName.falseName, SymName.trueName,
      SymName.trueIntroName, SymName.natName, SymName.natZeroName, SymName.natSuccName,
      SymName.mkSimple, SymName.ofList]
  have hEqVal : standardBaseModel SymName.eqName =
      semLam (.ty Nat (fun k => .base SymName.natName k))
        (fun (a : Nat) => semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (b : Nat) => .prop (a = b))) := by
    simp [standardBaseModel, SymName.eqName, SymName.falseName, SymName.trueName,
      SymName.trueIntroName, SymName.natName, SymName.natZeroName, SymName.natSuccName,
      SymName.natAddName, SymName.stringName, SymName.mkSimple, SymName.ofList]
  have hEqRefl : standardBaseModel SymName.eqReflName = .prf := by
    simp [standardBaseModel, SymName.eqReflName, SymName.falseName, SymName.trueName,
      SymName.trueIntroName, SymName.natName, SymName.natZeroName, SymName.natSuccName,
      SymName.natAddName, SymName.stringName, SymName.eqName, SymName.mkSimple, SymName.ofList]
  have hPropext : standardBaseModel SymName.propextName = .prf := by
    simp [standardBaseModel, SymName.propextName, SymName.falseName, SymName.trueName,
      SymName.trueIntroName, SymName.natName, SymName.natZeroName, SymName.natSuccName,
      SymName.natAddName, SymName.stringName, SymName.eqName, SymName.eqReflName,
      SymName.mkSimple, SymName.ofList]
  have hQuotSound : standardBaseModel SymName.quotSoundName = .prf := by
    simp [standardBaseModel, SymName.quotSoundName, SymName.falseName, SymName.trueName,
      SymName.trueIntroName, SymName.natName, SymName.natZeroName, SymName.natSuccName,
      SymName.natAddName, SymName.stringName, SymName.eqName, SymName.eqReflName, SymName.propextName,
      SymName.mkSimple, SymName.ofList]
  have hChoice : standardBaseModel SymName.classicalChoiceName = .prf := by
    simp [standardBaseModel, SymName.classicalChoiceName, SymName.falseName, SymName.trueName,
      SymName.trueIntroName, SymName.natName, SymName.natZeroName, SymName.natSuccName,
      SymName.natAddName, SymName.stringName, SymName.eqName, SymName.eqReflName,
      SymName.propextName, SymName.quotSoundName, SymName.mkSimple, SymName.ofList]
  have hVR : standardBaseModel SymName.verificationResultName =
      semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (_ : Nat) => .prop True) := by
    simp [standardBaseModel, SymName.verificationResultName, SymName.falseName, SymName.trueName,
      SymName.trueIntroName, SymName.natName, SymName.natZeroName, SymName.natSuccName,
      SymName.natAddName, SymName.stringName, SymName.eqName, SymName.eqReflName,
      SymName.propextName, SymName.quotSoundName, SymName.classicalChoiceName,
      SymName.mkSimple, SymName.ofList]
  have hVRMk : standardBaseModel verificationResultMkName = .prf := by
    simp [standardBaseModel, verificationResultMkName, SymName.verificationResultName,
      SymName.falseName, SymName.trueName, SymName.trueIntroName, SymName.natName,
      SymName.natZeroName, SymName.natSuccName, SymName.natAddName, SymName.stringName,
      SymName.eqName, SymName.eqReflName, SymName.propextName, SymName.quotSoundName,
      SymName.classicalChoiceName, SymName.mkSimple, SymName.ofList]
  have hLookupCases : ∀ n ci, standardBaseEnv.lookup n = some ci →
      (n = SymName.falseName ∧ ci = baseFalseDecl) ∨
      (n = SymName.trueName ∧ ci = baseTrueDecl) ∨
      (n = SymName.trueIntroName ∧ ci = baseTrueIntroDecl) ∨
      (n = SymName.natName ∧ ci = baseNatDecl) ∨
      (n = SymName.natZeroName ∧ ci = baseNatZeroDecl) ∨
      (n = SymName.natSuccName ∧ ci = baseNatSuccDecl) ∨
      (n = SymName.natAddName ∧ ci = baseNatAddDecl) ∨
      (n = SymName.stringName ∧ ci = baseStringDecl) ∨
      (n = SymName.eqName ∧ ci = baseEqDecl) ∨
      (n = SymName.eqReflName ∧ ci = baseEqReflDecl) ∨
      (n = SymName.propextName ∧ ci = basePropextDecl) ∨
      (n = SymName.quotSoundName ∧ ci = baseQuotSoundDecl) ∨
      (n = SymName.classicalChoiceName ∧ ci = baseClassicalChoiceDecl) ∨
      (n = SymName.verificationResultName ∧ ci = baseVerificationResultDecl) ∨
      (n = verificationResultMkName ∧ ci = baseVerificationResultMkDecl) := by
    intro n ci hlu
    have hmem := KernelEnv.lookup_mem hlu
    simp only [standardBaseEnv, mkBaseKernelEnv, standardBaseDecls, List.map,
      List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    exact hmem
  refine {
    has_false := by decide
    has_true := by decide
    has_nat := by decide
    has_string := by decide
    false_interp := hFalseTy
    true_interp := hTrueTy
    nat_interp := hNatTy
    string_interp := hStrTy
    const_sound := by
      intro n ci hlu
      rcases hLookupCases n ci hlu with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨rfl, by decide, by intro c hc; simp [baseFalseDecl, ExprSkeleton.usedConstants] at hc, ?_⟩
        simp only [baseFalseDecl, evalExpr, hFalseTy, Inhabits]; exact ⟨False, rfl⟩
      · refine ⟨rfl, by decide, by intro c hc; simp [baseTrueDecl, ExprSkeleton.usedConstants] at hc, ?_⟩
        simp only [baseTrueDecl, evalExpr, hTrueTy, Inhabits]; exact ⟨True, rfl⟩
      · refine ⟨rfl, by decide, by intro c hc; simp [baseTrueIntroDecl, ExprSkeleton.usedConstants] at hc; subst hc; decide, ?_⟩
        simp only [baseTrueIntroDecl, evalExpr, hTrueIntro, hTrueTy, Inhabits]; exact ⟨trivial, trivial⟩
      · refine ⟨rfl, by decide, by intro c hc; simp [baseNatDecl, ExprSkeleton.usedConstants] at hc, ?_⟩
        simp only [baseNatDecl, evalExpr, hNatTy, Inhabits]; exact Or.inr (Or.inr ⟨Nat, _, hNatInj, rfl⟩)
      · refine ⟨rfl, by decide, by intro c hc; simp [baseNatZeroDecl, ExprSkeleton.usedConstants] at hc; subst hc; decide, ?_⟩
        simp only [baseNatZeroDecl, evalExpr, hNatZero, hNatTy, Inhabits]; exact ⟨0, rfl⟩
      · refine ⟨rfl, by decide, by intro c hc; simp [baseNatSuccDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, ExprSkeleton.usedConstants] at hc; rcases hc with rfl | rfl <;> decide, ?_⟩
        simp only [baseNatSuccDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, evalExpr, hNatSucc, hNatTy]
        exact semLam_inhabits_semPi (fun _ => hNatInj) (fun (k : Nat) => ⟨k + 1, rfl⟩)
      · refine ⟨rfl, by decide, by intro c hc; simp [baseNatAddDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, ExprSkeleton.usedConstants] at hc; rcases hc with rfl | rfl | rfl <;> decide, ?_⟩
        simp only [baseNatAddDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, evalExpr, hNatAdd, hNatTy]
        apply semLam_inhabits_semPi
        · intro _
          have hpi := semPi_inhabits_sort (u := 1) (v := 1)
            (domV := .ty Nat (fun k => .base SymName.natName k))
            (bodyFn := fun _ => .ty Nat (fun k => .base SymName.natName k))
            (Or.inr (Or.inr ⟨Nat, _, hNatInj, rfl⟩))
            (fun _ => Or.inr (Or.inr ⟨Nat, _, hNatInj, rfl⟩))
          exact inhabits_sort_implies_isSemType (u := 1) hpi
        · intro _
          exact semLam_inhabits_semPi (fun _ => hNatInj) (fun m => ⟨m, rfl⟩)
      · refine ⟨rfl, by decide, by intro c hc; simp [baseStringDecl, ExprSkeleton.usedConstants] at hc, ?_⟩
        simp only [baseStringDecl, evalExpr, hStrTy, Inhabits]; exact Or.inr (Or.inr ⟨String, _, hStrInj, rfl⟩)
      · refine ⟨rfl, by decide, by intro c hc; simp [baseEqDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, ExprSkeleton.usedConstants] at hc; rcases hc with rfl | rfl <;> decide, ?_⟩
        simp only [baseEqDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, evalExpr, hEqVal]
        apply semLam_inhabits_semPi
        · intro _
          have hpi := semPi_inhabits_sort (u := 1) (v := 1)
            (domV := .ty Nat (fun k => .base SymName.natName k))
            (bodyFn := fun _ => .propSort)
            (Or.inr (Or.inr ⟨Nat, _, hNatInj, rfl⟩))
            (fun _ => Or.inl rfl)
          exact inhabits_sort_implies_isSemType (u := 1) hpi
        · intro a
          exact semLam_inhabits_semPi (fun _ => trivial) (fun b => ⟨a = b, rfl⟩)
      · refine ⟨rfl, by decide, by intro c hc; simp [baseEqReflDecl, ExprSkeleton.usedConstants] at hc; rcases hc with rfl | rfl <;> decide, ?_⟩
        have hEqBody : ∀ (nt : SemVal), nt = .ty Nat (fun k => .base SymName.natName k) →
            Inhabits .prf
              (semPi nt (fun a =>
                semApp (semApp (semLam (.ty Nat (fun k => .base SymName.natName k))
                  (fun (x : Nat) => semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (y : Nat) => .prop (x = y))))
                  (nt.decode a)) (nt.decode a))) := by
          intro nt hnt; subst hnt
          dsimp only [SemVal.decode]
          have hstep : ∀ a : Nat,
              semApp (semApp (semLam (.ty Nat (fun k => .base SymName.natName k))
                (fun (x : Nat) => semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (y : Nat) => .prop (x = y))))
                (.base SymName.natName a)) (.base SymName.natName a) = .prop (a = a) := by
            intro a
            have h1 := semApp_semLam (domV := .ty Nat (fun k => .base SymName.natName k)) hNatInj
              (fun (x : Nat) => semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (y : Nat) => .prop (x = y))) a
            have h2 := semApp_semLam (domV := .ty Nat (fun k => .base SymName.natName k)) hNatInj
              (fun (y : Nat) => .prop (a = y)) a
            exact (congrArg (fun fn => semApp fn (.base SymName.natName a)) h1).trans h2
          rw [semPi_eq_prop (domV := .ty Nat (fun k => .base SymName.natName k)) (fun a => ⟨a = a, hstep a⟩)]
          refine ⟨rfl, fun a => ?_⟩
          rw [hstep a]
          rfl
        simp only [baseEqReflDecl, evalExpr, hEqRefl, hEqVal]
        exact hEqBody (standardBaseModel SymName.natName) hNatTy
      · refine ⟨rfl, by decide, by intro c hc; simp [basePropextDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, ExprSkeleton.usedConstants] at hc; subst hc; decide, ?_⟩
        simp only [basePropextDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, evalExpr, hPropext, hTrueTy]
        rw [semPi_eq_prop (fun P => ⟨_, by
          rw [semPi_eq_prop (fun Q => ⟨_, by
            rw [semPi_eq_prop (fun _ => ⟨_, by
              rw [semPi_eq_prop (fun _ => ⟨True, rfl⟩)]⟩)]⟩)]⟩)]
        refine ⟨rfl, fun P => ?_⟩
        rw [semPi_eq_prop (fun Q => ⟨_, by
          rw [semPi_eq_prop (fun _ => ⟨_, by
            rw [semPi_eq_prop (fun _ => ⟨True, rfl⟩)]⟩)]⟩)]
        intro Q
        rw [semPi_eq_prop (fun _ => ⟨_, by rw [semPi_eq_prop (fun _ => ⟨True, rfl⟩)]⟩)]
        intro _
        rw [semPi_eq_prop (fun _ => ⟨True, rfl⟩)]
        intro _; trivial
      · refine ⟨rfl, by decide, by intro c hc; simp [baseQuotSoundDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, ExprSkeleton.usedConstants] at hc; rcases hc with rfl | rfl <;> decide, ?_⟩
        simp only [baseQuotSoundDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, evalExpr, hQuotSound, hTrueTy]
        rw [semPi_eq_prop (fun _ => ⟨True, rfl⟩)]
        exact ⟨rfl, fun _ => trivial⟩
      · refine ⟨rfl, by decide, by intro c hc; simp [baseClassicalChoiceDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, ExprSkeleton.usedConstants] at hc; rcases hc with rfl | rfl <;> decide, ?_⟩
        simp only [baseClassicalChoiceDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, evalExpr, hChoice, hTrueTy]
        rw [semPi_eq_prop (fun _ => ⟨True, rfl⟩)]
        exact ⟨rfl, fun _ => trivial⟩
      · refine ⟨rfl, by decide, by intro c hc; simp [baseVerificationResultDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, ExprSkeleton.usedConstants] at hc; subst hc; decide, ?_⟩
        simp only [baseVerificationResultDecl, ExprSkeleton.arrow, ExprSkeleton.liftBVar, evalExpr, hVR]
        exact semLam_inhabits_semPi (fun _ => trivial) (fun _ => ⟨True, rfl⟩)
      · refine ⟨rfl, by decide, by intro c hc; simp [baseVerificationResultMkDecl, ExprSkeleton.usedConstants] at hc; rcases hc with rfl | rfl | rfl <;> decide, ?_⟩
        have hVRBody : ∀ (nt tr : SemVal),
            nt = .ty Nat (fun k => .base SymName.natName k) →
            tr = .prop True →
            Inhabits .prf
              (semPi nt (fun a =>
                semPi tr (fun _ =>
                  semApp (semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (_ : Nat) => .prop True))
                    (nt.decode a)))) := by
          intro nt tr hnt htr; subst hnt; subst htr
          dsimp only [SemVal.decode]
          have hstep : ∀ a : Nat,
              semApp (semLam (.ty Nat (fun k => .base SymName.natName k)) (fun (_ : Nat) => .prop True))
                (.base SymName.natName a) = .prop True := by
            intro a
            exact semApp_semLam (domV := .ty Nat (fun k => .base SymName.natName k)) hNatInj (fun (_ : Nat) => .prop True) a
          rw [semPi_eq_prop (domV := .ty Nat (fun k => .base SymName.natName k))
            (fun a => ⟨_, semPi_eq_prop (domV := .prop True) (fun _ => ⟨True, hstep a⟩)⟩)]
          refine ⟨rfl, fun a => ?_⟩
          rw [semPi_eq_prop (domV := .prop True) (fun _ => ⟨True, hstep a⟩)]
          intro _
          rw [hstep a]
          trivial
        simp only [baseVerificationResultMkDecl, evalExpr, hVRMk, hVR]
        exact hVRBody (standardBaseModel SymName.natName) (standardBaseModel SymName.trueName) hNatTy hTrueTy
    defn_sound := by
      intro n ci v hlu hk _
      rcases hLookupCases n ci hlu with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases hk
    induct_sound := by
      intro n ci ctors hlu hk
      rcases hLookupCases n ci hlu with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals try cases hk
      · exact ⟨List.nodup_nil,
          (fun _ => by rw [hFalseTy]; congr 1; exact propext ⟨False.elim, fun h => by cases h⟩),
          (fun h => by cases h)⟩
      · exact ⟨by simp,
          (fun _ => by rw [hTrueTy]; congr 1; exact propext ⟨fun _ => rfl, fun _ => trivial⟩),
          (fun h => by cases h)⟩
      · refine ⟨by simp [SymName.natZeroName, SymName.natSuccName, SymName.ofList], (fun h => by cases h), ?_⟩
        intro _ hnb; simp [isBuiltinCarrierName] at hnb
      · refine ⟨List.nodup_nil, (fun h => by cases h), ?_⟩
        intro _ hnb; simp [isBuiltinCarrierName] at hnb
      · exact ⟨by simp, (fun h => by cases h), (fun h => by cases h)⟩
      · exact ⟨by simp, (fun h => by cases h), (fun h => by cases h)⟩
    ctor_sound := by
      intro n ci p indCi ctors hlu hk hty hluP hkP
      rcases hLookupCases n ci hlu with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals try cases hk
      · rcases hLookupCases SymName.trueName indCi hluP with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        all_goals try (rcases h with ⟨heq, _⟩; exact absurd heq (by decide))
        rcases h with ⟨_, rfl⟩
        exact ⟨(fun _ => hTrueIntro), (fun h => by cases h)⟩
      · rcases hLookupCases SymName.natName indCi hluP with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        all_goals try (rcases h with ⟨heq, _⟩; exact absurd heq (by decide))
        rcases h with ⟨_, rfl⟩
        exact ⟨(fun h => by cases h), (fun _ hnb => by simp [isBuiltinCarrierName] at hnb)⟩
      · cases hty
      · cases hty
      · cases hty
    proj_sound := by
      intro structName idx fTy v hfield _
      have hnone : lookupStructFieldType? standardBaseEnv structName idx = none := by
        unfold lookupStructFieldType?
        cases hluS : standardBaseEnv.lookup structName with
        | none => rfl
        | some indCi =>
          rcases hLookupCases structName indCi hluS with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          all_goals try rfl
      rw [hnone] at hfield
      cases hfield
  }

/-! ## Section 7: Operational Vulnerability Models (Pre-Fix Lean 4.34.1 & Pre-Fix `TrustedBoundary`) -/

/-- State of Lean 4.34.1's `Lean.Kernel.Environment.replay` (`src/lean/Lean/Replay.lean` lines 36–41). -/
structure NaiveReplayState where
  env : KernelEnv
  remaining : List SymName
  postponedConstructors : List SymName := []
  postponedRecursors : List SymName := []
  deriving DecidableEq, Repr

/-- Erase a name from a list. -/
def eraseName (n : SymName) : List SymName → List SymName
  | [] => []
  | x :: xs => if x == n then eraseName n xs else x :: eraseName n xs

/--
Faithful operational model of pre-`#16677` Lean 4.34.1 `Replay.lean` (`replayConstant` lines 74–136).
Reproduces all four key-vs-`ci.name` soundness bugs:
1. `.ctorDecl` postpones `ci.name` (NOT map key `name`).
2. `.recDecl` postpones `ci.name` (NOT map key `name`).
3. `.quotDecl` replays `Eq` and adds canonical `Quot` without checking `name == ci.name` or `ci.type`.
4. `.thmDecl` short-circuits when `env.lookup ci.name` matches `(name, type, all)` without checking `name == ci.name`.
-/
def naiveReplayConstant (newConstants : KernelEnv) (kernelFuel : Nat) :
    Nat → SymName → NaiveReplayState → Except AuditFailure NaiveReplayState
  | 0, _, st => .ok st
  | stepFuel + 1, name, st => do
    if !st.remaining.contains name then
      return st
    let mut s : NaiveReplayState := { st with remaining := eraseName name st.remaining }
    match newConstants.lookup name with
    | none => return s
    | some ci =>
      let deps := ci.type.usedConstants ++ (match ci.value? with | some v => v.usedConstants | none => [])
      for dep in deps do
        if s.remaining.contains dep then
          s ← naiveReplayConstant newConstants kernelFuel stepFuel dep s
      match ci.kind with
      | .defnDecl | .opaqueDecl | .axiomDecl =>
        let env' ← kernelCheckDecl s.env kernelFuel true ci
        return { s with env := env' }
      | .thmDecl =>
        -- Lean 4.34.1 Replay.lean lines 90–96: short-circuit on duplicate `ci.name` ignoring map key `name`!
        match s.env.lookup ci.name with
        | some prev =>
          if prev.kind == .thmDecl && prev.name == ci.name &&
             prev.type == ci.type && prev.all == ci.all then
            return s
          else
            let env' ← kernelCheckDecl s.env kernelFuel false ci
            return { s with env := env' }
        | none =>
          let env' ← kernelCheckDecl s.env kernelFuel false ci
          return { s with env := env' }
      | .inductDecl ctors =>
        let mut env' ← kernelCheckDecl s.env kernelFuel false ci
        for oName in ci.all do
          s := { s with remaining := eraseName oName s.remaining }
        for ctorName in ctors do
          match newConstants.lookup ctorName with
          | some ctorCi =>
            env' ← kernelCheckDecl env' kernelFuel false ctorCi
          | none => throw (.kernelReplayMissingDep ci.name ctorName)
        let recName := SymName.str ci.name "rec"
        match newConstants.lookup recName with
        | some recCi =>
          env' ← kernelCheckDecl env' kernelFuel false recCi
        | none => pure ()
        return { s with env := env' }
      | .ctorDecl _ =>
        -- BUG (`lean4#16677`): inserts `ci.name` instead of map key `name`!
        return { s with postponedConstructors := ci.name :: s.postponedConstructors }
      | .recDecl _ =>
        -- BUG (`lean4#16677`): inserts `ci.name` instead of map key `name`!
        return { s with postponedRecursors := ci.name :: s.postponedRecursors }
      | .quotDecl =>
        -- BUG (`lean4#16677`): adds `quotDecl` without verifying `name == ci.name` or `ci.type`!
        if !s.env.contains SymName.eqName then
          throw (.kernelReplayMissingDep name SymName.eqName)
        return s

/--
Faithful operational model of pre-`#16677` Lean 4.34.1 `Kernel.Environment.replay`
(`src/lean/Lean/Replay.lean` lines 148–190).
-/
def naiveLean434Replay (base : KernelEnv) (kernelFuel : Nat)
    (newConstants : KernelEnv) : Except AuditFailure KernelEnv := do
  let initRem := newConstants.filterMap fun (n, ci) =>
    if !ci.isUnsafe && !ci.isPartial then some n else none
  let mut st : NaiveReplayState := { env := base, remaining := initRem }
  let stepFuel := newConstants.length + 4
  for n in initRem do
    st ← naiveReplayConstant newConstants kernelFuel stepFuel n st
  -- `checkPostponedConstructors` (Replay.lean lines 148–153): looks up by `ctor` (`ci.name`), ignoring aliased map key!
  for ctor in st.postponedConstructors do
    match st.env.lookup ctor, newConstants.lookup ctor with
    | some c1, some c2 =>
      if c1 != c2 then
        throw (.kernelTypeError ctor "Invalid constructor")
    | _, _ =>
      throw (.kernelTypeError ctor "No such constructor")
  -- `checkPostponedRecursors` (Replay.lean lines 159–164): looks up by `ctor` (`ci.name`), ignoring aliased map key!
  for recName in st.postponedRecursors do
    match st.env.lookup recName, newConstants.lookup recName with
    | some r1, some r2 =>
      if r1 != r2 then
        throw (.kernelTypeError recName "Invalid recursor")
    | _, _ =>
      throw (.kernelTypeError recName "No such recursor")
  return st.env

/--
Simple DFS axiom closure walker on an environment `env` (used by both the naive and hardened auditors).
-/
def walkEdgesFuel (env : KernelEnv) :
    Nat → List SymName → List SymName → Except AuditFailure (List SymName)
  | 0, _, visited => .ok visited
  | _ + 1, [], visited => .ok visited
  | fuel + 1, n :: pending, visited => do
    if visited.contains n then
      walkEdgesFuel env fuel pending visited
    else
      match env.lookup n with
      | none => throw (.unknownConstant n)
      | some ci =>
        let edges ← ConstantRecord.declarationEdges ci
        walkEdgesFuel env fuel (edges ++ pending) (n :: visited)

/--
Faithful operational model of pre-fix `TrustedBoundary.lean` `downstreamAudit` (line 408) and
`verifyAudit` (line 607):
- Builds `importedEnv := finalizeImportedEnv` (`constNames.zip constants`) without checking
  `constNames == constants.map (·.name)` or duplicate names.
- Checks `verifyRoots` headers and axiom-freeness against `importedEnv`.
- Builds `replayLocals` via `insertOverwrite ci.name ci`, silently overwriting an earlier forged
  entry sharing `ci.name` with a later benign entry!
- Replays `replayLocals` cleanly and returns `.ok`!
-/
def naiveInsertByCiNameAudit (pkg : PackageAuditInput) (kernelFuel : Nat := 64) :
    Except AuditFailure KernelEnv := do
  let baseEnv := mkBaseKernelEnv pkg.baseEnv
  let importedEnv := KernelEnv.finalizeImportedEnv pkg.modules ++ baseEnv
  -- Check verifyRoots header & axiom closure on `importedEnv` (passing when forged body is axiom-free!)
  for root in pkg.verifyRoots do
    match importedEnv.lookup root with
    | none => throw (.unknownConstant root)
    | some ci =>
      if ci.kind != .thmDecl then
        throw (.invalidVerifyRoot root "not a theorem")
      if ci.type.getAppFn != .const SymName.verificationResultName then
        throw (.invalidVerifyRoot root "not a VerificationResult")
      let visited ← walkEdgesFuel importedEnv (importedEnv.length + 2) [root] []
      for dep in visited do
        match importedEnv.lookup dep with
        | none => throw (.unknownConstant dep)
        | some depCi =>
          if depCi.isUnsafe || depCi.isPartial then
            throw (.unsafeOrPartialDecl depCi.originModule dep)
          if depCi.isAxiom && !SymName.isFoundationalAxiom dep then
            throw (.forbiddenAxiom root dep depCi.originModule)
  -- BUG (`TrustedBoundary.lean` lines 408 & 607): `replayLocals := replayLocals.insert ci.name ci`
  let mut replayLocals : KernelEnv := []
  for inv in pkg.modules do
    for ci in inv.constants do
      if ci.isUnsafe || ci.isPartial then
        throw (.unsafeOrPartialDecl inv.moduleName ci.name)
      if ci.isAxiom && !SymName.isFoundationalAxiom ci.name then
        throw (.forbiddenAxiom ci.name ci.name inv.moduleName)
      replayLocals := replayLocals.insertOverwrite ci.name ci
  replayCleanEnv baseEnv kernelFuel false (replayLocals.map Prod.snd)

/--
Naive pre-`lowmem_lean` (`cl/1027843093`) validator that falsely rejects valid multi-element
mutual `.all` blocks on `thmDecl` and `opaqueDecl`.
-/
def naiveSingleAllCheck (inv : ModuleInventory) : Except AuditFailure Unit := do
  for ci in inv.constants do
    match ci.kind with
    | .thmDecl | .opaqueDecl =>
      if ci.all != [ci.name] then
        throw (.invalidMutualAll inv.moduleName ci.name "naive single-element .all check rejected mutual block")
    | _ => pure ()

/-! ## Section 8: Hardened `validateReplayInventory`, `auditAndReplayPackage`, & Soundness Theorems -/

/-- Total recursive list checker in `Except AuditFailure Unit` (clean structural induction). -/
def checkEach {α : Type} : List α → (α → Except AuditFailure Unit) → Except AuditFailure Unit
  | [], _ => .ok ()
  | x :: rest, f => do
    f x
    checkEach rest f

theorem checkEach_ok_mem {α : Type} {xs : List α} {f : α → Except AuditFailure Unit}
    (h : checkEach xs f = .ok ()) : ∀ x ∈ xs, f x = .ok () := by
  induction xs with
  | nil => intro _ hx; cases hx
  | cons a tl ih =>
    intro x hx
    simp only [checkEach, bind, Except.bind] at h
    cases hfa : f a with
    | error _ => rw [hfa] at h; cases h
    | ok u =>
      cases u; rw [hfa] at h
      cases hx with
      | head => exact hfa
      | tail _ htl => exact ih h x htl

/-- Validate multi-part `.olean` presence on disk (`V17`, `V18`: refuse silent fallback to `.olean`). -/
def validateOleanParts (inv : ModuleInventory) : Except AuditFailure Unit := do
  if !inv.oleanParts.hasOlean then
    throw (.missingOleanBase inv.moduleName)
  if inv.oleanParts.isModuleMode then
    if !inv.oleanParts.hasServer then
      throw (.missingOleanServer inv.moduleName)
    if !inv.oleanParts.hasPrivate then
      throw (.missingOleanPrivate inv.moduleName)

/-- Validate module role against canonical naming rules (`V15`: reject `Topic.Proofs.Defs` spoofing). -/
def validateModuleRole (inv : ModuleInventory) : Except AuditFailure Unit := do
  if inv.role == .defsExempt && !SymName.isStrictExemptModuleName inv.moduleName then
    throw (.spoofedExemptModule inv.moduleName)

/-- Lookup a declaration by `ci.name` inside a module's `constants` list. -/
def findConstByName (consts : List ConstantRecord) (n : SymName) : Option ConstantRecord :=
  consts.find? fun ci => ci.name == n

/-- Validate a single mutual peer of `ci` in `inv`. -/
def validateMutualPeer (inv : ModuleInventory) (ci : ConstantRecord) (peerName : SymName) :
    Except AuditFailure Unit :=
  match findConstByName inv.constants peerName with
  | none =>
    throw (.invalidMutualAll inv.moduleName ci.name "missing mutual peer in inventory")
  | some peerCi => do
    if peerCi.kind.tag != ci.kind.tag then
      throw (.invalidMutualAll inv.moduleName ci.name "incompatible mutual peer kind")
    if peerCi.all != ci.all then
      throw (.invalidMutualAll inv.moduleName ci.name "asymmetric mutual .all membership")

/--
Validate mutual `.all` group invariants (`lowmem_lean` `cl/1027843093`):
- Accepts valid multi-element mutual blocks on `thmDecl`, `opaqueDecl`, `defnDecl`, `inductDecl`.
- Rejects empty `.all`, duplicates in `.all`, `anonymous ∈ .all`, `ci.name ∉ .all`, missing peers,
  incompatible peer `DeclKind` tag, asymmetric peer `.all`, and open expressions in `declarationEdges`.
-/
def validateMutualAll (inv : ModuleInventory) : Except AuditFailure Unit :=
  checkEach inv.constants fun ci => do
    if ci.kind.carriesMutualAll then
      if ci.all.isEmpty then
        throw (.invalidMutualAll inv.moduleName ci.name "empty .all list")
      if hasDuplicates ci.all then
        throw (.invalidMutualAll inv.moduleName ci.name "duplicate entry in .all")
      if ci.all.any SymName.isAnonymous then
        throw (.invalidMutualAll inv.moduleName ci.name "anonymous name in .all")
      match ci.kind with
      | .recDecl _ =>
        pure ()
      | _ =>
        if !ci.all.contains ci.name then
          throw (.invalidMutualAll inv.moduleName ci.name "ci.name missing from .all")
        checkEach ci.all (validateMutualPeer inv ci)
    let _ ← ConstantRecord.declarationEdges ci

/--
Check whether `ci` is a legitimate Lean equation-compiler `_unsafe_rec` companion for a safe
parent definition in the same module with matching type (hardened over `TrustedBoundary.lean` lines 255–260).
-/
def isCodegenUnsafeRecInMod (inv : ModuleInventory) (ci : ConstantRecord) : Bool :=
  if ci.safety != .partialDecl then false
  else
    match ci.name.unsafeRecParent? with
    | none => false
    | some parent =>
      match findConstByName inv.constants parent with
      | none => false
      | some parentCi =>
        parentCi.safety == .safe &&
        parentCi.originModule == inv.moduleName &&
        ci.type == parentCi.type

/-- Validate a single `(k, ci)` entry in a module's `replayMap`. -/
def validateReplayEntry (modName : SymName) (p : SymName × ConstantRecord) :
    Except AuditFailure Unit := do
  let (k, ci) := p
  if k.isAnonymous || ci.name.isAnonymous then
    throw (.anonymousConstantName modName)
  if k != ci.name then
    throw (.keyNameMismatch modName k ci.name)
  if ci.hasValue && ci.value?.isNone then
    throw (.missingStoredValue modName ci.name)
  if ci.originModule != modName && !SymName.isReservedAuxName ci.name then
    throw (.originMismatch modName ci.name ci.originModule)

/--
Hardened single-module `.olean` replay-inventory validator (`validateReplayInventory`).
Enforces:
1. Multi-part `.olean.{server,private}` presence (`V17`, `V18`).
2. `strictExempt` anti-spoofing (`V15`).
3. Exact `constNames` / `constants` / `replayMap` length, alignment, `Nodup`, and key-equals-`ci.name`
   bijection (defeating `lean4#16677` and `TrustedBoundary` `replayLocals` overwrite).
4. Origin discipline, non-anonymous names, stored value presence, and mutual `.all` integrity (`lowmem_lean`).
-/
def validateReplayInventory (inv : ModuleInventory) : Except AuditFailure Unit := do
  validateOleanParts inv
  validateModuleRole inv
  if inv.constNames.length != inv.constants.length then
    throw (.inventoryLengthMismatch inv.moduleName inv.constNames.length inv.constants.length)
  if inv.replayMap != inv.constNames.zip inv.constants then
    throw (.replayMapDrift inv.moduleName)
  if hasDuplicates inv.constNames then
    throw (.duplicateConstName inv.moduleName inv.moduleName)
  checkEach inv.replayMap (validateReplayEntry inv.moduleName)
  validateMutualAll inv

/-- True iff `inv` is genuinely exempt from `strict_proofs` extension restrictions (`Defs` module). -/
def isStrictExemptModule (inv : ModuleInventory) : Bool :=
  inv.role == .defsExempt && SymName.isStrictExemptModuleName inv.moduleName

/--
Audit persistent environment extension tables and public namespace suffix shadowing for a module
(`V01`, `V02`, `V07`, `V08`, `V10`, `V11`, `V12`, `V13`, `V15`, `V16`).
Explicitly ignores `.cachedExportedAxioms` (`V06`) so tampered caches can never mask axioms.
-/
def validateModuleExtensions (cfg : AuditConfig) (inv : ModuleInventory)
    (protectedNames : List SymName) : Except AuditFailure Unit := do
  if !cfg.enforceStrictProofs || inv.role == .foundation || isStrictExemptModule inv then
    return ()
  for ext in inv.extEntries do
    match ext with
    | .macroEntry d _ =>
      throw (.forbiddenMacroOrElab inv.moduleName "macro" d)
    | .commandElabEntry d _ =>
      throw (.forbiddenMacroOrElab inv.moduleName "command_elab" d)
    | .localCommandElabEntry d _ persistedGlobal =>
      if persistedGlobal then
        throw (.forbiddenMacroOrElab inv.moduleName "local_command_elab_global" d)
    | .scopedElabEntry d _ =>
      throw (.forbiddenMacroOrElab inv.moduleName "scoped_elab" d)
    | .scopedMacroEntry d _ =>
      throw (.forbiddenMacroOrElab inv.moduleName "scoped_macro" d)
    | .scopedInstanceEntry d _ _ =>
      throw (.forbiddenInstanceOrCoe inv.moduleName "scoped_instance" d)
    | .termElabEntry d _ =>
      throw (.forbiddenMacroOrElab inv.moduleName "term_elab" d)
    | .delabEntry d _ =>
      throw (.forbiddenMacroOrElab inv.moduleName "delab" d)
    | .appUnexpanderEntry d _ =>
      throw (.forbiddenMacroOrElab inv.moduleName "app_unexpander" d)
    | .instanceEntry d _ targetOrigin _ =>
      if targetOrigin != inv.moduleName then
        throw (.forbiddenInstanceOrCoe inv.moduleName "imported_instance" d)
    | .defaultInstanceEntry d _ =>
      throw (.forbiddenInstanceOrCoe inv.moduleName "default_instance" d)
    | .coeEntry d _ _ =>
      throw (.forbiddenInstanceOrCoe inv.moduleName "coe" d)
    | .reducibilityOverride target targetOrigin _ =>
      if targetOrigin != inv.moduleName then
        throw (.forbiddenReducibilityOverride inv.moduleName target)
    | .exportAlias aliasName target _ =>
      throw (.forbiddenShadowingOrExport inv.moduleName aliasName target)
    | .regularInitHook d =>
      throw (.forbiddenInitOrCodegenHook inv.moduleName "initialize" d)
    | .metaInitHook d =>
      throw (.forbiddenInitOrCodegenHook inv.moduleName "meta_initialize" d)
    | .implementedByHook d _ =>
      throw (.forbiddenInitOrCodegenHook inv.moduleName "implemented_by" d)
    | .externHook d _ =>
      throw (.forbiddenInitOrCodegenHook inv.moduleName "extern" d)
    | .cachedExportedAxioms _ _ =>
      -- Defense-in-depth (`V06`): never trust cached axiom extension tables!
      pure ()
  -- Public namespace suffix shadowing check (`V15`)
  for ci in inv.constants do
    if !ci.isPrivate && !ci.name.isPrivateName && !ci.name.hasInternalPart then
      for suf in ci.name.properSuffixes do
        if protectedNames.contains suf then
          throw (.forbiddenShadowingOrExport inv.moduleName ci.name suf)

/-- Find any private instance exposed in a module (used for `V14` `import all` leakage checks). -/
def findPrivateInstance? (inv : ModuleInventory) : Option SymName :=
  inv.extEntries.findSome? fun
    | .instanceEntry d _ _ true => some d
    | _ => none

/-- Audit import edges across the package (`V14`: forbid `import all` and catch private-instance leakage). -/
def validateImports (pkg : PackageAuditInput) : Except AuditFailure Unit := do
  for inv in pkg.modules do
    if inv.role != .foundation then
      for imp in inv.imports do
        if imp.importAll then
          match pkg.modules.find? (fun m => m.moduleName == imp.module) with
          | some targetMod =>
            match findPrivateInstance? targetMod with
            | some instName =>
              throw (.privateInstanceLeakViaImportAll inv.moduleName imp.module instName)
            | none =>
              throw (.forbiddenImportAll inv.moduleName imp.module)
          | none =>
            throw (.forbiddenImportAll inv.moduleName imp.module)
        if imp.isMeta && imp.module != SymName.mkSimple "Init" then
          throw (.forbiddenImportAll inv.moduleName imp.module)

/-- Lookup the `ModuleRole` of a module name in `pkg`. -/
def roleOfModule (pkg : PackageAuditInput) (modName : SymName) : ModuleRole :=
  match pkg.modules.find? (fun m => m.moduleName == modName) with
  | some inv => inv.role
  | none =>
    if SymName.isStdlibModule modName then .foundation
    else if SymName.isAssumptionsModule modName then .assumptions
    else if SymName.hasPrefix (SymName.mkSimple "Trusted") modName then .trusted
    else if SymName.hasPrefix (SymName.mkSimple "Anneal") modName then .theory
    else .spec

/--
Enforce Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation (`TrustedBoundary.lean` lines 289–306):
Walk constants reachable from `rootType`, unfolding definitions in `unfoldRoles`, and reject any
constant originating in a `.theory` module.
-/
def checkStatementOriginsFuel (pkg : PackageAuditInput) (allEnv : KernelEnv) (rootName : SymName) :
    Nat → List SymName → List SymName → Except AuditFailure Unit
  | 0, _, _ => .ok ()
  | _ + 1, [], _ => .ok ()
  | fuel + 1, n :: pending, visited => do
    if visited.contains n then
      checkStatementOriginsFuel pkg allEnv rootName fuel pending visited
    else
      match allEnv.lookup n with
      | none => throw (.unknownConstant n)
      | some ci =>
        let role := roleOfModule pkg ci.originModule
        if role == .theory then
          throw (.statementTheoryLeak rootName n ci.originModule)
        let nextDeps ←
          if role == .verify || role == .spec || role == .proof || role == .assumptions then
            ConstantRecord.declarationEdges ci
          else
            pure []
        checkStatementOriginsFuel pkg allEnv rootName fuel (nextDeps ++ pending) (n :: visited)

/-- Recursive checker over visited closure nodes (clean structural induction for soundness). -/
def checkVisitedClosure (cfg : AuditConfig) (pkg : PackageAuditInput) (allEnv : KernelEnv)
    (rootName : SymName) : List SymName → List SymName → Except AuditFailure (List SymName)
  | [], acc => .ok acc
  | dep :: rest, acc => do
    match allEnv.lookup dep with
    | none => throw (.unknownConstant dep)
    | some depCi =>
      if depCi.isUnsafe || depCi.isPartial then
        throw (.unsafeOrPartialDecl depCi.originModule dep)
      if depCi.isAxiom then
        if dep == SymName.sorryAxName then
          throw (.forbiddenAxiom rootName dep depCi.originModule)
        else if SymName.isNativeReductionAxiom dep then
          let okProv := cfg.allowProvisionalNative &&
            roleOfModule pkg depCi.originModule == .proof &&
            dep != SymName.trustCompilerName
          if !okProv then
            throw (.forbiddenNativeReductionAxiom rootName dep)
          checkVisitedClosure cfg pkg allEnv rootName rest (dep :: acc)
        else if SymName.isFoundationalAxiom dep && roleOfModule pkg depCi.originModule == .foundation then
          checkVisitedClosure cfg pkg allEnv rootName rest (dep :: acc)
        else if cfg.allowAssumptions && roleOfModule pkg depCi.originModule == .assumptions then
          checkVisitedClosure cfg pkg allEnv rootName rest (dep :: acc)
        else
          throw (.forbiddenAxiom rootName dep depCi.originModule)
      else
        checkVisitedClosure cfg pkg allEnv rootName rest acc

/-- Direct axiom & safety audit over all declarations reachable from `rootName` (ignores `cachedExportedAxioms`). -/
def auditDirectClosure (cfg : AuditConfig) (pkg : PackageAuditInput) (allEnv : KernelEnv)
    (rootName : SymName) : Except AuditFailure (List SymName) := do
  let visited ← walkEdgesFuel allEnv (allEnv.length + 2) [rootName] []
  checkVisitedClosure cfg pkg allEnv rootName visited []

/-- Certificate returned by `auditAndReplayPackage` upon passing all checks and clean-env replay. -/
structure AuditCertificate where
  replayedEnv : KernelEnv
  importedEnv : KernelEnv
  replayedCount : Nat
  verifiedRoots : List SymName
  reachedAxioms : List SymName
  deriving DecidableEq, Repr

/-- Collect the protected `Init`/`foundation`/`Defs` constant names for `V15` suffix-shadowing detection. -/
def collectProtectedNames (pkg : PackageAuditInput) : List SymName :=
  let baseNames := pkg.baseEnv.map ConstantRecord.name
  let modNames := pkg.modules.flatMap fun inv =>
    if inv.role == .foundation || isStrictExemptModule inv then inv.constNames else []
  baseNames ++ modNames

/-- Collect all non-`_unsafe_rec` declarations from `pkg.modules` to submit to clean-env kernel replay. -/
def collectReplayDecls (pkg : PackageAuditInput) : List ConstantRecord :=
  pkg.modules.flatMap fun inv =>
    inv.constants.filter fun ci => !isCodegenUnsafeRecInMod inv ci

/-- Validate `extraConstNames` provenance across all modules. -/
def auditExtraConstProvenance (pkg : PackageAuditInput) (allEnv : KernelEnv) :
    Except AuditFailure Unit := do
  for inv in pkg.modules do
    for extra in inv.extraConstNames do
      if allEnv.contains extra && !inv.constNames.contains extra then
        throw (.extraConstProvenanceMismatch inv.moduleName extra)

/-- Validate module-wide declaration safety and axiom admissibility (catching unreferenced axioms `V04`). -/
def auditModuleDeclarations (cfg : AuditConfig) (pkg : PackageAuditInput) :
    Except AuditFailure Unit := do
  for inv in pkg.modules do
    for ci in inv.constants do
      if !isCodegenUnsafeRecInMod inv ci then
        if ci.isUnsafe || ci.isPartial then
          throw (.unsafeOrPartialDecl inv.moduleName ci.name)
        if ci.isAxiom then
          if ci.name == SymName.sorryAxName then
            throw (.forbiddenAxiom ci.name ci.name inv.moduleName)
          else if SymName.isNativeReductionAxiom ci.name then
            let okProv := cfg.allowProvisionalNative &&
              inv.role == .proof && ci.name != SymName.trustCompilerName
            if !okProv then
              throw (.forbiddenNativeReductionAxiom ci.name ci.name)
          else if inv.role == .foundation && SymName.isFoundationalAxiom ci.name then
            pure ()
          else if inv.role == .assumptions && cfg.allowAssumptions then
            pure ()
          else if inv.role == .test then
            pure ()
          else
            throw (.forbiddenAxiom ci.name ci.name inv.moduleName)

/-- Direct constant-closure walk and statement-vs-proof origin separation on all roots (`V05`, `V06`). -/
def auditPackageClosures (cfg : AuditConfig) (pkg : PackageAuditInput) (allEnv : KernelEnv) :
    Except AuditFailure (List SymName) := do
  let mut allReachedAxioms : List SymName := []
  for inv in pkg.modules do
    if inv.role != .test then
      for ci in inv.constants do
        if !isCodegenUnsafeRecInMod inv ci then
          let axs ← auditDirectClosure cfg pkg allEnv ci.name
          allReachedAxioms := axs ++ allReachedAxioms
  for root in pkg.verifyRoots do
    match allEnv.lookup root with
    | none => throw (.unknownConstant root)
    | some ci =>
      if ci.kind != .thmDecl then
        throw (.invalidVerifyRoot root "verify root must be a theorem")
      if ci.type.getAppFn != .const SymName.verificationResultName then
        throw (.invalidVerifyRoot root "verify root must have VerificationResult type")
      let typeEdges ← ExprSkeleton.expressionEdges root ci.type
      checkStatementOriginsFuel pkg allEnv root (allEnv.length + 2) typeEdges []
      let axs ← auditDirectClosure cfg pkg allEnv root
      allReachedAxioms := axs ++ allReachedAxioms
  for root in pkg.claimRoots do
    match allEnv.lookup root with
    | none => throw (.unknownConstant root)
    | some ci =>
      if ci.kind != .thmDecl then
        throw (.invalidVerifyRoot root "claim root must be a theorem")
      let typeEdges ← ExprSkeleton.expressionEdges root ci.type
      checkStatementOriginsFuel pkg allEnv root (allEnv.length + 2) typeEdges []
      let axs ← auditDirectClosure cfg pkg allEnv root
      allReachedAxioms := axs ++ allReachedAxioms
  return allReachedAxioms

/-- Validate every module's replay inventory and source defense-in-depth scanner. -/
def auditAllInventoriesAndSources (cfg : AuditConfig) (mods : List ModuleInventory) :
    Except AuditFailure Unit :=
  checkEach mods fun inv => do
    validateReplayInventory inv
    if let some src := inv.sourceText? then
      SourceScanner.scanSourceDefenseInDepth cfg inv.moduleName inv.role src

/-- Validate extension tables and suffix shadowing across all modules. -/
def auditAllModuleExtensions (cfg : AuditConfig) (mods : List ModuleInventory)
    (protectedNames : List SymName) : Except AuditFailure Unit :=
  checkEach mods fun inv => validateModuleExtensions cfg inv protectedNames

/--
Complete hardened `.olean` replay-key, extension, source, axiom-closure, statement-origin, and
clean-environment kernel replay pipeline (`auditAndReplayPackage`).
-/
def auditAndReplayPackage (cfg : AuditConfig) (pkg : PackageAuditInput) :
    Except AuditFailure AuditCertificate := do
  -- 1. Validate every module's `.olean` parts, role, inventory bijection, mutual `.all`, and source scan
  auditAllInventoriesAndSources cfg pkg.modules
  -- 2. Validate global uniqueness across baseEnv + all modules (zero shadowing / zero overwrites)
  let baseNames := pkg.baseEnv.map ConstantRecord.name
  let allModNames := pkg.modules.flatMap ModuleInventory.constNames
  if hasDuplicates (baseNames ++ allModNames) then
    throw (.duplicateConstName .anonymous .anonymous)
  -- 3. Validate imports (`V14`: forbid `import all` & private-instance leakage)
  validateImports pkg
  -- 4. Validate extension tables & suffix shadowing (`V01`, `V02`, `V07`, `V08`, `V10`–`V13`, `V15`, `V16`)
  let protectedNames := collectProtectedNames pkg
  auditAllModuleExtensions cfg pkg.modules protectedNames
  -- 5. Build exact imported environment and verify `extraConstNames` provenance
  let baseKernelEnv := mkBaseKernelEnv pkg.baseEnv
  let importedEnv := KernelEnv.finalizeImportedEnv pkg.modules
  let allEnv := importedEnv ++ baseKernelEnv
  auditExtraConstProvenance pkg allEnv
  -- 6. Module-wide declaration safety & axiom audit (defeating `V04_unref_axiom` & `pillar_1`)
  auditModuleDeclarations cfg pkg
  -- 7. Direct constant-closure walk on all non-test declarations + verify/claim roots (`V05`, `V06`)
  let allReachedAxioms ← auditPackageClosures cfg pkg allEnv
  -- 8. Clean-environment kernel replay (`V03`, `V09`, `lean4#16677`, `TrustedBoundary` overwrite)
  let replayDecls := collectReplayDecls pkg
  let allowAxiom := cfg.allowAssumptions || cfg.allowProvisionalNative
  let replayedEnv ← replayCleanEnv baseKernelEnv cfg.kernelFuel allowAxiom replayDecls
  return {
    replayedEnv := replayedEnv
    importedEnv := importedEnv
    replayedCount := replayDecls.length
    verifiedRoots := pkg.verifyRoots
    reachedAxioms := allReachedAxioms
  }

/-! ### Section 8.1: Core Section 3.3 Inventory, Mutual `.all`, Closure, & End-to-End Soundness Theorems -/

/-- Helper: unzipping `zip` when lengths match and every pair satisfies `p.1 = p.2.name`. -/
theorem zip_keys_eq_map_name {ns : List SymName} {cs : List ConstantRecord}
    (hlen : ns.length = cs.length)
    (hpair : ∀ p ∈ ns.zip cs, p.1 = p.2.name) :
    ns = cs.map ConstantRecord.name := by
  induction ns generalizing cs with
  | nil =>
    cases cs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons n ntl ih =>
    cases cs with
    | nil => simp at hlen
    | cons c ctl =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hhd : n = c.name := hpair (n, c) (by simp)
      have htl : ∀ p ∈ ntl.zip ctl, p.1 = p.2.name := fun p hp =>
        hpair p (by simp [hp])
      simp only [List.map_cons, hhd, ih hlen htl]

/-- Helper: lookup in `zip ns cs` when `ns = cs.map (·.name)` equals `findConstByName cs`. -/
theorem lookup_zip_eq_findConstByName {ns : List SymName} {cs : List ConstantRecord}
    (heq : ns = cs.map ConstantRecord.name) (k : SymName) :
    KernelEnv.lookup (ns.zip cs) k = findConstByName cs k := by
  subst heq
  induction cs with
  | nil => rfl
  | cons c ctl ih =>
    simp only [List.map_cons, List.zip_cons_cons, KernelEnv.lookup, findConstByName, List.find?_cons]
    by_cases hk : c.name = k
    · subst hk; simp
    · have h1 : (c.name == k) = false := beq_false_of_ne hk
      simp only [h1, Bool.false_eq_true, ↓reduceIte]
      exact ih

/-- Helper: extract every validation invariant from `validateReplayInventory inv = .ok ()`. -/
theorem validateReplayInventory_elim {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) :
    validateOleanParts inv = .ok () ∧
    validateModuleRole inv = .ok () ∧
    inv.constNames.length = inv.constants.length ∧
    inv.replayMap = inv.constNames.zip inv.constants ∧
    inv.constNames.Nodup ∧
    (∀ p ∈ inv.replayMap,
      p.1.isAnonymous = false ∧ p.2.name.isAnonymous = false ∧
      p.1 = p.2.name ∧
      (p.2.hasValue = true → p.2.value?.isSome = true) ∧
      (p.2.originModule = inv.moduleName ∨ SymName.isReservedAuxName p.2.name = true)) ∧
    validateMutualAll inv = .ok () := by
  unfold validateReplayInventory at h
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  cases ho : validateOleanParts inv with
  | error _ => rw [ho] at h; cases h
  | ok uo =>
    cases uo; rw [ho] at h; dsimp only at h
    cases hr : validateModuleRole inv with
    | error _ => rw [hr] at h; cases h
    | ok ur =>
      cases ur; rw [hr] at h; dsimp only at h
      split at h; · cases h
      rename_i hlenNot
      have hlen : inv.constNames.length = inv.constants.length := by
        by_cases he : inv.constNames.length = inv.constants.length
        · exact he
        · exfalso; apply hlenNot; simp [he]
      split at h; · cases h
      rename_i hmapNot
      have hmap : inv.replayMap = inv.constNames.zip inv.constants := by
        by_cases he : inv.replayMap = inv.constNames.zip inv.constants
        · exact he
        · exfalso; apply hmapNot; simp [he]
      split at h; · cases h
      rename_i hdupNot
      have hnodup : inv.constNames.Nodup := by
        cases hd : hasDuplicates inv.constNames
        · exact (hasDuplicates_eq_false_iff_nodup inv.constNames).mp hd
        · exact absurd hd hdupNot
      cases hloop : checkEach inv.replayMap (validateReplayEntry inv.moduleName) with
      | error _ => rw [hloop] at h; cases h
      | ok ul =>
        cases ul; rw [hloop] at h; dsimp only at h
        have hpairs := checkEach_ok_mem hloop
        refine ⟨rfl, rfl, hlen, hmap, hnodup, ?_, h⟩
        intro p hp
        rcases p with ⟨k, ci⟩
        have hpi := hpairs (k, ci) hp
        unfold validateReplayEntry at hpi
        dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hpi
        split at hpi; · cases hpi
        rename_i hanon
        have hkAnon : k.isAnonymous = false ∧ ci.name.isAnonymous = false := by
          cases h1 : k.isAnonymous <;> cases h2 : ci.name.isAnonymous
          · exact ⟨rfl, rfl⟩
          · exfalso; apply hanon; simp [h2]
          · exfalso; apply hanon; simp [h1]
          · exfalso; apply hanon; simp [h1]
        split at hpi; · cases hpi
        rename_i hneKey
        have hkeyEq : k = ci.name := by
          by_cases he : k = ci.name
          · exact he
          · exfalso; apply hneKey; simp [he]
        split at hpi; · cases hpi
        rename_i hvalMiss
        have hvalOk : ci.hasValue = true → ci.value?.isSome = true := by
          intro hhv
          cases hv : ci.value? with
          | some _ => rfl
          | none => exfalso; apply hvalMiss; simp [hhv, hv]
        split at hpi; · cases hpi
        rename_i horigBad
        have horigOk : ci.originModule = inv.moduleName ∨ SymName.isReservedAuxName ci.name = true := by
          by_cases ho1 : ci.originModule = inv.moduleName
          · exact Or.inl ho1
          · cases hr1 : SymName.isReservedAuxName ci.name
            · exfalso; apply horigBad; simp [ho1, hr1]
            · exact Or.inr rfl
        exact ⟨hkAnon.1, hkAnon.2, hkeyEq, hvalOk, horigOk⟩

/-- Theorem 3.3.1a: Validated inventory has equal `constNames`/`constants` lengths and exact `replayMap`. -/
theorem validInventory_length_eq {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) :
    inv.constNames.length = inv.constants.length ∧
    inv.replayMap = inv.constNames.zip inv.constants := by
  have ⟨_, _, hlen, hmap, _, _, _⟩ := validateReplayInventory_elim h
  exact ⟨hlen, hmap⟩

/-- Theorem 3.3.1b: Validated inventory has duplicate-free `constNames`. -/
theorem validInventory_constNames_nodup {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) :
    inv.constNames.Nodup :=
  (validateReplayInventory_elim h).2.2.2.2.1

/-- Theorem 3.3.1c: Every pair in `inv.replayMap` satisfies `p.1 = p.2.name`, and `constNames = constants.map (·.name)`. -/
theorem validInventory_key_eq_ci_name {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) :
    (∀ p ∈ inv.replayMap, p.1 = p.2.name) ∧
    inv.constNames = inv.constants.map ConstantRecord.name := by
  have ⟨_, _, hlen, hmap, _, hpairs, _⟩ := validateReplayInventory_elim h
  have h1 : ∀ p ∈ inv.replayMap, p.1 = p.2.name := fun p hp => (hpairs p hp).2.2.1
  have h2 : ∀ p ∈ inv.constNames.zip inv.constants, p.1 = p.2.name := by
    rw [← hmap]; exact h1
  exact ⟨h1, zip_keys_eq_map_name hlen h2⟩

/--
Theorem 3.3.1d (Inventory Lookup Bijection — Zero Overwrites, Zero Key-Name Aliasing):
Lookup by map key `n` in `inv.replayMap` and in `finalizeImportedEnv [inv]` is extensionally
identical to lookup by `ci.name` in `inv.constants`!
-/
theorem validInventory_lookup_bijection {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) (n : SymName) :
    KernelEnv.lookup inv.replayMap n = findConstByName inv.constants n ∧
    KernelEnv.lookup (KernelEnv.finalizeImportedEnv [inv]) n = findConstByName inv.constants n := by
  have ⟨_, hmap⟩ := validInventory_length_eq h
  have ⟨_, hnames⟩ := validInventory_key_eq_ci_name h
  have hbi := lookup_zip_eq_findConstByName hnames n
  refine ⟨by rw [hmap]; exact hbi, ?_⟩
  simp only [KernelEnv.finalizeImportedEnv, List.foldl_cons, List.foldl_nil, List.nil_append]
  exact hbi

/--
Theorem 3.3.2 (Mutual `.all` Integrity — `lowmem_lean` `cl/1027843093`):
Every mutual-bearing constant in a validated inventory has non-empty, duplicate-free, non-anonymous
`.all`, and for `defnDecl`/`thmDecl`/`opaqueDecl`/`inductDecl` contains `ci.name` and is closed
symmetrically across peers of matching `DeclKind.tag` in `inv.constants`, with every peer
included in `ConstantRecord.declarationEdges`.
-/
theorem validInventory_mutual_all_wf {inv : ModuleInventory}
    (h : validateReplayInventory inv = .ok ()) :
    ∀ ci ∈ inv.constants,
      ci.kind.carriesMutualAll = true →
      ci.all ≠ [] ∧
      ci.all.Nodup ∧
      (∀ a ∈ ci.all, a.isAnonymous = false) ∧
      (∀ edges, ConstantRecord.declarationEdges ci = .ok edges → ∀ a ∈ ci.all, a ∈ edges) ∧
      (match ci.kind with
       | .recDecl _ => True
       | _ =>
         ci.name ∈ ci.all ∧
         ∀ peerName ∈ ci.all,
           ∃ peerCi, findConstByName inv.constants peerName = some peerCi ∧
             peerCi.kind.tag = ci.kind.tag ∧
             peerCi.all = ci.all) := by
  have hmut := (validateReplayInventory_elim h).2.2.2.2.2.2
  unfold validateMutualAll at hmut
  have hmem := checkEach_ok_mem hmut
  intro ci hci hcarries
  have hstep := hmem ci hci
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hstep
  simp only [hcarries, ↓reduceIte] at hstep
  split at hstep; · cases hstep
  rename_i hnotEmpty
  have hne : ci.all ≠ [] := by
    intro he; apply hnotEmpty; simp [he]
  split at hstep; · cases hstep
  rename_i hnotDup
  have hnd : ci.all.Nodup := by
    cases hd : hasDuplicates ci.all
    · exact (hasDuplicates_eq_false_iff_nodup ci.all).mp hd
    · exact absurd hd hnotDup
  split at hstep; · cases hstep
  rename_i hnotAnon
  have hnoAnon : ∀ a ∈ ci.all, a.isAnonymous = false := by
    intro a ha
    cases hia : a.isAnonymous
    · rfl
    · exfalso; apply hnotAnon
      exact List.any_eq_true.mpr ⟨a, ha, hia⟩
  have hEdgesAll : ∀ edges, ConstantRecord.declarationEdges ci = .ok edges → ∀ a ∈ ci.all, a ∈ edges := by
    intro edges hedges a ha
    unfold ConstantRecord.declarationEdges at hedges
    dsimp only [bind, Except.bind, pure, Except.pure] at hedges
    cases hte : ExprSkeleton.expressionEdges ci.name ci.type with
    | error _ => rw [hte] at hedges; cases hedges
    | ok te =>
      rw [hte] at hedges; dsimp only at hedges
      -- Regardless of `ci.value?`, each `carriesMutualAll` kind appends `ci.all` into `result`
      cases hval : ci.value? with
      | none =>
        rw [hval] at hedges; dsimp only at hedges
        cases hk : ci.kind <;> rw [hk] at hcarries hedges
        all_goals try cases hcarries
        all_goals try (injection hedges with heq; subst heq; simp [ha])
        · rename_i rules
          exact ConstantRecord.recRuleEdges_preserves ci.name rules hedges a (List.mem_append_right _ ha)
      | some v =>
        rw [hval] at hedges; dsimp only at hedges
        cases hve : ExprSkeleton.expressionEdges ci.name v with
        | error _ => rw [hve] at hedges; cases hedges
        | ok ve =>
          rw [hve] at hedges; dsimp only at hedges
          cases hk : ci.kind <;> rw [hk] at hcarries hedges
          all_goals try cases hcarries
          all_goals try (injection hedges with heq; subst heq; simp [ha])
          · rename_i rules
            exact ConstantRecord.recRuleEdges_preserves ci.name rules hedges a (List.mem_append_right _ ha)
  refine ⟨hne, hnd, hnoAnon, hEdgesAll, ?_⟩
  cases hk : ci.kind with
  | recDecl _ => trivial
  | axiomDecl | quotDecl | ctorDecl _ => rw [hk] at hcarries; cases hcarries
  | defnDecl | thmDecl | opaqueDecl | inductDecl _ =>
    rw [hk] at hstep; dsimp only at hstep
    split at hstep; · cases hstep
    rename_i hnotMemSelf
    have hself : ci.name ∈ ci.all := by
      by_cases hm : ci.name ∈ ci.all
      · exact hm
      · exfalso; apply hnotMemSelf; simp [hm]
    cases hploop : checkEach ci.all (validateMutualPeer inv ci) with
    | error _ => rw [hploop] at hstep; cases hstep
    | ok _ =>
      have hpeers := checkEach_ok_mem hploop
      refine ⟨hself, fun peerName hpMem => ?_⟩
      have hpOk := hpeers peerName hpMem
      unfold validateMutualPeer at hpOk
      dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hpOk
      cases hfind : findConstByName inv.constants peerName with
      | none => rw [hfind] at hpOk; cases hpOk
      | some peerCi =>
        rw [hfind] at hpOk; dsimp only at hpOk
        split at hpOk; · cases hpOk
        rename_i htagNot
        have htagEq : peerCi.kind.tag = ci.kind.tag := by
          by_cases he : peerCi.kind.tag = ci.kind.tag
          · exact he
          · exfalso; apply htagNot; simp [he]
        split at hpOk; · cases hpOk
        rename_i hallNot
        have hallEq : peerCi.all = ci.all := by
          by_cases he : peerCi.all = ci.all
          · exact he
          · exfalso; apply hallNot; simp [he]
        exact ⟨peerCi, rfl, by rw [← hk]; exact htagEq, hallEq⟩

/--
Theorem 3.3.3 (Direct Axiom, Native-Reduction `pillar_1`, & Statement-Origin Soundness):
If `auditDirectClosure` succeeds under unconditional config (`allowAssumptions = false`,
`allowProvisionalNative = false`), then every constant `dep` visited in the direct transitive
dependency graph (ignoring `cachedExportedAxioms`) is safe (non-unsafe, non-partial), and if it
is an axiom it is NEVER `sorryAx`, NEVER a native-reduction/compiler-trust axiom
(`ofReduceBool`, `ofReduceNat`, `trustCompiler`, `._native.*`), and MUST be one of Lean's 3
foundational axioms `{propext, Quot.sound, Classical.choice}` from a `.foundation` module.
-/
theorem validPackage_axiom_closure_sound {cfg : AuditConfig} {pkg : PackageAuditInput}
    {allEnv : KernelEnv} {rootName : SymName} {reached : List SymName}
    (hNoAssump : cfg.allowAssumptions = false)
    (hNoProv : cfg.allowProvisionalNative = false)
    (hAudit : auditDirectClosure cfg pkg allEnv rootName = .ok reached) :
    ∃ visited,
      walkEdgesFuel allEnv (allEnv.length + 2) [rootName] [] = .ok visited ∧
      ∀ dep ∈ visited,
        ∃ depCi, allEnv.lookup dep = some depCi ∧
          depCi.isUnsafe = false ∧ depCi.isPartial = false ∧
          (depCi.isAxiom = true →
            dep ≠ SymName.sorryAxName ∧
            SymName.isNativeReductionAxiom dep = false ∧
            SymName.isFoundationalAxiom dep = true ∧
            roleOfModule pkg depCi.originModule = .foundation) := by
  unfold auditDirectClosure at hAudit
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hAudit
  cases hwalk : walkEdgesFuel allEnv (allEnv.length + 2) [rootName] [] with
  | error _ => rw [hwalk] at hAudit; cases hAudit
  | ok visited =>
    rw [hwalk] at hAudit; dsimp only at hAudit
    refine ⟨visited, rfl, ?_⟩
    -- Prove loop invariant over `visited`
    have hloop : ∀ (xs acc res : List SymName),
        checkVisitedClosure cfg pkg allEnv rootName xs acc = .ok res →
        ∀ dep ∈ xs,
          ∃ depCi, allEnv.lookup dep = some depCi ∧
            depCi.isUnsafe = false ∧ depCi.isPartial = false ∧
            (depCi.isAxiom = true →
              dep ≠ SymName.sorryAxName ∧
              SymName.isNativeReductionAxiom dep = false ∧
              SymName.isFoundationalAxiom dep = true ∧
              roleOfModule pkg depCi.originModule = .foundation) := by
      intro xs
      induction xs with
      | nil => intro _ _ _ _ hm; cases hm
      | cons d tl ih =>
        intro acc res hr dep hmem
        unfold checkVisitedClosure at hr
        dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hr
        cases hlu : allEnv.lookup d with
        | none => rw [hlu] at hr; cases hr
        | some dCi =>
          rw [hlu] at hr; dsimp only at hr
          split at hr; · cases hr
          rename_i hnotUP
          have hsafe : dCi.isUnsafe = false ∧ dCi.isPartial = false := by
            cases hu : dCi.isUnsafe <;> cases hp : dCi.isPartial
            · exact ⟨rfl, rfl⟩
            · exfalso; apply hnotUP; simp [hp]
            · exfalso; apply hnotUP; simp [hu]
            · exfalso; apply hnotUP; simp [hu]
          split at hr
          · rename_i hax
            split at hr; · cases hr
            rename_i hnotSorry
            split at hr
            · simp only [hNoProv, Bool.false_and, Bool.not_false, ↓reduceIte] at hr
              cases hr
            · rename_i hnotNat
              split at hr
              · rename_i hfound
                simp only [Bool.and_eq_true, beq_iff_eq] at hfound
                cases hmem with
                | head =>
                  refine ⟨dCi, hlu, hsafe.1, hsafe.2, fun _ => ?_⟩
                  refine ⟨fun hs => hnotSorry (by simp [hs]), ?_, hfound.1, hfound.2⟩
                  cases hn : SymName.isNativeReductionAxiom d
                  · rfl
                  · exact absurd hn hnotNat
                | tail _ htl => exact ih (d :: acc) res hr dep htl
              · simp only [hNoAssump, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hr
                cases hr
          · rename_i hnotAx
            cases hmem with
            | head =>
              exact ⟨dCi, hlu, hsafe.1, hsafe.2, fun ha => absurd ha hnotAx⟩
            | tail _ htl => exact ih acc res hr dep htl
    exact hloop visited [] reached hAudit

/-- Helper: every entry `(n, ci)` in `finalizeImportedEnv mods` comes from some module's `constNames.zip constants`. -/
theorem finalizeImportedEnv_mem_exists_mod (mods : List ModuleInventory) (p : SymName × ConstantRecord)
    (hmem : p ∈ KernelEnv.finalizeImportedEnv mods) :
    ∃ inv ∈ mods, p ∈ inv.constNames.zip inv.constants := by
  have hgen : ∀ (acc : KernelEnv) (ms : List ModuleInventory),
      p ∈ ms.foldl (fun a inv => a ++ inv.constNames.zip inv.constants) acc →
      p ∈ acc ∨ ∃ inv ∈ ms, p ∈ inv.constNames.zip inv.constants := by
    intro acc ms
    induction ms generalizing acc with
    | nil => intro h; exact Or.inl h
    | cons m rest ih =>
      intro h
      simp only [List.foldl_cons] at h
      rcases ih (acc ++ m.constNames.zip m.constants) h with h1 | ⟨inv, hinv, hp⟩
      · rcases List.mem_append.mp h1 with hacc | hm
        · exact Or.inl hacc
        · exact Or.inr ⟨m, List.mem_cons_self, hm⟩
      · exact Or.inr ⟨inv, List.mem_cons_of_mem _ hinv, hp⟩
  rcases hgen [] mods hmem with hnil | hex
  · cases hnil
  · exact hex

/--
Theorem 3.3.4 (End-to-End Clean-Env Kernel Replay Soundness Theorem):
If `auditAndReplayPackage cfg pkg = .ok cert`, then:
1. Every module in `pkg.modules` satisfies `validateReplayInventory`, intact `.olean` parts,
   strict module role, source defense-in-depth, import restrictions (`V14`), and extension/shadowing
   rules (`V01`–`V18`).
2. Every constant `ci` accessible in `cert.importedEnv` at any key `n` satisfies `ci.name = n`
   (zero key-name mismatch, zero `lean4#16677` / `TrustedBoundary` overwrite aliasing).
3. When `cfg.allowAssumptions = false`, `cfg.allowProvisionalNative = false`, and `pkg.baseEnv`
   admits a sound semantic model `EnvSound (mkBaseKernelEnv pkg.baseEnv) M`:
   - `cert.replayedEnv` admits a sound semantic model `M'`;
   - **NO** constant accessible in `cert.replayedEnv` has type `False`;
   - **NO** constant accessible in `cert.importedEnv` (even including verified safe `_unsafe_rec`
     codegen companions!) has type `False`!
-/
theorem auditAndReplayPackage_sound {cfg : AuditConfig} {pkg : PackageAuditInput}
    {cert : AuditCertificate}
    (hAudit : auditAndReplayPackage cfg pkg = .ok cert) :
    (∀ inv ∈ pkg.modules,
      validateReplayInventory inv = .ok () ∧
      validateOleanParts inv = .ok () ∧
      validateModuleRole inv = .ok () ∧
      (∀ src, inv.sourceText? = some src →
        SourceScanner.scanSourceDefenseInDepth cfg inv.moduleName inv.role src = .ok ()) ∧
      validateModuleExtensions cfg inv (collectProtectedNames pkg) = .ok ()) ∧
    validateImports pkg = .ok () ∧
    (∀ n ci, cert.importedEnv.lookup n = some ci → ci.name = n) ∧
    (cfg.allowAssumptions = false →
     cfg.allowProvisionalNative = false →
     ∀ M : SymName → SemVal,
       EnvSound (mkBaseKernelEnv pkg.baseEnv) M →
       (∃ M' : SymName → SemVal, EnvSound cert.replayedEnv M') ∧
       (∀ n ci, cert.replayedEnv.lookup n = some ci → ci.type ≠ .const SymName.falseName) ∧
       (∀ n ci, cert.importedEnv.lookup n = some ci → ci.type ≠ .const SymName.falseName)) := by
  unfold auditAndReplayPackage at hAudit
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hAudit
  cases hstep1 : auditAllInventoriesAndSources cfg pkg.modules with
  | error _ => rw [hstep1] at hAudit; cases hAudit
  | ok u1 =>
    cases u1; rw [hstep1] at hAudit; dsimp only at hAudit
    unfold auditAllInventoriesAndSources at hstep1
    have hmod1 := checkEach_ok_mem hstep1
    have hinvValid : ∀ inv ∈ pkg.modules,
        validateReplayInventory inv = .ok () ∧
        (∀ src, inv.sourceText? = some src →
          SourceScanner.scanSourceDefenseInDepth cfg inv.moduleName inv.role src = .ok ()) := by
      intro inv hinv
      have h1 := hmod1 inv hinv
      dsimp only [bind, Except.bind, pure, Except.pure] at h1
      cases hv : validateReplayInventory inv with
      | error _ => rw [hv] at h1; cases h1
      | ok uv =>
        cases uv; rw [hv] at h1; dsimp only at h1
        refine ⟨rfl, fun src hsrc => ?_⟩
        rw [hsrc] at h1; exact h1
    split at hAudit; · cases hAudit
    cases hstep3 : validateImports pkg with
    | error _ => rw [hstep3] at hAudit; cases hAudit
    | ok u3 =>
      cases u3; rw [hstep3] at hAudit; dsimp only at hAudit
      cases hstep4 : auditAllModuleExtensions cfg pkg.modules (collectProtectedNames pkg) with
      | error _ => rw [hstep4] at hAudit; cases hAudit
      | ok u4 =>
        cases u4; rw [hstep4] at hAudit; dsimp only at hAudit
        unfold auditAllModuleExtensions at hstep4
        have hmodExt := checkEach_ok_mem hstep4
        cases hstep5 : auditExtraConstProvenance pkg
            (KernelEnv.finalizeImportedEnv pkg.modules ++ mkBaseKernelEnv pkg.baseEnv) with
        | error _ => rw [hstep5] at hAudit; cases hAudit
        | ok u5 =>
          cases u5; rw [hstep5] at hAudit; dsimp only at hAudit
          cases hstep6 : auditModuleDeclarations cfg pkg with
          | error _ => rw [hstep6] at hAudit; cases hAudit
          | ok u6 =>
            cases u6; rw [hstep6] at hAudit; dsimp only at hAudit
            cases hstep7 : auditPackageClosures cfg pkg
                (KernelEnv.finalizeImportedEnv pkg.modules ++ mkBaseKernelEnv pkg.baseEnv) with
            | error _ => rw [hstep7] at hAudit; cases hAudit
            | ok axs =>
              rw [hstep7] at hAudit; dsimp only at hAudit
              cases hstep8 : replayCleanEnv (mkBaseKernelEnv pkg.baseEnv) cfg.kernelFuel
                  (cfg.allowAssumptions || cfg.allowProvisionalNative)
                  (collectReplayDecls pkg) with
              | error _ => rw [hstep8] at hAudit; cases hAudit
              | ok repEnv =>
                rw [hstep8] at hAudit
                injection hAudit with hcert
                subst hcert
                refine ⟨?_, rfl, ?_, ?_⟩
                · intro inv hinv
                  have ⟨hv, hsrc⟩ := hinvValid inv hinv
                  have ⟨ho, hr, _, _, _, _, _⟩ := validateReplayInventory_elim hv
                  exact ⟨hv, ho, hr, hsrc, hmodExt inv hinv⟩
                · intro n ci hlu
                  have hmem := KernelEnv.lookup_mem hlu
                  rcases finalizeImportedEnv_mem_exists_mod pkg.modules (n, ci) hmem with ⟨inv, hinv, hzip⟩
                  have hv := (hinvValid inv hinv).1
                  have ⟨_, hmap⟩ := validInventory_length_eq hv
                  have ⟨hkey, _⟩ := validInventory_key_eq_ci_name hv
                  rw [← hmap] at hzip
                  exact (hkey (n, ci) hzip).symm
                · intro hNoA hNoP M hBaseM
                  have hrep := hstep8
                  simp only [hNoA, hNoP, Bool.or_self] at hrep
                  rcases replayCleanEnv_preserves_sound hBaseM cfg.kernelFuel _ hrep with ⟨M', hM'⟩
                  have hnoFalseRep := kernelEnv_no_false hM'
                  refine ⟨⟨M', hM'⟩, hnoFalseRep, ?_⟩
                  intro n ci hlu hty
                  have hmem := KernelEnv.lookup_mem hlu
                  rcases finalizeImportedEnv_mem_exists_mod pkg.modules (n, ci) hmem with ⟨inv, hinv, hzip⟩
                  have hciInInv : ci ∈ inv.constants := List.of_mem_zip hzip |>.2
                  have ⟨_, hcontRep⟩ := replayCleanEnv_contains_decl hrep
                  by_cases hrec : isCodegenUnsafeRecInMod inv ci = true
                  · unfold isCodegenUnsafeRecInMod at hrec
                    split at hrec; · cases hrec
                    cases hpar : ci.name.unsafeRecParent? with
                    | none => rw [hpar] at hrec; cases hrec
                    | some parent =>
                      rw [hpar] at hrec; dsimp only at hrec
                      cases hfind : findConstByName inv.constants parent with
                      | none => rw [hfind] at hrec; cases hrec
                      | some parentCi =>
                        rw [hfind] at hrec
                        simp only [Bool.and_eq_true, beq_iff_eq] at hrec
                        rcases hrec with ⟨⟨hpSafe, _⟩, htypeEq⟩
                        have hpMem : parentCi ∈ inv.constants := List.mem_of_find?_eq_some hfind
                        have hpNotRec : isCodegenUnsafeRecInMod inv parentCi = false := by
                          unfold isCodegenUnsafeRecInMod
                          simp [hpSafe]
                        have hpInCollect : parentCi ∈ collectReplayDecls pkg := by
                          unfold collectReplayDecls
                          exact List.mem_flatMap.mpr ⟨inv, hinv, List.mem_filter.mpr ⟨hpMem, by simp [hpNotRec]⟩⟩
                        have hpInRep := hcontRep parentCi hpInCollect
                        exact hnoFalseRep parentCi.name parentCi hpInRep (htypeEq.symm.trans hty)
                  · have hrecF : isCodegenUnsafeRecInMod inv ci = false := by
                      cases hc : isCodegenUnsafeRecInMod inv ci
                      · rfl
                      · exact absurd hc hrec
                    have hciInCollect : ci ∈ collectReplayDecls pkg := by
                      unfold collectReplayDecls
                      exact List.mem_flatMap.mpr ⟨inv, hinv, List.mem_filter.mpr ⟨hciInInv, by simp [hrecF]⟩⟩
                    have hciInRep := hcontRep ci hciInCollect
                    exact hnoFalseRep ci.name ci hciInRep hty

/-! ## Section 9: Constructive Vulnerability Exploits, 18-Vector Tamper Suite (`V01`–`V18`), & Positive Witnesses -/

/-- Helper to construct a well-formed single-module inventory with aligned `constNames`/`replayMap`. -/
def mkAlignedModule (modName : SymName) (role : ModuleRole) (decls : List ConstantRecord)
    (oleanParts : OleanArtifactParts := {})
    (imports : List ImportSpec := [])
    (extEntries : List EnvExtEntry := [])
    (sourceText? : Option String := none)
    (extraConstNames : List SymName := []) : ModuleInventory := {
  moduleName := modName
  role := role
  oleanParts := oleanParts
  imports := imports
  constNames := decls.map ConstantRecord.name
  constants := decls
  extraConstNames := extraConstNames
  replayMap := decls.map fun ci => (ci.name, ci)
  extEntries := extEntries
  sourceText? := sourceText?
}

/-- Default unconditional strict audit configuration (`allowAssumptions = false`, `allowProvisionalNative = false`). -/
def defaultUnconditionalConfig : AuditConfig := {
  allowAssumptions := false
  allowProvisionalNative := false
  enforceStrictProofs := true
  kernelFuel := 16
}

/-! ### Section 9.1: Operational Vulnerability Exploits (§3.2) -/

/-- Reusable simple inductive `T : Type 0 | T.mk : T` with canonical recursor `T.rec`. -/
def demoModName : SymName := SymName.ofList ["Demo", "Exploit"]
def demoIndName : SymName := SymName.ofList ["Demo", "T"]
def demoCtorName : SymName := SymName.ofList ["Demo", "T", "mk"]
def demoRecName : SymName := SymName.ofList ["Demo", "T", "rec"]
def demoRenamedKey : SymName := SymName.ofList ["Demo", "forgedFalse"]

def demoIndDecl : ConstantRecord := {
  name := demoIndName
  kind := .inductDecl [demoCtorName]
  type := .sort 1
  all := [demoIndName]
  originModule := demoModName
}

def demoCtorDecl : ConstantRecord := {
  name := demoCtorName
  kind := .ctorDecl demoIndName
  type := .const demoIndName
  originModule := demoModName
}

def demoRecDecl : ConstantRecord := {
  name := demoRecName
  kind := .recDecl [{ ctor := demoCtorName, nfields := 0, rhs := .const SymName.trueIntroName }]
  type := canonicalPropRecType demoIndName [demoCtorName]
  all := [demoIndName]
  originModule := demoModName
}

/-- Forged `.recDecl` claiming `type := False` stored under map key `Demo.forgedFalse` with `ci.name := Demo.T.rec`. -/
def forgedRecDecl : ConstantRecord := {
  name := demoRecName
  kind := .recDecl [{ ctor := demoCtorName, nfields := 0, rhs := .const SymName.trueIntroName }]
  type := .const SymName.falseName
  all := [demoIndName]
  originModule := demoModName
}

def issue16675RecInventory : ModuleInventory := {
  moduleName := demoModName
  role := .proof
  constNames := [demoIndName, demoCtorName, demoRecName, demoRenamedKey]
  constants := [demoIndDecl, demoCtorDecl, demoRecDecl, forgedRecDecl]
  replayMap := [
    (demoIndName, demoIndDecl),
    (demoCtorName, demoCtorDecl),
    (demoRecName, demoRecDecl),
    (demoRenamedKey, forgedRecDecl)
  ]
}

/--
Theorem 3.2.1a (`lean4#16677` / `issue16675` recursor key-mismatch bypass):
`naiveLean434Replay` accepts the forged inventory because `postponedRecursors` tracks `ci.name`
(`Demo.T.rec`) instead of map key `Demo.forgedFalse`; meanwhile `finalizeImportedEnv` binds
`Demo.forgedFalse` to a constant of type `False`, and `validateReplayInventory` rejects with `.keyNameMismatch`.
-/
theorem issue16675_recursor_bypass :
    (naiveLean434Replay standardBaseEnv 16 issue16675RecInventory.replayMap).isOk = true ∧
    (KernelEnv.finalizeImportedEnv [issue16675RecInventory]).lookup demoRenamedKey = some forgedRecDecl ∧
    forgedRecDecl.type = .const SymName.falseName ∧
    validateReplayInventory issue16675RecInventory =
      .error (.keyNameMismatch demoModName demoRenamedKey demoRecName) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Forged `.ctorDecl` claiming `type := False` stored under map key `Demo.forgedFalse` with `ci.name := Demo.T.mk`. -/
def forgedCtorDecl : ConstantRecord := {
  name := demoCtorName
  kind := .ctorDecl demoIndName
  type := .const SymName.falseName
  originModule := demoModName
}

def issue16675CtorInventory : ModuleInventory := {
  moduleName := demoModName
  role := .proof
  constNames := [demoIndName, demoCtorName, demoRecName, demoRenamedKey]
  constants := [demoIndDecl, demoCtorDecl, demoRecDecl, forgedCtorDecl]
  replayMap := [
    (demoIndName, demoIndDecl),
    (demoCtorName, demoCtorDecl),
    (demoRecName, demoRecDecl),
    (demoRenamedKey, forgedCtorDecl)
  ]
}

/-- Theorem 3.2.1b (`lean4#16677` constructor key-mismatch bypass). -/
theorem issue16675_ctor_bypass :
    (naiveLean434Replay standardBaseEnv 16 issue16675CtorInventory.replayMap).isOk = true ∧
    (KernelEnv.finalizeImportedEnv [issue16675CtorInventory]).lookup demoRenamedKey = some forgedCtorDecl ∧
    forgedCtorDecl.type = .const SymName.falseName ∧
    validateReplayInventory issue16675CtorInventory =
      .error (.keyNameMismatch demoModName demoRenamedKey demoCtorName) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Forged `.quotDecl` claiming `type := False` stored under map key `Demo.forgedFalse` with `ci.name := Quot`. -/
def forgedQuotDecl : ConstantRecord := {
  name := SymName.quotName
  kind := .quotDecl
  type := .const SymName.falseName
  originModule := demoModName
}

def issue16675QuotInventory : ModuleInventory := {
  moduleName := demoModName
  role := .proof
  constNames := [demoRenamedKey]
  constants := [forgedQuotDecl]
  replayMap := [(demoRenamedKey, forgedQuotDecl)]
}

/-- Theorem 3.2.1c (`lean4#16677` quotient key-mismatch bypass). -/
theorem issue16675_quot_bypass :
    (naiveLean434Replay standardBaseEnv 16 issue16675QuotInventory.replayMap).isOk = true ∧
    (KernelEnv.finalizeImportedEnv [issue16675QuotInventory]).lookup demoRenamedKey = some forgedQuotDecl ∧
    forgedQuotDecl.type = .const SymName.falseName ∧
    validateReplayInventory issue16675QuotInventory =
      .error (.keyNameMismatch demoModName demoRenamedKey SymName.quotName) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Forged duplicate `.thmDecl` short-circuit (`Replay.lean` lines 90–96): aliased key matches header of valid theorem. -/
def validThmName : SymName := SymName.ofList ["Demo", "validThm"]

def validThmDecl : ConstantRecord := {
  name := validThmName
  kind := .thmDecl
  type := .const SymName.trueName
  value? := some (.const SymName.trueIntroName)
  hasValue := true
  all := [validThmName]
  originModule := demoModName
}

def forgedDupThmDecl : ConstantRecord := {
  name := validThmName
  kind := .thmDecl
  type := .const SymName.trueName
  value? := some (.const SymName.falseName) -- ill-typed body skipped because header matches!
  hasValue := true
  all := [validThmName]
  originModule := demoModName
}

def issue16675ThmDupInventory : ModuleInventory := {
  moduleName := demoModName
  role := .proof
  constNames := [validThmName, demoRenamedKey]
  constants := [validThmDecl, forgedDupThmDecl]
  replayMap := [(validThmName, validThmDecl), (demoRenamedKey, forgedDupThmDecl)]
}

/-- Theorem 3.2.1d (`lean4#16677` duplicate `.thmInfo` short-circuit bypass). -/
theorem issue16675_thm_dup_bypass :
    (naiveLean434Replay standardBaseEnv 16 issue16675ThmDupInventory.replayMap).isOk = true ∧
    (KernelEnv.finalizeImportedEnv [issue16675ThmDupInventory]).lookup demoRenamedKey = some forgedDupThmDecl ∧
    validateReplayInventory issue16675ThmDupInventory =
      .error (.keyNameMismatch demoModName demoRenamedKey validThmName) := by
  refine ⟨rfl, rfl, rfl⟩

/--
Pre-fix `TrustedBoundary.lean` (`downstreamAudit` line 408 / `verifyAudit` line 607) overwrite exploit:
`constNames = [Verify.Foo.verified, Verify.Foo.helper]`,
`constants = [ci_forged_verified, ci_benign_verified]`, BOTH having `.name = Verify.Foo.verified`.
-/
def verifyFooModName : SymName := SymName.ofList ["Verify", "Foo"]
def verifyFooThmName : SymName := SymName.ofList ["Verify", "Foo", "verified"]
def verifyFooHelperKey : SymName := SymName.ofList ["Verify", "Foo", "helper"]

def ciForgedVerified : ConstantRecord := {
  name := verifyFooThmName
  kind := .thmDecl
  type := .app (.const SymName.verificationResultName) (.natLit 0)
  value? := some (.const SymName.trueIntroName) -- ILL-TYPED (`True` vs `VerificationResult 0`), yet axiom-free!
  hasValue := true
  all := [verifyFooThmName]
  originModule := verifyFooModName
}

def ciBenignVerified : ConstantRecord := {
  name := verifyFooThmName
  kind := .thmDecl
  type := .const SymName.trueName
  value? := some (.const SymName.trueIntroName)
  hasValue := true
  all := [verifyFooThmName]
  originModule := verifyFooModName
}

def overwriteExploitModule : ModuleInventory := {
  moduleName := verifyFooModName
  role := .verify
  constNames := [verifyFooThmName, verifyFooHelperKey]
  constants := [ciForgedVerified, ciBenignVerified]
  replayMap := [(verifyFooThmName, ciForgedVerified), (verifyFooHelperKey, ciBenignVerified)]
}

def overwriteExploitPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [overwriteExploitModule]
  verifyRoots := [verifyFooThmName]
}

/--
Theorem 3.2.2 (`TrustedBoundary.lean` lines 408 & 607 `replayLocals` overwrite bypass):
1. `ciForgedVerified` genuinely fails `kernelCheckDecl` (ill-typed proof term).
2. `naiveInsertByCiNameAudit` STILL returns `.ok` on `overwriteExploitPkg` because `replayLocals`
   overwrites `Verify.Foo.verified` with `ciBenignVerified`, while `importedEnv` serves `ciForgedVerified`.
3. `validateReplayInventory` and `auditAndReplayPackage` both reject with `.keyNameMismatch`.
-/
theorem trustedBoundary_overwrite_bypass :
    (kernelCheckDecl standardBaseEnv 16 false ciForgedVerified).isOk = false ∧
    (naiveInsertByCiNameAudit overwriteExploitPkg 16).isOk = true ∧
    (KernelEnv.finalizeImportedEnv overwriteExploitPkg.modules).lookup verifyFooThmName =
      some ciForgedVerified ∧
    validateReplayInventory overwriteExploitModule =
      .error (.keyNameMismatch verifyFooModName verifyFooHelperKey verifyFooThmName) ∧
    auditAndReplayPackage defaultUnconditionalConfig overwriteExploitPkg =
      .error (.keyNameMismatch verifyFooModName verifyFooHelperKey verifyFooThmName) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Section 9.2: `lowmem_lean` (`cl/1027843093`) Mutual `.all` Acceptance & Malformed Rejections -/

def mutualModName : SymName := SymName.ofList ["Proof", "Parity"]
def evenNonnegName : SymName := SymName.ofList ["Proof", "Parity", "even_nonneg"]
def oddNonnegName : SymName := SymName.ofList ["Proof", "Parity", "odd_nonneg"]

def evenNonnegDecl : ConstantRecord := {
  name := evenNonnegName
  kind := .thmDecl
  type := .const SymName.trueName
  value? := some (.const SymName.trueIntroName)
  hasValue := true
  all := [evenNonnegName, oddNonnegName]
  originModule := mutualModName
}

def oddNonnegDecl : ConstantRecord := {
  name := oddNonnegName
  kind := .thmDecl
  type := .const SymName.trueName
  value? := some (.const SymName.trueIntroName)
  hasValue := true
  all := [evenNonnegName, oddNonnegName]
  originModule := mutualModName
}

def validMutualThmModule : ModuleInventory :=
  mkAlignedModule mutualModName .proof [evenNonnegDecl, oddNonnegDecl]

def validMutualThmPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [validMutualThmModule]
}

/--
Theorem 3.2.3a (`lowmem_lean` `cl/1027843093`):
`naiveSingleAllCheck` falsely rejects a valid 2-theorem mutual block, whereas
`validateReplayInventory` and `auditAndReplayPackage` soundly accept it.
-/
theorem mutual_thm_false_rejection_and_sound_acceptance :
    (naiveSingleAllCheck validMutualThmModule).isOk = false ∧
    validateReplayInventory validMutualThmModule = .ok () ∧
    (auditAndReplayPackage defaultUnconditionalConfig validMutualThmPkg).isOk = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- Malformed `.all` cases (all 7 rejected constructively by `validateReplayInventory` / `auditAndReplayPackage`). -/
def malformedAllEmptyMod : ModuleInventory :=
  mkAlignedModule mutualModName .proof [{ evenNonnegDecl with all := [] }]

def malformedAllDupMod : ModuleInventory :=
  mkAlignedModule mutualModName .proof [{ evenNonnegDecl with all := [evenNonnegName, evenNonnegName] }]

def malformedAllAnonMod : ModuleInventory :=
  mkAlignedModule mutualModName .proof [{ evenNonnegDecl with all := [evenNonnegName, .anonymous] }]

def malformedAllMissingSelfMod : ModuleInventory :=
  mkAlignedModule mutualModName .proof [{ evenNonnegDecl with all := [oddNonnegName] }, oddNonnegDecl]

def malformedAllAsymMod : ModuleInventory :=
  mkAlignedModule mutualModName .proof [evenNonnegDecl, { oddNonnegDecl with all := [oddNonnegName] }]

def malformedAllMissingPeerMod : ModuleInventory :=
  mkAlignedModule mutualModName .proof [evenNonnegDecl]

def malformedAllIncompatKindMod : ModuleInventory :=
  mkAlignedModule mutualModName .proof [evenNonnegDecl, { oddNonnegDecl with kind := .defnDecl }]

def sorryAxDecl : ConstantRecord := {
  name := SymName.sorryAxName
  kind := .axiomDecl
  type := .const SymName.falseName
  originModule := SymName.ofList ["Init", "Prelude"]
}

def hiddenSorryMutualMod : ModuleInventory :=
  mkAlignedModule mutualModName .proof [
    evenNonnegDecl,
    { oddNonnegDecl with value? := some (.app (.lam (.const SymName.falseName) (.const SymName.trueIntroName)) (.const SymName.sorryAxName)) }
  ]

def hiddenSorryMutualPkg : PackageAuditInput := {
  baseEnv := sorryAxDecl :: standardBaseDecls
  modules := [hiddenSorryMutualMod]
}

theorem malformedAll_all_seven_rejected :
    validateReplayInventory malformedAllEmptyMod =
      .error (.invalidMutualAll mutualModName evenNonnegName "empty .all list") ∧
    validateReplayInventory malformedAllDupMod =
      .error (.invalidMutualAll mutualModName evenNonnegName "duplicate entry in .all") ∧
    validateReplayInventory malformedAllAnonMod =
      .error (.invalidMutualAll mutualModName evenNonnegName "anonymous name in .all") ∧
    validateReplayInventory malformedAllMissingSelfMod =
      .error (.invalidMutualAll mutualModName evenNonnegName "ci.name missing from .all") ∧
    validateReplayInventory malformedAllAsymMod =
      .error (.invalidMutualAll mutualModName evenNonnegName "asymmetric mutual .all membership") ∧
    validateReplayInventory malformedAllMissingPeerMod =
      .error (.invalidMutualAll mutualModName evenNonnegName "missing mutual peer in inventory") ∧
    validateReplayInventory malformedAllIncompatKindMod =
      .error (.invalidMutualAll mutualModName evenNonnegName "incompatible mutual peer kind") ∧
    auditDirectClosure defaultUnconditionalConfig hiddenSorryMutualPkg
      (KernelEnv.finalizeImportedEnv hiddenSorryMutualPkg.modules ++ mkBaseKernelEnv hiddenSorryMutualPkg.baseEnv)
      evenNonnegName =
      .error (.forbiddenAxiom evenNonnegName SymName.sorryAxName (SymName.ofList ["Init", "Prelude"])) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Section 9.3: `pillar_1` (`cl/1027950821`) Native-Reduction & Compiler-Trust Axiom Bans -/

def pillarProofMod : SymName := SymName.ofList ["Proof", "Native"]
def pillarThmName : SymName := SymName.ofList ["Proof", "Native", "usesNative"]

def mkNativeAxiomPkg (axName : SymName) (axOrigin : SymName) : PackageAuditInput :=
  let axDecl : ConstantRecord := {
    name := axName
    kind := .axiomDecl
    type := .const SymName.trueName
    originModule := axOrigin
  }
  let thmDecl : ConstantRecord := {
    name := pillarThmName
    kind := .thmDecl
    type := .const SymName.trueName
    value? := some (.const axName)
    hasValue := true
    all := [pillarThmName]
    originModule := pillarProofMod
  }
  {
    baseEnv := axDecl :: standardBaseDecls
    modules := [mkAlignedModule pillarProofMod .proof [thmDecl]]
  }

def pillarOfReduceNatPkg : PackageAuditInput :=
  mkNativeAxiomPkg SymName.ofReduceNatName (SymName.ofList ["Init", "Meta"])

def pillarOfReduceBoolPkg : PackageAuditInput :=
  mkNativeAxiomPkg SymName.ofReduceBoolName (SymName.ofList ["Init", "Meta"])

def pillarTrustCompilerPkg : PackageAuditInput :=
  mkNativeAxiomPkg SymName.trustCompilerName (SymName.ofList ["Lean", "Compiler"])

def pillarNativeCompName : SymName :=
  SymName.ofList ["Proof", "Native", "_native", "decide_1"]

def pillarNativeCompPkg : PackageAuditInput :=
  mkNativeAxiomPkg pillarNativeCompName pillarProofMod

def provisionalConfig : AuditConfig := {
  allowAssumptions := false
  allowProvisionalNative := true
  enforceStrictProofs := true
  kernelFuel := 16
}

theorem pillar1_native_reduction_all_rejected :
    auditAndReplayPackage defaultUnconditionalConfig pillarOfReduceNatPkg =
      .error (.forbiddenNativeReductionAxiom pillarThmName SymName.ofReduceNatName) ∧
    auditAndReplayPackage defaultUnconditionalConfig pillarOfReduceBoolPkg =
      .error (.forbiddenNativeReductionAxiom pillarThmName SymName.ofReduceBoolName) ∧
    auditAndReplayPackage defaultUnconditionalConfig pillarTrustCompilerPkg =
      .error (.forbiddenNativeReductionAxiom pillarThmName SymName.trustCompilerName) ∧
    auditAndReplayPackage provisionalConfig pillarTrustCompilerPkg =
      .error (.forbiddenNativeReductionAxiom pillarThmName SymName.trustCompilerName) ∧
    auditAndReplayPackage defaultUnconditionalConfig pillarNativeCompPkg =
      .error (.forbiddenNativeReductionAxiom pillarThmName pillarNativeCompName) ∧
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig pillarProofMod .proof
      "theorem bad : True := by decide +native" =
      .error (.forbiddenSourceOption pillarProofMod "native_decide/decide +native") ∧
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig pillarProofMod .proof
      "theorem bad : True := by native_decide" =
      .error (.forbiddenSourceOption pillarProofMod "native_decide/decide +native") ∧
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig pillarProofMod .proof
      "theorem bad : True := by bv_decide" =
      .error (.forbiddenSourceOption pillarProofMod "native_decide/decide +native") := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Section 9.4: Complete 18-Vector Negative Tamper Suite (`bensherman` `cl/1027652636`, `V01`–`V18`) -/

def topicDefsModName : SymName := SymName.ofList ["Topic", "Defs"]
def topicProofModName : SymName := SymName.ofList ["Topic", "Proofs"]
def topicSpecModName : SymName := SymName.ofList ["Topic", "Spec"]
def topicVerifyModName : SymName := SymName.ofList ["Verify", "Topic"]
def topicTheoryModName : SymName := SymName.ofList ["Anneal", "TheoryHelper"]

def defsBeforeName : SymName := SymName.mkSimple "Before"
def defsBeforeDecl : ConstantRecord := {
  name := defsBeforeName
  kind := .defnDecl
  type := .const SymName.natName
  value? := some (.natLit 7)
  hasValue := true
  all := [defsBeforeName]
  originModule := topicDefsModName
}

def topicDefsLocalInstName : SymName := SymName.ofList ["Topic", "Defs", "instBefore"]

def validDefsModule : ModuleInventory :=
  mkAlignedModule topicDefsModName .defsExempt [defsBeforeDecl]
    (extEntries := [.instanceEntry topicDefsLocalInstName defsBeforeName topicDefsModName false])

def cleanProofThmName : SymName := SymName.ofList ["Topic", "Proofs", "cleanLemma"]
def cleanProofThmDecl : ConstantRecord := {
  name := cleanProofThmName
  kind := .thmDecl
  type := .const SymName.trueName
  value? := some (.const SymName.trueIntroName)
  hasValue := true
  all := [cleanProofThmName]
  originModule := topicProofModName
}

def validVerifyThmName : SymName := SymName.ofList ["Verify", "Topic", "verified"]
def validVerifyThmDecl : ConstantRecord := {
  name := validVerifyThmName
  kind := .thmDecl
  type := .app (.const SymName.verificationResultName) (.natLit 0)
  value? := some (.app (.app (.const verificationResultMkName) (.natLit 0)) (.const cleanProofThmName))
  hasValue := true
  all := [validVerifyThmName]
  originModule := topicVerifyModName
}

def mkSingleProofPkg (proofMod : ModuleInventory)
    (extraBase : List ConstantRecord := [])
    (extraMods : List ModuleInventory := [])
    (verifyRoots : List SymName := []) : PackageAuditInput := {
  baseEnv := extraBase ++ standardBaseDecls
  modules := validDefsModule :: proofMod :: extraMods
  verifyRoots := verifyRoots
}

/-- `V01_hijack_macro`: `macro_rules` hijacking audit command in `proof` module. -/
def v01Pkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.macroEntry (SymName.ofList ["Topic", "Proofs", "hijackMacro"])
      (SymName.ofList ["Lean", "Parser", "Command", "audit"])]))

theorem V01_hijack_macro_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v01Pkg =
      .error (.forbiddenMacroOrElab topicProofModName "macro"
        (SymName.ofList ["Topic", "Proofs", "hijackMacro"])) := rfl

/-- `V02_hijack_elab`: `@[command_elab]` overriding audit command in `proof` module. -/
def v02Pkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.commandElabEntry (SymName.ofList ["Topic", "Proofs", "hijackElab"])
      (SymName.ofList ["Lean", "Parser", "Command", "audit"])]))

theorem V02_hijack_elab_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v02Pkg =
      .error (.forbiddenMacroOrElab topicProofModName "command_elab"
        (SymName.ofList ["Topic", "Proofs", "hijackElab"])) := rfl

/-- `V03_skip_kernel_tc`: `set_option debug.skipKernelTC true` + ill-typed kernel decl (caught by BOTH layers!). -/
def illTypedFalseThmName : SymName := SymName.ofList ["Topic", "Proofs", "badFalse"]
def illTypedFalseThmDecl : ConstantRecord := {
  name := illTypedFalseThmName
  kind := .thmDecl
  type := .const SymName.falseName
  value? := some (.const SymName.trueIntroName)
  hasValue := true
  all := [illTypedFalseThmName]
  originModule := topicProofModName
}

def v03Source : String :=
  "set_option debug.skipKernelTC true\ntheorem badFalse : False := True.intro"

def v03Pkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [illTypedFalseThmDecl]
    (sourceText? := some v03Source))

theorem V03_skip_kernel_tc_rejected_both_layers :
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig topicProofModName .proof v03Source =
      .error (.forbiddenSourceOption topicProofModName "debug.skipKernelTC") ∧
    auditAndReplayPackage defaultUnconditionalConfig v03Pkg =
      .error (.forbiddenSourceOption topicProofModName "debug.skipKernelTC") ∧
    replayCleanEnv standardBaseEnv 16 false [defsBeforeDecl, illTypedFalseThmDecl] =
      .error (.kernelTypeError illTypedFalseThmName "theorem proof term type mismatch") := by
  refine ⟨rfl, rfl, rfl⟩

/-- `V04_unref_axiom`: unreferenced non-standard `axiom` declared in `spec` module. -/
def v04UnrefAxiomName : SymName := SymName.ofList ["Topic", "Spec", "secretAxiom"]
def v04UnrefAxiomDecl : ConstantRecord := {
  name := v04UnrefAxiomName
  kind := .axiomDecl
  type := .const SymName.falseName
  originModule := topicSpecModName
}

def v04Pkg : PackageAuditInput :=
  mkSingleProofPkg
    (mkAlignedModule topicProofModName .proof [cleanProofThmDecl])
    (extraMods := [
      mkAlignedModule topicSpecModName .spec [v04UnrefAxiomDecl],
      mkAlignedModule topicVerifyModName .verify [validVerifyThmDecl]
    ])
    (verifyRoots := [validVerifyThmName])

theorem V04_unref_axiom_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v04Pkg =
      .error (.forbiddenAxiom v04UnrefAxiomName v04UnrefAxiomName topicSpecModName) := rfl

/-- `V05_shadow_sorry`: `sorryAx` hidden behind renamed/shadowed `opaque` helper. -/
def v05OpaqueHelperName : SymName := SymName.ofList ["Topic", "Proofs", "opaqueShadow"]
def v05OpaqueHelperDecl : ConstantRecord := {
  name := v05OpaqueHelperName
  kind := .opaqueDecl
  type := .const SymName.trueName
  value? := some (.app (.lam (.const SymName.falseName) (.const SymName.trueIntroName)) (.const SymName.sorryAxName))
  hasValue := true
  all := [v05OpaqueHelperName]
  originModule := topicProofModName
}

def v05UsingThmDecl : ConstantRecord := {
  name := cleanProofThmName
  kind := .thmDecl
  type := .const SymName.trueName
  value? := some (.const v05OpaqueHelperName)
  hasValue := true
  all := [cleanProofThmName]
  originModule := topicProofModName
}

def v05Pkg : PackageAuditInput :=
  mkSingleProofPkg
    (mkAlignedModule topicProofModName .proof [v05OpaqueHelperDecl, v05UsingThmDecl])
    (extraBase := [sorryAxDecl])

theorem V05_shadow_sorry_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v05Pkg =
      .error (.forbiddenAxiom v05OpaqueHelperName SymName.sorryAxName (SymName.ofList ["Init", "Prelude"])) := rfl

/--
`V06_tamper_ext`: `exportedAxiomsExt` tampered to report `[]` axioms for a `sorryAx`-dependent theorem.
Zero forbidden `GlobalDecl`s / extensions; source scan, inventory, imports, and extensions ALL PASS;
caught specifically by direct constant-closure walk ignoring `cachedExportedAxioms`!
-/
def v06SorryThmName : SymName := SymName.ofList ["Topic", "Proofs", "tamperedCacheThm"]
def v06SorryThmDecl : ConstantRecord := {
  name := v06SorryThmName
  kind := .thmDecl
  type := .const SymName.trueName
  value? := some (.app (.lam (.const SymName.falseName) (.const SymName.trueIntroName)) (.const SymName.sorryAxName))
  hasValue := true
  all := [v06SorryThmName]
  originModule := topicProofModName
}

def v06ProofMod : ModuleInventory :=
  mkAlignedModule topicProofModName .proof [v06SorryThmDecl]
    (extEntries := [.cachedExportedAxioms v06SorryThmName []])
    (sourceText? := some "-- clean source\ntheorem tamperedCacheThm : True := trivial")

def v06Pkg : PackageAuditInput :=
  mkSingleProofPkg v06ProofMod (extraBase := [sorryAxDecl])

theorem V06_tamper_ext_isolated_rejection :
    validateReplayInventory v06ProofMod = .ok () ∧
    validateImports v06Pkg = .ok () ∧
    validateModuleExtensions defaultUnconditionalConfig v06ProofMod (collectProtectedNames v06Pkg) = .ok () ∧
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig topicProofModName .proof
      (v06ProofMod.sourceText?.getD "") = .ok () ∧
    auditAndReplayPackage defaultUnconditionalConfig v06Pkg =
      .error (.forbiddenAxiom v06SorryThmName SymName.sorryAxName (SymName.ofList ["Init", "Prelude"])) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `V07_local_elab_bad`: `local elab` persisting unscoped `.global` `command_elab` entry in `proof` module. -/
def v07Pkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.localCommandElabEntry (SymName.ofList ["Topic", "Proofs", "locElab"])
      (SymName.ofList ["Lean", "Parser", "Command", "audit"]) true]))

theorem V07_local_elab_bad_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v07Pkg =
      .error (.forbiddenMacroOrElab topicProofModName "local_command_elab_global"
        (SymName.ofList ["Topic", "Proofs", "locElab"])) := rfl

/-- `V08_nonlocal_elab_bad`: non-local `elab` in `proof` module with 0 `sorry`s. -/
def v08Pkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.commandElabEntry (SymName.ofList ["Topic", "Proofs", "nonLocalElab"])
      (SymName.ofList ["Topic", "Syntax", "myCmd"])]))

theorem V08_nonlocal_elab_bad_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v08Pkg =
      .error (.forbiddenMacroOrElab topicProofModName "command_elab"
        (SymName.ofList ["Topic", "Proofs", "nonLocalElab"])) := rfl

/--
`V09_replay_only`: ill-typed proof term injected programmatically.
Clean source text, zero extensions, valid inventory bijection, zero axioms — passes EVERY pre-replay
check and fails **EXCLUSIVELY** at clean-env kernel replay (`replayCleanEnv`)!
-/
def v09ProofMod : ModuleInventory :=
  mkAlignedModule topicProofModName .proof [illTypedFalseThmDecl]
    (sourceText? := some "-- clean source\ntheorem badFalse : False := trivial")

def v09Pkg : PackageAuditInput :=
  mkSingleProofPkg v09ProofMod

theorem V09_replay_only_isolated_rejection :
    validateReplayInventory v09ProofMod = .ok () ∧
    SourceScanner.scanSourceDefenseInDepth defaultUnconditionalConfig topicProofModName .proof
      (v09ProofMod.sourceText?.getD "") = .ok () ∧
    validateImports v09Pkg = .ok () ∧
    validateModuleExtensions defaultUnconditionalConfig v09ProofMod (collectProtectedNames v09Pkg) = .ok () ∧
    auditModuleDeclarations defaultUnconditionalConfig v09Pkg = .ok () ∧
    (auditPackageClosures defaultUnconditionalConfig v09Pkg
      (KernelEnv.finalizeImportedEnv v09Pkg.modules ++ mkBaseKernelEnv v09Pkg.baseEnv)).isOk = true ∧
    auditAndReplayPackage defaultUnconditionalConfig v09Pkg =
      .error (.kernelTypeError illTypedFalseThmName "theorem proof term type mismatch") := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `V10_hooks_bad`: ALL 4 hook kinds (`initialize`, `meta initialize`, `@[implemented_by]`, `@[extern]`). -/
def v10RegularInitPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.regularInitHook (SymName.ofList ["Topic", "Proofs", "initHook"])]))

def v10MetaInitPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.metaInitHook (SymName.ofList ["Topic", "Proofs", "metaInitHook"])]))

def v10ImplByPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.implementedByHook cleanProofThmName (SymName.ofList ["Topic", "Proofs", "evilImpl"])]))

def v10ExternPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.externHook cleanProofThmName (SymName.mkSimple "c_evil_symbol")]))

theorem V10_hooks_bad_all_four_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v10RegularInitPkg =
      .error (.forbiddenInitOrCodegenHook topicProofModName "initialize"
        (SymName.ofList ["Topic", "Proofs", "initHook"])) ∧
    auditAndReplayPackage defaultUnconditionalConfig v10MetaInitPkg =
      .error (.forbiddenInitOrCodegenHook topicProofModName "meta_initialize"
        (SymName.ofList ["Topic", "Proofs", "metaInitHook"])) ∧
    auditAndReplayPackage defaultUnconditionalConfig v10ImplByPkg =
      .error (.forbiddenInitOrCodegenHook topicProofModName "implemented_by" cleanProofThmName) ∧
    auditAndReplayPackage defaultUnconditionalConfig v10ExternPkg =
      .error (.forbiddenInitOrCodegenHook topicProofModName "extern" cleanProofThmName) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `V11_scoped_attrs_bad`: `scoped elab`, `scoped macro`, and `scoped instance` in `proof` module. -/
def v11ScopedElabPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.scopedElabEntry (SymName.ofList ["Topic", "Proofs", "scElab"]) topicProofModName]))

def v11ScopedMacroPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.scopedMacroEntry (SymName.ofList ["Topic", "Proofs", "scMacro"]) topicProofModName]))

def v11ScopedInstPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.scopedInstanceEntry (SymName.ofList ["Topic", "Proofs", "scInst"]) topicProofModName defsBeforeName]))

theorem V11_scoped_attrs_bad_all_three_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v11ScopedElabPkg =
      .error (.forbiddenMacroOrElab topicProofModName "scoped_elab"
        (SymName.ofList ["Topic", "Proofs", "scElab"])) ∧
    auditAndReplayPackage defaultUnconditionalConfig v11ScopedMacroPkg =
      .error (.forbiddenMacroOrElab topicProofModName "scoped_macro"
        (SymName.ofList ["Topic", "Proofs", "scMacro"])) ∧
    auditAndReplayPackage defaultUnconditionalConfig v11ScopedInstPkg =
      .error (.forbiddenInstanceOrCoe topicProofModName "scoped_instance"
        (SymName.ofList ["Topic", "Proofs", "scInst"])) := by
  refine ⟨rfl, rfl, rfl⟩

/-- `V12_inst_and_coe_bad`: imported `Defs` instance, `default_instance`, and `coe` in `proof` (while `Defs` local instance passes!). -/
def v12ImportedInstPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.instanceEntry (SymName.ofList ["Topic", "Proofs", "badInst"])
      defsBeforeName topicDefsModName false]))

def v12DefaultInstPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.defaultInstanceEntry (SymName.ofList ["Topic", "Proofs", "badDefInst"]) defsBeforeName]))

def v12CoePkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.coeEntry (SymName.ofList ["Topic", "Proofs", "badCoe"]) SymName.natName SymName.stringName]))

def v12BenignDefsPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl])

theorem V12_inst_and_coe_bad_and_benign_defs_ok :
    auditAndReplayPackage defaultUnconditionalConfig v12ImportedInstPkg =
      .error (.forbiddenInstanceOrCoe topicProofModName "imported_instance"
        (SymName.ofList ["Topic", "Proofs", "badInst"])) ∧
    auditAndReplayPackage defaultUnconditionalConfig v12DefaultInstPkg =
      .error (.forbiddenInstanceOrCoe topicProofModName "default_instance"
        (SymName.ofList ["Topic", "Proofs", "badDefInst"])) ∧
    auditAndReplayPackage defaultUnconditionalConfig v12CoePkg =
      .error (.forbiddenInstanceOrCoe topicProofModName "coe"
        (SymName.ofList ["Topic", "Proofs", "badCoe"])) ∧
    (auditAndReplayPackage defaultUnconditionalConfig v12BenignDefsPkg).isOk = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `V13_reducibility_bad`: `set_option allowUnsafeReducibility true` + imported `reducibility` override on `Nat.add`. -/
def v13SourcePkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (sourceText? := some "set_option allowUnsafeReducibility true\nattribute [reducible] Nat.add"))

def v13ExtPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.reducibilityOverride SymName.natAddName (SymName.ofList ["Init", "Prelude"]) "reducible"]))

theorem V13_reducibility_bad_both_layers_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v13SourcePkg =
      .error (.forbiddenSourceOption topicProofModName "allowUnsafeReducibility") ∧
    auditAndReplayPackage defaultUnconditionalConfig v13ExtPkg =
      .error (.forbiddenReducibilityOverride topicProofModName SymName.natAddName) := by
  refine ⟨rfl, rfl⟩

/-- `V14_import_all_bad`: `import all` of `Proofs` from `Spec`/`Verify` + private-instance leakage check. -/
def v14PlainImportAllPkg : PackageAuditInput :=
  mkSingleProofPkg
    (mkAlignedModule topicProofModName .proof [cleanProofThmDecl])
    (extraMods := [
      mkAlignedModule topicVerifyModName .verify [validVerifyThmDecl]
        (imports := [{ module := topicProofModName, importAll := true }])
    ])

def v14PrivInstName : SymName := SymName.ofList ["_private", "Topic", "Proofs", "secretInst"]

def v14PrivateInstLeakPkg : PackageAuditInput :=
  mkSingleProofPkg
    (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
      (extEntries := [.instanceEntry v14PrivInstName cleanProofThmName topicProofModName true]))
    (extraMods := [
      mkAlignedModule topicVerifyModName .verify [validVerifyThmDecl]
        (imports := [{ module := topicProofModName, importAll := true }])
    ])

theorem V14_import_all_and_private_instance_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v14PlainImportAllPkg =
      .error (.forbiddenImportAll topicVerifyModName topicProofModName) ∧
    auditAndReplayPackage defaultUnconditionalConfig v14PrivateInstLeakPkg =
      .error (.privateInstanceLeakViaImportAll topicVerifyModName topicProofModName v14PrivInstName) := by
  refine ⟨rfl, rfl⟩

/-- `V15_export_shadow_bad`: `export` alias, public suffix shadowing of `Init`/`Defs`, and `Topic.Proofs.Defs` non-exemption. -/
def v15ExportAliasPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.exportAlias (SymName.ofList ["Topic", "Proofs", "add"])
      SymName.natAddName (SymName.ofList ["Init", "Prelude"])]))

def v15ShadowInitName : SymName := SymName.ofList ["Pkg", "Nat", "add"]
def v15ShadowInitDecl : ConstantRecord := {
  name := v15ShadowInitName
  kind := .defnDecl
  type := .const SymName.natName
  value? := some (.natLit 0)
  hasValue := true
  all := [v15ShadowInitName]
  originModule := topicProofModName
}

def v15ShadowInitPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [v15ShadowInitDecl])

def v15ShadowDefsName : SymName := SymName.ofList ["Pkg", "Before"]
def v15ShadowDefsDecl : ConstantRecord := {
  name := v15ShadowDefsName
  kind := .defnDecl
  type := .const SymName.natName
  value? := some (.natLit 99)
  hasValue := true
  all := [v15ShadowDefsName]
  originModule := topicProofModName
}

def v15ShadowDefsPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [v15ShadowDefsDecl])

def spoofedProofsDefsModName : SymName := SymName.ofList ["Topic", "Proofs", "Defs"]
def v15SpoofedExemptPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [mkAlignedModule spoofedProofsDefsModName .defsExempt []]
}

theorem V15_export_shadow_and_spoofed_defs_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v15ExportAliasPkg =
      .error (.forbiddenShadowingOrExport topicProofModName
        (SymName.ofList ["Topic", "Proofs", "add"]) SymName.natAddName) ∧
    auditAndReplayPackage defaultUnconditionalConfig v15ShadowInitPkg =
      .error (.forbiddenShadowingOrExport topicProofModName v15ShadowInitName SymName.natAddName) ∧
    auditAndReplayPackage defaultUnconditionalConfig v15ShadowDefsPkg =
      .error (.forbiddenShadowingOrExport topicProofModName v15ShadowDefsName defsBeforeName) ∧
    SymName.isStrictExemptModuleName topicDefsModName = true ∧
    SymName.isStrictExemptModuleName spoofedProofsDefsModName = false ∧
    auditAndReplayPackage defaultUnconditionalConfig v15SpoofedExemptPkg =
      .error (.spoofedExemptModule spoofedProofsDefsModName) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `V16_term_delab_bad`: `term_elab`, `@[delab]`, and `@[app_unexpander]` in `proof` module. -/
def v16TermElabPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.termElabEntry (SymName.ofList ["Topic", "Proofs", "tElab"]) (SymName.mkSimple "term")]))

def v16DelabPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.delabEntry (SymName.ofList ["Topic", "Proofs", "myDelab"]) SymName.natAddName]))

def v16UnexpPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (extEntries := [.appUnexpanderEntry (SymName.ofList ["Topic", "Proofs", "myUnexp"]) SymName.natAddName]))

theorem V16_term_delab_bad_all_three_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v16TermElabPkg =
      .error (.forbiddenMacroOrElab topicProofModName "term_elab"
        (SymName.ofList ["Topic", "Proofs", "tElab"])) ∧
    auditAndReplayPackage defaultUnconditionalConfig v16DelabPkg =
      .error (.forbiddenMacroOrElab topicProofModName "delab"
        (SymName.ofList ["Topic", "Proofs", "myDelab"])) ∧
    auditAndReplayPackage defaultUnconditionalConfig v16UnexpPkg =
      .error (.forbiddenMacroOrElab topicProofModName "app_unexpander"
        (SymName.ofList ["Topic", "Proofs", "myUnexp"])) := by
  refine ⟨rfl, rfl, rfl⟩

/-- `V17_missing_olean_server`: `isModuleMode = true` with missing `.olean.server` (refusing fallback). -/
def v17Pkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (oleanParts := { isModuleMode := true, hasOlean := true, hasServer := false, hasPrivate := true }))

theorem V17_missing_olean_server_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v17Pkg =
      .error (.missingOleanServer topicProofModName) := rfl

/-- `V18_missing_olean_private`: `isModuleMode = true` with missing `.olean.private` (refusing fallback). -/
def v18Pkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [cleanProofThmDecl]
    (oleanParts := { isModuleMode := true, hasOlean := true, hasServer := true, hasPrivate := false }))

theorem V18_missing_olean_private_rejected :
    auditAndReplayPackage defaultUnconditionalConfig v18Pkg =
      .error (.missingOleanPrivate topicProofModName) := rfl

/-! ### Section 9.5: Realistic Positive Witnesses, Comment/String Non-False-Positives, Statement Separation, & `_unsafe_rec` -/

def theoryLemmaName : SymName := SymName.ofList ["Anneal", "TheoryHelper", "theoryProp"]
def theoryLemmaDecl : ConstantRecord := {
  name := theoryLemmaName
  kind := .defnDecl
  type := .const SymName.trueName
  value? := some (.const SymName.trueIntroName)
  hasValue := true
  all := [theoryLemmaName]
  originModule := topicTheoryModName
}

def safeRecFnName : SymName := SymName.ofList ["Topic", "Proofs", "safeRecFn"]
def safeRecFnDecl : ConstantRecord := {
  name := safeRecFnName
  kind := .defnDecl
  type := .const SymName.natName
  value? := some (.natLit 42)
  hasValue := true
  all := [safeRecFnName]
  originModule := topicProofModName
}

def safeRecUnsafeCompanionDecl : ConstantRecord := {
  name := SymName.str safeRecFnName "_unsafe_rec"
  kind := .defnDecl
  safety := .partialDecl
  type := .const SymName.natName
  value? := some (.natLit 42)
  hasValue := true
  all := [SymName.str safeRecFnName "_unsafe_rec"]
  originModule := topicProofModName
}

def proofUsesTheoryName : SymName := SymName.ofList ["Topic", "Proofs", "usesTheoryInProof"]
def proofUsesTheoryDecl : ConstantRecord := {
  name := proofUsesTheoryName
  kind := .thmDecl
  type := .const SymName.trueName
  value? := some (.const theoryLemmaName)
  hasValue := true
  all := [proofUsesTheoryName]
  originModule := topicProofModName
}

def baselineDefsSource : String :=
  "-- debug.skipKernelTC\n/- /- allowUnsafeReducibility -/ -/\ndef Before := 7"

def baselineProofSource : String :=
  "def s := \"\\\"debug.skipKernelTC\\\" native_decide\"\ndef c := '\"'\ntheorem t := True.intro"

def baselineVerifyDecl : ConstantRecord := {
  name := validVerifyThmName
  kind := .thmDecl
  type := .app (.const SymName.verificationResultName) (.natLit 0)
  value? := some (.app (.app (.const verificationResultMkName) (.natLit 0)) (.const proofUsesTheoryName))
  hasValue := true
  all := [validVerifyThmName]
  originModule := topicVerifyModName
}

/--
Realistic multi-module positive baseline package exercising:
- `Topic.Defs` (`defsExempt` with benign local `instanceEntry` + line/nested-block comments mentioning forbidden options)
- `Anneal.TheoryHelper` (`.theory` module used ONLY inside proofs, NOT theorem statements)
- `Topic.Proofs` (`.proof` with escaped string literals and char literal `'"'` mentioning forbidden options,
  valid 2-theorem mutual block, safe `_unsafe_rec` codegen companion, and full `.olean.{server,private}`
  module-mode artifacts!)
- `Verify.Topic` (`.verify` with `Verify.Topic.verified : VerificationResult 0`).
-/
def validBaselinePackage : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [
    { validDefsModule with sourceText? := some baselineDefsSource },
    mkAlignedModule topicTheoryModName .theory [theoryLemmaDecl],
    mkAlignedModule topicProofModName .proof
      [cleanProofThmDecl, safeRecFnDecl, safeRecUnsafeCompanionDecl, proofUsesTheoryDecl,
        { evenNonnegDecl with originModule := topicProofModName },
        { oddNonnegDecl with originModule := topicProofModName }]
      (oleanParts := { isModuleMode := true, hasOlean := true, hasServer := true, hasPrivate := true })
      (imports := [{ module := topicDefsModName }, { module := topicTheoryModName }])
      (sourceText? := some baselineProofSource),
    mkAlignedModule topicVerifyModName .verify [baselineVerifyDecl]
      (oleanParts := { isModuleMode := true, hasOlean := true, hasServer := true, hasPrivate := true })
      (imports := [{ module := topicProofModName }])
  ]
  verifyRoots := [validVerifyThmName]
}

/-- Positive witness: `validBaselinePackage` passes the entire hardened audit & clean-env kernel replay! -/
theorem validBaselinePackage_accepted :
    (auditAndReplayPackage defaultUnconditionalConfig validBaselinePackage).isOk = true := rfl

/-- End-to-end instantiation of `auditAndReplayPackage_sound` on `validBaselinePackage`: zero `False` inhabitation! -/
theorem validBaselinePackage_no_false :
    ∃ cert,
      auditAndReplayPackage defaultUnconditionalConfig validBaselinePackage = .ok cert ∧
      (∀ n ci, cert.replayedEnv.lookup n = some ci → ci.type ≠ .const SymName.falseName) ∧
      (∀ n ci, cert.importedEnv.lookup n = some ci → ci.type ≠ .const SymName.falseName) := by
  cases h : auditAndReplayPackage defaultUnconditionalConfig validBaselinePackage with
  | error e =>
    have hok := validBaselinePackage_accepted
    rw [h] at hok
    cases hok
  | ok cert =>
    have hsound := (auditAndReplayPackage_sound h).2.2.2 rfl rfl standardBaseModel standardBaseEnv_sound
    exact ⟨cert, rfl, hsound.2.1, hsound.2.2⟩

/-- Statement-vs-Proof Origin Separation negative test: referencing a `.theory` decl in `Verify.*.verified`'s type fails! -/
def theoryClaimTypeName : SymName := SymName.ofList ["Anneal", "TheoryHelper", "theoryIdx"]
def theoryClaimTypeDecl : ConstantRecord := {
  name := theoryClaimTypeName
  kind := .defnDecl
  type := .const SymName.natName
  value? := some (.natLit 0)
  hasValue := true
  all := [theoryClaimTypeName]
  originModule := topicTheoryModName
}

def leakyVerifyDecl : ConstantRecord := {
  name := validVerifyThmName
  kind := .thmDecl
  type := .app (.const SymName.verificationResultName) (.const theoryClaimTypeName)
  value? := some (.app (.app (.const verificationResultMkName) (.const theoryClaimTypeName)) (.const SymName.trueIntroName))
  hasValue := true
  all := [validVerifyThmName]
  originModule := topicVerifyModName
}

def statementLeakPkg : PackageAuditInput := {
  baseEnv := standardBaseDecls
  modules := [
    mkAlignedModule topicTheoryModName .theory [theoryClaimTypeDecl],
    mkAlignedModule topicVerifyModName .verify [leakyVerifyDecl]
  ]
  verifyRoots := [validVerifyThmName]
}

theorem statementTheoryLeak_rejected :
    auditAndReplayPackage defaultUnconditionalConfig statementLeakPkg =
      .error (.statementTheoryLeak validVerifyThmName theoryClaimTypeName topicTheoryModName) := rfl

/-- Spoofed `_unsafe_rec` with mismatched type `False` is NOT excused as a codegen companion and is rejected! -/
def spoofedUnsafeRecDecl : ConstantRecord := {
  name := SymName.str safeRecFnName "_unsafe_rec"
  kind := .defnDecl
  safety := .partialDecl
  type := .const SymName.falseName
  value? := some (.const SymName.trueIntroName)
  hasValue := true
  all := [SymName.str safeRecFnName "_unsafe_rec"]
  originModule := topicProofModName
}

def spoofedUnsafeRecPkg : PackageAuditInput :=
  mkSingleProofPkg (mkAlignedModule topicProofModName .proof [safeRecFnDecl, spoofedUnsafeRecDecl])

theorem spoofedUnsafeRec_rejected :
    auditAndReplayPackage defaultUnconditionalConfig spoofedUnsafeRecPkg =
      .error (.unsafeOrPartialDecl topicProofModName (SymName.str safeRecFnName "_unsafe_rec")) := rfl

end Anneal.ReplayKeyAndTamperAuditPrototype
