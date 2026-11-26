import Anneal.Rustc.V2026_06_01.SymbolicEval.PinnedSpecEquivAndCalls

namespace Anneal.Rustc.V2026_06_01.SymbolicEval

open Trusted.Refinement
open Trusted.Sequence
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Scalars
open Anneal.Memory
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower

/-!
Differential-testing outcome classifiers, strict UB / panic refutation combinators, and
signature / polymorphic obligation adapter kernel checks (section 10, `SignatureValidationTests`).
-/

/-! ## 10. Differential Testing Outcome Classifiers & Strict UB / Panic Refutation Combinators -/

/--
Fine-grained bounded execution verdict for differential testing against Miri.

Unlike `reachesFaultExecBounded` (which conflates `FailureKind.ub` and
`FailureKind.unsupported`), `MirDiffVerdict` separates genuine Undefined
Behavior (`.ub`) from fail-closed unmodeled constructs (`.unsupported`),
unresolved external calls (`.externalCall`), safe unwinding (`.panic`),
process abort (`.abort`), normal termination (`.normal`), and fuel exhaustion
(`.outOfFuel`).
-/
inductive MirDiffVerdict : Type where
  | normal (retVal : Value) (mem : Memory)
  | panic
  | abort
  | ub
  | unsupported
  | externalCall (defPath : DefPath)
  | outOfFuel

/--
Decidable, printable projection of `MirDiffVerdict` for `#eval` reporting and
equality checks in differential test suites.
-/
inductive MirDiffTag : Type where
  | normalUnit
  | normalScalar (bits : Nat) (sizeBytes : Nat)
  | normalOther
  | panic
  | abort
  | ub
  | unsupported
  | externalCall (defPath : DefPath)
  | outOfFuel
  deriving DecidableEq, Repr

/-- Project a `MirDiffVerdict` to its body-independent `MirDiffTag`. -/
def MirDiffVerdict.toTag : MirDiffVerdict → MirDiffTag
  | .normal .unit _ => .normalUnit
  | .normal (.scalar sc) _ => .normalScalar sc.bits sc.sizeBytes
  | .normal _ _ => .normalOther
  | .panic => .panic
  | .abort => .abort
  | .ub => .ub
  | .unsupported => .unsupported
  | .externalCall defPath => .externalCall defPath
  | .outOfFuel => .outOfFuel

/--
Return `true` when every variant in `variants` has an empty `FieldsShape`
(`.arbitrary [] _`).
-/
def allVariantsFieldless : List FieldsShape → Bool
  | .nil => true
  | .arbitrary .nil _ :: rest => allVariantsFieldless rest
  | _ :: _ => false

/--
Return `true` when return local `_0` in `body.localDecls` can represent a
scalar-backed enum (`RigidTy.adt`, generic `RigidTy.param`, or an omitted
`localDecls` table).

Rejects zero-element arrays (`[T; 0]`), empty tuples (`()`), and other non-ADT
types that construct `.aggregate 0 []` in MIR so they are never misclassified
as scalar-represented enums if `body.fnAbi.ret.layout` differs.
-/
def returnLocalAllowsScalarEnum (body : CapturedMir) : Bool :=
  match get? body.localDecls 0 with
  | .none => true
  | .some decl0 =>
    match decl0.ty.kind with
    | .adt _ _ => true
    | .param _ _ => true
    | _ => false

/--
Return the cardinality of inclusive wrap-around range `r` within `[0, modulus)`,
or `.none` when either endpoint lies outside `[0, modulus)`.
-/
def wrappingRangeCount (r : WrappingRange) (modulus : Nat) : Option Nat :=
  match
    Bool.and
      (Nat.ble (.succ r.start) modulus)
      (Nat.ble (.succ r.end_) modulus)
  with
  | false => .none
  | true =>
    match Nat.ble r.start r.end_ with
    | true => .some (Nat.add (Nat.sub r.end_ r.start) 1)
    | false => .some (Nat.add (Nat.add (Nat.sub modulus r.start) r.end_) 1)

/--
Resolve the concrete positive-sized return `TypeLayout` of `body`.

Consults return local `_0` in `body.layouts` first. When `_0` resolves to a
concrete zero-sized layout (`l.size.bytes = 0` and
`TypeLayout.isParamPlaceholder l = false`), returns `.none` without falling back
to `body.fnAbi.ret.layout` so concrete zero-sized return types stay zero-sized.
Falls back to `body.fnAbi.ret.layout` only when `_0` is absent from
`body.localDecls`, missing from `body.layouts`, or still an uninstantiated
parametric placeholder slot.
-/
def resolveReturnLayout? (body : CapturedMir) : Option TypeLayout :=
  let fallbackFnAbi : Option TypeLayout :=
    match body.fnAbi.ret.layout.size.bytes with
    | _ + 1 => .some body.fnAbi.ret.layout
    | 0 => .none
  match get? body.localDecls 0 with
  | .some decl0 =>
    match LayoutTable.lookup body.layouts decl0.ty.layoutIdx with
    | .some l =>
      match l.size.bytes with
      | _ + 1 => .some l
      | 0 =>
        match TypeLayout.isParamPlaceholder l with
        | true => fallbackFnAbi
        | false => .none
    | .none => fallbackFnAbi
  | .none => fallbackFnAbi

/--
Validate that candidate bit pattern `bits` fits in `[0, modulus)` and satisfies
`ScalarInt.inRange` for `sz` bytes under `validRange`.
-/
def validateScalarEnumCandidate
    (bits sz modulus : Nat) (validRange : WrappingRange) :
    Option (Nat × Nat) :=
  match
    Bool.and
      (Nat.ble (.succ bits) modulus)
      (ScalarInt.inRange { bits := bits, sizeBytes := sz } validRange)
  with
  | true => .some (bits, sz)
  | false => .none

/--
Compute the candidate unsigned discriminant bit pattern of `variantIdx` for a
validated `sz`-byte integer scalar return layout (`modulus = scalarModulus sz`).

Because `CapturedMir` records `TypeLayout` without `AdtDef` per-variant
discriminants, `VariantsShape.multiple` determines each variant's bit pattern
only when:

1. Every variant has an empty `FieldsShape` (`allVariantsFieldless`), excluding
   niche-encoded payload enums such as `Option<bool>` or `Option<OnlyZero>`
   whose fieldless variant uses a displaced niche tag.
2. `wrappingRangeCount validRange modulus` equals `variantShapes.length`,
   excluding gapped explicit-discriminant enums (`A = 1, B = 5`) while unifying
   zero-based enums (`0..=k-1`), `rustc`-captured single-variant `#[repr(int)]`
   enums (`c..=c` with one `VariantsShape.multiple` entry), non-zero contiguous
   enums (`a..=a+k-1`), and negative-start signed contiguous enums such as
   `core::cmp::Ordering` (`255..=1` for `i8`) via
   `wrapScalarBits (validRange.start + variantIdx) modulus`. Non-monotonic
   permutations of a contiguous range (`High = 2, Mid = 1, Low = 0`) share the
   same `TypeLayout` as ascending order until `CapturedMir` captures `AdtDef`
   discriminants.
3. Full-width signed `0..=modulus-1` ranges are excluded because wrapping
   normalization erases whether variant `0` starts at `0` or `-2^(8*sz - 1)`.
-/
def scalarEnumCandidateBits?
    (body : CapturedMir)
    (retLayout : TypeLayout)
    (sz modulus : Nat)
    (isSigned : Bool)
    (validRange : WrappingRange)
    (variantIdx : VariantIdx) :
    Option Nat :=
  match retLayout.variants with
  | .multiple _ _ (vHead :: vTail) =>
    let variantShapes := vHead :: vTail
    let numVariants := length variantShapes
    let rangeMatchesCount :=
      match wrappingRangeCount validRange modulus with
      | .some cnt => Nat.beq cnt numVariants
      | .none => false
    let nonAmbiguousSignedFull :=
      Bool.not
        (Bool.and
          isSigned
          (Bool.and
            (Nat.beq validRange.start 0)
            (Nat.beq validRange.end_ (Nat.sub modulus 1))))
    let ok :=
      Bool.and
        (Nat.ble (.succ variantIdx) numVariants)
        (Bool.and
          (allVariantsFieldless variantShapes)
          (Bool.and rangeMatchesCount nonAmbiguousSignedFull))
    match ok with
    | true => .some (wrapScalarBits (Nat.add validRange.start variantIdx) modulus)
    | false => .none
  | .multiple _ _ .nil =>
    match wrappingRangeCount validRange modulus with
    | .none => .none
    | .some _ =>
      let isOrdering :=
        match get? body.localDecls 0 with
        | .some { ty := { kind := .adt defPath _, .. }, .. } =>
          Bool.and
            (stringEq defPath "core::cmp::Ordering")
            (Bool.and
              (Nat.beq sz 1)
              (Bool.and
                (Nat.beq validRange.start 255)
                (Nat.beq validRange.end_ 1)))
        | _ => false
      match isOrdering with
      | true =>
        match variantIdx with
        | 0 => .some 255
        | 1 => .some 0
        | 2 => .some 1
        | _ => .none
      | false =>
        match Bool.and (Bool.not isSigned) (Nat.beq validRange.start 0) with
        | true => .some variantIdx
        | false => .none
  | .single expectedIdx =>
    match
      retLayout.fields,
      Nat.beq variantIdx expectedIdx,
      Nat.beq validRange.start validRange.end_
    with
    | .arbitrary .nil _, true, true => .some validRange.start
    | _, _, _ => .none
  | .empty => .none

/--
Compute the unsigned `(bits, sizeBytes)` scalar representation of a fieldless
enum return value `.aggregate variantIdx []` when `body`'s return layout uses
`BackendRepr.scalar (ScalarLayout.initialized (.int (8 * sz) _) validRange)`
with `1 ≤ sz ≤ 16`.

MIR execution preserves fieldless enum values as `Value.aggregate variantIdx []`
so `Rvalue.discriminant` can inspect their variant index, whereas Miri's
differential runner observes the return place's `BackendRepr::Scalar` bit
pattern. This helper bridges that representation at function return while
keeping zero-sized types, payload-bearing aggregates, niche-encoded payload
enums, and gapped explicit-discriminant enums classified as `.none`.
-/
def scalarEnumReturnTag?
    (body : CapturedMir) (variantIdx : VariantIdx) : Option (Nat × Nat) :=
  match returnLocalAllowsScalarEnum body, resolveReturnLayout? body with
  | true, .some retLayout =>
    match
      retLayout.isUninhabited,
      retLayout.size.bytes,
      retLayout.backendRepr
    with
    | false, sz@(_ + 1), .scalar (.initialized (.int primBits isSigned) validRange) =>
      match Bool.and (Nat.ble sz 16) (Nat.beq primBits (Nat.mul sz 8)) with
      | false => .none
      | true =>
        let modulus := scalarModulus sz
        match
          scalarEnumCandidateBits?
            body retLayout sz modulus isSigned validRange variantIdx
        with
        | .some candidateBits =>
          validateScalarEnumCandidate candidateBits sz modulus validRange
        | .none => .none
    | _, _, _ => .none
  | _, _ => .none

/--
Project a `MirDiffVerdict` to its decidable `MirDiffTag` using `body`'s return
layout metadata so scalar-represented fieldless enums report `.normalScalar`
matching Miri's `BackendRepr::Scalar` runner.
-/
def MirDiffVerdict.toTagWithBody
    (body : CapturedMir) (v : MirDiffVerdict) : MirDiffTag :=
  match v with
  | .normal (.aggregate variantIdx .nil) _ =>
    match scalarEnumReturnTag? body variantIdx with
    | .some (bits, sz) => .normalScalar bits sz
    | .none => .normalOther
  | _ => v.toTag

/--
Evaluate `body` from `st : MirExecState` for up to `fuel` steps, classifying the
terminal outcome or fault into a `MirDiffVerdict`.
-/
def evalMirDiffExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : MirDiffVerdict :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match stepMirStatePeriodic fuel' body st with
    | .ret (.normal (retVal, mem)) => .normal retVal mem
    | .ret .panic => .panic
    | .ret .abort => .abort
    | .tau st' => evalMirDiffExecBounded fuel' body st'
    | .vis (.inl (.fail .ub)) _ => .ub
    | .vis (.inl (.fail .unsupported)) _ => .unsupported
    | .vis (.inl (.fail .outOfFuel)) _ => .outOfFuel
    | .vis (.inr (.inl _)) k => evalMirDiffExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) _ => .externalCall req.defPath

/--
Evaluate `body` starting from `s : MachineState` for up to `fuel` steps and
return its `MirDiffVerdict`.
-/
def evalMirDiffBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : MirDiffVerdict :=
  evalMirDiffExecBounded fuel body (.running s)

/--
Evaluate `body` starting from `s : MachineState` for up to `fuel` steps and
return its decidable `MirDiffTag`.
-/
def evalMirDiffTagBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : MirDiffTag :=
  (evalMirDiffBounded fuel body s).toTagWithBody body

/--
Return the active statement or terminator source span of `st` in `body` (or
`"none"` when not running or when the span is empty or `"<dummy>"`).
-/
def activeMirSpan (body : CapturedMir) (st : MirExecState) : String :=
  let raw :=
    match st with
    | .running s =>
      let cur :=
        match s.memory.activeCallee with
        | .some callee => callee
        | .none => body
      match get? cur.basicBlocks s.frame.blockIdx with
      | .some bb =>
        match get? bb.statements s.frame.stmtIdx with
        | .some stmt => stmt.span
        | .none => bb.terminator.span
      | .none => "none"
    | _ => "none"
  match Bool.or (stringEq raw "") (stringEq raw "<dummy>") with
  | true => "none"
  | false => raw

/--
Evaluate `body` from `st : MirExecState` for up to `fuel` steps and return both
its `MirDiffTag` (via `MirDiffVerdict.toTagWithBody`) and the active fault or
unwind source span (`"none"` on normal return).
-/
def probeMirDiffExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) :
    MirDiffTag × String :=
  match fuel with
  | 0 => (.outOfFuel, activeMirSpan body st)
  | fuel' + 1 =>
    match stepMirStatePeriodic fuel' body st with
    | .ret (.normal (retVal, mem)) =>
      ((MirDiffVerdict.normal retVal mem).toTagWithBody body, "none")
    | .ret .panic => (.panic, activeMirSpan body st)
    | .ret .abort => (.abort, activeMirSpan body st)
    | .tau st' => probeMirDiffExecBounded fuel' body st'
    | .vis (.inl (.fail .ub)) _ => (.ub, activeMirSpan body st)
    | .vis (.inl (.fail .unsupported)) _ => (.unsupported, activeMirSpan body st)
    | .vis (.inl (.fail .outOfFuel)) _ => (.outOfFuel, activeMirSpan body st)
    | .vis (.inr (.inl _)) k =>
      probeMirDiffExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) _ =>
      (.externalCall req.defPath, activeMirSpan body st)

/--
Evaluate `body` starting from `s : MachineState` for up to `fuel` steps and
return its `(MirDiffTag, span)` pair.
-/
def probeMirDiffBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) :
    MirDiffTag × String :=
  probeMirDiffExecBounded fuel body (.running s)

/--
`probeMirDiffExecBounded` always agrees in its tag projection with
`(evalMirDiffExecBounded fuel body st).toTagWithBody body`.
-/
theorem probeMirDiffExecBounded_fst_eq_toTagWithBody
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) :
    (probeMirDiffExecBounded fuel body st).1 =
      (evalMirDiffExecBounded fuel body st).toTagWithBody body := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel' ih =>
    unfold probeMirDiffExecBounded evalMirDiffExecBounded
    rw [stepMirStatePeriodic_eq]
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal p =>
        rcases p with ⟨retVal, mem⟩
        rfl
      | panic => rfl
      | abort => rfl
    | tau st' => exact ih st'
    | vis i k =>
      rcases i with f | (e | c)
      · rcases f with ⟨fk⟩
        cases fk <;> rfl
      · cases e
        exact ih (k PUnit.unit)
      · rcases c with ⟨req⟩
        rfl

/--
`probeMirDiffBounded` always agrees in its tag projection with
`evalMirDiffTagBounded`.
-/
theorem probeMirDiffBounded_fst_eq_evalMirDiffTagBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) :
    (probeMirDiffBounded fuel body s).1 =
      evalMirDiffTagBounded fuel body s :=
  probeMirDiffExecBounded_fst_eq_toTagWithBody fuel body (.running s)

/--
Computable bounded strict-UB detector over `MirExecState`: returns `true` only
when `body` reaches an explicit Undefined Behavior fault (`FailureKind.ub`)
within `fuel` steps along `.tau` and `MirObsE` transitions.

Crucially, `reachesStrictUBExecBounded` returns `false` on
`FailureKind.unsupported`, ensuring that differential tests against Miri `fail/`
suites never mistake an unimplemented MIR feature for a successful UB detection.
-/
def reachesStrictUBExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirStatePeriodic fuel' body st with
    | .ret _ => false
    | .tau st' => reachesStrictUBExecBounded fuel' body st'
    | .vis (.inl (.fail .ub)) _ => true
    | .vis (.inl (.fail .unsupported)) _ => false
    | .vis (.inl (.fail .outOfFuel)) _ => false
    | .vis (.inr (.inl _)) k =>
      reachesStrictUBExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr _)) _ => false

/-- Computable bounded strict-UB detector starting from `s : MachineState`. -/
def reachesStrictUBBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : Bool :=
  reachesStrictUBExecBounded fuel body (.running s)

/--
Every strict-UB detection (`reachesStrictUBExecBounded`) is also a fault
detection (`reachesFaultExecBounded`).
-/
theorem reachesFaultExecBounded_of_reachesStrictUBExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_ub : reachesStrictUBExecBounded fuel body st = true) :
    reachesFaultExecBounded fuel body st = true := by
  induction fuel generalizing st with
  | zero => nomatch h_ub
  | succ fuel' ih =>
    unfold reachesStrictUBExecBounded at h_ub
    unfold reachesFaultExecBounded
    rw [stepMirStatePeriodic_eq] at h_ub ⊢
    cases h_step : stepMirState body st with
    | ret _ =>
      simp only [h_step] at h_ub
      nomatch h_ub
    | tau st' =>
      simp only [h_step] at h_ub ⊢
      exact ih st' h_ub
    | vis i k =>
      rcases i with f | (e | c)
      · rfl
      · simp only [h_step] at h_ub ⊢
        exact ih (k PUnit.unit) h_ub
      · simp only [h_step] at h_ub
        nomatch h_ub

/--
If `reachesStrictUBBounded fuel body s = true`, then `mirTree body s` violates
`TreeSafe` by reaching `FailureKind.ub`.
-/
theorem reachesStrictUBBounded_not_treeSafe
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (h_ub : reachesStrictUBBounded fuel body s = true) :
    ¬ TreeSafe (mirTree body s) :=
  reachesFaultBounded_not_treeSafe fuel body s
    (reachesFaultExecBounded_of_reachesStrictUBExecBounded fuel body (.running s) h_ub)

/--
Refute a stateless `c : Claim` (`¬ c.holds`) by exhibiting a concrete input
`args` satisfying `c.pre args` whose bounded execution specifically hits
`FailureKind.ub` (and not `.unsupported`) within `fuel` steps.
-/
theorem refuteClaimByStrictUB
    (c : Claim)
    (fuel : Nat)
    (args : List Value)
    (h_pre : c.pre args)
    (h_ub :
      reachesStrictUBBounded fuel c.body
        (initMachineStateWithCallees c.body args c.callees) = true := by
      rfl) :
    ¬ c.holds :=
  refuteClaimByBoundedUB c fuel args h_pre
    (reachesFaultExecBounded_of_reachesStrictUBExecBounded
      fuel c.body (.running (initMachineStateWithCallees c.body args c.callees)) h_ub)

/--
Refute a stateful `c : StatefulClaim` (`¬ c.holds`) by exhibiting a concrete
`(args, mem)` satisfying `c.pre args mem` whose bounded execution specifically
hits `FailureKind.ub` (and not `.unsupported`) within `fuel` steps.
-/
theorem refuteStatefulClaimByStrictUB
    (c : StatefulClaim)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_pre : c.pre args mem)
    (h_ub :
      reachesStrictUBBounded fuel c.body
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees) = true := by
      rfl) :
    ¬ c.holds :=
  refuteStatefulClaimByBoundedUB c fuel args mem h_pre
    (reachesFaultExecBounded_of_reachesStrictUBExecBounded
      fuel c.body (.running (initMachineStateWithMemoryAndCallees c.body args mem c.callees)) h_ub)

/--
Refute a total-correctness `c : TotalClaim` (`¬ c.holds`) by exhibiting a
concrete `(args, mem)` satisfying `c.pre args mem` whose bounded execution
specifically hits `FailureKind.ub` (and not `.unsupported`) within `fuel` steps.
-/
theorem refuteTotalClaimByStrictUB
    (c : TotalClaim)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_pre : c.pre args mem)
    (h_ub :
      reachesStrictUBBounded fuel c.body
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees) = true := by
      rfl) :
    ¬ c.holds :=
  refuteTotalClaimByBoundedUB c fuel args mem h_pre
    (reachesFaultExecBounded_of_reachesStrictUBExecBounded
      fuel c.body (.running (initMachineStateWithMemoryAndCallees c.body args mem c.callees)) h_ub)

/--
Computable bounded panic detector over `MirExecState`: returns `true` when
`body` reaches `.ret .panic` within `fuel` steps along `.tau` and `MirObsE`
transitions without hitting any fault.
-/
def reachesPanicExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirStatePeriodic fuel' body st with
    | .ret .panic => true
    | .ret (.normal _) => false
    | .ret .abort => false
    | .tau st' => reachesPanicExecBounded fuel' body st'
    | .vis (.inl _) _ => false
    | .vis (.inr (.inl _)) k => reachesPanicExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr _)) _ => false

/-- Computable bounded panic detector starting from `s : MachineState`. -/
def reachesPanicBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : Bool :=
  reachesPanicExecBounded fuel body (.running s)

/--
Soundness of `reachesPanicExecBounded`: if `reachesPanicExecBounded fuel body st`
returns `true`, then `ITree.cofix (stepMirState body) st` reaches `.ret .panic`
along some finite event trace `tr`.
-/
theorem reachesPanicExecBounded_reachesRet
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_panic : reachesPanicExecBounded fuel body st = true) :
    ∃ tr, ReachesRet (ITree.cofix (stepMirState body) st) tr .panic := by
  induction fuel generalizing st with
  | zero => nomatch h_panic
  | succ fuel' ih =>
    unfold reachesPanicExecBounded at h_panic
    rw [stepMirStatePeriodic_eq] at h_panic
    have h_obs :
        (ITree.cofix (stepMirState body) st).observe =
          (stepMirState body st).map (ITree.cofix (stepMirState body)) :=
      ITree.observe_cofix (stepMirState body) st
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal _ =>
        simp only [h_step] at h_panic
        nomatch h_panic
      | panic =>
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        exact ⟨[], _, Reaches.refl _, h_obs⟩
      | abort =>
        simp only [h_step] at h_panic
        nomatch h_panic
    | tau st' =>
      simp only [h_step] at h_panic
      rw [h_step] at h_obs
      dsimp only [ITreeF.map] at h_obs
      rcases ih st' h_panic with ⟨tr, u, h_reach, h_u⟩
      exact ⟨tr, u, Reaches.tau h_obs h_reach, h_u⟩
    | vis i k =>
      rcases i with f | (e | c)
      · simp only [h_step] at h_panic
        nomatch h_panic
      · simp only [h_step] at h_panic
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        rcases ih (k PUnit.unit) h_panic with ⟨tr, u, h_reach, h_u⟩
        exact ⟨⟨.inr (.inl e), PUnit.unit⟩ :: tr, u,
          Reaches.vis h_obs False.elim PUnit.unit h_reach, h_u⟩
      · simp only [h_step] at h_panic
        nomatch h_panic

/--
If `reachesPanicBounded fuel body s = true`, then `mirTree body s` reaches
`.ret .panic` along some finite event trace `tr`.
-/
theorem reachesPanicBounded_reachesRet
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (h_panic : reachesPanicBounded fuel body s = true) :
    ∃ tr, ReachesRet (mirTree body s) tr .panic :=
  reachesPanicExecBounded_reachesRet fuel body (.running s) h_panic

/--
Refute a total-correctness `c : TotalClaim` (`¬ c.holds`) by exhibiting a
concrete `(args, mem)` satisfying `c.pre args mem` whose bounded execution
cleanly unwinds to `.ret .panic` within `fuel` steps.
-/
theorem refuteTotalClaimByBoundedPanic
    (c : TotalClaim)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_pre : c.pre args mem)
    (h_panic :
      reachesPanicBounded fuel c.body
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees) = true := by
      rfl) :
    ¬ c.holds := by
  intro h_holds
  rcases reachesPanicBounded_reachesRet fuel c.body
    (initMachineStateWithMemoryAndCallees c.body args mem c.callees) h_panic with ⟨tr, h_ret⟩
  rcases (h_holds args mem h_pre).2.2.2 tr .panic h_ret with
    ⟨_, _, h_eq, _⟩
  nomatch h_eq

/--
If `reachesPanicExecBounded fuel body st = true`, then `wpCoalBounded` holds
under `mirDefaultWP` with vacuous normal-return postcondition
`(∀ retVal mem', out = .normal (retVal, mem') → False)`, certifying that the
panic execution path is completely UB-free (`TreeSafe`).
-/
theorem wpCoalBounded_of_reachesPanicExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_panic : reachesPanicExecBounded fuel body st = true) :
    wpCoalBounded fuel mirDefaultWP (stepMirState body)
      (fun out _ => ∀ retVal mem', out = .normal (retVal, mem') → False)
      st PUnit.unit := by
  induction fuel generalizing st with
  | zero => nomatch h_panic
  | succ fuel' ih =>
    unfold reachesPanicExecBounded at h_panic
    rw [stepMirStatePeriodic_eq] at h_panic
    unfold wpCoalBounded
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal _ =>
        simp only [h_step] at h_panic
        nomatch h_panic
      | panic =>
        intro _ _ h_eq
        nomatch h_eq
      | abort =>
        simp only [h_step] at h_panic
        nomatch h_panic
    | tau st' =>
      simp only [h_step] at h_panic ⊢
      exact ih st' h_panic
    | vis i k =>
      rcases i with f | (e | c)
      · simp only [h_step] at h_panic
        nomatch h_panic
      · simp only [h_step] at h_panic ⊢
        cases e
        exact ih (k PUnit.unit) h_panic
      · simp only [h_step] at h_panic
        nomatch h_panic

/--
If `reachesPanicBounded fuel body s = true`, then `wpMirBounded` holds with
postcondition `∀ retVal mem', out = .normal (retVal, mem') → False`.
-/
theorem wpMirBounded_of_reachesPanicBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (h_panic : reachesPanicBounded fuel body s = true) :
    wpMirBounded fuel body s
      (fun out => ∀ retVal mem', out = .normal (retVal, mem') → False) :=
  wpCoalBounded_of_reachesPanicExecBounded fuel body (.running s) h_panic

/--
Certify a Miri `panic` test at `(args, mem)`: proves both
1. `StatefulVerificationResult` with `post := False` (certifying that execution
   unwinds without Undefined Behavior and never returns normally), and
2. `¬ TotalClaim.holds` (refuting total correctness because execution panics).
-/
theorem verifySafePanicMirPointBounded
    (body : CapturedMir)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_panic :
      reachesPanicBounded fuel body
        (initMachineStateWithMemory body args mem) = true := by
      rfl) :
    StatefulVerificationResult
      { body := body
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ _ _ => False } ∧
    ¬ ({ body := body
         pre := fun a m => a = args ∧ m = mem
         post := fun _ _ _ _ => True } : TotalClaim).holds := by
  refine ⟨?_, ?_⟩
  · refine verifyStatefulMirBounded _ fuel ?_
    rintro a m ⟨rfl, rfl⟩
    exact wpMirBounded_of_reachesPanicBounded fuel body
      (initMachineStateWithMemory body a m) h_panic
  · exact refuteTotalClaimByBoundedPanic
      { body := body
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ _ _ => True }
      fuel args mem ⟨rfl, rfl⟩ h_panic

/-! ### Safe Panics Across Uninterpreted External Calls -/

/--
Frame-preserving rely contract for the external calls of a modular safe-panic
certificate (`verifyModularSafePanicMirBounded`). It places no requirement on a
call request, and it assumes only that the callee returns an initialized value
(`valueContainsUninit retVal = false`) or unwinds to the same call frame
(`callFramePreserved`), or aborts. It assumes nothing else about the returned
value or about the rest of the post-call memory.

A `StatefulVerificationResult` cannot certify a body that panics after an
uninterpreted external call: `mirDefaultWP` lets that call return any answer,
including `Value.uninit` (which faults when moved into `panic_fmt`) or a memory
whose call stack or callee table is corrupted, and the caller can then fault.
This contract rules out those answers.

`TrustedBoundary.checkStatementOrigins` rejects a `Verify.*` certificate whose
statement mentions an `Anneal.*` constant, so generated certificates spell out
this structure with `Trusted.*` constants only. That spelling and this
definition agree by unfolding.
-/
def framePreservingCallContract : MirCallContract where
  pre _ := True
  post req ans :=
    match ans with
    | .returned retVal memAfter =>
      And (valueContainsUninit retVal = false) (callFramePreserved req.memory memAfter)
    | .panicked memAfter => callFramePreserved req.memory memAfter
    | .aborted => True

/--
Every answer that `framePreservingCallContract` permits preserves the caller's
call frame, so `wpMirFrameModularSym` may restore that frame after the call.
-/
theorem framePreservingCallContract_framePreserved :
    ∀ (req : MirCallReq) (ans : MirCallAns),
      framePreservingCallContract.post req ans →
        ans.framePreserved req.memory := by
  intro req ans h_post
  cases ans with
  | returned _ _ => exact h_post.2
  | panicked _ => exact h_post
  | aborted => exact h_post

/--
`framePreservingCallContract` is satisfiable, so a certificate that assumes it
is not vacuous: the handler under which every external call returns an
initialized `retVal` and leaves memory unchanged implements it.
-/
theorem framePreservingCallContract_holdsOn_returnUnchanged
    (retVal : Value) (h_init : valueContainsUninit retVal = false := by rfl) :
    framePreservingCallContract.holdsOn
      (fun req => ITree.ret (.returned retVal req.memory)) :=
  holdsOn_of_envSatisfiesContract _ _ fun _ _ _ h_post =>
    DWLP.ret (h_post _ ⟨h_init, rfl, rfl, rfl, rfl, [], rfl⟩)

/--
Answers to the uninterpreted external calls along one execution path: the
`n`-th external call on the path returns `(answers n).1` or unwinds, in both
cases with post-call memory `(answers n).2` under the caller's restored call
frame.
-/
abbrev MirCallAnswerStream : Type := Nat → Value × Memory

/-- Prepend `answer` to `answers`. -/
def MirCallAnswerStream.cons
    (answer : Value × Memory) (answers : MirCallAnswerStream) :
    MirCallAnswerStream
  | 0 => answer
  | n + 1 => answers n

/-- Answer stream that returns `()` with `emptyMemory` at every call. -/
def MirCallAnswerStream.unitEmpty : MirCallAnswerStream :=
  fun _ => (.unit, emptyMemory)

/--
Computable bounded modular safe-panic checker over `MirExecState`: returns
`true` when every execution path from `st` stops within `fuel` steps at
`.ret .panic` or `.ret .abort`, without faulting and without returning
normally.

Unlike `reachesPanicExecBounded`, which stops at the first uninterpreted
external call `req`, it continues past the call on all three kinds of answer:
the callee returns `(answers 0).1`, the callee unwinds, or the callee aborts.
The returned and unwound branches resume with post-call memory
`restoreCallFrame req.memory (answers 0).2`, and every branch passes the rest of
the stream to later calls.

Proving `∀ answers, reachesModularSafePanicExecBounded fuel body answers st =
true` by kernel evaluation with `answers` free shows that no path inspects a
returned value or the non-frame part of a post-call memory. Such a proof yields
the modular certificate of
`wpMirExecFrameModularSym_of_reachesModularSafePanicExecBounded`, which covers
every answer that `framePreservingCallContract` permits.

Every branch carries the full remaining `fuel`, so a body with `n` reachable
external calls evaluates up to `3 ^ n` paths.
-/
def reachesModularSafePanicExecBounded
    (fuel : Nat)
    (body : CapturedMir)
    (answers : MirCallAnswerStream)
    (st : MirExecState) :
    Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret .panic => true
    | .ret .abort => true
    | .ret (.normal _) => false
    | .tau st' => reachesModularSafePanicExecBounded fuel' body answers st'
    | .vis (.inl _) _ => false
    | .vis (.inr (.inl _)) k =>
      reachesModularSafePanicExecBounded fuel' body answers (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) k =>
      let rest : MirCallAnswerStream := fun n => answers (n + 1)
      let memAfter := restoreCallFrame req.memory (answers 0).2
      Bool.and
        (reachesModularSafePanicExecBounded fuel' body rest
          (k (.returned (answers 0).1 memAfter)))
        (Bool.and
          (reachesModularSafePanicExecBounded fuel' body rest
            (k (.panicked memAfter)))
          (reachesModularSafePanicExecBounded fuel' body rest (k .aborted)))

/--
Soundness of `reachesModularSafePanicExecBounded`: if it returns `true` on every
answer stream, then the frame-restoring modular weakest precondition under
`framePreservingCallContract` holds with the vacuous normal-return
postcondition, so no answer that the contract permits leads to a fault or to a
normal return.

At an external call, the weakest precondition quantifies over each permitted
answer `ans` and resumes with `ans.restoreFrame req.memory`. The proof
instantiates the stream so that its head is the value and memory of `ans`,
which reproduces exactly that continuation; this is why the checker must
succeed on every stream rather than on one.
-/
theorem wpMirExecFrameModularSym_of_reachesModularSafePanicExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_check :
      ∀ answers : MirCallAnswerStream,
        (∀ n, valueContainsUninit (answers n).1 = false) →
        reachesModularSafePanicExecBounded fuel body answers st = true) :
    wpMirExecFrameModularSym framePreservingCallContract fuel body st
      (fun out => ∀ retVal mem', out = .normal (retVal, mem') → False) := by
  induction fuel generalizing st with
  | zero => nomatch h_check MirCallAnswerStream.unitEmpty (fun _ => rfl)
  | succ fuel ih =>
    unfold wpMirExecFrameModularSym
    rw [evalSymNodeTreeFrameModular_eq, stepMirExecFrameSymTree_eval]
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal _ =>
        have h := h_check MirCallAnswerStream.unitEmpty (fun _ => rfl)
        unfold reachesModularSafePanicExecBounded at h
        simp only [h_step] at h
        nomatch h
      | panic => intro _ _ h_eq; nomatch h_eq
      | abort => intro _ _ h_eq; nomatch h_eq
    | tau st' =>
      refine ih st' (fun answers h_init => ?_)
      have h := h_check answers h_init
      unfold reachesModularSafePanicExecBounded at h
      simp only [h_step] at h
      exact h
    | vis i k =>
      rcases i with f | (e | c)
      · have h := h_check MirCallAnswerStream.unitEmpty (fun _ => rfl)
        unfold reachesModularSafePanicExecBounded at h
        simp only [h_step] at h
        nomatch h
      · cases e
        refine ih (k PUnit.unit) (fun answers h_init => ?_)
        have h := h_check answers h_init
        unfold reachesModularSafePanicExecBounded at h
        simp only [h_step] at h
        exact h
      · rcases c with ⟨req⟩
        refine ⟨trivial, fun ans h_post => ?_⟩
        cases ans with
        | returned retVal memAfter =>
          refine ih _ (fun answers h_init => ?_)
          have h :=
            h_check (MirCallAnswerStream.cons (retVal, memAfter) answers) (by
              intro n
              cases n with
              | zero => exact h_post.1
              | succ m => exact h_init m)
          unfold reachesModularSafePanicExecBounded at h
          simp only [h_step, Bool.and_eq_true] at h
          exact h.1
        | panicked memAfter =>
          refine ih _ (fun answers h_init => ?_)
          have h :=
            h_check (MirCallAnswerStream.cons (.unit, memAfter) answers) (by
              intro n
              cases n with
              | zero => rfl
              | succ m => exact h_init m)
          unfold reachesModularSafePanicExecBounded at h
          simp only [h_step, Bool.and_eq_true] at h
          exact h.2.1
        | aborted =>
          refine ih _ (fun answers h_init => ?_)
          have h :=
            h_check (MirCallAnswerStream.cons (.unit, emptyMemory) answers) (by
              intro n
              cases n with
              | zero => rfl
              | succ m => exact h_init m)
          unfold reachesModularSafePanicExecBounded at h
          simp only [h_step, Bool.and_eq_true] at h
          exact h.2.2

/--
Computable bounded panic detector across external calls over `MirExecState`:
returns `true` when the execution path from `st` in which every uninterpreted
external call `req` answers `pick req` reaches `.ret .panic` within `fuel` steps
without faulting.

Unlike `reachesPanicExecBounded`, it does not stop at an external call. The
interaction tree constrains no answer, so the path it follows is a genuine path
of the tree for every `pick`.
-/
def reachesPanicAcrossCallsExecBounded
    (pick : MirCallReq → MirCallAns)
    (fuel : Nat)
    (body : CapturedMir)
    (st : MirExecState) :
    Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret .panic => true
    | .ret (.normal _) => false
    | .ret .abort => false
    | .tau st' => reachesPanicAcrossCallsExecBounded pick fuel' body st'
    | .vis (.inl _) _ => false
    | .vis (.inr (.inl _)) k =>
      reachesPanicAcrossCallsExecBounded pick fuel' body (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) k =>
      reachesPanicAcrossCallsExecBounded pick fuel' body (k (pick req))

/--
Computable bounded panic detector across external calls starting from
`s : MachineState`.
-/
def reachesPanicAcrossCallsBounded
    (pick : MirCallReq → MirCallAns)
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : Bool :=
  reachesPanicAcrossCallsExecBounded pick fuel body (.running s)

/--
Closed instance of both hypotheses of `verifyModularSafePanicMirBounded` from
`s : MachineState`, which `rfl` and `decide` can compute: the modular checker on
the answer stream `MirCallAnswerStream.unitEmpty`, and the panic detector on the
path where every external call returns `()` with unchanged memory.

Those hypotheses imply this check (`reachesModularSafePanicBounded_of_forall`),
so a `false` result shows that `verifyModularSafePanicMirBounded` cannot certify
`body` from `s` at this `fuel`. A `known_anneal_bug_ratchet` for a Miri `panic`
test requires such a result, so it fails to build once the certificate applies,
but it can still record a body that aborts or faults instead of panicking.
-/
def reachesModularSafePanicBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : Bool :=
  Bool.and
    (reachesModularSafePanicExecBounded fuel body MirCallAnswerStream.unitEmpty
      (.running s))
    (reachesPanicAcrossCallsBounded (fun req => .returned .unit req.memory)
      fuel body s)

/--
The hypotheses of `verifyModularSafePanicMirBounded` imply their closed instance
`reachesModularSafePanicBounded`.
-/
theorem reachesModularSafePanicBounded_of_forall
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (h_modular :
      ∀ answers : MirCallAnswerStream,
        (∀ n, valueContainsUninit (answers n).1 = false) →
        reachesModularSafePanicExecBounded fuel body answers (.running s) =
          true)
    (h_panic :
      reachesPanicAcrossCallsBounded (fun req => .returned .unit req.memory)
        fuel body s = true) :
    reachesModularSafePanicBounded fuel body s = true := by
  unfold reachesModularSafePanicBounded
  rw [h_modular MirCallAnswerStream.unitEmpty (fun _ => rfl), h_panic]
  rfl

/--
Soundness of `reachesPanicAcrossCallsExecBounded`: if it returns `true`, then
`ITree.cofix (stepMirState body) st` reaches `.ret .panic` along a finite trace
whose external-call events carry the answers `pick` chose.
-/
theorem reachesPanicAcrossCallsExecBounded_reachesRet
    (pick : MirCallReq → MirCallAns)
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_panic : reachesPanicAcrossCallsExecBounded pick fuel body st = true) :
    ∃ tr, ReachesRet (ITree.cofix (stepMirState body) st) tr .panic := by
  induction fuel generalizing st with
  | zero => nomatch h_panic
  | succ fuel' ih =>
    unfold reachesPanicAcrossCallsExecBounded at h_panic
    have h_obs :
        (ITree.cofix (stepMirState body) st).observe =
          (stepMirState body st).map (ITree.cofix (stepMirState body)) :=
      ITree.observe_cofix (stepMirState body) st
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal _ =>
        simp only [h_step] at h_panic
        nomatch h_panic
      | panic =>
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        exact ⟨[], _, Reaches.refl _, h_obs⟩
      | abort =>
        simp only [h_step] at h_panic
        nomatch h_panic
    | tau st' =>
      simp only [h_step] at h_panic
      rw [h_step] at h_obs
      dsimp only [ITreeF.map] at h_obs
      rcases ih st' h_panic with ⟨tr, u, h_reach, h_u⟩
      exact ⟨tr, u, Reaches.tau h_obs h_reach, h_u⟩
    | vis i k =>
      rcases i with f | (e | c)
      · simp only [h_step] at h_panic
        nomatch h_panic
      · simp only [h_step] at h_panic
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        rcases ih (k PUnit.unit) h_panic with ⟨tr, u, h_reach, h_u⟩
        exact ⟨⟨.inr (.inl e), PUnit.unit⟩ :: tr, u,
          Reaches.vis h_obs False.elim PUnit.unit h_reach, h_u⟩
      · rcases c with ⟨req⟩
        simp only [h_step] at h_panic
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        rcases ih (k (pick req)) h_panic with ⟨tr, u, h_reach, h_u⟩
        exact ⟨⟨.inr (.inr (.call req)), pick req⟩ :: tr, u,
          Reaches.vis h_obs False.elim (pick req) h_reach, h_u⟩

/--
Refute a total-correctness `c : TotalClaim` (`¬ c.holds`) by exhibiting a
concrete `(args, mem)` satisfying `c.pre args mem` whose bounded execution
unwinds to `.ret .panic` within `fuel` steps when each uninterpreted external
call `req` answers `pick req`. Like `refuteTotalClaimByBoundedPanic`, it assumes
nothing about external callees: `TotalClaim.holds` constrains every path of the
interaction tree, including the one that `pick` selects.
-/
theorem refuteTotalClaimByBoundedPanicAcrossCalls
    (c : TotalClaim)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_pre : c.pre args mem)
    (pick : MirCallReq → MirCallAns)
    (h_panic :
      reachesPanicAcrossCallsBounded pick fuel c.body
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees) =
          true := by
      rfl) :
    ¬ c.holds := by
  intro h_holds
  rcases reachesPanicAcrossCallsExecBounded_reachesRet pick fuel c.body _ h_panic
    with ⟨tr, h_ret⟩
  rcases (h_holds args mem h_pre).2.2.2 tr .panic h_ret with ⟨_, _, h_eq, _⟩
  nomatch h_eq

/-- One step of `reachesModularSafePanicExecBounded` after `stepMirState`. -/
def reachesModularSafePanicExecStep
    (fuel : Nat) (body : CapturedMir) (answers : MirCallAnswerStream)
    (node : MirStepNode) : Bool :=
  match node with
  | .ret .panic => true
  | .ret .abort => true
  | .ret (.normal _) => false
  | .tau st' => reachesModularSafePanicExecBounded fuel body answers st'
  | .vis (.inl _) _ => false
  | .vis (.inr (.inl _)) k =>
    reachesModularSafePanicExecBounded fuel body answers (k PUnit.unit)
  | .vis (.inr (.inr (.call req))) k =>
    Bool.and
      (reachesModularSafePanicExecBounded fuel body (fun n => answers (n + 1))
        (k (.returned (answers 0).1 (restoreCallFrame req.memory (answers 0).2))))
      (Bool.and
        (reachesModularSafePanicExecBounded fuel body (fun n => answers (n + 1))
          (k (.panicked (restoreCallFrame req.memory (answers 0).2))))
        (reachesModularSafePanicExecBounded fuel body (fun n => answers (n + 1))
          (k .aborted)))

theorem modular_call_branches_true {a b c : Bool}
    (ha : a = true) (hb : b = true) (hc : c = true) :
    Bool.and a (Bool.and b c) = true := by
  rw [ha, hb, hc]
  rfl

theorem reachesModularSafePanicExecBounded_succ
    (fuel : Nat) (body : CapturedMir) (answers : MirCallAnswerStream)
    (st : MirExecState) :
    reachesModularSafePanicExecBounded (fuel + 1) body answers st =
      reachesModularSafePanicExecStep fuel body answers (stepMirState body st) :=
  rfl

/-- Extract the initialized value of `locals[idx]`, or `.unit` otherwise. -/
def peekLocalInitOrUnit (locals : List LocalSlot) (idx : LocalIdx) : Value :=
  match Trusted.Sequence.get? locals idx with
  | .some (.init v) => v
  | _ => .unit

theorem evalOperands_cons_eq (locals : List LocalSlot) (op : Operand) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl) (callStack : List SavedCallerFrame) :
    evalOperands locals (op :: ops) borrows globals layouts callerLocals localDecls callStack =
      match evalOperand locals op borrows globals layouts callerLocals localDecls callStack with
      | .ok v locals' =>
        match evalOperands locals' ops borrows globals layouts callerLocals localDecls callStack with
        | .ok vs locals'' => .ok (v :: vs) locals''
        | .ub => .ub
        | .unsupported => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported := rfl

theorem evalOperand_move_nil_eq (locals : List LocalSlot) (idx : LocalIdx)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl) (callStack : List SavedCallerFrame) :
    evalOperand locals (.move { local_ := idx, projection := .nil })
      borrows globals layouts callerLocals localDecls callStack =
      match valueContainsUninit (peekLocalInitOrUnit locals idx) with
      | true => .ub
      | false =>
        match Trusted.Sequence.get? locals idx with
        | .some (.init v) =>
          match Trusted.Sequence.set? locals idx .uninit with
          | .some locals' => .ok v locals'
          | .none => .ub
        | .some .uninit => .ub
        | .some .dead => .ub
        | .none => .ub := by
  delta evalOperand peekLocalInitOrUnit
  dsimp only []
  cases Trusted.Sequence.get? locals idx with
  | none => rfl
  | some slot =>
    cases slot with
    | init v =>
      dsimp only []
      have h_r : readProjectedValue locals v .nil =
          match valueContainsUninit v with
          | false => .ok v
          | true => .ub := rfl
      rw [h_r]
      cases valueContainsUninit v <;> rfl
    | uninit => rfl
    | dead => rfl

theorem evalOperand_copy_nil_eq (locals : List LocalSlot) (idx : LocalIdx)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl) (callStack : List SavedCallerFrame) :
    evalOperand locals (.copy { local_ := idx, projection := .nil })
      borrows globals layouts callerLocals localDecls callStack =
      match valueContainsUninit (peekLocalInitOrUnit locals idx) with
      | true => .ub
      | false =>
        match Trusted.Sequence.get? locals idx with
        | .some (.init v) => .ok v locals
        | .some .uninit => .ub
        | .some .dead => .ub
        | .none => .ub := by
  delta evalOperand peekLocalInitOrUnit
  dsimp only []
  cases Trusted.Sequence.get? locals idx with
  | none => rfl
  | some slot =>
    cases slot with
    | init v =>
      dsimp only []
      have h_r : readProjectedValue locals v .nil =
          match valueContainsUninit v with
          | false => .ok v
          | true => .ub := rfl
      rw [h_r]
      cases valueContainsUninit v <;> rfl
    | uninit => rfl
    | dead => rfl

theorem reachesModularSafePanicExecStep_tau
    (fuel : Nat) (body : CapturedMir) (answers : MirCallAnswerStream) (st' : MirExecState) :
    reachesModularSafePanicExecStep fuel body answers (.tau st') =
      reachesModularSafePanicExecBounded fuel body answers st' := rfl

theorem reachesModularSafePanicExecStep_ret_panic
    (fuel : Nat) (body : CapturedMir) (answers : MirCallAnswerStream) :
    reachesModularSafePanicExecStep fuel body answers (.ret .panic) = true := rfl

theorem reachesModularSafePanicExecStep_ret_abort
    (fuel : Nat) (body : CapturedMir) (answers : MirCallAnswerStream) :
    reachesModularSafePanicExecStep fuel body answers (.ret .abort) = true := rfl

theorem reachesModularSafePanicExecStep_obs
    (fuel : Nat) (body : CapturedMir) (answers : MirCallAnswerStream)
    (obs : MirObsE.I) (k : PUnit → MirExecState) :
    reachesModularSafePanicExecStep fuel body answers (.vis (.inr (.inl obs)) k) =
      reachesModularSafePanicExecBounded fuel body answers (k PUnit.unit) := rfl

theorem reachesModularSafePanicExecStep_call
    (fuel : Nat) (body : CapturedMir) (answers : MirCallAnswerStream)
    (req : MirCallReq) (k : MirCallAns → MirExecState) :
    reachesModularSafePanicExecStep fuel body answers (.vis (.inr (.inr (.call req))) k) =
      Bool.and
        (reachesModularSafePanicExecBounded fuel body (fun n => answers (n + 1))
          (k (.returned (answers 0).1 (restoreCallFrame req.memory (answers 0).2))))
        (Bool.and
          (reachesModularSafePanicExecBounded fuel body (fun n => answers (n + 1))
            (k (.panicked (restoreCallFrame req.memory (answers 0).2))))
          (reachesModularSafePanicExecBounded fuel body (fun n => answers (n + 1))
            (k .aborted))) := rfl

/--
Certify a Miri `panic` test whose execution passes through uninterpreted
external calls, with linked `callees`, at `(args, mem)`. It proves both
1. `ModularVerificationResult` with `post := False` under
   `framePreservingCallContract.holdsOn`: for every external-call handler that
   returns an initialized value or unwinds to the caller's call frame (or
   aborts), execution never faults and never returns normally; and
2. `¬ TotalClaim.holds`, refuting total correctness.

`h_modular` discharges the first conjunct
(`wpMirExecFrameModularSym_of_reachesModularSafePanicExecBounded`). `h_panic`
discharges the second along the path on which each external call returns `.unit`
and leaves memory unchanged (`refuteTotalClaimByBoundedPanicAcrossCalls`).

A body that panics without an external call satisfies both hypotheses as well,
but `verifySafePanicMirPointBounded` certifies it with the stronger-looking
`StatefulVerificationResult`, which quantifies over every call answer.
-/
theorem verifyModularSafePanicMirBounded
    (body : CapturedMir)
    (callees : List CapturedMir)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_modular :
      ∀ answers : MirCallAnswerStream,
        (∀ n, valueContainsUninit (answers n).1 = false) →
        reachesModularSafePanicExecBounded fuel body answers
          (.running (initMachineStateWithMemoryAndCallees body args mem callees)) =
            true := by
      intro answers h_init
      repeat' (
        try (conv =>
          lhs; arg 4; whnf
          try (arg 1; dsimp only [advanceStmt, pushCalleeFrame, resumeExternalCall,
            resumeExternalDivergingCall, restoreCallFrame,
            initMachineStateWithMemoryAndCallees, initMachineStateWithMemory,
            initMachineState, emptyMemory]))
        rw [reachesModularSafePanicExecBounded_succ]
        (conv => lhs; arg 4; whnf)
        first
        | exact reachesModularSafePanicExecStep_ret_panic _ _ _
        | exact reachesModularSafePanicExecStep_ret_abort _ _ _
        | rw [reachesModularSafePanicExecStep_tau]
        | rw [reachesModularSafePanicExecStep_obs]
        | (rw [reachesModularSafePanicExecStep_call]; apply modular_call_branches_true)
        | (
            (conv =>
              lhs; arg 4
              simp (config := { decide := false }) only [
                evalOperandsWithBodyCast_cons, evalOperandsWithBodyCast_nil,
                evalOperandWithBodyCast_constant, evalOperandWithBodyCast_copy,
                evalOperandWithBodyCast_move_nil,
                evalOperands_cons_eq, evalOperand_move_nil_eq, evalOperand_copy_nil_eq])
            (conv in valueContainsUninit _ => arg 1; whnf)
            (conv =>
              lhs; arg 4
              simp (config := { decide := false }) only [h_init]
              whnf)
            first
            | exact reachesModularSafePanicExecStep_ret_panic _ _ _
            | exact reachesModularSafePanicExecStep_ret_abort _ _ _
            | rw [reachesModularSafePanicExecStep_tau]
            | rw [reachesModularSafePanicExecStep_obs]
            | (rw [reachesModularSafePanicExecStep_call]; apply modular_call_branches_true)
          )
      ))
    (h_panic :
      reachesPanicAcrossCallsBounded (fun req => .returned .unit req.memory)
        fuel body (initMachineStateWithMemoryAndCallees body args mem callees) =
          true := by
      rfl) :
    ModularVerificationResult
      { body := body
        envAssumed := framePreservingCallContract.holdsOn
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ _ _ => False
        callees := callees } ∧
    ¬ ({ body := body
         pre := fun a m => a = args ∧ m = mem
         post := fun _ _ _ _ => True
         callees := callees } : TotalClaim).holds := by
  refine ⟨?_, ?_⟩
  · refine verifyModularFrameContractWithCalleesMirSym
      framePreservingCallContract framePreservingCallContract_framePreserved
      body callees _ _ fuel ?_
    rintro a m ⟨rfl, rfl⟩
    exact wpMirExecFrameModularSym_of_reachesModularSafePanicExecBounded
      fuel body _ h_modular
  · exact refuteTotalClaimByBoundedPanicAcrossCalls
      { body := body
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ _ _ => True
        callees := callees }
      fuel args mem ⟨rfl, rfl⟩ (fun req => .returned .unit req.memory)
      h_panic

/--
If `(evalMirDiffExecBounded fuel body st).toTag = .normalUnit`, then
`wpCoalBounded` holds under `mirDefaultWP` with postcondition `.normal (.unit, mem')`.
-/
theorem wpCoalBounded_of_evalMirDiffExecBounded_normalUnit
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_ok : (evalMirDiffExecBounded fuel body st).toTag = .normalUnit) :
    wpCoalBounded fuel mirDefaultWP (stepMirState body)
      (fun out _ => ∃ retVal mem', out = .normal (retVal, mem') ∧ retVal = .unit)
      st PUnit.unit := by
  induction fuel generalizing st with
  | zero => nomatch h_ok
  | succ fuel' ih =>
    unfold evalMirDiffExecBounded at h_ok
    rw [stepMirStatePeriodic_eq] at h_ok
    unfold wpCoalBounded
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal p =>
        rcases p with ⟨rv, m⟩
        simp only [h_step] at h_ok ⊢
        cases rv with
        | unit => exact ⟨.unit, m, rfl, rfl⟩
        | scalar _ => nomatch h_ok
        | ptr _ _ => nomatch h_ok
        | aggregate _ _ => nomatch h_ok
        | uninit => nomatch h_ok
      | panic =>
        simp only [h_step] at h_ok
        nomatch h_ok
      | abort =>
        simp only [h_step] at h_ok
        nomatch h_ok
    | tau st' =>
      simp only [h_step] at h_ok ⊢
      exact ih st' h_ok
    | vis i k =>
      rcases i with f | (e | c)
      · rcases f with ⟨fk⟩
        cases fk <;> (simp only [h_step, MirDiffVerdict.toTag] at h_ok; nomatch h_ok)
      · simp only [h_step] at h_ok ⊢
        cases e
        exact ih (k PUnit.unit) h_ok
      · rcases c with ⟨req⟩
        simp only [h_step, MirDiffVerdict.toTag] at h_ok
        nomatch h_ok

/--
If `(evalMirDiffExecBounded fuel body st).toTag = .normalScalar bits sizeBytes`,
then `wpCoalBounded` holds under `mirDefaultWP` with postcondition
`.normal (.scalar ⟨bits, sizeBytes⟩, mem')`.
-/
theorem wpCoalBounded_of_evalMirDiffExecBounded_normalScalar
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (bits sizeBytes : Nat)
    (h_ok :
      (evalMirDiffExecBounded fuel body st).toTag =
        .normalScalar bits sizeBytes) :
    wpCoalBounded fuel mirDefaultWP (stepMirState body)
      (fun out _ =>
        ∃ retVal mem',
          out = .normal (retVal, mem') ∧
          retVal = .scalar { bits := bits, sizeBytes := sizeBytes })
      st PUnit.unit := by
  induction fuel generalizing st with
  | zero => nomatch h_ok
  | succ fuel' ih =>
    unfold evalMirDiffExecBounded at h_ok
    rw [stepMirStatePeriodic_eq] at h_ok
    unfold wpCoalBounded
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal p =>
        rcases p with ⟨rv, m⟩
        simp only [h_step] at h_ok ⊢
        cases rv with
        | unit => nomatch h_ok
        | scalar sc =>
          rcases sc with ⟨b, sz⟩
          dsimp only [MirDiffVerdict.toTag] at h_ok
          injection h_ok with h_b h_sz
          subst h_b
          subst h_sz
          exact ⟨.scalar { bits := b, sizeBytes := sz }, m, rfl, rfl⟩
        | ptr _ _ => nomatch h_ok
        | aggregate _ _ => nomatch h_ok
        | uninit => nomatch h_ok
      | panic =>
        simp only [h_step] at h_ok
        nomatch h_ok
      | abort =>
        simp only [h_step] at h_ok
        nomatch h_ok
    | tau st' =>
      simp only [h_step] at h_ok ⊢
      exact ih st' h_ok
    | vis i k =>
      rcases i with f | (e | c)
      · rcases f with ⟨fk⟩
        cases fk <;> (simp only [h_step, MirDiffVerdict.toTag] at h_ok; nomatch h_ok)
      · simp only [h_step] at h_ok ⊢
        cases e
        exact ih (k PUnit.unit) h_ok
      · rcases c with ⟨req⟩
        simp only [h_step, MirDiffVerdict.toTag] at h_ok
        nomatch h_ok

/--
`MirDiffVerdict.toTagWithBody` produces `.normalUnit` only when `v.toTag` is
already `.normalUnit`, because scalar-represented fieldless enum refinement maps
`.normal (.aggregate _ []) _` solely to `.normalScalar` or `.normalOther`.
-/
theorem MirDiffVerdict.toTag_eq_normalUnit_of_toTagWithBody
    (body : CapturedMir) (v : MirDiffVerdict)
    (h : v.toTagWithBody body = .normalUnit) :
    v.toTag = .normalUnit := by
  cases v with
  | normal rv mem =>
    cases rv with
    | unit => rfl
    | scalar _ => nomatch h
    | ptr _ _ => nomatch h
    | uninit => nomatch h
    | aggregate varIdx fields =>
      cases fields with
      | nil =>
        dsimp only [MirDiffVerdict.toTagWithBody] at h
        cases h_tag : scalarEnumReturnTag? body varIdx with
        | none =>
          rw [h_tag] at h
          nomatch h
        | some pair =>
          rcases pair with ⟨bits, sz⟩
          rw [h_tag] at h
          nomatch h
      | cons _ _ => nomatch h
  | panic => nomatch h
  | abort => nomatch h
  | ub => nomatch h
  | unsupported => nomatch h
  | externalCall _ => nomatch h
  | outOfFuel => nomatch h

/--
Certify a Miri `pass` test returning `()` at `(args, mem)`: proves
`TotalVerificationResult` via `evalMirDiffTagBounded ... = .normalUnit`.
-/
theorem verifyTotalMirUnitPointBounded
    (body : CapturedMir)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_ok :
      evalMirDiffTagBounded fuel body
        (initMachineStateWithMemory body args mem) = .normalUnit := by
      rfl) :
    TotalVerificationResult
      { body := body
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ retVal _ => retVal = .unit } := by
  refine verifyTotalMirBounded _ fuel ?_
  rintro a m ⟨rfl, rfl⟩
  exact wpCoalBounded_of_evalMirDiffExecBounded_normalUnit
    fuel body (.running (initMachineStateWithMemory body a m))
    (MirDiffVerdict.toTag_eq_normalUnit_of_toTagWithBody body _ h_ok)

/--
Certify a Miri `pass` test returning `.scalar ⟨bits, sizeBytes⟩` at
`(args, mem)`: proves `TotalVerificationResult` via
`(evalMirDiffBounded ...).toTag = .normalScalar bits sizeBytes`.
-/
theorem verifyTotalMirScalarPointBounded
    (body : CapturedMir)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (bits sizeBytes : Nat)
    (h_ok :
      (evalMirDiffBounded fuel body
        (initMachineStateWithMemory body args mem)).toTag =
          .normalScalar bits sizeBytes := by
      rfl) :
    TotalVerificationResult
      { body := body
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ retVal _ =>
          retVal = .scalar { bits := bits, sizeBytes := sizeBytes } } := by
  refine verifyTotalMirBounded _ fuel ?_
  rintro a m ⟨rfl, rfl⟩
  exact wpCoalBounded_of_evalMirDiffExecBounded_normalScalar
    fuel body (.running (initMachineStateWithMemory body a m))
    bits sizeBytes h_ok

/--
Soundness of `validateScalarEnumCandidate`: any `.some (outBits, outSz)` result
preserves `(bits, sz)` and establishes `bits < modulus` together with
`ScalarInt.inRange`.
-/
theorem validateScalarEnumCandidate_spec
    (bits sz modulus : Nat) (validRange : WrappingRange) (outBits outSz : Nat)
    (h :
      validateScalarEnumCandidate bits sz modulus validRange =
        .some (outBits, outSz)) :
    outBits = bits ∧
    outSz = sz ∧
    bits < modulus ∧
    ScalarInt.inRange { bits := bits, sizeBytes := sz } validRange = true := by
  unfold validateScalarEnumCandidate at h
  cases h_ble : Nat.ble (.succ bits) modulus with
  | false =>
    simp only [h_ble, Bool.false_and] at h
    nomatch h
  | true =>
    cases h_in :
        ScalarInt.inRange { bits := bits, sizeBytes := sz } validRange with
    | false =>
      simp only [h_ble, h_in, Bool.and_false] at h
      nomatch h
    | true =>
      simp only [h_ble, h_in, Bool.and_true] at h
      injection h with h_pair
      injection h_pair with h_b h_sz
      exact ⟨h_b.symm, h_sz.symm, Eq.mp Nat.ble_eq h_ble, rfl⟩

/--
Soundness of `scalarEnumReturnTag?`: whenever `scalarEnumReturnTag? body
variantIdx = .some (bits, sizeBytes)`, the return local permits a scalar-backed
enum, `1 ≤ sizeBytes ≤ 16`, `bits < scalarModulus sizeBytes`, and `body`'s
resolved return layout is an inhabited `sizeBytes`-byte integer
`BackendRepr.scalar (ScalarLayout.initialized (.int (sizeBytes * 8) _)
validRange)` containing `bits`.
-/
theorem scalarEnumReturnTag?_spec
    (body : CapturedMir) (variantIdx bits sizeBytes : Nat)
    (h : scalarEnumReturnTag? body variantIdx = .some (bits, sizeBytes)) :
    returnLocalAllowsScalarEnum body = true ∧
    0 < sizeBytes ∧
    sizeBytes ≤ 16 ∧
    bits < scalarModulus sizeBytes ∧
    ∃ retLayout isSigned validRange,
      resolveReturnLayout? body = .some retLayout ∧
      retLayout.isUninhabited = false ∧
      retLayout.size.bytes = sizeBytes ∧
      retLayout.backendRepr =
        .scalar
          (.initialized (.int (Nat.mul sizeBytes 8) isSigned) validRange) ∧
      ScalarInt.inRange
        { bits := bits, sizeBytes := sizeBytes } validRange = true := by
  unfold scalarEnumReturnTag? at h
  cases h_local : returnLocalAllowsScalarEnum body with
  | false =>
    simp only [h_local] at h
    nomatch h
  | true =>
    cases h_ret : resolveReturnLayout? body with
    | none =>
      simp only [h_local, h_ret] at h
      nomatch h
    | some retLayout =>
      simp only [h_local, h_ret] at h
      cases h_uninh : retLayout.isUninhabited with
      | true =>
        simp only [h_uninh] at h
        nomatch h
      | false =>
        cases h_sz : retLayout.size.bytes with
        | zero =>
          simp only [h_uninh, h_sz] at h
          nomatch h
        | succ szPred =>
          cases h_repr : retLayout.backendRepr with
          | memory =>
            simp only [h_uninh, h_sz, h_repr] at h
            nomatch h
          | scalarPair _ _ =>
            simp only [h_uninh, h_sz, h_repr] at h
            nomatch h
          | scalar sl =>
            cases sl with
            | union _ =>
              simp only [h_uninh, h_sz, h_repr] at h
              nomatch h
            | initialized pk validRange =>
              cases pk with
              | float _ =>
                simp only [h_uninh, h_sz, h_repr] at h
                nomatch h
              | pointer _ =>
                simp only [h_uninh, h_sz, h_repr] at h
                nomatch h
              | int primBits isSigned =>
                simp only [h_uninh, h_sz, h_repr] at h
                cases h_w : Nat.ble (.succ szPred) 16 with
                | false =>
                  simp only [h_w, Bool.false_and] at h
                  nomatch h
                | true =>
                  cases h_p : Nat.beq primBits (Nat.mul (.succ szPred) 8) with
                  | false =>
                    simp only [h_w, h_p, Bool.and_false] at h
                    nomatch h
                  | true =>
                    simp only [h_w, h_p, Bool.and_true] at h
                    cases h_cand :
                        scalarEnumCandidateBits?
                          body
                          retLayout
                          (.succ szPred)
                          (scalarModulus (.succ szPred))
                          isSigned
                          validRange
                          variantIdx with
                    | none =>
                      simp only [h_cand] at h
                      nomatch h
                    | some candBits =>
                      simp only [h_cand] at h
                      rcases validateScalarEnumCandidate_spec
                        candBits (.succ szPred) (scalarModulus (.succ szPred))
                        validRange bits sizeBytes h with
                        ⟨rfl, rfl, h_lt_mod, h_in⟩
                      have h_prim : primBits = Nat.mul (.succ szPred) 8 :=
                        Nat.eq_of_beq_eq_true h_p
                      subst h_prim
                      exact
                        ⟨ rfl
                        , Nat.zero_lt_succ szPred
                        , Eq.mp Nat.ble_eq h_w
                        , h_lt_mod
                        , ⟨retLayout, isSigned, validRange,
                            rfl, h_uninh, h_sz, h_repr, h_in⟩ ⟩

/--
Inversion lemma for `MirDiffVerdict.toTagWithBody`: a `.normalScalar bits
sizeBytes` tag arises only from a `.normal` return carrying either `.scalar
⟨bits, sizeBytes⟩` or a fieldless enum `.aggregate variantIdx []` whose
`scalarEnumReturnTag?` resolves to `(bits, sizeBytes)`.
-/
theorem MirDiffVerdict.eq_normal_of_toTagWithBody_normalScalar
    (body : CapturedMir) (v : MirDiffVerdict) (bits sizeBytes : Nat)
    (h : v.toTagWithBody body = .normalScalar bits sizeBytes) :
    ∃ retVal mem,
      v = .normal retVal mem ∧
      (retVal = .scalar { bits := bits, sizeBytes := sizeBytes } ∨
        ∃ variantIdx,
          retVal = .aggregate variantIdx .nil ∧
          scalarEnumReturnTag? body variantIdx = .some (bits, sizeBytes)) := by
  cases v with
  | normal rv mem =>
    cases rv with
    | unit => nomatch h
    | scalar sc =>
      rcases sc with ⟨b, sz⟩
      dsimp only [MirDiffVerdict.toTagWithBody, MirDiffVerdict.toTag] at h
      injection h with h_b h_sz
      subst h_b
      subst h_sz
      exact ⟨.scalar { bits := b, sizeBytes := sz }, mem, rfl, Or.inl rfl⟩
    | ptr _ _ => nomatch h
    | uninit => nomatch h
    | aggregate varIdx fields =>
      cases fields with
      | nil =>
        dsimp only [MirDiffVerdict.toTagWithBody] at h
        cases h_tag : scalarEnumReturnTag? body varIdx with
        | none =>
          rw [h_tag] at h
          nomatch h
        | some pair =>
          rcases pair with ⟨b, sz⟩
          rw [h_tag] at h
          injection h with h_b h_sz
          subst h_b
          subst h_sz
          exact
            ⟨.aggregate varIdx .nil, mem, rfl, Or.inr ⟨varIdx, rfl, h_tag⟩⟩
      | cons _ _ => nomatch h
  | panic => nomatch h
  | abort => nomatch h
  | ub => nomatch h
  | unsupported => nomatch h
  | externalCall _ => nomatch h
  | outOfFuel => nomatch h

/--
If `(evalMirDiffExecBounded fuel body st).toTagWithBody body = .normalScalar
bits sizeBytes`, then `wpCoalBounded` holds under `mirDefaultWP` with a normal
return carrying either `.scalar ⟨bits, sizeBytes⟩` or a scalar-represented
fieldless enum `.aggregate variantIdx []` with `scalarEnumReturnTag? body
variantIdx = .some (bits, sizeBytes)`.
-/
theorem wpCoalBounded_of_evalMirDiffExecBounded_toTagWithBody_normalScalar
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (bits sizeBytes : Nat)
    (h_ok :
      (evalMirDiffExecBounded fuel body st).toTagWithBody body =
        .normalScalar bits sizeBytes) :
    wpCoalBounded fuel mirDefaultWP (stepMirState body)
      (fun out _ =>
        ∃ retVal mem',
          out = .normal (retVal, mem') ∧
          (retVal = .scalar { bits := bits, sizeBytes := sizeBytes } ∨
            ∃ variantIdx,
              retVal = .aggregate variantIdx .nil ∧
              scalarEnumReturnTag? body variantIdx =
                .some (bits, sizeBytes)))
      st PUnit.unit := by
  induction fuel generalizing st with
  | zero => nomatch h_ok
  | succ fuel' ih =>
    unfold evalMirDiffExecBounded at h_ok
    rw [stepMirStatePeriodic_eq] at h_ok
    unfold wpCoalBounded
    cases h_step : stepMirState body st with
    | ret out =>
      cases out with
      | normal p =>
        rcases p with ⟨rv, m⟩
        simp only [h_step] at h_ok ⊢
        rcases MirDiffVerdict.eq_normal_of_toTagWithBody_normalScalar
          body (.normal rv m) bits sizeBytes h_ok with
          ⟨rv', m', h_eq, h_post⟩
        injection h_eq with h_rv h_m
        subst h_rv
        subst h_m
        exact ⟨rv, m, rfl, h_post⟩
      | panic =>
        simp only [h_step] at h_ok
        nomatch h_ok
      | abort =>
        simp only [h_step] at h_ok
        nomatch h_ok
    | tau st' =>
      simp only [h_step] at h_ok ⊢
      exact ih st' h_ok
    | vis i k =>
      rcases i with f | (e | c)
      · rcases f with ⟨fk⟩
        cases fk <;>
          (simp only [h_step, MirDiffVerdict.toTagWithBody,
            MirDiffVerdict.toTag] at h_ok; nomatch h_ok)
      · simp only [h_step] at h_ok ⊢
        cases e
        exact ih (k PUnit.unit) h_ok
      · rcases c with ⟨req⟩
        simp only [h_step, MirDiffVerdict.toTagWithBody,
          MirDiffVerdict.toTag] at h_ok
        nomatch h_ok

/--
Certify a Miri `pass` test reporting `MIRI_PASS:scalar:<bits>:<sizeBytes>` via
`evalMirDiffTagBounded`, covering both primitive `.scalar` returns and
scalar-represented fieldless enum `.aggregate variantIdx []` returns.
-/
theorem verifyTotalMirDiffScalarPointBounded
    (body : CapturedMir)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (bits sizeBytes : Nat)
    (h_ok :
      evalMirDiffTagBounded fuel body
        (initMachineStateWithMemory body args mem) =
          .normalScalar bits sizeBytes := by
      rfl) :
    TotalVerificationResult
      { body := body
        pre := fun a m => a = args ∧ m = mem
        post := fun _ _ retVal _ =>
          retVal = .scalar { bits := bits, sizeBytes := sizeBytes } ∨
            ∃ variantIdx,
              retVal = .aggregate variantIdx .nil ∧
              scalarEnumReturnTag? body variantIdx =
                .some (bits, sizeBytes) } := by
  refine verifyTotalMirBounded _ fuel ?_
  rintro a m ⟨rfl, rfl⟩
  exact wpCoalBounded_of_evalMirDiffExecBounded_toTagWithBody_normalScalar
    fuel body (.running (initMachineStateWithMemory body a m))
    bits sizeBytes h_ok

/--
Certify a Miri `fail` (Undefined Behavior) test at `(args, mem)`: proves that
both `StatefulClaim.holds` and `TotalClaim.holds` are refuted by reaching
`FailureKind.ub` (and specifically NOT `FailureKind.unsupported`).
-/
theorem refuteMirPointByStrictUB
    (body : CapturedMir)
    (fuel : Nat)
    (args : List Value)
    (mem : Memory)
    (h_ub :
      reachesStrictUBBounded fuel body
        (initMachineStateWithMemory body args mem) = true := by
      rfl) :
    ¬ ({ body := body
         pre := fun a m => a = args ∧ m = mem
         post := fun _ _ _ _ => True } : StatefulClaim).holds ∧
    ¬ ({ body := body
         pre := fun a m => a = args ∧ m = mem
         post := fun _ _ _ _ => True } : TotalClaim).holds :=
  ⟨refuteStatefulClaimByStrictUB _ fuel args mem ⟨rfl, rfl⟩ h_ub,
   refuteTotalClaimByStrictUB _ fuel args mem ⟨rfl, rfl⟩ h_ub⟩

/-!
## Signature & Polymorphic Obligation Adapter Lemmas and Kernel Checks
-/

/--
For a 1-argument `CapturedMir` body with `localDecls = retDecl :: d1 :: rest`,
`argsMatchSignature body [a] mem` reduces to `body.argCount = 1` and
`valueMatchesTyAndLayout defaultSignatureFuel body d1.ty d1.ty.layoutIdx a mem`.
-/
@[simp]
theorem argsMatchSignature_singleton
    (body : CapturedMir)
    (retDecl d1 : LocalDecl)
    (rest : List LocalDecl)
    (a : Value)
    (mem : Memory)
    (hDecls : body.localDecls = retDecl :: d1 :: rest)
    (hArgCount : body.argCount = 1) :
    Trusted.VerificationResult.argsMatchSignature body [a] mem ↔
      Trusted.VerificationResult.valueMatchesTyAndLayout
        Trusted.VerificationResult.defaultSignatureFuel
        body d1.ty d1.ty.layoutIdx a mem := by
  simp [Trusted.VerificationResult.argsMatchSignature, hDecls, hArgCount]

section SignatureValidationTests

open Trusted.VerificationResult

@[reducible]
private def testLayoutU32 : TypeLayout :=
  { size := ⟨4⟩
    align := ⟨4⟩
    backendRepr :=
      .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

@[reducible]
private def testLayoutBool : TypeLayout :=
  { size := ⟨1⟩
    align := ⟨1⟩
    backendRepr :=
      .scalar (.initialized (.int 8 false) ⟨0, 1⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

@[reducible]
private def testLayoutChar : TypeLayout :=
  { size := ⟨4⟩
    align := ⟨4⟩
    backendRepr :=
      .scalar (.initialized (.int 32 false) ⟨0, 1114111⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

@[reducible]
private def testLayoutRefU32 : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨8⟩
    backendRepr :=
      .scalar (.initialized (.pointer 0) ⟨1, 18446744073709551615⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [0] }

@[reducible]
private def testLayoutSliceU32 : TypeLayout :=
  { size := ⟨16⟩
    align := ⟨8⟩
    backendRepr :=
      .scalarPair
        (.initialized (.pointer 0) ⟨1, 18446744073709551615⟩)
        (.initialized (.int 64 false) ⟨0, 18446744073709551615⟩)
    fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [0] }

@[reducible]
private def testLayoutArrayU32x2 : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨4⟩
    backendRepr := .memory
    fields := .array ⟨4⟩ 2
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [0] }

@[reducible]
private def testLayoutTupleU32Bool : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨4⟩
    backendRepr :=
      .scalarPair
        (.initialized (.int 32 false) ⟨0, 4294967295⟩)
        (.initialized (.int 8 false) ⟨0, 1⟩)
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [0, 1] }

@[reducible]
private def testLayoutOptionU32 : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨4⟩
    backendRepr :=
      .scalarPair
        (.initialized (.int 32 false) ⟨0, 1⟩)
        (.initialized (.int 32 false) ⟨0, 4294967295⟩)
    fields := .arbitrary [⟨0⟩] [0]
    variants :=
      .multiple
        (.initialized (.int 32 false) ⟨0, 1⟩)
        0
        [.arbitrary [] [], .arbitrary [⟨4⟩] [0]]
    isUninhabited := false }

@[reducible]
private def testLayoutResultU32Bool : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨4⟩
    backendRepr :=
      .scalarPair
        (.initialized (.int 32 false) ⟨0, 1⟩)
        (.initialized (.int 32 false) ⟨0, 4294967295⟩)
    fields := .arbitrary [⟨0⟩] [0]
    variants :=
      .multiple
        (.initialized (.int 32 false) ⟨0, 1⟩)
        0
        [.arbitrary [⟨4⟩] [0], .arbitrary [⟨4⟩] [0]]
    isUninhabited := false }

@[reducible]
private def testLayoutFnPtr : TypeLayout :=
  { size := ⟨8⟩
    align := ⟨8⟩
    backendRepr :=
      .scalar (.initialized (.pointer 0) ⟨1, 18446744073709551615⟩)
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

@[reducible]
private def testLayoutPlaceholder : TypeLayout :=
  { size := ⟨0⟩
    align := ⟨0⟩
    backendRepr := .memory
    fields := .primitive
    variants := .empty
    isUninhabited := false }

@[reducible]
private def testLayoutTable : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [ testLayoutU32
      , testLayoutBool
      , testLayoutChar
      , testLayoutRefU32
      , testLayoutSliceU32
      , testLayoutArrayU32x2
      , testLayoutTupleU32Bool
      , testLayoutOptionU32
      , testLayoutResultU32Bool
      , testLayoutFnPtr
      , testLayoutPlaceholder
      ] }

@[reducible]
private def mkTestBody (argTy retTy : Ty) (tParams : Nat := 0) : CapturedMir :=
  { defPath := "test::item"
    phase := .runtimeOptimized
    role := .subject
    argCount := 1
    localDecls :=
      [ { mutability := .mut, ty := retTy, debugName := .none }
      , { mutability := .not, ty := argTy, debugName := .none }
      ]
    basicBlocks := []
    fnAbi :=
      { args := []
        ret := { layout := testLayoutU32, mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts := testLayoutTable
    allocations := []
    typeParamCount := tParams }

@[reducible]
private def testLiveMem8 : Memory :=
  { emptyMemory with
    globals :=
      [ { allocId := 1
          bytes :=
            [ .some 1, .some 0, .some 0, .some 0
            , .some 2, .some 0, .some 0, .some 0 ]
          relocations := []
          align := ⟨4⟩
          mutability := .mut } ]
    borrows :=
      [ { tag := 2
          targetLocal := 0
          targetProjection := []
          perm := .active } ]
    callerLocals :=
      [ .init (.scalar ⟨77, 4⟩) ] }

/-- Valid `bool`, `char`, and `u32` scalars satisfy `argsMatchSignature`, while
invalid `bool` (`2`), surrogate `char` (`0xD800`), and oversized `u32` bit
patterns are rejected. -/
theorem sig_scalars_validated :
    argsMatchSignature
      (mkTestBody ⟨.bool, 1⟩ ⟨.bool, 1⟩) [.scalar ⟨1, 1⟩] emptyMemory ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.bool, 1⟩ ⟨.bool, 1⟩) [.scalar ⟨2, 1⟩] emptyMemory ∧
    argsMatchSignature
      (mkTestBody ⟨.char, 2⟩ ⟨.char, 2⟩) [.scalar ⟨0x41, 4⟩] emptyMemory ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.char, 2⟩ ⟨.char, 2⟩) [.scalar ⟨0xD800, 4⟩] emptyMemory ∧
    argsMatchSignature
      (mkTestBody ⟨.uint .u32, 0⟩ ⟨.uint .u32, 0⟩)
      [.scalar ⟨42, 4⟩] emptyMemory ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.uint .u32, 0⟩ ⟨.uint .u32, 0⟩)
      [.scalar ⟨42, 1⟩] emptyMemory := by
  dsimp [emptyMemory]; decide

/-- Thin references `&u32` and `&mut u32` require a live, aligned allocation in
`mem.globals` or `mem.borrows`; unallocated or misaligned pointers are rejected. -/
theorem sig_thin_ref_validated :
    argsMatchSignature
      (mkTestBody ⟨.ref .not (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨1, 0⟩ 8]
      testLiveMem8 ∧
    argsMatchSignature
      (mkTestBody ⟨.ref .mut (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨2, 0⟩ 8]
      testLiveMem8 ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .not (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨1, 2⟩ 8]
      testLiveMem8 ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .not (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨77, 0⟩ 8]
      testLiveMem8 := by
  dsimp [emptyMemory]; decide

/-- Wide slices `&[u32]` require a 2-field aggregate `(dataPtr, len)` backed by
a live allocation of at least `len * 4` bytes with `len * 4 <= maxIsizeBytes`. -/
theorem sig_wide_slice_validated :
    argsMatchSignature
      (mkTestBody ⟨.ref .not (.slice (.uint .u32)), 4⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨2, 8⟩]]
      testLiveMem8 ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .not (.slice (.uint .u32)), 4⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨3, 8⟩]]
      testLiveMem8 ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .not (.slice (.uint .u32)), 4⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.ptr ⟨1, 0⟩ 8, .scalar ⟨0x4000000000000000, 8⟩]]
      testLiveMem8 := by
  dsimp [emptyMemory]; decide

/-- Fixed-size arrays `[u32; 2]`, tuples `(u32, bool)`, `Option<u32>`,
`Result<u32, bool>`, raw pointers `*const u32`, and `FnPtr` are structurally
constrained by `argsMatchSignature` and `retMatchesSignature`. -/
theorem sig_composites_and_adts_validated :
    argsMatchSignature
      (mkTestBody ⟨.array (.uint .u32) 2, 5⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩]]
      emptyMemory ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.array (.uint .u32) 2, 5⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.scalar ⟨10, 4⟩]]
      emptyMemory ∧
    argsMatchSignature
      (mkTestBody ⟨.tuple [.uint .u32, .bool], 6⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨1, 1⟩]]
      emptyMemory ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.tuple [.uint .u32, .bool], 6⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨2, 1⟩]]
      emptyMemory ∧
    argsMatchSignature
      (mkTestBody ⟨.adt "core::option::Option" [.uint .u32], 7⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 []]
      emptyMemory ∧
    argsMatchSignature
      (mkTestBody ⟨.adt "core::option::Option" [.uint .u32], 7⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 1 [.scalar ⟨99, 4⟩]]
      emptyMemory ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.adt "core::option::Option" [.uint .u32], 7⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 2 []]
      emptyMemory ∧
    retMatchesSignature
      (mkTestBody
        ⟨.uint .u32, 0⟩
        ⟨.adt "core::result::Result" [.uint .u32, .bool], 8⟩)
      (.aggregate 0 [.scalar ⟨7, 4⟩])
      emptyMemory ∧
    retMatchesSignature
      (mkTestBody
        ⟨.uint .u32, 0⟩
        ⟨.adt "core::result::Result" [.uint .u32, .bool], 8⟩)
      (.aggregate 1 [.scalar ⟨1, 1⟩])
      emptyMemory ∧
    ¬ retMatchesSignature
      (mkTestBody
        ⟨.uint .u32, 0⟩
        ⟨.adt "core::result::Result" [.uint .u32, .bool], 8⟩)
      (.aggregate 1 [.scalar ⟨2, 1⟩])
      emptyMemory ∧
    argsMatchSignature
      (mkTestBody ⟨.rawPtr .not (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨1, 0⟩ 8]
      emptyMemory ∧
    argsMatchSignature
      (mkTestBody
        ⟨.fnPtr [.uint .u32] (.uint .u32) .safe .rust, 9⟩
        ⟨.uint .u32, 0⟩)
      [.ptr ⟨99, 0⟩ 8]
      testLiveMem8 ∧
    ¬ argsMatchSignature
      (mkTestBody
        ⟨.fnPtr [.uint .u32] (.uint .u32) .safe .rust, 9⟩
        ⟨.uint .u32, 0⟩)
      [.ptr ⟨99, 4⟩ 8]
      testLiveMem8 := by
  set_option linter.unusedSimpArgs false in
  simp [
    emptyMemory,
    TypeLayout.isParamPlaceholder,
    wrappingRangeContains,
    primitiveKindByteWidth,
    scalarLayoutByteWidth,
    alignUp,
    maxNat
  ]

/-- Uninstantiated `RigidTy.param` is rejected (`False`), while instantiating
`polyBody` via `CapturedMir.instantiate` computes the concrete `TypeLayout` and
validates arguments and return values against the substituted type. -/
theorem sig_polymorphic_instantiate_validated :
    let polyBody := mkTestBody ⟨.param 0 "T", 10⟩ ⟨.param 0 "T", 10⟩ 1
    let subst : TypeSubst := [(.uint .u32, testLayoutU32)]
    ¬ argsMatchSignature polyBody [.scalar ⟨42, 4⟩] emptyMemory ∧
    argsMatchSignature
      (polyBody.instantiate subst)
      [.scalar ⟨42, 4⟩]
      emptyMemory ∧
    retMatchesSignature
      (polyBody.instantiate subst)
      (.scalar ⟨42, 4⟩)
      emptyMemory ∧
    ¬ argsMatchSignature
      (polyBody.instantiate subst)
      [.scalar ⟨1, 1⟩]
      emptyMemory := by
  set_option linter.unusedSimpArgs false in
  simp [
    emptyMemory,
    TypeLayout.isParamPlaceholder,
    wrappingRangeContains,
    primitiveKindByteWidth,
    scalarLayoutByteWidth,
    alignUp,
    maxNat,
    Trusted.Sequence.get?,
    Trusted.Sequence.length,
    UintTy.byteWidth,
    UintTy.bitWidth,
    IntTy.byteWidth,
    IntTy.bitWidth,
    FloatTy.byteWidth,
    appendTypeLayouts,
    setTypeLayoutAt,
    lookupFieldLayouts,
    computeArbitraryFieldsAux,
    computeUnionSizeAndAlign,
    computeAggregateBackendRepr,
    tagScalarByteWidth,
    recomputeVariantShapesAux,
    TypeLayout.recomputeFromFieldLayouts,
    Trusted.Rustc.V2026_06_01.Layout.substitutePlaceholderEntries,
    Trusted.Rustc.V2026_06_01.Layout.recomputeEntriesWith,
    LayoutTable.appendParamLayouts,
    LayoutTable.lookup,
    TypeSubst.lookup,
    TypeSubst.layouts,
    TypeSubst.length,
    RigidTy.instantiate,
    RigidTy.instantiateList,
    RigidTy.hasSubstParam,
    RigidTy.hasSubstParamList,
    RigidTy.isCompoundSubstParam,
    RigidTy.isTrivialZst,
    RigidTy.computeLayout,
    RigidTy.computeLayoutList,
    Trusted.Rustc.V2026_06_01.Layout.LayoutTable.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.LayoutTable.instantiate,
    Ty.instantiate,
    ConstOperand.instantiate,
    TraitRef.instantiate,
    TraitImplEntry.instantiate,
    TraitImplEntry.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.Place.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Operand.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Operand.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.AggregateKind.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Rvalue.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.NonDivergingIntrinsic.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.StatementKind.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Statement.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Statement.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.Terminator.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.LocalDecl.instantiate,
    Trusted.Rustc.V2026_06_01.MirAst.LocalDecl.instantiateList,
    Trusted.Rustc.V2026_06_01.MirAst.appendTys,
    Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.Place.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Operand.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Operand.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.AggregateKind.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Rvalue.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.NonDivergingIntrinsic.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.StatementKind.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Statement.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Statement.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.Terminator.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData.collectTys,
    Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.LocalDecl.collectTysList,
    Trusted.Rustc.V2026_06_01.MirAst.collectBodyTys,
    Trusted.Rustc.V2026_06_01.MirAst.hasNonParamTyAtIdx,
    Trusted.Rustc.V2026_06_01.MirAst.hasCompoundParamTyAtIdx,
    Trusted.Rustc.V2026_06_01.MirAst.substituteTyParamLayoutsAux,
    Trusted.Rustc.V2026_06_01.MirAst.recomputeTyCompoundLayoutsAux,
    Trusted.Rustc.V2026_06_01.MirAst.hasNonParamDeclAtIdx,
    Trusted.Rustc.V2026_06_01.MirAst.hasCompoundParamDeclAtIdx,
    Trusted.Rustc.V2026_06_01.MirAst.substituteDeclParamLayoutsAux,
    Trusted.Rustc.V2026_06_01.MirAst.recomputeDeclCompoundLayoutsAux,
    LayoutTable.instantiateForBody,
    LayoutTable.instantiateForDecls,
    Trusted.Rustc.V2026_06_01.MirAst.ArgAbi.recomputeMode,
    Trusted.Rustc.V2026_06_01.MirAst.ArgAbi.instantiateForDecl,
    Trusted.Rustc.V2026_06_01.MirAst.ArgAbi.instantiateListForDecls,
    Trusted.Rustc.V2026_06_01.MirAst.FnAbi.instantiate,
    dropGenericParams,
    CapturedMir.instantiate
  ]

/-- Sub-borrows into composite caller locals (`targetProjection != []` or
nonzero `offsetBytes`) and offset slice borrows (`&arr[1..3]`) check both the
lower (`entry.rangeOffset ≤ p.offsetBytes`) and upper
(`p.offsetBytes + size ≤ entry.rangeOffset + entry.rangeLen`) sub-range bounds
as well as array element byte capacity. -/
theorem sig_subborrow_and_slice_offset_validated :
    let subBorrowMem : Memory :=
      { emptyMemory with
        borrows :=
          [ { tag := 3
              targetLocal := 0
              targetProjection := [.index 1]
              perm := .active
              rangeOffset := 4
              rangeLen := 4 }
          , { tag := 4
              targetLocal := 0
              targetProjection := []
              perm := .frozen
              rangeOffset := 0
              rangeLen := 8 } ]
        callerLocals :=
          [ .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩]) ] }
    argsMatchSignature
      (mkTestBody ⟨.ref .mut (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨3, 4⟩ 8]
      subBorrowMem ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .mut (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨3, 0⟩ 8]
      subBorrowMem ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .mut (.uint .u32), 3⟩ ⟨.uint .u32, 0⟩)
      [.ptr ⟨3, 8⟩ 8]
      subBorrowMem ∧
    argsMatchSignature
      (mkTestBody ⟨.ref .not (.slice (.uint .u32)), 4⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.ptr ⟨4, 4⟩ 8, .scalar ⟨1, 8⟩]]
      subBorrowMem ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .not (.slice (.uint .u32)), 4⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.ptr ⟨3, 0⟩ 8, .scalar ⟨2, 8⟩]]
      subBorrowMem ∧
    ¬ argsMatchSignature
      (mkTestBody ⟨.ref .not (.slice (.uint .u32)), 4⟩ ⟨.uint .u32, 0⟩)
      [.aggregate 0 [.ptr ⟨4, 4⟩ 8, .scalar ⟨2, 8⟩]]
      subBorrowMem := by
  set_option linter.unusedSimpArgs false in
  simp [
    emptyMemory,
    TypeLayout.isParamPlaceholder,
    wrappingRangeContains,
    primitiveKindByteWidth,
    scalarLayoutByteWidth,
    alignUp,
    maxNat
  ]

end SignatureValidationTests

end Anneal.Rustc.V2026_06_01.SymbolicEval
