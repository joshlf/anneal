import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.EffectWP
import Anneal.ITreeWP
import Anneal.Rustc.V2026_06_01.Lower

namespace Anneal.Rustc.V2026_06_01.TraceCheck

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
open Anneal.Rustc.V2026_06_01.Lower

/-!
Executable trace-consistency checking, differential-testing triage diagnostics
(`TraceReplayDiag`), and byte-level runtime observer decoding for
`Trusted.Rustc.V2026_06_01` interaction trees (`mirTree`, `mirStatefulTree`,
and `mirObsErasedStatefulTree`).

This module connects runtime traces captured from compiled Rust artifacts to the
coinductive `MIR -> ITree` operational model along two axes:

1. **Interposition & Branch-Observation Modes**:
   - **Full trace checking (`checkBranches = true`)**: verifies that an observed
     trace of `TerminatorKind.switchInt` branch tags (`MirObsE`) and external
     procedure calls (`MirCallE`) is a valid execution path in `mirStatefulTree`
     (`reconstructFullMirTrace_sound`, `checkFullObservedTraceBounded_sound`).
   - **Branch-erased call-boundary checking (`checkBranches = false`)**: verifies
     that an observed trace of external procedure calls (`MirCallE`) and terminal
     outcomes is a valid execution path in `mirObsErasedStatefulTree`
     (`ITree.interp silenceMirObs (mirStatefulTree ...)`), allowing traces from
     optimized binaries where LLVM elides or reorders internal `switchInt`
     branches to be checked without false mismatches
     (`reconstructObsErasedMirTrace_sound`,
     `checkObsErasedObservedTraceBounded_sound`).
   - **Inlining duality (`inlinedCallees`)**: callees placed in `Memory.callees`
     are stepped transparently via `.tau` transitions, whereas callees omitted
     from `Memory.callees` are checked at `MirCallE` boundaries.

2. **Raw Byte & Shadow-Provenance Decoding**:
   - **Closed-world / value-only byte decoding**: decodes raw runtime `&[u8]`
     slices (`List UInt8`) for scalars, booleans, characters, tuples, arrays,
     and `repr(Rust)`/`repr(C)` structs and enums (ignoring uninitialized
     inter-field padding bytes while enforcing bit-validity and niche ranges)
     using `decodeValueFromBytes` and the compiler-extracted `LayoutTable` and
     `LocalDecl`s in `CapturedMir`.
   - **Shadow provenance table (`ShadowProvenanceTable`)**: translates native
     runtime virtual addresses in 8-byte thin pointers (`&T`, `&mut T`,
     `*const T`, `*mut T`) and 16-byte wide slice pointers (`&[T]`) into
     `AbstractByte.init` sequences annotated with abstract `(allocId, tag)`
     provenance and relative byte offset `addr - baseAddr`.

3. **Structured Differential-Testing Triage Diagnostics (`TraceReplayDiag`)**:
   - Pinpoints exact argument/event/outcome byte-decoding failures, operational
     faults (`FailureKind`, `blockIdx`, `stmtIdx`), unexpected external calls,
     call argument mismatches, `switchInt` branch tag mismatches, unconsumed
     trailing events, terminal outcome mismatches, and step-fuel exhaustion via
     `diagnoseObservedTraceBounded`, `diagnoseRawByteTraceBounded`,
     `diagnoseRawByteTraceFullBounded`, and
     `diagnoseRawByteTraceObsErasedBounded`.
-/

/-! ## 1. Computable Structural Equality & `DecidableEq`/`Repr` Instances -/

/-- Build a `DecidableEq` instance from a sound and reflexive boolean comparator. -/
@[reducible]
def decidableEqOfBoolEq {α : Type} (eqb : α → α → Bool)
    (h_sound : ∀ x y, eqb x y = true → x = y)
    (h_refl : ∀ x, eqb x x = true) : DecidableEq α :=
  fun x y =>
    if h : eqb x y = true then
      isTrue (h_sound x y h)
    else
      isFalse (fun heq => by subst heq; exact h (h_refl x))

/-- Computable structural equality on `ScalarInt`. -/
@[reducible]
def scalarIntEq (s₁ s₂ : ScalarInt) : Bool :=
  Nat.beq s₁.bits s₂.bits && Nat.beq s₁.sizeBytes s₂.sizeBytes

theorem scalarIntEq_sound {s₁ s₂ : ScalarInt}
    (h : scalarIntEq s₁ s₂ = true) : s₁ = s₂ := by
  cases s₁ with
  | mk b₁ sz₁ =>
    cases s₂ with
    | mk b₂ sz₂ =>
      unfold scalarIntEq at h
      revert h
      cases hb : Nat.beq b₁ b₂ <;> cases hsz : Nat.beq sz₁ sz₂ <;> intro h
      · nomatch h
      · nomatch h
      · nomatch h
      · rw [Nat.beq_eq.mp hb, Nat.beq_eq.mp hsz]

theorem scalarIntEq_refl (s : ScalarInt) : scalarIntEq s s = true := by
  cases s with
  | mk b sz =>
    unfold scalarIntEq
    rw [Nat.beq_refl b, Nat.beq_refl sz]
    rfl

instance instDecidableEqScalarInt : DecidableEq ScalarInt :=
  decidableEqOfBoolEq scalarIntEq (fun _ _ => scalarIntEq_sound) scalarIntEq_refl

instance instReprScalarInt : Repr ScalarInt where
  reprPrec s prec :=
    Repr.addAppParen ("ScalarInt.mk " ++ repr s.bits ++ " " ++ repr s.sizeBytes) prec

/-- Computable structural equality on `ProvenancePtr`. -/
@[reducible]
def provenancePtrEq (p₁ p₂ : ProvenancePtr) : Bool :=
  Nat.beq p₁.allocId p₂.allocId && Nat.beq p₁.offsetBytes p₂.offsetBytes

theorem provenancePtrEq_sound {p₁ p₂ : ProvenancePtr}
    (h : provenancePtrEq p₁ p₂ = true) : p₁ = p₂ := by
  cases p₁ with
  | mk a₁ o₁ =>
    cases p₂ with
    | mk a₂ o₂ =>
      unfold provenancePtrEq at h
      revert h
      cases ha : Nat.beq a₁ a₂ <;> cases ho : Nat.beq o₁ o₂ <;> intro h
      · nomatch h
      · nomatch h
      · nomatch h
      · rw [Nat.beq_eq.mp ha, Nat.beq_eq.mp ho]

theorem provenancePtrEq_refl (p : ProvenancePtr) : provenancePtrEq p p = true := by
  cases p with
  | mk a o =>
    unfold provenancePtrEq
    rw [Nat.beq_refl a, Nat.beq_refl o]
    rfl

instance instDecidableEqProvenancePtr : DecidableEq ProvenancePtr :=
  decidableEqOfBoolEq provenancePtrEq (fun _ _ => provenancePtrEq_sound) provenancePtrEq_refl

instance instReprProvenancePtr : Repr ProvenancePtr where
  reprPrec p prec :=
    Repr.addAppParen ("ProvenancePtr.mk " ++ repr p.allocId ++ " " ++ repr p.offsetBytes) prec

mutual
  /-- Computable structural equality on runtime `Value`s. -/
  @[reducible]
  def valueEq : Value → Value → Bool
    | .unit, .unit => true
    | .scalar s₁, .scalar s₂ => scalarIntEq s₁ s₂
    | .ptr p₁ sz₁, .ptr p₂ sz₂ =>
      provenancePtrEq p₁ p₂ && Nat.beq sz₁ sz₂
    | .aggregate v₁ fs₁, .aggregate v₂ fs₂ =>
      Nat.beq v₁ v₂ && valueListEq fs₁ fs₂
    | _, _ => false

  /-- Computable structural equality on `List Value`. -/
  @[reducible]
  def valueListEq : List Value → List Value → Bool
    | [], [] => true
    | v₁ :: vs₁, v₂ :: vs₂ => valueEq v₁ v₂ && valueListEq vs₁ vs₂
    | _, _ => false
end

mutual
  theorem valueEq_sound {v₁ v₂ : Value}
      (h : valueEq v₁ v₂ = true) : v₁ = v₂ := by
    cases v₁ with
    | unit =>
      cases v₂ with
      | unit => rfl
      | scalar _ => nomatch h
      | ptr _ _ => nomatch h
      | aggregate _ _ => nomatch h
    | scalar s₁ =>
      cases v₂ with
      | scalar s₂ =>
        exact congrArg Value.scalar (scalarIntEq_sound h)
      | _ => nomatch h
    | ptr p₁ sz₁ =>
      cases v₂ with
      | ptr p₂ sz₂ =>
        unfold valueEq at h
        revert h
        cases hp : provenancePtrEq p₁ p₂ <;> cases hsz : Nat.beq sz₁ sz₂ <;> intro h
        · nomatch h
        · nomatch h
        · nomatch h
        · rw [provenancePtrEq_sound hp, Nat.beq_eq.mp hsz]
      | _ => nomatch h
    | aggregate var₁ fs₁ =>
      cases v₂ with
      | aggregate var₂ fs₂ =>
        unfold valueEq at h
        revert h
        cases hv : Nat.beq var₁ var₂ <;> cases hfs : valueListEq fs₁ fs₂ <;> intro h
        · nomatch h
        · nomatch h
        · nomatch h
        · rw [Nat.beq_eq.mp hv, valueListEq_sound hfs]
      | _ => nomatch h

  theorem valueListEq_sound {vs₁ vs₂ : List Value}
      (h : valueListEq vs₁ vs₂ = true) : vs₁ = vs₂ := by
    cases vs₁ with
    | nil =>
      cases vs₂ with
      | nil => rfl
      | cons _ _ => nomatch h
    | cons v₁ rest₁ =>
      cases vs₂ with
      | nil => nomatch h
      | cons v₂ rest₂ =>
        unfold valueListEq at h
        revert h
        cases hv : valueEq v₁ v₂ <;> cases hrest : valueListEq rest₁ rest₂ <;> intro h
        · nomatch h
        · nomatch h
        · nomatch h
        · rw [valueEq_sound hv, valueListEq_sound hrest]
end

mutual
  theorem valueEq_refl : (v : Value) → valueEq v v = true
    | .unit => rfl
    | .scalar s => scalarIntEq_refl s
    | .ptr p sz => by
      unfold valueEq
      rw [provenancePtrEq_refl p, Nat.beq_refl sz]
      rfl
    | .aggregate var fs => by
      unfold valueEq
      rw [Nat.beq_refl var, valueListEq_refl fs]
      rfl

  theorem valueListEq_refl : (vs : List Value) → valueListEq vs vs = true
    | [] => rfl
    | v :: rest => by
      unfold valueListEq
      rw [valueEq_refl v, valueListEq_refl rest]
      rfl
end

instance instDecidableEqValue : DecidableEq Value :=
  decidableEqOfBoolEq valueEq (fun _ _ => valueEq_sound) valueEq_refl

/--
Single-step structural equality on `Value` parameterized by the list comparator
`ih`, defined with non-overlapping single-variable `match` expressions.
-/
@[reducible]
def valueHeadEq
    (ih : List Value → List Value → Bool) (v₁ v₂ : Value) : Bool :=
  match v₁ with
  | .unit =>
    match v₂ with
    | .unit => true
    | .scalar _ => false
    | .ptr _ _ => false
    | .aggregate _ _ => false
  | .scalar s₁ =>
    match v₂ with
    | .unit => false
    | .scalar s₂ => scalarIntEq s₁ s₂
    | .ptr _ _ => false
    | .aggregate _ _ => false
  | .ptr p₁ sz₁ =>
    match v₂ with
    | .unit => false
    | .scalar _ => false
    | .ptr p₂ sz₂ => provenancePtrEq p₁ p₂ && Nat.beq sz₁ sz₂
    | .aggregate _ _ => false
  | .aggregate var₁ fs₁ =>
    match v₂ with
    | .unit => false
    | .scalar _ => false
    | .ptr _ _ => false
    | .aggregate var₂ fs₂ => Nat.beq var₁ var₂ && ih fs₁ fs₂

/--
Fuel-bounded structural equality on `List Value`, defined via `Nat.rec` and
exhaustive single-variable `match` expressions so it lowers to non-dependent
`Nat.rec`, `List.casesOn`, and `Value.casesOn` without `.brecOn` or dependent
splitter motives.
-/
@[reducible]
def valueListEqFuel : Nat → List Value → List Value → Bool :=
  Nat.rec
    (motive := fun _ => List Value → List Value → Bool)
    (fun _ _ => false)
    (fun _ ih xs ys =>
      match xs with
      | [] =>
        match ys with
        | [] => true
        | _ :: _ => false
      | v₁ :: vs₁ =>
        match ys with
        | [] => false
        | v₂ :: vs₂ =>
          valueHeadEq ih v₁ v₂ && ih vs₁ vs₂)

/--
Fuel-bounded structural equality on runtime `Value`s without `Value.brecOn` or
dependent multi-variable splitter motives.
-/
@[reducible]
def valueEqFuel (fuel : Nat) (v₁ v₂ : Value) : Bool :=
  valueHeadEq (valueListEqFuel fuel) v₁ v₂

theorem valueHeadEq_sound
    {ih : List Value → List Value → Bool}
    (h_ih : ∀ {as bs}, ih as bs = true → as = bs)
    {v₁ v₂ : Value}
    (h : valueHeadEq ih v₁ v₂ = true) : v₁ = v₂ := by
  cases v₁ with
  | unit =>
    cases v₂ with
    | unit => rfl
    | scalar _ => nomatch h
    | ptr _ _ => nomatch h
    | aggregate _ _ => nomatch h
  | scalar s₁ =>
    cases v₂ with
    | unit => nomatch h
    | scalar s₂ => exact congrArg Value.scalar (scalarIntEq_sound h)
    | ptr _ _ => nomatch h
    | aggregate _ _ => nomatch h
  | ptr p₁ sz₁ =>
    cases v₂ with
    | unit => nomatch h
    | scalar _ => nomatch h
    | ptr p₂ sz₂ =>
      rcases Bool.and_eq_true_iff.mp h with ⟨hp, hsz⟩
      rw [provenancePtrEq_sound hp, Nat.beq_eq.mp hsz]
    | aggregate _ _ => nomatch h
  | aggregate var₁ fs₁ =>
    cases v₂ with
    | unit => nomatch h
    | scalar _ => nomatch h
    | ptr _ _ => nomatch h
    | aggregate var₂ fs₂ =>
      rcases Bool.and_eq_true_iff.mp h with ⟨hvar, hfs⟩
      rw [Nat.beq_eq.mp hvar, h_ih hfs]

theorem valueListEqFuel_sound :
    ∀ (fuel : Nat) {xs ys : List Value},
      valueListEqFuel fuel xs ys = true → xs = ys
  | 0, _, _, h => nomatch h
  | _ + 1, [], [], _ => rfl
  | _ + 1, [], _ :: _, h => nomatch h
  | _ + 1, _ :: _, [], h => nomatch h
  | fuel + 1, v₁ :: vs₁, v₂ :: vs₂, h => by
    change
      (valueHeadEq (valueListEqFuel fuel) v₁ v₂ &&
       valueListEqFuel fuel vs₁ vs₂) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨hHead, hTail⟩
    rw [valueHeadEq_sound (fun hfs => valueListEqFuel_sound fuel hfs) hHead,
        valueListEqFuel_sound fuel hTail]

theorem valueEqFuel_sound {fuel : Nat} {v₁ v₂ : Value}
    (h : valueEqFuel fuel v₁ v₂ = true) : v₁ = v₂ :=
  valueHeadEq_sound (fun hfs => valueListEqFuel_sound fuel hfs) h

mutual
  def reprValuePrec : Value → Nat → Std.Format
    | .unit, _ => "Value.unit"
    | .scalar s, prec =>
      Repr.addAppParen ("Value.scalar " ++ reprArg s) prec
    | .ptr p sz, prec =>
      Repr.addAppParen ("Value.ptr " ++ reprArg p ++ " " ++ repr sz) prec
    | .aggregate v fs, prec =>
      Repr.addAppParen ("Value.aggregate " ++ repr v ++ " [" ++ reprValueList fs ++ "]") prec

  def reprValueList : List Value → Std.Format
    | [] => ""
    | [v] => reprValuePrec v 0
    | v :: rest => reprValuePrec v 0 ++ ", " ++ reprValueList rest
end

instance instReprValue : Repr Value := ⟨reprValuePrec⟩

deriving instance DecidableEq, Repr for Size
deriving instance DecidableEq, Repr for Align
deriving instance DecidableEq, Repr for WrappingRange
deriving instance DecidableEq, Repr for PrimitiveKind
deriving instance DecidableEq, Repr for ScalarLayout
deriving instance DecidableEq, Repr for FieldsShape
deriving instance DecidableEq, Repr for VariantsShape
deriving instance DecidableEq, Repr for BackendRepr
deriving instance DecidableEq, Repr for TypeLayout
deriving instance DecidableEq, Repr for AbiPassMode
deriving instance DecidableEq, Repr for ArgAbi
deriving instance DecidableEq, Repr for CallConv
deriving instance DecidableEq, Repr for FnAbi
deriving instance DecidableEq, Repr for LayoutTable
deriving instance DecidableEq, Repr for UintTy
deriving instance DecidableEq, Repr for IntTy
deriving instance DecidableEq, Repr for FloatTy
deriving instance DecidableEq, Repr for Mutability
deriving instance DecidableEq, Repr for Safety

mutual
  @[reducible]
  def rigidTyEq : RigidTy → RigidTy → Bool
    | .bool, .bool => true
    | .char, .char => true
    | .int w₁, .int w₂ => decide (w₁ = w₂)
    | .uint w₁, .uint w₂ => decide (w₁ = w₂)
    | .float w₁, .float w₂ => decide (w₁ = w₂)
    | .never, .never => true
    | .str, .str => true
    | .tuple fs₁, .tuple fs₂ => rigidTyListEq fs₁ fs₂
    | .array e₁ n₁, .array e₂ n₂ => rigidTyEq e₁ e₂ && Nat.beq n₁ n₂
    | .slice e₁, .slice e₂ => rigidTyEq e₁ e₂
    | .ref m₁ p₁, .ref m₂ p₂ => decide (m₁ = m₂) && rigidTyEq p₁ p₂
    | .rawPtr m₁ p₁, .rawPtr m₂ p₂ => decide (m₁ = m₂) && rigidTyEq p₁ p₂
    | .adt d₁ a₁, .adt d₂ a₂ => (d₁ == d₂) && rigidTyListEq a₁ a₂
    | .fnDef d₁ a₁, .fnDef d₂ a₂ => (d₁ == d₂) && rigidTyListEq a₁ a₂
    | .fnPtr i₁ o₁ s₁ c₁, .fnPtr i₂ o₂ s₂ c₂ =>
      rigidTyListEq i₁ i₂ && rigidTyEq o₁ o₂ && decide (s₁ = s₂) && decide (c₁ = c₂)
    | .closure d₁ u₁, .closure d₂ u₂ => (d₁ == d₂) && rigidTyListEq u₁ u₂
    | .dynamic d₁, .dynamic d₂ => d₁ == d₂
    | .foreign d₁, .foreign d₂ => d₁ == d₂
    | .param i₁ n₁, .param i₂ n₂ => Nat.beq i₁ i₂ && (n₁ == n₂)
    | .alias d₁ a₁, .alias d₂ a₂ => (d₁ == d₂) && rigidTyListEq a₁ a₂
    | .other s₁, .other s₂ => s₁ == s₂
    | _, _ => false

  @[reducible]
  def rigidTyListEq : List RigidTy → List RigidTy → Bool
    | [], [] => true
    | t₁ :: ts₁, t₂ :: ts₂ => rigidTyEq t₁ t₂ && rigidTyListEq ts₁ ts₂
    | _, _ => false
end

mutual
  theorem rigidTyEq_sound {t₁ t₂ : RigidTy}
      (h : rigidTyEq t₁ t₂ = true) : t₁ = t₂ := by
    cases t₁ with
    | bool => cases t₂ with | bool => rfl | _ => nomatch h
    | char => cases t₂ with | char => rfl | _ => nomatch h
    | never => cases t₂ with | never => rfl | _ => nomatch h
    | str => cases t₂ with | str => rfl | _ => nomatch h
    | int w₁ =>
      cases t₂ with
      | int w₂ => exact congrArg RigidTy.int (of_decide_eq_true h)
      | _ => nomatch h
    | uint w₁ =>
      cases t₂ with
      | uint w₂ => exact congrArg RigidTy.uint (of_decide_eq_true h)
      | _ => nomatch h
    | float w₁ =>
      cases t₂ with
      | float w₂ => exact congrArg RigidTy.float (of_decide_eq_true h)
      | _ => nomatch h
    | tuple fs₁ =>
      cases t₂ with
      | tuple fs₂ => exact congrArg RigidTy.tuple (rigidTyListEq_sound h)
      | _ => nomatch h
    | array e₁ n₁ =>
      cases t₂ with
      | array e₂ n₂ =>
        unfold rigidTyEq at h
        revert h
        cases he : rigidTyEq e₁ e₂ <;> cases hn : Nat.beq n₁ n₂ <;> intro h
        · nomatch h
        · nomatch h
        · nomatch h
        · rw [rigidTyEq_sound he, Nat.beq_eq.mp hn]
      | _ => nomatch h
    | slice e₁ =>
      cases t₂ with
      | slice e₂ => exact congrArg RigidTy.slice (rigidTyEq_sound h)
      | _ => nomatch h
    | ref m₁ p₁ =>
      cases t₂ with
      | ref m₂ p₂ =>
        unfold rigidTyEq at h
        revert h
        cases hm : decide (m₁ = m₂) <;> cases hp : rigidTyEq p₁ p₂ <;> intro h
        · nomatch h
        · nomatch h
        · nomatch h
        · rw [of_decide_eq_true hm, rigidTyEq_sound hp]
      | _ => nomatch h
    | rawPtr m₁ p₁ =>
      cases t₂ with
      | rawPtr m₂ p₂ =>
        unfold rigidTyEq at h
        revert h
        cases hm : decide (m₁ = m₂) <;> cases hp : rigidTyEq p₁ p₂ <;> intro h
        · nomatch h
        · nomatch h
        · nomatch h
        · rw [of_decide_eq_true hm, rigidTyEq_sound hp]
      | _ => nomatch h
    | adt d₁ a₁ =>
      cases t₂ with
      | adt d₂ a₂ =>
        unfold rigidTyEq at h
        revert h
        cases hd : (d₁ == d₂) <;> cases ha : rigidTyListEq a₁ a₂ <;> intro h
        · nomatch h
        · nomatch h
        · nomatch h
        · rw [beq_iff_eq.mp hd, rigidTyListEq_sound ha]
      | _ => nomatch h
    | fnDef d₁ a₁ =>
      cases t₂ with
      | fnDef d₂ a₂ =>
        unfold rigidTyEq at h
        revert h
        cases hd : (d₁ == d₂) <;> cases ha : rigidTyListEq a₁ a₂ <;> intro h
        · nomatch h
        · nomatch h
        · nomatch h
        · rw [beq_iff_eq.mp hd, rigidTyListEq_sound ha]
      | _ => nomatch h
    | fnPtr i₁ o₁ s₁ conv₁ =>
      cases t₂ with
      | fnPtr i₂ o₂ s₂ conv₂ =>
        unfold rigidTyEq at h
        revert h
        cases hi : rigidTyListEq i₁ i₂
        · intro h; nomatch h
        · cases ho : rigidTyEq o₁ o₂
          · intro h; nomatch h
          · cases hs : decide (s₁ = s₂)
            · intro h; nomatch h
            · cases hc : decide (conv₁ = conv₂)
              · intro h; nomatch h
              · intro _
                rw [rigidTyListEq_sound hi, rigidTyEq_sound ho,
                  of_decide_eq_true hs, of_decide_eq_true hc]
      | _ => nomatch h
    | closure d₁ u₁ =>
      cases t₂ with
      | closure d₂ u₂ =>
        unfold rigidTyEq at h
        revert h
        cases hd : (d₁ == d₂) <;> cases hu : rigidTyListEq u₁ u₂ <;> intro h
        · nomatch h
        · nomatch h
        · nomatch h
        · rw [beq_iff_eq.mp hd, rigidTyListEq_sound hu]
      | _ => nomatch h
    | dynamic d₁ =>
      cases t₂ with
      | dynamic d₂ => exact congrArg RigidTy.dynamic (beq_iff_eq.mp h)
      | _ => nomatch h
    | foreign d₁ =>
      cases t₂ with
      | foreign d₂ => exact congrArg RigidTy.foreign (beq_iff_eq.mp h)
      | _ => nomatch h
    | param i₁ n₁ =>
      cases t₂ with
      | param i₂ n₂ =>
        unfold rigidTyEq at h
        revert h
        cases hi : Nat.beq i₁ i₂ <;> cases hn : (n₁ == n₂) <;> intro h
        · nomatch h
        · nomatch h
        · nomatch h
        · rw [Nat.beq_eq.mp hi, beq_iff_eq.mp hn]
      | _ => nomatch h
    | alias d₁ a₁ =>
      cases t₂ with
      | alias d₂ a₂ =>
        unfold rigidTyEq at h
        revert h
        cases hd : (d₁ == d₂) <;> cases ha : rigidTyListEq a₁ a₂ <;> intro h
        · nomatch h
        · nomatch h
        · nomatch h
        · rw [beq_iff_eq.mp hd, rigidTyListEq_sound ha]
      | _ => nomatch h
    | other s₁ =>
      cases t₂ with
      | other s₂ => exact congrArg RigidTy.other (beq_iff_eq.mp h)
      | _ => nomatch h

  theorem rigidTyListEq_sound {ts₁ ts₂ : List RigidTy}
      (h : rigidTyListEq ts₁ ts₂ = true) : ts₁ = ts₂ := by
    cases ts₁ with
    | nil =>
      cases ts₂ with
      | nil => rfl
      | cons _ _ => nomatch h
    | cons t₁ rest₁ =>
      cases ts₂ with
      | nil => nomatch h
      | cons t₂ rest₂ =>
        unfold rigidTyListEq at h
        revert h
        cases ht : rigidTyEq t₁ t₂ <;> cases hrest : rigidTyListEq rest₁ rest₂ <;> intro h
        · nomatch h
        · nomatch h
        · nomatch h
        · rw [rigidTyEq_sound ht, rigidTyListEq_sound hrest]
end

mutual
  theorem rigidTyEq_refl : (t : RigidTy) → rigidTyEq t t = true
    | .bool => rfl
    | .char => rfl
    | .int w => by unfold rigidTyEq; exact decide_eq_true rfl
    | .uint w => by unfold rigidTyEq; exact decide_eq_true rfl
    | .float w => by unfold rigidTyEq; exact decide_eq_true rfl
    | .never => rfl
    | .str => rfl
    | .tuple fs => rigidTyListEq_refl fs
    | .array e n => by unfold rigidTyEq; rw [rigidTyEq_refl e, Nat.beq_refl n]; rfl
    | .slice e => rigidTyEq_refl e
    | .ref m p => by unfold rigidTyEq; rw [decide_eq_true rfl, rigidTyEq_refl p]; rfl
    | .rawPtr m p => by unfold rigidTyEq; rw [decide_eq_true rfl, rigidTyEq_refl p]; rfl
    | .adt d a => by unfold rigidTyEq; rw [beq_self_eq_true d, rigidTyListEq_refl a]; rfl
    | .fnDef d a => by unfold rigidTyEq; rw [beq_self_eq_true d, rigidTyListEq_refl a]; rfl
    | .fnPtr i o s conv => by
      unfold rigidTyEq
      rw [rigidTyListEq_refl i, rigidTyEq_refl o, decide_eq_true rfl, decide_eq_true rfl]
      rfl
    | .closure d u => by unfold rigidTyEq; rw [beq_self_eq_true d, rigidTyListEq_refl u]; rfl
    | .dynamic d => beq_self_eq_true d
    | .foreign d => beq_self_eq_true d
    | .param i n => by unfold rigidTyEq; rw [Nat.beq_refl i, beq_self_eq_true n]; rfl
    | .alias d a => by unfold rigidTyEq; rw [beq_self_eq_true d, rigidTyListEq_refl a]; rfl
    | .other s => beq_self_eq_true s

  theorem rigidTyListEq_refl : (ts : List RigidTy) → rigidTyListEq ts ts = true
    | [] => rfl
    | t :: rest => by unfold rigidTyListEq; rw [rigidTyEq_refl t, rigidTyListEq_refl rest]; rfl
end

instance instDecidableEqRigidTy : DecidableEq RigidTy :=
  decidableEqOfBoolEq rigidTyEq (fun _ _ => rigidTyEq_sound) rigidTyEq_refl

instance instReprRigidTy : Repr RigidTy where
  reprPrec _ _ := "RigidTy"

@[reducible]
def intTyTag : IntTy → Nat
  | .isize => 0 | .i8 => 1 | .i16 => 2 | .i32 => 3 | .i64 => 4 | .i128 => 5

@[reducible]
def intTyEq (a b : IntTy) : Bool := Nat.beq (intTyTag a) (intTyTag b)

@[reducible]
def uintTyTag : UintTy → Nat
  | .usize => 0 | .u8 => 1 | .u16 => 2 | .u32 => 3 | .u64 => 4 | .u128 => 5

@[reducible]
def uintTyEq (a b : UintTy) : Bool := Nat.beq (uintTyTag a) (uintTyTag b)

@[reducible]
def floatTyTag : FloatTy → Nat
  | .f16 => 0 | .f32 => 1 | .f64 => 2 | .f128 => 3

@[reducible]
def floatTyEq (a b : FloatTy) : Bool := Nat.beq (floatTyTag a) (floatTyTag b)

@[reducible]
def mutabilityTag : Mutability → Nat
  | .not => 0 | .mut => 1

@[reducible]
def mutabilityEq (a b : Mutability) : Bool := Nat.beq (mutabilityTag a) (mutabilityTag b)

@[reducible]
def safetyTag : Safety → Nat
  | .safe => 0 | .unsafe_ => 1

@[reducible]
def safetyEq (a b : Safety) : Bool := Nat.beq (safetyTag a) (safetyTag b)

@[reducible]
def callConvEq (a b : CallConv) : Bool :=
  match a with
  | .rust =>
    match b with
    | .rust => true | .c => false | .rustIntrinsic => false | .other _ => false
  | .c =>
    match b with
    | .rust => false | .c => true | .rustIntrinsic => false | .other _ => false
  | .rustIntrinsic =>
    match b with
    | .rust => false | .c => false | .rustIntrinsic => true | .other _ => false
  | .other s₁ =>
    match b with
    | .rust => false | .c => false | .rustIntrinsic => false | .other s₂ => stringEq s₁ s₂

@[reducible]
def rigidTyTag : RigidTy → Nat
  | .bool => 0
  | .char => 1
  | .int _ => 2
  | .uint _ => 3
  | .float _ => 4
  | .never => 5
  | .str => 6
  | .tuple _ => 7
  | .array _ _ => 8
  | .slice _ => 9
  | .ref _ _ => 10
  | .rawPtr _ _ => 11
  | .adt _ _ => 12
  | .fnDef _ _ => 13
  | .fnPtr _ _ _ _ => 14
  | .closure _ _ => 15
  | .dynamic _ => 16
  | .foreign _ => 17
  | .other _ => 18
  | .param _ _ => 19
  | .alias _ _ => 20
    
/--
Fuel-bounded structural equality on `List RigidTy`, defined via `Nat.rec` and
non-overlapping `match` expressions without `RigidTy.brecOn` or dependent
splitter motives.
-/
@[reducible]
def rigidTyListEqFuel : Nat → List RigidTy → List RigidTy → Bool :=
  Nat.rec
    (motive := fun _ => List RigidTy → List RigidTy → Bool)
    (fun _ _ => false)
    (fun _ ih xs ys =>
      match xs with
      | [] =>
        match ys with
        | [] => true
        | _ :: _ => false
      | t₁ :: ts₁ =>
        match ys with
        | [] => false
        | t₂ :: ts₂ =>
          let headEq : Bool :=
            if Nat.beq (rigidTyTag t₁) (rigidTyTag t₂) then
              match t₁ with
              | .bool => true
              | .char => true
              | .int w₁ =>
                match t₂ with
                | .int w₂ => intTyEq w₁ w₂
                | .bool | .char | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .uint w₁ =>
                match t₂ with
                | .uint w₂ => uintTyEq w₁ w₂
                | .bool | .char | .int _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .float w₁ =>
                match t₂ with
                | .float w₂ => floatTyEq w₁ w₂
                | .bool | .char | .int _ | .uint _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .never => true
              | .str => true
              | .tuple fs₁ =>
                match t₂ with
                | .tuple fs₂ => ih fs₁ fs₂
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .array e₁ n₁ =>
                match t₂ with
                | .array e₂ n₂ => ih [e₁] [e₂] && Nat.beq n₁ n₂
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .slice e₁ =>
                match t₂ with
                | .slice e₂ => ih [e₁] [e₂]
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .ref m₁ p₁ =>
                match t₂ with
                | .ref m₂ p₂ => mutabilityEq m₁ m₂ && ih [p₁] [p₂]
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .rawPtr m₁ p₁ =>
                match t₂ with
                | .rawPtr m₂ p₂ => mutabilityEq m₁ m₂ && ih [p₁] [p₂]
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .adt d₁ a₁ =>
                match t₂ with
                | .adt d₂ a₂ => stringEq d₁ d₂ && ih a₁ a₂
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .fnDef d₁ a₁ =>
                match t₂ with
                | .fnDef d₂ a₂ => stringEq d₁ d₂ && ih a₁ a₂
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .fnPtr i₁ o₁ s₁ c₁ =>
                match t₂ with
                | .fnPtr i₂ o₂ s₂ c₂ =>
                  ih (o₁ :: i₁) (o₂ :: i₂) && safetyEq s₁ s₂ && callConvEq c₁ c₂
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .closure d₁ u₁ =>
                match t₂ with
                | .closure d₂ u₂ => stringEq d₁ d₂ && ih u₁ u₂
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .dynamic d₁ =>
                match t₂ with
                | .dynamic d₂ => stringEq d₁ d₂
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
              | .foreign d₁ =>
                match t₂ with
                | .foreign d₂ => stringEq d₁ d₂
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .other _ | .param _ _ | .alias _ _ => false
              | .other s₁ =>
                match t₂ with
                | .other s₂ => stringEq s₁ s₂
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .param _ _ | .alias _ _ => false
              | .param idx1 name1 =>
                match t₂ with
                | .param idx2 name2 => Nat.beq idx1 idx2 && stringEq name1 name2
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .alias _ _ => false
              | .alias d1 a1 =>
                match t₂ with
                | .alias d2 a2 => stringEq d1 d2 && ih a1 a2
                | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
                | .tuple _ | .array _ _ | .slice _ | .ref _ _ | .rawPtr _ _
                | .adt _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
                | .dynamic _ | .foreign _ | .other _ | .param _ _ => false

            else
              false
          headEq && ih ts₁ ts₂)

/-- Fuel-bounded structural equality on `RigidTy` without `RigidTy.brecOn`. -/
@[reducible]
def rigidTyEqFuel (fuel : Nat) (t₁ t₂ : RigidTy) : Bool :=
  rigidTyListEqFuel fuel [t₁] [t₂]

deriving instance DecidableEq, Repr for Ty
deriving instance DecidableEq, Repr for GenericParamDef
deriving instance DecidableEq, Repr for TraitRef
deriving instance DecidableEq, Repr for TraitImplEntry
deriving instance DecidableEq, Repr for ConstScalar
deriving instance DecidableEq, Repr for ConstValue
deriving instance DecidableEq, Repr for ConstOperand
deriving instance DecidableEq, Repr for MirPhaseTag
deriving instance DecidableEq, Repr for ContractRole
deriving instance DecidableEq, Repr for ProjectionElem
deriving instance DecidableEq, Repr for Place
deriving instance DecidableEq, Repr for Operand
deriving instance DecidableEq, Repr for BinOp
deriving instance DecidableEq, Repr for UnOp
deriving instance DecidableEq, Repr for NullOp
deriving instance DecidableEq, Repr for BorrowKind
deriving instance DecidableEq, Repr for CastKind
deriving instance DecidableEq, Repr for AggregateKind
deriving instance DecidableEq, Repr for Rvalue
deriving instance DecidableEq, Repr for NonDivergingIntrinsic
deriving instance DecidableEq, Repr for RetagKind
deriving instance DecidableEq, Repr for StatementKind
deriving instance DecidableEq, Repr for Statement
deriving instance DecidableEq, Repr for SwitchTargets
deriving instance DecidableEq, Repr for UnwindAction
deriving instance DecidableEq, Repr for TerminatorKind
deriving instance DecidableEq, Repr for Terminator
deriving instance DecidableEq, Repr for BasicBlockData
deriving instance DecidableEq, Repr for LocalDecl
deriving instance DecidableEq, Repr for CapturedAllocation
deriving instance DecidableEq, Repr for CapturedMir
deriving instance DecidableEq, Repr for MirObs
deriving instance DecidableEq, Repr for LocalSlot
deriving instance DecidableEq, Repr for StackFrame
deriving instance DecidableEq, Repr for TreeBorrowPerm
deriving instance DecidableEq, Repr for BorrowEntry
deriving instance DecidableEq, Repr for SavedCallerFrame
deriving instance DecidableEq, Repr for FnPtrEntry
deriving instance DecidableEq, Repr for Memory
deriving instance DecidableEq, Repr for MachineState
deriving instance DecidableEq, Repr for MirCallReq
deriving instance DecidableEq, Repr for MirCallAns

/-- `DecidableEq` instance for completed `MirEffect` interaction events. -/
instance instDecidableEqEventMirEffect : DecidableEq (Event MirEffect)
  | ⟨req₁, ans₁⟩, ⟨req₂, ans₂⟩ =>
    match req₁, req₂ with
    | .inl (.fail f₁), .inl (.fail f₂) =>
      if h : f₁ = f₂ then
        isTrue (by cases h; cases ans₁)
      else
        isFalse (fun heq => by cases heq; exact h rfl)
    | .inr (.inl (.emit o₁)), .inr (.inl (.emit o₂)) =>
      if h : o₁ = o₂ then
        isTrue (by cases h; cases ans₁; cases ans₂; rfl)
      else
        isFalse (fun heq => by cases heq; exact h rfl)
    | .inr (.inr (.call r₁)), .inr (.inr (.call r₂)) =>
      if hr : r₁ = r₂ then
        let a₁ : MirCallAns := ans₁
        let a₂ : MirCallAns := ans₂
        if ha : a₁ = a₂ then
          isTrue (by
            cases hr
            change ({ req := .inr (.inr (.call r₁)), ans := a₁ } : Event MirEffect) =
              { req := .inr (.inr (.call r₁)), ans := a₂ }
            rw [ha])
        else
          isFalse (fun heq => by cases heq; exact ha rfl)
      else
        isFalse (fun heq => by cases heq; exact hr rfl)
    | .inl _, .inr _ => isFalse (fun heq => by cases heq)
    | .inr _, .inl _ => isFalse (fun heq => by cases heq)
    | .inr (.inl _), .inr (.inr _) => isFalse (fun heq => by cases heq)
    | .inr (.inr _), .inr (.inl _) => isFalse (fun heq => by cases heq)

/-- `Repr` instance for completed `MirEffect` interaction events. -/
instance instReprEventMirEffect : Repr (Event MirEffect) where
  reprPrec ev prec :=
    match ev.req, ev.ans with
    | .inl (.fail kind), _ =>
      Repr.addAppParen ("Event.fail " ++ reprArg kind) prec
    | .inr (.inl (.emit obs)), _ =>
      Repr.addAppParen ("Event.obs " ++ reprArg obs) prec
    | .inr (.inr (.call req)), ans =>
      let callAns : MirCallAns := ans
      Repr.addAppParen ("Event.call " ++ reprArg req ++ " " ++ reprArg callAns) prec

/-! ## 2. Observed Runtime Events, Outcomes, and Trace Correspondence -/

/--
Single observable interaction event captured by a runtime trace observer:
- `.branch tag`: a `TerminatorKind.switchInt` branch observation (`MirObs.event tag`).
- `.extCall defPath args retVal`: an unresolved external procedure call to
  `defPath` with argument values `args` that returned `retVal` normally.
- `.extCallPanic defPath args`: an unresolved external procedure call to
  `defPath` with argument values `args` that unwound (panicked).
- `.extCallAbort defPath args`: an unresolved external procedure call to
  `defPath` with argument values `args` that aborted the process.
-/
inductive ObservedEvent : Type where
  | branch (tag : Nat)
  | extCall (defPath : DefPath) (args : List Value) (retVal : Value)
  | extCallPanic (defPath : DefPath) (args : List Value)
  | extCallAbort (defPath : DefPath) (args : List Value)
  deriving Repr, DecidableEq

/-- Alias for `ObservedEvent`. -/
abbrev ObservedTraceEvent : Type := ObservedEvent

/-- Decoded external call record before embedding into `ObservedEvent`. -/
structure ObservedCallEvent : Type where
  defPath : DefPath
  args : List Value
  retVal : Option Value := none
  panicked : Bool := false
  deriving Repr, DecidableEq

/-- Convert an `ObservedCallEvent` into an `ObservedEvent`. -/
@[reducible]
def ObservedCallEvent.toObservedEvent (ev : ObservedCallEvent) : ObservedEvent :=
  match ev.retVal with
  | some v => .extCall ev.defPath ev.args v
  | none =>
    if ev.panicked then .extCallPanic ev.defPath ev.args
    else .extCallAbort ev.defPath ev.args

/-- Terminal outcome of a root function invocation captured by a runtime observer. -/
inductive ObservedOutcome : Type where
  | normal (retVal : Value)
  | panic
  | abort
  deriving Repr, DecidableEq

/--
Complete decoded runtime trace for a root `CapturedMir` invocation, pairing the
root input `args`, initial `initMem`, transparent `inlinedCallees` (stepped via
`.tau`), observed interaction `events`, and terminal `outcome`.
-/
structure ObservedTrace : Type where
  args : List Value
  initMem : Memory := emptyMemory
  inlinedCallees : List CapturedMir := []
  events : List ObservedEvent
  outcome : ObservedOutcome
  deriving Repr, DecidableEq

/-- Alias for `ObservedTrace`. -/
abbrev ObservedExecutionTrace : Type := ObservedTrace

/--
Relational correspondence between an observed terminal outcome `obsOut` and a
model `MirOutcome` `out`.
-/
def MatchesObservedOutcome (obsOut : ObservedOutcome) (out : MirOutcome) : Prop :=
  match obsOut, out with
  | .normal expectedRet, .normal (actualRet, _) => actualRet = expectedRet
  | .panic, .panic => True
  | .abort, .abort => True
  | _, _ => False

/-- Computable boolean check for `MatchesObservedOutcome`. -/
@[reducible]
def checkOutcomeMatches (obsOut : ObservedOutcome) (out : MirOutcome) : Bool :=
  match obsOut with
  | .normal expectedRet =>
    match out with
    | .normal (actualRet, _) => valueEqFuel 16 actualRet expectedRet
    | .panic => false
    | .abort => false
  | .panic =>
    match out with
    | .normal _ => false
    | .panic => true
    | .abort => false
  | .abort =>
    match out with
    | .normal _ => false
    | .panic => false
    | .abort => true

theorem checkOutcomeMatches_sound {obsOut : ObservedOutcome} {out : MirOutcome}
    (h : checkOutcomeMatches obsOut out = true) :
    MatchesObservedOutcome obsOut out := by
  cases obsOut with
  | normal expectedRet =>
    cases out with
    | normal p => exact valueEqFuel_sound h
    | panic => nomatch h
    | abort => nomatch h
  | panic =>
    cases out with
    | normal _ => nomatch h
    | panic => trivial
    | abort => nomatch h
  | abort =>
    cases out with
    | normal _ => nomatch h
    | panic => nomatch h
    | abort => trivial

/--
Single-event correspondence between an `ObservedEvent` captured by a runtime
observer and a concrete `Event MirEffect` in the interaction tree.
-/
def MatchesObservedEvent (obsEv : ObservedEvent) (mirEv : Event MirEffect) : Prop :=
  match obsEv, mirEv with
  | .branch tag, ⟨.inr (.inl (.emit (.event tag'))), PUnit.unit⟩ =>
    tag' = tag
  | .extCall defPath args retVal, ⟨.inr (.inr (.call req)), ans⟩ =>
    req.defPath = defPath ∧ req.args = args ∧ ans = .returned retVal req.memory
  | .extCallPanic defPath args, ⟨.inr (.inr (.call req)), ans⟩ =>
    req.defPath = defPath ∧ req.args = args ∧ ans = .panicked req.memory
  | .extCallAbort defPath args, ⟨.inr (.inr (.call req)), ans⟩ =>
    req.defPath = defPath ∧ req.args = args ∧ ans = .aborted
  | _, _ => False

/--
Pointwise correspondence between a list of `ObservedEvent`s and a concrete
interaction-tree trace `List (Event MirEffect)`.
-/
def MatchesObservedEvents : List ObservedEvent → List (Event MirEffect) → Prop
  | [], [] => True
  | obsEv :: obsRest, mirEv :: mirRest =>
    MatchesObservedEvent obsEv mirEv ∧ MatchesObservedEvents obsRest mirRest
  | _, _ => False

/--
Match a single `ObservedEvent` against an external `MirCallReq`, returning the
synthesized `MirCallAns` when the callee `defPath` and `args` match.
-/
@[reducible]
def matchCallObservedEvent (req : MirCallReq) : ObservedEvent → Option MirCallAns
  | .extCall defPath args retVal =>
    if (req.defPath == defPath) && valueListEqFuel 16 req.args args then
      some (.returned retVal req.memory)
    else
      none
  | .extCallPanic defPath args =>
    if (req.defPath == defPath) && valueListEqFuel 16 req.args args then
      some (.panicked req.memory)
    else
      none
  | .extCallAbort defPath args =>
    if (req.defPath == defPath) && valueListEqFuel 16 req.args args then
      some .aborted
    else
      none
  | .branch _ => none

theorem matchCallObservedEvent_sound
    {req : MirCallReq} {obsEv : ObservedEvent} {ans : MirCallAns}
    (h : matchCallObservedEvent req obsEv = some ans) :
    MatchesObservedEvent obsEv ⟨.inr (.inr (.call req)), ans⟩ := by
  cases obsEv with
  | branch _ => nomatch h
  | extCall defPath args retVal =>
    change
      (if (req.defPath == defPath) && valueListEqFuel 16 req.args args then
        some (MirCallAns.returned retVal req.memory)
      else
        none) = some ans at h
    revert h
    cases hd : (req.defPath == defPath) <;>
      cases ha : valueListEqFuel 16 req.args args <;> intro h
    · nomatch h
    · nomatch h
    · nomatch h
    · cases h
      exact ⟨beq_iff_eq.mp hd, valueListEqFuel_sound 16 ha, rfl⟩
  | extCallPanic defPath args =>
    change
      (if (req.defPath == defPath) && valueListEqFuel 16 req.args args then
        some (MirCallAns.panicked req.memory)
      else
        none) = some ans at h
    revert h
    cases hd : (req.defPath == defPath) <;>
      cases ha : valueListEqFuel 16 req.args args <;> intro h
    · nomatch h
    · nomatch h
    · nomatch h
    · cases h
      exact ⟨beq_iff_eq.mp hd, valueListEqFuel_sound 16 ha, rfl⟩
  | extCallAbort defPath args =>
    change
      (if (req.defPath == defPath) && valueListEqFuel 16 req.args args then
        some MirCallAns.aborted
      else
        none) = some ans at h
    revert h
    cases hd : (req.defPath == defPath) <;>
      cases ha : valueListEqFuel 16 req.args args <;> intro h
    · nomatch h
    · nomatch h
    · nomatch h
    · cases h
      exact ⟨beq_iff_eq.mp hd, valueListEqFuel_sound 16 ha, rfl⟩

/-! ## 3. Full Trace Replay (`checkBranches = true`) and Soundness -/

/-- Extract the active `(blockIdx, stmtIdx)` program counter from `MirExecState`. -/
@[reducible]
def execStateCursor : MirExecState → Nat × Nat
  | .running s => (s.frame.blockIdx, s.frame.stmtIdx)
  | _ => (0, 0)

/-- Extract the active `CapturedMir` body from `MirExecState` (defaulting to `rootBody`). -/
@[reducible]
def execStateActiveBody (rootBody : CapturedMir) : MirExecState → CapturedMir
  | .running s =>
    match s.memory.activeCallee with
    | some calleeBody => calleeBody
    | none => rootBody
  | _ => rootBody

/-- Return `true` if `s : ScalarLayout` is a pointer primitive. -/
@[reducible]
def scalarLayoutIsPointer : ScalarLayout → Bool
  | .initialized p _ =>
    match p with
    | .pointer _ => true
    | .int _ _ | .float _ => false
  | .union p =>
    match p with
    | .pointer _ => true
    | .int _ _ | .float _ => false

/-- Return `true` if `pred` holds for any index in `idxs` (bounded by fuel `32`). -/
@[reducible]
def anyLayoutIdxSatisfies (pred : Nat → Bool) (idxs : List Nat) : Bool :=
  (Nat.rec
    (motive := fun _ => List Nat → Bool)
    (fun _ => false)
    (fun _ ih xs =>
      match xs with
      | [] => false
      | fIdx :: rest => if pred fIdx then true else ih rest)
    32) idxs

/--
Test whether the `TypeLayout` at `layoutIdx` in `layouts` (or any transitive
field layout in `l.fieldLayouts`) has a pointer scalar representation.
-/
@[reducible]
def layoutHasPointerScalar : Nat → LayoutTable → Nat → Bool :=
  Nat.rec
    (motive := fun _ => LayoutTable → Nat → Bool)
    (fun _ _ => false)
    (fun _ ih layouts layoutIdx =>
      match LayoutTable.lookup layouts layoutIdx with
      | none => false
      | some l =>
        let reprHasPtr : Bool :=
          match l.backendRepr with
          | .scalar s0 => scalarLayoutIsPointer s0
          | .scalarPair s0 s1 =>
            Bool.or (scalarLayoutIsPointer s0) (scalarLayoutIsPointer s1)
          | .memory => false
        if reprHasPtr then
          true
        else
          anyLayoutIdxSatisfies (ih layouts) l.fieldLayouts)

/--
Fuel-bounded check testing whether all `RigidTy`s in a list are `Freeze`
(contain no `UnsafeCell` interior mutability or raw pointer), defined via
`Nat.rec` and non-overlapping `match` expressions.
-/
@[reducible]
def rigidTyListIsFreezeFuel : Nat → List RigidTy → Bool :=
  Nat.rec
    (motive := fun _ => List RigidTy → Bool)
    (fun _ => true)
    (fun _ ih xs =>
      match xs with
      | [] => true
      | t :: rest =>
        let headFreeze : Bool :=
          match t with
          | .rawPtr _ _ => false
          | .adt defPath args =>
            if stringEq defPath "core::cell::UnsafeCell" ||
                stringEq defPath "std::cell::UnsafeCell" then
              false
            else
              ih args
          | .tuple fields => ih fields
          | .array elem _ => ih [elem]
          | .slice elem => ih [elem]
          | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
          | .ref _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _
          | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => true
        headFreeze && ih rest)

/--
Fuel-bounded check testing whether a `RigidTy` is `Freeze` without `.brecOn`.
-/
@[reducible]
def rigidTyIsFreezeFuel (fuel : Nat) (ty : RigidTy) : Bool :=
  rigidTyListIsFreezeFuel fuel [ty]

/--
Structurally recursive fuel-bounded helper testing whether any `RigidTy` in a
worklist contains `&mut T`, `*const T` / `*mut T`, or an interior-mutable
shared reference (`&UnsafeCell<T>`).
-/
@[reducible]
def rigidTyListHasImpureExtCallPtr : Nat → List RigidTy → Bool :=
  Nat.rec
    (motive := fun _ => List RigidTy → Bool)
    (fun _ => false)
    (fun _ ih xs =>
      match xs with
      | [] => false
      | t :: rest =>
        let headImpure : Bool :=
          match t with
          | .ref m pointee =>
            match m with
            | .mut => true
            | .not =>
              Bool.or
                (Bool.not (rigidTyIsFreezeFuel 16 pointee))
                (ih [pointee])
          | .rawPtr _ _ => true
          | .tuple fields => ih fields
          | .array elem _ => ih [elem]
          | .slice elem => ih [elem]
          | .adt defPath args =>
            if Bool.not (rigidTyIsFreezeFuel 16 (.adt defPath args)) ||
                stringEq defPath "core::ptr::non_null::NonNull" ||
                stringEq defPath "core::ptr::unique::Unique" then
              true
            else
              ih args
          | .closure _ upvars => ih upvars
          | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
          | .fnDef _ _ | .fnPtr _ _ _ _ | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ => false
        if headImpure then
          true
        else
          ih rest)

/--
Test whether a `RigidTy` contains a mutable reference (`&mut T`), raw pointer
(`*const T` / `*mut T`), or interior-mutable shared reference (`&UnsafeCell<T>`)
through which an external callee could read or mutate memory outside the pure
`MirCallE` value boundary.
-/
@[reducible]
def rigidTyHasImpureExtCallPtr (fuel : Nat) (ty : RigidTy) : Bool :=
  rigidTyListHasImpureExtCallPtr fuel [ty]

/--
Test whether a parameter `Ty` carries `&mut` or raw-pointer capabilities that
violate `TraceCheck`'s memory-pure external-callee assumption, inspecting both
`ty.kind` and (when `layouts` is supplied) `ty.layoutIdx` in `layouts`.
-/
@[reducible]
def tyHasImpureExtCallPtr
    (ty : Ty) (layouts : LayoutTable := emptyLayoutTable) : Bool :=
  if rigidTyHasImpureExtCallPtr 16 ty.kind then
    true
  else
    match ty.kind with
    | .ref m pointee =>
      match m with
      | .mut => true
      | .not => Bool.not (rigidTyIsFreezeFuel 16 pointee)
    | .adt _ _ | .tuple _ | .array _ _ | .slice _ | .closure _ _ =>
      layoutHasPointerScalar 16 layouts ty.layoutIdx
    | .bool | .char | .int _ | .uint _ | .float _ | .never | .str
    | .rawPtr _ _ | .fnDef _ _ | .fnPtr _ _ _ _ | .dynamic _ | .foreign _ | .other _ | .param _ _ | .alias _ _ =>
      false

/--
Return the 0-based argument index of the first parameter in `sigBody` whose type
carries `&mut` or a raw pointer (`tyHasImpureExtCallPtr`), or `none` if all
parameters are memory-pure.
-/
@[reducible]
def findCalleeImpurePtrArgIdxAux
    (layouts : LayoutTable) : Nat → Nat → List LocalDecl → Option Nat :=
  Nat.rec
    (motive := fun _ => Nat → List LocalDecl → Option Nat)
    (fun _ _ => none)
    (fun _ ih argIdx decls =>
      match decls with
      | [] => none
      | decl :: rest =>
        if tyHasImpureExtCallPtr decl.ty layouts then
          some argIdx
        else
          ih (argIdx + 1) rest)

/--
Check a callee's `CapturedMir` signature for any `&mut` or raw-pointer parameter,
returning `some argIdx` for the first impure parameter.
-/
@[reducible]
def findCalleeImpurePtrArgIdx? (sigBody : CapturedMir) : Option Nat :=
  findCalleeImpurePtrArgIdxAux sigBody.layouts sigBody.argCount 0 (sigBody.localDecls.drop 1)

/--
Inspect a caller basic block's `TerminatorKind.call` / `TerminatorKind.tailCall`
argument operands for any `&mut` or raw-pointer argument type using `operandTy`,
returning `some argIdx` on the first impure argument.
-/
@[reducible]
def findCallOperandsImpurePtrArgIdxAux
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (argIdx : Nat) (ops : List Operand) : Option Nat :=
  (Nat.rec
    (motive := fun _ => Nat → List Operand → Option Nat)
    (fun _ _ => none)
    (fun _ ih idx xs =>
      match xs with
      | [] => none
      | op :: rest =>
        match operandTy localDecls layouts op with
        | some ty =>
          if tyHasImpureExtCallPtr ty layouts then
            some idx
          else
            ih (idx + 1) rest
        | none =>
          ih (idx + 1) rest)
    32) argIdx ops

/--
Check whether the call terminator at `blockIdx` in `body` passes any `&mut` or
raw-pointer argument operand.
-/
@[reducible]
def findBlockCallImpurePtrArgIdx?
    (body : CapturedMir) (blockIdx : Nat) : Option Nat :=
  match get? body.basicBlocks blockIdx with
  | some bb =>
    match bb.terminator.kind with
    | .call _ argOps _ _ _ | .tailCall _ argOps =>
      findCallOperandsImpurePtrArgIdxAux body.localDecls body.layouts 0 argOps
    | _ => none
  | none => none

/--
Structurally recursive fuel-bounded helper testing whether any runtime `Value`
in a worklist contains a pointer whose borrow in `borrows` is mutable/non-frozen
(`.active` or `.reserved`) or untracked (`none`, such as a raw pointer).
-/
@[reducible]
def valueListHasImpureExtCallPtr (borrows : List BorrowEntry) : Nat → List Value → Bool :=
  Nat.rec
    (motive := fun _ => List Value → Bool)
    (fun _ => false)
    (fun _ ih xs =>
      match xs with
      | [] => false
      | v :: rest =>
        let headImpure : Bool :=
          match v with
          | .ptr ptrVal _ =>
            match lookupBorrow borrows ptrVal.tag with
            | some b =>
              match b.perm with
              | .frozen => false
              | .reserved | .active | .disabled => true
            | none => true
          | .aggregate _ fields =>
            ih fields
          | .unit | .scalar _ => false
        if headImpure then
          true
        else
          ih rest)

/--
Test whether an evaluated runtime `Value` passed in a `MirCallReq` contains a
pointer whose borrow in `borrows` is mutable/non-frozen (`.active` or
`.reserved`) or untracked (`none`, such as a raw pointer).
-/
@[reducible]
def valueHasImpureExtCallPtr (borrows : List BorrowEntry) (fuel : Nat) (v : Value) : Bool :=
  valueListHasImpureExtCallPtr borrows fuel [v]

/--
Return the 0-based argument index of the first runtime argument in `args` that
contains a mutable or untracked raw pointer under `borrows`.
-/
@[reducible]
def findCallReqImpurePtrArgIdxAux
    (borrows : List BorrowEntry) (argIdx : Nat) (args : List Value) : Option Nat :=
  (Nat.rec
    (motive := fun _ => Nat → List Value → Option Nat)
    (fun _ _ => none)
    (fun _ ih idx xs =>
      match xs with
      | [] => none
      | v :: rest =>
        if valueHasImpureExtCallPtr borrows 16 v then
          some idx
        else
          ih (idx + 1) rest)
    32) argIdx args

/--
Inspect a runtime `MirCallReq` for any argument containing a mutable (`&mut`)
or untracked raw pointer capability.
-/
@[reducible]
def findCallReqImpurePtrArgIdx? (req : MirCallReq) : Option Nat :=
  findCallReqImpurePtrArgIdxAux req.memory.borrows 0 req.args

/--
Combined call-site operand-type and runtime `MirCallReq` argument check for
`&mut` or raw-pointer external call arguments.
-/
@[reducible]
def findActiveCallImpurePtrArgIdx?
    (activeBody : CapturedMir) (blockIdx : Nat) (req : MirCallReq) : Option Nat :=
  match findBlockCallImpurePtrArgIdx? activeBody blockIdx with
  | some argIdx => some argIdx
  | none => findCallReqImpurePtrArgIdx? req

/--
Fuel-bounded replay of `events` and `outcome` against `stepMirState body` with
full `MirObsE` (`switchInt`) and `MirCallE` checking (`checkBranches = true`).
Rejects external calls whose call-site argument operands or runtime values take
`&mut` or raw-pointer capabilities (`findActiveCallImpurePtrArgIdx? = some _`).
-/
@[reducible]
def reconstructFullMirTrace
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    Option (List (Event MirEffect) × MirOutcome) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret out =>
      match events with
      | [] =>
        if checkOutcomeMatches outcome out then
          some ([], out)
        else
          none
      | _ :: _ => none
    | .tau st' =>
      reconstructFullMirTrace fuel' body st' events outcome
    | .vis (.inl _) _ => none
    | .vis (.inr (.inl (.emit .silent))) _ => none
    | .vis (.inr (.inl (.emit (.event tag)))) k =>
      match events with
      | .branch expectedTag :: rest =>
        if Nat.beq tag expectedTag then
          match reconstructFullMirTrace fuel' body (k PUnit.unit) rest outcome with
          | some (trRest, out) =>
            some (⟨.inr (.inl (.emit (.event tag))), PUnit.unit⟩ :: trRest, out)
          | none => none
        else
          none
      | _ => none
    | .vis (.inr (.inr (.call req))) k =>
      match
        findActiveCallImpurePtrArgIdx?
          (execStateActiveBody body st) (execStateCursor st).1 req
      with
      | some _ => none
      | none =>
        match events with
        | obsEv :: rest =>
          match matchCallObservedEvent req obsEv with
          | some ans =>
            match reconstructFullMirTrace fuel' body (k ans) rest outcome with
            | some (trRest, out) =>
              some (⟨.inr (.inr (.call req)), ans⟩ :: trRest, out)
            | none => none
          | none => none
        | [] => none

/--
Computable boolean checker for full (`MirObsE` + `MirCallE`) trace consistency
(`checkBranches = true`).
-/
@[reducible]
def checkFullObservedTraceBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) : Bool :=
  (reconstructFullMirTrace fuel body (.running s) events outcome).isSome

/--
Soundness of `reconstructFullMirTrace`: when `reconstructFullMirTrace` succeeds
with `some (tr, out)`, `tr` matches `events`, `out` matches `outcome`, and
`ITree.cofix (stepMirState body) st` reaches `out` along `tr`.
-/
theorem reconstructFullMirTrace_sound
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (tr : List (Event MirEffect)) (out : MirOutcome)
    (h_ok : reconstructFullMirTrace fuel body st events outcome = some (tr, out)) :
    MatchesObservedEvents events tr ∧
    MatchesObservedOutcome outcome out ∧
    ReachesRet (ITree.cofix (stepMirState body) st) tr out := by
  induction fuel generalizing st events tr with
  | zero => nomatch h_ok
  | succ fuel' ih =>
    unfold reconstructFullMirTrace at h_ok
    have h_obs :
        (ITree.cofix (stepMirState body) st).observe =
          (stepMirState body st).map (ITree.cofix (stepMirState body)) :=
      ITree.observe_cofix (stepMirState body) st
    cases h_step : stepMirState body st with
    | ret out₀ =>
      simp only [h_step] at h_ok
      cases events with
      | nil =>
        revert h_ok
        cases hm : checkOutcomeMatches outcome out₀ <;> intro h_ok
        · nomatch h_ok
        · injection h_ok with h_pair
          injection h_pair with h_tr h_o
          subst h_tr h_o
          rw [h_step] at h_obs
          dsimp only [ITreeF.map] at h_obs
          exact ⟨trivial, checkOutcomeMatches_sound hm,
            ⟨ITree.cofix (stepMirState body) st, .refl _, h_obs⟩⟩
      | cons _ _ => nomatch h_ok
    | tau st' =>
      simp only [h_step] at h_ok
      rw [h_step] at h_obs
      dsimp only [ITreeF.map] at h_obs
      rcases ih st' events tr h_ok with ⟨h_evs, h_out, ⟨u, h_reach, h_u⟩⟩
      exact ⟨h_evs, h_out, ⟨u, .tau h_obs h_reach, h_u⟩⟩
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · simp only [h_step] at h_ok; nomatch h_ok
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent => simp only [h_step] at h_ok; nomatch h_ok
          | event tag =>
            simp only [h_step] at h_ok
            cases events with
            | nil => nomatch h_ok
            | cons ev rest =>
              cases ev with
              | branch expectedTag =>
                change
                  (if Nat.beq tag expectedTag then
                    match reconstructFullMirTrace fuel' body (k PUnit.unit) rest outcome with
                    | some (trRest, out) =>
                      some (⟨.inr (.inl (.emit (.event tag))), PUnit.unit⟩ :: trRest, out)
                    | none => none
                  else
                    none) = some (tr, out) at h_ok
                revert h_ok
                cases htag : Nat.beq tag expectedTag <;> intro h_ok
                · nomatch h_ok
                · cases h_rec : reconstructFullMirTrace fuel' body (k PUnit.unit) rest outcome with
                  | none => rw [h_rec] at h_ok; nomatch h_ok
                  | some pair =>
                    rw [h_rec] at h_ok
                    cases h_ok
                    rcases ih (k PUnit.unit) rest pair.1 h_rec with
                      ⟨h_evs, h_out, ⟨u, h_reach, h_u⟩⟩
                    rw [h_step] at h_obs
                    dsimp only [ITreeF.map] at h_obs
                    exact ⟨⟨Nat.beq_eq.mp htag, h_evs⟩, h_out,
                      ⟨u, .vis h_obs False.elim PUnit.unit h_reach, h_u⟩⟩
              | _ => nomatch h_ok
      · cases callReq with
        | call req =>
          simp only [h_step] at h_ok
          cases h_imp :
              findActiveCallImpurePtrArgIdx?
                (execStateActiveBody body st) (execStateCursor st).1 req with
          | some _ => simp only [h_imp] at h_ok; nomatch h_ok
          | none =>
            simp only [h_imp] at h_ok
            cases events with
            | nil => nomatch h_ok
            | cons obsEv rest =>
              change
                (match matchCallObservedEvent req obsEv with
                 | some ans =>
                   match reconstructFullMirTrace fuel' body (k ans) rest outcome with
                   | some (trRest, out) =>
                     some (⟨.inr (.inr (.call req)), ans⟩ :: trRest, out)
                   | none => none
                 | none => none) = some (tr, out) at h_ok
              cases h_match : matchCallObservedEvent req obsEv with
              | none => rw [h_match] at h_ok; nomatch h_ok
              | some ans =>
                rw [h_match] at h_ok
                change
                  (match reconstructFullMirTrace fuel' body (k ans) rest outcome with
                   | some (trRest, out) =>
                     some (⟨.inr (.inr (.call req)), ans⟩ :: trRest, out)
                   | none => none) = some (tr, out) at h_ok
                cases h_rec : reconstructFullMirTrace fuel' body (k ans) rest outcome with
                | none => rw [h_rec] at h_ok; nomatch h_ok
                | some pair =>
                  rw [h_rec] at h_ok
                  cases h_ok
                  rcases ih (k ans) rest pair.1 h_rec with
                    ⟨h_evs, h_out, ⟨u, h_reach, h_u⟩⟩
                  rw [h_step] at h_obs
                  dsimp only [ITreeF.map] at h_obs
                  exact ⟨⟨matchCallObservedEvent_sound h_match, h_evs⟩, h_out,
                    ⟨u, .vis h_obs False.elim ans h_reach, h_u⟩⟩

/--
Soundness of `checkFullObservedTraceBounded`: if `checkFullObservedTraceBounded`
returns `true`, then `mirTree body s` reaches a terminal outcome `out` matching
`outcome` along a trace `tr` matching `events`.
-/
theorem checkFullObservedTraceBounded_sound
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok : checkFullObservedTraceBounded fuel body s events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (mirTree body s) tr out := by
  unfold checkFullObservedTraceBounded at h_ok
  cases h_rec : reconstructFullMirTrace fuel body (.running s) events outcome with
  | none => rw [h_rec] at h_ok; nomatch h_ok
  | some pair =>
    exact ⟨pair.1, pair.2,
      reconstructFullMirTrace_sound fuel body (.running s) events outcome
        pair.1 pair.2 h_rec⟩

/-! ## 4. Branch-Erased Trace Replay (`checkBranches = false`) and Soundness -/

/--
Fuel-bounded replay of call-boundary `events` and `outcome` against
`stepMirState body` with branch observations silenced (`checkBranches = false`,
corresponding to `mirObsErasedStatefulTree`).
-/
@[reducible]
def reconstructObsErasedMirTrace
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    Option (List (Event MirEffect) × MirOutcome) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret out =>
      match events with
      | [] =>
        if checkOutcomeMatches outcome out then
          some ([], out)
        else
          none
      | _ :: _ => none
    | .tau st' =>
      reconstructObsErasedMirTrace fuel' body st' events outcome
    | .vis (.inl _) _ => none
    | .vis (.inr (.inl _)) k =>
      reconstructObsErasedMirTrace fuel' body (k PUnit.unit) events outcome
    | .vis (.inr (.inr (.call req))) k =>
      match
        findActiveCallImpurePtrArgIdx?
          (execStateActiveBody body st) (execStateCursor st).1 req
      with
      | some _ => none
      | none =>
        match events with
        | obsEv :: rest =>
          match matchCallObservedEvent req obsEv with
          | some ans =>
            match reconstructObsErasedMirTrace fuel' body (k ans) rest outcome with
            | some (trRest, out) =>
              some (⟨.inr (.inr (.call req)), ans⟩ :: trRest, out)
            | none => none
          | none => none
        | [] => none

/--
Computable boolean checker for branch-erased (`MirCallE`-only) trace consistency
(`checkBranches = false`).
-/
@[reducible]
def checkObsErasedObservedTraceBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) : Bool :=
  (reconstructObsErasedMirTrace fuel body (.running s) events outcome).isSome

private theorem reachesRet_interp_silenceMirObs_ret
    {t : ITree MirEffect MirOutcome} {out : MirOutcome}
    (h_obs : t.observe = .ret out) :
    ReachesRet (ITree.interp silenceMirObs t) [] out := by
  have hEq : t = .ret out := by rw [← ITree.fold_observe t, h_obs]; rfl
  rw [hEq, interp_ret]
  exact ⟨.ret out, .refl _, ITree.observe_ret out⟩

private theorem reachesRet_interp_silenceMirObs_tau
    {t t' : ITree MirEffect MirOutcome}
    {tr : List (Event MirEffect)} {out : MirOutcome}
    (h_obs : t.observe = .tau t')
    (h_reach : ReachesRet (ITree.interp silenceMirObs t') tr out) :
    ReachesRet (ITree.interp silenceMirObs t) tr out := by
  have hEq : t = .tau t' := by rw [← ITree.fold_observe t, h_obs]; rfl
  rw [hEq, interp_tau]
  rcases h_reach with ⟨u, hr, hu⟩
  exact ⟨u, .tau (ITree.observe_tau _) hr, hu⟩

private theorem reachesRet_interp_silenceMirObs_obs
    {t : ITree MirEffect MirOutcome}
    {obsReq : MirObsE.I}
    {k : MirObsE.O obsReq → ITree MirEffect MirOutcome}
    {tr : List (Event MirEffect)} {out : MirOutcome}
    (h_obs : t.observe = .vis (.inr (.inl obsReq)) k)
    (h_reach : ReachesRet (ITree.interp silenceMirObs (k PUnit.unit)) tr out) :
    ReachesRet (ITree.interp silenceMirObs t) tr out := by
  have hEq : t = .vis (.inr (.inl obsReq)) k := by
    rw [← ITree.fold_observe t, h_obs]; rfl
  erw [hEq, interp_vis]
  have h_bind :
      (silenceMirObs (.inr (.inl obsReq)) >>=
        fun o => .tau (ITree.interp silenceMirObs (k o))) =
      .tau (ITree.interp silenceMirObs (k PUnit.unit)) :=
    ret_bind PUnit.unit (fun o => .tau (ITree.interp silenceMirObs (k o)))
  erw [h_bind]
  rcases h_reach with ⟨u, hr, hu⟩
  exact ⟨u, .tau (ITree.observe_tau _) hr, hu⟩

private theorem reachesRet_interp_silenceMirObs_call
    {t : ITree MirEffect MirOutcome}
    {req : MirCallReq}
    {k : MirEffect.O (.inr (.inr (.call req))) → ITree MirEffect MirOutcome}
    {ans : MirCallAns}
    {tr : List (Event MirEffect)} {out : MirOutcome}
    (h_obs : t.observe = .vis (.inr (.inr (.call req))) k)
    (h_reach : ReachesRet (ITree.interp silenceMirObs (k ans)) tr out) :
    ReachesRet
      (ITree.interp silenceMirObs t)
      (⟨.inr (.inr (.call req)), ans⟩ :: tr)
      out := by
  have hEq : t = .vis (.inr (.inr (.call req))) k := by
    rw [← ITree.fold_observe t, h_obs]; rfl
  erw [hEq, interp_vis]
  have h_vis :
      (silenceMirObs (.inr (.inr (.call req))) >>=
        fun o => .tau (ITree.interp silenceMirObs (k o))).observe =
      .vis (.inr (.inr (.call req)))
        (fun o => .ret o >>= fun o' => .tau (ITree.interp silenceMirObs (k o'))) := by
    change (ITree.vis (E := MirEffect) (.inr (.inr (.call req))) ITree.ret >>=
      fun o => .tau (ITree.interp silenceMirObs (k o))).observe = _
    erw [vis_bind, ITree.observe_vis]
  have h_cont :
      (ITree.ret ans >>= fun o' => .tau (ITree.interp silenceMirObs (k o'))).observe =
      .tau (ITree.interp silenceMirObs (k ans)) := by
    erw [ret_bind, ITree.observe_tau]
  rcases h_reach with ⟨u, hr, hu⟩
  exact ⟨u, .vis h_vis False.elim ans (.tau h_cont hr), hu⟩

/--
Soundness of `reconstructObsErasedMirTrace`: when `reconstructObsErasedMirTrace`
succeeds with `some (tr, out)`, `tr` matches `events`, `out` matches `outcome`,
and `ITree.interp silenceMirObs (ITree.cofix (stepMirState body) st)` reaches
`out` along `tr`.
-/
theorem reconstructObsErasedMirTrace_sound
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (tr : List (Event MirEffect)) (out : MirOutcome)
    (h_ok : reconstructObsErasedMirTrace fuel body st events outcome = some (tr, out)) :
    MatchesObservedEvents events tr ∧
    MatchesObservedOutcome outcome out ∧
    ReachesRet (ITree.interp silenceMirObs (ITree.cofix (stepMirState body) st)) tr out := by
  induction fuel generalizing st events tr with
  | zero => nomatch h_ok
  | succ fuel' ih =>
    unfold reconstructObsErasedMirTrace at h_ok
    have h_obs :
        (ITree.cofix (stepMirState body) st).observe =
          (stepMirState body st).map (ITree.cofix (stepMirState body)) :=
      ITree.observe_cofix (stepMirState body) st
    cases h_step : stepMirState body st with
    | ret out₀ =>
      simp only [h_step] at h_ok
      cases events with
      | nil =>
        revert h_ok
        cases hm : checkOutcomeMatches outcome out₀ <;> intro h_ok
        · nomatch h_ok
        · injection h_ok with h_pair
          injection h_pair with h_tr h_o
          subst h_tr h_o
          rw [h_step] at h_obs
          dsimp only [ITreeF.map] at h_obs
          exact ⟨trivial, checkOutcomeMatches_sound hm,
            reachesRet_interp_silenceMirObs_ret h_obs⟩
      | cons _ _ => nomatch h_ok
    | tau st' =>
      simp only [h_step] at h_ok
      rw [h_step] at h_obs
      dsimp only [ITreeF.map] at h_obs
      rcases ih st' events tr h_ok with ⟨h_evs, h_out, h_reach⟩
      exact ⟨h_evs, h_out, reachesRet_interp_silenceMirObs_tau h_obs h_reach⟩
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · simp only [h_step] at h_ok; nomatch h_ok
      · simp only [h_step] at h_ok
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        rcases ih (k PUnit.unit) events tr h_ok with ⟨h_evs, h_out, h_reach⟩
        exact ⟨h_evs, h_out, reachesRet_interp_silenceMirObs_obs h_obs h_reach⟩
      · cases callReq with
        | call req =>
          simp only [h_step] at h_ok
          cases h_imp :
              findActiveCallImpurePtrArgIdx?
                (execStateActiveBody body st) (execStateCursor st).1 req with
          | some _ => simp only [h_imp] at h_ok; nomatch h_ok
          | none =>
            simp only [h_imp] at h_ok
            cases events with
            | nil => nomatch h_ok
            | cons obsEv rest =>
              change
                (match matchCallObservedEvent req obsEv with
                 | some ans =>
                   match reconstructObsErasedMirTrace fuel' body (k ans) rest outcome with
                   | some (trRest, out) =>
                     some (⟨.inr (.inr (.call req)), ans⟩ :: trRest, out)
                   | none => none
                 | none => none) = some (tr, out) at h_ok
              cases h_match : matchCallObservedEvent req obsEv with
              | none => rw [h_match] at h_ok; nomatch h_ok
              | some ans =>
                rw [h_match] at h_ok
                change
                  (match reconstructObsErasedMirTrace fuel' body (k ans) rest outcome with
                   | some (trRest, out) =>
                     some (⟨.inr (.inr (.call req)), ans⟩ :: trRest, out)
                   | none => none) = some (tr, out) at h_ok
                cases h_rec : reconstructObsErasedMirTrace fuel' body (k ans) rest outcome with
                | none => rw [h_rec] at h_ok; nomatch h_ok
                | some pair =>
                  rcases pair with ⟨trRest, out'⟩
                  rw [h_rec] at h_ok
                  cases h_ok
                  rcases ih (k ans) rest trRest h_rec with ⟨h_evs, h_out, h_reach⟩
                  rw [h_step] at h_obs
                  dsimp only [ITreeF.map] at h_obs
                  exact ⟨⟨matchCallObservedEvent_sound h_match, h_evs⟩, h_out,
                    reachesRet_interp_silenceMirObs_call h_obs h_reach⟩

/--
Soundness of `checkObsErasedObservedTraceBounded`: if
`checkObsErasedObservedTraceBounded` returns `true` from
`initMachineStateWithMemory body args mem`, then `mirObsErasedStatefulTree body args mem`
reaches a terminal outcome `out` matching `outcome` along a `MirCallE` trace `tr`
matching `events`.
-/
theorem checkObsErasedObservedTraceBounded_sound
    (fuel : Nat) (body : CapturedMir) (args : List Value) (mem : Memory)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok :
      checkObsErasedObservedTraceBounded fuel body
        (initMachineStateWithMemory body args mem) events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (mirObsErasedStatefulTree body args mem) tr out := by
  unfold checkObsErasedObservedTraceBounded at h_ok
  cases h_rec :
      reconstructObsErasedMirTrace fuel body
        (.running (initMachineStateWithMemory body args mem)) events outcome with
  | none => rw [h_rec] at h_ok; nomatch h_ok
  | some pair =>
    exact ⟨pair.1, pair.2,
      reconstructObsErasedMirTrace_sound fuel body
        (.running (initMachineStateWithMemory body args mem)) events outcome
        pair.1 pair.2 h_rec⟩

/--
Unified trace-consistency dispatcher supporting both `checkBranches = true`
(`mirStatefulTree`) and `checkBranches = false` (`mirObsErasedStatefulTree`),
with `trace.inlinedCallees` installed in `Memory.callees`.
-/
@[reducible]
def checkObservedTraceConsistencyBounded
    (fuel : Nat) (checkBranches : Bool) (body : CapturedMir)
    (trace : ObservedTrace) : Bool :=
  let mem := { trace.initMem with callees := trace.inlinedCallees }
  let s := initMachineStateWithMemory body trace.args mem
  match checkBranches with
  | true => checkFullObservedTraceBounded fuel body s trace.events trace.outcome
  | false => checkObsErasedObservedTraceBounded fuel body s trace.events trace.outcome

/-! ## 5. Connection to Verification Certificates & Postcondition Refutation -/

/--
If a `StatefulVerificationResult c` certificate holds and an observed full trace
is consistent with `c.body` on inputs `(args, mem)` satisfying `c.pre args mem`
with normal return `retVal`, then `retVal` provably satisfies `c.post` for some
post-state `mem'`.
-/
theorem verifiedStatefulClaim_satisfies_observedTrace
    {c : StatefulClaim}
    (h_ver : StatefulVerificationResult c)
    (fuel : Nat) (args : List Value) (mem : Memory)
    (events : List ObservedEvent) (retVal : Value)
    (h_pre : c.pre args mem)
    (h_trace :
      checkFullObservedTraceBounded fuel c.body
        (initMachineStateWithMemory c.body args mem)
        events (.normal retVal) = true) :
    ∃ mem', c.post args mem retVal mem' := by
  rcases checkFullObservedTraceBounded_sound fuel c.body
      (initMachineStateWithMemory c.body args mem) events (.normal retVal) h_trace with
    ⟨tr, out, _, h_out, h_reach⟩
  cases out with
  | normal p =>
    rcases p with ⟨actualRet, mem'⟩
    dsimp [MatchesObservedOutcome] at h_out
    subst h_out
    exact ⟨mem', (h_ver.proof args mem h_pre).2 (tr, .normal (actualRet, mem'))
      h_reach h_pre actualRet mem' rfl⟩
  | panic => nomatch h_out
  | abort => nomatch h_out

/--
Refute a `StatefulClaim` (`¬ c.holds`) by exhibiting a runtime trace consistent
with `c.body` on inputs `(args, mem)` satisfying `c.pre args mem` whose normal
return value `retVal` violates `c.post` across all post-states `mem'`.
-/
theorem refuteStatefulClaimByObservedTrace
    (c : StatefulClaim)
    (fuel : Nat) (args : List Value) (mem : Memory)
    (events : List ObservedEvent) (retVal : Value)
    (h_pre : c.pre args mem)
    (h_trace :
      checkFullObservedTraceBounded fuel c.body
        (initMachineStateWithMemory c.body args mem)
        events (.normal retVal) = true)
    (h_bad : ∀ mem', ¬ c.post args mem retVal mem') :
    ¬ c.holds := by
  intro h_holds
  rcases verifiedStatefulClaim_satisfies_observedTrace ⟨h_holds⟩ fuel args mem
      events retVal h_pre h_trace with ⟨mem', h_post⟩
  exact h_bad mem' h_post

/-! ## 6. Raw Byte-Slice & Shadow-Provenance Decoding (`RawByteTrace`) -/

/--
Entry in the runtime observer's shadow provenance table mapping a watched native
virtual address range `[baseAddr, baseAddr + byteLen)` to its abstract MIR
`(allocId, tag)` provenance and optional initial referent bytes `rawBytes`.
-/
structure ShadowAllocEntry : Type where
  baseAddr : Nat
  byteLen : Nat
  allocId : AllocId
  tag : Nat := allocId
  rawBytes : List UInt8 := []
  deriving DecidableEq, Repr

/-- Table of watched runtime allocations used to reconstruct pointer provenance. -/
abbrev ShadowProvenanceTable : Type := List ShadowAllocEntry

/-- Lift a raw byte list `List UInt8` into provenance-free `AbstractByte.init`s. -/
@[reducible]
def rawBytesToAbstractBytes : List UInt8 → List AbstractByte
  | [] => []
  | b :: rest => .init b none :: rawBytesToAbstractBytes rest

/-- Decode a little-endian `List UInt8` into its unsigned `Nat` value. -/
@[reducible]
def decodeRawLittleEndianNat : List UInt8 → Nat
  | [] => 0
  | b :: rest => Nat.add b.toBitVec.toNat (Nat.mul 256 (decodeRawLittleEndianNat rest))

/--
Look up a native runtime virtual address `addr` in `ShadowProvenanceTable`,
returning `(entry, addr - entry.baseAddr)` for the first entry whose range
`[baseAddr, baseAddr + byteLen]` contains `addr`.
-/
@[reducible]
def lookupShadowAllocEntry? :
    ShadowProvenanceTable → Nat → Option (ShadowAllocEntry × Nat)
  | [], _ => none
  | entry :: rest, addr =>
    if Nat.ble entry.baseAddr addr &&
        Nat.ble addr (Nat.add entry.baseAddr entry.byteLen) then
      some (entry, Nat.sub addr entry.baseAddr)
    else
      lookupShadowAllocEntry? rest addr

/--
Look up a native runtime virtual address `addr` in `ShadowProvenanceTable`,
returning `(allocId, tag, addr - baseAddr)` for the first entry whose range
`[baseAddr, baseAddr + byteLen]` contains `addr`.
-/
@[reducible]
def lookupShadowProvenance :
    ShadowProvenanceTable → Nat → Option (AllocId × Nat × Nat)
  | table, addr =>
    match lookupShadowAllocEntry? table addr with
    | some (entry, relOffset) => some (entry.allocId, entry.tag, relOffset)
    | none => none

/--
Translate an 8-byte little-endian native pointer byte slice using `table`:
when the decoded 64-bit address matches an entry in `table`, returns 8
little-endian `AbstractByte.init` bytes encoding the relative offset
`addr - entry.baseAddr` with provenance `some (entry.allocId, entry.tag)`;
otherwise returns provenance-free `rawBytesToAbstractBytes`.
-/
@[reducible]
def translatePointerBytes
    (table : ShadowProvenanceTable) (rawPtrBytes : List UInt8) :
    List AbstractByte :=
  let addr := decodeRawLittleEndianNat rawPtrBytes
  match lookupShadowProvenance table addr with
  | some (allocId, tag, relOffset) =>
    encodeLittleEndianBytes relOffset 8 (some (allocId, tag))
  | none =>
    rawBytesToAbstractBytes rawPtrBytes

/-- Test whether a `RigidTy` pointee represents an unsized wide-pointer target. -/
@[reducible]
def isWidePointee : RigidTy → Bool
  | .slice _ => true
  | .str => true
  | .dynamic _ => true
  | _ => false

/-- Extract a contiguous subslice `[offset .. offset + len)` from `raw : List UInt8`. -/
@[reducible]
def sliceRawBytes (raw : List UInt8) (offset len : Nat) : Option (List UInt8) :=
  if Nat.ble (Nat.add offset len) (length raw) then
    some ((raw.drop offset).take len)
  else
    none

/--
Convert a raw runtime byte slice corresponding to a `ScalarLayout` into
`List AbstractByte`, translating 8-byte pointer scalars through `table`.
-/
@[reducible]
def rawScalarLayoutBytes
    (table : ShadowProvenanceTable) (s : ScalarLayout) (rawSlice : List UInt8) :
    List AbstractByte :=
  match s with
  | .initialized (.pointer _) _ | .union (.pointer _) =>
    if Nat.beq (length rawSlice) 8 then
      translatePointerBytes table rawSlice
    else
      rawBytesToAbstractBytes rawSlice
  | _ => rawBytesToAbstractBytes rawSlice

/--
Convert `count` array chunks of `elemSz` bytes from `raw` using `convChunk`.
-/
@[reducible]
def rawArrayChunksWith
    (convChunk : List UInt8 → List AbstractByte)
    (elemSz : Nat) :
    Nat → List UInt8 → Option (List AbstractByte)
  | 0 => fun raw =>
    match raw with
    | [] => some []
    | _ :: _ => none
  | n + 1 => fun raw =>
    if Nat.ble elemSz (length raw) then
      let chunk := raw.take elemSz
      let rest := raw.drop elemSz
      match rawArrayChunksWith convChunk elemSz n rest with
      | some restBytes => some (appendAbstractBytes (convChunk chunk) restBytes)
      | none => none
    else
      none

/--
Overlay converted field slices at `offsets` onto `buf` (initially all `.uninit`)
using `fieldKinds` and `sizeOfKind`, leaving inter-field and trailing padding
bytes as `AbstractByte.uninit`.
-/
@[reducible]
def rawFieldsAtOffsetsByKinds
    (convKind : RigidTy → List UInt8 → List AbstractByte)
    (sizeOfKind : RigidTy → Option Nat)
    (raw : List UInt8) :
    List Size → List RigidTy → List AbstractByte → Option (List AbstractByte)
  | [] => fun ks buf =>
    match ks with
    | [] => some buf
    | _ :: _ => none
  | off :: offRest => fun ks buf =>
    match ks with
    | [] => none
    | k :: kRest =>
      match sizeOfKind k with
      | none => none
      | some fSz =>
        match sliceRawBytes raw off.bytes fSz with
        | none => none
        | some rawSlice =>
          match writeAbstractBytesAt buf off.bytes (convKind k rawSlice) with
          | none => none
          | some buf' =>
            rawFieldsAtOffsetsByKinds convKind sizeOfKind raw offRest kRest buf'

/--
Overlay converted field slices at `offsets` onto `buf` (initially all `.uninit`)
using `fieldLayouts` (`TypeLayout.fieldLayouts`), leaving inter-field and
trailing padding bytes as `AbstractByte.uninit`.
-/
@[reducible]
def rawFieldsAtOffsetsByLayoutIdxs
    (convLayoutIdx : Nat → List UInt8 → List AbstractByte)
    (layouts : LayoutTable)
    (raw : List UInt8) :
    List Size → List Nat → List AbstractByte → Option (List AbstractByte)
  | [] => fun fs buf =>
    match fs with
    | [] => some buf
    | _ :: _ => none
  | off :: offRest => fun fs buf =>
    match fs with
    | [] => none
    | fIdx :: fRest =>
      match LayoutTable.lookup layouts fIdx with
      | none => none
      | some fl =>
        match sliceRawBytes raw off.bytes fl.size.bytes with
        | none => none
        | some rawSlice =>
          match writeAbstractBytesAt buf off.bytes (convLayoutIdx fIdx rawSlice) with
          | none => none
          | some buf' =>
            rawFieldsAtOffsetsByLayoutIdxs
              convLayoutIdx layouts raw offRest fRest buf'

/--
Find a layout index in `entries` whose byte size equals `targetBytes` and whose
shape is a single-variant `.arbitrary` aggregate with at least one field or a
multi-variant `.multiple` enum.
-/
@[reducible]
def findMatchingAggregateLayoutIdx?
    (targetBytes : Nat) : Nat → List TypeLayout → Option Nat
  | _, [] => none
  | idx, l :: rest =>
    match l.variants, l.fields with
    | .single _, .arbitrary (_ :: _) _ =>
      if Nat.beq l.size.bytes targetBytes then
        some idx
      else
        findMatchingAggregateLayoutIdx? targetBytes (idx + 1) rest
    | .multiple _ _ _, _ =>
      if Nat.beq l.size.bytes targetBytes then
        some idx
      else
        findMatchingAggregateLayoutIdx? targetBytes (idx + 1) rest
    | _, _ => findMatchingAggregateLayoutIdx? targetBytes (idx + 1) rest

/-- Find any layout index in `entries` whose `size.bytes == targetBytes`. -/
@[reducible]
def findAnyLayoutIdxBySize?
    (targetBytes : Nat) : Nat → List TypeLayout → Option Nat
  | _, [] => none
  | idx, l :: rest =>
    if Nat.beq l.size.bytes targetBytes then
      some idx
    else
      findAnyLayoutIdxBySize? targetBytes (idx + 1) rest

/--
Resolve the element `LayoutIdx` for an array with layout `arrayLayoutIdx` and
element byte stride `elemSz`.
-/
@[reducible]
def resolveArrayElemLayoutIdx
    (layouts : LayoutTable) (arrayLayoutIdx elemSz : Nat) : Nat :=
  match LayoutTable.lookup layouts arrayLayoutIdx with
  | some l =>
    match l.fieldLayouts with
    | elemIdx :: _ => elemIdx
    | [] =>
      match findMatchingAggregateLayoutIdx? elemSz 0 layouts.entries with
      | some idx => idx
      | none =>
        match findAnyLayoutIdxBySize? elemSz 0 layouts.entries with
        | some idx => idx
        | none => 0
  | none =>
    match findMatchingAggregateLayoutIdx? elemSz 0 layouts.entries with
    | some idx => idx
    | none => 0

/-- Number of fields in a `FieldsShape`. -/
@[reducible]
def fieldsShapeCount : FieldsShape → Nat
  | .arbitrary offsets _ => length offsets
  | .union n => n
  | .array _ n => n
  | .primitive => 0

/-- Total number of fields across all variants in `variantShapes`. -/
@[reducible]
def totalVariantFieldCount : List FieldsShape → Nat
  | [] => 0
  | vs :: rest => Nat.add (fieldsShapeCount vs) (totalVariantFieldCount rest)

/-- Starting index in a flattened `fieldLayouts` list for variant `varIdx`. -/
@[reducible]
def variantFieldStartIdx : List FieldsShape → Nat → Nat
  | [] => fun _ => 0
  | vs :: rest => fun varIdx =>
    match varIdx with
    | 0 => 0
    | varIdx' + 1 =>
      Nat.add (fieldsShapeCount vs) (variantFieldStartIdx rest varIdx')

/--
Infer the largest power-of-two scalar byte width in `[16, 8, 4, 2, 1]` that fits
within `maxSpan` and divides `offset` (or `offset == 0`).
-/
@[reducible]
def inferAlignedScalarWidth (offset maxSpan : Nat) : Nat :=
  let fitsAndAligned := fun (w : Nat) =>
    Nat.ble w maxSpan && (Nat.beq offset 0 || Nat.beq (Nat.mod offset w) 0)
  if fitsAndAligned 16 then 16
  else if fitsAndAligned 8 then 8
  else if fitsAndAligned 4 then 4
  else if fitsAndAligned 2 then 2
  else if Nat.ble 1 maxSpan then 1
  else 0

/--
Populate variant field bytes at `varOffsets` into `buf` when per-variant
`fieldLayouts` are not present on the `TypeLayout`, leaving inter-field and
trailing padding bytes as `AbstractByte.uninit`.
-/
@[reducible]
def rawVariantFieldsByAlignedSpan
    (table : ShadowProvenanceTable) (l : TypeLayout) (tagOffBytes : Nat)
    (raw : List UInt8) :
    List Size → List AbstractByte → Option (List AbstractByte)
  | [], buf => some buf
  | off :: offRest, buf =>
    let nextOff :=
      match offRest with
      | next :: _ => next.bytes
      | [] => l.size.bytes
    if Nat.ble off.bytes nextOff then
      let maxSpan := Nat.sub nextOff off.bytes
      let (fieldSz, scalarOpt) : Nat × Option ScalarLayout :=
        match l.backendRepr with
        | .scalarPair _ s1 =>
          if Nat.ble (Nat.add tagOffBytes 1) off.bytes then
            match scalarLayoutByteWidth s1 with
            | some sz1 =>
              if Nat.ble sz1 maxSpan && Nat.beq (Nat.mod off.bytes sz1) 0 then
                (sz1, some s1)
              else
                (inferAlignedScalarWidth off.bytes maxSpan, none)
            | none => (inferAlignedScalarWidth off.bytes maxSpan, none)
          else
            (inferAlignedScalarWidth off.bytes maxSpan, none)
        | _ => (inferAlignedScalarWidth off.bytes maxSpan, none)
      match sliceRawBytes raw off.bytes fieldSz with
      | none => none
      | some fRawSlice =>
        let fAbs :=
          match scalarOpt with
          | some s1 => rawScalarLayoutBytes table s1 fRawSlice
          | none => rawBytesToAbstractBytes fRawSlice
        match writeAbstractBytesAt buf off.bytes fAbs with
        | none => none
        | some buf' =>
          rawVariantFieldsByAlignedSpan table l tagOffBytes raw offRest buf'
    else
      none

/--
Fuel-bounded conversion of a raw runtime byte slice `raw : List UInt8` captured
for a value of type `ty` under `layouts` and `table` into `List AbstractByte`:
- Thin (8-byte) and wide (16-byte) pointers and references have their address
  bytes translated via `translatePointerBytes table`.
- Aggregate types (`.tuple`, `.adt`, `.array`) initialize an `AbstractByte.uninit`
  buffer of `l.size.bytes` and populate only active field/tag byte spans from
  `layouts`, preserving all inter-field and trailing padding offsets as
  `AbstractByte.uninit`.
-/
@[reducible]
def rawBytesWithLayoutAndProvenance :
    Nat → LayoutTable → ShadowProvenanceTable → Ty → List UInt8 → List AbstractByte
  | 0, _, _, _, raw => rawBytesToAbstractBytes raw
  | fuel' + 1, layouts, table, ty, raw =>
    match ty.kind with
    | .ref _ pointee | .rawPtr _ pointee =>
      match isWidePointee pointee with
      | false =>
        if Nat.beq (length raw) 8 then
          translatePointerBytes table raw
        else
          rawBytesToAbstractBytes raw
      | true =>
        if Nat.beq (length raw) 16 then
          let ptrBytes := raw.take 8
          let metaBytes := raw.drop 8
          appendAbstractBytes
            (translatePointerBytes table ptrBytes)
            (rawBytesToAbstractBytes metaBytes)
        else
          rawBytesToAbstractBytes raw
    | .fnPtr _ _ _ _ =>
      if Nat.beq (length raw) 8 then
        translatePointerBytes table raw
      else
        rawBytesToAbstractBytes raw
    | .array elemKind n =>
      match Nat.beq n 0 with
      | true => []
      | false =>
        let elemSzOpt : Option Nat :=
          match rigidTyKindByteSize elemKind with
          | some sz => some sz
          | none =>
            match LayoutTable.lookup layouts ty.layoutIdx with
            | some l =>
              match l.fields with
              | .array stride _ => some stride.bytes
              | _ => none
            | none => none
        match elemSzOpt with
        | none => rawBytesToAbstractBytes raw
        | some elemSz =>
          if Nat.beq (length raw) (Nat.mul elemSz n) then
            let elemLayoutIdx := resolveArrayElemLayoutIdx layouts ty.layoutIdx elemSz
            match
              rawArrayChunksWith
                (fun chunk =>
                  rawBytesWithLayoutAndProvenance fuel' layouts table
                    { kind := elemKind, layoutIdx := elemLayoutIdx } chunk)
                elemSz n raw
            with
            | some bs => bs
            | none => rawBytesToAbstractBytes raw
          else
            rawBytesToAbstractBytes raw
    | .tuple (kHead :: kTail) =>
      let fieldKinds := kHead :: kTail
      let convKind := fun (k : RigidTy) (bs : List UInt8) =>
        rawBytesWithLayoutAndProvenance fuel' layouts table
          { kind := k, layoutIdx := 0 } bs
      let sizeOfKind := fun (k : RigidTy) =>
        rigidTyByteSize layouts { kind := k, layoutIdx := 0 }
      match LayoutTable.lookup layouts ty.layoutIdx with
      | some l =>
        if Nat.beq (length raw) l.size.bytes then
          match l.fields with
          | .arbitrary offsets _ =>
            let initBuf := replicateUninitBytes l.size.bytes
            match
              if Nat.beq (length l.fieldLayouts) (length offsets) &&
                  Nat.beq (length fieldKinds) (length offsets) then
                rawFieldsAtOffsetsByLayoutIdxs
                  (fun fIdx bs =>
                    rawBytesWithLayoutAndProvenance fuel' layouts table
                      { kind := .adt "" [], layoutIdx := fIdx } bs)
                  layouts raw offsets l.fieldLayouts initBuf
              else
                none
            with
            | some bs => bs
            | none =>
              match
                rawFieldsAtOffsetsByKinds
                  convKind sizeOfKind raw offsets fieldKinds initBuf
              with
              | some bs => bs
              | none => rawBytesToAbstractBytes raw
          | _ => rawBytesToAbstractBytes raw
        else
          rawBytesToAbstractBytes raw
      | none => rawBytesToAbstractBytes raw
    | .adt _ args =>
      match LayoutTable.lookup layouts ty.layoutIdx with
      | none => rawBytesToAbstractBytes raw
      | some l =>
        if l.isUninhabited || Bool.not (Nat.beq (length raw) l.size.bytes) then
          rawBytesToAbstractBytes raw
        else
          let convKind := fun (k : RigidTy) (bs : List UInt8) =>
            rawBytesWithLayoutAndProvenance fuel' layouts table
              { kind := k, layoutIdx := 0 } bs
          let sizeOfKind := fun (k : RigidTy) =>
            rigidTyByteSize layouts { kind := k, layoutIdx := 0 }
          let convLayoutIdx := fun (fIdx : Nat) (bs : List UInt8) =>
            rawBytesWithLayoutAndProvenance fuel' layouts table
              { kind := .adt "" [], layoutIdx := fIdx } bs
          let initBuf := replicateUninitBytes l.size.bytes
          match l.variants with
          | .empty => initBuf
          | .single _ =>
            match l.fields with
            | .arbitrary [] _ => initBuf
            | .arbitrary offsets _ =>
              let byFieldLayouts : Option (List AbstractByte) :=
                if Nat.beq (length l.fieldLayouts) (length offsets) then
                  rawFieldsAtOffsetsByLayoutIdxs
                    convLayoutIdx layouts raw offsets l.fieldLayouts initBuf
                else
                  none
              match byFieldLayouts with
              | some bs => bs
              | none =>
                let byArgs : Option (List AbstractByte) :=
                  if Nat.beq (length args) (length offsets) then
                    rawFieldsAtOffsetsByKinds
                      convKind sizeOfKind raw offsets args initBuf
                  else
                    none
                match byArgs with
                | some bs => bs
                | none =>
                  match offsets, l.backendRepr with
                  | off0 :: [], .scalar s0 =>
                    match scalarLayoutByteWidth s0 with
                    | some sz0 =>
                      match sliceRawBytes raw off0.bytes sz0 with
                      | some slice0 =>
                        match
                          writeAbstractBytesAt
                            initBuf off0.bytes (rawScalarLayoutBytes table s0 slice0)
                        with
                        | some bs => bs
                        | none => rawBytesToAbstractBytes raw
                      | none => rawBytesToAbstractBytes raw
                    | none => rawBytesToAbstractBytes raw
                  | off0 :: off1 :: [], .scalarPair s0 s1 =>
                    match scalarLayoutByteWidth s0, scalarLayoutByteWidth s1 with
                    | some sz0, some sz1 =>
                      match
                        sliceRawBytes raw off0.bytes sz0,
                        sliceRawBytes raw off1.bytes sz1
                      with
                      | some slice0, some slice1 =>
                        match
                          writeAbstractBytesAt
                            initBuf off0.bytes (rawScalarLayoutBytes table s0 slice0)
                        with
                        | some buf0 =>
                          match
                            writeAbstractBytesAt
                              buf0 off1.bytes (rawScalarLayoutBytes table s1 slice1)
                          with
                          | some bs => bs
                          | none => rawBytesToAbstractBytes raw
                        | none => rawBytesToAbstractBytes raw
                      | _, _ => rawBytesToAbstractBytes raw
                    | _, _ => rawBytesToAbstractBytes raw
                  | _, _ => rawBytesToAbstractBytes raw
            | .primitive =>
              if Nat.beq l.size.bytes 0 then
                []
              else
                match l.backendRepr with
                | .scalar s0 => rawScalarLayoutBytes table s0 raw
                | _ => rawBytesToAbstractBytes raw
            | .array stride count =>
              let elemLayoutIdx :=
                resolveArrayElemLayoutIdx layouts ty.layoutIdx stride.bytes
              match
                rawArrayChunksWith
                  (fun chunk =>
                    rawBytesWithLayoutAndProvenance fuel' layouts table
                      { kind := .adt "" [], layoutIdx := elemLayoutIdx } chunk)
                  stride.bytes count raw
              with
              | some bs => bs
              | none => rawBytesToAbstractBytes raw
            | .union _ => rawBytesToAbstractBytes raw
          | .multiple tagLayout tagField variantShapes =>
            match l.fields, scalarLayoutByteWidth tagLayout with
            | .arbitrary outerOffsets _, some tagSz =>
              match get? outerOffsets tagField with
              | none => rawBytesToAbstractBytes raw
              | some tagOff =>
                match sliceRawBytes raw tagOff.bytes tagSz with
                | none => rawBytesToAbstractBytes raw
                | some rawTagSlice =>
                  let tagAbs := rawScalarLayoutBytes table tagLayout rawTagSlice
                  match writeAbstractBytesAt initBuf tagOff.bytes tagAbs with
                  | none => rawBytesToAbstractBytes raw
                  | some bufWithTag =>
                    match decodeScalarLayoutBytes tagLayout tagAbs with
                    | some (.scalar tagSc) =>
                      let varIdx := tagSc.bits
                      match get? variantShapes varIdx with
                      | some (.arbitrary [] _) => bufWithTag
                      | some (.arbitrary varOffsets _) =>
                        let totalVarFields := totalVariantFieldCount variantShapes
                        let byVarFieldLayouts : Option (List AbstractByte) :=
                          if Nat.beq (length l.fieldLayouts) totalVarFields &&
                              Nat.ble 1 totalVarFields then
                            let startIdx := variantFieldStartIdx variantShapes varIdx
                            let varFieldLayouts :=
                              (l.fieldLayouts.drop startIdx).take (length varOffsets)
                            rawFieldsAtOffsetsByLayoutIdxs
                              convLayoutIdx layouts raw varOffsets varFieldLayouts bufWithTag
                          else
                            none
                        match byVarFieldLayouts with
                        | some bs => bs
                        | none =>
                          if Nat.beq (length args) (length varOffsets) then
                            match
                              rawFieldsAtOffsetsByKinds
                                convKind sizeOfKind raw varOffsets args bufWithTag
                            with
                            | some bs => bs
                            | none => rawBytesToAbstractBytes raw
                          else
                            match
                              rawVariantFieldsByAlignedSpan
                                table l tagOff.bytes raw varOffsets bufWithTag
                            with
                            | some bs => bs
                            | none => rawBytesToAbstractBytes raw
                      | _ => rawBytesToAbstractBytes raw
                    | _ => rawBytesToAbstractBytes raw
            | _, _ => rawBytesToAbstractBytes raw
    | _ => rawBytesToAbstractBytes raw

/--
Convert a raw runtime byte slice `raw : List UInt8` captured for a value of type
`ty` into `List AbstractByte`, applying `table` to reconstruct `(allocId, tag)`
provenance and relative offsets for thin (8-byte) and wide (16-byte) pointers
and references, and using `layouts` (when supplied) to decode padding offsets as
`AbstractByte.uninit`.
-/
@[reducible]
def rawBytesWithProvenance
    (table : ShadowProvenanceTable) (ty : Ty) (raw : List UInt8)
    (layouts : LayoutTable := emptyLayoutTable) :
    List AbstractByte :=
  rawBytesWithLayoutAndProvenance defaultCodecFuel layouts table ty raw

/--
Decode variant fields at `varOffsets` from `absBytes` using aligned scalar widths
when `decodeFieldsBySpan` encounters `.uninit` inter-field or trailing padding.
-/
@[reducible]
def decodeVariantFieldsByAlignedSpan
    (absBytes : List AbstractByte) (l : TypeLayout) (tagOffBytes : Nat) :
    List Size → Option (List Value)
  | [] => some []
  | off :: offRest =>
    let nextOff :=
      match offRest with
      | next :: _ => next.bytes
      | [] => l.size.bytes
    if Nat.ble off.bytes nextOff then
      let maxSpan := Nat.sub nextOff off.bytes
      if Nat.beq maxSpan 0 then
        match decodeVariantFieldsByAlignedSpan absBytes l tagOffBytes offRest with
        | some vs => some (.unit :: vs)
        | none => none
      else
        let fieldSz : Nat :=
          match l.backendRepr with
          | .scalarPair _ s1 =>
            if Nat.ble (Nat.add tagOffBytes 1) off.bytes then
              match scalarLayoutByteWidth s1 with
              | some sz1 =>
                if Nat.ble sz1 maxSpan && Nat.beq (Nat.mod off.bytes sz1) 0 then
                  sz1
                else
                  inferAlignedScalarWidth off.bytes maxSpan
              | none => inferAlignedScalarWidth off.bytes maxSpan
            else
              inferAlignedScalarWidth off.bytes maxSpan
          | _ => inferAlignedScalarWidth off.bytes maxSpan
        match sliceAbstractBytes absBytes off.bytes fieldSz with
        | none => none
        | some fSlice =>
          match decodeScalarBytes fSlice false with
          | none => none
          | some (sv, _) =>
            match decodeVariantFieldsByAlignedSpan absBytes l tagOffBytes offRest with
            | some vs => some (.scalar sv :: vs)
            | none => none
    else
      none

/--
Decode `count` array chunks of `elemSz` bytes from `raw : List UInt8` using
`decodeChunk`.
-/
@[reducible]
def decodeRawArrayChunksWith
    (decodeChunk : List UInt8 → Option Value)
    (elemSz : Nat) :
    Nat → List UInt8 → Option (List Value)
  | 0 => fun raw =>
    match raw with
    | [] => some []
    | _ :: _ => none
  | n + 1 => fun raw =>
    if Nat.ble elemSz (length raw) then
      let chunk := raw.take elemSz
      let rest := raw.drop elemSz
      match
        decodeChunk chunk,
        decodeRawArrayChunksWith decodeChunk elemSz n rest
      with
      | some v, some vs => some (v :: vs)
      | _, _ => none
    else
      none

/--
Decode a raw runtime byte slice `raw : List UInt8` into a `Value` of type `ty`
under `layouts` and shadow provenance table `table` using `decodeValueFromBytes`,
marking padding offsets as `AbstractByte.uninit` via `layouts`.
-/
@[reducible]
def decodeRawValue
    (layouts : LayoutTable) (table : ShadowProvenanceTable)
    (ty : Ty) (raw : List UInt8) : Option Value :=
  match ty.kind with
  | .array elemKind n =>
    if Nat.beq n 0 then
      if Nat.beq (length raw) 0 then some (.aggregate 0 []) else none
    else
      let elemSzOpt : Option Nat :=
        match rigidTyKindByteSize elemKind with
        | some sz => some sz
        | none =>
          match LayoutTable.lookup layouts ty.layoutIdx with
          | some l =>
            match l.fields with
            | .array stride _ => some stride.bytes
            | _ => none
          | none => none
      match elemSzOpt with
      | none => none
      | some elemSz =>
        if Nat.beq (length raw) (Nat.mul elemSz n) then
          let elemLayoutIdx := resolveArrayElemLayoutIdx layouts ty.layoutIdx elemSz
          let elemTy : Ty := { kind := elemKind, layoutIdx := elemLayoutIdx }
          match
            decodeRawArrayChunksWith
              (fun chunk =>
                decodeValueFromBytes defaultCodecFuel layouts elemTy
                  (rawBytesWithProvenance table elemTy chunk layouts))
              elemSz n raw
          with
          | some elems => some (.aggregate 0 elems)
          | none => none
        else
          none
  | .adt _ _ =>
    match LayoutTable.lookup layouts ty.layoutIdx with
    | some l =>
      match l.variants with
      | .multiple tagLayout tagField variantShapes =>
        if l.isUninhabited || Bool.not (Nat.beq (length raw) l.size.bytes) then
          none
        else
          let absBytes := rawBytesWithProvenance table ty raw layouts
          match l.fields, scalarLayoutByteWidth tagLayout with
          | .arbitrary outerOffsets _, some tagSz =>
            match get? outerOffsets tagField with
            | none => none
            | some tagOff =>
              match sliceAbstractBytes absBytes tagOff.bytes tagSz with
              | none => none
              | some tagSlice =>
                match decodeScalarLayoutBytes tagLayout tagSlice with
                | some (.scalar tagSc) =>
                  let varIdx := tagSc.bits
                  match get? variantShapes varIdx with
                  | some (.arbitrary varOffsets _) =>
                    let totalVarFields := totalVariantFieldCount variantShapes
                    let byVarFieldLayouts : Option (List Value) :=
                      if Nat.beq (length l.fieldLayouts) totalVarFields &&
                          Nat.ble 1 totalVarFields then
                        let startIdx := variantFieldStartIdx variantShapes varIdx
                        let varFieldLayouts :=
                          (l.fieldLayouts.drop startIdx).take (length varOffsets)
                        decodeFieldsByLayoutIdxs
                          (fun fIdx bs =>
                            decodeValueFromBytes defaultCodecFuel layouts
                              { kind := .adt "" [], layoutIdx := fIdx } bs)
                          layouts absBytes varOffsets varFieldLayouts
                      else
                        none
                    match byVarFieldLayouts with
                    | some vals => some (.aggregate varIdx vals)
                    | none =>
                      match
                        decodeVariantFieldsByAlignedSpan
                          absBytes l tagOff.bytes varOffsets
                      with
                      | some vals => some (.aggregate varIdx vals)
                      | none =>
                        match decodeFieldsBySpan absBytes l.size.bytes varOffsets with
                        | some vals => some (.aggregate varIdx vals)
                        | none => none
                  | _ => none
                | _ => none
          | _, _ => none
      | _ =>
        let absBytes := rawBytesWithProvenance table ty raw layouts
        decodeValueFromBytes defaultCodecFuel layouts ty absBytes
    | none =>
      let absBytes := rawBytesWithProvenance table ty raw layouts
      decodeValueFromBytes defaultCodecFuel layouts ty absBytes
  | _ =>
    let absBytes := rawBytesWithProvenance table ty raw layouts
    decodeValueFromBytes defaultCodecFuel layouts ty absBytes

/-- Alias for `decodeRawValue`. -/
abbrev decodeRawValueWithTable := decodeRawValue

/-- Decode a list of raw runtime byte slices against a list of parameter `LocalDecl`s. -/
@[reducible]
def decodeRawArgsByDecls
    (layouts : LayoutTable) (table : ShadowProvenanceTable)
    (decls : List LocalDecl) : List (List UInt8) → Option (List Value)
  | [] => some []
  | raw :: rawRest =>
    match decls with
    | [] => none
    | decl :: declRest =>
      match
        decodeRawValue layouts table decl.ty raw,
        decodeRawArgsByDecls layouts table declRest rawRest
      with
      | some v, some vs => some (v :: vs)
      | _, _ => none

/--
Decode the incoming root or callee argument byte slices `rawArgs` using the
function's `CapturedMir` (`body.localDecls` slots `1..=body.argCount` and
`body.layouts`).
-/
@[reducible]
def decodeFnArgsFromRawBytes
    (body : CapturedMir) (table : ShadowProvenanceTable)
    (rawArgs : List (List UInt8)) : Option (List Value) :=
  if Nat.beq (length rawArgs) body.argCount then
    decodeRawArgsByDecls body.layouts table (body.localDecls.drop 1) rawArgs
  else
    none

/--
Decode a function's return value byte slice `rawRet` using `body.localDecls[0]`
(`_0`) and `body.layouts`.
-/
@[reducible]
def decodeFnRetFromRawBytes
    (body : CapturedMir) (table : ShadowProvenanceTable)
    (rawRet : List UInt8) : Option Value :=
  match body.localDecls with
  | retDecl :: _ => decodeRawValue body.layouts table retDecl.ty rawRet
  | [] => none

/-- Round `offset` up to the next multiple of `align` (when `align > 1`). -/
@[reducible]
def alignUpOffset (offset align : Nat) : Nat :=
  if Nat.ble align 1 then
    offset
  else
    let rem := Nat.mod offset align
    if Nat.beq rem 0 then
      offset
    else
      Nat.add offset (Nat.sub align rem)

/-- Look up a `Ty` with `t.kind == targetKind` in `decls`. -/
@[reducible]
def findTyInLocalDecls? (targetKind : RigidTy) : List LocalDecl → Option Ty
  | [] => none
  | decl :: rest =>
    if rigidTyEqFuel 8 decl.ty.kind targetKind then
      some decl.ty
    else
      findTyInLocalDecls? targetKind rest

/--
Search `bodies` for a `LocalDecl` whose `ty.kind == targetKind`, returning both
the body's `LayoutTable` and the matching `Ty`.
-/
@[reducible]
def findTyWithLayoutsInBodies?
    (targetKind : RigidTy) : List CapturedMir → Option (LayoutTable × Ty)
  | [] => none
  | b :: rest =>
    match findTyInLocalDecls? targetKind b.localDecls with
    | some ty => some (b.layouts, ty)
    | none => findTyWithLayoutsInBodies? targetKind rest

/--
Extract the projected `Ty` of `.deref :: .field targetFieldIdx fieldTy :: _` on
`paramLocal` from a `Place`, if present.
-/
@[reducible]
def matchDerefFieldPlaceTy?
    (paramLocal targetFieldIdx : Nat) (p : Place) : Option Ty :=
  if Nat.beq p.local_ paramLocal then
    match p.projection with
    | .deref :: .field fIdx fTy :: _ =>
      if Nat.beq fIdx targetFieldIdx then some fTy else none
    | _ => none
  else
    none

/--
Extract the field index `fIdx` of any `.deref :: .field fIdx _ :: _` projection
on `paramLocal` from a `Place`, if present.
-/
@[reducible]
def matchDerefAnyFieldIdx? (paramLocal : Nat) (p : Place) : Option Nat :=
  if Nat.beq p.local_ paramLocal then
    match p.projection with
    | .deref :: .field fIdx _ :: _ => some fIdx
    | _ => none
  else
    none

/-- Combine two `Option Nat` values by taking the maximum when both are `some`. -/
@[reducible]
def maxOptionNat : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some x, some y => if Nat.ble x y then some y else some x

/-- Search an `Operand` for a dereferenced field projection on `paramLocal`. -/
@[reducible]
def findDerefFieldTyInOperand?
    (paramLocal targetFieldIdx : Nat) : Operand → Option Ty
  | .copy p | .move p => matchDerefFieldPlaceTy? paramLocal targetFieldIdx p
  | .constant _ => none

/-- Search an `Operand` for the maximum dereferenced field index on `paramLocal`. -/
@[reducible]
def findMaxDerefFieldIdxInOperand? (paramLocal : Nat) : Operand → Option Nat
  | .copy p | .move p => matchDerefAnyFieldIdx? paramLocal p
  | .constant _ => none

/-- Search an `Rvalue` for a dereferenced field projection on `paramLocal`. -/
@[reducible]
def findDerefFieldTyInRvalue?
    (paramLocal targetFieldIdx : Nat) : Rvalue → Option Ty
  | .use op | .repeat op _ | .cast _ op _ | .unaryOp _ op | .shallowInitBox op _
  | .wrapUnsafeBinder op _ =>
    findDerefFieldTyInOperand? paramLocal targetFieldIdx op
  | .ref _ p | .rawPtr _ p | .len p | .discriminant p | .copyForDeref p =>
    matchDerefFieldPlaceTy? paramLocal targetFieldIdx p
  | .binaryOp _ lhs rhs =>
    match findDerefFieldTyInOperand? paramLocal targetFieldIdx lhs with
    | some ty => some ty
    | none => findDerefFieldTyInOperand? paramLocal targetFieldIdx rhs
  | _ => none

/-- Search an `Rvalue` for the maximum dereferenced field index on `paramLocal`. -/
@[reducible]
def findMaxDerefFieldIdxInRvalue? (paramLocal : Nat) : Rvalue → Option Nat
  | .use op | .repeat op _ | .cast _ op _ | .unaryOp _ op | .shallowInitBox op _
  | .wrapUnsafeBinder op _ =>
    findMaxDerefFieldIdxInOperand? paramLocal op
  | .ref _ p | .rawPtr _ p | .len p | .discriminant p | .copyForDeref p =>
    matchDerefAnyFieldIdx? paramLocal p
  | .binaryOp _ lhs rhs =>
    maxOptionNat
      (findMaxDerefFieldIdxInOperand? paramLocal lhs)
      (findMaxDerefFieldIdxInOperand? paramLocal rhs)
  | _ => none

/-- Search a list of `Statement`s for a dereferenced field projection on `paramLocal`. -/
@[reducible]
def findDerefFieldTyInStmts?
    (paramLocal targetFieldIdx : Nat) : List Statement → Option Ty
  | [] => none
  | stmt :: rest =>
    let found : Option Ty :=
      match stmt.kind with
      | .assign dst rv =>
        match matchDerefFieldPlaceTy? paramLocal targetFieldIdx dst with
        | some ty => some ty
        | none => findDerefFieldTyInRvalue? paramLocal targetFieldIdx rv
      | .setDiscriminant p _ | .deinit p | .placeMention p | .retag _ p =>
        matchDerefFieldPlaceTy? paramLocal targetFieldIdx p
      | _ => none
    match found with
    | some ty => some ty
    | none => findDerefFieldTyInStmts? paramLocal targetFieldIdx rest

/-- Search a list of `Statement`s for the maximum dereferenced field index on `paramLocal`. -/
@[reducible]
def findMaxDerefFieldIdxInStmts?
    (paramLocal : Nat) : List Statement → Option Nat
  | [] => none
  | stmt :: rest =>
    let cur : Option Nat :=
      match stmt.kind with
      | .assign dst rv =>
        maxOptionNat
          (matchDerefAnyFieldIdx? paramLocal dst)
          (findMaxDerefFieldIdxInRvalue? paramLocal rv)
      | .setDiscriminant p _ | .deinit p | .placeMention p | .retag _ p =>
        matchDerefAnyFieldIdx? paramLocal p
      | _ => none
    maxOptionNat cur (findMaxDerefFieldIdxInStmts? paramLocal rest)

/-- Search `BasicBlockData`s for a dereferenced field projection on `paramLocal`. -/
@[reducible]
def findDerefFieldTyInBlocks?
    (paramLocal targetFieldIdx : Nat) : List BasicBlockData → Option Ty
  | [] => none
  | bb :: rest =>
    match findDerefFieldTyInStmts? paramLocal targetFieldIdx bb.statements with
    | some ty => some ty
    | none => findDerefFieldTyInBlocks? paramLocal targetFieldIdx rest

/-- Search `BasicBlockData`s for the maximum dereferenced field index on `paramLocal`. -/
@[reducible]
def findMaxDerefFieldIdxInBlocks?
    (paramLocal : Nat) : List BasicBlockData → Option Nat
  | [] => none
  | bb :: rest =>
    maxOptionNat
      (findMaxDerefFieldIdxInStmts? paramLocal bb.statements)
      (findMaxDerefFieldIdxInBlocks? paramLocal rest)

/-- Resolve `(sizeBytes, alignBytes)` for a field `Ty` under `layouts`. -/
@[reducible]
def fieldTySizeAndAlign (layouts : LayoutTable) (fieldTy : Ty) : Option Nat × Nat :=
  match LayoutTable.lookup layouts fieldTy.layoutIdx with
  | some fl => (some fl.size.bytes, fl.align.bytes)
  | none => (rigidTyByteSize layouts fieldTy, 1)

/--
Decode dereferenced struct fields `0 ..= maxFieldIdx` of `paramLocal` from
`refRawBytes` when `pointee`'s `TypeLayout` is absent from `rootBody.layouts`
(e.g., in hand-written MIR fixtures). Supports both unprojected leading fields
and 2-field `repr(Rust)` alignment-reordered structs.
-/
@[reducible]
def decodeProjectedStructFieldsSequential
    (rootBody : CapturedMir) (table : ShadowProvenanceTable)
    (paramLocal : Nat) (refRawBytes : List UInt8) :
    Nat → Nat → Nat → List Value
  | 0, _, _ => []
  | rem + 1, fieldIdx, curOffset =>
    match findDerefFieldTyInBlocks? paramLocal fieldIdx rootBody.basicBlocks with
    | none =>
      let b0 : Nat :=
        match sliceRawBytes refRawBytes curOffset 1 with
        | some (b :: _) => b.toBitVec.toNat
        | _ => 0
      .scalar ⟨b0, 1⟩ ::
        decodeProjectedStructFieldsSequential
          rootBody table paramLocal refRawBytes
          rem (fieldIdx + 1) (curOffset + 1)
    | some fieldTy =>
      let (fSizeOpt, fAlign) := fieldTySizeAndAlign rootBody.layouts fieldTy
      match fSizeOpt with
      | none => []
      | some fSize =>
        let alignedOff := alignUpOffset curOffset fAlign
        match sliceRawBytes refRawBytes alignedOff fSize with
        | none => []
        | some fRawSlice =>
          match decodeRawValue rootBody.layouts table fieldTy fRawSlice with
          | none => []
          | some fVal =>
            fVal ::
              decodeProjectedStructFieldsSequential
                rootBody table paramLocal refRawBytes
                rem (fieldIdx + 1) (Nat.add alignedOff fSize)

/--
Decode dereferenced struct fields of `paramLocal` using the field projections in
`rootBody.basicBlocks` when no `TypeLayout` for the struct is present in
`rootBody.layouts`.
-/
@[reducible]
def decodeProjectedStructFieldsFromBody
    (rootBody : CapturedMir) (table : ShadowProvenanceTable)
    (paramLocal : Nat) (refRawBytes : List UInt8) : List Value :=
  match findMaxDerefFieldIdxInBlocks? paramLocal rootBody.basicBlocks with
  | none => []
  | some maxFieldIdx =>
    if Nat.beq maxFieldIdx 1 then
      match
        findDerefFieldTyInBlocks? paramLocal 0 rootBody.basicBlocks,
        findDerefFieldTyInBlocks? paramLocal 1 rootBody.basicBlocks
      with
      | some fTy0, some fTy1 =>
        let (szOpt0, al0) := fieldTySizeAndAlign rootBody.layouts fTy0
        let (szOpt1, al1) := fieldTySizeAndAlign rootBody.layouts fTy1
        match szOpt0, szOpt1 with
        | some sz0, some sz1 =>
          if Nat.ble (Nat.add al0 1) al1 then
            let off0 := alignUpOffset sz1 al0
            match
              sliceRawBytes refRawBytes off0 sz0,
              sliceRawBytes refRawBytes 0 sz1
            with
            | some slice0, some slice1 =>
              match
                decodeRawValue rootBody.layouts table fTy0 slice0,
                decodeRawValue rootBody.layouts table fTy1 slice1
              with
              | some v0, some v1 => [v0, v1]
              | _, _ =>
                decodeProjectedStructFieldsSequential
                  rootBody table paramLocal refRawBytes 2 0 0
            | _, _ =>
              decodeProjectedStructFieldsSequential
                rootBody table paramLocal refRawBytes 2 0 0
          else
            decodeProjectedStructFieldsSequential
              rootBody table paramLocal refRawBytes 2 0 0
        | _, _ =>
          decodeProjectedStructFieldsSequential
            rootBody table paramLocal refRawBytes 2 0 0
      | _, _ =>
        decodeProjectedStructFieldsSequential
          rootBody table paramLocal refRawBytes 2 0 0
    else
      decodeProjectedStructFieldsSequential
        rootBody table paramLocal refRawBytes (maxFieldIdx + 1) 0 0

/--
Resolve the pointee `(LayoutTable, Ty)` and optional byte size for a pointer or
reference parameter of type `ptrTy` pointing to `pointee : RigidTy`.
-/
@[reducible]
def resolvePointeeTyAndSize
    (rootBody : CapturedMir) (auxBodies : List CapturedMir)
    (ptrTy : Ty) (pointee : RigidTy) (availByteLen : Nat) :
    LayoutTable × Ty × Option Nat :=
  let fromPtrFieldLayouts : Option (LayoutTable × Ty × Option Nat) :=
    match LayoutTable.lookup rootBody.layouts ptrTy.layoutIdx with
    | some ptrLayout =>
      match ptrLayout.fieldLayouts with
      | pointeeIdx :: _ =>
        match LayoutTable.lookup rootBody.layouts pointeeIdx with
        | some pl =>
          some (rootBody.layouts, { kind := pointee, layoutIdx := pointeeIdx }, some pl.size.bytes)
        | none => none
      | [] => none
    | none => none
  match fromPtrFieldLayouts with
  | some res => res
  | none =>
    match findTyWithLayoutsInBodies? pointee (rootBody :: auxBodies) with
    | some (layouts, ty) =>
      let szOpt :=
        match rigidTyKindByteSize pointee with
        | some sz => some sz
        | none =>
          match LayoutTable.lookup layouts ty.layoutIdx with
          | some pl => some pl.size.bytes
          | none => none
      (layouts, ty, szOpt)
    | none =>
      match rigidTyKindByteSize pointee with
      | some sz => (rootBody.layouts, { kind := pointee, layoutIdx := 0 }, some sz)
      | none =>
        match findMatchingAggregateLayoutIdx? availByteLen 0 rootBody.layouts.entries with
        | some lIdx =>
          (rootBody.layouts, { kind := pointee, layoutIdx := lIdx }, some availByteLen)
        | none =>
          (rootBody.layouts, { kind := pointee, layoutIdx := 0 }, none)

/--
Decode the referent bytes `refRawBytes` of a registered pointer parameter
`paramLocal` pointing to `pointee : RigidTy`.
-/
@[reducible]
def decodePointeeReferentValue
    (rootBody : CapturedMir) (auxBodies : List CapturedMir)
    (table : ShadowProvenanceTable) (paramLocal : Nat)
    (ptrTy : Ty) (pointee : RigidTy) (refRawBytes : List UInt8) : Option Value :=
  let (pointeeLayouts, pointeeTy, _) :=
    resolvePointeeTyAndSize rootBody auxBodies ptrTy pointee (length refRawBytes)
  let hasExplicitLayout : Bool :=
    match LayoutTable.lookup rootBody.layouts ptrTy.layoutIdx with
    | some ptrLayout =>
      match ptrLayout.fieldLayouts with
      | _ :: _ => true
      | [] => (findTyWithLayoutsInBodies? pointee (rootBody :: auxBodies)).isSome
    | none => (findTyWithLayoutsInBodies? pointee (rootBody :: auxBodies)).isSome
  if hasExplicitLayout then
    decodeRawValue pointeeLayouts table pointeeTy refRawBytes
  else
    let projFields :=
      decodeProjectedStructFieldsFromBody rootBody table paramLocal refRawBytes
    match projFields with
    | _ :: _ => some (.aggregate 0 projFields)
    | [] =>
      decodeRawValue pointeeLayouts table pointeeTy refRawBytes

/--
Sequential helper for populating `List AbstractByte` from dereferenced struct
field projections when no explicit `TypeLayout` for the struct is present in
`rootBody.layouts`, leaving inter-field and trailing padding as `.uninit`.
-/
@[reducible]
def rawProjectedStructBytesSequential
    (rootBody : CapturedMir) (table : ShadowProvenanceTable)
    (paramLocal : Nat) (refRawBytes : List UInt8) :
    Nat → Nat → Nat → List AbstractByte → Option (List AbstractByte)
  | 0, _, _, buf => some buf
  | rem + 1, fieldIdx, curOffset, buf =>
    match findDerefFieldTyInBlocks? paramLocal fieldIdx rootBody.basicBlocks with
    | none =>
      let bAbs : List AbstractByte :=
        match sliceRawBytes refRawBytes curOffset 1 with
        | some s => rawBytesToAbstractBytes s
        | none => [.init 0 none]
      match writeAbstractBytesAt buf curOffset bAbs with
      | none => none
      | some buf' =>
        rawProjectedStructBytesSequential
          rootBody table paramLocal refRawBytes
          rem (fieldIdx + 1) (curOffset + 1) buf'
    | some fieldTy =>
      let (fSizeOpt, fAlign) := fieldTySizeAndAlign rootBody.layouts fieldTy
      match fSizeOpt with
      | none => none
      | some fSize =>
        let alignedOff := alignUpOffset curOffset fAlign
        match sliceRawBytes refRawBytes alignedOff fSize with
        | none => none
        | some fRawSlice =>
          let fAbs := rawBytesWithProvenance table fieldTy fRawSlice rootBody.layouts
          match writeAbstractBytesAt buf alignedOff fAbs with
          | none => none
          | some buf' =>
            rawProjectedStructBytesSequential
              rootBody table paramLocal refRawBytes
              rem (fieldIdx + 1) (Nat.add alignedOff fSize) buf'

/--
Populate `List AbstractByte` for a dereferenced struct parameter `paramLocal`
from the field projections in `rootBody.basicBlocks` when no `TypeLayout` for
the struct is present in `rootBody.layouts`.
-/
@[reducible]
def rawProjectedStructBytesFromBody
    (rootBody : CapturedMir) (table : ShadowProvenanceTable)
    (paramLocal : Nat) (refRawBytes : List UInt8) : Option (List AbstractByte) :=
  let initBuf := replicateUninitBytes (length refRawBytes)
  match findMaxDerefFieldIdxInBlocks? paramLocal rootBody.basicBlocks with
  | none => none
  | some maxFieldIdx =>
    if Nat.beq maxFieldIdx 1 then
      match
        findDerefFieldTyInBlocks? paramLocal 0 rootBody.basicBlocks,
        findDerefFieldTyInBlocks? paramLocal 1 rootBody.basicBlocks
      with
      | some fTy0, some fTy1 =>
        let (szOpt0, al0) := fieldTySizeAndAlign rootBody.layouts fTy0
        let (szOpt1, al1) := fieldTySizeAndAlign rootBody.layouts fTy1
        match szOpt0, szOpt1 with
        | some sz0, some sz1 =>
          if Nat.ble (Nat.add al0 1) al1 then
            let off0 := alignUpOffset sz1 al0
            match
              sliceRawBytes refRawBytes off0 sz0,
              sliceRawBytes refRawBytes 0 sz1
            with
            | some slice0, some slice1 =>
              let abs0 := rawBytesWithProvenance table fTy0 slice0 rootBody.layouts
              let abs1 := rawBytesWithProvenance table fTy1 slice1 rootBody.layouts
              match writeAbstractBytesAt initBuf 0 abs1 with
              | some buf1 => writeAbstractBytesAt buf1 off0 abs0
              | none => none
            | _, _ =>
              rawProjectedStructBytesSequential
                rootBody table paramLocal refRawBytes 2 0 0 initBuf
          else
            rawProjectedStructBytesSequential
              rootBody table paramLocal refRawBytes 2 0 0 initBuf
        | _, _ =>
          rawProjectedStructBytesSequential
            rootBody table paramLocal refRawBytes 2 0 0 initBuf
      | _, _ =>
        rawProjectedStructBytesSequential
          rootBody table paramLocal refRawBytes 2 0 0 initBuf
    else
      rawProjectedStructBytesSequential
        rootBody table paramLocal refRawBytes (maxFieldIdx + 1) 0 0 initBuf

/--
Convert the referent bytes `refRawBytes` of a registered pointer parameter
`paramLocal` pointing to `pointee : RigidTy` into `List AbstractByte`, marking
padding offsets as `.uninit`.
-/
@[reducible]
def decodePointeeReferentAbsBytes
    (rootBody : CapturedMir) (auxBodies : List CapturedMir)
    (table : ShadowProvenanceTable) (paramLocal : Nat)
    (ptrTy : Ty) (pointee : RigidTy) (refRawBytes : List UInt8) : List AbstractByte :=
  let (pointeeLayouts, pointeeTy, _) :=
    resolvePointeeTyAndSize rootBody auxBodies ptrTy pointee (length refRawBytes)
  let hasExplicitLayout : Bool :=
    match LayoutTable.lookup rootBody.layouts ptrTy.layoutIdx with
    | some ptrLayout =>
      match ptrLayout.fieldLayouts with
      | _ :: _ => true
      | [] => (findTyWithLayoutsInBodies? pointee (rootBody :: auxBodies)).isSome
    | none => (findTyWithLayoutsInBodies? pointee (rootBody :: auxBodies)).isSome
  if hasExplicitLayout then
    rawBytesWithProvenance table pointeeTy refRawBytes pointeeLayouts
  else
    match rawProjectedStructBytesFromBody rootBody table paramLocal refRawBytes with
    | some bs => bs
    | none => rawBytesWithProvenance table pointeeTy refRawBytes pointeeLayouts

/-- Convert `AbstractByte` into `Option UInt8` (`none` for `.uninit`). -/
@[reducible]
def abstractByteToOptionUInt8 : AbstractByte → Option UInt8
  | .init b _ => some b
  | .uninit => none

/-- Map `abstractByteToOptionUInt8` across a list of `AbstractByte`s. -/
@[reducible]
def abstractBytesToGlobalBytes : List AbstractByte → List (Option UInt8)
  | [] => []
  | b :: rest => abstractByteToOptionUInt8 b :: abstractBytesToGlobalBytes rest

/-- Construct a list of `n` `LocalSlot.dead` entries. -/
@[reducible]
def replicateDeadLocals : Nat → List LocalSlot
  | 0 => []
  | n + 1 => .dead :: replicateDeadLocals n

/-- Compute the maximum `localDecls.length` across a list of `CapturedMir` bodies. -/
@[reducible]
def maxLocalCountInBodies : List CapturedMir → Nat
  | [] => 0
  | b :: rest =>
    let restMax := maxLocalCountInBodies rest
    let curLen := length b.localDecls
    if Nat.ble restMax curLen then curLen else restMax

/--
Pad `callerLocals` with `.dead` slots so its length is at least `minLen`,
ensuring that any appended caller local slot has an index `>= length locals` in
both `rootBody` and all `inlinedCallees`.
-/
@[reducible]
def ensureCallerLocalsPad (callerLocals : List LocalSlot) (minLen : Nat) : List LocalSlot :=
  if Nat.ble minLen (length callerLocals) then
    callerLocals
  else
    callerLocals ++ replicateDeadLocals (Nat.sub minLen (length callerLocals))

/--
Determine the initial `TreeBorrowPerm` for an incoming pointer/reference
parameter of mutability `mutbl` and pointee `pointee`.
-/
@[reducible]
def ptrParamBorrowPerm (mutbl : Mutability) (pointee : RigidTy) : TreeBorrowPerm :=
  match mutbl with
  | .mut => .active
  | .not =>
    if rigidTyIsFreezeFuel 16 pointee then .frozen else .reserved

/--
Populate `mem.borrows`, `mem.callerLocals`, and `mem.globals` for a single
registered pointer/reference parameter when its runtime address resolves to a
`ShadowAllocEntry` carrying non-empty initial `rawBytes`.
-/
@[reducible]
def populateSinglePtrParamMemory
    (rootBody : CapturedMir) (auxBodies : List CapturedMir)
    (table : ShadowProvenanceTable) (minCallerIdx : Nat)
    (paramLocal : Nat) (decl : LocalDecl) (rawArg : List UInt8) (argVal : Value)
    (mem : Memory) : Memory :=
  match decl.ty.kind with
  | .ref mutbl pointee | .rawPtr mutbl pointee =>
    match mem with
    | ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
       activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs⟩ =>
      match isWidePointee pointee with
      | false =>
        match argVal with
        | .ptr ptrVal 8 =>
          if Nat.beq (length rawArg) 8 then
            let addr := decodeRawLittleEndianNat rawArg
            match lookupShadowAllocEntry? table addr with
            | none => mem
            | some (entry, relOffset) =>
              if Nat.beq (length entry.rawBytes) 0 ||
                  Bool.not (Nat.ble relOffset (length entry.rawBytes)) then
                mem
              else
                let availBytes := entry.rawBytes.drop relOffset
                let (_, _, pointeeSzOpt) :=
                  resolvePointeeTyAndSize
                    rootBody auxBodies decl.ty pointee (length availBytes)
                let refRawBytes :=
                  match pointeeSzOpt with
                  | some sz =>
                    if Nat.ble sz (length availBytes) then
                      availBytes.take sz
                    else
                      availBytes
                  | none => availBytes
                match
                  decodePointeeReferentValue
                    rootBody auxBodies table paramLocal decl.ty pointee refRawBytes
                with
                | none => mem
                | some referentVal =>
                  let paddedCallerLocals :=
                    ensureCallerLocalsPad callerLocals minCallerIdx
                  let targetLocal := length paddedCallerLocals
                  let nextCallerLocals := paddedCallerLocals ++ [LocalSlot.init referentVal]
                  let perm := ptrParamBorrowPerm mutbl pointee
                  let nextBorrows :=
                    match lookupBorrow borrows ptrVal.tag with
                    | some _ => borrows
                    | none =>
                      { tag := ptrVal.tag
                        targetLocal := targetLocal
                        targetProjection := []
                        perm := perm } :: borrows
                  let nextTagVal :=
                    if Nat.ble nextTag ptrVal.tag then
                      Nat.add ptrVal.tag 1
                    else
                      nextTag
                  let nextGlobals :=
                    match lookupGlobalAlloc globals entry.allocId with
                    | some _ => globals
                    | none =>
                      let absBytes :=
                        decodePointeeReferentAbsBytes
                          rootBody auxBodies table paramLocal decl.ty pointee refRawBytes
                      { allocId := entry.allocId
                        bytes := abstractBytesToGlobalBytes absBytes
                        relocations := []
                        align := { bytes := 8 }
                        mutability := mutbl } :: globals
                  ⟨nextAllocId, nextGlobals, nextBorrows, nextTagVal, callees, traitImpls, callStack, activeCallee, activeProtectors, nextProtector, nextCallerLocals, fnPtrs⟩
          else
            mem
        | _ => mem
      | true =>
        match pointee, argVal with
        | .slice elemKind, .aggregate 0 [.ptr ptrVal 8, .scalar metaSv] =>
          if Nat.beq (length rawArg) 16 then
            let addr := decodeRawLittleEndianNat (rawArg.take 8)
            match lookupShadowAllocEntry? table addr with
            | none => mem
            | some (entry, relOffset) =>
              if Nat.beq (length entry.rawBytes) 0 ||
                  Bool.not (Nat.ble relOffset (length entry.rawBytes)) then
                mem
              else
                let availBytes := entry.rawBytes.drop relOffset
                let arrayKind : RigidTy := .array elemKind metaSv.bits
                let elemSz :=
                  match rigidTyKindByteSize elemKind with
                  | some sz => sz
                  | none =>
                    let (_, _, elemSzOpt) :=
                      resolvePointeeTyAndSize
                        rootBody auxBodies decl.ty elemKind (length availBytes)
                    match elemSzOpt with
                    | some sz => sz
                    | none => 0
                let sliceByteLen := Nat.mul elemSz metaSv.bits
                let refRawBytes :=
                  if Nat.ble 1 sliceByteLen && Nat.ble sliceByteLen (length availBytes) then
                    availBytes.take sliceByteLen
                  else
                    availBytes
                match
                  decodePointeeReferentValue
                    rootBody auxBodies table paramLocal decl.ty arrayKind refRawBytes
                with
                | none => mem
                | some referentVal =>
                  let paddedCallerLocals :=
                    ensureCallerLocalsPad callerLocals minCallerIdx
                  let targetLocal := length paddedCallerLocals
                  let nextCallerLocals := paddedCallerLocals ++ [LocalSlot.init referentVal]
                  let perm := ptrParamBorrowPerm mutbl pointee
                  let nextBorrows :=
                    match lookupBorrow borrows ptrVal.tag with
                    | some _ => borrows
                    | none =>
                      { tag := ptrVal.tag
                        targetLocal := targetLocal
                        targetProjection := []
                        perm := perm } :: borrows
                  let nextTagVal :=
                    if Nat.ble nextTag ptrVal.tag then
                      Nat.add ptrVal.tag 1
                    else
                      nextTag
                  let nextGlobals :=
                    match lookupGlobalAlloc globals entry.allocId with
                    | some _ => globals
                    | none =>
                      let absBytes :=
                        decodePointeeReferentAbsBytes
                          rootBody auxBodies table paramLocal decl.ty arrayKind refRawBytes
                      { allocId := entry.allocId
                        bytes := abstractBytesToGlobalBytes absBytes
                        relocations := []
                        align := { bytes := 8 }
                        mutability := mutbl } :: globals
                  ⟨nextAllocId, nextGlobals, nextBorrows, nextTagVal, callees, traitImpls, callStack, activeCallee, activeProtectors, nextProtector, nextCallerLocals, fnPtrs⟩
          else
            mem
        | _, _ => mem
  | _ => mem

/--
Walk all parameters of `rootBody` (`localDecls.drop 1`) and populate initial
memory in `mem` for registered pointer allocations.
-/
@[reducible]
def populateShadowPointerMemoryAux
    (rootBody : CapturedMir) (auxBodies : List CapturedMir)
    (table : ShadowProvenanceTable) (minCallerIdx : Nat)
    (paramLocal : Nat) (decls : List LocalDecl) (rawArgs : List (List UInt8)) :
    List Value → Memory → Memory
  | [], mem => mem
  | argVal :: argRest, mem =>
    match decls, rawArgs with
    | decl :: declRest, rawArg :: rawRest =>
      let mem' :=
        populateSinglePtrParamMemory
          rootBody auxBodies table minCallerIdx paramLocal decl rawArg argVal mem
      populateShadowPointerMemoryAux
        rootBody auxBodies table minCallerIdx (paramLocal + 1)
        declRest rawRest argRest mem'
    | _, _ => mem

/--
Supply initial `borrows`, `callerLocals`, and `globals` in `baseMem` for any
pointer or reference argument of `rootBody` whose runtime address is registered
in `table` (`ShadowProvenanceTable`) with initial `rawBytes`. Unregistered
pointer arguments are left unmapped so dereferencing them faults with `.ub`.
-/
@[reducible]
def populateShadowPointerMemory
    (rootBody : CapturedMir) (auxBodies : List CapturedMir)
    (table : ShadowProvenanceTable) (rawArgs : List (List UInt8))
    (args : List Value) (baseMem : Memory) : Memory :=
  match table with
  | [] => baseMem
  | _ :: _ =>
    let minCallerIdx := maxLocalCountInBodies (rootBody :: auxBodies)
    populateShadowPointerMemoryAux
      rootBody auxBodies table minCallerIdx 1
      (rootBody.localDecls.drop 1) rawArgs args baseMem

/--
Raw byte-level interaction event recorded at runtime before `LayoutTable`
decoding.
-/
inductive RawObservedEvent : Type where
  | branch (tag : Nat)
  | extCall (defPath : DefPath) (rawArgs : List (List UInt8)) (rawRet : List UInt8)
  | extCallPanic (defPath : DefPath) (rawArgs : List (List UInt8))
  | extCallAbort (defPath : DefPath) (rawArgs : List (List UInt8))
  deriving Repr, DecidableEq

/-- Alias for `RawObservedEvent`. -/
abbrev RawTraceEvent : Type := RawObservedEvent

/-- Raw external call record before embedding into `RawObservedEvent`. -/
structure RawCallEvent : Type where
  defPath : DefPath
  rawArgs : List (List UInt8)
  rawRet : Option (List UInt8) := none
  panicked : Bool := false
  deriving Repr, DecidableEq

/-- Convert a `RawCallEvent` into a `RawObservedEvent`. -/
@[reducible]
def RawCallEvent.toRawObservedEvent (ev : RawCallEvent) : RawObservedEvent :=
  match ev.rawRet with
  | some ret => .extCall ev.defPath ev.rawArgs ret
  | none =>
    if ev.panicked then .extCallPanic ev.defPath ev.rawArgs
    else .extCallAbort ev.defPath ev.rawArgs

/-- Raw byte-level terminal outcome recorded at runtime. -/
inductive RawObservedOutcome : Type where
  | normal (rawRet : List UInt8)
  | panic
  | abort
  deriving Repr, DecidableEq

/-- Alias for `RawObservedOutcome`. -/
abbrev RawOutcome : Type := RawObservedOutcome

/--
Complete raw byte-level execution trace captured by a runtime observer wrapping
a compiled Rust artifact.
-/
structure RawByteTrace : Type where
  rawArgs : List (List UInt8)
  initMem : Memory := emptyMemory
  inlinedCallees : List CapturedMir := []
  events : List RawObservedEvent
  outcome : RawObservedOutcome
  deriving Repr, DecidableEq

/--
Decode a single `RawObservedEvent` using `calleeSigs` and `table`.
Rejects (`none`) any external call whose callee signature takes a `&mut` or
raw-pointer parameter (`findCalleeImpurePtrArgIdx? sigBody = some _`), since
`TraceCheck` assumes memory-pure external callees.
-/
@[reducible]
def decodeRawObservedEvent
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable) :
    RawObservedEvent → Option ObservedEvent
  | .branch tag => some (.branch tag)
  | .extCall defPath rawArgs rawRet =>
    match findCallee? calleeSigs defPath with
    | some sigBody =>
      match findCalleeImpurePtrArgIdx? sigBody with
      | some _ => none
      | none =>
        match
          decodeFnArgsFromRawBytes sigBody table rawArgs,
          decodeFnRetFromRawBytes sigBody table rawRet
        with
        | some args, some retVal => some (.extCall defPath args retVal)
        | _, _ => none
    | none => none
  | .extCallPanic defPath rawArgs =>
    match findCallee? calleeSigs defPath with
    | some sigBody =>
      match findCalleeImpurePtrArgIdx? sigBody with
      | some _ => none
      | none =>
        match decodeFnArgsFromRawBytes sigBody table rawArgs with
        | some args => some (.extCallPanic defPath args)
        | none => none
    | none => none
  | .extCallAbort defPath rawArgs =>
    match findCallee? calleeSigs defPath with
    | some sigBody =>
      match findCalleeImpurePtrArgIdx? sigBody with
      | some _ => none
      | none =>
        match decodeFnArgsFromRawBytes sigBody table rawArgs with
        | some args => some (.extCallAbort defPath args)
        | none => none
    | none => none

/-- Decode a list of `RawObservedEvent`s using `calleeSigs` and `table`. -/
@[reducible]
def decodeRawObservedEvents
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable) :
    List RawObservedEvent → Option (List ObservedEvent)
  | [] => some []
  | ev :: rest =>
    match
      decodeRawObservedEvent calleeSigs table ev,
      decodeRawObservedEvents calleeSigs table rest
    with
    | some dEv, some dRest => some (dEv :: dRest)
    | _, _ => none

/-- Decode a `RawObservedOutcome` using `rootBody` and `table`. -/
@[reducible]
def decodeRawObservedOutcome
    (rootBody : CapturedMir) (table : ShadowProvenanceTable) :
    RawObservedOutcome → Option ObservedOutcome
  | .normal rawRet =>
    match decodeFnRetFromRawBytes rootBody table rawRet with
    | some retVal => some (.normal retVal)
    | none => none
  | .panic => some .panic
  | .abort => some .abort

/--
Decode a complete `RawByteTrace` into a typed `ObservedTrace` using the
compiler-extracted `LayoutTable` and `LocalDecl` metadata in `rootBody` and
`calleeSigs`, populating initial memory for registered pointer allocations via
`populateShadowPointerMemory`.
-/
@[reducible]
def decodeRawByteTrace
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    Option ObservedTrace :=
  match
    decodeFnArgsFromRawBytes rootBody table rawTrace.rawArgs,
    decodeRawObservedEvents calleeSigs table rawTrace.events,
    decodeRawObservedOutcome rootBody table rawTrace.outcome
  with
  | some args, some events, some outcome =>
    match
      populateShadowPointerMemory
        rootBody
        (calleeSigs ++ rawTrace.inlinedCallees)
        table
        rawTrace.rawArgs
        args
        rawTrace.initMem
    with
    | ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
       activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs⟩ =>
      some {
        args := args
        initMem := ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
                    activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs⟩
        inlinedCallees := rawTrace.inlinedCallees
        events := events
        outcome := outcome
      }
  | _, _, _ => none

/--
Computable end-to-end check that a `RawByteTrace` decodes cleanly under
`rootBody`, `calleeSigs`, and `table` and is consistent with `mirStatefulTree`
(`checkBranches = true`).
-/
@[reducible]
def checkRawByteTraceFullBounded
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace =>
    checkObservedTraceConsistencyBounded fuel true rootBody obsTrace
  | none => false

/--
Computable end-to-end check that a `RawByteTrace` decodes cleanly under
`rootBody`, `calleeSigs`, and `table` and is consistent with
`mirObsErasedStatefulTree` (`checkBranches = false`).
-/
@[reducible]
def checkRawByteTraceObsErasedBounded
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace =>
    checkObservedTraceConsistencyBounded fuel false rootBody obsTrace
  | none => false

/--
End-to-end soundness of `checkRawByteTraceFullBounded`: when it returns `true`,
the raw byte slices decode to a typed `obsTrace : ObservedTrace` whose execution
reaches a matching `out` along `tr` in `mirStatefulTree`.
-/
theorem checkRawByteTraceFullBounded_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceFullBounded fuel rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out := by
  unfold checkRawByteTraceFullBounded at h_ok
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    rcases checkFullObservedTraceBounded_sound fuel rootBody
        (initMachineStateWithMemory rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        obsTrace.events obsTrace.outcome h_ok with
      ⟨tr, out, h_evs, h_out, h_reach⟩
    exact ⟨obsTrace, tr, out, rfl, h_evs, h_out, h_reach⟩

/--
End-to-end soundness of `checkRawByteTraceObsErasedBounded`: when it returns
`true`, the raw byte slices decode to a typed `obsTrace : ObservedTrace` whose
execution reaches a matching `out` along a `MirCallE` trace `tr` in
`mirObsErasedStatefulTree`.
-/
theorem checkRawByteTraceObsErasedBounded_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceObsErasedBounded fuel rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out := by
  unfold checkRawByteTraceObsErasedBounded at h_ok
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    rcases checkObsErasedObservedTraceBounded_sound fuel rootBody obsTrace.args
        { obsTrace.initMem with callees := obsTrace.inlinedCallees }
        obsTrace.events obsTrace.outcome h_ok with
      ⟨tr, out, h_evs, h_out, h_reach⟩
    exact ⟨obsTrace, tr, out, rfl, h_evs, h_out, h_reach⟩

/-! ## 7. Differential-Testing Triage Diagnostic Replay (`TraceReplayDiag`) -/

/--
Computable diagnostic classification returned by `diagnoseObservedTraceBounded`
and `diagnoseRawByteTraceBounded` for differential testing and counterexample
triage.
-/
inductive TraceReplayDiag where
  | ok (tr : List (Event MirEffect)) (out : MirOutcome)
  | decodeArgFailed (argIdx : Nat)
  | decodeEventFailed (evIdx : Nat)
  | decodeOutcomeFailed
  | impureExtCallPtrArg (defPath : DefPath) (evIdx : Nat) (argIdx : Nat)
  | stepFaulted (kind : FailureKind) (blockIdx stmtIdx : Nat)
  | unexpectedExtCall (defPath : DefPath) (blockIdx : Nat)
  | callArgMismatch (defPath : DefPath) (blockIdx : Nat)
  | branchTagMismatch (actualTag expectedTag : Nat) (blockIdx : Nat)
  | unconsumedEventsRemaining (remainingCount : Nat)
  | outcomeMismatch (actualOut : MirOutcome) (expectedOut : ObservedOutcome)
  | outOfFuel (lastBlockIdx lastStmtIdx : Nat)
  deriving Repr, DecidableEq

/-- Returns `true` iff `diag` is `TraceReplayDiag.ok _ _`. -/
@[reducible]
def TraceReplayDiag.isOk : TraceReplayDiag → Bool
  | .ok _ _ => true
  | _ => false

/--
Concise, stable machine-readable tag name for differential-testing triage
reports.
-/
@[reducible]
def TraceReplayDiag.tagName : TraceReplayDiag → String
  | .ok _ _ => "ok"
  | .decodeArgFailed _ => "decode_arg_failed"
  | .decodeEventFailed _ => "decode_event_failed"
  | .decodeOutcomeFailed => "decode_outcome_failed"
  | .impureExtCallPtrArg _ _ _ => "impure_ext_call_ptr_arg"
  | .stepFaulted _ _ _ => "step_faulted"
  | .unexpectedExtCall _ _ => "unexpected_ext_call"
  | .callArgMismatch _ _ => "call_arg_mismatch"
  | .branchTagMismatch _ _ _ => "branch_tag_mismatch"
  | .unconsumedEventsRemaining _ => "unconsumed_events"
  | .outcomeMismatch _ _ => "outcome_mismatch"
  | .outOfFuel _ _ => "out_of_fuel"

/--
Classify an external `MirCallReq` against the next `ObservedEvent`, distinguishing
callee `DefPath` mismatches (`.unexpectedExtCall`) from argument mismatches
(`.callArgMismatch`).
-/
@[reducible]
def diagnoseCallObservedEvent
    (req : MirCallReq) (blockIdx : Nat) (obsEv : ObservedEvent) :
    Except TraceReplayDiag MirCallAns :=
  match obsEv with
  | .branch _ =>
    .error (.unexpectedExtCall req.defPath blockIdx)
  | .extCall defPath args retVal =>
    if stringEq req.defPath defPath then
      if valueListEqFuel 16 req.args args then
        .ok (.returned retVal req.memory)
      else
        .error (.callArgMismatch req.defPath blockIdx)
    else
      .error (.unexpectedExtCall req.defPath blockIdx)
  | .extCallPanic defPath args =>
    if stringEq req.defPath defPath then
      if valueListEqFuel 16 req.args args then
        .ok (.panicked req.memory)
      else
        .error (.callArgMismatch req.defPath blockIdx)
    else
      .error (.unexpectedExtCall req.defPath blockIdx)
  | .extCallAbort defPath args =>
    if stringEq req.defPath defPath then
      if valueListEqFuel 16 req.args args then
        .ok .aborted
      else
        .error (.callArgMismatch req.defPath blockIdx)
    else
      .error (.unexpectedExtCall req.defPath blockIdx)

/--
Fuel-bounded diagnostic replay over `stepMirState body` parameterized by
`checkBranches : Bool`. Returns `.ok tr out` on exact replay or the first
structural/semantic divergence (`TraceReplayDiag`).
-/
@[reducible]
def diagnoseMirExecBounded
    (fuel : Nat) (checkBranches : Bool) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    TraceReplayDiag :=
  match fuel with
  | 0 =>
    let cur := execStateCursor st
    .outOfFuel cur.1 cur.2
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret actualOut =>
      match events with
      | [] =>
        if checkOutcomeMatches outcome actualOut then
          .ok [] actualOut
        else
          .outcomeMismatch actualOut outcome
      | _ :: _ =>
        .unconsumedEventsRemaining events.length
    | .tau st' =>
      diagnoseMirExecBounded fuel' checkBranches body st' events outcome
    | .vis (.inl (.fail kind)) _ =>
      let cur := execStateCursor st
      .stepFaulted kind cur.1 cur.2
    | .vis (.inr (.inl (.emit obs))) k =>
      match checkBranches with
      | false =>
        diagnoseMirExecBounded fuel' false body (k PUnit.unit) events outcome
      | true =>
        let cur := execStateCursor st
        match obs with
        | .silent =>
          .stepFaulted .unsupported cur.1 cur.2
        | .event actualTag =>
          match events with
          | .branch expectedTag :: rest =>
            if Nat.beq actualTag expectedTag then
              match diagnoseMirExecBounded fuel' true body (k PUnit.unit) rest outcome with
              | .ok trRest out =>
                .ok (⟨.inr (.inl (.emit (.event actualTag))), PUnit.unit⟩ :: trRest) out
              | diag => diag
            else
              .branchTagMismatch actualTag expectedTag cur.1
          | _ =>
            .branchTagMismatch actualTag 0 cur.1
    | .vis (.inr (.inr (.call req))) k =>
      let blockIdx := (execStateCursor st).1
      let activeBody := execStateActiveBody body st
      match findActiveCallImpurePtrArgIdx? activeBody blockIdx req with
      | some argIdx =>
        .impureExtCallPtrArg req.defPath 0 argIdx
      | none =>
        match events with
        | [] =>
          .unexpectedExtCall req.defPath blockIdx
        | obsEv :: rest =>
          match diagnoseCallObservedEvent req blockIdx obsEv with
          | .error diag => diag
          | .ok ans =>
            match diagnoseMirExecBounded fuel' checkBranches body (k ans) rest outcome with
            | .ok trRest out =>
              .ok (⟨.inr (.inr (.call req)), ans⟩ :: trRest) out
            | diag => diag

/--
Diagnose a decoded `ObservedTrace` against `body` with fuel bound `fuel` and
branch-observation mode `checkBranches : Bool`.
-/
@[reducible]
def diagnoseObservedTraceBounded
    (fuel : Nat) (checkBranches : Bool) (body : CapturedMir)
    (trace : ObservedTrace) : TraceReplayDiag :=
  let mem := { trace.initMem with callees := trace.inlinedCallees }
  let s := initMachineStateWithMemory body trace.args mem
  diagnoseMirExecBounded fuel checkBranches body (.running s) trace.events trace.outcome

/--
Decode `rawArgs` slot-by-slot while tracking the 0-based argument index `argIdx`
to report `.decodeArgFailed argIdx` on the first failing argument.
-/
@[reducible]
def diagnoseDecodeRawArgsAux
    (layouts : LayoutTable) (table : ShadowProvenanceTable)
    (argIdx : Nat) (decls : List LocalDecl) :
    List (List UInt8) → Except Nat (List Value)
  | [] => .ok []
  | raw :: rawRest =>
    match decls with
    | [] => .error argIdx
    | decl :: declRest =>
      match decodeRawValue layouts table decl.ty raw with
      | none => .error argIdx
      | some v =>
        match diagnoseDecodeRawArgsAux layouts table (argIdx + 1) declRest rawRest with
        | .ok vs => .ok (v :: vs)
        | .error failedIdx => .error failedIdx

/--
Decode root argument byte slices `rawArgs` against `body`, reporting the exact
failing 0-based argument index on mismatch.
-/
@[reducible]
def diagnoseDecodeFnArgs
    (body : CapturedMir) (table : ShadowProvenanceTable)
    (rawArgs : List (List UInt8)) : Except Nat (List Value) :=
  if Nat.beq (length rawArgs) body.argCount then
    diagnoseDecodeRawArgsAux body.layouts table 0 (body.localDecls.drop 1) rawArgs
  else
    .error (length rawArgs)

/--
Diagnose and decode a single `RawObservedEvent` at index `evIdx`, flagging
external calls that take `&mut` or raw-pointer arguments with
`.impureExtCallPtrArg defPath evIdx argIdx` and reporting `.decodeEventFailed evIdx`
on malformed argument/return bytes or missing callee signatures.
-/
@[reducible]
def diagnoseDecodeRawEvent
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (evIdx : Nat) : RawObservedEvent → Except TraceReplayDiag ObservedEvent
  | .branch tag => .ok (.branch tag)
  | .extCall defPath rawArgs rawRet =>
    match findCallee? calleeSigs defPath with
    | some sigBody =>
      match findCalleeImpurePtrArgIdx? sigBody with
      | some argIdx => .error (.impureExtCallPtrArg defPath evIdx argIdx)
      | none =>
        match
          decodeFnArgsFromRawBytes sigBody table rawArgs,
          decodeFnRetFromRawBytes sigBody table rawRet
        with
        | some args, some retVal => .ok (.extCall defPath args retVal)
        | _, _ => .error (.decodeEventFailed evIdx)
    | none => .error (.decodeEventFailed evIdx)
  | .extCallPanic defPath rawArgs =>
    match findCallee? calleeSigs defPath with
    | some sigBody =>
      match findCalleeImpurePtrArgIdx? sigBody with
      | some argIdx => .error (.impureExtCallPtrArg defPath evIdx argIdx)
      | none =>
        match decodeFnArgsFromRawBytes sigBody table rawArgs with
        | some args => .ok (.extCallPanic defPath args)
        | none => .error (.decodeEventFailed evIdx)
    | none => .error (.decodeEventFailed evIdx)
  | .extCallAbort defPath rawArgs =>
    match findCallee? calleeSigs defPath with
    | some sigBody =>
      match findCalleeImpurePtrArgIdx? sigBody with
      | some argIdx => .error (.impureExtCallPtrArg defPath evIdx argIdx)
      | none =>
        match decodeFnArgsFromRawBytes sigBody table rawArgs with
        | some args => .ok (.extCallAbort defPath args)
        | none => .error (.decodeEventFailed evIdx)
    | none => .error (.decodeEventFailed evIdx)

/--
Decode `rawEvents` item-by-item while tracking the 0-based event index `evIdx`
to report `.impureExtCallPtrArg` or `.decodeEventFailed evIdx` on the first
failing event.
-/
@[reducible]
def diagnoseDecodeRawEventsAux
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable) :
    Nat → List RawObservedEvent → Except TraceReplayDiag (List ObservedEvent)
  | _, [] => .ok []
  | evIdx, ev :: rest =>
    match diagnoseDecodeRawEvent calleeSigs table evIdx ev with
    | .error diag => .error diag
    | .ok dEv =>
      match diagnoseDecodeRawEventsAux calleeSigs table (evIdx + 1) rest with
      | .ok dRest => .ok (dEv :: dRest)
      | .error diag => .error diag

/--
End-to-end diagnostic replay of a `RawByteTrace`: first pinpoints any
`decodeArgFailed`, `impureExtCallPtrArg`, `decodeEventFailed`, or
`decodeOutcomeFailed` error with its exact 0-based index, populates initial
memory for registered pointer allocations via `populateShadowPointerMemory`, and
executes `diagnoseObservedTraceBounded`.
-/
@[reducible]
def diagnoseRawByteTraceBounded
    (fuel : Nat) (checkBranches : Bool) (rootBody : CapturedMir)
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (rawTrace : RawByteTrace) : TraceReplayDiag :=
  match diagnoseDecodeFnArgs rootBody table rawTrace.rawArgs with
  | .error argIdx => .decodeArgFailed argIdx
  | .ok args =>
    match diagnoseDecodeRawEventsAux calleeSigs table 0 rawTrace.events with
    | .error diag => diag
    | .ok events =>
      match decodeRawObservedOutcome rootBody table rawTrace.outcome with
      | none => .decodeOutcomeFailed
      | some outcome =>
        match
          populateShadowPointerMemory
            rootBody
            (calleeSigs ++ rawTrace.inlinedCallees)
            table
            rawTrace.rawArgs
            args
            rawTrace.initMem
        with
        | ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
           activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs⟩ =>
          diagnoseObservedTraceBounded fuel checkBranches rootBody {
            args := args
            initMem := ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
                        activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs⟩
            inlinedCallees := rawTrace.inlinedCallees
            events := events
            outcome := outcome
          }

/--
Convenience wrapper for `diagnoseRawByteTraceBounded` with full branch and call
checking (`checkBranches = true`).
-/
@[reducible]
def diagnoseRawByteTraceFullBounded
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceBounded fuel true rootBody calleeSigs table rawTrace

/--
Convenience wrapper for `diagnoseRawByteTraceBounded` with branch-erased
call-boundary checking (`checkBranches = false`).
-/
@[reducible]
def diagnoseRawByteTraceObsErasedBounded
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceBounded fuel false rootBody calleeSigs table rawTrace

end Anneal.Rustc.V2026_06_01.TraceCheck
