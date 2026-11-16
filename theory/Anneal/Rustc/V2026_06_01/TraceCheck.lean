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
in a worklist contains a pointer whose borrow in `borrows` is not `.frozen` (a
mutable reservation, an activated `.unique` borrow, an interior-mutable `.cell`
borrow, or a `.disabled` tag) or untracked (`none`, such as a raw pointer).
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
              | .cell | .reservedFrz _ | .reservedIM | .unique | .disabled =>
                true
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
pointer whose borrow in `borrows` is not `.frozen` or untracked (`none`, such as
a raw pointer); see `valueListHasImpureExtCallPtr`.
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
Allocation-free tail-recursive full trace replay (`checkBranches = true`)
over `stepMirState body`, returning `some out` when `events` and `outcome`
match without allocating intermediate `Event MirEffect` trace lists.
-/
@[reducible]
def reconstructFullMirTraceFast
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    Option MirOutcome :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret out =>
      match events with
      | [] =>
        if checkOutcomeMatches outcome out then
          some out
        else
          none
      | _ :: _ => none
    | .tau st' =>
      reconstructFullMirTraceFast fuel' body st' events outcome
    | .vis (.inl _) _ => none
    | .vis (.inr (.inl (.emit .silent))) _ => none
    | .vis (.inr (.inl (.emit (.event tag)))) k =>
      match events with
      | .branch expectedTag :: rest =>
        if Nat.beq tag expectedTag then
          reconstructFullMirTraceFast fuel' body (k PUnit.unit) rest outcome
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
            reconstructFullMirTraceFast fuel' body (k ans) rest outcome
          | none => none
        | [] => none

/--
Allocation-free tail-recursive boolean checker for full (`MirObsE` + `MirCallE`)
trace consistency (`checkBranches = true`), equal to
`(reconstructFullMirTrace ...).isSome` (`checkFullMirTraceFast_eq`). Because
kernel and elaborator reduction are lazy, this tail-recursive form has the same
measured kernel cost as `reconstructFullMirTrace`; it is provided as a
structurally simpler alternative implementation, not as an accelerator.
-/
@[reducible]
def checkFullMirTraceFast
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret out =>
      match events with
      | [] => checkOutcomeMatches outcome out
      | _ :: _ => false
    | .tau st' =>
      checkFullMirTraceFast fuel' body st' events outcome
    | .vis (.inl _) _ => false
    | .vis (.inr (.inl (.emit .silent))) _ => false
    | .vis (.inr (.inl (.emit (.event tag)))) k =>
      match events with
      | .branch expectedTag :: rest =>
        if Nat.beq tag expectedTag then
          checkFullMirTraceFast fuel' body (k PUnit.unit) rest outcome
        else
          false
      | _ => false
    | .vis (.inr (.inr (.call req))) k =>
      match
        findActiveCallImpurePtrArgIdx?
          (execStateActiveBody body st) (execStateCursor st).1 req
      with
      | some _ => false
      | none =>
        match events with
        | obsEv :: rest =>
          match matchCallObservedEvent req obsEv with
          | some ans =>
            checkFullMirTraceFast fuel' body (k ans) rest outcome
          | none => false
        | [] => false

/--
`reconstructFullMirTraceFast` computes the exact terminal `MirOutcome` projection
of `reconstructFullMirTrace` without allocating intermediate `Event MirEffect`
lists.
-/
theorem reconstructFullMirTraceFast_eq
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    reconstructFullMirTraceFast fuel body st events outcome =
      (reconstructFullMirTrace fuel body st events outcome).map Prod.snd := by
  induction fuel generalizing st events with
  | zero => rfl
  | succ fuel' ih =>
    unfold reconstructFullMirTraceFast reconstructFullMirTrace
    cases stepMirState body st with
    | ret out₀ =>
      cases events with
      | nil =>
        change (if checkOutcomeMatches outcome out₀ then some out₀ else none) =
          (if checkOutcomeMatches outcome out₀ then some (([] : List (Event MirEffect)), out₀) else none).map Prod.snd
        cases checkOutcomeMatches outcome out₀ <;> rfl
      | cons _ _ => rfl
    | tau st' => exact ih st' events
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · rfl
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent => rfl
          | event tag =>
            cases events with
            | nil => rfl
            | cons ev rest =>
              cases ev with
              | branch expectedTag =>
                change
                  (if Nat.beq tag expectedTag then
                    reconstructFullMirTraceFast fuel' body (k PUnit.unit) rest outcome
                  else none) =
                  (if Nat.beq tag expectedTag then
                    match reconstructFullMirTrace fuel' body (k PUnit.unit) rest outcome with
                    | some (trRest, out) =>
                      some ((⟨.inr (.inl (.emit (.event tag))), PUnit.unit⟩ : Event MirEffect) :: trRest, out)
                    | none => none
                  else none).map Prod.snd
                cases Nat.beq tag expectedTag with
                | false => rfl
                | true =>
                  have ih' := ih (k PUnit.unit) rest
                  cases h_rec : reconstructFullMirTrace fuel' body (k PUnit.unit) rest outcome <;>
                    (rw [h_rec] at ih'; exact ih')
              | _ => rfl
      · cases callReq with
        | call req =>
          cases events with
          | nil =>
            change
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => none
               | none => none) =
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => none
               | none => (none : Option (List (Event MirEffect) × MirOutcome))).map Prod.snd
            cases findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req <;> rfl
          | cons obsEv rest =>
            change
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => none
               | none =>
                 match matchCallObservedEvent req obsEv with
                 | some ans => reconstructFullMirTraceFast fuel' body (k ans) rest outcome
                 | none => none) =
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => none
               | none =>
                 match matchCallObservedEvent req obsEv with
                 | some ans =>
                   match reconstructFullMirTrace fuel' body (k ans) rest outcome with
                   | some (trRest, out) =>
                     some ((⟨.inr (.inr (.call req)), ans⟩ : Event MirEffect) :: trRest, out)
                   | none => none
                 | none => none).map Prod.snd
            cases findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
            | some _ => rfl
            | none =>
              cases matchCallObservedEvent req obsEv with
              | none => rfl
              | some ans =>
                change reconstructFullMirTraceFast fuel' body (k ans) rest outcome =
                  (match reconstructFullMirTrace fuel' body (k ans) rest outcome with
                   | some (trRest, out) =>
                     some ((⟨.inr (.inr (.call req)), ans⟩ : Event MirEffect) :: trRest, out)
                   | none => none).map Prod.snd
                have ih' := ih (k ans) rest
                cases h_rec : reconstructFullMirTrace fuel' body (k ans) rest outcome <;>
                  (rw [h_rec] at ih'; exact ih')

/--
`checkFullMirTraceFast` agrees with `(reconstructFullMirTrace ...).isSome`.
-/
theorem checkFullMirTraceFast_eq
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    checkFullMirTraceFast fuel body st events outcome =
      (reconstructFullMirTrace fuel body st events outcome).isSome := by
  induction fuel generalizing st events with
  | zero => rfl
  | succ fuel' ih =>
    unfold checkFullMirTraceFast reconstructFullMirTrace
    cases stepMirState body st with
    | ret out₀ =>
      cases events with
      | nil =>
        change checkOutcomeMatches outcome out₀ =
          (if checkOutcomeMatches outcome out₀ then some (([] : List (Event MirEffect)), out₀) else none).isSome
        cases checkOutcomeMatches outcome out₀ <;> rfl
      | cons _ _ => rfl
    | tau st' => exact ih st' events
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · rfl
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent => rfl
          | event tag =>
            cases events with
            | nil => rfl
            | cons ev rest =>
              cases ev with
              | branch expectedTag =>
                change
                  (if Nat.beq tag expectedTag then
                    checkFullMirTraceFast fuel' body (k PUnit.unit) rest outcome
                  else false) =
                  (if Nat.beq tag expectedTag then
                    match reconstructFullMirTrace fuel' body (k PUnit.unit) rest outcome with
                    | some (trRest, out) =>
                      some ((⟨.inr (.inl (.emit (.event tag))), PUnit.unit⟩ : Event MirEffect) :: trRest, out)
                    | none => none
                  else none).isSome
                cases Nat.beq tag expectedTag with
                | false => rfl
                | true =>
                  have ih' := ih (k PUnit.unit) rest
                  cases h_rec : reconstructFullMirTrace fuel' body (k PUnit.unit) rest outcome <;>
                    (rw [h_rec] at ih'; exact ih')
              | _ => rfl
      · cases callReq with
        | call req =>
          cases events with
          | nil =>
            change
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => false
               | none => false) =
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => none
               | none => (none : Option (List (Event MirEffect) × MirOutcome))).isSome
            cases findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req <;> rfl
          | cons obsEv rest =>
            change
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => false
               | none =>
                 match matchCallObservedEvent req obsEv with
                 | some ans => checkFullMirTraceFast fuel' body (k ans) rest outcome
                 | none => false) =
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => none
               | none =>
                 match matchCallObservedEvent req obsEv with
                 | some ans =>
                   match reconstructFullMirTrace fuel' body (k ans) rest outcome with
                   | some (trRest, out) =>
                     some ((⟨.inr (.inr (.call req)), ans⟩ : Event MirEffect) :: trRest, out)
                   | none => none
                 | none => none).isSome
            cases findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
            | some _ => rfl
            | none =>
              cases matchCallObservedEvent req obsEv with
              | none => rfl
              | some ans =>
                change checkFullMirTraceFast fuel' body (k ans) rest outcome =
                  (match reconstructFullMirTrace fuel' body (k ans) rest outcome with
                   | some (trRest, out) =>
                     some ((⟨.inr (.inr (.call req)), ans⟩ : Event MirEffect) :: trRest, out)
                   | none => none).isSome
                have ih' := ih (k ans) rest
                cases h_rec : reconstructFullMirTrace fuel' body (k ans) rest outcome <;>
                  (rw [h_rec] at ih'; exact ih')

/--
Computable boolean checker for full (`MirObsE` + `MirCallE`) trace consistency
(`checkBranches = true`).

The definition is intentionally kept as `(reconstructFullMirTrace ...).isSome`
(equal to the tail-recursive `checkFullMirTraceFast` by `checkFullMirTraceFast_eq`):
Lean's kernel and elaborator reduce lazily to weak-head normal form, so the
discarded `Event MirEffect` list is never materialized. Measured on
`mirLoopWithOracleCall` at `k = 32` (`tests/mir/ITreeApproxRunnerTests.lean`), the
`checkRawByteTraceFullBounded_sound ... rfl` application that `cargo-anneal` emits
costs `13101` heartbeat units via `reconstructFullMirTrace` versus `13667` via
`checkFullMirTraceFast` (kernel-only `decide +kernel`: `4461` versus `4449`).
-/
@[reducible]
def checkFullObservedTraceBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) : Bool :=
  (reconstructFullMirTrace fuel body (.running s) events outcome).isSome

/-- `checkFullObservedTraceBounded` agrees with the tail-recursive
`checkFullMirTraceFast`. -/
theorem checkFullObservedTraceBounded_eq_fast
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    checkFullObservedTraceBounded fuel body s events outcome =
      checkFullMirTraceFast fuel body (.running s) events outcome :=
  (checkFullMirTraceFast_eq fuel body (.running s) events outcome).symm

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
Soundness of `reconstructFullMirTraceFast`: when it returns `some out`, there
exists a concrete trace `tr` matching `events` along which `ITree.cofix (stepMirState body) st`
reaches `out` matching `outcome`.
-/
theorem reconstructFullMirTraceFast_sound
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (out : MirOutcome)
    (h_ok : reconstructFullMirTraceFast fuel body st events outcome = some out) :
    ∃ tr,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (ITree.cofix (stepMirState body) st) tr out := by
  rw [reconstructFullMirTraceFast_eq] at h_ok
  cases h_rec : reconstructFullMirTrace fuel body st events outcome with
  | none => rw [h_rec] at h_ok; nomatch h_ok
  | some pair =>
    rw [h_rec] at h_ok
    injection h_ok with h_out
    subst h_out
    exact ⟨pair.1,
      reconstructFullMirTrace_sound fuel body st events outcome pair.1 pair.2 h_rec⟩

/--
Soundness of `checkFullMirTraceFast`: when it returns `true`, there exist `tr`
and `out` matching `events` and `outcome` reached by `ITree.cofix (stepMirState body) st`.
-/
theorem checkFullMirTraceFast_sound
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok : checkFullMirTraceFast fuel body st events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (ITree.cofix (stepMirState body) st) tr out := by
  rw [checkFullMirTraceFast_eq] at h_ok
  cases h_rec : reconstructFullMirTrace fuel body st events outcome with
  | none => rw [h_rec] at h_ok; nomatch h_ok
  | some pair =>
    exact ⟨pair.1, pair.2,
      reconstructFullMirTrace_sound fuel body st events outcome pair.1 pair.2 h_rec⟩

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
Allocation-free tail-recursive branch-erased trace replay (`checkBranches = false`)
over `stepMirState body`, returning `some out` when call-boundary `events` and
`outcome` match without allocating intermediate `Event MirEffect` trace lists.
-/
@[reducible]
def reconstructObsErasedMirTraceFast
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    Option MirOutcome :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret out =>
      match events with
      | [] =>
        if checkOutcomeMatches outcome out then
          some out
        else
          none
      | _ :: _ => none
    | .tau st' =>
      reconstructObsErasedMirTraceFast fuel' body st' events outcome
    | .vis (.inl _) _ => none
    | .vis (.inr (.inl _)) k =>
      reconstructObsErasedMirTraceFast fuel' body (k PUnit.unit) events outcome
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
            reconstructObsErasedMirTraceFast fuel' body (k ans) rest outcome
          | none => none
        | [] => none

/--
Allocation-free tail-recursive boolean checker for branch-erased (`MirCallE`-only)
trace consistency (`checkBranches = false`), equal to
`(reconstructObsErasedMirTrace ...).isSome` (`checkObsErasedMirTraceFast_eq`),
with the same measured kernel cost (lazy reduction never materializes the
discarded trace list).
-/
@[reducible]
def checkObsErasedMirTraceFast
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret out =>
      match events with
      | [] => checkOutcomeMatches outcome out
      | _ :: _ => false
    | .tau st' =>
      checkObsErasedMirTraceFast fuel' body st' events outcome
    | .vis (.inl _) _ => false
    | .vis (.inr (.inl _)) k =>
      checkObsErasedMirTraceFast fuel' body (k PUnit.unit) events outcome
    | .vis (.inr (.inr (.call req))) k =>
      match
        findActiveCallImpurePtrArgIdx?
          (execStateActiveBody body st) (execStateCursor st).1 req
      with
      | some _ => false
      | none =>
        match events with
        | obsEv :: rest =>
          match matchCallObservedEvent req obsEv with
          | some ans =>
            checkObsErasedMirTraceFast fuel' body (k ans) rest outcome
          | none => false
        | [] => false

/--
`reconstructObsErasedMirTraceFast` computes the exact terminal `MirOutcome`
projection of `reconstructObsErasedMirTrace` without allocating intermediate
`Event MirEffect` lists.
-/
theorem reconstructObsErasedMirTraceFast_eq
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    reconstructObsErasedMirTraceFast fuel body st events outcome =
      (reconstructObsErasedMirTrace fuel body st events outcome).map Prod.snd := by
  induction fuel generalizing st events with
  | zero => rfl
  | succ fuel' ih =>
    unfold reconstructObsErasedMirTraceFast reconstructObsErasedMirTrace
    cases stepMirState body st with
    | ret out₀ =>
      cases events with
      | nil =>
        change (if checkOutcomeMatches outcome out₀ then some out₀ else none) =
          (if checkOutcomeMatches outcome out₀ then some (([] : List (Event MirEffect)), out₀) else none).map Prod.snd
        cases checkOutcomeMatches outcome out₀ <;> rfl
      | cons _ _ => rfl
    | tau st' => exact ih st' events
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · rfl
      · exact ih (k PUnit.unit) events
      · cases callReq with
        | call req =>
          cases events with
          | nil =>
            change
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => none
               | none => none) =
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => none
               | none => (none : Option (List (Event MirEffect) × MirOutcome))).map Prod.snd
            cases findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req <;> rfl
          | cons obsEv rest =>
            change
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => none
               | none =>
                 match matchCallObservedEvent req obsEv with
                 | some ans => reconstructObsErasedMirTraceFast fuel' body (k ans) rest outcome
                 | none => none) =
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => none
               | none =>
                 match matchCallObservedEvent req obsEv with
                 | some ans =>
                   match reconstructObsErasedMirTrace fuel' body (k ans) rest outcome with
                   | some (trRest, out) =>
                     some ((⟨.inr (.inr (.call req)), ans⟩ : Event MirEffect) :: trRest, out)
                   | none => none
                 | none => none).map Prod.snd
            cases findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
            | some _ => rfl
            | none =>
              cases matchCallObservedEvent req obsEv with
              | none => rfl
              | some ans =>
                change reconstructObsErasedMirTraceFast fuel' body (k ans) rest outcome =
                  (match reconstructObsErasedMirTrace fuel' body (k ans) rest outcome with
                   | some (trRest, out) =>
                     some ((⟨.inr (.inr (.call req)), ans⟩ : Event MirEffect) :: trRest, out)
                   | none => none).map Prod.snd
                have ih' := ih (k ans) rest
                cases h_rec : reconstructObsErasedMirTrace fuel' body (k ans) rest outcome <;>
                  (rw [h_rec] at ih'; exact ih')

/--
`checkObsErasedMirTraceFast` agrees with `(reconstructObsErasedMirTrace ...).isSome`.
-/
theorem checkObsErasedMirTraceFast_eq
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    checkObsErasedMirTraceFast fuel body st events outcome =
      (reconstructObsErasedMirTrace fuel body st events outcome).isSome := by
  induction fuel generalizing st events with
  | zero => rfl
  | succ fuel' ih =>
    unfold checkObsErasedMirTraceFast reconstructObsErasedMirTrace
    cases stepMirState body st with
    | ret out₀ =>
      cases events with
      | nil =>
        change checkOutcomeMatches outcome out₀ =
          (if checkOutcomeMatches outcome out₀ then some (([] : List (Event MirEffect)), out₀) else none).isSome
        cases checkOutcomeMatches outcome out₀ <;> rfl
      | cons _ _ => rfl
    | tau st' => exact ih st' events
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · rfl
      · exact ih (k PUnit.unit) events
      · cases callReq with
        | call req =>
          cases events with
          | nil =>
            change
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => false
               | none => false) =
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => none
               | none => (none : Option (List (Event MirEffect) × MirOutcome))).isSome
            cases findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req <;> rfl
          | cons obsEv rest =>
            change
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => false
               | none =>
                 match matchCallObservedEvent req obsEv with
                 | some ans => checkObsErasedMirTraceFast fuel' body (k ans) rest outcome
                 | none => false) =
              (match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
               | some _ => none
               | none =>
                 match matchCallObservedEvent req obsEv with
                 | some ans =>
                   match reconstructObsErasedMirTrace fuel' body (k ans) rest outcome with
                   | some (trRest, out) =>
                     some ((⟨.inr (.inr (.call req)), ans⟩ : Event MirEffect) :: trRest, out)
                   | none => none
                 | none => none).isSome
            cases findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
            | some _ => rfl
            | none =>
              cases matchCallObservedEvent req obsEv with
              | none => rfl
              | some ans =>
                change checkObsErasedMirTraceFast fuel' body (k ans) rest outcome =
                  (match reconstructObsErasedMirTrace fuel' body (k ans) rest outcome with
                   | some (trRest, out) =>
                     some ((⟨.inr (.inr (.call req)), ans⟩ : Event MirEffect) :: trRest, out)
                   | none => none).isSome
                have ih' := ih (k ans) rest
                cases h_rec : reconstructObsErasedMirTrace fuel' body (k ans) rest outcome <;>
                  (rw [h_rec] at ih'; exact ih')

/--
Computable boolean checker for branch-erased (`MirCallE`-only) trace consistency
(`checkBranches = false`).

Kept as `(reconstructObsErasedMirTrace ...).isSome` (equal to the tail-recursive
`checkObsErasedMirTraceFast` by `checkObsErasedMirTraceFast_eq`); lazy weak-head
reduction never materializes the discarded trace list, and the generated
`checkRawByteTraceObsErasedBounded_sound ... rfl` application at `k = 32` costs
`12932` heartbeat units versus `13409` via `checkObsErasedMirTraceFast`
(kernel-only: `4420` versus `4413`).
-/
@[reducible]
def checkObsErasedObservedTraceBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) : Bool :=
  (reconstructObsErasedMirTrace fuel body (.running s) events outcome).isSome

/-- `checkObsErasedObservedTraceBounded` agrees with the tail-recursive
`checkObsErasedMirTraceFast`. -/
theorem checkObsErasedObservedTraceBounded_eq_fast
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    checkObsErasedObservedTraceBounded fuel body s events outcome =
      checkObsErasedMirTraceFast fuel body (.running s) events outcome :=
  (checkObsErasedMirTraceFast_eq fuel body (.running s) events outcome).symm

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
Soundness of `reconstructObsErasedMirTraceFast`: when it returns `some out`,
there exists a `MirCallE` trace `tr` matching `events` along which
`ITree.interp silenceMirObs (ITree.cofix (stepMirState body) st)` reaches `out`
matching `outcome`.
-/
theorem reconstructObsErasedMirTraceFast_sound
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (out : MirOutcome)
    (h_ok : reconstructObsErasedMirTraceFast fuel body st events outcome = some out) :
    ∃ tr,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (ITree.interp silenceMirObs (ITree.cofix (stepMirState body) st)) tr out := by
  rw [reconstructObsErasedMirTraceFast_eq] at h_ok
  cases h_rec : reconstructObsErasedMirTrace fuel body st events outcome with
  | none => rw [h_rec] at h_ok; nomatch h_ok
  | some pair =>
    rw [h_rec] at h_ok
    injection h_ok with h_out
    subst h_out
    exact ⟨pair.1,
      reconstructObsErasedMirTrace_sound fuel body st events outcome pair.1 pair.2 h_rec⟩

/--
Soundness of `checkObsErasedMirTraceFast`: when it returns `true`, there exist
`tr` and `out` matching `events` and `outcome` reached by
`ITree.interp silenceMirObs (ITree.cofix (stepMirState body) st)`.
-/
theorem checkObsErasedMirTraceFast_sound
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok : checkObsErasedMirTraceFast fuel body st events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (ITree.interp silenceMirObs (ITree.cofix (stepMirState body) st)) tr out := by
  rw [checkObsErasedMirTraceFast_eq] at h_ok
  cases h_rec : reconstructObsErasedMirTrace fuel body st events outcome with
  | none => rw [h_rec] at h_ok; nomatch h_ok
  | some pair =>
    exact ⟨pair.1, pair.2,
      reconstructObsErasedMirTrace_sound fuel body st events outcome pair.1 pair.2 h_rec⟩

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
Soundness of `checkObsErasedObservedTraceBounded` with `callees`: if
`checkObsErasedObservedTraceBounded` returns `true` from
`initMachineStateWithMemoryAndCallees body args mem callees`, then
`mirObsErasedStatefulTreeWithCallees body args mem callees` reaches a terminal
outcome `out` matching `outcome` along a `MirCallE` trace `tr` matching `events`.
-/
theorem checkObsErasedObservedTraceWithCalleesBounded_sound
    (fuel : Nat) (body : CapturedMir) (args : List Value) (mem : Memory)
    (callees : List CapturedMir)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok :
      checkObsErasedObservedTraceBounded fuel body
        (initMachineStateWithMemoryAndCallees body args mem callees)
        events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTreeWithCallees body args mem callees) tr out := by
  unfold checkObsErasedObservedTraceBounded at h_ok
  cases h_rec :
      reconstructObsErasedMirTrace fuel body
        (.running (initMachineStateWithMemoryAndCallees body args mem callees))
        events outcome with
  | none => rw [h_rec] at h_ok; nomatch h_ok
  | some pair =>
    exact ⟨pair.1, pair.2,
      reconstructObsErasedMirTrace_sound fuel body
        (.running (initMachineStateWithMemoryAndCallees body args mem callees))
        events outcome pair.1 pair.2 h_rec⟩

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

/--
Unified trace-consistency dispatcher initializing `MachineState` via
`initMachineStateWithMemoryAndCallees body trace.args trace.initMem trace.inlinedCallees`
so that both `trace.inlinedCallees` and `body.traitImpls` are populated when
`trace.inlinedCallees` is non-empty.
-/
@[reducible]
def checkObservedTraceWithCalleesBounded
    (fuel : Nat) (checkBranches : Bool) (body : CapturedMir)
    (trace : ObservedTrace) : Bool :=
  let s := initMachineStateWithMemoryAndCallees body trace.args trace.initMem trace.inlinedCallees
  match checkBranches with
  | true => checkFullObservedTraceBounded fuel body s trace.events trace.outcome
  | false => checkObsErasedObservedTraceBounded fuel body s trace.events trace.outcome

/-! ### Suffix-Free `CofixA` Approximants & Walkers for `mirStatefulTree` and `mirObsErasedStatefulTree` -/

/-- Direct `CofixA` approximant of `ITree.cofix (stepMirState body) st` at depth `n`. -/
@[reducible]
def mirExecApprox (body : CapturedMir) (n : Nat) (st : MirExecState) :
    CofixA MirEffect MirOutcome n :=
  approxCofix (stepMirState body) n st

/-- Direct `CofixA` approximant of `mirStatefulTree body args mem` at depth `n`. -/
@[reducible]
def mirStatefulApprox
    (body : CapturedMir) (args : List Value) (mem : Memory) (n : Nat) :
    CofixA MirEffect MirOutcome n :=
  mirExecApprox body n (.running (initMachineStateWithMemory body args mem))

/-- Direct `CofixA` approximant of `mirStatefulTreeWithCallees body args mem callees` at depth `n`. -/
@[reducible]
def mirStatefulWithCalleesApprox
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (callees : List CapturedMir) (n : Nat) :
    CofixA MirEffect MirOutcome n :=
  mirExecApprox body n
    (.running (initMachineStateWithMemoryAndCallees body args mem callees))

@[simp]
theorem ofITree_mirTree (body : CapturedMir) (s : MachineState) (n : Nat) :
    ofITree n (mirTree body s) = mirExecApprox body n (.running s) :=
  ofITree_cofix (stepMirState body) (.running s) n

@[simp]
theorem ofITree_mirStatefulTree
    (body : CapturedMir) (args : List Value) (mem : Memory) (n : Nat) :
    ofITree n (mirStatefulTree body args mem) = mirStatefulApprox body args mem n :=
  ofITree_cofix (stepMirState body) (.running (initMachineStateWithMemory body args mem)) n

@[simp]
theorem ofITree_mirStatefulTreeWithCallees
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (callees : List CapturedMir) (n : Nat) :
    ofITree n (mirStatefulTreeWithCallees body args mem callees) =
      mirStatefulWithCalleesApprox body args mem callees n :=
  ofITree_cofix (stepMirState body)
    (.running (initMachineStateWithMemoryAndCallees body args mem callees)) n

/--
Suffix-free `CofixA` handler corresponding to `silenceMirObs`: silences
`MirObsE` into `.ret PUnit.unit` while preserving `MirFailE` and `MirCallE`.
-/
@[reducible]
def silenceMirObsApprox :
    (i : MirEffect.I) → (m : Nat) → CofixA MirEffect (MirEffect.O i) m
  | _, 0 => .zero
  | .inl (.fail fk), _ + 1 => .vis (.inl (.fail fk)) PEmpty.elim
  | .inr (.inl _), _ + 1 => .ret PUnit.unit
  | .inr (.inr (.call req)), m' + 1 =>
    .vis (.inr (.inr (.call req))) (fun ans => CofixA.retApprox ans m')

/-- `ofITree m (silenceMirObs i)` agrees with `silenceMirObsApprox i m` for all `i, m`. -/
@[simp]
theorem ofITree_silenceMirObs (i : MirEffect.I) (m : Nat) :
    ofITree m (silenceMirObs i) = silenceMirObsApprox i m := by
  cases m with
  | zero => rfl
  | succ m' =>
    rcases i with f | (obsReq | callReq)
    · cases f with
      | fail fk =>
        change ofITree (m' + 1)
            (ITree.vis (E := MirEffect) (.inl (.fail fk)) ITree.ret >>= fun o => PEmpty.elim o) =
          CofixA.vis (E := MirEffect) (.inl (.fail fk)) PEmpty.elim
        erw [vis_bind, ofITree_vis]
        congr 1; funext o; exact PEmpty.elim o
    · exact ofITree_ret (E := MirEffect) m' PUnit.unit
    · cases callReq with
      | call req =>
        exact ofITree_trigger (E := MirEffect) m' (.inr (.inr (.call req)))

/--
Direct `CofixA` approximant of `ITree.interp silenceMirObs (ITree.cofix (stepMirState body) st)`
computed via `interpApprox silenceMirObsApprox` with zero `ITree.observe`.
-/
@[reducible]
def mirObsErasedExecApprox (body : CapturedMir) (n : Nat) (st : MirExecState) :
    CofixA MirEffect MirOutcome n :=
  interpApprox silenceMirObsApprox n (mirExecApprox body n st)

/--
Direct `CofixA` approximant of `mirObsErasedStatefulTree body args mem` at depth `n`.
-/
@[reducible]
def mirObsErasedStatefulApprox
    (body : CapturedMir) (args : List Value) (mem : Memory) (n : Nat) :
    CofixA MirEffect MirOutcome n :=
  interpApprox silenceMirObsApprox n (mirStatefulApprox body args mem n)

/--
Direct `CofixA` approximant of `mirObsErasedStatefulTreeWithCallees body args mem callees`
at depth `n`.
-/
@[reducible]
def mirObsErasedStatefulWithCalleesApprox
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (callees : List CapturedMir) (n : Nat) :
    CofixA MirEffect MirOutcome n :=
  interpApprox silenceMirObsApprox n
    (mirStatefulWithCalleesApprox body args mem callees n)

/-- Bridge theorem equating `ofITree n (ITree.interp silenceMirObs t)` with
`interpApprox silenceMirObsApprox n (ofITree n t)`. -/
@[simp]
theorem ofITree_interp_silenceMirObs
    (t : ITree MirEffect MirOutcome) (n : Nat) :
    ofITree n (ITree.interp silenceMirObs t) =
      interpApprox silenceMirObsApprox n (ofITree n t) := by
  rw [ofITree_interp]
  exact (interpApprox_congr ofITree_silenceMirObs n).1 (ofITree n t)

/-- Bridge theorem equating `ofITree n (mirObsErasedStatefulTree body args mem)`
with `mirObsErasedStatefulApprox body args mem n`. -/
@[simp]
theorem ofITree_mirObsErasedStatefulTree
    (body : CapturedMir) (args : List Value) (mem : Memory) (n : Nat) :
    ofITree n (mirObsErasedStatefulTree body args mem) =
      mirObsErasedStatefulApprox body args mem n := by
  unfold mirObsErasedStatefulTree mirObsErasedStatefulTreeWithCallees mirObsErasedStatefulApprox
  rw [ofITree_interp_silenceMirObs, ofITree_mirStatefulTreeWithCallees]
  rfl

/-- Bridge theorem equating `ofITree n (mirObsErasedStatefulTreeWithCallees body args mem callees)`
with `mirObsErasedStatefulWithCalleesApprox body args mem callees n`. -/
@[simp]
theorem ofITree_mirObsErasedStatefulTreeWithCallees
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (callees : List CapturedMir) (n : Nat) :
    ofITree n (mirObsErasedStatefulTreeWithCallees body args mem callees) =
      mirObsErasedStatefulWithCalleesApprox body args mem callees n := by
  unfold mirObsErasedStatefulTreeWithCallees mirObsErasedStatefulWithCalleesApprox
  rw [ofITree_interp_silenceMirObs, ofITree_mirStatefulTreeWithCallees]

/--
Eliminate a `MirEffect` visible node `(i : MirEffect.I)` and its continuation
`k : MirEffect.O i → X` without generating index-transporting `Eq.ndrec` casts:
matching on `i : MirEffect.I` before introducing `k` refines the return type
`(MirEffect.O i → X) → α` by definitional reduction in each arm.
-/
@[inline, reducible]
def elimMirVis {X α : Type}
    (onFail : FailureKind → (PEmpty → X) → α)
    (onSilent : (PUnit → X) → α)
    (onEvent : Nat → (PUnit → X) → α)
    (onCall : MirCallReq → (MirCallAns → X) → α)
    (i : MirEffect.I) : (MirEffect.O i → X) → α :=
  Sum.casesOn (motive := fun i : MirEffect.I => (MirEffect.O i → X) → α) i
    (fun f =>
      FailReq.casesOn (motive := fun f => (MirEffect.O (.inl f) → X) → α) f
        (fun fk => onFail fk))
    (fun rest =>
      Sum.casesOn (motive := fun r => (MirEffect.O (.inr r) → X) → α) rest
        (fun obsReq =>
          ObsReq.casesOn (motive := fun o => (MirEffect.O (.inr (.inl o)) → X) → α) obsReq
            (fun obs =>
              MirObs.casesOn
                (motive := fun ob => (MirEffect.O (.inr (.inl (.emit ob))) → X) → α)
                obs
                onSilent
                (fun tag => onEvent tag)))
        (fun callReq =>
          CallReq.casesOn (motive := fun c => (MirEffect.O (.inr (.inr c)) → X) → α) callReq
            (fun req => onCall req)))

/--
Direct suffix-free `CofixA` boolean trace checker over `CofixA MirEffect MirOutcome n`,
replaying `ObservedEvent`s and `ObservedOutcome` by structural recursion on the
finite `CofixA` approximant without `ITree.observe` or `Event MirEffect` list
allocation.

Defined via `CofixA.casesOn` and `elimMirVis` so that its definitional closure
is completely free of `Eq.rec` / `Eq.ndrec` / `Nat.noConfusion` index transports.

An approximant node carries no `MirExecState`, so this walker can only reject
impure external calls by runtime argument value (`findCallReqImpurePtrArgIdx?`).
Over the plain approximants `mirExecApprox` / `mirStatefulApprox` it is therefore
more permissive than `checkFullMirTraceFast` (which also rejects impure call-site
operand types); run it over `mirExecGuardedApprox` for the exact policy
(`checkMirTraceApprox_guarded_eq`).
-/
@[reducible]
def checkMirTraceApprox :
    {n : Nat} → CofixA MirEffect MirOutcome n →
    List ObservedEvent → ObservedOutcome → Bool
  | _, a, events, outcome =>
    CofixA.casesOn
      (motive := fun _ _ => List ObservedEvent → ObservedOutcome → Bool)
      a
      (fun _ _ => false)
      (fun out evs outc =>
        match evs with
        | [] => checkOutcomeMatches outc out
        | _ :: _ => false)
      (fun t' evs outc =>
        checkMirTraceApprox t' evs outc)
      (fun i k evs outc =>
        elimMirVis
          (fun _ _ => false)
          (fun _ => false)
          (fun tag k' =>
            match evs with
            | .branch expectedTag :: rest =>
              if Nat.beq tag expectedTag then
                checkMirTraceApprox (k' PUnit.unit) rest outc
              else
                false
            | _ => false)
          (fun req k' =>
            match findCallReqImpurePtrArgIdx? req with
            | some _ => false
            | none =>
              match evs with
              | obsEv :: rest =>
                match matchCallObservedEvent req obsEv with
                | some ans =>
                  checkMirTraceApprox (k' ans) rest outc
                | none => false
              | [] => false)
          i k)
      events outcome

theorem checkMirTraceApprox_sound_reachesRetApprox
    {n : Nat} {a : CofixA MirEffect MirOutcome n}
    {events : List ObservedEvent} {outcome : ObservedOutcome}
    (h_ok : checkMirTraceApprox a events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRetApprox a tr out := by
  induction a generalizing events with
  | zero => nomatch h_ok
  | ret out₀ =>
    cases events with
    | nil =>
      exact ⟨[], out₀, trivial, checkOutcomeMatches_sound h_ok, .ret out₀⟩
    | cons _ _ => nomatch h_ok
  | tau t' ih =>
    rcases ih h_ok with ⟨tr, out, h_evs, h_out, h_reach⟩
    exact ⟨tr, out, h_evs, h_out, .tau h_reach⟩
  | vis i k ih =>
    rcases i with f | (obsReq | callReq)
    · nomatch h_ok
    · cases obsReq with
      | emit obs =>
        cases obs with
        | silent => nomatch h_ok
        | event tag =>
          cases events with
          | nil => nomatch h_ok
          | cons ev rest =>
            cases ev with
            | branch expectedTag =>
              change
                (if Nat.beq tag expectedTag then
                  checkMirTraceApprox (k PUnit.unit) rest outcome
                else false) = true at h_ok
              revert h_ok
              cases htag : Nat.beq tag expectedTag <;> intro h_ok
              · nomatch h_ok
              · rcases ih PUnit.unit h_ok with ⟨trRest, out, h_evs, h_out, h_reach⟩
                exact ⟨⟨.inr (.inl (.emit (.event tag))), PUnit.unit⟩ :: trRest,
                  out, ⟨Nat.beq_eq.mp htag, h_evs⟩, h_out,
                  ReachesRetApprox.vis (E := MirEffect)
                    (i := .inr (.inl (.emit (.event tag))))
                    False.elim PUnit.unit h_reach⟩
            | _ => nomatch h_ok
    · cases callReq with
      | call req =>
        unfold checkMirTraceApprox elimMirVis at h_ok
        dsimp only at h_ok
        cases h_imp : findCallReqImpurePtrArgIdx? req with
        | some _ => simp only [h_imp] at h_ok; nomatch h_ok
        | none =>
          simp only [h_imp] at h_ok
          cases events with
          | nil => nomatch h_ok
          | cons obsEv rest =>
            cases h_match : matchCallObservedEvent req obsEv with
            | none => simp only [h_match] at h_ok; nomatch h_ok
            | some ans =>
              simp only [h_match] at h_ok
              rcases ih ans h_ok with ⟨trRest, out, h_evs, h_out, h_reach⟩
              exact ⟨⟨.inr (.inr (.call req)), ans⟩ :: trRest,
                out, ⟨matchCallObservedEvent_sound h_match, h_evs⟩, h_out,
                ReachesRetApprox.vis (E := MirEffect)
                  (i := .inr (.inr (.call req)))
                  False.elim ans h_reach⟩

/-- Soundness of `checkMirTraceApprox` over `ofITree n t`. -/
theorem checkMirTraceApprox_sound
    {n : Nat} {t : ITree MirEffect MirOutcome}
    {events : List ObservedEvent} {outcome : ObservedOutcome}
    (h_ok : checkMirTraceApprox (ofITree n t) events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet t tr out := by
  rcases checkMirTraceApprox_sound_reachesRetApprox h_ok with
    ⟨tr, out, h_evs, h_out, h_reach⟩
  exact ⟨tr, out, h_evs, h_out, h_reach.toReachesRet⟩

/-- Soundness of `checkMirTraceApprox` on `mirStatefulApprox`. -/
theorem checkMirStatefulApprox_sound
    (n : Nat) (body : CapturedMir) (args : List Value) (mem : Memory)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok :
      checkMirTraceApprox (mirStatefulApprox body args mem n) events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (mirStatefulTree body args mem) tr out := by
  rw [← ofITree_mirStatefulTree] at h_ok
  exact checkMirTraceApprox_sound h_ok

/-- Soundness of `checkMirTraceApprox` on `mirObsErasedStatefulApprox`
(`interpApprox silenceMirObsApprox`). -/
theorem checkMirObsErasedStatefulApprox_sound
    (n : Nat) (body : CapturedMir) (args : List Value) (mem : Memory)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok :
      checkMirTraceApprox (mirObsErasedStatefulApprox body args mem n) events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (mirObsErasedStatefulTree body args mem) tr out := by
  rw [← ofITree_mirObsErasedStatefulTree] at h_ok
  exact checkMirTraceApprox_sound h_ok

/-! ### Policy-Exact `CofixA` Trace Checkers (`stepMirStateGuarded`)

A `CofixA` approximant forgets the `MirExecState` (active body and program
counter) at every node, so `checkMirTraceApprox` walking the plain approximant
`approxCofix (stepMirState body)` can only re-check runtime argument values
(`findCallReqImpurePtrArgIdx?`); it cannot re-check call-site operand types
(`findBlockCallImpurePtrArgIdx?`, e.g. a `*const T` / `*mut T` operand whose
runtime tag happens to be `.frozen`). It is therefore strictly more permissive
than `checkFullMirTraceFast` / `checkObsErasedMirTraceFast`.

`stepMirStateGuarded` folds the complete `findActiveCallImpurePtrArgIdx?` policy
into the step function itself (rejected calls become fail-closed
`.unsupported` fault nodes), so walkers over
`mirExecGuardedApprox = approxCofix (stepMirStateGuarded body)` reject exactly
the traces the coalgebra-direct checkers reject
(`checkMirTraceApprox_guarded_eq`, `checkMirObsErasedTraceApprox_guarded_eq`). -/

/-- Fold the external-call purity policy of `checkFullMirTraceFast` into one MIR
step node: an external call rejected by `findActiveCallImpurePtrArgIdx?` becomes a
fail-closed `.unsupported` fault node; all other nodes are unchanged.
Defined via `ITreeF.casesOn` and `elimMirVis` so its definitional closure is free
of `Eq.rec` / `Eq.ndrec` index transports. -/
@[reducible]
def guardMirCallNode (body : CapturedMir) (st : MirExecState)
    (node : MirStepNode) : MirStepNode :=
  ITreeF.casesOn (motive := fun _ => MirStepNode) node
    (fun out => .ret out)
    (fun st' => .tau st')
    (elimMirVis
      (fun fk k => .vis (.inl (.fail fk)) k)
      (fun k => .vis (.inr (.inl (.emit .silent))) k)
      (fun tag k => .vis (.inr (.inl (.emit (.event tag)))) k)
      (fun req k =>
        match findActiveCallImpurePtrArgIdx? (execStateActiveBody body st) (execStateCursor st).1 req with
        | some _ => MirStepNode.fail .unsupported
        | none => .vis (.inr (.inr (.call req))) k))

/-- Policy-guarded MIR step (`stepMirState` with `guardMirCallNode`). -/
@[reducible]
def stepMirStateGuarded (body : CapturedMir) (st : MirExecState) : MirStepNode :=
  guardMirCallNode body st (stepMirState body st)

/-- Policy-guarded `CofixA` approximant of `ITree.cofix (stepMirState body) st`. -/
@[reducible]
def mirExecGuardedApprox (body : CapturedMir) (n : Nat) (st : MirExecState) :
    CofixA MirEffect MirOutcome n :=
  approxCofix (stepMirStateGuarded body) n st

theorem findCallReqImpurePtrArgIdx?_eq_none_of_active
    {activeBody : CapturedMir} {blockIdx : Nat} {req : MirCallReq}
    (h : findActiveCallImpurePtrArgIdx? activeBody blockIdx req = none) :
    findCallReqImpurePtrArgIdx? req = none := by
  unfold findActiveCallImpurePtrArgIdx? at h
  split at h
  · nomatch h
  · exact h

/--
Exact agreement of the policy-guarded approximant walker with the
coalgebra-direct full checker at every fuel: `checkMirTraceApprox` over
`mirExecGuardedApprox body n st` equals `checkFullMirTraceFast n body st`.
-/
theorem checkMirTraceApprox_guarded_eq (body : CapturedMir) (n : Nat) :
    ∀ (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome),
      checkMirTraceApprox (mirExecGuardedApprox body n st) events outcome =
        checkFullMirTraceFast n body st events outcome := by
  induction n with
  | zero => intro _ _ _; rfl
  | succ m ih =>
    intro st events outcome
    unfold mirExecGuardedApprox at ih ⊢
    unfold approxCofix stepMirStateGuarded checkFullMirTraceFast
    cases hs : stepMirState body st with
    | ret out => rfl
    | tau st' => exact ih st' events outcome
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · rfl
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent => rfl
          | event tag =>
            cases events with
            | nil => rfl
            | cons ev rest =>
              cases ev with
              | branch expectedTag =>
                dsimp only [guardMirCallNode, elimMirVis]
                unfold checkMirTraceApprox
                dsimp only [elimMirVis]
                cases Nat.beq tag expectedTag with
                | false => rfl
                | true => exact ih (k PUnit.unit) rest outcome
              | extCall _ _ _ => rfl
              | extCallPanic _ _ => rfl
              | extCallAbort _ _ => rfl
      · cases callReq with
        | call req =>
          dsimp only [guardMirCallNode, elimMirVis]
          cases hpol :
              findActiveCallImpurePtrArgIdx? (execStateActiveBody body st)
                (execStateCursor st).1 req with
          | some _ => rfl
          | none =>
            have hreq := findCallReqImpurePtrArgIdx?_eq_none_of_active hpol
            dsimp only
            unfold checkMirTraceApprox
            dsimp only [elimMirVis]
            simp only [hreq]
            cases events with
            | nil => rfl
            | cons obsEv rest =>
              dsimp only
              cases matchCallObservedEvent req obsEv with
              | none => rfl
              | some ans => exact ih (k ans) rest outcome

/--
Suffix-free branch-erased `CofixA` trace walker: silences `MirObsE` nodes inline
(continuing at `k PUnit.unit` without consuming events) and replays external
calls against `events`, mirroring `checkObsErasedMirTraceFast` on approximants.
Defined via `CofixA.casesOn` and `elimMirVis` so its definitional closure is free
of `Eq.rec` / `Eq.ndrec` / `Nat.noConfusion` index transports.
-/
@[reducible]
def checkMirObsErasedTraceApprox :
    {n : Nat} → CofixA MirEffect MirOutcome n →
    List ObservedEvent → ObservedOutcome → Bool
  | _, a, events, outcome =>
    CofixA.casesOn
      (motive := fun _ _ => List ObservedEvent → ObservedOutcome → Bool)
      a
      (fun _ _ => false)
      (fun out evs outc =>
        match evs with
        | [] => checkOutcomeMatches outc out
        | _ :: _ => false)
      (fun t' evs outc =>
        checkMirObsErasedTraceApprox t' evs outc)
      (fun i k evs outc =>
        elimMirVis
          (fun _ _ => false)
          (fun k' => checkMirObsErasedTraceApprox (k' PUnit.unit) evs outc)
          (fun _ k' => checkMirObsErasedTraceApprox (k' PUnit.unit) evs outc)
          (fun req k' =>
            match findCallReqImpurePtrArgIdx? req with
            | some _ => false
            | none =>
              match evs with
              | obsEv :: rest =>
                match matchCallObservedEvent req obsEv with
                | some ans =>
                  checkMirObsErasedTraceApprox (k' ans) rest outc
                | none => false
              | [] => false)
          i k)
      events outcome

/--
Exact agreement of the branch-erased approximant walker over the policy-guarded
approximant with `checkObsErasedMirTraceFast` at every fuel.
-/
theorem checkMirObsErasedTraceApprox_guarded_eq (body : CapturedMir) (n : Nat) :
    ∀ (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome),
      checkMirObsErasedTraceApprox (mirExecGuardedApprox body n st) events outcome =
        checkObsErasedMirTraceFast n body st events outcome := by
  induction n with
  | zero => intro _ _ _; rfl
  | succ m ih =>
    intro st events outcome
    unfold mirExecGuardedApprox at ih ⊢
    unfold approxCofix stepMirStateGuarded checkObsErasedMirTraceFast
    cases hs : stepMirState body st with
    | ret out => rfl
    | tau st' => exact ih st' events outcome
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · rfl
      · cases obsReq with
        | emit obs =>
          cases obs <;> exact ih (k PUnit.unit) events outcome
      · cases callReq with
        | call req =>
          dsimp only [guardMirCallNode, elimMirVis]
          cases hpol :
              findActiveCallImpurePtrArgIdx? (execStateActiveBody body st)
                (execStateCursor st).1 req with
          | some _ => rfl
          | none =>
            have hreq := findCallReqImpurePtrArgIdx?_eq_none_of_active hpol
            dsimp only
            unfold checkMirObsErasedTraceApprox
            dsimp only [elimMirVis]
            simp only [hreq]
            cases events with
            | nil => rfl
            | cons obsEv rest =>
              dsimp only
              cases matchCallObservedEvent req obsEv with
              | none => rfl
              | some ans => exact ih (k ans) rest outcome

/-- Simulation from the `interpApprox silenceMirObsApprox` route to the inline
branch-erasing walker, simultaneously in source and handler mode. -/
private theorem checkMirTraceApprox_interpSilence_aux :
    ∀ n : Nat,
      (∀ {d : Nat} (a : CofixA MirEffect MirOutcome d)
          (events : List ObservedEvent) (outcome : ObservedOutcome),
        checkMirTraceApprox (interpApprox silenceMirObsApprox n a) events outcome = true →
        checkMirObsErasedTraceApprox a events outcome = true) ∧
      (∀ {d : Nat} (req : MirCallReq)
          (k : MirEffect.O (.inr (.inr (.call req))) → CofixA MirEffect MirOutcome d)
          (ans : MirCallAns) (events : List ObservedEvent) (outcome : ObservedOutcome),
        checkMirTraceApprox
            (interpHandlerApprox silenceMirObsApprox n (i := .inr (.inr (.call req)))
              (CofixA.retApprox (E := MirEffect) ans n) k) events outcome = true →
        checkMirObsErasedTraceApprox (k ans) events outcome = true) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ _ _ h => ?_, fun _ _ _ _ _ h => ?_⟩
    · nomatch h
    · nomatch h
  | succ m ih =>
    obtain ⟨ihS, ihH⟩ := ih
    refine ⟨?_, ?_⟩
    · intro d a events outcome h
      cases a with
      | zero => exact ihS .zero events outcome h
      | ret out => exact h
      | tau t' => exact ihS t' events outcome h
      | vis i k =>
        rcases i with f | (obsReq | callReq)
        · cases f with
          | fail fk => nomatch h
        · cases obsReq with
          | emit obs =>
            cases obs <;> exact ihS (k PUnit.unit) events outcome h
        · cases callReq with
          | call req =>
            have hred : checkMirTraceApprox
                (interpApprox silenceMirObsApprox (m + 1)
                  (CofixA.vis (E := MirEffect) (.inr (.inr (.call req))) k))
                events outcome =
                checkMirTraceApprox
                  (CofixA.vis (E := MirEffect) (.inr (.inr (.call req)))
                    (fun ans => interpHandlerApprox silenceMirObsApprox m
                      (i := .inr (.inr (.call req))) (CofixA.retApprox (E := MirEffect) ans m) k))
                  events outcome := rfl
            rw [hred] at h
            unfold checkMirTraceApprox at h
            dsimp only [elimMirVis] at h
            unfold checkMirObsErasedTraceApprox
            dsimp only [elimMirVis]
            cases hreq : findCallReqImpurePtrArgIdx? req with
            | some _ => simp only [hreq, Bool.false_eq_true] at h
            | none =>
              simp only [hreq] at h ⊢
              cases events with
              | nil => nomatch h
              | cons obsEv rest =>
                dsimp only at h ⊢
                cases hm : matchCallObservedEvent req obsEv with
                | none => simp only [hm, Bool.false_eq_true] at h
                | some ans =>
                  simp only [hm] at h ⊢
                  exact ihH req k ans rest outcome h
    · intro d req k ans events outcome h
      cases m with
      | zero => nomatch h
      | succ m' =>
        exact ihS (k ans) events outcome h

/--
The `interpApprox silenceMirObsApprox` route (the `CofixA` image of
`ITree.interp silenceMirObs`, see `ofITree_interp_silenceMirObs`) over the
policy-guarded approximant accepts only traces that `checkObsErasedMirTraceFast`
accepts at the same fuel (each external call costs one extra output depth in the
interpreted approximant, so the converse needs `fuel + #calls`).
-/
theorem checkMirTraceApprox_interpSilence_guarded_imp
    (body : CapturedMir) (n : Nat) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok :
      checkMirTraceApprox
        (interpApprox silenceMirObsApprox n (mirExecGuardedApprox body n st))
        events outcome = true) :
    checkObsErasedMirTraceFast n body st events outcome = true := by
  rw [← checkMirObsErasedTraceApprox_guarded_eq]
  exact (checkMirTraceApprox_interpSilence_aux n).1 _ events outcome h_ok

/-- Fuel monotonicity of `checkFullMirTraceFast`: if `checkFullMirTraceFast`
accepts at fuel `m` and `m ≤ n`, it accepts at fuel `n`. -/
theorem checkFullMirTraceFast_mono
    {m n : Nat} (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok : checkFullMirTraceFast m body st events outcome = true)
    (hmn : m ≤ n) :
    checkFullMirTraceFast n body st events outcome = true := by
  induction m generalizing n st events with
  | zero => nomatch h_ok
  | succ m' ih =>
    cases n with
    | zero => omega
    | succ n' =>
      have hmn' : m' ≤ n' := Nat.le_of_succ_le_succ hmn
      unfold checkFullMirTraceFast at h_ok ⊢
      cases h_step : stepMirState body st with
      | ret out₀ =>
        simp only [h_step] at h_ok ⊢
        exact h_ok
      | tau st' =>
        simp only [h_step] at h_ok ⊢
        exact ih st' events h_ok hmn'
      | vis i k =>
        rcases i with f | (obsReq | callReq)
        · simp only [h_step] at h_ok; nomatch h_ok
        · cases obsReq with
          | emit obs =>
            cases obs with
            | silent => simp only [h_step] at h_ok; nomatch h_ok
            | event tag =>
              simp only [h_step] at h_ok ⊢
              cases events with
              | nil => nomatch h_ok
              | cons ev rest =>
                cases ev with
                | branch expectedTag =>
                  dsimp only at h_ok ⊢
                  revert h_ok
                  cases Nat.beq tag expectedTag <;> intro h_ok
                  · nomatch h_ok
                  · exact ih (k PUnit.unit) rest h_ok hmn'
                | _ => nomatch h_ok
        · cases callReq with
          | call req =>
            simp only [h_step] at h_ok ⊢
            cases h_imp :
                findActiveCallImpurePtrArgIdx?
                  (execStateActiveBody body st) (execStateCursor st).1 req with
            | some _ => simp only [h_imp] at h_ok; nomatch h_ok
            | none =>
              simp only [h_imp] at h_ok ⊢
              cases events with
              | nil => nomatch h_ok
              | cons obsEv rest =>
                dsimp only at h_ok ⊢
                cases h_match : matchCallObservedEvent req obsEv with
                | none => simp only [h_match] at h_ok; nomatch h_ok
                | some ans =>
                  simp only [h_match] at h_ok ⊢
                  exact ih (k ans) rest h_ok hmn'

/-- Fuel monotonicity of `checkObsErasedMirTraceFast`: if `checkObsErasedMirTraceFast`
accepts at fuel `m` and `m ≤ n`, it accepts at fuel `n`. -/
theorem checkObsErasedMirTraceFast_mono
    {m n : Nat} (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok : checkObsErasedMirTraceFast m body st events outcome = true)
    (hmn : m ≤ n) :
    checkObsErasedMirTraceFast n body st events outcome = true := by
  induction m generalizing n st events with
  | zero => nomatch h_ok
  | succ m' ih =>
    cases n with
    | zero => omega
    | succ n' =>
      have hmn' : m' ≤ n' := Nat.le_of_succ_le_succ hmn
      unfold checkObsErasedMirTraceFast at h_ok ⊢
      cases h_step : stepMirState body st with
      | ret out₀ =>
        simp only [h_step] at h_ok ⊢
        exact h_ok
      | tau st' =>
        simp only [h_step] at h_ok ⊢
        exact ih st' events h_ok hmn'
      | vis i k =>
        rcases i with f | (obsReq | callReq)
        · simp only [h_step] at h_ok; nomatch h_ok
        · simp only [h_step] at h_ok ⊢
          exact ih (k PUnit.unit) events h_ok hmn'
        · cases callReq with
          | call req =>
            simp only [h_step] at h_ok ⊢
            cases h_imp :
                findActiveCallImpurePtrArgIdx?
                  (execStateActiveBody body st) (execStateCursor st).1 req with
            | some _ => simp only [h_imp] at h_ok; nomatch h_ok
            | none =>
              simp only [h_imp] at h_ok ⊢
              cases events with
              | nil => nomatch h_ok
              | cons obsEv rest =>
                dsimp only at h_ok ⊢
                cases h_match : matchCallObservedEvent req obsEv with
                | none => simp only [h_match] at h_ok; nomatch h_ok
                | some ans =>
                  simp only [h_match] at h_ok ⊢
                  exact ih (k ans) rest h_ok hmn'

/-- Converse completeness from `checkObsErasedMirTraceFast` to the
`interpApprox silenceMirObsApprox` route: if `checkObsErasedMirTraceFast` accepts
in `fuel` steps, then `checkMirTraceApprox` accepts
`interpApprox silenceMirObsApprox n (mirExecGuardedApprox body m st)` whenever
`fuel ≤ m` and `fuel + events.length ≤ n`. -/
private theorem checkObsErasedMirTraceFast_imp_interpSilence_aux
    (body : CapturedMir) (fuel : Nat) :
    ∀ {m n : Nat} (st : MirExecState)
      (events : List ObservedEvent) (outcome : ObservedOutcome),
      checkObsErasedMirTraceFast fuel body st events outcome = true →
      fuel ≤ m →
      fuel + events.length ≤ n →
      checkMirTraceApprox
        (interpApprox silenceMirObsApprox n (mirExecGuardedApprox body m st))
        events outcome = true := by
  induction fuel with
  | zero => intro _ _ _ _ _ h_ok _ _; nomatch h_ok
  | succ fuel' ih =>
    intro m n st events outcome h_ok hfm hfn
    cases m with
    | zero => omega
    | succ m' =>
      cases n with
      | zero => omega
      | succ n' =>
        unfold checkObsErasedMirTraceFast at h_ok
        unfold mirExecGuardedApprox approxCofix stepMirStateGuarded
        cases hs : stepMirState body st with
        | ret out₀ =>
          simp only [hs] at h_ok
          exact h_ok
        | tau st' =>
          simp only [hs] at h_ok
          exact ih st' events outcome h_ok (by omega) (by omega)
        | vis i k =>
          rcases i with f | (obsReq | callReq)
          · simp only [hs] at h_ok; nomatch h_ok
          · cases obsReq with
            | emit obs =>
              simp only [hs] at h_ok
              cases obs <;>
                exact ih (k PUnit.unit) events outcome h_ok (by omega) (by omega)
          · cases callReq with
            | call req =>
              simp only [hs] at h_ok
              dsimp only [guardMirCallNode, elimMirVis]
              cases hpol :
                  findActiveCallImpurePtrArgIdx? (execStateActiveBody body st)
                    (execStateCursor st).1 req with
              | some _ => simp only [hpol] at h_ok; nomatch h_ok
              | none =>
                simp only [hpol] at h_ok
                cases events with
                | nil => nomatch h_ok
                | cons obsEv rest =>
                  dsimp only at h_ok
                  cases hm : matchCallObservedEvent req obsEv with
                  | none => simp only [hm] at h_ok; nomatch h_ok
                  | some ans =>
                    simp only [hm] at h_ok
                    cases n' with
                    | zero =>
                      simp only [List.length_cons] at hfn
                      omega
                    | succ n'' =>
                      have hreq := findCallReqImpurePtrArgIdx?_eq_none_of_active hpol
                      dsimp only
                      have hred :
                          checkMirTraceApprox
                            (interpApprox silenceMirObsApprox (n'' + 2)
                              (CofixA.vis (E := MirEffect) (.inr (.inr (.call req)))
                                (fun o => approxCofix (stepMirStateGuarded body) m' (k o))))
                            (obsEv :: rest) outcome =
                          (match findCallReqImpurePtrArgIdx? req with
                           | some _ => false
                           | none =>
                             match matchCallObservedEvent req obsEv with
                             | some ans' =>
                               checkMirTraceApprox
                                 (interpApprox silenceMirObsApprox n''
                                   (mirExecGuardedApprox body m' (k ans')))
                                 rest outcome
                             | none => false) := rfl
                      rw [hred, hreq, hm]
                      simp only [List.length_cons] at hfn
                      exact ih (k ans) rest outcome h_ok (by omega) (by omega)

/--
Tight converse to `checkMirTraceApprox_interpSilence_guarded_imp`: every trace
accepted by `checkObsErasedMirTraceFast` at `fuel` is accepted by
`checkMirTraceApprox` over `interpApprox silenceMirObsApprox n (mirExecGuardedApprox body n st)`
for all `n ≥ fuel + events.length` (each external call emits one `.vis` node and
one handler-return `.tau` node in the interpreted approximant).
-/
theorem checkObsErasedMirTraceFast_imp_interpSilence_guarded
    {fuel n : Nat} (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok : checkObsErasedMirTraceFast fuel body st events outcome = true)
    (hfn : fuel + events.length ≤ n) :
    checkMirTraceApprox
      (interpApprox silenceMirObsApprox n (mirExecGuardedApprox body n st))
      events outcome = true :=
  checkObsErasedMirTraceFast_imp_interpSilence_aux body fuel st events outcome
    h_ok (by omega) hfn

/-- Monotonicity of `checkMirTraceApprox` under `CofixA.trunc`: if a truncated
approximant `a.trunc` is accepted by `checkMirTraceApprox`, then `a` is
accepted as well. -/
theorem checkMirTraceApprox_trunc
    {n : Nat} {a : CofixA MirEffect MirOutcome (n + 1)}
    {events : List ObservedEvent} {outcome : ObservedOutcome}
    (h : checkMirTraceApprox a.trunc events outcome = true) :
    checkMirTraceApprox a events outcome = true := by
  induction n generalizing events with
  | zero => nomatch h
  | succ m' ih =>
    cases a with
    | ret out₀ => exact h
    | tau t' => exact ih h
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · cases f with
        | fail _ => nomatch h
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent => nomatch h
          | event tag =>
            cases events with
            | nil => nomatch h
            | cons ev rest =>
              cases ev with
              | branch expectedTag =>
                change
                  (if Nat.beq tag expectedTag then
                    checkMirTraceApprox (k PUnit.unit).trunc rest outcome
                  else false) = true at h
                change
                  (if Nat.beq tag expectedTag then
                    checkMirTraceApprox (k PUnit.unit) rest outcome
                  else false) = true
                revert h
                cases Nat.beq tag expectedTag <;> intro h
                · nomatch h
                · exact ih h
              | _ => nomatch h
      · cases callReq with
        | call req =>
          revert h
          unfold CofixA.trunc approxStep checkMirTraceApprox elimMirVis
          dsimp only
          cases findCallReqImpurePtrArgIdx? req with
          | some _ => intro h; nomatch h
          | none =>
            cases events with
            | nil => intro h; nomatch h
            | cons obsEv rest =>
              dsimp only
              cases matchCallObservedEvent req obsEv with
              | none => intro h; nomatch h
              | some ans =>
                intro h
                exact ih h

/-- Depth monotonicity of `checkMirTraceApprox` over `ofITree`: if `ofITree m t`
is accepted and `m ≤ n`, then `ofITree n t` is accepted. -/
theorem checkMirTraceApprox_ofITree_mono
    {m n : Nat} {t : ITree MirEffect MirOutcome}
    {events : List ObservedEvent} {outcome : ObservedOutcome}
    (h : checkMirTraceApprox (ofITree m t) events outcome = true)
    (hmn : m ≤ n) :
    checkMirTraceApprox (ofITree n t) events outcome = true := by
  induction hmn with
  | refl => exact h
  | @step k _ ih =>
    rw [← trunc_ofITree k t] at ih
    exact checkMirTraceApprox_trunc ih

/-- Fuel monotonicity of `checkMirTraceApprox` over `interpApprox silenceMirObsApprox`
and `mirExecGuardedApprox`. -/
theorem checkMirTraceApprox_interpSilence_guarded_mono
    {m n : Nat} (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok :
      checkMirTraceApprox
        (interpApprox silenceMirObsApprox m (mirExecGuardedApprox body m st))
        events outcome = true)
    (hmn : m ≤ n) :
    checkMirTraceApprox
      (interpApprox silenceMirObsApprox n (mirExecGuardedApprox body n st))
      events outcome = true := by
  unfold mirExecGuardedApprox at h_ok ⊢
  rw [← ofITree_cofix, ← ofITree_interp_silenceMirObs] at h_ok ⊢
  exact checkMirTraceApprox_ofITree_mono h_ok hmn

/-! ## 5. Connection to Verification Certificates & Postcondition Refutation -/

/--
If a `VerificationResult c` certificate holds and an observed full trace is
consistent with `c.body` (and `c.callees`) on inputs `args` satisfying
`c.pre args` with normal return `retVal`, then `retVal` provably satisfies
`c.post args retVal`.
-/
theorem verifiedClaim_satisfies_observedTrace
    {c : Claim}
    (h_ver : VerificationResult c)
    (fuel : Nat) (args : List Value)
    (events : List ObservedEvent) (retVal : Value)
    (h_pre : c.pre args)
    (h_trace :
      checkFullObservedTraceBounded fuel c.body
        (initMachineStateWithCallees c.body args c.callees)
        events (.normal retVal) = true) :
    c.post args retVal := by
  rcases checkFullObservedTraceBounded_sound fuel c.body
      (initMachineStateWithCallees c.body args c.callees)
      events (.normal retVal) h_trace with
    ⟨tr, out, _, h_out, h_reach⟩
  cases out with
  | normal p =>
    rcases p with ⟨actualRet, mem'⟩
    dsimp [MatchesObservedOutcome] at h_out
    subst h_out
    exact (h_ver.proof args h_pre).2 (tr, .normal (actualRet, mem'))
      h_reach h_pre actualRet mem' rfl
  | panic => nomatch h_out
  | abort => nomatch h_out

/--
Refute a stateless `Claim` (`¬ c.holds`) by exhibiting a runtime trace
consistent with `c.body` and `c.callees` on inputs `args` satisfying `c.pre args`
whose normal return value `retVal` violates `c.post args retVal`.
-/
theorem refuteClaimByObservedTrace
    (c : Claim)
    (fuel : Nat) (args : List Value)
    (events : List ObservedEvent) (retVal : Value)
    (h_pre : c.pre args)
    (h_trace :
      checkFullObservedTraceBounded fuel c.body
        (initMachineStateWithCallees c.body args c.callees)
        events (.normal retVal) = true)
    (h_bad : ¬ c.post args retVal) :
    ¬ c.holds := by
  intro h_holds
  exact h_bad (verifiedClaim_satisfies_observedTrace ⟨h_holds⟩ fuel args
    events retVal h_pre h_trace)

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
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
        events (.normal retVal) = true) :
    ∃ mem', c.post args mem retVal mem' := by
  rcases checkFullObservedTraceBounded_sound fuel c.body
      (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
      events (.normal retVal) h_trace with
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
        (initMachineStateWithMemoryAndCallees c.body args mem c.callees)
        events (.normal retVal) = true)
    (h_bad : ∀ mem', ¬ c.post args mem retVal mem') :
    ¬ c.holds := by
  intro h_holds
  rcases verifiedStatefulClaim_satisfies_observedTrace ⟨h_holds⟩ fuel args mem
      events retVal h_pre h_trace with ⟨mem', h_post⟩
  exact h_bad mem' h_post

/--
If a universally quantified polymorphic stateful claim holds across all
`typeArgs` of length `paramCount`, and an observed full trace at a specific
instantiation `typeArgs` returns `retVal`, then `retVal` provably satisfies the
instantiated claim's postcondition for some post-state `mem'`.
-/
theorem verifiedPolyStatefulClaim_satisfies_observedTrace
    {claimFor : TypeSubst → StatefulClaim} {paramCount : Nat}
    (h_poly : ∀ typeArgs : TypeSubst,
      typeArgs.length = paramCount →
      StatefulVerificationResult (claimFor typeArgs))
    (typeArgs : TypeSubst)
    (h_len : typeArgs.length = paramCount)
    (fuel : Nat) (args : List Value) (mem : Memory)
    (events : List ObservedEvent) (retVal : Value)
    (h_pre : (claimFor typeArgs).pre args mem)
    (h_trace :
      checkFullObservedTraceBounded fuel (claimFor typeArgs).body
        (initMachineStateWithMemoryAndCallees (claimFor typeArgs).body args mem
          (claimFor typeArgs).callees)
        events (.normal retVal) = true) :
    ∃ mem', (claimFor typeArgs).post args mem retVal mem' :=
  verifiedStatefulClaim_satisfies_observedTrace (h_poly typeArgs h_len) fuel args
    mem events retVal h_pre h_trace

/--
Refute a universally quantified polymorphic stateful claim by exhibiting a
single monomorphized instantiation `typeArgs` (with `typeArgs.length = paramCount`)
and a consistent runtime trace whose normal return `retVal` violates the
postcondition across all post-states `mem'`.
-/
theorem refutePolyStatefulClaimByObservedTrace
    (claimFor : TypeSubst → StatefulClaim) (paramCount : Nat)
    (typeArgs : TypeSubst)
    (h_len : typeArgs.length = paramCount)
    (fuel : Nat) (args : List Value) (mem : Memory)
    (events : List ObservedEvent) (retVal : Value)
    (h_pre : (claimFor typeArgs).pre args mem)
    (h_trace :
      checkFullObservedTraceBounded fuel (claimFor typeArgs).body
        (initMachineStateWithMemoryAndCallees (claimFor typeArgs).body args mem
          (claimFor typeArgs).callees)
        events (.normal retVal) = true)
    (h_bad : ∀ mem', ¬ (claimFor typeArgs).post args mem retVal mem') :
    ¬ (∀ ta : TypeSubst, ta.length = paramCount →
        StatefulVerificationResult (claimFor ta)) := by
  intro h_poly
  exact refuteStatefulClaimByObservedTrace (claimFor typeArgs) fuel args mem
    events retVal h_pre h_trace h_bad (h_poly typeArgs h_len).proof

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
parameter of mutability `mutbl` and pointee `pointee`: `.active` (`.unique`)
for mutable parameters, and for shared parameters the same choice as
`sharedBorrowPerm` and `fnEntryRetagPerm .not`, `.frozen` for `Freeze`
pointees and `.cell` for interior-mutable (`!Freeze`) pointees.
-/
@[reducible]
def ptrParamBorrowPerm (mutbl : Mutability) (pointee : RigidTy) : TreeBorrowPerm :=
  match mutbl with
  | .mut => .active
  | .not =>
    if rigidTyIsFreezeFuel 16 pointee then .frozen else .cell

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
       activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩ =>
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
                  ⟨nextAllocId, nextGlobals, nextBorrows, nextTagVal, callees, traitImpls, callStack, activeCallee, activeProtectors, nextProtector, nextCallerLocals, fnPtrs, exposedAllocIds⟩
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
                  ⟨nextAllocId, nextGlobals, nextBorrows, nextTagVal, callees, traitImpls, callStack, activeCallee, activeProtectors, nextProtector, nextCallerLocals, fnPtrs, exposedAllocIds⟩
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
       activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩ =>
      some {
        args := args
        initMem := ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
                    activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩
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

/--
Computable end-to-end check that a `RawByteTrace` decodes cleanly under
`rootBody`, `calleeSigs`, and `table` and is consistent with
`mirStatefulTreeWithCallees` (`checkBranches = true`), populating
`rootBody.traitImpls` when `obsTrace.inlinedCallees` is non-empty.
-/
@[reducible]
def checkRawByteTraceWithCalleesFullBounded
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace =>
    checkObservedTraceWithCalleesBounded fuel true rootBody obsTrace
  | none => false

/--
Computable end-to-end check that a `RawByteTrace` decodes cleanly under
`rootBody`, `calleeSigs`, and `table` and is consistent with
`mirObsErasedStatefulTreeWithCallees` (`checkBranches = false`), populating
`rootBody.traitImpls` when `obsTrace.inlinedCallees` is non-empty.
-/
@[reducible]
def checkRawByteTraceWithCalleesObsErasedBounded
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace =>
    checkObservedTraceWithCalleesBounded fuel false rootBody obsTrace
  | none => false

/--
End-to-end soundness of `checkRawByteTraceWithCalleesFullBounded`: when it
returns `true`, the raw byte slices decode to a typed `obsTrace : ObservedTrace`
whose execution reaches a matching `out` along `tr` in
`mirStatefulTreeWithCallees`.
-/
theorem checkRawByteTraceWithCalleesFullBounded_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesFullBounded
        fuel rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out := by
  unfold checkRawByteTraceWithCalleesFullBounded at h_ok
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    rcases checkFullObservedTraceBounded_sound fuel rootBody
        (initMachineStateWithMemoryAndCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        obsTrace.events obsTrace.outcome h_ok with
      ⟨tr, out, h_evs, h_out, h_reach⟩
    exact ⟨obsTrace, tr, out, rfl, h_evs, h_out, h_reach⟩

/--
End-to-end soundness of `checkRawByteTraceWithCalleesObsErasedBounded`: when it
returns `true`, the raw byte slices decode to a typed `obsTrace : ObservedTrace`
whose execution reaches a matching `out` along a `MirCallE` trace `tr` in
`mirObsErasedStatefulTreeWithCallees`.
-/
theorem checkRawByteTraceWithCalleesObsErasedBounded_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesObsErasedBounded
        fuel rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out := by
  unfold checkRawByteTraceWithCalleesObsErasedBounded at h_ok
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    rcases checkObsErasedObservedTraceWithCalleesBounded_sound
        fuel rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees
        obsTrace.events obsTrace.outcome h_ok with
      ⟨tr, out, h_evs, h_out, h_reach⟩
    exact ⟨obsTrace, tr, out, rfl, h_evs, h_out, h_reach⟩

/-! ### Tail-Recursive (`*Fast`) and Policy-Exact `CofixA` (`*Approx`) `RawByteTrace` Checkers

Measured kernel-cost profile (`mirLoopWithOracleCall`, see
`tests/mir/ITreeApproxRunnerTests.lean`): `decodeRawByteTrace` accounts for roughly
13% of a `checkRawByteTrace*Bounded` confirmation and `stepMirState` for most of
the remainder; the checker wrapper itself is negligible, so the tail-recursive
`*Fast` forms below have the same kernel cost as `checkRawByteTrace*Bounded`.
The elaborator's `rfl` pass (`Meta.isDefEq`) dominates instead: the
`checkRawByteTrace*Bounded_sound ... rfl` application that `cargo-anneal` emits
costs about 2.9x the kernel-only check (`k = 32`: `13101` versus `4527` heartbeat
units; a standalone `theorem ... := rfl` on the checker costs `22654`) and needs
more than the default `maxRecDepth` at `k >= 64`. A hypothesis proved
`by decide +kernel` is checked by the kernel alone, with no additional axioms (no
`Lean.ofReduceBool`). The `diagnoseRawByteTrace*Bounded` tag theorem that
`cargo-anneal` emits alongside already performs the same evaluation, and
`diagnoseRawByteTrace*Bounded_tag_ok_sound` turns that `"ok"` tag into the
consistency certificate without a second evaluation.
-/

/-- End-to-end full trace checker over `RawByteTrace` running the tail-recursive
`checkFullMirTraceFast` (equal to `checkRawByteTraceFullBounded`,
`checkRawByteTraceFullBoundedFast_eq`). -/
@[reducible]
def checkRawByteTraceFullBoundedFast
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace =>
    checkFullMirTraceFast fuel rootBody
      (.running (initMachineStateWithMemory rootBody obsTrace.args
        { obsTrace.initMem with callees := obsTrace.inlinedCallees }))
      obsTrace.events obsTrace.outcome
  | none => false

/-- End-to-end branch-erased trace checker over `RawByteTrace` running the
tail-recursive `checkObsErasedMirTraceFast` (equal to
`checkRawByteTraceObsErasedBounded`, `checkRawByteTraceObsErasedBoundedFast_eq`). -/
@[reducible]
def checkRawByteTraceObsErasedBoundedFast
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace =>
    checkObsErasedMirTraceFast fuel rootBody
      (.running (initMachineStateWithMemory rootBody obsTrace.args
        { obsTrace.initMem with callees := obsTrace.inlinedCallees }))
      obsTrace.events obsTrace.outcome
  | none => false

/-- `checkRawByteTraceWithCalleesFullBounded` with the tail-recursive
`checkFullMirTraceFast` (`checkRawByteTraceWithCalleesFullBoundedFast_eq`). -/
@[reducible]
def checkRawByteTraceWithCalleesFullBoundedFast
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace =>
    checkFullMirTraceFast fuel rootBody
      (.running (initMachineStateWithMemoryAndCallees rootBody obsTrace.args
        obsTrace.initMem obsTrace.inlinedCallees))
      obsTrace.events obsTrace.outcome
  | none => false

/-- `checkRawByteTraceWithCalleesObsErasedBounded` with the tail-recursive
`checkObsErasedMirTraceFast` (`checkRawByteTraceWithCalleesObsErasedBoundedFast_eq`). -/
@[reducible]
def checkRawByteTraceWithCalleesObsErasedBoundedFast
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace =>
    checkObsErasedMirTraceFast fuel rootBody
      (.running (initMachineStateWithMemoryAndCallees rootBody obsTrace.args
        obsTrace.initMem obsTrace.inlinedCallees))
      obsTrace.events obsTrace.outcome
  | none => false

theorem checkRawByteTraceFullBoundedFast_eq
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    checkRawByteTraceFullBoundedFast fuel rootBody calleeSigs table rawTrace =
      checkRawByteTraceFullBounded fuel rootBody calleeSigs table rawTrace := by
  unfold checkRawByteTraceFullBoundedFast checkRawByteTraceFullBounded
  cases decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rfl
  | some obsTrace => exact (checkFullObservedTraceBounded_eq_fast _ _ _ _ _).symm

theorem checkRawByteTraceObsErasedBoundedFast_eq
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    checkRawByteTraceObsErasedBoundedFast fuel rootBody calleeSigs table rawTrace =
      checkRawByteTraceObsErasedBounded fuel rootBody calleeSigs table rawTrace := by
  unfold checkRawByteTraceObsErasedBoundedFast checkRawByteTraceObsErasedBounded
  cases decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rfl
  | some obsTrace => exact (checkObsErasedObservedTraceBounded_eq_fast _ _ _ _ _).symm

theorem checkRawByteTraceWithCalleesFullBoundedFast_eq
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    checkRawByteTraceWithCalleesFullBoundedFast fuel rootBody calleeSigs table rawTrace =
      checkRawByteTraceWithCalleesFullBounded fuel rootBody calleeSigs table rawTrace := by
  unfold checkRawByteTraceWithCalleesFullBoundedFast checkRawByteTraceWithCalleesFullBounded
  cases decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rfl
  | some obsTrace => exact (checkFullObservedTraceBounded_eq_fast _ _ _ _ _).symm

theorem checkRawByteTraceWithCalleesObsErasedBoundedFast_eq
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    checkRawByteTraceWithCalleesObsErasedBoundedFast fuel rootBody calleeSigs table rawTrace =
      checkRawByteTraceWithCalleesObsErasedBounded fuel rootBody calleeSigs table rawTrace := by
  unfold checkRawByteTraceWithCalleesObsErasedBoundedFast
    checkRawByteTraceWithCalleesObsErasedBounded
  cases decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rfl
  | some obsTrace => exact (checkObsErasedObservedTraceBounded_eq_fast _ _ _ _ _).symm

/-- Soundness of `checkRawByteTraceFullBoundedFast`. -/
theorem checkRawByteTraceFullBounded_fast_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceFullBoundedFast fuel rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out := by
  rw [checkRawByteTraceFullBoundedFast_eq] at h_ok
  exact checkRawByteTraceFullBounded_sound fuel rootBody calleeSigs table rawTrace h_ok

/-- Soundness of `checkRawByteTraceObsErasedBoundedFast`. -/
theorem checkRawByteTraceObsErasedBounded_fast_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceObsErasedBoundedFast fuel rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out := by
  rw [checkRawByteTraceObsErasedBoundedFast_eq] at h_ok
  exact checkRawByteTraceObsErasedBounded_sound fuel rootBody calleeSigs table rawTrace h_ok

/-- Soundness of `checkRawByteTraceWithCalleesFullBoundedFast`. -/
theorem checkRawByteTraceWithCalleesFullBounded_fast_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesFullBoundedFast
        fuel rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out := by
  rw [checkRawByteTraceWithCalleesFullBoundedFast_eq] at h_ok
  exact checkRawByteTraceWithCalleesFullBounded_sound fuel rootBody calleeSigs table rawTrace h_ok

/-- Soundness of `checkRawByteTraceWithCalleesObsErasedBoundedFast`. -/
theorem checkRawByteTraceWithCalleesObsErasedBounded_fast_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesObsErasedBoundedFast
        fuel rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out := by
  rw [checkRawByteTraceWithCalleesObsErasedBoundedFast_eq] at h_ok
  exact checkRawByteTraceWithCalleesObsErasedBounded_sound
    fuel rootBody calleeSigs table rawTrace h_ok

/--
End-to-end `CofixA`-approximant full trace checker: `checkMirTraceApprox` over
the policy-guarded approximant `mirExecGuardedApprox`. Equal to
`checkRawByteTraceFullBounded` at every fuel (`checkRawByteTraceFullApprox_eq`),
including its rejection of impure (`&mut` / raw-pointer) external calls by call-site
operand type.
-/
@[reducible]
def checkRawByteTraceFullApprox
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace =>
    checkMirTraceApprox
      (mirExecGuardedApprox rootBody fuel
        (.running (initMachineStateWithMemory rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })))
      obsTrace.events obsTrace.outcome
  | none => false

/--
End-to-end `CofixA`-approximant branch-erased trace checker:
`checkMirTraceApprox` over `interpApprox silenceMirObsApprox` (the `CofixA` image
of `ITree.interp silenceMirObs`) applied to the policy-guarded approximant.
Accepts only traces accepted by `checkRawByteTraceObsErasedBounded` at the same
fuel (`checkRawByteTraceObsErasedApprox_imp`); each external call costs one extra
output depth (`.vis` then the handler-return `.tau`).
-/
@[reducible]
def checkRawByteTraceObsErasedApprox
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace =>
    checkMirTraceApprox
      (interpApprox silenceMirObsApprox fuel
        (mirExecGuardedApprox rootBody fuel
          (.running (initMachineStateWithMemory rootBody obsTrace.args
            { obsTrace.initMem with callees := obsTrace.inlinedCallees }))))
      obsTrace.events obsTrace.outcome
  | none => false

/-- `checkRawByteTraceFullApprox` with `initMachineStateWithMemoryAndCallees`
(equal to `checkRawByteTraceWithCalleesFullBounded`). -/
@[reducible]
def checkRawByteTraceWithCalleesFullApprox
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace =>
    checkMirTraceApprox
      (mirExecGuardedApprox rootBody fuel
        (.running (initMachineStateWithMemoryAndCallees rootBody obsTrace.args
          obsTrace.initMem obsTrace.inlinedCallees)))
      obsTrace.events obsTrace.outcome
  | none => false

/-- `checkRawByteTraceObsErasedApprox` with `initMachineStateWithMemoryAndCallees`
(implies `checkRawByteTraceWithCalleesObsErasedBounded`). -/
@[reducible]
def checkRawByteTraceWithCalleesObsErasedApprox
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace =>
    checkMirTraceApprox
      (interpApprox silenceMirObsApprox fuel
        (mirExecGuardedApprox rootBody fuel
          (.running (initMachineStateWithMemoryAndCallees rootBody obsTrace.args
            obsTrace.initMem obsTrace.inlinedCallees))))
      obsTrace.events obsTrace.outcome
  | none => false

/-- `checkRawByteTraceFullApprox` equals `checkRawByteTraceFullBounded` at every fuel. -/
theorem checkRawByteTraceFullApprox_eq
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    checkRawByteTraceFullApprox fuel rootBody calleeSigs table rawTrace =
      checkRawByteTraceFullBounded fuel rootBody calleeSigs table rawTrace := by
  rw [← checkRawByteTraceFullBoundedFast_eq]
  unfold checkRawByteTraceFullApprox checkRawByteTraceFullBoundedFast
  cases decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rfl
  | some obsTrace => exact checkMirTraceApprox_guarded_eq _ _ _ _ _

/-- `checkRawByteTraceWithCalleesFullApprox` equals
`checkRawByteTraceWithCalleesFullBounded` at every fuel. -/
theorem checkRawByteTraceWithCalleesFullApprox_eq
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    checkRawByteTraceWithCalleesFullApprox fuel rootBody calleeSigs table rawTrace =
      checkRawByteTraceWithCalleesFullBounded fuel rootBody calleeSigs table rawTrace := by
  rw [← checkRawByteTraceWithCalleesFullBoundedFast_eq]
  unfold checkRawByteTraceWithCalleesFullApprox checkRawByteTraceWithCalleesFullBoundedFast
  cases decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rfl
  | some obsTrace => exact checkMirTraceApprox_guarded_eq _ _ _ _ _

/-- Every trace accepted by `checkRawByteTraceObsErasedApprox` is accepted by
`checkRawByteTraceObsErasedBounded` at the same fuel. -/
theorem checkRawByteTraceObsErasedApprox_imp
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceObsErasedApprox fuel rootBody calleeSigs table rawTrace = true) :
    checkRawByteTraceObsErasedBounded fuel rootBody calleeSigs table rawTrace = true := by
  rw [← checkRawByteTraceObsErasedBoundedFast_eq]
  unfold checkRawByteTraceObsErasedApprox at h_ok
  unfold checkRawByteTraceObsErasedBoundedFast
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    exact checkMirTraceApprox_interpSilence_guarded_imp _ _ _ _ _ h_ok

/-- Every trace accepted by `checkRawByteTraceWithCalleesObsErasedApprox` is
accepted by `checkRawByteTraceWithCalleesObsErasedBounded` at the same fuel. -/
theorem checkRawByteTraceWithCalleesObsErasedApprox_imp
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesObsErasedApprox
        fuel rootBody calleeSigs table rawTrace = true) :
    checkRawByteTraceWithCalleesObsErasedBounded
      fuel rootBody calleeSigs table rawTrace = true := by
  rw [← checkRawByteTraceWithCalleesObsErasedBoundedFast_eq]
  unfold checkRawByteTraceWithCalleesObsErasedApprox at h_ok
  unfold checkRawByteTraceWithCalleesObsErasedBoundedFast
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    exact checkMirTraceApprox_interpSilence_guarded_imp _ _ _ _ _ h_ok

/-- Soundness of `checkRawByteTraceFullApprox`. -/
theorem checkRawByteTraceFullApprox_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceFullApprox fuel rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out := by
  rw [checkRawByteTraceFullApprox_eq] at h_ok
  exact checkRawByteTraceFullBounded_sound fuel rootBody calleeSigs table rawTrace h_ok

/-- Soundness of `checkRawByteTraceObsErasedApprox`. -/
theorem checkRawByteTraceObsErasedApprox_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceObsErasedApprox fuel rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out :=
  checkRawByteTraceObsErasedBounded_sound fuel rootBody calleeSigs table rawTrace
    (checkRawByteTraceObsErasedApprox_imp fuel rootBody calleeSigs table rawTrace h_ok)

/-- Soundness of `checkRawByteTraceWithCalleesFullApprox`. -/
theorem checkRawByteTraceWithCalleesFullApprox_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesFullApprox fuel rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out := by
  rw [checkRawByteTraceWithCalleesFullApprox_eq] at h_ok
  exact checkRawByteTraceWithCalleesFullBounded_sound fuel rootBody calleeSigs table rawTrace h_ok

/-- Soundness of `checkRawByteTraceWithCalleesObsErasedApprox`. -/
theorem checkRawByteTraceWithCalleesObsErasedApprox_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesObsErasedApprox
        fuel rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out :=
  checkRawByteTraceWithCalleesObsErasedBounded_sound fuel rootBody calleeSigs table rawTrace
    (checkRawByteTraceWithCalleesObsErasedApprox_imp
      fuel rootBody calleeSigs table rawTrace h_ok)

theorem decodeRawObservedEvents_length
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable) :
    ∀ {rawEvs : List RawObservedEvent} {evs : List ObservedEvent},
      decodeRawObservedEvents calleeSigs table rawEvs = some evs →
      evs.length = rawEvs.length
  | [], _, h => by injection h with h'; subst h'; rfl
  | ev :: rest, _, h => by
    unfold decodeRawObservedEvents at h
    cases h₁ : decodeRawObservedEvent calleeSigs table ev with
    | none => rw [h₁] at h; nomatch h
    | some dEv =>
      rw [h₁] at h
      cases h₂ : decodeRawObservedEvents calleeSigs table rest with
      | none => rw [h₂] at h; nomatch h
      | some dRest =>
        rw [h₂] at h
        injection h with h'
        subst h'
        simp [decodeRawObservedEvents_length calleeSigs table h₂]

theorem decodeRawByteTrace_events_length
    {rootBody : CapturedMir} {calleeSigs : List CapturedMir}
    {table : ShadowProvenanceTable} {rawTrace : RawByteTrace}
    {obsTrace : ObservedTrace}
    (h : decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace) :
    obsTrace.events.length = rawTrace.events.length := by
  unfold decodeRawByteTrace at h
  cases h₁ : decodeFnArgsFromRawBytes rootBody table rawTrace.rawArgs with
  | none => rw [h₁] at h; nomatch h
  | some args =>
    rw [h₁] at h
    cases h₂ : decodeRawObservedEvents calleeSigs table rawTrace.events with
    | none => rw [h₂] at h; nomatch h
    | some events =>
      rw [h₂] at h
      cases h₃ : decodeRawObservedOutcome rootBody table rawTrace.outcome with
      | none => rw [h₃] at h; nomatch h
      | some outcome =>
        rw [h₃] at h
        injection h with h'
        subst h'
        exact decodeRawObservedEvents_length calleeSigs table h₂

/-- Fuel monotonicity of `checkRawByteTraceFullBounded`. -/
theorem checkRawByteTraceFullBounded_mono
    {m n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceFullBounded m rootBody calleeSigs table rawTrace = true)
    (hmn : m ≤ n) :
    checkRawByteTraceFullBounded n rootBody calleeSigs table rawTrace = true := by
  rw [← checkRawByteTraceFullBoundedFast_eq] at h_ok ⊢
  unfold checkRawByteTraceFullBoundedFast at h_ok ⊢
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    exact checkFullMirTraceFast_mono rootBody _ obsTrace.events obsTrace.outcome h_ok hmn

/-- Fuel monotonicity of `checkRawByteTraceObsErasedBounded`. -/
theorem checkRawByteTraceObsErasedBounded_mono
    {m n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceObsErasedBounded m rootBody calleeSigs table rawTrace = true)
    (hmn : m ≤ n) :
    checkRawByteTraceObsErasedBounded n rootBody calleeSigs table rawTrace = true := by
  rw [← checkRawByteTraceObsErasedBoundedFast_eq] at h_ok ⊢
  unfold checkRawByteTraceObsErasedBoundedFast at h_ok ⊢
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    exact checkObsErasedMirTraceFast_mono rootBody _ obsTrace.events obsTrace.outcome h_ok hmn

/-- Fuel monotonicity of `checkRawByteTraceFullApprox`. -/
theorem checkRawByteTraceFullApprox_mono
    {m n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceFullApprox m rootBody calleeSigs table rawTrace = true)
    (hmn : m ≤ n) :
    checkRawByteTraceFullApprox n rootBody calleeSigs table rawTrace = true := by
  rw [checkRawByteTraceFullApprox_eq] at h_ok ⊢
  exact checkRawByteTraceFullBounded_mono rootBody calleeSigs table rawTrace h_ok hmn

/-- Fuel monotonicity of `checkRawByteTraceObsErasedApprox`. -/
theorem checkRawByteTraceObsErasedApprox_mono
    {m n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceObsErasedApprox m rootBody calleeSigs table rawTrace = true)
    (hmn : m ≤ n) :
    checkRawByteTraceObsErasedApprox n rootBody calleeSigs table rawTrace = true := by
  unfold checkRawByteTraceObsErasedApprox at h_ok ⊢
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    exact checkMirTraceApprox_interpSilence_guarded_mono
      rootBody _ obsTrace.events obsTrace.outcome h_ok hmn

/-- Fuel monotonicity of `checkRawByteTraceWithCalleesFullBounded`. -/
theorem checkRawByteTraceWithCalleesFullBounded_mono
    {m n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesFullBounded m rootBody calleeSigs table rawTrace = true)
    (hmn : m ≤ n) :
    checkRawByteTraceWithCalleesFullBounded n rootBody calleeSigs table rawTrace = true := by
  rw [← checkRawByteTraceWithCalleesFullBoundedFast_eq] at h_ok ⊢
  unfold checkRawByteTraceWithCalleesFullBoundedFast at h_ok ⊢
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    exact checkFullMirTraceFast_mono rootBody _ obsTrace.events obsTrace.outcome h_ok hmn

/-- Fuel monotonicity of `checkRawByteTraceWithCalleesObsErasedBounded`. -/
theorem checkRawByteTraceWithCalleesObsErasedBounded_mono
    {m n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesObsErasedBounded m rootBody calleeSigs table rawTrace = true)
    (hmn : m ≤ n) :
    checkRawByteTraceWithCalleesObsErasedBounded n rootBody calleeSigs table rawTrace = true := by
  rw [← checkRawByteTraceWithCalleesObsErasedBoundedFast_eq] at h_ok ⊢
  unfold checkRawByteTraceWithCalleesObsErasedBoundedFast at h_ok ⊢
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    exact checkObsErasedMirTraceFast_mono rootBody _ obsTrace.events obsTrace.outcome h_ok hmn

/-- Fuel monotonicity of `checkRawByteTraceWithCalleesFullApprox`. -/
theorem checkRawByteTraceWithCalleesFullApprox_mono
    {m n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesFullApprox m rootBody calleeSigs table rawTrace = true)
    (hmn : m ≤ n) :
    checkRawByteTraceWithCalleesFullApprox n rootBody calleeSigs table rawTrace = true := by
  rw [checkRawByteTraceWithCalleesFullApprox_eq] at h_ok ⊢
  exact checkRawByteTraceWithCalleesFullBounded_mono
    rootBody calleeSigs table rawTrace h_ok hmn

/-- Fuel monotonicity of `checkRawByteTraceWithCalleesObsErasedApprox`. -/
theorem checkRawByteTraceWithCalleesObsErasedApprox_mono
    {m n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesObsErasedApprox m rootBody calleeSigs table rawTrace = true)
    (hmn : m ≤ n) :
    checkRawByteTraceWithCalleesObsErasedApprox n rootBody calleeSigs table rawTrace = true := by
  unfold checkRawByteTraceWithCalleesObsErasedApprox at h_ok ⊢
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    exact checkMirTraceApprox_interpSilence_guarded_mono
      rootBody _ obsTrace.events obsTrace.outcome h_ok hmn

/-- Tight converse to `checkRawByteTraceObsErasedApprox_imp`: every trace accepted by
`checkRawByteTraceObsErasedBounded` at `fuel` is accepted by
`checkRawByteTraceObsErasedApprox` at every depth `n ≥ fuel + rawTrace.events.length`. -/
theorem checkRawByteTraceObsErasedBounded_imp_approx
    {fuel n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceObsErasedBounded fuel rootBody calleeSigs table rawTrace = true)
    (hfn : fuel + rawTrace.events.length ≤ n) :
    checkRawByteTraceObsErasedApprox n rootBody calleeSigs table rawTrace = true := by
  rw [← checkRawByteTraceObsErasedBoundedFast_eq] at h_ok
  unfold checkRawByteTraceObsErasedBoundedFast at h_ok
  unfold checkRawByteTraceObsErasedApprox
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    have hlen := decodeRawByteTrace_events_length h_dec
    exact checkObsErasedMirTraceFast_imp_interpSilence_guarded
      rootBody _ obsTrace.events obsTrace.outcome h_ok (by omega)

/-- Tight converse to `checkRawByteTraceWithCalleesObsErasedApprox_imp`: every trace
accepted by `checkRawByteTraceWithCalleesObsErasedBounded` at `fuel` is accepted by
`checkRawByteTraceWithCalleesObsErasedApprox` at every depth
`n ≥ fuel + rawTrace.events.length`. -/
theorem checkRawByteTraceWithCalleesObsErasedBounded_imp_approx
    {fuel n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesObsErasedBounded
        fuel rootBody calleeSigs table rawTrace = true)
    (hfn : fuel + rawTrace.events.length ≤ n) :
    checkRawByteTraceWithCalleesObsErasedApprox
      n rootBody calleeSigs table rawTrace = true := by
  rw [← checkRawByteTraceWithCalleesObsErasedBoundedFast_eq] at h_ok
  unfold checkRawByteTraceWithCalleesObsErasedBoundedFast at h_ok
  unfold checkRawByteTraceWithCalleesObsErasedApprox
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    have hlen := decodeRawByteTrace_events_length h_dec
    exact checkObsErasedMirTraceFast_imp_interpSilence_guarded
      rootBody _ obsTrace.events obsTrace.outcome h_ok (by omega)

/-- Exact existential equivalence between `checkRawByteTraceObsErasedApprox`
and `checkRawByteTraceObsErasedBounded`: a branch-erased `RawByteTrace` is accepted
at some `CofixA` approximant depth iff it is accepted at some coalgebra step fuel. -/
theorem exists_checkRawByteTraceObsErasedApprox_iff
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (∃ n, checkRawByteTraceObsErasedApprox n rootBody calleeSigs table rawTrace = true) ↔
      (∃ fuel, checkRawByteTraceObsErasedBounded fuel rootBody calleeSigs table rawTrace = true) :=
  ⟨fun ⟨n, h⟩ => ⟨n, checkRawByteTraceObsErasedApprox_imp n rootBody calleeSigs table rawTrace h⟩,
   fun ⟨fuel, h⟩ =>
     ⟨fuel + rawTrace.events.length,
      checkRawByteTraceObsErasedBounded_imp_approx
        rootBody calleeSigs table rawTrace h (Nat.le_refl _)⟩⟩

/-- Exact existential equivalence between `checkRawByteTraceWithCalleesObsErasedApprox`
and `checkRawByteTraceWithCalleesObsErasedBounded`. -/
theorem exists_checkRawByteTraceWithCalleesObsErasedApprox_iff
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (∃ n, checkRawByteTraceWithCalleesObsErasedApprox n rootBody calleeSigs table rawTrace = true) ↔
      (∃ fuel,
        checkRawByteTraceWithCalleesObsErasedBounded fuel rootBody calleeSigs table rawTrace = true) :=
  ⟨fun ⟨n, h⟩ =>
    ⟨n, checkRawByteTraceWithCalleesObsErasedApprox_imp n rootBody calleeSigs table rawTrace h⟩,
   fun ⟨fuel, h⟩ =>
     ⟨fuel + rawTrace.events.length,
      checkRawByteTraceWithCalleesObsErasedBounded_imp_approx
        rootBody calleeSigs table rawTrace h (Nat.le_refl _)⟩⟩

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
Diagnose a decoded `ObservedTrace` against `body` using
`initMachineStateWithMemoryAndCallees body trace.args trace.initMem trace.inlinedCallees`
so that both `trace.inlinedCallees` and `body.traitImpls` are populated when
`trace.inlinedCallees` is non-empty.
-/
@[reducible]
def diagnoseObservedTraceWithCalleesBounded
    (fuel : Nat) (checkBranches : Bool) (body : CapturedMir)
    (trace : ObservedTrace) : TraceReplayDiag :=
  let s := initMachineStateWithMemoryAndCallees body trace.args trace.initMem trace.inlinedCallees
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
           activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩ =>
          diagnoseObservedTraceBounded fuel checkBranches rootBody {
            args := args
            initMem := ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
                        activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩
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

/--
End-to-end diagnostic replay of a `RawByteTrace` using
`diagnoseObservedTraceWithCalleesBounded` so that both `rawTrace.inlinedCallees`
and `rootBody.traitImpls` are populated. Like `diagnoseRawByteTraceBounded` (and
like `decodeRawByteTrace`, which the `checkRawByteTraceWithCallees*Bounded`
checkers replay), initial memory for registered pointer allocations is populated
via `populateShadowPointerMemory`, so the diagnosis accepts exactly the traces the
checkers accept (`diagnoseRawByteTraceWithCalleesFullBounded_isOk`).
-/
@[reducible]
def diagnoseRawByteTraceWithCalleesBounded
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
           activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩ =>
          diagnoseObservedTraceWithCalleesBounded fuel checkBranches rootBody {
            args := args
            initMem := ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
                        activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩
            inlinedCallees := rawTrace.inlinedCallees
            events := events
            outcome := outcome
          }

/--
Convenience wrapper for `diagnoseRawByteTraceWithCalleesBounded` with full
branch and call checking (`checkBranches = true`).
-/
@[reducible]
def diagnoseRawByteTraceWithCalleesFullBounded
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceWithCalleesBounded fuel true rootBody calleeSigs table rawTrace

/--
Convenience wrapper for `diagnoseRawByteTraceWithCalleesBounded` with
branch-erased call-boundary checking (`checkBranches = false`).
-/
@[reducible]
def diagnoseRawByteTraceWithCalleesObsErasedBounded
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceWithCalleesBounded fuel false rootBody calleeSigs table rawTrace

/-! ### Agreement of Diagnostic Replay with the Soundness Checkers

`cargo-anneal` emits, per recorded trace, a `checkRawByteTrace*Bounded_sound`
consistency theorem and a separate `diagnoseRawByteTrace*Bounded` tag theorem,
each confirmed by its own reduction of the same MIR execution. The theorems below
prove that the triage diagnosis accepts (`isOk`, equivalently `tagName = "ok"`)
exactly when the soundness checker accepts, at every fuel, so a confirmed `"ok"`
tag is itself a sound `ReachesRet` certificate
(`diagnoseRawByteTraceFullBounded_tag_ok_sound`,
`diagnoseRawByteTraceObsErasedBounded_tag_ok_sound`).
-/

private theorem listByteEq_eq_true_iff_eq :
    ∀ (xs ys : List UInt8), listByteEq xs ys = true ↔ xs = ys
  | [], [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _ :: _ => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | _ :: _, [] => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | b₁ :: bs₁, b₂ :: bs₂ => by
    have ih := listByteEq_eq_true_iff_eq bs₁ bs₂
    simp only [listByteEq]
    cases hb : Nat.beq b₁.toBitVec.toNat b₂.toBitVec.toNat with
    | false =>
      refine ⟨fun h => (nomatch h), fun h => ?_⟩
      injection h with hb₁ _
      subst hb₁
      rw [Nat.beq_refl] at hb
      nomatch hb
    | true =>
      have hByte : b₁ = b₂ :=
        UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb))
      subst hByte
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [ih.mp h]
      · injection h with _ h'
        exact ih.mpr h'

/-- `Trusted`'s byte-wise `stringEq` coincides with `String` equality (`==`). -/
theorem stringEq_eq_beq (a b : String) : stringEq a b = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq]
  constructor
  · intro h
    unfold stringEq at h
    exact String.toByteArray_inj.mp
      (ByteArray.ext (Array.toList_inj.mp ((listByteEq_eq_true_iff_eq _ _).mp h)))
  · rintro rfl
    unfold stringEq
    exact (listByteEq_eq_true_iff_eq _ _).mpr rfl

/-- `diagnoseCallObservedEvent` accepts exactly the call answers of
`matchCallObservedEvent`. -/
theorem diagnoseCallObservedEvent_toOption
    (req : MirCallReq) (blockIdx : Nat) (obsEv : ObservedEvent) :
    (diagnoseCallObservedEvent req blockIdx obsEv).toOption =
      matchCallObservedEvent req obsEv := by
  cases obsEv with
  | branch _ => rfl
  | extCall defPath args retVal =>
    simp only [diagnoseCallObservedEvent, matchCallObservedEvent, stringEq_eq_beq]
    cases req.defPath == defPath <;> cases valueListEqFuel 16 req.args args <;> rfl
  | extCallPanic defPath args =>
    simp only [diagnoseCallObservedEvent, matchCallObservedEvent, stringEq_eq_beq]
    cases req.defPath == defPath <;> cases valueListEqFuel 16 req.args args <;> rfl
  | extCallAbort defPath args =>
    simp only [diagnoseCallObservedEvent, matchCallObservedEvent, stringEq_eq_beq]
    cases req.defPath == defPath <;> cases valueListEqFuel 16 req.args args <;> rfl

theorem diagnoseCallObservedEvent_error_not_ok
    {req : MirCallReq} {blockIdx : Nat} {obsEv : ObservedEvent} {d : TraceReplayDiag}
    (h : diagnoseCallObservedEvent req blockIdx obsEv = .error d) :
    d.isOk = false := by
  cases obsEv with
  | branch _ => injection h with h; subst h; rfl
  | extCall defPath args retVal =>
    simp only [diagnoseCallObservedEvent] at h
    split at h
    · split at h
      · nomatch h
      · injection h with h; subst h; rfl
    · injection h with h; subst h; rfl
  | extCallPanic defPath args =>
    simp only [diagnoseCallObservedEvent] at h
    split at h
    · split at h
      · nomatch h
      · injection h with h; subst h; rfl
    · injection h with h; subst h; rfl
  | extCallAbort defPath args =>
    simp only [diagnoseCallObservedEvent] at h
    split at h
    · split at h
      · nomatch h
      · injection h with h; subst h; rfl
    · injection h with h; subst h; rfl

private theorem diagnose_cons_ok_isOk (ev : Event MirEffect) (d : TraceReplayDiag) :
    (match d with
     | .ok trRest out => TraceReplayDiag.ok (ev :: trRest) out
     | diag => diag).isOk = d.isOk := by
  cases d <;> rfl

/-- The diagnostic replay with branch checking accepts exactly when
`checkFullMirTraceFast` does, at every fuel. -/
theorem diagnoseMirExecBounded_isOk_full (body : CapturedMir) (fuel : Nat) :
    ∀ (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome),
      (diagnoseMirExecBounded fuel true body st events outcome).isOk =
        checkFullMirTraceFast fuel body st events outcome := by
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ m ih =>
    intro st events outcome
    unfold diagnoseMirExecBounded checkFullMirTraceFast
    cases hs : stepMirState body st with
    | ret out =>
      cases events with
      | nil =>
        dsimp only
        cases checkOutcomeMatches outcome out <;> rfl
      | cons _ _ => rfl
    | tau st' => exact ih st' events outcome
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · cases f; rfl
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent => rfl
          | event tag =>
            cases events with
            | nil => rfl
            | cons ev rest =>
              cases ev with
              | branch expectedTag =>
                dsimp only
                cases Nat.beq tag expectedTag with
                | false => rfl
                | true =>
                  exact (diagnose_cons_ok_isOk
                    ⟨.inr (.inl (.emit (.event tag))), PUnit.unit⟩
                    (diagnoseMirExecBounded m true body (k PUnit.unit) rest outcome)).trans
                    (ih (k PUnit.unit) rest outcome)
              | extCall _ _ _ => rfl
              | extCallPanic _ _ => rfl
              | extCallAbort _ _ => rfl
      · cases callReq with
        | call req =>
          dsimp only
          cases findActiveCallImpurePtrArgIdx? (execStateActiveBody body st)
              (execStateCursor st).1 req with
          | some _ => rfl
          | none =>
            dsimp only
            cases events with
            | nil => rfl
            | cons obsEv rest =>
              dsimp only
              have hmatch := diagnoseCallObservedEvent_toOption req (execStateCursor st).1 obsEv
              cases hd : diagnoseCallObservedEvent req (execStateCursor st).1 obsEv with
              | error d =>
                rw [hd] at hmatch
                rw [← hmatch]
                exact diagnoseCallObservedEvent_error_not_ok hd
              | ok ans =>
                rw [hd] at hmatch
                rw [← hmatch]
                exact (diagnose_cons_ok_isOk ⟨.inr (.inr (.call req)), ans⟩
                  (diagnoseMirExecBounded m true body (k ans) rest outcome)).trans
                  (ih (k ans) rest outcome)

/-- The branch-erased diagnostic replay accepts exactly when
`checkObsErasedMirTraceFast` does, at every fuel. -/
theorem diagnoseMirExecBounded_isOk_obsErased (body : CapturedMir) (fuel : Nat) :
    ∀ (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome),
      (diagnoseMirExecBounded fuel false body st events outcome).isOk =
        checkObsErasedMirTraceFast fuel body st events outcome := by
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ m ih =>
    intro st events outcome
    unfold diagnoseMirExecBounded checkObsErasedMirTraceFast
    cases hs : stepMirState body st with
    | ret out =>
      cases events with
      | nil =>
        dsimp only
        cases checkOutcomeMatches outcome out <;> rfl
      | cons _ _ => rfl
    | tau st' => exact ih st' events outcome
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · cases f; rfl
      · cases obsReq with
        | emit obs => exact ih (k PUnit.unit) events outcome
      · cases callReq with
        | call req =>
          dsimp only
          cases findActiveCallImpurePtrArgIdx? (execStateActiveBody body st)
              (execStateCursor st).1 req with
          | some _ => rfl
          | none =>
            dsimp only
            cases events with
            | nil => rfl
            | cons obsEv rest =>
              dsimp only
              have hmatch := diagnoseCallObservedEvent_toOption req (execStateCursor st).1 obsEv
              cases hd : diagnoseCallObservedEvent req (execStateCursor st).1 obsEv with
              | error d =>
                rw [hd] at hmatch
                rw [← hmatch]
                exact diagnoseCallObservedEvent_error_not_ok hd
              | ok ans =>
                rw [hd] at hmatch
                rw [← hmatch]
                exact (diagnose_cons_ok_isOk ⟨.inr (.inr (.call req)), ans⟩
                  (diagnoseMirExecBounded m false body (k ans) rest outcome)).trans
                  (ih (k ans) rest outcome)

theorem diagnoseDecodeRawArgsAux_toOption
    (layouts : LayoutTable) (table : ShadowProvenanceTable) :
    ∀ (argIdx : Nat) (decls : List LocalDecl) (raws : List (List UInt8)),
      (diagnoseDecodeRawArgsAux layouts table argIdx decls raws).toOption =
        decodeRawArgsByDecls layouts table decls raws
  | argIdx, decls, [] => by
    rw [diagnoseDecodeRawArgsAux.eq_1 layouts table argIdx decls,
      decodeRawArgsByDecls.eq_1 layouts table decls]
    rfl
  | argIdx, decls, raw :: rawRest => by
    cases decls with
    | nil => rfl
    | cons decl declRest =>
      have ih := diagnoseDecodeRawArgsAux_toOption layouts table (argIdx + 1) declRest rawRest
      simp only [diagnoseDecodeRawArgsAux, decodeRawArgsByDecls]
      cases decodeRawValue layouts table decl.ty raw with
      | none => rfl
      | some v =>
        dsimp only
        cases h : diagnoseDecodeRawArgsAux layouts table (argIdx + 1) declRest rawRest with
        | error e =>
          rw [h] at ih
          rw [← ih]
          rfl
        | ok vs =>
          rw [h] at ih
          rw [← ih]
          rfl

theorem diagnoseDecodeFnArgs_toOption
    (body : CapturedMir) (table : ShadowProvenanceTable) (rawArgs : List (List UInt8)) :
    (diagnoseDecodeFnArgs body table rawArgs).toOption =
      decodeFnArgsFromRawBytes body table rawArgs := by
  unfold diagnoseDecodeFnArgs decodeFnArgsFromRawBytes
  cases Nat.beq (length rawArgs) body.argCount with
  | false => rfl
  | true => exact diagnoseDecodeRawArgsAux_toOption _ _ 0 _ _

theorem diagnoseDecodeRawEvent_toOption
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (evIdx : Nat) (ev : RawObservedEvent) :
    (diagnoseDecodeRawEvent calleeSigs table evIdx ev).toOption =
      decodeRawObservedEvent calleeSigs table ev := by
  cases ev with
  | branch _ => rfl
  | extCall defPath rawArgs rawRet =>
    simp only [diagnoseDecodeRawEvent, decodeRawObservedEvent]
    cases findCallee? calleeSigs defPath with
    | none => rfl
    | some sigBody =>
      dsimp only
      cases findCalleeImpurePtrArgIdx? sigBody with
      | some _ => rfl
      | none =>
        dsimp only
        cases decodeFnArgsFromRawBytes sigBody table rawArgs <;>
          cases decodeFnRetFromRawBytes sigBody table rawRet <;> rfl
  | extCallPanic defPath rawArgs =>
    simp only [diagnoseDecodeRawEvent, decodeRawObservedEvent]
    cases findCallee? calleeSigs defPath with
    | none => rfl
    | some sigBody =>
      dsimp only
      cases findCalleeImpurePtrArgIdx? sigBody with
      | some _ => rfl
      | none =>
        dsimp only
        cases decodeFnArgsFromRawBytes sigBody table rawArgs <;> rfl
  | extCallAbort defPath rawArgs =>
    simp only [diagnoseDecodeRawEvent, decodeRawObservedEvent]
    cases findCallee? calleeSigs defPath with
    | none => rfl
    | some sigBody =>
      dsimp only
      cases findCalleeImpurePtrArgIdx? sigBody with
      | some _ => rfl
      | none =>
        dsimp only
        cases decodeFnArgsFromRawBytes sigBody table rawArgs <;> rfl

theorem diagnoseDecodeRawEvent_error_not_ok
    {calleeSigs : List CapturedMir} {table : ShadowProvenanceTable}
    {evIdx : Nat} {ev : RawObservedEvent} {d : TraceReplayDiag}
    (h : diagnoseDecodeRawEvent calleeSigs table evIdx ev = .error d) :
    d.isOk = false := by
  cases ev with
  | branch _ => nomatch h
  | extCall defPath rawArgs rawRet =>
    simp only [diagnoseDecodeRawEvent] at h
    split at h
    · split at h
      · injection h with h; subst h; rfl
      · split at h
        · nomatch h
        · injection h with h; subst h; rfl
    · injection h with h; subst h; rfl
  | extCallPanic defPath rawArgs =>
    simp only [diagnoseDecodeRawEvent] at h
    split at h
    · split at h
      · injection h with h; subst h; rfl
      · split at h
        · nomatch h
        · injection h with h; subst h; rfl
    · injection h with h; subst h; rfl
  | extCallAbort defPath rawArgs =>
    simp only [diagnoseDecodeRawEvent] at h
    split at h
    · split at h
      · injection h with h; subst h; rfl
      · split at h
        · nomatch h
        · injection h with h; subst h; rfl
    · injection h with h; subst h; rfl

theorem diagnoseDecodeRawEventsAux_toOption
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable) :
    ∀ (evIdx : Nat) (evs : List RawObservedEvent),
      (diagnoseDecodeRawEventsAux calleeSigs table evIdx evs).toOption =
        decodeRawObservedEvents calleeSigs table evs
  | _, [] => rfl
  | evIdx, ev :: rest => by
    have ih := diagnoseDecodeRawEventsAux_toOption calleeSigs table (evIdx + 1) rest
    have hev := diagnoseDecodeRawEvent_toOption calleeSigs table evIdx ev
    simp only [diagnoseDecodeRawEventsAux, decodeRawObservedEvents]
    cases hd : diagnoseDecodeRawEvent calleeSigs table evIdx ev with
    | error d =>
      rw [hd] at hev
      rw [← hev]
      rfl
    | ok dEv =>
      rw [hd] at hev
      rw [← hev]
      dsimp only
      cases hr : diagnoseDecodeRawEventsAux calleeSigs table (evIdx + 1) rest with
      | error d =>
        rw [hr] at ih
        rw [← ih]
        rfl
      | ok dRest =>
        rw [hr] at ih
        rw [← ih]
        rfl

theorem diagnoseDecodeRawEventsAux_error_not_ok
    {calleeSigs : List CapturedMir} {table : ShadowProvenanceTable} :
    ∀ {evIdx : Nat} {evs : List RawObservedEvent} {d : TraceReplayDiag},
      diagnoseDecodeRawEventsAux calleeSigs table evIdx evs = .error d →
      d.isOk = false
  | _, [], _, h => nomatch h
  | evIdx, ev :: rest, d, h => by
    simp only [diagnoseDecodeRawEventsAux] at h
    cases hd : diagnoseDecodeRawEvent calleeSigs table evIdx ev with
    | error d' =>
      rw [hd] at h
      injection h with h
      subst h
      exact diagnoseDecodeRawEvent_error_not_ok hd
    | ok dEv =>
      rw [hd] at h
      dsimp only at h
      cases hr : diagnoseDecodeRawEventsAux calleeSigs table (evIdx + 1) rest with
      | error d' =>
        rw [hr] at h
        injection h with h
        subst h
        exact diagnoseDecodeRawEventsAux_error_not_ok hr
      | ok dRest =>
        rw [hr] at h
        nomatch h

private theorem diagnoseRawByteTraceBounded_isOk_aux
    (fuel : Nat) (checkBranches : Bool) (rootBody : CapturedMir)
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceBounded fuel checkBranches rootBody calleeSigs table rawTrace).isOk =
      match decodeRawByteTrace rootBody calleeSigs table rawTrace with
      | some obsTrace =>
        (diagnoseObservedTraceBounded fuel checkBranches rootBody obsTrace).isOk
      | none => false := by
  unfold diagnoseRawByteTraceBounded decodeRawByteTrace
  rw [← diagnoseDecodeFnArgs_toOption, ← diagnoseDecodeRawEventsAux_toOption calleeSigs table 0]
  cases hargs : diagnoseDecodeFnArgs rootBody table rawTrace.rawArgs with
  | error _ => rfl
  | ok args =>
    cases hevs : diagnoseDecodeRawEventsAux calleeSigs table 0 rawTrace.events with
    | error d => exact diagnoseDecodeRawEventsAux_error_not_ok hevs
    | ok events =>
      cases decodeRawObservedOutcome rootBody table rawTrace.outcome with
      | none => rfl
      | some outcome => rfl

/-- `diagnoseRawByteTraceFullBounded` accepts exactly when
`checkRawByteTraceFullBounded` does, at every fuel. -/
theorem diagnoseRawByteTraceFullBounded_isOk
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceFullBounded fuel rootBody calleeSigs table rawTrace).isOk =
      checkRawByteTraceFullBounded fuel rootBody calleeSigs table rawTrace := by
  unfold diagnoseRawByteTraceFullBounded
  rw [diagnoseRawByteTraceBounded_isOk_aux, ← checkRawByteTraceFullBoundedFast_eq]
  unfold checkRawByteTraceFullBoundedFast
  cases decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rfl
  | some obsTrace => exact diagnoseMirExecBounded_isOk_full rootBody fuel _ _ _

/-- `diagnoseRawByteTraceObsErasedBounded` accepts exactly when
`checkRawByteTraceObsErasedBounded` does, at every fuel. -/
theorem diagnoseRawByteTraceObsErasedBounded_isOk
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceObsErasedBounded fuel rootBody calleeSigs table rawTrace).isOk =
      checkRawByteTraceObsErasedBounded fuel rootBody calleeSigs table rawTrace := by
  unfold diagnoseRawByteTraceObsErasedBounded
  rw [diagnoseRawByteTraceBounded_isOk_aux, ← checkRawByteTraceObsErasedBoundedFast_eq]
  unfold checkRawByteTraceObsErasedBoundedFast
  cases decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rfl
  | some obsTrace => exact diagnoseMirExecBounded_isOk_obsErased rootBody fuel _ _ _

theorem TraceReplayDiag.isOk_of_tagName_eq_ok {d : TraceReplayDiag}
    (h : d.tagName = "ok") : d.isOk = true := by
  cases d <;> first | rfl | (simp only [TraceReplayDiag.tagName] at h; contradiction)

/-- A confirmed `"ok"` tag of `diagnoseRawByteTraceFullBounded` (the theorem
`cargo-anneal` emits for every trace) is a sound `ReachesRet` certificate for
`mirStatefulTree`, with no second evaluation of the execution. -/
theorem diagnoseRawByteTraceFullBounded_tag_ok_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_tag :
      (diagnoseRawByteTraceFullBounded fuel rootBody calleeSigs table rawTrace).tagName = "ok") :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out := by
  have h_ok := TraceReplayDiag.isOk_of_tagName_eq_ok h_tag
  rw [diagnoseRawByteTraceFullBounded_isOk] at h_ok
  exact checkRawByteTraceFullBounded_sound fuel rootBody calleeSigs table rawTrace h_ok

/-- A confirmed `"ok"` tag of `diagnoseRawByteTraceObsErasedBounded` is a sound
`ReachesRet` certificate for `mirObsErasedStatefulTree`. -/
theorem diagnoseRawByteTraceObsErasedBounded_tag_ok_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_tag :
      (diagnoseRawByteTraceObsErasedBounded fuel rootBody calleeSigs table rawTrace).tagName =
        "ok") :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out := by
  have h_ok := TraceReplayDiag.isOk_of_tagName_eq_ok h_tag
  rw [diagnoseRawByteTraceObsErasedBounded_isOk] at h_ok
  exact checkRawByteTraceObsErasedBounded_sound fuel rootBody calleeSigs table rawTrace h_ok

private theorem diagnoseRawByteTraceWithCalleesBounded_isOk_aux
    (fuel : Nat) (checkBranches : Bool) (rootBody : CapturedMir)
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceWithCalleesBounded
        fuel checkBranches rootBody calleeSigs table rawTrace).isOk =
      match decodeRawByteTrace rootBody calleeSigs table rawTrace with
      | some obsTrace =>
        (diagnoseObservedTraceWithCalleesBounded fuel checkBranches rootBody obsTrace).isOk
      | none => false := by
  unfold diagnoseRawByteTraceWithCalleesBounded decodeRawByteTrace
  rw [← diagnoseDecodeFnArgs_toOption, ← diagnoseDecodeRawEventsAux_toOption calleeSigs table 0]
  cases hargs : diagnoseDecodeFnArgs rootBody table rawTrace.rawArgs with
  | error _ => rfl
  | ok args =>
    cases hevs : diagnoseDecodeRawEventsAux calleeSigs table 0 rawTrace.events with
    | error d => exact diagnoseDecodeRawEventsAux_error_not_ok hevs
    | ok events =>
      cases decodeRawObservedOutcome rootBody table rawTrace.outcome with
      | none => rfl
      | some outcome => rfl

/-- `diagnoseRawByteTraceWithCalleesFullBounded` accepts exactly when
`checkRawByteTraceWithCalleesFullBounded` does, at every fuel. -/
theorem diagnoseRawByteTraceWithCalleesFullBounded_isOk
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceWithCalleesFullBounded fuel rootBody calleeSigs table rawTrace).isOk =
      checkRawByteTraceWithCalleesFullBounded fuel rootBody calleeSigs table rawTrace := by
  unfold diagnoseRawByteTraceWithCalleesFullBounded
  rw [diagnoseRawByteTraceWithCalleesBounded_isOk_aux,
    ← checkRawByteTraceWithCalleesFullBoundedFast_eq]
  unfold checkRawByteTraceWithCalleesFullBoundedFast
  cases decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rfl
  | some obsTrace => exact diagnoseMirExecBounded_isOk_full rootBody fuel _ _ _

/-- `diagnoseRawByteTraceWithCalleesObsErasedBounded` accepts exactly when
`checkRawByteTraceWithCalleesObsErasedBounded` does, at every fuel. -/
theorem diagnoseRawByteTraceWithCalleesObsErasedBounded_isOk
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceWithCalleesObsErasedBounded
        fuel rootBody calleeSigs table rawTrace).isOk =
      checkRawByteTraceWithCalleesObsErasedBounded fuel rootBody calleeSigs table rawTrace := by
  unfold diagnoseRawByteTraceWithCalleesObsErasedBounded
  rw [diagnoseRawByteTraceWithCalleesBounded_isOk_aux,
    ← checkRawByteTraceWithCalleesObsErasedBoundedFast_eq]
  unfold checkRawByteTraceWithCalleesObsErasedBoundedFast
  cases decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rfl
  | some obsTrace => exact diagnoseMirExecBounded_isOk_obsErased rootBody fuel _ _ _

/-- A confirmed `"ok"` tag of `diagnoseRawByteTraceWithCalleesFullBounded` is a
sound `ReachesRet` certificate for `mirStatefulTreeWithCallees`. -/
theorem diagnoseRawByteTraceWithCalleesFullBounded_tag_ok_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_tag :
      (diagnoseRawByteTraceWithCalleesFullBounded
        fuel rootBody calleeSigs table rawTrace).tagName = "ok") :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out := by
  have h_ok := TraceReplayDiag.isOk_of_tagName_eq_ok h_tag
  rw [diagnoseRawByteTraceWithCalleesFullBounded_isOk] at h_ok
  exact checkRawByteTraceWithCalleesFullBounded_sound
    fuel rootBody calleeSigs table rawTrace h_ok

/-- A confirmed `"ok"` tag of `diagnoseRawByteTraceWithCalleesObsErasedBounded`
is a sound `ReachesRet` certificate for `mirObsErasedStatefulTreeWithCallees`. -/
theorem diagnoseRawByteTraceWithCalleesObsErasedBounded_tag_ok_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_tag :
      (diagnoseRawByteTraceWithCalleesObsErasedBounded
        fuel rootBody calleeSigs table rawTrace).tagName = "ok") :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out := by
  have h_ok := TraceReplayDiag.isOk_of_tagName_eq_ok h_tag
  rw [diagnoseRawByteTraceWithCalleesObsErasedBounded_isOk] at h_ok
  exact checkRawByteTraceWithCalleesObsErasedBounded_sound
    fuel rootBody calleeSigs table rawTrace h_ok

theorem TraceReplayDiag.tagName_eq_ok_of_isOk {d : TraceReplayDiag}
    (h : d.isOk = true) : d.tagName = "ok" := by
  cases d <;> first | rfl | nomatch h

/-- Fuel monotonicity of `diagnoseRawByteTraceFullBounded`'s `"ok"` tag. -/
theorem diagnoseRawByteTraceFullBounded_tag_ok_mono
    {m n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_tag :
      (diagnoseRawByteTraceFullBounded m rootBody calleeSigs table rawTrace).tagName = "ok")
    (hmn : m ≤ n) :
    (diagnoseRawByteTraceFullBounded n rootBody calleeSigs table rawTrace).tagName = "ok" := by
  apply TraceReplayDiag.tagName_eq_ok_of_isOk
  rw [diagnoseRawByteTraceFullBounded_isOk]
  have h_ok := TraceReplayDiag.isOk_of_tagName_eq_ok h_tag
  rw [diagnoseRawByteTraceFullBounded_isOk] at h_ok
  exact checkRawByteTraceFullBounded_mono rootBody calleeSigs table rawTrace h_ok hmn

/-- Fuel monotonicity of `diagnoseRawByteTraceObsErasedBounded`'s `"ok"` tag. -/
theorem diagnoseRawByteTraceObsErasedBounded_tag_ok_mono
    {m n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_tag :
      (diagnoseRawByteTraceObsErasedBounded m rootBody calleeSigs table rawTrace).tagName = "ok")
    (hmn : m ≤ n) :
    (diagnoseRawByteTraceObsErasedBounded n rootBody calleeSigs table rawTrace).tagName = "ok" := by
  apply TraceReplayDiag.tagName_eq_ok_of_isOk
  rw [diagnoseRawByteTraceObsErasedBounded_isOk]
  have h_ok := TraceReplayDiag.isOk_of_tagName_eq_ok h_tag
  rw [diagnoseRawByteTraceObsErasedBounded_isOk] at h_ok
  exact checkRawByteTraceObsErasedBounded_mono rootBody calleeSigs table rawTrace h_ok hmn

/-! ### Tail-Recursive Allocation-Free Diagnostic Replay (`diagnose*BoundedFast`)

`diagnoseMirExecBounded` matches on the recursive `TraceReplayDiag` at every
`.vis (.emit (.event _))` and `.vis (.call _)` step to prepend the event onto
`.ok trRest out`. When `cargo-anneal` runs Stage 1 `#eval` probes (which are
strict call-by-value and format `reprStr diag`) or Stage 2 `.tagName = "ok"`
confirmations, the `tr : List (Event MirEffect)` field inside `.ok tr out` is
never inspected.

`diagnoseMirExecBoundedFast` (and its `ObservedTrace` / `RawByteTrace` wrappers)
is tail-recursive across all transitions (`.tau`, `.vis (.emit ...)`, and
`.vis (.call ...)`), uses `elimMirVis` to avoid index-unifying `Eq.ndrec` casts
on `MirEffect.I`, returns `.ok [] actualOut` on success without allocating
intermediate `Event MirEffect` lists, and returns the exact same failure
`TraceReplayDiag` on every non-`ok` arm (`diagnoseMirExecBoundedFast_eq`,
`diagnoseRawByteTraceBoundedFast_tagName`,
`diagnoseRawByteTraceBoundedFast_eq_of_not_isOk`).
-/

/-- Erase the reconstructed `List (Event MirEffect)` witness inside
`TraceReplayDiag.ok tr out` while leaving every failure constructor unchanged. -/
@[reducible]
def TraceReplayDiag.eraseTrace : TraceReplayDiag → TraceReplayDiag
  | .ok _ out => .ok [] out
  | diag => diag

@[simp]
theorem TraceReplayDiag.isOk_eraseTrace (d : TraceReplayDiag) :
    d.eraseTrace.isOk = d.isOk := by
  cases d <;> rfl

@[simp]
theorem TraceReplayDiag.tagName_eraseTrace (d : TraceReplayDiag) :
    d.eraseTrace.tagName = d.tagName := by
  cases d <;> rfl

theorem TraceReplayDiag.eraseTrace_eq_self_of_not_isOk {d : TraceReplayDiag}
    (h : d.isOk = false) : d.eraseTrace = d := by
  cases d <;> first | rfl | nomatch h

/-- Tail-recursive allocation-free diagnostic replay over `stepMirState body`
parameterized by `checkBranches : Bool`. Returns `.ok [] actualOut` on exact
replay and the exact same `TraceReplayDiag` failure constructor as
`diagnoseMirExecBounded` on any divergence. -/
@[reducible]
def diagnoseMirExecBoundedFast
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
      diagnoseMirExecBoundedFast fuel' checkBranches body st' events outcome
    | .vis i k =>
      elimMirVis
        (fun kind _ =>
          let cur := execStateCursor st
          .stepFaulted kind cur.1 cur.2)
        (fun k' =>
          match checkBranches with
          | false =>
            diagnoseMirExecBoundedFast fuel' false body (k' PUnit.unit) events outcome
          | true =>
            let cur := execStateCursor st
            .stepFaulted .unsupported cur.1 cur.2)
        (fun actualTag k' =>
          match checkBranches with
          | false =>
            diagnoseMirExecBoundedFast fuel' false body (k' PUnit.unit) events outcome
          | true =>
            let cur := execStateCursor st
            match events with
            | .branch expectedTag :: rest =>
              if Nat.beq actualTag expectedTag then
                diagnoseMirExecBoundedFast fuel' true body (k' PUnit.unit) rest outcome
              else
                .branchTagMismatch actualTag expectedTag cur.1
            | _ =>
              .branchTagMismatch actualTag 0 cur.1)
        (fun req k' =>
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
                diagnoseMirExecBoundedFast fuel' checkBranches body (k' ans) rest outcome)
        i k

/-- `diagnoseMirExecBoundedFast` computes the exact trace-erased projection
`TraceReplayDiag.eraseTrace` of `diagnoseMirExecBounded`. -/
theorem diagnoseMirExecBoundedFast_eq
    (fuel : Nat) (checkBranches : Bool) (body : CapturedMir) :
    ∀ (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome),
      diagnoseMirExecBoundedFast fuel checkBranches body st events outcome =
        (diagnoseMirExecBounded fuel checkBranches body st events outcome).eraseTrace := by
  induction fuel generalizing checkBranches with
  | zero => intro _ _ _; rfl
  | succ fuel' ih =>
    intro st events outcome
    unfold diagnoseMirExecBoundedFast diagnoseMirExecBounded
    cases stepMirState body st with
    | ret actualOut =>
      cases events with
      | nil =>
        dsimp only
        cases checkOutcomeMatches outcome actualOut <;> rfl
      | cons _ _ => rfl
    | tau st' => exact ih checkBranches st' events outcome
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · cases f; rfl
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent =>
            cases checkBranches with
            | false => exact ih false (k PUnit.unit) events outcome
            | true => rfl
          | event actualTag =>
            cases checkBranches with
            | false => exact ih false (k PUnit.unit) events outcome
            | true =>
              dsimp only [elimMirVis]
              cases events with
              | nil => rfl
              | cons ev rest =>
                cases ev with
                | branch expectedTag =>
                  dsimp only
                  cases Nat.beq actualTag expectedTag with
                  | false => rfl
                  | true =>
                    rw [ih true (k PUnit.unit) rest outcome]
                    cases diagnoseMirExecBounded fuel' true body (k PUnit.unit) rest outcome <;> rfl
                | extCall _ _ _ => rfl
                | extCallPanic _ _ => rfl
                | extCallAbort _ _ => rfl
      · cases callReq with
        | call req =>
          dsimp only [elimMirVis]
          cases findActiveCallImpurePtrArgIdx? (execStateActiveBody body st)
              (execStateCursor st).1 req with
          | some _ => rfl
          | none =>
            dsimp only
            cases events with
            | nil => rfl
            | cons obsEv rest =>
              dsimp only
              cases hd : diagnoseCallObservedEvent req (execStateCursor st).1 obsEv with
              | error d =>
                have hnot := diagnoseCallObservedEvent_error_not_ok hd
                exact (TraceReplayDiag.eraseTrace_eq_self_of_not_isOk hnot).symm
              | ok ans =>
                change diagnoseMirExecBoundedFast fuel' checkBranches body (k ans) rest outcome =
                  (match diagnoseMirExecBounded fuel' checkBranches body (k ans) rest outcome with
                   | .ok trRest out =>
                     TraceReplayDiag.ok (⟨.inr (.inr (.call req)), ans⟩ :: trRest) out
                   | diag => diag).eraseTrace
                rw [ih checkBranches (k ans) rest outcome]
                cases diagnoseMirExecBounded fuel' checkBranches body (k ans) rest outcome <;> rfl

theorem diagnoseMirExecBoundedFast_isOk
    (fuel : Nat) (checkBranches : Bool) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    (diagnoseMirExecBoundedFast fuel checkBranches body st events outcome).isOk =
      (diagnoseMirExecBounded fuel checkBranches body st events outcome).isOk := by
  rw [diagnoseMirExecBoundedFast_eq, TraceReplayDiag.isOk_eraseTrace]

theorem diagnoseMirExecBoundedFast_tagName
    (fuel : Nat) (checkBranches : Bool) (body : CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    (diagnoseMirExecBoundedFast fuel checkBranches body st events outcome).tagName =
      (diagnoseMirExecBounded fuel checkBranches body st events outcome).tagName := by
  rw [diagnoseMirExecBoundedFast_eq, TraceReplayDiag.tagName_eraseTrace]

/-- Tail-recursive diagnostic replay of a decoded `ObservedTrace`. -/
@[reducible]
def diagnoseObservedTraceBoundedFast
    (fuel : Nat) (checkBranches : Bool) (body : CapturedMir)
    (trace : ObservedTrace) : TraceReplayDiag :=
  let mem := { trace.initMem with callees := trace.inlinedCallees }
  let s := initMachineStateWithMemory body trace.args mem
  diagnoseMirExecBoundedFast fuel checkBranches body (.running s) trace.events trace.outcome

/-- Tail-recursive diagnostic replay of a decoded `ObservedTrace` with `callees`. -/
@[reducible]
def diagnoseObservedTraceWithCalleesBoundedFast
    (fuel : Nat) (checkBranches : Bool) (body : CapturedMir)
    (trace : ObservedTrace) : TraceReplayDiag :=
  let s := initMachineStateWithMemoryAndCallees body trace.args trace.initMem trace.inlinedCallees
  diagnoseMirExecBoundedFast fuel checkBranches body (.running s) trace.events trace.outcome

/-- Tail-recursive allocation-free end-to-end diagnostic replay of a `RawByteTrace`. -/
@[reducible]
def diagnoseRawByteTraceBoundedFast
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
           activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩ =>
          diagnoseObservedTraceBoundedFast fuel checkBranches rootBody {
            args := args
            initMem := ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
                        activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩
            inlinedCallees := rawTrace.inlinedCallees
            events := events
            outcome := outcome
          }

@[reducible]
def diagnoseRawByteTraceFullBoundedFast
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceBoundedFast fuel true rootBody calleeSigs table rawTrace

@[reducible]
def diagnoseRawByteTraceObsErasedBoundedFast
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceBoundedFast fuel false rootBody calleeSigs table rawTrace

@[reducible]
def diagnoseRawByteTraceWithCalleesBoundedFast
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
           activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩ =>
          diagnoseObservedTraceWithCalleesBoundedFast fuel checkBranches rootBody {
            args := args
            initMem := ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
                        activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩
            inlinedCallees := rawTrace.inlinedCallees
            events := events
            outcome := outcome
          }

@[reducible]
def diagnoseRawByteTraceWithCalleesFullBoundedFast
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceWithCalleesBoundedFast fuel true rootBody calleeSigs table rawTrace

@[reducible]
def diagnoseRawByteTraceWithCalleesObsErasedBoundedFast
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceWithCalleesBoundedFast fuel false rootBody calleeSigs table rawTrace

theorem diagnoseRawByteTraceBoundedFast_eq
    (fuel : Nat) (checkBranches : Bool) (rootBody : CapturedMir)
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (rawTrace : RawByteTrace) :
    diagnoseRawByteTraceBoundedFast fuel checkBranches rootBody calleeSigs table rawTrace =
      (diagnoseRawByteTraceBounded fuel checkBranches rootBody calleeSigs table rawTrace).eraseTrace := by
  unfold diagnoseRawByteTraceBoundedFast diagnoseRawByteTraceBounded
  cases diagnoseDecodeFnArgs rootBody table rawTrace.rawArgs with
  | error _ => rfl
  | ok args =>
    cases hevs : diagnoseDecodeRawEventsAux calleeSigs table 0 rawTrace.events with
    | error d =>
      exact (TraceReplayDiag.eraseTrace_eq_self_of_not_isOk
        (diagnoseDecodeRawEventsAux_error_not_ok hevs)).symm
    | ok events =>
      cases decodeRawObservedOutcome rootBody table rawTrace.outcome with
      | none => rfl
      | some outcome =>
        exact diagnoseMirExecBoundedFast_eq fuel checkBranches rootBody _ _ _

theorem diagnoseRawByteTraceBoundedFast_isOk
    (fuel : Nat) (checkBranches : Bool) (rootBody : CapturedMir)
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceBoundedFast fuel checkBranches rootBody calleeSigs table rawTrace).isOk =
      (diagnoseRawByteTraceBounded fuel checkBranches rootBody calleeSigs table rawTrace).isOk := by
  rw [diagnoseRawByteTraceBoundedFast_eq, TraceReplayDiag.isOk_eraseTrace]

theorem diagnoseRawByteTraceBoundedFast_tagName
    (fuel : Nat) (checkBranches : Bool) (rootBody : CapturedMir)
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceBoundedFast fuel checkBranches rootBody calleeSigs table rawTrace).tagName =
      (diagnoseRawByteTraceBounded fuel checkBranches rootBody calleeSigs table rawTrace).tagName := by
  rw [diagnoseRawByteTraceBoundedFast_eq, TraceReplayDiag.tagName_eraseTrace]

theorem diagnoseRawByteTraceFullBoundedFast_tagName
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceFullBoundedFast fuel rootBody calleeSigs table rawTrace).tagName =
      (diagnoseRawByteTraceFullBounded fuel rootBody calleeSigs table rawTrace).tagName :=
  diagnoseRawByteTraceBoundedFast_tagName fuel true rootBody calleeSigs table rawTrace

theorem diagnoseRawByteTraceObsErasedBoundedFast_tagName
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceObsErasedBoundedFast fuel rootBody calleeSigs table rawTrace).tagName =
      (diagnoseRawByteTraceObsErasedBounded fuel rootBody calleeSigs table rawTrace).tagName :=
  diagnoseRawByteTraceBoundedFast_tagName fuel false rootBody calleeSigs table rawTrace

/-- On any diverging trace (`isOk = false`), `diagnoseRawByteTraceBoundedFast`
returns the exact same `TraceReplayDiag` value as `diagnoseRawByteTraceBounded`. -/
theorem diagnoseRawByteTraceBoundedFast_eq_of_not_isOk
    {fuel : Nat} {checkBranches : Bool} {rootBody : CapturedMir}
    {calleeSigs : List CapturedMir} {table : ShadowProvenanceTable}
    {rawTrace : RawByteTrace}
    (h : (diagnoseRawByteTraceBounded fuel checkBranches rootBody calleeSigs table rawTrace).isOk =
      false) :
    diagnoseRawByteTraceBoundedFast fuel checkBranches rootBody calleeSigs table rawTrace =
      diagnoseRawByteTraceBounded fuel checkBranches rootBody calleeSigs table rawTrace := by
  rw [diagnoseRawByteTraceBoundedFast_eq]
  exact TraceReplayDiag.eraseTrace_eq_self_of_not_isOk h

/-! ### Branch Erasure: Full Acceptance Implies Branch-Erased Acceptance

`cargo-anneal` emits, for each `checkBranches = true` trace, a second
branch-erased consistency theorem over the same recording with its `.branch`
events removed, confirmed by a second evaluation. The theorems below show that
full acceptance already implies branch-erased acceptance of the erased event list
on both the `CofixA` approximant walker (`checkMirTraceApprox_imp_obsErased`) and
the coalgebra-direct checker (`checkFullMirTraceFast_imp_obsErased`), so that
certificate follows from the full one without re-running the MIR execution
(`checkRawByteTraceObsErasedBounded_of_full`,
`diagnoseRawByteTraceFullBounded_tag_ok_obsErased_sound`).
-/

/-- Remove `.branch` observations from an observed event list. -/
@[reducible]
def eraseBranchEvents : List ObservedEvent → List ObservedEvent
  | [] => []
  | .branch _ :: rest => eraseBranchEvents rest
  | .extCall defPath args retVal :: rest =>
    .extCall defPath args retVal :: eraseBranchEvents rest
  | .extCallPanic defPath args :: rest => .extCallPanic defPath args :: eraseBranchEvents rest
  | .extCallAbort defPath args :: rest => .extCallAbort defPath args :: eraseBranchEvents rest

/-- Remove `.branch` observations from a raw recorded event list. -/
@[reducible]
def eraseRawBranchEvents : List RawObservedEvent → List RawObservedEvent
  | [] => []
  | .branch _ :: rest => eraseRawBranchEvents rest
  | .extCall defPath rawArgs rawRet :: rest =>
    .extCall defPath rawArgs rawRet :: eraseRawBranchEvents rest
  | .extCallPanic defPath rawArgs :: rest =>
    .extCallPanic defPath rawArgs :: eraseRawBranchEvents rest
  | .extCallAbort defPath rawArgs :: rest =>
    .extCallAbort defPath rawArgs :: eraseRawBranchEvents rest

/-- On any finite `CofixA` approximant `a`, full trace acceptance by
`checkMirTraceApprox` implies branch-erased acceptance by
`checkMirObsErasedTraceApprox` on `eraseBranchEvents events`. -/
theorem checkMirTraceApprox_imp_obsErased
    {n : Nat} {a : CofixA MirEffect MirOutcome n}
    {events : List ObservedEvent} {outcome : ObservedOutcome}
    (h : checkMirTraceApprox a events outcome = true) :
    checkMirObsErasedTraceApprox a (eraseBranchEvents events) outcome = true := by
  induction a generalizing events with
  | zero => nomatch h
  | ret out =>
    cases events with
    | nil => exact h
    | cons _ _ => nomatch h
  | tau t' ih => exact ih h
  | vis i k ih =>
    rcases i with f | (obsReq | callReq)
    · cases f; nomatch h
    · cases obsReq with
      | emit obs =>
        cases obs with
        | silent => nomatch h
        | event tag =>
          cases events with
          | nil => nomatch h
          | cons ev rest =>
            cases ev with
            | branch expectedTag =>
              change
                (if Nat.beq tag expectedTag then
                  checkMirTraceApprox (k PUnit.unit) rest outcome
                else false) = true at h
              revert h
              cases Nat.beq tag expectedTag <;> intro h
              · nomatch h
              · exact ih PUnit.unit (events := rest) h
            | extCall _ _ _ => nomatch h
            | extCallPanic _ _ => nomatch h
            | extCallAbort _ _ => nomatch h
    · cases callReq with
      | call req =>
        revert h
        unfold checkMirTraceApprox checkMirObsErasedTraceApprox elimMirVis
        dsimp only
        cases findCallReqImpurePtrArgIdx? req with
        | some _ => intro h; nomatch h
        | none =>
          cases events with
          | nil => intro h; nomatch h
          | cons obsEv rest =>
            cases obsEv with
            | branch _ => intro h; nomatch h
            | extCall defPath args retVal =>
              dsimp only
              cases matchCallObservedEvent req (.extCall defPath args retVal) with
              | none => intro h; nomatch h
              | some ans =>
                intro h
                exact ih ans (events := rest) h
            | extCallPanic defPath args =>
              dsimp only
              cases matchCallObservedEvent req (.extCallPanic defPath args) with
              | none => intro h; nomatch h
              | some ans =>
                intro h
                exact ih ans (events := rest) h
            | extCallAbort defPath args =>
              dsimp only
              cases matchCallObservedEvent req (.extCallAbort defPath args) with
              | none => intro h; nomatch h
              | some ans =>
                intro h
                exact ih ans (events := rest) h

/-- Full replay acceptance implies branch-erased replay acceptance of the erased
event list at the same fuel (immediate corollary of `checkMirTraceApprox_imp_obsErased`
via `checkMirTraceApprox_guarded_eq` and `checkMirObsErasedTraceApprox_guarded_eq`). -/
theorem checkFullMirTraceFast_imp_obsErased (body : CapturedMir) (fuel : Nat)
    (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h : checkFullMirTraceFast fuel body st events outcome = true) :
    checkObsErasedMirTraceFast fuel body st (eraseBranchEvents events) outcome = true := by
  rw [← checkMirTraceApprox_guarded_eq] at h
  rw [← checkMirObsErasedTraceApprox_guarded_eq]
  exact checkMirTraceApprox_imp_obsErased h

/-- A decoded non-branch raw event is a non-branch observed event. -/
private theorem eraseBranchEvents_cons_of_decode
    {calleeSigs : List CapturedMir} {table : ShadowProvenanceTable}
    {ev : RawObservedEvent} {dEv : ObservedEvent}
    (hnb : ∀ tag, ev ≠ .branch tag)
    (h : decodeRawObservedEvent calleeSigs table ev = some dEv) (l : List ObservedEvent) :
    eraseBranchEvents (dEv :: l) = dEv :: eraseBranchEvents l := by
  cases ev with
  | branch tag => exact absurd rfl (hnb tag)
  | extCall defPath rawArgs rawRet =>
    simp only [decodeRawObservedEvent] at h
    split at h
    · split at h
      · nomatch h
      · split at h
        · injection h with h; subst h; rfl
        · nomatch h
    · nomatch h
  | extCallPanic defPath rawArgs =>
    simp only [decodeRawObservedEvent] at h
    split at h
    · split at h
      · nomatch h
      · split at h
        · injection h with h; subst h; rfl
        · nomatch h
    · nomatch h
  | extCallAbort defPath rawArgs =>
    simp only [decodeRawObservedEvent] at h
    split at h
    · split at h
      · nomatch h
      · split at h
        · injection h with h; subst h; rfl
        · nomatch h
    · nomatch h

private theorem decodeRawObservedEvents_cons_erase
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (ev : RawObservedEvent) (hnb : ∀ tag, ev ≠ .branch tag) (rest : List RawObservedEvent)
    (ih : decodeRawObservedEvents calleeSigs table (eraseRawBranchEvents rest) =
      (decodeRawObservedEvents calleeSigs table rest).map eraseBranchEvents) :
    decodeRawObservedEvents calleeSigs table (ev :: eraseRawBranchEvents rest) =
      (decodeRawObservedEvents calleeSigs table (ev :: rest)).map eraseBranchEvents := by
  simp only [decodeRawObservedEvents]
  rw [ih]
  cases hd : decodeRawObservedEvent calleeSigs table ev with
  | none => cases decodeRawObservedEvents calleeSigs table rest <;> rfl
  | some dEv =>
    cases decodeRawObservedEvents calleeSigs table rest with
    | none => rfl
    | some dRest =>
      simp only [Option.map, eraseBranchEvents_cons_of_decode hnb hd dRest]

/-- Decoding commutes with branch erasure. -/
theorem decodeRawObservedEvents_eraseRawBranchEvents
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable) :
    ∀ (evs : List RawObservedEvent),
      decodeRawObservedEvents calleeSigs table (eraseRawBranchEvents evs) =
        (decodeRawObservedEvents calleeSigs table evs).map eraseBranchEvents
  | [] => rfl
  | .branch tag :: rest => by
    have ih := decodeRawObservedEvents_eraseRawBranchEvents calleeSigs table rest
    simp only [eraseRawBranchEvents, decodeRawObservedEvents, decodeRawObservedEvent]
    rw [ih]
    cases decodeRawObservedEvents calleeSigs table rest <;> rfl
  | .extCall defPath rawArgs rawRet :: rest =>
    decodeRawObservedEvents_cons_erase calleeSigs table (.extCall defPath rawArgs rawRet) (fun _ h => nomatch h) rest
      (decodeRawObservedEvents_eraseRawBranchEvents calleeSigs table rest)
  | .extCallPanic defPath rawArgs :: rest =>
    decodeRawObservedEvents_cons_erase calleeSigs table (.extCallPanic defPath rawArgs) (fun _ h => nomatch h) rest
      (decodeRawObservedEvents_eraseRawBranchEvents calleeSigs table rest)
  | .extCallAbort defPath rawArgs :: rest =>
    decodeRawObservedEvents_cons_erase calleeSigs table (.extCallAbort defPath rawArgs) (fun _ h => nomatch h) rest
      (decodeRawObservedEvents_eraseRawBranchEvents calleeSigs table rest)

/-- Decoding a branch-erased `RawByteTrace` erases the branches of the decoded
`ObservedTrace` (arguments, outcome, and populated initial memory are unchanged). -/
theorem decodeRawByteTrace_eraseRawBranchEvents
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    decodeRawByteTrace rootBody calleeSigs table
        { rawTrace with events := eraseRawBranchEvents rawTrace.events } =
      (decodeRawByteTrace rootBody calleeSigs table rawTrace).map
        (fun t => { t with events := eraseBranchEvents t.events }) := by
  unfold decodeRawByteTrace
  dsimp only
  rw [decodeRawObservedEvents_eraseRawBranchEvents]
  cases decodeFnArgsFromRawBytes rootBody table rawTrace.rawArgs with
  | none => rfl
  | some args =>
    cases decodeRawObservedEvents calleeSigs table rawTrace.events with
    | none => rfl
    | some events =>
      cases decodeRawObservedOutcome rootBody table rawTrace.outcome with
      | none => rfl
      | some outcome => rfl

/-- A full (`checkBranches = true`) acceptance of `rawTrace` implies the
branch-erased acceptance of `rawTrace` with its `.branch` events removed, at the
same fuel. -/
theorem checkRawByteTraceObsErasedBounded_of_full
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceFullBounded fuel rootBody calleeSigs table rawTrace = true) :
    checkRawByteTraceObsErasedBounded fuel rootBody calleeSigs table
      { rawTrace with events := eraseRawBranchEvents rawTrace.events } = true := by
  rw [← checkRawByteTraceFullBoundedFast_eq] at h_ok
  rw [← checkRawByteTraceObsErasedBoundedFast_eq]
  unfold checkRawByteTraceFullBoundedFast at h_ok
  unfold checkRawByteTraceObsErasedBoundedFast
  rw [decodeRawByteTrace_eraseRawBranchEvents]
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    exact checkFullMirTraceFast_imp_obsErased rootBody fuel _ _ _ h_ok

/-- `WithCallees` counterpart of `checkRawByteTraceObsErasedBounded_of_full`. -/
theorem checkRawByteTraceWithCalleesObsErasedBounded_of_full
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesFullBounded fuel rootBody calleeSigs table rawTrace = true) :
    checkRawByteTraceWithCalleesObsErasedBounded fuel rootBody calleeSigs table
      { rawTrace with events := eraseRawBranchEvents rawTrace.events } = true := by
  rw [← checkRawByteTraceWithCalleesFullBoundedFast_eq] at h_ok
  rw [← checkRawByteTraceWithCalleesObsErasedBoundedFast_eq]
  unfold checkRawByteTraceWithCalleesFullBoundedFast at h_ok
  unfold checkRawByteTraceWithCalleesObsErasedBoundedFast
  rw [decodeRawByteTrace_eraseRawBranchEvents]
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    exact checkFullMirTraceFast_imp_obsErased rootBody fuel _ _ _ h_ok

/-- `CofixA` approximant counterpart of `checkRawByteTraceObsErasedBounded_of_full`:
full acceptance by `checkRawByteTraceFullApprox` at `fuel` implies branch-erased
acceptance by `checkRawByteTraceObsErasedApprox` on the branch-erased recording
at every depth `n ≥ fuel + (eraseRawBranchEvents rawTrace.events).length`. -/
theorem checkRawByteTraceObsErasedApprox_of_fullApprox
    {fuel n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceFullApprox fuel rootBody calleeSigs table rawTrace = true)
    (hfn : fuel + (eraseRawBranchEvents rawTrace.events).length ≤ n) :
    checkRawByteTraceObsErasedApprox n rootBody calleeSigs table
      { rawTrace with events := eraseRawBranchEvents rawTrace.events } = true := by
  rw [checkRawByteTraceFullApprox_eq] at h_ok
  exact checkRawByteTraceObsErasedBounded_imp_approx rootBody calleeSigs table
    { rawTrace with events := eraseRawBranchEvents rawTrace.events }
    (checkRawByteTraceObsErasedBounded_of_full fuel rootBody calleeSigs table rawTrace h_ok)
    hfn

/-- `WithCallees` counterpart of `checkRawByteTraceObsErasedApprox_of_fullApprox`. -/
theorem checkRawByteTraceWithCalleesObsErasedApprox_of_fullApprox
    {fuel n : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesFullApprox fuel rootBody calleeSigs table rawTrace = true)
    (hfn : fuel + (eraseRawBranchEvents rawTrace.events).length ≤ n) :
    checkRawByteTraceWithCalleesObsErasedApprox n rootBody calleeSigs table
      { rawTrace with events := eraseRawBranchEvents rawTrace.events } = true := by
  rw [checkRawByteTraceWithCalleesFullApprox_eq] at h_ok
  exact checkRawByteTraceWithCalleesObsErasedBounded_imp_approx rootBody calleeSigs table
    { rawTrace with events := eraseRawBranchEvents rawTrace.events }
    (checkRawByteTraceWithCalleesObsErasedBounded_of_full
      fuel rootBody calleeSigs table rawTrace h_ok)
    hfn

/-- Direct term-mode certificate deriving the branch-erased `ReachesRet`
consistency theorem (`{id}_trace_obs_erased_consistent` in `cargo-anneal`) from
an already-confirmed `"ok"` tag of `diagnoseRawByteTraceFullBounded` and
`h_erase : obsErasedTrace = { rawTrace with events := eraseRawBranchEvents rawTrace.events }`
(discharged by `rfl` on the event list alone, with no second or third MIR
execution). -/
theorem diagnoseRawByteTraceFullBounded_tag_ok_obsErased_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace obsErasedTrace : RawByteTrace)
    (h_tag :
      (diagnoseRawByteTraceFullBounded fuel rootBody calleeSigs table rawTrace).tagName = "ok")
    (h_erase :
      obsErasedTrace = { rawTrace with events := eraseRawBranchEvents rawTrace.events }) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table obsErasedTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out := by
  subst h_erase
  have h_full := TraceReplayDiag.isOk_of_tagName_eq_ok h_tag
  rw [diagnoseRawByteTraceFullBounded_isOk] at h_full
  exact checkRawByteTraceObsErasedBounded_sound fuel rootBody calleeSigs table
    { rawTrace with events := eraseRawBranchEvents rawTrace.events }
    (checkRawByteTraceObsErasedBounded_of_full fuel rootBody calleeSigs table rawTrace h_full)

/-- `WithCallees` counterpart of `diagnoseRawByteTraceFullBounded_tag_ok_obsErased_sound`. -/
theorem diagnoseRawByteTraceWithCalleesFullBounded_tag_ok_obsErased_sound
    (fuel : Nat) (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace obsErasedTrace : RawByteTrace)
    (h_tag :
      (diagnoseRawByteTraceWithCalleesFullBounded
        fuel rootBody calleeSigs table rawTrace).tagName = "ok")
    (h_erase :
      obsErasedTrace = { rawTrace with events := eraseRawBranchEvents rawTrace.events }) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table obsErasedTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out := by
  subst h_erase
  have h_full := TraceReplayDiag.isOk_of_tagName_eq_ok h_tag
  rw [diagnoseRawByteTraceWithCalleesFullBounded_isOk] at h_full
  exact checkRawByteTraceWithCalleesObsErasedBounded_sound fuel rootBody calleeSigs table
    { rawTrace with events := eraseRawBranchEvents rawTrace.events }
    (checkRawByteTraceWithCalleesObsErasedBounded_of_full
      fuel rootBody calleeSigs table rawTrace h_full)

/-! ## 8. Fuel-Free Entrypoints: Automatic `CapturedMir` Step Bounds \& Observation-Driven Replay

The `*Bounded` checkers take a caller-chosen `fuel` numeral (`cargo-anneal` and
`itree-difftest` currently pass a fixed constant). The entrypoints in this section
take no fuel: every step budget is derived from the `CapturedMir` bodies and the
observed trace.

* `blockStepCount body` counts one `stepMirState` transition per statement and one
  per terminator (`goto`, `drop`, `assert`, `switchInt`, intrinsic or inlined
  `call` entry, `return`, `unwindResume`), i.e. the transitions one frame instance
  takes to run every basic block of `body` once.
* With `checkBranches = true` every `switchInt` emits a `MirObsE` event, so between
  two consecutive visible events a frame instance only follows `goto` / `drop` /
  `return` edges, the success edge of `assert`, and the return edges of the inlined
  calls it makes. For an acyclic direct call graph of depth `k ≤ inlinedCallees.length`
  where `S(b) = blockStepCount b`, finishing all pending callees and remaining caller
  blocks telescopes to at most
  `S(c_k) + ∑_{j=1}^{k-1} S(c_j) ∏_{i=j+1}^k (S(c_i) + 1) + S(body) ∏_{i=1}^k (S(c_i) + 1)
   = (S(body) + 1) ∏_{i=1}^k (S(c_i) + 1) - 1`
  transitions; the extra `inlinedCallees.length + 1` factor in `defaultIntraEventSteps`
  provides slack for repeated inlined frames already on `callStack` when the segment
  begins (and for the final `.halted out => .ret out` transition after an unwinding
  or aborting external call).
* Segments that can exceed `defaultIntraEventSteps` under `checkBranches = true` are:
  (i) silent loops that exit without `switchInt` through a failing `assert` or an
      unwinding callee (`isUnwindingPanicDefPath` caught by `.cleanup`),
  (ii) indirect inlined calls (`TerminatorKind.call` / `TerminatorKind.tailCall`
       whose `func` operand is a function-pointer local resolved via `s.memory.fnPtrs`),
       which can dispatch to different callees on successive visits to the same
       basic block as the function-pointer local is updated,
  (iii) inlined `TerminatorKind.tailCall` (`enterTailCalleeFrame`), which replaces
        `activeCallee` at `blockIdx = 0` without pushing a `SavedCallerFrame`, and
  (iv) recursive inlined call chains deeper than `inlinedCallees.length` frames.
  On those segments `reconstructFullMirTraceAuto`, `checkFullMirTraceAuto`, and
  `diagnoseFullMirTraceAuto` soundly reject (`none` / `false` / `.outOfFuel`).
* `reconstructFullMirTraceAuto`, `checkFullMirTraceAuto`, and `diagnoseFullMirTraceAuto`
  all recurse structurally on `events : List ObservedEvent` as the outer recursion and
  spend at most `defaultIntraEventSteps` transitions per segment (the visible transition
  included). `checkFullMirTraceWithin` / `checkFullMirTraceAuto` is tail-recursive and
  never allocates `List (Event MirEffect)` pairs, while agreeing identically with
  `(reconstructFullMirTraceWithin ...).isSome` (`checkFullMirTraceWithin_eq`) and
  `(diagnoseFullMirTraceWithin ...).isOk` (`diagnoseFullMirTraceWithin_isOk`,
  `diagnoseRawByteTraceFull_isOk`). Its soundness needs no bound at all
  (`reconstructFullMirTraceWithin_sound`, `checkFullMirTraceWithin_sound`), a larger
  per-segment budget never loses an accepted trace (`reconstructFullMirTraceWithin_mono`,
  `checkFullMirTraceWithin_mono`), and any global-budget `checkFullMirTraceFast fuel`
  acceptance with `fuel ≤ intra` is also accepted by `checkFullMirTraceWithin`
  (`checkFullMirTraceFast_imp_within_of_le`).
* `checkBranches = false` erases `switchInt`, so loops between external calls are
  silent and no body-derived bound is complete. The fuel-free branch-erased
  checkers run `checkObsErasedObservedTraceBounded` with the global budget
  `defaultObsErasedTraceSteps` (every call-free segment may pass over the whole
  program `defaultIntraEventSteps + 1` times); when the full trace is available,
  `checkRawByteTraceFull_obsErased_sound` derives the branch-erased certificate
  from the full fuel-free check with no budget at all.
-/

/-- `stepMirState` transitions needed to run every basic block of `bbs` once: one
per statement plus one for the terminator. -/
@[reducible]
def basicBlocksStepCount : List BasicBlockData → Nat
  | [] => 0
  | bb :: bbs => bb.statements.length + 1 + basicBlocksStepCount bbs

/-- `basicBlocksStepCount body.basicBlocks`: the silent transitions one frame instance
of `body` can take before it must revisit a basic block. -/
@[reducible]
def blockStepCount (body : CapturedMir) : Nat :=
  basicBlocksStepCount body.basicBlocks

/-- `∏ c ∈ inlinedCallees, (blockStepCount c + 1)`. -/
@[reducible]
def calleesStepProduct : List CapturedMir → Nat
  | [] => 1
  | c :: cs => (blockStepCount c + 1) * calleesStepProduct cs

/-- Automatic per-segment budget: the `stepMirState` transitions (visible transition
included) allowed between two consecutive visible events of a `checkBranches = true`
replay of `body` with transparent `inlinedCallees`. -/
@[reducible]
def defaultIntraEventSteps (body : CapturedMir) (inlinedCallees : List CapturedMir) : Nat :=
  (inlinedCallees.length + 1) *
    ((blockStepCount body + 1) * calleesStepProduct inlinedCallees)

/-- Automatic global budget for a `checkBranches = true` trace with `eventCount`
visible events: `eventCount + 1` segments of `defaultIntraEventSteps` each. -/
@[reducible]
def defaultTraceStepsOfLength (body : CapturedMir) (inlinedCallees : List CapturedMir)
    (eventCount : Nat) : Nat :=
  (eventCount + 1) * defaultIntraEventSteps body inlinedCallees

/-- `defaultTraceStepsOfLength body inlinedCallees events.length`. -/
@[reducible]
def defaultTraceSteps (body : CapturedMir) (inlinedCallees : List CapturedMir)
    (events : List ObservedEvent) : Nat :=
  defaultTraceStepsOfLength body inlinedCallees events.length

/-- Automatic global budget for a branch-erased (`checkBranches = false`) trace with
`eventCount` call events: every call-free segment may pass over the whole program
`defaultIntraEventSteps + 1` times. -/
@[reducible]
def defaultObsErasedTraceStepsOfLength (body : CapturedMir)
    (inlinedCallees : List CapturedMir) (eventCount : Nat) : Nat :=
  defaultTraceStepsOfLength body inlinedCallees eventCount *
    (defaultIntraEventSteps body inlinedCallees + 1)

/-- `defaultObsErasedTraceStepsOfLength body inlinedCallees events.length`. -/
@[reducible]
def defaultObsErasedTraceSteps (body : CapturedMir) (inlinedCallees : List CapturedMir)
    (events : List ObservedEvent) : Nat :=
  defaultObsErasedTraceStepsOfLength body inlinedCallees events.length

/-- `defaultTraceSteps` for an undecoded `RawByteTrace` (decoding preserves the event
count and the inlined callees). -/
@[reducible]
def defaultRawTraceSteps (rootBody : CapturedMir) (rawTrace : RawByteTrace) : Nat :=
  defaultTraceStepsOfLength rootBody rawTrace.inlinedCallees rawTrace.events.length

/-- `defaultObsErasedTraceSteps` for an undecoded `RawByteTrace`. -/
@[reducible]
def defaultRawObsErasedTraceSteps (rootBody : CapturedMir) (rawTrace : RawByteTrace) : Nat :=
  defaultObsErasedTraceStepsOfLength rootBody rawTrace.inlinedCallees rawTrace.events.length

/--
One observation-driven replay segment (`checkBranches = true`): runs silent `.tau`
transitions of `stepMirState body` from `st` and consumes exactly one visible event
matching `ev`, within at most `fuel` transitions (using `elimMirVis` on `.vis` nodes
so no `Eq.ndrec` index transport is generated). Returns the recorded
`Event MirEffect` and the post-event state.
-/
@[reducible]
def stepFullMirEventWithin (body : CapturedMir) :
    Nat → MirExecState → ObservedEvent → Option (Event MirEffect × MirExecState)
  | 0, _, _ => none
  | fuel + 1, st, ev =>
    match stepMirState body st with
    | .ret _ => none
    | .tau st' => stepFullMirEventWithin body fuel st' ev
    | .vis i k =>
      elimMirVis
        (fun _ _ => none)
        (fun _ => none)
        (fun tag kObs =>
          match ev with
          | .branch expectedTag =>
            if Nat.beq tag expectedTag then
              some (⟨.inr (.inl (.emit (.event tag))), PUnit.unit⟩, kObs PUnit.unit)
            else
              none
          | _ => none)
        (fun req kCall =>
          match
            findActiveCallImpurePtrArgIdx?
              (execStateActiveBody body st) (execStateCursor st).1 req
          with
          | some _ => none
          | none =>
            match matchCallObservedEvent req ev with
            | some ans => some (⟨.inr (.inr (.call req)), ans⟩, kCall ans)
            | none => none)
        i k

/-- Allocation-free observation-driven replay segment (`checkBranches = true`):
runs silent `.tau` transitions of `stepMirState body` from `st` and consumes one
visible event matching `ev` within at most `fuel` transitions, returning only the
post-event `MirExecState` without allocating `Event MirEffect`. -/
@[reducible]
def stepFullMirEventFastWithin (body : CapturedMir) :
    Nat → MirExecState → ObservedEvent → Option MirExecState
  | 0, _, _ => none
  | fuel + 1, st, ev =>
    match stepMirState body st with
    | .ret _ => none
    | .tau st' => stepFullMirEventFastWithin body fuel st' ev
    | .vis i k =>
      elimMirVis
        (fun _ _ => none)
        (fun _ => none)
        (fun tag kObs =>
          match ev with
          | .branch expectedTag =>
            if Nat.beq tag expectedTag then
              some (kObs PUnit.unit)
            else
              none
          | _ => none)
        (fun req kCall =>
          match
            findActiveCallImpurePtrArgIdx?
              (execStateActiveBody body st) (execStateCursor st).1 req
          with
          | some _ => none
          | none =>
            match matchCallObservedEvent req ev with
            | some ans => some (kCall ans)
            | none => none)
        i k

/-- Final observation-driven replay segment: runs silent `.tau` transitions from `st`
to a terminal `.ret out` matching `outcome`, within at most `fuel` transitions. -/
@[reducible]
def finishFullMirTraceWithin (body : CapturedMir) :
    Nat → MirExecState → ObservedOutcome → Option MirOutcome
  | 0, _, _ => none
  | fuel + 1, st, outcome =>
    match stepMirState body st with
    | .ret out => if checkOutcomeMatches outcome out then some out else none
    | .tau st' => finishFullMirTraceWithin body fuel st' outcome
    | .vis _ _ => none

/-- Allocation-free boolean final segment of an observation-driven replay. -/
@[reducible]
def checkFullMirFinishWithin (body : CapturedMir) :
    Nat → MirExecState → ObservedOutcome → Bool
  | 0, _, _ => false
  | fuel + 1, st, outcome =>
    match stepMirState body st with
    | .ret out => checkOutcomeMatches outcome out
    | .tau st' => checkFullMirFinishWithin body fuel st' outcome
    | .vis _ _ => false

/--
Observation-driven full trace replay (`checkBranches = true`) recursing structurally
on `events`, with at most `intra` `stepMirState` transitions per segment.
-/
@[reducible]
def reconstructFullMirTraceWithin (body : CapturedMir) (intra : Nat) :
    MirExecState → List ObservedEvent → ObservedOutcome →
      Option (List (Event MirEffect) × MirOutcome)
  | st, [], outcome =>
    match finishFullMirTraceWithin body intra st outcome with
    | some out => some ([], out)
    | none => none
  | st, ev :: rest, outcome =>
    match stepFullMirEventWithin body intra st ev with
    | some (e, st') =>
      match reconstructFullMirTraceWithin body intra st' rest outcome with
      | some (trRest, out) => some (e :: trRest, out)
      | none => none
    | none => none

/--
Tail-recursive, allocation-free boolean observation-driven full trace checker
(`checkBranches = true`) recursing structurally on `events` as the outer recursion,
with at most `intra` `stepMirState` transitions per segment and zero
`List (Event MirEffect)` allocation.
-/
@[reducible]
def checkFullMirTraceWithin (body : CapturedMir) (intra : Nat) :
    MirExecState → List ObservedEvent → ObservedOutcome → Bool
  | st, [], outcome => checkFullMirFinishWithin body intra st outcome
  | st, ev :: rest, outcome =>
    match stepFullMirEventFastWithin body intra st ev with
    | some st' => checkFullMirTraceWithin body intra st' rest outcome
    | none => false

/--
Fuel-free observation-driven full trace replay (`checkBranches = true`): recurses
structurally on `events`, bounding each silent segment by
`defaultIntraEventSteps body inlinedCallees`.
-/
@[reducible]
def reconstructFullMirTraceAuto (body : CapturedMir) (inlinedCallees : List CapturedMir)
    (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome) :
    Option (List (Event MirEffect) × MirOutcome) :=
  reconstructFullMirTraceWithin body (defaultIntraEventSteps body inlinedCallees)
    st events outcome

/--
Tail-recursive, allocation-free fuel-free boolean full trace checker
(`checkBranches = true`): recurses structurally on `events`, bounding each silent
segment by `defaultIntraEventSteps body inlinedCallees`.
-/
@[reducible]
def checkFullMirTraceAuto (body : CapturedMir) (inlinedCallees : List CapturedMir)
    (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome) :
    Bool :=
  checkFullMirTraceWithin body (defaultIntraEventSteps body inlinedCallees)
    st events outcome

theorem stepFullMirEventFastWithin_eq (body : CapturedMir) :
    ∀ (fuel : Nat) (st : MirExecState) (ev : ObservedEvent),
      stepFullMirEventFastWithin body fuel st ev =
        (stepFullMirEventWithin body fuel st ev).map Prod.snd := by
  intro fuel
  induction fuel with
  | zero => intro _ _; rfl
  | succ fuel' ih =>
    intro st ev
    unfold stepFullMirEventFastWithin stepFullMirEventWithin
    cases stepMirState body st with
    | ret _ => rfl
    | tau st' => exact ih st' ev
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · cases f; rfl
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent => rfl
          | event tag =>
            dsimp only [elimMirVis]
            cases ev with
            | branch expectedTag =>
              dsimp only
              cases Nat.beq tag expectedTag <;> rfl
            | _ => rfl
      · cases callReq with
        | call req =>
          dsimp only [elimMirVis]
          cases findActiveCallImpurePtrArgIdx?
              (execStateActiveBody body st) (execStateCursor st).1 req with
          | some _ => rfl
          | none =>
            dsimp only
            cases matchCallObservedEvent req ev <;> rfl

theorem checkFullMirFinishWithin_eq (body : CapturedMir) :
    ∀ (fuel : Nat) (st : MirExecState) (outcome : ObservedOutcome),
      checkFullMirFinishWithin body fuel st outcome =
        (finishFullMirTraceWithin body fuel st outcome).isSome := by
  intro fuel
  induction fuel with
  | zero => intro _ _; rfl
  | succ fuel' ih =>
    intro st outcome
    unfold checkFullMirFinishWithin finishFullMirTraceWithin
    cases stepMirState body st with
    | ret out =>
      dsimp only
      cases checkOutcomeMatches outcome out <;> rfl
    | tau st' => exact ih st' outcome
    | vis _ _ => rfl

/-- Exact agreement between the tail-recursive allocation-free boolean checker
`checkFullMirTraceWithin` and `(reconstructFullMirTraceWithin ...).isSome`. -/
theorem checkFullMirTraceWithin_eq (body : CapturedMir) (intra : Nat) :
    ∀ (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome),
      checkFullMirTraceWithin body intra st events outcome =
        (reconstructFullMirTraceWithin body intra st events outcome).isSome := by
  intro st events
  induction events generalizing st with
  | nil =>
    intro outcome
    unfold checkFullMirTraceWithin reconstructFullMirTraceWithin
    rw [checkFullMirFinishWithin_eq]
    cases finishFullMirTraceWithin body intra st outcome <;> rfl
  | cons ev rest ih =>
    intro outcome
    unfold checkFullMirTraceWithin reconstructFullMirTraceWithin
    rw [stepFullMirEventFastWithin_eq]
    cases stepFullMirEventWithin body intra st ev with
    | none => rfl
    | some pair =>
      rcases pair with ⟨e, st'⟩
      dsimp only [Option.map]
      rw [ih st' outcome]
      cases reconstructFullMirTraceWithin body intra st' rest outcome <;> rfl

/-- Exact agreement between `checkFullMirTraceAuto` and
`(reconstructFullMirTraceAuto ...).isSome`. -/
theorem checkFullMirTraceAuto_eq
    (body : CapturedMir) (inlinedCallees : List CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    checkFullMirTraceAuto body inlinedCallees st events outcome =
      (reconstructFullMirTraceAuto body inlinedCallees st events outcome).isSome :=
  checkFullMirTraceWithin_eq body (defaultIntraEventSteps body inlinedCallees)
    st events outcome

theorem stepFullMirEventWithin_sound (body : CapturedMir) :
    ∀ (fuel : Nat) (st : MirExecState) (ev : ObservedEvent)
      (e : Event MirEffect) (st' : MirExecState),
      stepFullMirEventWithin body fuel st ev = some (e, st') →
      MatchesObservedEvent ev e ∧
      Reaches (ITree.cofix (stepMirState body) st) [e]
        (ITree.cofix (stepMirState body) st') := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; nomatch h
  | succ fuel' ih =>
    intro st ev e st' h_ok
    unfold stepFullMirEventWithin at h_ok
    have h_obs :
        (ITree.cofix (stepMirState body) st).observe =
          (stepMirState body st).map (ITree.cofix (stepMirState body)) :=
      ITree.observe_cofix (stepMirState body) st
    cases h_step : stepMirState body st with
    | ret out₀ => simp only [h_step] at h_ok; nomatch h_ok
    | tau st₁ =>
      simp only [h_step] at h_ok
      rw [h_step] at h_obs
      dsimp only [ITreeF.map] at h_obs
      rcases ih st₁ ev e st' h_ok with ⟨h_ev, h_reach⟩
      exact ⟨h_ev, .tau h_obs h_reach⟩
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · simp only [h_step] at h_ok; nomatch h_ok
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent => simp only [h_step] at h_ok; nomatch h_ok
          | event tag =>
            simp only [h_step] at h_ok
            cases ev with
            | branch expectedTag =>
              change
                (if Nat.beq tag expectedTag then
                  some (⟨.inr (.inl (.emit (.event tag))), PUnit.unit⟩, k PUnit.unit)
                else none) = some (e, st') at h_ok
              revert h_ok
              cases htag : Nat.beq tag expectedTag <;> intro h_ok
              · nomatch h_ok
              · cases h_ok
                rw [h_step] at h_obs
                dsimp only [ITreeF.map] at h_obs
                exact ⟨Nat.beq_eq.mp htag,
                  .vis h_obs False.elim PUnit.unit (.refl _)⟩
            | _ => nomatch h_ok
      · cases callReq with
        | call req =>
          simp only [h_step] at h_ok
          dsimp only [elimMirVis] at h_ok
          cases h_imp :
              findActiveCallImpurePtrArgIdx?
                (execStateActiveBody body st) (execStateCursor st).1 req with
          | some _ => rw [h_imp] at h_ok; nomatch h_ok
          | none =>
            rw [h_imp] at h_ok
            dsimp only at h_ok
            cases h_match : matchCallObservedEvent req ev with
            | none => rw [h_match] at h_ok; nomatch h_ok
            | some ans =>
              rw [h_match] at h_ok
              cases h_ok
              rw [h_step] at h_obs
              dsimp only [ITreeF.map] at h_obs
              exact ⟨matchCallObservedEvent_sound h_match,
                .vis h_obs False.elim ans (.refl _)⟩

theorem finishFullMirTraceWithin_sound (body : CapturedMir) :
    ∀ (fuel : Nat) (st : MirExecState) (outcome : ObservedOutcome) (out : MirOutcome),
      finishFullMirTraceWithin body fuel st outcome = some out →
      MatchesObservedOutcome outcome out ∧
      ReachesRet (ITree.cofix (stepMirState body) st) [] out := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; nomatch h
  | succ fuel' ih =>
    intro st outcome out h_ok
    unfold finishFullMirTraceWithin at h_ok
    have h_obs :
        (ITree.cofix (stepMirState body) st).observe =
          (stepMirState body st).map (ITree.cofix (stepMirState body)) :=
      ITree.observe_cofix (stepMirState body) st
    cases h_step : stepMirState body st with
    | ret out₀ =>
      simp only [h_step] at h_ok
      revert h_ok
      cases hm : checkOutcomeMatches outcome out₀ <;> intro h_ok
      · nomatch h_ok
      · simp only [ite_true, Option.some.injEq] at h_ok
        subst h_ok
        rw [h_step] at h_obs
        dsimp only [ITreeF.map] at h_obs
        exact ⟨checkOutcomeMatches_sound hm,
          ⟨ITree.cofix (stepMirState body) st, .refl _, h_obs⟩⟩
    | tau st₁ =>
      simp only [h_step] at h_ok
      rw [h_step] at h_obs
      dsimp only [ITreeF.map] at h_obs
      rcases ih st₁ outcome out h_ok with ⟨h_out, ⟨u, h_reach, h_u⟩⟩
      exact ⟨h_out, ⟨u, .tau h_obs h_reach, h_u⟩⟩
    | vis _ _ => simp only [h_step] at h_ok; nomatch h_ok

/--
Soundness of `reconstructFullMirTraceWithin` for every per-segment budget `intra`:
when it returns `some (tr, out)`, `tr` matches `events`, `out` matches `outcome`, and
`ITree.cofix (stepMirState body) st` reaches `out` along `tr` (fuel-free `ReachesRet`).
-/
theorem reconstructFullMirTraceWithin_sound
    (body : CapturedMir) (intra : Nat) :
    ∀ (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome)
      (tr : List (Event MirEffect)) (out : MirOutcome),
      reconstructFullMirTraceWithin body intra st events outcome = some (tr, out) →
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (ITree.cofix (stepMirState body) st) tr out := by
  intro st events
  induction events generalizing st with
  | nil =>
    intro outcome tr out h_ok
    unfold reconstructFullMirTraceWithin at h_ok
    cases h_fin : finishFullMirTraceWithin body intra st outcome with
    | none => rw [h_fin] at h_ok; nomatch h_ok
    | some out₀ =>
      rw [h_fin] at h_ok
      cases h_ok
      rcases finishFullMirTraceWithin_sound body intra st outcome _ h_fin with
        ⟨h_out, h_reach⟩
      exact ⟨trivial, h_out, h_reach⟩
  | cons ev rest ih =>
    intro outcome tr out h_ok
    unfold reconstructFullMirTraceWithin at h_ok
    cases h_seg : stepFullMirEventWithin body intra st ev with
    | none => rw [h_seg] at h_ok; nomatch h_ok
    | some pair =>
      rcases pair with ⟨e, st₁⟩
      rw [h_seg] at h_ok
      cases h_rec : reconstructFullMirTraceWithin body intra st₁ rest outcome with
      | none =>
        simp only [h_rec] at h_ok; nomatch h_ok
      | some q =>
        rcases q with ⟨trRest, out₁⟩
        simp only [h_rec, Option.some.injEq, Prod.mk.injEq] at h_ok
        rcases h_ok with ⟨rfl, rfl⟩
        rcases stepFullMirEventWithin_sound body intra st ev e st₁ h_seg with
          ⟨h_ev, h_step⟩
        rcases ih st₁ outcome trRest out₁ h_rec with ⟨h_evs, h_out, ⟨u, h_reach, h_u⟩⟩
        exact ⟨⟨h_ev, h_evs⟩, h_out, ⟨u, reaches_trans h_step h_reach, h_u⟩⟩

/--
Soundness of the fuel-free observation-driven replay `reconstructFullMirTraceAuto`,
lifting directly into fuel-free `ReachesRet`.
-/
theorem reconstructFullMirTraceAuto_sound
    (body : CapturedMir) (inlinedCallees : List CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (tr : List (Event MirEffect)) (out : MirOutcome)
    (h_ok : reconstructFullMirTraceAuto body inlinedCallees st events outcome =
      some (tr, out)) :
    MatchesObservedEvents events tr ∧
    MatchesObservedOutcome outcome out ∧
    ReachesRet (ITree.cofix (stepMirState body) st) tr out :=
  reconstructFullMirTraceWithin_sound body _ st events outcome tr out h_ok

/-- Budget monotonicity of one observation-driven replay segment: a segment accepted
within `m` transitions is accepted, with the same event and post-event state, within
every `n ≥ m`. -/
theorem stepFullMirEventWithin_mono (body : CapturedMir) :
    ∀ {m n : Nat} (st : MirExecState) (ev : ObservedEvent)
      (r : Event MirEffect × MirExecState),
      stepFullMirEventWithin body m st ev = some r → m ≤ n →
      stepFullMirEventWithin body n st ev = some r := by
  intro m
  induction m with
  | zero => intro _ _ _ _ h; nomatch h
  | succ m' ih =>
    intro n st ev r h_ok hmn
    cases n with
    | zero => omega
    | succ n' =>
      have hmn' : m' ≤ n' := Nat.le_of_succ_le_succ hmn
      unfold stepFullMirEventWithin at h_ok ⊢
      revert h_ok
      cases stepMirState body st with
      | tau st₁ => exact fun h_ok => ih st₁ ev r h_ok hmn'
      | ret _ => exact id
      | vis i k =>
        rcases i with f | (obsReq | callReq)
        · exact id
        · rcases obsReq with ⟨obs⟩
          cases obs <;> exact id
        · rcases callReq with ⟨req⟩
          exact id

/-- Budget monotonicity of the final observation-driven replay segment. -/
theorem finishFullMirTraceWithin_mono (body : CapturedMir) :
    ∀ {m n : Nat} (st : MirExecState) (outcome : ObservedOutcome) (out : MirOutcome),
      finishFullMirTraceWithin body m st outcome = some out → m ≤ n →
      finishFullMirTraceWithin body n st outcome = some out := by
  intro m
  induction m with
  | zero => intro _ _ _ _ h; nomatch h
  | succ m' ih =>
    intro n st outcome out h_ok hmn
    cases n with
    | zero => omega
    | succ n' =>
      have hmn' : m' ≤ n' := Nat.le_of_succ_le_succ hmn
      unfold finishFullMirTraceWithin at h_ok ⊢
      revert h_ok
      cases stepMirState body st with
      | tau st₁ => exact fun h_ok => ih st₁ outcome out h_ok hmn'
      | ret _ => exact id
      | vis _ _ => exact id

/-- Kleene budget monotonicity of the observation-driven replay: a trace accepted with
per-segment budget `m` is accepted, with the same reconstructed trace and outcome,
with every per-segment budget `n ≥ m` (so enlarging the automatic bound never loses
an accepted trace). -/
theorem reconstructFullMirTraceWithin_mono (body : CapturedMir) {m n : Nat}
    (h_le : m ≤ n) :
    ∀ (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome)
      (p : List (Event MirEffect) × MirOutcome),
      reconstructFullMirTraceWithin body m st events outcome = some p →
      reconstructFullMirTraceWithin body n st events outcome = some p := by
  intro st events
  induction events generalizing st with
  | nil =>
    intro outcome p h_ok
    unfold reconstructFullMirTraceWithin at h_ok ⊢
    cases h_fin : finishFullMirTraceWithin body m st outcome with
    | none => rw [h_fin] at h_ok; nomatch h_ok
    | some out =>
      rw [h_fin] at h_ok
      rw [finishFullMirTraceWithin_mono body st outcome out h_fin h_le]
      exact h_ok
  | cons ev rest ih =>
    intro outcome p h_ok
    unfold reconstructFullMirTraceWithin at h_ok ⊢
    cases h_seg : stepFullMirEventWithin body m st ev with
    | none => rw [h_seg] at h_ok; nomatch h_ok
    | some pair =>
      rcases pair with ⟨e, st₁⟩
      rw [h_seg] at h_ok
      rw [stepFullMirEventWithin_mono body st ev (e, st₁) h_seg h_le]
      cases h_rec : reconstructFullMirTraceWithin body m st₁ rest outcome with
      | none => simp only [h_rec] at h_ok; nomatch h_ok
      | some q =>
        simp only [h_rec] at h_ok
        simp only [ih st₁ outcome q h_rec]
        exact h_ok

/-- A replay segment accepted within `fuel` transitions, followed by a suffix accepted
by `checkFullMirTraceFast` at fuel `g`, is accepted by `checkFullMirTraceFast` at
fuel `fuel + g`. -/
theorem stepFullMirEventWithin_checkFullMirTraceFast (body : CapturedMir) :
    ∀ (fuel g : Nat) (st : MirExecState) (ev : ObservedEvent)
      (rest : List ObservedEvent) (outcome : ObservedOutcome)
      (e : Event MirEffect) (st' : MirExecState),
      stepFullMirEventWithin body fuel st ev = some (e, st') →
      checkFullMirTraceFast g body st' rest outcome = true →
      checkFullMirTraceFast (fuel + g) body st (ev :: rest) outcome = true := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ h; nomatch h
  | succ fuel' ih =>
    intro g st ev rest outcome e st' h_seg h_rest
    rw [Nat.add_right_comm]
    unfold stepFullMirEventWithin at h_seg
    unfold checkFullMirTraceFast
    cases h_step : stepMirState body st with
    | ret out₀ => simp only [h_step] at h_seg; nomatch h_seg
    | tau st₁ =>
      simp only [h_step] at h_seg ⊢
      exact ih g st₁ ev rest outcome e st' h_seg h_rest
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · simp only [h_step] at h_seg; nomatch h_seg
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent => simp only [h_step] at h_seg; nomatch h_seg
          | event tag =>
            simp only [h_step] at h_seg ⊢
            dsimp only [elimMirVis] at h_seg
            cases ev with
            | branch expectedTag =>
              dsimp only at h_seg ⊢
              revert h_seg
              cases Nat.beq tag expectedTag <;> intro h_seg
              · nomatch h_seg
              · cases h_seg
                exact checkFullMirTraceFast_mono body _ rest outcome h_rest
                  (Nat.le_add_left g fuel')
            | extCall _ _ _ => nomatch h_seg
            | extCallPanic _ _ => nomatch h_seg
            | extCallAbort _ _ => nomatch h_seg
      · cases callReq with
        | call req =>
          simp only [h_step] at h_seg ⊢
          dsimp only [elimMirVis] at h_seg
          cases h_imp :
              findActiveCallImpurePtrArgIdx?
                (execStateActiveBody body st) (execStateCursor st).1 req with
          | some _ => rw [h_imp] at h_seg; nomatch h_seg
          | none =>
            rw [h_imp] at h_seg
            dsimp only at h_seg ⊢
            cases h_match : matchCallObservedEvent req ev with
            | none => rw [h_match] at h_seg; nomatch h_seg
            | some ans =>
              rw [h_match] at h_seg
              cases h_seg
              exact checkFullMirTraceFast_mono body _ rest outcome h_rest
                (Nat.le_add_left g fuel')

/-- A final segment accepted within `fuel` transitions is accepted by
`checkFullMirTraceFast` at fuel `fuel`. -/
theorem finishFullMirTraceWithin_checkFullMirTraceFast (body : CapturedMir) :
    ∀ (fuel : Nat) (st : MirExecState) (outcome : ObservedOutcome) (out : MirOutcome),
      finishFullMirTraceWithin body fuel st outcome = some out →
      checkFullMirTraceFast fuel body st [] outcome = true := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; nomatch h
  | succ fuel' ih =>
    intro st outcome out h_fin
    unfold finishFullMirTraceWithin at h_fin
    unfold checkFullMirTraceFast
    cases h_step : stepMirState body st with
    | ret out₀ =>
      simp only [h_step] at h_fin ⊢
      revert h_fin
      cases checkOutcomeMatches outcome out₀ <;> intro h_fin
      · nomatch h_fin
      · rfl
    | tau st₁ =>
      simp only [h_step] at h_fin ⊢
      exact ih st₁ outcome out h_fin
    | vis _ _ => simp only [h_step] at h_fin; nomatch h_fin

/--
Every trace accepted by the observation-driven replay with per-segment budget `intra`
is accepted by the global-fuel checker `checkFullMirTraceFast` at fuel
`(events.length + 1) * intra`.
-/
theorem reconstructFullMirTraceWithin_checkFullMirTraceFast
    (body : CapturedMir) (intra : Nat) :
    ∀ (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome)
      (p : List (Event MirEffect) × MirOutcome),
      reconstructFullMirTraceWithin body intra st events outcome = some p →
      checkFullMirTraceFast ((events.length + 1) * intra) body st events outcome = true := by
  intro st events
  induction events generalizing st with
  | nil =>
    intro outcome p h_ok
    unfold reconstructFullMirTraceWithin at h_ok
    cases h_fin : finishFullMirTraceWithin body intra st outcome with
    | none => rw [h_fin] at h_ok; nomatch h_ok
    | some out₀ =>
      rw [List.length_nil, Nat.zero_add, Nat.one_mul]
      exact finishFullMirTraceWithin_checkFullMirTraceFast body intra st outcome out₀ h_fin
  | cons ev rest ih =>
    intro outcome p h_ok
    unfold reconstructFullMirTraceWithin at h_ok
    cases h_seg : stepFullMirEventWithin body intra st ev with
    | none => rw [h_seg] at h_ok; nomatch h_ok
    | some pair =>
      rcases pair with ⟨e, st₁⟩
      rw [h_seg] at h_ok
      cases h_rec : reconstructFullMirTraceWithin body intra st₁ rest outcome with
      | none => simp only [h_rec] at h_ok; nomatch h_ok
      | some q =>
        have h_fuel :
            ((ev :: rest).length + 1) * intra = intra + (rest.length + 1) * intra := by
          rw [List.length_cons, Nat.add_mul (rest.length + 1) 1 intra, Nat.one_mul]
          exact Nat.add_comm _ _
        rw [h_fuel]
        exact stepFullMirEventWithin_checkFullMirTraceFast body intra _ st ev rest
          outcome e st₁ h_seg (ih st₁ outcome q h_rec)

/-- `reconstructFullMirTraceAuto` acceptance implies `checkFullMirTraceFast`
acceptance at the automatic global budget `defaultTraceSteps`. -/
theorem reconstructFullMirTraceAuto_checkFullMirTraceFast
    (body : CapturedMir) (inlinedCallees : List CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok : (reconstructFullMirTraceAuto body inlinedCallees st events outcome).isSome = true) :
    checkFullMirTraceFast (defaultTraceSteps body inlinedCallees events)
      body st events outcome = true := by
  cases h_rec : reconstructFullMirTraceAuto body inlinedCallees st events outcome with
  | none => rw [h_rec] at h_ok; nomatch h_ok
  | some p =>
    exact reconstructFullMirTraceWithin_checkFullMirTraceFast body _ st events outcome p h_rec

/-- Kleene budget monotonicity of the boolean observation-driven checker
`checkFullMirTraceWithin`. -/
theorem checkFullMirTraceWithin_mono (body : CapturedMir) {m n : Nat}
    (h_le : m ≤ n) (st : MirExecState) (events : List ObservedEvent)
    (outcome : ObservedOutcome)
    (h_ok : checkFullMirTraceWithin body m st events outcome = true) :
    checkFullMirTraceWithin body n st events outcome = true := by
  rw [checkFullMirTraceWithin_eq] at h_ok ⊢
  cases h_rec : reconstructFullMirTraceWithin body m st events outcome with
  | none => rw [h_rec] at h_ok; nomatch h_ok
  | some p =>
    rw [reconstructFullMirTraceWithin_mono body h_le st events outcome p h_rec]
    rfl

/-- Soundness of the boolean observation-driven checker `checkFullMirTraceWithin`. -/
theorem checkFullMirTraceWithin_sound
    (body : CapturedMir) (intra : Nat) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok : checkFullMirTraceWithin body intra st events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (ITree.cofix (stepMirState body) st) tr out := by
  rw [checkFullMirTraceWithin_eq] at h_ok
  cases h_rec : reconstructFullMirTraceWithin body intra st events outcome with
  | none => rw [h_rec] at h_ok; nomatch h_ok
  | some p =>
    exact ⟨p.1, p.2,
      reconstructFullMirTraceWithin_sound body intra st events outcome p.1 p.2 h_rec⟩

/-- Soundness of the fuel-free boolean observation-driven checker `checkFullMirTraceAuto`. -/
theorem checkFullMirTraceAuto_sound
    (body : CapturedMir) (inlinedCallees : List CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok : checkFullMirTraceAuto body inlinedCallees st events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (ITree.cofix (stepMirState body) st) tr out :=
  checkFullMirTraceWithin_sound body _ st events outcome h_ok

/-- `checkFullMirTraceAuto` acceptance implies `checkFullMirTraceFast` acceptance at
`defaultTraceSteps`. -/
theorem checkFullMirTraceAuto_checkFullMirTraceFast
    (body : CapturedMir) (inlinedCallees : List CapturedMir) (st : MirExecState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok : checkFullMirTraceAuto body inlinedCallees st events outcome = true) :
    checkFullMirTraceFast (defaultTraceSteps body inlinedCallees events)
      body st events outcome = true := by
  rw [checkFullMirTraceAuto_eq] at h_ok
  exact reconstructFullMirTraceAuto_checkFullMirTraceFast
    body inlinedCallees st events outcome h_ok

private def checkFullMirTraceWithinCur (body : CapturedMir) (curBudget intra : Nat)
    (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome) : Bool :=
  match events with
  | [] => checkFullMirFinishWithin body curBudget st outcome
  | ev :: rest =>
    match stepFullMirEventFastWithin body curBudget st ev with
    | some st' => checkFullMirTraceWithin body intra st' rest outcome
    | none => false

private theorem checkFullMirTraceWithinCur_self (body : CapturedMir) (intra : Nat)
    (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome) :
    checkFullMirTraceWithinCur body intra intra st events outcome =
      checkFullMirTraceWithin body intra st events outcome := by
  cases events <;> rfl

private theorem checkFullMirTraceFast_imp_within_aux (body : CapturedMir) :
    ∀ (fuel curBudget intra : Nat),
      fuel ≤ curBudget →
      fuel ≤ intra →
      ∀ (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome),
        checkFullMirTraceFast fuel body st events outcome = true →
        checkFullMirTraceWithinCur body curBudget intra st events outcome = true := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ h; nomatch h
  | succ fuel' ih =>
    intro curBudget intra h_cur h_intra st events outcome h_fast
    cases curBudget with
    | zero => omega
    | succ cur' =>
      have h_cur' : fuel' ≤ cur' := Nat.le_of_succ_le_succ h_cur
      have h_intra' : fuel' ≤ intra := Nat.le_of_succ_le h_intra
      unfold checkFullMirTraceFast at h_fast
      cases h_step : stepMirState body st with
      | ret out₀ =>
        rw [h_step] at h_fast
        cases events with
        | nil =>
          unfold checkFullMirTraceWithinCur checkFullMirFinishWithin
          rw [h_step]
          exact h_fast
        | cons _ _ => nomatch h_fast
      | tau st₁ =>
        rw [h_step] at h_fast
        cases events with
        | nil =>
          unfold checkFullMirTraceWithinCur checkFullMirFinishWithin
          rw [h_step]
          exact ih cur' intra h_cur' h_intra' st₁ [] outcome h_fast
        | cons ev rest =>
          unfold checkFullMirTraceWithinCur stepFullMirEventFastWithin
          rw [h_step]
          exact ih cur' intra h_cur' h_intra' st₁ (ev :: rest) outcome h_fast
      | vis i k =>
        rw [h_step] at h_fast
        rcases i with f | (obsReq | callReq)
        · cases f; nomatch h_fast
        · cases obsReq with
          | emit obs =>
            cases obs with
            | silent => nomatch h_fast
            | event tag =>
              cases events with
              | nil => nomatch h_fast
              | cons ev rest =>
                cases ev with
                | branch expectedTag =>
                  unfold checkFullMirTraceWithinCur stepFullMirEventFastWithin
                  rw [h_step]
                  dsimp only [elimMirVis] at h_fast ⊢
                  revert h_fast
                  cases Nat.beq tag expectedTag <;> intro h_fast
                  · nomatch h_fast
                  · change checkFullMirTraceWithin body intra (k PUnit.unit) rest outcome = true
                    rw [← checkFullMirTraceWithinCur_self]
                    exact ih intra intra h_intra' h_intra' (k PUnit.unit) rest outcome h_fast
                | extCall _ _ _ => nomatch h_fast
                | extCallPanic _ _ => nomatch h_fast
                | extCallAbort _ _ => nomatch h_fast
        · cases callReq with
          | call req =>
            dsimp only at h_fast
            cases h_imp :
                findActiveCallImpurePtrArgIdx?
                  (execStateActiveBody body st) (execStateCursor st).1 req with
            | some _ => rw [h_imp] at h_fast; nomatch h_fast
            | none =>
              rw [h_imp] at h_fast
              cases events with
              | nil => nomatch h_fast
              | cons ev rest =>
                change
                  (match matchCallObservedEvent req ev with
                   | some ans => checkFullMirTraceFast fuel' body (k ans) rest outcome
                   | none => false) = true at h_fast
                unfold checkFullMirTraceWithinCur stepFullMirEventFastWithin
                rw [h_step]
                dsimp only [elimMirVis]
                rw [h_imp]
                dsimp only
                cases h_match : matchCallObservedEvent req ev with
                | none => rw [h_match] at h_fast; nomatch h_fast
                | some ans =>
                  rw [h_match] at h_fast
                  change checkFullMirTraceWithin body intra (k ans) rest outcome = true
                  rw [← checkFullMirTraceWithinCur_self]
                  exact ih intra intra h_intra' h_intra' (k ans) rest outcome h_fast

/-- Converse completeness from global-fuel `checkFullMirTraceFast` to observation-driven
`checkFullMirTraceWithin`: any trace accepted in `fuel ≤ intra` total transitions uses
at most `fuel ≤ intra` transitions per segment, so `checkFullMirTraceWithin` accepts it. -/
theorem checkFullMirTraceFast_imp_within_of_le
    (body : CapturedMir) {fuel intra : Nat} (h_le : fuel ≤ intra)
    (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_fast : checkFullMirTraceFast fuel body st events outcome = true) :
    checkFullMirTraceWithin body intra st events outcome = true := by
  rw [← checkFullMirTraceWithinCur_self]
  exact checkFullMirTraceFast_imp_within_aux body fuel intra intra
    h_le h_le st events outcome h_fast

/-- Converse completeness from `checkFullMirTraceFast` to
`reconstructFullMirTraceWithin` when `fuel ≤ intra`. -/
theorem reconstructFullMirTraceWithin_isSome_of_checkFullMirTraceFast_le
    (body : CapturedMir) {fuel intra : Nat} (h_le : fuel ≤ intra)
    (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_fast : checkFullMirTraceFast fuel body st events outcome = true) :
    (reconstructFullMirTraceWithin body intra st events outcome).isSome = true := by
  rw [← checkFullMirTraceWithin_eq]
  exact checkFullMirTraceFast_imp_within_of_le body h_le st events outcome h_fast

/-- Fuel-free full (`MirObsE` + `MirCallE`) trace checker (`checkBranches = true`),
replaying `events` observation-driven and tail-recursively from `s` with the automatic
per-segment budget derived from `body` and the transparent callees `s.memory.callees`. -/
@[reducible]
def checkFullObservedTrace (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) : Bool :=
  checkFullMirTraceAuto body s.memory.callees (.running s) events outcome

theorem checkFullObservedTrace_eq_reconstructAuto
    (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) :
    checkFullObservedTrace body s events outcome =
      (reconstructFullMirTraceAuto body s.memory.callees (.running s) events outcome).isSome :=
  checkFullMirTraceAuto_eq body s.memory.callees (.running s) events outcome

/-- Fuel-free soundness of `checkFullObservedTrace`. -/
theorem checkFullObservedTrace_sound
    (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok : checkFullObservedTrace body s events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (mirTree body s) tr out :=
  checkFullMirTraceAuto_sound body s.memory.callees (.running s) events outcome h_ok

/-- `checkFullObservedTrace` acceptance implies `checkFullObservedTraceBounded`
acceptance at the automatic global budget `defaultTraceSteps`. -/
theorem checkFullObservedTrace_imp_bounded
    (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok : checkFullObservedTrace body s events outcome = true) :
    checkFullObservedTraceBounded (defaultTraceSteps body s.memory.callees events)
      body s events outcome = true := by
  rw [checkFullObservedTraceBounded_eq_fast]
  exact checkFullMirTraceAuto_checkFullMirTraceFast body _ (.running s) events outcome h_ok

/-- Converse: `checkFullObservedTraceBounded` acceptance at `fuel ≤ defaultIntraEventSteps`
implies fuel-free `checkFullObservedTrace` acceptance. -/
theorem checkFullObservedTraceBounded_imp_fuelFree_of_le
    (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) {fuel : Nat}
    (h_le : fuel ≤ defaultIntraEventSteps body s.memory.callees)
    (h_ok : checkFullObservedTraceBounded fuel body s events outcome = true) :
    checkFullObservedTrace body s events outcome = true := by
  rw [checkFullObservedTraceBounded_eq_fast] at h_ok
  exact checkFullMirTraceFast_imp_within_of_le body h_le (.running s) events outcome h_ok

/-- Fuel-free branch-erased (`MirCallE`-only) trace checker (`checkBranches = false`)
with the automatic global budget `defaultObsErasedTraceSteps`. -/
@[reducible]
def checkObsErasedObservedTrace (body : CapturedMir) (s : MachineState)
    (events : List ObservedEvent) (outcome : ObservedOutcome) : Bool :=
  checkObsErasedObservedTraceBounded
    (defaultObsErasedTraceSteps body s.memory.callees events) body s events outcome

/-- Fuel-free soundness of `checkObsErasedObservedTrace`. -/
theorem checkObsErasedObservedTrace_sound
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok :
      checkObsErasedObservedTrace body
        (initMachineStateWithMemory body args mem) events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet (mirObsErasedStatefulTree body args mem) tr out :=
  checkObsErasedObservedTraceBounded_sound _ body args mem events outcome h_ok

/-- Fuel-free soundness of `checkObsErasedObservedTrace` with transparent `callees`. -/
theorem checkObsErasedObservedTraceWithCallees_sound
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (callees : List CapturedMir)
    (events : List ObservedEvent) (outcome : ObservedOutcome)
    (h_ok :
      checkObsErasedObservedTrace body
        (initMachineStateWithMemoryAndCallees body args mem callees)
        events outcome = true) :
    ∃ tr out,
      MatchesObservedEvents events tr ∧
      MatchesObservedOutcome outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTreeWithCallees body args mem callees) tr out :=
  checkObsErasedObservedTraceWithCalleesBounded_sound _ body args mem callees
    events outcome h_ok

/-- Fuel-free trace-consistency dispatcher (`Memory.callees := trace.inlinedCallees`),
the fuel-free counterpart of `checkObservedTraceConsistencyBounded`. -/
@[reducible]
def checkObservedTraceConsistency (checkBranches : Bool) (body : CapturedMir)
    (trace : ObservedTrace) : Bool :=
  let s := initMachineStateWithMemory body trace.args
    { trace.initMem with callees := trace.inlinedCallees }
  match checkBranches with
  | true =>
    checkFullMirTraceAuto body trace.inlinedCallees (.running s)
      trace.events trace.outcome
  | false =>
    checkObsErasedObservedTraceBounded
      (defaultObsErasedTraceSteps body trace.inlinedCallees trace.events)
      body s trace.events trace.outcome

/-- Fuel-free trace-consistency dispatcher initializing `MachineState` via
`initMachineStateWithMemoryAndCallees`, the fuel-free counterpart of
`checkObservedTraceWithCalleesBounded`. -/
@[reducible]
def checkObservedTraceWithCallees (checkBranches : Bool) (body : CapturedMir)
    (trace : ObservedTrace) : Bool :=
  let s := initMachineStateWithMemoryAndCallees body trace.args trace.initMem
    trace.inlinedCallees
  match checkBranches with
  | true =>
    checkFullMirTraceAuto body trace.inlinedCallees (.running s)
      trace.events trace.outcome
  | false =>
    checkObsErasedObservedTraceBounded
      (defaultObsErasedTraceSteps body trace.inlinedCallees trace.events)
      body s trace.events trace.outcome

/-- Fuel-free end-to-end full check of a `RawByteTrace` against `mirStatefulTree`
(`checkBranches = true`). -/
@[reducible]
def checkRawByteTraceFull (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace => checkObservedTraceConsistency true rootBody obsTrace
  | none => false

/-- Fuel-free end-to-end branch-erased check of a `RawByteTrace` against
`mirObsErasedStatefulTree` (`checkBranches = false`). -/
@[reducible]
def checkRawByteTraceObsErased (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace => checkObservedTraceConsistency false rootBody obsTrace
  | none => false

/-- Fuel-free end-to-end full check of a `RawByteTrace` against
`mirStatefulTreeWithCallees` (`checkBranches = true`). -/
@[reducible]
def checkRawByteTraceWithCalleesFull (rootBody : CapturedMir)
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace => checkObservedTraceWithCallees true rootBody obsTrace
  | none => false

/-- Fuel-free end-to-end branch-erased check of a `RawByteTrace` against
`mirObsErasedStatefulTreeWithCallees` (`checkBranches = false`). -/
@[reducible]
def checkRawByteTraceWithCalleesObsErased (rootBody : CapturedMir)
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (rawTrace : RawByteTrace) : Bool :=
  match decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | some obsTrace => checkObservedTraceWithCallees false rootBody obsTrace
  | none => false

/-- Fuel-free end-to-end soundness of `checkRawByteTraceFull`: lifts directly into
fuel-free `ReachesRet (mirStatefulTree ...)` with no `fuel` parameter. -/
theorem checkRawByteTraceFull_sound
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceFull rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out := by
  unfold checkRawByteTraceFull at h_ok
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    rcases checkFullMirTraceAuto_sound rootBody obsTrace.inlinedCallees
        (.running (initMachineStateWithMemory rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees }))
        obsTrace.events obsTrace.outcome h_ok with
      ⟨tr, out, h_evs, h_out, h_reach⟩
    exact ⟨obsTrace, tr, out, rfl, h_evs, h_out, h_reach⟩

/-- Fuel-free end-to-end soundness of `checkRawByteTraceObsErased`: lifts directly
into fuel-free `ReachesRet (mirObsErasedStatefulTree ...)` with no `fuel` parameter. -/
theorem checkRawByteTraceObsErased_sound
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceObsErased rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out := by
  unfold checkRawByteTraceObsErased at h_ok
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    rcases checkObsErasedObservedTraceBounded_sound _ rootBody obsTrace.args
        { obsTrace.initMem with callees := obsTrace.inlinedCallees }
        obsTrace.events obsTrace.outcome h_ok with
      ⟨tr, out, h_evs, h_out, h_reach⟩
    exact ⟨obsTrace, tr, out, rfl, h_evs, h_out, h_reach⟩

/-- Fuel-free end-to-end soundness of `checkRawByteTraceWithCalleesFull`. -/
theorem checkRawByteTraceWithCalleesFull_sound
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceWithCalleesFull rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out := by
  unfold checkRawByteTraceWithCalleesFull at h_ok
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    rcases checkFullMirTraceAuto_sound rootBody obsTrace.inlinedCallees
        (.running (initMachineStateWithMemoryAndCallees rootBody obsTrace.args
          obsTrace.initMem obsTrace.inlinedCallees))
        obsTrace.events obsTrace.outcome h_ok with
      ⟨tr, out, h_evs, h_out, h_reach⟩
    exact ⟨obsTrace, tr, out, rfl, h_evs, h_out, h_reach⟩

/-- Fuel-free end-to-end soundness of `checkRawByteTraceWithCalleesObsErased`. -/
theorem checkRawByteTraceWithCalleesObsErased_sound
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok :
      checkRawByteTraceWithCalleesObsErased rootBody calleeSigs table rawTrace = true) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out := by
  unfold checkRawByteTraceWithCalleesObsErased at h_ok
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    rcases checkObsErasedObservedTraceWithCalleesBounded_sound _ rootBody obsTrace.args
        obsTrace.initMem obsTrace.inlinedCallees obsTrace.events obsTrace.outcome h_ok with
      ⟨tr, out, h_evs, h_out, h_reach⟩
    exact ⟨obsTrace, tr, out, rfl, h_evs, h_out, h_reach⟩

/-- Decoding a `RawByteTrace` preserves its transparent inlined callees. -/
theorem decodeRawByteTrace_inlinedCallees
    {rootBody : CapturedMir} {calleeSigs : List CapturedMir}
    {table : ShadowProvenanceTable} {rawTrace : RawByteTrace}
    {obsTrace : ObservedTrace}
    (h : decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace) :
    obsTrace.inlinedCallees = rawTrace.inlinedCallees := by
  unfold decodeRawByteTrace at h
  cases h₁ : decodeFnArgsFromRawBytes rootBody table rawTrace.rawArgs with
  | none => rw [h₁] at h; nomatch h
  | some args =>
    rw [h₁] at h
    cases h₂ : decodeRawObservedEvents calleeSigs table rawTrace.events with
    | none => rw [h₂] at h; nomatch h
    | some events =>
      rw [h₂] at h
      cases h₃ : decodeRawObservedOutcome rootBody table rawTrace.outcome with
      | none => rw [h₃] at h; nomatch h
      | some outcome =>
        rw [h₃] at h
        injection h with h'
        subst h'
        rfl

/-- The fuel-free full check implies the `*Bounded` full check at the automatic global
budget `defaultRawTraceSteps`. -/
theorem checkRawByteTraceFull_imp_bounded
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceFull rootBody calleeSigs table rawTrace = true) :
    checkRawByteTraceFullBounded (defaultRawTraceSteps rootBody rawTrace)
      rootBody calleeSigs table rawTrace = true := by
  rw [← checkRawByteTraceFullBoundedFast_eq]
  unfold checkRawByteTraceFull at h_ok
  unfold checkRawByteTraceFullBoundedFast
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    have h_len := decodeRawByteTrace_events_length h_dec
    have h_cal := decodeRawByteTrace_inlinedCallees h_dec
    have h_auto := checkFullMirTraceAuto_checkFullMirTraceFast rootBody _ _
      obsTrace.events obsTrace.outcome h_ok
    unfold defaultRawTraceSteps
    rw [← h_len, ← h_cal]
    exact h_auto

/-- Converse: `checkRawByteTraceFullBounded` acceptance at `fuel ≤ defaultIntraEventSteps`
implies fuel-free `checkRawByteTraceFull` acceptance. -/
theorem checkRawByteTraceFullBounded_imp_fuelFree_of_le
    {fuel : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_le : fuel ≤ defaultIntraEventSteps rootBody rawTrace.inlinedCallees)
    (h_ok : checkRawByteTraceFullBounded fuel rootBody calleeSigs table rawTrace = true) :
    checkRawByteTraceFull rootBody calleeSigs table rawTrace = true := by
  rw [← checkRawByteTraceFullBoundedFast_eq] at h_ok
  unfold checkRawByteTraceFullBoundedFast at h_ok
  unfold checkRawByteTraceFull
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    have h_cal := decodeRawByteTrace_inlinedCallees h_dec
    have h_le' : fuel ≤ defaultIntraEventSteps rootBody obsTrace.inlinedCallees := by
      rw [h_cal]
      exact h_le
    exact checkFullMirTraceFast_imp_within_of_le rootBody h_le' _ _ _ h_ok

/-- The fuel-free `WithCallees` full check implies the `*Bounded` check at the
automatic global budget `defaultRawTraceSteps`. -/
theorem checkRawByteTraceWithCalleesFull_imp_bounded
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceWithCalleesFull rootBody calleeSigs table rawTrace = true) :
    checkRawByteTraceWithCalleesFullBounded (defaultRawTraceSteps rootBody rawTrace)
      rootBody calleeSigs table rawTrace = true := by
  rw [← checkRawByteTraceWithCalleesFullBoundedFast_eq]
  unfold checkRawByteTraceWithCalleesFull at h_ok
  unfold checkRawByteTraceWithCalleesFullBoundedFast
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    have h_len := decodeRawByteTrace_events_length h_dec
    have h_cal := decodeRawByteTrace_inlinedCallees h_dec
    have h_auto := checkFullMirTraceAuto_checkFullMirTraceFast rootBody _ _
      obsTrace.events obsTrace.outcome h_ok
    unfold defaultRawTraceSteps
    rw [← h_len, ← h_cal]
    exact h_auto

/-- Converse: `checkRawByteTraceWithCalleesFullBounded` acceptance at
`fuel ≤ defaultIntraEventSteps` implies fuel-free `checkRawByteTraceWithCalleesFull`
acceptance. -/
theorem checkRawByteTraceWithCalleesFullBounded_imp_fuelFree_of_le
    {fuel : Nat} (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_le : fuel ≤ defaultIntraEventSteps rootBody rawTrace.inlinedCallees)
    (h_ok :
      checkRawByteTraceWithCalleesFullBounded fuel rootBody calleeSigs table rawTrace = true) :
    checkRawByteTraceWithCalleesFull rootBody calleeSigs table rawTrace = true := by
  rw [← checkRawByteTraceWithCalleesFullBoundedFast_eq] at h_ok
  unfold checkRawByteTraceWithCalleesFullBoundedFast at h_ok
  unfold checkRawByteTraceWithCalleesFull
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rw [h_dec] at h_ok; nomatch h_ok
  | some obsTrace =>
    rw [h_dec] at h_ok
    have h_cal := decodeRawByteTrace_inlinedCallees h_dec
    have h_le' : fuel ≤ defaultIntraEventSteps rootBody obsTrace.inlinedCallees := by
      rw [h_cal]
      exact h_le
    exact checkFullMirTraceFast_imp_within_of_le rootBody h_le' _ _ _ h_ok

/-- The fuel-free branch-erased check is exactly the `*Bounded` check at the automatic
global budget `defaultRawObsErasedTraceSteps`. -/
theorem checkRawByteTraceObsErased_eq_bounded
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    checkRawByteTraceObsErased rootBody calleeSigs table rawTrace =
      checkRawByteTraceObsErasedBounded (defaultRawObsErasedTraceSteps rootBody rawTrace)
        rootBody calleeSigs table rawTrace := by
  unfold checkRawByteTraceObsErased checkRawByteTraceObsErasedBounded
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rfl
  | some obsTrace =>
    have h_len := decodeRawByteTrace_events_length h_dec
    have h_cal := decodeRawByteTrace_inlinedCallees h_dec
    unfold defaultRawObsErasedTraceSteps
    rw [← h_len, ← h_cal]

/-- The fuel-free `WithCallees` branch-erased check is exactly the `*Bounded` check at
the automatic global budget `defaultRawObsErasedTraceSteps`. -/
theorem checkRawByteTraceWithCalleesObsErased_eq_bounded
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    checkRawByteTraceWithCalleesObsErased rootBody calleeSigs table rawTrace =
      checkRawByteTraceWithCalleesObsErasedBounded
        (defaultRawObsErasedTraceSteps rootBody rawTrace)
        rootBody calleeSigs table rawTrace := by
  unfold checkRawByteTraceWithCalleesObsErased checkRawByteTraceWithCalleesObsErasedBounded
  cases h_dec : decodeRawByteTrace rootBody calleeSigs table rawTrace with
  | none => rfl
  | some obsTrace =>
    have h_len := decodeRawByteTrace_events_length h_dec
    have h_cal := decodeRawByteTrace_inlinedCallees h_dec
    unfold defaultRawObsErasedTraceSteps
    rw [← h_len, ← h_cal]

/-- Fuel-free branch-erased certificate from the fuel-free full check: when the full
trace `rawTrace` is accepted, the branch-erased tree reaches a matching outcome along
the call events of `obsErasedTrace = { rawTrace with events := eraseRawBranchEvents
rawTrace.events }` (`h_erase`, discharged by `rfl` on the event lists), with no
branch-erased step budget and no second MIR execution. -/
theorem checkRawByteTraceFull_obsErased_sound
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace obsErasedTrace : RawByteTrace)
    (h_ok : checkRawByteTraceFull rootBody calleeSigs table rawTrace = true)
    (h_erase :
      obsErasedTrace = { rawTrace with events := eraseRawBranchEvents rawTrace.events }) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table obsErasedTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out := by
  subst h_erase
  exact checkRawByteTraceObsErasedBounded_sound _ rootBody calleeSigs table _
    (checkRawByteTraceObsErasedBounded_of_full _ rootBody calleeSigs table rawTrace
      (checkRawByteTraceFull_imp_bounded rootBody calleeSigs table rawTrace h_ok))

/-- `WithCallees` counterpart of `checkRawByteTraceFull_obsErased_sound`. -/
theorem checkRawByteTraceWithCalleesFull_obsErased_sound
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace obsErasedTrace : RawByteTrace)
    (h_ok : checkRawByteTraceWithCalleesFull rootBody calleeSigs table rawTrace = true)
    (h_erase :
      obsErasedTrace = { rawTrace with events := eraseRawBranchEvents rawTrace.events }) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table obsErasedTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out := by
  subst h_erase
  exact checkRawByteTraceWithCalleesObsErasedBounded_sound _ rootBody calleeSigs table _
    (checkRawByteTraceWithCalleesObsErasedBounded_of_full _ rootBody calleeSigs table rawTrace
      (checkRawByteTraceWithCalleesFull_imp_bounded rootBody calleeSigs table rawTrace h_ok))

/-- Diagnostic replay of one observation-driven segment (`checkBranches = true`)
within `fuel` transitions, reporting the exact `TraceReplayDiag` on divergence. -/
@[reducible]
def diagnoseStepFullMirEventWithin (body : CapturedMir) :
    Nat → MirExecState → ObservedEvent → Nat →
      Except TraceReplayDiag (Event MirEffect × MirExecState)
  | 0, st, _, _ =>
    let cur := execStateCursor st
    .error (.outOfFuel cur.1 cur.2)
  | fuel + 1, st, ev, remCount =>
    match stepMirState body st with
    | .ret _ => .error (.unconsumedEventsRemaining remCount)
    | .tau st' => diagnoseStepFullMirEventWithin body fuel st' ev remCount
    | .vis i k =>
      elimMirVis
        (fun kind _ =>
          let cur := execStateCursor st
          .error (.stepFaulted kind cur.1 cur.2))
        (fun _ =>
          let cur := execStateCursor st
          .error (.stepFaulted .unsupported cur.1 cur.2))
        (fun actualTag kObs =>
          let cur := execStateCursor st
          match ev with
          | .branch expectedTag =>
            if Nat.beq actualTag expectedTag then
              .ok (⟨.inr (.inl (.emit (.event actualTag))), PUnit.unit⟩, kObs PUnit.unit)
            else
              .error (.branchTagMismatch actualTag expectedTag cur.1)
          | _ => .error (.branchTagMismatch actualTag 0 cur.1))
        (fun req kCall =>
          let blockIdx := (execStateCursor st).1
          let activeBody := execStateActiveBody body st
          match findActiveCallImpurePtrArgIdx? activeBody blockIdx req with
          | some argIdx => .error (.impureExtCallPtrArg req.defPath 0 argIdx)
          | none =>
            match diagnoseCallObservedEvent req blockIdx ev with
            | .error diag => .error diag
            | .ok ans => .ok (⟨.inr (.inr (.call req)), ans⟩, kCall ans))
        i k

/-- Allocation-free diagnostic replay of one observation-driven segment
(`checkBranches = true`) within `fuel` transitions. -/
@[reducible]
def diagnoseStepFullMirEventFastWithin (body : CapturedMir) :
    Nat → MirExecState → ObservedEvent → Nat → Except TraceReplayDiag MirExecState
  | 0, st, _, _ =>
    let cur := execStateCursor st
    .error (.outOfFuel cur.1 cur.2)
  | fuel + 1, st, ev, remCount =>
    match stepMirState body st with
    | .ret _ => .error (.unconsumedEventsRemaining remCount)
    | .tau st' => diagnoseStepFullMirEventFastWithin body fuel st' ev remCount
    | .vis i k =>
      elimMirVis
        (fun kind _ =>
          let cur := execStateCursor st
          .error (.stepFaulted kind cur.1 cur.2))
        (fun _ =>
          let cur := execStateCursor st
          .error (.stepFaulted .unsupported cur.1 cur.2))
        (fun actualTag kObs =>
          let cur := execStateCursor st
          match ev with
          | .branch expectedTag =>
            if Nat.beq actualTag expectedTag then
              .ok (kObs PUnit.unit)
            else
              .error (.branchTagMismatch actualTag expectedTag cur.1)
          | _ => .error (.branchTagMismatch actualTag 0 cur.1))
        (fun req kCall =>
          let blockIdx := (execStateCursor st).1
          let activeBody := execStateActiveBody body st
          match findActiveCallImpurePtrArgIdx? activeBody blockIdx req with
          | some argIdx => .error (.impureExtCallPtrArg req.defPath 0 argIdx)
          | none =>
            match diagnoseCallObservedEvent req blockIdx ev with
            | .error diag => .error diag
            | .ok ans => .ok (kCall ans))
        i k

/-- Diagnostic replay of the final silent segment (`events = []`) within `fuel`
transitions. -/
@[reducible]
def diagnoseFinishFullMirTraceWithin (body : CapturedMir) :
    Nat → MirExecState → ObservedOutcome → TraceReplayDiag
  | 0, st, _ =>
    let cur := execStateCursor st
    .outOfFuel cur.1 cur.2
  | fuel + 1, st, outcome =>
    match stepMirState body st with
    | .ret actualOut =>
      if checkOutcomeMatches outcome actualOut then
        .ok [] actualOut
      else
        .outcomeMismatch actualOut outcome
    | .tau st' => diagnoseFinishFullMirTraceWithin body fuel st' outcome
    | .vis i k =>
      elimMirVis
        (fun kind _ =>
          let cur := execStateCursor st
          .stepFaulted kind cur.1 cur.2)
        (fun _ =>
          let cur := execStateCursor st
          .stepFaulted .unsupported cur.1 cur.2)
        (fun actualTag _ =>
          let cur := execStateCursor st
          .branchTagMismatch actualTag 0 cur.1)
        (fun req _ =>
          let blockIdx := (execStateCursor st).1
          let activeBody := execStateActiveBody body st
          match findActiveCallImpurePtrArgIdx? activeBody blockIdx req with
          | some argIdx => .impureExtCallPtrArg req.defPath 0 argIdx
          | none => .unexpectedExtCall req.defPath blockIdx)
        i k

/-- Observation-driven diagnostic replay (`checkBranches = true`) recursing
structurally on `events : List ObservedEvent` with per-segment budget `intra`. -/
@[reducible]
def diagnoseFullMirTraceWithin (body : CapturedMir) (intra : Nat) :
    MirExecState → List ObservedEvent → ObservedOutcome → TraceReplayDiag
  | st, [], outcome => diagnoseFinishFullMirTraceWithin body intra st outcome
  | st, ev :: rest, outcome =>
    match diagnoseStepFullMirEventWithin body intra st ev (ev :: rest).length with
    | .error diag => diag
    | .ok (e, st') =>
      match diagnoseFullMirTraceWithin body intra st' rest outcome with
      | .ok trRest out => .ok (e :: trRest) out
      | diag => diag

/-- Tail-recursive, allocation-free observation-driven diagnostic replay
(`checkBranches = true`) recursing structurally on `events : List ObservedEvent`
with per-segment budget `intra`. -/
@[reducible]
def diagnoseFullMirTraceFastWithin (body : CapturedMir) (intra : Nat) :
    MirExecState → List ObservedEvent → ObservedOutcome → TraceReplayDiag
  | st, [], outcome => diagnoseFinishFullMirTraceWithin body intra st outcome
  | st, ev :: rest, outcome =>
    match diagnoseStepFullMirEventFastWithin body intra st ev (ev :: rest).length with
    | .error diag => diag
    | .ok st' => diagnoseFullMirTraceFastWithin body intra st' rest outcome

/-- Fuel-free observation-driven diagnostic replay (`checkBranches = true`) with
per-segment budget `defaultIntraEventSteps body inlinedCallees`. -/
@[reducible]
def diagnoseFullMirTraceAuto (body : CapturedMir) (inlinedCallees : List CapturedMir)
    (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome) :
    TraceReplayDiag :=
  diagnoseFullMirTraceWithin body (defaultIntraEventSteps body inlinedCallees)
    st events outcome

/-- Tail-recursive, allocation-free fuel-free observation-driven diagnostic replay
(`checkBranches = true`). -/
@[reducible]
def diagnoseFullMirTraceFastAuto (body : CapturedMir) (inlinedCallees : List CapturedMir)
    (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome) :
    TraceReplayDiag :=
  diagnoseFullMirTraceFastWithin body (defaultIntraEventSteps body inlinedCallees)
    st events outcome

theorem diagnoseStepFullMirEventWithin_toOption (body : CapturedMir) :
    ∀ (fuel : Nat) (st : MirExecState) (ev : ObservedEvent) (remCount : Nat),
      (diagnoseStepFullMirEventWithin body fuel st ev remCount).toOption =
        stepFullMirEventWithin body fuel st ev := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ fuel' ih =>
    intro st ev remCount
    unfold diagnoseStepFullMirEventWithin stepFullMirEventWithin
    cases stepMirState body st with
    | ret _ => rfl
    | tau st' => exact ih st' ev remCount
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · cases f; rfl
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent => rfl
          | event actualTag =>
            dsimp only [elimMirVis]
            cases ev with
            | branch expectedTag =>
              dsimp only
              cases Nat.beq actualTag expectedTag <;> rfl
            | _ => rfl
      · cases callReq with
        | call req =>
          dsimp only [elimMirVis]
          cases findActiveCallImpurePtrArgIdx?
              (execStateActiveBody body st) (execStateCursor st).1 req with
          | some _ => rfl
          | none =>
            dsimp only
            have hmatch := diagnoseCallObservedEvent_toOption req (execStateCursor st).1 ev
            cases hd : diagnoseCallObservedEvent req (execStateCursor st).1 ev with
            | error _ =>
              rw [hd] at hmatch
              rw [← hmatch]
              rfl
            | ok ans =>
              rw [hd] at hmatch
              rw [← hmatch]
              rfl

theorem diagnoseStepFullMirEventWithin_error_not_ok (body : CapturedMir) :
    ∀ {fuel : Nat} {st : MirExecState} {ev : ObservedEvent} {remCount : Nat}
      {d : TraceReplayDiag},
      diagnoseStepFullMirEventWithin body fuel st ev remCount = .error d →
      d.isOk = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ d h
    injection h with h; subst h; rfl
  | succ fuel' ih =>
    intro st ev remCount d h
    unfold diagnoseStepFullMirEventWithin at h
    cases hs : stepMirState body st with
    | ret _ =>
      rw [hs] at h; injection h with h; subst h; rfl
    | tau st' =>
      rw [hs] at h; exact ih h
    | vis i k =>
      rw [hs] at h
      rcases i with f | (obsReq | callReq)
      · cases f; injection h with h; subst h; rfl
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent => injection h with h; subst h; rfl
          | event actualTag =>
            dsimp only [elimMirVis] at h
            cases ev with
            | branch expectedTag =>
              dsimp only at h
              revert h
              cases Nat.beq actualTag expectedTag <;> intro h
              · injection h with h; subst h; rfl
              · nomatch h
            | extCall _ _ _ => injection h with h; subst h; rfl
            | extCallPanic _ _ => injection h with h; subst h; rfl
            | extCallAbort _ _ => injection h with h; subst h; rfl
      · cases callReq with
        | call req =>
          dsimp only [elimMirVis] at h
          cases h_imp : findActiveCallImpurePtrArgIdx?
              (execStateActiveBody body st) (execStateCursor st).1 req with
          | some _ =>
            rw [h_imp] at h; injection h with h; subst h; rfl
          | none =>
            rw [h_imp] at h
            dsimp only at h
            cases hd : diagnoseCallObservedEvent req (execStateCursor st).1 ev with
            | error d' =>
              rw [hd] at h; injection h with h; subst h
              exact diagnoseCallObservedEvent_error_not_ok hd
            | ok _ =>
              rw [hd] at h; nomatch h

theorem diagnoseStepFullMirEventFastWithin_eq (body : CapturedMir) :
    ∀ (fuel : Nat) (st : MirExecState) (ev : ObservedEvent) (remCount : Nat),
      diagnoseStepFullMirEventFastWithin body fuel st ev remCount =
        (diagnoseStepFullMirEventWithin body fuel st ev remCount).map Prod.snd := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ fuel' ih =>
    intro st ev remCount
    unfold diagnoseStepFullMirEventFastWithin diagnoseStepFullMirEventWithin
    cases stepMirState body st with
    | ret _ => rfl
    | tau st' => exact ih st' ev remCount
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · cases f; rfl
      · cases obsReq with
        | emit obs =>
          cases obs with
          | silent => rfl
          | event actualTag =>
            dsimp only [elimMirVis]
            cases ev with
            | branch expectedTag =>
              dsimp only
              cases Nat.beq actualTag expectedTag <;> rfl
            | _ => rfl
      · cases callReq with
        | call req =>
          dsimp only [elimMirVis]
          cases findActiveCallImpurePtrArgIdx?
              (execStateActiveBody body st) (execStateCursor st).1 req with
          | some _ => rfl
          | none =>
            dsimp only
            cases diagnoseCallObservedEvent req (execStateCursor st).1 ev <;> rfl

theorem diagnoseFinishFullMirTraceWithin_isOk (body : CapturedMir) :
    ∀ (fuel : Nat) (st : MirExecState) (outcome : ObservedOutcome),
      (diagnoseFinishFullMirTraceWithin body fuel st outcome).isOk =
        checkFullMirFinishWithin body fuel st outcome := by
  intro fuel
  induction fuel with
  | zero => intro _ _; rfl
  | succ fuel' ih =>
    intro st outcome
    unfold diagnoseFinishFullMirTraceWithin checkFullMirFinishWithin
    cases stepMirState body st with
    | ret actualOut =>
      dsimp only
      cases checkOutcomeMatches outcome actualOut <;> rfl
    | tau st' => exact ih st' outcome
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · cases f; rfl
      · cases obsReq with
        | emit obs =>
          cases obs <;> rfl
      · cases callReq with
        | call req =>
          dsimp only [elimMirVis]
          cases findActiveCallImpurePtrArgIdx?
              (execStateActiveBody body st) (execStateCursor st).1 req <;> rfl

theorem diagnoseFinishFullMirTraceWithin_eraseTrace (body : CapturedMir) :
    ∀ (fuel : Nat) (st : MirExecState) (outcome : ObservedOutcome),
      (diagnoseFinishFullMirTraceWithin body fuel st outcome).eraseTrace =
        diagnoseFinishFullMirTraceWithin body fuel st outcome := by
  intro fuel
  induction fuel with
  | zero => intro _ _; rfl
  | succ fuel' ih =>
    intro st outcome
    unfold diagnoseFinishFullMirTraceWithin
    cases stepMirState body st with
    | ret actualOut =>
      dsimp only
      cases checkOutcomeMatches outcome actualOut <;> rfl
    | tau st' => exact ih st' outcome
    | vis i k =>
      rcases i with f | (obsReq | callReq)
      · cases f; rfl
      · cases obsReq with
        | emit obs =>
          cases obs <;> rfl
      · cases callReq with
        | call req =>
          dsimp only [elimMirVis]
          cases findActiveCallImpurePtrArgIdx?
              (execStateActiveBody body st) (execStateCursor st).1 req <;> rfl

/-- Exact agreement between `diagnoseFullMirTraceWithin` and
`checkFullMirTraceWithin` at every per-segment budget `intra`. -/
theorem diagnoseFullMirTraceWithin_isOk (body : CapturedMir) (intra : Nat) :
    ∀ (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome),
      (diagnoseFullMirTraceWithin body intra st events outcome).isOk =
        checkFullMirTraceWithin body intra st events outcome := by
  intro st events
  induction events generalizing st with
  | nil =>
    intro outcome
    unfold diagnoseFullMirTraceWithin checkFullMirTraceWithin
    exact diagnoseFinishFullMirTraceWithin_isOk body intra st outcome
  | cons ev rest ih =>
    intro outcome
    unfold diagnoseFullMirTraceWithin checkFullMirTraceWithin
    rw [stepFullMirEventFastWithin_eq, ← diagnoseStepFullMirEventWithin_toOption body intra st ev (ev :: rest).length]
    cases h_seg : diagnoseStepFullMirEventWithin body intra st ev (ev :: rest).length with
    | error d =>
      exact diagnoseStepFullMirEventWithin_error_not_ok body h_seg
    | ok pair =>
      rcases pair with ⟨e, st'⟩
      dsimp only [Except.toOption, Option.map]
      exact (diagnose_cons_ok_isOk e
        (diagnoseFullMirTraceWithin body intra st' rest outcome)).trans
        (ih st' outcome)

/-- Tail-recursive `diagnoseFullMirTraceFastWithin` equals `eraseTrace` of
`diagnoseFullMirTraceWithin`. -/
theorem diagnoseFullMirTraceFastWithin_eq (body : CapturedMir) (intra : Nat) :
    ∀ (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome),
      diagnoseFullMirTraceFastWithin body intra st events outcome =
        (diagnoseFullMirTraceWithin body intra st events outcome).eraseTrace := by
  intro st events
  induction events generalizing st with
  | nil =>
    intro outcome
    unfold diagnoseFullMirTraceFastWithin diagnoseFullMirTraceWithin
    exact (diagnoseFinishFullMirTraceWithin_eraseTrace body intra st outcome).symm
  | cons ev rest ih =>
    intro outcome
    unfold diagnoseFullMirTraceFastWithin diagnoseFullMirTraceWithin
    rw [diagnoseStepFullMirEventFastWithin_eq]
    cases h_seg : diagnoseStepFullMirEventWithin body intra st ev (ev :: rest).length with
    | error d =>
      exact (TraceReplayDiag.eraseTrace_eq_self_of_not_isOk
        (diagnoseStepFullMirEventWithin_error_not_ok body h_seg)).symm
    | ok pair =>
      rcases pair with ⟨e, st'⟩
      dsimp only [Except.map]
      rw [ih st' outcome]
      cases diagnoseFullMirTraceWithin body intra st' rest outcome <;> rfl

/-- Exact agreement between `diagnoseFullMirTraceAuto` and `checkFullMirTraceAuto`. -/
theorem diagnoseFullMirTraceAuto_isOk
    (body : CapturedMir) (inlinedCallees : List CapturedMir)
    (st : MirExecState) (events : List ObservedEvent) (outcome : ObservedOutcome) :
    (diagnoseFullMirTraceAuto body inlinedCallees st events outcome).isOk =
      checkFullMirTraceAuto body inlinedCallees st events outcome :=
  diagnoseFullMirTraceWithin_isOk body (defaultIntraEventSteps body inlinedCallees)
    st events outcome

/-- Fuel-free observation-driven diagnostic replay of a decoded `ObservedTrace`
(`checkBranches = true`). -/
@[reducible]
def diagnoseFullObservedTrace (body : CapturedMir) (trace : ObservedTrace) :
    TraceReplayDiag :=
  let mem := { trace.initMem with callees := trace.inlinedCallees }
  let s := initMachineStateWithMemory body trace.args mem
  diagnoseFullMirTraceAuto body trace.inlinedCallees (.running s) trace.events trace.outcome

/-- Fuel-free observation-driven diagnostic replay of a decoded `ObservedTrace`
with `callees` (`checkBranches = true`). -/
@[reducible]
def diagnoseFullObservedTraceWithCallees (body : CapturedMir) (trace : ObservedTrace) :
    TraceReplayDiag :=
  let s := initMachineStateWithMemoryAndCallees body trace.args trace.initMem trace.inlinedCallees
  diagnoseFullMirTraceAuto body trace.inlinedCallees (.running s) trace.events trace.outcome

/-- Tail-recursive allocation-free fuel-free diagnostic replay of a decoded
`ObservedTrace` (`checkBranches = true`). -/
@[reducible]
def diagnoseFullObservedTraceFast (body : CapturedMir) (trace : ObservedTrace) :
    TraceReplayDiag :=
  let mem := { trace.initMem with callees := trace.inlinedCallees }
  let s := initMachineStateWithMemory body trace.args mem
  diagnoseFullMirTraceFastAuto body trace.inlinedCallees (.running s) trace.events trace.outcome

/-- Tail-recursive allocation-free fuel-free diagnostic replay of a decoded
`ObservedTrace` with `callees` (`checkBranches = true`). -/
@[reducible]
def diagnoseFullObservedTraceWithCalleesFast (body : CapturedMir) (trace : ObservedTrace) :
    TraceReplayDiag :=
  let s := initMachineStateWithMemoryAndCallees body trace.args trace.initMem trace.inlinedCallees
  diagnoseFullMirTraceFastAuto body trace.inlinedCallees (.running s) trace.events trace.outcome

/-- Fuel-free diagnostic replay for `checkRawByteTraceFull`, recursing structurally
on `events` with the automatic per-segment budget `defaultIntraEventSteps` so that
`(diagnoseRawByteTraceFull ...).isOk = checkRawByteTraceFull ...` holds identically. -/
@[reducible]
def diagnoseRawByteTraceFull (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
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
           activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩ =>
          diagnoseFullObservedTrace rootBody {
            args := args
            initMem := ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
                        activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩
            inlinedCallees := rawTrace.inlinedCallees
            events := events
            outcome := outcome
          }

/-- Tail-recursive allocation-free fuel-free diagnostic replay for `checkRawByteTraceFull`. -/
@[reducible]
def diagnoseRawByteTraceFullFast (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
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
           activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩ =>
          diagnoseFullObservedTraceFast rootBody {
            args := args
            initMem := ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
                        activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩
            inlinedCallees := rawTrace.inlinedCallees
            events := events
            outcome := outcome
          }

/-- Global-budget fuel-free diagnostic replay (`diagnoseRawByteTraceFullBounded` at
`defaultRawTraceSteps`). -/
@[reducible]
def diagnoseRawByteTraceFullGlobal (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceFullBounded (defaultRawTraceSteps rootBody rawTrace)
    rootBody calleeSigs table rawTrace

/-- Fuel-free diagnostic replay for `checkRawByteTraceObsErased`. -/
@[reducible]
def diagnoseRawByteTraceObsErased (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceObsErasedBounded (defaultRawObsErasedTraceSteps rootBody rawTrace)
    rootBody calleeSigs table rawTrace

/-- Tail-recursive allocation-free fuel-free diagnostic replay for `checkRawByteTraceObsErased`. -/
@[reducible]
def diagnoseRawByteTraceObsErasedFast (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceObsErasedBoundedFast (defaultRawObsErasedTraceSteps rootBody rawTrace)
    rootBody calleeSigs table rawTrace

/-- Fuel-free diagnostic replay for `checkRawByteTraceWithCalleesFull`, recursing
structurally on `events` with the automatic per-segment budget `defaultIntraEventSteps`. -/
@[reducible]
def diagnoseRawByteTraceWithCalleesFull (rootBody : CapturedMir)
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
           activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩ =>
          diagnoseFullObservedTraceWithCallees rootBody {
            args := args
            initMem := ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
                        activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩
            inlinedCallees := rawTrace.inlinedCallees
            events := events
            outcome := outcome
          }

/-- Tail-recursive allocation-free fuel-free diagnostic replay for
`checkRawByteTraceWithCalleesFull`. -/
@[reducible]
def diagnoseRawByteTraceWithCalleesFullFast (rootBody : CapturedMir)
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
           activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩ =>
          diagnoseFullObservedTraceWithCalleesFast rootBody {
            args := args
            initMem := ⟨nextAllocId, globals, borrows, nextTag, callees, traitImpls, callStack,
                        activeCallee, activeProtectors, nextProtector, callerLocals, fnPtrs, exposedAllocIds⟩
            inlinedCallees := rawTrace.inlinedCallees
            events := events
            outcome := outcome
          }

/-- Global-budget fuel-free `WithCallees` diagnostic replay. -/
@[reducible]
def diagnoseRawByteTraceWithCalleesFullGlobal (rootBody : CapturedMir)
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceWithCalleesFullBounded (defaultRawTraceSteps rootBody rawTrace)
    rootBody calleeSigs table rawTrace

/-- Fuel-free diagnostic replay for `checkRawByteTraceWithCalleesObsErased`. -/
@[reducible]
def diagnoseRawByteTraceWithCalleesObsErased (rootBody : CapturedMir)
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceWithCalleesObsErasedBounded
    (defaultRawObsErasedTraceSteps rootBody rawTrace) rootBody calleeSigs table rawTrace

/-- Tail-recursive allocation-free fuel-free diagnostic replay for
`checkRawByteTraceWithCalleesObsErased`. -/
@[reducible]
def diagnoseRawByteTraceWithCalleesObsErasedFast (rootBody : CapturedMir)
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable)
    (rawTrace : RawByteTrace) : TraceReplayDiag :=
  diagnoseRawByteTraceWithCalleesObsErasedBoundedFast
    (defaultRawObsErasedTraceSteps rootBody rawTrace) rootBody calleeSigs table rawTrace

/-- The fuel-free full diagnosis agrees identically with the fuel-free full check. -/
theorem diagnoseRawByteTraceFull_isOk
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceFull rootBody calleeSigs table rawTrace).isOk =
      checkRawByteTraceFull rootBody calleeSigs table rawTrace := by
  unfold diagnoseRawByteTraceFull checkRawByteTraceFull decodeRawByteTrace
  rw [← diagnoseDecodeFnArgs_toOption, ← diagnoseDecodeRawEventsAux_toOption calleeSigs table 0]
  cases hargs : diagnoseDecodeFnArgs rootBody table rawTrace.rawArgs with
  | error _ => rfl
  | ok args =>
    cases hevs : diagnoseDecodeRawEventsAux calleeSigs table 0 rawTrace.events with
    | error d => exact diagnoseDecodeRawEventsAux_error_not_ok hevs
    | ok events =>
      cases decodeRawObservedOutcome rootBody table rawTrace.outcome with
      | none => rfl
      | some outcome =>
        exact diagnoseFullMirTraceAuto_isOk rootBody rawTrace.inlinedCallees _ events outcome

/-- The fuel-free `WithCallees` full diagnosis agrees identically with the fuel-free
`WithCallees` full check. -/
theorem diagnoseRawByteTraceWithCalleesFull_isOk
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceWithCalleesFull rootBody calleeSigs table rawTrace).isOk =
      checkRawByteTraceWithCalleesFull rootBody calleeSigs table rawTrace := by
  unfold diagnoseRawByteTraceWithCalleesFull checkRawByteTraceWithCalleesFull decodeRawByteTrace
  rw [← diagnoseDecodeFnArgs_toOption, ← diagnoseDecodeRawEventsAux_toOption calleeSigs table 0]
  cases hargs : diagnoseDecodeFnArgs rootBody table rawTrace.rawArgs with
  | error _ => rfl
  | ok args =>
    cases hevs : diagnoseDecodeRawEventsAux calleeSigs table 0 rawTrace.events with
    | error d => exact diagnoseDecodeRawEventsAux_error_not_ok hevs
    | ok events =>
      cases decodeRawObservedOutcome rootBody table rawTrace.outcome with
      | none => rfl
      | some outcome =>
        exact diagnoseFullMirTraceAuto_isOk rootBody rawTrace.inlinedCallees _ events outcome

theorem diagnoseRawByteTraceFullFast_eq
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    diagnoseRawByteTraceFullFast rootBody calleeSigs table rawTrace =
      (diagnoseRawByteTraceFull rootBody calleeSigs table rawTrace).eraseTrace := by
  unfold diagnoseRawByteTraceFullFast diagnoseRawByteTraceFull
  cases diagnoseDecodeFnArgs rootBody table rawTrace.rawArgs with
  | error _ => rfl
  | ok args =>
    cases hevs : diagnoseDecodeRawEventsAux calleeSigs table 0 rawTrace.events with
    | error d =>
      exact (TraceReplayDiag.eraseTrace_eq_self_of_not_isOk
        (diagnoseDecodeRawEventsAux_error_not_ok hevs)).symm
    | ok events =>
      cases decodeRawObservedOutcome rootBody table rawTrace.outcome with
      | none => rfl
      | some outcome =>
        exact diagnoseFullMirTraceFastWithin_eq rootBody _ _ events outcome

theorem diagnoseRawByteTraceFullFast_isOk
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceFullFast rootBody calleeSigs table rawTrace).isOk =
      checkRawByteTraceFull rootBody calleeSigs table rawTrace := by
  rw [diagnoseRawByteTraceFullFast_eq, TraceReplayDiag.isOk_eraseTrace,
      diagnoseRawByteTraceFull_isOk]

theorem diagnoseRawByteTraceFullFast_tagName
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceFullFast rootBody calleeSigs table rawTrace).tagName =
      (diagnoseRawByteTraceFull rootBody calleeSigs table rawTrace).tagName := by
  rw [diagnoseRawByteTraceFullFast_eq, TraceReplayDiag.tagName_eraseTrace]

/-- Exact equivalence between an `"ok"` tag of `diagnoseRawByteTraceFull` and
`checkRawByteTraceFull = true`. -/
theorem diagnoseRawByteTraceFull_tag_ok_iff_check
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceFull rootBody calleeSigs table rawTrace).tagName = "ok" ↔
      checkRawByteTraceFull rootBody calleeSigs table rawTrace = true := by
  rw [← diagnoseRawByteTraceFull_isOk]
  exact ⟨TraceReplayDiag.isOk_of_tagName_eq_ok, TraceReplayDiag.tagName_eq_ok_of_isOk⟩

/-- Exact equivalence between an `"ok"` tag of `diagnoseRawByteTraceWithCalleesFull`
and `checkRawByteTraceWithCalleesFull = true`. -/
theorem diagnoseRawByteTraceWithCalleesFull_tag_ok_iff_check
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceWithCalleesFull rootBody calleeSigs table rawTrace).tagName = "ok" ↔
      checkRawByteTraceWithCalleesFull rootBody calleeSigs table rawTrace = true := by
  rw [← diagnoseRawByteTraceWithCalleesFull_isOk]
  exact ⟨TraceReplayDiag.isOk_of_tagName_eq_ok, TraceReplayDiag.tagName_eq_ok_of_isOk⟩

/-- A trace accepted by the fuel-free full check is diagnosed `"ok"`. -/
theorem diagnoseRawByteTraceFull_tag_ok_of_check
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceFull rootBody calleeSigs table rawTrace = true) :
    (diagnoseRawByteTraceFull rootBody calleeSigs table rawTrace).tagName = "ok" :=
  (diagnoseRawByteTraceFull_tag_ok_iff_check rootBody calleeSigs table rawTrace).mpr h_ok

/-- A trace accepted by the fuel-free `WithCallees` full check is diagnosed `"ok"`. -/
theorem diagnoseRawByteTraceWithCalleesFull_tag_ok_of_check
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_ok : checkRawByteTraceWithCalleesFull rootBody calleeSigs table rawTrace = true) :
    (diagnoseRawByteTraceWithCalleesFull rootBody calleeSigs table rawTrace).tagName = "ok" :=
  (diagnoseRawByteTraceWithCalleesFull_tag_ok_iff_check
    rootBody calleeSigs table rawTrace).mpr h_ok

/-- The fuel-free branch-erased diagnosis agrees exactly with the fuel-free check. -/
theorem diagnoseRawByteTraceObsErased_isOk
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceObsErased rootBody calleeSigs table rawTrace).isOk =
      checkRawByteTraceObsErased rootBody calleeSigs table rawTrace :=
  (diagnoseRawByteTraceObsErasedBounded_isOk _ rootBody calleeSigs table rawTrace).trans
    (checkRawByteTraceObsErased_eq_bounded rootBody calleeSigs table rawTrace).symm

/-- Exact equivalence between an `"ok"` tag of `diagnoseRawByteTraceObsErased`
and `checkRawByteTraceObsErased = true`. -/
theorem diagnoseRawByteTraceObsErased_tag_ok_iff_check
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceObsErased rootBody calleeSigs table rawTrace).tagName = "ok" ↔
      checkRawByteTraceObsErased rootBody calleeSigs table rawTrace = true := by
  rw [← diagnoseRawByteTraceObsErased_isOk]
  exact ⟨TraceReplayDiag.isOk_of_tagName_eq_ok, TraceReplayDiag.tagName_eq_ok_of_isOk⟩

/-- The fuel-free `WithCallees` branch-erased diagnosis agrees exactly with the
fuel-free check. -/
theorem diagnoseRawByteTraceWithCalleesObsErased_isOk
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceWithCalleesObsErased rootBody calleeSigs table rawTrace).isOk =
      checkRawByteTraceWithCalleesObsErased rootBody calleeSigs table rawTrace :=
  (diagnoseRawByteTraceWithCalleesObsErasedBounded_isOk _ rootBody calleeSigs table
      rawTrace).trans
    (checkRawByteTraceWithCalleesObsErased_eq_bounded rootBody calleeSigs table rawTrace).symm

/-- Exact equivalence between an `"ok"` tag of `diagnoseRawByteTraceWithCalleesObsErased`
and `checkRawByteTraceWithCalleesObsErased = true`. -/
theorem diagnoseRawByteTraceWithCalleesObsErased_tag_ok_iff_check
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace) :
    (diagnoseRawByteTraceWithCalleesObsErased
        rootBody calleeSigs table rawTrace).tagName = "ok" ↔
      checkRawByteTraceWithCalleesObsErased rootBody calleeSigs table rawTrace = true := by
  rw [← diagnoseRawByteTraceWithCalleesObsErased_isOk]
  exact ⟨TraceReplayDiag.isOk_of_tagName_eq_ok, TraceReplayDiag.tagName_eq_ok_of_isOk⟩

/-- Fuel-free soundness of an `"ok"` full diagnosis. -/
theorem diagnoseRawByteTraceFull_tag_ok_sound
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_tag : (diagnoseRawByteTraceFull rootBody calleeSigs table rawTrace).tagName = "ok") :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out :=
  checkRawByteTraceFull_sound rootBody calleeSigs table rawTrace
    ((diagnoseRawByteTraceFull_tag_ok_iff_check rootBody calleeSigs table rawTrace).mp h_tag)

/-- Fuel-free soundness of an `"ok"` branch-erased diagnosis. -/
theorem diagnoseRawByteTraceObsErased_tag_ok_sound
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_tag :
      (diagnoseRawByteTraceObsErased rootBody calleeSigs table rawTrace).tagName = "ok") :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out :=
  diagnoseRawByteTraceObsErasedBounded_tag_ok_sound _ rootBody calleeSigs table rawTrace h_tag

/-- Fuel-free soundness of an `"ok"` `WithCallees` full diagnosis. -/
theorem diagnoseRawByteTraceWithCalleesFull_tag_ok_sound
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_tag :
      (diagnoseRawByteTraceWithCalleesFull rootBody calleeSigs table rawTrace).tagName = "ok") :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out :=
  checkRawByteTraceWithCalleesFull_sound rootBody calleeSigs table rawTrace
    ((diagnoseRawByteTraceWithCalleesFull_tag_ok_iff_check
      rootBody calleeSigs table rawTrace).mp h_tag)

/-- Fuel-free soundness of an `"ok"` `WithCallees` branch-erased diagnosis. -/
theorem diagnoseRawByteTraceWithCalleesObsErased_tag_ok_sound
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace : RawByteTrace)
    (h_tag :
      (diagnoseRawByteTraceWithCalleesObsErased
        rootBody calleeSigs table rawTrace).tagName = "ok") :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table rawTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out :=
  diagnoseRawByteTraceWithCalleesObsErasedBounded_tag_ok_sound _ rootBody calleeSigs table
    rawTrace h_tag

/-- Fuel-free branch-erased certificate from an `"ok"` fuel-free full diagnosis
(`diagnoseRawByteTraceFull`), with `h_erase` discharged by `rfl` on the event lists:
the three theorems a generated chunk emits per recording need one MIR execution. -/
theorem diagnoseRawByteTraceFull_tag_ok_obsErased_sound
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace obsErasedTrace : RawByteTrace)
    (h_tag : (diagnoseRawByteTraceFull rootBody calleeSigs table rawTrace).tagName = "ok")
    (h_erase :
      obsErasedTrace = { rawTrace with events := eraseRawBranchEvents rawTrace.events }) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table obsErasedTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTree rootBody obsTrace.args
          { obsTrace.initMem with callees := obsTrace.inlinedCallees })
        tr out :=
  checkRawByteTraceFull_obsErased_sound rootBody calleeSigs table rawTrace obsErasedTrace
    ((diagnoseRawByteTraceFull_tag_ok_iff_check rootBody calleeSigs table rawTrace).mp h_tag)
    h_erase

/-- `WithCallees` counterpart of `diagnoseRawByteTraceFull_tag_ok_obsErased_sound`. -/
theorem diagnoseRawByteTraceWithCalleesFull_tag_ok_obsErased_sound
    (rootBody : CapturedMir) (calleeSigs : List CapturedMir)
    (table : ShadowProvenanceTable) (rawTrace obsErasedTrace : RawByteTrace)
    (h_tag :
      (diagnoseRawByteTraceWithCalleesFull rootBody calleeSigs table rawTrace).tagName = "ok")
    (h_erase :
      obsErasedTrace = { rawTrace with events := eraseRawBranchEvents rawTrace.events }) :
    ∃ obsTrace tr out,
      decodeRawByteTrace rootBody calleeSigs table obsErasedTrace = some obsTrace ∧
      MatchesObservedEvents obsTrace.events tr ∧
      MatchesObservedOutcome obsTrace.outcome out ∧
      ReachesRet
        (mirObsErasedStatefulTreeWithCallees
          rootBody obsTrace.args obsTrace.initMem obsTrace.inlinedCallees)
        tr out :=
  checkRawByteTraceWithCalleesFull_obsErased_sound rootBody calleeSigs table rawTrace
    obsErasedTrace
    ((diagnoseRawByteTraceWithCalleesFull_tag_ok_iff_check
      rootBody calleeSigs table rawTrace).mp h_tag)
    h_erase

end Anneal.Rustc.V2026_06_01.TraceCheck
