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
  match obsOut, out with
  | .normal expectedRet, .normal (actualRet, _) => valueEq actualRet expectedRet
  | .panic, .panic => true
  | .abort, .abort => true
  | _, _ => false

theorem checkOutcomeMatches_sound {obsOut : ObservedOutcome} {out : MirOutcome}
    (h : checkOutcomeMatches obsOut out = true) :
    MatchesObservedOutcome obsOut out := by
  cases obsOut with
  | normal expectedRet =>
    cases out with
    | normal p => exact valueEq_sound h
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
    if (req.defPath == defPath) && valueListEq req.args args then
      some (.returned retVal req.memory)
    else
      none
  | .extCallPanic defPath args =>
    if (req.defPath == defPath) && valueListEq req.args args then
      some (.panicked req.memory)
    else
      none
  | .extCallAbort defPath args =>
    if (req.defPath == defPath) && valueListEq req.args args then
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
      (if (req.defPath == defPath) && valueListEq req.args args then
        some (MirCallAns.returned retVal req.memory)
      else
        none) = some ans at h
    revert h
    cases hd : (req.defPath == defPath) <;>
      cases ha : valueListEq req.args args <;> intro h
    · nomatch h
    · nomatch h
    · nomatch h
    · cases h
      exact ⟨beq_iff_eq.mp hd, valueListEq_sound ha, rfl⟩
  | extCallPanic defPath args =>
    change
      (if (req.defPath == defPath) && valueListEq req.args args then
        some (MirCallAns.panicked req.memory)
      else
        none) = some ans at h
    revert h
    cases hd : (req.defPath == defPath) <;>
      cases ha : valueListEq req.args args <;> intro h
    · nomatch h
    · nomatch h
    · nomatch h
    · cases h
      exact ⟨beq_iff_eq.mp hd, valueListEq_sound ha, rfl⟩
  | extCallAbort defPath args =>
    change
      (if (req.defPath == defPath) && valueListEq req.args args then
        some MirCallAns.aborted
      else
        none) = some ans at h
    revert h
    cases hd : (req.defPath == defPath) <;>
      cases ha : valueListEq req.args args <;> intro h
    · nomatch h
    · nomatch h
    · nomatch h
    · cases h
      exact ⟨beq_iff_eq.mp hd, valueListEq_sound ha, rfl⟩

/-! ## 3. Full Trace Replay (`checkBranches = true`) and Soundness -/

/--
Fuel-bounded replay of `events` and `outcome` against `stepMirState body` with
full `MirObsE` (`switchInt`) and `MirCallE` checking (`checkBranches = true`).
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

/-! ## 6. Raw Byte-Slice & Shadow-Provenance Decoding (`RawByteTrace`) -/

/--
Entry in the runtime observer's shadow provenance table mapping a watched native
virtual address range `[baseAddr, baseAddr + byteLen)` to its abstract MIR
`(allocId, tag)` provenance.
-/
structure ShadowAllocEntry : Type where
  baseAddr : Nat
  byteLen : Nat
  allocId : AllocId
  tag : Nat := allocId
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
returning `(allocId, tag, addr - baseAddr)` for the first entry whose range
`[baseAddr, baseAddr + byteLen]` contains `addr`.
-/
@[reducible]
def lookupShadowProvenance :
    ShadowProvenanceTable → Nat → Option (AllocId × Nat × Nat)
  | [], _ => none
  | entry :: rest, addr =>
    if Nat.ble entry.baseAddr addr &&
        Nat.ble addr (Nat.add entry.baseAddr entry.byteLen) then
      some (entry.allocId, entry.tag, Nat.sub addr entry.baseAddr)
    else
      lookupShadowProvenance rest addr

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

/--
Convert a raw runtime byte slice `raw : List UInt8` captured for a value of type
`ty` into `List AbstractByte`, applying `table` to reconstruct `(allocId, tag)`
provenance and relative offsets for thin (8-byte) and wide (16-byte) pointers
and references.
-/
@[reducible]
def rawBytesWithProvenance
    (table : ShadowProvenanceTable) (ty : Ty) (raw : List UInt8) :
    List AbstractByte :=
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
  | _ => rawBytesToAbstractBytes raw

/--
Decode a raw runtime byte slice `raw : List UInt8` into a `Value` of type `ty`
under `layouts` and shadow provenance table `table` using `decodeValueFromBytes`.
-/
@[reducible]
def decodeRawValue
    (layouts : LayoutTable) (table : ShadowProvenanceTable)
    (ty : Ty) (raw : List UInt8) : Option Value :=
  decodeValueFromBytes defaultCodecFuel layouts ty
    (rawBytesWithProvenance table ty raw)

/-- Alias for `decodeRawValue`. -/
abbrev decodeRawValueWithTable := decodeRawValue

/-- Decode a list of raw runtime byte slices against a list of parameter `LocalDecl`s. -/
@[reducible]
def decodeRawArgsByDecls
    (layouts : LayoutTable) (table : ShadowProvenanceTable) :
    List LocalDecl → List (List UInt8) → Option (List Value)
  | _, [] => some []
  | [], _ :: _ => none
  | decl :: declRest, raw :: rawRest =>
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

/-- Decode a single `RawObservedEvent` using `calleeSigs` and `table`. -/
@[reducible]
def decodeRawObservedEvent
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable) :
    RawObservedEvent → Option ObservedEvent
  | .branch tag => some (.branch tag)
  | .extCall defPath rawArgs rawRet =>
    match findCallee? calleeSigs defPath with
    | some sigBody =>
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
      match decodeFnArgsFromRawBytes sigBody table rawArgs with
      | some args => some (.extCallPanic defPath args)
      | none => none
    | none => none
  | .extCallAbort defPath rawArgs =>
    match findCallee? calleeSigs defPath with
    | some sigBody =>
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
`calleeSigs`.
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
    some {
      args := args
      initMem := rawTrace.initMem
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
  | .stepFaulted _ _ _ => "step_faulted"
  | .unexpectedExtCall _ _ => "unexpected_ext_call"
  | .callArgMismatch _ _ => "call_arg_mismatch"
  | .branchTagMismatch _ _ _ => "branch_tag_mismatch"
  | .unconsumedEventsRemaining _ => "unconsumed_events"
  | .outcomeMismatch _ _ => "outcome_mismatch"
  | .outOfFuel _ _ => "out_of_fuel"

/-- Extract the active `(blockIdx, stmtIdx)` program counter from `MirExecState`. -/
@[reducible]
def execStateCursor : MirExecState → Nat × Nat
  | .running s => (s.frame.blockIdx, s.frame.stmtIdx)
  | _ => (0, 0)

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
    if req.defPath == defPath then
      if valueListEq req.args args then
        .ok (.returned retVal req.memory)
      else
        .error (.callArgMismatch req.defPath blockIdx)
    else
      .error (.unexpectedExtCall req.defPath blockIdx)
  | .extCallPanic defPath args =>
    if req.defPath == defPath then
      if valueListEq req.args args then
        .ok (.panicked req.memory)
      else
        .error (.callArgMismatch req.defPath blockIdx)
    else
      .error (.unexpectedExtCall req.defPath blockIdx)
  | .extCallAbort defPath args =>
    if req.defPath == defPath then
      if valueListEq req.args args then
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
    let (lastBlockIdx, lastStmtIdx) := execStateCursor st
    .outOfFuel lastBlockIdx lastStmtIdx
  | fuel' + 1 =>
    let (blockIdx, stmtIdx) := execStateCursor st
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
      .stepFaulted kind blockIdx stmtIdx
    | .vis (.inr (.inl (.emit obs))) k =>
      match checkBranches with
      | false =>
        diagnoseMirExecBounded fuel' false body (k PUnit.unit) events outcome
      | true =>
        match obs with
        | .silent =>
          .stepFaulted .unsupported blockIdx stmtIdx
        | .event actualTag =>
          match events with
          | .branch expectedTag :: rest =>
            if Nat.beq actualTag expectedTag then
              match diagnoseMirExecBounded fuel' true body (k PUnit.unit) rest outcome with
              | .ok trRest out =>
                .ok (⟨.inr (.inl (.emit (.event actualTag))), PUnit.unit⟩ :: trRest) out
              | diag => diag
            else
              .branchTagMismatch actualTag expectedTag blockIdx
          | _ =>
            .branchTagMismatch actualTag 0 blockIdx
    | .vis (.inr (.inr (.call req))) k =>
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
    (layouts : LayoutTable) (table : ShadowProvenanceTable) :
    Nat → List LocalDecl → List (List UInt8) → Except Nat (List Value)
  | _, _, [] => .ok []
  | argIdx, [], _ :: _ => .error argIdx
  | argIdx, decl :: declRest, raw :: rawRest =>
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
Decode `rawEvents` item-by-item while tracking the 0-based event index `evIdx`
to report `.decodeEventFailed evIdx` on the first failing event.
-/
@[reducible]
def diagnoseDecodeRawEventsAux
    (calleeSigs : List CapturedMir) (table : ShadowProvenanceTable) :
    Nat → List RawObservedEvent → Except Nat (List ObservedEvent)
  | _, [] => .ok []
  | evIdx, ev :: rest =>
    match decodeRawObservedEvent calleeSigs table ev with
    | none => .error evIdx
    | some dEv =>
      match diagnoseDecodeRawEventsAux calleeSigs table (evIdx + 1) rest with
      | .ok dRest => .ok (dEv :: dRest)
      | .error failedIdx => .error failedIdx

/--
End-to-end diagnostic replay of a `RawByteTrace`: first pinpoints any
`decodeArgFailed`, `decodeEventFailed`, or `decodeOutcomeFailed` error with its
exact 0-based index, then executes `diagnoseObservedTraceBounded`.
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
    | .error evIdx => .decodeEventFailed evIdx
    | .ok events =>
      match decodeRawObservedOutcome rootBody table rawTrace.outcome with
      | none => .decodeOutcomeFailed
      | some outcome =>
        diagnoseObservedTraceBounded fuel checkBranches rootBody {
          args := args
          initMem := rawTrace.initMem
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
