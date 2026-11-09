/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.IntrinsicLM4_2

/-!
# Saturating Arithmetic Simulation for `LM-4.2`

Relates the `saturating_add` / `saturating_sub` arm of the vendored
`Intrinsics.eval` under `annealIntrinsicHooks` (`annealSaturatingEval`) to
Anneal's `evalSaturatingArith`. Saturating arithmetic never has undefined
behavior: on related operands of one integral type, both machines compute the
overflowing operation (`AddWithOverflow` / `SubWithOverflow`), keep its wrapped
result when it does not overflow, and otherwise saturate at the same bound.

* `annealSaturatingEval_simulation`: `annealSaturatingEval` writes a scalar
  related to Anneal's result to the destination and returns to the target
  block.
* `evalSaturatingArith_sizeBytes`: Anneal's result has the width of its
  operands.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-- `Scalar.toBool` inverts `Scalar.fromBool`. -/
private theorem scalar_fromBool_toBool (b : Bool) :
    (Miri.Memory.Scalar.fromBool (Prov := AnnealProv) b).toBool = .ok b := by
  cases b <;> rfl

/-- The backend scalar of an integral type is signed exactly when its
`IntegerKind` is. -/
private theorem IsIntegralTy.backendRepr_isSigned {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (h : IsIntegralTy ty kind) (layouts : LayoutTable) :
    (translateTy ty layouts).layout.backendRepr.isSigned = .ok kind.signed := by
  rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
  · cases it <;> (simp only [translateTy, hk]; rfl)
  · cases ut <;> (simp only [translateTy, hk]; rfl)

/-- At every valid width, `Size.signedIntMax` and `Scalar.fromInt` produce the
scalar whose bit pattern is Anneal's signed maximum `signedHalfModulus sz - 1`.
-/
private theorem saturating_signedMax {sz : Nat} (hsz : ValidScalarBytes sz) :
    ∃ (bound : Int) (mr : Miri.Memory.ScalarInt),
      (translateSizeBytes sz).signedIntMax = .ok bound ∧
      Miri.Memory.Scalar.fromInt (Prov := AnnealProv) bound (translateSizeBytes sz) =
        .ok (.fromScalarInt mr) ∧
      ScalarRel ⟨Nat.sub (signedHalfModulus sz) 1, sz⟩ mr := by
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl, rfl, by simp [ValidScalarBytes], by decide, rfl, rfl⟩

/-- At every valid width, `Size.signedIntMin` and `Scalar.fromInt` produce the
scalar whose bit pattern is Anneal's signed minimum `signedHalfModulus sz`. -/
private theorem saturating_signedMin {sz : Nat} (hsz : ValidScalarBytes sz) :
    ∃ (bound : Int) (mr : Miri.Memory.ScalarInt),
      (translateSizeBytes sz).signedIntMin = .ok bound ∧
      Miri.Memory.Scalar.fromInt (Prov := AnnealProv) bound (translateSizeBytes sz) =
        .ok (.fromScalarInt mr) ∧
      ScalarRel ⟨signedHalfModulus sz, sz⟩ mr := by
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl, rfl, by simp [ValidScalarBytes], by decide, rfl, rfl⟩

/-- At every valid width, `Size.unsignedIntMax` and `Scalar.fromUInt` produce
the scalar whose bit pattern is Anneal's unsigned maximum
`scalarModulus sz - 1`. -/
private theorem saturating_unsignedMax {sz : Nat} (hsz : ValidScalarBytes sz) :
    ∃ (bound : BitVec 128) (mr : Miri.Memory.ScalarInt),
      (translateSizeBytes sz).unsignedIntMax = .ok bound ∧
      Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) bound (translateSizeBytes sz) =
        .ok (.fromScalarInt mr) ∧
      ScalarRel ⟨Nat.sub (scalarModulus sz) 1, sz⟩ mr := by
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl, rfl, by simp [ValidScalarBytes], by decide, rfl, rfl⟩

/-- At every valid width, `Scalar.fromUInt 0` produces the scalar `0`. -/
private theorem saturating_unsignedZero {sz : Nat} (hsz : ValidScalarBytes sz) :
    ∃ mr : Miri.Memory.ScalarInt,
      Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) 0 (translateSizeBytes sz) =
        .ok (.fromScalarInt mr) ∧
      ScalarRel ⟨0, sz⟩ mr := by
  rcases hsz with rfl | rfl | rfl | rfl | rfl <;>
    (refine ⟨_, rfl, ?_⟩; exact ⟨by simp [ValidScalarBytes], by decide, rfl, rfl⟩)

/-- `AddWithOverflow` (`isAdd`) or `SubWithOverflow` on related operands of
equal width: Anneal's `evalScalarBinOp` returns the wrapped result and the
overflow flag as a two-scalar aggregate without changing locals or memory, and
`lean-miri`'s `IntegerOps.binary` returns `IntegerResult.withOverflow` with a
related wrapped result and the same flag. -/
theorem saturating_withOverflow (isAdd : Bool)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes) (kind : Miri.MIR.IntegerKind)
    (locals : List LocalSlot) (mem : Memory) :
    ∃ (wsc : MirAst.ScalarInt) (wmsc : Miri.Memory.ScalarInt) (ovf : Bool),
      evalScalarBinOp (if isAdd then .addWithOverflow else .subWithOverflow)
          sc₁ sc₂ locals mem kind.signed =
        .ok (.aggregate 0 [.scalar wsc, .scalar (boolToScalar ovf)]) locals mem ∧
      Miri.Interpreter.IntegerOps.binary (if isAdd then .AddWithOverflow else .SubWithOverflow)
          ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
          ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ =
        .ok (.withOverflow wmsc ovf) ∧
      ScalarRel wsc wmsc := by
  cases isAdd
  · have hsim := evalCheckedSub_simulation hrel₁ hrel₂ hsz_eq kind locals mem
    have hshape := integerOps_binary_withOverflow_shape (op := .subWithOverflow)
      (Or.inr (Or.inl rfl)) hrel₁ hrel₂ kind kind
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize evalScalarBinOp .subWithOverflow sc₁ sc₂ locals mem kind.signed = A at hsim ⊢
    generalize hM : Miri.Interpreter.IntegerOps.binary .SubWithOverflow
      ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
      ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ = M at hsim
    cases hsim with
    | scalar sc msc _ => exact absurd hM (hshape.1 msc)
    | withOverflow sc msc ovf hrel => exact ⟨sc, msc, ovf, rfl, rfl, hrel⟩
    | boolean b => exact absurd hM (hshape.2.1 b)
    | ub reason => exact absurd hM (hshape.2.2 reason)
  · have hsim := evalCheckedAdd_simulation hrel₁ hrel₂ hsz_eq kind locals mem
    have hshape := integerOps_binary_withOverflow_shape (op := .addWithOverflow)
      (Or.inl rfl) hrel₁ hrel₂ kind kind
    simp only [↓reduceIte]
    generalize evalScalarBinOp .addWithOverflow sc₁ sc₂ locals mem kind.signed = A at hsim ⊢
    generalize hM : Miri.Interpreter.IntegerOps.binary .AddWithOverflow
      ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
      ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ = M at hsim
    cases hsim with
    | scalar sc msc _ => exact absurd hM (hshape.1 msc)
    | withOverflow sc msc ovf hrel => exact ⟨sc, msc, ovf, rfl, rfl, hrel⟩
    | boolean b => exact absurd hM (hshape.2.1 b)
    | ub reason => exact absurd hM (hshape.2.2 reason)

/-- The wrapped result of `lean-miri`'s `AddWithOverflow` / `SubWithOverflow`
has the width of the operands. -/
private theorem saturating_withOverflow_size (isAdd : Bool)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes) (kind : Miri.MIR.IntegerKind)
    {wmsc : Miri.Memory.ScalarInt} {ovf : Bool}
    (h : Miri.Interpreter.IntegerOps.binary (if isAdd then .AddWithOverflow else .SubWithOverflow)
          ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
          ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ =
        .ok (.withOverflow wmsc ovf)) :
    wmsc.size = translateSizeBytes sc₁.sizeBytes := by
  cases isAdd
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .SubWithOverflow rfl] at h
    dsimp only at h
    rw [arithmeticInt_nonDivRem_eq .SubWithOverflow _ _ _ kind rfl rfl] at h
    obtain ⟨msc', lossy, htr, hrel', _⟩ := truncateInt_spec hrel₁.validBytes kind
      (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits -
        decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits)
    simp only [bind, Except.bind, pure, Except.pure, htr, scalarResultInt,
      Miri.MIR.BinOp.isUnchecked, Miri.MIR.BinOp.isOverflowing, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
      Miri.Interpreter.IntegerResult.withOverflow.injEq] at h
    rw [← h.1]
    exact hrel'.size_eq
  · simp only [↓reduceIte] at h
    rw [integerOps_binary_sameType_eq hrel₁ hrel₂ hsz_eq kind .AddWithOverflow rfl] at h
    dsimp only at h
    rw [arithmeticInt_nonDivRem_eq .AddWithOverflow _ _ _ kind rfl rfl] at h
    obtain ⟨msc', lossy, htr, hrel', _⟩ := truncateInt_spec hrel₁.validBytes kind
      (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits +
        decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits)
    simp only [bind, Except.bind, pure, Except.pure, htr, scalarResultInt,
      Miri.MIR.BinOp.isUnchecked, Miri.MIR.BinOp.isOverflowing, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
      Miri.Interpreter.IntegerResult.withOverflow.injEq] at h
    rw [← h.1]
    exact hrel'.size_eq

/-- `evalSaturatingArith` given the result of its overflowing operation: the
wrapped result `wsc` without overflow; on overflow, for a signed type, the bit
patterns `signedHalfModulus - 1` (maximum) or `signedHalfModulus` (minimum) by
the sign of `lhs`, and for an unsigned type, `scalarModulus - 1` (addition) or
`0` (subtraction). Locals and memory are unchanged. -/
theorem evalSaturatingArith_of_withOverflow {isAdd : Bool} {lhs rhs wsc : MirAst.ScalarInt}
    {locals : List LocalSlot} {mem : Memory} {isSigned ovf : Bool}
    (h : evalScalarBinOp (if isAdd then .addWithOverflow else .subWithOverflow)
        lhs rhs locals mem isSigned =
      .ok (.aggregate 0 [.scalar wsc, .scalar (boolToScalar ovf)]) locals mem) :
    evalSaturatingArith isAdd lhs rhs locals mem isSigned =
      .ok (.scalar (if ovf then
          (if isSigned then
            (if isSignedNegative lhs.bits lhs.sizeBytes then
              ⟨signedHalfModulus lhs.sizeBytes, lhs.sizeBytes⟩
            else ⟨Nat.sub (signedHalfModulus lhs.sizeBytes) 1, lhs.sizeBytes⟩)
          else if isAdd then ⟨Nat.sub (scalarModulus lhs.sizeBytes) 1, lhs.sizeBytes⟩
          else ⟨0, lhs.sizeBytes⟩)
        else wsc)) locals mem := by
  cases isAdd <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;>
    simp only [evalSaturatingArith, h] <;>
    cases ovf <;> cases isSigned <;> (try cases isSignedNegative lhs.bits lhs.sizeBytes) <;> rfl

/-- Every result of `evalSaturatingArith` on related operands of equal width has
the width of the operands. -/
theorem evalSaturatingArith_sizeBytes (isAdd : Bool)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes) (kind : Miri.MIR.IntegerKind)
    {locals locals' : List LocalSlot} {mem mem' : Memory} {r : MirAst.ScalarInt}
    (h : evalSaturatingArith isAdd sc₁ sc₂ locals mem kind.signed = .ok (.scalar r) locals' mem') :
    r.sizeBytes = sc₁.sizeBytes := by
  obtain ⟨wsc, wmsc, ovf, hA, hM, hwrel⟩ :=
    saturating_withOverflow isAdd hrel₁ hrel₂ hsz_eq kind locals mem
  rw [evalSaturatingArith_of_withOverflow hA] at h
  simp only [RvalueEvalResult.ok.injEq, Value.scalar.injEq] at h
  rw [← h.1]
  cases ovf
  · exact translateSizeBytes_inj hwrel.validBytes hrel₁.validBytes
      (hwrel.size_eq.symm.trans (saturating_withOverflow_size isAdd hrel₁ hrel₂ hsz_eq kind hM))
  · cases kind.signed <;> (try cases isAdd) <;>
      (try cases isSignedNegative sc₁.bits sc₁.sizeBytes) <;> rfl

/-- `liftScalarResult` of a successful result is `pure`. -/
private theorem liftScalarResult_mapError_ok {S A ε : Type} (f : ε → Miri.Interpreter.StepError)
    (x : A) : liftScalarResult (S := S) (Except.mapError f (.ok x)) = pure x := rfl

/-- A canonical bit pattern decodes to a non-negative signed integer exactly
when Anneal's `isSignedNegative` is `false`. -/
private theorem decodeBitsInt_true_nonneg_iff {sz x : Nat} (hsz : ValidScalarBytes sz)
    (hx : x < 2 ^ (8 * sz)) :
    decodeBitsInt true sz x ≥ 0 ↔ isSignedNegative x sz = false := by
  rw [isSignedNegative_eq hsz hx, decide_eq_false_iff_not, Nat.not_le]
  unfold decodeBitsInt
  by_cases hlt : x < 2 ^ (8 * sz - 1)
  · simp only [hlt, ↓reduceIte, iff_true]
    omega
  · simp only [hlt, ↓reduceIte, iff_false]
    omega

/-- **`annealSaturatingEval_simulation` (`LM-4.2`)**: on `ScalarRel`-related
operands of the integral type `ty`, Anneal's `evalSaturatingArith` returns a
scalar `r` without changing locals or memory, and `annealSaturatingEval` writes
a scalar `mr` related to `r` to `dest` and returns to `target`.

Neither machine reports undefined behavior. Both compute the overflowing
operation (`AddWithOverflow` / `SubWithOverflow`) and keep its wrapped result
when the overflow flag is clear. Otherwise both saturate: a signed type at its
maximum or minimum by the sign of the first operand, an unsigned type at its
maximum (addition) or `0` (subtraction). -/
theorem annealSaturatingEval_simulation
    {ld : List LocalDecl} {ly : LayoutTable} (isAdd : Bool) {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (hint : IsIntegralTy ty kind)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz₁ : (translateTy ty ly).layout.size = translateSizeBytes sc₁.sizeBytes)
    (hsz₂ : (translateTy ty ly).layout.size = translateSizeBytes sc₂.sizeBytes)
    (locals : List LocalSlot) (mem : Memory)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId)
    (m : AnnealStepState) :
    ∃ r mr, evalSaturatingArith isAdd sc₁ sc₂ locals mem kind.signed = .ok (.scalar r) locals mem ∧
      ScalarRel r mr ∧
      annealSaturatingEval ld ly isAdd
          ⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty ly⟩
          ⟨.immediate (.scalar (.fromScalarInt msc₂)), translateTy ty ly⟩ dest target m =
        (do annealWriteImmediate (.scalar (.fromScalarInt mr)) dest
            annealReturnToBlock target
            pure true) m := by
  have hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes :=
    translateSizeBytes_inj hrel₁.validBytes hrel₂.validBytes (hsz₁.symm.trans hsz₂)
  obtain ⟨wsc, wmsc, ovf, hA, hM, hwrel⟩ :=
    saturating_withOverflow isAdd hrel₁ hrel₂ hsz_eq kind locals mem
  rw [evalSaturatingArith_of_withOverflow hA]
  have hR₁ : annealReadImmediate
      (⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty ly⟩ :
        Miri.Interpreter.OpTy AnnealProv) =
      pure ⟨.scalar (.fromScalarInt msc₁), translateTy ty ly⟩ := rfl
  have hR₂ : annealReadImmediate
      (⟨.immediate (.scalar (.fromScalarInt msc₂)), translateTy ty ly⟩ :
        Miri.Interpreter.OpTy AnnealProv) =
      pure ⟨.scalar (.fromScalarInt msc₂), translateTy ty ly⟩ := rfl
  have hK : annealIntegerKindOf (translateTy ty ly).ty = pure kind := by
    unfold annealIntegerKindOf
    rw [show (translateTy ty ly).ty = encodeTyId ty from rfl, hint.classify]
  have hB : Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) ()
      (if isAdd = true then .AddWithOverflow else .SubWithOverflow)
      ⟨.scalar (.fromScalarInt msc₁), translateTy ty ly⟩
      ⟨.scalar (.fromScalarInt msc₂), translateTy ty ly⟩ =
      pure ⟨.scalarPair (.fromScalarInt wmsc) (.fromBool ovf),
        findOverflowTupleLayout ld ly (translateTy ty ly)⟩ := by
    funext s
    have hstep := scalarOps_binary_integer_step ld
      (bop := if isAdd then .addWithOverflow else .subWithOverflow)
      hint hint hrel₁ hrel₂ hsz₁ hsz₂ (Or.inr rfl) s
    have htr : translateBinOp (if isAdd then .addWithOverflow else .subWithOverflow) =
        (if isAdd then .AddWithOverflow else .SubWithOverflow) := by cases isAdd <;> rfl
    rw [htr, hM] at hstep
    rw [hstep]
    rfl
  have hO : liftScalarResult (S := AnnealStepState)
      (Except.mapError Miri.Interpreter.ScalarOps.scalarError
        (Miri.Memory.Scalar.fromBool (Prov := AnnealProv) ovf).toBool) = pure ovf := by
    rw [scalar_fromBool_toBool]; rfl
  have hP : liftScalarResult (S := AnnealStepState)
      (Except.mapError Miri.Interpreter.ScalarOps.immediateError
        (Miri.Interpreter.Immediate.scalarPair (Prov := AnnealProv) (.fromScalarInt wmsc)
          (.fromBool ovf)).toScalarPair) = pure (.fromScalarInt wmsc, .fromBool ovf) := rfl
  have hS : liftScalarResult (S := AnnealStepState)
      (Except.mapError Miri.Interpreter.ScalarOps.immediateError
        (Miri.Interpreter.Immediate.scalar (Prov := AnnealProv) (.fromScalarInt msc₁)).toScalar) =
      pure (.fromScalarInt msc₁) := rfl
  unfold annealSaturatingEval
  simp only [hR₁, hR₂, pure_bind, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hK, hB, hP,
    hO, hint.backendRepr_isSigned ly, hS, hsz₁, scalar_fromScalarInt_toInt_eq hrel₁,
    liftScalarResult_mapError_ok]
  cases ovf
  · exact ⟨wsc, wmsc, rfl, hwrel, rfl⟩
  · have hx : sc₁.bits < 2 ^ (8 * sc₁.sizeBytes) := by
      rw [← scalarModulus_eq_two_pow]; exact hrel₁.canonical
    cases hs : kind.signed
    · cases isAdd
      · obtain ⟨mr, hfrom, hrel⟩ := saturating_unsignedZero hrel₁.validBytes
        refine ⟨⟨0, sc₁.sizeBytes⟩, mr, rfl, hrel, ?_⟩
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hfrom,
          liftScalarResult_mapError_ok, pure_bind]
      · obtain ⟨bound, mr, hmax, hfrom, hrel⟩ := saturating_unsignedMax hrel₁.validBytes
        refine ⟨⟨Nat.sub (scalarModulus sc₁.sizeBytes) 1, sc₁.sizeBytes⟩, mr, rfl, hrel, ?_⟩
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hmax, hfrom,
          liftScalarResult_mapError_ok, pure_bind]
    · cases hneg : isSignedNegative sc₁.bits sc₁.sizeBytes
      · have hge : decodeBitsInt true sc₁.sizeBytes sc₁.bits ≥ 0 :=
          (decodeBitsInt_true_nonneg_iff hrel₁.validBytes hx).mpr hneg
        obtain ⟨bound, mr, hmax, hfrom, hrel⟩ := saturating_signedMax hrel₁.validBytes
        refine ⟨⟨Nat.sub (signedHalfModulus sc₁.sizeBytes) 1, sc₁.sizeBytes⟩, mr, rfl, hrel, ?_⟩
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hge, hmax, hfrom,
          liftScalarResult_mapError_ok, pure_bind]
      · have hlt : ¬ decodeBitsInt true sc₁.sizeBytes sc₁.bits ≥ 0 := by
          rw [decodeBitsInt_true_nonneg_iff hrel₁.validBytes hx, hneg]; decide
        obtain ⟨bound, mr, hmin, hfrom, hrel⟩ := saturating_signedMin hrel₁.validBytes
        refine ⟨⟨signedHalfModulus sc₁.sizeBytes, sc₁.sizeBytes⟩, mr, rfl, hrel, ?_⟩
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlt, hmin, hfrom,
          liftScalarResult_mapError_ok, pure_bind]

end LeanMiriSpec.Correspondence
