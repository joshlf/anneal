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
# `exact_div` Simulation for `LM-4.2`

Relates Anneal's `evalScalarExactDiv` to the `exact_div` arm of the vendored
`Miri.Interpreter.Intrinsics.eval` under `annealIntrinsicHooks`
(`annealExactDivEval` in `IntrinsicLM4_2.lean`).

The two sides compute exact division differently. The vendored arm runs
`ScalarOps.binary .Rem`, reports undefined behavior for a nonzero remainder,
and then runs `ScalarOps.binary .Div`. Anneal's `evalExactDiv` instead checks
the divisor, signed overflow, and the remainder of the magnitudes directly.

* `evalExactDiv_rem_div_cases` proves, inside Anneal, that `evalExactDiv`
  agrees with `evalScalarBinOp .rem` followed by `evalScalarBinOp .div`.
* `annealExactDivEval_scalar_eq` discharges the arm's operand reads and type
  checks on two immediate scalars of one integral type.
* `annealExactDivEval_simulation` combines both with the existing `Rem` and
  `Div` simulation (`evalBinOp_arithmetic_simulation`).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Anneal side: exact division through `rem` and `div` -/

/-- Packages the remainder bits `RB`, quotient bits `DB`, and exact-division
result `E` of one width `sz` into the existential shape of
`evalExactDiv_rem_div_cases`. -/
private theorem exactDiv_finish {RB DB sz : Nat} {E : Option MirAst.ScalarInt}
    {locals : List LocalSlot} {mem : Memory}
    (h : (RB ≠ 0 ∧ E = none) ∨ (RB = 0 ∧ E = some ⟨DB, sz⟩)) :
    ∃ r : MirAst.ScalarInt,
      RvalueEvalResult.ok (.scalar ⟨RB, sz⟩) locals mem = .ok (.scalar r) locals mem ∧
      r.sizeBytes = sz ∧
      ((r.bits ≠ 0 ∧ E = none) ∨
        (r.bits = 0 ∧ ∃ q : MirAst.ScalarInt,
          RvalueEvalResult.ok (.scalar ⟨DB, sz⟩) locals mem = .ok (.scalar q) locals mem ∧
          E = some q)) := by
  refine ⟨⟨RB, sz⟩, rfl, rfl, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, ⟨DB, sz⟩, rfl, h2⟩

/-- **Exact division through `rem` and `div`.** On two canonical scalars of one
valid width, Anneal's `evalExactDiv` agrees with evaluating
`evalScalarBinOp .rem` and then `evalScalarBinOp .div`, the order the vendored
`exact_div` arm uses:

* if `rem` is undefined behavior (`rhs = 0`, or signed `MIN % -1`),
  `evalExactDiv` returns `none`;
* if `rem` returns a nonzero remainder of the same width, `evalExactDiv`
  returns `none`;
* if `rem` returns zero, `div` returns a quotient `q` and `evalExactDiv`
  returns `some q`. -/
theorem evalExactDiv_rem_div_cases {sc₁ sc₂ : MirAst.ScalarInt} (signed : Bool)
    (hsz : ValidScalarBytes sc₁.sizeBytes) (hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes)
    (hx : sc₁.bits < scalarModulus sc₁.sizeBytes) (hy : sc₂.bits < scalarModulus sc₁.sizeBytes)
    (locals : List LocalSlot) (mem : Memory) :
    (evalScalarBinOp .rem sc₁ sc₂ locals mem signed = .ub ∧ evalExactDiv sc₁ sc₂ signed = none) ∨
    (∃ r : MirAst.ScalarInt,
      evalScalarBinOp .rem sc₁ sc₂ locals mem signed = .ok (.scalar r) locals mem ∧
      r.sizeBytes = sc₁.sizeBytes ∧
      ((r.bits ≠ 0 ∧ evalExactDiv sc₁ sc₂ signed = none) ∨
        (r.bits = 0 ∧ ∃ q : MirAst.ScalarInt,
          evalScalarBinOp .div sc₁ sc₂ locals mem signed = .ok (.scalar q) locals mem ∧
          evalExactDiv sc₁ sc₂ signed = some q))) := by
  obtain ⟨x, sz⟩ := sc₁
  obtain ⟨y, sz₂⟩ := sc₂
  dsimp only at hsz hsz_eq hx hy ⊢
  subst hsz_eq
  rw [scalarModulus_eq_two_pow] at hx hy
  obtain ⟨hM, hH⟩ := two_pow_byte_split hsz
  have hbeq0 : Nat.beq sz 0 = false := by
    rcases hsz with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hw0 := (validScalarBytes_bits_le_128 hsz).2
  have hhalf : signedHalfModulus sz = 2 ^ (8 * sz - 1) := by
    simp only [signedHalfModulus, scalarModulus_eq_two_pow, two_pow_div_two (8 * sz) hw0]
  by_cases hy0 : y = 0
  · subst hy0
    left
    constructor
    · simp only [evalScalarBinOp, hbeq0, Nat.beq_refl]
    · simp only [evalExactDiv, hbeq0, Nat.beq_refl, Bool.not_false, Bool.and_true,
        wrapScalarBits_eq_mod, Nat.zero_mod]
  have hyb : Nat.beq y 0 = false := by
    rw [nat_beq_eq_decide]; exact decide_eq_false hy0
  cases signed
  · -- unsigned
    have hrlt : x % y < 2 ^ (8 * sz) := Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hy0)) hy
    have hqlt : x / y < 2 ^ (8 * sz) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
    have hrem : evalScalarBinOp .rem ⟨x, sz⟩ ⟨y, sz⟩ locals mem false =
        .ok (.scalar ⟨x % y, sz⟩) locals mem := by
      simp only [evalScalarBinOp, hbeq0, Nat.beq_refl, hyb, scalarModulus_eq_two_pow,
        wrapScalarBits_eq_mod, nat_mod_eq_mod, Nat.mod_eq_of_lt hrlt]
    have hdiv : evalScalarBinOp .div ⟨x, sz⟩ ⟨y, sz⟩ locals mem false =
        .ok (.scalar ⟨x / y, sz⟩) locals mem := by
      simp only [evalScalarBinOp, hbeq0, Nat.beq_refl, hyb, scalarModulus_eq_two_pow,
        wrapScalarBits_eq_mod, nat_div_eq_div, Nat.mod_eq_of_lt hqlt]
    have hex : evalExactDiv ⟨x, sz⟩ ⟨y, sz⟩ false =
        if x % y = 0 then some ⟨x / y, sz⟩ else none := by
      simp only [evalExactDiv, hbeq0, Nat.beq_refl, Bool.not_false, Bool.and_true,
        scalarModulus_eq_two_pow, wrapScalarBits_eq_mod, Nat.mod_eq_of_lt hx,
        Nat.mod_eq_of_lt hy, hyb, nat_mod_eq_mod, nat_div_eq_div]
      by_cases hr0 : x % y = 0
      · simp only [hr0, ↓reduceIte]
      · have hb : Nat.beq (x % y) 0 = false := by rw [nat_beq_eq_decide]; exact decide_eq_false hr0
        simp only [hb, hr0, ↓reduceIte]
    right
    refine ⟨_, hrem, rfl, ?_⟩
    by_cases hr0 : x % y = 0
    · exact Or.inr ⟨hr0, _, hdiv, by simp only [hex, hr0, ↓reduceIte]⟩
    · exact Or.inl ⟨hr0, by simp only [hex, hr0, ↓reduceIte]⟩
  · -- signed
    have hrem : evalScalarBinOp .rem ⟨x, sz⟩ ⟨y, sz⟩ locals mem true =
        evalSignedRem x y sz locals mem := by
      simp only [evalScalarBinOp, hbeq0, Nat.beq_refl, hyb]
    have hdiv : evalScalarBinOp .div ⟨x, sz⟩ ⟨y, sz⟩ locals mem true =
        evalSignedDiv x y sz locals mem := by
      simp only [evalScalarBinOp, hbeq0, Nat.beq_refl, hyb]
    rw [hrem, hdiv]
    simp only [evalSignedRem, evalSignedDiv, evalExactDiv, hbeq0, Nat.beq_refl, Bool.not_false,
      Bool.and_true, hyb, scalarModulus_eq_two_pow, Nat.mul_eq, Nat.sub_eq, Nat.mul_comm sz 8,
      scalarPow2_eq_two_pow, wrapScalarBits_eq_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
      hhalf]
    simp only [isSignedNegative_eq hsz hx, isSignedNegative_eq hsz hy, nat_beq_eq_decide,
      nat_ble_eq_decide, nat_div_eq_div, nat_mod_eq_mod]
    by_cases hg : x = 2 ^ (8 * sz - 1) ∧ y = 2 ^ (8 * sz) - 1
    · left
      have hgb : (decide (x = 2 ^ (8 * sz - 1)) && decide (y = 2 ^ (8 * sz) - 1)) = true := by
        rw [decide_eq_true hg.1, decide_eq_true hg.2]; rfl
      simp only [hgb, and_self]
    · right
      have hgb : (decide (x = 2 ^ (8 * sz - 1)) && decide (y = 2 ^ (8 * sz) - 1)) = false := by
        by_cases h1 : x = 2 ^ (8 * sz - 1)
        · rw [decide_eq_true h1, decide_eq_false (fun h2 => hg ⟨h1, h2⟩)]; rfl
        · rw [decide_eq_false h1]; rfl
      simp only [hgb]
      generalize 2 ^ (8 * sz - 1) = H at hM hH hx hy hg ⊢
      generalize 2 ^ (8 * sz) = M at hM hx hy hg ⊢
      by_cases hxH : H ≤ x <;> by_cases hyH : H ≤ y
      · -- negative dividend, negative divisor
        have hxm : (M - x) % M = M - x := Nat.mod_eq_of_lt (by omega)
        have hym : (M - y) % M = M - y := Nat.mod_eq_of_lt (by omega)
        simp only [decide_eq_true hxH, decide_eq_true hyH, hxm, hym]
        apply exactDiv_finish
        have hrlt : (M - x) % (M - y) < M - y := Nat.mod_lt _ (by omega)
        have hqle : (M - x) / (M - y) ≤ M - x := Nat.div_le_self _ _
        generalize (M - x) % (M - y) = r at hrlt ⊢
        generalize (M - x) / (M - y) = q at hqle ⊢
        by_cases hr0 : r = 0
        · subst hr0
          right
          refine ⟨rfl, ?_⟩
          by_cases hq0 : q = 0
          · subst hq0; rfl
          · simp only [decide_eq_false hq0, Nat.mod_eq_of_lt (show q < M by omega)]
            rfl
        · left
          simp only [decide_eq_false hr0, Nat.mod_eq_of_lt (show M - r < M by omega)]
          exact ⟨Nat.sub_ne_zero_of_lt (Nat.lt_of_lt_of_le hrlt (Nat.sub_le M y)), trivial⟩
      · -- negative dividend, non-negative divisor
        have hxm : (M - x) % M = M - x := Nat.mod_eq_of_lt (by omega)
        simp only [decide_eq_true hxH, decide_eq_false hyH, hxm]
        apply exactDiv_finish
        have hrlt : (M - x) % y < y := Nat.mod_lt _ (by omega)
        have hqle : (M - x) / y ≤ M - x := Nat.div_le_self _ _
        generalize (M - x) % y = r at hrlt ⊢
        generalize (M - x) / y = q at hqle ⊢
        by_cases hr0 : r = 0
        · subst hr0
          right
          refine ⟨rfl, ?_⟩
          by_cases hq0 : q = 0
          · subst hq0
            simp only [Nat.sub_zero, Nat.mod_self]
            rfl
          · simp only [decide_eq_false hq0]
            rfl
        · left
          simp only [decide_eq_false hr0, Nat.mod_eq_of_lt (show M - r < M by omega)]
          exact ⟨Nat.sub_ne_zero_of_lt (Nat.lt_trans hrlt (by omega)), trivial⟩
      · -- non-negative dividend, negative divisor
        have hym : (M - y) % M = M - y := Nat.mod_eq_of_lt (by omega)
        simp only [decide_eq_false hxH, decide_eq_true hyH, hym]
        apply exactDiv_finish
        have hrlt : x % (M - y) < M - y := Nat.mod_lt _ (by omega)
        have hqle : x / (M - y) ≤ x := Nat.div_le_self _ _
        generalize x % (M - y) = r at hrlt ⊢
        generalize x / (M - y) = q at hqle ⊢
        by_cases hr0 : r = 0
        · subst hr0
          right
          refine ⟨rfl, ?_⟩
          by_cases hq0 : q = 0
          · subst hq0
            simp only [Nat.sub_zero, Nat.mod_self]
            rfl
          · simp only [decide_eq_false hq0]
            rfl
        · left
          simp only [decide_eq_false hr0, Nat.mod_eq_of_lt (show r < M by omega)]
          exact ⟨hr0, trivial⟩
      · -- non-negative dividend, non-negative divisor
        simp only [decide_eq_false hxH, decide_eq_false hyH]
        apply exactDiv_finish
        have hrlt : x % y < y := Nat.mod_lt _ (by omega)
        have hqle : x / y ≤ x := Nat.div_le_self _ _
        generalize x % y = r at hrlt ⊢
        generalize x / y = q at hqle ⊢
        by_cases hr0 : r = 0
        · subst hr0
          right
          refine ⟨rfl, ?_⟩
          by_cases hq0 : q = 0
          · subst hq0; rfl
          · simp only [decide_eq_false hq0, Nat.mod_eq_of_lt (show q < M by omega)]
            rfl
        · left
          simp only [decide_eq_false hr0, Nat.mod_eq_of_lt (show r < M by omega)]
          exact ⟨hr0, trivial⟩

/-! ## 2. `lean-miri` side -/

/-- `Scalar.toBits` of the `lean-miri` scalar of a `ScalarRel`-related integer
at its own width returns the 128-bit zero extension of `sc.bits`. -/
theorem scalar_toBits_fromScalarInt_of_scalarRel {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBits
        (translateSizeBytes sc.sizeBytes) = .ok (BitVec.ofNat 128 sc.bits) := by
  have htb := hrel.toBits_eq
  have hb0 : ((translateSizeBytes sc.sizeBytes).bytes == 0) = false := by
    rcases hrel.validBytes with h | h | h | h | h <;> rw [h] <;> rfl
  unfold Miri.Memory.Scalar.toBits Miri.Memory.Scalar.toScalarInt
    Miri.Memory.Scalar.tryToScalarInt Miri.Memory.Scalar.fromScalarInt
  simp only [hb0, Bool.false_eq_true, ↓reduceIte]
  dsimp only [bind, Except.bind, Except.mapError, pure, Except.pure]
  rw [htb]

/-- A nonzero canonical bit pattern stays nonzero in `BitVec 128`. -/
theorem bitVec_ofNat_bne_zero_of_scalarRel {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) (h : sc.bits ≠ 0) :
    (BitVec.ofNat 128 sc.bits != 0) = true := by
  rw [bne_iff_ne, ne_eq]
  intro heq
  have h2 := congrArg BitVec.toNat heq
  rw [bitVec_ofNat_toNat_of_valid hrel.validBytes hrel.canonical] at h2
  exact h h2

/-- Inversion of `IntegerBinOpResultRel` at Anneal undefined behavior. -/
theorem IntegerBinOpResultRel.ub_inv {locals : List LocalSlot} {mem : Memory}
    {res : Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult}
    (h : IntegerBinOpResultRel locals mem .ub res) :
    ∃ reason, res = .error (.undefinedBehavior reason) := by
  cases h with
  | ub reason => exact ⟨reason, rfl⟩

/-- Inversion of `IntegerBinOpResultRel` at an Anneal scalar result whose
`lean-miri` result is not boolean. -/
theorem IntegerBinOpResultRel.scalar_inv {locals : List LocalSlot} {mem : Memory}
    {sc : MirAst.ScalarInt}
    {res : Except Miri.Interpreter.IntegerOpError Miri.Interpreter.IntegerResult}
    (h : IntegerBinOpResultRel locals mem (.ok (.scalar sc) locals mem) res)
    (hnb : ∀ b, res ≠ .ok (.boolean b)) :
    ∃ msc, res = .ok (.scalar msc) ∧ ScalarRel sc msc := by
  cases h with
  | scalar _ msc hrel => exact ⟨msc, rfl, hrel⟩
  | boolean b => exact absurd rfl (hnb b)

/-- `liftScalarResult` of a success passes its value to the continuation. -/
private theorem liftScalarResult_ok_bind {S A B : Type} (a : A)
    (f : A → Miri.Interpreter.RvalueM S B) :
    (liftScalarResult (.ok a) >>= f) = f a := rfl

/-- `annealExactDivEval` on two immediate scalars of one integral type: the
operand reads, the operand type check, and the integer kind check succeed
without changing the state, which leaves `rem`, the remainder test, and
`div`. -/
theorem annealExactDivEval_scalar_eq (ld : List LocalDecl) (ly : LayoutTable) {ty : Ty}
    {kind : Miri.MIR.IntegerKind} (hint : IsIntegralTy ty kind)
    (s₁ s₂ : Miri.Memory.Scalar AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId)
    (m : AnnealStepState) :
    annealExactDivEval ld ly ⟨.immediate (.scalar s₁), translateTy ty ly⟩
        ⟨.immediate (.scalar s₂), translateTy ty ly⟩ dest target m =
      (do
        let rem ← Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) () .Rem
          ⟨.scalar s₁, translateTy ty ly⟩ ⟨.scalar s₂, translateTy ty ly⟩
        let rem ← liftScalarResult
          (rem.imm.toScalar |>.mapError Miri.Interpreter.ScalarOps.immediateError)
        let rem ← liftScalarResult
          (rem.toBits (translateTy ty ly).layout.size |>.mapError
            Miri.Interpreter.ScalarOps.scalarError)
        if rem != 0 then
          throw (Miri.Interpreter.StepError.undefinedBehavior "exact_div has nonzero remainder")
        let result ← Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) () .Div
          ⟨.scalar s₁, translateTy ty ly⟩ ⟨.scalar s₂, translateTy ty ly⟩
        annealWriteImmediate result.imm dest
        annealReturnToBlock target
        pure true) m := by
  have hcls : classifyEncodedTyId (translateTy ty ly).ty = .ok (.integer kind) := hint.classify
  have hk : annealIntegerKindOf (translateTy ty ly).ty = pure kind := by
    unfold annealIntegerKindOf
    simp only [hcls]
  have hk' : annealIntegerKindOf (translateTy ty ly).ty m = .ok kind m := (congrFun hk m).trans rfl
  have hr₁ : annealReadImmediate ⟨.immediate (.scalar s₁), translateTy ty ly⟩ m =
      .ok ⟨.scalar s₁, translateTy ty ly⟩ m := rfl
  have hr₂ : annealReadImmediate ⟨.immediate (.scalar s₂), translateTy ty ly⟩ m =
      .ok ⟨.scalar s₂, translateTy ty ly⟩ m := rfl
  unfold annealExactDivEval
  rw [EStateM.bind_eq_ok hr₁]
  dsimp only
  rw [EStateM.bind_eq_ok hr₂]
  dsimp only
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact (EStateM.bind_eq_ok hk').trans rfl

/-! ## 3. The `exact_div` arm -/

/-- **Simulation of the `exact_div` arm.** On two related immediate scalars of
one integral type, Anneal's `evalScalarExactDiv` and the vendored `exact_div`
arm of `Intrinsics.eval` (`annealExactDivEval`) agree:

* both report undefined behavior (division by zero, signed `MIN / -1`, or a
  nonzero remainder), and `lean-miri` fails in the unchanged state `m`; or
* Anneal returns a quotient `q` related to a `lean-miri` quotient `mq`, and the
  arm continues from `m` by writing `mq` to `dest` and returning to `target`. -/
theorem annealExactDivEval_simulation
    {ld : List LocalDecl} {ly : LayoutTable} {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (hint : IsIntegralTy ty kind)
    {sc₁ sc₂ : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁) (hrel₂ : ScalarRel sc₂ msc₂)
    (hsz₁ : (translateTy ty ly).layout.size = translateSizeBytes sc₁.sizeBytes)
    (hsz₂ : (translateTy ty ly).layout.size = translateSizeBytes sc₂.sizeBytes)
    (locals : List LocalSlot) (mem : Memory)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId)
    (m : AnnealStepState) :
    (evalScalarExactDiv sc₁ sc₂ locals mem kind.signed = .ub ∧
      ∃ msg, annealExactDivEval ld ly ⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty ly⟩
          ⟨.immediate (.scalar (.fromScalarInt msc₂)), translateTy ty ly⟩ dest target m =
        .error (.undefinedBehavior msg) m) ∨
    (∃ q mq, evalScalarExactDiv sc₁ sc₂ locals mem kind.signed = .ok (.scalar q) locals mem ∧
      ScalarRel q mq ∧
      annealExactDivEval ld ly ⟨.immediate (.scalar (.fromScalarInt msc₁)), translateTy ty ly⟩
          ⟨.immediate (.scalar (.fromScalarInt msc₂)), translateTy ty ly⟩ dest target m =
        (do annealWriteImmediate (.scalar (.fromScalarInt mq)) dest
            annealReturnToBlock target
            pure true) m) := by
  have hsz_eq : sc₁.sizeBytes = sc₂.sizeBytes :=
    translateSizeBytes_inj hrel₁.validBytes hrel₂.validBytes (hsz₁.symm.trans hsz₂)
  have hy : sc₂.bits < scalarModulus sc₁.sizeBytes := hsz_eq ▸ hrel₂.canonical
  have hstepR := scalarOps_binary_integer_step ld (bop := .rem) hint hint hrel₁ hrel₂ hsz₁ hsz₂
    (Or.inr rfl) m
  have hstepD := scalarOps_binary_integer_step ld (bop := .div) hint hint hrel₁ hrel₂ hsz₁ hsz₂
    (Or.inr rfl) m
  obtain ⟨-, -, hnoBoolR⟩ := integerOps_binary_noncmp_nonovf_shape (op := .rem)
    (Or.inl (by simp [IsNonOvfArithOrBitwiseBinOp])) hrel₁ hrel₂ kind kind
  obtain ⟨-, -, hnoBoolD⟩ := integerOps_binary_noncmp_nonovf_shape (op := .div)
    (Or.inl (by simp [IsNonOvfArithOrBitwiseBinOp])) hrel₁ hrel₂ kind kind
  have hirelR := evalBinOp_arithmetic_simulation (op := .rem)
    (by simp [IsArithmeticOrCmpBinOp]) rfl hrel₁ hrel₂ hsz_eq kind locals mem
  have hirelD := evalBinOp_arithmetic_simulation (op := .div)
    (by simp [IsArithmeticOrCmpBinOp]) rfl hrel₁ hrel₂ hsz_eq kind locals mem
  rw [annealExactDivEval_scalar_eq ld ly hint]
  rcases evalExactDiv_rem_div_cases kind.signed hrel₁.validBytes hsz_eq hrel₁.canonical hy
      locals mem with
    ⟨hremUB, hexNone⟩ | ⟨r, hremOk, hrsz, ⟨hr0, hexNone⟩ | ⟨hr0, q, hdivOk, hexSome⟩⟩
  · -- `rem` is undefined behavior: division by zero or signed `MIN % -1`.
    left
    refine ⟨by simp only [evalScalarExactDiv, hexNone], ?_⟩
    rw [hremUB] at hirelR
    obtain ⟨reason, hR⟩ := hirelR.ub_inv
    rw [hR] at hstepR
    have hm : Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) () .Rem
        ⟨.scalar (.fromScalarInt msc₁), translateTy ty ly⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy ty ly⟩ m =
        .error (.undefinedBehavior (toString (repr reason))) m := hstepR.trans rfl
    exact ⟨_, EStateM.bind_eq_error hm⟩
  · -- A nonzero remainder.
    left
    refine ⟨by simp only [evalScalarExactDiv, hexNone], ?_⟩
    rw [hremOk] at hirelR
    obtain ⟨mr, hR, hrelr⟩ := hirelR.scalar_inv hnoBoolR
    rw [hR] at hstepR
    have hm : Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) () .Rem
        ⟨.scalar (.fromScalarInt msc₁), translateTy ty ly⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy ty ly⟩ m =
        .ok ⟨.scalar (.fromScalarInt mr), translateTy ty ly⟩ m := hstepR.trans rfl
    have htb : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) mr).toBits
        (translateTy ty ly).layout.size = .ok (BitVec.ofNat 128 r.bits) := by
      rw [hsz₁, ← hrsz]
      exact scalar_toBits_fromScalarInt_of_scalarRel hrelr
    have hne := bitVec_ofNat_bne_zero_of_scalarRel hrelr hr0
    refine ⟨"exact_div has nonzero remainder", ?_⟩
    rw [EStateM.bind_eq_ok hm]
    simp only [Miri.Interpreter.Immediate.toScalar, Except.mapError, liftScalarResult_ok_bind,
      htb, hne, ↓reduceIte]
    rfl
  · -- A zero remainder: `div` succeeds.
    right
    rw [hremOk] at hirelR
    obtain ⟨mr, hR, hrelr⟩ := hirelR.scalar_inv hnoBoolR
    rw [hR] at hstepR
    rw [hdivOk] at hirelD
    obtain ⟨mq, hD, hrelq⟩ := hirelD.scalar_inv hnoBoolD
    rw [hD] at hstepD
    have hm : Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) () .Rem
        ⟨.scalar (.fromScalarInt msc₁), translateTy ty ly⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy ty ly⟩ m =
        .ok ⟨.scalar (.fromScalarInt mr), translateTy ty ly⟩ m := hstepR.trans rfl
    have hmD : Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) () .Div
        ⟨.scalar (.fromScalarInt msc₁), translateTy ty ly⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy ty ly⟩ m =
        .ok ⟨.scalar (.fromScalarInt mq), translateTy ty ly⟩ m := hstepD.trans rfl
    have htb : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) mr).toBits
        (translateTy ty ly).layout.size = .ok (BitVec.ofNat 128 r.bits) := by
      rw [hsz₁, ← hrsz]
      exact scalar_toBits_fromScalarInt_of_scalarRel hrelr
    have hz : (BitVec.ofNat 128 r.bits != 0) = false := by
      rw [hr0]; decide
    refine ⟨q, mq, by simp only [evalScalarExactDiv, hexSome], hrelq, ?_⟩
    rw [EStateM.bind_eq_ok hm]
    simp only [Miri.Interpreter.Immediate.toScalar, Except.mapError, liftScalarResult_ok_bind,
      htb, hz, Bool.false_eq_true, ↓reduceIte]
    exact (EStateM.bind_eq_ok hmD).trans rfl

end LeanMiriSpec.Correspondence
